import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.LocalField.Lattices
import LanglandsFirstMainLemma.LocalField.MonogenicUniformizer
import LanglandsFirstMainLemma.LocalField.Valuation
import LanglandsSecondMainLemma.Basic.Fields
import LanglandsSecondMainLemma.Local.Newton
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Invariant.Galois

/-!
# Ramification / Unramified Part

This file formalizes the first paragraph of the proof of Paper Lemma D.2. For an actual finite
Galois extension of nonarchimedean local fields, it constructs the residue action on the actual
residue fields, identifies its quotient by inertia with the residue Galois group, and constructs
the inertia fixed field by lifting a primitive residue element with the quantitative Newton
lemma.

The degree calculation is retained: the lifted-generator field has degree equal to the total
residue degree, its residue field maps onto the residue field of the ambient extension, and its
ramification index is one. Thus the fixed-field assertion is an equality of actual intermediate
fields, not merely an abstract field isomorphism.
-/

namespace LanglandsSecondMainLemma.Ramification

open LanglandsFirstMainLemma
open Polynomial
open scoped Pointwise

noncomputable section

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]

private noncomputable def galoisIntegerAutHom :
    Gal(K/F) →* RingAut (ringOfIntegers K) where
  toFun := galoisIntegerEquiv F K
  map_one' := by
    ext x
    rfl
  map_mul' σ τ := by
    ext x
    rfl

@[implicit_reducible]
private noncomputable def galoisIntegerAction :
    MulSemiringAction Gal(K/F) (ringOfIntegers K) :=
  MulSemiringAction.compHom (ringOfIntegers K)
    (galoisIntegerAutHom (F := F) (K := K))

section ResidueAction

local instance : MulSemiringAction Gal(K/F) (ringOfIntegers K) :=
  galoisIntegerAction

local instance : SMulCommClass Gal(K/F) (ringOfIntegers F) (ringOfIntegers K) :=
  { smul_comm := by
      intro σ x y
      have hfix : σ • algebraMap (ringOfIntegers F) (ringOfIntegers K) x =
          algebraMap (ringOfIntegers F) (ringOfIntegers K) x := by
        apply Subtype.ext
        change σ (algebraMap F K (x : F)) = algebraMap F K (x : F)
        simp
      rw [Algebra.smul_def, smul_mul', hfix, ← Algebra.smul_def] }

local instance : SMulDistribClass Gal(K/F) (ringOfIntegers K) K :=
  { smul_distrib_smul := by
      intro σ x y
      change σ ((x : K) * y) = ((σ • x : ringOfIntegers K) : K) * σ y
      rw [map_mul]
      rfl }

private lemma maximalIdeal_fixed (σ : Gal(K/F)) :
    σ • IsLocalRing.maximalIdeal (ringOfIntegers K) =
      IsLocalRing.maximalIdeal (ringOfIntegers K) := by
  rw [Ideal.pointwise_smul_def]
  exact IsLocalRing.map_ringEquiv_maximalIdeal (galoisIntegerEquiv F K σ)

private noncomputable def allStabilizerHom :
    Gal(K/F) →*
      MulAction.stabilizer Gal(K/F) (IsLocalRing.maximalIdeal (ringOfIntegers K)) :=
  (MonoidHom.id Gal(K/F)).codRestrict _ fun σ =>
    maximalIdeal_fixed (F := F) (K := K) σ

private theorem allStabilizerHom_surjective :
    Function.Surjective (allStabilizerHom (F := F) (K := K)) := by
  rintro ⟨σ, hσ⟩
  exact ⟨σ, rfl⟩

variable [IsGalois F K]

local instance : IsIntegralClosure
    (ringOfIntegers K) (ringOfIntegers F) K :=
  ringOfIntegers_isIntegralClosure F K

local instance : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
  ringOfIntegers_moduleFinite F K

local instance : IsGaloisGroup Gal(K/F)
    (ringOfIntegers F) (ringOfIntegers K) :=
  IsGaloisGroup.of_isFractionRing Gal(K/F)
    (ringOfIntegers F) (ringOfIntegers K) F K

/-- The genuine residue action of the Galois group of `K/F`. It is obtained by restricting
Galois automorphisms to the integer ring and then using the canonical action on its quotient by
the maximal ideal. -/
noncomputable def residueAction :
    Gal(K/F) →* Gal(ResidueField K / ResidueField F) :=
  (Ideal.Quotient.stabilizerHom
    (IsLocalRing.maximalIdeal (ringOfIntegers K))
    (IsLocalRing.maximalIdeal (ringOfIntegers F)) Gal(K/F)).comp
      (allStabilizerHom (F := F) (K := K))

/-- The residue action is onto the actual residue-field Galois group. -/
theorem residueAction_surjective :
    Function.Surjective (residueAction (F := F) (K := K)) :=
  (Ideal.Quotient.stabilizerHom_surjective Gal(K/F)
    (IsLocalRing.maximalIdeal (ringOfIntegers F))
    (IsLocalRing.maximalIdeal (ringOfIntegers K))).comp
      (allStabilizerHom_surjective (F := F) (K := K))

/-- On an integral element, the residue action is reduction after applying the original Galois
automorphism. -/
@[simp]
theorem residueAction_apply_residue (σ : Gal(K/F)) (x : ringOfIntegers K) :
    residueAction (F := F) (K := K) σ (residueMap K x) =
      residueMap K (galoisIntegerEquiv F K σ x) := by
  change Ideal.Quotient.stabilizerHom _ _ Gal(K/F)
      (allStabilizerHom (F := F) (K := K) σ) (residueMap K x) = _
  rw [show residueMap K x =
      (x : (ringOfIntegers K) ⧸
        IsLocalRing.maximalIdeal (ringOfIntegers K)) from rfl,
    Ideal.Quotient.stabilizerHom_apply]
  rfl

end ResidueAction

/-- Inertia is the kernel of the actual residue action. -/
@[reducible]
def inertiaSubgroup [IsGalois F K] : Subgroup Gal(K/F) :=
  (residueAction (F := F) (K := K)).ker

/-- The residue action itself, rather than a cardinality comparison, identifies the quotient by
inertia with the Galois group of the actual residue-field extension. -/
noncomputable def residueActionQuotientEquiv [IsGalois F K] :
    Gal(K/F) ⧸ inertiaSubgroup (F := F) (K := K) ≃*
      Gal(ResidueField K / ResidueField F) :=
  QuotientGroup.liftEquiv (inertiaSubgroup (F := F) (K := K))
    (residueAction_surjective (F := F) (K := K)) rfl

/-- The quotient equivalence is induced by the residue action. -/
@[simp]
theorem residueActionQuotientEquiv_mk [IsGalois F K] (σ : Gal(K/F)) :
    residueActionQuotientEquiv (F := F) (K := K) (QuotientGroup.mk σ) =
      residueAction (F := F) (K := K) σ := by
  rfl

omit [Module.Finite F K] in
/-- Lift a primitive residue element together with the Newton neighborhood in which its lift is
unique. The uniqueness data is kept private and is used below to identify the fixing subgroup. -/
private theorem lift_residue_generator [IsGalois F K] :
    ∃ (a a0 : ringOfIntegers K) (P : (ringOfIntegers F)[X]),
      P.Monic ∧
      P.map (residueMap F) = minpoly (ResidueField F) (residueMap K a) ∧
      IntermediateField.adjoin (ResidueField F) {residueMap K a} = ⊤ ∧
      (P.map (algebraMap (ringOfIntegers F) (ringOfIntegers K))).IsRoot a ∧
      residueMap K a0 = residueMap K a ∧
      (0 : WithTop ℤ) < ord K ((a : K) - (a0 : K)) ∧
      ∀ c : ringOfIntegers K,
        (P.map (algebraMap (ringOfIntegers F) (ringOfIntegers K))).IsRoot c →
        (0 : WithTop ℤ) < ord K ((c : K) - (a0 : K)) → c = a := by
  let abar : ResidueField K :=
    (Field.exists_primitive_element (ResidueField F) (ResidueField K)).choose
  have habar : IntermediateField.adjoin (ResidueField F) {abar} = ⊤ :=
    (Field.exists_primitive_element (ResidueField F) (ResidueField K)).choose_spec
  let pbar : (ResidueField F)[X] := minpoly (ResidueField F) abar
  obtain ⟨P, hPred, _, hPmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective (residueMap_surjective F) pbar)
      (minpoly.monic (Algebra.IsIntegral.isIntegral abar))
  let PK : (ringOfIntegers K)[X] :=
    P.map (algebraMap (ringOfIntegers F) (ringOfIntegers K))
  let a0 : ringOfIntegers K := teichmuller K abar
  have hPKred : PK.map (residueMap K) =
      pbar.map (extensionResidueMap F K) := by
    calc
      PK.map (residueMap K) =
          P.map ((residueMap K).comp
            (algebraMap (ringOfIntegers F) (ringOfIntegers K))) :=
        Polynomial.map_map _ _ _
      _ = P.map ((extensionResidueMap F K).comp (residueMap F)) := by
        congr 2
      _ = (P.map (residueMap F)).map (extensionResidueMap F K) := by
        rw [Polynomial.map_map]
      _ = pbar.map (extensionResidueMap F K) := by rw [hPred]
  have hreszero : residueMap K (PK.eval a0) = 0 := by
    rw [← Polynomial.eval_map_apply, hPKred, residueMap_teichmuller]
    simpa [pbar, Polynomial.aeval_def] using minpoly.aeval (ResidueField F) abar
  have hrespos :
      (0 : WithTop ℤ) < ord K ((PK.eval a0 : ringOfIntegers K) : K) := by
    apply (ord_pos_iff_mem_maximalIdeal K (PK.eval a0)).2
    exact (IsLocalRing.residue_eq_zero_iff (PK.eval a0)).1 hreszero
  have hderivred : residueMap K (PK.derivative.eval a0) ≠ 0 := by
    rw [← Polynomial.eval_map_apply, ← Polynomial.derivative_map, hPKred,
      Polynomial.derivative_map, residueMap_teichmuller]
    simpa [pbar, Polynomial.aeval_def] using
      (Algebra.IsSeparable.isSeparable (ResidueField F) abar).aeval_derivative_ne_zero
        (minpoly.aeval (ResidueField F) abar)
  have hderivord :
      ord K ((PK.derivative.eval a0 : ringOfIntegers K) : K) =
        (0 : WithTop ℤ) := by
    apply le_antisymm
    · apply le_of_not_gt
      intro hpos
      have hmem :=
        (ord_pos_iff_mem_maximalIdeal K (PK.derivative.eval a0)).1 hpos
      exact hderivred ((IsLocalRing.residue_eq_zero_iff _).2 hmem)
    · exact (ord_nonneg_iff_mem_integer K _).2 (PK.derivative.eval a0).property
  obtain ⟨a, haRoot, haBall, _, haUnique⟩ :=
    Local.newton PK a0 0 hderivord (by simpa using hrespos)
  have haRed : residueMap K a = abar := by
    rw [← residueMap_teichmuller K abar, residueMap_eq_residueMap_iff]
    change (((a - a0 : ringOfIntegers K) : K)) ∈ lattice K 1
    rw [mem_lattice_one_iff_mem_maximalIdeal K (a - a0)]
    exact (ord_pos_iff_mem_maximalIdeal K (a - a0)).1 (by simpa using haBall)
  refine ⟨a, a0, P, hPmonic, ?_, ?_, haRoot, ?_, haBall, haUnique⟩
  · simpa [pbar, haRed] using hPred
  · simpa [haRed] using habar
  · calc
      residueMap K a0 = abar := by simp [a0]
      _ = residueMap K a := haRed.symm

/-- The Newton lift is fixed exactly by inertia. -/
private theorem maximalUnramified_fixedField_aux [IsGalois F K] :
    ∃ (a : ringOfIntegers K) (P : (ringOfIntegers F)[X]),
      P.Monic ∧
      P.map (residueMap F) = minpoly (ResidueField F) (residueMap K a) ∧
      IntermediateField.adjoin (ResidueField F) {residueMap K a} = ⊤ ∧
      (P.map (algebraMap (ringOfIntegers F) (ringOfIntegers K))).IsRoot a ∧
      IntermediateField.adjoin F {(a : K)} =
        IntermediateField.fixedField (inertiaSubgroup (F := F) (K := K)) := by
  obtain ⟨a, a0, P, hPmonic, hPred, hprimitive, haRoot, ha0red, haNear, haUnique⟩ :=
    lift_residue_generator (F := F) (K := K)
  let E : IntermediateField F K := IntermediateField.adjoin F {(a : K)}
  have hfixing : E.fixingSubgroup = inertiaSubgroup (F := F) (K := K) := by
    ext σ
    constructor
    · intro hσ
      have hσfix : ∀ x ∈ E, σ x = x :=
        (IntermediateField.mem_fixingSubgroup_iff E σ).1 hσ
      have hσaK : σ (a : K) = (a : K) := by
        apply hσfix
        exact IntermediateField.subset_adjoin F {(a : K)}
          (Set.mem_singleton (a : K))
      have hσa : galoisIntegerEquiv F K σ a = a := Subtype.ext hσaK
      change residueAction (F := F) (K := K) σ = 1
      have hprimitiveAlg :
          Algebra.adjoin (ResidueField F) {residueMap K a} = ⊤ :=
        (IntermediateField.adjoin_eq_top_iff).1 hprimitive
      have hAlgHom :
          (residueAction (F := F) (K := K) σ :
              ResidueField K →ₐ[ResidueField F] ResidueField K) =
            (1 : Gal(ResidueField K / ResidueField F)) := by
        apply AlgHom.ext_of_adjoin_eq_top hprimitiveAlg
        intro x hx
        simp only [Set.mem_singleton_iff] at hx
        subst x
        simp [hσa]
      apply AlgEquiv.ext
      intro x
      exact DFunLike.congr_fun hAlgHom x
    · intro hσ
      change residueAction (F := F) (K := K) σ = 1 at hσ
      let σa : ringOfIntegers K := galoisIntegerEquiv F K σ a
      have hσaRed : residueMap K σa = residueMap K a0 := by
        calc
          residueMap K σa =
              residueAction (F := F) (K := K) σ (residueMap K a) := by
            symm
            exact residueAction_apply_residue (F := F) (K := K) σ a
          _ = residueMap K a := by rw [hσ]; rfl
          _ = residueMap K a0 := ha0red.symm
      have hcoeff :
          (galoisIntegerEquiv F K σ).toRingHom.comp
              (algebraMap (ringOfIntegers F) (ringOfIntegers K)) =
            algebraMap (ringOfIntegers F) (ringOfIntegers K) := by
        ext x
        change σ (algebraMap F K (x : F)) = algebraMap F K (x : F)
        simp
      have hσaRoot :
          (P.map (algebraMap (ringOfIntegers F) (ringOfIntegers K))).IsRoot σa := by
        have h := haRoot.map (f := (galoisIntegerEquiv F K σ).toRingHom)
        rw [Polynomial.map_map, hcoeff] at h
        exact h
      have hσaNear : (0 : WithTop ℤ) < ord K ((σa : K) - (a0 : K)) := by
        have hlattice := (residueMap_eq_residueMap_iff K σa a0).1 hσaRed
        have hmax : σa - a0 ∈ IsLocalRing.maximalIdeal (ringOfIntegers K) := by
          apply (mem_lattice_one_iff_mem_maximalIdeal K (σa - a0)).1
          exact hlattice
        exact (ord_pos_iff_mem_maximalIdeal K (σa - a0)).2 hmax
      have hσa : σa = a := haUnique σa hσaRoot hσaNear
      apply (IntermediateField.mem_fixingSubgroup_iff E σ).2
      intro x hx
      exact IntermediateField.adjoin_induction (F := F) (s := {(a : K)})
        (p := fun x _ => σ x = x)
        (by
          intro x hx
          simp only [Set.mem_singleton_iff] at hx
          subst x
          change ((σa : ringOfIntegers K) : K) = (a : K)
          rw [hσa])
        (by intro x; simp)
        (by intro x y hx hy hxf hyf; simp [hxf, hyf])
        (by intro x hx hxf; simp [hxf])
        (by intro x y hx hy hxf hyf; simp [hxf, hyf]) hx
  refine ⟨a, P, hPmonic, hPred, hprimitive, haRoot, ?_⟩
  change E = _
  rw [← hfixing]
  exact (IsGalois.fixedField_fixingSubgroup E).symm

omit [Module.Finite F K] in
/-- The polynomial lift bounds the degree of the lifted-generator field by the residue degree. -/
private theorem degree_upper [IsGalois F K] :
    ∀ (a : ringOfIntegers K) (P : (ringOfIntegers F)[X]),
      P.Monic →
      P.map (residueMap F) = minpoly (ResidueField F) (residueMap K a) →
      IntermediateField.adjoin (ResidueField F) {residueMap K a} = ⊤ →
      (P.map (algebraMap (ringOfIntegers F) (ringOfIntegers K))).IsRoot a →
      Module.finrank F (IntermediateField.adjoin F {(a : K)}) ≤
        residueDegree F K := by
  intro a P hPmonic hPred hprimitive haRoot
  let PF : F[X] := P.map (algebraMap (ringOfIntegers F) F)
  have hcoeff :
      (algebraMap (ringOfIntegers K) K).comp
          (algebraMap (ringOfIntegers F) (ringOfIntegers K)) =
        (algebraMap F K).comp (algebraMap (ringOfIntegers F) F) := by
    ext x
    rfl
  have hrootK : (PF.map (algebraMap F K)).IsRoot (a : K) := by
    have h := haRoot.map (f := algebraMap (ringOfIntegers K) K)
    rw [Polynomial.map_map, hcoeff] at h
    rw [show algebraMap (ringOfIntegers K) K a = (a : K) by rfl] at h
    simpa [PF, Polynomial.map_map] using h
  have haeval : Polynomial.aeval (a : K) PF = 0 := by
    simpa [Polynomial.aeval_def] using hrootK
  have hdvd : minpoly F (a : K) ∣ PF := minpoly.dvd F (a : K) haeval
  have hmindeg : (minpoly F (a : K)).natDegree ≤ PF.natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd (hPmonic.map _).ne_zero
  have hPdegree :
      P.natDegree = Module.finrank (ResidueField F) (ResidueField K) := by
    rw [← hPmonic.natDegree_map (residueMap F), hPred]
    exact (Field.primitive_element_iff_minpoly_natDegree_eq
      (ResidueField F) (residueMap K a)).1 hprimitive
  calc
    Module.finrank F (IntermediateField.adjoin F {(a : K)}) =
        (minpoly F (a : K)).natDegree :=
      IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (a : K))
    _ ≤ PF.natDegree := hmindeg
    _ = P.natDegree := hPmonic.natDegree_map _
    _ = Module.finrank (ResidueField F) (ResidueField K) := hPdegree
    _ = residueDegree F K :=
      (residueDegree_eq_finrank_residueField F K).symm

/-- The residue map from the lifted-generator field reaches every element of the ambient residue
field. -/
private theorem intermediate_residue_surjective
    (a : ringOfIntegers K)
    (hprimitive :
      IntermediateField.adjoin (ResidueField F) {residueMap K a} = ⊤) :
    let E : IntermediateField F K := IntermediateField.adjoin F {(a : K)}
    letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E
    letI : TopologicalSpace E := Basic.intermediateFieldTopology E
    letI : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E
    letI : ValuativeExtension F E := Basic.intermediateField_lowerValuativeExtension E
    letI : ValuativeExtension E K := Basic.intermediateField_upperValuativeExtension E
    Function.Surjective (algebraMap (ResidueField E) (ResidueField K)) := by
  dsimp only
  let E : IntermediateField F K := IntermediateField.adjoin F {(a : K)}
  letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E
  letI : TopologicalSpace E := Basic.intermediateFieldTopology E
  letI : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E
  letI : ValuativeExtension F E := Basic.intermediateField_lowerValuativeExtension E
  letI : ValuativeExtension E K := Basic.intermediateField_upperValuativeExtension E
  letI : IsScalarTower
      (ringOfIntegers F) (ringOfIntegers E) (ringOfIntegers K) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap F K (x : F) = algebraMap E K (algebraMap F E (x : F))
      rw [← IsScalarTower.algebraMap_apply F E K])
  letI : IsLocalHom
      (algebraMap (ringOfIntegers F) (ringOfIntegers E)) := inferInstance
  letI : IsLocalHom
      (algebraMap (ringOfIntegers F) (ringOfIntegers K)) := inferInstance
  let ι : ResidueField E →ₐ[ResidueField F] ResidueField K :=
    IsScalarTower.toAlgHom (ResidueField F) (ResidueField E) (ResidueField K)
  let aE : E := ⟨(a : K),
    IntermediateField.subset_adjoin F {(a : K)}
      (Set.mem_singleton (a : K))⟩
  have haEint : aE ∈ ringOfIntegers E :=
    (Basic.mem_intermediateField_canonicalRingOfIntegers_iff E aE).2 a.property
  let aOE : ringOfIntegers E := ⟨aE, haEint⟩
  have hgenMem : residueMap K a ∈ ι.fieldRange := by
    apply (AlgHom.mem_fieldRange).2
    refine ⟨residueMap E aOE, ?_⟩
    dsimp only [ι]
    change algebraMap (ResidueField E) (ResidueField K) (residueMap E aOE) = _
    rw [IsLocalRing.ResidueField.algebraMap_residue]
    rfl
  have hadjoin :
      IntermediateField.adjoin (ResidueField F) {residueMap K a} ≤
        ι.fieldRange := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact hgenMem
  have hrange : ι.fieldRange = ⊤ := by
    apply top_unique
    rw [← hprimitive]
    exact hadjoin
  have hι : Function.Surjective ι := AlgHom.fieldRange_eq_top.mp hrange
  intro x
  obtain ⟨y, hy⟩ := hι x
  exact ⟨y, by simpa [ι] using hy⟩

/-- Exact degree, residue-degree, and ramification-index calculations for the constructed field. -/
private theorem intermediate_unramified_data [IsGalois F K]
    (a : ringOfIntegers K) (P : (ringOfIntegers F)[X])
    (hPmonic : P.Monic)
    (hPred : P.map (residueMap F) =
      minpoly (ResidueField F) (residueMap K a))
    (hprimitive :
      IntermediateField.adjoin (ResidueField F) {residueMap K a} = ⊤)
    (haRoot : (P.map
      (algebraMap (ringOfIntegers F) (ringOfIntegers K))).IsRoot a) :
    let E : IntermediateField F K := IntermediateField.adjoin F {(a : K)}
    Module.finrank F E = residueDegree F K ∧
      letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E
      letI : TopologicalSpace E := Basic.intermediateFieldTopology E
      letI : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E
      letI : ValuativeExtension F E := Basic.intermediateField_lowerValuativeExtension E
      ramificationIndex F E = 1 ∧ residueDegree F E = residueDegree F K := by
  dsimp only
  let E : IntermediateField F K := IntermediateField.adjoin F {(a : K)}
  have hupper : Module.finrank F E ≤ residueDegree F K :=
    degree_upper (F := F) (K := K) a P hPmonic hPred hprimitive haRoot
  letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E
  letI : TopologicalSpace E := Basic.intermediateFieldTopology E
  letI : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E
  letI : ValuativeExtension F E := Basic.intermediateField_lowerValuativeExtension E
  letI : ValuativeExtension E K := Basic.intermediateField_upperValuativeExtension E
  letI : IsScalarTower
      (ringOfIntegers F) (ringOfIntegers E) (ringOfIntegers K) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap F K (x : F) = algebraMap E K (algebraMap F E (x : F))
      rw [← IsScalarTower.algebraMap_apply F E K])
  letI : IsLocalHom
      (algebraMap (ringOfIntegers F) (ringOfIntegers E)) := inferInstance
  letI : IsLocalHom
      (algebraMap (ringOfIntegers F) (ringOfIntegers K)) := inferInstance
  let ι : ResidueField E →ₐ[ResidueField F] ResidueField K :=
    IsScalarTower.toAlgHom (ResidueField F) (ResidueField E) (ResidueField K)
  have hsurj :
      Function.Surjective (algebraMap (ResidueField E) (ResidueField K)) :=
    intermediate_residue_surjective (F := F) (K := K) a hprimitive
  have hιsurj : Function.Surjective ι := by
    intro x
    obtain ⟨y, hy⟩ := hsurj x
    exact ⟨y, by simpa [ι] using hy⟩
  let e : ResidueField E ≃ₐ[ResidueField F] ResidueField K :=
    AlgEquiv.ofBijective ι ⟨ι.injective, hιsurj⟩
  have hresidueFinrank :
      Module.finrank (ResidueField F) (ResidueField E) =
        Module.finrank (ResidueField F) (ResidueField K) :=
    e.toLinearEquiv.finrank_eq
  have hresidue : residueDegree F E = residueDegree F K := by
    rw [residueDegree_eq_finrank_residueField F E,
      residueDegree_eq_finrank_residueField F K]
    exact hresidueFinrank
  have hlower : residueDegree F K ≤ Module.finrank F E := by
    rw [← hresidue, finrank_eq_ramificationIndex_mul_residueDegree F E]
    have hepos := ramificationIndex_pos F E
    exact Nat.le_mul_of_pos_left _ hepos
  have hdegree : Module.finrank F E = residueDegree F K :=
    le_antisymm hupper hlower
  have hramification : ramificationIndex F E = 1 := by
    have hformula := finrank_eq_ramificationIndex_mul_residueDegree F E
    rw [hdegree, hresidue] at hformula
    have hfpos := residueDegree_pos F K
    exact Nat.eq_of_mul_eq_mul_right hfpos (by simpa using hformula.symm)
  exact ⟨hdegree, hramification, hresidue⟩

/-- The maximal unramified subfield from the first paragraph of Paper Lemma D.2.

The witness `a` is an actual integer of `K`. Its reduction generates `k_K/k_F`; `P` is a
monic lift of that generator's minimal polynomial and actually vanishes at `a`. The actual
intermediate field `F(a)` is equal to the fixed field of the kernel of the residue action. Its
extension over `F` is Galois, its degree and residue degree are the full residue degree of
`K/F`, and its ramification index is one. -/
theorem maximalUnramified_fixedField [IsGalois F K] :
    ∃ (a : ringOfIntegers K) (P : (ringOfIntegers F)[X]),
      P.Monic ∧
      P.map (residueMap F) = minpoly (ResidueField F) (residueMap K a) ∧
      IntermediateField.adjoin (ResidueField F) {residueMap K a} = ⊤ ∧
      (P.map (algebraMap (ringOfIntegers F) (ringOfIntegers K))).IsRoot a ∧
      let E : IntermediateField F K := IntermediateField.adjoin F {(a : K)}
      E = IntermediateField.fixedField (inertiaSubgroup (F := F) (K := K)) ∧
        IsGalois F E ∧ Module.finrank F E = residueDegree F K ∧
        letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E
        letI : TopologicalSpace E := Basic.intermediateFieldTopology E
        letI : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E
        letI : ValuativeExtension F E := Basic.intermediateField_lowerValuativeExtension E
        ramificationIndex F E = 1 ∧ residueDegree F E = residueDegree F K := by
  obtain ⟨a, P, hPmonic, hPred, hprimitive, haRoot, hfixed⟩ :=
    maximalUnramified_fixedField_aux (F := F) (K := K)
  have hGalois :
      let E : IntermediateField F K := IntermediateField.adjoin F {(a : K)}
      IsGalois F E := by
    dsimp only
    rw [hfixed]
    exact IsGalois.of_fixedField_normal_subgroup
      (inertiaSubgroup (F := F) (K := K))
  have hdata := intermediate_unramified_data (F := F) (K := K)
    a P hPmonic hPred hprimitive haRoot
  exact ⟨a, P, hPmonic, hPred, hprimitive, haRoot, hfixed, hGalois, hdata⟩

end

end LanglandsSecondMainLemma.Ramification
