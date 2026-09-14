import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.EqualChar.NormCharacter

/-!
# Products of Artin--Schreier norm characters

The characteristic-two argument of `D:quadratic-norms`, lines 8994--9005
of the corrected manuscript. We first make the residue formula independent
of the constructed Laurent coordinates, then use its additivity and
nontriviality on every nonzero Artin--Schreier class.
-/

open scoped LaurentSeries PowerSeries
open LanglandsFirstMainLemma
open LanglandsSecondMainLemma.Residues LanglandsSecondMainLemma.EqualChar

namespace LanglandsSecondMainLemma.Characters
noncomputable section

open private laurentRingHom_ext_of_order existsEqualCharacteristicPresentation from
  LanglandsSecondMainLemma.Residues.EqualCharacteristicPresentation
open private parameter_order formalSubstitution_orderTop eq_parameter_powerSeriesPart from
  LanglandsSecondMainLemma.Residues.TraceCompatibility
open private laurentDerivative_substitution from LanglandsSecondMainLemma.Residues.LogNorm
open private residueField_charTwo actualResidueSymbol_ne_one
  not_artinSchreier_of_generator from
  LanglandsSecondMainLemma.EqualChar.NormCharacter

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Changing the coefficient-compatible uniformizer preserves `Res(f du/u)`.
The order-one substitution and its chain rule are the already proved formal
residue results, applied to the coordinate transition of the actual field. -/
theorem residue_logarithmicDerivative_coordinates
    (P Q : EqualCharacteristicPresentation F) (f u : F) :
    residue (P.laurentEquiv.symm f * logarithmicDerivative (P.laurentEquiv.symm u)) =
      residue (Q.laurentEquiv.symm f * logarithmicDerivative (Q.laurentEquiv.symm u)) := by
  let φ := Q.laurentEquiv.symm.toRingHom.comp P.laurentEquiv.toRingHom
  have hC (a : ResidueField F) : φ (HahnSeries.C a) = HahnSeries.C a := by
    apply Q.laurentEquiv.injective
    change Q.laurentEquiv (Q.laurentEquiv.symm (P.laurentEquiv (HahnSeries.C a))) = _
    rw [RingEquiv.apply_symm_apply, P.laurentEquiv_C, Q.laurentEquiv_C,
      P.coefficient_eq_teichmuller, Q.coefficient_eq_teichmuller]
  have hord (x : (ResidueField F)⸨X⸩) : (φ x).orderTop = x.orderTop := by
    rw [← Q.laurentEquiv_order]
    change ord F (Q.laurentEquiv (Q.laurentEquiv.symm (P.laurentEquiv x))) = _
    rw [RingEquiv.apply_symm_apply, P.laurentEquiv_order]
  let t := φ (HahnSeries.single 1 1)
  have ht : t.orderTop = 1 := by
    rw [hord, HahnSeries.orderTop_single one_ne_zero]
    rfl
  have ht0 : t ≠ 0 := by intro h; simp [h] at ht
  have hto : t.order = 1 := by
    have h := HahnSeries.order_eq_orderTop_of_ne_zero ht0
    rw [ht] at h
    exact WithTop.coe_eq_coe.mp h
  let v := t.powerSeriesPart
  have hv : IsUnit (PowerSeries.constantCoeff v) := by
    rw [isUnit_iff_ne_zero, ← PowerSeries.coeff_zero_eq_constantCoeff]
    change t.powerSeriesPart.coeff 0 ≠ 0
    rw [LaurentSeries.powerSeriesPart_coeff]
    simpa using HahnSeries.leadingCoeff_ne_zero.mpr ht0
  let s := FreeBasis.parameter 1 v
  have hs : (s : (ResidueField F)⸨X⸩) = t :=
    eq_parameter_powerSeriesPart t 1 hto
  have hso : s.order = 1 := parameter_order 1 v hv
  let ψ := formalSubstitution s 1 (by omega) hso
  have hψC (a : ResidueField F) : ψ (HahnSeries.C a) = HahnSeries.C a := by
    rw [← PowerSeries.coe_C]
    change formalSubstitution s 1 _ _ _ = _
    rw [formalSubstitution_coe, PowerSeries.subst_C]
    rfl
  have hψX : ψ (HahnSeries.single 1 1) = t := by
    rw [← PowerSeries.coe_X]
    change formalSubstitution s 1 _ _ _ = _
    rw [formalSubstitution_coe, PowerSeries.subst_X (FreeBasis.parameter_hasSubst 1 v)]
    exact hs
  have heq : φ = ψ := by
    apply laurentRingHom_ext_of_order 1 (by omega)
    · intro a; rw [hC, hψC]
    · exact hψX.symm
    · intro x; simpa using hord x
    · exact formalSubstitution_orderTop 1 v hv
  have hφ : IsLaurentSubstitution 1 (RingHom.id _) (s : (ResidueField F)⸨X⸩) φ :=
    ⟨hC, hs.symm, fun x ↦ by simpa using hord x⟩
  have hd (x : (ResidueField F)⸨X⸩) :=
    laurentDerivative_substitution 1 (by omega) (RingHom.id _) s
      (FreeBasis.parameter_hasSubst 1 v) φ hφ x
  have hlog (x : (ResidueField F)⸨X⸩) :
      logarithmicDerivative (φ x) =
        φ (logarithmicDerivative x) * (PowerSeries.derivative _ s : (ResidueField F)⸨X⸩) := by
    simp only [logarithmicDerivative, hd, map_mul, map_inv₀, mul_assoc]
  have hf : φ (P.laurentEquiv.symm f) = Q.laurentEquiv.symm f := by simp [φ]
  have hu : φ (P.laurentEquiv.symm u) = Q.laurentEquiv.symm u := by simp [φ]
  rw [← hf, ← hu, hlog, ← mul_assoc, ← map_mul, heq]
  exact (change_uniformizer s hso _).symm

variable [CharP F 2]
local instance : CharP (ResidueField F) 2 := residueField_charTwo F
local instance : Algebra (ZMod 2) (ResidueField F) := ZMod.algebra _ _

/-- The exact residue sign is independent of the choice of Laurent coordinates. -/
theorem actualResidueSymbol_coordinates (P Q : EqualCharacteristicPresentation F) (f : F) :
    actualResidueSymbol F P f = actualResidueSymbol F Q f := by
  ext u
  simp only [actualResidueSymbol_apply, residueExponent]
  rw [residue_logarithmicDerivative_coordinates F P Q]

/-- Continuity is proved on a whole open unit layer, for every parameter,
including the zero and unramified Artin--Schreier classes. -/
theorem actualResidueSymbol_continuous (P : EqualCharacteristicPresentation F) (f : F) :
    Continuous (actualResidueSymbol F P f) := by
  let g := P.laurentEquiv.symm f
  let t := g.order.natAbs
  have hg : ((-(t : ℤ) : ℤ) : WithTop ℤ) ≤ g.orderTop := by
    by_cases h : g = 0
    · simp [h]
    · rw [← HahnSeries.order_eq_orderTop_of_ne_zero h]
      exact WithTop.coe_le_coe.mpr (by
        have := Int.le_natAbs (a := -g.order)
        simp only [Int.natAbs_neg] at this
        dsimp [t]
        omega)
  have hone (u : Fˣ) (hu : u ∈ unitFiltration F (t + 1)) :
      actualResidueSymbol F P f u = 1 := by
    apply Units.ext
    rw [actualResidueSymbol_apply]
    have hdeep : ((t + 1 : ℕ) : WithTop ℤ) ≤
        (P.laurentEquiv.symm (u : F) - 1).orderTop := by
      have h := (mem_unitFiltration_succ_iff_ord F t u).mp hu
      rw [← P.laurentEquiv_order]
      simp only [map_sub, map_one, RingEquiv.apply_symm_apply]
      exact_mod_cast h
    rw [residueExponent_deepUnit g _ t hg hdeep]
    rfl
  apply continuous_of_continuousAt_one (actualResidueSymbol F P f)
  have hevent : ∀ᶠ u in nhds (1 : Fˣ), actualResidueSymbol F P f u = 1 :=
    Filter.Eventually.mono
      ((unitFiltration_isOpen F (t + 1)).mem_nhds (Subgroup.one_mem _)) hone
  exact continuousAt_const.congr_of_eventuallyEq hevent

/-- A single constructed presentation of the base field, used for every class. -/
def artinSchreierPresentation : EqualCharacteristicPresentation F :=
  existsEqualCharacteristicPresentation F (equalCharacteristicTwo F)

/-- The continuous quadratic character attached to an Artin--Schreier parameter.
Its identification with the actual norm character is proved below. -/
def artinSchreierNormCharacter (f : F) : ContinuousQuasiChar F :=
  ⟨actualResidueSymbol F (artinSchreierPresentation F) f,
    actualResidueSymbol_continuous F (artinSchreierPresentation F) f⟩

/-- Additivity of the residue exponent gives multiplication of characters. -/
theorem artinSchreierNormCharacter_add (f g : F) :
    artinSchreierNormCharacter F (f + g) =
      artinSchreierNormCharacter F f * artinSchreierNormCharacter F g := by
  ext u
  change binaryAddChar (residueExponent
      ((artinSchreierPresentation F).laurentEquiv.symm (f + g))
      ((artinSchreierPresentation F).laurentEquiv.symm (u : F))) =
    binaryAddChar (residueExponent ((artinSchreierPresentation F).laurentEquiv.symm f)
      ((artinSchreierPresentation F).laurentEquiv.symm (u : F))) *
    binaryAddChar (residueExponent ((artinSchreierPresentation F).laurentEquiv.symm g)
      ((artinSchreierPresentation F).laurentEquiv.symm (u : F)))
  rw [map_add, residueExponent_add, AddChar.map_add_eq_mul]

/-- Every constructed character is quadratic, including the trivial class. -/
theorem artinSchreierNormCharacter_sq (f : F) :
    artinSchreierNormCharacter F f ^ 2 = 1 := by
  rw [pow_two, ← artinSchreierNormCharacter_add, CharTwo.add_self_eq_zero]
  ext u
  change (-1 : ℂ) ^ (residueExponent
    ((artinSchreierPresentation F).laurentEquiv.symm 0)
    ((artinSchreierPresentation F).laurentEquiv.symm (u : F))).val = 1
  simp [residueExponent, residue]

/-- The kernel consists exactly of the Artin--Schreier coboundaries.
Nontriviality uses the full accepted residue theorem, also at constant classes. -/
theorem artinSchreierNormCharacter_eq_one_iff (f : F) :
    artinSchreierNormCharacter F f = 1 ↔ ∃ w : F, w ^ 2 + w = f := by
  constructor
  · intro h
    by_contra hf
    apply actualResidueSymbol_ne_one F (artinSchreierPresentation F) f hf
    exact congrArg ContinuousMonoidHom.toMonoidHom h
  · rintro ⟨w, rfl⟩
    ext u
    change (-1 : ℂ) ^ (residueExponent
      ((artinSchreierPresentation F).laurentEquiv.symm (w ^ 2 + w))
      ((artinSchreierPresentation F).laurentEquiv.symm (u : F))).val = 1
    rw [map_add, map_pow, residueExponent_artinSchreier _ _
      ((map_ne_zero _).mpr u.ne_zero)]
    rfl

/-- Identification with any nontrivial continuous character of the actual
quadratic norm quotient. This uses only the accepted single-extension theorem;
there is no crossed-norm or SML input. -/
theorem artinSchreierNormCharacter_eq_normCharacter
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [ValuativeExtension F E]
    [Module.Finite F E] [IsGalois F E]
    (hdegree : Module.finrank F E = 2) (f : F) (z : E)
    (hz : z ^ 2 + z = algebraMap F E f)
    (hgen : z ∉ Set.range (algebraMap F E))
    (ω : NormCharacter F E) (hω : ω ≠ 1) :
    ω.1 = artinSchreierNormCharacter F f := by
  obtain ⟨ν, _, huniq, hformula, _⟩ := normCharacter F E hdegree f z hz hgen
  rw [huniq ω hω]
  let P := Classical.choice (exists_equalCharacteristicExtensionPresentation
    F E (equalCharacteristicTwo F))
  ext u
  calc
    (ν.1 u : ℂ) = (actualResidueSymbol F P.base f u : ℂ) := hformula u
    _ = (artinSchreierNormCharacter F f u : ℂ) :=
      congrArg (fun a : ℂˣ ↦ (a : ℂ))
        (DFunLike.congr_fun (actualResidueSymbol_coordinates F P.base
          (artinSchreierPresentation F) f) u)

/-- The actual Artin--Schreier coboundary subgroup, the range of `w ↦ w²+w`. -/
def artinSchreierCoboundaries : AddSubgroup F :=
  ((frobenius F 2).toAddMonoidHom + AddMonoidHom.id F).range

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp] theorem mem_artinSchreierCoboundaries (f : F) :
    f ∈ artinSchreierCoboundaries F ↔ ∃ w : F, w ^ 2 + w = f := Iff.rfl

local instance : AddCommGroup (Additive (ContinuousQuasiChar F)) := inferInstance

/-- Addition of parameters becomes multiplication of continuous characters. -/
def artinSchreierCharacterHom : F →+ Additive (ContinuousQuasiChar F) where
  toFun f := Additive.ofMul (artinSchreierNormCharacter F f)
  map_zero' := by
    change artinSchreierNormCharacter F 0 = 1
    exact (artinSchreierNormCharacter_eq_one_iff F 0).2 ⟨0, by simp⟩
  map_add' f g := artinSchreierNormCharacter_add F f g

/-- Artin--Schreier classes of the actual local field. -/
abbrev ArtinSchreierClass := F ⧸ artinSchreierCoboundaries F

private theorem artinSchreierCoboundaries_le_ker :
    artinSchreierCoboundaries F ≤ (artinSchreierCharacterHom F).ker := by
  intro f hf
  change artinSchreierNormCharacter F f = 1
  exact (artinSchreierNormCharacter_eq_one_iff F f).2 hf

/-- The norm-character map on Artin--Schreier classes, written additively in
its target so that its group law is multiplication of continuous characters. -/
def artinSchreierClassToQuadraticCharacter :
    ArtinSchreierClass F →+ Additive (ContinuousQuasiChar F) := by
  apply QuotientAddGroup.lift (artinSchreierCoboundaries F) (artinSchreierCharacterHom F)
  exact artinSchreierCoboundaries_le_ker F

/-- The characteristic-two argument of `D:quadratic-norms`: Artin--Schreier
classes embed as continuous quadratic norm characters. The preceding
identification theorem gives the norm character of every actual quadratic
extension with the stated Artin--Schreier generator. -/
theorem quadraticNormCharacters_char_two :
    Function.Injective (artinSchreierClassToQuadraticCharacter F) := by
  apply (QuotientAddGroup.injective_lift_iff (artinSchreierCoboundaries F)
    (artinSchreierCharacterHom F) (artinSchreierCoboundaries_le_ker F)).2
  ext f
  change (∃ w : F, w ^ 2 + w = f) ↔ artinSchreierNormCharacter F f = 1
  exact (artinSchreierNormCharacter_eq_one_iff F f).symm

/-- The three nonzero classes `f`, `g`, and `f+g` give precisely the product
identity and pairwise separation used in the biquadratic argument. -/
theorem artinSchreierNormCharacter_product_distinct (f g : F)
    (hf : ¬ ∃ w : F, w ^ 2 + w = f)
    (hg : ¬ ∃ w : F, w ^ 2 + w = g)
    (hfg : ¬ ∃ w : F, w ^ 2 + w = f + g) :
    artinSchreierNormCharacter F (f + g) =
        artinSchreierNormCharacter F f * artinSchreierNormCharacter F g ∧
      artinSchreierNormCharacter F f ≠ artinSchreierNormCharacter F g ∧
      artinSchreierNormCharacter F f ≠ artinSchreierNormCharacter F (f + g) ∧
      artinSchreierNormCharacter F g ≠ artinSchreierNormCharacter F (f + g) := by
  have hf' := (artinSchreierNormCharacter_eq_one_iff F f).not.mpr hf
  have hg' := (artinSchreierNormCharacter_eq_one_iff F g).not.mpr hg
  have hfg' := (artinSchreierNormCharacter_eq_one_iff F (f + g)).not.mpr hfg
  have hzero : artinSchreierNormCharacter F 0 = 1 :=
    (artinSchreierNormCharacter_eq_one_iff F 0).2 ⟨0, by simp⟩
  refine ⟨artinSchreierNormCharacter_add F f g, ?_, ?_, ?_⟩
  · intro heq
    apply hfg'
    rw [artinSchreierNormCharacter_add, ← heq, ← artinSchreierNormCharacter_add,
      CharTwo.add_self_eq_zero, hzero]
  · intro heq
    apply hg'
    apply ContinuousMonoidHom.ext
    intro u
    exact mul_eq_left.mp (DFunLike.congr_fun
      ((artinSchreierNormCharacter_add F f g).symm.trans heq.symm) u)
  · intro heq
    apply hf'
    apply ContinuousMonoidHom.ext
    intro u
    exact mul_eq_right.mp (DFunLike.congr_fun
      ((artinSchreierNormCharacter_add F f g).symm.trans heq.symm) u)

/-- The three actual lower norm characters, in the Artin--Schreier labeling
`a₂ = a₀ + a₁`. The characters are constructed from the local extensions;
none is an assumed residue model. Biquadratic field classification supplies
this labeling to the final characteristic-independent assembly. -/
theorem quadraticNormCharacters_char_two_of_generators
    (E : Fin 3 → Type) [∀ i, Field (E i)] [∀ i, ValuativeRel (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, IsNonarchimedeanLocalField (E i)]
    [∀ i, Algebra F (E i)] [∀ i, ValuativeExtension F (E i)]
    [∀ i, Module.Finite F (E i)] [∀ i, IsGalois F (E i)]
    (a : Fin 3 → F) (z : (i : Fin 3) → E i)
    (hdegree : ∀ i, Module.finrank F (E i) = 2)
    (hz : ∀ i, z i ^ 2 + z i = algebraMap F (E i) (a i))
    (hgen : ∀ i, z i ∉ Set.range (algebraMap F (E i)))
    (ha : a 2 = a 0 + a 1) :
    ∃ ω : (i : Fin 3) → NormCharacter F (E i),
      (∀ i, ω i ≠ 1) ∧
      (ω 2).1 = (ω 0).1 * (ω 1).1 ∧
      (ω 0).1 ≠ (ω 1).1 ∧ (ω 0).1 ≠ (ω 2).1 ∧ (ω 1).1 ≠ (ω 2).1 := by
  have hex (i : Fin 3) : ∃ ω : NormCharacter F (E i), ω ≠ 1 := by
    obtain ⟨ω, hω, _⟩ := normCharacter F (E i) (hdegree i) (a i) (z i) (hz i) (hgen i)
    exact ⟨ω, hω⟩
  choose ω hω using hex
  have heq (i : Fin 3) : (ω i).1 = artinSchreierNormCharacter F (a i) :=
    artinSchreierNormCharacter_eq_normCharacter F (E i) (hdegree i)
      (a i) (z i) (hz i) (hgen i) (ω i) (hω i)
  have hclass (i : Fin 3) : ¬ ∃ w : F, w ^ 2 + w = a i :=
    not_artinSchreier_of_generator F (E i) (a i) (z i) (hz i) (hgen i)
  refine ⟨ω, hω, ?_⟩
  rw [heq 0, heq 1, heq 2, ha]
  exact artinSchreierNormCharacter_product_distinct F (a 0) (a 1)
    (hclass 0) (hclass 1) (by rw [← ha]; exact hclass 2)

end
end LanglandsSecondMainLemma.Characters
