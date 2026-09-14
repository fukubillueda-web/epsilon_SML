import LanglandsFirstMainLemma.Delta.FirstMainStatement
import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsFirstMainLemma.Main
import LanglandsSecondMainLemma.Dyadic.Equal.HighCoefficient
import LanglandsSecondMainLemma.Characters.Conjugacy

/-!
# Exact high comparison in characteristic two

Paper Theorem 11.13 (`D:EQ:highcomparison`). The common correction is retained.
All local constants are FML's canonical constants, and all lower norm characters
occur in the induction expression.
-/

namespace LanglandsSecondMainLemma.Dyadic.Equal
noncomputable section
open LanglandsFirstMainLemma
open scoped BigOperators
open private originLine_degrees origin_residueDegrees origin_group_equiv from
  LanglandsSecondMainLemma.Dyadic.Equal.Origin
open private primeNormCharacter_card from LanglandsSecondMainLemma.Characters.Conjugacy
open private lowerCyclic from LanglandsSecondMainLemma.Dyadic.Equal.Twist
open private field_injective from LanglandsSecondMainLemma.Dyadic.Equal.Models
open private depth_ledger from LanglandsSecondMainLemma.Dyadic.Equal.Compatibility

/-- Apply the released stable-twist theorem with numerator one and the actual
admissible denominator. The stationary identity is required on the whole ideal. -/
private theorem stable_at_denominator
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [CharP E 2]
    (ν θ : LocalQuasiCharData E) (ψ : LocalAddCharData E)
    (hq : 1 < θ.conductor) (hν : ν.conductor ≤ θ.conductor / 2)
    (γ : AdmissibleGamma E θ ψ)
    (hlin : ∀ u : Eˣ, 1 - (u : E) ∈ lattice E (((θ.conductor + 1) / 2 : ℕ) : ℤ) →
      θ.character u = ψ.character ((1 - (u : E)) / (γ : Eˣ))) :
    localConstant E (ν.character * θ.character) ψ.character =
      (ν.character γ : ℂ) * localConstant E θ.character ψ.character := by
  let q := θ.conductor
  have he : q % 2 ≤ 1 := by omega
  have hq' : θ.conductor = 2 * (q / 2) + q % 2 := by dsimp [q]; omega
  let hr := stableTwist_stationaryDepth E θ (q / 2) (q % 2) he hq' hq
  let c : lattice E ((θ.conductor : ℤ) - (θ.conductor : ℤ)) := ⟨1, by simp⟩
  have hc : latticeQuotientMk E
      (sub_le_sub_left hr.int_le_conductor (θ.conductor : ℤ)) c =
      stationaryNumeratorClass E θ ψ (θ.conductor : ℤ) hr γ γ.property := by
    apply (latticeQuotientMk_eq_stationaryNumeratorClass_iff E θ ψ
      (θ.conductor : ℤ) hr γ γ.property c).2
    intro z
    have hz : 1 - ((positiveUnitOfLattice E hr.pos z : Eˣ) : E) = (z : E) := by
      rw [coe_positiveUnitOfLattice, CharTwo.sub_eq_add, ← add_assoc,
        CharTwo.add_self_eq_zero, zero_add]
    have hdepth : (((θ.conductor + 1) / 2 : ℕ) : ℤ) = ((q / 2 + q % 2 : ℕ) : ℤ) := by
      dsimp [q]; omega
    have h := hlin (positiveUnitOfLattice E hr.pos z) (by rw [hz, hdepth]; exact z.property)
    simpa only [hz, c, one_mul] using h
  have hfactor : stableStationaryRepresentativeUnit E θ ψ hr γ c hc = 1 := by
    apply Units.ext; rfl
  have hs := stableTwist E ν θ ψ (q / 2) (q % 2) he hq' hq hν γ c hc
  dsimp only at hs
  rw [← localConstant_isDeltaFinite E, ← localConstant_isDeltaFinite E,
    hfactor, div_one] at hs
  exact hs

/-- FML additive scaling, expressed at the canonical local constant. -/
private theorem localConstant_scale (E : Type) [Field E] [ValuativeRel E]
    [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    (χ : ContinuousQuasiChar E) (ψ : LocalAddCharData E) (u : Eˣ) :
    localConstant E χ (scaleAddCharData E ψ u).character =
      (χ u : ℂ) * localConstant E χ ψ.character := by
  let θ := canonicalLocalQuasiCharData E χ
  obtain ⟨γ⟩ := AdmissibleGamma.exists_admissible (F := E) (χ := θ) (ψ := ψ)
  have hs := delta_additive_scale E θ ψ u γ (scaleAdmissibleGamma E u γ)
  rw [← localConstant_isDeltaFinite E, ← localConstant_isDeltaFinite E] at hs
  exact hs

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  [CharP F 2] [CharP K 2] [IsKleinFour Gal(K/F)]

local instance highComparisonValuativeRel (L : IntermediateField F K) : ValuativeRel L :=
  Basic.intermediateFieldValuativeRel L
local instance highComparisonTopology (L : IntermediateField F K) : TopologicalSpace L :=
  Basic.intermediateFieldTopology L
local instance highComparisonLocalField (L : IntermediateField F K) : IsNonarchimedeanLocalField L :=
  Basic.intermediateField_localField L
local instance highComparisonLowerExtension (L : IntermediateField F K) : ValuativeExtension F L :=
  Basic.intermediateField_lowerValuativeExtension L
local instance highComparisonUpperExtension (L : IntermediateField F K) : ValuativeExtension L K :=
  Basic.intermediateField_upperValuativeExtension L
local instance highComparisonIsGalois (L : IntermediateField F K) : IsGalois F L := by
  letI : IsMulCommutative Gal(K/F) := IsKleinFour.isMulCommutative
  letI : L.fixingSubgroup.Normal := inferInstance
  have h := IsGalois.of_fixedField_normal_subgroup L.fixingSubgroup
  rwa [IsGalois.fixedField_fixingSubgroup L] at h


namespace SimultaneousASGenerators
variable {P : Residues.EqualCharacteristicPresentation F}
  (G : SimultaneousASGenerators F K P)

omit [IsGalois F K] [CharP F 2] [CharP K 2] in
/-- The upstairs and downstairs stable bounds at exactly `h₀`. -/
theorem high_stable_bounds {h : ℤ} (hh : G.highThreshold ≤ h) (i : Fin 3) :
    1 < 2 * G.highDepth h i ∧
    (G.minimalConductor i : ℤ) ≤ G.highDepth h i ∧
    2 * ((G.t i : ℤ) + 1) ≤ (G.t 1 : ℤ) + 1 + h := by
  have hs := G.smallest
  have ht := G.third_break
  have hp := (G.edge 0).2.2.2.1
  obtain ⟨a, ha⟩ := (G.edge 0).2.2.2.2.1
  obtain ⟨b, hb⟩ := (G.edge 1).2.2.2.2.1
  dsimp only [highThreshold, lowerDepth] at hh
  fin_cases i <;> simp only [highDepth, lowerDepth, minimalConductor] <;> norm_num
  all_goals try rw [show G.t ⟨2, by decide⟩ = G.t 1 from ht]
  all_goals omega

/-- The complete lower induction expression. -/
def highInductionFactor (i : Fin 3) (θ : ContinuousQuasiChar (G.field i))
    (ψ : ContinuousAddChar F) : ℂ := by
  letI := lowerCyclic G i
  letI := primeCyclicNormCharacter_finite F (G.field i)
  letI := Fintype.ofFinite (NormCharacter F (G.field i))
  exact localConstant (G.field i) θ (tracePullbackAddChar F (G.field i) ψ) *
    ∏ μ : NormCharacter F (G.field i), localConstant F μ.1 ψ

/-- The restriction corrected by the complete lower norm-character product. -/
def highDeterminant (i : Fin 3) (χ : ContinuousQuasiChar (G.field i)) :
    ContinuousQuasiChar F :=
  Characters.restrictQuasiChar F (G.field i) χ *
    Characters.intermediateNormCharacterProduct Nat.prime_two (origin_group_equiv F K)
      (G.field i) (originLine_degrees F K (G.g i) (G.nontrivial i)).1

/-- Exact comparison on one edge, before identifying the common determinant. -/
private theorem high_edge (hres : residueDegree F K = 1)
    (lambda : ContinuousQuasiChar F)
    (χ : (i : Fin 3) → ContinuousQuasiChar (G.field i))
    (hcore : ∀ i u, u ∈ unitFiltration (G.field i) (G.stationaryDepth i) →
      χ i u = G.modelValue i u)
    {h : ℤ} (hh : G.highThreshold ≤ h)
    (hn : (multiplicativeConductorExponent F lambda : ℤ) = (G.t 1 : ℤ) + 1 + h)
    (a : Fˣ) (ha : ord F (a : F) = ((-h : ℤ) : WithTop ℤ))
    (hbase : ∀ u : Fˣ,
      1 - (u : F) ∈ lattice F (((G.t 1 : ℤ) + 1 + h + 1) / 2) →
        lambda u = originAddChar F P ((G.t 1 : ℤ) + 1) ((a : F) * (1 - (u : F))))
    (H : HighCoefficientData G h a lambda χ) (i : Fin 3) :
    G.highInductionFactor i (χ i * normQuasiChar F (G.field i) lambda)
        (originAddChar F P ((G.t 1 : ℤ) + 1)) =
      (G.highDeterminant i (χ i) a⁻¹ : ℂ) *
        (originAddChar F P ((G.t 1 : ℤ) + 1) (Algebra.norm F G.Y / (a : F)) : ℂ) *
        localConstant F lambda (originAddChar F P ((G.t 1 : ℤ) + 1)) ^ 2 := by
  let L := G.field i
  let Ψ := originAddChar F P ((G.t 1 : ℤ) + 1)
  letI := lowerCyclic G i
  letI := primeCyclicNormCharacter_finite F L
  letI := Fintype.ofFinite (NormCharacter F L)
  have hb := G.high_stable_bounds hh i
  let ν : LocalQuasiCharData L :=
    ⟨χ i, G.minimalConductor i, G.conductor_of_modelChart hres i (χ i) (hcore i)⟩
  let θ := canonicalLocalQuasiCharData L (normQuasiChar F L lambda)
  let ψ : LocalAddCharData L :=
    ⟨tracePullbackAddChar F L Ψ, -G.additiveModulus i, G.modelAddChar_conductor hres i⟩
  have hq : (θ.conductor : ℤ) = 2 * G.highDepth h i := H.pullback_conductor i
  let γ : AdmissibleGamma L θ ψ := ⟨(H.coefficient i)⁻¹, by
    rw [Units.val_inv_eq_inv_val, ord_inv, H.coefficient_order,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg]
    congr 1
    change -(-2 * h) = (θ.conductor : ℤ) - G.additiveModulus i
    rw [hq]
    dsimp [highDepth, additiveModulus, lowerDepth]
    obtain ⟨r, hr⟩ := (G.edge i).2.2.2.2.1
    omega⟩
  have hu := stable_at_denominator L ν θ ψ (by omega) (by dsimp [ν]; omega) γ (by
    intro u hu
    have hd : (((θ.conductor + 1) / 2 : ℕ) : ℤ) = G.highDepth h i := by omega
    have he := H.stationary i u (by rwa [← hd])
    simpa only [θ, canonicalLocalQuasiCharData_character, L, Ψ, ψ, γ, Units.val_inv_eq_inv_val, div_inv_eq_mul, mul_comm] using he)
  have hcoreval := H.core_value i 1
  simp only [map_one, one_mul] at hcoreval
  change localConstant L (χ i * normQuasiChar F L lambda) (tracePullbackAddChar F L Ψ) =
    (χ i (H.coefficient i)⁻¹ : ℂ) *
      localConstant L (normQuasiChar F L lambda) (tracePullbackAddChar F L Ψ) at hu
  rw [hcoreval, Units.val_mul] at hu
  let θF := canonicalLocalQuasiCharData F lambda
  let ψF : LocalAddCharData F :=
    ⟨Ψ, -((G.t 1 : ℤ) + 1), originAddChar_conductor F P ((G.t 1 : ℤ) + 1)⟩
  let γF : AdmissibleGamma F θF ψF := ⟨a⁻¹, by
    rw [Units.val_inv_eq_inv_val, ord_inv, ha,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg]
    congr 1
    change -(-h) = (multiplicativeConductorExponent F lambda : ℤ) + -((G.t 1 : ℤ) + 1)
    omega⟩
  have hlower (μ : NormCharacter F L) :
      localConstant F (μ.1 * lambda) Ψ = (μ.1 a⁻¹ : ℂ) * localConstant F lambda Ψ := by
    let μF := canonicalLocalQuasiCharData F μ.1
    have hm : μF.conductor ≤ G.t i + 1 := by
      obtain ⟨π, hπ, hgen⟩ := monogenicUniformizer F L
        (origin_residueDegrees F K hres L).1
      exact μF.isConductor.minimal _
        (ramifiedNormCharacter_trivialOn_break_succ F L
          (G.edge i).2.2.2.2.2.2.2.1 (origin_residueDegrees F K hres L).1 π hπ hgen μ)
    apply stable_at_denominator F μF θF ψF (by dsimp [θF, canonicalLocalQuasiCharData]; omega)
      (by dsimp [θF, canonicalLocalQuasiCharData]; omega) γF
    intro u hu
    have hd : (((θF.conductor + 1) / 2 : ℕ) : ℤ) =
        ((G.t 1 : ℤ) + 1 + h + 1) / 2 := by dsimp [θF, canonicalLocalQuasiCharData]; omega
    have he := hbase u (by rwa [← hd])
    simpa only [θF, canonicalLocalQuasiCharData_character, Ψ, ψF, γF, Units.val_inv_eq_inv_val, div_inv_eq_mul, mul_comm] using he
  have hfml := firstMainLemma F L
    (PrimeCyclicExtension.toCyclicPrimeExtension (F := F) (K := L)) lambda Ψ
    ψF.isConductor.character_ne_one
  change localConstant L (normQuasiChar F L lambda) (tracePullbackAddChar F L Ψ) *
      (∏ μ : NormCharacter F L, localConstant F μ.1 Ψ) =
      ∏ μ : NormCharacter F L, localConstant F (μ.1 * lambda) Ψ at hfml
  simp_rw [hlower] at hfml
  rw [Finset.prod_mul_distrib] at hfml
  have hcard : Fintype.card (NormCharacter F L) = 2 := by
    rw [← Nat.card_eq_fintype_card, primeNormCharacter_card,
      (originLine_degrees F K (G.g i) (G.nontrivial i)).1]
  simp only [Finset.prod_const, Finset.card_univ, hcard] at hfml
  change localConstant L (χ i * normQuasiChar F L lambda) (tracePullbackAddChar F L Ψ) *
    (∏ μ : NormCharacter F L, localConstant F μ.1 Ψ) = _
  rw [hu, mul_assoc, hfml]
  have hprod : (∏ μ : NormCharacter F L, (μ.1 a⁻¹ : ℂ)) =
      (Characters.intermediateNormCharacterProduct Nat.prime_two (origin_group_equiv F K)
        (G.field i) (originLine_degrees F K (G.g i) (G.nontrivial i)).1 a⁻¹ : ℂ) := by
    change _ = (Characters.normCharacterProduct F L a⁻¹ : ℂ)
    rw [Characters.normCharacterProduct_apply]
    simp [normCharacterFinset]
  rw [hprod]
  change _ = ((χ i (Units.map (algebraMap F L).toMonoidHom a⁻¹) *
    Characters.intermediateNormCharacterProduct Nat.prime_two (origin_group_equiv F K)
      (G.field i) (originLine_degrees F K (G.g i) (G.nontrivial i)).1 a⁻¹ : ℂˣ) : ℂ) * _ * _
  push_cast
  ring

omit [CharP F 2] [CharP K 2] in
/-- Additive scaling of the full induction expression, retaining its determinant. -/
private theorem high_factor_scale (i : Fin 3)
    (χ : ContinuousQuasiChar (G.field i)) (lambda : ContinuousQuasiChar F)
    (ψ : LocalAddCharData F) (u : Fˣ) :
    G.highInductionFactor i (χ * normQuasiChar F (G.field i) lambda)
        (scaleAddCharData F ψ u).character =
      (G.highDeterminant i χ u : ℂ) * (lambda u : ℂ) ^ 2 *
        G.highInductionFactor i (χ * normQuasiChar F (G.field i) lambda) ψ.character := by
  let L := G.field i
  letI := lowerCyclic G i
  letI := primeCyclicNormCharacter_finite F L
  letI := Fintype.ofFinite (NormCharacter F L)
  let ψL := canonicalLocalAddCharData L (tracePullbackAddChar F L ψ.character)
    (Basic.tracePullbackAddChar_ne_one F L ψ.character ψ.isConductor.character_ne_one)
  let uL := Units.map (algebraMap F L).toMonoidHom u
  have hscale : tracePullbackAddChar F L (scaleAddCharData F ψ u).character =
      (scaleAddCharData L ψL uL).character := by
    apply ContinuousAddChar.ext
    intro x
    change ψ.character ((u : F) * Algebra.trace F L x) =
      ψ.character (Algebra.trace F L (algebraMap F L (u : F) * x))
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hnorm : normUnits F L uL = u ^ 2 := by
    apply Units.ext
    change Algebra.norm F (algebraMap F L (u : F)) = (u : F) ^ 2
    rw [Algebra.norm_algebraMap, (originLine_degrees F K (G.g i) (G.nontrivial i)).1]
  change localConstant L (χ * normQuasiChar F L lambda)
    (tracePullbackAddChar F L (scaleAddCharData F ψ u).character) *
      (∏ μ : NormCharacter F L, localConstant F μ.1 (scaleAddCharData F ψ u).character) = _
  rw [hscale, localConstant_scale L]
  simp_rw [localConstant_scale F]
  rw [Finset.prod_mul_distrib]
  have hprod : (∏ μ : NormCharacter F L, (μ.1 u : ℂ)) =
      (Characters.normCharacterProduct F L u : ℂ) := by
    rw [Characters.normCharacterProduct_apply]
    simp [normCharacterFinset]
  rw [hprod]
  have hvalue : (χ * normQuasiChar F L lambda) uL = χ uL * lambda u ^ 2 := by
    change χ uL * lambda (normUnits F L uL) = _
    rw [hnorm, map_pow]
  rw [hvalue]
  change _ = ((χ uL * Characters.normCharacterProduct F L u : ℂˣ) : ℂ) * _ *
    (localConstant L (χ * normQuasiChar F L lambda) ψL.character * _)
  push_cast
  ring

omit [CharP F 2] [CharP K 2] in
/-- Compatibility gives a single corrected restriction on all three fields. -/
private theorem high_determinant_eq
    (χ : (i : Fin 3) → ContinuousQuasiChar (G.field i))
    (Θ : ContinuousQuasiChar K)
    (hc : ∀ i, normQuasiChar (G.field i) K (χ i) = Θ)
    (hp : ¬ ∃ eta : ContinuousQuasiChar F, normQuasiChar F K eta = Θ)
    (i : Fin 3) : G.highDeterminant i (χ i) = G.highDeterminant 0 (χ 0) := by
  by_cases hi : i = 0
  · subst i; rfl
  obtain ⟨_, _, _, _, hranges, _⟩ := Characters.quadraticProduct F
    (origin_group_equiv F K) G.field
    (fun j ↦ (originLine_degrees F K (G.g j) (G.nontrivial j)).1) (field_injective G)
  exact (Characters.conjugacy Nat.prime_two (origin_group_equiv F K)
    (G.field i) (G.field 0)
    (originLine_degrees F K (G.g i) (G.nontrivial i)).1
    (originLine_degrees F K (G.g 0) (G.nontrivial 0)).1
    (fun he ↦ hi (hranges he)) (χ i) (χ 0) Θ (hc i) (hc 0) hp).2.2.1

end SimultaneousASGenerators

/-- **Exact high comparison**, Theorem 11.13 (`D:EQ:highanswer`).
For every actual primitive core family and every high base twist, the complete
induction expressions have the displayed common value. The actual base
stationary coefficient is arbitrary; `highBaseCoefficient_exists` constructs it.
The core charts and compatibility are supplied by `twist`.

Writing `Ψ = originAddChar ... T₂`, the additive character in the formula is
`ψ(x) = Ψ(α⁻¹ x)`, so `c_F = (α A)⁻¹`, exactly as in the paper. The scale `α`
is arbitrary and nonzero. In particular the canonical normalization is covered.
No unitarity or exact-norm representative assumption is made. -/
theorem highComparison (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (G : SimultaneousASGenerators F K P)
    (χ : (i : Fin 3) → ContinuousQuasiChar (G.field i))
    (Θ : ContinuousQuasiChar K)
    (hc : ∀ i, normQuasiChar (G.field i) K (χ i) = Θ)
    (hp : ¬ ∃ eta : ContinuousQuasiChar F, normQuasiChar F K eta = Θ)
    (hcore : ∀ i u, u ∈ unitFiltration (G.field i) (G.stationaryDepth i) →
      χ i u = G.modelValue i u)
    (lambda : ContinuousQuasiChar F) {h : ℤ} (hh : G.highThreshold ≤ h)
    (hn : (multiplicativeConductorExponent F lambda : ℤ) = (G.t 1 : ℤ) + 1 + h)
    (a : Fˣ) (ha : ord F (a : F) = ((-h : ℤ) : WithTop ℤ))
    (hbase : ∀ u : Fˣ,
      1 - (u : F) ∈ lattice F (((G.t 1 : ℤ) + 1 + h + 1) / 2) →
        lambda u = originAddChar F P ((G.t 1 : ℤ) + 1) ((a : F) * (1 - (u : F))))
    (α : Fˣ) :
    let Ψ : LocalAddCharData F := ⟨originAddChar F P ((G.t 1 : ℤ) + 1),
      -((G.t 1 : ℤ) + 1), originAddChar_conductor F P ((G.t 1 : ℤ) + 1)⟩
    let ψ := (scaleAddCharData F Ψ α⁻¹).character
    let expression := fun i ↦ G.highInductionFactor i
      (χ i * normQuasiChar F (G.field i) lambda) ψ
    (∀ i, expression i =
      (G.highDeterminant 0 (χ 0) ((α * a)⁻¹) : ℂ) *
        (Ψ.character (Algebra.norm F G.Y / (a : F)) : ℂ) *
        localConstant F lambda ψ ^ 2) ∧ expression 0 = expression 1 := by
  dsimp only
  let Ψ : LocalAddCharData F := ⟨originAddChar F P ((G.t 1 : ℤ) + 1),
    -((G.t 1 : ℤ) + 1), originAddChar_conductor F P ((G.t 1 : ℤ) + 1)⟩
  obtain ⟨H⟩ := highCoefficient hres P G lambda χ hcore hh hn a ha hbase
  have he (i : Fin 3) :
      G.highInductionFactor i (χ i * normQuasiChar F (G.field i) lambda)
          (scaleAddCharData F Ψ α⁻¹).character =
        (G.highDeterminant 0 (χ 0) ((α * a)⁻¹) : ℂ) *
          (Ψ.character (Algebra.norm F G.Y / (a : F)) : ℂ) *
          localConstant F lambda (scaleAddCharData F Ψ α⁻¹).character ^ 2 := by
    rw [G.high_factor_scale i (χ i) lambda Ψ α⁻¹,
      G.high_edge hres lambda χ hcore hh hn a ha hbase H i,
      G.high_determinant_eq χ Θ hc hp i, localConstant_scale F]
    rw [mul_inv, map_mul]
    push_cast
    ring
  exact ⟨he, (he 0).trans (he 1).symm⟩


end
end LanglandsSecondMainLemma.Dyadic.Equal
