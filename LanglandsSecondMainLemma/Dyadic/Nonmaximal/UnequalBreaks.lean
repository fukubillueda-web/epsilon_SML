import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsFirstMainLemma.Ramification.NormBelowBreak
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.MinimalFunctions

/-!
# Unequal nonmaximal dyadic breaks

Paper `D:NM:minimal-two`. The residue maps below use literal norm
increments. Their surjectivity is proved using the public FML lifting
results on the two strict sides of the upper ramification breaks.
-/

namespace LanglandsSecondMainLemma.Dyadic.Nonmaximal

noncomputable section

open LanglandsFirstMainLemma
open private norm_increment_mem norm_increment_congruent minimal_stationary from
  LanglandsSecondMainLemma.Dyadic.Nonmaximal.MinimalFunctions

open private commonOrigin_edge residualScale from
  LanglandsSecondMainLemma.Stationary.CommonOrigin
open private even_normCharacter_conductor from
  LanglandsSecondMainLemma.Dyadic.Nonmaximal.LowerCharacters
open private primeNormCharacter_card normCharacterProduct_two from
  LanglandsSecondMainLemma.Characters.Conjugacy

set_option maxHeartbeats 1000000

section Coordinates

variable (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- Every element of the source ideal agrees, modulo the next ideal,
with the Teichmüller source chosen for its actual residue coordinate. -/
private theorem source_representative {n : ℕ}
    (π : Eˣ) (hπ : ord E (π : E) = 1) (v : lattice E (n : ℤ)) :
    ∃ x : ResidueField E,
      (minimalSourceLift E π hπ n (teichmuller E x) : E) - (v : E) ∈
        lattice E ((n : ℤ) + 1) := by
  have hp : ord E ((π : E) ^ n) = ((n : ℤ) : WithTop ℤ) := by
    rw [ord_pow, hπ]; norm_cast; simp
  let z : ringOfIntegers E := ⟨(v : E) / (π : E) ^ n,
    (mem_lattice_zero_iff E).mp
      ((div_mem_lattice_iff E _ _ (n : ℤ) 0 hp).mpr (by simp))⟩
  refine ⟨residueMap E z, ?_⟩
  have hz : ((teichmuller E (residueMap E z) : ringOfIntegers E) : E) - (z : E) ∈
      lattice E 1 :=
    (residueMap_eq_residueMap_iff E _ _).mp (residueMap_teichmuller E _)
  have h := mul_mem_lattice E (show (π : E) ^ n ∈ lattice E (n : ℤ) by
    rw [mem_lattice, hp]) hz
  convert h using 1
  dsimp only [minimalSourceLift, z]
  field_simp

/-- FML's finite definition gives additive scaling for the canonical
local constant, with no unitarity condition on the quasi-character. -/
private theorem unequal_localConstant_scale (θ : LocalQuasiCharData E)
    (ψ : LocalAddCharData E) (α : Eˣ) :
    localConstant E θ.character (scaleAddCharData E ψ α).character =
      (θ.character α : ℂ) * localConstant E θ.character ψ.character := by
  let γ : AdmissibleGamma E θ ψ := Classical.choice (AdmissibleGamma.exists_admissible (F := E))
  rw [localConstant_isDeltaFinite E θ (scaleAddCharData E ψ α) (scaleAdmissibleGamma E α γ),
    localConstant_isDeltaFinite E θ ψ γ]
  exact delta_additive_scale E θ ψ α γ (scaleAdmissibleGamma E α γ)

variable (M : Type) [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra E M] [ValuativeExtension E M]
  [Module.Finite E M] [Algebra.IsQuadraticExtension E M] [PrimeCyclicExtension E M]

/-- The actual graded norm in residue coordinates, with arbitrary target scale. -/
def unequalNormCoordinate {t n b : ℕ} (htpos : 1 ≤ t) (_hn : 0 < n)
    (ht : PrimeCyclicExtension.IsLowerBreak E M (2 * t - 1))
    (hres : residueDegree E M = 1)
    (htrace : (b : ℤ) ≤ ((n : ℤ) + 2 * t) / 2) (hnorm : b ≤ n)
    (π : Mˣ) (hπ : ord M (π : M) = 1)
    (δ : Eˣ) (hδ : ord E (δ : E) = ((b : ℤ) : WithTop ℤ))
    (x : ResidueField M) : ResidueField E :=
  minimalCriticalCoordinate E δ hδ
    ⟨norm E M (1 + (minimalSourceLift M π hπ n (teichmuller M x) : M)) - 1,
      norm_increment_mem E M htpos ht hres htrace (by exact_mod_cast hnorm)
        (minimalSourceLift M π hπ n (teichmuller M x)).property⟩

/-- A one-step norm lift suffices for bijectivity of the actual residue
map. No exact norm representative is requested or assumed. -/
private theorem unequalNormCoordinate_bijective {t n b : ℕ}
    (htpos : 1 ≤ t) (hn : 0 < n) (hb : 0 < b)
    (ht : PrimeCyclicExtension.IsLowerBreak E M (2 * t - 1))
    (hres : residueDegree E M = 1)
    (htrace : (b : ℤ) ≤ ((n : ℤ) + 2 * t) / 2) (hnorm : b ≤ n)
    (hnext : (b : ℤ) + 1 ≤ ((n : ℤ) + 1 + 2 * t) / 2)
    (π : Mˣ) (hπ : ord M (π : M) = 1)
    (δ : Eˣ) (hδ : ord E (δ : E) = ((b : ℤ) : WithTop ℤ))
    (hlift : ∀ u : Eˣ, u ∈ unitFiltration E b →
      ∃ x : Mˣ, x ∈ unitFiltration M n ∧
        u / normUnits E M x ∈ unitFiltration E (b + 1)) :
    Function.Bijective
      (unequalNormCoordinate E M htpos hn ht hres htrace hnorm π hπ δ hδ) := by
  letI := residueFieldFintype E
  letI := residueFieldFintype M
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨?_, ?_⟩
  · intro y
    let w : lattice E (b : ℤ) := ⟨(δ : E) * (teichmuller E y : E), by
      simpa only [add_zero] using mul_mem_lattice E
        (show (δ : E) ∈ lattice E (b : ℤ) by rw [mem_lattice, hδ])
        ((mem_lattice_zero_iff E).mpr (teichmuller E y).property)⟩
    let u := positiveUnitOfLattice E hb w
    obtain ⟨x, hx, herr⟩ := hlift u u.property
    have hv : (x : M) - 1 ∈ lattice M (n : ℤ) := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      exact (mem_unitFiltration_succ_iff_sub_mem_lattice M j x).mp hx
    let v : lattice M (n : ℤ) := ⟨(x : M) - 1, hv⟩
    obtain ⟨z, hz⟩ := source_representative M π hπ v
    refine ⟨z, ?_⟩
    have hnv : norm E M (1 + (v : M)) - 1 ∈ lattice E (b : ℤ) :=
      norm_increment_mem E M htpos ht hres htrace (by exact_mod_cast hnorm) hv
    have hxval : 1 + (v : M) = (x : M) := by dsimp [v]; ring
    have hnormunit : normUnits E M x ∈ unitGroup E := by
      rw [mem_unitGroup_iff_ord_eq_zero, coe_normUnits, ord_norm, hres, one_nsmul]
      exact (mem_unitGroup_iff_ord_eq_zero M x).mp (unitFiltration_le_unitGroup M n hx)
    have hdiff := (congruentAtDepth_iff_sub_mem_lattice E _ _ _).mp
      ((div_mem_unitFiltration_iff_congruentAtDepth E (b + 1) u (normUnits E M x)
        (unitFiltration_le_unitGroup E b u.property) hnormunit).mp herr)
    have heq := minimalCriticalCoordinate_eq_of_congruent E δ hδ
      ⟨norm E M (1 + (v : M)) - 1, hnv⟩ w (by
        have h := neg_mem_lattice E hdiff
        simpa only [u, coe_positiveUnitOfLattice, coe_normUnits, hxval,
          neg_sub, Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using h)
    have hrep := norm_increment_congruent E M htpos hn ht hres hnext hnorm
      (minimalSourceLift M π hπ n (teichmuller M z)) v hz
    have hcoord := minimalCriticalCoordinate_eq_of_congruent E δ hδ
      ⟨_, norm_increment_mem E M htpos ht hres htrace (by exact_mod_cast hnorm)
        (minimalSourceLift M π hπ n (teichmuller M z)).property⟩
      ⟨_, hnv⟩ (by simpa only [sub_sub_sub_cancel_right] using hrep)
    change minimalCriticalCoordinate E δ hδ _ = y
    rw [hcoord, heq]
    change reduce E ((δ : E) * (teichmuller E y : E) / (δ : E)) _ = y
    simpa only [mul_div_cancel_left₀ _ (Units.ne_zero δ), reduce_mk] using
      residueMap_teichmuller E y
  · change residueCard M = residueCard E
    exact residueCard_eq_of_residueDegree_eq_one E M hres

/-- The first upper edge is strictly below its break. FML's graded norm
bijection gives a lift modulo the next ideal, for every target residue. -/
theorem unequalFirstNorm_bijective {a r : ℕ} (ha : 1 ≤ a) (har : a < r)
    (ht : PrimeCyclicExtension.IsLowerBreak E M (4 * r - 2 * a - 1))
    (hres : residueDegree E M = 1)
    (π : Mˣ) (hπ : ord M (π : M) = 1)
    (δ : Eˣ) (hδ : ord E (δ : E) = (((2 * r - 1 : ℕ) : ℤ) : WithTop ℤ)) :
    Function.Bijective
      (unequalNormCoordinate E M (t := 2 * r - a) (by omega) (by omega)
        (by convert ht using 1; omega) hres (by omega) le_rfl π hπ δ hδ) := by
  apply unequalNormCoordinate_bijective E M (hb := by omega) (hnext := by omega)
  obtain ⟨p, hp, hgen⟩ := monogenicUniformizer E M hres
  intro u hu
  exact exists_normUnitFiltration_oneStepCorrection E M (2 * r - 1)
    (normMapsUnitFiltration_belowBreak E M ht (by omega) hres p hp hgen)
    (normMapsUnitFiltration_belowBreak E M ht (by omega) hres p hp hgen)
    (gradedNorm_bijective_belowBreak E M ht (by omega) hres p hp hgen).2 u hu

/-- The second upper edge is strictly above its break. The exact FML
trace-ideal lift supplies source depth `2r-1` and target depth `a+r-1`. -/
theorem unequalOtherNorm_bijective {a r : ℕ} (ha : 1 ≤ a) (har : a < r)
    (ht : PrimeCyclicExtension.IsLowerBreak E M (2 * a - 1))
    (hres : residueDegree E M = 1)
    (π : Mˣ) (hπ : ord M (π : M) = 1)
    (δ : Eˣ) (hδ : ord E (δ : E) = (((a + r - 1 : ℕ) : ℤ) : WithTop ℤ)) :
    Function.Bijective
      (unequalNormCoordinate E M (n := 2 * r - 1) ha (by omega)
        ht hres (by omega) (by omega) π hπ δ hδ) := by
  apply unequalNormCoordinate_bijective E M (hb := by omega) (hnext := by omega)
  obtain ⟨p, hp, hgen⟩ := monogenicUniformizer E M hres
  intro u hu
  have h := exists_wild_norm_aboveBreak_oneStep E M ht (by omega) hres p hp hgen
    (r - a - 1) u (by convert hu using 1; congr 1; omega)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two E M] at h
  have hs : 2 * a - 1 + 2 * (r - a - 1) + (2 - 1) + 1 = 2 * r - 1 := by omega
  have hb : 2 * a - 1 + 1 + (r - a - 1) + 1 = a + r - 1 + 1 := by omega
  simpa only [hs, hb] using h

end Coordinates

section Comparison

variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  [IsKleinFour Gal(K/F)]
  (L₁ L₂ : IntermediateField F K)

attribute [local instance] Basic.intermediateFieldValuativeRel
  Basic.intermediateFieldTopology Basic.intermediateField_localField
  Basic.intermediateField_lowerValuativeExtension Basic.intermediateField_upperValuativeExtension

variable [Algebra.IsQuadraticExtension F L₁] [Algebra.IsQuadraticExtension L₁ K]
  [Algebra.IsQuadraticExtension F L₂] [Algebra.IsQuadraticExtension L₂ K]
  [PrimeCyclicExtension F L₁] [PrimeCyclicExtension L₁ K]
  [PrimeCyclicExtension F L₂] [PrimeCyclicExtension L₂ K]

/-- The complete minimal factor on one actual edge, including the lower
quadratic factor. The lower residual sum is one because its conductor is
even; its multiplicative coefficient is an actual trace norm. -/
private theorem unequal_minimal_factor
    (L : IntermediateField F K)
    [Algebra.IsQuadraticExtension F L] [Algebra.IsQuadraticExtension L K]
    [PrimeCyclicExtension F L] [PrimeCyclicExtension L K]
    {q b : ℕ} {w : ℤ} (hq : 1 ≤ q) (hb : 0 < b)
    (htF : PrimeCyclicExtension.IsLowerBreak F L (2 * q - 1))
    (hresF : residueDegree F L = 1) (hresK : residueDegree L K = 1)
    (θ : LocalQuasiCharData L) (hm : θ.conductor = 2 * b + 1)
    (ω : NormCharacter F L) (hω : ω ≠ 1)
    (Ψ : LocalAddCharData F) (ΨL : LocalAddCharData L)
    (hΨL : ΨL.character = Ψ.character.compTrace)
    (Θ : ContinuousQuasiChar K) (hc : normQuasiChar L K θ.character = Θ)
    (C : Kˣ) (hC : ord K (C : K) =
      ((-(2 * Ψ.conductor + 2 * q) - (θ.conductor : ℤ) : ℤ) : WithTop ℤ))
    (hw : w = -Ψ.conductor - 2 * q)
    (H : MinimalOriginSide L q (b + 1) w ω Ψ.character θ.character (C : K)) :
    localConstant L θ.character ΨL.character * localConstant F ω.1 Ψ.character =
      ((Characters.restrictQuasiChar F L θ.character * ω.1) (-1) : ℂ) *
        (Θ C : ℂ)⁻¹ * (Ψ.character (-elementarySymmetric F K 2 (C : K)) : ℂ) *
        Stationary.normalizedResidualFactor L θ ΨL 1 (normUnits L K C) b hm
          (by omega) (residualScale L b).1 (residualScale L b).2 := by
  let ωD := canonicalLocalQuasiCharData F ω.1
  have hmω : ωD.conductor = 2 * q :=
    (ωD.conductor_eq_of_isConductor (even_normCharacter_conductor F L q hq htF hresF ω hω)).symm
  have hone (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
      [IsNonarchimedeanLocalField E] : unitOrder E 1 = 0 := by
    unfold unitOrder
    rw [Units.val_one, ord_one]
    rfl
  have hs := minimal_stationary L hq hb htF hresF hresK θ Ψ ΨL hΨL C hC H.upper_formula
  have hZ : Stationary.IsOrdinaryStationaryCoefficient L θ
      (scaleAddCharData L ΨL (Units.map (algebraMap F L).toMonoidHom 1))
      (normUnits L K C) (by omega) := by
    constructor
    · simpa only [map_one, scaleAddCharData_conductor, hone, add_zero] using hs.1
    · have hd : θ.conductor / 2 + θ.conductor % 2 = b + 1 := by omega
      simp only [hd, map_one]
      simpa only [Stationary.IsNormalizedStationaryCoefficientAtDepth,
        scaleAddCharData_character_apply, Units.val_one, one_mul] using hs.2
  have hW : Stationary.IsOrdinaryStationaryCoefficient F ωD (scaleAddCharData F Ψ 1)
      (Stationary.commonOriginLowerCoefficient L C H.trace_ne_zero) (by omega) := by
    constructor
    · change ord F (norm F L (trace L K (C : K))) = _
      rw [ord_norm, hresF, one_nsmul, H.trace_order, hw]
      simp only [scaleAddCharData_conductor, hone, add_zero, hmω, Nat.cast_mul, Nat.cast_ofNat]
    · have hd : ωD.conductor / 2 + ωD.conductor % 2 = q := by omega
      simp only [hd]
      intro v
      change ω.1 _ = _
      simpa only [scaleAddCharData_character_apply, Units.val_one, one_mul,
        Stationary.commonOriginLowerCoefficient, coe_normUnits, Units.val_mk0] using
        H.lower_formula v v.property (positiveUnitOfLattice F (by omega) (-v))
          (by simp only [coe_positiveUnitOfLattice, Submodule.coe_neg, sub_eq_add_neg])
  have h := commonOrigin_edge L θ ωD ω rfl Θ hc Ψ ΨL hΨL 1 C
    H.trace_ne_zero (by omega) (by omega) hZ hW
  have hd : θ.conductor / 2 = b := by omega
  have hodd : θ.conductor % 2 ≠ 0 := by omega
  have heven : ωD.conductor % 2 = 0 := by omega
  subst b
  simpa only [Stationary.commonOriginResidualProduct, map_one,
    Stationary.completeNormalizedResidualFactor, dif_neg hodd, dif_pos heven,
    mul_one, inv_one, scaleAddCharData_character_apply, Units.val_one, one_mul,
    ωD, canonicalLocalQuasiCharData_character] using h


/-- The complete normalized upper residual sums agree at the constructed
minimal origin. Both affine phases remain in the functions being summed. -/
theorem unequalBreaks_residualFactors
    {a r : ℕ} (ha : 1 ≤ a) (har : a < r)
    (htF₁ : PrimeCyclicExtension.IsLowerBreak F L₁ (2 * a - 1))
    (htF₂ : PrimeCyclicExtension.IsLowerBreak F L₂ (2 * r - 1))
    (htK₁ : PrimeCyclicExtension.IsLowerBreak L₁ K (4 * r - 2 * a - 1))
    (htK₂ : PrimeCyclicExtension.IsLowerBreak L₂ K (2 * a - 1))
    (hresF₁ : residueDegree F L₁ = 1) (hresF₂ : residueDegree F L₂ = 1)
    (hresK₁ : residueDegree L₁ K = 1) (hresK₂ : residueDegree L₂ K = 1)
    (θ₁ : LocalQuasiCharData L₁) (θ₂ : LocalQuasiCharData L₂)
    (hm₁ : θ₁.conductor = 4 * r - 1) (hm₂ : θ₂.conductor = 2 * a + 2 * r - 1)
    (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂)
    (Ψ : LocalAddCharData F) (hΨ : Ψ.conductor = -2 * (r : ℤ))
    (Ψ₁ : LocalAddCharData L₁) (Ψ₂ : LocalAddCharData L₂)
    (hΨ₁ : Ψ₁.character = Ψ.character.compTrace)
    (hΨ₂ : Ψ₂.character = Ψ.character.compTrace)
    (Θ : ContinuousQuasiChar K)
    (hc₁ : normQuasiChar L₁ K θ₁.character = Θ)
    (hc₂ : normQuasiChar L₂ K θ₂.character = Θ)
    (C : Kˣ) (hC : ord K (C : K) = ((1 - 2 * (a : ℤ) : ℤ) : WithTop ℤ))
    (H₁ : MinimalOriginSide L₁ a (2 * r) (2 * ((r : ℤ) - a)) ω₁
      Ψ.character θ₁.character (C : K))
    (H₂ : MinimalOriginSide L₂ r (a + r) 0 ω₂ Ψ.character θ₂.character (C : K))
    (δ₁ : L₁ˣ) (hδ₁ : ord L₁ (δ₁ : L₁) = (((2 * r - 1 : ℕ) : ℤ) : WithTop ℤ))
    (δ₂ : L₂ˣ) (hδ₂ : ord L₂ (δ₂ : L₂) = (((a + r - 1 : ℕ) : ℤ) : WithTop ℤ))
    (π : Kˣ) (hπ : ord K (π : K) = 1) :
    Stationary.normalizedResidualFactor L₁ θ₁ Ψ₁ 1 (normUnits L₁ K C)
        (2 * r - 1) (by omega) (by omega) δ₁ hδ₁ =
      Stationary.normalizedResidualFactor L₂ θ₂ Ψ₂ 1 (normUnits L₂ K C)
        (a + r - 1) (by omega) (by omega) δ₂ hδ₂ := by
  letI := residueFieldFintype K
  letI := residueFieldFintype L₁
  letI := residueFieldFintype L₂
  let p₁ := unequalNormCoordinate L₁ K (t := 2 * r - a) (by omega) (by omega)
    (by convert htK₁ using 1; omega) hresK₁ (by omega) le_rfl π hπ δ₁ hδ₁
  let p₂ := unequalNormCoordinate L₂ K (n := 2 * r - 1) ha (by omega)
    htK₂ hresK₂ (by omega) (by omega) π hπ δ₂ hδ₂
  have hp₁ : Function.Bijective p₁ :=
    unequalFirstNorm_bijective L₁ K ha har htK₁ hresK₁ π hπ δ₁ hδ₁
  have hp₂ : Function.Bijective p₂ :=
    unequalOtherNorm_bijective L₂ K ha har htK₂ hresK₂ π hπ δ₂ hδ₂
  let f₁ := Stationary.normalizedResidualFunction L₁ θ₁ Ψ₁ 1 (normUnits L₁ K C)
    (2 * r - 1) (by omega) (by omega) δ₁ hδ₁
  let f₂ := Stationary.normalizedResidualFunction L₂ θ₂ Ψ₂ 1 (normUnits L₂ K C)
    (a + r - 1) (by omega) (by omega) δ₂ hδ₂
  have hpoint : ∀ x, f₁ (p₁ x) = f₂ (p₂ x) := by
    intro x
    let v := minimalSourceLift K π hπ (2 * r - 1) (teichmuller K x)
    have h := dyadicNonmaximal_commonFunctions L₁ L₂ ha har.le
      htF₁ htF₂ htK₁ htK₂ hresF₁ hresF₂ hresK₁ hresK₂
      θ₁ θ₂ hm₁ hm₂ ω₁ ω₂ Ψ hΨ Ψ₁ Ψ₂ hΨ₁ hΨ₂ Θ hc₁ hc₂ C hC
      H₁ H₂ δ₁ hδ₁ δ₂ hδ₂ v
    dsimp only at h
    have heq := h.1.trans h.2.symm
    convert heq using 1 <;> congr 2
  have hsum : ∑ x, f₁ x = ∑ x, f₂ x := by
    calc
      ∑ x, f₁ x = ∑ x, f₁ (p₁ x) :=
        (Fintype.sum_bijective p₁ hp₁ _ f₁ (fun _ => rfl)).symm
      _ = ∑ x, f₂ (p₂ x) := Finset.sum_congr rfl (fun x _ => hpoint x)
      _ = ∑ x, f₂ x := Fintype.sum_bijective p₂ hp₂ _ f₂ (fun _ => rfl)
  have hcard : residueCard L₁ = residueCard L₂ :=
    (residueCard_eq_of_residueDegree_eq_one L₁ K hresK₁).symm.trans
      (residueCard_eq_of_residueDegree_eq_one L₂ K hresK₂)
  unfold Stationary.normalizedResidualFactor
  rw [hcard]
  exact congrArg _ hsum

/-- The normalized minimal comparison and the corrected restriction
needed to undo the additive normalization. -/
private theorem unequal_normalizedComparison
    {a r : ℕ} (ha : 1 ≤ a) (har : a < r)
    (htF₁ : PrimeCyclicExtension.IsLowerBreak F L₁ (2 * a - 1))
    (htF₂ : PrimeCyclicExtension.IsLowerBreak F L₂ (2 * r - 1))
    (htK₁ : PrimeCyclicExtension.IsLowerBreak L₁ K (4 * r - 2 * a - 1))
    (htK₂ : PrimeCyclicExtension.IsLowerBreak L₂ K (2 * a - 1))
    (hresF₁ : residueDegree F L₁ = 1) (hresF₂ : residueDegree F L₂ = 1)
    (hresK₁ : residueDegree L₁ K = 1) (hresK₂ : residueDegree L₂ K = 1)
    (θ₁ : LocalQuasiCharData L₁) (θ₂ : LocalQuasiCharData L₂)
    (hm₁ : θ₁.conductor = 4 * r - 1) (hm₂ : θ₂.conductor = 2 * a + 2 * r - 1)
    (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂)
    (hω₁ : ω₁ ≠ 1) (hω₂ : ω₂ ≠ 1)
    (Ψ : LocalAddCharData F) (hΨ : Ψ.conductor = -2 * (r : ℤ))
    (Ψ₁ : LocalAddCharData L₁) (Ψ₂ : LocalAddCharData L₂)
    (hΨ₁ : Ψ₁.character = Ψ.character.compTrace)
    (hΨ₂ : Ψ₂.character = Ψ.character.compTrace)
    (Θ : ContinuousQuasiChar K)
    (hc₁ : normQuasiChar L₁ K θ₁.character = Θ)
    (hc₂ : normQuasiChar L₂ K θ₂.character = Θ)
    (C : Kˣ) (hC : ord K (C : K) = ((1 - 2 * (a : ℤ) : ℤ) : WithTop ℤ))
    (H₁ : MinimalOriginSide L₁ a (2 * r) (2 * ((r : ℤ) - a)) ω₁
      Ψ.character θ₁.character (C : K))
    (H₂ : MinimalOriginSide L₂ r (a + r) 0 ω₂ Ψ.character θ₂.character (C : K))
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (hne : Ramification.intermediateNormRange L₁ ≠ Ramification.intermediateNormRange L₂)
    (hprimitive : ¬ ∃ χ : ContinuousQuasiChar F, normQuasiChar F K χ = Θ) :
    Characters.restrictQuasiChar F L₁ θ₁.character * ω₁.1 =
        Characters.restrictQuasiChar F L₂ θ₂.character * ω₂.1 ∧
    localConstant L₁ θ₁.character Ψ₁.character * localConstant F ω₁.1 Ψ.character =
      localConstant L₂ θ₂.character Ψ₂.character * localConstant F ω₂.1 Ψ.character := by
  have hdeg₁ := Algebra.IsQuadraticExtension.finrank_eq_two F L₁
  have hdeg₂ := Algebra.IsQuadraticExtension.finrank_eq_two F L₂
  have hconj := Characters.conjugacy Nat.prime_two hG L₁ L₂ hdeg₁ hdeg₂ hne
    θ₁.character θ₂.character Θ hc₁ hc₂ hprimitive
  letI := primeCyclicNormCharacter_finite F L₁
  letI := primeCyclicNormCharacter_finite F L₂
  have hprod₁ : Characters.intermediateNormCharacterProduct Nat.prime_two hG L₁ hdeg₁ = ω₁.1 :=
    normCharacterProduct_two F L₁
      ((primeNormCharacter_card F L₁).trans hdeg₁) ω₁ hω₁
  have hprod₂ : Characters.intermediateNormCharacterProduct Nat.prime_two hG L₂ hdeg₂ = ω₂.1 :=
    normCharacterProduct_two F L₂
      ((primeNormCharacter_card F L₂).trans hdeg₂) ω₂ hω₂
  have hD := hconj.2.2.1
  rw [hprod₁, hprod₂] at hD
  have hf₁ := unequal_minimal_factor L₁ ha (show 0 < 2 * r - 1 by omega)
    htF₁ hresF₁ hresK₁ θ₁ (by omega) ω₁ hω₁ Ψ Ψ₁ hΨ₁ Θ hc₁ C
    (by convert hC using 1; rw [hΨ, hm₁]; congr 1; omega)
    (show 2 * ((r : ℤ) - a) = -Ψ.conductor - 2 * a by rw [hΨ]; ring)
    (by simpa only [show 2 * r - 1 + 1 = 2 * r by omega] using H₁)
  have hf₂ := unequal_minimal_factor L₂ (show 1 ≤ r by omega)
    (show 0 < a + r - 1 by omega) htF₂ hresF₂ hresK₂ θ₂ (by omega) ω₂ hω₂
    Ψ Ψ₂ hΨ₂ Θ hc₂ C
    (by convert hC using 1; rw [hΨ, hm₂]; congr 1; omega)
    (show (0 : ℤ) = -Ψ.conductor - 2 * r by rw [hΨ]; ring)
    (by simpa only [show a + r - 1 + 1 = a + r by omega] using H₂)
  obtain ⟨p, hp⟩ := exists_ord_eq K 1
  have hp0 : p ≠ 0 := (ord_ne_top_iff K).mp (by rw [hp]; exact WithTop.coe_ne_top)
  have hres := unequalBreaks_residualFactors L₁ L₂ ha har htF₁ htF₂ htK₁ htK₂
    hresF₁ hresF₂ hresK₁ hresK₂ θ₁ θ₂ hm₁ hm₂ ω₁ ω₂ Ψ hΨ Ψ₁ Ψ₂ hΨ₁ hΨ₂
    Θ hc₁ hc₂ C hC H₁ H₂
    (residualScale L₁ (2 * r - 1)).1
    (residualScale L₁ (2 * r - 1)).2
    (residualScale L₂ (a + r - 1)).1
    (residualScale L₂ (a + r - 1)).2 (Units.mk0 p hp0) hp
  refine ⟨hD, ?_⟩
  rw [hf₁, hf₂, hD, hres]

/-- **Paper 13.11 (`D:NM:minimal-two`).** For a primitive compatible pair
with unequal breaks, the full local-constant products agree. `H₁,H₂`
are the proved `minimalOrigin` outputs, and the conductor and additive
normalization data come from `twist` and `lowerCharacters`. The complete
lower quadratic characters are retained. No residual comparison or norm
surjectivity is assumed. The same statement applies with fields 2 and 3
relabeled. -/
theorem unequalBreaks
    {a r : ℕ} (ha : 1 ≤ a) (har : a < r)
    (htF₁ : PrimeCyclicExtension.IsLowerBreak F L₁ (2 * a - 1))
    (htF₂ : PrimeCyclicExtension.IsLowerBreak F L₂ (2 * r - 1))
    (htK₁ : PrimeCyclicExtension.IsLowerBreak L₁ K (4 * r - 2 * a - 1))
    (htK₂ : PrimeCyclicExtension.IsLowerBreak L₂ K (2 * a - 1))
    (hresF₁ : residueDegree F L₁ = 1) (hresF₂ : residueDegree F L₂ = 1)
    (hresK₁ : residueDegree L₁ K = 1) (hresK₂ : residueDegree L₂ K = 1)
    (θ₁ : LocalQuasiCharData L₁) (θ₂ : LocalQuasiCharData L₂)
    (hm₁ : θ₁.conductor = 4 * r - 1) (hm₂ : θ₂.conductor = 2 * a + 2 * r - 1)
    (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂)
    (hω₁ : ω₁ ≠ 1) (hω₂ : ω₂ ≠ 1)
    (Ψ : LocalAddCharData F) (hΨ : Ψ.conductor = -2 * (r : ℤ))
    (Ψ₁ : LocalAddCharData L₁) (Ψ₂ : LocalAddCharData L₂)
    (hΨ₁ : Ψ₁.character = Ψ.character.compTrace)
    (hΨ₂ : Ψ₂.character = Ψ.character.compTrace)
    (Θ : ContinuousQuasiChar K)
    (hc₁ : normQuasiChar L₁ K θ₁.character = Θ)
    (hc₂ : normQuasiChar L₂ K θ₂.character = Θ)
    (C : Kˣ) (hC : ord K (C : K) = ((1 - 2 * (a : ℤ) : ℤ) : WithTop ℤ))
    (H₁ : MinimalOriginSide L₁ a (2 * r) (2 * ((r : ℤ) - a)) ω₁
      Ψ.character θ₁.character (C : K))
    (H₂ : MinimalOriginSide L₂ r (a + r) 0 ω₂ Ψ.character θ₂.character (C : K))
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (hne : Ramification.intermediateNormRange L₁ ≠ Ramification.intermediateNormRange L₂)
    (hprimitive : ¬ ∃ χ : ContinuousQuasiChar F, normQuasiChar F K χ = Θ)
    (ψ : LocalAddCharData F) (ψ₁ : LocalAddCharData L₁) (ψ₂ : LocalAddCharData L₂)
    (α : Fˣ)
    (hscale : Ψ.character = (scaleAddCharData F ψ α).character)
    (hscale₁ : Ψ₁.character =
      (scaleAddCharData L₁ ψ₁ (Units.map (algebraMap F L₁).toMonoidHom α)).character)
    (hscale₂ : Ψ₂.character =
      (scaleAddCharData L₂ ψ₂ (Units.map (algebraMap F L₂).toMonoidHom α)).character) :
    localConstant L₁ θ₁.character ψ₁.character * localConstant F ω₁.1 ψ.character =
      localConstant L₂ θ₂.character ψ₂.character * localConstant F ω₂.1 ψ.character := by
  obtain ⟨hD, h⟩ := unequal_normalizedComparison L₁ L₂ ha har htF₁ htF₂ htK₁ htK₂
    hresF₁ hresF₂ hresK₁ hresK₂ θ₁ θ₂ hm₁ hm₂ ω₁ ω₂ hω₁ hω₂ Ψ hΨ Ψ₁ Ψ₂
    hΨ₁ hΨ₂ Θ hc₁ hc₂ C hC H₁ H₂ hG hne hprimitive
  let α₁ := Units.map (algebraMap F L₁).toMonoidHom α
  let α₂ := Units.map (algebraMap F L₂).toMonoidHom α
  have hsω₁ := unequal_localConstant_scale F (canonicalLocalQuasiCharData F ω₁.1) ψ α
  have hsω₂ := unequal_localConstant_scale F (canonicalLocalQuasiCharData F ω₂.1) ψ α
  rw [canonicalLocalQuasiCharData_character] at hsω₁ hsω₂
  rw [hscale₁, hscale₂, hscale, unequal_localConstant_scale L₁ θ₁ ψ₁ α₁,
    unequal_localConstant_scale L₂ θ₂ ψ₂ α₂, hsω₁, hsω₂] at h
  have hweight : (θ₁.character α₁ : ℂ) * (ω₁.1 α : ℂ) =
      (θ₂.character α₂ : ℂ) * (ω₂.1 α : ℂ) := by
    exact congrArg (fun χ : ContinuousQuasiChar F => (χ α : ℂ)) hD
  have h' : ((θ₁.character α₁ : ℂ) * (ω₁.1 α : ℂ)) *
      (localConstant L₁ θ₁.character ψ₁.character * localConstant F ω₁.1 ψ.character) =
      ((θ₂.character α₂ : ℂ) * (ω₂.1 α : ℂ)) *
      (localConstant L₂ θ₂.character ψ₂.character * localConstant F ω₂.1 ψ.character) := by
    calc
      _ = ((θ₁.character α₁ : ℂ) * localConstant L₁ θ₁.character ψ₁.character) *
          ((ω₁.1 α : ℂ) * localConstant F ω₁.1 ψ.character) := by ring
      _ = _ := h
      _ = _ := by ring
  rw [← hweight] at h'
  exact mul_left_cancel₀ (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) h'

end Comparison

end

end LanglandsSecondMainLemma.Dyadic.Nonmaximal
