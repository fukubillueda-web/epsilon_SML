import LanglandsSecondMainLemma.Dyadic.Maximal.MinimalComparison
import LanglandsSecondMainLemma.Dyadic.Maximal.HigherComparison
import LanglandsSecondMainLemma.Dyadic.Maximal.Twist
import LanglandsSecondMainLemma.Characters.InducingChoice

/-!
# Maximal dyadic comparison

Paper `D:MX:main`, with the Kummer construction immediately before
`D:MX:align` (lines 6890–6901) and the final assembly (lines 7375–7386).

The actual lower breaks give the trace estimates and valuation-normalized
Kummer generators. `comparison_alignment` constructs the aligned coordinates
and preserves the first two fields; `comparison_thirdField` identifies the
third generated field. The actual quadratic traces and diamond break ledger
supply the edge actions and upper breaks needed by the origin constructor.

The existing minimal and higher comparisons cover consecutive conductor
ranges. `comparison` transports the original compatible family to the
constructed origin and repeats the construction with the maximal fields
interchanged. Its conclusion keeps FML's canonical local constants and the
complete lower norm-character product, without a conductor bound or a
unitarity assumption.
-/

namespace LanglandsSecondMainLemma.Dyadic.Maximal
open LanglandsFirstMainLemma
open scoped BigOperators
noncomputable section

variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

open private normCharacterProduct_two from LanglandsSecondMainLemma.Characters.Conjugacy
open private primeNormCards from LanglandsSecondMainLemma.Characters.CrossedNorm

omit [Module.Free F K] in
/-- On a quadratic field the complete correction character is the unique
nonidentity norm character. -/
theorem comparison_lowerProduct
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (L : IntermediateField F K) (hL : Module.finrank F L = 2)
    (tau : NormCharacter F L) (htau : tau ≠ 1) :
    Characters.intermediateNormCharacterProduct Nat.prime_two hG L hL = tau.1 := by
  have E := Basic.intermediateField_tower_compatible Nat.prime_two hG L hL
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F L E.2.2.2.2.2.2.2.2.2.2.2.1
  letI := primeCyclicNormCharacter_finite F L
  exact normCharacterProduct_two F L ((primeNormCards F L).2.trans hL) tau htau

omit [Module.Free F K] in
/-- The complete finite product of lower local constants in degree two.
The trivial character is included and its canonical constant is proved to be one. -/
theorem comparison_inducingFactor
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (L : IntermediateField F K) (hL : Module.finrank F L = 2)
    (theta : ContinuousQuasiChar L) (psi : LocalAddCharData F) :
    Characters.inducingFactor Nat.prime_two hG psi.character L hL theta =
      localConstant L theta (tracePullbackAddChar F L psi.character) *
        localConstant F
          (Characters.intermediateNormCharacterProduct Nat.prime_two hG L hL) psi.character := by
  classical
  have E := Basic.intermediateField_tower_compatible Nat.prime_two hG L hL
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F L E.2.2.2.2.2.2.2.2.2.2.2.1
  letI := primeCyclicNormCharacter_finite F L
  letI := normCharacterFintype F L
  have hcard : Nat.card (NormCharacter F L) = 2 := (primeNormCards F L).2.trans hL
  obtain ⟨tau, htau, huniq⟩ := (Nat.card_eq_two_iff' (1 : NormCharacter F L)).mp hcard
  have hone : localConstant F (1 : ContinuousQuasiChar F) psi.character = 1 := by
    let chi := canonicalLocalQuasiCharData F (1 : ContinuousQuasiChar F)
    let gamma : AdmissibleGamma F chi psi := Classical.choice AdmissibleGamma.exists_admissible
    exact (localConstant_isDeltaFinite F chi psi gamma).trans
      (delta_trivial_of_character_eq_one F chi rfl psi gamma)
  have hprod : (normCharacterFinset F L).prod (fun nu => localConstant F nu.1 psi.character) =
      localConstant F tau.1 psi.character := by
    change (∏ nu : NormCharacter F L, localConstant F nu.1 psi.character) = _
    rw [Fintype.prod_eq_mul (1 : NormCharacter F L) tau htau.symm]
    · rw [NormCharacter.coe_one, hone, one_mul]
    · intro nu hnu
      exact (hnu.2 (huniq nu hnu.1)).elim
  change localConstant L theta (tracePullbackAddChar F L psi.character) *
    (normCharacterFinset F L).prod (fun nu => localConstant F nu.1 psi.character) = _
  rw [hprod, comparison_lowerProduct hG L hL tau htau]

open private higher_base_coefficient higher_residue_degrees from
  LanglandsSecondMainLemma.Dyadic.Maximal.HigherCoefficients
open private quadraticNormRanges_ne from LanglandsSecondMainLemma.Dyadic.Maximal.Twist

/-- The initial normalization of `D:MX:normalization` is constructed from
the actual maximal lower norm character by whole-ideal stationary duality. -/
theorem comparison_normalizingCoefficient
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (L : IntermediateField F K) (hL : Module.finrank F L = 2)
    (hres : residueDegree F K = 1) (e : ℕ) (he : 1 ≤ e)
    (ht : actualLowerBreak hG L hL (2 * e))
    (tau : NormCharacter F L) (htau : tau ≠ 1) (psi : LocalAddCharData F) :
    ∃ alpha : Fˣ,
      ord F (alpha : F) = ((-psi.conductor - (2 * (e : ℤ) + 1) : ℤ) : WithTop ℤ) ∧
      ∀ (z : F) (hz : z ∈ lattice F ((e + 1 : ℕ) : ℤ)),
        tau.1 (lowerOneSubUnit F (e + 1) (by omega) z hz) =
          (scaleAddCharData F psi alpha).character z := by
  have E := Basic.intermediateField_tower_compatible Nat.prime_two hG L hL
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F L E.2.2.2.2.2.2.2.2.2.2.2.1
  have ht' : PrimeCyclicExtension.IsLowerBreak F L (2 * e) := ht
  obtain ⟨piL, hpL, hgL⟩ := monogenicUniformizer F L (higher_residue_degrees L hres).1
  have hc := ramifiedNormCharacter_conductor F L ht'
    (higher_residue_degrees L hres).1 piL hpL hgL tau htau
  have hn := multiplicativeConductorExponent_eq_of_isConductor F tau.1 hc
  obtain ⟨alpha, ha, hchart⟩ := higher_base_coefficient F tau.1 psi
    (-psi.conductor) (by omega) (2 * e + 1) hn (by omega)
  refine ⟨alpha, ?_, ?_⟩
  · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using ha
  · intro z hz
    have hdepth : (2 * e + 1 + 1) / 2 = e + 1 := by omega
    simpa only [hdepth, scaleAddCharData_character_apply] using hchart z (by simpa [hdepth] using hz)

/-- The two uniformizer trace estimates immediately before `D:MX:align`
(paper lines 6895–6900), constructed from the actual lower breaks.
The maximal trace may vanish; its conclusion is whole-ideal membership. -/
theorem comparison_uniformizerTraces
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (I J : IntermediateField F K) (hI : Module.finrank F I = 2)
    (hJ : Module.finrank F J = 2) (hres : residueDegree F K = 1)
    (a e : ℕ) (ha : 1 ≤ a)
    (htI : actualLowerBreak hG I hI (2 * a - 1))
    (htJ : actualLowerBreak hG J hJ (2 * e)) :
    ∃ piI : ringOfIntegers I, ∃ piJ : ringOfIntegers J,
      (ValuativeRel.valuation I).IsUniformizer (piI : I) ∧
      (ValuativeRel.valuation J).IsUniformizer (piJ : J) ∧
      Algebra.adjoin (ringOfIntegers F) ({piI} : Set (ringOfIntegers I)) = ⊤ ∧
      Algebra.adjoin (ringOfIntegers F) ({piJ} : Set (ringOfIntegers J)) = ⊤ ∧
      ord F (trace F I (piI : I)) = (a : WithTop ℤ) ∧
      trace F J (piJ : J) ∈ lattice F ((e : ℤ) + 1) := by
  have EI := Basic.intermediateField_tower_compatible Nat.prime_two hG I hI
  have EJ := Basic.intermediateField_tower_compatible Nat.prime_two hG J hJ
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F I EI.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F J EJ.2.2.2.2.2.2.2.2.2.2.2.1
  have htI' : PrimeCyclicExtension.IsLowerBreak F I (2 * a - 1) := htI
  have htJ' : PrimeCyclicExtension.IsLowerBreak F J (2 * e) := htJ
  have hrI := (higher_residue_degrees I hres).1
  have hrJ := (higher_residue_degrees J hres).1
  obtain ⟨piI, hpI, hgI⟩ := monogenicUniformizer F I hrI
  obtain ⟨piJ, hpJ, hgJ⟩ := monogenicUniformizer F J hrJ
  have heI : ramificationIndex F I = 2 := by
    simpa [hI, hrI] using (finrank_eq_ramificationIndex_mul_residueDegree F I).symm
  have heJ : ramificationIndex F J = 2 := by
    simpa [hJ, hrJ] using (finrank_eq_ramificationIndex_mul_residueDegree F J).symm
  have hdI : differentExponent F I = 2 * a := by
    rw [differentExponent_eq F I htI' piI hpI hgI, hI]
    omega
  have hdJ : differentExponent F J = 2 * e + 1 := by
    rw [differentExponent_eq F J htJ' piJ hpJ hgJ, hJ]
    omega
  have hmI : (piI : I) ∈ lattice I 1 := by
    simp [mem_lattice, ord_uniformizer I hpI]
  have hmJ : (piJ : J) ∈ lattice J 1 := by
    simp [mem_lattice, ord_uniformizer J hpJ]
  refine ⟨piI, piJ, hpI, hpJ, hgI, hgJ, ?_, ?_⟩
  · exact (quadratic_trace_shell_iff F I piI hpI hgI (by norm_num) heI hI
      (by rw [hdI]; push_cast; ring) (piI : I) hmI).2 (ord_uniformizer I hpI)
  · have h := trace_mem_lattice_floor F J piJ hpJ hgJ 1 hmJ
    have hd : (1 + (differentExponent F J : ℤ)) / (ramificationIndex F J : ℤ) =
        (e : ℤ) + 1 := by rw [hdJ, heJ]; omega
    simpa only [hd] using h

open private quadratic_trace_eq quadratic_norm_eq from
  LanglandsSecondMainLemma.Dyadic.Maximal.Origin

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] [Module.Free F K] in
private theorem comparison_traceZero_adjoin
    (L : IntermediateField F K) (hL : Module.finrank F L = 2)
    (htwo : (2 : F) ≠ 0) (x : L) (hx : x ≠ 0) (htrace : trace F L x = 0) :
    IntermediateField.adjoin F {x} = ⊤ := by
  letI := IntermediateField.isSimpleOrder_of_finrank_prime F L (hL ▸ Nat.prime_two)
  rcases eq_bot_or_eq_top (IntermediateField.adjoin F {x}) with hbot | htop
  · have hmem : x ∈ IntermediateField.adjoin F {x} :=
      IntermediateField.subset_adjoin F {x} (Set.mem_singleton x)
    rw [hbot, IntermediateField.mem_bot] at hmem
    obtain ⟨y, hy⟩ := hmem
    have h : 2 * y = (0 : F) := by
      simpa only [← hy, trace_algebraMap, hL, nsmul_eq_mul, Nat.cast_ofNat] using htrace
    have hy0 := (mul_eq_zero.mp h).resolve_left htwo
    exact (hx (by rw [← hy, hy0, map_zero])).elim
  · exact htop

/-- At the maximal break, subtracting half the actual trace preserves the
uniformizer order and gives a trace-zero square root (paper lines 6899–6901).
No nonvanishing assumption on the original trace is needed. -/
theorem comparison_centeredUniformizer
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (J : IntermediateField F K) (hJ : Module.finrank F J = 2)
    (hres : residueDegree F K = 1) (e : ℕ)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (htJ : actualLowerBreak hG J hJ (2 * e)) :
    ∃ R : J, trace F J R = 0 ∧ ord J R = 1 ∧
      R ^ 2 = algebraMap F J (-norm F J R) ∧ ord F (-norm F J R) = 1 := by
  have EJ := Basic.intermediateField_tower_compatible Nat.prime_two hG J hJ
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F J EJ.2.2.2.2.2.2.2.2.2.2.2.1
  have htJ' : PrimeCyclicExtension.IsLowerBreak F J (2 * e) := htJ
  have hrJ := (higher_residue_degrees J hres).1
  obtain ⟨piJ, hpJ, hgJ⟩ := monogenicUniformizer F J hrJ
  have heJ : ramificationIndex F J = 2 := by
    simpa [hJ, hrJ] using (finrank_eq_ramificationIndex_mul_residueDegree F J).symm
  have hdJ : differentExponent F J = 2 * e + 1 := by
    rw [differentExponent_eq F J htJ' piJ hpJ hgJ, hJ]
    omega
  have htrace : trace F J (piJ : J) ∈ lattice F ((e : ℤ) + 1) := by
    have h := trace_mem_lattice_floor F J piJ hpJ hgJ 1 (x := (piJ : J))
      (by simp [mem_lattice, ord_uniformizer J hpJ])
    have hd : (1 + (differentExponent F J : ℤ)) / (ramificationIndex F J : ℤ) =
        (e : ℤ) + 1 := by rw [hdJ, heJ]; omega
    simpa only [hd] using h
  have htwo0 : (2 : F) ≠ 0 := (ord_ne_top_iff F).1 (by
    rw [htwo]; exact WithTop.coe_ne_top)
  let c : F := trace F J (piJ : J) / 2
  have hc : c ∈ lattice F 1 :=
    (div_mem_lattice_iff F _ _ (e : ℤ) 1 htwo).2 htrace
  have hcJ : (2 : WithTop ℤ) ≤ ord J (algebraMap F J c) := by
    rw [ord_algebraMap, heJ]
    have h := nsmul_le_nsmul_right ((mem_lattice F).1 hc) 2
    simpa using h
  let R : J := (piJ : J) - algebraMap F J c
  have hRtrace : trace F J R = 0 := by
    simp only [R, map_sub, trace_algebraMap, hJ, Nat.cast_ofNat, c, nsmul_eq_mul]
    field_simp [htwo0]
    ring
  have hRord : ord J R = 1 := by
    have hlt : ord J (piJ : J) < ord J (algebraMap F J c) := by
      rw [ord_uniformizer J hpJ]
      exact lt_of_lt_of_le (by norm_num) hcJ
    dsimp only [R]
    rw [sub_eq_add_neg, ord_add_eq_min J (by simpa using ne_of_lt hlt),
      ord_neg, min_eq_left (le_of_lt hlt), ord_uniformizer J hpJ]
  let sigma := PrimeCyclicExtension.generator F J
  have hsigma : sigma ≠ 1 := PrimeCyclicExtension.generator_ne_one F J
  have hsR : sigma R = -R := by
    have h := quadratic_trace_eq sigma hsigma hJ R
    rw [hRtrace, map_zero] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  refine ⟨R, hRtrace, hRord, ?_, ?_⟩
  · rw [map_neg, quadratic_norm_eq sigma hsigma hJ, hsR]
    ring
  · rw [ord_neg, ord_norm, hrJ, one_nsmul, hRord]

/-- The distinguished trace-zero Kummer generator has the exact square
defect prescribed before `D:MX:align`. Its primitive-element property is
proved in the given field, rather than assumed for a stationary model. -/
theorem comparison_distinguishedGenerator
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (I J : IntermediateField F K) (hI : Module.finrank F I = 2)
    (hJ : Module.finrank F J = 2) (hres : residueDegree F K = 1)
    (a e : ℕ) (ha : 1 ≤ a) (hae : a ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (htI : actualLowerBreak hG I hI (2 * a - 1))
    (htJ : actualLowerBreak hG J hJ (2 * e)) :
    ∃ s : I, ∃ epsilon : F,
      trace F I s = 0 ∧ s ^ 2 = algebraMap F I (1 + epsilon) ∧
      ord F epsilon = (((2 * (e : ℤ) - 2 * (a : ℤ) + 1) : ℤ) : WithTop ℤ) ∧
      IntermediateField.adjoin F {s} = ⊤ := by
  have EI := Basic.intermediateField_tower_compatible Nat.prime_two hG I hI
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F I EI.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨piI, _piJ, hpI, _hpJ, _hgI, _hgJ, htrI, _htrJ⟩ :=
    comparison_uniformizerTraces hG I J hI hJ hres a e ha htI htJ
  have hrI := (higher_residue_degrees I hres).1
  let T : F := trace F I (piI : I)
  have hT : T ≠ 0 := (ord_ne_top_iff F).1 (by
    rw [show ord F T = (a : WithTop ℤ) from htrI]; exact WithTop.coe_ne_top)
  have htwo0 : (2 : F) ≠ 0 := (ord_ne_top_iff F).1 (by
    rw [htwo]; exact WithTop.coe_ne_top)
  let s : I := 1 - algebraMap F I (2 / T) * (piI : I)
  let epsilon : F := -(2 ^ 2 * norm F I (piI : I) / T ^ 2)
  have hsTrace : trace F I s = 0 := by
    have hm : trace F I (algebraMap F I (2 / T) * (piI : I)) = (2 / T) * T := by
      simpa [T, Algebra.smul_def] using (trace F I).map_smul (2 / T) (piI : I)
    simp only [s, map_sub, hm]
    rw [show trace F I (1 : I) = (2 : F) by
      rw [← map_one (algebraMap F I), trace_algebraMap, hI]; simp]
    field_simp [hT]
    ring
  let sigma := PrimeCyclicExtension.generator F I
  have hsigma : sigma ≠ 1 := PrimeCyclicExtension.generator_ne_one F I
  have htr := quadratic_trace_eq sigma hsigma hI (piI : I)
  have hnorm := quadratic_norm_eq sigma hsigma hI (piI : I)
  have hsSq : s ^ 2 = algebraMap F I (1 + epsilon) := by
    have hTI : algebraMap F I T ≠ 0 := (map_ne_zero (algebraMap F I)).2 hT
    simp only [s, epsilon, map_add, map_one, map_neg, map_div₀, map_mul, map_pow,
      map_ofNat]
    rw [hnorm]
    field_simp [hTI]
    change algebraMap F I T = _ at htr
    linear_combination -4 * (piI : I) * htr
  have heps : ord F epsilon =
      (((2 * (e : ℤ) - 2 * (a : ℤ) + 1) : ℤ) : WithTop ℤ) := by
    simp only [epsilon, ord_neg, ord_div, ord_mul, ord_pow, htwo, ord_norm,
      hrI, one_nsmul, ord_uniformizer I hpI, show ord F T = (a : WithTop ℤ) from htrI]
    simp only [two_nsmul]
    change (((e : ℤ) + e + 1 - ((a : ℤ) + a) : ℤ) : WithTop ℤ) = _
    apply congrArg (fun z : ℤ => (z : WithTop ℤ))
    ring
  have hs0 : s ≠ 0 := by
    intro hz
    have hzero : 1 + epsilon = 0 := (algebraMap F I).injective (by simpa [hz] using hsSq.symm)
    have heq : epsilon = -1 := by linear_combination hzero
    rw [heq, ord_neg, ord_one] at heps
    have hbad : (0 : ℤ) = 2 * (e : ℤ) - 2 * (a : ℤ) + 1 := by exact_mod_cast heps
    omega
  exact ⟨s, epsilon, hsTrace, hsSq, heps, comparison_traceZero_adjoin I hI htwo0 s hs0 hsTrace⟩


private theorem comparison_unitCoefficient
    (pi : ringOfIntegers F)
    (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F))
    (b : ℕ) (x : F) (hx : ord F x = (b : WithTop ℤ)) :
    ∃ u : (ringOfIntegers F)ˣ, x = (pi : F) ^ b * (u : F) := by
  have hp : (pi : F) ≠ 0 := (ord_ne_top_iff F).1 (by
    rw [ord_uniformizer F hpi]; norm_num)
  let y : F := x / (pi : F) ^ b
  have hy : ord F y = 0 := by
    simp only [y, ord_div, ord_pow, ord_uniformizer F hpi, hx]
    norm_cast
    simp
  have hy0 : y ≠ 0 := (ord_ne_top_iff F).1 (by rw [hy]; norm_num)
  let u : (ringOfIntegers F)ˣ :=
    ⟨⟨y, (ord_nonneg_iff_mem_integer F y).1 (by rw [hy])⟩,
      ⟨y⁻¹, (ord_nonneg_iff_mem_integer F y⁻¹).1 (by rw [ord_inv, hy]; simp)⟩,
      by ext; exact mul_inv_cancel₀ hy0,
      by ext; exact inv_mul_cancel₀ hy0⟩
  refine ⟨u, ?_⟩
  change x = (pi : F) ^ b * (x / (pi : F) ^ b)
  field_simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K] [IsGalois F K] in
private theorem comparison_adjoin_coe
    (L : IntermediateField F K) (x : L)
    (hx : IntermediateField.adjoin F {x} = ⊤) :
    IntermediateField.adjoin F {(x : K)} = L := by
  rw [← IntermediateField.lift_adjoin_simple, hx, IntermediateField.lift_top]

open private adjoin_mul_algebraMap_eq from
  LanglandsSecondMainLemma.Dyadic.Maximal.Alignment

/-- The maximal Kummer generator is scaled by precisely `pi^(e-a)`.
Its square has order `b`, and it generates the original maximal field. -/
theorem comparison_maximalGenerator
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (J : IntermediateField F K) (hJ : Module.finrank F J = 2)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers F)
    (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F))
    (a e b : ℕ) (hae : a ≤ e) (hb : b = 2 * e - 2 * a + 1)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (htJ : actualLowerBreak hG J hJ (2 * e)) :
    ∃ R0 : K, ∃ w0 : (ringOfIntegers F)ˣ,
      R0 ^ 2 = algebraMap F K ((pi : F) ^ b * (w0 : F)) ∧
      IntermediateField.adjoin F {R0} = J := by
  obtain ⟨R, htrace, hRord, hsq, hnorm⟩ :=
    comparison_centeredUniformizer hG J hJ hres e htwo htJ
  have htwo0 : (2 : F) ≠ 0 := (ord_ne_top_iff F).1 (by
    rw [htwo]; exact WithTop.coe_ne_top)
  have hR0 : R ≠ 0 := (ord_ne_top_iff J).1 (by rw [hRord]; norm_num)
  have hgen := comparison_traceZero_adjoin J hJ htwo0 R hR0 htrace
  have hp : (pi : F) ≠ 0 := (ord_ne_top_iff F).1 (by
    rw [ord_uniformizer F hpi]; norm_num)
  let c : F := (pi : F) ^ (e - a)
  let d : F := -norm F J R * c ^ 2
  have hd : ord F d = (b : WithTop ℤ) := by
    simp only [d, c, ord_mul, ord_pow, hnorm, ord_uniformizer F hpi]
    have hb' : b = 1 + (e - a) * 2 := by omega
    rw [hb']
    simp only [two_nsmul, nsmul_one]
    norm_cast
    omega
  obtain ⟨w0, hw0⟩ := comparison_unitCoefficient pi hpi b d hd
  refine ⟨(R : K) * algebraMap F K c, w0, ?_, ?_⟩
  · rw [mul_pow, ← map_pow, ← hw0]
    have hsqK := congrArg (algebraMap J K) hsq
    simp only [map_pow, ← IsScalarTower.algebraMap_apply F J K,
      IntermediateField.algebraMap_apply] at hsqK
    rw [hsqK, ← map_mul]
  · rw [adjoin_mul_algebraMap_eq F (R : K) c (pow_ne_zero _ hp)]
    exact comparison_adjoin_coe J R hgen

/-- Construct the aligned coordinates directly from the actual lower breaks.
Both field identifications are equalities of intermediate fields of `K/F`;
no normalized Kummer coordinates are hypotheses of this result. -/
theorem comparison_alignment
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (I J : IntermediateField F K) (hI : Module.finrank F I = 2)
    (hJ : Module.finrank F J = 2) (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = 2)
    (pi : ringOfIntegers F)
    (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F))
    (a e b : ℕ) (ha : 1 ≤ a) (hae : a ≤ e) (hb : b = 2 * e - 2 * a + 1)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (htI : actualLowerBreak hG I hI (2 * a - 1))
    (htJ : actualLowerBreak hG J hJ (2 * e)) :
    ∃ u0 w0 : (ringOfIntegers F)ˣ, ∃ s R0 : K,
      ∃ D : AlignmentData pi e a b u0 w0 s R0,
        D.firstField = I ∧ D.secondField = J := by
  obtain ⟨s, epsilon, _htrace, hs, heps, hgen⟩ :=
    comparison_distinguishedGenerator hG I J hI hJ hres a e ha hae htwo htI htJ
  have heps' : ord F epsilon = (b : WithTop ℤ) := by
    rw [heps]
    have hb' : (b : ℤ) = 2 * (e : ℤ) - 2 * (a : ℤ) + 1 := by omega
    exact_mod_cast hb'.symm
  obtain ⟨u0, hu0⟩ := comparison_unitCoefficient pi hpi b epsilon heps'
  obtain ⟨R0, w0, hR0, hRgen⟩ :=
    comparison_maximalGenerator hG J hJ hres pi hpi a e b hae hb htwo htJ
  have hsK : (s : K) ^ 2 = algebraMap F K (1 + (pi : F) ^ b * (u0 : F)) := by
    have h := congrArg (algebraMap I K) hs
    simpa only [map_pow, ← IsScalarTower.algebraMap_apply F I K,
      IntermediateField.algebraMap_apply, hu0] using h
  obtain ⟨D⟩ := alignment hchar pi hpi e a b htwo ha hae hb u0 w0 (s : K) R0 hsK hR0
  refine ⟨u0, w0, (s : K), R0, D, ?_, ?_⟩
  · exact D.adjoin_S.trans (comparison_adjoin_coe I s hgen)
  · exact D.adjoin_R.trans hRgen

variable {pi : ringOfIntegers F} {e a b : ℕ}
  {u0 w0 : (ringOfIntegers F)ˣ} {s R0 : K}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeExtension F K] [Module.Free F K] in
private theorem comparison_mem_of_fixed
    (L : IntermediateField F K) (hdegree : Module.finrank L K = 2)
    (htwo : (2 : K) ≠ 0) (g : Gal(K/L)) (hg : g ≠ 1)
    (x : K) (hx : g x = x) : x ∈ L := by
  have htr := quadratic_trace_eq g hg hdegree x
  rw [hx, IntermediateField.algebraMap_apply] at htr
  have heq : ((trace L K x / 2 : L) : K) = x := by
    push_cast
    apply (div_eq_iff htwo).2
    linear_combination htr
  rw [← heq]
  exact Subtype.property _

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeExtension F K] [Module.Free F K] [IsGalois F K] in
private theorem comparison_generator_not_mem
    (I J : IntermediateField F K) (hI : Module.finrank F I = 2)
    (hJ : Module.finrank F J = 2) (hne : J ≠ I)
    (x : K) (hx : IntermediateField.adjoin F {x} = J) : x ∉ I := by
  intro hmem
  have hle : J ≤ I := by
    rw [← hx, IntermediateField.adjoin_le_iff]
    intro y hy
    rcases hy with rfl
    exact hmem
  exact hne (IntermediateField.eq_of_le_of_finrank_eq hle (hJ.trans hI.symm))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] [Module.Free F K] in
/-- An actual upper automorphism negates the square-root generator of any
other quadratic field. The fixed-point implication is proved by the actual
quadratic trace, including division by the nonzero element `2`. -/
private theorem comparison_upper_action
    (I J : IntermediateField F K) (hI : Module.finrank F I = 2)
    (hJ : Module.finrank F J = 2) (hdegree : Module.finrank I K = 2)
    (hne : J ≠ I) (htwo : (2 : K) ≠ 0)
    (x : K) (c : F) (hx : IntermediateField.adjoin F {x} = J)
    (hsq : x ^ 2 = algebraMap F K c) (g : Gal(K/I)) (hg : g ≠ 1) :
    g x = -x := by
  apply (sq_eq_sq_iff_eq_or_eq_neg.mp ?_).resolve_left ?_
  · rw [← map_pow, hsq, IsScalarTower.algebraMap_apply F I K, g.commutes]
  · intro hfix
    exact comparison_generator_not_mem I J hI hJ hne x hx
      (comparison_mem_of_fixed I hdegree htwo g hg x hfix)

/-- The aligned product generates the given third quadratic field.
This transports the third field of the paper's diagram as an actual
intermediate field, rather than just identifying a square class. -/
theorem comparison_thirdField
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (D : AlignmentData pi e a b u0 w0 s R0)
    (I J H : IntermediateField F K) (hI : Module.finrank F I = 2)
    (hJ : Module.finrank F J = 2) (hH : Module.finrank F H = 2)
    (hIJ : I ≠ J) (hIH : I ≠ H) (hJH : J ≠ H)
    (hfirst : D.firstField = I) (hsecond : D.secondField = J)
    (htwo : (2 : F) ≠ 0) : D.thirdField = H := by
  have EI := Basic.intermediateField_tower_compatible Nat.prime_two hG I hI
  have EH := Basic.intermediateField_tower_compatible Nat.prime_two hG H hH
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension I K EI.2.2.2.2.2.2.2.2.2.2.2.2
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension H K EH.2.2.2.2.2.2.2.2.2.2.2.2
  have hdI : Module.finrank I K = 2 := EI.2.2.2.2.2.2.2.2.2.2.1
  have hdH : Module.finrank H K = 2 := EH.2.2.2.2.2.2.2.2.2.2.1
  have htwoK : (2 : K) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap F K)).2 htwo
  let gI := PrimeCyclicExtension.generator I K
  let gH := PrimeCyclicExtension.generator H K
  have hgI : gI ≠ 1 := PrimeCyclicExtension.generator_ne_one I K
  have hgH : gH ≠ 1 := PrimeCyclicExtension.generator_ne_one H K
  have hHS := comparison_upper_action H I hH hI hdH hIH htwoK
    D.S (1 + D.epsilon) hfirst D.S_sq gH hgH
  have hHR := comparison_upper_action H J hH hJ hdH hJH htwoK
    D.R D.rSquare hsecond D.R_sq gH hgH
  have hIR := comparison_upper_action I J hI hJ hdI hIJ.symm htwoK
    D.R D.rSquare hsecond D.R_sq gI hgI
  have hIS : gI D.S = D.S := by
    have hmem : D.S ∈ I := hfirst ▸ IntermediateField.mem_adjoin_simple_self F D.S
    exact gI.commutes ⟨D.S, hmem⟩
  have hmem : D.S * D.R ∈ H := comparison_mem_of_fixed H hdH htwoK gH hgH _ (by
    rw [map_mul, hHS, hHR, neg_mul_neg])
  have hS0 : D.S ≠ 0 := by
    intro hzero
    exact comparison_generator_not_mem J I hJ hI hIJ D.S hfirst (hzero ▸ J.zero_mem)
  have hR0 : D.R ≠ 0 := by
    intro hzero
    exact comparison_generator_not_mem I J hI hJ hIJ.symm D.R hsecond (hzero ▸ I.zero_mem)
  let z : H := ⟨D.S * D.R, hmem⟩
  have hzbase : z ∉ Set.range (algebraMap F H) := by
    rintro ⟨c, hc⟩
    have hcK : algebraMap F K c = D.S * D.R := by
      simpa only [← IsScalarTower.algebraMap_apply F H K,
        IntermediateField.algebraMap_apply, z] using
        congrArg (algebraMap H K) hc
    have hfix : gI (D.S * D.R) = D.S * D.R := by
      rw [← hcK, IsScalarTower.algebraMap_apply F I K, gI.commutes]
    rw [map_mul, hIS, hIR] at hfix
    exact (mul_ne_zero hS0 hR0) ((mul_eq_zero.mp
      (show (2 : K) * (D.S * D.R) = 0 by linear_combination -hfix)).resolve_left htwoK)
  have hzgen : IntermediateField.adjoin F {z} = ⊤ := by
    letI := IntermediateField.isSimpleOrder_of_finrank_prime F H (hH ▸ Nat.prime_two)
    rcases eq_bot_or_eq_top (IntermediateField.adjoin F {z}) with hbot | htop
    · have hz := IntermediateField.mem_adjoin_simple_self F z
      rw [hbot, IntermediateField.mem_bot] at hz
      exact (hzbase hz).elim
    · exact htop
  exact comparison_adjoin_coe H z hzgen

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K] [IsGalois F K] in
private theorem comparison_lower_action
    (x : K) (c : F) (hsq : x ^ 2 = algebraMap F K c)
    (q : Gal((IntermediateField.adjoin F {x})/F)) (hq : q ≠ 1) :
    q ⟨x, IntermediateField.mem_adjoin_simple_self F x⟩ =
      -⟨x, IntermediateField.mem_adjoin_simple_self F x⟩ := by
  let z : IntermediateField.adjoin F {x} :=
    ⟨x, IntermediateField.mem_adjoin_simple_self F x⟩
  have hzsq : z ^ 2 = algebraMap F (IntermediateField.adjoin F {x}) c := by
    apply Subtype.ext
    exact hsq
  apply (sq_eq_sq_iff_eq_or_eq_neg.mp ?_).resolve_left ?_
  · change (q z) ^ 2 = z ^ 2
    rw [← map_pow, hzsq, q.commutes]
  · intro hfix
    apply hq
    apply AlgEquiv.coe_toAlgHom_injective
    apply IntermediateField.adjoin_algHom_ext
    intro y hy
    rcases hy with rfl
    exact hfix

private theorem comparison_breakPair
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (L : IntermediateField F K) (hL : Module.finrank F L = 2)
    (hcard : Nat.card L.fixingSubgroup = 2) (t u : ℕ)
    (hpair : Ramification.IntermediateBreakPair Nat.prime_two hG L.fixingSubgroup hcard t u) :
    actualLowerBreak hG L hL t ∧ actualUpperBreak hG L hL u := by
  have hpair' :
      actualLowerBreak hG (IntermediateField.fixedField L.fixingSubgroup)
        (by rw [IsGalois.fixedField_fixingSubgroup]; exact hL) t ∧
      actualUpperBreak hG (IntermediateField.fixedField L.fixingSubgroup)
        (by rw [IsGalois.fixedField_fixingSubgroup]; exact hL) u := hpair
  simpa only [IsGalois.fixedField_fixingSubgroup] using hpair'

/-- The two unequal lower breaks determine the upper breaks, via the
proved diamond ramification ledger. This also determines the breaks on
every other quadratic field. -/
theorem comparison_upperBreaks
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (I J : IntermediateField F K) (hI : Module.finrank F I = 2)
    (hJ : Module.finrank F J = 2) (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = 2) (a e : ℕ) (ha : 1 ≤ a) (hae : a ≤ e)
    (htI : actualLowerBreak hG I hI (2 * a - 1))
    (htJ : actualLowerBreak hG J hJ (2 * e)) :
    actualUpperBreak hG I hI (4 * e - 2 * a + 1) ∧
      ∀ (L : IntermediateField F K) (hL : Module.finrank F L = 2), L ≠ I →
        actualLowerBreak hG L hL (2 * e) ∧ actualUpperBreak hG L hL (2 * a - 1) := by
  obtain ⟨P⟩ := (Ramification.diamondBreaks Nat.prime_two hG hchar).1 hres
  have hcard (L : IntermediateField F K) (hL : Module.finrank F L = 2) :
      Nat.card L.fixingSubgroup = 2 := by
    rw [IsGalois.card_fixingSubgroup_eq_finrank]
    exact (Basic.intermediateField_tower_compatible Nat.prime_two hG L hL).2.2.2.2.2.2.2.2.2.2.1
  have huniq (L : IntermediateField F K) (hL : Module.finrank F L = 2)
      (t u : ℕ) (ht : actualLowerBreak hG L hL t) (hu : actualLowerBreak hG L hL u) : t = u := by
    letI := PrimeCyclicExtension.ofCyclicPrimeExtension F L
      (Basic.intermediateField_tower_compatible Nat.prime_two hG L hL).2.2.2.2.2.2.2.2.2.2.2.1
    exact PrimeCyclicExtension.isLowerBreak_unique F L ht hu
  have hdist (L : IntermediateField F K) (hL : Module.finrank F L = 2)
      (hline : L.fixingSubgroup = P.H₀) :
      actualLowerBreak hG L hL P.t ∧ actualUpperBreak hG L hL P.b := by
    apply comparison_breakPair hG L hL (hcard L hL) P.t P.b
    simpa only [hline] using P.distinguished_breaks
  have hother (L : IntermediateField F K) (hL : Module.finrank F L = 2)
      (hline : L.fixingSubgroup ≠ P.H₀) :
      ∃ t, (actualLowerBreak hG L hL t ∧ actualUpperBreak hG L hL P.t) ∧
        t = P.t + (P.b - P.t) / 2 ∧ P.b = P.t + 2 * (t - P.t) := by
    obtain ⟨t, ht, _, heq, hb⟩ := P.other_breaks _ (hcard L hL) hline
    exact ⟨t, comparison_breakPair hG L hL (hcard L hL) t P.t ht, heq, hb⟩
  have hlineI : I.fixingSubgroup = P.H₀ := by
    by_contra hnI
    obtain ⟨tI, htI', heqI, _⟩ := hother I hI hnI
    have hvalI := huniq I hI _ _ htI htI'.1
    by_cases hlineJ : J.fixingSubgroup = P.H₀
    · have hvalJ := huniq J hJ _ _ htJ (hdist J hJ hlineJ).1
      omega
    · obtain ⟨tJ, htJ', heqJ, _⟩ := hother J hJ hlineJ
      have hvalJ := huniq J hJ _ _ htJ htJ'.1
      omega
  have ht : P.t = 2 * a - 1 := (huniq I hI _ _ htI (hdist I hI hlineI).1).symm
  have hlineJ : J.fixingSubgroup ≠ P.H₀ := by
    intro hlineJ
    have hvalJ := huniq J hJ _ _ htJ (hdist J hJ hlineJ).1
    omega
  obtain ⟨tJ, htJ', heqJ, hbJ⟩ := hother J hJ hlineJ
  have htJval := huniq J hJ _ _ htJ htJ'.1
  have hb : P.b = 4 * e - 2 * a + 1 := by omega
  refine ⟨by simpa only [hb] using (hdist I hI hlineI).2, ?_⟩
  intro L hL hne
  have hnL : L.fixingSubgroup ≠ P.H₀ := by
    intro heq
    apply hne
    have hf := congrArg IntermediateField.fixedField (heq.trans hlineI.symm)
    simpa only [IsGalois.fixedField_fixingSubgroup] using hf
  obtain ⟨tL, htL, heqL, _⟩ := hother L hL hnL
  have htLval : tL = 2 * e := by omega
  simpa only [htLval, ht] using htL

/-- The two proved conductor ranges exhaust every continuous base twist.
The full charts are those constructed by `lowerCharacters` and `twist`;
this intermediate lemma does not assert their existence. -/
theorem comparison_allConductors_of_charts
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)
    (hres : residueDegree F K = 1)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (ha : 1 ≤ a) (hae : a ≤ e) (hb : b = 2 * e - 2 * a + 1)
    (ht₁ : actualLowerBreak hG D.firstField O.first_degree (2 * a - 1))
    (ht₂ : actualLowerBreak hG D.secondField O.second_degree (2 * e))
    (ht₃ : actualLowerBreak hG D.thirdField O.third_degree (2 * e))
    (hU₁ : actualUpperBreak hG D.firstField O.first_degree (4 * e - 2 * a + 1))
    (hU₂ : actualUpperBreak hG D.secondField O.second_degree (2 * a - 1))
    (g1 : Gal(K/D.firstField)) (hg1 : g1 ≠ 1) (hg1R : g1 D.R = -D.R)
    (g2 : Gal(K/D.secondField)) (hg2 : g2 ≠ 1) (hg2S : g2 D.S = -D.S)
    (q1 : Gal(D.firstField/F)) (hq1 : q1 ≠ 1)
    (hq1S : q1 D.firstGenerator = -D.firstGenerator)
    (q2 : Gal(D.secondField/F)) (hq2 : q2 ≠ 1)
    (hq2R : q2 D.secondGenerator = -D.secondGenerator)
    (q3 : Gal(D.thirdField/F)) (hq3 : q3 ≠ 1)
    (hq3SR : q3 D.thirdGenerator = -D.thirdGenerator)
    (tau₁ : NormCharacter F D.firstField) (htau₁ : tau₁ ≠ 1)
    (tau₂ : NormCharacter F D.secondField) (htau₂ : tau₂ ≠ 1)
    (tau₃ : NormCharacter F D.thirdField) (htau₃ : tau₃ ≠ 1)
    (psi : LocalAddCharData F) (alpha : Fˣ)
    (halpha : ord F (alpha : F) =
      ((-psi.conductor - (2 * (e : ℤ) + 1) : ℤ) : WithTop ℤ))
    (chi₁ : ContinuousQuasiChar D.firstField) (chi₂ : ContinuousQuasiChar D.secondField)
    (chi₃ : ContinuousQuasiChar D.thirdField)
    (hchi₁ : IsMultiplicativeConductor D.firstField chi₁ (4 * e + 1))
    (hchi₂ : IsMultiplicativeConductor D.secondField chi₂ (2 * e + 2 * a))
    (H : NormalizationFormulas F D.firstField D.secondField D.thirdField
      a e ha tau₁ tau₂ tau₃ psi D.beta1 D.beta2 D.beta3 D.h1 D.h2 D.h3
      D.a1 D.a2 D.a3 chi₁ chi₂ chi₃ alpha)
    (lambda : LocalQuasiCharData F)
    (theta₁ : LocalQuasiCharData D.firstField) (theta₂ : LocalQuasiCharData D.secondField)
    (htheta₁ : theta₁.character = chi₁ * normQuasiChar F D.firstField lambda.character)
    (htheta₂ : theta₂.character = chi₂ * normQuasiChar F D.secondField lambda.character)
    (Theta : ContinuousQuasiChar K)
    (hc₁ : normQuasiChar D.firstField K theta₁.character = Theta)
    (hc₂ : normQuasiChar D.secondField K theta₂.character = Theta)
    (hprimitive : ¬ ∃ chi : ContinuousQuasiChar F, normQuasiChar F K chi = Theta)
    (hne : Ramification.intermediateNormRange D.firstField ≠
      Ramification.intermediateNormRange D.secondField)
    (psi₁ : LocalAddCharData D.firstField) (psi₂ : LocalAddCharData D.secondField)
    (hpsi₁ : psi₁.character = psi.character.compTrace)
    (hpsi₂ : psi₂.character = psi.character.compTrace) :
    LanglandsFirstMainLemma.localConstant D.firstField theta₁.character psi₁.character *
        LanglandsFirstMainLemma.localConstant F
          (Characters.intermediateNormCharacterProduct Nat.prime_two hG D.firstField O.first_degree)
          psi.character =
      LanglandsFirstMainLemma.localConstant D.secondField theta₂.character psi₂.character *
        LanglandsFirstMainLemma.localConstant F
          (Characters.intermediateNormCharacterProduct Nat.prime_two hG D.secondField O.second_degree)
          psi.character := by
  by_cases hn : lambda.conductor ≤ 2 * e + a
  · exact minimalComparison hG D O hres htwo ha hae hb ht₁ ht₂ ht₃ hU₁ hU₂
      g1 hg1 hg1R g2 hg2 hg2S q1 hq1 hq1S q2 hq2 hq2R q3 hq3 hq3SR
      tau₁ htau₁ tau₂ htau₂ tau₃ htau₃ psi alpha halpha
      chi₁ chi₂ chi₃ hchi₁ hchi₂ H lambda hn theta₁ theta₂ htheta₁ htheta₂
      Theta hc₁ hc₂ hprimitive hne psi₁ psi₂ hpsi₁ hpsi₂
  · have hc : multiplicativeConductorExponent F lambda.character = lambda.conductor :=
      multiplicativeConductorExponent_eq_of_isConductor F lambda.character lambda.isConductor
    have hah : a ≤ lambda.conductor - (2 * e + 1) := by omega
    have hn' : multiplicativeConductorExponent F lambda.character =
        2 * e + 1 + (lambda.conductor - (2 * e + 1)) := by omega
    have hh := higherComparison hG hres htwo ha hae hb D O ht₁ ht₂ ht₃ hU₁ hU₂
      tau₁ htau₁ tau₂ htau₂ tau₃ htau₃ psi alpha halpha
      chi₁ chi₂ chi₃ hchi₁ hchi₂ H lambda.character
      (lambda.conductor - (2 * e + 1)) hah hn'
      g1 hg1 hg1R g2 hg2 hg2S q1 hq1 hq1S q2 hq2 hq2R q3 hq3 hq3SR Theta
      (htheta₁ ▸ hc₁) (htheta₂ ▸ hc₂) hprimitive
    rw [comparison_lowerProduct hG D.firstField O.first_degree tau₁ htau₁,
      comparison_lowerProduct hG D.secondField O.second_degree tau₂ htau₂,
      htheta₁, htheta₂, hpsi₁, hpsi₂]
    exact hh

/-- Every primitive compatible family on a supplied aligned diagram satisfies
the distinguished comparison, with no conductor bound or unitarity condition.
The initial normalization, lower charts, cores, and common twist are all
constructed internally. The given characters are recovered using the exact
local-constant preservation in `twist`. The final `comparison` constructs
this intermediate theorem's aligned diagram and field identifications from
the actual ramification data. -/
theorem comparison_of_alignment
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = 2)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (ha : 1 ≤ a) (hae : a ≤ e) (hb : b = 2 * e - 2 * a + 1)
    (ht₁ : actualLowerBreak hG D.firstField O.first_degree (2 * a - 1))
    (ht₂ : actualLowerBreak hG D.secondField O.second_degree (2 * e))
    (ht₃ : actualLowerBreak hG D.thirdField O.third_degree (2 * e))
    (hU₁ : actualUpperBreak hG D.firstField O.first_degree (4 * e - 2 * a + 1))
    (hU₂ : actualUpperBreak hG D.secondField O.second_degree (2 * a - 1))
    (hU₃ : actualUpperBreak hG D.thirdField O.third_degree (2 * a - 1))
    (g1 : Gal(K/D.firstField)) (hg1 : g1 ≠ 1) (hg1R : g1 D.R = -D.R)
    (g2 : Gal(K/D.secondField)) (hg2 : g2 ≠ 1) (hg2S : g2 D.S = -D.S)
    (q1 : Gal(D.firstField/F)) (hq1 : q1 ≠ 1)
    (hq1S : q1 D.firstGenerator = -D.firstGenerator)
    (q2 : Gal(D.secondField/F)) (hq2 : q2 ≠ 1)
    (hq2R : q2 D.secondGenerator = -D.secondGenerator)
    (q3 : Gal(D.thirdField/F)) (hq3 : q3 ≠ 1)
    (hq3SR : q3 D.thirdGenerator = -D.thirdGenerator)
    (tau₁ : NormCharacter F D.firstField) (htau₁ : tau₁ ≠ 1)
    (tau₂ : NormCharacter F D.secondField) (htau₂ : tau₂ ≠ 1)
    (tau₃ : NormCharacter F D.thirdField) (htau₃ : tau₃ ≠ 1)
    (psi : LocalAddCharData F)
    (theta₁ : ContinuousQuasiChar D.firstField) (theta₂ : ContinuousQuasiChar D.secondField)
    (theta₃ : ContinuousQuasiChar D.thirdField)
    (Theta : ContinuousQuasiChar K)
    (hc₁ : normQuasiChar D.firstField K theta₁ = Theta)
    (hc₂ : normQuasiChar D.secondField K theta₂ = Theta)
    (hc₃ : normQuasiChar D.thirdField K theta₃ = Theta)
    (hprimitive : ¬ ∃ chi : ContinuousQuasiChar F, normQuasiChar F K chi = Theta) :
    Characters.inducingFactor Nat.prime_two hG psi.character D.firstField O.first_degree theta₁ =
      Characters.inducingFactor Nat.prime_two hG psi.character D.secondField O.second_degree theta₂ := by
  have E₁ := Basic.intermediateField_tower_compatible Nat.prime_two hG D.firstField O.first_degree
  have E₂ := Basic.intermediateField_tower_compatible Nat.prime_two hG D.secondField O.second_degree
  have E₃ := Basic.intermediateField_tower_compatible Nat.prime_two hG D.thirdField O.third_degree
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F D.firstField E₁.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F D.secondField E₂.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F D.thirdField E₃.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension D.firstField K E₁.2.2.2.2.2.2.2.2.2.2.2.2
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension D.secondField K E₂.2.2.2.2.2.2.2.2.2.2.2.2
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension D.thirdField K E₃.2.2.2.2.2.2.2.2.2.2.2.2
  have ht₁' : PrimeCyclicExtension.IsLowerBreak F D.firstField (2 * a - 1) := ht₁
  have ht₂' : PrimeCyclicExtension.IsLowerBreak F D.secondField (2 * e) := ht₂
  have ht₃' : PrimeCyclicExtension.IsLowerBreak F D.thirdField (2 * e) := ht₃
  have hU₁' : PrimeCyclicExtension.IsLowerBreak D.firstField K (4 * e - 2 * a + 1) := hU₁
  have hU₂' : PrimeCyclicExtension.IsLowerBreak D.secondField K (2 * a - 1) := hU₂
  have hU₃' : PrimeCyclicExtension.IsLowerBreak D.thirdField K (2 * a - 1) := hU₃
  obtain ⟨alpha, halpha, hchart₃⟩ := comparison_normalizingCoefficient
    hG D.thirdField O.third_degree hres e (by omega) ht₃ tau₃ htau₃ psi
  have Hlower := lowerCharacters hG hres htwo ha hae hb D O ht₁' ht₂' ht₃'
    tau₁ htau₁ tau₂ htau₂ tau₃ htau₃ (scaleAddCharData F psi alpha).character hchart₃
  obtain ⟨chi₁, chi₂, chi₃, hchi₁, hchi₂, _hchi₃, _hcc₁, _hcc₃,
      _hcorePrimitive, hR₁, hR₂, hR₃, lambda, sigma, omega₁, omega₂, omega₃,
      _ho₁, _ho₂, _ho₃, _hconj₁, _hconj₂, _hconj₃, _hdet₁₂, _hdet₃₂,
      hreal₁, hreal₂, hpull, heq₁, heq₂, _hconductors⟩ :=
    twist hG hres hchar htwo ha hae hb D O ht₁' ht₂' ht₃' hU₁' hU₂' hU₃'
      tau₁ tau₂ tau₃ htau₃ (scaleAddCharData F psi alpha).character Hlower
      theta₁ theta₂ theta₃ Theta hc₁ hc₂ hc₃ hprimitive psi.character psi.isConductor.character_ne_one
  have H : NormalizationFormulas F D.firstField D.secondField D.thirdField
      a e ha tau₁ tau₂ tau₃ psi D.beta1 D.beta2 D.beta3 D.h1 D.h2 D.h3
      D.a1 D.a2 D.a3 chi₁ chi₂ chi₃ alpha := ⟨Hlower, hR₁, hR₂, hR₃⟩
  have hne : Ramification.intermediateNormRange D.firstField ≠
      Ramification.intermediateNormRange D.secondField :=
    quadraticNormRanges_ne F D.firstField D.secondField ht₁' ht₂'
      (higher_residue_degrees D.firstField hres).1
      (higher_residue_degrees D.secondField hres).1 O.first_degree (by omega)
  let lambdaData := canonicalLocalQuasiCharData F lambda
  let thetaData₁ := canonicalLocalQuasiCharData D.firstField
    (chi₁ * normQuasiChar F D.firstField lambda)
  let thetaData₂ := canonicalLocalQuasiCharData D.secondField
    (chi₂ * normQuasiChar F D.secondField lambda)
  let psi₁ := canonicalLocalAddCharData D.firstField
    (tracePullbackAddChar F D.firstField psi.character)
    (Basic.tracePullbackAddChar_ne_one F D.firstField psi.character psi.isConductor.character_ne_one)
  let psi₂ := canonicalLocalAddCharData D.secondField
    (tracePullbackAddChar F D.secondField psi.character)
    (Basic.tracePullbackAddChar_ne_one F D.secondField psi.character psi.isConductor.character_ne_one)
  have hcompare := comparison_allConductors_of_charts hG D O hres htwo ha hae hb
    ht₁ ht₂ ht₃ hU₁ hU₂ g1 hg1 hg1R g2 hg2 hg2S
    q1 hq1 hq1S q2 hq2 hq2R q3 hq3 hq3SR tau₁ htau₁ tau₂ htau₂ tau₃ htau₃
    psi alpha halpha chi₁ chi₂ chi₃ hchi₁ hchi₂ H lambdaData
    thetaData₁ thetaData₂ rfl rfl Theta
    (by simpa only [thetaData₁, canonicalLocalQuasiCharData_character, ← hreal₁] using hpull)
    (by simpa only [thetaData₂, canonicalLocalQuasiCharData_character, ← hreal₂] using hc₂)
    hprimitive hne psi₁ psi₂ rfl rfl
  change localConstant D.firstField (chi₁ * normQuasiChar F D.firstField lambda)
      (tracePullbackAddChar F D.firstField psi.character) * _ =
    localConstant D.secondField (chi₂ * normQuasiChar F D.secondField lambda)
      (tracePullbackAddChar F D.secondField psi.character) * _ at hcompare
  rw [heq₁, heq₂] at hcompare
  rw [comparison_inducingFactor hG D.firstField O.first_degree theta₁ psi,
    comparison_inducingFactor hG D.secondField O.second_degree theta₂ psi]
  exact hcompare

omit [Module.Free F K] in
private theorem comparison_normCharacter_exists
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (L : IntermediateField F K) (hL : Module.finrank F L = 2) :
    ∃ tau : NormCharacter F L, tau ≠ 1 := by
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F L
    (Basic.intermediateField_tower_compatible Nat.prime_two hG L hL).2.2.2.2.2.2.2.2.2.2.2.1
  letI := primeCyclicNormCharacter_finite F L
  obtain ⟨tau, htau, _⟩ := (Nat.card_eq_two_iff' (1 : NormCharacter F L)).mp
    ((primeNormCards F L).2.trans hL)
  exact ⟨tau, htau⟩

/-- Transport the given family to the constructed aligned origin. All six
edge actions, all breaks, and the complete origin ledger are constructed
from the original fields before applying the conductor assembly. -/
private theorem comparison_pair
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (I J H : IntermediateField F K) (hI : Module.finrank F I = 2)
    (hJ : Module.finrank F J = 2) (hH : Module.finrank F H = 2)
    (hIJ : I ≠ J) (hIH : I ≠ H) (hJH : J ≠ H)
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = 2)
    (pi : ringOfIntegers F)
    (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F))
    (a e : ℕ) (ha : 1 ≤ a) (hae : a ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (htI : actualLowerBreak hG I hI (2 * a - 1))
    (htJ : actualLowerBreak hG J hJ (2 * e))
    (thetaI : ContinuousQuasiChar I) (thetaJ : ContinuousQuasiChar J)
    (thetaH : ContinuousQuasiChar H) (Theta : ContinuousQuasiChar K)
    (hcI : normQuasiChar I K thetaI = Theta)
    (hcJ : normQuasiChar J K thetaJ = Theta)
    (hcH : normQuasiChar H K thetaH = Theta)
    (hprimitive : ¬ ∃ chi : ContinuousQuasiChar F, normQuasiChar F K chi = Theta)
    (psi : LocalAddCharData F) :
    Characters.inducingFactor Nat.prime_two hG psi.character I hI thetaI =
      Characters.inducingFactor Nat.prime_two hG psi.character J hJ thetaJ := by
  let b := 2 * e - 2 * a + 1
  have htwo0 : (2 : F) ≠ 0 := (ord_ne_top_iff F).1 (by
    rw [htwo]; exact WithTop.coe_ne_top)
  have htwoK : (2 : K) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap F K)).2 htwo0
  obtain ⟨u0, w0, s, R0, D, hfirst, hsecond⟩ :=
    comparison_alignment hG I J hI hJ hres hchar pi hpi a e b ha hae rfl htwo htI htJ
  have hthird := comparison_thirdField hG D I J H hI hJ hH hIJ hIH hJH hfirst hsecond htwo0
  subst I
  subst J
  subst H
  have E₁ := Basic.intermediateField_tower_compatible Nat.prime_two hG D.firstField hI
  have E₂ := Basic.intermediateField_tower_compatible Nat.prime_two hG D.secondField hJ
  have E₃ := Basic.intermediateField_tower_compatible Nat.prime_two hG D.thirdField hH
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F D.firstField E₁.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F D.secondField E₂.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F D.thirdField E₃.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension D.firstField K E₁.2.2.2.2.2.2.2.2.2.2.2.2
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension D.secondField K E₂.2.2.2.2.2.2.2.2.2.2.2.2
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension D.thirdField K E₃.2.2.2.2.2.2.2.2.2.2.2.2
  let g1 := PrimeCyclicExtension.generator D.firstField K
  let g2 := PrimeCyclicExtension.generator D.secondField K
  let g3 := PrimeCyclicExtension.generator D.thirdField K
  have hg1 : g1 ≠ 1 := PrimeCyclicExtension.generator_ne_one D.firstField K
  have hg2 : g2 ≠ 1 := PrimeCyclicExtension.generator_ne_one D.secondField K
  have hg3 : g3 ≠ 1 := PrimeCyclicExtension.generator_ne_one D.thirdField K
  have hg1R := comparison_upper_action D.firstField D.secondField hI hJ
    E₁.2.2.2.2.2.2.2.2.2.2.1 hIJ.symm htwoK D.R D.rSquare rfl D.R_sq g1 hg1
  have hg2S := comparison_upper_action D.secondField D.firstField hJ hI
    E₂.2.2.2.2.2.2.2.2.2.2.1 hIJ htwoK D.S (1 + D.epsilon) rfl D.S_sq g2 hg2
  have hg3S := comparison_upper_action D.thirdField D.firstField hH hI
    E₃.2.2.2.2.2.2.2.2.2.2.1 hIH htwoK D.S (1 + D.epsilon) rfl D.S_sq g3 hg3
  have hg3R := comparison_upper_action D.thirdField D.secondField hH hJ
    E₃.2.2.2.2.2.2.2.2.2.2.1 hJH htwoK D.R D.rSquare rfl D.R_sq g3 hg3
  let q1 := PrimeCyclicExtension.generator F D.firstField
  let q2 := PrimeCyclicExtension.generator F D.secondField
  let q3 := PrimeCyclicExtension.generator F D.thirdField
  have hq1 : q1 ≠ 1 := PrimeCyclicExtension.generator_ne_one F D.firstField
  have hq2 : q2 ≠ 1 := PrimeCyclicExtension.generator_ne_one F D.secondField
  have hq3 : q3 ≠ 1 := PrimeCyclicExtension.generator_ne_one F D.thirdField
  have hq1S := comparison_lower_action D.S (1 + D.epsilon) D.S_sq q1 hq1
  have hq2R := comparison_lower_action D.R D.rSquare D.R_sq q2 hq2
  have hq3SR := comparison_lower_action (D.S * D.R) ((1 + D.epsilon) * D.rSquare)
    (by rw [mul_pow, D.S_sq, D.R_sq, map_mul]) q3 hq3
  have O := dyadicMaximal_origin_data hG hres htwo ha hae rfl D hI hJ hH
    g1 hg1 hg1R g2 hg2 hg2S g3 hg3 hg3S hg3R q1 hq1 hq1S q2 hq2 hq2R
  obtain ⟨hU₁, hother⟩ := comparison_upperBreaks hG D.firstField D.secondField hI hJ
    hres hchar a e ha hae htI htJ
  have hU₂ := (hother D.secondField hJ hIJ.symm).2
  obtain ⟨ht₃, hU₃⟩ := hother D.thirdField hH hIH.symm
  obtain ⟨tau₁, htau₁⟩ := comparison_normCharacter_exists hG D.firstField hI
  obtain ⟨tau₂, htau₂⟩ := comparison_normCharacter_exists hG D.secondField hJ
  obtain ⟨tau₃, htau₃⟩ := comparison_normCharacter_exists hG D.thirdField hH
  exact comparison_of_alignment hG D O hres hchar htwo ha hae rfl
    htI htJ ht₃ hU₁ hU₂ hU₃ g1 hg1 hg1R g2 hg2 hg2S
    q1 hq1 hq1S q2 hq2 hq2R q3 hq3 hq3SR tau₁ htau₁ tau₂ htau₂ tau₃ htau₃
    psi thetaI thetaJ thetaH Theta hcI hcJ hcH hprimitive

/-- **Maximal dyadic comparison (`D:MX:main`).** For the three actual
quadratic fields at the stated lower breaks, every primitive compatible
family has equal complete induction factors. The aligned coordinates and
all origin data are constructed from the fields. There is no conductor
bound or unitarity assumption, and the lower product includes every norm
character, including the trivial character. -/
theorem comparison
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (I J H : IntermediateField F K) (hI : Module.finrank F I = 2)
    (hJ : Module.finrank F J = 2) (hH : Module.finrank F H = 2)
    (hIJ : I ≠ J) (hIH : I ≠ H) (hJH : J ≠ H)
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = 2)
    (a e : ℕ) (ha : 1 ≤ a) (hae : a ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (htI : actualLowerBreak hG I hI (2 * a - 1))
    (htJ : actualLowerBreak hG J hJ (2 * e))
    (htH : actualLowerBreak hG H hH (2 * e))
    (thetaI : ContinuousQuasiChar I) (thetaJ : ContinuousQuasiChar J)
    (thetaH : ContinuousQuasiChar H) (Theta : ContinuousQuasiChar K)
    (hcI : normQuasiChar I K thetaI = Theta)
    (hcJ : normQuasiChar J K thetaJ = Theta)
    (hcH : normQuasiChar H K thetaH = Theta)
    (hprimitive : ¬ ∃ chi : ContinuousQuasiChar F, normQuasiChar F K chi = Theta)
    (psi : LocalAddCharData F) :
    Characters.inducingFactor Nat.prime_two hG psi.character I hI thetaI =
        Characters.inducingFactor Nat.prime_two hG psi.character J hJ thetaJ ∧
      Characters.inducingFactor Nat.prime_two hG psi.character I hI thetaI =
        Characters.inducingFactor Nat.prime_two hG psi.character H hH thetaH := by
  obtain ⟨pi, hpi⟩ := Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial
    (ValuativeRel.valuation F)
  exact ⟨comparison_pair hG I J H hI hJ hH hIJ hIH hJH hres hchar pi hpi
      a e ha hae htwo htI htJ thetaI thetaJ thetaH Theta hcI hcJ hcH hprimitive psi,
    comparison_pair hG I H J hI hH hJ hIH hIJ hJH.symm hres hchar pi hpi
      a e ha hae htwo htI htH thetaI thetaH thetaJ Theta hcI hcH hcJ hprimitive psi⟩

end
end LanglandsSecondMainLemma.Dyadic.Maximal
