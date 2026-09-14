import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.Normalization
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.CommonError

/-!
# Higher nonmaximal dyadic families

Paper Theorem 13.13 (`D:NM:higher`), with the
whole setup `D:NM:breaks`, `D:NM:origin`, and `D:NM:adjust`.
The upper domains and all error exponents are integer-indexed ideals.
The original lower trace norms are retained, and the increment
`p_X^2 + 2 k₀ p_X` is retained as a common phase.

FML's stationary quotient supplies the actual base coefficient.
Normalization and the common-error identities then construct both full
upper stationary coefficients. Applying FML's even Lamprecht formula at
the inverse raw covectors proves `higher` for the complete products.
-/

namespace LanglandsSecondMainLemma.Dyadic.Nonmaximal

open LanglandsFirstMainLemma

open private odd_core_twist_conductor
  from LanglandsSecondMainLemma.Dyadic.Nonmaximal.Twist
open private even_normCharacter_conductor even_trace_conductor
  from LanglandsSecondMainLemma.Dyadic.Nonmaximal.LowerCharacters

noncomputable section

section ActualFields

variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]
  {L₁ L₂ L₃ : IntermediateField F K}

attribute [local instance] Basic.intermediateFieldValuativeRel
  Basic.intermediateFieldTopology Basic.intermediateField_localField
  Basic.intermediateField_lowerValuativeExtension Basic.intermediateField_upperValuativeExtension

variable [Algebra.IsQuadraticExtension F L₁] [Algebra.IsQuadraticExtension F L₂]
  [Algebra.IsQuadraticExtension F L₃]
  {a r : ℕ} {x : L₁} {y : L₂} {z : L₃} {f g d : F}

/-- The actual higher twists and the original lower characters all have
the even conductors used in `D:NM:higher-depths`. The odd core conductor
argument is reused from `twist`, including the endpoint `h = a`.
The hypotheses on the cores are outputs of the accepted realization. -/
theorem higher_conductors
    [PrimeCyclicExtension F L₁] [PrimeCyclicExtension F L₂]
    (ha : 1 ≤ a) (har : a ≤ r) (h : ℕ) (hah : a ≤ h)
    (ht₁ : PrimeCyclicExtension.IsLowerBreak F L₁ (2 * a - 1))
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F L₂ (2 * r - 1))
    (hres₁ : residueDegree F L₁ = 1) (hres₂ : residueDegree F L₂ = 1)
    (χ₁ : ContinuousQuasiChar L₁) (χ₂ : ContinuousQuasiChar L₂)
    (hc₁ : IsMultiplicativeConductor L₁ χ₁ (4 * r - 1))
    (hc₂ : IsMultiplicativeConductor L₂ χ₂ (2 * a + 2 * r - 1))
    (lambda : ContinuousQuasiChar F)
    (hn : multiplicativeConductorExponent F lambda = 2 * r + h)
    (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂)
    (hω₁ : ω₁ ≠ 1) (hω₂ : ω₂ ≠ 1) :
    IsMultiplicativeConductor L₁ (χ₁ * normQuasiChar F L₁ lambda)
        (2 * (2 * r + h - a)) ∧
      IsMultiplicativeConductor L₂ (χ₂ * normQuasiChar F L₂ lambda)
        (2 * (r + h)) ∧
      IsMultiplicativeConductor F ω₁.1 (2 * a) ∧
      IsMultiplicativeConductor F ω₂.1 (2 * r) := by
  have h₁ := (odd_core_twist_conductor F L₁ a (4 * r - 1) (2 * r + a)
    ha (by omega) (by omega) ht₁ hres₁ χ₁ hc₁ lambda).2 (by rw [hn]; omega)
  have h₂ := (odd_core_twist_conductor F L₂ r (2 * a + 2 * r - 1) (2 * r + a)
    (by omega) (by omega) (by omega) ht₂ hres₂ χ₂ hc₂ lambda).2 (by rw [hn]; omega)
  have hM₁ : multiplicativeConductorExponent L₁ (χ₁ * normQuasiChar F L₁ lambda) =
      2 * (2 * r + h - a) := by
    have hh := h₁.1
    rw [hn] at hh
    omega
  have hM₂ : multiplicativeConductorExponent L₂ (χ₂ * normQuasiChar F L₂ lambda) =
      2 * (r + h) := by
    have hh := h₂.1
    rw [hn] at hh
    omega
  refine ⟨?_, ?_, even_normCharacter_conductor F L₁ a ha ht₁ hres₁ ω₁ hω₁,
    even_normCharacter_conductor F L₂ r (by omega) ht₂ hres₂ ω₂ hω₂⟩
  · rw [← hM₁]
    exact multiplicativeConductorExponent_isConductor L₁ _
  · rw [← hM₂]
    exact multiplicativeConductorExponent_isConductor L₂ _

/-- The trace and norm of every element of either full higher stationary
ideal belong to the full ordinary stationary ideal of the base character.
Here `n = 2r+h` and `ceil(n/2) = (2r+h+1)/2`; there is no upper bound on `h`.
This is the domain assertion immediately after `D:NM:higher-depths`. -/
theorem higher_norm_trace_domains
    [PrimeCyclicExtension F L₁] [PrimeCyclicExtension F L₂]
    (ha : 1 ≤ a) (har : a ≤ r) (h : ℤ) (hah : (a : ℤ) ≤ h)
    (ht₁ : PrimeCyclicExtension.IsLowerBreak F L₁ (2 * a - 1))
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F L₂ (2 * r - 1))
    (hres₁ : residueDegree F L₁ = 1) (hres₂ : residueDegree F L₂ = 1) :
    (∀ v ∈ lattice L₁ (2 * (r : ℤ) + h - a),
      trace F L₁ v ∈ lattice F ((2 * (r : ℤ) + h + 1) / 2) ∧
        norm F L₁ v ∈ lattice F ((2 * (r : ℤ) + h + 1) / 2)) ∧
    (∀ v ∈ lattice L₂ ((r : ℤ) + h),
      trace F L₂ v ∈ lattice F ((2 * (r : ℤ) + h + 1) / 2) ∧
        norm F L₂ v ∈ lattice F ((2 * (r : ℤ) + h + 1) / 2)) := by
  constructor
  · intro v hv
    constructor
    · obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F L₁ hres₁
      have hm : trace F L₁ v ∈ Submodule.map
          ((trace F L₁).restrictScalars (ringOfIntegers F))
          ((lattice L₁ (2 * (r : ℤ) + h - a)).restrictScalars (ringOfIntegers F)) :=
        Submodule.mem_map.mpr ⟨v, hv, rfl⟩
      rw [cyclicPrime_trace_lattice_image_eq F L₁ ht₁ hres₁ pi hpi hgen,
        Algebra.IsQuadraticExtension.finrank_eq_two F L₁] at hm
      simp only [Nat.reduceSub, one_mul,
        Nat.sub_add_cancel (show 1 ≤ 2 * a by omega), Nat.cast_mul, Nat.cast_ofNat] at hm
      exact lattice_antitone F (by omega) hm
    · apply lattice_antitone F (show (2 * (r : ℤ) + h + 1) / 2 ≤
          2 * (r : ℤ) + h - a by omega)
      rw [mem_lattice, ord_norm, hres₁, one_nsmul]
      exact hv
  · intro v hv
    constructor
    · obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F L₂ hres₂
      have hm : trace F L₂ v ∈ Submodule.map
          ((trace F L₂).restrictScalars (ringOfIntegers F))
          ((lattice L₂ ((r : ℤ) + h)).restrictScalars (ringOfIntegers F)) :=
        Submodule.mem_map.mpr ⟨v, hv, rfl⟩
      rw [cyclicPrime_trace_lattice_image_eq F L₂ ht₂ hres₂ pi hpi hgen,
        Algebra.IsQuadraticExtension.finrank_eq_two F L₂] at hm
      simp only [Nat.reduceSub, one_mul,
        Nat.sub_add_cancel (show 1 ≤ 2 * r by omega), Nat.cast_mul, Nat.cast_ofNat] at hm
      exact lattice_antitone F (by omega) hm
    · apply lattice_antitone F (show (2 * (r : ℤ) + h + 1) / 2 ≤
          (r : ℤ) + h by omega)
      rw [mem_lattice, ord_norm, hres₂, one_nsmul]
      exact hv

omit [Algebra.IsQuadraticExtension F L₃] in
/-- The two argument depths and the two weighted-error depths in the
first paragraph of the proof of `D:NM:higher`.

The bounds record is the conclusion of `commonError`. The denominators
are the original nonzero lower trace norms of the constructed origin.
Only the weighted errors, after multiplication by the actual norms of
the variables, are asserted to be in the trivial ideal. -/
theorem higher_error_depths
    (O : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (har : a ≤ r) (h : ℤ)
    (hres₁ : residueDegree F L₁ = 1) (hres₂ : residueDegree F L₂ = 1)
    (g₁ : Gal(K/L₁)) (g₂ : Gal(K/L₂)) (X : L₃)
    (B : CommonErrorBounds O g₁ g₂ X h) :
    (∀ v ∈ lattice L₁ (2 * (r : ℤ) + h - a),
      O.firstCrossedTrace g₁ X * v /
          algebraMap F L₁ (norm F L₁ (trace L₁ K O.Y)) ∈ lattice L₁ (a : ℤ) ∧
        (O.commonErrorTerm g₁ X / norm F L₁ (trace L₁ K O.Y)) * norm F L₁ v ∈
          lattice F (2 * (r : ℤ))) ∧
    (∀ v ∈ lattice L₂ ((r : ℤ) + h),
      O.secondCrossedTrace g₂ X * v /
          algebraMap F L₂ (norm F L₂ (trace L₂ K O.Y)) ∈ lattice L₂ (r : ℤ) ∧
        (O.commonErrorTerm g₁ X / norm F L₂ (trace L₂ K O.Y)) * norm F L₂ v ∈
          lattice F (2 * (r : ℤ))) := by
  have hram₁ : ramificationIndex F L₁ = 2 := by
    have hh := finrank_eq_ramificationIndex_mul_residueDegree F L₁
    rw [Algebra.IsQuadraticExtension.finrank_eq_two F L₁, hres₁, mul_one] at hh
    exact hh.symm
  have hram₂ : ramificationIndex F L₂ = 2 := by
    have hh := finrank_eq_ramificationIndex_mul_residueDegree F L₂
    rw [Algebra.IsQuadraticExtension.finrank_eq_two F L₂, hres₂, mul_one] at hh
    exact hh.symm
  have hβ₁ : ord L₁ (algebraMap F L₁ (norm F L₁ (trace L₁ K O.Y))) =
      ((4 * ((r : ℤ) - a) : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hram₁, O.lowerNormTrace₁_order, ← WithTop.coe_nsmul]
    congr 1
    simp only [nsmul_eq_mul]
    ring
  have hβ₂ : ord L₂ (algebraMap F L₂ (norm F L₂ (trace L₂ K O.Y))) =
      ((0 : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hram₂, O.lowerNormTrace₂_order, nsmul_zero]
    rfl
  have he₁ : O.commonErrorTerm g₁ X / norm F L₁ (trace L₁ K O.Y) ∈
      lattice F ((a : ℤ) - h) := by
    rw [div_mem_lattice_iff F _ _ (2 * ((r : ℤ) - a)) ((a : ℤ) - h)
      O.lowerNormTrace₁_order]
    convert (mem_lattice F).mpr B.error_bound using 1
    congr 1
    ring
  have he₂ : O.commonErrorTerm g₁ X / norm F L₂ (trace L₂ K O.Y) ∈
      lattice F (2 * (r : ℤ) - a - h) := by
    rw [div_mem_lattice_iff F _ _ 0 (2 * (r : ℤ) - a - h)
      (by simpa using O.lowerNormTrace₂_order), zero_add]
    exact B.error_bound
  constructor
  · intro v hv
    constructor
    · rw [div_mem_lattice_iff L₁ _ _ (4 * ((r : ℤ) - a)) (a : ℤ) hβ₁]
      convert mul_mem_lattice L₁ ((mem_lattice L₁).mpr B.first_crossed_bound) hv using 1
      congr 1
      ring
    · have hn : norm F L₁ v ∈ lattice F (2 * (r : ℤ) + h - a) := by
        rw [mem_lattice, ord_norm, hres₁, one_nsmul]
        exact hv
      convert mul_mem_lattice F he₁ hn using 1
      congr 1
      ring
  · intro v hv
    constructor
    · rw [div_mem_lattice_iff L₂ _ _ 0 (r : ℤ) hβ₂, zero_add]
      convert mul_mem_lattice L₂ ((mem_lattice L₂).mpr B.second_crossed_bound) hv using 1
      congr 1
      ring
    · have hn : norm F L₂ v ∈ lattice F ((r : ℤ) + h) := by
        rw [mem_lattice, ord_norm, hres₂, one_nsmul]
        exact hv
      exact lattice_antitone F (by omega) (mul_mem_lattice F he₂ hn)

omit [Algebra.IsQuadraticExtension F L₁] [Algebra.IsQuadraticExtension F L₂]
  [Algebra.IsQuadraticExtension F L₃] in
/-- In the higher range the third-field adjustment strictly dominates
the original `Y`. Thus the actual adjusted origin and its two upper
norms are nonzero, and all three orders are exactly `-2h`. -/
theorem higher_origin_order
    [Algebra.IsQuadraticExtension L₃ K]
    (O : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (h : ℤ) (hah : (a : ℤ) ≤ h)
    (hres₁K : residueDegree L₁ K = 1) (hres₂K : residueDegree L₂ K = 1)
    (hres₃K : residueDegree L₃ K = 1)
    (X : L₃) (hX : ord L₃ X = ((-h : ℤ) : WithTop ℤ)) :
    O.adjustedOrigin X ≠ 0 ∧
      ord K (O.adjustedOrigin X) = ((-2 * h : ℤ) : WithTop ℤ) ∧
      ord L₁ (norm L₁ K (O.adjustedOrigin X)) = ((-2 * h : ℤ) : WithTop ℤ) ∧
      ord L₂ (norm L₂ K (O.adjustedOrigin X)) = ((-2 * h : ℤ) : WithTop ℤ) := by
  have hram : ramificationIndex L₃ K = 2 := by
    have hh := finrank_eq_ramificationIndex_mul_residueDegree L₃ K
    rw [Algebra.IsQuadraticExtension.finrank_eq_two L₃ K, hres₃K, mul_one] at hh
    exact hh.symm
  have hxK : ord K (X : K) = ((-2 * h : ℤ) : WithTop ℤ) := by
    change ord K (algebraMap L₃ K X) = _
    rw [ord_algebraMap, hram, hX, ← WithTop.coe_nsmul]
    congr 1
    simp only [nsmul_eq_mul]
    ring
  have hord : ord K (O.adjustedOrigin X) = ((-2 * h : ℤ) : WithTop ℤ) := by
    change ord K (O.Y - (X : K)) = _
    rw [sub_eq_add_neg, ord_add_eq_min K (by
      rw [ord_neg, hxK, O.Y_order]
      exact ne_of_gt (WithTop.coe_lt_coe.mpr (by omega))),
      ord_neg, hxK, O.Y_order, min_eq_right]
    exact WithTop.coe_le_coe.mpr (by omega)
  refine ⟨(ord_ne_top_iff K).mp (by rw [hord]; exact WithTop.coe_ne_top), hord, ?_, ?_⟩
  · rw [ord_norm, hres₁K, one_nsmul, hord]
  · rw [ord_norm, hres₂K, one_nsmul, hord]

/-- Construct the higher adjustment from any actual base coefficient of
order `-h`. Normalization supplies an exact third-field norm while
preserving every fixed lower and core formula, and `commonError` supplies
the exact identities and estimates for this very choice of `X`.

The raw coefficient and its character values on the whole base field are
preserved. `higher_stationary` applies this result to the coefficient
constructed from the actual base character's full stationary quotient. -/
theorem higher_normalized_origin
    [IsGalois F K]
    [Algebra.IsQuadraticExtension L₁ K] [Algebra.IsQuadraticExtension L₂ K]
    [Algebra.IsQuadraticExtension L₃ K]
    [PrimeCyclicExtension F L₁] [PrimeCyclicExtension F L₂]
    [PrimeCyclicExtension F L₃]
    (e a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (ht₁ : PrimeCyclicExtension.IsLowerBreak F L₁ (2 * a - 1))
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F L₂ (2 * r - 1))
    (ht₃ : PrimeCyclicExtension.IsLowerBreak F L₃ (2 * r - 1))
    (hres₁ : residueDegree F L₁ = 1) (hres₂ : residueDegree F L₂ = 1)
    (hres₃ : residueDegree F L₃ = 1)
    (hres₁K : residueDegree L₁ K = 1) (hres₂K : residueDegree L₂ K = 1)
    (hres₃K : residueDegree L₃ K = 1)
    (O : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (g₁ : Gal(K/L₁)) (hg₁ : g₁ ≠ 1) (g₂ : Gal(K/L₂)) (hg₂ : g₂ ≠ 1)
    (q₃ : Gal(L₃/F)) (hq₃ : q₃ ≠ 1)
    (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂) (ω₃ : NormCharacter F L₃)
    (hω₃ : ω₃ ≠ 1) (ψ : LocalAddCharData F) (α : Fˣ)
    (χ₁ : ContinuousQuasiChar L₁) (χ₂ : ContinuousQuasiChar L₂)
    (χ₃ : ContinuousQuasiChar L₃) :
    let β₁ := normUnits F L₁ (Units.mk0 (trace L₁ K O.Y) O.upperTraces_ne_zero.1)
    let β₂ := normUnits F L₂ (Units.mk0 (trace L₂ K O.Y) O.upperTraces_ne_zero.2.1)
    let β₃ := normUnits F L₃ (Units.mk0 (trace L₃ K O.Y) O.upperTraces_ne_zero.2.2)
    let FixedFormulas := NormalizationFormulas F L₁ L₂ L₃ a r ω₁ ω₂ ω₃ ψ β₁ β₂ β₃
      (norm L₁ K O.Y) (norm L₂ K O.Y) (norm L₃ K O.Y) χ₁ χ₂ χ₃
    FixedFormulas α →
      ∀ (h : ℤ), (a : ℤ) ≤ h →
      ∀ (Astar : Fˣ), ord F (Astar : F) = ((-h : ℤ) : WithTop ℤ) →
      ∃ (u : unitFiltration F (2 * r - 1)) (X : L₃ˣ),
        FixedFormulas (α * (u : Fˣ)) ∧
        Astar / (u : Fˣ) = normUnits F L₃ X ∧
        (α * (u : Fˣ)) * (Astar / (u : Fˣ)) = α * Astar ∧
        (∀ v : F,
          (scaleAddCharData F ψ (α * (u : Fˣ))).character
              (((Astar / (u : Fˣ) : Fˣ) : F) * v) =
            (scaleAddCharData F ψ α).character ((Astar : F) * v)) ∧
        ord L₃ (X : L₃) = ((-h : ℤ) : WithTop ℤ) ∧
        O.adjustedOrigin (X : L₃) ≠ 0 ∧
        ord K (O.adjustedOrigin (X : L₃)) = ((-2 * h : ℤ) : WithTop ℤ) ∧
        ord L₁ (norm L₁ K (O.adjustedOrigin (X : L₃))) = ((-2 * h : ℤ) : WithTop ℤ) ∧
        ord L₂ (norm L₂ K (O.adjustedOrigin (X : L₃))) = ((-2 * h : ℤ) : WithTop ℤ) ∧
        CommonErrorIdentities O g₁ g₂ q₃ (X : L₃) ∧
        CommonErrorBounds O g₁ g₂ (X : L₃) h := by
  dsimp only
  intro H h hah Astar hAstar
  obtain ⟨u, X, hnorm, H', _, hX, hraw, hvalues⟩ :=
    (normalization L₁ L₂ L₃ a r ha har ht₁ ht₂ ht₃ hres₁ hres₂ hres₃
      x y z f g d O ω₁ ω₂ ω₃ hω₃ ψ α χ₁ χ₂ χ₃ H).2 Astar
  have hXord : ord L₃ (X : L₃) = ((-h : ℤ) : WithTop ℤ) := hX.trans hAstar
  obtain ⟨hC, hCord, hN₁, hN₂⟩ :=
    higher_origin_order O h hah hres₁K hres₂K hres₃K X hXord
  obtain ⟨I, B⟩ := commonError O e ha har hre htwo hres₁ hres₂ hres₃
    g₁ hg₁ g₂ hg₂ q₃ hq₃ (X : L₃)
  exact ⟨u, X, H', hnorm, hraw, hvalues, hXord, hC, hCord, hN₁, hN₂,
    I, B h (by rw [mem_lattice, hXord])⟩

omit [Algebra.IsQuadraticExtension F L₃] in
/-- The exact additive arguments in the last paragraph of `D:NM:higher`.
The two lower coefficients are the *original* norms of the traces of `Y`.
There is no assertion that the adjusted trace norms are stationary, nor
that the common increment belongs to the additive kernel. -/
theorem higher_common_phase
    [IsGalois F K] [IsKleinFour Gal(K/F)]
    [Algebra.IsQuadraticExtension L₁ K] [Algebra.IsQuadraticExtension L₂ K]
    (O : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (g₁ : Gal(K/L₁)) (g₂ : Gal(K/L₂)) (q₃ : Gal(L₃/F)) (X : L₃)
    (I : CommonErrorIdentities O g₁ g₂ q₃ X) (Ψ : ContinuousAddChar F) :
    Ψ (-trace F L₁ (norm L₁ K (O.adjustedOrigin X)) - norm F L₁ (trace L₁ K O.Y)) =
        Ψ (-elementarySymmetric F K 2 (O.adjustedOrigin X) + O.traceNormIncrement X) ∧
      Ψ (-trace F L₂ (norm L₂ K (O.adjustedOrigin X)) - norm F L₂ (trace L₂ K O.Y)) =
        Ψ (-elementarySymmetric F K 2 (O.adjustedOrigin X) + O.traceNormIncrement X) := by
  constructor
  · congr 1
    rw [Algebra.biquadraticE2 F K L₁, I.first_trace_norm]
    ring
  · congr 1
    rw [Algebra.biquadraticE2 F K L₂, I.second_trace_norm]
    ring

end ActualFields

section HigherStationary

variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  {L₁ L₂ L₃ : IntermediateField F K}

attribute [local instance] Basic.intermediateFieldValuativeRel
  Basic.intermediateFieldTopology Basic.intermediateField_localField
  Basic.intermediateField_lowerValuativeExtension Basic.intermediateField_upperValuativeExtension

variable [Algebra.IsQuadraticExtension F L₁] [Algebra.IsQuadraticExtension F L₂]
  [Algebra.IsQuadraticExtension F L₃]
  [Algebra.IsQuadraticExtension L₁ K] [Algebra.IsQuadraticExtension L₂ K]
  [Algebra.IsQuadraticExtension L₃ K]
  [PrimeCyclicExtension F L₁] [PrimeCyclicExtension F L₂]
  [PrimeCyclicExtension F L₃]
  {a r : ℕ} {x : L₁} {y : L₂} {z : L₃} {f g d : F}

set_option maxHeartbeats 1200000 in
/-- Construct the actual full higher stationary coefficients in
`D:NM:higher`. The base coefficient is selected from FML's stationary
quotient; normalization preserves its raw covector and all fixed charts.
The two weighted errors are discarded only at depth `2r`.

`H` consists precisely of the lower data and realized core charts from
`lowerCharacters` and `twist`. No stationary property of the adjusted
origin, or exact norm choice, is an input. -/
theorem higher_stationary
    (e : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (ht₁ : PrimeCyclicExtension.IsLowerBreak F L₁ (2 * a - 1))
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F L₂ (2 * r - 1))
    (ht₃ : PrimeCyclicExtension.IsLowerBreak F L₃ (2 * r - 1))
    (hres₁ : residueDegree F L₁ = 1) (hres₂ : residueDegree F L₂ = 1)
    (hres₃ : residueDegree F L₃ = 1)
    (hres₁K : residueDegree L₁ K = 1) (hres₂K : residueDegree L₂ K = 1)
    (hres₃K : residueDegree L₃ K = 1)
    (O : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (g₁ : Gal(K/L₁)) (hg₁ : g₁ ≠ 1) (g₂ : Gal(K/L₂)) (hg₂ : g₂ ≠ 1)
    (q₃ : Gal(L₃/F)) (hq₃ : q₃ ≠ 1)
    (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂) (ω₃ : NormCharacter F L₃)
    (hω₃ : ω₃ ≠ 1) (ψ : LocalAddCharData F) (α : Fˣ)
    (χ₁ : ContinuousQuasiChar L₁) (χ₂ : ContinuousQuasiChar L₂)
    (χ₃ : ContinuousQuasiChar L₃) (lambda : ContinuousQuasiChar F)
    (h : ℕ) (hah : a ≤ h)
    (hn : multiplicativeConductorExponent F lambda = 2 * r + h) :
    let β₁ := normUnits F L₁ (Units.mk0 (trace L₁ K O.Y) O.upperTraces_ne_zero.1)
    let β₂ := normUnits F L₂ (Units.mk0 (trace L₂ K O.Y) O.upperTraces_ne_zero.2.1)
    let β₃ := normUnits F L₃ (Units.mk0 (trace L₃ K O.Y) O.upperTraces_ne_zero.2.2)
    let Fixed := NormalizationFormulas F L₁ L₂ L₃ a r ω₁ ω₂ ω₃ ψ β₁ β₂ β₃
      (norm L₁ K O.Y) (norm L₂ K O.Y) (norm L₃ K O.Y) χ₁ χ₂ χ₃
    Fixed α → ∃ (α' : Fˣ) (X : L₃ˣ),
      Fixed α' ∧ O.adjustedOrigin (X : L₃) ≠ 0 ∧
      ord L₁ (norm L₁ K (O.adjustedOrigin (X : L₃))) =
        ((-2 * (h : ℤ) : ℤ) : WithTop ℤ) ∧
      ord L₂ (norm L₂ K (O.adjustedOrigin (X : L₃))) =
        ((-2 * (h : ℤ) : ℤ) : WithTop ℤ) ∧
      CommonErrorIdentities O g₁ g₂ q₃ (X : L₃) ∧
      (∀ v ∈ lattice L₁ (2 * (r : ℤ) + h - a), ∀ V : L₁ˣ, (V : L₁) = 1 - v →
        (χ₁ * normQuasiChar F L₁ lambda) V =
          tracePullbackAddChar F L₁ (scaleAddCharData F ψ α').character
            (norm L₁ K (O.adjustedOrigin (X : L₃)) * v)) ∧
      (∀ v ∈ lattice L₂ ((r : ℤ) + h), ∀ V : L₂ˣ, (V : L₂) = 1 - v →
        (χ₂ * normQuasiChar F L₂ lambda) V =
          tracePullbackAddChar F L₂ (scaleAddCharData F ψ α').character
            (norm L₂ K (O.adjustedOrigin (X : L₃)) * v)) := by
  dsimp only
  intro H
  let Ψ := scaleAddCharData F ψ α
  let lambdaData := canonicalLocalQuasiCharData F lambda
  let n := 2 * r + h
  let q := (n + 1) / 2
  have hlambda : lambdaData.conductor = n := hn
  have hq : IsLamprechtStationaryDepth lambdaData.conductor q := by
    rw [hlambda]
    dsimp only [q, n]
    constructor <;> omega
  have hΓ : ord F ((1 : Fˣ) : F) =
      ((2 * (r : ℤ) + Ψ.conductor : ℤ) : WithTop ℤ) := by
    rw [show Ψ.conductor = -2 * (r : ℤ) from H.1.base_conductor]
    simp
  obtain ⟨c, hc⟩ := latticeQuotientMk_surjective F
    (sub_le_sub_left hq.int_le_conductor (2 * (r : ℤ)))
    (stationaryNumeratorClass F lambdaData Ψ (2 * (r : ℤ)) hq 1 hΓ)
  have hcord : ord F (c : F) = ((-(h : ℤ) : ℤ) : WithTop ℤ) := by
    rw [stationaryNumeratorClass_representative_ord F lambdaData Ψ _ hq 1 hΓ c hc, hlambda]
    congr 1
    dsimp only [n]
    push_cast
    ring
  let Astar : Fˣ := Units.mk0 (-(c : F)) (neg_ne_zero.mpr
    ((ord_ne_top_iff F).mp (by rw [hcord]; exact WithTop.coe_ne_top)))
  have hAstar : ord F (Astar : F) = ((-(h : ℤ) : ℤ) : WithTop ℤ) := by
    simpa only [Astar, Units.val_mk0, ord_neg] using hcord
  have hbase : ∀ v ∈ lattice F (q : ℤ), ∀ V : Fˣ, (V : F) = 1 - v →
      lambda V = Ψ.character ((Astar : F) * v) := by
    intro v hv V hV
    have hv' := stationaryNumeratorClass_linearization F lambdaData Ψ _ hq 1 hΓ c hc
      ⟨-v, neg_mem_lattice F hv⟩
    have he : (positiveUnitOfLattice F hq.pos ⟨-v, neg_mem_lattice F hv⟩ : Fˣ) = V := by
      apply Units.ext
      simp only [coe_positiveUnitOfLattice, hV, sub_eq_add_neg]
    rw [he] at hv'
    simpa only [lambdaData, canonicalLocalQuasiCharData_character, Units.val_one, div_one,
      Astar, Units.val_mk0, mul_neg, neg_mul] using hv'
  obtain ⟨u, X, H', hnorm, _, hvalues, _, hC, _, hN₁, hN₂, I, B⟩ :=
    higher_normalized_origin e a r ha har hre htwo ht₁ ht₂ ht₃
      hres₁ hres₂ hres₃ hres₁K hres₂K hres₃K O g₁ hg₁ g₂ hg₂ q₃ hq₃
      ω₁ ω₂ ω₃ hω₃ ψ α χ₁ χ₂ χ₃ H h (by exact_mod_cast hah) Astar hAstar
  let α' := α * (u : Fˣ)
  let Ψ' := scaleAddCharData F ψ α'
  have hbase' : ∀ v ∈ lattice F (q : ℤ), ∀ V : Fˣ, (V : F) = 1 - v →
      lambda V = Ψ'.character (O.adjustmentNorm (X : L₃) * v) := by
    intro v hv V hV
    rw [hbase v hv V hV, ← hvalues v, hnorm]
    rfl
  have htriv : AddCharTrivialOnLattice F Ψ'.character (2 * (r : ℤ)) := by
    convert Ψ'.isConductor.trivial using 1
    rw [show Ψ'.conductor = -2 * (r : ℤ) from H'.1.base_conductor]
    ring
  obtain ⟨hdepth₁, hdepth₂⟩ := higher_error_depths O har h hres₁ hres₂ g₁ g₂ X B
  obtain ⟨hdom₁, hdom₂⟩ := higher_norm_trace_domains ha har (h : ℤ)
    (by exact_mod_cast hah) ht₁ ht₂ hres₁ hres₂
  have hqcast : (q : ℤ) = (2 * (r : ℤ) + h + 1) / 2 := by
    dsimp only [q, n]
    omega
  -- Apply the exact norm-phase identity to the already proved argument
  -- depths, then remove just the weighted error in the base trivial ideal.
  have crossed (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
      [IsNonarchimedeanLocalField E] [Algebra F E]
      [ValuativeExtension F E] [Module.Finite F E]
      [Algebra.IsQuadraticExtension F E]
      (β : Fˣ) (Q : E) (v : E) (s : ℤ)
      (hphase : ∀ w ∈ lattice E s,
        tracePullbackAddChar F E Ψ'.character (algebraMap F E (β : F) * w) =
          Ψ'.character ((β : F) * norm F E w))
      (harg : Q * v / algebraMap F E (β : F) ∈ lattice E s)
      (hweighted : norm F E Q = (β : F) * O.adjustmentNorm (X : L₃) +
        O.commonErrorTerm g₁ (X : L₃))
      (herr : (O.commonErrorTerm g₁ (X : L₃) / (β : F)) * norm F E v ∈
        lattice F (2 * (r : ℤ))) :
      tracePullbackAddChar F E Ψ'.character (Q * v) =
        Ψ'.character (O.adjustmentNorm (X : L₃) * norm F E v) := by
    have hp := hphase _ harg
    have hβ : algebraMap F E (β : F) ≠ 0 :=
      (map_ne_zero (algebraMap F E)).mpr (Units.ne_zero β)
    rw [show algebraMap F E (β : F) * (Q * v / algebraMap F E (β : F)) =
        Q * v by field_simp] at hp
    have halg : (β : F) * norm F E (Q * v / algebraMap F E (β : F)) =
        O.adjustmentNorm (X : L₃) * norm F E v +
          (O.commonErrorTerm g₁ (X : L₃) / (β : F)) * norm F E v := by
      rw [div_eq_mul_inv, map_mul, Algebra.norm_inv, map_mul,
        LanglandsFirstMainLemma.norm_algebraMap,
        Algebra.IsQuadraticExtension.finrank_eq_two F E, hweighted]
      field_simp
    rw [halg, ContinuousAddChar.map_add_eq_mul, htriv _ herr, mul_one] at hp
    exact hp
  have chart (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
      [IsNonarchimedeanLocalField E] [Algebra F E]
      [ValuativeExtension F E] [Module.Finite F E]
      [Algebra.IsQuadraticExtension F E]
      (χ : ContinuousQuasiChar E) (c Q Z : E) (s : ℕ) (b : ℤ)
      (hs : 0 < s) (hsb : (s : ℤ) ≤ b)
      (hcore : ∀ V : unitFiltration E s, χ (V : Eˣ) =
        tracePullbackAddChar F E Ψ'.character (c * (1 - ((V : Eˣ) : E))))
      (hdom : ∀ v ∈ lattice E b,
        trace F E v ∈ lattice F (q : ℤ) ∧ norm F E v ∈ lattice F (q : ℤ))
      (hp : ∀ v ∈ lattice E b,
        tracePullbackAddChar F E Ψ'.character (Q * v) =
          Ψ'.character (O.adjustmentNorm (X : L₃) * norm F E v))
      (hZ : Z = c + algebraMap F E (O.adjustmentNorm (X : L₃)) - Q) :
      ∀ v ∈ lattice E b, ∀ V : Eˣ, (V : E) = 1 - v →
        (χ * normQuasiChar F E lambda) V =
          tracePullbackAddChar F E Ψ'.character (Z * v) := by
    intro v hv V hV
    have hVs : V ∈ unitFiltration E s := by
      obtain ⟨s', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
      rw [mem_unitFiltration_succ_iff_sub_mem_lattice, hV, sub_sub_cancel_left]
      exact neg_mem_lattice E (lattice_antitone E hsb hv)
    have hc := hcore ⟨V, hVs⟩
    simp only [hV, sub_sub_cancel] at hc
    have hnV : (normUnits F E V : F) = 1 - (trace F E v - norm F E v) := by
      rw [coe_normUnits, hV]
      have hn := wildQuadratic_norm_sub F E
        (Algebra.IsQuadraticExtension.finrank_eq_two F E) 1 v
      simp only [Units.val_one, map_one, one_pow, one_mul] at hn
      rw [hn]
      ring
    change χ V * lambda (normUnits F E V) = _
    rw [hc,
      hbase' _ (sub_mem_lattice F (hdom v hv).1 (hdom v hv).2) _ hnV,
      hZ, show (c + algebraMap F E (O.adjustmentNorm (X : L₃)) - Q) * v =
        c * v + (algebraMap F E (O.adjustmentNorm (X : L₃)) * v - Q * v) by ring,
      ContinuousAddChar.map_add_eq_mul]
    congr 1
    have hsub (w w' : E) : tracePullbackAddChar F E Ψ'.character (w - w') =
        tracePullbackAddChar F E Ψ'.character w /
          tracePullbackAddChar F E Ψ'.character w' :=
      (tracePullbackAddChar F E Ψ'.character).toAddChar.map_sub_eq_div w w'
    rw [hsub, hp v hv, tracePullbackAddChar_apply]
    have ht : trace F E (algebraMap F E (O.adjustmentNorm (X : L₃)) * v) =
        O.adjustmentNorm (X : L₃) * trace F E v := by
      simpa [Algebra.smul_def] using
        (trace F E).map_smul (O.adjustmentNorm (X : L₃)) v
    rw [ht, mul_sub]
    exact Ψ'.character.toAddChar.map_sub_eq_div _ _
  refine ⟨α', X, H', hC, hN₁, hN₂, I, ?_, ?_⟩
  · apply chart L₁ χ₁ (norm L₁ K O.Y) (O.firstCrossedTrace g₁ X) _
      (2 * r) _ (by omega) (by omega) H'.2.1
    · simpa only [hqcast] using hdom₁
    · intro v hv
      exact crossed L₁ _ _ v (a : ℤ) H'.1.first_phase (hdepth₁ v hv).1
        I.first_weighted_norm (hdepth₁ v hv).2
    · exact I.first_norm
  · apply chart L₂ χ₂ (norm L₂ K O.Y) (O.secondCrossedTrace g₂ X) _
      (a + r) _ (by omega) (by push_cast; omega) H'.2.2.1
    · simpa only [hqcast] using hdom₂
    · intro v hv
      exact crossed L₂ _ _ v (r : ℤ) H'.1.second_phase (hdepth₂ v hv).1
        I.second_weighted_norm (hdepth₂ v hv).2
    · exact I.second_norm

end HigherStationary

section HigherComparison

variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  [IsKleinFour Gal(K/F)] {L₁ L₂ L₃ : IntermediateField F K}

attribute [local instance] Basic.intermediateFieldValuativeRel
  Basic.intermediateFieldTopology Basic.intermediateField_localField
  Basic.intermediateField_lowerValuativeExtension Basic.intermediateField_upperValuativeExtension

variable [Algebra.IsQuadraticExtension F L₁] [Algebra.IsQuadraticExtension F L₂]
  [Algebra.IsQuadraticExtension F L₃]
  [Algebra.IsQuadraticExtension L₁ K] [Algebra.IsQuadraticExtension L₂ K]
  [Algebra.IsQuadraticExtension L₃ K]
  [PrimeCyclicExtension F L₁] [PrimeCyclicExtension F L₂]
  [PrimeCyclicExtension F L₃]
  {a r : ℕ} {x : L₁} {y : L₂} {z : L₃} {f g d : F}

set_option maxHeartbeats 1600000 in
/-- **Paper Theorem 13.13 (`D:NM:higher`).** The complete local-constant
products agree for every realized higher family, including `h = a`.

The core conductors, charts, common norm pullback and corrected restriction
are the conclusions of `twist`; the origin and lower formulas have the
constructors `dyadicNonmaximal_origin_data_from_alignment` and
`lowerCharacters`. All stationary data for the
given higher twist are constructed by `higher_stationary` inside the proof.
The original lower trace norms are retained. The final additive argument
is `-E₂(C) + traceNormIncrement X`, with no triviality assumption on the
increment. FML's canonical `localConstant` is used for arbitrary continuous
quasi-characters, without a unitarity hypothesis. -/
theorem higher
    (e : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (ht₁ : PrimeCyclicExtension.IsLowerBreak F L₁ (2 * a - 1))
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F L₂ (2 * r - 1))
    (ht₃ : PrimeCyclicExtension.IsLowerBreak F L₃ (2 * r - 1))
    (hres₁ : residueDegree F L₁ = 1) (hres₂ : residueDegree F L₂ = 1)
    (hres₃ : residueDegree F L₃ = 1)
    (hres₁K : residueDegree L₁ K = 1) (hres₂K : residueDegree L₂ K = 1)
    (hres₃K : residueDegree L₃ K = 1)
    (O : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (g₁ : Gal(K/L₁)) (hg₁ : g₁ ≠ 1) (g₂ : Gal(K/L₂)) (hg₂ : g₂ ≠ 1)
    (q₃ : Gal(L₃/F)) (hq₃ : q₃ ≠ 1)
    (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂) (ω₃ : NormCharacter F L₃)
    (hω₁ : ω₁ ≠ 1) (hω₂ : ω₂ ≠ 1) (hω₃ : ω₃ ≠ 1)
    (ψ : LocalAddCharData F) (α : Fˣ)
    (χ₁ : ContinuousQuasiChar L₁) (χ₂ : ContinuousQuasiChar L₂)
    (χ₃ : ContinuousQuasiChar L₃)
    (hc₁ : IsMultiplicativeConductor L₁ χ₁ (4 * r - 1))
    (hc₂ : IsMultiplicativeConductor L₂ χ₂ (2 * a + 2 * r - 1))
    (lambda : ContinuousQuasiChar F) (h : ℕ) (hah : a ≤ h)
    (hn : multiplicativeConductorExponent F lambda = 2 * r + h)
    (hcomp : normQuasiChar L₁ K (χ₁ * normQuasiChar F L₁ lambda) =
      normQuasiChar L₂ K (χ₂ * normQuasiChar F L₂ lambda))
    (hdet : Characters.restrictQuasiChar F L₁ (χ₁ * normQuasiChar F L₁ lambda) * ω₁.1 =
      Characters.restrictQuasiChar F L₂ (χ₂ * normQuasiChar F L₂ lambda) * ω₂.1) :
    let β₁ := normUnits F L₁ (Units.mk0 (trace L₁ K O.Y) O.upperTraces_ne_zero.1)
    let β₂ := normUnits F L₂ (Units.mk0 (trace L₂ K O.Y) O.upperTraces_ne_zero.2.1)
    let β₃ := normUnits F L₃ (Units.mk0 (trace L₃ K O.Y) O.upperTraces_ne_zero.2.2)
    NormalizationFormulas F L₁ L₂ L₃ a r ω₁ ω₂ ω₃ ψ β₁ β₂ β₃
      (norm L₁ K O.Y) (norm L₂ K O.Y) (norm L₃ K O.Y) χ₁ χ₂ χ₃ α →
    LanglandsFirstMainLemma.localConstant L₁ (χ₁ * normQuasiChar F L₁ lambda)
        (tracePullbackAddChar F L₁ ψ.character) *
      LanglandsFirstMainLemma.localConstant F ω₁.1 ψ.character =
    LanglandsFirstMainLemma.localConstant L₂ (χ₂ * normQuasiChar F L₂ lambda)
        (tracePullbackAddChar F L₂ ψ.character) *
      LanglandsFirstMainLemma.localConstant F ω₂.1 ψ.character := by
  dsimp only
  intro H
  obtain ⟨α', X, H', hC, hN₁, hN₂, I, hs₁, hs₂⟩ :=
    higher_stationary e ha har hre htwo ht₁ ht₂ ht₃ hres₁ hres₂ hres₃
      hres₁K hres₂K hres₃K O g₁ hg₁ g₂ hg₂ q₃ hq₃ ω₁ ω₂ ω₃ hω₃
      ψ α χ₁ χ₂ χ₃ lambda h hah hn H
  obtain ⟨hm₁, hm₂, hmω₁, hmω₂⟩ := higher_conductors ha har h hah ht₁ ht₂
    hres₁ hres₂ χ₁ χ₂ hc₁ hc₂ lambda hn ω₁ ω₂ hω₁ hω₂
  let C : Kˣ := Units.mk0 (O.adjustedOrigin (X : L₃)) hC
  let Ψ := scaleAddCharData F ψ α'
  -- Choose the inverse of the actual raw covector as the admissible
  -- denominator. Its stationary numerator is literally one, so the
  -- pinned FML even formula has no residual sum or representative choice.
  have even (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
      [IsNonarchimedeanLocalField E]
      (χ : LocalQuasiCharData E) (ψE : LocalAddCharData E)
      (b : ℕ) (hb : 0 < b) (hm : χ.conductor = 2 * b)
      (Z : Eˣ)
      (hZ : ord E (Z : E) = ((-ψE.conductor - 2 * (b : ℤ) : ℤ) : WithTop ℤ))
      (hs : ∀ v ∈ lattice E (b : ℤ), ∀ V : Eˣ, (V : E) = 1 - v →
        χ.character V = ψE.character ((Z : E) * v)) :
      LanglandsFirstMainLemma.localConstant E χ.character ψE.character =
        (χ.character ((-Z)⁻¹) : ℂ) * (ψE.character (-(Z : E)) : ℂ) := by
    let Γ : AdmissibleGamma E χ ψE := ⟨(-Z)⁻¹, by
      rw [Units.val_inv_eq_inv_val, Units.val_neg, ord_inv, ord_neg, hZ, hm]
      exact_mod_cast (show -(-ψE.conductor - 2 * (b : ℤ)) =
        2 * (b : ℤ) + ψE.conductor by ring)⟩
    let hr := lamprechtFormula_stationaryDepth E χ b 0 (by omega)
      (by omega) (by omega)
    let c : lattice E ((χ.conductor : ℤ) - χ.conductor) := ⟨1, by simp⟩
    have hc : latticeQuotientMk E (sub_le_sub_left hr.int_le_conductor (χ.conductor : ℤ)) c =
        stationaryNumeratorClass E χ ψE (χ.conductor : ℤ) hr Γ Γ.property := by
      apply (latticeQuotientMk_eq_stationaryNumeratorClass_iff E χ ψE
        (χ.conductor : ℤ) hr Γ Γ.property c).mpr
      intro v
      have hv := hs (-(v : E)) (neg_mem_lattice E v.property)
        (positiveUnitOfLattice E hr.pos v) (by
          simp only [coe_positiveUnitOfLattice, sub_neg_eq_add])
      rw [hv]
      congr 1
      simp [c, Γ, Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_comm]
    have hrep : lamprechtStationaryRepresentativeUnit E χ ψE hr Γ c hc = 1 := by
      apply Units.ext
      rfl
    rw [localConstant_isDeltaFinite E χ ψE Γ,
      lamprechtEven E χ ψE b hm (by omega) Γ c hc]
    change (χ.character ((-Z)⁻¹) : ℂ) * lamprechtElementaryFactor E χ ψE Γ
      (lamprechtStationaryRepresentativeUnit E χ ψE hr Γ c hc) = _
    rw [hrep, lamprechtElementaryFactor]
    simp only [map_one, Units.val_one, inv_one, mul_one]
    simp [Γ, Units.val_inv_eq_inv_val]
  -- The edge calculation uses each original lower norm coefficient. The
  -- two fields share this calculation but keep their separate conductors.
  have edge (E : IntermediateField F K)
      [Algebra.IsQuadraticExtension F E] [PrimeCyclicExtension F E]
      (q b : ℕ) (hq : 1 ≤ q) (hb : 0 < b) (hqb : q + b = 2 * r + h)
      (ht : PrimeCyclicExtension.IsLowerBreak F E (2 * q - 1))
      (hres : residueDegree F E = 1)
      (θ : ContinuousQuasiChar E) (ω : NormCharacter F E)
      (hmθ : IsMultiplicativeConductor E θ (2 * b))
      (hmω : IsMultiplicativeConductor F ω.1 (2 * q))
      (β : Fˣ) (hβ : ord F (β : F) = ((2 * (r : ℤ) - 2 * (q : ℤ) : ℤ) : WithTop ℤ))
      (hωβ : ω.1 β = 1)
      (hN : ord E (norm E K (C : K)) = ((-2 * (h : ℤ) : ℤ) : WithTop ℤ))
      (hsθ : ∀ v ∈ lattice E (b : ℤ), ∀ V : Eˣ, (V : E) = 1 - v →
        θ V = tracePullbackAddChar F E Ψ.character (norm E K (C : K) * v))
      (hsω : ∀ v ∈ lattice F (q : ℤ), ∀ V : Fˣ, (V : F) = 1 - v →
        ω.1 V = Ψ.character ((β : F) * v)) :
      LanglandsFirstMainLemma.localConstant E θ (tracePullbackAddChar F E ψ.character) *
        LanglandsFirstMainLemma.localConstant F ω.1 ψ.character =
      ((Characters.restrictQuasiChar F E θ * ω.1) (-α'⁻¹) : ℂ) *
        (normQuasiChar E K θ C : ℂ)⁻¹ *
        (Ψ.character (-trace F E (norm E K (C : K)) - (β : F)) : ℂ) := by
    let θD : LocalQuasiCharData E := ⟨θ, 2 * b, hmθ⟩
    let ωD : LocalQuasiCharData F := ⟨ω.1, 2 * q, hmω⟩
    let ψE : LocalAddCharData E := ⟨tracePullbackAddChar F E ψ.character,
      2 * ψ.conductor + 2 * (q : ℤ), even_trace_conductor F E q hq ht hres
        ψ.character ψ.conductor ψ.isConductor⟩
    let αE := Units.map (algebraMap F E).toMonoidHom α'
    let Z := normUnits E K C
    have hram : ramificationIndex F E = 2 := by
      have hh := finrank_eq_ramificationIndex_mul_residueDegree F E
      rw [Algebra.IsQuadraticExtension.finrank_eq_two F E, hres, mul_one] at hh
      exact hh.symm
    have htα (v : E) : ψE.character ((αE : E) * v) =
        tracePullbackAddChar F E Ψ.character v := by
      change ψ.character (trace F E (algebraMap F E (α' : F) * v)) =
        ψ.character ((α' : F) * trace F E v)
      congr 1
      simpa [Algebra.smul_def] using (trace F E).map_smul (α' : F) v
    have hrawθ : ord E ((αE * Z : Eˣ) : E) =
        ((-ψE.conductor - 2 * (b : ℤ) : ℤ) : WithTop ℤ) := by
      rw [Units.val_mul, coe_normUnits]
      change ord E (algebraMap F E (α' : F) * norm E K (C : K)) = _
      rw [ord_mul, ord_algebraMap, hram, H'.1.normalizing_order, hN,
        ← WithTop.coe_nsmul, ← WithTop.coe_add]
      congr 1
      dsimp only [ψE]
      simp only [nsmul_eq_mul]
      have hqbZ : (q : ℤ) + b = 2 * (r : ℤ) + h := by exact_mod_cast hqb
      omega
    have hrawω : ord F ((α' * β : Fˣ) : F) =
        ((-ψ.conductor - 2 * (q : ℤ) : ℤ) : WithTop ℤ) := by
      rw [Units.val_mul, ord_mul, H'.1.normalizing_order, hβ, ← WithTop.coe_add]
      congr 1
      ring
    have hfθ := even E θD ψE b hb rfl (αE * Z) hrawθ (by
      intro v hv V hV
      rw [show θD.character V = θ V from rfl, hsθ v hv V hV]
      simpa only [Units.val_mul, Z, coe_normUnits, mul_assoc] using (htα ((Z : E) * v)).symm)
    have hfω := even F ωD ψ q (by omega) rfl (α' * β) hrawω (by
      intro v hv V hV
      exact (hsω v hv V hV).trans (by
        simp only [Ψ, scaleAddCharData_character_apply, Units.val_mul, mul_assoc]))
    have huE : (-(αE * Z))⁻¹ =
        Units.map (algebraMap F E).toMonoidHom (-α'⁻¹) * Z⁻¹ := by
      simp [αE, mul_comm]
    have huF : (-(α' * β))⁻¹ = -α'⁻¹ * β⁻¹ := by simp [mul_comm]
    have hmult : (θD.character ((-(αE * Z))⁻¹) : ℂ) *
        (ωD.character ((-(α' * β))⁻¹) : ℂ) =
        ((Characters.restrictQuasiChar F E θ * ω.1) (-α'⁻¹) : ℂ) *
          (normQuasiChar E K θ C : ℂ)⁻¹ := by
      change (θ ((-(αE * Z))⁻¹) : ℂ) * (ω.1 ((-(α' * β))⁻¹) : ℂ) = _
      rw [huE, huF, map_mul, map_mul, map_inv, map_inv, hωβ]
      change (θ (Units.map (algebraMap F E).toMonoidHom (-α'⁻¹)) * (θ Z)⁻¹ : ℂˣ) *
        (ω.1 (-α'⁻¹) * (1 : ℂˣ)⁻¹ : ℂˣ) =
        (θ (Units.map (algebraMap F E).toMonoidHom (-α'⁻¹)) * ω.1 (-α'⁻¹) : ℂˣ) *
          (θ Z : ℂ)⁻¹
      push_cast
      ring
    have hadd : (ψE.character (-((αE * Z : Eˣ) : E)) : ℂ) *
        (ψ.character (-((α' * β : Fˣ) : F)) : ℂ) =
        (Ψ.character (-trace F E (norm E K (C : K)) - (β : F)) : ℂ) := by
      have he : ψE.character (-((αE * Z : Eˣ) : E)) =
          Ψ.character (-trace F E (norm E K (C : K))) := by
        rw [Units.val_mul, ← mul_neg, htα, tracePullbackAddChar_apply, map_neg]
        rfl
      rw [he]
      have hf : ψ.character (-((α' * β : Fˣ) : F)) = Ψ.character (-(β : F)) := by
        simp only [Ψ, scaleAddCharData_character_apply, Units.val_mul, mul_neg]
      rw [hf, ← Units.val_mul, ← ContinuousAddChar.map_add_eq_mul]
      simp only [sub_eq_add_neg]
    change LanglandsFirstMainLemma.localConstant E θD.character ψE.character *
      LanglandsFirstMainLemma.localConstant F ωD.character ψ.character = _
    rw [hfθ, hfω]
    calc
      _ = ((θD.character ((-(αE * Z))⁻¹) : ℂ) *
            (ωD.character ((-(α' * β))⁻¹) : ℂ)) *
          ((ψE.character (-((αE * Z : Eˣ) : E)) : ℂ) *
            (ψ.character (-((α' * β : Fˣ) : F)) : ℂ)) := by ring
      _ = _ := by rw [hmult, hadd]
  have hb₁ : ((2 * r + h - a : ℕ) : ℤ) = 2 * (r : ℤ) + h - a := by omega
  have hb₂ : ((r + h : ℕ) : ℤ) = (r : ℤ) + h := by omega
  have hf₁ := edge L₁ a (2 * r + h - a) ha (by omega) (by omega) ht₁ hres₁
    _ ω₁ hm₁ hmω₁ _ (by
      change ord F (norm F L₁ (trace L₁ K O.Y)) = _
      rw [O.lowerNormTrace₁_order]
      congr 1
      ring) H'.1.first_norm_value hN₁
      (by simpa only [hb₁, Ψ, C, Units.val_mk0] using hs₁) H'.1.first_formula
  have hf₂ := edge L₂ r (r + h) (by omega) (by omega) (by omega) ht₂ hres₂
    _ ω₂ hm₂ hmω₂ _ (by
      change ord F (norm F L₂ (trace L₂ K O.Y)) = _
      rw [O.lowerNormTrace₂_order]
      simp) H'.1.second_norm_value hN₂
      (by simpa only [hb₂, Ψ, C, Units.val_mk0] using hs₂) H'.1.second_formula
  have hphase := higher_common_phase O g₁ g₂ q₃ X I Ψ.character
  rw [hf₁, hf₂, hdet, hcomp]
  congr 2
  simpa only [C, Units.val_mk0, coe_normUnits] using hphase.1.trans hphase.2.symm

end HigherComparison

end

end LanglandsSecondMainLemma.Dyadic.Nonmaximal
