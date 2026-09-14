import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Parameters.FourFactors
import LanglandsSecondMainLemma.Odd.Total.PowerNorm

/-!
# Odd / Transition / Denominators

Paper Lemma 9.21 (`O:T:denominator`), corrected source lines 4438–4550.
The denominators are the actual norm `P = N(1+u a)` and `D = 1+u^p N(a)`.
Their unit orders and their congruence are proved from the positive transition
depth and FML's strong symmetric bound. Both outer weights are retained.
The final theorem uses the actual diamond, symmetric coefficient and trace;
neither a stationary model nor character cancellation is an input.
-/

namespace LanglandsSecondMainLemma.Odd.Transition

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem weighted_depths (p t delta m : ℤ) (hp : 3 ≤ p)
    (hd : 0 ≤ delta) (hm : 0 ≤ m) (hmt : t < p * m) :
    let ell := m + ((p - 2) * t + (p - 1) * (delta + 1)) / p
    1 + t + delta ≤ (p - 2) * m + (p - 1) * delta + ell ∧
    1 + t + delta ≤ (p - 1) * m - t + (p - 1) * (m + delta) + ell := by
  dsimp only
  have hp0 : 0 < p := by omega
  have hdelta : 0 ≤ (p * (p - 1) - 1) * delta :=
    mul_nonneg (by nlinarith) hd
  have hfirst : 0 ≤ (p - 3) * (p * m) :=
    mul_nonneg (by omega) (mul_nonneg hp0.le hm)
  have hgap : (p + 2) * (t + 1) ≤ (p + 2) * (p * m) :=
    mul_le_mul_of_nonneg_left (by omega) (by omega)
  constructor
  · have h : 1 + t + delta - ((p - 2) * m + (p - 1) * delta + m) ≤
        ((p - 2) * t + (p - 1) * (delta + 1)) / p := by
      rw [Int.le_ediv_iff_mul_le hp0]
      nlinarith
    linarith
  · have h : 1 + t + delta - ((p - 1) * m - t + (p - 1) * (m + delta) + m) ≤
        ((p - 2) * t + (p - 1) * (delta + 1)) / p := by
      rw [Int.le_ediv_iff_mul_le hp0]
      nlinarith
    linarith

/-- The two actual denominators and their inverse powers have the same
integer precision supplied by the nonterminal norm coefficients. -/
theorem denominator_congruences
    (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Free F E] [Module.Finite F E] [PrimeCyclicExtension F E]
    {p t delta m : ℕ} (hp : 2 < p) (ht : 0 < t)
    (hdegree : Module.finrank F E = p) (hres : residueDegree F E = 1)
    (hbreak : PrimeCyclicExtension.IsLowerBreak F E (t + delta))
    (hmt : t < p * m) (u : F) (a : E)
    (hu : ord F u = ((m : ℤ) : WithTop ℤ))
    (ha : ord E a = ((-(t : ℤ) : ℤ) : WithTop ℤ)) :
    let C := 1 + algebraMap F E u * a
    let D := 1 + u ^ p * norm F E a
    let P := norm F E C
    let ell := (m : ℤ) +
      (((p : ℤ) - 2) * t + ((p : ℤ) - 1) * (delta + 1)) / p
    ord E C = 0 ∧ ord F D = 0 ∧ ord F P = 0 ∧
      P - D ∈ lattice F ell ∧
      P⁻¹ - D⁻¹ ∈ lattice F ell ∧
      P⁻¹ ^ 2 - D⁻¹ ^ 2 ∈ lattice F ell := by
  dsimp only
  let q : ℤ := (p : ℤ) * m - t
  let ell : ℤ := (m : ℤ) +
    (((p : ℤ) - 2) * t + ((p : ℤ) - 1) * (delta + 1)) / p
  have hpZ : 0 < (p : ℤ) := by omega
  have hq : 0 < q := by
    have h : (t : ℤ) < (p : ℤ) * m := by exact_mod_cast hmt
    dsimp only [q]
    omega
  have he : ramificationIndex F E = p := by
    simpa only [hdegree, hres, mul_one] using
      (finrank_eq_ramificationIndex_mul_residueDegree F E).symm
  have hz : ord E (algebraMap F E u * a) = (q : WithTop ℤ) := by
    rw [ord_mul, ord_algebraMap, he, hu, ha]
    simp only [← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul]
    rfl
  have hC : ord E (1 + algebraMap F E u * a) = 0 := by
    rw [(ord E).map_add_eq_of_lt_left (by simpa only [ord_one, hz, WithTop.coe_pos] using hq), ord_one]
  have hA : ord F (norm F E a) = ((-(t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_norm, hres, one_nsmul, ha]
  have hsmall : ord F (u ^ p * norm F E a) = (q : WithTop ℤ) := by
    rw [ord_mul, ord_pow, hu, hA]
    simp only [← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul]
    rfl
  have hD : ord F (1 + u ^ p * norm F E a) = 0 := by
    rw [(ord F).map_add_eq_of_lt_left (by simpa only [ord_one, hsmall, WithTop.coe_pos] using hq), ord_one]
  have hP : ord F (norm F E (1 + algebraMap F E u * a)) = 0 := by
    rw [ord_norm, hres, one_nsmul, hC]
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have hchar := residueCharacteristic_eq_degree_of_positive_isLowerBreak F E
    hbreak (by omega) pi hpi hgen
  have htrace := traceIdealLowerBound_of_integralGenerator F E hbreak hres pi hpi hgen
  have hsym := wild_symmetric_bound F E (t + delta) hbreak (by omega) hchar
    (he.trans hdegree.symm) htrace q hz.ge
  have hcoeff : ∀ j : ℕ, 1 ≤ j → j < p →
      elementarySymmetric F E j (algebraMap F E u * a) ∈ lattice F ell := by
    intro j hj hjp
    apply (mem_lattice F).2
    have hjZ : 1 ≤ (j : ℤ) := by omega
    have hnum : q + ((p : ℤ) - 1) * ((t : ℤ) + delta + 1) ≤
        (j : ℤ) * q + ((p : ℤ) - 1) * ((t : ℤ) + delta + 1) := by
      nlinarith
    have hfloor := Int.ediv_le_ediv hpZ hnum
    have heq : (q + ((p : ℤ) - 1) * ((t : ℤ) + delta + 1)) / p = ell := by
      have : q + ((p : ℤ) - 1) * ((t : ℤ) + delta + 1) =
          (m : ℤ) * p + (((p : ℤ) - 2) * t + ((p : ℤ) - 1) * (delta + 1)) := by
        dsimp only [q]
        ring
      rw [this, Int.add_ediv_of_dvd_left (dvd_mul_left _ _), Int.mul_ediv_cancel _ hpZ.ne']
    rw [heq] at hfloor
    refine (WithTop.coe_le_coe.mpr hfloor).trans ?_
    simpa only [hdegree, wildDifferentContribution, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ p),
      Nat.cast_add, Nat.cast_one] using hsym.1 hj (by omega)
  have hdiff : norm F E (1 + algebraMap F E u * a) -
      (1 + u ^ p * norm F E a) ∈ lattice F ell := by
    have hsum : (∑ j ∈ Finset.range (p - 1),
        elementarySymmetric F E (j + 1) (algebraMap F E u * a)) ∈ lattice F ell := by
      apply sum_mem_lattice F
      intro j hj
      exact hcoeff (j + 1) (by omega) (by have := Finset.mem_range.mp hj; omega)
    rw [norm_one_add_eq_one_add_sum_elementarySymmetric, hdegree,
      show p = p - 1 + 1 by omega, Finset.sum_range_succ]
    rw [show p - 1 + 1 = p by omega, ← hdegree, elementarySymmetric_finrank,
      map_mul, LanglandsFirstMainLemma.norm_algebraMap, hdegree]
    convert hsum using 1
    abel
  have hc : CongruentAtDepth ell (norm F E (1 + algebraMap F E u * a))
      (1 + u ^ p * norm F E a) :=
    (congruentAtDepth_iff_sub_mem_lattice F _ _ _).2 hdiff
  have hi := hc.inv hP hD
  have hiP : 0 ≤ ord F (norm F E (1 + algebraMap F E u * a))⁻¹ := by simp [hP]
  have hiD : 0 ≤ ord F (1 + u ^ p * norm F E a)⁻¹ := by simp [hD]
  have hs := hi.mul hiP hiD hi
  exact ⟨hC, hD, hP, hdiff,
    (congruentAtDepth_iff_sub_mem_lattice F _ _ _).1 hi,
    (congruentAtDepth_iff_sub_mem_lattice F _ _ _).1 (by simpa only [pow_two] using hs)⟩

/-- Multiplication by the two literal outer weights reaches the additive
conductor ideal; no assertion about a character kernel is used. -/
private theorem weighted_mem
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {p t delta m : ℕ} (hp : 2 < p) (hmt : t < p * m)
    {u A₀ H J z : F}
    (hu : ord F u = ((m : ℤ) : WithTop ℤ))
    (hA : ord F A₀ = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hH : ((((p : ℤ) - 1) * delta : ℤ) : WithTop ℤ) ≤ ord F H)
    (hJ : ((((p : ℤ) - 1) * (m + delta) : ℤ) : WithTop ℤ) ≤ ord F J)
    (hz : z ∈ lattice F ((m : ℤ) +
      (((p : ℤ) - 2) * t + ((p : ℤ) - 1) * (delta + 1)) / p)) :
    u ^ (p - 2) * H * z ∈ lattice F (1 + (t : ℤ) + delta) ∧
    u ^ (p - 1) * A₀ * J * z ∈ lattice F (1 + (t : ℤ) + delta) := by
  have harith := weighted_depths (p : ℤ) t delta m (by omega)
    (by omega) (by omega) (by exact_mod_cast hmt)
  have hpow (n : ℕ) : ord F (u ^ n) = (((n : ℤ) * m : ℤ) : WithTop ℤ) := by
    simp only [ord_pow, hu, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have hweight₁ : u ^ (p - 2) * H ∈
      lattice F (((p : ℤ) - 2) * m + ((p : ℤ) - 1) * delta) := by
    rw [mem_lattice, ord_mul, hpow, Nat.cast_sub (by omega : 2 ≤ p)]
    simpa only [WithTop.coe_add, Nat.cast_ofNat] using
      add_le_add (le_refl ((((p : ℤ) - 2) * m : ℤ) : WithTop ℤ)) hH
  have hweight₂ : u ^ (p - 1) * A₀ * J ∈
      lattice F (((p : ℤ) - 1) * m - t + ((p : ℤ) - 1) * (m + delta)) := by
    rw [mem_lattice, ord_mul, ord_mul, hpow, hA,
      Nat.cast_sub (by omega : 1 ≤ p)]
    simpa only [WithTop.coe_add, WithTop.coe_sub, Nat.cast_one,
      sub_eq_add_neg] using
      add_le_add (le_refl ((((p : ℤ) - 1) * m - t : ℤ) : WithTop ℤ)) hJ
  exact ⟨lattice_antitone F harith.1 (mul_mem_lattice F hweight₁ hz),
    lattice_antitone F harith.2 (mul_mem_lattice F hweight₂ hz)⟩

open private realization_tower_data from
  LanglandsSecondMainLemma.Odd.Models.Realization

section Diamond

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]
  {p : ℕ} (hp : p.Prime)
  (hG : Nonempty
    (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
  (R : Total.OddTotalBreakData (F := F) (K := K) hp hG)

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

local notation "B₁" => R.B₁
local notation "B₂" => R.B₂

local instance : PrimeCyclicExtension B₁ K :=
  PrimeCyclicExtension.ofCyclicPrimeExtension B₁ K
    (Basic.intermediateField_tower_compatible hp hG B₁ R.degree_B₁).2.2.2.2.2.2.2.2.2.2.2.2
local instance : PrimeCyclicExtension F B₂ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₂
    (Basic.intermediateField_tower_compatible hp hG B₂ R.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.1

set_option maxHeartbeats 600000 in
/-- **Paper Lemma 9.21 (`O:T:denominator`).**

The fields are the actual totally ramified `C_p × C_p` diamond. Here `a`
is the actual upper norm of `Delta`, `s` its negative penultimate symmetric
coefficient on the other upper edge, and `T` the actual trace of
`(Delta/w)^(p-1)`. The exact lower norm of `w` is preserved.

The conclusion includes order zero of `C`, `D` and `P`, the unweighted
norm congruence at its full integer depth, both weighted inverse-square
congruences, and the first weighted inverse-first-power congruence.
No restrictions on field characteristic or characters are needed for
these valuation statements. In the transition setup one applies this to
`u = alpha/gamma` and its already preserved exact norm choice of `w`.
In fact the inequalities also hold without the setup's `p ∤ t` condition. -/
theorem denominators
    (hres : residueDegree F K = 1)
    {m : ℕ} (hmt : R.t < p * m)
    (Delta : K) (hDelta : ord K Delta = ((-(R.t : ℤ) : ℤ) : WithTop ℤ))
    (u : Fˣ) (hu : ord F (u : F) = ((m : ℤ) : WithTop ℤ))
    (w : B₂ˣ) (hw : normUnits F B₂ w = u⁻¹) :
    let a := norm B₂ K Delta
    let A₀ := norm F B₂ a
    let C := 1 + algebraMap F B₂ (u : F) * a
    let D := 1 + (u : F) ^ p * A₀
    let P := norm F B₂ C
    let s := -elementarySymmetric B₁ K (p - 1) Delta
    let H := norm F B₁ s
    let T := trace B₁ K ((Delta / algebraMap B₂ K (w : B₂)) ^ (p - 1))
    let J := norm F B₁ T
    let ell := (m : ℤ) +
      (((p : ℤ) - 2) * R.t + ((p : ℤ) - 1) * (R.delta + 1)) / p
    ord B₂ C = 0 ∧ ord F D = 0 ∧ ord F P = 0 ∧
      P - D ∈ lattice F ell ∧
      (u : F) ^ (p - 2) * H * (P⁻¹ ^ 2 - D⁻¹ ^ 2) ∈
        lattice F (1 + (R.t₂ : ℤ)) ∧
      (u : F) ^ (p - 1) * A₀ * J * (P⁻¹ ^ 2 - D⁻¹ ^ 2) ∈
        lattice F (1 + (R.t₂ : ℤ)) ∧
      (u : F) ^ (p - 2) * H * (P⁻¹ - D⁻¹) ∈
        lattice F (1 + (R.t₂ : ℤ)) := by
  dsimp only
  obtain ⟨hd₁, hrF₁, hrK₁, _, _⟩ :=
    realization_tower_data hp hG hres B₁ R.degree_B₁
  obtain ⟨_, hrF₂, hrK₂, _, heK₂⟩ :=
    realization_tower_data hp hG hres B₂ R.degree_B₂
  have hpZ : 0 < (p : ℤ) := by have := hp.pos; omega
  have hprime : 0 < R.tPrime := by have := R.t_pos; have := R.tPrime_eq; omega
  have hbreak : PrimeCyclicExtension.IsLowerBreak B₁ K R.tPrime := R.B₁_breaks.2
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer B₁ K hrK₁
  have hchar := residueCharacteristic_eq_degree_of_positive_isLowerBreak B₁ K
    hbreak hprime pi hpi hgen
  have htrace := traceIdealLowerBound_of_integralGenerator B₁ K hbreak hrK₁ pi hpi hgen
  have heK₁ : ramificationIndex B₁ K = Module.finrank B₁ K := by
    simpa only [hrK₁, mul_one] using
      (finrank_eq_ramificationIndex_mul_residueDegree B₁ K).symm
  have hsym := wild_symmetric_bound B₁ K R.tPrime hbreak hprime hchar heK₁
    htrace (-(R.t : ℤ)) hDelta.ge
  have hfloorS : ((p : ℤ) - 1) * R.delta ≤
      (((p : ℤ) - 1) * (-(R.t : ℤ)) +
        ((p : ℤ) - 1) * ((R.tPrime : ℤ) + 1)) / p := by
    rw [Int.le_ediv_iff_mul_le hpZ, R.tPrime_eq]
    push_cast
    nlinarith
  have hs : ((((p : ℤ) - 1) * R.delta : ℤ) : WithTop ℤ) ≤
      ord B₁ (-elementarySymmetric B₁ K (p - 1) Delta) := by
    rw [ord_neg]
    refine (WithTop.coe_le_coe.mpr hfloorS).trans ?_
    simpa only [hd₁, wildDifferentContribution, Nat.cast_mul,
      Nat.cast_sub hp.one_le, Nat.cast_one, Nat.cast_add] using
      hsym.1 (show 1 ≤ p - 1 by have := R.odd_prime; omega) (by omega)
  have hwNorm : norm F B₂ (w : B₂) = (u : F)⁻¹ := by
    simpa only [coe_normUnits, Units.val_inv_eq_inv_val] using congrArg Units.val hw
  have hwOrd : ord B₂ (w : B₂) = ((-(m : ℤ) : ℤ) : WithTop ℤ) := by
    have hn := congrArg (ord F) hwNorm
    simpa only [ord_norm, hrF₂, one_nsmul, ord_inv, hu,
      WithTop.LinearOrderedAddCommGroup.coe_neg] using hn
  have harg : ord K ((Delta / algebraMap B₂ K (w : B₂)) ^ (p - 1)) =
      ((((p : ℤ) - 1) * ((p : ℤ) * m - R.t) : ℤ) : WithTop ℤ) := by
    rw [ord_pow, ord_div, ord_algebraMap, heK₂, hwOrd, hDelta]
    simp only [← WithTop.coe_nsmul, ← WithTop.LinearOrderedAddCommGroup.coe_sub, nsmul_eq_mul,
      Nat.cast_sub hp.one_le, Nat.cast_one]
    congr 1
    ring
  have hfloorT : ((p : ℤ) - 1) * (m + R.delta) ≤
      (((p : ℤ) - 1) * ((p : ℤ) * m - R.t) +
        ((p : ℤ) - 1) * ((R.tPrime : ℤ) + 1)) / p := by
    rw [Int.le_ediv_iff_mul_le hpZ, R.tPrime_eq]
    push_cast
    nlinarith
  have hT : ((((p : ℤ) - 1) * (m + R.delta) : ℤ) : WithTop ℤ) ≤
      ord B₁ (trace B₁ K ((Delta / algebraMap B₂ K (w : B₂)) ^ (p - 1))) := by
    refine (WithTop.coe_le_coe.mpr hfloorT).trans ?_
    simpa only [hd₁, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one,
      Nat.cast_add] using htrace _ _ harg.ge
  have ha : ord B₂ (norm B₂ K Delta) = ((-(R.t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_norm, hrK₂, one_nsmul, hDelta]
  have hbreak₂ : PrimeCyclicExtension.IsLowerBreak F B₂ (R.t + R.delta) := by
    rw [← R.t₂_eq]
    exact R.B₂_breaks.1
  obtain ⟨hC, hD, hP, hdiff, hi, hi₂⟩ := denominator_congruences F B₂
    (p := p) (t := R.t) (delta := R.delta) (m := m)
    R.odd_prime R.t_pos R.degree_B₂ hrF₂ hbreak₂ hmt (u : F) _ hu ha
  have hA : ord F (norm F B₂ (norm B₂ K Delta)) =
      ((-(R.t : ℤ) : ℤ) : WithTop ℤ) := by rw [ord_norm, hrF₂, one_nsmul, ha]
  have hH : ((((p : ℤ) - 1) * R.delta : ℤ) : WithTop ℤ) ≤
      ord F (norm F B₁ (-elementarySymmetric B₁ K (p - 1) Delta)) := by
    simpa only [ord_norm, hrF₁, one_nsmul] using hs
  have hJ : ((((p : ℤ) - 1) * (m + R.delta) : ℤ) : WithTop ℤ) ≤
      ord F (norm F B₁
        (trace B₁ K ((Delta / algebraMap B₂ K (w : B₂)) ^ (p - 1)))) := by
    simpa only [ord_norm, hrF₁, one_nsmul] using hT
  have hweights₂ := weighted_mem F R.odd_prime hmt hu hA hH hJ hi₂
  have hweights₁ := weighted_mem F R.odd_prime hmt hu hA hH hJ hi
  refine ⟨hC, hD, hP, hdiff, ?_, ?_, ?_⟩
  · simpa only [R.t₂_eq, Nat.cast_add, add_assoc] using hweights₂.1
  · simpa only [R.t₂_eq, Nat.cast_add, add_assoc] using hweights₂.2
  · simpa only [R.t₂_eq, Nat.cast_add, add_assoc] using hweights₁.1

end Diamond

end

end LanglandsSecondMainLemma.Odd.Transition
