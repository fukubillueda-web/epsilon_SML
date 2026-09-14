import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsSecondMainLemma.Odd.Transition.Denominators
import LanglandsSecondMainLemma.Finite.Interpolation

/-!
# Odd / Transition / Rational

Paper Lemma 9.22 (`O:T:rational`), corrected source lines 4438–4617.
The exact rational identities are separated from their weighted valuation
bounds. The final declaration uses the actual totally ramified diamond
and preserves the full gamma-conductor `1 + t₂ + p m`.
-/

open LanglandsFirstMainLemma
open scoped BigOperators

namespace LanglandsSecondMainLemma.Odd.Transition
noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The three weighted error depths in the proof of `O:T:rational`. -/
private theorem rational_depths (p t d m : ℤ) (hp : 3 ≤ p) (ht : 1 ≤ t)
    (hd : 0 ≤ d) (hm : 1 ≤ m) :
    let b := (p - 1) * (t + d)
    let r := (p - 1) * m
    let n := 1 + t + d + p * m
    n ≤ b + 2 * r ∧ n ≤ p * r + b + r ∧
      n ≤ b + p * m - t + r := by
  dsimp only
  have h₁ : 0 ≤ (p - 3) * t := mul_nonneg (by omega) (by omega)
  have h₂ : 0 ≤ (p - 2) * d := mul_nonneg (by omega) hd
  have h₃ : 1 ≤ (p - 2) * m := by nlinarith
  have h₄ : 2 ≤ (p - 1) * m := by nlinarith
  have h₅ : 0 ≤ (p - 2) * ((p - 1) * m) :=
    mul_nonneg (by omega) (by positivity)
  constructor
  · nlinarith
  constructor <;> nlinarith

section Local
variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
private theorem lattice_pow {x : E} {r : ℤ} (hx : x ∈ lattice E r) (i : ℕ) :
    x ^ i ∈ lattice E ((i : ℤ) * r) := by
  rw [mem_lattice, ord_pow]
  simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using nsmul_le_nsmul_right ((mem_lattice E).1 hx) i
private theorem lattice_div_unit {x y : E} {r : ℤ} (hx : x ∈ lattice E r)
    (hy : ord E y = 0) : x / y ∈ lattice E r := by
  rw [mem_lattice, ord_div, hy, sub_zero]
  exact hx
private theorem lattice_mul_integral {x y : E} {r : ℤ} (hx : x ∈ lattice E r)
    (hy : 0 ≤ ord E y) : x * y ∈ lattice E r := by
  simpa only [add_zero] using mul_mem_lattice E hx ((mem_lattice E).2 hy)
private theorem ne_zero_of_ord_zero {x : E} (hx : ord E x = 0) : x ≠ 0 := by
  intro h
  simp [h] at hx

/-- The mixed-characteristic binomial error, also valid when the prime is zero. -/
private theorem binomial_error {p : ℕ} (hp : p.Prime) {b q : ℤ}
    (hq : 0 ≤ q) (hb : (p : E) ∈ lattice E b)
    {z : E} (hz : z ∈ lattice E q) :
    (1 + z) ^ p - (1 + z ^ p) ∈ lattice E (b + q) := by
  have hexp := (Commute.all z (1 : E)).add_pow_prime_pow_eq' hp 1
  norm_num at hexp
  have hsum : (∑ j ∈ Finset.Ioo 0 p,
      z ^ j * (1 : E) ^ (p - j) * ((Nat.choose p j / p : ℕ) : E)) ∈ lattice E q := by
    apply sum_mem_lattice E
    intro j hj
    have hjpos := (Finset.mem_Ioo.mp hj).1
    have hzj := lattice_antitone E (show q ≤ (j : ℤ) * q by
      have : 1 ≤ (j : ℤ) := by omega
      nlinarith) (lattice_pow E hz j)
    simp only [one_pow, mul_one]
    exact lattice_mul_integral E hzj ((ord_nonneg_iff_mem_integer E _).2
      (show (((Nat.choose p j / p : ℕ) : E)) ∈ ringOfIntegers E from
        (Nat.cast (Nat.choose p j / p) : ringOfIntegers E).property))
  have hmul := mul_mem_lattice E hb hsum
  convert hmul using 1
  simp only [one_pow, mul_one] at hexp ⊢
  linear_combination hexp
end Local

section Algebra
variable {E : Type*} [Field E]
private theorem sum_reversal {p : ℕ} (hp : 2 < p) (G k : E) :
    (∑ i ∈ Finset.range (p - 2), G * k ^ (p - (i + 1)) / (i + 1 : ℕ)) =
      ∑ j ∈ Finset.range (p - 2), G * k ^ (j + 2) / (p - (j + 2) : ℕ) := by
  rw [← Finset.sum_range_reflect (fun i => G * k ^ (p - (i + 1)) / (i + 1 : ℕ))]
  apply Finset.sum_congr rfl
  intro j hj
  have hjp := Finset.mem_range.mp hj
  rw [show p - 2 - 1 - j + 1 = p - (j + 2) by omega,
    show p - (p - (j + 2)) = j + 2 by omega]

private theorem positive_log_split {p : ℕ} (hp : 2 < p) (k : E) :
    (∑ j ∈ Finset.range (p - 1), k ^ (j + 1) / (j + 1 : ℕ)) =
      k + ∑ j ∈ Finset.range (p - 2), k ^ (j + 2) / (j + 2 : ℕ) := by
  conv_lhs => rw [show p - 1 = (p - 2) + 1 by omega, Finset.sum_range_succ']
  simp only [zero_add, pow_one, Nat.cast_one, div_one, Nat.add_assoc]
  rw [add_comm]

/-- Reindex the complete first sum without changing its terminal coefficient. -/
private theorem rational_reversal {p : ℕ} (hp : 2 < p) (G k : E)
    (hunit : ∀ j : ℕ, 0 < j → j < p → (j : E) ≠ 0) :
    -G * k + (∑ i ∈ Finset.range (p - 2), G * k ^ (p - (i + 1)) / (i + 1 : ℕ)) +
        G * (∑ j ∈ Finset.range (p - 1), k ^ (j + 1) / (j + 1 : ℕ)) =
      ∑ j ∈ Finset.range (p - 2),
        (p : E) * G * k ^ (j + 2) / ((j + 2 : ℕ) * (p - (j + 2) : ℕ)) := by
  rw [sum_reversal hp, positive_log_split hp, mul_add]
  have heq (j : ℕ) (hj : j ∈ Finset.range (p - 2)) :
      G * k ^ (j + 2) / (p - (j + 2) : ℕ) + G * (k ^ (j + 2) / (j + 2 : ℕ)) =
        (p : E) * G * k ^ (j + 2) / ((j + 2 : ℕ) * (p - (j + 2) : ℕ)) := by
    have hjp := Finset.mem_range.mp hj
    have h₁ := hunit (j + 2) (by omega) (by omega)
    have h₂ := hunit (p - (j + 2)) (by omega) (by omega)
    have hc : (p : E) = (j + 2 : ℕ) + (p - (j + 2) : ℕ) := by
      rw [← Nat.cast_add, Nat.add_sub_of_le (by omega)]
    rw [hc]
    field_simp
  calc
    _ = (∑ j ∈ Finset.range (p - 2), G * k ^ (j + 2) / (p - (j + 2) : ℕ)) +
        G * (∑ j ∈ Finset.range (p - 2), k ^ (j + 2) / (j + 2 : ℕ)) := by ring
    _ = _ := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl heq

/-- Paper identity `O:T:FGexact`, with `C` denoting the full power `C^p`. -/
private theorem FG_exact (P C Q q eta : E) (hP : P - q ≠ 0) (hQ : Q - q ≠ 0) :
    P / (P - q) - eta * C / (Q - q) - (1 - eta) =
      q * (1 / (P - q) - eta / (Q - q)) - eta * (C - Q) / (Q - q) := by
  field_simp
  ring

/-- Both identities `O:T:Fidentity`, together with the original denominator check. -/
private theorem rational_coordinates {p : ℕ} (hp : 0 < p) (u w a : E)
    (hu : u ≠ 0) (hw : w ≠ 0) (hC : 1 + u * a ≠ 0)
    (hQ : 1 + u ^ p * a ^ p - u ^ (p - 1) ≠ 0) :
    let W := u⁻¹
    let C := 1 + u * a
    let Q := 1 + u ^ p * a ^ p
    let q := u ^ (p - 1)
    let k := u * w / C
    let eta := W / w ^ p
    let G := eta * C ^ p / (Q - q)
    W ^ p - W + a ^ p ≠ 0 ∧
      G * k ^ p = q / (Q - q) ∧
      ∀ i : ℕ, i ≤ p → W / (W ^ p - W + a ^ p) * ((W + a) / w) ^ i =
        G * k ^ (p - i) := by
  dsimp only
  have huPow : u ^ (p - 1) * u = u ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel hp]
  have hd : u⁻¹ ^ p - u⁻¹ + a ^ p =
      (1 + u ^ p * a ^ p - u ^ (p - 1)) / u ^ p := by
    rw [inv_pow]
    field_simp
    rw [← huPow]
    ring
  have hden : u⁻¹ ^ p - u⁻¹ + a ^ p ≠ 0 := by rw [hd]; exact div_ne_zero hQ (pow_ne_zero _ hu)
  have hk : u * w / (1 + u * a) ≠ 0 := div_ne_zero (mul_ne_zero hu hw) hC
  have hbase : (u⁻¹ + a) / w = (u * w / (1 + u * a))⁻¹ := by
    field_simp
  have hGp : (u⁻¹ / w ^ p * (1 + u * a) ^ p / (1 + u ^ p * a ^ p - u ^ (p - 1))) *
      (u * w / (1 + u * a)) ^ p = u ^ (p - 1) / (1 + u ^ p * a ^ p - u ^ (p - 1)) := by
    rw [div_pow, mul_pow]
    field_simp
    rw [← huPow]
    ring
  have hcoef : u⁻¹ / (u⁻¹ ^ p - u⁻¹ + a ^ p) =
      u ^ (p - 1) / (1 + u ^ p * a ^ p - u ^ (p - 1)) := by
    rw [hd]
    field_simp
    rw [← huPow]
    ring
  refine ⟨hden, hGp, ?_⟩
  intro i hi
  rw [hbase, pow_sub₀ _ hk hi, ← mul_assoc, hGp, hcoef, inv_pow]
end Algebra

section Estimates
variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
/-- Every term of degree at least two reaches the same full conductor ideal. -/
private theorem rational_from_bounds {p : ℕ} (hp : 2 < p)
    (hchar : residueCharacteristic E = p) {b r n : ℤ} (hr : 0 ≤ r)
    (hn : n ≤ b + 2 * r) {k G Fstar eta : E}
    (hk : k ∈ lattice E r) (hG : 0 ≤ ord E G)
    (hprime : (p : E) ∈ lattice E b)
    (hFG : Fstar - G ∈ lattice E b)
    (hlinear : (Fstar - G - (1 - eta)) * k ∈ lattice E n) :
    -G * k + (∑ i ∈ Finset.range (p - 2), G * k ^ (p - (i + 1)) / (i + 1 : ℕ)) +
        Fstar * (∑ j ∈ Finset.range (p - 1), k ^ (j + 1) / (j + 1 : ℕ)) -
          k * (1 - eta) ∈ lattice E n := by
  have hunit (j : ℕ) (hj : 0 < j) (hjp : j < p) : ord E (j : E) = 0 :=
    ord_natCast_eq_zero_of_lt_residueCharacteristic E hj (hchar ▸ hjp)
  have hpow (j : ℕ) (hj : 2 ≤ j) : k ^ j ∈ lattice E (2 * r) :=
    lattice_antitone E (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hr)
      (lattice_pow E hk j)
  have herr : (∑ j ∈ Finset.range (p - 2),
      (p : E) * G * k ^ (j + 2) / ((j + 2 : ℕ) * (p - (j + 2) : ℕ))) ∈ lattice E n := by
    apply sum_mem_lattice E
    intro j hj
    have hjp := Finset.mem_range.mp hj
    apply lattice_antitone E hn
    apply lattice_div_unit E (mul_mem_lattice E (lattice_mul_integral E hprime hG)
      (hpow (j + 2) (by omega)))
    rw [ord_mul, hunit (j + 2) (by omega) (by omega),
      hunit (p - (j + 2)) (by omega) (by omega), add_zero]
  rw [← rational_reversal hp G k (fun j hj hjp => ne_zero_of_ord_zero E (hunit j hj hjp))] at herr
  have htail : (Fstar - G) *
      (∑ j ∈ Finset.range (p - 2), k ^ (j + 2) / (j + 2 : ℕ)) ∈ lattice E n := by
    rw [Finset.mul_sum]
    apply sum_mem_lattice E
    intro j hj
    have hjp := Finset.mem_range.mp hj
    rw [← mul_div_assoc]
    exact lattice_antitone E hn (lattice_div_unit E
      (mul_mem_lattice E hFG (hpow (j + 2) (by omega)))
      (hunit (j + 2) (by omega) (by omega)))
  have htotal := (lattice E n).add_mem herr ((lattice E n).add_mem hlinear htail)
  convert htotal using 1
  rw [positive_log_split hp]
  ring
end Estimates

section Coefficients
variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
/-- Retain both weighted terms of `O:T:FGexact` before using their depths. -/
private theorem rational_coefficient_bounds
    {P Cp Q q eta k : E} {b r d s n : ℤ}
    (hd : 0 ≤ d) (hs : 0 ≤ s) (hn₁ : n ≤ d + b + r) (hn₂ : n ≤ b + s + r)
    (hP : ord E (P - q) = 0) (hQ : ord E (Q - q) = 0)
    (heta : 0 ≤ ord E eta) (hk : k ∈ lattice E r) (hq : q ∈ lattice E d)
    (hPC : P - Cp ∈ lattice E b) (hCQ : Cp - Q ∈ lattice E (b + s))
    (he : 1 - eta ∈ lattice E b) :
    let Fstar := P / (P - q)
    let G := eta * Cp / (Q - q)
    Fstar - G ∈ lattice E b ∧
      (Fstar - G - (1 - eta)) * k ∈ lattice E n := by
  let bracket := 1 / (P - q) - eta / (Q - q)
  have hPn := ne_zero_of_ord_zero E hP
  have hQn := ne_zero_of_ord_zero E hQ
  have hCQb := lattice_antitone E (show b ≤ b + s by omega) hCQ
  have hPQ : P - Q ∈ lattice E b := by
    convert (lattice E b).add_mem hPC hCQb using 1
    ring
  have hb : bracket ∈ lattice E b := by
    have hnum : (Q - P) + (1 - eta) * (P - q) ∈ lattice E b :=
      (lattice E b).add_mem (by simpa only [neg_sub] using (lattice E b).neg_mem hPQ)
        (lattice_mul_integral E he hP.ge)
    have hden : ord E ((P - q) * (Q - q)) = 0 := by rw [ord_mul, hP, hQ, add_zero]
    convert lattice_div_unit E hnum hden using 1
    dsimp only [bracket]
    field_simp
    ring
  have hleft := mul_mem_lattice E hq hb
  have hright : eta * (Cp - Q) / (Q - q) ∈ lattice E (b + s) := by
    apply lattice_div_unit E _ hQ
    simpa only [mul_comm] using lattice_mul_integral E hCQ heta
  have herr' : q * bracket - eta * (Cp - Q) / (Q - q) ∈ lattice E b :=
    (lattice E b).sub_mem (lattice_antitone E (by omega) hleft)
      (lattice_antitone E (by omega) hright)
  have hlin := (lattice E n).sub_mem
    (lattice_antitone E hn₁ (mul_mem_lattice E hleft hk))
    (lattice_antitone E hn₂ (mul_mem_lattice E hright hk))
  dsimp only
  constructor
  · have heq := FG_exact P Cp Q q eta hPn hQn
    convert (lattice E b).add_mem herr' he using 1
    dsimp only [bracket] at *
    linear_combination heq
  · rw [FG_exact P Cp Q q eta hPn hQn, sub_mul]
    exact hlin
end Coefficients

section Cyclic
variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E]
  [Module.Free F E] [Module.Finite F E] [PrimeCyclicExtension F E]

/-- Construct all valuation inputs from the actual lower cyclic extension. -/
private theorem rational_cyclic
    {p t delta m : ℕ} (hp : 2 < p) (ht : 0 < t)
    (hdegree : Module.finrank F E = p) (hres : residueDegree F E = 1)
    (hbreak : PrimeCyclicExtension.IsLowerBreak F E (t + delta))
    (hmt : t < p * m) (a : E)
    (ha : ord E a = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (u : Fˣ) (hu : ord F (u : F) = ((m : ℤ) : WithTop ℤ))
    (w : Eˣ) (hw : normUnits F E w = u⁻¹) :
    let U := algebraMap F E (u : F)
    let W := U⁻¹
    let C := 1 + U * a
    let k := U * (w : E) / C
    let P := algebraMap F E (norm F E C)
    let Fstar := P / (P - U ^ (p - 1))
    let Fi := fun i : ℕ => W / (W ^ p - W + a ^ p) * ((W + a) / (w : E)) ^ i
    let eta := W / (w : E) ^ p;
    -Fi (p - 1) + (∑ i ∈ Finset.range (p - 2), Fi (i + 1) / (i + 1 : ℕ)) +
        Fstar * (∑ j ∈ Finset.range (p - 1), k ^ (j + 1) / (j + 1 : ℕ)) -
          k * (1 - eta) ∈ lattice E (1 + (t : ℤ) + delta + (p : ℤ) * m) := by
  let U := algebraMap F E (u : F)
  let W := U⁻¹
  let C := 1 + U * a
  let Q := 1 + U ^ p * a ^ p
  let q₀ := U ^ (p - 1)
  let k := U * (w : E) / C
  let P := algebraMap F E (norm F E C)
  let Fstar := P / (P - q₀)
  let eta := W / (w : E) ^ p
  let G := eta * C ^ p / (Q - q₀)
  let Fi := fun i : ℕ => W / (W ^ p - W + a ^ p) * ((W + a) / (w : E)) ^ i
  let b : ℤ := ((p : ℤ) - 1) * ((t : ℤ) + delta)
  let r : ℤ := ((p : ℤ) - 1) * m
  let s : ℤ := (p : ℤ) * m - t
  let n : ℤ := 1 + (t : ℤ) + delta + (p : ℤ) * m
  change -Fi (p - 1) + (∑ i ∈ Finset.range (p - 2), Fi (i + 1) / (i + 1 : ℕ)) +
      Fstar * (∑ j ∈ Finset.range (p - 1), k ^ (j + 1) / (j + 1 : ℕ)) -
        k * (1 - eta) ∈ lattice E n
  have hprime : p.Prime := hdegree ▸ PrimeCyclicExtension.degree_prime F E
  have hpZ : 0 < (p : ℤ) := by omega
  have hm : 0 < m := by nlinarith
  have hs : 0 < s := by
    have : (t : ℤ) < (p : ℤ) * m := by exact_mod_cast hmt
    dsimp only [s]
    omega
  have hr : 0 < r := by
    dsimp only [r]
    exact mul_pos (by omega) (by exact_mod_cast hm)
  have he : ramificationIndex F E = p := by
    simpa only [hdegree, hres, mul_one] using
      (finrank_eq_ramificationIndex_mul_residueDegree F E).symm
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have hcharF : residueCharacteristic F = p :=
    (residueCharacteristic_eq_degree_of_positive_isLowerBreak F E hbreak
      (by omega) pi hpi hgen).trans hdegree
  have hcharE : residueCharacteristic E = p :=
    (residueCharacteristic_extension_eq F E).trans hcharF
  have htrace := traceIdealLowerBound_of_integralGenerator F E hbreak hres pi hpi hgen
  have hbase := degree_natCast_ord_bound F E p
    (((p - 1) * (t + delta + 1) : ℕ) : ℤ) hprime.pos hdegree
      (by simpa only [hdegree, wildDifferentContribution] using htrace)
  have hpbound : (p : E) ∈ lattice E b := by
    have hscaled := nsmul_le_nsmul_right hbase p
    rw [← WithTop.coe_nsmul] at hscaled
    rw [mem_lattice, show (p : E) = algebraMap F E (p : F) by simp, ord_algebraMap, he]
    refine (WithTop.coe_le_coe.mpr ?_).trans hscaled
    change b ≤ (p : ℤ) * ((((p - 1) * (t + delta + 1) : ℕ) : ℤ) / p)
    have hmod := Int.emod_lt_of_pos (b + p - 1) hpZ
    have hdiv := Int.mul_ediv_add_emod (b + p - 1) (p : ℤ)
    have hd : (((p - 1) * (t + delta + 1) : ℕ) : ℤ) = b + p - 1 := by
      dsimp only [b]
      push_cast [Nat.cast_sub hprime.one_le]
      ring
    rw [hd]
    omega
  obtain ⟨hC, _, hPF, _, _, _⟩ := denominator_congruences F E hp ht hdegree hres hbreak hmt
    (u : F) a hu ha
  change ord E C = 0 at hC
  change ord F (norm F E C) = 0 at hPF
  have hP : ord E P = 0 := by dsimp only [P]; rw [ord_algebraMap, hPF, nsmul_zero]
  have hU : ord E U = (((p : ℤ) * m : ℤ) : WithTop ℤ) := by
    dsimp only [U]
    rw [ord_algebraMap, he, hu, ← WithTop.coe_nsmul]
    rfl
  have hW : ord E W = ((-(p : ℤ) * m : ℤ) : WithTop ℤ) := by
    dsimp only [W]
    rw [ord_inv, hU, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
    congr 1
    ring
  have hwNorm : norm F E (w : E) = (u : F)⁻¹ := by
    simpa only [coe_normUnits, Units.val_inv_eq_inv_val] using congrArg Units.val hw
  have hwOrd : ord E (w : E) = ((-(m : ℤ) : ℤ) : WithTop ℤ) := by
    have hn := congrArg (ord F) hwNorm
    simpa only [ord_norm, hres, one_nsmul, ord_inv, hu,
      WithTop.LinearOrderedAddCommGroup.coe_neg] using hn
  have hwPow : ord E ((w : E) ^ p) = ((-(p : ℤ) * m : ℤ) : WithTop ℤ) := by
    rw [ord_pow, hwOrd, ← WithTop.coe_nsmul]
    simp only [nsmul_eq_mul, mul_neg, neg_mul]
  have hk : ord E k = (r : WithTop ℤ) := by
    dsimp only [k]
    rw [ord_div, hC, sub_zero, ord_mul, hU, hwOrd, ← WithTop.coe_add]
    congr 1
    dsimp only [r]
    ring
  have hq : ord E q₀ = (((p : ℤ) * r : ℤ) : WithTop ℤ) := by
    dsimp only [q₀]
    rw [ord_pow, hU, ← WithTop.coe_nsmul]
    simp only [nsmul_eq_mul, Nat.cast_sub hprime.one_le, Nat.cast_one]
    congr 1
    dsimp only [r]
    ring
  have hz : ord E (U * a) = (s : WithTop ℤ) := by
    rw [ord_mul, hU, ha, ← WithTop.coe_add]
    rfl
  have hQ : ord E Q = 0 := by
    have hpos : 0 < ord E ((U * a) ^ p) := by
      rw [ord_pow, hz, ← WithTop.coe_nsmul, WithTop.coe_pos]
      simpa only [nsmul_eq_mul] using mul_pos hpZ hs
    dsimp only [Q]
    rw [← mul_pow, (ord E).map_add_eq_of_lt_left (by simpa only [ord_one] using hpos), ord_one]
  have hqpos : 0 < ord E q₀ := by rw [hq, WithTop.coe_pos]; exact mul_pos hpZ hr
  have hPq : ord E (P - q₀) = 0 := by
    rw [(ord E).map_sub_eq_of_lt_left (by simpa only [hP] using hqpos), hP]
  have hQq : ord E (Q - q₀) = 0 := by
    rw [(ord E).map_sub_eq_of_lt_left (by simpa only [hQ] using hqpos), hQ]
  have heta : ord E eta = 0 := by
    dsimp only [eta]
    rw [ord_div, hW, hwPow, ← WithTop.LinearOrderedAddCommGroup.coe_sub]
    simp
  have hG : ord E G = 0 := by
    dsimp only [G]
    rw [ord_div, hQq, sub_zero, ord_mul, heta, ord_pow, hC, nsmul_zero, add_zero]
  have hPC : P - C ^ p ∈ lattice E b := by
    have h := Total.powerNorm F E p (t + delta) hdegree hp hbreak (by omega) hres C
    rw [hC, nsmul_zero, zero_add] at h
    have h' : C ^ p - P ∈ lattice E b := by
      apply (mem_lattice E).2
      simpa only [Nat.cast_mul, Nat.cast_sub hprime.one_le, Nat.cast_add, Nat.cast_one, b, P] using h
    simpa only [neg_sub] using (lattice E b).neg_mem h'
  have hCQ : C ^ p - Q ∈ lattice E (b + s) := by
    simpa only [C, Q, mul_pow] using binomial_error E hprime hs.le hpbound ((mem_lattice E).2 hz.ge)
  have hediff : 1 - eta ∈ lattice E b := by
    have h := Total.powerNorm F E p (t + delta) hdegree hp hbreak (by omega) hres (w : E)
    rw [hwOrd, hwNorm, map_inv₀] at h
    have hdiff : (w : E) ^ p - W ∈ lattice E (-(p : ℤ) * m + b) := by
      apply (mem_lattice E).2
      simpa only [← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul,
        Nat.cast_mul, Nat.cast_sub hprime.one_le, Nat.cast_add, Nat.cast_one, mul_neg, neg_mul,
        b, W, U] using h
    have heq : 1 - eta = ((w : E) ^ p - W) / (w : E) ^ p := by
      dsimp only [eta]
      field_simp
    rw [heq]
    exact (div_mem_lattice_iff E _ _ _ _ hwPow).2 hdiff
  have hdepth := rational_depths (p : ℤ) t delta m (by omega) (by omega) (by omega) (by omega)
  obtain ⟨hFG, hlin⟩ := rational_coefficient_bounds E
    (b := b) (r := r) (d := (p : ℤ) * r) (s := s) (n := n)
    (mul_nonneg hpZ.le hr.le) hs.le hdepth.2.1
    (by dsimp only [n, b, s, r]; linear_combination hdepth.2.2) hPq hQq heta.ge
    ((mem_lattice E).2 hk.ge) ((mem_lattice E).2 hq.ge) hPC hCQ hediff
  have hresult := rational_from_bounds E hp hcharE hr.le hdepth.1
    ((mem_lattice E).2 hk.ge) hG.ge hpbound hFG hlin
  have hUne : U ≠ 0 := (map_ne_zero (algebraMap F E)).2 u.ne_zero
  have hCne := ne_zero_of_ord_zero E hC
  have hQne := ne_zero_of_ord_zero E hQq
  have hcoords := rational_coordinates hprime.pos U (w : E) a hUne w.ne_zero hCne hQne
  have hFi (i : ℕ) (hi : i ≤ p) : Fi i = G * k ^ (p - i) := hcoords.2.2 i hi
  rw [hFi (p - 1) (by omega), show p - (p - 1) = 1 by omega, pow_one, ← neg_mul]
  convert hresult using 1
  congr 3
  apply Finset.sum_congr rfl
  intro i hi
  rw [hFi (i + 1) (by have := Finset.mem_range.mp hi; omega)]
end Cyclic

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

local notation "B₂" => R.B₂
local instance : PrimeCyclicExtension F B₂ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₂
    (Basic.intermediateField_tower_compatible hp hG B₂ R.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.1

/-- **Paper Lemma 9.22 (`O:T:rational`).** The two literal rational sums,
with `a = N_{K/B₂}(Delta)` and the preserved exact choice `N_{B₂/F}(w) = u⁻¹`,
cancel modulo the full gamma-conductor ideal `1 + t₂ + p m`.

Here `u = alpha/gamma` in the stationary setup. All fractions are evaluated
in the actual second intermediate field. The proof derives their nonzero
denominators and the weighted norm--power errors from the genuine field
and norm data. Both field characteristics are included through `WithTop ℤ`.
The character and conductor constructions supply these inputs; this
stronger field identity needs no assumptions about character values. -/
theorem rational
    (hres : residueDegree F K = 1)
    {m : ℕ} (hmt : R.t < p * m)
    (Delta : K) (hDelta : ord K Delta = ((-(R.t : ℤ) : ℤ) : WithTop ℤ))
    (u : Fˣ) (hu : ord F (u : F) = ((m : ℤ) : WithTop ℤ))
    (w : B₂ˣ) (hw : normUnits F B₂ w = u⁻¹) :
    let a := norm B₂ K Delta
    let U := algebraMap F B₂ (u : F)
    let W := U⁻¹
    let C := 1 + U * a
    let k := U * (w : B₂) / C
    let P := algebraMap F B₂ (norm F B₂ C)
    let Fstar := P / (P - U ^ (p - 1))
    let Fi := fun i : ℕ => W / (W ^ p - W + a ^ p) * ((W + a) / (w : B₂)) ^ i
    let eta := W / (w : B₂) ^ p;
    -Fi (p - 1) + (∑ i ∈ Finset.range (p - 2), Fi (i + 1) / (i + 1 : ℕ)) +
        Fstar * (∑ j ∈ Finset.range (p - 1), k ^ (j + 1) / (j + 1 : ℕ)) -
          k * (1 - eta) ∈ lattice B₂ (1 + (R.t₂ : ℤ) + (p : ℤ) * m) := by
  obtain ⟨_, hrF₂, hrK₂, _, _⟩ :=
    realization_tower_data hp hG hres B₂ R.degree_B₂
  have ha : ord B₂ (norm B₂ K Delta) = ((-(R.t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_norm, hrK₂, one_nsmul, hDelta]
  have hbreak : PrimeCyclicExtension.IsLowerBreak F B₂ (R.t + R.delta) := by
    rw [← R.t₂_eq]
    exact R.B₂_breaks.1
  simpa only [R.t₂_eq, Nat.cast_add, add_assoc] using
    rational_cyclic F B₂ R.odd_prime R.t_pos R.degree_B₂ hrF₂ hbreak hmt
      (norm B₂ K Delta) ha u hu w hw
end Diamond
end
end LanglandsSecondMainLemma.Odd.Transition
