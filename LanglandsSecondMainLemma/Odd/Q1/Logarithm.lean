import LanglandsSecondMainLemma.Odd.Q1.Entry
import LanglandsSecondMainLemma.Odd.Linear.Final
import LanglandsSecondMainLemma.Odd.Quadratic.Trace

/-!
# The full logarithm of the actual first factor

Paper Proposition 9.13 (`O:Q:logentry`), with the actual norm quotient of
`O:Q:entry`. Newton's identities retain their alternating signs and the
exceptional top square. All remainders are killed at the full conductor
in the first lower field, before transporting the surviving traces.
-/

namespace LanglandsSecondMainLemma.Odd.Q1
noncomputable section
open LanglandsFirstMainLemma
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
open private truncatedLog_sub_quadratic_mem from LanglandsSecondMainLemma.Odd.EnhancedStationary

/-- A uniform positive depth valid on both sides of `m = t`. -/
theorem logarithm_depths (p t delta m : ℤ)
    (hp : 3 ≤ p) (ht : 1 ≤ t) (hd : 0 ≤ delta) (hm : t < p * m) :
    let r := (p - 1) * (delta + min m t)
    0 < r ∧ 1 + 2 * t + p * delta ≤ p * r ∧
      1 + 2 * t + p * delta ≤ 3 * r ∧
      (∀ i : ℤ, 1 ≤ i → i ≤ p - 1 →
        r ≤ (p - 1) * (t + delta) + i * (m - t)) ∧
      (∀ k : ℤ, 2 ≤ k → k ≤ 2 * p - 3 →
        1 + 2 * t + p * delta ≤ 2 * (p - 1) * (t + delta) + k * (m - t)) := by
  have hmpos : 1 ≤ m := by nlinarith
  dsimp only
  have hpd := mul_nonneg (by omega : 0 ≤ p - 1) hd
  have hpt := mul_nonneg (by omega : 0 ≤ p - 3) (by omega : 0 ≤ t)
  by_cases hmt : m ≤ t
  · rw [min_eq_left hmt]
    have hpm := mul_nonneg (by omega : 0 ≤ p - 3) (by omega : 0 ≤ m)
    have hdd := mul_nonneg (by nlinarith : 0 ≤ p * (p - 2)) hd
    have hdd' := mul_nonneg (by omega : 0 ≤ 2 * p - 3) hd
    have hr : 0 < (p - 1) * (delta + m) := mul_pos (by omega) (by omega)
    refine ⟨hr, ?_, ?_, ?_, ?_⟩
    · have hh := mul_nonneg (by omega : 0 ≤ p) hpm
      nlinarith
    · nlinarith
    · intro i hi hip
      have hh := mul_nonneg (by omega : 0 ≤ p - 1 - i) (by omega : 0 ≤ t - m)
      nlinarith
    · intro k hk hkp
      have hh := mul_nonneg (by omega : 0 ≤ 2 * p - 3 - k) (by omega : 0 ≤ t - m)
      have hh' := mul_nonneg (by omega : 0 ≤ 2 * p - 3) (by omega : 0 ≤ p * m - t - 1)
      have hh'' := mul_nonneg (by omega : 0 ≤ p) (mul_nonneg (by omega : 0 ≤ p - 2) hd)
      have hgoal : 0 ≤ p * (2 * (p - 1) * (t + delta) + k * (m - t) -
          (1 + 2 * t + p * delta)) := by
        have hhh := mul_nonneg (by omega : 0 ≤ p) hh
        nlinarith
      nlinarith
  · rw [min_eq_right (by omega)]
    have hr : 0 < (p - 1) * (delta + t) := mul_pos (by omega) (by omega)
    have hdd := mul_nonneg (by nlinarith : 0 ≤ p * (p - 2)) hd
    have hdd' := mul_nonneg (by omega : 0 ≤ 2 * p - 3) hd
    have hpp := mul_nonneg (by nlinarith : 0 ≤ p * (p - 1) - 3) (by omega : 0 ≤ t)
    refine ⟨hr, ?_, ?_, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · intro i hi hip
      have hh := mul_nonneg (by omega : 0 ≤ i) (by omega : 0 ≤ m - t)
      nlinarith
    · intro k hk hkp
      have hh := mul_nonneg (by omega : 0 ≤ k - 2) (by omega : 0 ≤ m - t)
      have hdd'' := mul_nonneg (by omega : 0 ≤ p - 2) hd
      nlinarith

section Lattice
variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

private theorem div_unit_mem {x d : E} {n : ℤ}
    (hx : x ∈ lattice E n) (hd : ord E d = 0) : x / d ∈ lattice E n := by
  exact (div_mem_lattice_iff E d x 0 n (by simpa using hd)).2 (by simpa using hx)

private theorem sign_mul_mem (i : ℕ) {x : E} {n : ℤ}
    (hx : x ∈ lattice E n) : (-1 : E) ^ i * x ∈ lattice E n := by
  simpa only [mem_lattice, ord_mul, ord_pow, ord_neg, ord_one, smul_zero, zero_add] using hx

/-- The nonlinear part of Newton's identity, divided only by a residue unit. -/
private theorem newton_remainder
    (K : Type*) [Field K] [Algebra E K]
    [Module.Free E K] [Module.Finite E K] [IsGalois E K]
    (x : K) (i : ℕ) (hi : 1 ≤ i) (hip : i < residueCharacteristic E)
    (H : ℤ)
    (hprod : ∀ j k : ℕ, 1 ≤ j → 1 ≤ k → j + k = i →
      elementarySymmetric E K j x * trace E K (x ^ k) ∈ lattice E H) :
    elementarySymmetric E K i x -
      (-1 : E) ^ (i + 1) * trace E K (x ^ i) / (i : E) ∈ lattice E H := by
  classical
  let s := (Finset.HasAntidiagonal.antidiagonal i).filter (fun a => a.1 < i)
  let f (a : ℕ × ℕ) := (-1 : E) ^ a.1 * elementarySymmetric E K a.1 x *
    galoisPowerSum E K a.2 x
  have hzero : (0, i) ∈ s := by simp [s]; omega
  have hfzero : f (0, i) = trace E K (x ^ i) := by
    simp [f, elementarySymmetric_zero, galoisPowerSum]
  have hsum : (∑ a ∈ s, f a) - trace E K (x ^ i) ∈ lattice E H := by
    rw [← Finset.sum_erase_add _ _ hzero, hfzero, add_sub_cancel_right]
    apply sum_mem_lattice E
    intro a ha
    obtain ⟨hne, ha⟩ := Finset.mem_erase.mp ha
    have ha' : a.1 + a.2 = i ∧ a.1 < i := by simpa [s] using ha
    have haj : 1 ≤ a.1 := by
      by_contra h
      have : a = (0, i) := Prod.ext (by omega) (by omega)
      exact hne this
    have hak : 1 ≤ a.2 := by omega
    simpa only [f, galoisPowerSum, mul_assoc] using
      sign_mul_mem E a.1 (hprod a.1 a.2 haj hak ha'.1)
  have ho : ord E (i : E) = 0 :=
    ord_natCast_eq_zero_of_lt_residueCharacteristic E hi hip
  have hinz : (i : E) ≠ 0 := by
    intro h
    simp [h] at ho
  have hn := elementarySymmetric_newton_identity E K x i
  change (i : E) * elementarySymmetric E K i x = (-1 : E) ^ (i + 1) *
    ∑ a ∈ s, f a at hn
  have heq : elementarySymmetric E K i x -
      (-1 : E) ^ (i + 1) * trace E K (x ^ i) / (i : E) =
      (-1 : E) ^ (i + 1) * ((∑ a ∈ s, f a) - trace E K (x ^ i)) / (i : E) := by
    apply (eq_div_iff hinz).2
    rw [sub_mul, div_mul_cancel₀ _ hinz]
    linear_combination hn
  rw [heq]
  exact div_unit_mem E (sign_mul_mem E _ hsum) ho

/-- Every product except the square of the top coefficient disappears. -/
private theorem sum_square_top {p : ℕ} (hp : 2 < p) (e : ℕ → E) (H : ℤ)
    (hprod : ∀ i ∈ Finset.Ico 1 p, ∀ j ∈ Finset.Ico 1 p,
      i + j ≤ 2 * p - 3 → e i * e j ∈ lattice E H) :
    (∑ i ∈ Finset.Ico 1 p, e i) ^ 2 - e (p - 1) ^ 2 ∈ lattice E H := by
  classical
  have h : (∑ i ∈ Finset.Ico 1 p, ∑ j ∈ Finset.Ico 1 p,
      (e i * e j - if i = p - 1 ∧ j = p - 1 then e (p - 1) ^ 2 else 0)) ∈
      lattice E H := by
    apply sum_mem_lattice E
    intro i hi
    apply sum_mem_lattice E
    intro j hj
    split_ifs with hij
    · obtain ⟨rfl, rfl⟩ := hij
      simp only [pow_two, sub_self]
      exact (lattice E H).zero_mem
    · rw [sub_zero]
      exact hprod i hi j hj (by
        obtain ⟨_, hi⟩ := Finset.mem_Ico.mp hi
        obtain ⟨_, hj⟩ := Finset.mem_Ico.mp hj
        omega)
  have htop : (∑ i ∈ Finset.Ico 1 p, ∑ j ∈ Finset.Ico 1 p,
      if i = p - 1 ∧ j = p - 1 then e (p - 1) ^ 2 else 0) = e (p - 1) ^ 2 := by
    simp [ite_and, show 1 ≤ p - 1 by omega, show p - 1 < p by omega]
  simpa only [Finset.sum_sub_distrib, htop, ← Finset.mul_sum,
    ← Finset.sum_mul, ← pow_two] using h

/-- The complete logarithmic calculation at the multiplicative conductor,
before any weight or field trace. The exceptional square is retained. -/
private theorem logarithm_expansion
    (K : Type*) [Field K] [Algebra E K]
    [Module.Free E K] [Module.Finite E K] [IsGalois E K]
    (p r : ℕ) (hp : 2 < p) (hchar : residueCharacteristic E = p)
    (H : ℤ) (hH : H ≤ 3 * (r : ℤ)) (x : K) (d : E) (hd : ord E d = 0)
    (he : ∀ i ∈ Finset.Ico 1 p, elementarySymmetric E K i x ∈ lattice E (r : ℤ))
    (hU : ∀ i ∈ Finset.Ico 1 p, trace E K (x ^ i) ∈ lattice E (r : ℤ))
    (hprod : ∀ i ∈ Finset.Ico 1 p, ∀ j ∈ Finset.Ico 1 p,
      i + j ≤ 2 * p - 3 →
      elementarySymmetric E K i x * elementarySymmetric E K j x ∈ lattice E H ∧
      elementarySymmetric E K i x * trace E K (x ^ j) ∈ lattice E H) :
    let S := ∑ i ∈ Finset.Ico 1 p, elementarySymmetric E K i x
    let V := ∑ i ∈ Finset.Ico 1 p, (-1 : E) ^ (i + 1) * trace E K (x ^ i) / (i : E)
    truncatedLog p (-S / d) -
      (-V / d + trace E K (x ^ (p - 1)) ^ 2 / (2 * (p - 1 : ℕ) ^ 2 * d ^ 2)) ∈
      lattice E H := by
  dsimp only
  let S := ∑ i ∈ Finset.Ico 1 p, elementarySymmetric E K i x
  let V := ∑ i ∈ Finset.Ico 1 p, (-1 : E) ^ (i + 1) * trace E K (x ^ i) / (i : E)
  let q := p - 1
  let A := (-1 : E) ^ (q + 1) * trace E K (x ^ q) / (q : E)
  have hq : q ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr ⟨by dsimp [q]; omega, by dsimp [q]; omega⟩
  have hqo : ord E (q : E) = 0 := ord_natCast_eq_zero_of_lt_residueCharacteristic E
    (Finset.mem_Ico.mp hq).1 (by rw [hchar]; exact (Finset.mem_Ico.mp hq).2)
  have htwo : ord E (2 : E) = 0 :=
    ord_natCast_eq_zero_of_lt_residueCharacteristic E (j := 2) (by omega) (by rw [hchar]; exact hp)
  have hlin : S - V ∈ lattice E H := by
    dsimp only [S, V]
    rw [← Finset.sum_sub_distrib]
    apply sum_mem_lattice E
    intro i hi
    apply newton_remainder E K x i (Finset.mem_Ico.mp hi).1
      (by rw [hchar]; exact (Finset.mem_Ico.mp hi).2)
    intro j k hj hk hjk
    exact (hprod j (Finset.mem_Ico.mpr ⟨hj, by have := (Finset.mem_Ico.mp hi).2; omega⟩)
      k (Finset.mem_Ico.mpr ⟨hk, by have := (Finset.mem_Ico.mp hi).2; omega⟩)
      (by have := (Finset.mem_Ico.mp hi).2; omega)).2
  have htop : elementarySymmetric E K q x - A ∈ lattice E (2 * (r : ℤ)) := by
    apply newton_remainder E K x q (Finset.mem_Ico.mp hq).1
      (by rw [hchar]; exact (Finset.mem_Ico.mp hq).2)
    intro j k hj hk hjk
    have hjp : j ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr ⟨hj, by dsimp [q] at hjk; omega⟩
    have hkp : k ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr ⟨hk, by dsimp [q] at hjk; omega⟩
    simpa only [two_mul] using mul_mem_lattice E (he j hjp) (hU k hkp)
  have hA : A ∈ lattice E (r : ℤ) := div_unit_mem E (sign_mul_mem E _ (hU q hq)) hqo
  have htopSquare : elementarySymmetric E K q x ^ 2 -
      trace E K (x ^ q) ^ 2 / (q : E) ^ 2 ∈ lattice E H := by
    have h := mul_mem_lattice E htop ((lattice E (r : ℤ)).add_mem (he q hq) hA)
    have hs : A ^ 2 = trace E K (x ^ q) ^ 2 / (q : E) ^ 2 := by
      dsimp only [A]
      rw [div_pow, mul_pow, ← pow_mul, mul_comm (q + 1) 2, pow_mul]
      simp
    have heq : (elementarySymmetric E K q x - A) *
        (elementarySymmetric E K q x + A) = elementarySymmetric E K q x ^ 2 -
          trace E K (x ^ q) ^ 2 / (q : E) ^ 2 := by rw [← hs]; ring
    rw [heq] at h
    exact lattice_antitone E (by omega) h
  have hquad : S ^ 2 - trace E K (x ^ q) ^ 2 / (q : E) ^ 2 ∈ lattice E H := by
    have h := (lattice E H).add_mem
      (sum_square_top E hp (fun i => elementarySymmetric E K i x) H
        (fun i hi j hj hij => (hprod i hi j hj hij).1)) htopSquare
    simpa only [q, S, sub_add_sub_cancel] using h
  have hS : S ∈ lattice E (r : ℤ) := sum_mem_lattice E he
  have hz : -S / d ∈ lattice E (r : ℤ) := div_unit_mem E ((lattice E _).neg_mem hS) hd
  have hrem := truncatedLog_sub_quadratic_mem E p r hchar (by omega) hz
  have hrem' : truncatedLog p (-S / d) - (-S / d) - (-S / d) ^ 2 / 2 ∈ lattice E H :=
    lattice_antitone E (by simpa using hH) hrem
  have hd2 : ord E (2 * d ^ 2) = 0 := by simp only [ord_mul, ord_pow, htwo, hd, smul_zero, add_zero]
  have h := (lattice E H).add_mem
    ((lattice E H).sub_mem hrem' (div_unit_mem E hlin hd))
    (div_unit_mem E hquad hd2)
  convert h using 1
  dsimp only [S, V, q]
  simp only [div_eq_mul_inv, mul_inv_rev, neg_mul]
  ring

end Lattice


section Trace
variable (E K : Type*) [Field E] [Field K] [Algebra E K]

private theorem trace_scalar (c : E) (x : K) :
    trace E K (algebraMap E K c * x) = c * trace E K x := by
  simpa only [Algebra.smul_def, Algebra.algebraMap_self_apply] using (trace E K).map_smul c x

/-- Rational coefficients are moved through the trace in the field in which
that trace takes values. No expression in the top field is fed to a lower character. -/
private theorem trace_signed_sum (p : ℕ) (x : ℕ → K) (y : K) :
    trace E K ((∑ i ∈ Finset.Ico 1 p, (-1 : K) ^ i / (i : K) * x i) +
      y / (2 * (p - 1 : ℕ) ^ 2)) =
    (∑ i ∈ Finset.Ico 1 p, (-1 : E) ^ i / (i : E) * trace E K (x i)) +
      trace E K y / (2 * (p - 1 : ℕ) ^ 2) := by
  rw [map_add, map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have h := trace_scalar E K ((-1 : E) ^ i / (i : E)) (x i)
    simpa only [map_div₀, map_pow, map_neg, map_one, map_natCast] using h
  · have h := trace_scalar E K ((2 * (p - 1 : ℕ) ^ 2 : E)⁻¹) y
    simpa only [map_inv₀, map_mul, map_ofNat, map_pow, map_natCast, div_eq_mul_inv,
      mul_comm] using h

private theorem trace_surviving_exponent (p : ℕ) (b d : E) (z : K) :
    trace E K
      ((∑ i ∈ Finset.Ico 1 p, (-1 : K) ^ i / (i : K) *
        (algebraMap E K b * z ^ i / algebraMap E K d)) +
      (algebraMap E K b * z ^ (p - 1) *
        algebraMap E K (trace E K (z ^ (p - 1))) / (algebraMap E K d) ^ 2) /
          (2 * (p - 1 : ℕ) ^ 2)) =
      b * (-(∑ i ∈ Finset.Ico 1 p,
        (-1 : E) ^ (i + 1) * trace E K (z ^ i) / (i : E)) / d +
        trace E K (z ^ (p - 1)) ^ 2 / (2 * (p - 1 : ℕ) ^ 2 * d ^ 2)) := by
  rw [trace_signed_sum]
  have ht (i : ℕ) : trace E K (algebraMap E K b * z ^ i / algebraMap E K d) =
      b * trace E K (z ^ i) / d := by
    calc
      _ = trace E K (algebraMap E K (b / d) * z ^ i) := by
        congr 1
        rw [map_div₀]
        ring
      _ = _ := by rw [trace_scalar]; ring
  have hq : trace E K (algebraMap E K b * z ^ (p - 1) *
      algebraMap E K (trace E K (z ^ (p - 1))) / (algebraMap E K d) ^ 2) =
      b * trace E K (z ^ (p - 1)) ^ 2 / d ^ 2 := by
    calc
      _ = trace E K (algebraMap E K (b * trace E K (z ^ (p - 1)) / d ^ 2) *
          z ^ (p - 1)) := by
        congr 1
        simp only [map_div₀, map_mul, map_pow]
        ring
      _ = _ := by rw [trace_scalar]; ring
  simp_rw [ht]
  rw [hq]
  have hs' : (∑ i ∈ Finset.Ico 1 p, (-1 : E) ^ i / (i : E) *
      (b * trace E K (z ^ i) / d)) =
      -b / d * ∑ i ∈ Finset.Ico 1 p,
        (-1 : E) ^ (i + 1) * trace E K (z ^ i) / (i : E) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_succ]
    ring
  rw [hs']
  ring


variable [Module.Free E K] [Module.Finite E K]

private theorem norm_one_add_split {p : ℕ} (hp : 1 ≤ p)
    (hdim : Module.finrank E K = p) (z : K) :
    norm E K (1 + z) = 1 + norm E K z +
      ∑ i ∈ Finset.Ico 1 p, elementarySymmetric E K i z := by
  have htop : elementarySymmetric E K p z = norm E K z := by
    simpa only [hdim] using elementarySymmetric_finrank E K z
  rw [norm_one_add_eq_sum_elementarySymmetric, hdim, Finset.sum_range_succ,
    ← Finset.sum_range_add_sum_Ico _ hp, Finset.sum_range_one, elementarySymmetric_zero, htop]
  ring

end Trace

open private realization_tower_data from LanglandsSecondMainLemma.Odd.Models.Realization
open private exact_coordinate_orders_and_generation from LanglandsSecondMainLemma.Odd.Total.ASCoordinate

section Diamond
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]
  {p : ℕ} (hp : p.Prime)
  (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
  (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
  (D : Total.OddTotalBreakData (F := F) (K := K) hp hG)

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension
local notation "B₁" => D.B₁
local notation "B₂" => D.B₂
local instance : PrimeCyclicExtension F B₁ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₁
    (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.2.2.2.1
local instance : PrimeCyclicExtension F B₂ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₂
    (Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.1

include hres hchar

/-- The accepted twisted estimates applied to the prescribed `Delta/w`.
The slope `m-t` remains an integer and is allowed to have either sign. -/
private theorem logarithm_twisted_bounds
    (Delta : K) (a : B₂) (hroot : Delta ^ p - Delta = algebraMap B₂ K a)
    (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ D.t) (w : B₂ˣ) (m : ℤ)
    (hw : ord B₂ (w : B₂) = ((-m : ℤ) : WithTop ℤ)) :
    let z := Delta / algebraMap B₂ K (w : B₂)
    ∀ i : ℕ, 1 ≤ i → i < p →
      elementarySymmetric B₁ K i z ∈
        lattice B₁ (((p : ℤ) - 1) * D.t₂ + i * (m - D.t)) ∧
      trace B₁ K (z ^ i) ∈
        lattice B₁ (((p : ℤ) - 1) * D.t₂ + i * (m - D.t)) := by
  obtain ⟨hd₂, _, _, _, he₂⟩ := realization_tower_data hp hG hres B₂ D.degree_B₂
  obtain ⟨_, hgen⟩ := exact_coordinate_orders_and_generation B₂ K hp D.t_pos
    hd₂ he₂ Delta a hDelta hprime hroot
  obtain ⟨htrace, hsym, _, _⟩ := Models.realization_twistedEstimates_of_coordinate
    hp hG hres hchar D Delta a hroot hDelta hprime hgen
  have hinv : ord B₂ ((w : B₂)⁻¹) = (m : WithTop ℤ) := by
    rw [ord_inv, hw, ← WithTop.LinearOrderedAddCommGroup.coe_neg, neg_neg]
  dsimp only
  intro i hi hip
  have hs := hsym (w : B₂)⁻¹ i hi hip
  have ht := htrace ((w : B₂)⁻¹ ^ i) i hip
  rw [hinv, ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul] at hs
  rw [ord_pow, hinv, ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul] at ht
  have hz : algebraMap B₂ K (w : B₂)⁻¹ * Delta =
      Delta / algebraMap B₂ K (w : B₂) := by simp [div_eq_mul_inv, mul_comm]
  have hzpow : algebraMap B₂ K ((w : B₂)⁻¹ ^ i) * Delta ^ i =
      (Delta / algebraMap B₂ K (w : B₂)) ^ i := by
    rw [map_pow, ← mul_pow, hz]
  rw [hz] at hs
  rw [hzpow] at ht
  constructor
  · rw [mem_lattice]
    convert hs using 1
    congr 1
    ring
  · rw [mem_lattice]
    convert ht using 1
    congr 1
    ring

/-- Full conductor precision for the logarithm of the actual relative change.
This supplies both the complete chart domain and the weighted error lattice
in `B₁`; no trace to `B₂` has yet been taken. -/
theorem logarithm_full_kernel
    (Delta : K) (a : B₂) (hroot : Delta ^ p - Delta = algebraMap B₂ K a)
    (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ D.t) (w : B₂ˣ) (m : ℤ)
    (hw : ord B₂ (w : B₂) = ((-m : ℤ) : WithTop ℤ))
    (hm : (D.t : ℤ) < (p : ℤ) * m) (d : B₁) (hd : ord B₁ d = 0) :
    let z := Delta / algebraMap B₂ K (w : B₂)
    let S := ∑ i ∈ Finset.Ico 1 p, elementarySymmetric B₁ K i z
    let V := ∑ i ∈ Finset.Ico 1 p,
      (-1 : B₁) ^ (i + 1) * trace B₁ K (z ^ i) / (i : B₁)
    S / d ∈ lattice B₁ (Models.firstModelDepth D : ℤ) ∧
      norm B₁ K Delta * (truncatedLog p (-S / d) -
        (-V / d + trace B₁ K (z ^ (p - 1)) ^ 2 /
          (2 * (p - 1 : ℕ) ^ 2 * d ^ 2))) ∈ lattice B₁ (1 + D.tPrime) := by
  let z := Delta / algebraMap B₂ K (w : B₂)
  let v (i : ℕ) : ℤ := ((p : ℤ) - 1) * D.t₂ + i * (m - D.t)
  let rZ := ((p : ℤ) - 1) * ((D.delta : ℤ) + min m D.t)
  let r := rZ.toNat
  have depths := logarithm_depths p D.t D.delta m (by exact_mod_cast D.odd_prime)
    (by exact_mod_cast D.t_pos) (Int.natCast_nonneg _) hm
  change 0 < rZ ∧ _ at depths
  have hr : (r : ℤ) = rZ := Int.toNat_of_nonneg depths.1.le
  have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
  have hm₁ : (Models.firstModelConductor D : ℤ) = 1 + 2 * D.t + (p : ℤ) * D.delta := by
    simp only [Models.firstModelConductor, D.tPrime_eq, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
    ring
  have hpr : Models.firstModelDepth D ≤ r := by
    apply (ceilDiv_le_iff_le_mul hp.pos).2
    exact_mod_cast (show (Models.firstModelConductor D : ℤ) ≤ (p : ℤ) * (r : ℤ) by
      rw [hr, hm₁]; exact depths.2.1)
  have h3r : (Models.firstModelConductor D : ℤ) ≤ 3 * (r : ℤ) := by
    rw [hr, hm₁]; exact depths.2.2.1
  have hv (i : ℕ) (hi : i ∈ Finset.Ico 1 p) : (r : ℤ) ≤ v i := by
    rw [hr]
    dsimp only [v]
    rw [ht₂]
    apply depths.2.2.2.1 i
    · exact_mod_cast (Finset.mem_Ico.mp hi).1
    · have := (Finset.mem_Ico.mp hi).2
      omega
  have hb := logarithm_twisted_bounds hp hG hres hchar D Delta a hroot hDelta hprime w m hw
  have he (i : ℕ) (hi : i ∈ Finset.Ico 1 p) : elementarySymmetric B₁ K i z ∈ lattice B₁ (r : ℤ) :=
    lattice_antitone B₁ (hv i hi) (hb i (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2).1
  have hU (i : ℕ) (hi : i ∈ Finset.Ico 1 p) : trace B₁ K (z ^ i) ∈ lattice B₁ (r : ℤ) :=
    lattice_antitone B₁ (hv i hi) (hb i (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2).2
  have hprod (i : ℕ) (hi : i ∈ Finset.Ico 1 p) (j : ℕ) (hj : j ∈ Finset.Ico 1 p)
      (hij : i + j ≤ 2 * p - 3) :
      elementarySymmetric B₁ K i z * elementarySymmetric B₁ K j z ∈
        lattice B₁ (Models.firstModelConductor D : ℤ) ∧
      elementarySymmetric B₁ K i z * trace B₁ K (z ^ j) ∈
        lattice B₁ (Models.firstModelConductor D : ℤ) := by
    have hdepth : (Models.firstModelConductor D : ℤ) ≤ v i + v j := by
      have h := depths.2.2.2.2 ((i : ℤ) + j)
        (by have := (Finset.mem_Ico.mp hi).1; have := (Finset.mem_Ico.mp hj).1; omega)
        (by have := D.odd_prime; omega)
      rw [← hm₁] at h
      convert h using 1
      dsimp only [v]
      rw [ht₂]
      ring
    obtain ⟨hei, _⟩ := hb i (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2
    obtain ⟨hej, hUj⟩ := hb j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
    exact ⟨lattice_antitone B₁ hdepth (mul_mem_lattice B₁ hei hej),
      lattice_antitone B₁ hdepth (mul_mem_lattice B₁ hei hUj)⟩
  have hexp := logarithm_expansion B₁ K p r D.odd_prime
    ((residueCharacteristic_extension_eq F B₁).trans hchar)
    (Models.firstModelConductor D) h3r z d hd he hU hprod
  obtain ⟨_, _, hrK₁, _, _⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  have hnorm : ord B₁ (norm B₁ K Delta) = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_norm, hrK₁, one_nsmul, hDelta]
  constructor
  · exact lattice_antitone B₁ (by exact_mod_cast hpr) (div_unit_mem B₁ (sum_mem_lattice B₁ he) hd)
  · have h := mul_mem_lattice B₁ ((mem_lattice B₁).2 hnorm.ge) hexp
    apply lattice_antitone B₁ _ h
    simp only [Models.firstModelConductor, Nat.cast_add, Nat.cast_one]
    omega


omit hres hchar [Module.Free F K] in
/-- Exact transport of the surviving exponent through the two traces.
The right side uses the actual `W_i` and quadratic trace definitions. -/
private theorem logarithm_transport (Psi : ContinuousAddChar F)
    (Delta : K) (w : B₂ˣ) (d : B₁)
    (hd : algebraMap B₁ K d = 1 + algebraMap B₁ K (norm B₁ K Delta) /
      algebraMap F K (Linear.transitionNorm D w)) :
    let z := Delta / algebraMap B₂ K (w : B₂)
    tracePullbackAddChar F B₁ Psi
      (norm B₁ K Delta *
        (-(∑ i ∈ Finset.Ico 1 p,
          (-1 : B₁) ^ (i + 1) * trace B₁ K (z ^ i) / (i : B₁)) / d +
          trace B₁ K (z ^ (p - 1)) ^ 2 /
            (2 * (p - 1 : ℕ) ^ 2 * d ^ 2))) =
    tracePullbackAddChar F B₂ Psi
      ((∑ i ∈ Finset.Ico 1 p, (-1 : B₂) ^ i / (i : B₂) * Linear.linearTrace D Delta w i) +
        Quadratic.quadraticTrace D Delta w / (2 * (p - 1 : ℕ) ^ 2)) := by
  dsimp only
  simp only [tracePullbackAddChar_apply]
  rw [← trace_surviving_exponent B₁ K,
    trace_trans F B₁ K, ← trace_trans F B₂ K, trace_signed_sum B₂ K]
  congr 1
  apply congrArg (trace F B₂)
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    congr 1
    dsimp only [Linear.linearTrace]
    rw [hd]
    congr 1
    ring
  · congr 1
    dsimp only [Quadratic.quadraticTrace, Quadratic.quadraticSummand,
      Quadratic.quadraticFunction, Quadratic.quadraticInner]
    rw [hd]
    congr 1
    ring


set_option maxHeartbeats 800000 in
/-- **Paper Proposition 9.13 (`O:Q:logentry`)**. The first factor is the
actual quotient of the primitive compatible quasi-characters. Its full
logarithm chart is the one provided by the accepted minimal-model construction.
The equality retains every alternating sign and the exceptional coefficient
`1/(2(p-1)^2)`, and evaluates only genuine `B₂` traces in the `B₂` character.
The discarded weighted expression lies in the whole conductor ideal by
`logarithm_full_kernel`, before this trace transport. -/
theorem logarithm
    (hprime : ¬ p ∣ D.t) (Delta : K) (a : B₂)
    (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hroot : Delta ^ p - Delta = algebraMap B₂ K a)
    (e : LocalAddCharData F) (alpha gamma : Fˣ)
    (halpha : ord F (alpha : F) =
      ((-e.conductor - (D.t₂ : ℤ) - 1 : ℤ) : WithTop ℤ))
    (chi : ContinuousQuasiChar B₁) (phi : ContinuousQuasiChar B₂)
    (hphi : IsMultiplicativeConductor B₂ phi (Models.secondModelConductor D))
    (hcompat : chi.compNorm (S := K) = phi.compNorm (S := K))
    (hprimitive : ¬ ∃ theta : ContinuousQuasiChar F,
      theta.compNorm (S := K) = phi.compNorm (S := K))
    (hchiFormula : ∀ u : unitFiltration B₁ (Models.firstModelDepth D),
      chi u = tracePullbackAddChar F B₁ e.character
        (algebraMap F B₁ (alpha : F) * norm B₁ K Delta *
          truncatedLog p (1 - ((u : B₁ˣ) : B₁))))
    {m : ℤ} (hu : ord F ((alpha / gamma : Fˣ) : F) = (m : WithTop ℤ))
    (hm : (D.t : ℤ) < p * m)
    (w : B₂ˣ) (hw : normUnits F B₂ w = gamma / alpha)
    (A₁ : B₁ˣ) (C₂ : B₂ˣ)
    (hA₁ : (A₁ : B₁) = algebraMap F B₁ (gamma : F) +
      algebraMap F B₁ (alpha : F) * norm B₁ K Delta)
    (hC₂ : (C₂ : B₂) = algebraMap F B₂ (gamma : F) -
      algebraMap F B₂ (alpha : F) * (w : B₂) +
      algebraMap F B₂ (alpha : F) * norm B₂ K Delta) :
    (chi A₁ / phi C₂)⁻¹ =
      tracePullbackAddChar F B₂ (scaleAddCharData F e alpha).character
        ((∑ i ∈ Finset.Ico 1 p,
          (-1 : B₂) ^ i / (i : B₂) * Linear.linearTrace D Delta w i) +
          Quadratic.quadraticTrace D Delta w / (2 * (p - 1 : ℕ) ^ 2)) := by
  let z := Delta / algebraMap B₂ K (w : B₂)
  let S := ∑ i ∈ Finset.Ico 1 p, elementarySymmetric B₁ K i z
  let V := ∑ i ∈ Finset.Ico 1 p,
    (-1 : B₁) ^ (i + 1) * trace B₁ K (z ^ i) / (i : B₁)
  let Psi := (scaleAddCharData F e alpha).character
  obtain ⟨hn, Z, N, hZ, hN, _, hNord, hentry⟩ :=
    entry hp hG hres D hprime Delta a hDelta hroot chi phi hphi hcompat hprimitive
      alpha gamma hu hm w hw A₁ C₂ hA₁ hC₂
  change norm B₁ K z = algebraMap F B₁ ((alpha / gamma : Fˣ) : F) * norm B₁ K Delta at hn
  change (Z : K) = 1 + z at hZ
  change (N : B₁) = 1 + norm B₁ K z at hN
  obtain ⟨hd₁, hrF₁, _, _, _⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  obtain ⟨_, hrF₂, _, _, _⟩ := realization_tower_data hp hG hres B₂ D.degree_B₂
  have hword : ord B₂ (w : B₂) = ((-m : ℤ) : WithTop ℤ) := by
    have h := congrArg (fun x : Fˣ => ord F (x : F)) hw
    have hg : gamma / alpha = (alpha / gamma : Fˣ)⁻¹ := by rw [inv_div]
    rw [hg] at h
    simpa only [coe_normUnits, ord_norm, hrF₂, one_nsmul,
      Units.val_inv_eq_inv_val, ord_inv, hu, ← WithTop.LinearOrderedAddCommGroup.coe_neg] using h
  obtain ⟨hE, hkernel⟩ := logarithm_full_kernel hp hG hres hchar D
    Delta a hroot hDelta hprime w m hword hm (N : B₁) hNord
  change S / (N : B₁) ∈ lattice B₁ (Models.firstModelDepth D : ℤ) at hE
  let R : B₁ˣ := normUnits B₁ K Z / N
  have hR : (R : B₁) = 1 + S / (N : B₁) := by
    simp only [R, Units.val_div_eq_div_val, coe_normUnits]
    rw [hZ, norm_one_add_split B₁ K hp.one_le hd₁]
    change (1 + norm B₁ K z + S) / (N : B₁) = _
    rw [← hN, add_div, div_self (Units.ne_zero N)]
  have hq : 0 < Models.firstModelDepth D := by
    have h := le_smul_ceilDiv (b := Models.firstModelConductor D) hp.pos
    change Models.firstModelConductor D ≤ p * Models.firstModelDepth D at h
    have hc : 0 < Models.firstModelConductor D := by simp [Models.firstModelConductor]
    by_contra hq
    have : Models.firstModelDepth D = 0 := by omega
    rw [this, mul_zero] at h
    omega
  have hRmem : R ∈ unitFiltration B₁ (Models.firstModelDepth D) := by
    rw [← Nat.sub_add_cancel hq, mem_unitFiltration_succ_iff_sub_mem_lattice,
      Nat.sub_add_cancel hq, hR, add_sub_cancel_left]
    exact hE
  have hlog : chi R = tracePullbackAddChar F B₁ Psi
      (norm B₁ K Delta * truncatedLog p (-S / (N : B₁))) := by
    have h := hchiFormula ⟨R, hRmem⟩
    simp only [hR, show 1 - (1 + S / (N : B₁)) = -S / (N : B₁) by ring] at h
    rw [h]
    simp only [tracePullbackAddChar_apply, Psi, scaleAddCharData_character_apply]
    congr 1
    rw [mul_assoc, trace_scalar F B₁]
  have haorder : unitOrder F alpha = -e.conductor - (D.t₂ : ℤ) - 1 :=
    WithTop.coe_injective ((ord_coe_eq_unitOrder F alpha).symm.trans halpha)
  have hsc : (scaleAddCharData F e alpha).conductor = -((D.t₂ + 1 : ℕ) : ℤ) := by
    rw [scaleAddCharData_conductor, haorder]
    push_cast
    ring
  have hPsiF : IsAdditiveConductor F Psi (-((D.t₂ + 1 : ℕ) : ℤ)) := by
    rw [← hsc]
    exact (scaleAddCharData F e alpha).isConductor
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F B₁ hrF₁
  have hPsi₁raw := additiveConductor_compTrace_cyclicPrime F B₁
    D.B₁_breaks.1 hrF₁ pi hpi hgen hPsiF
  have hc : (p : ℤ) * (-((D.t₂ + 1 : ℕ) : ℤ)) +
      (((p - 1) * (D.t + 1) : ℕ) : ℤ) = -((D.tPrime + 1 : ℕ) : ℤ) := by
    simp only [D.t₂_eq, D.tPrime_eq, Nat.cast_add, Nat.cast_one,
      Nat.cast_mul, Nat.cast_sub hp.one_le]
    ring
  have hPsi₁ : IsAdditiveConductor B₁ (tracePullbackAddChar F B₁ Psi)
      (-((D.tPrime + 1 : ℕ) : ℤ)) := by
    have hdF₁ : Module.finrank F B₁ = p := D.degree_B₁
    rw [hdF₁, hc] at hPsi₁raw
    exact hPsi₁raw
  have heq : tracePullbackAddChar F B₁ Psi
      (norm B₁ K Delta * truncatedLog p (-S / (N : B₁))) =
      tracePullbackAddChar F B₁ Psi
      (norm B₁ K Delta * (-V / (N : B₁) + trace B₁ K (z ^ (p - 1)) ^ 2 /
        (2 * (p - 1 : ℕ) ^ 2 * (N : B₁) ^ 2))) := by
    apply div_eq_one.mp
    calc
      _ = tracePullbackAddChar F B₁ Psi
          (norm B₁ K Delta * truncatedLog p (-S / (N : B₁)) -
            norm B₁ K Delta * (-V / (N : B₁) + trace B₁ K (z ^ (p - 1)) ^ 2 /
              (2 * (p - 1 : ℕ) ^ 2 * (N : B₁) ^ 2))) :=
        (tracePullbackAddChar F B₁ Psi).toAddChar.map_sub_eq_div _ _ |>.symm
      _ = 1 := by
        apply hPsi₁.trivial
        rw [← mul_sub]
        have hdepth : -(-((D.tPrime + 1 : ℕ) : ℤ)) = 1 + (D.tPrime : ℤ) := by
          push_cast
          ring
        rw [hdepth]
        exact hkernel
  have hW : Linear.transitionNorm D w = ((gamma / alpha : Fˣ) : F) :=
    congrArg (fun x : Fˣ => (x : F)) hw
  have hden : algebraMap B₁ K (N : B₁) =
      1 + algebraMap B₁ K (norm B₁ K Delta) / algebraMap F K (Linear.transitionNorm D w) := by
    rw [hN, hn, map_add, map_one, map_mul,
      ← IsScalarTower.algebraMap_apply F B₁ K, hW]
    have hi : ((alpha / gamma : Fˣ) : F) = (((gamma / alpha : Fˣ) : F))⁻¹ := by
      rw [← Units.val_inv_eq_inv_val, inv_div]
    rw [hi, map_inv₀]
    ring
  exact hentry.trans (hlog.trans (heq.trans (logarithm_transport hp hG D Psi Delta w N hden)))

end Diamond

end
end LanglandsSecondMainLemma.Odd.Q1
