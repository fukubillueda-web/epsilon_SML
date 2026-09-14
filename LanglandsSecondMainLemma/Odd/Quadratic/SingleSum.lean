import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Quadratic.Conjugates

/-!
# Reduction of the quadratic packet to one rational sum

Paper `O:D:onesum`, with the setup `O:D:WPdef` and `O:D:Tbound`.
The two cancellations use only the exact zero sum of the representatives.
For the last signed sum we retain the weaker bound `-(p-2)t` obtained
by subtracting the constant power; its full weighted depth is still at
least `1+p*t₂`. The stronger exact signed power sum is unnecessary here.
All estimates use integer lattices in the common field. The rational
linearization below is exact algebra and uses no factorial denominators.
-/

namespace LanglandsSecondMainLemma.Odd.Quadratic

noncomputable section
open LanglandsFirstMainLemma
open scoped BigOperators

open private pow_mem_int_lattice natCast_mem_int_lattice_zero from
  LanglandsSecondMainLemma.Odd.Total.TranslatedNorm
open private pow_sub_pow_mem_lattice from
  LanglandsSecondMainLemma.Odd.Total.CoefficientExtraction
open private quadraticFunction_sub inner_mem from
  LanglandsSecondMainLemma.Odd.Quadratic.Conjugates
open private realization_tower_data from
  LanglandsSecondMainLemma.Odd.Models.Realization

section Rational

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

private theorem order_zero_ne {x : E} (hx : ord E x = 0) : x ≠ 0 :=
  (ord_ne_top_iff E).1 (by rw [hx]; simp)

private theorem unit_div_sub_mem (a b u v : E) (H : ℤ)
    (_ha : a ∈ lattice E 0) (hb : b ∈ lattice E 0)
    (hu : ord E u = 0) (hv : ord E v = 0)
    (hab : a - b ∈ lattice E H) (huv : u - v ∈ lattice E H) :
    a / u - b / v ∈ lattice E H := by
  rw [div_sub_div _ _ (order_zero_ne E hu) (order_zero_ne E hv)]
  apply (div_mem_lattice_iff E _ _ 0 H (by simp [hu, hv])).2
  have heq : a * v - u * b = (a - b) * v - b * (u - v) := by ring
  rw [heq, zero_add]
  exact (lattice E H).sub_mem
    (by simpa using mul_mem_lattice E hab (show v ∈ lattice E 0 from hv.ge))
    (by simpa using mul_mem_lattice E hb huv)

/-- The secant slope, including its value on the diagonal. -/
private def quadraticSlope (W X Y : E) : E :=
  (1 - X / W * (Y / W)) / ((1 + X / W) ^ 2 * (1 + Y / W) ^ 2)

private theorem slope_mem (W X Y : E)
    (hx : X / W ∈ lattice E 0) (hy : Y / W ∈ lattice E 0)
    (hcx : ord E (1 + X / W) = 0) (hcy : ord E (1 + Y / W) = 0) :
    quadraticSlope E W X Y ∈ lattice E 0 := by
  apply (div_mem_lattice_iff E _ _ 0 0 (by simp [hcx, hcy])).2
  simp only [zero_add]
  apply (lattice E 0).sub_mem (show (1 : E) ∈ lattice E 0 by
    simp only [mem_lattice, ord_one, WithTop.coe_zero, le_refl])
  simpa using mul_mem_lattice E hx hy

private theorem slope_sub_mem (W X Y b : E) (H : ℤ)
    (hx : X / W ∈ lattice E 0) (hy : Y / W ∈ lattice E 0)
    (hb : b / W ∈ lattice E 0)
    (hcx : ord E (1 + X / W) = 0) (hcy : ord E (1 + Y / W) = 0)
    (hcb : ord E (1 + b / W) = 0)
    (hxb : (X - b) / W ∈ lattice E H) (hyb : (Y - b) / W ∈ lattice E H) :
    quadraticSlope E W X Y - quadraticSlope E W b b ∈ lattice E H := by
  have hone : (1 : E) ∈ lattice E 0 := by
    simp only [mem_lattice, ord_one, WithTop.coe_zero, le_refl]
  have hn (u v : E) (hu : u ∈ lattice E 0) (hv : v ∈ lattice E 0) :
      1 - u * v ∈ lattice E 0 :=
    (lattice E 0).sub_mem hone (by simpa using mul_mem_lattice E hu hv)
  apply unit_div_sub_mem E _ _ _ _ H (hn _ _ hx hy) (hn _ _ hb hb)
    (by simp [hcx, hcy]) (by simp [hcb])
  · have heq : (1 - X / W * (Y / W)) - (1 - b / W * (b / W)) =
        -((X - b) / W * (Y / W) + b / W * ((Y - b) / W)) := by ring
    rw [heq]
    apply (lattice E H).neg_mem
    exact (lattice E H).add_mem
      (by simpa using mul_mem_lattice E hxb hy)
      (by simpa using mul_mem_lattice E hb hyb)
  · have hpow (z : E) (hz : ord E (1 + z / W) = 0)
        (hzb : (z - b) / W ∈ lattice E H) :
        (1 + z / W) ^ 2 - (1 + b / W) ^ 2 ∈ lattice E H := by
      have h := pow_sub_pow_mem_lattice E (show 1 + z / W ∈ lattice E 0 from hz.ge)
        (show 1 + b / W ∈ lattice E 0 from hcb.ge)
        (show (1 + z / W) - (1 + b / W) ∈ lattice E H by
          convert hzb using 1; ring) 2
      simpa using h
    have heq : (1 + X / W) ^ 2 * (1 + Y / W) ^ 2 -
        (1 + b / W) ^ 2 * (1 + b / W) ^ 2 =
        ((1 + X / W) ^ 2 - (1 + b / W) ^ 2) * (1 + Y / W) ^ 2 +
          (1 + b / W) ^ 2 * ((1 + Y / W) ^ 2 - (1 + b / W) ^ 2) := by ring
    rw [heq]
    exact (lattice E H).add_mem
      (by
        simpa using mul_mem_lattice E (hpow X hcx hxb)
          (show (1 + Y / W) ^ 2 ∈ lattice E 0 by
            simp only [mem_lattice, ord_pow, hcy, nsmul_zero, WithTop.coe_zero, le_refl]))
      (by
        simpa using mul_mem_lattice E
          (show (1 + b / W) ^ 2 ∈ lattice E 0 by
            simp only [mem_lattice, ord_pow, hcb, nsmul_zero, WithTop.coe_zero, le_refl])
          (hpow Y hcy hyb))

private theorem function_sub_eq (W X Y : E)
    (hx : ord E (1 + X / W) = 0) (hy : ord E (1 + Y / W) = 0) :
    quadraticFunction E W X - quadraticFunction E W Y =
      (X - Y) * quadraticSlope E W X Y := by
  rw [quadraticFunction_sub E W X Y (order_zero_ne E hx) (order_zero_ne E hy)]
  dsimp only [quadraticSlope]
  ring

end Rational

private theorem discard_depths (p t delta M : ℤ)
    (hp : 3 ≤ p) (ht : 0 ≤ t) (hd : 0 ≤ delta) (hM : t + 1 ≤ M) :
    let S := p * (p - 1) * delta
    let K := 1 + p * (t + delta)
    K ≤ p * (p - 1) * (t + delta) + 2 * (p - 1) * M - (p ^ 2 - p - 1) * t ∧
    K ≤ p * (p - 1) * (t + delta) + 2 * (p - 1) * M - (p ^ 2 - 2) * t ∧
    K ≤ S + 2 * (p - 1) * M - (p - 1) * t + p * (t + delta) ∧
    K ≤ 2 * S + (3 * p - 2) * M - (p - 1) * t ∧
    K ≤ 2 * S + 2 * (p - 1) * M - (p - 2) * t := by
  dsimp only
  have hq : 0 ≤ p - 1 := by omega
  have hqt := mul_nonneg hq ht
  have hd₁ := mul_nonneg (mul_nonneg (by omega : 0 ≤ p) (by omega : 0 ≤ p - 2)) hd
  have hd₂ := mul_nonneg (mul_nonneg (by omega : 0 ≤ p) (by omega : 0 ≤ 2 * p - 3)) hd
  have hS := mul_nonneg (mul_nonneg (by omega : 0 ≤ p) hq) hd
  have hM₁ := mul_nonneg (by omega : 0 ≤ 2 * (p - 1)) (by omega : 0 ≤ M - t - 1)
  have hM₂ := mul_nonneg (by omega : 0 ≤ 3 * p - 2) (by omega : 0 ≤ M - t - 1)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

section Diamond

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]
  {p : ℕ} {hp : p.Prime}
  {hG : Nonempty
    (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))}
  (D : Total.OddTotalBreakData (F := F) (K := K) hp hG)

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

local notation "B₁" => D.B₁
local notation "B₂" => D.B₂

local instance : PrimeCyclicExtension F B₁ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₁
    (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.2.2.2.1
local instance : PrimeCyclicExtension B₂ K :=
  PrimeCyclicExtension.ofCyclicPrimeExtension B₂ K
    (Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.2

variable {D} {Delta : K} {a : D.B₂} {w : D.B₂ˣ} {m : ℤ}
  (L : Linear.OddLinearData D Delta a w m)

local notation "P" => (p : ℤ)
local notation "q" => (p - 1 : ℕ)
local notation "M" => ((p : ℤ) * m)
local notation "S" => ((p : ℤ) * (p - 1) * D.delta : ℤ)
local notation "v" => algebraMap B₂ K (w : B₂)
local notation "W" => algebraMap F K (Linear.transitionNorm D w)
local notation "b" => algebraMap B₁ K (norm B₁ K Delta)
local notation "s" => algebraMap B₁ K (Linear.linearS D Delta)
local notation "T" => algebraMap B₁ K (quadraticInner D w Delta)

include L

omit [Module.Free F K] in
private theorem translate_order (xi : F) (hxi : xi ∈ lattice F 0) :
    ord K (Delta + algebraMap F K xi) = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) := by
  have hc : 0 ≤ ord K (algebraMap F K xi) := by
    rw [ord_algebraMap]
    exact nsmul_nonneg hxi _
  rw [(ord K).map_add_eq_of_lt_left (by
    rw [L.Delta_order]
    exact (WithTop.coe_lt_coe.mpr (by have := D.t_pos; omega : -(D.t : ℤ) < 0)).trans_le hc),
    L.Delta_order]

omit [Module.Free F K] in
private theorem translate_norm_order (hres : residueDegree F K = 1)
    (xi : F) (hxi : xi ∈ lattice F 0) :
    ord K (algebraMap B₁ K (norm B₁ K (Delta + algebraMap F K xi))) =
      ((-(P * D.t) : ℤ) : WithTop ℤ) := by
  obtain ⟨_, _, hr, _, he⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  rw [ord_algebraMap, ord_norm, hr, one_nsmul, translate_order L xi hxi, he,
    ← WithTop.coe_nsmul]
  simp only [nsmul_eq_mul, mul_neg]

omit [Module.Free F K] in
private theorem shift_norm_remainder (hres : residueDegree F K = 1)
    (xi : F) (hxi : xi ∈ lattice F 0) (hroot : xi ^ p = xi) :
    algebraMap B₁ K (norm B₁ K (Delta + algebraMap F K xi)) - b -
        algebraMap F K xi + algebraMap F K xi * s ∈ lattice K (S + P * D.t) := by
  classical
  obtain ⟨hd, _, _, _, _⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  let c : B₁ := algebraMap F B₁ xi
  let e (i : ℕ) : B₁ := elementarySymmetric B₁ K i Delta * c ^ (p - i)
  have hp3 : 3 ≤ p := by have := D.odd_prime; omega
  have hn := (Total.filteredNormPolynomial_eval B₁ K Delta c).symm
  simp only [Total.filteredNormPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, hd] at hn
  change norm B₁ K (Delta + algebraMap B₁ K c) = ∑ i ∈ Finset.range (p + 1), e i at hn
  have hsplit : (∑ i ∈ Finset.range p, e i) =
      (∑ i ∈ Finset.range (p - 1), e i) + e (p - 1) := by
    simpa only [Nat.sub_add_cancel hp.one_le] using Finset.sum_range_succ e (p - 1)
  rw [Finset.sum_range_succ, hsplit] at hn
  have hlo : (∑ i ∈ Finset.range (p - 1), e i) =
      (∑ i ∈ Finset.Ico 1 (p - 1), e i) + e 0 := by
    rw [Finset.sum_Ico_eq_sub _ (by omega), Finset.sum_range_one, sub_add_cancel]
  rw [hlo] at hn
  have he0 : e 0 = c := by simp [e, c, ← map_pow, hroot]
  have hep : e p = norm B₁ K Delta := by simp [e, ← hd]
  have heq : e (p - 1) = -c * Linear.linearS D Delta := by
    simp [e, Linear.linearS, show p - (p - 1) = 1 by omega, mul_comm]
  rw [he0, hep, heq] at hn
  have heqK : algebraMap B₁ K (norm B₁ K (Delta + algebraMap F K xi)) - b -
      algebraMap F K xi + algebraMap F K xi * s =
      ∑ i ∈ Finset.Ico 1 (p - 1), algebraMap B₁ K (e i) := by
    have h := congrArg (algebraMap B₁ K) hn
    simp only [map_add, map_mul, map_neg, map_sum, c,
      ← IsScalarTower.algebraMap_apply F B₁ K] at h
    linear_combination h
  rw [heqK]
  apply sum_mem_lattice K
  intro i hi
  obtain ⟨hi, hip⟩ := Finset.mem_Ico.mp hi
  have hc : algebraMap B₁ K c ∈ lattice K 0 := by
    simp only [c, ← IsScalarTower.algebraMap_apply F B₁ K, mem_lattice, ord_algebraMap]
    exact nsmul_nonneg hxi _
  have h := mul_mem_lattice K (L.symmetric_order i hi (by omega))
    (pow_mem_int_lattice K hc (p - i))
  simp only [mul_zero, add_zero] at h
  apply lattice_antitone K _ (show algebraMap B₁ K (e i) ∈
    lattice K (P * ((P - 1) * D.t₂ - (i : ℤ) * D.t)) by
      simpa only [e, map_mul, map_pow] using h)
  have hiZ : (i : ℤ) ≤ P - 2 := by omega
  have hz := mul_nonneg (by omega : 0 ≤ P - 2 - i) (Int.natCast_nonneg D.t)
  have hz' := mul_nonneg (Int.natCast_nonneg p) hz
  rw [D.t₂_eq]
  push_cast
  nlinarith

/-- The normalized power trace `U_j` from the proof of `O:D:onesum`. -/
private def powerTrace (j : ℕ) : K :=
  algebraMap B₁ K (trace B₁ K (Delta ^ j / v ^ q))

omit [Module.Free F K] in
private theorem inverse_power_mem : v⁻¹ ^ q ∈ lattice K ((P - 1) * M) := by
  rw [mem_lattice, ord_pow, ord_inv, L.w_order_K,
    ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_nsmul]
  simp only [nsmul_eq_mul, neg_neg, Nat.cast_sub hp.one_le, Nat.cast_one, le_refl]

omit [Module.Free F K] in
private theorem powerTrace_mem (j : ℕ) (hj : j < p) :
    powerTrace (D := D) (Delta := Delta) (w := w) j ∈
      lattice K (P * ((P - 1) * D.t₂ - (j : ℤ) * D.t) + (P - 1) * M) := by
  have h := L.crossed_trace_order ((w : B₂)⁻¹ ^ q) j hj
  have hw : ord K (algebraMap B₂ K ((w : B₂)⁻¹ ^ q)) =
      (((P - 1) * M : ℤ) : WithTop ℤ) := by
    rw [map_pow, map_inv₀, ord_pow, ord_inv, L.w_order_K,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_nsmul]
    simp only [nsmul_eq_mul, neg_neg, Nat.cast_sub hp.one_le, Nat.cast_one]
  rw [hw, ← WithTop.coe_add] at h
  simpa only [mem_lattice, powerTrace, div_eq_mul_inv, inv_pow, map_pow, map_inv₀, mul_comm] using h

omit [Module.Free F K] [IsGalois F K] L in
private theorem inner_expansion (xi : F) :
    algebraMap B₁ K (quadraticInner D w (Delta + algebraMap F K xi)) =
      ∑ j ∈ Finset.range (q + 1),
        ((q).choose j : K) * algebraMap F K xi ^ (q - j) *
          powerTrace (D := D) (Delta := Delta) (w := w) j := by
  have heq : ((Delta + algebraMap F K xi) / v) ^ q =
      ∑ j ∈ Finset.range (q + 1),
        (((q).choose j : B₁) * algebraMap F B₁ xi ^ (q - j)) • (Delta ^ j / v ^ q) := by
    rw [div_pow, add_pow, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Algebra.smul_def, map_mul, map_pow, map_natCast,
      ← IsScalarTower.algebraMap_apply F B₁ K]
    ring
  simp only [quadraticInner, heq, map_sum, map_smul]
  simp only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply,
    map_mul, map_pow, map_natCast, ← IsScalarTower.algebraMap_apply F B₁ K, powerTrace,
    mul_assoc]

omit [Module.Free F K] in
private theorem inner_remainder (xi : F) (hxi : xi ∈ lattice F 0) :
    algebraMap B₁ K (quadraticInner D w (Delta + algebraMap F K xi)) - T -
      (q : K) * algebraMap F K xi *
        powerTrace (D := D) (Delta := Delta) (w := w) (p - 2) ∈
      lattice K (P * ((P - 1) * D.t₂ - (P - 3) * D.t) + (P - 1) * M) := by
  classical
  have hp3 : 3 ≤ p := by have := D.odd_prime; omega
  let c : K := algebraMap F K xi
  let U := powerTrace (D := D) (Delta := Delta) (w := w)
  let term (j : ℕ) : K := ((q).choose j : K) * c ^ (q - j) * U j
  have hUq : U q = T := by simp only [U, powerTrace, quadraticInner, div_pow]
  have heq : algebraMap B₁ K (quadraticInner D w (Delta + c)) - T -
      (q : K) * c * U (p - 2) = ∑ j ∈ Finset.range (p - 2), term j := by
    rw [inner_expansion (D := D) (Delta := Delta) (w := w) xi, Finset.sum_range_succ]
    change (∑ j ∈ Finset.range q, term j) + term q - T - (q : K) * c * U (p - 2) = _
    have hsplit : (∑ j ∈ Finset.range q, term j) =
        (∑ j ∈ Finset.range (p - 2), term j) + term (p - 2) := by
      convert Finset.sum_range_succ term (p - 2) using 1
      rw [show p - 2 + 1 = q by omega]
    rw [hsplit]
    have htop : term q = T := by simp [term, hUq]
    have hnext : term (p - 2) = (q : K) * c * U (p - 2) := by
      have he : p - 2 = q - 1 := by omega
      simp [term, he, (Nat.choose_symm (by omega : 1 ≤ q)).trans (Nat.choose_one_right q),
        show q - (q - 1) = 1 by omega]
    rw [htop, hnext]
    ring
  rw [heq]
  apply sum_mem_lattice K
  intro j hj
  have hjp : j ≤ p - 3 := by have := Finset.mem_range.mp hj; omega
  have hc : c ∈ lattice K 0 := by
    rw [mem_lattice, ord_algebraMap]
    exact nsmul_nonneg hxi _
  have hscalar : ((q).choose j : K) * c ^ (q - j) ∈ lattice K 0 := by
    simpa only [mul_zero, zero_add] using mul_mem_lattice K
      (natCast_mem_int_lattice_zero K _) (pow_mem_int_lattice K hc _)
  have h := mul_mem_lattice K hscalar (powerTrace_mem L j (by omega))
  simp only [zero_add] at h
  apply lattice_antitone K _ h
  have hjZ : (j : ℤ) ≤ P - 3 := by omega
  have hz := mul_nonneg (by omega : 0 ≤ P - 3 - j) (Int.natCast_nonneg D.t)
  nlinarith [mul_nonneg (Int.natCast_nonneg p)
    (by nlinarith : 0 ≤ (P - 3) * D.t - j * D.t)]

omit [Module.Free F K] in
private theorem ratio_mem (X : K) (hX : ord K X = ((-(P * D.t) : ℤ) : WithTop ℤ)) :
    X / W ∈ lattice K 0 := by
  rw [mem_lattice, ord_div, hX, L.W_order_K,
    ← WithTop.LinearOrderedAddCommGroup.coe_sub, WithTop.coe_le_coe]
  have h := mul_nonneg (Int.natCast_nonneg p) (show 0 ≤ M - D.t by have := L.transition; omega)
  nlinarith

omit [Module.Free F K] in
private theorem base_translate_order (xi : F) (hxi : xi ∈ lattice F 0) :
    ord K (b + algebraMap F K xi) = ((-(P * D.t) : ℤ) : WithTop ℤ) := by
  have hc : 0 ≤ ord K (algebraMap F K xi) := by
    rw [ord_algebraMap]
    exact nsmul_nonneg hxi _
  rw [(ord K).map_add_eq_of_lt_left (by
    rw [L.b_order_K]
    apply lt_of_lt_of_le _ hc
    apply WithTop.coe_lt_coe.mpr
    exact neg_neg_of_pos (mul_pos (by exact_mod_cast hp.pos) (by exact_mod_cast D.t_pos))),
    L.b_order_K]

omit [Module.Free F K] in
private theorem power_shift_mem (xi : F) (hxi : xi ∈ lattice F 0) :
    ((Delta + algebraMap F K xi) / v) ^ q ∈ lattice K ((P - 1) * (M - D.t)) ∧
    ((Delta + algebraMap F K xi) / v) ^ q - (Delta / v) ^ q ∈
      lattice K ((P - 1) * M - (P - 2) * D.t) := by
  have hp3 : 3 ≤ p := by have := D.odd_prime; omega
  have hDelta : Delta ∈ lattice K (-(D.t : ℤ)) := L.Delta_order.ge
  have hshift : Delta + algebraMap F K xi ∈ lattice K (-(D.t : ℤ)) :=
    (translate_order L xi hxi).ge
  constructor
  · have h := mul_mem_lattice K (pow_mem_int_lattice K hshift q) (inverse_power_mem L)
    simp only [div_eq_mul_inv, mul_pow]
    convert h using 1
    congr 1
    push_cast [Nat.cast_sub hp.one_le]
    ring
  · have hc : (Delta + algebraMap F K xi) - Delta ∈ lattice K 0 := by
      rw [add_sub_cancel_left, mem_lattice, ord_algebraMap]
      exact nsmul_nonneg hxi _
    have h := mul_mem_lattice K (pow_sub_pow_mem_lattice K hshift hDelta hc q)
      (inverse_power_mem L)
    have heq : ((Delta + algebraMap F K xi) / v) ^ q - (Delta / v) ^ q =
        ((Delta + algebraMap F K xi) ^ q - Delta ^ q) * v⁻¹ ^ q := by
      simp only [div_eq_mul_inv, mul_pow]
      ring
    rw [heq]
    convert h using 1
    congr 1
    push_cast [Nat.cast_sub (show 1 ≤ q by omega), Nat.cast_sub hp.one_le]
    ring

omit [Module.Free F K] in
private theorem norm_shift_bounds (hres : residueDegree F K = 1)
    (xi : F) (hxi : xi ∈ lattice F 0) (hroot : xi ^ p = xi) :
    let X := algebraMap B₁ K (norm B₁ K (Delta + algebraMap F K xi))
    (X - b ∈ lattice K 0) ∧
    (X - (b + algebraMap F K xi) ∈ lattice K S) ∧
    (X - (b + algebraMap F K xi) + algebraMap F K xi * s ∈ lattice K (P * D.t₂)) := by
  dsimp only
  have hp3 : 3 ≤ p := by have := D.odd_prime; omega
  have hS : 0 ≤ S := mul_nonneg
    (mul_nonneg (Int.natCast_nonneg p) (by omega)) (Int.natCast_nonneg D.delta)
  have hc : algebraMap F K xi ∈ lattice K 0 := by
    rw [mem_lattice, ord_algebraMap]
    exact nsmul_nonneg hxi _
  have hcs : algebraMap F K xi * s ∈ lattice K S := by
    simpa only [zero_add] using mul_mem_lattice K hc L.s_order
  have hr := shift_norm_remainder L hres xi hxi hroot
  have hrS := lattice_antitone K (le_add_of_nonneg_right (mul_nonneg (Int.natCast_nonneg p) (Int.natCast_nonneg D.t))) hr
  have hdiff := (lattice K S).sub_mem hrS hcs
  simp only [add_sub_cancel_right] at hdiff
  have hdiff' : algebraMap B₁ K (norm B₁ K (Delta + algebraMap F K xi)) -
      (b + algebraMap F K xi) ∈ lattice K S := by
    simpa only [sub_add_eq_sub_sub] using hdiff
  refine ⟨?_, hdiff', ?_⟩
  · have h := (lattice K 0).add_mem (lattice_antitone K hS hdiff) hc
    simpa only [sub_add_cancel] using h
  · apply lattice_antitone K _ (show _ ∈ lattice K (S + P * D.t) by
      simpa only [sub_add_eq_sub_sub] using hr)
    rw [D.t₂_eq]
    push_cast
    have hz := mul_nonneg (mul_nonneg (Int.natCast_nonneg p) (by omega : 0 ≤ P - 2))
      (Int.natCast_nonneg D.delta)
    nlinarith

omit [Module.Free F K] in
private theorem divide_integral_mem (z : K) (hz : z ∈ lattice K 0) :
    z / W ∈ lattice K (P * M) := by
  apply (div_mem_lattice_iff K _ _ (- (P ^ 2 * m)) (P * M) L.W_order_K).2
  convert hz using 1
  congr 1
  ring

omit [Module.Free F K] in
/-- Both outer weights are present in the norm linearization. The common
slope is evaluated at the original norm `b`; it is not an assumed phase. -/
private theorem norm_function_linearization (hres : residueDegree F K = 1)
    (xi : F) (hxi : xi ∈ lattice F 0) (hroot : xi ^ p = xi) :
    T * ((Delta + algebraMap F K xi) / v) ^ q *
      (quadraticFunction K W (algebraMap B₁ K (norm B₁ K (Delta + algebraMap F K xi))) -
        quadraticFunction K W (b + algebraMap F K xi) +
          algebraMap F K xi * s * quadraticSlope K W b b) ∈
      lattice K (1 + P * D.t₂) := by
  let c : K := algebraMap F K xi
  let X : K := algebraMap B₁ K (norm B₁ K (Delta + c))
  let Y : K := b + c
  let k : K := quadraticSlope K W b b
  let weight : K := T * ((Delta + c) / v) ^ q
  have hp3 : 3 ≤ p := by have := D.odd_prime; omega
  have hpZ : (3 : ℤ) ≤ P := by exact_mod_cast hp3
  have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
  have depths := discard_depths P D.t D.delta M hpZ (Int.natCast_nonneg _)
    (Int.natCast_nonneg _) L.transition
  dsimp only at depths
  rw [← ht₂] at depths
  obtain ⟨hxb, hxy, hr⟩ := norm_shift_bounds L hres xi hxi hroot
  have hx := translate_norm_order L hres xi hxi
  have hy := base_translate_order L xi hxi
  have hcx := L.denominator_order X hx
  have hcy := L.denominator_order Y hy
  have hcb := L.denominator_order b L.b_order_K
  have hk : k ∈ lattice K 0 := slope_mem K W b b
    (ratio_mem L b L.b_order_K) (ratio_mem L b L.b_order_K) hcb hcb
  have hc : c ∈ lattice K 0 := by
    rw [mem_lattice, ord_algebraMap]
    exact nsmul_nonneg hxi _
  have hsl : quadraticSlope K W X Y - k ∈ lattice K (P * M) := by
    apply slope_sub_mem K W X Y b (P * M) (ratio_mem L X hx) (ratio_mem L Y hy)
      (ratio_mem L b L.b_order_K) hcx hcy hcb (divide_integral_mem L _ hxb)
    apply divide_integral_mem L
    simpa only [Y, add_sub_cancel_left] using hc
  have hwgt : weight ∈ lattice K (S + 2 * (P - 1) * M - (P - 1) * D.t) := by
    have h := mul_mem_lattice K (inner_mem L) (power_shift_mem L xi hxi).1
    convert h using 1
    congr 1
    ring
  have he₁ := mul_mem_lattice K hwgt (mul_mem_lattice K hxy hsl)
  have he₂ := mul_mem_lattice K hwgt (mul_mem_lattice K hr hk)
  have heq : weight * (quadraticFunction K W X - quadraticFunction K W Y + c * s * k) =
      weight * ((X - Y) * (quadraticSlope K W X Y - k)) +
        weight * ((X - Y + c * s) * k) := by
    rw [function_sub_eq K W X Y hcx hcy]
    ring
  change weight * (quadraticFunction K W X - quadraticFunction K W Y + c * s * k) ∈ _
  rw [heq]
  apply (lattice K _).add_mem
  · apply lattice_antitone K _ he₁
    convert depths.2.2.2.1 using 1; ring
  · apply lattice_antitone K _ he₂
    convert depths.2.2.1 using 1; ring

omit [Module.Free F K] in
/-- The product multiplying the translated inner trace changes integrally
in its norm factor and gains one coordinate power in its other factor. -/
private theorem outer_function_difference (hres : residueDegree F K = 1)
    (xi : F) (hxi : xi ∈ lattice F 0) (hroot : xi ^ p = xi) :
    quadraticFunction K W (algebraMap B₁ K (norm B₁ K (Delta + algebraMap F K xi))) *
        ((Delta + algebraMap F K xi) / v) ^ q -
      quadraticFunction K W b * (Delta / v) ^ q ∈
        lattice K ((P - 1) * M - 2 * (P - 1) * D.t) := by
  let X : K := algebraMap B₁ K (norm B₁ K (Delta + algebraMap F K xi))
  have hx := translate_norm_order L hres xi hxi
  have hcx := L.denominator_order X hx
  have hcb := L.denominator_order b L.b_order_K
  have hfX : quadraticFunction K W X ∈ lattice K (-(P * D.t)) := by
    rw [mem_lattice, quadraticFunction, ord_div, ord_pow, hcx, hx]
    simp only [nsmul_zero, sub_zero, le_refl]
  have hfd : quadraticFunction K W X - quadraticFunction K W b ∈ lattice K 0 := by
    rw [function_sub_eq K W X b hcx hcb]
    simpa only [zero_add] using mul_mem_lattice K (norm_shift_bounds L hres xi hxi hroot).1
      (slope_mem K W X b (ratio_mem L X hx) (ratio_mem L b L.b_order_K) hcx hcb)
  have hpow0 : (Delta / v) ^ q ∈ lattice K ((P - 1) * (M - D.t)) := by
    simpa only [map_zero, add_zero] using
      (power_shift_mem L 0 ((lattice F 0).zero_mem)).1
  have heq : quadraticFunction K W X * ((Delta + algebraMap F K xi) / v) ^ q -
      quadraticFunction K W b * (Delta / v) ^ q =
      quadraticFunction K W X * (((Delta + algebraMap F K xi) / v) ^ q - (Delta / v) ^ q) +
        (quadraticFunction K W X - quadraticFunction K W b) * (Delta / v) ^ q := by ring
  rw [heq]
  apply (lattice K _).add_mem
  · convert mul_mem_lattice K hfX (power_shift_mem L xi hxi).2 using 1
    congr 1
    ring
  · apply lattice_antitone K _ (mul_mem_lattice K hfd hpow0)
    have hp3 : 3 ≤ p := by have := D.odd_prime; omega
    have hz := mul_nonneg (by omega : 0 ≤ P - 1) (Int.natCast_nonneg D.t)
    nlinarith

omit [Module.Free F K] in
/-- Discard the lower inner-trace terms only after multiplying by the
rational norm factor and the outer power. The degree `p-2` term uses the
zero sum of the representatives. -/
private theorem translated_inner_reduction {I : Type*} [Fintype I]
    (hres : residueDegree F K = 1) (xi : I → F)
    (hxi : ∀ j, xi j ∈ lattice F 0) (hroot : ∀ j, xi j ^ p = xi j)
    (hsum : ∑ j, xi j = 0) :
    (∑ j, quadraticSummand D w (Delta + algebraMap F K (xi j))) -
      (∑ j, quadraticFunction K W
        (algebraMap B₁ K (norm B₁ K (Delta + algebraMap F K (xi j)))) *
          ((Delta + algebraMap F K (xi j)) / v) ^ q * T) ∈
      lattice K (1 + P * D.t₂) := by
  classical
  let c (j : I) : K := algebraMap F K (xi j)
  let A (j : I) : K := quadraticFunction K W
    (algebraMap B₁ K (norm B₁ K (Delta + c j))) * ((Delta + c j) / v) ^ q
  let A₀ : K := quadraticFunction K W b * (Delta / v) ^ q
  let U : K := powerTrace (D := D) (Delta := Delta) (w := w) (p - 2)
  have hp3 : 3 ≤ p := by have := D.odd_prime; omega
  have hpZ : (3 : ℤ) ≤ P := by exact_mod_cast hp3
  have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
  have depths := discard_depths P D.t D.delta M hpZ (Int.natCast_nonneg _)
    (Int.natCast_nonneg _) L.transition
  dsimp only at depths
  rw [← ht₂] at depths
  have hU : U ∈ lattice K (P * ((P - 1) * D.t₂ - (P - 2) * D.t) + (P - 1) * M) := by
    simpa only [Nat.cast_sub (show 2 ≤ p by omega), Nat.cast_ofNat] using
      powerTrace_mem L (p - 2) (by omega)
  have hterm (j : I) : quadraticSummand D w (Delta + c j) - A j * T -
      A₀ * (q : K) * c j * U ∈ lattice K (1 + P * D.t₂) := by
    have hc : c j ∈ lattice K 0 := by
      rw [mem_lattice, ord_algebraMap]
      exact nsmul_nonneg (hxi j) _
    have hqc : (q : K) * c j ∈ lattice K 0 := by
      simpa only [zero_add] using mul_mem_lattice K (natCast_mem_int_lattice_zero K q) hc
    have hX := translate_norm_order L hres (xi j) (hxi j)
    have hden := L.denominator_order _ hX
    have hf : quadraticFunction K W
        (algebraMap B₁ K (norm B₁ K (Delta + c j))) ∈ lattice K (-(P * D.t)) := by
      rw [mem_lattice, quadraticFunction, ord_div, ord_pow, hden, hX]
      simp only [nsmul_zero, sub_zero, le_refl]
    have hA : A j ∈ lattice K (-(P * D.t) + (P - 1) * (M - D.t)) :=
      mul_mem_lattice K hf (power_shift_mem L (xi j) (hxi j)).1
    have heq : quadraticSummand D w (Delta + c j) - A j * T - A₀ * (q : K) * c j * U =
        A j * (algebraMap B₁ K (quadraticInner D w (Delta + c j)) - T - (q : K) * c j * U) +
          (A j - A₀) * ((q : K) * c j) * U := by
      dsimp only [quadraticSummand, A]
      ring
    rw [heq]
    apply (lattice K _).add_mem
    · apply lattice_antitone K _ (mul_mem_lattice K hA (inner_remainder L (xi j) (hxi j)))
      convert depths.1 using 1; ring
    · have h := mul_mem_lattice K
        (mul_mem_lattice K (outer_function_difference L hres (xi j) (hxi j) (hroot j)) hqc) hU
      apply lattice_antitone K _ h
      convert depths.2.1 using 1; ring
  have hzero : ∑ j, A₀ * (q : K) * c j * U = 0 := by
    simp only [← Finset.sum_mul, ← Finset.mul_sum, c, ← map_sum, hsum, map_zero, mul_zero, zero_mul]
  have h := sum_mem_lattice K (fun j (_ : j ∈ Finset.univ) => hterm j)
  simpa only [Finset.sum_sub_distrib, hzero, sub_zero, A, c] using h

omit [Module.Free F K] in
/-- The final signed correction needs only `sum xi = 0`: subtracting the
constant outer power gives a bound sufficient with both `T` and `s`.
No exact power-sum identity is introduced as a hypothesis. -/
private theorem translated_norm_reduction {I : Type*} [Fintype I]
    (hres : residueDegree F K = 1) (xi : I → F)
    (hxi : ∀ j, xi j ∈ lattice F 0) (hroot : ∀ j, xi j ^ p = xi j)
    (hsum : ∑ j, xi j = 0) :
    (∑ j, quadraticFunction K W
      (algebraMap B₁ K (norm B₁ K (Delta + algebraMap F K (xi j)))) *
        ((Delta + algebraMap F K (xi j)) / v) ^ q * T) -
    (∑ j, quadraticFunction K W (b + algebraMap F K (xi j)) *
        ((Delta + algebraMap F K (xi j)) / v) ^ q * T) ∈
      lattice K (1 + P * D.t₂) := by
  classical
  let c (j : I) : K := algebraMap F K (xi j)
  let A (j : I) : K := ((Delta + c j) / v) ^ q
  let k : K := quadraticSlope K W b b
  have hp3 : 3 ≤ p := by have := D.odd_prime; omega
  have hpZ : (3 : ℤ) ≤ P := by exact_mod_cast hp3
  have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
  have depths := discard_depths P D.t D.delta M hpZ (Int.natCast_nonneg _)
    (Int.natCast_nonneg _) L.transition
  dsimp only at depths
  rw [← ht₂] at depths
  have hsumc : ∑ j, c j = 0 := by simp only [c, ← map_sum, hsum, map_zero]
  have hsumA : (∑ j, c j * A j) ∈ lattice K ((P - 1) * M - (P - 2) * D.t) := by
    have heq : (∑ j, c j * A j) = ∑ j, c j * (A j - (Delta / v) ^ q) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsumc, zero_mul, sub_zero]
    rw [heq]
    apply sum_mem_lattice K
    intro j _
    have hc : c j ∈ lattice K 0 := by
      rw [mem_lattice, ord_algebraMap]
      exact nsmul_nonneg (hxi j) _
    simpa only [zero_add] using mul_mem_lattice K hc (power_shift_mem L (xi j) (hxi j)).2
  have hk : k ∈ lattice K 0 := slope_mem K W b b
    (ratio_mem L b L.b_order_K) (ratio_mem L b L.b_order_K)
    (L.denominator_order b L.b_order_K) (L.denominator_order b L.b_order_K)
  have hsigned : (∑ j, T * A j * (c j * s * k)) ∈ lattice K (1 + P * D.t₂) := by
    have heq : (∑ j, T * A j * (c j * s * k)) = T * s * k * ∑ j, c j * A j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    have h := mul_mem_lattice K (mul_mem_lattice K (mul_mem_lattice K (inner_mem L) L.s_order) hk) hsumA
    apply lattice_antitone K _ h
    convert depths.2.2.2.2 using 1; ring
  have herr := sum_mem_lattice K (fun j (_ : j ∈ Finset.univ) =>
    norm_function_linearization L hres (xi j) (hxi j) (hroot j))
  have h := (lattice K (1 + P * D.t₂)).sub_mem herr hsigned
  convert h using 1
  dsimp only [A, c, k]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, add_sub_cancel_right]
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Paper `O:D:onesum` (Lemma 9.10). The actual quadratic trace in `B₂`
is congruent, in the common field at the full modulus `1+p*t₂`, to the
complete rational sum over `{0} ∪ μ_(p-1)`. The coordinate, crossed norm,
inner trace, and denominator are those of the supplied `OddLinearData`,
which has the proved constructor `Odd.Linear.oddLinearData_construct`.
Both field characteristics and every odd prime are included. -/
theorem singleSum (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = p) :
    letI : Fact p.Prime := ⟨hp⟩
    algebraMap B₂ K (quadraticTrace D Delta w) -
      T / v ^ q * (∑ j : ZMod p,
        (Delta + algebraMap F K (primeTeichmuller F p hchar j : F)) ^ q *
          quadraticFunction K W
            (b + algebraMap F K (primeTeichmuller F p hchar j : F))) ∈
      lattice K (1 + P * D.t₂) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let xi (j : ZMod p) : F := primeTeichmuller F p hchar j
  have hxi (j : ZMod p) : xi j ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (primeTeichmuller F p hchar j).property
  have hroot (j : ZMod p) : xi j ^ p = xi j := by
    dsimp only [xi]
    exact_mod_cast primeTeichmuller_pow_residueCharacteristic F p hchar j
  have hsum : ∑ j, xi j = 0 := by
    have h := congrArg ((ValuativeRel.valuation F).integer.subtype)
      (sum_primeTeichmuller F p hchar)
    simpa [xi, show p ≠ 2 by have := D.odd_prime; omega] using h
  obtain ⟨_, _, _, hconj⟩ := conjugates D hres hchar Delta a w m L
  have hinner := translated_inner_reduction L hres xi hxi hroot hsum
  have hnorm := translated_norm_reduction L hres xi hxi hroot hsum
  have h := (lattice K (1 + P * D.t₂)).add_mem
    ((lattice K (1 + P * D.t₂)).add_mem hconj hinner) hnorm
  have htotal : algebraMap B₂ K (quadraticTrace D Delta w) -
      (∑ j : ZMod p, quadraticFunction K W (b + algebraMap F K (xi j)) *
        ((Delta + algebraMap F K (xi j)) / v) ^ q * T) ∈ lattice K (1 + P * D.t₂) := by
    convert h using 1
    dsimp only [xi]
    ring
  have heq : (∑ j : ZMod p,
      quadraticFunction K W (b + algebraMap F K (xi j)) *
        ((Delta + algebraMap F K (xi j)) / v) ^ q * T) =
      T / v ^ q * (∑ j : ZMod p,
        (Delta + algebraMap F K (xi j)) ^ q *
          quadraticFunction K W (b + algebraMap F K (xi j))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [div_pow]
    ring
  rw [heq] at htotal
  exact htotal

end Diamond
end
end LanglandsSecondMainLemma.Odd.Quadratic
