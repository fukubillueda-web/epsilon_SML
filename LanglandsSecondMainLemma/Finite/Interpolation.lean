import Mathlib

/-!
# Finite interpolation over Teichmuller representatives

This file proves paper Lemma `O:D:interpolation`.  The finset
`teichmullerUnits K p` is the full set of `(p - 1)`-st roots of unity in `K`,
and `teichmullerSet K p` adjoins zero.  A primitive root witnesses that this
set has exactly the expected representatives.  The proofs are algebraic and
therefore apply unchanged in characteristic zero and characteristic `p`.

Besides the rational interpolation formula and its two power sums, the file
proves the exact differentiated identity by factoring `X ^ p - X` over the
representative set and differentiating that finite product twice.
-/

namespace LanglandsSecondMainLemma.Finite

noncomputable section

open scoped BigOperators
open Finset Polynomial

variable {K : Type*} [Field K]

/-- The nonzero Teichmuller representatives: all `(p - 1)`-st roots of unity. -/
def teichmullerUnits (K : Type*) [Field K] (p : ℕ) : Finset K :=
  nthRootsFinset (p - 1) (1 : K)

/-- The `p` Teichmuller representatives `{0} ∪ μ_(p-1)`. -/
def teichmullerSet (K : Type*) [Field K] (p : ℕ) : Finset K :=
  haveI := Classical.decEq K
  insert 0 (teichmullerUnits K p)

private lemma sum_teichmullerUnits_eq_sum_range {p : ℕ} {zeta : K}
    (hzeta : IsPrimitiveRoot zeta (p - 1)) (f : K → K) :
    ∑ xi ∈ teichmullerUnits K p, f xi = ∑ j ∈ range (p - 1), f (zeta ^ j) := by
  classical
  have heq : teichmullerUnits K p = (range (p - 1)).image (zeta ^ ·) := by
    simp only [teichmullerUnits, nthRootsFinset_def]
    rw [hzeta.nthRoots_eq (one_pow (p - 1)), Multiset.toFinset_map,
      Multiset.toFinset_range]
    simp only [mul_one]
  rw [heq, sum_image]
  exact fun i hi j hj hij => hzeta.pow_inj (mem_range.mp hi) (mem_range.mp hj) hij

private lemma zero_notMem_teichmullerUnits {p : ℕ} (hp : 2 < p) :
    (0 : K) ∉ teichmullerUnits K p := by
  classical
  rw [teichmullerUnits, mem_nthRootsFinset (by omega : 0 < p - 1)]
  simp only [zero_pow (by omega : p - 1 ≠ 0), zero_ne_one, not_false_eq_true]

private lemma sum_teichmullerSet {p : ℕ} (hp : 2 < p) (f : K → K) :
    ∑ xi ∈ teichmullerSet K p, f xi = f 0 + ∑ xi ∈ teichmullerUnits K p, f xi := by
  classical
  simp [teichmullerSet, zero_notMem_teichmullerUnits hp]

private lemma root_power_sum {n k : ℕ} {zeta : K} (hzeta : IsPrimitiveRoot zeta n) :
    ∑ j ∈ range n, (zeta ^ j) ^ k = if n ∣ k then (n : K) else 0 := by
  classical
  by_cases hdiv : n ∣ k
  · simp only [if_pos hdiv]
    obtain ⟨d, rfl⟩ := hdiv
    have hterm (j : ℕ) : (zeta ^ j) ^ (n * d) = 1 := by
      rw [← pow_mul, show j * (n * d) = n * (j * d) by ac_rfl,
        pow_mul, hzeta.pow_eq_one, one_pow]
    simp_rw [hterm]
    simp
  · simp only [if_neg hdiv]
    have hne : zeta ^ k ≠ 1 := fun h => hdiv (hzeta.dvd_of_pow_eq_one k h)
    have hpow : (zeta ^ k) ^ n = 1 := by
      rw [← pow_mul, mul_comm k n, pow_mul, hzeta.pow_eq_one, one_pow]
    have hgeom : (∑ j ∈ range n, (zeta ^ k) ^ j) * (zeta ^ k - 1) = 0 := by
      rw [geom_sum_mul, hpow, sub_self]
    have : ∑ j ∈ range n, (zeta ^ k) ^ j = 0 := by
      exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne)
    have hterm (j : ℕ) : (zeta ^ j) ^ k = (zeta ^ k) ^ j := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    simpa only [hterm] using this

private lemma teichmullerUnits_power_sum {p k : ℕ} {zeta : K}
    (hzeta : IsPrimitiveRoot zeta (p - 1)) :
    ∑ xi ∈ teichmullerUnits K p, xi ^ k =
      if p - 1 ∣ k then ((p - 1 : ℕ) : K) else 0 := by
  rw [sum_teichmullerUnits_eq_sum_range hzeta]
  exact root_power_sum (k := k) hzeta

private lemma binomial_root_sum {n i : ℕ} (hn : 0 < n) (hi : i ≤ n) (Delta : K) :
    ∑ k ∈ range (i + 1), (i.choose k : K) * Delta ^ (i - k) *
        (if n ∣ k then (n : K) else 0) =
      (n : K) * Delta ^ i + if i = n then (n : K) else 0 := by
  classical
  let F : ℕ → K := fun k => (i.choose k : K) * Delta ^ (i - k) *
    (if n ∣ k then (n : K) else 0)
  by_cases hin : i = n
  · subst i
    rw [show n + 1 = n.succ by omega, sum_range_succ]
    have hfirst : ∑ k ∈ range n, F k = F 0 := by
      apply sum_eq_single 0
      · intro k hk hk0
        have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hkn : k < n := mem_range.mp hk
        simp only [F, if_neg (Nat.not_dvd_of_pos_of_lt hkpos hkn), mul_zero]
      · simp [hn]
    rw [hfirst]
    simp [F, mul_comm]
  · have hil : i < n := lt_of_le_of_ne hi hin
    have hsum : ∑ k ∈ range (i + 1), F k = F 0 := by
      apply sum_eq_single 0
      · intro k hk hk0
        have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hki : k < i + 1 := mem_range.mp hk
        have hkn : k < n := by omega
        simp only [F, if_neg (Nat.not_dvd_of_pos_of_lt hkpos hkn), mul_zero]
      · simp
    rw [hsum]
    simp [F, hin, mul_comm]

private lemma teichmullerUnits_shifted_power_sum {p i : ℕ} {zeta : K} (hp : 2 < p)
    (hzeta : IsPrimitiveRoot zeta (p - 1)) (hi : i < p) (Delta : K) :
    ∑ xi ∈ teichmullerUnits K p, (Delta + xi) ^ i =
      (p - 1 : ℕ) * Delta ^ i +
        if i = p - 1 then ((p - 1 : ℕ) : K) else 0 := by
  classical
  simp_rw [add_comm Delta, add_pow]
  rw [sum_comm]
  calc
    _ = ∑ k ∈ range (i + 1),
        (∑ xi ∈ teichmullerUnits K p, xi ^ k) *
          (Delta ^ (i - k) * (i.choose k : K)) := by
      apply sum_congr rfl
      intro k hk
      rw [Finset.sum_mul]
      simp only [mul_assoc]
    _ = ∑ k ∈ range (i + 1), (i.choose k : K) * Delta ^ (i - k) *
        (∑ xi ∈ teichmullerUnits K p, xi ^ k) := by
      apply sum_congr rfl
      intro k hk
      ring
    _ = _ := by
      simp_rw [teichmullerUnits_power_sum hzeta]
      exact binomial_root_sum (K := K) (by omega) (Nat.le_sub_one_of_lt hi) Delta

/-- The first power sum in paper Lemma `O:D:interpolation`. -/
lemma teichmullerSet_shifted_power_sum {p i : ℕ} {zeta : K} (hp : 2 < p)
    (hzeta : IsPrimitiveRoot zeta (p - 1)) (hi : i < p) (Delta : K) :
    ∑ xi ∈ teichmullerSet K p, (Delta + xi) ^ i =
      (p : K) * Delta ^ i +
        if i = p - 1 then ((p - 1 : ℕ) : K) else 0 := by
  rw [sum_teichmullerSet hp, teichmullerUnits_shifted_power_sum hp hzeta hi]
  have hpcast : (p : K) = (1 : K) + (p - 1 : ℕ) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    congr
    omega
  rw [hpcast]
  split_ifs
  · ring
  · ring

private lemma weighted_binomial_root_sum {n i : ℕ} (hn : 1 < n)
    (hi0 : 0 < i) (hi : i ≤ n) (Delta : K) :
    ∑ k ∈ range (i + 1), (i.choose k : K) * Delta ^ (i - k) *
        (if n ∣ k + 1 then (n : K) else 0) =
      (n : K) * ((if i = n - 1 then (1 : K) else 0) +
        (i : K) * Delta * if i = n then (1 : K) else 0) := by
  classical
  let F : ℕ → K := fun k => (i.choose k : K) * Delta ^ (i - k) *
    (if n ∣ k + 1 then (n : K) else 0)
  by_cases hiTop : i = n
  · subst i
    have hsum : ∑ k ∈ range (n + 1), F k = F (n - 1) := by
      apply sum_eq_single (n - 1)
      · intro k hk hkne
        have hklt : k < n + 1 := mem_range.mp hk
        by_cases hdiv : n ∣ k + 1
        · have heq : k + 1 = n := Nat.eq_of_dvd_of_lt_two_mul
              (by omega) hdiv (by omega)
          exact (hkne (by omega)).elim
        · simp [F, hdiv]
      · simp
    rw [hsum]
    have hpred : n - 1 + 1 = n := by omega
    have hdiff : n - (n - 1) = 1 := by omega
    have hne : n ≠ n - 1 := by omega
    have hchoose : n.choose (n - 1) = n := by
      rw [← hpred]
      exact Nat.choose_succ_self_right (n - 1)
    simp [F, hpred, hdiff, hne, hchoose]
    ring
  · have hil : i < n := lt_of_le_of_ne hi hiTop
    by_cases hiPred : i = n - 1
    · subst i
      have hsum : ∑ k ∈ range (n - 1 + 1), F k = F (n - 1) := by
        apply sum_eq_single (n - 1)
        · intro k hk hkne
          have hklt : k < n - 1 + 1 := mem_range.mp hk
          by_cases hdiv : n ∣ k + 1
          · have heq : k + 1 = n := Nat.eq_of_dvd_of_lt_two_mul
                (by omega) hdiv (by omega)
            exact (hkne (by omega)).elim
          · simp [F, hdiv]
        · simp
      rw [hsum]
      have hpred : n - 1 + 1 = n := by omega
      simp [F, hpred, hiTop]
    · have hiSmall : i < n - 1 := by omega
      have hzero : ∑ k ∈ range (i + 1), F k = 0 := by
        apply sum_eq_zero
        intro k hk
        have hki : k < i + 1 := mem_range.mp hk
        have hkpos : 0 < k + 1 := by omega
        have hklt : k + 1 < n := by omega
        simp [F, Nat.not_dvd_of_pos_of_lt hkpos hklt]
      rw [hzero]
      simp [hiTop, hiPred]

/-- The weighted nonzero power sum in paper Lemma `O:D:interpolation`. -/
lemma teichmullerUnits_weighted_shifted_power_sum {p i : ℕ} {zeta : K}
    (hp : 2 < p) (hzeta : IsPrimitiveRoot zeta (p - 1))
    (hi0 : 0 < i) (hi : i < p) (Delta : K) :
    ∑ xi ∈ teichmullerUnits K p, xi * (Delta + xi) ^ i =
      (p - 1 : ℕ) * ((if i = p - 2 then (1 : K) else 0) +
        (i : K) * Delta * if i = p - 1 then (1 : K) else 0) := by
  classical
  simp_rw [add_comm Delta, add_pow, mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ k ∈ range (i + 1),
        (∑ xi ∈ teichmullerUnits K p, xi ^ (k + 1)) *
          (Delta ^ (i - k) * (i.choose k : K)) := by
      apply sum_congr rfl
      intro k hk
      rw [Finset.sum_mul]
      apply sum_congr rfl
      intro xi hxi
      rw [pow_succ]
      ring
    _ = ∑ k ∈ range (i + 1), (i.choose k : K) * Delta ^ (i - k) *
        (∑ xi ∈ teichmullerUnits K p, xi ^ (k + 1)) := by
      apply sum_congr rfl
      intro k hk
      ring
    _ = _ := by
      simp_rw [teichmullerUnits_power_sum hzeta]
      simpa only [show p - 1 - 1 = p - 2 by omega] using
        weighted_binomial_root_sum (K := K) (n := p - 1) (by omega) hi0
          (Nat.le_sub_one_of_lt hi) Delta

private lemma nonpole_ne {p : ℕ} {Z xi : K}
    (hZ : -Z ∉ teichmullerSet K p) (hxi : xi ∈ teichmullerSet K p) :
    Z + xi ≠ 0 := by
  intro h
  apply hZ
  have : xi = -Z := by linear_combination h
  rwa [← this]

private lemma prime_pred_even {p : ℕ} (hprime : p.Prime) (hp : 2 < p) : Even (p - 1) := by
  obtain ⟨d, hd⟩ := hprime.odd_of_ne_two (by omega)
  use d
  omega

private lemma nonpole_zero_ne {p : ℕ} {Z : K}
    (hZ : -Z ∉ teichmullerSet K p) : Z ≠ 0 := by
  have h := nonpole_ne hZ (show (0 : K) ∈ teichmullerSet K p by simp [teichmullerSet])
  simpa using h

private lemma nonpole_pred_power_sub_ne {p : ℕ} (hprime : p.Prime) (hp : 2 < p)
    {Z : K} (hZ : -Z ∉ teichmullerSet K p) : Z ^ (p - 1) - 1 ≠ 0 := by
  intro h
  have hpow : Z ^ (p - 1) = 1 := sub_eq_zero.mp h
  apply hZ
  have hnegpow : (-Z) ^ (p - 1) = 1 := by
    rw [(prime_pred_even hprime hp).neg_pow, hpow]
  have hmem : -Z ∈ teichmullerUnits K p := by
    rw [teichmullerUnits, mem_nthRootsFinset (by omega)]
    exact hnegpow
  simp [teichmullerSet, hmem]

private lemma frobenius_sub_eq_mul {p : ℕ} (hp : 0 < p) (Z : K) :
    Z ^ p - Z = Z * (Z ^ (p - 1) - 1) := by
  calc
    Z ^ p - Z = Z ^ (p - 1 + 1) - Z := by congr 2; omega
    _ = Z * (Z ^ (p - 1) - 1) := by rw [pow_succ]; ring

private lemma nonpole_frobenius_sub_ne {p : ℕ} (hprime : p.Prime) (hp : 2 < p)
    {Z : K} (hZ : -Z ∉ teichmullerSet K p) : Z ^ p - Z ≠ 0 := by
  rw [frobenius_sub_eq_mul (by omega)]
  exact mul_ne_zero (nonpole_zero_ne hZ) (nonpole_pred_power_sub_ne hprime hp hZ)

private lemma teichmullerUnits_reciprocal_sum {p : ℕ} {zeta : K}
    (hprime : p.Prime) (hp : 2 < p) (hzeta : IsPrimitiveRoot zeta (p - 1))
    {Z : K} (hZ : -Z ∉ teichmullerSet K p) :
    ∑ xi ∈ teichmullerUnits K p, 1 / (Z + xi) =
      (p - 1 : ℕ) * Z ^ (p - 2) / (Z ^ (p - 1) - 1) := by
  classical
  let n := p - 1
  let P : K[X] := X ^ n - C 1
  have hn : 0 < n := by omega
  have hZmu : -Z ∉ teichmullerUnits K p := by
    intro h
    exact hZ (by simp [teichmullerSet, h])
  have hP : P.eval (-Z) ≠ 0 := by
    intro heval
    have hpow : (-Z) ^ n = 1 := by
      exact sub_eq_zero.mp (by simpa [P, eval_sub, eval_pow] using heval)
    apply hZmu
    rw [teichmullerUnits, mem_nthRootsFinset hn]
    exact hpow
  have hsplit : P.Splits := by
    exact X_pow_sub_C_splits_of_isPrimitiveRoot hzeta (one_pow n)
  have hlog := hsplit.eval_derivative_div_eval_of_ne_zero hP
  have hroots :
      (P.roots.map fun xi => 1 / (-Z - xi)).sum =
        ∑ xi ∈ teichmullerUnits K p, 1 / (-Z - xi) := by
    rw [teichmullerUnits, nthRootsFinset_def,
      ← Multiset.toFinset_eq (hzeta.nthRoots_one_nodup), Finset.sum_mk]
    rfl
  rw [hroots] at hlog
  have hpodd : Odd p := hprime.odd_of_ne_two (by omega)
  obtain ⟨d, hd⟩ := hpodd
  have hneven : Even n := by
    use d
    omega
  have hnodd : Odd (n - 1) := by
    use d - 1
    omega
  have hn_eq : n = p - 1 := rfl
  have hn1_eq : n - 1 = p - 2 := by omega
  have hcalc :
      -(n : K) * Z ^ (n - 1) / (Z ^ n - 1) =
        ∑ xi ∈ teichmullerUnits K p, 1 / (-Z - xi) := by
    simpa [P, derivative_sub, derivative_X_pow, hnodd.neg_pow, hneven.neg_pow] using hlog
  calc
    ∑ xi ∈ teichmullerUnits K p, 1 / (Z + xi) =
        -(∑ xi ∈ teichmullerUnits K p, 1 / (-Z - xi)) := by
      apply Eq.symm
      rw [← Finset.sum_neg_distrib]
      apply sum_congr rfl
      intro xi hxi
      rw [show -Z - xi = -(Z + xi) by ring, one_div, inv_neg, neg_neg]
      exact (one_div (Z + xi)).symm
    _ = (n : K) * Z ^ (n - 1) / (Z ^ n - 1) := by rw [← hcalc]; ring
    _ = _ := by rw [hn_eq, hn1_eq]

private lemma teichmullerSet_reciprocal_sum {p : ℕ} {zeta : K}
    (hprime : p.Prime) (hp : 2 < p) (hzeta : IsPrimitiveRoot zeta (p - 1))
    {Z : K} (hZ : -Z ∉ teichmullerSet K p) :
    ∑ xi ∈ teichmullerSet K p, 1 / (Z + xi) =
      (p : K) / Z + (p - 1 : ℕ) / (Z ^ p - Z) := by
  rw [sum_teichmullerSet hp, teichmullerUnits_reciprocal_sum hprime hp hzeta hZ]
  have hZ0 := nonpole_zero_ne hZ
  have hpred := nonpole_pred_power_sub_ne hprime hp hZ
  rw [frobenius_sub_eq_mul (K := K) (by omega) Z]
  have hpcast : (p : K) = (1 : K) + (p - 1 : ℕ) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    congr
    omega
  rw [hpcast]
  have hpowpred : Z * Z ^ (p - 2) = Z ^ (p - 1) := by
    rw [show p - 1 = p - 2 + 1 by omega, pow_succ]
    ring
  field_simp [hZ0, hpred]
  simp only [add_zero]
  linear_combination (Z * (p - 1 : ℕ)) * hpowpred

/-- Exact finite interpolation over `{0} ∪ μ_(p-1)`. -/
theorem interpolation {p i : ℕ} {zeta : K}
    (hprime : p.Prime) (hp : 2 < p) (hzeta : IsPrimitiveRoot zeta (p - 1))
    (hi : i < p) (Delta Z : K) (hZ : -Z ∉ teichmullerSet K p) :
    ∑ xi ∈ teichmullerSet K p, (Delta + xi) ^ i / (Z + xi) =
      (p : K) * Delta ^ i / Z +
        (p - 1 : ℕ) * (Delta - Z) ^ i / (Z ^ p - Z) := by
  induction i with
  | zero =>
      simpa using teichmullerSet_reciprocal_sum hprime hp hzeta hZ
  | succ i ih =>
      have hi' : i < p := by omega
      have hnotTop : i ≠ p - 1 := by omega
      have hrec :
          ∑ xi ∈ teichmullerSet K p, (Delta + xi) ^ (i + 1) / (Z + xi) =
            (Delta - Z) *
                (∑ xi ∈ teichmullerSet K p, (Delta + xi) ^ i / (Z + xi)) +
              ∑ xi ∈ teichmullerSet K p, (Delta + xi) ^ i := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply sum_congr rfl
        intro xi hxi
        have hden : Z + xi ≠ 0 := nonpole_ne hZ hxi
        rw [pow_succ]
        field_simp
        ring
      rw [hrec, ih hi',
        teichmullerSet_shifted_power_sum hp hzeta hi' Delta, if_neg hnotTop]
      have hZ0 := nonpole_zero_ne hZ
      have hD := nonpole_frobenius_sub_ne hprime hp hZ
      field_simp
      ring

private def vanishingPolynomial (K : Type*) [Field K] (p : ℕ) : K[X] :=
  X ^ p - X

private def rootCofactor (K : Type*) [Field K] (p : ℕ) (xi : K) : K[X] :=
  haveI := Classical.decEq K
  ∏ eta ∈ (teichmullerSet K p).erase xi, (X - C eta)

private lemma vanishingPolynomial_eq_prod {p : ℕ} {zeta : K}
    (hp : 2 < p) (hzeta : IsPrimitiveRoot zeta (p - 1)) :
    vanishingPolynomial K p = ∏ xi ∈ teichmullerSet K p, (X - C xi) := by
  classical
  rw [teichmullerSet, prod_insert (zero_notMem_teichmullerUnits hp)]
  change vanishingPolynomial K p =
    (X - C 0) * ∏ xi ∈ nthRootsFinset (p - 1) (1 : K), (X - C xi)
  rw [← X_pow_sub_one_eq_prod (by omega) hzeta]
  simp only [vanishingPolynomial, C_0, sub_zero]
  have hpow : X * X ^ (p - 1) = (X : K[X]) ^ p := by
    calc
      X * X ^ (p - 1) = X ^ (p - 1 + 1) := by rw [pow_succ]; ring
      _ = X ^ p := by congr 1; omega
  rw [← hpow]
  ring

private lemma vanishingPolynomial_eq_factor_mul_cofactor {p : ℕ} {zeta xi : K}
    (hp : 2 < p) (hzeta : IsPrimitiveRoot zeta (p - 1))
    (hxi : xi ∈ teichmullerSet K p) :
    vanishingPolynomial K p = (X - C xi) * rootCofactor K p xi := by
  classical
  rw [vanishingPolynomial_eq_prod hp hzeta, rootCofactor]
  rw [← Finset.mul_prod_erase _ _ hxi]

private lemma derivative_vanishingPolynomial_eq_sum_cofactors {p : ℕ} {zeta : K}
    (hp : 2 < p) (hzeta : IsPrimitiveRoot zeta (p - 1)) :
    (vanishingPolynomial K p).derivative =
      ∑ xi ∈ teichmullerSet K p, rootCofactor K p xi := by
  classical
  rw [vanishingPolynomial_eq_prod hp hzeta, derivative_prod_finset]
  simp only [derivative_sub, derivative_X, derivative_C, sub_zero, mul_one]
  rfl

private lemma eval_vanishingPolynomial_ne_of_notMem {p : ℕ} (hp : 2 < p)
    {x : K} (hx : x ∉ teichmullerSet K p) : (vanishingPolynomial K p).eval x ≠ 0 := by
  intro heval
  have hxp : x ^ p - x = 0 := by simpa [vanishingPolynomial] using heval
  by_cases hx0 : x = 0
  · apply hx
    simp [teichmullerSet, hx0]
  · have hpow : x ^ (p - 1) = 1 := by
      have hmul : x * (x ^ (p - 1) - 1) = 0 := by
        rw [← frobenius_sub_eq_mul (K := K) (by omega)]
        exact hxp
      exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hx0)
    apply hx
    have hmem : x ∈ teichmullerUnits K p := by
      rw [teichmullerUnits, mem_nthRootsFinset (by omega)]
      exact hpow
    simp [teichmullerSet, hmem]

private lemma inverse_square_sum_eq_derivatives {p : ℕ} {zeta : K}
    (hp : 2 < p) (hzeta : IsPrimitiveRoot zeta (p - 1))
    {x : K} (hx : x ∉ teichmullerSet K p) :
    ∑ xi ∈ teichmullerSet K p, 1 / (x - xi) ^ 2 =
      ((vanishingPolynomial K p).derivative.eval x) ^ 2 /
          ((vanishingPolynomial K p).eval x) ^ 2 -
        (vanishingPolynomial K p).derivative.derivative.eval x /
          (vanishingPolynomial K p).eval x := by
  classical
  let D := vanishingPolynomial K p
  let q : K → K[X] := rootCofactor K p
  have hD0 : D.eval x ≠ 0 := eval_vanishingPolynomial_ne_of_notMem hp hx
  have hden (xi : K) (hxi : xi ∈ teichmullerSet K p) : x - xi ≠ 0 := by
    intro heq
    apply hx
    have : xi = x := (sub_eq_zero.mp heq).symm
    rwa [← this]
  have hqeval (xi : K) (hxi : xi ∈ teichmullerSet K p) :
      (q xi).eval x = D.eval x / (x - xi) := by
    have hfactor := vanishingPolynomial_eq_factor_mul_cofactor hp hzeta hxi
    have heval := congrArg (Polynomial.eval x) hfactor
    simp only [eval_mul, eval_sub, eval_X, eval_C] at heval
    apply (eq_div_iff (hden xi hxi)).2
    rw [mul_comm]
    exact heval.symm
  have hqderiv (xi : K) (hxi : xi ∈ teichmullerSet K p) :
      (q xi).derivative.eval x =
        (D.derivative.eval x - (q xi).eval x) / (x - xi) := by
    have hfactor := vanishingPolynomial_eq_factor_mul_cofactor hp hzeta hxi
    have hderiv := congrArg Polynomial.derivative hfactor
    have heval := congrArg (Polynomial.eval x) hderiv
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
      one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C] at heval
    change D.derivative.eval x = (q xi).eval x +
      (x - xi) * (q xi).derivative.eval x at heval
    apply (eq_div_iff (hden xi hxi)).2
    rw [mul_comm]
    apply (eq_sub_iff_add_eq).2
    simpa [add_comm] using heval.symm
  have hD1 : D.derivative.eval x =
      ∑ xi ∈ teichmullerSet K p, (q xi).eval x := by
    have hpoly := derivative_vanishingPolynomial_eq_sum_cofactors hp hzeta
    have heval := congrArg (Polynomial.eval x) hpoly
    rw [eval_finsetSum] at heval
    simpa [D, q] using heval
  have hD2 : D.derivative.derivative.eval x =
      ∑ xi ∈ teichmullerSet K p, (q xi).derivative.eval x := by
    have hpoly := congrArg Polynomial.derivative
      (derivative_vanishingPolynomial_eq_sum_cofactors hp hzeta)
    simp only [map_sum] at hpoly
    have heval := congrArg (Polynomial.eval x) hpoly
    rw [eval_finsetSum] at heval
    simpa [D, q] using heval
  have hA : ∑ xi ∈ teichmullerSet K p, 1 / (x - xi) =
      D.derivative.eval x / D.eval x := by
    apply (eq_div_iff hD0).2
    rw [hD1, Finset.sum_mul]
    apply sum_congr rfl
    intro xi hxi
    rw [hqeval xi hxi]
    field_simp [hden xi hxi]
  have hsecond : D.derivative.derivative.eval x =
      D.derivative.eval x *
          (∑ xi ∈ teichmullerSet K p, 1 / (x - xi)) -
        D.eval x *
          (∑ xi ∈ teichmullerSet K p, 1 / (x - xi) ^ 2) := by
    rw [hD2]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro xi hxi
    rw [hqderiv xi hxi, hqeval xi hxi]
    field_simp [hden xi hxi]
  let Q : K := ∑ xi ∈ teichmullerSet K p, 1 / (x - xi) ^ 2
  change D.derivative.derivative.eval x =
    D.derivative.eval x * (∑ xi ∈ teichmullerSet K p, 1 / (x - xi)) -
      D.eval x * Q at hsecond
  rw [hA] at hsecond
  have hsecond' : D.derivative.derivative.eval x * D.eval x =
      (D.derivative.eval x) ^ 2 - (D.eval x) ^ 2 * Q := by
    field_simp [hD0] at hsecond
    exact hsecond
  change Q = (D.derivative.eval x) ^ 2 / (D.eval x) ^ 2 -
    D.derivative.derivative.eval x / D.eval x
  field_simp [hD0]
  rw [mul_comm (D.eval x) (D.derivative.derivative.eval x), hsecond']
  ring

private lemma teichmullerSet_reciprocal_square_sum {p : ℕ} {zeta : K}
    (hprime : p.Prime) (hp : 2 < p) (hzeta : IsPrimitiveRoot zeta (p - 1))
    {Z : K} (hZ : -Z ∉ teichmullerSet K p) :
    ∑ xi ∈ teichmullerSet K p, 1 / (Z + xi) ^ 2 =
      (p : K) / Z ^ 2 +
        (p - 1 : ℕ) * ((p : K) * Z ^ (p - 1) - 1) / (Z ^ p - Z) ^ 2 := by
  have hbase := inverse_square_sum_eq_derivatives hp hzeta hZ
  have hpodd : Odd p := hprime.odd_of_ne_two (by omega)
  have hpredeven : Even (p - 1) := prime_pred_even hprime hp
  have hDval : (vanishingPolynomial K p).eval (-Z) = -(Z ^ p - Z) := by
    simp only [vanishingPolynomial, eval_sub, eval_pow, eval_X]
    rw [hpodd.neg_pow]
    ring
  obtain ⟨d, hd⟩ := hpodd
  have hpredodd : Odd (p - 2) := by
    use d - 1
    omega
  have hD1val : (vanishingPolynomial K p).derivative.eval (-Z) =
      (p : K) * Z ^ (p - 1) - 1 := by
    simp [vanishingPolynomial, derivative_sub, derivative_X_pow, hpredeven.neg_pow]
  have hD2val : (vanishingPolynomial K p).derivative.derivative.eval (-Z) =
      -((p : K) * (p - 1 : ℕ) * Z ^ (p - 2)) := by
    have hpoly : (vanishingPolynomial K p).derivative.derivative =
        C (p : K) * (C ((p - 1 : ℕ) : K) * X ^ (p - 2)) := by
      simp [vanishingPolynomial, derivative_sub, derivative_X_pow,
        show p - 1 - 1 = p - 2 by omega]
    rw [hpoly]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    rw [hpredodd.neg_pow]
    ring
  rw [hDval, hD1val, hD2val] at hbase
  simp only [neg_sq, neg_div_neg_eq] at hbase
  have hlhs :
      (∑ xi ∈ teichmullerSet K p, 1 / (-Z - xi) ^ 2) =
        ∑ xi ∈ teichmullerSet K p, 1 / (Z + xi) ^ 2 := by
    apply sum_congr rfl
    intro xi hxi
    rw [show -Z - xi = -(Z + xi) by ring, neg_sq]
  rw [hlhs] at hbase
  have hZ0 := nonpole_zero_ne hZ
  have hD := nonpole_frobenius_sub_ne hprime hp hZ
  have hpred := nonpole_pred_power_sub_ne hprime hp hZ
  have hfactor := frobenius_sub_eq_mul (K := K) hprime.pos Z
  have hpowpred : Z * Z ^ (p - 2) = Z ^ (p - 1) := by
    rw [show p - 1 = p - 2 + 1 by omega, pow_succ]
    ring
  have hratio :
      (p : K) * (p - 1 : ℕ) * Z ^ (p - 2) /
          (Z * (Z ^ (p - 1) - 1)) =
        (p : K) * (p - 1 : ℕ) * Z ^ (p - 1) /
          (Z ^ 2 * (Z ^ (p - 1) - 1)) := by
    field_simp [hZ0, hpred]
    calc
      (p : K) * (p - 1 : ℕ) * Z ^ (p - 2) * Z =
          (p : K) * (p - 1 : ℕ) * (Z * Z ^ (p - 2)) := by ring
      _ = _ := by rw [hpowpred]
  rw [hbase, hfactor, hratio]
  have hpcast : (p : K) = (1 : K) + (p - 1 : ℕ) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    congr
    omega
  field_simp [hZ0, hpred]
  rw [hpcast]
  ring

private lemma differentiated_step_algebra
    (P N I U A B C Z D E : K) (hZ : Z ≠ 0) (hD : D ≠ 0)
    (hAB : A * B = C) :
    A * (P * U / Z ^ 2 + N * (I * B / D + C * E / D ^ 2)) +
        (P * U / Z + N * C / D) =
      P * ((A + Z) * U) / Z ^ 2 +
        N * ((I + 1) * C / D + (A * C) * E / D ^ 2) := by
  field_simp [hZ, hD]
  ring_nf
  linear_combination (D * Z ^ 2 * N * I) * hAB

/-- The algebraically differentiated finite interpolation identity. -/
theorem interpolation_derivative {p i : ℕ} {zeta : K}
    (hprime : p.Prime) (hp : 2 < p) (hzeta : IsPrimitiveRoot zeta (p - 1))
    (hi : i < p) (Delta Z : K) (hZ : -Z ∉ teichmullerSet K p) :
    ∑ xi ∈ teichmullerSet K p, (Delta + xi) ^ i / (Z + xi) ^ 2 =
      (p : K) * Delta ^ i / Z ^ 2 +
        (p - 1 : ℕ) *
          ((i : K) * (Delta - Z) ^ (i - 1) / (Z ^ p - Z) +
            (Delta - Z) ^ i * ((p : K) * Z ^ (p - 1) - 1) /
              (Z ^ p - Z) ^ 2) := by
  induction i with
  | zero =>
      simp
      simpa [div_eq_mul_inv, mul_assoc] using
        teichmullerSet_reciprocal_square_sum hprime hp hzeta hZ
  | succ i ih =>
      have hi' : i < p := by omega
      have hrec :
          ∑ xi ∈ teichmullerSet K p, (Delta + xi) ^ (i + 1) / (Z + xi) ^ 2 =
            (Delta - Z) *
                (∑ xi ∈ teichmullerSet K p,
                  (Delta + xi) ^ i / (Z + xi) ^ 2) +
              ∑ xi ∈ teichmullerSet K p,
                (Delta + xi) ^ i / (Z + xi) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply sum_congr rfl
        intro xi hxi
        have hden : Z + xi ≠ 0 := nonpole_ne hZ hxi
        rw [pow_succ]
        field_simp [hden]
        ring
      rw [hrec, ih hi', interpolation hprime hp hzeta hi' Delta Z hZ]
      have hZ0 := nonpole_zero_ne hZ
      have hD := nonpole_frobenius_sub_ne hprime hp hZ
      by_cases hi0 : i = 0
      · subst i
        simp
        field_simp [hZ0, hD]
        ring
      · have hpow :
            (Delta - Z) * (Delta - Z) ^ (i - 1) = (Delta - Z) ^ i := by
          rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi0)]
        have hstep := differentiated_step_algebra
          (P := (p : K)) (N := (p - 1 : ℕ)) (I := (i : K))
          (U := Delta ^ i) (A := Delta - Z) (B := (Delta - Z) ^ (i - 1))
          (C := (Delta - Z) ^ i) (Z := Z) (D := Z ^ p - Z)
          (E := (p : K) * Z ^ (p - 1) - 1) hZ0 hD hpow
        simp only [pow_succ, Nat.cast_add, Nat.cast_one] at ⊢
        rw [show i + 1 - 1 = i by omega]
        convert hstep using 1 <;> ring

end
end LanglandsSecondMainLemma.Finite
