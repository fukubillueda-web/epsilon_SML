import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Total.TranslatedNorm
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Odd / Total / Filtered Coefficients

The monomials in Paper `O:A:lem:filtered` are indexed by their multiplicities
at the actual elementary symmetric coefficients, including the norm coefficient.
The estimates use integer lattice depths and retain the outer factor `X`.

The final congruence uses actual local-field norms, traces, and Teichmuller
representatives. Its integral Newton expansion is evaluated on the actual
Galois conjugates, and the two exceptional terms are retained exactly.
-/

namespace LanglandsSecondMainLemma.Odd.Total

open LanglandsFirstMainLemma
open scoped BigOperators

noncomputable section

/-- The number of factors in a coefficient monomial. The index `i : Fin p`
stands for the elementary symmetric coefficient of degree `i+1`. -/
def filteredLength {p : ℕ} (lambda : Fin p → ℕ) : ℕ := ∑ i, lambda i

/-- The total symmetric weight of a coefficient monomial. -/
def filteredWeight {p : ℕ} (lambda : Fin p → ℕ) : ℕ :=
  ∑ i : Fin p, ((i : ℕ) + 1) * lambda i

/-- The number of factors other than the top norm coefficient. -/
def filteredLowerLength {p : ℕ} (lambda : Fin p → ℕ) : ℕ :=
  ∑ i : Fin p, if (i : ℕ) + 1 < p then lambda i else 0

/-- The actual coefficient monomial, including all multiplicities. -/
def filteredMonomial {p : ℕ} {E : Type*} [CommMonoid E]
    (e : Fin p → E) (lambda : Fin p → ℕ) : E := ∏ i, e i ^ lambda i

private theorem filtered_pow_mem
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {x : E} {a : ℤ} (hx : x ∈ lattice E a) (n : ℕ) :
    x ^ n ∈ lattice E ((n : ℤ) * a) := by
  rw [mem_lattice] at hx ⊢
  rw [ord_pow]
  simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using nsmul_le_nsmul_right hx n

private theorem filtered_prod_mem
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {I : Type*} (s : Finset I) (x : I → E) (a : I → ℤ)
    (hx : ∀ i ∈ s, x i ∈ lattice E (a i)) :
    (∏ i ∈ s, x i) ∈ lattice E (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi, Finset.sum_insert hi] using
      mul_mem_lattice E (hx i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hx j (Finset.mem_insert_of_mem hj)))

/-- The characteristic-polynomial deficiency is at most `(p-1)nu`.
Consequently a deficiency of at least `p` forces at least two lower
coefficients. This uses the whole multiplicity vector. -/
theorem filtered_deficiency_le {p : ℕ} (lambda : Fin p → ℕ) :
    (p : ℤ) * filteredLength lambda - filteredWeight lambda ≤
      ((p : ℤ) - 1) * filteredLowerLength lambda := by
  simp only [filteredLength, filteredWeight, filteredLowerLength,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hi : (i : ℕ) < p := i.isLt
  have hl : (0 : ℤ) ≤ lambda i := Int.natCast_nonneg _
  split_ifs with h
  · have hi0 : (0 : ℤ) ≤ (i : ℕ) := Int.natCast_nonneg _
    nlinarith
  · have hip : (i : ℕ) + 1 = p := by omega
    have hipZ : ((i : ℕ) : ℤ) + 1 = p := by exact_mod_cast hip
    simp only [Nat.cast_zero, mul_zero]
    nlinarith

/-- Every factor has degree at most `p`. -/
theorem filtered_weight_le {p : ℕ} (lambda : Fin p → ℕ) :
    filteredWeight lambda ≤ p * filteredLength lambda := by
  simp only [filteredWeight, filteredLength, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (by omega : (i : ℕ) + 1 ≤ p)

/-- Paper `O:A:eq:monomial`. This is the precise weighted estimate, before
discarding any monomial. The norm coefficient has depth `-t`; the other
coefficients have depth `(p-1)(t+delta)-i*t`.

The integer `v` is the paper's index in `n=(p-1)v+k`, and can be negative.
It is unrelated to the lower-field order used to construct the outer `X`. -/
theorem filteredMonomial_mem
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {p : ℕ} (t delta R v : ℤ) (k : ℕ)
    (e : Fin p → E) (lambda : Fin p → ℕ) (X : E)
    (he : ∀ i : Fin p, e i ∈ lattice E
      ((((p : ℤ) - 1) - ((i : ℕ) + 1)) * t +
        if (i : ℕ) + 1 < p then ((p : ℤ) - 1) * delta else 0))
    (hX : X ∈ lattice E (R + ((k : ℤ) - 1) * t))
    (hweight : (filteredWeight lambda : ℤ) = ((p : ℤ) - 1) * v + k) :
    X * filteredMonomial e lambda ∈ lattice E
      (R - t + ((p : ℤ) - 1) *
        (((filteredLength lambda : ℤ) - v) * t + filteredLowerLength lambda * delta)) := by
  have hm := filtered_prod_mem E Finset.univ (fun i => e i ^ lambda i)
    (fun i => (lambda i : ℤ) *
      ((((p : ℤ) - 1) - ((i : ℕ) + 1)) * t +
        if (i : ℕ) + 1 < p then ((p : ℤ) - 1) * delta else 0))
    (fun i _ => filtered_pow_mem E (he i) (lambda i))
  have hsum : (∑ i : Fin p, (lambda i : ℤ) *
      ((((p : ℤ) - 1) - ((i : ℕ) + 1)) * t +
        if (i : ℕ) + 1 < p then ((p : ℤ) - 1) * delta else 0)) =
      (((p : ℤ) - 1) * filteredLength lambda - filteredWeight lambda) * t +
        ((p : ℤ) - 1) * filteredLowerLength lambda * delta := by
    simp only [filteredLength, filteredWeight, filteredLowerLength,
      Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> push_cast <;> ring
  rw [hsum] at hm
  have hdepth : R + ((k : ℤ) - 1) * t +
      ((((p : ℤ) - 1) * filteredLength lambda - filteredWeight lambda) * t +
        ((p : ℤ) - 1) * filteredLowerLength lambda * delta) =
      R - t + ((p : ℤ) - 1) *
        (((filteredLength lambda : ℤ) - v) * t + filteredLowerLength lambda * delta) := by
    rw [hweight]
    ring
  simpa only [hdepth, filteredMonomial] using mul_mem_lattice E hX hm

/-- The nonboundary monomials have at least two lower factors. This is
the first case in the proof of `O:A:lem:filtered`. -/
theorem filtered_lowerLength_ge_two
    {p k : ℕ} (hp : 2 ≤ p) (hk : k ≤ p)
    (lambda : Fin p → ℕ) {v : ℤ} (hv : 0 ≤ v)
    (hweight : (filteredWeight lambda : ℤ) = ((p : ℤ) - 1) * v + k)
    (hlength : v + 2 ≤ (filteredLength lambda : ℤ)) :
    2 ≤ filteredLowerLength lambda := by
  have hdef := filtered_deficiency_le lambda
  have hpZ : (2 : ℤ) ≤ p := by exact_mod_cast hp
  have hkZ : (k : ℤ) ≤ p := by exact_mod_cast hk
  have hmul := mul_nonneg (sub_nonneg.mpr hlength) (show (0 : ℤ) ≤ p by omega)
  rw [hweight] at hdef
  by_contra h
  have hnu : (filteredLowerLength lambda : ℤ) ≤ 1 := by exact_mod_cast (by omega : filteredLowerLength lambda ≤ 1)
  have hmul' := mul_nonneg (sub_nonneg.mpr hnu) (show (0 : ℤ) ≤ (p : ℤ) - 1 by omega)
  nlinarith

/-- Integer arithmetic behind the terminal depth estimate. In particular
this keeps the case `p=3, delta=0` at the exact stated precision. -/
theorem filtered_deep_depth
    {p : ℕ} (hp : 3 ≤ p) {t delta R a nu : ℤ}
    (ht : 0 ≤ t) (hd : 0 ≤ delta) (ha : 2 ≤ a) (hnu : 2 ≤ nu) :
    (p : ℤ) * (t + delta) + R ≤
      R - t + ((p : ℤ) - 1) * (a * t + nu * delta) := by
  have hpZ : (3 : ℤ) ≤ p := by exact_mod_cast hp
  have h₁ := mul_nonneg (sub_nonneg.mpr ha) ht
  have h₂ := mul_nonneg (sub_nonneg.mpr hnu) hd
  have h₃ := mul_nonneg (show (0 : ℤ) ≤ (p : ℤ) - 1 by omega)
    (show 0 ≤ a * t + nu * delta - 2 * (t + delta) by nlinarith)
  have h₄ := mul_nonneg (show (0 : ℤ) ≤ (p : ℤ) - 3 by omega) ht
  have h₅ := mul_nonneg (show (0 : ℤ) ≤ (p : ℤ) - 2 by omega) hd
  nlinarith

/-- The coefficient-free part of the first case of `O:A:lem:filtered`.
Any integral scalar coefficient preserves this depth. -/
theorem filteredMonomial_deep
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {p k : ℕ} (hp : 3 ≤ p) (hk : k ≤ p)
    (t delta R v : ℤ) (ht : 0 ≤ t) (hd : 0 ≤ delta) (hv : 0 ≤ v)
    (e : Fin p → E) (lambda : Fin p → ℕ) (X : E)
    (hm : X * filteredMonomial e lambda ∈ lattice E
      (R - t + ((p : ℤ) - 1) *
        (((filteredLength lambda : ℤ) - v) * t + filteredLowerLength lambda * delta)))
    (hweight : (filteredWeight lambda : ℤ) = ((p : ℤ) - 1) * v + k)
    (hlength : v + 2 ≤ (filteredLength lambda : ℤ)) :
    X * filteredMonomial e lambda ∈ lattice E ((p : ℤ) * (t + delta) + R) := by
  have hnu := filtered_lowerLength_ge_two (by omega : 2 ≤ p) hk lambda hv hweight hlength
  exact lattice_antitone E (filtered_deep_depth hp ht hd (by omega) (by exact_mod_cast hnu)) hm

/-- One factor of `p` removes the boundary monomials containing at least
one lower coefficient. The estimate includes equal characteristic, where
the prime factor is zero. -/
theorem filteredMonomial_prime_mul_mem
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {p : ℕ} (hp : 3 ≤ p) (t delta R : ℤ) (ht : 0 ≤ t) (hd : 0 ≤ delta)
    (z : E) {nu : ℕ} (hnu : 1 ≤ nu)
    (hz : z ∈ lattice E (R - t + ((p : ℤ) - 1) * (t + nu * delta)))
    (hpval : (p : E) ∈ lattice E (((p : ℤ) - 1) * (t + delta))) :
    (p : E) * z ∈ lattice E ((p : ℤ) * (t + delta) + R) := by
  have h := mul_mem_lattice E hpval hz
  apply lattice_antitone E _ h
  have hdeep := filtered_deep_depth hp (R := R) (nu := (nu : ℤ) + 1)
    ht hd (by omega : (2 : ℤ) ≤ 2) (by omega)
  convert hdeep using 1
  ring

/-- The exceptional pure-norm boundary term has coefficient `p^2`.
Two prime factors suffice even though its lower length is zero. -/
theorem filteredMonomial_prime_sq_mul_mem
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {p : ℕ} (hp : 3 ≤ p) (t delta R : ℤ) (ht : 0 ≤ t) (hd : 0 ≤ delta)
    (z : E) (hz : z ∈ lattice E (R - t + ((p : ℤ) - 1) * t))
    (hpval : (p : E) ∈ lattice E (((p : ℤ) - 1) * (t + delta))) :
    (p : E) ^ 2 * z ∈ lattice E ((p : ℤ) * (t + delta) + R) := by
  have h := mul_mem_lattice E (filtered_pow_mem E hpval 2) hz
  apply lattice_antitone E _ h
  have hdeep := filtered_deep_depth hp (R := R) ht hd (by omega : (2 : ℤ) ≤ 3)
    (by omega : (2 : ℤ) ≤ 2)
  convert hdeep using 1
  norm_num
  ring

/-! The Newton coefficient is defined over the integers by a polynomial
coefficient, so its integrality never requires dividing by a possibly zero
field element. The following Euler identity replaces the factorial quotient
in the paper. -/

/-- The unsigned integral Newton coefficient of a multiplicity vector.
For length `r>0` and weight `n`, it is `n(r-1)! / ∏ lambda_i!`.
The polynomial definition also makes sense in length zero. -/
def filteredNewtonCoefficient {p : ℕ} (lambda : Fin p → ℕ) : ℤ :=
  MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm lambda)
    ((∑ i : Fin p, MvPolynomial.C (((i : ℕ) + 1 : ℕ) : ℤ) * MvPolynomial.X i) *
      (∑ i : Fin p, MvPolynomial.X i) ^ (filteredLength lambda - 1))

private theorem filtered_coeff_X_mul_pderiv
    {I : Type*} (i : I) (f : MvPolynomial I ℤ) (m : I →₀ ℕ) :
    MvPolynomial.coeff m (MvPolynomial.X i * MvPolynomial.pderiv i f) =
      (m i : ℤ) * MvPolynomial.coeff m f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add, mul_add, MvPolynomial.coeff_add, hf, hg]
  | monomial n a =>
    rw [MvPolynomial.X_mul_pderiv_monomial, MvPolynomial.coeff_smul]
    by_cases h : n = m
    · subst n; simp
    · simp [MvPolynomial.coeff_monomial, h]

/-- The denominator-cleared Newton coefficient formula. Both sides are
integers, including at `r=p`, where division in the residue field is illegal. -/
theorem filteredNewtonCoefficient_length_mul
    {p : ℕ} (lambda : Fin p → ℕ) :
    (filteredLength lambda : ℤ) * filteredNewtonCoefficient lambda =
      (filteredWeight lambda : ℤ) * Nat.multinomial Finset.univ lambda := by
  classical
  let m : Fin p →₀ ℕ := Finsupp.equivFunOnFinite.symm lambda
  let A : MvPolynomial (Fin p) ℤ := ∑ i, MvPolynomial.X i
  let B : MvPolynomial (Fin p) ℤ :=
    ∑ i : Fin p, MvPolynomial.C (((i : ℕ) + 1 : ℕ) : ℤ) * MvPolynomial.X i
  let r := filteredLength lambda
  have hderiv (i : Fin p) : MvPolynomial.pderiv i A = 1 := by
    simp [A, map_sum, MvPolynomial.pderiv_X, Pi.single_apply]
  have heuler : (r : MvPolynomial (Fin p) ℤ) * (B * A ^ (r - 1)) =
      ∑ i : Fin p, MvPolynomial.C (((i : ℕ) + 1 : ℕ) : ℤ) *
        (MvPolynomial.X i * MvPolynomial.pderiv i (A ^ r)) := by
    simp only [MvPolynomial.pderiv_pow, hderiv, mul_one, B, Finset.sum_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hc : MvPolynomial.coeff m (A ^ r) =
      (Nat.multinomial Finset.univ lambda : ℤ) := by
    rw [MvPolynomial.coeff_sum_X_pow_of_fintype]
    have hsum : m.sum (fun _ n => n) = r := by
      exact Finsupp.equivFunOnFinite_symm_sum lambda
    rw [if_pos hsum, Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
    rfl
  have h := congrArg (MvPolynomial.coeff m) heuler
  simp only [← MvPolynomial.C_eq_coe_nat, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_sum, filtered_coeff_X_mul_pderiv, hc] at h
  change (r : ℤ) * filteredNewtonCoefficient lambda = _ at h
  rw [h]
  simp only [filteredWeight, Nat.cast_sum, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Finset.sum_mul, m, Finsupp.coe_equivFunOnFinite_symm]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Multinomial coefficients of length `p` are divisible by `p` whenever
every multiplicity is less than `p`. This is exactly the factorial-unit
argument used at the boundary; it does not divide inside a field. -/
theorem filtered_multinomial_prime_dvd
    {p : ℕ} (hp : p.Prime) (lambda : Fin p → ℕ)
    (hlength : filteredLength lambda = p) (hlt : ∀ i, lambda i < p) :
    p ∣ Nat.multinomial Finset.univ lambda := by
  have hden : ¬ p ∣ ∏ i : Fin p, (lambda i).factorial :=
    (Nat.prime_iff.mp hp).not_dvd_finsetProd
      (fun i _ => fun h => (not_le_of_gt (hlt i)) (hp.dvd_factorial.mp h))
  have hspec := Nat.multinomial_spec Finset.univ lambda
  change (∏ i, (lambda i).factorial) * Nat.multinomial Finset.univ lambda =
    (filteredLength lambda).factorial at hspec
  rw [hlength] at hspec
  exact (hp.dvd_mul.mp (hspec.symm ▸ hp.dvd_factorial.mpr le_rfl)).resolve_left hden

/-- A multiplicity attaining the whole length forces a constant selection. -/
theorem filtered_single_of_length
    {p : ℕ} (lambda : Fin p → ℕ) (i : Fin p)
    (hi : lambda i = filteredLength lambda) :
    lambda = Pi.single i (filteredLength lambda) := by
  classical
  have hsum : ∑ j ∈ Finset.univ.erase i, lambda j = 0 := by
    have h := Finset.add_sum_erase Finset.univ lambda (Finset.mem_univ i)
    rw [hi] at h
    change filteredLength lambda + _ = filteredLength lambda at h
    omega
  have hzero (j : Fin p) (hji : j ≠ i) : lambda j = 0 := by
    have h := Finset.single_le_sum (f := lambda) (fun _ _ => Nat.zero_le _)
      (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
    rw [hsum] at h
    omega
  funext j
  by_cases hji : j = i
  · subst j; simpa using hi
  · simp [hji, hzero j hji]

@[simp]
theorem filteredWeight_single {p : ℕ} (i : Fin p) (r : ℕ) :
    filteredWeight (Pi.single i r) = ((i : ℕ) + 1) * r := by
  classical
  simp [filteredWeight, Pi.single_apply]

@[simp]
theorem filteredLength_single {p : ℕ} (i : Fin p) (r : ℕ) :
    filteredLength (Pi.single i r) = r := by
  classical
  simp [filteredLength]

/-- A constant selection has unsigned Newton coefficient equal to its
symmetric degree. This proves the exceptional coefficient exactly. -/
theorem filteredNewtonCoefficient_single {p : ℕ} (i : Fin p) {r : ℕ} (hr : 0 < r) :
    filteredNewtonCoefficient (Pi.single i r) = (i : ℕ) + 1 := by
  have h := filteredNewtonCoefficient_length_mul (Pi.single i r)
  rw [filteredLength_single, filteredWeight_single, Nat.multinomial_single] at h
  have hrZ : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
  apply mul_left_cancel₀ hrZ
  simpa [Nat.cast_mul, mul_comm] using h

/-- The coefficient difference in the boundary case `r=v+1`, where the
Newton sign is negative. The separate `b^k` term is handled at `r=v`. -/
def filteredBoundaryCoefficient {p : ℕ} (k v : ℕ) (lambda : Fin p → ℕ) : ℤ :=
  ((p : ℤ) - 1) * k.choose (filteredLength lambda) *
      Nat.multinomial Finset.univ lambda + k.choose v * filteredNewtonCoefficient lambda

/-- The exact boundary cancellation with the length cleared. The only
remaining issue is whether the length itself is divisible by `p`. -/
theorem filteredBoundaryCoefficient_length_mul
    {p k v : ℕ} (lambda : Fin p → ℕ)
    (hv : v ≤ k) (hlength : filteredLength lambda = v + 1)
    (hweight : filteredWeight lambda = (p - 1) * v + k) (hp : 1 ≤ p) :
    (filteredLength lambda : ℤ) * filteredBoundaryCoefficient k v lambda =
      (p : ℤ) * k * k.choose v * Nat.multinomial Finset.univ lambda := by
  have hc := filteredNewtonCoefficient_length_mul lambda
  have hb : (filteredLength lambda : ℤ) * k.choose (filteredLength lambda) =
      ((k : ℤ) - v) * k.choose v := by
    rw [hlength]
    have h := congrArg (fun n : ℕ => (n : ℤ)) (Nat.choose_succ_right_eq k v)
    push_cast [Nat.cast_sub hv] at h
    push_cast
    nlinarith only [h]
  calc
    _ = ((p : ℤ) - 1) *
          ((filteredLength lambda : ℤ) * k.choose (filteredLength lambda)) *
            Nat.multinomial Finset.univ lambda +
          k.choose v * ((filteredLength lambda : ℤ) * filteredNewtonCoefficient lambda) := by
      dsimp only [filteredBoundaryCoefficient]; ring
    _ = _ := by
      rw [hc, hb, hweight]
      push_cast [Nat.cast_sub hp]
      ring

/-- The ordinary boundary case: a nonzero length less than `p` is a unit
modulo `p`, so the exact length-cleared identity gives divisibility. -/
theorem filteredBoundaryCoefficient_prime_dvd_of_length_lt
    {p k v : ℕ} (hp : p.Prime) (lambda : Fin p → ℕ)
    (hv : v ≤ k) (hlength : filteredLength lambda = v + 1)
    (hweight : filteredWeight lambda = (p - 1) * v + k)
    (hlt : filteredLength lambda < p) :
    (p : ℤ) ∣ filteredBoundaryCoefficient k v lambda := by
  have h := filteredBoundaryCoefficient_length_mul lambda hv hlength hweight hp.one_le
  have hd : (p : ℤ) ∣ (filteredLength lambda : ℤ) * filteredBoundaryCoefficient k v lambda := by
    rw [h]
    exact ⟨k * k.choose v * Nat.multinomial Finset.univ lambda, by ring⟩
  apply ((Nat.prime_iff_prime_int.mp hp).dvd_mul.mp hd).resolve_left
  rw [Int.natCast_dvd_natCast]
  exact Nat.not_dvd_of_pos_of_lt (by omega) hlt

/-- At length `p`, exponent `k=p`, and `v=p-1`, the weight is not divisible
by `p`. Hence no multiplicity can be `p`, and both coefficients are
divisible by `p`. -/
theorem filteredBoundaryCoefficient_prime_dvd_at_prime
    {p : ℕ} (hp : p.Prime) (lambda : Fin p → ℕ)
    (hlength : filteredLength lambda = p)
    (hweight : filteredWeight lambda = (p - 1) * (p - 1) + p) :
    (p : ℤ) ∣ filteredBoundaryCoefficient p (p - 1) lambda := by
  have hlt (i : Fin p) : lambda i < p := by
    have hi : lambda i ≤ p := by
      rw [← hlength]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    by_contra h
    have heq : lambda i = filteredLength lambda := by omega
    have hw := filtered_single_of_length lambda i heq
    have hw' := congrArg filteredWeight hw
    rw [filteredWeight_single, hlength, hweight] at hw'
    have hwZ := congrArg (fun n : ℕ => (n : ℤ)) hw'
    push_cast [Nat.cast_sub hp.one_le] at hwZ
    have hpZ : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    by_cases hitop : (i : ℕ) + 1 = p
    · have hiZ : ((i : ℕ) : ℤ) + 1 = p := by exact_mod_cast hitop
      nlinarith
    · have hiZ : ((i : ℕ) : ℤ) + 1 ≤ (p : ℤ) - 1 := by have := i.isLt; omega
      have hmul := mul_le_mul_of_nonneg_right hiZ (show (0 : ℤ) ≤ p by omega)
      nlinarith
  have hm : (p : ℤ) ∣ (Nat.multinomial Finset.univ lambda : ℤ) :=
    Int.natCast_dvd_natCast.mpr (filtered_multinomial_prime_dvd hp lambda hlength hlt)
  have hchoose : p.choose (p - 1) = p := by
    have h := Nat.choose_succ_self_right (p - 1)
    simpa only [Nat.sub_add_cancel hp.one_le] using h
  dsimp only [filteredBoundaryCoefficient]
  rw [hchoose]
  exact dvd_add (dvd_mul_of_dvd_right hm _) (dvd_mul_right _ _)

/-- The last Newton boundary, `v=k`, has `n=pk` and length `k+1`.
Unless `k=p-1`, that length is coprime to `p`, so the coefficient is
divisible by `p`. This includes `k=p`. -/
theorem filteredNewtonCoefficient_prime_dvd_last
    {p k : ℕ} (hp : p.Prime) (hk : k ≤ p) (hne : k ≠ p - 1)
    (lambda : Fin p → ℕ) (hlength : filteredLength lambda = k + 1)
    (hweight : filteredWeight lambda = p * k) :
    (p : ℤ) ∣ filteredNewtonCoefficient lambda := by
  have h := filteredNewtonCoefficient_length_mul lambda
  rw [hlength, hweight, Nat.cast_mul] at h
  have hd : (p : ℤ) ∣ ((k + 1 : ℕ) : ℤ) * filteredNewtonCoefficient lambda := by
    rw [h]
    exact ⟨k * Nat.multinomial Finset.univ lambda, by ring⟩
  apply ((Nat.prime_iff_prime_int.mp hp).dvd_mul.mp hd).resolve_left
  rw [Int.natCast_dvd_natCast]
  intro hd
  have hp2 := hp.two_le
  have hle := Nat.le_of_dvd (by omega : 0 < k + 1) hd
  have : k + 1 = p ∨ k + 1 = p + 1 := by omega
  rcases this with heq | heq
  · omega
  · rw [heq] at hd
    have : p ∣ 1 := Nat.dvd_add_self_left.mp hd
    exact hp.not_dvd_one this

/-- The unique nonzero residue in the last boundary is the pure
`e_(p-1)^p` selection. Its coefficient is exactly `p-1`. -/
theorem filteredNewtonCoefficient_exceptional
    {p : ℕ} (hp : p.Prime) (lambda : Fin p → ℕ)
    (hlength : filteredLength lambda = p)
    (hweight : filteredWeight lambda = p * (p - 1)) :
    let i : Fin p := ⟨p - 2, by have := hp.two_le; omega⟩
    (p : ℤ) ∣ filteredNewtonCoefficient lambda -
      (if lambda = Pi.single i p then (p : ℤ) - 1 else 0) := by
  classical
  dsimp only
  let i : Fin p := ⟨p - 2, by have := hp.two_le; omega⟩
  change (p : ℤ) ∣ filteredNewtonCoefficient lambda -
    (if lambda = Pi.single i p then (p : ℤ) - 1 else 0)
  by_cases hsingle : lambda = Pi.single i p
  · rw [if_pos hsingle, hsingle, filteredNewtonCoefficient_single i hp.pos]
    have hi : ((i : ℕ) : ℤ) + 1 = (p : ℤ) - 1 := by
      dsimp [i]
      have := hp.two_le
      omega
    rw [hi, sub_self]
    exact dvd_zero _
  · rw [if_neg hsingle, sub_zero]
    have hlt (j : Fin p) : lambda j < p := by
      have hj : lambda j ≤ p := by
        rw [← hlength]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      by_contra h
      have heq : lambda j = filteredLength lambda := by omega
      have hsingle' := filtered_single_of_length lambda j heq
      rw [hlength] at hsingle'
      have hw := congrArg filteredWeight hsingle'
      rw [hweight, filteredWeight_single, mul_comm p] at hw
      have hjdeg : (j : ℕ) + 1 = p - 1 := (mul_right_cancel₀ hp.ne_zero hw).symm
      have hji : j = i := Fin.ext (by dsimp [i]; omega)
      exact hsingle (hji ▸ hsingle')
    have hmul := filteredNewtonCoefficient_length_mul lambda
    rw [hlength, hweight, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one] at hmul
    have heq : filteredNewtonCoefficient lambda =
        ((p : ℤ) - 1) * Nat.multinomial Finset.univ lambda := by
      apply mul_left_cancel₀ (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0)
      simpa only [mul_assoc] using hmul
    rw [heq]
    exact dvd_mul_of_dvd_right
      (Int.natCast_dvd_natCast.mpr (filtered_multinomial_prime_dvd hp lambda hlength hlt)) _

/-- The maximal possible weight is attained only by a power of the norm
coefficient. This identifies the actual multiplicity vector, rather than
just its numerical weight. -/
theorem filtered_maximalWeight
    {p : ℕ} (hp : 0 < p) (lambda : Fin p → ℕ)
    (hw : filteredWeight lambda = p * filteredLength lambda) :
    lambda = Pi.single ⟨p - 1, by omega⟩ (filteredLength lambda) := by
  classical
  let top : Fin p := ⟨p - 1, by omega⟩
  have hs : (∑ i : Fin p, ((p : ℤ) - ((i : ℕ) + 1)) * lambda i) = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [sub_eq_zero]
    have hwZ := congrArg (fun n : ℕ => (n : ℤ)) hw
    simpa only [filteredWeight, filteredLength, Nat.cast_sum, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one] using hwZ.symm
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun (i : Fin p) _ => mul_nonneg (by have := i.isLt; omega : (0 : ℤ) ≤ (p : ℤ) - ((i : ℕ) + 1))
      (Int.natCast_nonneg (lambda i)))).mp hs
  have hzero (i : Fin p) (hi : i ≠ top) : lambda i = 0 := by
    have hitop : (i : ℕ) + 1 ≠ p := by
      intro h
      exact hi (Fin.ext (by dsimp only [top]; omega))
    have hfactor : (p : ℤ) - ((i : ℕ) + 1) ≠ 0 := by omega
    exact_mod_cast (mul_eq_zero.mp (hterm i (Finset.mem_univ i))).resolve_left hfactor
  have ht : lambda top = filteredLength lambda := by
    dsimp only [filteredLength]
    symm
    exact Finset.sum_eq_single top (fun i _ hi => hzero i hi) (by simp)
  exact filtered_single_of_length lambda top ht

/-- At `r=v` the only monomial is `b^k`, so the two exact coefficients
are both `p`. -/
theorem filtered_diagonal_selection
    {p k v : ℕ} (hp : 0 < p) (lambda : Fin p → ℕ)
    (hv : v ≤ k) (hlength : filteredLength lambda = v)
    (hweight : filteredWeight lambda = (p - 1) * v + k) :
    v = k ∧ lambda = Pi.single ⟨p - 1, by omega⟩ k := by
  have hbound := filtered_weight_le lambda
  have hpZ : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  have hboundZ := congrArg (fun n : ℕ => (n : ℤ)) hweight
  rw [Nat.cast_add, Nat.cast_mul, hpZ] at hboundZ
  have hb : (filteredWeight lambda : ℤ) ≤ (p : ℤ) * filteredLength lambda := by
    exact_mod_cast hbound
  rw [hlength] at hb
  have hvk : v = k := by
    have hvZ : (v : ℤ) ≤ k := by exact_mod_cast hv
    have : (v : ℤ) = k := by nlinarith
    exact_mod_cast this
  refine ⟨hvk, ?_⟩
  have hw : filteredWeight lambda = p * filteredLength lambda := by
    rw [hweight, hlength, ← hvk]
    nlinarith [Nat.sub_add_cancel hp]
  simpa only [hlength, hvk] using filtered_maximalWeight hp lambda hw

private theorem filtered_intCast_mul_mem
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (c : ℤ) {z : E} {a : ℤ}
    (hz : z ∈ lattice E a) : (c : E) * z ∈ lattice E a := by
  have hc : (c : E) ∈ lattice E 0 :=
    (mem_lattice_zero_iff E).mpr (c : ringOfIntegers E).property
  simpa only [zero_add] using mul_mem_lattice E hc hz

/-- Integral coefficients divisible by `p` may be applied to the
boundary lattice estimate in either field characteristic. -/
theorem filteredMonomial_coefficient_mem
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {p : ℕ} (hp : 3 ≤ p) (t delta R : ℤ) (ht : 0 ≤ t) (hd : 0 ≤ delta)
    (z : E) {nu : ℕ} (hnu : 1 ≤ nu)
    (hz : z ∈ lattice E (R - t + ((p : ℤ) - 1) * (t + nu * delta)))
    (hpval : (p : E) ∈ lattice E (((p : ℤ) - 1) * (t + delta)))
    (c : ℤ) (hc : (p : ℤ) ∣ c) :
    (c : E) * z ∈ lattice E ((p : ℤ) * (t + delta) + R) := by
  obtain ⟨d, rfl⟩ := hc
  have h := filtered_intCast_mul_mem E d
    (filteredMonomial_prime_mul_mem E hp t delta R ht hd z hnu hz hpval)
  simpa only [Int.cast_mul, Int.cast_natCast, mul_assoc, mul_left_comm] using h

/-- The monomial bound for the genuine characteristic-polynomial
coefficients. The norm coefficient's order is obtained from FML's exact
norm valuation in the totally ramified upper extension. -/
theorem filtered_actualMonomial_mem
    (E K : Type*) [Field E] [Field K]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra E K] [ValuativeExtension E K] [Module.Free E K] [Module.Finite E K]
    {p : ℕ} (hdegree : Module.finrank E K = p) (hram : ramificationIndex E K = p)
    (Delta : K) (t delta R v : ℤ) (k : ℕ)
    (hDelta : ord K Delta = ((-t : ℤ) : WithTop ℤ))
    (he : ∀ j : ℕ, 1 ≤ j → j < p →
      elementarySymmetric E K j Delta ∈ lattice E (((p : ℤ) - 1) * (t + delta) - j * t))
    (lambda : Fin p → ℕ) (X : E)
    (hX : X ∈ lattice E (R + ((k : ℤ) - 1) * t))
    (hweight : (filteredWeight lambda : ℤ) = ((p : ℤ) - 1) * v + k) :
    X * filteredMonomial (fun i : Fin p => elementarySymmetric E K ((i : ℕ) + 1) Delta) lambda ∈
      lattice E (R - t + ((p : ℤ) - 1) *
        (((filteredLength lambda : ℤ) - v) * t + filteredLowerLength lambda * delta)) := by
  apply filteredMonomial_mem E t delta R v k _ lambda X _ hX hweight
  intro i
  by_cases hi : (i : ℕ) + 1 < p
  · rw [if_pos hi]
    have hdepth : ((p : ℤ) - 1 - ((i : ℕ) + 1)) * t + ((p : ℤ) - 1) * delta =
        ((p : ℤ) - 1) * (t + delta) - (((i : ℕ) + 1 : ℕ) : ℤ) * t := by
      push_cast
      ring
    rw [hdepth]
    exact he ((i : ℕ) + 1) (by omega) hi
  · have hip : (i : ℕ) + 1 = p := by have := i.isLt; omega
    rw [if_neg hi, add_zero, hip]
    have hipZ : ((i : ℕ) : ℤ) + 1 = p := by exact_mod_cast hip
    rw [hipZ]
    have hdepth : ((p : ℤ) - 1 - p) * t = -t := by ring
    rw [hdepth, mem_lattice, elementarySymmetric_degree_ord E K p hdegree hram, hDelta]


/-! An integral Newton polynomial, built by the Newton recurrence. Its
coefficient theorem below is proved for actual multiplicity vectors, and
its evaluation is the power sum of an arbitrary finite family. -/
namespace FilteredNewton

open MvPolynomial

/-- The unsigned Newton polynomial in elementary coefficients of degrees
`1,...,p`. Substitution of `(-1)^(i+1)e_i` recovers the usual power sum. -/
def ghost (p n : ℕ) : MvPolynomial (Fin p) ℤ :=
  ∑ i : Fin p, if hi : (i : ℕ) + 1 ≤ n then
    if (i : ℕ) + 1 = n then C (n : ℤ) * X i
    else X i * ghost p (n - ((i : ℕ) + 1))
  else 0
termination_by n

@[simp] theorem ghost_zero (p : ℕ) : ghost p 0 = 0 := by
  rw [ghost]
  simp

theorem ghost_homogeneous (p n : ℕ) :
    IsWeightedHomogeneous (fun i : Fin p => (i : ℕ) + 1) (ghost p n) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [ghost]
    apply IsWeightedHomogeneous.sum
    intro i _
    split_ifs with hi heq
    · rw [← heq]
      exact (isWeightedHomogeneous_X (R := ℤ) (fun i : Fin p => (i : ℕ) + 1) i).C_mul _
    · have hn : n - ((i : ℕ) + 1) < n := by omega
      have h := (isWeightedHomogeneous_X (R := ℤ) (fun i : Fin p => (i : ℕ) + 1) i).mul
        (ih _ hn)
      simpa only [Nat.add_sub_of_le hi] using h
    · exact isWeightedHomogeneous_zero (R := ℤ) _ _

private lemma weight_eq {p : ℕ} (m : Fin p →₀ ℕ) :
    Finsupp.weight (fun i : Fin p => (i : ℕ) + 1) m = filteredWeight m := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · simp only [filteredWeight, nsmul_eq_mul, mul_comm, Nat.cast_id]
  · intro i; simp

private lemma length_eq {p : ℕ} (m : Fin p →₀ ℕ) :
    Finsupp.weight (fun _ : Fin p => (1 : ℕ)) m = filteredLength m := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · simp only [filteredLength, nsmul_eq_mul, mul_one, Nat.cast_id]
  · intro i; simp

private lemma length_le_weight {p : ℕ} (m : Fin p →₀ ℕ) :
    filteredLength m ≤ filteredWeight m := by
  apply Finset.sum_le_sum
  intro i _
  exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

private lemma sub_length {p : ℕ} (m : Fin p →₀ ℕ) (i : Fin p) (hi : m i ≠ 0) :
    filteredLength (⇑(m - Finsupp.single i 1 : Fin p →₀ ℕ)) + 1 = filteredLength m := by
  simpa only [length_eq] using Finsupp.weight_sub_single_add (w := fun _ : Fin p => (1 : ℕ)) hi

private lemma sub_weight {p : ℕ} (m : Fin p →₀ ℕ) (i : Fin p) (hi : m i ≠ 0) :
    filteredWeight (⇑(m - Finsupp.single i 1 : Fin p →₀ ℕ)) + ((i : ℕ) + 1) = filteredWeight m := by
  simpa only [weight_eq] using Finsupp.weight_sub_single_add (w := fun i : Fin p => (i : ℕ) + 1) hi

private def A (p : ℕ) : MvPolynomial (Fin p) ℤ := ∑ i, X i
private def B (p : ℕ) : MvPolynomial (Fin p) ℤ := ∑ i : Fin p, C (((i : ℕ) + 1 : ℕ) : ℤ) * X i

theorem ghost_coeff_weight_ne {p n : ℕ} (m : Fin p →₀ ℕ) (h : filteredWeight m ≠ n) :
    coeff m (ghost p n) = 0 := by
  apply (ghost_homogeneous p n).coeff_eq_zero
  simpa only [weight_eq] using h

theorem ghost_coeff {p n : ℕ} (hn : 0 < n) (m : Fin p →₀ ℕ)
    (hw : filteredWeight m = n) : coeff m (ghost p n) = filteredNewtonCoefficient m := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    have hrpos : 0 < filteredLength m := by
      by_contra h
      have hlen : ∀ i : Fin p, m i = 0 := by
        have hz : ∑ i : Fin p, m i = 0 := by change filteredLength m = 0; omega
        exact fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hz i (Finset.mem_univ i)
      have hm0 : m = 0 := Finsupp.ext (fun i => hlen i)
      simp [hm0, filteredWeight] at hw
      omega
    by_cases hr1 : filteredLength m = 1
    · obtain ⟨i, hi⟩ : ∃ i : Fin p, 0 < m i := by
        by_contra h
        simp only [not_exists, not_lt, Nat.le_zero] at h
        simp [filteredLength, h] at hr1
      have hle : m i ≤ filteredLength m :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have hsingle := filtered_single_of_length (⇑m) i (by omega)
      rw [hr1] at hsingle
      have hm : m = Finsupp.single i 1 := Finsupp.ext (fun j => by simpa only [Pi.single_apply, Finsupp.single_apply, eq_comm] using congrFun hsingle j)
      have hwi : n = (i : ℕ) + 1 := by
        have h := congrArg filteredWeight hsingle
        rw [filteredWeight_single, mul_one, hw] at h
        exact h
      rw [show filteredNewtonCoefficient m = (i : ℕ) + 1 by
        have h := congrArg filteredNewtonCoefficient hsingle
        simpa only [filteredNewtonCoefficient_single i Nat.zero_lt_one] using h]
      rw [ghost, coeff_sum]
      apply (Finset.sum_eq_single i ?_ (by simp)).trans ?_
      · intro j _ hji
        by_cases hjn : (j : ℕ) + 1 ≤ n
        · rw [dif_pos hjn]
          by_cases hjn' : (j : ℕ) + 1 = n
          · have hji' : j = i := Fin.ext (by omega)
            exact (hji hji').elim
          · rw [if_neg hjn', coeff_X_mul', hm, if_neg]
            simp [hji]
        · rw [dif_neg hjn, coeff_zero]
      · rw [dif_pos (by omega), if_pos (by omega), coeff_C_mul, hm]
        simp [hwi, X, coeff_monomial]
    · have hr2 : 2 ≤ filteredLength m := by omega
      have hstep : filteredNewtonCoefficient m =
          ∑ i : Fin p, if hi : m i ≠ 0 then
            filteredNewtonCoefficient (⇑(m - Finsupp.single i 1 : Fin p →₀ ℕ)) else 0 := by
        have hpowers : B p * A p ^ (filteredLength m - 1) =
            A p * (B p * A p ^ (filteredLength m - 2)) := by
          rw [show filteredLength m - 1 = (filteredLength m - 2) + 1 by omega, pow_succ]
          ring
        change coeff (Finsupp.equivFunOnFinite.symm (m : Fin p → ℕ))
          (B p * A p ^ (filteredLength m - 1)) = _
        rw [Finsupp.equivFunOnFinite_symm_coe, hpowers, A, Finset.sum_mul, coeff_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [coeff_X_mul']
        by_cases hi : m i ≠ 0
        · rw [if_pos (Finsupp.mem_support_iff.mpr hi), dif_pos hi]
          have hr := sub_length m i hi
          dsimp only [filteredNewtonCoefficient]
          rw [Finsupp.equivFunOnFinite_symm_coe]
          have hexp : filteredLength (⇑(m - Finsupp.single i 1 : Fin p →₀ ℕ)) - 1 = filteredLength m - 2 := by omega
          rw [hexp]
          rfl
        · rw [if_neg (by simpa only [Finsupp.mem_support_iff] using hi), dif_neg hi]
      rw [hstep, ghost, coeff_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : m i ≠ 0
      · rw [dif_pos hi]
        have hwsub := sub_weight m i hi
        have hrsub := sub_length m i hi
        have hwpos := length_le_weight (m - Finsupp.single i 1)
        have hdi : (i : ℕ) + 1 < n := by omega
        rw [dif_pos hdi.le, if_neg hdi.ne, coeff_X_mul', if_pos (Finsupp.mem_support_iff.mpr hi)]
        apply ih (n - ((i : ℕ) + 1)) (by omega) (by omega) _ (by omega)
      · rw [dif_neg hi]
        by_cases hdi : (i : ℕ) + 1 ≤ n
        · rw [dif_pos hdi]
          by_cases hdieq : (i : ℕ) + 1 = n
          · rw [if_pos hdieq, coeff_C_mul]
            have hmne : m ≠ Finsupp.single i 1 := by
              intro hm
              have h := congrArg (fun m : Fin p →₀ ℕ => m i) hm
              simp only [Finsupp.single_eq_same] at h
              exact hi (by omega)
            simp [X, coeff_monomial, Ne.symm hmne]
          · rw [if_neg hdieq, coeff_X_mul', if_neg (by simpa only [Finsupp.mem_support_iff] using hi)]
        · rw [dif_neg hdi, coeff_zero]

open LanglandsFirstMainLemma.FiniteFamily

theorem finite_newton_range {I R : Type*} [Fintype I] [CommRing R]
    (z : I → R) {n : ℕ} (hn : 0 < n) :
    finitePowerSum z n =
      ∑ i ∈ Finset.range n,
        if i + 1 = n then (-1 : R) ^ (n + 1) * n * finiteElementarySymmetric z n
        else (-1 : R) ^ (i + 2) * finiteElementarySymmetric z (i + 1) *
          finitePowerSum z (n - (i + 1)) := by
  have h := congrArg (MvPolynomial.aeval z)
    (MvPolynomial.psum_eq_mul_esymm_sub_sum I R n hn)
  have hev (j : ℕ) : MvPolynomial.aeval z (esymm I R j) = finiteElementarySymmetric z j :=
    MvPolynomial.aeval_esymm_eq_multiset_esymm I R j z
  simp only [map_sub, map_mul, map_pow, map_neg, map_one, map_natCast, map_sum, hev] at h
  have hpow (j : ℕ) : MvPolynomial.aeval z (psum I R j) = finitePowerSum z j := by
    simp [psum, finitePowerSum]
  simp only [hpow, Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Set.mem_Ioo] at h
  rw [Finset.sum_range_succ] at h
  simp only [lt_self_iff_false, and_false, if_false, add_zero] at h
  have hn' : n = (n - 1) + 1 := by omega
  conv_rhs => rw [hn', Finset.sum_range_succ]
  simp only [← hn']
  have hsum : (∑ x ∈ Finset.range n, if 0 < x ∧ x < n then
      (-1 : R) ^ x * finiteElementarySymmetric z x * finitePowerSum z (n - x) else 0) =
      ∑ i ∈ Finset.range (n - 1),
        (-1 : R) ^ (i + 1) * finiteElementarySymmetric z (i + 1) * finitePowerSum z (n - (i + 1)) := by
    conv_lhs => rw [hn', Finset.sum_range_succ']
    simp only [← hn', lt_self_iff_false, false_and, if_false, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (show 0 < i + 1 ∧ i + 1 < n from by have := Finset.mem_range.mp hi; omega)]
  rw [hsum] at h
  rw [h, sub_eq_add_neg, add_comm]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [if_neg (by have := Finset.mem_range.mp hi; omega), show i + 2 = (i + 1) + 1 by omega, pow_succ]
  ring

theorem finite_esymm_zero {I R : Type*} [Fintype I] [CommRing R]
    (z : I → R) {n : ℕ} (hn : Fintype.card I < n) : finiteElementarySymmetric z n = 0 := by
  simp only [finiteElementarySymmetric, Multiset.esymm]
  rw [Multiset.powersetCard_eq_empty n (by simpa using hn)]
  simp

theorem finite_newton {I R : Type*} [Fintype I] [CommRing R]
    (z : I → R) {n : ℕ} (hn : 0 < n) :
    finitePowerSum z n =
      ∑ i : Fin (Fintype.card I), if (i : ℕ) + 1 ≤ n then
        if (i : ℕ) + 1 = n then (-1 : R) ^ (n + 1) * n * finiteElementarySymmetric z n
        else (-1 : R) ^ ((i : ℕ) + 2) * finiteElementarySymmetric z ((i : ℕ) + 1) *
          finitePowerSum z (n - ((i : ℕ) + 1))
      else 0 := by
  classical
  rw [finite_newton_range z hn]
  let f (i : ℕ) : R := if i + 1 ≤ n then
        if i + 1 = n then (-1 : R) ^ (n + 1) * n * finiteElementarySymmetric z n
        else (-1 : R) ^ (i + 2) * finiteElementarySymmetric z (i + 1) * finitePowerSum z (n - (i + 1))
      else 0
  change _ = ∑ i : Fin (Fintype.card I), f (i : ℕ)
  rw [Fin.sum_univ_eq_sum_range f]
  have hlhs : (∑ i ∈ Finset.range n, if i + 1 = n then
      (-1 : R) ^ (n + 1) * n * finiteElementarySymmetric z n else
      (-1 : R) ^ (i + 2) * finiteElementarySymmetric z (i + 1) * finitePowerSum z (n - (i + 1))) =
      ∑ i ∈ Finset.range n, f i := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [f]
    rw [if_pos (show i + 1 ≤ n from by have := Finset.mem_range.mp hi; omega)]
  rw [hlhs]
  have hzero (i : ℕ) (hi : Fintype.card I ≤ i) : f i = 0 := by
    dsimp only [f]
    split_ifs with h h'
    · rw [finite_esymm_zero z (by omega), mul_zero]
    · rw [finite_esymm_zero z (by omega), mul_zero, zero_mul]
    · rfl
  rcases le_total n (Fintype.card I) with h | h
  · apply Finset.sum_subset (Finset.range_mono h)
    intro i _ hi
    have hni : ¬i + 1 ≤ n := by
      have hni : n ≤ i := by simpa only [Finset.mem_range, not_lt] using hi
      omega
    exact if_neg hni
  · symm
    apply Finset.sum_subset (Finset.range_mono h)
    intro i _ hi
    exact hzero i (by simpa only [Finset.mem_range, not_lt] using hi)

theorem ghost_eval {I R : Type*} [Fintype I] [CommRing R]
    (z : I → R) {n : ℕ} (hn : 0 < n) :
    eval₂ (Int.castRingHom R)
      (fun i : Fin (Fintype.card I) => (-1 : R) ^ ((i : ℕ) + 2) *
        finiteElementarySymmetric z ((i : ℕ) + 1)) (ghost (Fintype.card I) n) = finitePowerSum z n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [ghost, eval₂_sum, finite_newton z hn]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi h'
    · simp only [eval₂_mul, eval₂_X, eval₂_natCast, map_natCast]
      have hi' : (i : ℕ) + 2 = n + 1 := by omega
      rw [hi', h']
      ring
    · rw [eval₂_mul, eval₂_X, ih _ (by omega) (by omega)]
    · exact eval₂_zero _ _

end FilteredNewton


/-- The characteristic-polynomial coefficients arranged as the actual
translated norm polynomial, with both endpoint coefficients included. -/
def filteredNormPolynomial
    (E K : Type*) [Field E] [Field K] [Algebra E K]
    [Module.Free E K] [Module.Finite E K] (Delta : K) : Polynomial E :=
  ∑ i ∈ Finset.range (Module.finrank E K + 1),
    Polynomial.C (elementarySymmetric E K i Delta) * Polynomial.X ^ (Module.finrank E K - i)

/-- Exact evaluation at every translate, including the zero translate. -/
theorem filteredNormPolynomial_eval
    (E K : Type*) [Field E] [Field K]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra E K] [Module.Free E K] [Module.Finite E K] [IsGalois E K]
    (Delta : K) (xi : E) :
    (filteredNormPolynomial E K Delta).eval xi = norm E K (Delta + algebraMap E K xi) := by
  classical
  rw [filteredNormPolynomial, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  by_cases hxi : xi = 0
  · subst xi
    simp only [map_zero, add_zero]
    rw [Finset.sum_eq_single (Module.finrank E K)]
    · simp
    · intro i hi hne
      have hip : i < Module.finrank E K := by have := Finset.mem_range.mp hi; omega
      simp [zero_pow (by omega : Module.finrank E K - i ≠ 0)]
    · simp
  · have h := low_norm_algebraMap_sub_eq_sum_elementarySymmetric E K xi hxi (-Delta)
    rw [show algebraMap E K xi - -Delta = Delta + algebraMap E K xi by ring] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    have he : elementarySymmetric E K i (-Delta) =
        (-1 : E) ^ i * elementarySymmetric E K i Delta := by
      simpa only [map_neg, map_one, neg_one_mul] using
        low_elementarySymmetric_algebraMap_mul E K i (-1) Delta
    rw [he]
    have hsign : (-1 : E) ^ i * (-1) ^ i = 1 := by rw [← mul_pow]; simp
    calc
      _ = ((-1 : E) ^ i * (-1) ^ i) *
          (elementarySymmetric E K i Delta * xi ^ (Module.finrank E K - i)) := by rw [hsign, one_mul]
      _ = _ := by ring

/-- The exact binomial trace expansion defining `Q_k`, before applying
Newton coefficients or discarding any terms. -/
theorem filtered_trace_binomial
    (E K : Type*) [Field E] [Field K] [Algebra E K]
    [Module.Free E K] [Module.Finite E K]
    {p : ℕ} (hp : 1 ≤ p) (Delta : K) (k : ℕ) :
    trace E K ((Delta ^ p - Delta) ^ k) =
      ∑ v ∈ Finset.range (k + 1),
        (-1 : E) ^ (k - v) * k.choose v * trace E K (Delta ^ (k + (p - 1) * v)) := by
  have heq : (Delta ^ p - Delta) ^ k =
      ∑ v ∈ Finset.range (k + 1),
        ((-1 : E) ^ (k - v) * k.choose v) • Delta ^ (k + (p - 1) * v) := by
    rw [sub_eq_add_neg, add_pow]
    apply Finset.sum_congr rfl
    intro v hv
    have hvk : v ≤ k := by have := Finset.mem_range.mp hv; omega
    rw [neg_pow]
    simp only [Algebra.smul_def, map_mul, map_pow, map_neg, map_one, map_natCast]
    have hexp : p * v + (k - v) = k + (p - 1) * v := by
      have h := Nat.sub_add_cancel hp
      nlinarith [Nat.sub_add_cancel hvk]
    rw [← pow_mul]
    calc
      _ = (-1 : K) ^ (k - v) * k.choose v * (Delta ^ (p * v) * Delta ^ (k - v)) := by ring
      _ = _ := by rw [← pow_add, hexp]
  rw [heq, map_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [map_smul, smul_eq_mul]

/-- Exact prime Teichmuller power sums, in either characteristic. -/
theorem filtered_teichmuller_moment
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (p : ℕ) [Fact p.Prime] (hchar : residueCharacteristic E = p) (n : ℕ) :
    (∑ j : (ZMod p)ˣ, (primeTeichmuller E p hchar (j : ZMod p) : E) ^ n) =
      if p - 1 ∣ n then ((p - 1 : ℕ) : E) else 0 := by
  classical
  let c : ZMod p → E := fun j => primeTeichmuller E p hchar j
  have hinj : Function.Injective c := by
    intro i j hij
    have hr := congrArg (residueMap E) (Subtype.ext hij)
    simp only [residueMap_primeTeichmuller] at hr
    exact (ZMod.castHom _ (ResidueField E)).injective hr
  let phi : (ZMod p)ˣ →* E :=
    { toFun := fun j => c (j : ZMod p) ^ n
      map_one' := by simp [c]
      map_mul' := by intro i j; simp [c, map_mul, mul_pow] }
  have heq : phi = 1 ↔ p - 1 ∣ n := by
    have hunit : (∀ j : (ZMod p)ˣ, j ^ n = 1) ↔ p - 1 ∣ n := by
      simpa only [ZMod.card] using FiniteField.forall_pow_eq_one_iff (ZMod p) n
    rw [← hunit]
    constructor
    · intro h j
      have hval := congrArg (fun f : (ZMod p)ˣ →* E => f j) h
      change c (j : ZMod p) ^ n = 1 at hval
      apply Units.ext
      apply hinj
      simpa only [Units.val_pow_eq_pow_val, Units.val_one, c, map_pow, Subring.coe_pow, map_one,
        Subring.coe_one] using hval
    · intro h
      ext j
      change c (j : ZMod p) ^ n = 1
      have hj := congrArg (fun u : (ZMod p)ˣ => c (u : ZMod p)) (h j)
      simpa only [Units.val_pow_eq_pow_val, c, map_pow, Subring.coe_pow, Units.val_one,
        map_one, Subring.coe_one] using hj
  change (∑ j : (ZMod p)ˣ, phi j) = _
  rw [sum_hom_units phi]
  simp only [heq, Fintype.card_units, ZMod.card, Nat.cast_ite, Nat.cast_zero]


namespace FilteredPolynomial

open MvPolynomial

theorem coeff_affine_pow {I R : Type*} [Fintype I] [CommRing R]
    (a : R) (b : I → R) (k : ℕ) (m : I →₀ ℕ) :
    coeff m ((C a + ∑ i, b i • X i : MvPolynomial I R) ^ k) =
      if m.sum (fun _ n => n) ≤ k then
        (k.choose (m.sum (fun _ n => n)) : R) * a ^ (k - m.sum (fun _ n => n)) *
          m.multinomial * m.prod (fun i n => b i ^ n)
      else 0 := by
  classical
  have hC (f : MvPolynomial I R) (c : R) : coeff m (f * C c) = coeff m f * c := by
    rw [mul_comm f, coeff_C_mul, mul_comm]
  rw [add_comm, add_pow, coeff_sum]
  simp only [← C_pow, ← C_eq_coe_nat, mul_assoc, ← C_mul, hC,
    coeff_linearCombination_X_pow_of_fintype]
  by_cases hr : m.sum (fun _ n => n) ≤ k
  · rw [if_pos hr, Finset.sum_eq_single (m.sum (fun _ n => n))]
    · simp only [ite_true]
      ring
    · intro j _ hj
      rw [if_neg (Ne.symm hj), zero_mul]
    · simp only [Finset.mem_range, Nat.lt_succ_iff, hr, not_true_eq_false, IsEmpty.forall_iff]
  · rw [if_neg hr]
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg (by have := Finset.mem_range.mp hj; omega), zero_mul]

/-- The characteristic-polynomial expansion of a translated norm. -/
def affine {p : ℕ} {R : Type*} [CommRing R] (c : R) : MvPolynomial (Fin p) R :=
  C (c ^ p) + ∑ i : Fin p, C (c ^ (p - ((i : ℕ) + 1))) * X i

lemma deficiency_identity {p : ℕ} (m : Fin p →₀ ℕ) :
    (∑ i : Fin p, (p - ((i : ℕ) + 1)) * m i) + filteredWeight m =
      p * filteredLength m := by
  simp only [filteredWeight, filteredLength, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← add_mul, Nat.sub_add_cancel (by omega : (i : ℕ) + 1 ≤ p)]

lemma length_sum {p : ℕ} (m : Fin p →₀ ℕ) :
    m.sum (fun _ n => n) = filteredLength m := by
  rw [Finsupp.sum_fintype]
  · rfl
  · simp

theorem coeff_affine {p : ℕ} {R : Type*} [CommRing R]
    (c : R) (k : ℕ) (m : Fin p →₀ ℕ) :
    coeff m (affine (p := p) c ^ k) =
      if filteredLength m ≤ k then
        (k.choose (filteredLength m) : R) * m.multinomial * c ^ (p * k - filteredWeight m)
      else 0 := by
  classical
  have h := coeff_affine_pow (c ^ p) (fun i : Fin p => c ^ (p - ((i : ℕ) + 1))) k m
  simp only [smul_eq_C_mul, length_sum] at h
  change coeff m (affine (p := p) c ^ k) = _ at h
  rw [h]
  split_ifs with hr
  · have hprod : m.prod (fun i r => (c ^ (p - ((i : ℕ) + 1))) ^ r) =
        c ^ (∑ i : Fin p, (p - ((i : ℕ) + 1)) * m i) := by
      rw [Finsupp.prod_fintype]
      · simp only [← pow_mul, ← Finset.prod_pow_eq_pow_sum]
      · simp
    rw [hprod, ← pow_mul]
    have hd := deficiency_identity m
    have hexp : p * (k - filteredLength m) +
        (∑ i : Fin p, (p - ((i : ℕ) + 1)) * m i) = p * k - filteredWeight m := by
      have h := Nat.sub_add_cancel hr
      have hw : filteredWeight m ≤ p * k :=
        (filtered_weight_le m).trans (Nat.mul_le_mul_left p hr)
      nlinarith [Nat.sub_add_cancel hw]
    calc
      _ = (k.choose (filteredLength m) : R) * m.multinomial *
          (c ^ (p * (k - filteredLength m)) * c ^ (∑ i : Fin p, (p - ((i : ℕ) + 1)) * m i)) := by ring
      _ = _ := by rw [← pow_add, hexp]
  · rfl

/-- The paper's translated norm sum, with the norm term kept separately. -/
def translated {p : ℕ} {R J : Type*} [CommRing R] [Fintype J]
    (hp : 0 < p) (c : J → R) (k : ℕ) : MvPolynomial (Fin p) R :=
  X ⟨p - 1, by omega⟩ ^ k + ∑ j, affine (p := p) (c j) ^ k

/-- The exact Teichmuller coefficient selection in `P_k`. -/
theorem coeff_translated {p : ℕ} {R J : Type*} [CommRing R] [Fintype J]
    (hp : 0 < p) (c : J → R)
    (hmoment : ∀ n : ℕ, (∑ j, c j ^ n) = if p - 1 ∣ n then ((p - 1 : ℕ) : R) else 0)
    (k : ℕ) (m : Fin p →₀ ℕ) :
    coeff m (translated hp c k) =
      (if m = Finsupp.single ⟨p - 1, by omega⟩ k then 1 else 0) +
      if filteredLength m ≤ k then
        (k.choose (filteredLength m) : R) * m.multinomial *
          (if p - 1 ∣ p * k - filteredWeight m then ((p - 1 : ℕ) : R) else 0)
      else 0 := by
  classical
  rw [translated, coeff_add, X_pow_eq_monomial, coeff_monomial, coeff_sum]
  simp only [eq_comm (a := Finsupp.single _ k), coeff_affine]
  by_cases hr : filteredLength m ≤ k
  · simp only [if_pos hr]
    rw [← Finset.mul_sum, hmoment]
  · simp only [if_neg hr, Finset.sum_const_zero, add_zero]

theorem coeff_scaled {I R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (b : I → S) (f : MvPolynomial I R) (m : I →₀ ℕ) :
    coeff m (eval₂ (C.comp phi) (fun i => C (b i) * X i) f) =
      phi (coeff m f) * m.prod (fun i n => b i ^ n) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp [eval₂_add, hf, hg, add_mul]
  | monomial n a =>
    rw [eval₂_monomial]
    simp only [RingHom.comp_apply, Finsupp.prod, mul_pow, ← C_pow,
      Finset.prod_mul_distrib, ← map_prod, prod_X_pow_eq_monomial,
      C_mul_monomial, mul_one, coeff_monomial]
    split_ifs with h
    · subst n; rfl
    · simp [map_zero]

/-- The signed Newton polynomial in the elementary symmetric coefficients. -/
def signed {p : ℕ} {R : Type*} [CommRing R] (n : ℕ) : MvPolynomial (Fin p) R :=
  eval₂ (C.comp (Int.castRingHom R)) (fun i : Fin p => C ((-1 : R) ^ ((i : ℕ) + 2)) * X i)
    (FilteredNewton.ghost p n)

theorem coeff_signed {p n : ℕ} {R : Type*} [CommRing R]
    (hn : 0 < n) (m : Fin p →₀ ℕ) :
    coeff m (signed (R := R) n) =
      if filteredWeight m = n then (-1 : R) ^ (n + filteredLength m) *
        (filteredNewtonCoefficient m : R) else 0 := by
  classical
  rw [signed, coeff_scaled]
  by_cases hw : filteredWeight m = n
  · rw [if_pos hw, FilteredNewton.ghost_coeff hn m hw]
    have hs : m.prod (fun i r => ((-1 : R) ^ ((i : ℕ) + 2)) ^ r) =
        (-1 : R) ^ (n + filteredLength m) := by
      rw [Finsupp.prod_fintype]
      · simp only [← pow_mul]
        rw [Finset.prod_pow_eq_pow_sum]
        congr 1
        rw [← hw]
        simp only [filteredWeight, filteredLength, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      · simp
    rw [hs]
    exact mul_comm _ _
  · rw [if_neg hw, FilteredNewton.ghost_coeff_weight_ne m hw, map_zero, zero_mul]

/-- The binomial expansion of the trace of `(Delta^p-Delta)^k`. -/
def tracePolynomial {p : ℕ} {R : Type*} [CommRing R] (k : ℕ) : MvPolynomial (Fin p) R :=
  ∑ v ∈ Finset.range (k + 1), C ((-1 : R) ^ (k - v) * k.choose v) *
    signed (p := p) (k + (p - 1) * v)

lemma newton_sign {R : Type*} [CommRing R] {p k v r : ℕ}
    (hodd : Odd p) (hv : v ≤ k) :
    (-1 : R) ^ (k - v) * (-1) ^ (k + (p - 1) * v + r) = (-1) ^ (r + v) := by
  obtain ⟨q, hq⟩ := hodd
  have hpEven : Even (p - 1) := ⟨q, by omega⟩
  rw [pow_add _ _ r, pow_add _ k, pow_mul, hpEven.neg_one_pow, one_pow, mul_one,
    ← mul_assoc]
  have hkv : (-1 : R) ^ (k - v) * (-1) ^ k = (-1) ^ v := by
    have heq : k = (k - v) + v := (Nat.sub_add_cancel hv).symm
    nth_rw 2 [heq]
    rw [pow_add, ← mul_assoc, ← mul_pow]
    simp
  rw [hkv, ← pow_add, add_comm]

/-- The signed integral Newton coefficient of `Q_k`. -/
theorem coeff_tracePolynomial {p k v : ℕ} {R : Type*} [CommRing R]
    (hp : 1 < p) (hodd : Odd p) (hk : 1 ≤ k) (hv : v ≤ k)
    (m : Fin p →₀ ℕ) (hw : filteredWeight m = k + (p - 1) * v) :
    coeff m (tracePolynomial (R := R) (p := p) k) =
      (-1 : R) ^ (filteredLength m + v) * k.choose v * (filteredNewtonCoefficient m : R) := by
  classical
  rw [tracePolynomial, coeff_sum, Finset.sum_eq_single v]
  · rw [coeff_C_mul, coeff_signed (by omega), if_pos hw]
    calc
      _ = ((-1 : R) ^ (k - v) * (-1) ^ (k + (p - 1) * v + filteredLength m)) *
          k.choose v * (filteredNewtonCoefficient m : R) := by ring
      _ = _ := by rw [newton_sign hodd hv]
  · intro j _ hjv
    have hne : filteredWeight m ≠ k + (p - 1) * j := by
      intro h
      have h' := Nat.add_left_cancel (hw.symm.trans h)
      exact hjv ((mul_left_cancel₀ (by omega : p - 1 ≠ 0) h').symm)
    rw [coeff_C_mul, coeff_signed (by omega), if_neg hne, mul_zero]
  · simp [Finset.mem_range, hv]

theorem coeff_tracePolynomial_zero {p k : ℕ} {R : Type*} [CommRing R]
    (hk : 1 ≤ k) (m : Fin p →₀ ℕ)
    (hw : ∀ v, v ≤ k → filteredWeight m ≠ k + (p - 1) * v) :
    coeff m (tracePolynomial (R := R) (p := p) k) = 0 := by
  rw [tracePolynomial, coeff_sum]
  apply Finset.sum_eq_zero
  intro v hv
  rw [coeff_C_mul, coeff_signed (by omega), if_neg (hw v (by have := Finset.mem_range.mp hv; omega)), mul_zero]

theorem eval_signed {p n : ℕ} {R : Type*} [CommRing R] (e : Fin p → R) :
    eval e (signed n) = eval₂ (Int.castRingHom R)
      (fun i : Fin p => (-1 : R) ^ ((i : ℕ) + 2) * e i) (FilteredNewton.ghost p n) := by
  rw [signed, eval₂_comp_left]
  have hc : (eval e).comp (C.comp (Int.castRingHom R)) = Int.castRingHom R := by
    ext a
    simp
  rw [hc]
  congr 1
  funext i
  simp only [Function.comp_apply, eval_mul, eval_C, eval_X]

/-- Newton's formula evaluated on the actual Galois conjugates. -/
theorem trace_eq_newton
    (E K : Type*) [Field E] [Field K] [Infinite E]
    [Algebra E K] [Module.Free E K] [Module.Finite E K] [IsGalois E K]
    {p : ℕ} (hdegree : Module.finrank E K = p) (Delta : K) {n : ℕ} (hn : 0 < n) :
    trace E K (Delta ^ n) = eval₂ (Int.castRingHom E)
      (fun i : Fin p => (-1 : E) ^ ((i : ℕ) + 2) * elementarySymmetric E K ((i : ℕ) + 1) Delta)
      (FilteredNewton.ghost p n) := by
  have hcard : Fintype.card Gal(K/E) = p := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hdegree]
  have h := FilteredNewton.ghost_eval (fun sigma : Gal(K/E) => sigma Delta) hn
  rw [hcard] at h
  apply (algebraMap E K).injective
  rw [trace_eq_sum_automorphisms]
  simp only [map_pow]
  rw [hom_eval₂]
  have hc : (algebraMap E K).comp (Int.castRingHom E) = Int.castRingHom K := by
    ext a
    simp
  rw [hc]
  simp only [map_mul, map_pow, map_neg, map_one,
    algebraMap_elementarySymmetric_eq_esymm_galois]
  exact h.symm

theorem eval_tracePolynomial
    (E K : Type*) [Field E] [Field K] [Infinite E]
    [Algebra E K] [Module.Free E K] [Module.Finite E K] [IsGalois E K]
    {p : ℕ} (hp : 1 ≤ p) (hdegree : Module.finrank E K = p) (Delta : K) {k : ℕ} (hk : 1 ≤ k) :
    eval (fun i : Fin p => elementarySymmetric E K ((i : ℕ) + 1) Delta)
      (tracePolynomial (p := p) k) = trace E K ((Delta ^ p - Delta) ^ k) := by
  rw [tracePolynomial, eval_sum, filtered_trace_binomial E K hp Delta k]
  apply Finset.sum_congr rfl
  intro v _
  rw [eval_mul, eval_C, eval_signed, trace_eq_newton E K hdegree Delta (by omega)]

theorem eval_affine
    (E K : Type*) [Field E] [Field K]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra E K] [Module.Free E K] [Module.Finite E K] [IsGalois E K]
    {p : ℕ} (hdegree : Module.finrank E K = p) (Delta : K) (c : E) :
    eval (fun i : Fin p => elementarySymmetric E K ((i : ℕ) + 1) Delta) (affine c) =
      norm E K (Delta + algebraMap E K c) := by
  rw [← filteredNormPolynomial_eval, filteredNormPolynomial, Polynomial.eval_finsetSum, hdegree]
  simp only [affine, eval_add, eval_C, eval_sum, eval_mul, eval_X,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [Finset.sum_range_succ', elementarySymmetric_zero, one_mul, Nat.sub_zero, add_comm]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => c ^ (p - (i + 1)) * elementarySymmetric E K (i + 1) Delta)]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma weight_ge_length {p : ℕ} (m : Fin p →₀ ℕ) :
    filteredLength m ≤ filteredWeight m := by
  exact Finset.sum_le_sum fun i _ => Nat.le_mul_of_pos_left _ (by omega)

lemma weight_zero_iff {p : ℕ} (m : Fin p →₀ ℕ) : filteredWeight m = 0 ↔ m = 0 := by
  constructor
  · intro h
    have hl : filteredLength m = 0 := by have := weight_ge_length m; omega
    ext i
    have hi := Finset.single_le_sum (f := fun i : Fin p => m i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    change m i ≤ filteredLength m at hi
    simpa only [Finsupp.zero_apply] using (show m i = 0 by omega)
  · rintro rfl
    simp [filteredWeight]

lemma weight_one {p : ℕ} (hp : 0 < p) (m : Fin p →₀ ℕ) (hw : filteredWeight m = 1) :
    m = Finsupp.single ⟨0, hp⟩ 1 := by
  have hle := weight_ge_length m
  have hl : filteredLength m = 1 := by
    by_contra h
    have hr : filteredLength m = 0 := by omega
    have hw' := filtered_weight_le m
    rw [hr, mul_zero, hw] at hw'
    omega
  have hsum : (∑ i : Fin p, (i : ℕ) * m i) = 0 := by
    have h : filteredWeight m = (∑ i : Fin p, (i : ℕ) * m i) + filteredLength m := by
      simp [filteredWeight, filteredLength, add_mul, Finset.sum_add_distrib]
    omega
  have hz (i : Fin p) (hi : i ≠ ⟨0, hp⟩) : m i = 0 := by
    have h := (Finset.sum_eq_zero_iff.mp hsum) i (Finset.mem_univ i)
    exact (Nat.mul_eq_zero.mp h).resolve_left (fun h => hi (Fin.ext h))
  have h0 : m ⟨0, hp⟩ = 1 := by
    rw [← hl]
    dsimp [filteredLength]
    exact (Finset.sum_eq_single _ (fun i _ hi => hz i hi) (by simp)).symm
  ext i
  by_cases hi : i = ⟨0, hp⟩
  · subst i; simpa using h0
  · simp [hi, hz i hi]

lemma selected_weight {p k n : ℕ} (hp : 3 ≤ p) (hk : k ≤ p) (hn : n ≤ p * k)
    (hdiv : p - 1 ∣ p * k - n) :
    (n = 0 ∧ k = p - 1) ∨ (n = 1 ∧ k = p) ∨
      ∃ v : ℕ, v ≤ k ∧ n = k + (p - 1) * v := by
  obtain ⟨d, hd⟩ := hdiv
  have hd' : n + (p - 1) * d = p * k := by omega
  by_cases hdle : d ≤ k
  · right; right
    refine ⟨k - d, by omega, ?_⟩
    nlinarith [Nat.sub_add_cancel hdle, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  · have hdk : d = k + 1 := by
      have h : k + 2 ≤ d → p * k < (p - 1) * d := by
        intro h
        nlinarith [Nat.mul_le_mul_left (p - 1) h, Nat.sub_add_cancel (by omega : 1 ≤ p)]
      have : d < k + 2 := by by_contra h'; have := h (by omega); omega
      omega
    rw [hdk] at hd'
    have hsmall : n + (p - 1) = k := by nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ p)]
    omega


def pCoefficient {p : ℕ} (hp : 0 < p) (k : ℕ) (m : Fin p →₀ ℕ) : ℤ :=
  (if m = Finsupp.single ⟨p - 1, by omega⟩ k then 1 else 0) +
    if filteredLength m ≤ k then
      k.choose (filteredLength m) * m.multinomial *
        (if p - 1 ∣ p * k - filteredWeight m then (p : ℤ) - 1 else 0)
    else 0

def rawCoefficient {p : ℕ} (hp : 0 < p) (k : ℕ) (m : Fin p →₀ ℕ) : ℤ :=
  pCoefficient hp k m - coeff m (tracePolynomial (p := p) (R := ℤ) k)

lemma cast_coeff_tracePolynomial {p k : ℕ} {R : Type*} [CommRing R]
    (hk : 1 ≤ k) (m : Fin p →₀ ℕ) :
    coeff m (tracePolynomial (p := p) (R := R) k) =
      ((coeff m (tracePolynomial (p := p) (R := ℤ) k) : ℤ) : R) := by
  simp only [tracePolynomial, coeff_sum, coeff_C_mul, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [coeff_signed (by omega), coeff_signed (by omega)]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast,
    Int.cast_ite, Int.cast_zero, Int.cast_id]

lemma translated_sub_trace_coeff {p k : ℕ} {R J : Type*} [CommRing R] [Fintype J]
    (hp : 0 < p) (hk : 1 ≤ k) (c : J → R)
    (hmoment : ∀ n : ℕ, (∑ j, c j ^ n) = if p - 1 ∣ n then ((p - 1 : ℕ) : R) else 0)
    (m : Fin p →₀ ℕ) :
    coeff m (translated hp c k - tracePolynomial k) = (rawCoefficient hp k m : R) := by
  rw [coeff_sub, coeff_translated hp c hmoment, cast_coeff_tracePolynomial hk]
  simp only [rawCoefficient, pCoefficient, Int.cast_sub, Int.cast_add, Int.cast_ite,
    Int.cast_one, Int.cast_zero, Int.cast_mul, Int.cast_natCast, Nat.cast_sub hp, Nat.cast_one]

lemma raw_boundary {p k v : ℕ} (hp : 1 < p) (hodd : Odd p) (hk : 1 ≤ k) (hv : v ≤ k)
    (m : Fin p →₀ ℕ) (hw : filteredWeight m = k + (p - 1) * v)
    (hr : filteredLength m = v + 1) :
    rawCoefficient (by omega) k m = filteredBoundaryCoefficient k v m := by
  have htop : m ≠ Finsupp.single ⟨p - 1, by omega⟩ k := by
    intro h
    have hl := congrArg (fun m : Fin p →₀ ℕ => filteredLength m) h
    have hn := congrArg (fun m : Fin p →₀ ℕ => filteredWeight m) h
    simp only [Finsupp.single_eq_pi_single, filteredLength_single, filteredWeight_single] at hl hn
    have : p - 1 + 1 = p := by omega
    rw [this] at hn
    nlinarith
  have hsign : (-1 : ℤ) ^ (filteredLength m + v) = -1 := by
    rw [hr]
    have h : Odd (v + 1 + v) := ⟨v, by omega⟩
    exact h.neg_one_pow
  rw [rawCoefficient, coeff_tracePolynomial hp hodd hk hv m hw, hsign, pCoefficient, if_neg htop]
  simp only [zero_add, neg_one_mul, Int.cast_id]
  rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
  by_cases hrk : filteredLength m ≤ k
  · rw [if_pos hrk]
    have hd : p - 1 ∣ p * k - filteredWeight m := by
      refine ⟨k - v, ?_⟩
      have hvl := Nat.sub_add_cancel hv
      have hsum : filteredWeight m + (p - 1) * (k - v) = p * k := by
        rw [hw]
        nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ p)]
      omega
    rw [if_pos hd]
    dsimp only [filteredBoundaryCoefficient]
    ring
  · rw [if_neg hrk]
    dsimp only [filteredBoundaryCoefficient]
    rw [Nat.choose_eq_zero_of_lt (by omega : k < filteredLength m)]
    simp


lemma raw_norm_power {p k : ℕ} (hp : 1 < p) (hodd : Odd p) (hk : 1 ≤ k) :
    rawCoefficient (p := p) (by omega) k (Finsupp.single ⟨p - 1, by omega⟩ k) = 0 := by
  let i : Fin p := ⟨p - 1, by omega⟩
  have hw : filteredWeight (Finsupp.single i k) = k + (p - 1) * k := by
    rw [Finsupp.single_eq_pi_single, filteredWeight_single]
    dsimp [i]
    nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hsign : (-1 : ℤ) ^ (k + k) = 1 := (show Even (k + k) from ⟨k, rfl⟩).neg_one_pow
  change rawCoefficient _ k (Finsupp.single i k) = 0
  rw [rawCoefficient, coeff_tracePolynomial hp hodd hk le_rfl _ hw, pCoefficient]
  rw [if_pos (show Finsupp.single i k = Finsupp.single ⟨p - 1, by omega⟩ k from rfl)]
  simp only [Finsupp.single_eq_pi_single, filteredLength_single, filteredNewtonCoefficient_single i (r := k) (by omega),
    Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _), Nat.multinomial_single,
    filteredWeight_single,
    le_refl, ite_true, Nat.choose_self, Nat.cast_one, mul_one, one_mul, hsign, Int.cast_id]
  have hi : ((i : ℕ) + 1) = p := by dsimp [i]; omega
  rw [hi, Nat.sub_self, if_pos (dvd_zero _)]
  have hiZ : ((i : ℕ) : ℤ) + 1 = p := by exact_mod_cast hi
  linarith

lemma lowerLength_zero {p : ℕ} (hp : 0 < p) (m : Fin p →₀ ℕ)
    (hnu : filteredLowerLength m = 0) :
    (m : Fin p → ℕ) = Pi.single ⟨p - 1, by omega⟩ (filteredLength m) := by
  let i : Fin p := ⟨p - 1, by omega⟩
  have hz (j : Fin p) (hj : j ≠ i) : m j = 0 := by
    have hjp : (j : ℕ) + 1 < p := by
      have := j.isLt
      by_contra h
      exact hj (Fin.ext (by dsimp [i]; omega))
    have h := (Finset.sum_eq_zero_iff.mp hnu) j (Finset.mem_univ j)
    simpa only [if_pos hjp] using h
  apply filtered_single_of_length m i
  dsimp [filteredLength]
  exact (Finset.sum_eq_single i (fun j _ hj => hz j hj) (by simp)).symm

lemma boundary_prime_dvd {p k v : ℕ} (hp : p.Prime) (hk : k ≤ p) (hv : v ≤ k)
    (m : Fin p →₀ ℕ) (hw : filteredWeight m = k + (p - 1) * v)
    (hr : filteredLength m = v + 1)
    (hex : k ≠ p - 1 ∨ m ≠ Finsupp.single ⟨p - 2, by have := hp.two_le; omega⟩ p) :
    (p : ℤ) ∣ filteredBoundaryCoefficient k v m := by
  have hw' : filteredWeight m = (p - 1) * v + k := by omega
  by_cases hrk : filteredLength m ≤ k
  · by_cases hrp : filteredLength m < p
    · exact filteredBoundaryCoefficient_prime_dvd_of_length_lt hp m hv hr hw' hrp
    · have hkp : k = p := by omega
      have hvp : v = p - 1 := by omega
      subst k; subst v
      exact filteredBoundaryCoefficient_prime_dvd_at_prime hp m (by omega) hw'
  · have hvk : v = k := by omega
    subst v
    have hn : filteredWeight m = p * k := by
      rw [hw]; nlinarith [Nat.sub_add_cancel hp.one_le]
    have heq : filteredBoundaryCoefficient k k m = filteredNewtonCoefficient m := by
      dsimp only [filteredBoundaryCoefficient]
      rw [Nat.choose_eq_zero_of_lt (by omega : k < filteredLength m), Nat.choose_self]
      ring
    rw [heq]
    by_cases hke : k = p - 1
    · have hme := hex.resolve_left (not_ne_iff.mpr hke)
      have hmf : (m : Fin p → ℕ) ≠ Pi.single ⟨p - 2, by have := hp.two_le; omega⟩ p := by
        intro h
        exact hme (DFunLike.coe_injective (h.trans (Finsupp.single_eq_pi_single _ _).symm))
      have h := filteredNewtonCoefficient_exceptional hp m (by have := hp.one_le; omega) (by simpa [hke] using hn)
      simpa only [if_neg hmf, sub_zero] using h
    · exact filteredNewtonCoefficient_prime_dvd_last hp hk hke m (by omega) hn


lemma boundary_mem
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    {p k v : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hk : k ≤ p) (hv : v ≤ k)
    (t delta R : ℤ) (ht : 0 ≤ t) (hd : 0 ≤ delta)
    (m : Fin p →₀ ℕ) (hw : filteredWeight m = k + (p - 1) * v)
    (hr : filteredLength m = v + 1)
    (hex : k ≠ p - 1 ∨ m ≠ Finsupp.single ⟨p - 2, by omega⟩ p)
    (z : E) (hz : z ∈ lattice E (R - t + ((p : ℤ) - 1) * (t + filteredLowerLength m * delta)))
    (hpval : (p : E) ∈ lattice E (((p : ℤ) - 1) * (t + delta))) :
    (filteredBoundaryCoefficient k v m : E) * z ∈ lattice E ((p : ℤ) * (t + delta) + R) := by
  by_cases hnu : 1 ≤ filteredLowerLength m
  · exact filteredMonomial_coefficient_mem E hp3 t delta R ht hd z hnu hz hpval _
      (boundary_prime_dvd hp hk hv m hw hr hex)
  · have hnuz : filteredLowerLength m = 0 := by omega
    have hm := lowerLength_zero hp.pos m hnuz
    have hn := congrArg filteredWeight hm
    rw [filteredWeight_single, hw, hr] at hn
    have hpp : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
    rw [hpp] at hn
    have hv0 : v = 0 := by nlinarith
    have hkp : k = p := by nlinarith
    subst v; subst k
    rw [hr] at hm
    have hc : filteredBoundaryCoefficient p 0 m = (p : ℤ) ^ 2 := by
      dsimp only [filteredBoundaryCoefficient]
      rw [hm, filteredLength_single, Nat.multinomial_single,
        filteredNewtonCoefficient_single _ (by omega), Nat.choose_one_right, Nat.choose_zero_right]
      push_cast [Nat.cast_sub hp.one_le]
      ring
    rw [hc, Int.cast_pow, Int.cast_natCast]
    apply filteredMonomial_prime_sq_mul_mem E hp3 t delta R ht hd z _ hpval
    simpa only [hnuz, Nat.cast_zero, zero_mul, add_zero] using hz

lemma ordinary_monomial_mem
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    {p k v : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hodd : Odd p) (hk1 : 1 ≤ k) (hk : k ≤ p) (hv : v ≤ k)
    (t delta R : ℤ) (ht : 0 ≤ t) (hd : 0 ≤ delta)
    (e : Fin p → E) (m : Fin p →₀ ℕ) (X : E)
    (hw : filteredWeight m = k + (p - 1) * v)
    (hex : k ≠ p - 1 ∨ m ≠ Finsupp.single ⟨p - 2, by omega⟩ p)
    (hm : X * filteredMonomial e m ∈ lattice E
      (R - t + ((p : ℤ) - 1) *
        (((filteredLength m : ℤ) - v) * t + filteredLowerLength m * delta)))
    (hpval : (p : E) ∈ lattice E (((p : ℤ) - 1) * (t + delta))) :
    (rawCoefficient hp.pos k m : E) * (X * filteredMonomial e m) ∈
      lattice E ((p : ℤ) * (t + delta) + R) := by
  have hweight : (filteredWeight m : ℤ) = ((p : ℤ) - 1) * v + k := by
    rw [hw]
    push_cast [Nat.cast_sub hp.one_le]
    ring
  have hrge : v ≤ filteredLength m := by
    have hl := filtered_weight_le m
    rw [hw] at hl
    nlinarith [Nat.sub_add_cancel hp.one_le]
  by_cases hr : filteredLength m = v
  · obtain ⟨hvk, hms⟩ := filtered_diagonal_selection hp.pos m hv hr (by omega)
    have hms' : m = Finsupp.single ⟨p - 1, by omega⟩ k :=
      DFunLike.coe_injective (hms.trans (Finsupp.single_eq_pi_single _ _).symm)
    rw [hms', raw_norm_power (by omega) hodd hk1, Int.cast_zero, zero_mul]
    exact (lattice E _).zero_mem
  · by_cases hr1 : filteredLength m = v + 1
    · rw [raw_boundary (by omega) hodd hk1 hv m hw hr1]
      apply boundary_mem E hp hp3 hk hv t delta R ht hd m hw hr1 hex _ _ hpval
      simpa only [hr1, Nat.cast_add, Nat.cast_one, add_sub_cancel_left, one_mul] using hm
    · have hz := filteredMonomial_deep E hp3 hk t delta R v ht hd (by omega)
        e m X hm hweight (by omega)
      simpa only [zsmul_eq_mul, Submodule.mem_toAddSubgroup] using (lattice E _).toAddSubgroup.zsmul_mem hz (rawCoefficient hp.pos k m)


lemma raw_constant {p k : ℕ} (hp : 3 ≤ p) (hk1 : 1 ≤ k) (hk : k ≤ p) :
    rawCoefficient (p := p) (by omega) k 0 = if k = p - 1 then (p : ℤ) - 1 else 0 := by
  have htop : (0 : Fin p →₀ ℕ) ≠ Finsupp.single ⟨p - 1, by omega⟩ k := by
    intro h
    have h' := congrArg (fun m : Fin p →₀ ℕ => m ⟨p - 1, by omega⟩) h
    simp only [Finsupp.zero_apply, Finsupp.single_eq_same] at h'
    omega
  rw [rawCoefficient, coeff_tracePolynomial_zero hk1 0 (by simp [filteredWeight]; omega),
    sub_zero, pCoefficient, if_neg htop]
  simp only [filteredLength, Finsupp.zero_apply, Finset.sum_const_zero, Nat.zero_le, ite_true,
    Nat.choose_zero_right, Nat.cast_one, one_mul, zero_add, filteredWeight, mul_zero,
    Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
  have hmulti : Nat.multinomial Finset.univ (0 : Fin p →₀ ℕ) = 1 := by simp [Nat.multinomial]
  rw [hmulti, Nat.cast_one, one_mul, Nat.sub_zero]
  have hd : p - 1 ∣ p * k ↔ k = p - 1 := by
    constructor
    · intro h
      have hkdiv : p - 1 ∣ k := by
        have heq : p * k = (p - 1) * k + k := by nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ p)]
        rw [heq] at h
        exact (Nat.dvd_add_right (dvd_mul_right (p - 1) k)).mp h
      obtain ⟨d, hd⟩ := hkdiv
      have hd1 : d = 1 := by
        have hp0 : 0 < p - 1 := by omega
        nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ p)]
      simpa only [hd1, mul_one] using hd
    · rintro rfl
      exact dvd_mul_left _ _
  simp only [hd]

lemma raw_exception {p : ℕ} (hp : 3 ≤ p) (hodd : Odd p) :
    rawCoefficient (p := p) (by omega) (p - 1) (Finsupp.single ⟨p - 2, by omega⟩ p) = (p : ℤ) - 1 := by
  let i : Fin p := ⟨p - 2, by omega⟩
  have hw : filteredWeight (Finsupp.single i p) = (p - 1) + (p - 1) * (p - 1) := by
    rw [Finsupp.single_eq_pi_single, filteredWeight_single]
    dsimp [i]
    nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ p), Nat.sub_add_cancel (by omega : 2 ≤ p)]
  have hr : filteredLength (Finsupp.single i p) = (p - 1) + 1 := by
    rw [Finsupp.single_eq_pi_single, filteredLength_single, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  change rawCoefficient _ _ (Finsupp.single i p) = _
  rw [raw_boundary (by omega) hodd (by omega) le_rfl _ hw hr]
  simp only [filteredBoundaryCoefficient, Finsupp.single_eq_pi_single, filteredLength_single,
    Nat.choose_eq_zero_of_lt (by omega : p - 1 < p), Nat.cast_zero, mul_zero, zero_mul,
    zero_add, Nat.choose_self, Nat.cast_one, one_mul,
    filteredNewtonCoefficient_single i (r := p) (by omega)]
  dsimp [i]
  omega


lemma raw_off_range {p k : ℕ} (hp : 3 ≤ p) (hk1 : 1 ≤ k) (hk : k ≤ p)
    (m : Fin p →₀ ℕ) (hm0 : m ≠ 0)
    (hno : ¬ ∃ v : ℕ, v ≤ k ∧ filteredWeight m = k + (p - 1) * v) :
    rawCoefficient (by omega) k m =
      if k = p ∧ m = Finsupp.single ⟨0, by omega⟩ 1 then (p : ℤ) * (p - 1) else 0 := by
  have htop : m ≠ Finsupp.single ⟨p - 1, by omega⟩ k := by
    intro h
    apply hno
    refine ⟨k, le_rfl, ?_⟩
    rw [h, Finsupp.single_eq_pi_single, filteredWeight_single]
    nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hQ := coeff_tracePolynomial_zero (R := ℤ) hk1 m (fun v hv hw => hno ⟨v, hv, hw⟩)
  rw [rawCoefficient, hQ, sub_zero, pCoefficient, if_neg htop, zero_add]
  by_cases hsel : filteredLength m ≤ k ∧ p - 1 ∣ p * k - filteredWeight m
  · obtain ⟨hr, hd⟩ := hsel
    obtain h | h | h := selected_weight hp hk ((filtered_weight_le m).trans (Nat.mul_le_mul_left p hr)) hd
    · exact (hm0 ((weight_zero_iff m).mp h.1)).elim
    · obtain ⟨hn, hkp⟩ := h
      have hms := weight_one (by omega) m hn
      subst k
      rw [if_pos hr, if_pos hd, if_pos ⟨rfl, hms⟩, hms]
      simp only [Finsupp.single_eq_pi_single, filteredLength_single, Nat.choose_one_right,
        Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _), Nat.multinomial_single,
        Nat.cast_one, mul_one]
    · exact (hno h).elim
  · have hnot : ¬ (k = p ∧ m = Finsupp.single ⟨0, by omega⟩ 1) := by
      rintro ⟨hkp, hms⟩
      apply hsel
      rw [hkp, hms]
      simp only [Finsupp.single_eq_pi_single, filteredLength_single, filteredWeight_single,
        Nat.zero_add, one_mul]
      refine ⟨by omega, ⟨p + 1, ?_⟩⟩
      have hsum : (p - 1) * (p + 1) + 1 = p * p := by
        nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ p)]
      omega
    rw [if_neg hnot]
    by_cases hr : filteredLength m ≤ k
    · rw [if_pos hr, if_neg (fun hd => hsel ⟨hr, hd⟩), mul_zero]
    · rw [if_neg hr]


def exceptional {p : ℕ} {R : Type*} [CommRing R] (hp : 3 ≤ p) (k : ℕ) : MvPolynomial (Fin p) R :=
  if k = p - 1 then C ((p : R) - 1) * (1 + X ⟨p - 2, by omega⟩ ^ p) else 0

lemma coeff_exceptional {p : ℕ} {R : Type*} [CommRing R] (hp : 3 ≤ p) (k : ℕ) (m : Fin p →₀ ℕ) :
    coeff m (exceptional (R := R) hp k) =
      if k = p - 1 then ((p : R) - 1) *
        ((if m = 0 then 1 else 0) + (if m = Finsupp.single ⟨p - 2, by omega⟩ p then 1 else 0)) else 0 := by
  classical
  by_cases h : k = p - 1
  · simp only [exceptional, if_pos h, coeff_C_mul, coeff_add, coeff_one, coeff_X_pow]
    simp only [eq_comm (a := (0 : Fin p →₀ ℕ)) (b := m),
      eq_comm (a := Finsupp.single ⟨p - 2, by omega⟩ p) (b := m)]
  · simp only [exceptional, if_neg h, coeff_zero]

lemma corrected_monomial_mem
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    {p k : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hodd : Odd p) (hk1 : 1 ≤ k) (hk : k ≤ p)
    (t delta R : ℤ) (ht : 0 ≤ t) (hd : 0 ≤ delta)
    (e : Fin p → E) (m : Fin p →₀ ℕ) (X : E)
    (hm : ∀ v : ℤ, (filteredWeight m : ℤ) = ((p : ℤ) - 1) * v + k →
      X * filteredMonomial e m ∈ lattice E
        (R - t + ((p : ℤ) - 1) *
          (((filteredLength m : ℤ) - v) * t + filteredLowerLength m * delta)))
    (hpval : (p : E) ∈ lattice E (((p : ℤ) - 1) * (t + delta))) :
    ((rawCoefficient hp.pos k m - coeff m (exceptional (R := ℤ) hp3 k) : ℤ) : E) *
      (X * filteredMonomial e m) ∈ lattice E ((p : ℤ) * (t + delta) + R) := by
  classical
  let i : Fin p := ⟨p - 2, by omega⟩
  have hi0 : Finsupp.single i p ≠ 0 := by
    intro h
    have h' := congrArg (fun m : Fin p →₀ ℕ => m i) h
    simp only [Finsupp.single_eq_same, Finsupp.zero_apply] at h'
    omega
  by_cases hm0 : m = 0
  · rw [hm0, raw_constant hp3 hk1 hk, coeff_exceptional]
    have hne : (0 : Fin p →₀ ℕ) ≠ Finsupp.single i p := Ne.symm hi0
    change (((if k = p - 1 then (p : ℤ) - 1 else 0) -
      (if k = p - 1 then ((p : ℤ) - 1) * ((if (0 : Fin p →₀ ℕ) = 0 then 1 else 0) +
        (if (0 : Fin p →₀ ℕ) = Finsupp.single i p then 1 else 0)) else 0) : ℤ) : E) * _ ∈ _
    simp only [ite_true, if_neg hne, add_zero, mul_one, sub_self, Int.cast_zero, zero_mul]
    exact (lattice E _).zero_mem
  by_cases hex : k = p - 1 ∧ m = Finsupp.single i p
  · obtain ⟨hke, hme⟩ := hex
    rw [hke, hme, raw_exception hp3 hodd, coeff_exceptional]
    change (((p : ℤ) - 1 - (if p - 1 = p - 1 then ((p : ℤ) - 1) *
      ((if Finsupp.single i p = 0 then 1 else 0) + (if Finsupp.single i p = Finsupp.single i p then 1 else 0))
      else 0) : ℤ) : E) * _ ∈ _
    simp only [ite_true, if_neg hi0, zero_add, mul_one, sub_self, Int.cast_zero, zero_mul]
    exact (lattice E _).zero_mem
  have hexc : coeff m (exceptional (R := ℤ) hp3 k) = 0 := by
    rw [coeff_exceptional]
    by_cases hke : k = p - 1
    · rw [if_pos hke, if_neg hm0, if_neg (fun hme => hex ⟨hke, hme⟩)]
      ring
    · rw [if_neg hke]
  rw [hexc, sub_zero]
  by_cases hrange : ∃ v : ℕ, v ≤ k ∧ filteredWeight m = k + (p - 1) * v
  · obtain ⟨v, hv, hw⟩ := hrange
    apply ordinary_monomial_mem E hp hp3 hodd hk1 hk hv t delta R ht hd e m X hw
      (not_and_or.mp hex) _ hpval
    apply hm v
    rw [hw]
    push_cast [Nat.cast_sub hp.one_le]
    ring
  · rw [raw_off_range hp3 hk1 hk m hm0 hrange]
    split_ifs with hlast
    · obtain ⟨hkp, hms⟩ := hlast
      have hw : (filteredWeight m : ℤ) = ((p : ℤ) - 1) * (-1) + k := by
        rw [hms, Finsupp.single_eq_pi_single, filteredWeight_single, hkp]
        push_cast
        ring
      have hz := hm (-1) hw
      have hr : filteredLength m = 1 := by rw [hms, Finsupp.single_eq_pi_single, filteredLength_single]
      have hnu : filteredLowerLength m = 1 := by
        rw [filteredLowerLength, Finset.sum_eq_single (⟨0, hp.pos⟩ : Fin p)]
        · simp [hms, show 1 < p from by omega]
        · intro j _ hj
          simp only [hms, Finsupp.single_eq_of_ne hj, ite_self]
        · simp
      have hz' : X * filteredMonomial e m ∈ lattice E (R - t + ((p : ℤ) - 1) * (t + (1 : ℕ) * delta)) := by
        rw [hr, hnu] at hz
        apply lattice_antitone E _ hz
        push_cast
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ (p : ℤ) - 1 by omega) ht]
      exact filteredMonomial_coefficient_mem E hp3 t delta R ht hd _ le_rfl hz' hpval _ (dvd_mul_right _ _)
    · simp only [Int.cast_zero, zero_mul]
      exact (lattice E _).zero_mem



end FilteredPolynomial

open FilteredPolynomial MvPolynomial

/-- Paper `O:A:lem:filtered` for actual upper-field conjugates. The coefficient
and prime valuation premises are `O:A:eq:ei` and `O:A:eq:pbound`. The outer
factor may be any element at the paper's weighted depth; in the diamond
application it is the lower norm mapped into `B_1`. -/
theorem filteredCoefficients
    (E K : Type*) [Field E] [Field K]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra E K] [ValuativeExtension E K] [Module.Free E K] [Module.Finite E K] [IsGalois E K]
    {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) (hchar : residueCharacteristic E = p)
    (hdegree : Module.finrank E K = p) (hram : ramificationIndex E K = p)
    (Delta : K) (t delta R : ℤ) (ht : 0 ≤ t) (hd : 0 ≤ delta)
    (hDelta : ord K Delta = ((-t : ℤ) : WithTop ℤ))
    (he : ∀ j : ℕ, 1 ≤ j → j < p →
      elementarySymmetric E K j Delta ∈ lattice E (((p : ℤ) - 1) * (t + delta) - j * t))
    (hpval : (p : E) ∈ lattice E (((p : ℤ) - 1) * (t + delta)))
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ p) (X : E)
    (hX : X ∈ lattice E (R + ((k : ℤ) - 1) * t)) :
    X * (norm E K Delta ^ k +
        (∑ j : (ZMod p)ˣ, norm E K (Delta + algebraMap E K (primeTeichmuller E p hchar j)) ^ k) -
        trace E K ((Delta ^ p - Delta) ^ k)) -
      (if k = p - 1 then ((p : E) - 1) * X *
        (1 + elementarySymmetric E K (p - 1) Delta ^ p) else 0) ∈
      lattice E ((p : ℤ) * (t + delta) + R) := by
  classical
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  letI : Infinite E := by
    let f : ℤ → E := fun n => Classical.choose (exists_ord_eq E n)
    apply Infinite.of_injective f
    intro m n h
    have hm := Classical.choose_spec (exists_ord_eq E m)
    have hn := Classical.choose_spec (exists_ord_eq E n)
    have ho := congrArg (ord E) h
    exact WithTop.coe_injective (hm.symm.trans (ho.trans hn))
  let e : Fin p → E := fun i => elementarySymmetric E K ((i : ℕ) + 1) Delta
  let c : (ZMod p)ˣ → E := fun j => primeTeichmuller E p hchar j
  let f : MvPolynomial (Fin p) E := translated hp.pos c k - tracePolynomial k - exceptional hp3 k
  have hf : X * eval e f ∈ lattice E ((p : ℤ) * (t + delta) + R) := by
    rw [MvPolynomial.eval_eq, Finset.mul_sum]
    apply (lattice E _).sum_mem
    intro m _
    have hc : coeff m f =
        ((rawCoefficient hp.pos k m - coeff m (exceptional (R := ℤ) hp3 k) : ℤ) : E) := by
      rw [show f = translated hp.pos c k - tracePolynomial k - exceptional hp3 k from rfl,
        coeff_sub, translated_sub_trace_coeff hp.pos hk1 c (filtered_teichmuller_moment E p hchar),
        coeff_exceptional, coeff_exceptional]
      simp only [Int.cast_sub, Int.cast_ite, Int.cast_mul, Int.cast_natCast, Int.cast_one,
        Int.cast_zero, Int.cast_add]
    rw [hc]
    have hm := corrected_monomial_mem E hp hp3 hodd hk1 hk t delta R ht hd e m X
      (fun v hv => filtered_actualMonomial_mem E K hdegree hram Delta t delta R v k
        hDelta he m X hX hv) hpval
    have hprod : (∏ i ∈ m.support, e i ^ m i) = filteredMonomial e m := by
      change m.prod (fun i n => e i ^ n) = _
      rw [Finsupp.prod_fintype]
      · rfl
      · simp
    rw [hprod]
    simpa only [mul_assoc, mul_left_comm] using hm
  have heval : eval e f = norm E K Delta ^ k +
      (∑ j : (ZMod p)ˣ, norm E K (Delta + algebraMap E K (c j)) ^ k) -
      trace E K ((Delta ^ p - Delta) ^ k) -
      (if k = p - 1 then ((p : E) - 1) * (1 + elementarySymmetric E K (p - 1) Delta ^ p) else 0) := by
    simp only [f, eval_sub, translated, eval_add, eval_pow, eval_X, eval_sum, e,
      eval_affine E K hdegree, eval_tracePolynomial E K (by omega) hdegree Delta hk1,
      exceptional]
    have htop : p - 1 + 1 = p := by omega
    have hex : p - 2 + 1 = p - 1 := by omega
    have hnorm : elementarySymmetric E K p Delta = norm E K Delta := by
      rw [← hdegree, elementarySymmetric_finrank]
    split_ifs <;> simp only [eval_mul, eval_C, eval_add, map_one, eval_pow, eval_X, map_zero,
      htop, hex, hnorm]
  rw [heval] at hf
  convert hf using 1
  dsimp only [c]
  split_ifs <;> ring

end

end LanglandsSecondMainLemma.Odd.Total
