import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsSecondMainLemma.Gauss.LeadingTerm
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Primitive digits and the factorial congruence

The arithmetic in the proof of Theorem 5.1 of `epsilon_SML.tex`, specifically
(O:F:digits), (O:F:digitsum), and (O:F:factorials), lines 858–896.

In that proof `q = p^f`, `ell` is prime, `ell ∣ q-1`, and the exponent of
`chi_0` satisfies `1 ≤ a ≤ q-2` and `ell ∤ a`. We write `q = ell*h+1`.
The digit calculation applies to all `a < q` coprime to `ell`; the factorial
calculation in fact applies to every `a < q` and every positive `ell`.
These are arithmetic statements independent of the choices of characters.

The factorial congruence is expressed by a strict norm bound on the ratio
in `ℚ_[p]`, i.e. the ratio belongs to `1 + maximalIdeal`. All factorials
are nonzero there. We never reduce a factorial divisible by `p` as a unit:
at each step we compare `t + j*q` to `t` using `0 < t < p^f`.
-/

open scoped BigOperators
open Finset

namespace LanglandsSecondMainLemma.Tame

noncomputable section

/-- The unordered digit indexed by `j` in (O:F:digits), with `q = ell*h+1`.
The quotient is `a/ell + 1` exactly when `j ≥ ell - a%ell`. -/
def primitiveDigit (ell h a j : ℕ) : ℕ := j * h + (a + j) / ell

/-- The primitive exponent `a*S/ell`, where `S = 1+q+⋯+q^(ell-1)`. -/
def primitiveExponent (q ell a : ℕ) : ℕ :=
  (a * ∑ i ∈ range ell, q ^ i) / ell

private theorem repeated_div (q a r i : ℕ) (hq : 0 < q) (ha : a < q) (hi : i ≤ r) :
    (a * ∑ j ∈ range r, q ^ j) / q ^ i = a * ∑ j ∈ range (r-i), q ^ j := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, ← Nat.div_div_eq_div_mul, ih (by omega)]
    have hr : r-i = (r-(i+1))+1 := by omega
    rw [hr, geom_sum_succ]
    have he : a * (q * (∑ j ∈ range (r-(i+1)), q ^ j) + 1) =
        a + q * (a * ∑ j ∈ range (r-(i+1)), q ^ j) := by ring
    rw [he, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt ha, zero_add]

private theorem repeated_mod (ell h a r : ℕ) :
    (a * ∑ j ∈ range r, (ell*h+1) ^ j) % ell = (a*r) % ell := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [geom_sum_succ]
    have he : a * ((ell*h+1) * (∑ j ∈ range r, (ell*h+1)^j) + 1) =
        ell * (h*a*(∑ j ∈ range r, (ell*h+1)^j)) +
          (a * ∑ j ∈ range r, (ell*h+1)^j) + a := by ring
    rw [he, Nat.add_mod, Nat.mul_add_mod_self_left, ih]
    simp [Nat.mul_add, Nat.add_mod]

private theorem divided_repeated_digit (ell h a r : ℕ) (hl : 0 < ell)
    (ha : a < ell*h+1) :
    ((a * ∑ j ∈ range (r+1), (ell*h+1)^j) / ell) % (ell*h+1) =
      primitiveDigit ell h a ((a*r)%ell) := by
  let q := ell*h+1
  let T := a * ∑ j ∈ range r, q^j
  have ht : T % ell < ell := Nat.mod_lt _ hl
  have he : a * ∑ j ∈ range (r+1), q^j =
      a + q*(T%ell) + ell*(q*(T/ell)) := by
    rw [geom_sum_succ]
    dsimp [T]
    have hd := Nat.mod_add_div (a * ∑ j ∈ range r, q^j) ell
    nlinarith
  have hb : (a + q*(T%ell)) / ell < q := by
    apply (Nat.div_lt_iff_lt_mul hl).mpr
    dsimp [q] at *
    nlinarith
  change (_ / ell) % q = _
  rw [he, Nat.add_mul_div_left _ _ hl, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hb]
  have he' : a + q*(T%ell) = (a+T%ell) + ell*((T%ell)*h) := by dsimp [q]; ring
  rw [he', Nat.add_mul_div_left _ _ hl]
  dsimp [T, q]
  rw [repeated_mod]
  exact Nat.add_comm _ _

/-- The natural quotient defining the exponent is exact. -/
theorem primitiveExponent_mul (ell h a : ℕ) :
    ell * primitiveExponent (ell*h+1) ell a =
      a * ∑ i ∈ range ell, (ell*h+1)^i := by
  unfold primitiveExponent
  apply Nat.mul_div_cancel'
  apply Nat.dvd_of_mod_eq_zero
  rw [repeated_mod]
  simp

/-- Agreement with the paper's geometric-quotient definition of `S`. -/
theorem primitiveExponent_eq (ell h a : ℕ) (hl : 0 < ell) (hh : 0 < h) :
    primitiveExponent (ell*h+1) ell a =
      (a * (((ell*h+1)^ell-1) / ((ell*h+1)-1))) / ell := by
  unfold primitiveExponent
  rw [Nat.geomSum_eq (by nlinarith) ell]

/-- The floor formula equals the manuscript's explicit indicator formula. -/
theorem primitiveDigit_eq (ell h a j : ℕ) (hl : 0 < ell) (hj : j < ell) :
    primitiveDigit ell h a j = a / ell + j*h +
      if ell - a % ell ≤ j then 1 else 0 := by
  have hm := Nat.mod_lt a hl
  have hd := Nat.mod_add_div a ell
  unfold primitiveDigit
  have he : a+j = (a%ell+j) + ell*(a/ell) := by omega
  rw [he, Nat.add_mul_div_left _ _ hl]
  by_cases hc : ell-a%ell ≤ j
  · rw [if_pos hc]
    have : (a%ell+j)/ell = 1 := (Nat.div_eq_iff hl).mpr (by omega)
    omega
  · rw [if_neg hc, Nat.div_eq_of_lt (by omega)]
    omega

/-- The ordered digits, prior to forgetting their order. -/
theorem primitiveExponent_digit (ell h a i : ℕ) (hl : 0 < ell)
    (ha : a < ell*h+1) (hi : i < ell) :
    Gauss.basePDigit (ell*h+1) (primitiveExponent (ell*h+1) ell a) i =
      primitiveDigit ell h a ((a*(ell-1-i))%ell) := by
  unfold Gauss.basePDigit primitiveExponent
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm ell ((ell*h+1)^i), ← Nat.div_div_eq_div_mul,
    repeated_div _ _ _ _ (by omega) ha (by omega)]
  have he : ell-i = (ell-1-i)+1 := by omega
  rw [he, divided_repeated_digit _ _ _ _ hl ha]

/-- (O:F:digits): all `ell` base-`q` positions, including zero digits, are
permuted by `i ↦ a*(ell-1-i) mod ell`. Here `q=ell*h+1`; the hypotheses
`ell` prime and `ell ∤ a` are exactly the primitivity used in this permutation. -/
theorem primitiveExponent_digits (ell h a : ℕ) (hl : ell.Prime)
    (ha : a < ell*h+1) (hprim : ¬ ell ∣ a) :
    ∃ σ : Equiv.Perm (Fin ell), ∀ i : Fin ell,
      Gauss.basePDigit (ell*h+1) (primitiveExponent (ell*h+1) ell a) i =
        a / ell + (σ i : ℕ)*h +
          if ell-a%ell ≤ (σ i : ℕ) then 1 else 0 := by
  let f : Fin ell → Fin ell := fun i ↦ ⟨(a*(ell-1-i))%ell, Nat.mod_lt _ hl.pos⟩
  have hf : Function.Injective f := by
    intro i j hij
    have he : a*(ell-1-i) ≡ a*(ell-1-j) [MOD ell] := congrArg Fin.val hij
    have hc := he.cancel_left_of_coprime ((hl.coprime_iff_not_dvd.mpr hprim).gcd_eq_one)
    have hi := i.isLt
    have hj := j.isLt
    rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : ell-1-i < ell),
      Nat.mod_eq_of_lt (by omega : ell-1-j < ell)] at hc
    apply Fin.ext
    omega
  let σ := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hf)
  refine ⟨σ, fun i ↦ ?_⟩
  rw [primitiveExponent_digit _ _ _ _ hl.pos ha i.isLt]
  exact primitiveDigit_eq ell h a (σ i) hl.pos (σ i).isLt

private theorem digit_increment (ell h a i : ℕ) (hl : 0 < ell) (hi : i < ell) :
    primitiveDigit ell h (a+1) i = primitiveDigit ell h a i +
      if i = ell-1-a%ell then 1 else 0 := by
  have hm := Nat.mod_lt a hl
  have hd := Nat.mod_add_div a ell
  have he : a+i = (a%ell+i) + ell*(a/ell) := by omega
  have he' : a+1+i = (a%ell+i+1) + ell*(a/ell) := by omega
  unfold primitiveDigit
  rw [he, he', Nat.add_mul_div_left _ _ hl, Nat.add_mul_div_left _ _ hl]
  by_cases hc : i = ell-1-a%ell
  · rw [if_pos hc, Nat.div_eq_of_lt (show a%ell+i < ell by omega)]
    have : (a%ell+i+1)/ell = 1 := (Nat.div_eq_iff hl).mpr (by omega)
    omega
  · rw [if_neg hc]
    by_cases hb : a%ell+i < ell
    · rw [Nat.div_eq_of_lt hb, Nat.div_eq_of_lt (by omega)]
      omega
    · have h1 : (a%ell+i)/ell = 1 := (Nat.div_eq_iff hl).mpr (by omega)
      have h2 : (a%ell+i+1)/ell = 1 := (Nat.div_eq_iff hl).mpr (by omega)
      omega

/-- The sum of the unordered digits, including the `j=0` term. -/
theorem primitiveDigit_sum (ell h a : ℕ) (hl : 0 < ell) :
    (∑ j ∈ range ell, primitiveDigit ell h a j) =
      a + ∑ j ∈ range ell, j*h := by
  induction a with
  | zero =>
    simp only [zero_add]
    apply sum_congr rfl
    intro j hj
    simp [primitiveDigit, Nat.div_eq_of_lt (mem_range.mp hj)]
  | succ a ih =>
    have hj : ell-1-a%ell < ell := by omega
    rw [sum_congr rfl (fun i hi ↦ digit_increment ell h a i hl (mem_range.mp hi)),
      sum_add_distrib, ih]
    simp [hj]
    omega

/-- (O:F:digitsum) for the actual base-`q` positions of the exponent. -/
theorem primitiveExponent_digitSum (ell h a : ℕ) (hl : ell.Prime)
    (ha : a < ell*h+1) (hprim : ¬ ell ∣ a) :
    Gauss.gaussDigitSum (ell*h+1) ell (primitiveExponent (ell*h+1) ell a) =
      a + ∑ j ∈ range ell, j*h := by
  obtain ⟨σ, hσ⟩ := primitiveExponent_digits ell h a hl ha hprim
  have he (i : Fin ell) :
      Gauss.basePDigit (ell*h+1) (primitiveExponent (ell*h+1) ell a) i =
        primitiveDigit ell h a (σ i) := by
    rw [hσ, primitiveDigit_eq _ _ _ _ hl.pos (σ i).isLt]
  unfold Gauss.gaussDigitSum
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [he]
  rw [Equiv.sum_comp σ (fun j : Fin ell ↦ primitiveDigit ell h a j),
    Fin.sum_univ_eq_sum_range, primitiveDigit_sum _ _ _ hl.pos]

/-- Reindexing the actual digit factorials by the permutation from (O:F:digits). -/
theorem primitiveExponent_digitFactorial (ell h a : ℕ) (hl : ell.Prime)
    (ha : a < ell*h+1) (hprim : ¬ ell ∣ a) :
    Gauss.gaussDigitFactorial (ell*h+1) ell (primitiveExponent (ell*h+1) ell a) =
      ∏ j ∈ range ell, (primitiveDigit ell h a j).factorial := by
  obtain ⟨σ, hσ⟩ := primitiveExponent_digits ell h a hl ha hprim
  have he (i : Fin ell) :
      Gauss.basePDigit (ell*h+1) (primitiveExponent (ell*h+1) ell a) i =
        primitiveDigit ell h a (σ i) := by
    rw [hσ, primitiveDigit_eq _ _ _ _ hl.pos (σ i).isLt]
  unfold Gauss.gaussDigitFactorial
  rw [← Fin.prod_univ_eq_prod_range]
  simp_rw [he]
  rw [Equiv.prod_comp σ (fun j : Fin ell ↦ (primitiveDigit ell h a j).factorial),
    Fin.prod_univ_eq_prod_range (fun j ↦ (primitiveDigit ell h a j).factorial)]

private theorem factorial_increment (ell h a : ℕ) (hl : 0 < ell) :
    (∏ i ∈ range ell, (primitiveDigit ell h (a+1) i).factorial) =
      (primitiveDigit ell h a (ell-1-a%ell)+1) *
        ∏ i ∈ range ell, (primitiveDigit ell h a i).factorial := by
  let j := ell-1-a%ell
  have hj : j < ell := by dsimp [j]; omega
  have he : ∀ i ∈ range ell,
      (primitiveDigit ell h (a+1) i).factorial =
        (if i = j then primitiveDigit ell h a j+1 else 1) *
          (primitiveDigit ell h a i).factorial := by
    intro i hi
    rw [digit_increment _ _ _ _ hl (mem_range.mp hi)]
    by_cases hij : i = j
    · simp [hij, j, Nat.factorial_succ]
    · simp [show i ≠ ell-1-a%ell from hij, hij]
  rw [prod_congr rfl he, prod_mul_distrib]
  simp [j, hj]

private theorem increment_coefficient (ell h a : ℕ) (hl : 0 < ell) :
    ell*(primitiveDigit ell h a (ell-1-a%ell)+1) =
      (a+1) + (ell-1-a%ell)*(ell*h+1) := by
  have hm := Nat.mod_lt a hl
  have hd := Nat.mod_add_div a ell
  have he : a+(ell-1-a%ell) = (ell-1)+ell*(a/ell) := by omega
  unfold primitiveDigit
  rw [he, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt (by omega), zero_add]
  have hs : (ell-1-a%ell)+a%ell+1 = ell := by omega
  nlinarith

private theorem principal_mul {p : ℕ} [Fact p.Prime] {x y : ℚ_[p]}
    (hx : ‖x-1‖ < 1) (hy : ‖y-1‖ < 1) : ‖x*y-1‖ < 1 := by
  have hxn : ‖x‖ = 1 := by
    simpa using Padic.norm_eq_of_norm_sub_lt_right (z1 := x) (z2 := 1) (by simpa using hx)
  have he : x*y-1 = x*(y-1)+(x-1) := by ring
  rw [he]
  apply (Padic.nonarchimedean _ _).trans_lt
  rw [max_lt_iff, norm_mul, hxn, one_mul]
  exact ⟨hy, hx⟩

/-- The key strict estimate: an integer between zero and `p^f` cannot
be divisible by `p^f`. No assertion that it is a `p`-adic unit is used. -/
private theorem norm_pow_lt_norm_nat {p : ℕ} [Fact p.Prime]
    (f t : ℕ) (ht : 0 < t) (htq : t < p^f) :
    ‖((p:ℚ_[p])^f)‖ < ‖(t:ℚ_[p])‖ := by
  by_contra hn
  have he : ‖((p:ℚ_[p])^f)‖ = (p:ℝ)^(-(f:ℤ)) := by
    rw [norm_pow, Padic.norm_p]
    simp [zpow_neg, zpow_natCast, inv_pow]
  have hd : (p^f:ℤ) ∣ (t:ℤ) :=
    (Padic.norm_int_le_pow_iff_dvd (p := p) t f).mp (by
      simpa only [Int.cast_natCast, ← he] using le_of_not_gt hn)
  have hd' : p^f ∣ t := by exact_mod_cast hd
  have := Nat.le_of_dvd ht hd'
  omega

private theorem increment_principal {p : ℕ} [Fact p.Prime]
    (f t j : ℕ) (ht : 0 < t) (htq : t < p^f) :
    ‖((t:ℚ_[p])+j*(p:ℚ_[p])^f)/(t:ℚ_[p])-1‖ < 1 := by
  have ht0 : (t:ℚ_[p]) ≠ 0 := by exact_mod_cast ht.ne'
  have he : ((t:ℚ_[p])+j*(p:ℚ_[p])^f)/(t:ℚ_[p])-1 =
      (j:ℚ_[p])*(p:ℚ_[p])^f/(t:ℚ_[p]) := by field_simp; ring
  rw [he, norm_div, div_lt_one (norm_pos_iff.mpr ht0), norm_mul]
  apply lt_of_le_of_lt _ (norm_pow_lt_norm_nat f t ht htq)
  exact mul_le_of_le_one_left (norm_nonneg _) (by
    simpa using Padic.norm_int_le_one (p := p) (j:ℤ))

private def factorialRatio (p ell h a : ℕ) [Fact p.Prime] : ℚ_[p] :=
  (ell:ℚ_[p])^a * (∏ j ∈ range ell, ((primitiveDigit ell h a j).factorial:ℚ_[p])) /
    ((a.factorial:ℚ_[p]) * ∏ j ∈ range ell, ((j*h).factorial:ℚ_[p]))

private theorem factorialRatio_zero (p ell h : ℕ) [Fact p.Prime] :
    factorialRatio p ell h 0 = 1 := by
  have he : ∀ j ∈ range ell, primitiveDigit ell h 0 j = j*h := by
    intro j hj
    simp [primitiveDigit, Nat.div_eq_of_lt (mem_range.mp hj)]
  unfold factorialRatio
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
  rw [prod_congr rfl (fun j hj ↦ by rw [he j hj])]
  apply div_self
  exact prod_ne_zero_iff.mpr (fun j _ ↦ by exact_mod_cast Nat.factorial_ne_zero (j*h))

private theorem factorialRatio_succ (p ell h a : ℕ) [Fact p.Prime] (hl : 0 < ell) :
    factorialRatio p ell h (a+1) = factorialRatio p ell h a *
      (((a+1:ℕ):ℚ_[p]) + (ell-1-a%ell:ℕ)*(ell*h+1:ℕ)) / ((a+1:ℕ):ℚ_[p]) := by
  have hcoef : (ell:ℚ_[p]) * ((primitiveDigit ell h a (ell-1-a%ell)+1:ℕ):ℚ_[p]) =
      ((a+1:ℕ):ℚ_[p]) + ((ell-1-a%ell:ℕ):ℚ_[p])*((ell*h+1:ℕ):ℚ_[p]) := by
    exact_mod_cast increment_coefficient ell h a hl
  have hprod : (∏ j ∈ range ell, ((primitiveDigit ell h (a+1) j).factorial:ℚ_[p])) =
      ((primitiveDigit ell h a (ell-1-a%ell)+1:ℕ):ℚ_[p]) *
        ∏ j ∈ range ell, ((primitiveDigit ell h a j).factorial:ℚ_[p]) := by
    exact_mod_cast factorial_increment ell h a hl
  unfold factorialRatio
  rw [hprod, pow_succ, Nat.factorial_succ, Nat.cast_mul]
  rw [← hcoef]
  ring

/-- (O:F:factorials) in the rational `p`-adic field: the ratio lies in
`1 + maximalIdeal`. The `j=0` factor in the lower product is `0! = 1`.
This holds even when the factorials have positive `p`-valuation. -/
theorem primitiveExponent_factorialUnit (p f ell h a : ℕ) [Fact p.Prime]
    (hl : 0 < ell) (hq : ell*h+1 = p^f) (ha : a < p^f) :
    ‖(ell:ℚ_[p])^a * (∏ j ∈ range ell, ((primitiveDigit ell h a j).factorial:ℚ_[p])) /
      ((a.factorial:ℚ_[p]) * ∏ j ∈ range ell, ((j*h).factorial:ℚ_[p])) - 1‖ < 1 := by
  change ‖factorialRatio p ell h a - 1‖ < 1
  induction a with
  | zero => rw [factorialRatio_zero p ell h]; simp
  | succ a ih =>
    rw [factorialRatio_succ p ell h a hl, mul_div_assoc]
    apply principal_mul (ih (by omega))
    have hc : ((ell*h+1:ℕ):ℚ_[p]) = (p:ℚ_[p])^f := by exact_mod_cast hq
    rw [hc]
    exact increment_principal f (a+1) (ell-1-a%ell) (by omega) ha

/-- The factorial congruence with the actual base-`q` digit factorial, ready
for the grouped leading Gauss congruence (O:F:groupedStick). -/
theorem primitiveExponent_factorialUnit_digits (p f ell h a : ℕ) [Fact p.Prime]
    (hl : ell.Prime) (hq : ell*h+1 = p^f) (ha : a < p^f) (hprim : ¬ ell ∣ a) :
    ‖(ell:ℚ_[p])^a *
        (Gauss.gaussDigitFactorial (p^f) ell (primitiveExponent (p^f) ell a):ℚ_[p]) /
      ((a.factorial:ℚ_[p]) * ∏ j ∈ range ell, ((j*h).factorial:ℚ_[p])) - 1‖ < 1 := by
  have he := primitiveExponent_digitFactorial ell h a hl (hq ▸ ha) hprim
  rw [hq] at he
  rw [he, Nat.cast_prod]
  exact primitiveExponent_factorialUnit p f ell h a hl.pos hq ha

end

end LanglandsSecondMainLemma.Tame
