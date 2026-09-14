import LanglandsSecondMainLemma.Gauss.FirstCoefficient
import LanglandsSecondMainLemma.Gauss.JacobiProduct
import Mathlib.Data.Nat.Factorial.NatCast

/-!
# The complete leading coefficient of the Gauss sum

Appendix A.3 (`A:leading-gauss`) of `epsilon_SML.tex`.  All sums use the
chosen coefficient field and its actual Teichmuller and trace characters.
-/

open scoped BigOperators
open Finset

namespace LanglandsSecondMainLemma.Gauss

noncomputable section

private theorem basePDigit_succ (p a i : ℕ) :
    basePDigit p a (i + 1) = basePDigit p (a / p) i := by
  simp [basePDigit, pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

/-- Remove one nonzero digit without borrowing in any other position. -/
private theorem remove_digit (p : ℕ) (hp : 1 < p) {f a : ℕ} (ha : 0 < a) (haf : a < p ^ f) :
    ∃ c j, j < f ∧ a = c + p ^ j ∧
      ∀ i, basePDigit p c i + (if i = j then 1 else 0) = basePDigit p a i := by
  induction f generalizing a with
  | zero => simp at haf; omega
  | succ f ih =>
    have hr := Nat.mod_lt a (by omega : 0 < p)
    have hsplit := Nat.mod_add_div a p
    by_cases hrem : a % p = 0
    · have had : 0 < a / p := by nlinarith
      have hadf : a / p < p ^ f := by
        rw [Nat.div_lt_iff_lt_mul (by omega : 0 < p)]
        simpa [pow_succ] using haf
      obtain ⟨c, j, hj, hcj, hd⟩ := ih had hadf
      refine ⟨p * c, j + 1, by omega, ?_, ?_⟩
      · rw [pow_succ]
        nlinarith
      · intro i
        cases i with
        | zero => simp [basePDigit, hrem]
        | succ i =>
          simpa [basePDigit_succ, Nat.mul_div_right _ (by omega : 0 < p)] using hd i
    · refine ⟨a - 1,0, by omega, by simp; omega, ?_⟩
      have hrepr : a - 1 = (a % p - 1) + p * (a / p) := by omega
      have hc : (a - 1) / p = a / p := by
        rw [hrepr, Nat.add_mul_div_left _ _ (by omega : 0 < p),
          Nat.div_eq_of_lt (by omega), zero_add]
      have hcr : (a - 1) % p + 1 = a % p := by
        rw [hrepr, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
        omega
      intro i
      cases i with
      | zero => simpa [basePDigit] using hcr
      | succ i => simp [basePDigit_succ, hc]

private theorem basePDigit_pow (p : ℕ) (hp : 1 < p) (j i : ℕ) :
    basePDigit p (p ^ j) i = if i = j then 1 else 0 := by
  by_cases hij : i ≤ j
  · have hdiv : p ^ j / p ^ i = p ^ (j - i) := by
      conv_lhs => rw [show j = (j - i) + i by omega, pow_add]
      exact Nat.mul_div_left _ (pow_pos (by omega) _)
    rw [basePDigit, hdiv]
    by_cases he : i = j
    · simp [he, Nat.mod_eq_of_lt hp]
    · have hpos : 0 < j - i := by omega
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j - i ≠ 0)
      simp [he, hn, pow_succ]
  · have hji : j < i := by omega
    have hlt := Nat.pow_lt_pow_right hp hji
    simp [basePDigit, Nat.div_eq_of_lt hlt, show i ≠ j by omega]

/-- The digit sum of an index, with the manuscript's fixed `f` positions. -/
def gaussDigitSum (p f a : ℕ) : ℕ := ∑ i ∈ range f, basePDigit p a i

/-- The product of the digit factorials. -/
def gaussDigitFactorial (p f a : ℕ) : ℕ :=
  ∏ i ∈ range f, (basePDigit p a i).factorial

variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]

noncomputable local instance : Fintype k := Fintype.ofFinite k

/-- The nonzero-element sum of A.1 equals the character sum of A.2. -/
theorem coefficientGaussSum_eq_liftedGaussSum
    (C : GaussCoefficientField p k) (a : ℕ) (ha : 0 < a) :
    coefficientGaussSum p k C a = liftedGaussSum p k C a := by
  classical
  letI : IsDomain C.IntegerRing := C.coefficientDomain
  have hunits : multiplicativeResidueUnits k = univ := by
    ext x
    simp [multiplicativeResidueUnits]
  have hterm (x : kˣ) :
      inverseTeichmullerPowChar p k C a (x : k) =
        teichmuller_lift p k C ((x⁻¹ : kˣ) : k) ^ a := by
    rw [inverseTeichmullerPowChar, MulChar.pow_apply' _ ha.ne',
      MulChar.inv_apply_eq_inv, teichmullerMulChar_apply]
    congr 1
    let u := Units.map (teichmuller_lift p k C).toMonoidHom x
    change Ring.inverse (u : C.IntegerRing) = _
    rw [Ring.inverse_unit]
    rfl
  unfold liftedGaussSum gaussSum
  rw [Fintype.sum_eq_add_sum_subtype_ne _ 0]
  simp only [MulChar.map_zero, zero_mul, zero_add]
  rw [coefficientGaussSum, hunits]
  calc
    _ = ∑ x : kˣ, inverseTeichmullerPowChar p k C a (x : k) *
        cyclotomicTraceAddChar p k C (x : k) := by
      apply sum_congr rfl
      intro x _
      rw [hterm]
      rfl
    _ = _ := (Equiv.sum_comp unitsEquivNeZero
      (fun x : {x : k // x ≠ 0} ↦ inverseTeichmullerPowChar p k C a x *
        cyclotomicTraceAddChar p k C x))

private theorem digit_step {p f a c j : ℕ} (hj : j < f)
    (hd : ∀ i, basePDigit p c i + (if i = j then 1 else 0) = basePDigit p a i) :
    gaussDigitSum p f a = gaussDigitSum p f c + 1 ∧
      gaussDigitFactorial p f a =
        (basePDigit p c j + 1) * gaussDigitFactorial p f c := by
  constructor
  · simp only [gaussDigitSum, ← hd, sum_add_distrib]
    simp [hj]
  · unfold gaussDigitFactorial
    rw [prod_eq_mul_prod_sdiff_singleton j _ (by simp [hj]),
      prod_eq_mul_prod_sdiff_singleton j (fun i ↦ (basePDigit p c i).factorial)
        (by simp [hj])]
    rw [← hd j, if_pos rfl, Nat.factorial_succ]
    have hrest :
        (∏ i ∈ range f \ {j}, (basePDigit p a i).factorial) =
          ∏ i ∈ range f \ {j}, (basePDigit p c i).factorial := by
      apply prod_congr rfl
      intro i hi
      have hij : i ≠ j := by simpa using (mem_sdiff.mp hi).2
      rw [← hd i, if_neg hij, Nat.add_zero]
    rw [hrest, Nat.mul_assoc]

private theorem digit_pow_sum_factorial {p f j : ℕ} (hp : 1 < p) (hj : j < f) :
    gaussDigitSum p f (p ^ j) = 1 ∧ gaussDigitFactorial p f (p ^ j) = 1 := by
  simp [gaussDigitSum, gaussDigitFactorial, basePDigit_pow p hp, hj]
  intro i _
  split_ifs <;> omega

omit [Finite k] in
private theorem residue_uniformizer (C : GaussCoefficientField p k) :
    cyclotomicResidueMap p k C.unramified C.uniformizer = 0 := by
  unfold cyclotomicResidueMap GaussCoefficientField.uniformizer
  apply AdjoinRoot.lift_root

private theorem residue_kernel (C : GaussCoefficientField p k) :
    RingHom.ker (cyclotomicResidueMap p k C.unramified) =
      Ideal.span {C.uniformizer} := by
  letI : IsDomain C.IntegerRing := C.coefficientDomain
  letI : IsLocalRing C.IntegerRing := C.coefficientLocalRing
  rw [IsLocalRing.ker_eq_maximalIdeal _ (fun x ↦
    ⟨teichmuller_lift p k C x, teichmuller_lift_reduction p k C x⟩)]
  exact cyclotomicUniformizer p k C

private theorem isUnit_of_residue_ne_zero (C : GaussCoefficientField p k)
    {u : C.IntegerRing} (hu : cyclotomicResidueMap p k C.unramified u ≠ 0) :
    IsUnit u := by
  letI : IsDomain C.IntegerRing := C.coefficientDomain
  letI : IsLocalRing C.IntegerRing := C.coefficientLocalRing
  rw [← IsLocalRing.notMem_maximalIdeal, cyclotomicUniformizer p k C,
    ← residue_kernel p k C, RingHom.mem_ker]
  exact hu

omit [Finite k] in
private theorem factorial_residue_ne_zero (a : ℕ) :
    (gaussDigitFactorial p (Module.finrank (ZMod p) k) a : k) ≠ 0 := by
  letI : CharP k p := charP_of_injective_algebraMap
    (RingHom.injective (algebraMap (ZMod p) k)) p
  rw [gaussDigitFactorial, Nat.cast_prod]
  apply prod_ne_zero_iff.mpr
  intro i _
  apply IsUnit.ne_zero
  exact (IsUnit.natCast_factorial_iff_of_charP p).mpr
    (Nat.mod_lt _ (Fact.out : p.Prime).pos)

private theorem first_factor (C : GaussCoefficientField p k) (hq : 2 < Nat.card k) :
    ∃ u : C.IntegerRing, coefficientGaussSum p k C 1 = C.uniformizer * u ∧
      cyclotomicResidueMap p k C.unramified u = -1 := by
  have h := (firstCoefficient p k C).1 hq
  rw [SModEq.sub_mem, Ideal.mem_span_singleton] at h
  obtain ⟨t, ht⟩ := h
  refine ⟨-1 + C.uniformizer * t, ?_, ?_⟩
  · linear_combination ht
  · simp [map_add, map_neg, map_mul, residue_uniformizer]

/-- Induction on the digit sum keeps the normalized coefficient integral.
The only division is by the Jacobi unit proved in Appendix A.2. -/
private theorem leading_factor (C : GaussCoefficientField p k) {a : ℕ}
    (ha : 0 < a) (haq : a < Nat.card k - 1) :
    ∃ u : C.IntegerRing,
      coefficientGaussSum p k C a =
        C.uniformizer ^ gaussDigitSum p (Module.finrank (ZMod p) k) a * u ∧
      cyclotomicResidueMap p k C.unramified u *
        (gaussDigitFactorial p (Module.finrank (ZMod p) k) a : k) = -1 := by
  letI : IsDomain C.IntegerRing := C.coefficientDomain
  let f := Module.finrank (ZMod p) k
  let φ := cyclotomicResidueMap p k C.unramified
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hq : 2 < Nat.card k := by omega
  have haf : a < p ^ f := by
    rw [FiniteField.pow_finrank_eq_card p k, Fintype.card_eq_nat_card]
    omega
  induction hsum : gaussDigitSum p f a using Nat.strong_induction_on generalizing a with
  | h n ih =>
    rw [← hsum]
    obtain ⟨c, j, hj, hac, hd⟩ := remove_digit p hp ha haf
    have hpowpos : 0 < p ^ j := pow_pos (by omega) _
    have hpowq : p ^ j < Nat.card k - 1 := by omega
    obtain ⟨v, hv, hvred⟩ := first_factor p k C hq
    have hvj : coefficientGaussSum p k C (p ^ j) = C.uniformizer * v := by
      rw [(firstCoefficient p k C).2 j hj hpowq]
      exact hv
    have hs := digit_pow_sum_factorial hp hj
    by_cases hc : c = 0
    · have haeq : a = p ^ j := by simpa [hc] using hac
      refine ⟨v, ?_, ?_⟩
      · rw [haeq, hs.1, pow_one]
        exact hvj
      · rw [haeq, hs.2, Nat.cast_one, mul_one]
        exact hvred
    · have hcpos : 0 < c := by omega
      have hstep := digit_step hj hd
      obtain ⟨u, hu, hured⟩ := ih (gaussDigitSum p f c) (by omega)
        hcpos (by omega) (by omega) rfl
      have habq : c + p ^ j < Fintype.card k - 1 := by
        rw [← hac, Fintype.card_eq_nat_card]
        exact haq
      have hnc : ∀ i < f, basePDigit p c i + basePDigit p (p ^ j) i < p := by
        intro i _
        rw [basePDigit_pow p hp, hd]
        exact Nat.mod_lt _ (by omega)
      obtain ⟨hprod, hunit, hred⟩ := jacobiProduct p k C hcpos hpowpos habq hnc
      let J := liftedJacobiSum p k C c (p ^ j)
      have hJred : φ J = -(basePDigit p c j + 1 : ℕ) := by
        rw [hred]
        congr 1
        rw [prod_eq_single j]
        · rw [basePDigit_pow p hp, if_pos rfl, Nat.choose_succ_self_right]
        · intro i _ hij
          simp [basePDigit_pow p hp, hij]
        · exact fun hn ↦ (hn (mem_range.mpr hj)).elim
      have hJinv : φ (Ring.inverse J) * φ J = 1 := by
        rw [← map_mul, Ring.inverse_mul_cancel J hunit, map_one]
      refine ⟨Ring.inverse J * u * v, ?_, ?_⟩
      · have heq : J * coefficientGaussSum p k C a =
            coefficientGaussSum p k C c * coefficientGaussSum p k C (p ^ j) := by
          rw [coefficientGaussSum_eq_liftedGaussSum p k C a ha,
            coefficientGaussSum_eq_liftedGaussSum p k C c hcpos,
            coefficientGaussSum_eq_liftedGaussSum p k C (p ^ j) hpowpos,
            hac]
          exact hprod.symm
        apply (mul_right_injective₀ hunit.ne_zero)
        change J * coefficientGaussSum p k C a = J *
          (C.uniformizer ^ gaussDigitSum p f a * (Ring.inverse J * u * v))
        rw [heq, hu, hvj, hstep.1, pow_succ]
        calc
          _ = (J * Ring.inverse J) *
              (C.uniformizer ^ gaussDigitSum p f c * u * (C.uniformizer * v)) := by
                rw [Ring.mul_inverse_cancel J hunit, one_mul]
          _ = _ := by ring
      · change φ (Ring.inverse J * u * v) * _ = _
        rw [map_mul, map_mul, hvred, hstep.2, Nat.cast_mul]
        have hcancel : φ (Ring.inverse J) * (basePDigit p c j + 1 : ℕ) = -1 := by
          rw [hJred, mul_neg] at hJinv
          linear_combination -hJinv
        calc
          _ = -(φ (Ring.inverse J) * (basePDigit p c j + 1 : ℕ)) *
              (φ u * (gaussDigitFactorial p f c : k)) := by ring
          _ = -1 := by rw [hcancel, hured]; ring

/-- Appendix A.3, for every prime, including two.  The first congruence is
`G_a = -pi^s / a!_p` to precision `pi^(s + 1)`.  The two ideal statements
say that the uniformizer valuation is exactly `s`.  The final equality
is the multiplicative congruence for the manuscript's minus convention:
`-G_a = (pi^s / a!_p) * (1 + pi*t)` for an integral `t`.

`Ring.inverse` is division by a unit in the integer ring; the first
conjunct proves that the denominator is indeed a unit. -/
theorem leadingTerm (C : GaussCoefficientField p k) {a : ℕ}
    (ha : 0 < a) (haq : a < Nat.card k - 1) :
    let s := gaussDigitSum p (Module.finrank (ZMod p) k) a
    let A : C.IntegerRing := (gaussDigitFactorial p (Module.finrank (ZMod p) k) a : ℕ)
    IsUnit A ∧
      (coefficientGaussSum p k C a ≡ -(C.uniformizer ^ s * Ring.inverse A)
        [SMOD Ideal.span {C.uniformizer ^ (s + 1)}]) ∧
      coefficientGaussSum p k C a ∈ Ideal.span {C.uniformizer ^ s} ∧
      coefficientGaussSum p k C a ∉ Ideal.span {C.uniformizer ^ (s + 1)} ∧
      ∃ t : C.IntegerRing, -coefficientGaussSum p k C a =
        (C.uniformizer ^ s * Ring.inverse A) * (1 + C.uniformizer * t) := by
  letI : IsDomain C.IntegerRing := C.coefficientDomain
  letI : IsLocalRing C.IntegerRing := C.coefficientLocalRing
  letI : IsDiscreteValuationRing C.IntegerRing := C.coefficientDVR
  let s := gaussDigitSum p (Module.finrank (ZMod p) k) a
  let A : C.IntegerRing := (gaussDigitFactorial p (Module.finrank (ZMod p) k) a : ℕ)
  let φ := cyclotomicResidueMap p k C.unramified
  obtain ⟨u, hu, hured⟩ := leading_factor p k C ha haq
  have hAred : φ A = (gaussDigitFactorial p (Module.finrank (ZMod p) k) a : k) :=
    map_natCast φ _
  have hA : IsUnit A := isUnit_of_residue_ne_zero p k C
    (hAred ▸ factorial_residue_ne_zero p k a)
  have hu0 : φ u ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hured
    exact one_ne_zero (neg_eq_zero.mp hured.symm)
  have hpi0 : C.uniformizer ≠ 0 := (cyclotomicUniformizer_irreducible p k C).ne_zero
  have herror : -u * A - 1 ∈ Ideal.span {C.uniformizer} := by
    rw [← residue_kernel p k C, RingHom.mem_ker, map_sub, map_mul, map_neg, map_one]
    change -(φ u) * φ A - 1 = 0
    rw [hAred, neg_mul, hured]
    ring
  rw [Ideal.mem_span_singleton] at herror
  obtain ⟨t, ht⟩ := herror
  have hminus : -coefficientGaussSum p k C a =
      (C.uniformizer ^ s * Ring.inverse A) * (1 + C.uniformizer * t) := by
    have hcancel := Ring.inverse_mul_cancel A hA
    rw [hu]
    calc
      _ = -(C.uniformizer ^ s * u) * (Ring.inverse A * A) := by
        rw [hcancel, mul_one]
      _ = (C.uniformizer ^ s * Ring.inverse A) * (-u * A) := by ring
      _ = _ := by rw [show -u * A = 1 + C.uniformizer * t by linear_combination ht]
  refine ⟨hA, ?_, ?_, ?_, t, hminus⟩
  · rw [SModEq.sub_mem, Ideal.mem_span_singleton]
    refine ⟨-(Ring.inverse A * t), ?_⟩
    change coefficientGaussSum p k C a - -(C.uniformizer ^ s * Ring.inverse A) = _
    rw [pow_succ]
    linear_combination -hminus
  · rw [Ideal.mem_span_singleton]
    exact ⟨u, hu⟩
  · rw [Ideal.mem_span_singleton]
    rintro ⟨b, hb⟩
    have hub : u = C.uniformizer * b := by
      apply mul_left_cancel₀ (pow_ne_zero s hpi0)
      calc
        C.uniformizer ^ s * u = coefficientGaussSum p k C a := hu.symm
        _ = C.uniformizer ^ (s + 1) * b := hb
        _ = C.uniformizer ^ s * (C.uniformizer * b) := by rw [pow_succ, mul_assoc]
    apply hu0
    rw [hub, map_mul, residue_uniformizer, zero_mul]

end
end LanglandsSecondMainLemma.Gauss
