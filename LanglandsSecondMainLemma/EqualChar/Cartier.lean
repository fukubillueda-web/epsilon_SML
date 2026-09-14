import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsSecondMainLemma.Residues.Substitution

/-!
# The Cartier operator in equal characteristic two

For a perfect coefficient field of characteristic two, this file defines the
Cartier operator on formal Laurent differentials by

`Cartier (∑ a n X^n dX) = ∑ sqrt (a (2m+1)) X^m dX`.

It proves the three identities collected in (D:EQ:Cartier) of the corrected
manuscript, as well as the stated extension from `dX / X` to `du / u` for every
nonzero Laurent series `u`.
-/

open scoped PowerSeries LaurentSeries
open HahnSeries

namespace LanglandsSecondMainLemma.EqualChar

noncomputable section

variable {k : Type*} [Field k] [Finite k] [CharP k 2]

local instance : Algebra (ZMod 2) k := ZMod.algebra k 2

/-- The unique square root in a finite field of characteristic two. -/
private def squareRoot (a : k) : k :=
  (frobeniusEquiv k 2).symm a

@[simp] private lemma squareRoot_sq (a : k) : squareRoot a ^ 2 = a := by
  exact (frobeniusEquiv k 2).apply_symm_apply a

@[simp] private lemma squareRoot_zero : squareRoot (0 : k) = 0 := by
  exact (frobeniusEquiv k 2).symm.map_zero

private lemma squareRoot_ne_zero {a : k} (ha : a ≠ 0) : squareRoot a ≠ 0 := by
  simpa [squareRoot] using (frobeniusEquiv k 2).symm.injective.ne ha

private lemma squareRoot_add (a b : k) :
    squareRoot (a + b) = squareRoot a + squareRoot b := by
  exact (frobeniusEquiv k 2).symm.map_add a b

/-- The Cartier operator on Laurent differentials, defined coefficientwise.
The differential basis `dX` is implicit in the Laurent series representing a
formal differential. -/
def cartier (η : Residues.FormalDifferential k) : Residues.FormalDifferential k :=
  HahnSeries.ofSuppBddBelow
    (fun m : ℤ ↦ squareRoot (η.coeff (2 * m + 1))) <| by
      refine ⟨min 0 η.order, ?_⟩
      intro m hm
      simp only [Function.mem_support] at hm
      have hcoeff : η.coeff (2 * m + 1) ≠ 0 := by
        intro hzero
        exact hm (by simp [hzero])
      have horder : η.order ≤ 2 * m + 1 :=
        HahnSeries.order_le_of_coeff_ne_zero hcoeff
      omega

@[simp] private lemma coeff_cartier (η : Residues.FormalDifferential k) (m : ℤ) :
    (cartier η).coeff m = squareRoot (η.coeff (2 * m + 1)) :=
  rfl

/-- Squaring the coefficient selected by Cartier returns the corresponding
odd coefficient of the original differential. -/
private lemma coeff_cartier_sq (η : Residues.FormalDifferential k) (m : ℤ) :
    (cartier η).coeff m ^ 2 = η.coeff (2 * m + 1) := by
  simp

private lemma cartier_add (η ω : Residues.FormalDifferential k) :
    cartier (η + ω) = cartier η + cartier ω := by
  ext m
  simp only [coeff_cartier, HahnSeries.coeff_add, squareRoot_add]

private lemma trace_squareRoot (a : k) :
    Algebra.trace (ZMod 2) k (squareRoot a) =
      Algebra.trace (ZMod 2) k a := by
  let σ : k ≃ₐ[ZMod 2] k :=
    FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) k
  have htrace := Algebra.trace_eq_of_algEquiv σ (squareRoot a)
  have happ : σ (squareRoot a) = a := by
    change squareRoot a ^ 2 = a
    exact squareRoot_sq a
  rw [happ] at htrace
  exact htrace.symm

/-- Absolute trace of the residue is invariant under Cartier.  This is the
third identity in (D:EQ:Cartier). -/
theorem cartier_residueTrace (η : Residues.FormalDifferential k) :
    Algebra.trace (ZMod 2) k (Residues.residue (cartier η)) =
      Algebra.trace (ZMod 2) k (Residues.residue η) := by
  rw [show Residues.residue (cartier η) = squareRoot (Residues.residue η) by
    simp [Residues.residue]]
  exact trace_squareRoot _

omit [Finite k] in
private lemma coeff_sq_odd (f : k⸨X⸩) (m : ℤ) :
    (f ^ 2).coeff (2 * m + 1) = 0 := by
  rw [pow_two, HahnSeries.coeff_mul]
  refine Finset.sum_involution (fun ij _ ↦ ij.swap) ?_ ?_
    (fun ij hij ↦ Finset.swap_mem_antidiagonal.mpr hij)
    (fun ij _ ↦ Prod.swap_swap ij)
  · intro ij hij
    change f.coeff ij.1 * f.coeff ij.2 + f.coeff ij.2 * f.coeff ij.1 = 0
    rw [mul_comm (f.coeff ij.2)]
    exact CharTwo.add_self_eq_zero _
  · intro ij hij _hterm hfixed
    have hsum : ij.1 + ij.2 = 2 * m + 1 :=
      (Finset.mem_antidiagonal.mp hij).2.2
    have heq : ij.1 = ij.2 := by
      exact (congrArg Prod.fst hfixed).symm
    rw [heq] at hsum
    omega

omit [Finite k] in
private lemma coeff_sq_even (f : k⸨X⸩) (m : ℤ) :
    (f ^ 2).coeff (2 * m) = f.coeff m ^ 2 := by
  rw [pow_two, HahnSeries.coeff_mul]
  let s := Finset.antidiagonal f.isPWO_support f.isPWO_support (2 * m)
  let d : ℤ × ℤ := (m, m)
  let term : ℤ × ℤ → k := fun ij ↦ f.coeff ij.1 * f.coeff ij.2
  change ∑ ij ∈ s, term ij = f.coeff m ^ 2
  by_cases hfm : f.coeff m = 0
  · have hsum : ∑ ij ∈ s, term ij = 0 := by
      refine Finset.sum_involution (fun ij _ ↦ ij.swap) ?_ ?_
        (fun ij hij ↦ Finset.swap_mem_antidiagonal.mpr hij)
        (fun ij _ ↦ Prod.swap_swap ij)
      · intro ij hij
        change f.coeff ij.1 * f.coeff ij.2 +
          f.coeff ij.2 * f.coeff ij.1 = 0
        rw [mul_comm (f.coeff ij.2)]
        exact CharTwo.add_self_eq_zero _
      · intro ij hij hterm hfixed
        have hsumIndex : ij.1 + ij.2 = 2 * m :=
          (Finset.mem_antidiagonal.mp hij).2.2
        have heq : ij.1 = ij.2 := (congrArg Prod.fst hfixed).symm
        have him : ij.1 = m := by rw [heq] at hsumIndex; omega
        apply hterm
        simp [term, him, hfm]
    simpa [hfm] using hsum
  · have hd : d ∈ s := by
      apply Finset.mem_antidiagonal.mpr
      refine ⟨HahnSeries.mem_support f m |>.mpr hfm,
        HahnSeries.mem_support f m |>.mpr hfm, ?_⟩
      simp [d]
      omega
    have herase : ∑ ij ∈ s.erase d, term ij = 0 := by
      refine Finset.sum_involution (fun ij _ ↦ ij.swap) ?_ ?_ ?_
        (fun ij _ ↦ Prod.swap_swap ij)
      · intro ij hij
        change f.coeff ij.1 * f.coeff ij.2 +
          f.coeff ij.2 * f.coeff ij.1 = 0
        rw [mul_comm (f.coeff ij.2)]
        exact CharTwo.add_self_eq_zero _
      · intro ij hij _hterm hfixed
        have hijs : ij ∈ s := (Finset.mem_erase.mp hij).2
        have hsumIndex : ij.1 + ij.2 = 2 * m :=
          (Finset.mem_antidiagonal.mp hijs).2.2
        have heq : ij.1 = ij.2 := (congrArg Prod.fst hfixed).symm
        have him : ij.1 = m := by rw [heq] at hsumIndex; omega
        apply (Finset.mem_erase.mp hij).1
        apply Prod.ext
        · exact him
        · simpa [heq] using him
      · intro ij hij
        apply Finset.mem_erase.mpr
        refine ⟨?_, Finset.swap_mem_antidiagonal.mpr (Finset.mem_erase.mp hij).2⟩
        intro hswap
        apply (Finset.mem_erase.mp hij).1
        calc
          ij = ij.swap.swap := (Prod.swap_swap ij).symm
          _ = d.swap := congrArg Prod.swap hswap
          _ = d := by simp [d]
    rw [← Finset.add_sum_erase s term hd, herase, add_zero]
    simp [term, d, pow_two]

/-- Cartier is Frobenius-semilinear: a squared Laurent coefficient can be
pulled through the operator with one power removed.  This is the first
identity in (D:EQ:Cartier). -/
theorem cartier_square_mul (f : k⸨X⸩) (η : Residues.FormalDifferential k) :
    cartier (f ^ 2 * η) = f * cartier η := by
  ext m
  apply CharTwo.sq_injective
  change (cartier (f ^ 2 * η)).coeff m ^ 2 = (f * cartier η).coeff m ^ 2
  rw [coeff_cartier_sq]
  have hright :
      (f * cartier η).coeff m ^ 2 =
        ∑ ij ∈ Finset.antidiagonal f.isPWO_support (cartier η).isPWO_support m,
          f.coeff ij.1 ^ 2 * η.coeff (2 * ij.2 + 1) := by
    rw [HahnSeries.coeff_mul, CharTwo.sum_sq]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [mul_pow, coeff_cartier_sq]
  rw [hright, HahnSeries.coeff_mul]
  symm
  let s := Finset.antidiagonal f.isPWO_support (cartier η).isPWO_support m
  let t := Finset.antidiagonal (f ^ 2).isPWO_support η.isPWO_support (2 * m + 1)
  change (∑ ij ∈ s, f.coeff ij.1 ^ 2 * η.coeff (2 * ij.2 + 1)) =
    ∑ ij ∈ t, (f ^ 2).coeff ij.1 * η.coeff ij.2
  refine Finset.sum_bij (fun ij _ ↦ (2 * ij.1, 2 * ij.2 + 1)) ?_ ?_ ?_ ?_
  · intro ij hij
    have hs := Finset.mem_antidiagonal.mp hij
    apply Finset.mem_antidiagonal.mpr
    refine ⟨?_, ?_, ?_⟩
    · apply HahnSeries.mem_support (f ^ 2) (2 * ij.1) |>.mpr
      rw [coeff_sq_even]
      exact pow_ne_zero 2 (HahnSeries.mem_support f ij.1 |>.mp hs.1)
    · apply HahnSeries.mem_support η (2 * ij.2 + 1) |>.mpr
      have hc := HahnSeries.mem_support (cartier η) ij.2 |>.mp hs.2.1
      exact fun hzero ↦ hc (by simp [hzero])
    · omega
  · intro a ha b hb hab
    apply Prod.ext
    · have h := congrArg Prod.fst hab
      dsimp only at h
      omega
    · have h := congrArg Prod.snd hab
      dsimp only at h
      omega
  · intro b hb
    have ht := Finset.mem_antidiagonal.mp hb
    rcases Int.even_or_odd' b.1 with ⟨r, hr | hr⟩
    · let q : ℤ := m - r
      have hb2 : b.2 = 2 * q + 1 := by
        dsimp only [q]
        omega
      let a : ℤ × ℤ := (r, q)
      have ha : a ∈ s := by
        apply Finset.mem_antidiagonal.mpr
        refine ⟨?_, ?_, ?_⟩
        · apply HahnSeries.mem_support f r |>.mpr
          have hsq := HahnSeries.mem_support (f ^ 2) b.1 |>.mp ht.1
          rw [hr, coeff_sq_even] at hsq
          exact fun hzero ↦ hsq (by simp [hzero])
        · apply HahnSeries.mem_support (cartier η) q |>.mpr
          apply squareRoot_ne_zero
          simpa [hb2] using HahnSeries.mem_support η b.2 |>.mp ht.2.1
        · dsimp only [a, q]
          omega
      refine ⟨a, ha, ?_⟩
      apply Prod.ext
      · simpa [a] using hr.symm
      · simpa [a] using hb2.symm
    · have hsq := HahnSeries.mem_support (f ^ 2) b.1 |>.mp ht.1
      rw [hr, coeff_sq_odd] at hsq
      exact (hsq rfl).elim
  · intro ij hij
    rw [coeff_sq_even]

private lemma cartier_eq_self_of_derivative_eq_sq (q : k⸨X⸩)
    (hq : LaurentSeries.derivative k q = q ^ 2) : cartier q = q := by
  ext m
  apply CharTwo.sq_injective
  change (cartier q).coeff m ^ 2 = q.coeff m ^ 2
  rw [coeff_cartier_sq]
  have hc := congrArg (fun x : k⸨X⸩ ↦ x.coeff (2 * m)) hq
  simp only [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
    Ring.choose_one_right] at hc
  norm_num at hc
  rw [CharTwo.two_eq_zero, zero_mul, zero_add, one_mul] at hc
  rw [coeff_sq_even] at hc
  exact hc

omit [Finite k] [CharP k 2] in
private lemma laurentDerivative_coe (p : k⟦X⟧) :
    LaurentSeries.derivative k (p : k⸨X⸩) =
      (PowerSeries.derivative k p : k⸨X⸩) := by
  ext i
  cases i with
  | ofNat n =>
      simp only [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
        Ring.choose_one_right]
      norm_num
      rw [PowerSeries.coeff_coe, if_neg (by omega)]
      have habs : (n + 1 : ℤ).natAbs = n + 1 := by omega
      rw [habs]
      simp [PowerSeries.coeff_derivative, mul_comm]
  | negSucc n =>
      cases n with
      | zero =>
          simp [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
            PowerSeries.coeff_coe]
      | succ n =>
          simp only [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
            Ring.choose_one_right]
          norm_num
          rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe,
            if_pos (by omega), if_pos (by omega)]
          simp

omit [Finite k] in
private lemma powerSeries_derivative_derivative (p : k⟦X⟧) :
    PowerSeries.derivative k (PowerSeries.derivative k p) = 0 := by
  ext n
  simp only [PowerSeries.coeff_derivative, map_zero]
  rw [mul_assoc]
  suffices (((n + 1 : ℕ) : k) + 1) * ((n : k) + 1) = 0 by
    rw [this, mul_zero]
  rcases Nat.even_or_odd' n with ⟨r, hr | hr⟩
  · have heven : (((n + 1 : ℕ) : k) + 1) = 0 := by
      rw [hr]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      rw [CharTwo.two_eq_zero]
      simp only [zero_mul, zero_add]
      norm_num
      exact CharTwo.two_eq_zero
    rw [heven, zero_mul]
  · have heven : ((n : k) + 1) = 0 := by
      rw [hr]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      rw [CharTwo.two_eq_zero]
      simp only [zero_mul, zero_add]
      norm_num
      exact CharTwo.two_eq_zero
    rw [heven, mul_zero]

omit [Finite k] in
private lemma powerSeries_dlog_derivative_eq_sq (p : k⟦X⟧) :
    PowerSeries.derivative k (p⁻¹ * PowerSeries.derivative k p) =
      (p⁻¹ * PowerSeries.derivative k p) ^ 2 := by
  rw [Derivation.leibniz, PowerSeries.derivative_inv',
    powerSeries_derivative_derivative]
  simp only [smul_eq_mul, mul_zero]
  have hneg (x : k⟦X⟧) : -x = x := by
    ext i
    simp only [map_neg, CharTwo.neg_eq]
  rw [hneg]
  ring

private lemma cartier_powerSeries_dlog (p : k⟦X⟧) :
    cartier ((p⁻¹ * PowerSeries.derivative k p : k⟦X⟧) : k⸨X⸩) =
      (p⁻¹ * PowerSeries.derivative k p : k⟦X⟧) := by
  apply cartier_eq_self_of_derivative_eq_sq
  rw [laurentDerivative_coe, powerSeries_dlog_derivative_eq_sq]
  exact map_pow (HahnSeries.ofPowerSeries ℤ k)
    (p⁻¹ * PowerSeries.derivative k p) 2

omit [Finite k] [CharP k 2] in
private lemma derivative_single_mul_coe (n : ℤ) (p : k⟦X⟧) :
    LaurentSeries.derivative k
        (HahnSeries.single n 1 * (p : k⸨X⸩)) =
      HahnSeries.single (n - 1) (n : k) * (p : k⸨X⸩) +
        HahnSeries.single n 1 * (PowerSeries.derivative k p : k⸨X⸩) := by
  ext i
  simp only [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
    Ring.choose_one_right]
  norm_num
  rw [HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul,
    HahnSeries.coeff_single_mul]
  simp only [one_mul]
  let j : ℤ := i - n
  have hindex0 : i - n = j := rfl
  have hindex1 : i + 1 - n = j + 1 := by dsimp only [j]; omega
  have hindex2 : i - (n - 1) = j + 1 := by dsimp only [j]; omega
  have hi : i = n + j := by dsimp only [j]; omega
  rw [hindex0, hindex1, hindex2, hi]
  cases j with
  | ofNat q =>
      simp only [Int.ofNat_eq_natCast]
      simp only [PowerSeries.coeff_coe]
      have hnonneg1 : ¬((q : ℤ) + 1 < 0) := by omega
      have hnonneg0 : ¬((q : ℤ) < 0) := by omega
      rw [if_neg hnonneg1, if_neg hnonneg0]
      have habs1 : ((q : ℤ) + 1).natAbs = q + 1 := by omega
      have habs0 : (q : ℤ).natAbs = q := by omega
      rw [habs1, habs0, PowerSeries.coeff_derivative]
      norm_num
      ring
  | negSucc q =>
      cases q with
      | zero =>
          simp [PowerSeries.coeff_coe]
      | succ q =>
          simp only [PowerSeries.coeff_coe]
          have hneg1 : Int.negSucc (q + 1) + 1 < 0 := by omega
          have hneg0 : Int.negSucc (q + 1) < 0 := by omega
          simp only [if_pos hneg1, if_pos hneg0]
          simp

private lemma cartier_single_neg_one (c : k) (hc : c ^ 2 = c) :
    cartier (HahnSeries.single (-1 : ℤ) c) =
      HahnSeries.single (-1 : ℤ) c := by
  ext m
  apply CharTwo.sq_injective
  change (cartier (HahnSeries.single (-1 : ℤ) c)).coeff m ^ 2 =
    (HahnSeries.single (-1 : ℤ) c).coeff m ^ 2
  rw [coeff_cartier_sq]
  by_cases hm : m = -1
  · subst m
    simp only [HahnSeries.coeff_single_same]
    norm_num
    exact hc.symm
  · have hindex : 2 * m + 1 ≠ -1 := by omega
    rw [HahnSeries.coeff_single_of_ne hindex,
      HahnSeries.coeff_single_of_ne hm]
    simp

/-- The Cartier operator fixes the logarithmic differential of every nonzero Laurent
series.  This is the coefficient form of `Cart(du/u) = du/u` in (4.2.1). -/
theorem cartier_dlog (u : k⸨X⸩) (hu : u ≠ 0) :
    cartier (u⁻¹ * LaurentSeries.derivative k u) =
      u⁻¹ * LaurentSeries.derivative k u := by
  let n : ℤ := u.order
  let p : k⟦X⟧ := u.powerSeriesPart
  let q : k⟦X⟧ := p⁻¹ * PowerSeries.derivative k p
  have hp : PowerSeries.constantCoeff p ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    dsimp only [p]
    rw [LaurentSeries.powerSeriesPart_coeff]
    simpa using HahnSeries.coeff_order_eq_zero.not.mpr hu
  have hpq : p * q = PowerSeries.derivative k p := by
    calc
      p * q = (p⁻¹ * p) * PowerSeries.derivative k p := by
        dsimp only [q]
        ring
      _ = PowerSeries.derivative k p := by
        rw [PowerSeries.inv_mul_cancel p hp, one_mul]
  have hfactor : HahnSeries.single n 1 * (p : k⸨X⸩) = u := by
    exact LaurentSeries.single_order_mul_powerSeriesPart u
  have hDu : LaurentSeries.derivative k u =
      HahnSeries.single (n - 1) (n : k) * (p : k⸨X⸩) +
        HahnSeries.single n 1 * (PowerSeries.derivative k p : k⸨X⸩) := by
    rw [← hfactor]
    exact derivative_single_mul_coe n p
  have hfirst : u * HahnSeries.single (-1 : ℤ) (n : k) =
      HahnSeries.single (n - 1) (n : k) * (p : k⸨X⸩) := by
    rw [← hfactor]
    have hs : HahnSeries.single n (1 : k) *
        HahnSeries.single (-1 : ℤ) (n : k) =
          HahnSeries.single (n - 1) (n : k) := by
      rw [HahnSeries.single_mul_single]
      simp only [one_mul, sub_eq_add_neg]
    calc
      (HahnSeries.single n 1 * (p : k⸨X⸩)) *
          HahnSeries.single (-1 : ℤ) (n : k) =
        (HahnSeries.single n 1 * HahnSeries.single (-1 : ℤ) (n : k)) *
          (p : k⸨X⸩) := by ring
      _ = HahnSeries.single (n - 1) (n : k) * (p : k⸨X⸩) := by rw [hs]
  have hsecond : u * (q : k⸨X⸩) =
      HahnSeries.single n 1 * (PowerSeries.derivative k p : k⸨X⸩) := by
    rw [← hfactor, mul_assoc, ← map_mul, hpq]
  have hlog : u⁻¹ * LaurentSeries.derivative k u =
      HahnSeries.single (-1 : ℤ) (n : k) + (q : k⸨X⸩) := by
    apply mul_left_cancel₀ hu
    rw [← mul_assoc, mul_inv_cancel₀ hu, one_mul, mul_add, hfirst, hsecond, hDu]
  have hn_sq : (n : k) ^ 2 = (n : k) := by
    change frobenius k 2 (n : k) = (n : k)
    exact map_intCast (frobenius k 2) n
  rw [hlog, cartier_add, cartier_single_neg_one (n : k) hn_sq]
  change HahnSeries.single (-1 : ℤ) (n : k) +
      cartier ((p⁻¹ * PowerSeries.derivative k p : k⟦X⟧) : k⸨X⸩) = _
  rw [cartier_powerSeries_dlog]

end

end LanglandsSecondMainLemma.EqualChar
