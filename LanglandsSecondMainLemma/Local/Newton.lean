import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.LocalField.Lattices
import LanglandsFirstMainLemma.LocalField.MonogenicUniformizer
import LanglandsFirstMainLemma.LocalField.Valuation
import LanglandsSecondMainLemma.Basic.Fields
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.RingTheory.Henselian

/-!
# Local / Newton

This file proves the quantitative Hensel lifting statement in Paper D.1 (`D:newton`) for the
canonical valuation ring of an arbitrary nonarchimedean local field. The normalized additive
order is FML's `LanglandsFirstMainLemma.ord`, with values in `WithTop ℤ` and zero of order
`greatest`.

Mathlib's quantitative Newton theorem is specialized to `ℤ_p`. We instead reuse the general
adic-completeness proof of Hensel's lemma. For a nonzero residual, put `e = f(a)`, `d = f'(a)`,
and `q = e / d`. The explicitly rescaled field polynomial

`H(X) = f(a + q X) / e`

has integral coefficients, constant and linear coefficients equal to one, and all higher
coefficients in the maximal ideal. It therefore lifts from the residual root `-1`. The actual
root is `b = a + q z`; integrality of `z` gives the quantitative bound. The zero-residual case
is kept separate. Uniqueness is proved on the entire strict ball, rather than only among the
roots obtained from this coordinate.
-/

namespace LanglandsSecondMainLemma.Local

open Polynomial
open LanglandsFirstMainLemma
open scoped Ring ValuativeRel

noncomputable section

/- Mathlib's proof that adic completeness implies the Henselian property never uses monicity
inside its Newton construction. The public `HenselianRing.is_henselian` interface nevertheless
requires a monic polynomial. This local specialization is the same construction with that
unused interface hypothesis removed. -/
private theorem exists_root_of_simple_residual
    {R : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (f : R[X]) (a₀ : R)
    (h₁ : f.eval a₀ ∈ IsLocalRing.maximalIdeal R)
    (h₂ : IsUnit
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (f.derivative.eval a₀))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ IsLocalRing.maximalIdeal R := by
  classical
  let I := IsLocalRing.maximalIdeal R
  let f' := derivative f
  let c : ℕ → R := fun n ↦ Nat.recOn n a₀ fun _ b ↦ b - f.eval b * (f'.eval b)⁻¹ʳ
  have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * (f'.eval (c n))⁻¹ʳ := by
    intro n
    simp only [c]
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at h₁ ⊢
      exact (ih.eval f).trans h₁
  have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
    intro n
    haveI := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert! h₂ using 1
    exact SModEq.def.mp ((hc_mod n).eval _)
  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using! h₁
    | succ n ih =>
      rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
        add_neg_cancel_comm]
      rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
        Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
      swap
      · intro i
        rw [zero_mul]
      refine Ideal.add_mem _ ?_ ?_
      · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one,
          Finset.sum_singleton, taylor_coeff_zero, taylor_coeff_one, pow_zero, pow_one,
          mul_one, mul_neg, mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n), mul_one,
          add_neg_cancel]
        exact Ideal.zero_mem _
      · refine Submodule.sum_mem _ ?_
        simp only [Finset.mem_Ico]
        rintro i ⟨h2i, _⟩
        have aux : n + 2 ≤ i * (n + 1) := by
          trans 2 * (n + 1) <;> nlinarith only [h2i]
        refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
        rw [pow_mul']
        exact Ideal.pow_mem_pow
          ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => rw [add_zero]
    | succ k ih =>
      rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
      rw [add_assoc]
      exact le_self_add
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
  refine ⟨a, ?_, ?_⟩
  · show f.IsRoot a
    suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by
      exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)
  · specialize ha (0 + 1)
    rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one,
      sub_eq_add_neg] at ha
    rw [← SModEq.sub_mem, ← add_zero a₀]
    refine ha.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ h₁

private lemma scaled_coefficient_positive {s r : ℤ} (hs : 0 ≤ s) (hsr : 2 * s < r)
    {n : ℕ} (hn : 2 ≤ n) : 0 < (n : ℤ) * (r - s) - r := by
  have hn' : 0 ≤ (n : ℤ) - 2 := by omega
  have hrs : 0 ≤ r - s := by omega
  have hprod : 0 ≤ ((n : ℤ) - 2) * (r - s) := mul_nonneg hn' hrs
  nlinarith

private theorem unique_root_in_newton_ball
    {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (f : (ringOfIntegers F)[X]) (a : ringOfIntegers F) (s : ℤ)
    (hderiv : ord F ((f.derivative.eval a : ringOfIntegers F) : F) =
      (s : WithTop ℤ))
    {b c : ringOfIntegers F} (hb : f.IsRoot b) (hc : f.IsRoot c)
    (hbball : (s : WithTop ℤ) < ord F ((b : F) - (a : F)))
    (hcball : (s : WithTop ℤ) < ord F ((c : F) - (a : F))) : b = c := by
  let i : ringOfIntegers F →+* F := (ValuativeRel.valuation F).integer.subtype
  have hs : 0 ≤ s := by
    have hdint : (0 : WithTop ℤ) ≤
        ord F ((f.derivative.eval a : ringOfIntegers F) : F) :=
      (ord_nonneg_iff_mem_integer F _).2 (f.derivative.eval a).property
    rw [hderiv] at hdint
    exact WithTop.coe_nonneg.mp hdint
  have derivative_stable (x : ringOfIntegers F)
      (hx : (s : WithTop ℤ) < ord F ((x : F) - (a : F))) :
      ord F (i (f.derivative.eval x)) = (s : WithTop ℤ) := by
    obtain ⟨k, hk⟩ := f.derivative.evalSubFactor x a
    have hkF := congrArg i hk
    have hkord : 0 ≤ ord F (i k) :=
      (ord_nonneg_iff_mem_integer F _).2 k.property
    have hdiff : (s : WithTop ℤ) <
        ord F (i (f.derivative.eval x) - i (f.derivative.eval a)) := by
      rw [map_sub] at hkF
      rw [hkF, map_mul, ord_mul]
      exact hx.trans_le (le_add_of_nonneg_left hkord)
    calc
      ord F (i (f.derivative.eval x)) =
          ord F (i (f.derivative.eval a) +
            (i (f.derivative.eval x) - i (f.derivative.eval a))) := by
              congr 1
              ring
      _ = min (ord F (i (f.derivative.eval a)))
          (ord F (i (f.derivative.eval x) - i (f.derivative.eval a))) :=
        ord_add_eq_min F (by
          rw [show ord F (i (f.derivative.eval a)) = (s : WithTop ℤ) by
            simpa [i] using hderiv]
          exact ne_of_lt hdiff)
      _ = (s : WithTop ℤ) := by
        rw [show ord F (i (f.derivative.eval a)) = (s : WithTop ℤ) by
          simpa [i] using hderiv, min_eq_left hdiff.le]
  have hbcball : (s : WithTop ℤ) < ord F ((b : F) - (c : F)) := by
    have hmin : (s : WithTop ℤ) <
        min (ord F ((b : F) - (a : F))) (ord F ((c : F) - (a : F))) :=
      lt_min hbball hcball
    calc
      (s : WithTop ℤ) <
          min (ord F ((b : F) - (a : F))) (ord F ((c : F) - (a : F))) := hmin
      _ ≤ ord F (((b : F) - (a : F)) - ((c : F) - (a : F))) :=
        ord_sub F _ _
      _ = ord F ((b : F) - (c : F)) := by
        congr 1
        ring
  by_contra hne
  have hsubne : b - c ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨k, hk⟩ := Polynomial.exists_mul_sq_add_linear_part_eq_eval_add f c (b - c)
  have hkzero : k * (b - c) ^ 2 + f.derivative.eval c * (b - c) = 0 := by
    have hadd : c + (b - c) = b := by ring
    rw [hadd, hb, hc] at hk
    simpa only [add_zero] using hk
  have hprod : (k * (b - c) + f.derivative.eval c) * (b - c) = 0 := by
    calc
      _ = k * (b - c) ^ 2 + f.derivative.eval c * (b - c) := by ring
      _ = 0 := hkzero
  have hfactor : k * (b - c) + f.derivative.eval c = 0 :=
    (mul_eq_zero.mp hprod).resolve_right hsubne
  have hderivEq : f.derivative.eval c = -k * (b - c) := by
    linear_combination hfactor
  have hkord : 0 ≤ ord F (i k) :=
    (ord_nonneg_iff_mem_integer F _).2 k.property
  have hgt : (s : WithTop ℤ) < ord F (i (f.derivative.eval c)) := by
    have hderivEqF := congrArg i hderivEq
    simp only [map_neg, map_mul, map_sub] at hderivEqF
    rw [hderivEqF, ord_mul, ord_neg]
    exact hbcball.trans_le (le_add_of_nonneg_left hkord)
  exact (ne_of_gt hgt) (derivative_stable c hcball)

private theorem exists_quantitative_root_of_residual_ne_zero
    {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (f : (ringOfIntegers F)[X]) (a : ringOfIntegers F) (s r : ℤ)
    (hres0 : f.eval a ≠ 0)
    (hderiv : ord F ((f.derivative.eval a : ringOfIntegers F) : F) =
      (s : WithTop ℤ))
    (hres : ord F ((f.eval a : ringOfIntegers F) : F) = (r : WithTop ℤ))
    (hstrict : 2 * s < r) :
    ∃ b : ringOfIntegers F,
      f.IsRoot b ∧
      (s : WithTop ℤ) < ord F ((b : F) - (a : F)) ∧
      ord F ((f.eval a : ringOfIntegers F) : F) - (s : WithTop ℤ) ≤
        ord F ((b : F) - (a : F)) := by
  let i : ringOfIntegers F →+* F := (ValuativeRel.valuation F).integer.subtype
  let fF : F[X] := f.map i
  let aF : F := i a
  let e : F := i (f.eval a)
  let d : F := i (f.derivative.eval a)
  let q : F := e / d
  -- This is the fractional-coordinate rescaling from the paper, performed in the field.
  let H : F[X] := ((fF.taylor aF).comp (C q * X)) * C e⁻¹
  have hdord : ord F d = (s : WithTop ℤ) := by
    simpa [d, i] using hderiv
  have heord : ord F e = (r : WithTop ℤ) := by
    simpa [e, i] using hres
  have hfeval : fF.eval aF = e := by
    simp only [fF, aF, e, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  have hfderiv : fF.derivative.eval aF = d := by
    simp only [fF, aF, d, Polynomial.derivative_map, Polynomial.eval_map,
      Polynomial.eval₂_at_apply]
  have hd0 : d ≠ 0 := by
    apply (ord_ne_top_iff F).mp
    rw [hdord]
    exact WithTop.coe_ne_top
  have he0 : e ≠ 0 := by
    exact fun he => hres0 (Subtype.ext (by simpa [e, i] using he))
  have hs : 0 ≤ s := by
    have hdint : (0 : WithTop ℤ) ≤ ord F d :=
      (ord_nonneg_iff_mem_integer F d).2 (by simp [d, i])
    rw [hdord] at hdint
    exact WithTop.coe_nonneg.mp hdint
  have hq : ord F q = ((r - s : ℤ) : WithTop ℤ) := by
    change ord F (e / d) = _
    rw [ord_div, heord, hdord]
    exact (WithTop.LinearOrderedAddCommGroup.coe_sub r s).symm
  have hHzero : H.coeff 0 = 1 := by
    simp [H, hfeval, he0]
  have hHone : H.coeff 1 = 1 := by
    simp only [H, Polynomial.coeff_mul_C, Polynomial.comp_C_mul_X_coeff,
      pow_one, Polynomial.taylor_coeff_one, hfderiv, q]
    field_simp
  have hHcoeffPos (n : ℕ) (hn : 2 ≤ n) : 0 < ord F (H.coeff n) := by
    have htaylor : 0 ≤ ord F ((fF.taylor aF).coeff n) := by
      have hmap : fF.taylor aF = (f.taylor a).map i := by
        simp [fF, aF, Polynomial.map_taylor]
      rw [hmap, Polynomial.coeff_map]
      exact (ord_nonneg_iff_mem_integer F _).2
        (by simp [i])
    simp only [H, Polynomial.coeff_mul_C, Polynomial.comp_C_mul_X_coeff]
    rw [ord_mul, ord_mul, ord_pow, ord_inv, hq, heord]
    have hscaled : (0 : WithTop ℤ) <
        n • ((r - s : ℤ) : WithTop ℤ) + -((r : ℤ) : WithTop ℤ) := by
      rw [← WithTop.coe_nsmul, ← WithTop.LinearOrderedAddCommGroup.coe_neg,
        ← WithTop.coe_add]
      exact WithTop.coe_lt_coe.mpr
        (by simpa [nsmul_eq_mul] using scaled_coefficient_positive hs hstrict hn)
    rw [add_assoc]
    exact hscaled.trans_le (le_add_of_nonneg_left htaylor)
  have hHcoeff (n : ℕ) : 0 ≤ ord F (H.coeff n) := by
    by_cases hn0 : n = 0
    · subst n
      simp [hHzero]
    by_cases hn1 : n = 1
    · subst n
      simp [hHone]
    exact (hHcoeffPos n (by omega)).le
  -- Every coefficient is integral, so `H` comes from an actual polynomial over the DVR.
  have hHrange : H ∈ (Polynomial.mapRingHom i).range := by
    rw [Polynomial.mem_map_range]
    intro n
    exact ⟨⟨H.coeff n, (ord_nonneg_iff_mem_integer F _).1 (hHcoeff n)⟩, rfl⟩
  obtain ⟨h, hh⟩ := hHrange
  have hhcoeff (n : ℕ) : i (h.coeff n) = H.coeff n := by
    calc
      i (h.coeff n) = (h.map i).coeff n := by rw [Polynomial.coeff_map]
      _ = H.coeff n := congrArg (fun p ↦ p.coeff n) hh
  have hhzero : h.coeff 0 = 1 := by
    apply Subtype.ext
    change i (h.coeff 0) = i 1
    rw [hhcoeff, hHzero, map_one]
  have hhone : h.coeff 1 = 1 := by
    apply Subtype.ext
    change i (h.coeff 1) = i 1
    rw [hhcoeff, hHone, map_one]
  have hhigher (n : ℕ) (hn : 2 ≤ n) :
      h.coeff n ∈ IsLocalRing.maximalIdeal (ringOfIntegers F) := by
    apply (ord_pos_iff_mem_maximalIdeal F _).mp
    change 0 < ord F (i (h.coeff n))
    rw [hhcoeff n]
    exact hHcoeffPos n hn
  let π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal (ringOfIntegers F))
  have hmod : h.map π = X + 1 := by
    ext n
    by_cases hn0 : n = 0
    · subst n
      simp only [Polynomial.coeff_map, hhzero, map_one, Polynomial.coeff_add,
        Polynomial.coeff_X_zero, Polynomial.coeff_one_zero, zero_add]
    by_cases hn1 : n = 1
    · subst n
      simp only [Polynomial.coeff_map, hhone, map_one, Polynomial.coeff_add,
        Polynomial.coeff_X_one, Polynomial.coeff_one, if_neg one_ne_zero, add_zero]
    have hn : 2 ≤ n := by omega
    have h1n : 1 ≠ n := by omega
    simp only [Polynomial.coeff_map]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hhigher n hn)]
    simp only [Polynomial.coeff_add, Polynomial.coeff_X, h1n, if_false,
      Polynomial.coeff_one, hn0, zero_add]
  have hevalmem : h.eval (-1) ∈ IsLocalRing.maximalIdeal (ringOfIntegers F) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change π (h.eval (-1)) = 0
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, hmod]
    simp
  have hderivunit : IsUnit (π (h.derivative.eval (-1))) := by
    have heq : π (h.derivative.eval (-1)) = 1 := by
      rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map,
        ← Polynomial.derivative_map, hmod]
      simp
    rw [heq]
    exact isUnit_one
  letI := IsTopologicalAddGroup.rightUniformSpace F
  letI := isUniformAddGroup_of_addCommGroup (G := F)
  obtain ⟨z, hz, _⟩ := exists_root_of_simple_residual h (-1) hevalmem hderivunit
  have hHz : H.eval (i z) = 0 := by
    calc
      H.eval (i z) = ((Polynomial.mapRingHom i) h).eval (i z) :=
        congrArg (fun p ↦ p.eval (i z)) hh.symm
      _ = i (h.eval z) := by
        change (h.map i).eval (i z) = i (h.eval z)
        rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
      _ = 0 := by rw [hz, map_zero]
  have hrootF : fF.eval (aF + q * i z) = 0 := by
    simp only [H, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.taylor_eval] at hHz
    rw [add_comm]
    apply (mul_eq_zero.mp hHz).resolve_right
    exact inv_ne_zero he0
  have hqnonneg : 0 ≤ ord F q := by
    rw [hq]
    exact WithTop.coe_nonneg.mpr (by omega)
  let qR : ringOfIntegers F :=
    ⟨q, (ord_nonneg_iff_mem_integer F q).mp hqnonneg⟩
  let b : ringOfIntegers F := a + qR * z
  have hb : f.IsRoot b := by
    apply Subtype.ext
    change i (f.eval b) = i 0
    rw [map_zero]
    calc
      i (f.eval b) = fF.eval (i b) := by
        simp only [fF, Polynomial.eval_map, Polynomial.eval₂_at_apply]
      _ = fF.eval (aF + q * i z) := by congr 2
      _ = 0 := hrootF
  have hznonneg : 0 ≤ ord F (z : F) :=
    (ord_nonneg_iff_mem_integer F _).2 z.property
  have hbsub : (b : F) - (a : F) = q * (z : F) := by
    simp only [b, qR, Subring.coe_add, Subring.coe_mul, add_sub_cancel_left]
  have hdisp : ((r - s : ℤ) : WithTop ℤ) ≤
      ord F ((b : F) - (a : F)) := by
    rw [hbsub, ord_mul, hq]
    exact le_add_of_nonneg_right hznonneg
  refine ⟨b, hb, ?_, ?_⟩
  · exact (WithTop.coe_lt_coe.mpr (by omega)).trans_le hdisp
  · rw [hres, ← WithTop.LinearOrderedAddCommGroup.coe_sub]
    exact hdisp

/-- **Paper D.1 (`D:newton`)**. Let `R` be the canonical complete discrete valuation ring of
a nonarchimedean local field. If `s = v(f'(a))` is finite and `v(f(a)) > 2s`, there is a unique
root in the strict ball `v(b-a) > s`, and it satisfies `v(b-a) ≥ v(f(a))-s`.

The conclusion's last conjunct states uniqueness among *all* roots in the strict ball; it does
not restrict competitors to roots satisfying the quantitative bound. -/
theorem newton
    {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (f : (ringOfIntegers F)[X]) (a : ringOfIntegers F) (s : ℤ)
    (hderiv : ord F ((f.derivative.eval a : ringOfIntegers F) : F) =
      (s : WithTop ℤ))
    (hres : ((2 * s : ℤ) : WithTop ℤ) <
      ord F ((f.eval a : ringOfIntegers F) : F)) :
    ∃ b : ringOfIntegers F,
      f.IsRoot b ∧
      (s : WithTop ℤ) < ord F ((b : F) - (a : F)) ∧
      ord F ((f.eval a : ringOfIntegers F) : F) - (s : WithTop ℤ) ≤
        ord F ((b : F) - (a : F)) ∧
      ∀ c : ringOfIntegers F, f.IsRoot c →
        (s : WithTop ℤ) < ord F ((c : F) - (a : F)) → c = b := by
  by_cases hzero : f.eval a = 0
  · refine ⟨a, hzero, ?_, ?_, ?_⟩
    · simp
    · simp [hzero]
    · intro c hc hcball
      exact unique_root_in_newton_ball f a s hderiv hc hzero hcball (by simp)
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp
      ((ord_ne_top_iff F).2 (fun h ↦ hzero (Subtype.ext h)))
    have hr' : ord F ((f.eval a : ringOfIntegers F) : F) = (r : WithTop ℤ) := hr.symm
    have hstrict : 2 * s < r := by
      rw [hr'] at hres
      exact WithTop.coe_lt_coe.mp hres
    obtain ⟨b, hb, hbball, hbound⟩ :=
      exists_quantitative_root_of_residual_ne_zero f a s r hzero hderiv hr' hstrict
    refine ⟨b, hb, hbball, hbound, ?_⟩
    intro c hc hcball
    exact unique_root_in_newton_ball f a s hderiv hc hb hcball hbball

end

end LanglandsSecondMainLemma.Local
