import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Total.Setup

/-!
# Odd / Total / Power Norm

Paper Lemma 7.1 (`O:A:lem:power`).  For a totally ramified cyclic extension
of odd prime degree `p` and positive lower break `u`, the difference between
the `p`-th power of an element and its norm gains `(p - 1)u` in normalized
upstairs order.

The proof expands the characteristic polynomial into FML's elementary
symmetric coefficients.  FML's strong wild symmetric bound is stated in
normalized downstairs order; `ord_algebraMap` and `e(L/M) = p` perform the
required conversion back to normalized upstairs order.
-/

namespace LanglandsSecondMainLemma.Odd.Total

open LanglandsFirstMainLemma
open scoped BigOperators

noncomputable section

/-- A nonarchimedean local field is infinite.  This local instance is used
only to identify characteristic-polynomial coefficients with elementary
symmetric functions of the Galois conjugates. -/
private theorem localFieldInfinite
    (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M] : Infinite M := by
  let f : ℤ → M := fun n ↦ (exists_ord_eq M n).choose
  have hf : Function.Injective f := by
    intro m n hmn
    have hm : ord M (f m) = (m : WithTop ℤ) := (exists_ord_eq M m).choose_spec
    have hn : ord M (f n) = (n : WithTop ℤ) := (exists_ord_eq M n).choose_spec
    have hcoe : (m : WithTop ℤ) = (n : WithTop ℤ) := hm.symm.trans <|
      (congrArg (ord M) hmn).trans hn
    exact WithTop.coe_injective hcoe
  exact Infinite.of_injective f hf

/-- The characteristic-polynomial identity used in Paper Lemma 7.1.
The terminal sign is negative because the extension degree is odd. -/
private theorem characteristicPower_sub_norm_eq
    (M L : Type*) [Field M] [Field L]
    [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [Algebra M L] [Module.Free M L] [Module.Finite M L] [IsGalois M L]
    (p : ℕ) (hdegree : Module.finrank M L = p) (hodd : Odd p) (y : L) :
    y ^ p - algebraMap M L (norm M L y) =
      -∑ i ∈ Finset.range (p - 1),
        (-1 : L) ^ (i + 1) *
          algebraMap M L (elementarySymmetric M L (i + 1) y) *
            y ^ (p - (i + 1)) := by
  letI : Infinite M := localFieldInfinite M
  let s := galoisConjugates M L y
  have hpoly :
      (s.map fun z ↦ Polynomial.X - Polynomial.C z).prod =
        (Algebra.lmul M L y).charpoly.map (algebraMap M L) := by
    rw [map_lmul_charpoly_eq_prod_galois M L]
    simp only [s, galoisConjugates, galoisConjugate, Finset.prod,
      Multiset.map_map, Function.comp_apply]
  have hroot : Polynomial.eval y
      ((s.map fun z ↦ Polynomial.X - Polynomial.C z).prod) = 0 := by
    rw [hpoly, Polynomial.eval_map]
    exact Algebra.aeval_self_charpoly_lmul y
  have hvieta := congrArg (Polynomial.eval y)
    (Multiset.prod_X_sub_X_eq_sum_esymm s)
  rw [hroot] at hvieta
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_neg, Polynomial.eval_one] at hvieta
  have hsum :
      ∑ j ∈ Finset.range (p + 1),
          (-1 : L) ^ j *
            (algebraMap M L (elementarySymmetric M L j y) * y ^ (p - j)) = 0 := by
    simpa only [s, galoisConjugates_card, hdegree,
      algebraMap_elementarySymmetric_eq_esymm_galois] using hvieta.symm
  have hp0 : 0 < p := hodd.pos
  have hpdecomp : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  have hsplit :
      ∑ i ∈ Finset.range p,
          (-1 : L) ^ (i + 1) *
            (algebraMap M L (elementarySymmetric M L (i + 1) y) *
              y ^ (p - (i + 1))) =
        (∑ i ∈ Finset.range (p - 1),
          (-1 : L) ^ (i + 1) *
            (algebraMap M L (elementarySymmetric M L (i + 1) y) *
              y ^ (p - (i + 1)))) +
          (-1 : L) ^ p *
            (algebraMap M L (elementarySymmetric M L p y) * y ^ (p - p)) := by
    conv_lhs =>
      rw [← hpdecomp, Finset.sum_range_succ]
    rw [hpdecomp]
  rw [Finset.sum_range_succ', hsplit] at hsum
  have hsign : (-1 : L) ^ p = -1 := hodd.neg_one_pow
  have hterminal : elementarySymmetric M L p y = norm M L y := by
    rw [← hdegree, elementarySymmetric_finrank]
  simp only [pow_zero, elementarySymmetric_zero, map_one, one_mul,
    Nat.sub_zero, Nat.sub_self, hterminal, hsign, neg_one_mul, mul_one] at hsum
  simp only [mul_assoc] at hsum ⊢
  linear_combination hsum

/-- Integer estimate behind the gain of `(p - 1)u` after the strong
symmetric bound is rescaled from downstairs order to upstairs order. -/
private theorem floor_coefficient_bound
    (p j u : ℕ) (q : ℤ) (hp : 0 < p) (hj : j < p) :
    (p : ℤ) * q + (((p - 1) * u : ℕ) : ℤ) ≤
      (p : ℤ) *
          (((j : ℤ) * q + (((p - 1) * (u + 1) : ℕ) : ℤ)) / (p : ℤ)) +
        ((p - j : ℕ) : ℤ) * q := by
  let A : ℤ := (j : ℤ) * q + (((p - 1) * (u + 1) : ℕ) : ℤ)
  have hpZ : 0 < (p : ℤ) := by exact_mod_cast hp
  have hmodlt : A % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos A hpZ
  have hdecomp : (p : ℤ) * (A / (p : ℤ)) + A % (p : ℤ) = A :=
    Int.mul_ediv_add_emod A (p : ℤ)
  have hpSub : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  have hjSub : ((p - j : ℕ) : ℤ) = (p : ℤ) - (j : ℤ) := by omega
  have hnonneg : 0 ≤ ((p - 1 : ℕ) : ℤ) - A % (p : ℤ) := by omega
  have hdiff :
      (p : ℤ) *
            (((j : ℤ) * q + (((p - 1) * (u + 1) : ℕ) : ℤ)) / (p : ℤ)) +
          ((p - j : ℕ) : ℤ) * q -
        ((p : ℤ) * q + (((p - 1) * u : ℕ) : ℤ)) =
      ((p - 1 : ℕ) : ℤ) - A % (p : ℤ) := by
    dsimp only [A] at hdecomp ⊢
    rw [hpSub, hjSub]
    push_cast [hpSub, hjSub] at hdecomp ⊢
    linear_combination hdecomp
  rw [← hdiff] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- **Paper 7.1 (`O:A:lem:power`)**.  Let `L/M` be a totally ramified
cyclic extension of odd prime degree `p`, with positive lower break `u`.
For every `y : L`,

`v_L(y^p - N_{L/M}(y)) ≥ p v_L(y) + (p - 1)u`.

The norm lies in `M` and is explicitly mapped to `L`.  Both occurrences of
`ord L` are therefore normalized on the upper field. -/
theorem powerNorm
    (M L : Type*) [Field M] [Field L]
    [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra M L] [ValuativeExtension M L]
    [Module.Free M L] [Module.Finite M L] [PrimeCyclicExtension M L]
    (p u : ℕ) (hdegree : Module.finrank M L = p) (hodd : 2 < p)
    (hbreak : PrimeCyclicExtension.IsLowerBreak M L u)
    (hu : 0 < u) (hres : residueDegree M L = 1) (y : L) :
    p • ord L y + ((((p - 1) * u : ℕ) : ℤ) : WithTop ℤ) ≤
      ord L (y ^ p - algebraMap M L (norm M L y)) := by
  have hp : p.Prime := by
    rw [← hdegree]
    exact PrimeCyclicExtension.degree_prime M L
  have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
  by_cases hy0 : y = 0
  · subst y
    simp [hp.ne_zero]
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff L).2 hy0)
  have hy : ord L y = (q : WithTop ℤ) := hq.symm
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer M L hres
  have hram : ramificationIndex M L = p := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree M L
    rw [hres, mul_one, hdegree] at h
    exact h.symm
  have hchar : residueCharacteristic M = Module.finrank M L :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak M L hbreak hu pi hpi hgen
  have htrace : TraceIdealLowerBound M L (Module.finrank M L)
      (wildDifferentContribution (Module.finrank M L) u) := by
    simpa only [wildDifferentContribution] using
      traceIdealLowerBound_of_integralGenerator M L hbreak hres pi hpi hgen
  have hramFin : ramificationIndex M L = Module.finrank M L :=
    hram.trans hdegree.symm
  have hsymmetric := wild_symmetric_bound M L u hbreak hu hchar
    hramFin htrace q (le_of_eq hy.symm)
  rw [characteristicPower_sub_norm_eq M L p hdegree hpOdd y, ord_neg]
  apply ord_sum L
  intro i hi
  simp only [Finset.mem_range] at hi
  let j := i + 1
  have hjpos : 1 ≤ j := by omega
  have hjlt : j < p := by dsimp only [j]; omega
  have hcoeff :
      (((((j : ℤ) * q + (((p - 1) * (u + 1) : ℕ) : ℤ)) / (p : ℤ) : ℤ)) :
          WithTop ℤ) ≤ ord M (elementarySymmetric M L j y) := by
    simpa only [hdegree, wildDifferentContribution] using
      hsymmetric.1 hjpos (by simpa only [hdegree] using hjlt)
  have hcoeffScaled := nsmul_le_nsmul_right hcoeff p
  have htermArithmetic := floor_coefficient_bound p j u q hp.pos hjlt
  have htarget :
      (((p : ℤ) * q + (((p - 1) * u : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤
        p • ord M (elementarySymmetric M L j y) +
          (p - j) • ord L y := by
    apply (WithTop.coe_le_coe.mpr htermArithmetic).trans
    have hsumBound := add_le_add hcoeffScaled
      (nsmul_le_nsmul_right (le_of_eq hy.symm) (p - j))
    rw [← WithTop.coe_nsmul, ← WithTop.coe_nsmul] at hsumBound
    simpa only [WithTop.coe_add, nsmul_eq_mul] using hsumBound
  rw [ord_mul, ord_mul, ord_pow, ord_pow, ord_neg, ord_one,
    nsmul_zero, zero_add, ord_algebraMap, hram]
  rw [hy, ← WithTop.coe_nsmul]
  simpa only [j, hy, WithTop.coe_add, nsmul_eq_mul] using htarget

end

end LanglandsSecondMainLemma.Odd.Total
