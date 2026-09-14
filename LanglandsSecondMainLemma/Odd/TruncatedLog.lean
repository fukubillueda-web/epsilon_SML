import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.LocalField.Lattices
import LanglandsFirstMainLemma.LocalField.MonogenicUniformizer
import LanglandsFirstMainLemma.LocalField.Valuation
import LanglandsFirstMainLemma.LocalField.FiniteQuotients
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.MvPowerSeries.Inverse

namespace LanglandsSecondMainLemma.Odd

open Polynomial
open LanglandsFirstMainLemma
open scoped BigOperators Ring ValuativeRel

noncomputable section

def truncatedLogPolynomial (K : Type*) [Field K] (p : ℕ) : K[X] :=
  X + ∑ j ∈ Finset.Ico 2 p, C (j : K)⁻¹ * X ^ j

def truncatedLog {K : Type*} [Field K] (p : ℕ) (z : K) : K :=
  (truncatedLogPolynomial K p).eval z

/-- The same truncated logarithm evaluated inside a two-variable polynomial ring. -/
def truncatedLogMvPolynomial (K : Type*) [Field K] (p : ℕ)
    (z : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 2) K :=
  z + ∑ j ∈ Finset.Ico 2 p, MvPolynomial.C (j : K)⁻¹ * z ^ j

/-- The polynomial measuring the failure of the truncated logarithm to convert multiplication
of `1-z` and `1-w` into addition. -/
def truncatedLogDefectPolynomial (K : Type*) [Field K] (p : ℕ) :
    MvPolynomial (Fin 2) K :=
  let z := MvPolynomial.X (0 : Fin 2)
  let w := MvPolynomial.X (1 : Fin 2)
  truncatedLogMvPolynomial K p (z + w - z * w) -
    truncatedLogMvPolynomial K p z - truncatedLogMvPolynomial K p w

@[simp] theorem truncatedLog_apply {K : Type*} [Field K] (p : ℕ) (z : K) :
    truncatedLog p z = z + ∑ j ∈ Finset.Ico 2 p, z ^ j / (j : K) := by
  simp only [truncatedLog, truncatedLogPolynomial, eval_add, eval_X,
    eval_finsetSum, eval_mul, eval_C, eval_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [div_eq_mul_inv, mul_comm]

private theorem ord_natCast_eq_zero
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p j : ℕ) (hchar : ringChar (ResidueField F) = p)
    (hjpos : 0 < j) (hjlt : j < p) :
    ord F (j : F) = 0 := by
  letI : CharP (ResidueField F) p := ringChar.of_eq hchar
  have hjres : (j : ResidueField F) ≠ 0 := by
    exact (CharP.cast_eq_zero_iff (ResidueField F) p j).not.mpr
      (Nat.not_dvd_of_pos_of_lt hjpos hjlt)
  have hjred : residueMap F (j : ringOfIntegers F) ≠ 0 := by
    simpa using hjres
  have hjnot : (j : F) ∉ lattice F 1 := by
    intro hj
    apply hjred
    apply (residueMap_eq_zero_iff F (j : ringOfIntegers F)).2
    simpa using hj
  have hj0 : (j : F) ≠ 0 := by
    intro h
    apply hjnot
    simp [h]
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).2 hj0)
  have hk0 : 0 ≤ k := by
    have : 0 ≤ ord F (j : F) :=
      (ord_nonneg_iff_mem_integer F _).2 (show (j : F) ∈ ringOfIntegers F by exact (j : ringOfIntegers F).property)
    rw [← hk] at this
    exact_mod_cast this
  have hk1 : ¬ (1 : ℤ) ≤ k := by
    intro h
    apply hjnot
    change ((1 : ℤ) : WithTop ℤ) ≤ ord F (j : F)
    rw [← hk]
    exact_mod_cast h
  rw [← hk]
  congr
  omega

private noncomputable def truncatedLogIntegerCoefficient
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) (hchar : ringChar (ResidueField F) = p) (j : ℕ) :
    ringOfIntegers F :=
  if h : 0 < j ∧ j < p then
    ⟨(j : F)⁻¹, (ord_nonneg_iff_mem_integer F _).1 (by
      rw [ord_inv, ord_natCast_eq_zero F p j hchar h.1 h.2]
      simp)⟩
  else 0

@[simp] private theorem coe_truncatedLogIntegerCoefficient
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) (hchar : ringChar (ResidueField F) = p) (j : ℕ)
    (hj : 0 < j ∧ j < p) :
    (truncatedLogIntegerCoefficient F p hchar j : F) = (j : F)⁻¹ := by
  simp [truncatedLogIntegerCoefficient, hj]

private noncomputable def truncatedLogIntegralPolynomial
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) (hchar : ringChar (ResidueField F) = p) :
    (ringOfIntegers F)[X] :=
  X + ∑ j ∈ Finset.Ico 2 p,
    C (truncatedLogIntegerCoefficient F p hchar j) * X ^ j

private theorem map_truncatedLogIntegralPolynomial
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) (hchar : ringChar (ResidueField F) = p) :
    (truncatedLogIntegralPolynomial F p hchar).map
      (ValuativeRel.valuation F).integer.subtype = truncatedLogPolynomial F p := by
  simp only [truncatedLogIntegralPolynomial, truncatedLogPolynomial,
    Polynomial.map_add, Polynomial.map_X]
  congr 1
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X]
  apply congrArg (fun a : F ↦ C a * X ^ j)
  exact coe_truncatedLogIntegerCoefficient F p hchar j
    ⟨by omega, hj'.2⟩

private theorem eval_truncatedLogIntegralPolynomial
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) (hchar : ringChar (ResidueField F) = p)
    (z : ringOfIntegers F) :
    ((truncatedLogIntegralPolynomial F p hchar).eval z : ringOfIntegers F) =
      truncatedLog p (z : F) := by
  rw [truncatedLog]
  rw [← map_truncatedLogIntegralPolynomial F p hchar]
  exact (Polynomial.eval_map_apply
    (p := truncatedLogIntegralPolynomial F p hchar)
    (ValuativeRel.valuation F).integer.subtype z).symm

private theorem coeff_truncatedLogIntegralPolynomial
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) (hchar : ringChar (ResidueField F) = p) (n : ℕ) :
    (truncatedLogIntegralPolynomial F p hchar).coeff n =
      (if n = 1 then 1 else if n ∈ Finset.Ico 2 p then
        truncatedLogIntegerCoefficient F p hchar n else 0) := by
  classical
  rw [truncatedLogIntegralPolynomial, coeff_add]
  simp only [coeff_X]
  by_cases hn : n = 1
  · subst n
    simp
  · have hn' : 1 ≠ n := Ne.symm hn
    simp [hn, hn']

private theorem natDegree_truncatedLogIntegralPolynomial
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) (hchar : ringChar (ResidueField F) = p) (hp : p.Prime) :
    (truncatedLogIntegralPolynomial F p hchar).natDegree = p - 1 := by
  have hp2 : 2 ≤ p := hp.two_le
  apply le_antisymm
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [coeff_truncatedLogIntegralPolynomial]
    have hn1 : n ≠ 1 := by omega
    rw [if_neg hn1]
    rw [if_neg]
    intro hnmem
    have hnltp := (Finset.mem_Ico.mp hnmem).2
    omega
  · apply le_natDegree_of_ne_zero
    rw [coeff_truncatedLogIntegralPolynomial]
    by_cases hp2eq : p = 2
    · rw [if_pos (by omega)]
      exact one_ne_zero
    · have hpgt : 2 < p := lt_of_le_of_ne hp2 (Ne.symm hp2eq)
      simp only [show p - 1 ≠ 1 by omega, if_false]
      rw [if_pos (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)]
      intro hzero
      have hzero' := congrArg
        (ValuativeRel.valuation F).integer.subtype hzero
      rw [map_zero] at hzero'
      change (truncatedLogIntegerCoefficient F p hchar (p - 1) : F) = 0 at hzero'
      rw [coe_truncatedLogIntegerCoefficient F p hchar (p - 1)
        ⟨by omega, by omega⟩] at hzero'
      apply (inv_ne_zero (by
        intro hcast
        have hord := ord_natCast_eq_zero F p (p - 1) hchar (by omega) (by omega)
        rw [hcast, ord_zero] at hord
        exact WithTop.top_ne_coe hord)) hzero'

/-- On the maximal ideal, the truncated logarithm has the same order as its input. -/
theorem ord_truncatedLog
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) (hchar : ringChar (ResidueField F) = p)
    {z : F} (hz : z ∈ lattice F 1) :
    ord F (truncatedLog p z) = ord F z := by
  by_cases hz0 : z = 0
  · subst z
    rw [truncatedLog_apply]
    simp only [zero_add]
    have hsum : ∑ j ∈ Finset.Ico 2 p, (0 : F) ^ j / (j : F) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [zero_pow (by have := (Finset.mem_Ico.mp hj).1; omega), zero_div]
    rw [hsum]
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).2 hz0)
  have hkpos : 0 < k := by
    rw [mem_lattice, ← hk] at hz
    exact_mod_cast hz
  let e : F := ∑ j ∈ Finset.Ico 2 p, z ^ j / (j : F)
  have he : ((k + 1 : ℤ) : WithTop ℤ) ≤ ord F e := by
    apply ord_sum F
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    rw [ord_div, ord_pow, ord_natCast_eq_zero F p j hchar (by omega) hj'.2]
    simp only [sub_zero]
    rw [← hk, ← WithTop.coe_nsmul]
    exact_mod_cast (show k + 1 ≤ (j : ℤ) * k by nlinarith)
  have hze : ord F z < ord F e := by
    rw [← hk]
    exact (WithTop.coe_lt_coe.mpr (lt_add_one k)).trans_le he
  rw [truncatedLog_apply]
  change ord F (z + e) = ord F z
  rw [ord_add_eq_min F (ne_of_lt hze), min_eq_left hze.le]

private theorem leadingCoeff_truncatedLogIntegralPolynomial
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) (hchar : ringChar (ResidueField F) = p) (hp : p.Prime) :
    (truncatedLogIntegralPolynomial F p hchar).leadingCoeff =
      truncatedLogIntegerCoefficient F p hchar (p - 1) := by
  have hp2le : 2 ≤ p := hp.two_le
  rw [leadingCoeff, natDegree_truncatedLogIntegralPolynomial F p hchar hp,
    coeff_truncatedLogIntegralPolynomial]
  by_cases hp2 : p = 2
  · have hc : truncatedLogIntegerCoefficient F p hchar (p - 1) = 1 := by
      apply Subtype.ext
      rw [coe_truncatedLogIntegerCoefficient F p hchar (p - 1)
        ⟨by omega, by omega⟩]
      have hcast : ((p - 1 : ℕ) : F) = 1 := by simp [hp2]
      rw [hcast, inv_one]
      rfl
    rw [if_pos (by omega), hc]
  · rw [if_neg (by omega), if_pos (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)]

private theorem isUnit_leadingCoeff_truncatedLogIntegralPolynomial
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) (hchar : ringChar (ResidueField F) = p) (hp : p.Prime) :
    IsUnit (truncatedLogIntegralPolynomial F p hchar).leadingCoeff := by
  have hp2le : 2 ≤ p := hp.two_le
  rw [leadingCoeff_truncatedLogIntegralPolynomial F p hchar hp]
  rw [isUnit_iff_exists_inv]
  let b : ringOfIntegers F :=
    ⟨((p - 1 : ℕ) : F), (ord_nonneg_iff_mem_integer F _).1 (by
      rw [ord_natCast_eq_zero F p (p - 1) hchar (by omega) (by omega)])⟩
  refine ⟨b, ?_⟩
  apply Subtype.ext
  change (truncatedLogIntegerCoefficient F p hchar (p - 1) : F) *
    ((p - 1 : ℕ) : F) = 1
  rw [coe_truncatedLogIntegerCoefficient F p hchar (p - 1)
    ⟨by omega, by omega⟩]
  apply inv_mul_cancel₀
  intro hcast
  have hord := ord_natCast_eq_zero F p (p - 1) hchar (by omega) (by omega)
  rw [hcast, ord_zero] at hord
  exact WithTop.top_ne_coe hord

private theorem derivative_truncatedLogIntegralPolynomial_eval_zero
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) (hchar : ringChar (ResidueField F) = p) :
    (truncatedLogIntegralPolynomial F p hchar).derivative.eval 0 = 1 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  rw [coeff_derivative, coeff_truncatedLogIntegralPolynomial]
  simp

private theorem leadingCoeff_sub_C_truncatedLogIntegralPolynomial
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) (hchar : ringChar (ResidueField F) = p) (hp : p.Prime)
    (w : ringOfIntegers F) :
    (truncatedLogIntegralPolynomial F p hchar - C w).leadingCoeff =
      (truncatedLogIntegralPolynomial F p hchar).leadingCoeff := by
  have hp2le : 2 ≤ p := hp.two_le
  have hpos : 0 < p - 1 := by omega
  apply leadingCoeff_sub_of_degree_lt
  calc
    (C w).degree ≤ 0 := degree_C_le
    _ < ((p - 1 : ℕ) : WithBot ℕ) := by exact_mod_cast hpos
    _ = (truncatedLogIntegralPolynomial F p hchar).degree := by
      rw [degree_eq_natDegree]
      · rw [natDegree_truncatedLogIntegralPolynomial F p hchar hp]
      · intro hzero
        have hnat := natDegree_truncatedLogIntegralPolynomial F p hchar hp
        rw [hzero, natDegree_zero] at hnat
        omega

private theorem exists_truncatedLog_eq
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) (hchar : ringChar (ResidueField F) = p) (hp : p.Prime)
    {w : F} (hw : w ∈ lattice F 1) :
    ∃ z : F, z ∈ lattice F 1 ∧ truncatedLog p z = w := by
  let wR : ringOfIntegers F :=
    ⟨w, (mem_lattice_zero_iff F).1 (lattice_antitone F (by omega) hw)⟩
  let q : (ringOfIntegers F)[X] :=
    truncatedLogIntegralPolynomial F p hchar - C wR
  have hqlead : q.leadingCoeff =
      (truncatedLogIntegralPolynomial F p hchar).leadingCoeff := by
    exact leadingCoeff_sub_C_truncatedLogIntegralPolynomial F p hchar hp wR
  have hqleadunit : IsUnit q.leadingCoeff := by
    rw [hqlead]
    exact isUnit_leadingCoeff_truncatedLogIntegralPolynomial F p hchar hp
  let f : (ringOfIntegers F)[X] := hqleadunit.unit⁻¹ • q
  have hfmonic : f.Monic := by
    exact q.monic_of_isUnit_leadingCoeff_inv_smul hqleadunit
  have hqeval : q.eval 0 = -wR := by
    change (truncatedLogIntegralPolynomial F p hchar - C wR).eval 0 = -wR
    rw [eval_sub, eval_C, ← coeff_zero_eq_eval_zero,
      coeff_truncatedLogIntegralPolynomial]
    simp
  have hqderiv : q.derivative.eval 0 = 1 := by
    simp only [q, derivative_sub, derivative_C, sub_zero]
    exact derivative_truncatedLogIntegralPolynomial_eval_zero F p hchar
  have hfeval : f.eval 0 ∈ IsLocalRing.maximalIdeal (ringOfIntegers F) := by
    change (hqleadunit.unit⁻¹ • q).eval 0 ∈ _
    rw [eval_smul, hqeval]
    exact (IsLocalRing.maximalIdeal (ringOfIntegers F)).smul_mem _
      ((IsLocalRing.maximalIdeal (ringOfIntegers F)).neg_mem
        ((mem_lattice_one_iff_mem_maximalIdeal F wR).1 (by simpa [wR] using hw)))
  have hfderiv : IsUnit
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (ringOfIntegers F))
        (f.derivative.eval 0)) := by
    have hunit : IsUnit (f.derivative.eval 0) := by
      change IsUnit ((hqleadunit.unit⁻¹ • q).derivative.eval 0)
      rw [derivative_smul, eval_smul, hqderiv]
      change IsUnit ((↑(hqleadunit.unit⁻¹) : ringOfIntegers F) * 1)
      exact hqleadunit.unit⁻¹.isUnit.mul isUnit_one
    exact hunit.map _
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  obtain ⟨zR, hzroot, hzmod⟩ :=
    HenselianRing.is_henselian f hfmonic 0 hfeval hfderiv
  have hqroot : q.eval zR = 0 := by
    have hfzero : f.eval zR = 0 := hzroot
    change (hqleadunit.unit⁻¹ • q).eval zR = 0 at hfzero
    rw [eval_smul, Units.smul_def] at hfzero
    exact (mul_eq_zero.mp hfzero).resolve_left (Units.ne_zero _)
  have hzmem : (zR : F) ∈ lattice F 1 := by
    apply (mem_lattice_one_iff_mem_maximalIdeal F zR).2
    simpa using hzmod
  refine ⟨(zR : F), hzmem, ?_⟩
  have hqrootF := congrArg (ValuativeRel.valuation F).integer.subtype hqroot
  rw [map_zero] at hqrootF
  change ((q.eval zR : ringOfIntegers F) : F) = 0 at hqrootF
  change ((((truncatedLogIntegralPolynomial F p hchar - C wR).eval zR :
    ringOfIntegers F)) : F) = 0 at hqrootF
  rw [eval_sub, eval_C] at hqrootF
  have hPeval := eval_truncatedLogIntegralPolynomial F p hchar zR
  change (((truncatedLogIntegralPolynomial F p hchar).eval zR :
    ringOfIntegers F) : F) - w = 0 at hqrootF
  rw [hPeval] at hqrootF
  exact sub_eq_zero.mp hqrootF

private theorem powSubPowFactor_mem_lattice_zero
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {x y : F}
    (hx : x ∈ lattice F 1) (hy : y ∈ lattice F 1) (j : ℕ) :
    (powSubPowFactor x y j).val ∈ lattice F 0 := by
  have hx0 : x ∈ lattice F 0 := lattice_antitone F (by omega) hx
  have hy0 : y ∈ lattice F 0 := lattice_antitone F (by omega) hy
  induction j with
  | zero => simp [powSubPowFactor]
  | succ j ih =>
      cases j with
      | zero => simp [powSubPowFactor]
      | succ k =>
          change (powSubPowFactor x y (k + 1)).val * x + y ^ (k + 1) ∈
            lattice F 0
          apply add_mem_lattice F
          · simpa using mul_mem_lattice F ih hx0
          · rw [mem_lattice, ord_pow]
            exact (nsmul_nonneg (show (0 : WithTop ℤ) ≤ ord F y from hy0)) (k + 1)

private theorem powSubPowFactor_mem_lattice_one
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {x y : F}
    (hx : x ∈ lattice F 1) (hy : y ∈ lattice F 1) {j : ℕ} (hj : 2 ≤ j) :
    (powSubPowFactor x y j).val ∈ lattice F 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show 2 + k = k + 2 by omega]
  change (powSubPowFactor x y (k + 1)).val * x + y ^ (k + 1) ∈ lattice F 1
  apply add_mem_lattice F
  · simpa using mul_mem_lattice F
      (powSubPowFactor_mem_lattice_zero F hx hy (k + 1)) hx
  · rw [pow_succ']
    simpa using mul_mem_lattice F hy
      (show y ^ k ∈ lattice F 0 by
        rw [mem_lattice, ord_pow]
        exact (nsmul_nonneg (by
          have hy0 := lattice_antitone F (show (0 : ℤ) ≤ 1 by omega) hy
          exact (show (0 : WithTop ℤ) ≤ ord F y from hy0))) k)

private def truncatedLogSubFactor (F : Type*) [Field F] (p : ℕ) (x y : F) : F :=
  1 + ∑ j ∈ Finset.Ico 2 p, (j : F)⁻¹ * (powSubPowFactor x y j).val

private theorem truncatedLog_sub_eq_factor_mul
    (F : Type*) [Field F] (p : ℕ) (x y : F) :
    truncatedLog p x - truncatedLog p y =
      truncatedLogSubFactor F p x y * (x - y) := by
  rw [truncatedLog_apply, truncatedLog_apply]
  have hsum :
      (∑ j ∈ Finset.Ico 2 p, x ^ j / (j : F)) -
          ∑ j ∈ Finset.Ico 2 p, y ^ j / (j : F) =
        ∑ j ∈ Finset.Ico 2 p,
          ((j : F)⁻¹ * (powSubPowFactor x y j).val) * (x - y) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    let fac := powSubPowFactor x y j
    change x ^ j / (j : F) - y ^ j / (j : F) =
      ((j : F)⁻¹ * fac.val) * (x - y)
    rcases fac with ⟨a, ha⟩
    dsimp only at ha ⊢
    calc
      x ^ j / (j : F) - y ^ j / (j : F) =
          (j : F)⁻¹ * (x ^ j - y ^ j) := by
            simp only [div_eq_mul_inv]
            ring
      _ = ((j : F)⁻¹ * a) * (x - y) := by
            rw [ha]
            ring
  rw [show x + (∑ j ∈ Finset.Ico 2 p, x ^ j / (j : F)) -
      (y + ∑ j ∈ Finset.Ico 2 p, y ^ j / (j : F)) =
      (x - y) + ((∑ j ∈ Finset.Ico 2 p, x ^ j / (j : F)) -
        ∑ j ∈ Finset.Ico 2 p, y ^ j / (j : F)) by ring]
  rw [hsum, truncatedLogSubFactor, ← Finset.sum_mul]
  ring

private theorem truncatedLogSubFactor_mem_one
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p : ℕ)
    (hchar : ringChar (ResidueField F) = p) {x y : F}
    (hx : x ∈ lattice F 1) (hy : y ∈ lattice F 1) :
    truncatedLogSubFactor F p x y - 1 ∈ lattice F 1 := by
  rw [truncatedLogSubFactor, add_sub_cancel_left]
  apply sum_mem_lattice F
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  have hcoeff : (j : F)⁻¹ ∈ lattice F 0 := by
    rw [mem_lattice, ord_inv, ord_natCast_eq_zero F p j hchar (by omega) (by omega)]
    simp
  simpa using mul_mem_lattice F hcoeff
    (powSubPowFactor_mem_lattice_one F hx hy hj'.1)

private theorem ord_truncatedLogSubFactor
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p : ℕ)
    (hchar : ringChar (ResidueField F) = p) {x y : F}
    (hx : x ∈ lattice F 1) (hy : y ∈ lattice F 1) :
    ord F (truncatedLogSubFactor F p x y) = 0 := by
  have hd := truncatedLogSubFactor_mem_one F p hchar hx hy
  have hgt : (0 : WithTop ℤ) < ord F (truncatedLogSubFactor F p x y - 1) :=
    lt_of_lt_of_le (by simp) hd
  have hne : ord F (truncatedLogSubFactor F p x y - 1) ≠ ord F 1 := by
    rw [ord_one]
    exact ne_of_gt hgt
  have h := ord_add_eq_min F hne
  rw [show truncatedLogSubFactor F p x y - 1 + 1 =
      truncatedLogSubFactor F p x y by ring] at h
  rw [ord_one, min_eq_right hgt.le] at h
  exact h

theorem ord_truncatedLog_sub
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p : ℕ)
    (hchar : ringChar (ResidueField F) = p) {x y : F}
    (hx : x ∈ lattice F 1) (hy : y ∈ lattice F 1) :
    ord F (truncatedLog p x - truncatedLog p y) = ord F (x - y) := by
  rw [truncatedLog_sub_eq_factor_mul, ord_mul,
    ord_truncatedLogSubFactor F p hchar hx hy, zero_add]

/-- The truncated logarithm, restricted to any positive valuation lattice. -/
noncomputable def truncatedLogOnLattice
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p r : ℕ)
    (hchar : ringChar (ResidueField F) = p) (hr : 1 ≤ r) :
    lattice F (r : ℤ) → lattice F (r : ℤ) := fun z =>
  ⟨truncatedLog p z, by
    have hz1 : (z : F) ∈ lattice F 1 :=
      lattice_antitone F (by exact_mod_cast hr) z.property
    rw [mem_lattice, ord_truncatedLog F p hchar hz1]
    exact z.property⟩

/-- Hensel's lemma makes the truncated logarithm a valuation-preserving bijection on every
positive lattice. -/
theorem truncatedLogOnLattice_bijective
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p r : ℕ)
    (hchar : ringChar (ResidueField F) = p) (hp : p.Prime) (hr : 1 ≤ r) :
    Function.Bijective (truncatedLogOnLattice F p r hchar hr) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hx1 : (x : F) ∈ lattice F 1 :=
      lattice_antitone F (by exact_mod_cast hr) x.property
    have hy1 : (y : F) ∈ lattice F 1 :=
      lattice_antitone F (by exact_mod_cast hr) y.property
    have hord := ord_truncatedLog_sub F p hchar hx1 hy1
    have hval : truncatedLog p (x : F) = truncatedLog p (y : F) :=
      congrArg Subtype.val hxy
    have htop : ord F ((x : F) - (y : F)) = ⊤ := by
      rw [← hord, hval, sub_self]
      exact (ord_eq_top_iff (F := F)).2 rfl
    exact sub_eq_zero.mp ((ord_eq_top_iff (F := F)).1 htop)
  · intro w
    have hw1 : (w : F) ∈ lattice F 1 :=
      lattice_antitone F (by exact_mod_cast hr) w.property
    obtain ⟨z, hz1, hz⟩ := exists_truncatedLog_eq F p hchar hp hw1
    have hzr : z ∈ lattice F (r : ℤ) := by
      rw [mem_lattice, ← ord_truncatedLog F p hchar hz1, hz]
      exact w.property
    exact ⟨⟨z, hzr⟩, Subtype.ext hz⟩

private theorem one_add_sum_Ico_pow_eq_geom {R : Type*} [Semiring R]
    (u : R) {p : ℕ} (hp : 2 ≤ p) :
    1 + ∑ j ∈ Finset.Ico 2 p, u ^ (j - 1) =
      ∑ k ∈ Finset.range (p - 1), u ^ k := by
  induction p, hp using Nat.le_induction with
  | base => simp
  | succ p hp ih =>
      rw [Finset.sum_Ico_succ_top hp]
      calc
        1 + (∑ j ∈ Finset.Ico 2 p, u ^ (j - 1) + u ^ (p - 1)) =
            (1 + ∑ j ∈ Finset.Ico 2 p, u ^ (j - 1)) + u ^ (p - 1) := by
              ac_rfl
        _ = (∑ k ∈ Finset.range (p - 1), u ^ k) + u ^ (p - 1) := by rw [ih]
        _ = ∑ k ∈ Finset.range (p + 1 - 1), u ^ k := by
          rw [show p + 1 - 1 = (p - 1) + 1 by omega, Finset.sum_range_succ]

private theorem pderiv_truncatedLogMvPolynomial
    (K : Type*) [Field K] (p : ℕ) (hp : 2 ≤ p)
    (hnz : ∀ j : ℕ, 0 < j → j < p → (j : K) ≠ 0)
    (i : Fin 2) (u : MvPolynomial (Fin 2) K) :
    MvPolynomial.pderiv i (truncatedLogMvPolynomial K p u) =
      (∑ k ∈ Finset.range (p - 1), u ^ k) * MvPolynomial.pderiv i u := by
  rw [truncatedLogMvPolynomial]
  simp only [map_add, map_sum, MvPolynomial.pderiv_C_mul,
    MvPolynomial.pderiv_pow]
  have hterm : ∀ j ∈ Finset.Ico 2 p,
      MvPolynomial.C (j : K)⁻¹ *
          ((j : MvPolynomial (Fin 2) K) * u ^ (j - 1) * MvPolynomial.pderiv i u) =
        u ^ (j - 1) * MvPolynomial.pderiv i u := by
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    change MvPolynomial.C (j : K)⁻¹ *
        (MvPolynomial.C (j : K) * u ^ (j - 1) * MvPolynomial.pderiv i u) = _
    rw [show MvPolynomial.C (j : K)⁻¹ *
        (MvPolynomial.C (j : K) * u ^ (j - 1) * MvPolynomial.pderiv i u) =
        (MvPolynomial.C (j : K)⁻¹ * MvPolynomial.C (j : K)) *
          (u ^ (j - 1) * MvPolynomial.pderiv i u) by ring,
      ← map_mul]
    rw [inv_mul_cancel₀ (hnz j (by omega) (by omega)), map_one, one_mul]
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_mul, ← one_add_sum_Ico_pow_eq_geom u hp]
  ring

private theorem pderiv_zero_truncatedLogDefectPolynomial
    (K : Type*) [Field K] (p : ℕ) (hp : 2 ≤ p)
    (hnz : ∀ j : ℕ, 0 < j → j < p → (j : K) ≠ 0) :
    MvPolynomial.pderiv (0 : Fin 2) (truncatedLogDefectPolynomial K p) =
      (∑ k ∈ Finset.range (p - 1),
          (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) -
            MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)) ^ k) *
        (1 - MvPolynomial.X (1 : Fin 2)) -
      ∑ k ∈ Finset.range (p - 1), MvPolynomial.X (0 : Fin 2) ^ k := by
  rw [truncatedLogDefectPolynomial]
  rw [map_sub, map_sub,
    pderiv_truncatedLogMvPolynomial K p hp hnz,
    pderiv_truncatedLogMvPolynomial K p hp hnz,
    pderiv_truncatedLogMvPolynomial K p hp hnz]
  simp

private theorem pderiv_one_truncatedLogDefectPolynomial
    (K : Type*) [Field K] (p : ℕ) (hp : 2 ≤ p)
    (hnz : ∀ j : ℕ, 0 < j → j < p → (j : K) ≠ 0) :
    MvPolynomial.pderiv (1 : Fin 2) (truncatedLogDefectPolynomial K p) =
      (∑ k ∈ Finset.range (p - 1),
          (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) -
            MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)) ^ k) *
        (1 - MvPolynomial.X (0 : Fin 2)) -
      ∑ k ∈ Finset.range (p - 1), MvPolynomial.X (1 : Fin 2) ^ k := by
  rw [truncatedLogDefectPolynomial]
  rw [map_sub, map_sub,
    pderiv_truncatedLogMvPolynomial K p hp hnz,
    pderiv_truncatedLogMvPolynomial K p hp hnz,
    pderiv_truncatedLogMvPolynomial K p hp hnz]
  simp

private theorem one_sub_X_mul_pderiv_zero_defect
    (K : Type*) [Field K] (p : ℕ) (hp : 2 ≤ p)
    (hnz : ∀ j : ℕ, 0 < j → j < p → (j : K) ≠ 0) :
    (1 - MvPolynomial.X (0 : Fin 2)) *
        MvPolynomial.pderiv (0 : Fin 2) (truncatedLogDefectPolynomial K p) =
      MvPolynomial.X (0 : Fin 2) ^ (p - 1) -
        (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) -
          MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)) ^ (p - 1) := by
  rw [pderiv_zero_truncatedLogDefectPolynomial K p hp hnz]
  let z : MvPolynomial (Fin 2) K := MvPolynomial.X 0
  let w : MvPolynomial (Fin 2) K := MvPolynomial.X 1
  let u : MvPolynomial (Fin 2) K := z + w - z * w
  change (1 - z) * ((∑ k ∈ Finset.range (p - 1), u ^ k) * (1 - w) -
      ∑ k ∈ Finset.range (p - 1), z ^ k) = z ^ (p - 1) - u ^ (p - 1)
  calc
    _ = (1 - u) * (∑ k ∈ Finset.range (p - 1), u ^ k) -
        (1 - z) * ∑ k ∈ Finset.range (p - 1), z ^ k := by
          rw [show 1 - u = (1 - z) * (1 - w) by simp [u]; ring]
          ring
    _ = (1 - u ^ (p - 1)) - (1 - z ^ (p - 1)) := by
          rw [mul_neg_geom_sum, mul_neg_geom_sum]
    _ = z ^ (p - 1) - u ^ (p - 1) := by ring

private theorem one_sub_X_mul_pderiv_one_defect
    (K : Type*) [Field K] (p : ℕ) (hp : 2 ≤ p)
    (hnz : ∀ j : ℕ, 0 < j → j < p → (j : K) ≠ 0) :
    (1 - MvPolynomial.X (1 : Fin 2)) *
        MvPolynomial.pderiv (1 : Fin 2) (truncatedLogDefectPolynomial K p) =
      MvPolynomial.X (1 : Fin 2) ^ (p - 1) -
        (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) -
          MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)) ^ (p - 1) := by
  rw [pderiv_one_truncatedLogDefectPolynomial K p hp hnz]
  let z : MvPolynomial (Fin 2) K := MvPolynomial.X 0
  let w : MvPolynomial (Fin 2) K := MvPolynomial.X 1
  let u : MvPolynomial (Fin 2) K := z + w - z * w
  change (1 - w) * ((∑ k ∈ Finset.range (p - 1), u ^ k) * (1 - z) -
      ∑ k ∈ Finset.range (p - 1), w ^ k) = w ^ (p - 1) - u ^ (p - 1)
  calc
    _ = (1 - u) * (∑ k ∈ Finset.range (p - 1), u ^ k) -
        (1 - w) * ∑ k ∈ Finset.range (p - 1), w ^ k := by
          rw [show 1 - u = (1 - z) * (1 - w) by simp [u]; ring]
          ring
    _ = (1 - u ^ (p - 1)) - (1 - w ^ (p - 1)) := by
          rw [mul_neg_geom_sum, mul_neg_geom_sum]
    _ = w ^ (p - 1) - u ^ (p - 1) := by ring

private theorem order_of_one_sub_mul_eq_pow_sub_pow
    {K σ : Type*} [Field K] (n : ℕ) (x u q : MvPowerSeries σ K)
    (hx : MvPowerSeries.constantCoeff x = 0)
    (hu : MvPowerSeries.constantCoeff u = 0)
    (h : (1 - x) * q = x ^ n - u ^ n) :
    (n : ℕ∞) ≤ MvPowerSeries.order q := by
  have hfac : MvPowerSeries.constantCoeff (1 - x) ≠ 0 := by simp [hx]
  have hq : q = (1 - x)⁻¹ * (x ^ n - u ^ n) := by
    calc
      q = 1 * q := by rw [one_mul]
      _ = ((1 - x)⁻¹ * (1 - x)) * q := by
        rw [MvPowerSeries.inv_mul_cancel (1 - x) hfac]
      _ = (1 - x)⁻¹ * ((1 - x) * q) := by ring
      _ = (1 - x)⁻¹ * (x ^ n - u ^ n) := by rw [h]
  have hxpow : (n : ℕ∞) ≤ MvPowerSeries.order (x ^ n) :=
    MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero n hx
  have hupow : (n : ℕ∞) ≤ MvPowerSeries.order (u ^ n) :=
    MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero n hu
  have hrhs : (n : ℕ∞) ≤ MvPowerSeries.order (x ^ n - u ^ n) := by
    rw [sub_eq_add_neg]
    exact le_trans (le_min hxpow (by simpa using hupow))
      (MvPowerSeries.min_order_le_add (f := x ^ n) (g := -(u ^ n)))
  rw [hq]
  have hadd : (n : ℕ∞) ≤ MvPowerSeries.order ((1 - x)⁻¹) +
      MvPowerSeries.order (x ^ n - u ^ n) := by
    calc
      (n : ℕ∞) = 0 + n := by simp
      _ ≤ MvPowerSeries.order ((1 - x)⁻¹) +
          MvPowerSeries.order (x ^ n - u ^ n) := add_le_add (by simp) hrhs
  exact le_trans hadd MvPowerSeries.le_order_mul

@[simp] private theorem coe_sub_mvPolynomial {K σ : Type*} [CommRing K]
    (a b : MvPolynomial σ K) :
    ((a - b : MvPolynomial σ K) : MvPowerSeries σ K) =
      (a : MvPowerSeries σ K) - (b : MvPowerSeries σ K) := by
  change MvPolynomial.coeToMvPowerSeries.ringHom (a - b) = _
  rw [map_sub]
  rfl

private theorem order_pderiv_truncatedLogDefectPolynomial
    (K : Type*) [Field K] (p : ℕ) (hp : 2 ≤ p)
    (hnz : ∀ j : ℕ, 0 < j → j < p → (j : K) ≠ 0) (i : Fin 2) :
    (p - 1 : ℕ) ≤ MvPowerSeries.order
      ((MvPolynomial.pderiv i (truncatedLogDefectPolynomial K p) :
        MvPolynomial (Fin 2) K) : MvPowerSeries (Fin 2) K) := by
  fin_cases i
  · apply order_of_one_sub_mul_eq_pow_sub_pow (p - 1)
      (MvPowerSeries.X (0 : Fin 2))
      (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2) -
        MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2)) _
    · simp
    · simp
    · simpa using congrArg MvPolynomial.coeToMvPowerSeries.ringHom
        (one_sub_X_mul_pderiv_zero_defect K p hp hnz)
  · apply order_of_one_sub_mul_eq_pow_sub_pow (p - 1)
      (MvPowerSeries.X (1 : Fin 2))
      (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2) -
        MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2)) _
    · simp
    · simp
    · simpa using congrArg MvPolynomial.coeToMvPowerSeries.ringHom
        (one_sub_X_mul_pderiv_one_defect K p hp hnz)

/-- Every monomial in the truncated-log defect has total degree at least `p`. -/
theorem coeff_truncatedLogDefectPolynomial_eq_zero
    (K : Type*) [Field K] (p : ℕ) (hp : 2 ≤ p)
    (hnz : ∀ j : ℕ, 0 < j → j < p → (j : K) ≠ 0)
    (d : Fin 2 →₀ ℕ) (hd : d.degree < p) :
    MvPolynomial.coeff d (truncatedLogDefectPolynomial K p) = 0 := by
  have hpositive (i : Fin 2) (hi : d i ≠ 0) :
      MvPolynomial.coeff d (truncatedLogDefectPolynomial K p) = 0 := by
    let m : Fin 2 →₀ ℕ := d - Finsupp.single i 1
    have hmdeg : m.degree + 1 = d.degree := by
      have hw := Finsupp.weight_sub_single_add (w := fun _ : Fin 2 => 1) hi
      simpa only [← Finsupp.degree_eq_weight_one] using hw
    have hmlt : m.degree < p - 1 := by omega
    have horder := order_pderiv_truncatedLogDefectPolynomial K p hp hnz i
    have hcoeffPS : MvPowerSeries.coeff m
        ((MvPolynomial.pderiv i (truncatedLogDefectPolynomial K p) :
          MvPolynomial (Fin 2) K) : MvPowerSeries (Fin 2) K) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      exact lt_of_lt_of_le (by exact_mod_cast hmlt) horder
    have hcoeff : MvPolynomial.coeff m
        (MvPolynomial.pderiv i (truncatedLogDefectPolynomial K p)) = 0 := by
      exact hcoeffPS
    rw [MvPolynomial.coeff_pderiv] at hcoeff
    have hmd : m + Finsupp.single i 1 = d :=
      Finsupp.sub_add_single_one_cancel hi
    rw [hmd] at hcoeff
    have hmi : m i + 1 = d i := by
      have hi' := congrArg (fun e : Fin 2 →₀ ℕ => e i) hmd
      simpa using hi'
    have hmiK : (m i : K) + 1 = (d i : K) := by
      simpa using congrArg (fun n : ℕ => (n : K)) hmi
    rw [hmiK] at hcoeff
    exact (mul_eq_zero.mp hcoeff).resolve_right
      (hnz (d i) (Nat.pos_of_ne_zero hi)
        (lt_of_le_of_lt (Finsupp.le_degree i d) hd))
  by_cases hzero : d (0 : Fin 2) = 0
  · by_cases hone : d (1 : Fin 2) = 0
    · have hd0 : d = 0 := by
        ext i
        fin_cases i <;> simp [hzero, hone]
      subst d
      have hs : (∑ j ∈ Finset.Ico 2 p, (j : K)⁻¹ * (0 : K) ^ j) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [zero_pow (Nat.ne_of_gt (lt_of_lt_of_le (by omega) (Finset.mem_Ico.mp hj).1)),
          mul_zero]
      rw [← MvPolynomial.constantCoeff_eq, ← MvPolynomial.eval_zero]
      simp only [truncatedLogDefectPolynomial, truncatedLogMvPolynomial,
        map_sub, map_add, map_mul, MvPolynomial.eval_X, map_sum, map_pow,
        MvPolynomial.eval_C, Pi.zero_apply, zero_add, zero_mul, sub_zero]
      rw [hs]
      ring
    · exact hpositive 1 hone
  · exact hpositive 0 hzero

private def truncatedLogIntegralMvPolynomial
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p : ℕ)
    (hchar : ringChar (ResidueField F) = p)
    (z : MvPolynomial (Fin 2) (ringOfIntegers F)) :
    MvPolynomial (Fin 2) (ringOfIntegers F) :=
  z + ∑ j ∈ Finset.Ico 2 p,
    MvPolynomial.C (truncatedLogIntegerCoefficient F p hchar j) * z ^ j

private theorem map_truncatedLogIntegralMvPolynomial
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p : ℕ)
    (hchar : ringChar (ResidueField F) = p)
    (z : MvPolynomial (Fin 2) (ringOfIntegers F)) :
    MvPolynomial.map (ValuativeRel.valuation F).integer.subtype
        (truncatedLogIntegralMvPolynomial F p hchar z) =
      truncatedLogMvPolynomial F p
        (MvPolynomial.map (ValuativeRel.valuation F).integer.subtype z) := by
  simp [truncatedLogIntegralMvPolynomial, truncatedLogMvPolynomial]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coe_truncatedLogIntegerCoefficient F p hchar j (by
    have hj' := Finset.mem_Ico.mp hj
    omega)]

private def truncatedLogIntegralDefectPolynomial
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p : ℕ)
    (hchar : ringChar (ResidueField F) = p) :
    MvPolynomial (Fin 2) (ringOfIntegers F) :=
  let z := MvPolynomial.X (0 : Fin 2)
  let w := MvPolynomial.X (1 : Fin 2)
  truncatedLogIntegralMvPolynomial F p hchar (z + w - z * w) -
    truncatedLogIntegralMvPolynomial F p hchar z -
      truncatedLogIntegralMvPolynomial F p hchar w

private theorem map_truncatedLogIntegralDefectPolynomial
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p : ℕ)
    (hchar : ringChar (ResidueField F) = p) :
    MvPolynomial.map (ValuativeRel.valuation F).integer.subtype
        (truncatedLogIntegralDefectPolynomial F p hchar) =
      truncatedLogDefectPolynomial F p := by
  simp [truncatedLogIntegralDefectPolynomial, truncatedLogDefectPolynomial,
    map_truncatedLogIntegralMvPolynomial]

theorem eval_truncatedLogMvPolynomial
    (K : Type*) [Field K] (p : ℕ) (z : MvPolynomial (Fin 2) K)
    (a : Fin 2 → K) :
    MvPolynomial.eval a (truncatedLogMvPolynomial K p z) =
      truncatedLog p (MvPolynomial.eval a z) := by
  simp [truncatedLogMvPolynomial, truncatedLog_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [div_eq_mul_inv]
  ring

/-- Evaluation identifies the formal defect with the actual truncated-log error. -/
theorem eval_truncatedLogDefectPolynomial
    (K : Type*) [Field K] (p : ℕ) (z w : K) :
    MvPolynomial.eval ![z, w] (truncatedLogDefectPolynomial K p) =
      truncatedLog p (z + w - z * w) - truncatedLog p z - truncatedLog p w := by
  simp [truncatedLogDefectPolynomial, eval_truncatedLogMvPolynomial]

private theorem pow_mem_lattice_nat
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {x : F} {r : ℕ}
    (hx : x ∈ lattice F (r : ℤ)) (n : ℕ) :
    x ^ n ∈ lattice F ((n * r : ℕ) : ℤ) := by
  rw [mem_lattice, ord_pow]
  have h := nsmul_le_nsmul_right
    (show ((r : ℤ) : WithTop ℤ) ≤ ord F x from hx) n
  calc
    ((((n * r : ℕ) : ℤ) : WithTop ℤ)) =
        (((n • (r : ℤ) : ℤ) : WithTop ℤ)) := by
          congr
    _ = n • (((r : ℤ) : WithTop ℤ)) := by rw [WithTop.coe_nsmul]
    _ ≤ n • ord F x := h

private theorem eval₂_mem_lattice_of_support_degree
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p r : ℕ)
    (Q : MvPolynomial (Fin 2) (ringOfIntegers F))
    (hdegree : ∀ d ∈ Q.support, p ≤ d.degree)
    (a : Fin 2 → F) (ha : ∀ i, a i ∈ lattice F (r : ℤ)) :
    MvPolynomial.eval₂ (ValuativeRel.valuation F).integer.subtype a Q ∈
      lattice F ((p * r : ℕ) : ℤ) := by
  rw [Q.as_sum, MvPolynomial.eval₂_sum]
  apply sum_mem_lattice F
  intro d hd
  rw [MvPolynomial.eval₂_monomial]
  have hc : ((Q.coeff d : ringOfIntegers F) : F) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (Q.coeff d).property
  have hpow0 := pow_mem_lattice_nat F (ha 0) (d 0)
  have hpow1 := pow_mem_lattice_nat F (ha 1) (d 1)
  have hprod : d.prod (fun i e => a i ^ e) = a 0 ^ d 0 * a 1 ^ d 1 := by
    rw [Finsupp.prod_fintype d _ (by simp), Fin.prod_univ_two]
  rw [hprod]
  have hterm := mul_mem_lattice F (mul_mem_lattice F hc hpow0) hpow1
  have hdepth : (0 : ℤ) + (d 0 * r : ℕ) + (d 1 * r : ℕ) =
      ((d.degree * r : ℕ) : ℤ) := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
    push_cast
    ring
  have hterm' : ((Q.coeff d : ringOfIntegers F) : F) *
      (a 0 ^ d 0 * a 1 ^ d 1) ∈ lattice F ((d.degree * r : ℕ) : ℤ) := by
    simpa only [mul_assoc, hdepth] using hterm
  exact lattice_antitone F (by
    exact_mod_cast Nat.mul_le_mul_right r (hdegree d hd)) hterm'

private theorem natCast_ne_zero_of_residueCharacteristic
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p j : ℕ)
    (hchar : ringChar (ResidueField F) = p)
    (hjpos : 0 < j) (hjlt : j < p) : (j : F) ≠ 0 := by
  intro hj
  have hord := ord_natCast_eq_zero F p j hchar hjpos hjlt
  rw [hj, ord_zero] at hord
  exact WithTop.top_ne_coe hord

private theorem support_degree_truncatedLogIntegralDefectPolynomial
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p : ℕ)
    (hchar : ringChar (ResidueField F) = p) (hp : p.Prime) :
    ∀ d ∈ (truncatedLogIntegralDefectPolynomial F p hchar).support,
      p ≤ d.degree := by
  intro d hd
  by_contra hdegree
  have hzero := coeff_truncatedLogDefectPolynomial_eq_zero F p hp.two_le
    (fun j hjpos hjlt =>
      natCast_ne_zero_of_residueCharacteristic F p j hchar hjpos hjlt)
    d (Nat.lt_of_not_ge hdegree)
  have hmap := congrArg (MvPolynomial.coeff d)
    (map_truncatedLogIntegralDefectPolynomial F p hchar)
  simp only [MvPolynomial.coeff_map] at hmap
  have hcoe : ((MvPolynomial.coeff d
      (truncatedLogIntegralDefectPolynomial F p hchar) : ringOfIntegers F) : F) = 0 := by
    change (ValuativeRel.valuation F).integer.subtype (MvPolynomial.coeff d
      (truncatedLogIntegralDefectPolynomial F p hchar)) = 0
    rw [hmap, hzero]
  have hcoeff : MvPolynomial.coeff d
      (truncatedLogIntegralDefectPolynomial F p hchar) = 0 := by
    exact Subtype.ext hcoe
  exact (MvPolynomial.mem_support_iff.mp hd) hcoeff

/-- At depth `r`, the truncated logarithm is additive for the multiplicative coordinate
`z + w - zw` modulo depth `p*r`. -/
theorem truncatedLog_defect_mem_lattice
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p r : ℕ)
    (hchar : ringChar (ResidueField F) = p) (hp : p.Prime)
    {z w : F} (hz : z ∈ lattice F (r : ℤ)) (hw : w ∈ lattice F (r : ℤ)) :
    truncatedLog p (z + w - z * w) - truncatedLog p z - truncatedLog p w ∈
      lattice F ((p * r : ℕ) : ℤ) := by
  have heval := eval₂_mem_lattice_of_support_degree F p r
    (truncatedLogIntegralDefectPolynomial F p hchar)
    (support_degree_truncatedLogIntegralDefectPolynomial F p hchar hp) ![z, w] (by
      intro i
      fin_cases i
      · exact hz
      · exact hw)
  rw [← eval_truncatedLogDefectPolynomial F p z w,
    ← map_truncatedLogIntegralDefectPolynomial F p hchar,
    MvPolynomial.eval_map]
  exact heval

private noncomputable def truncatedLogNegLatticeQuotientMap
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p r M : ℕ)
    (hchar : ringChar (ResidueField F) = p) (hr : 1 ≤ r) (hrM : r ≤ M) :
    LatticeQuotient F (r : ℤ) (M : ℤ) (by exact_mod_cast hrM) →
      LatticeQuotient F (r : ℤ) (M : ℤ) (by exact_mod_cast hrM) := by
  let hZ : (r : ℤ) ≤ (M : ℤ) := by exact_mod_cast hrM
  exact Quotient.lift
    (fun x => latticeQuotientMk F hZ
      (truncatedLogOnLattice F p r hchar hr (-x)))
    (by
      intro x y hxy
      apply (latticeQuotientMk_eq_mk_iff F hZ).2
      have hxyInside : x - y ∈ latticeInside F hZ :=
        (Submodule.quotientRel_def (latticeInside F hZ)).1 hxy
      have hxyM : (x : F) - (y : F) ∈ lattice F (M : ℤ) :=
        (mem_latticeInside F hZ).1 hxyInside
      have hx1 : (-(x : F)) ∈ lattice F 1 := neg_mem_lattice F
        (lattice_antitone F (by exact_mod_cast hr) x.property)
      have hy1 : (-(y : F)) ∈ lattice F 1 := neg_mem_lattice F
        (lattice_antitone F (by exact_mod_cast hr) y.property)
      rw [mem_lattice] at hxyM ⊢
      change ((M : ℤ) : WithTop ℤ) ≤
        ord F (truncatedLog p (-(x : F)) - truncatedLog p (-(y : F)))
      rw [ord_truncatedLog_sub F p hchar hx1 hy1]
      rw [show (-(x : F)) - (-(y : F)) = -((x : F) - (y : F)) by ring,
        ord_neg]
      exact hxyM)

@[simp] private theorem truncatedLogNegLatticeQuotientMap_mk
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p r M : ℕ)
    (hchar : ringChar (ResidueField F) = p) (hr : 1 ≤ r) (hrM : r ≤ M)
    (x : lattice F (r : ℤ)) :
    truncatedLogNegLatticeQuotientMap F p r M hchar hr hrM
        (latticeQuotientMk F (by exact_mod_cast hrM) x) =
      latticeQuotientMk F (by exact_mod_cast hrM)
        (truncatedLogOnLattice F p r hchar hr (-x)) := rfl

private theorem truncatedLogNegLatticeQuotientMap_bijective
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p r M : ℕ)
    (hchar : ringChar (ResidueField F) = p) (hp : p.Prime)
    (hr : 1 ≤ r) (hrM : r ≤ M) :
    Function.Bijective
      (truncatedLogNegLatticeQuotientMap F p r M hchar hr hrM) := by
  let hZ : (r : ℤ) ≤ (M : ℤ) := by exact_mod_cast hrM
  constructor
  · intro q₁ q₂ hq
    obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective F hZ q₁
    obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective F hZ q₂
    rw [truncatedLogNegLatticeQuotientMap_mk,
      truncatedLogNegLatticeQuotientMap_mk] at hq
    apply (latticeQuotientMk_eq_mk_iff F hZ).2
    have hout := (latticeQuotientMk_eq_mk_iff F hZ).1 hq
    have hx1 : (-(x : F)) ∈ lattice F 1 := neg_mem_lattice F
      (lattice_antitone F (by exact_mod_cast hr) x.property)
    have hy1 : (-(y : F)) ∈ lattice F 1 := neg_mem_lattice F
      (lattice_antitone F (by exact_mod_cast hr) y.property)
    rw [mem_lattice] at hout ⊢
    change ((M : ℤ) : WithTop ℤ) ≤
      ord F (truncatedLog p (-(x : F)) - truncatedLog p (-(y : F))) at hout
    rw [ord_truncatedLog_sub F p hchar hx1 hy1] at hout
    rw [show (-(x : F)) - (-(y : F)) = -((x : F) - (y : F)) by ring,
      ord_neg] at hout
    exact hout
  · intro q
    obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective F hZ q
    obtain ⟨z, hz⟩ := (truncatedLogOnLattice_bijective F p r hchar hp hr).2 y
    refine ⟨latticeQuotientMk F hZ (-z), ?_⟩
    rw [truncatedLogNegLatticeQuotientMap_mk]
    have hzval := congrArg Subtype.val hz
    simpa using congrArg (latticeQuotientMk F hZ) hz

private noncomputable def truncatedLogNegLatticeQuotientEquiv
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p r M : ℕ)
    (hchar : ringChar (ResidueField F) = p) (hp : p.Prime)
    (hr : 1 ≤ r) (hrM : r ≤ M) :
    LatticeQuotient F (r : ℤ) (M : ℤ) (by exact_mod_cast hrM) ≃
      LatticeQuotient F (r : ℤ) (M : ℤ) (by exact_mod_cast hrM) :=
  Equiv.ofBijective (truncatedLogNegLatticeQuotientMap F p r M hchar hr hrM)
    (truncatedLogNegLatticeQuotientMap_bijective F p r M hchar hp hr hrM)

@[simp] private theorem truncatedLogNegLatticeQuotientEquiv_mk
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p r M : ℕ)
    (hchar : ringChar (ResidueField F) = p) (hp : p.Prime)
    (hr : 1 ≤ r) (hrM : r ≤ M) (x : lattice F (r : ℤ)) :
    truncatedLogNegLatticeQuotientEquiv F p r M hchar hp hr hrM
        (latticeQuotientMk F (by exact_mod_cast hrM) x) =
      latticeQuotientMk F (by exact_mod_cast hrM)
        (truncatedLogOnLattice F p r hchar hr (-x)) := rfl

/-- The additive coordinate `1 - u` of a principal unit `u`. -/
noncomputable def truncatedLogUnitArgument
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {r : ℕ} (hr : 0 < r)
    (u : unitFiltration F r) : lattice F (r : ℤ) :=
  -positiveUnitDisplacement F hr u

@[simp] theorem coe_truncatedLogUnitArgument
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {r : ℕ} (hr : 0 < r)
    (u : unitFiltration F r) :
    (truncatedLogUnitArgument F hr u : F) = 1 - ((u : Fˣ) : F) := by
  simp [truncatedLogUnitArgument]

/-- The truncated logarithm chart
`[u] ↦ [P(1-u)]` from a positive unit-filtration quotient to its additive
lattice quotient.  The hypothesis `M ≤ p * r` is exactly what kills the
formal-group defect modulo the target lattice. -/
noncomputable def truncatedLogQuotientMulEquiv
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p r M : ℕ)
    (hchar : ringChar (ResidueField F) = p) (hp : p.Prime)
    (hr : 1 ≤ r) (hrM : r ≤ M) (hM : M ≤ p * r) :
    UnitFiltrationQuotient F r M hrM ≃*
      Multiplicative
        (LatticeQuotient F (r : ℤ) (M : ℤ) (by exact_mod_cast hrM)) where
  toEquiv :=
    ((positiveUnitFiltrationQuotientEquivLattice F (by omega) hrM).trans
      (truncatedLogNegLatticeQuotientEquiv F p r M hchar hp hr hrM)).trans
        Multiplicative.ofAdd
  map_mul' := by
    let hZ : (r : ℤ) ≤ (M : ℤ) := by exact_mod_cast hrM
    intro q₁ q₂
    induction q₁ using Quotient.inductionOn with
    | _ u =>
      induction q₂ using Quotient.inductionOn with
      | _ v =>
        change
          latticeQuotientMk F hZ
              (truncatedLogOnLattice F p r hchar hr
                (truncatedLogUnitArgument F (by omega) (u * v))) =
            latticeQuotientMk F hZ
                (truncatedLogOnLattice F p r hchar hr
                  (truncatedLogUnitArgument F (by omega) u)) +
              latticeQuotientMk F hZ
                (truncatedLogOnLattice F p r hchar hr
                  (truncatedLogUnitArgument F (by omega) v))
        rw [← map_add]
        apply (latticeQuotientMk_eq_mk_iff F hZ).2
        let z : F := truncatedLogUnitArgument F (by omega) u
        let w : F := truncatedLogUnitArgument F (by omega) v
        have hz : z ∈ lattice F (r : ℤ) :=
          (truncatedLogUnitArgument F (by omega) u).property
        have hw : w ∈ lattice F (r : ℤ) :=
          (truncatedLogUnitArgument F (by omega) v).property
        have hdefect :=
          truncatedLog_defect_mem_lattice F p r hchar hp hz hw
        have hdeep :
            truncatedLog p (z + w - z * w) -
                truncatedLog p z - truncatedLog p w ∈ lattice F (M : ℤ) :=
          lattice_antitone F (by exact_mod_cast hM) hdefect
        change
          truncatedLog p
                (truncatedLogUnitArgument F (by omega) (u * v) : F) -
              (truncatedLog p z + truncatedLog p w) ∈
            lattice F (M : ℤ)
        rw [show
          (truncatedLogUnitArgument F (by omega) (u * v) : F) =
              z + w - z * w by
            simp only [coe_truncatedLogUnitArgument, Subgroup.coe_mul,
              Units.val_mul]
            simp only [z, w, coe_truncatedLogUnitArgument]
            ring]
        simpa only [sub_add_eq_sub_sub] using hdeep

@[simp] theorem truncatedLogQuotientMulEquiv_mk
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p r M : ℕ)
    (hchar : ringChar (ResidueField F) = p) (hp : p.Prime)
    (hr : 1 ≤ r) (hrM : r ≤ M) (hM : M ≤ p * r)
    (u : unitFiltration F r) :
    truncatedLogQuotientMulEquiv F p r M hchar hp hr hrM hM
        (unitFiltrationQuotientMk F hrM u) =
      Multiplicative.ofAdd
        (latticeQuotientMk F (by exact_mod_cast hrM)
          (truncatedLogOnLattice F p r hchar hr
            (truncatedLogUnitArgument F (by omega) u))) := rfl

/-- Representative form of `truncatedLogQuotientMulEquiv`: the class of
`1 - z` is sent to the class of `P(z)`. -/
@[simp] theorem truncatedLogQuotientMulEquiv_one_sub
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p r M : ℕ)
    (hchar : ringChar (ResidueField F) = p) (hp : p.Prime)
    (hr : 1 ≤ r) (hrM : r ≤ M) (hM : M ≤ p * r)
    (z : lattice F (r : ℤ)) :
    truncatedLogQuotientMulEquiv F p r M hchar hp hr hrM hM
        (unitFiltrationQuotientMk F hrM
          (positiveUnitOfLattice F (by omega) (-z))) =
      Multiplicative.ofAdd
        (latticeQuotientMk F (by exact_mod_cast hrM)
          (truncatedLogOnLattice F p r hchar hr z)) := by
  rw [truncatedLogQuotientMulEquiv_mk]
  congr 3
  ext
  simp [truncatedLogUnitArgument]

end
end LanglandsSecondMainLemma.Odd
