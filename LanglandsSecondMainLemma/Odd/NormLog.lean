import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.TruncatedLog
import LanglandsSecondMainLemma.Local.TraceIdeals
import Mathlib.Algebra.CharP.Quotient
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Odd / Norm Log

This is the full trace--norm logarithm identity of Paper Lemma 6.3
(`O:I:normlog`).  The proof expands the universal defect in variables indexed
by the Galois group.  Its monomials have total degree at least the prime
degree.  Under cyclic translation, every nonconstant exponent vector has a
free orbit; its specialization is a field trace and hence receives the exact
trace-ideal bound.  A fixed exponent vector is constant, so its specialization
is a power of the norm.  Reduction modulo the degree shows that the
coefficient of every such fixed monomial is divisible by the degree; this is
the cancellation of the single weight-`p` norm term in the paper.

The unramified assertion is proved independently from the same universal
expansion.  It does not use the ramified conclusion.
-/

namespace LanglandsSecondMainLemma.Odd

open LanglandsFirstMainLemma
open scoped BigOperators Ring ValuativeRel

noncomputable section

private noncomputable def normLogCoefficient
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) (hchar : residueCharacteristic F = p) (j : ℕ) :
    ringOfIntegers F :=
  if h : 0 < j ∧ j < p then
    ⟨(j : F)⁻¹, (ord_nonneg_iff_mem_integer F _).1 (by
      rw [ord_inv,
        ord_natCast_eq_zero_of_lt_residueCharacteristic F h.1 (hchar.symm ▸ h.2)]
      simp)⟩
  else 0

@[simp] private theorem coe_normLogCoefficient
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) (hchar : residueCharacteristic F = p) (j : ℕ)
    (hj : 0 < j) (hjp : j < p) :
    (normLogCoefficient F p hchar j : F) = (j : F)⁻¹ := by
  simp [normLogCoefficient, hj, hjp]

private def integralTruncatedLogMv
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {σ : Type*} (p : ℕ) (hchar : residueCharacteristic F = p)
    (x : MvPolynomial σ (ringOfIntegers F)) :
    MvPolynomial σ (ringOfIntegers F) :=
  ∑ j ∈ Finset.Ico 1 p,
    MvPolynomial.C (normLogCoefficient F p hchar j) * x ^ j

private def fieldTruncatedLogMv
    (K : Type*) [Field K] {σ : Type*} (p : ℕ)
    (x : MvPolynomial σ K) : MvPolynomial σ K :=
  x + ∑ j ∈ Finset.Ico 2 p, MvPolynomial.C (j : K)⁻¹ * x ^ j

private def universalNormArgument
    (R σ : Type*) [CommRing R] [Fintype σ] : MvPolynomial σ R :=
  1 - ∏ i : σ, (1 - MvPolynomial.X i)

private def integralUniversalNormLogDefect
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (σ : Type*) [Fintype σ]
    (p : ℕ) (hchar : residueCharacteristic F = p) :
    MvPolynomial σ (ringOfIntegers F) :=
  integralTruncatedLogMv F p hchar
      (universalNormArgument (ringOfIntegers F) σ) -
    ∑ i : σ, integralTruncatedLogMv F p hchar (MvPolynomial.X i) -
    ∏ i : σ, integralTruncatedLogMv F p hchar (MvPolynomial.X i)

private def integralUniversalLogDefectWithoutNorm
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (σ : Type*) [Fintype σ]
    (p : ℕ) (hchar : residueCharacteristic F = p) :
    MvPolynomial σ (ringOfIntegers F) :=
  integralTruncatedLogMv F p hchar
      (universalNormArgument (ringOfIntegers F) σ) -
    ∑ i : σ, integralTruncatedLogMv F p hchar (MvPolynomial.X i)

private def universalNormLogDefect
    (K σ : Type*) [Field K] [Fintype σ] (p : ℕ) :
    MvPolynomial σ K :=
  fieldTruncatedLogMv K p (universalNormArgument K σ) -
    ∑ i : σ, fieldTruncatedLogMv K p (MvPolynomial.X i) -
    ∏ i : σ, fieldTruncatedLogMv K p (MvPolynomial.X i)

private def universalLogDefectWithoutNorm
    (K σ : Type*) [Field K] [Fintype σ] (p : ℕ) :
    MvPolynomial σ K :=
  fieldTruncatedLogMv K p (universalNormArgument K σ) -
    ∑ i : σ, fieldTruncatedLogMv K p (MvPolynomial.X i)

private theorem eval_integralTruncatedLogMv
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {σ : Type*} (p : ℕ) (hchar : residueCharacteristic F = p) (hp : 2 ≤ p)
    (a : σ → F) (x : MvPolynomial σ (ringOfIntegers F)) :
    MvPolynomial.eval₂ (ValuativeRel.valuation F).integer.subtype a
        (integralTruncatedLogMv F p hchar x) =
      truncatedLog p
        (MvPolynomial.eval₂ (ValuativeRel.valuation F).integer.subtype a x) := by
  rw [integralTruncatedLogMv, truncatedLog_apply]
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow]
  rw [show Finset.Ico 1 p = insert 1 (Finset.Ico 2 p) by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega]
  rw [Finset.sum_insert (by simp)]
  have hc1 : (ValuativeRel.valuation F).integer.subtype
      (normLogCoefficient F p hchar 1) = 1 := by
    simpa using coe_normLogCoefficient F p hchar 1 (by omega) (by omega)
  rw [hc1]
  simp only [one_mul, pow_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  have hcj : (ValuativeRel.valuation F).integer.subtype
      (normLogCoefficient F p hchar j) = (j : F)⁻¹ := by
    simpa using coe_normLogCoefficient F p hchar j (by omega) hj'.2
  rw [hcj]
  ring

private theorem eval_integralTruncatedLogMv_extension
    (F K : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [Algebra F K]
    {σ : Type*} (p : ℕ) (hchar : residueCharacteristic F = p) (hp : 2 ≤ p)
    (a : σ → K) (x : MvPolynomial σ (ringOfIntegers F)) :
    MvPolynomial.eval₂
        ((algebraMap F K).comp (ValuativeRel.valuation F).integer.subtype) a
        (integralTruncatedLogMv F p hchar x) =
      truncatedLog p
        (MvPolynomial.eval₂
          ((algebraMap F K).comp (ValuativeRel.valuation F).integer.subtype) a x) := by
  rw [integralTruncatedLogMv, truncatedLog_apply]
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow]
  rw [show Finset.Ico 1 p = insert 1 (Finset.Ico 2 p) by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega]
  rw [Finset.sum_insert (by simp)]
  have hc1 : ((algebraMap F K).comp
      (ValuativeRel.valuation F).integer.subtype)
      (normLogCoefficient F p hchar 1) = 1 := by
    change algebraMap F K (normLogCoefficient F p hchar 1 : F) = 1
    rw [coe_normLogCoefficient F p hchar 1 (by omega) (by omega)]
    simp
  rw [hc1]
  simp only [one_mul, pow_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  have hcj : ((algebraMap F K).comp
      (ValuativeRel.valuation F).integer.subtype)
      (normLogCoefficient F p hchar j) = (j : K)⁻¹ := by
    change algebraMap F K (normLogCoefficient F p hchar j : F) = (j : K)⁻¹
    rw [coe_normLogCoefficient F p hchar j (by omega) hj'.2]
    simp
  rw [hcj]
  ring

private theorem eval_universalNormArgument
    (R S σ : Type*) [CommRing R] [CommRing S] [Fintype σ]
    (f : R →+* S) (a : σ → S) :
    MvPolynomial.eval₂ f a (universalNormArgument R σ) =
      1 - ∏ i : σ, (1 - a i) := by
  simp [universalNormArgument]

private theorem map_integralTruncatedLogMv
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {σ : Type*} (p : ℕ) (hchar : residueCharacteristic F = p) (hp : 2 ≤ p)
    (x : MvPolynomial σ (ringOfIntegers F)) :
    MvPolynomial.map (ValuativeRel.valuation F).integer.subtype
        (integralTruncatedLogMv F p hchar x) =
      fieldTruncatedLogMv F p
        (MvPolynomial.map (ValuativeRel.valuation F).integer.subtype x) := by
  rw [integralTruncatedLogMv, fieldTruncatedLogMv]
  simp only [map_sum, map_mul, MvPolynomial.map_C, map_pow]
  rw [show Finset.Ico 1 p = insert 1 (Finset.Ico 2 p) by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega]
  rw [Finset.sum_insert (by simp)]
  have hc1 : (ValuativeRel.valuation F).integer.subtype
      (normLogCoefficient F p hchar 1) = 1 := by
    simpa using coe_normLogCoefficient F p hchar 1 (by omega) (by omega)
  rw [hc1]
  simp only [map_one, one_mul, pow_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  have hcj : (ValuativeRel.valuation F).integer.subtype
      (normLogCoefficient F p hchar j) = (j : F)⁻¹ := by
    simpa using coe_normLogCoefficient F p hchar j (by omega) hj'.2
  rw [hcj]

private theorem map_integralUniversalNormLogDefect
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (σ : Type*) [Fintype σ]
    (p : ℕ) (hchar : residueCharacteristic F = p) (hp : 2 ≤ p) :
    MvPolynomial.map (ValuativeRel.valuation F).integer.subtype
        (integralUniversalNormLogDefect F σ p hchar) =
      universalNormLogDefect F σ p := by
  rw [integralUniversalNormLogDefect, universalNormLogDefect]
  simp only [map_sub, map_sum, map_prod]
  simp_rw [map_integralTruncatedLogMv F p hchar hp]
  simp [universalNormArgument]

private theorem pderiv_universalNormArgument
    (K σ : Type*) [Field K] [Fintype σ] [DecidableEq σ] (i : σ) :
    MvPolynomial.pderiv i (universalNormArgument K σ) =
      ∏ j ∈ (Finset.univ.erase i), (1 - MvPolynomial.X j) := by
  have hzero (s : Finset σ) (his : i ∉ s) :
      MvPolynomial.pderiv i
          (∏ j ∈ s, (1 - MvPolynomial.X j : MvPolynomial σ K)) = 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hjs ih =>
        have hji : j ≠ i := by
          intro h
          subst j
          exact his (Finset.mem_insert_self i s)
        have his' : i ∉ s := fun hi ↦ his (Finset.mem_insert_of_mem hi)
        rw [Finset.prod_insert hjs, MvPolynomial.pderiv_mul, ih his', mul_zero,
          add_zero]
        have hjzero : MvPolynomial.pderiv i
            (1 - MvPolynomial.X j : MvPolynomial σ K) = 0 := by
          rw [map_sub, MvPolynomial.pderiv_one,
            MvPolynomial.pderiv_X_of_ne hji]
          simp
        rw [hjzero, zero_mul]
  rw [universalNormArgument]
  rw [← Finset.mul_prod_erase (s := Finset.univ)
    (f := fun j : σ ↦ (1 - MvPolynomial.X j : MvPolynomial σ K)) (Finset.mem_univ i)]
  have hrest : MvPolynomial.pderiv i
      (∏ j ∈ Finset.univ.erase i, (1 - MvPolynomial.X j : MvPolynomial σ K)) = 0 :=
    hzero _ (by simp)
  have hself : MvPolynomial.pderiv i
      (1 - MvPolynomial.X i : MvPolynomial σ K) = -1 := by
    rw [map_sub, MvPolynomial.pderiv_one, MvPolynomial.pderiv_X_self]
    ring
  rw [map_sub, MvPolynomial.pderiv_one, MvPolynomial.pderiv_mul,
    hself, hrest]
  ring

private theorem pderiv_fieldTruncatedLogMv
    (K σ : Type*) [Field K] (p : ℕ) (hp : 2 ≤ p)
    (hnz : ∀ j : ℕ, 0 < j → j < p → (j : K) ≠ 0)
    (i : σ) (u : MvPolynomial σ K) :
    MvPolynomial.pderiv i (fieldTruncatedLogMv K p u) =
      (∑ k ∈ Finset.range (p - 1), u ^ k) * MvPolynomial.pderiv i u := by
  rw [fieldTruncatedLogMv]
  simp only [map_add, map_sum, MvPolynomial.pderiv_C_mul,
    MvPolynomial.pderiv_pow]
  have hterm : ∀ j ∈ Finset.Ico 2 p,
      MvPolynomial.C (j : K)⁻¹ *
          ((j : MvPolynomial σ K) * u ^ (j - 1) * MvPolynomial.pderiv i u) =
        u ^ (j - 1) * MvPolynomial.pderiv i u := by
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    change MvPolynomial.C (j : K)⁻¹ *
        (MvPolynomial.C (j : K) * u ^ (j - 1) * MvPolynomial.pderiv i u) = _
    rw [show MvPolynomial.C (j : K)⁻¹ *
        (MvPolynomial.C (j : K) * u ^ (j - 1) * MvPolynomial.pderiv i u) =
        (MvPolynomial.C (j : K)⁻¹ * MvPolynomial.C (j : K)) *
          (u ^ (j - 1) * MvPolynomial.pderiv i u) by ring, ← map_mul]
    rw [inv_mul_cancel₀ (hnz j (by omega) (by omega)), map_one, one_mul]
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_mul]
  clear hnz hterm
  have hgeom :
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
  rw [← hgeom]
  ring

private theorem one_sub_X_mul_pderiv_universalLogDefectWithoutNorm
    (K σ : Type*) [Field K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) (hp : 2 ≤ p)
    (hnz : ∀ j : ℕ, 0 < j → j < p → (j : K) ≠ 0) (i : σ) :
    (1 - MvPolynomial.X i) *
        MvPolynomial.pderiv i (universalLogDefectWithoutNorm K σ p) =
      MvPolynomial.X i ^ (p - 1) -
        universalNormArgument K σ ^ (p - 1) := by
  let u : MvPolynomial σ K := universalNormArgument K σ
  let geom (x : MvPolynomial σ K) :=
    ∑ k ∈ Finset.range (p - 1), x ^ k
  have hsum : MvPolynomial.pderiv i
      (∑ j : σ, fieldTruncatedLogMv K p (MvPolynomial.X j)) =
      geom (MvPolynomial.X i) := by
    rw [map_sum]
    rw [Finset.sum_eq_single i]
    · rw [pderiv_fieldTruncatedLogMv K σ p hp hnz]
      simp [geom]
    · intro j _ hji
      rw [pderiv_fieldTruncatedLogMv K σ p hp hnz]
      rw [MvPolynomial.pderiv_X_of_ne hji]
      simp
    · simp
  have hdu := pderiv_universalNormArgument K σ i
  have hmuldu :
      (1 - MvPolynomial.X i) * MvPolynomial.pderiv i u = 1 - u := by
    rw [hdu]
    dsimp only [u]
    rw [universalNormArgument]
    rw [← Finset.mul_prod_erase (s := Finset.univ)
      (f := fun j : σ ↦ (1 - MvPolynomial.X j : MvPolynomial σ K))
      (Finset.mem_univ i)]
    ring
  rw [universalLogDefectWithoutNorm, map_sub,
    pderiv_fieldTruncatedLogMv K σ p hp hnz, hsum]
  change (1 - MvPolynomial.X i) *
      (geom u * MvPolynomial.pderiv i u - geom (MvPolynomial.X i)) = _
  calc
    _ = (1 - u) * geom u -
        (1 - MvPolynomial.X i) * geom (MvPolynomial.X i) := by
          rw [← hmuldu]
          ring
    _ = (1 - u ^ (p - 1)) - (1 - MvPolynomial.X i ^ (p - 1)) := by
      simp only [geom]
      rw [mul_neg_geom_sum, mul_neg_geom_sum]
    _ = _ := by ring

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

private theorem order_pderiv_universalLogDefectWithoutNorm
    (K σ : Type*) [Field K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) (hp : 2 ≤ p)
    (hnz : ∀ j : ℕ, 0 < j → j < p → (j : K) ≠ 0) (i : σ) :
    (p - 1 : ℕ) ≤ MvPowerSeries.order
      ((MvPolynomial.pderiv i (universalLogDefectWithoutNorm K σ p) :
        MvPolynomial σ K) : MvPowerSeries σ K) := by
  apply order_of_one_sub_mul_eq_pow_sub_pow (p - 1)
      (MvPowerSeries.X i)
      ((universalNormArgument K σ : MvPolynomial σ K) : MvPowerSeries σ K) _
  · simp
  · rw [universalNormArgument]
    have hprod :
        (((∏ j : σ, (1 - MvPolynomial.X j : MvPolynomial σ K)) :
            MvPolynomial σ K) : MvPowerSeries σ K) =
          ∏ j : σ, (1 - MvPowerSeries.X j) := by
      change MvPolynomial.coeToMvPowerSeries.ringHom
          (∏ j : σ, (1 - MvPolynomial.X j : MvPolynomial σ K)) = _
      simp
    rw [show (((1 - ∏ j : σ,
        (1 - MvPolynomial.X j : MvPolynomial σ K)) : MvPolynomial σ K) :
          MvPowerSeries σ K) =
        1 - (((∏ j : σ, (1 - MvPolynomial.X j : MvPolynomial σ K)) :
          MvPolynomial σ K) : MvPowerSeries σ K) by
      change MvPolynomial.coeToMvPowerSeries.ringHom (1 - ∏ j : σ,
        (1 - MvPolynomial.X j : MvPolynomial σ K)) = _
      rw [map_sub, map_one]
      rfl]
    rw [hprod]
    simp
  · simpa using congrArg MvPolynomial.coeToMvPowerSeries.ringHom
      (one_sub_X_mul_pderiv_universalLogDefectWithoutNorm K σ p hp hnz i)

private theorem order_pderiv_of_order
    {K σ : Type*} [Field K] (q : MvPolynomial σ K) (i : σ) (n : ℕ)
    (hq : (n + 1 : ℕ) ≤ MvPowerSeries.order
      ((q : MvPolynomial σ K) : MvPowerSeries σ K)) :
    (n : ℕ) ≤ MvPowerSeries.order
      ((MvPolynomial.pderiv i q : MvPolynomial σ K) : MvPowerSeries σ K) := by
  apply MvPowerSeries.le_order
  intro d hd
  have hd' : d.degree < n := by exact_mod_cast hd
  change MvPolynomial.coeff d (MvPolynomial.pderiv i q) = 0
  rw [MvPolynomial.coeff_pderiv]
  have hdegree : (d + Finsupp.single i 1).degree < n + 1 := by
    rw [map_add, Finsupp.degree_single]
    omega
  have hzero := MvPowerSeries.coeff_of_lt_order
    (f := ((q : MvPolynomial σ K) : MvPowerSeries σ K))
    (lt_of_lt_of_le (by exact_mod_cast hdegree) hq)
  change MvPolynomial.coeff (d + Finsupp.single i 1) q = 0 at hzero
  rw [hzero, zero_mul]

private theorem constantCoeff_fieldTruncatedLogMv_X
    (K σ : Type*) [Field K] (p : ℕ) (i : σ) :
    MvPolynomial.constantCoeff
      (fieldTruncatedLogMv K p (MvPolynomial.X i)) = 0 := by
  rw [fieldTruncatedLogMv]
  simp only [map_add, MvPolynomial.constantCoeff_X, map_sum, map_mul,
    MvPolynomial.constantCoeff_C, map_pow, zero_add]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  simp [show j ≠ 0 by omega]

private theorem order_product_fieldTruncatedLogMv
    (K σ : Type*) [Field K] [Fintype σ] (p : ℕ) :
    (Fintype.card σ : ℕ) ≤ MvPowerSeries.order
      (((∏ i : σ, fieldTruncatedLogMv K p (MvPolynomial.X i)) :
        MvPolynomial σ K) : MvPowerSeries σ K) := by
  have hcoe :
      (((∏ i : σ, fieldTruncatedLogMv K p (MvPolynomial.X i)) :
          MvPolynomial σ K) : MvPowerSeries σ K) =
        ∏ i : σ, ((fieldTruncatedLogMv K p (MvPolynomial.X i) :
          MvPolynomial σ K) : MvPowerSeries σ K) := by
    change MvPolynomial.coeToMvPowerSeries.ringHom
      (∏ i : σ, fieldTruncatedLogMv K p (MvPolynomial.X i)) = _
    simp
  rw [hcoe]
  calc
    (Fintype.card σ : ℕ∞) = ∑ _i : σ, (1 : ℕ∞) := by simp
    _ ≤ ∑ i : σ, MvPowerSeries.order
        ((fieldTruncatedLogMv K p (MvPolynomial.X i) :
          MvPolynomial σ K) : MvPowerSeries σ K) := by
      apply Finset.sum_le_sum
      intro i _
      apply MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
      change MvPolynomial.constantCoeff
        (fieldTruncatedLogMv K p (MvPolynomial.X i)) = 0
      exact constantCoeff_fieldTruncatedLogMv_X K σ p i
    _ ≤ MvPowerSeries.order
        (∏ i : σ, ((fieldTruncatedLogMv K p (MvPolynomial.X i) :
          MvPolynomial σ K) : MvPowerSeries σ K)) := by
      simpa using MvPowerSeries.le_order_prod
        (fun i : σ ↦ ((fieldTruncatedLogMv K p (MvPolynomial.X i) :
          MvPolynomial σ K) : MvPowerSeries σ K)) Finset.univ

private theorem order_pderiv_universalNormLogDefect
    (K σ : Type*) [Field K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) (hp : 2 ≤ p) (hcard : Fintype.card σ = p)
    (hnz : ∀ j : ℕ, 0 < j → j < p → (j : K) ≠ 0) (i : σ) :
    (p - 1 : ℕ) ≤ MvPowerSeries.order
      ((MvPolynomial.pderiv i (universalNormLogDefect K σ p) :
        MvPolynomial σ K) : MvPowerSeries σ K) := by
  have hwithout := order_pderiv_universalLogDefectWithoutNorm K σ p hp hnz i
  let q : MvPolynomial σ K :=
    ∏ j : σ, fieldTruncatedLogMv K p (MvPolynomial.X j)
  have hqorder : (p : ℕ) ≤ MvPowerSeries.order
      ((q : MvPolynomial σ K) : MvPowerSeries σ K) := by
    simpa [q, hcard] using order_product_fieldTruncatedLogMv K σ p
  have hqderiv : (p - 1 : ℕ) ≤ MvPowerSeries.order
      ((MvPolynomial.pderiv i q : MvPolynomial σ K) : MvPowerSeries σ K) := by
    apply order_pderiv_of_order q i (p - 1)
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ p)] using hqorder
  have hpoly : universalNormLogDefect K σ p =
      universalLogDefectWithoutNorm K σ p - q := by
    rfl
  rw [hpoly, map_sub]
  simp only [coe_sub_mvPolynomial]
  rw [sub_eq_add_neg]
  exact le_trans (le_min hwithout (by simpa using hqderiv))
    (MvPowerSeries.min_order_le_add
      (f := ((MvPolynomial.pderiv i (universalLogDefectWithoutNorm K σ p) :
        MvPolynomial σ K) : MvPowerSeries σ K))
      (g := -((MvPolynomial.pderiv i q : MvPolynomial σ K) :
        MvPowerSeries σ K)))

private theorem coeff_universalNormLogDefect_eq_zero
    (K σ : Type*) [Field K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) (hp : 2 ≤ p) (hcard : Fintype.card σ = p)
    (hnz : ∀ j : ℕ, 0 < j → j < p → (j : K) ≠ 0)
    (d : σ →₀ ℕ) (hd : d.degree < p) :
    MvPolynomial.coeff d (universalNormLogDefect K σ p) = 0 := by
  have hpositive (i : σ) (hi : d i ≠ 0) :
      MvPolynomial.coeff d (universalNormLogDefect K σ p) = 0 := by
    let m : σ →₀ ℕ := d - Finsupp.single i 1
    have hmdeg : m.degree + 1 = d.degree := by
      have hw := Finsupp.weight_sub_single_add (w := fun _ : σ ↦ 1) hi
      simpa only [← Finsupp.degree_eq_weight_one] using hw
    have hmlt : m.degree < p - 1 := by omega
    have horder := order_pderiv_universalNormLogDefect K σ p hp hcard hnz i
    have hcoeffPS : MvPowerSeries.coeff m
        ((MvPolynomial.pderiv i (universalNormLogDefect K σ p) :
          MvPolynomial σ K) : MvPowerSeries σ K) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      exact lt_of_lt_of_le (by exact_mod_cast hmlt) horder
    have hcoeff : MvPolynomial.coeff m
        (MvPolynomial.pderiv i (universalNormLogDefect K σ p)) = 0 :=
      hcoeffPS
    rw [MvPolynomial.coeff_pderiv] at hcoeff
    have hmd : m + Finsupp.single i 1 = d :=
      Finsupp.sub_add_single_one_cancel hi
    rw [hmd] at hcoeff
    have hmi : m i + 1 = d i := by
      have hi' := congrArg (fun e : σ →₀ ℕ ↦ e i) hmd
      simpa using hi'
    have hmiK : (m i : K) + 1 = (d i : K) := by
      simpa using congrArg (fun n : ℕ ↦ (n : K)) hmi
    rw [hmiK] at hcoeff
    exact (mul_eq_zero.mp hcoeff).resolve_right
      (hnz (d i) (Nat.pos_of_ne_zero hi)
        (lt_of_le_of_lt (Finsupp.le_degree i d) hd))
  by_cases hd0 : d = 0
  · subst d
    rw [← MvPolynomial.constantCoeff_eq, ← MvPolynomial.eval_zero]
    haveI : Nonempty σ := Fintype.card_pos_iff.mp (by omega)
    have hs : (∑ j ∈ Finset.Ico 2 p, (j : K)⁻¹ * (0 : K) ^ j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj' := Finset.mem_Ico.mp hj
      simp [show j ≠ 0 by omega]
    simp [universalNormLogDefect, universalNormArgument, fieldTruncatedLogMv,
      hs]
  · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd0
    exact hpositive i (Finsupp.mem_support_iff.mp hi)

private theorem coeff_integralUniversalNormLogDefect_eq_zero
    (F σ : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Fintype σ] [DecidableEq σ]
    (p : ℕ) (hp : 2 ≤ p) (hcard : Fintype.card σ = p)
    (hchar : residueCharacteristic F = p)
    (d : σ →₀ ℕ) (hd : d.degree < p) :
    MvPolynomial.coeff d (integralUniversalNormLogDefect F σ p hchar) = 0 := by
  have hnz : ∀ j : ℕ, 0 < j → j < p → (j : F) ≠ 0 := by
    intro j hj hjp
    have hord := ord_natCast_eq_zero_of_lt_residueCharacteristic F hj
      (hchar.symm ▸ hjp)
    intro hjzero
    rw [hjzero, ord_zero] at hord
    simp at hord
  have hmap := congrArg (MvPolynomial.coeff d)
    (map_integralUniversalNormLogDefect F σ p hchar hp)
  rw [MvPolynomial.coeff_map,
    coeff_universalNormLogDefect_eq_zero F σ p hp hcard hnz d hd] at hmap
  apply Subtype.ext
  simpa using hmap

private theorem map_integralUniversalLogDefectWithoutNorm
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (σ : Type*) [Fintype σ]
    (p : ℕ) (hchar : residueCharacteristic F = p) (hp : 2 ≤ p) :
    MvPolynomial.map (ValuativeRel.valuation F).integer.subtype
        (integralUniversalLogDefectWithoutNorm F σ p hchar) =
      universalLogDefectWithoutNorm F σ p := by
  rw [integralUniversalLogDefectWithoutNorm, universalLogDefectWithoutNorm]
  simp only [map_sub, map_sum]
  simp_rw [map_integralTruncatedLogMv F p hchar hp]
  simp [universalNormArgument]

private theorem coeff_universalLogDefectWithoutNorm_eq_zero
    (K σ : Type*) [Field K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) (hp : 2 ≤ p) (hcard : Fintype.card σ = p)
    (hnz : ∀ j : ℕ, 0 < j → j < p → (j : K) ≠ 0)
    (d : σ →₀ ℕ) (hd : d.degree < p) :
    MvPolynomial.coeff d (universalLogDefectWithoutNorm K σ p) = 0 := by
  let q : MvPolynomial σ K :=
    ∏ i : σ, fieldTruncatedLogMv K p (MvPolynomial.X i)
  have hqorder : (p : ℕ) ≤ MvPowerSeries.order
      ((q : MvPolynomial σ K) : MvPowerSeries σ K) := by
    simpa [q, hcard] using order_product_fieldTruncatedLogMv K σ p
  have hqzeroPS := MvPowerSeries.coeff_of_lt_order
    (f := ((q : MvPolynomial σ K) : MvPowerSeries σ K))
    (lt_of_lt_of_le (by exact_mod_cast hd) hqorder)
  have hqzero : MvPolynomial.coeff d q = 0 := hqzeroPS
  have hfull := coeff_universalNormLogDefect_eq_zero K σ p hp hcard hnz d hd
  have hpoly : universalNormLogDefect K σ p =
      universalLogDefectWithoutNorm K σ p - q := rfl
  rw [hpoly, MvPolynomial.coeff_sub, hqzero, sub_zero] at hfull
  exact hfull

private theorem coeff_integralUniversalLogDefectWithoutNorm_eq_zero
    (F σ : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Fintype σ] [DecidableEq σ]
    (p : ℕ) (hp : 2 ≤ p) (hcard : Fintype.card σ = p)
    (hchar : residueCharacteristic F = p)
    (d : σ →₀ ℕ) (hd : d.degree < p) :
    MvPolynomial.coeff d
      (integralUniversalLogDefectWithoutNorm F σ p hchar) = 0 := by
  have hnz : ∀ j : ℕ, 0 < j → j < p → (j : F) ≠ 0 := by
    intro j hj hjp
    have hord := ord_natCast_eq_zero_of_lt_residueCharacteristic F hj
      (hchar.symm ▸ hjp)
    intro hjzero
    rw [hjzero, ord_zero] at hord
    simp at hord
  have hmap := congrArg (MvPolynomial.coeff d)
    (map_integralUniversalLogDefectWithoutNorm F σ p hchar hp)
  rw [MvPolynomial.coeff_map,
    coeff_universalLogDefectWithoutNorm_eq_zero F σ p hp hcard hnz d hd] at hmap
  apply Subtype.ext
  simpa using hmap

@[reducible] private def exponentMulAction (G : Type*) [Group G] : MulAction G (G →₀ ℕ) where
  smul g d := Finsupp.equivMapDomain (Equiv.mulLeft g) d
  one_smul d := by
    change Finsupp.equivMapDomain (Equiv.mulLeft 1) d = d
    ext x
    rw [Finsupp.equivMapDomain_apply]
    change d (1⁻¹ * x) = d x
    simp
  mul_smul g h d := by
    change Finsupp.equivMapDomain (Equiv.mulLeft (g * h)) d =
      Finsupp.equivMapDomain (Equiv.mulLeft g)
        (Finsupp.equivMapDomain (Equiv.mulLeft h) d)
    ext x
    rw [Finsupp.equivMapDomain_apply, Finsupp.equivMapDomain_apply,
      Finsupp.equivMapDomain_apply]
    change d ((g * h)⁻¹ * x) = d (h⁻¹ * (g⁻¹ * x))
    simp [mul_assoc]

private theorem smul_exponent_apply
    {G : Type*} [Group G] (g : G) (d : G →₀ ℕ) (x : G) :
    ((@SMul.smul G (G →₀ ℕ) (exponentMulAction G).toSMul g d) x) =
      d (g⁻¹ * x) := by
  rw [show @SMul.smul G (G →₀ ℕ) (exponentMulAction G).toSMul g d =
      Finsupp.equivMapDomain (Equiv.mulLeft g) d by rfl,
    Finsupp.equivMapDomain_apply]
  rfl

private theorem integralUniversalNormLogDefect_isSymmetric
    (F σ : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Fintype σ]
    (p : ℕ) (hchar : residueCharacteristic F = p) :
    (integralUniversalNormLogDefect F σ p hchar).IsSymmetric := by
  intro e
  have hrenameP (x : MvPolynomial σ (ringOfIntegers F)) :
      MvPolynomial.rename e (integralTruncatedLogMv F p hchar x) =
        integralTruncatedLogMv F p hchar (MvPolynomial.rename e x) := by
    simp [integralTruncatedLogMv]
  have harg : MvPolynomial.rename e
      (universalNormArgument (ringOfIntegers F) σ) =
      universalNormArgument (ringOfIntegers F) σ := by
    simp only [universalNormArgument, map_sub, map_one, map_prod,
      MvPolynomial.rename_X]
    congr 1
    exact Equiv.prod_comp e (fun x : σ ↦
      (1 - MvPolynomial.X x : MvPolynomial σ (ringOfIntegers F)))
  have hsum : MvPolynomial.rename e
      (∑ i : σ, integralTruncatedLogMv F p hchar (MvPolynomial.X i)) =
      ∑ i : σ, integralTruncatedLogMv F p hchar (MvPolynomial.X i) := by
    simp only [map_sum, hrenameP, MvPolynomial.rename_X]
    exact Equiv.sum_comp e (fun i : σ ↦
      integralTruncatedLogMv F p hchar (MvPolynomial.X i))
  have hprod : MvPolynomial.rename e
      (∏ i : σ, integralTruncatedLogMv F p hchar (MvPolynomial.X i)) =
      ∏ i : σ, integralTruncatedLogMv F p hchar (MvPolynomial.X i) := by
    simp only [map_prod, hrenameP, MvPolynomial.rename_X]
    exact Equiv.prod_comp e (fun i : σ ↦
      integralTruncatedLogMv F p hchar (MvPolynomial.X i))
  simp only [integralUniversalNormLogDefect, map_sub, hrenameP, harg, hsum,
    hprod]

private theorem coeff_exponent_translate
    (F G : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Fintype G] [Group G]
    (p : ℕ) (hchar : residueCharacteristic F = p)
    (g : G) (d : G →₀ ℕ) :
    MvPolynomial.coeff
        (Finsupp.equivMapDomain (Equiv.mulLeft g) d)
        (integralUniversalNormLogDefect F G p hchar) =
      MvPolynomial.coeff d (integralUniversalNormLogDefect F G p hchar) := by
  have h := MvPolynomial.coeff_rename_mapDomain (Equiv.mulLeft g)
    (Equiv.mulLeft g).injective
    (integralUniversalNormLogDefect F G p hchar) d
  rw [integralUniversalNormLogDefect_isSymmetric F G p hchar] at h
  simpa only [Finsupp.equivMapDomain_eq_mapDomain] using h

private theorem degree_exponent_translate
    {G : Type*} [Group G] [Fintype G] (g : G) (d : G →₀ ℕ) :
    (Finsupp.equivMapDomain (Equiv.mulLeft g) d).degree = d.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
  simp_rw [Finsupp.equivMapDomain_apply]
  exact Equiv.sum_comp (Equiv.mulLeft g).symm d

private def conjugateMonomial
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (z : K) (d : Gal(K/F) →₀ ℕ) : K :=
  ∏ σ : Gal(K/F), (σ z) ^ d σ

private theorem conjugateMonomial_translate
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (g : Gal(K/F)) (z : K) (d : Gal(K/F) →₀ ℕ) :
    conjugateMonomial z (Finsupp.equivMapDomain (Equiv.mulLeft g) d) =
      g (conjugateMonomial z d) := by
  have hreindex := Equiv.prod_comp (Equiv.mulLeft g)
    (fun x : Gal(K/F) ↦
      (x z) ^ (Finsupp.equivMapDomain (Equiv.mulLeft g) d) x)
  rw [conjugateMonomial, conjugateMonomial]
  rw [← hreindex]
  simp only [Finsupp.equivMapDomain_apply]
  change (∏ x : Gal(K/F), ((g * x) z) ^ d (g⁻¹ * (g * x))) =
    g (∏ x : Gal(K/F), (x z) ^ d x)
  simp

private theorem fixed_exponent_eq_constant
    {G : Type*} [Group G] [Fintype G]
    (d : G →₀ ℕ)
    (hfixed : ∀ g : G, Finsupp.equivMapDomain (Equiv.mulLeft g) d = d) :
    ∀ x : G, d x = d 1 := by
  intro x
  have hx := congrArg (fun e : G →₀ ℕ ↦ e x)
    (hfixed x)
  rw [Finsupp.equivMapDomain_apply] at hx
  change d (x⁻¹ * x) = d x at hx
  simpa using hx.symm

private theorem fixed_exponent_eq_of_degree_eq
    {G : Type*} [Group G] [Fintype G]
    (d e : G →₀ ℕ)
    (hd : ∀ g : G, Finsupp.equivMapDomain (Equiv.mulLeft g) d = d)
    (he : ∀ g : G, Finsupp.equivMapDomain (Equiv.mulLeft g) e = e)
    (hdegree : d.degree = e.degree) : d = e := by
  have hdconst := fixed_exponent_eq_constant d hd
  have heconst := fixed_exponent_eq_constant e he
  have hddegree : d.degree = Fintype.card G * d 1 := by
    rw [Finsupp.degree_eq_sum]
    simp_rw [hdconst]
    simp
  have hedegree : e.degree = Fintype.card G * e 1 := by
    rw [Finsupp.degree_eq_sum]
    simp_rw [heconst]
    simp
  have hvalue : d 1 = e 1 := by
    have hcard : 0 < Fintype.card G := Fintype.card_pos
    apply Nat.mul_left_cancel hcard
    rw [← hddegree, ← hedegree]
    exact hdegree
  ext x
  rw [hdconst x, heconst x, hvalue]

private theorem sum_eq_sum_orbit_sums
    {G X R : Type*} [Group G] [MulAction G X] [Fintype X]
    [Fintype (MulAction.orbitRel.Quotient G X)]
    [∀ ω : MulAction.orbitRel.Quotient G X,
      Fintype (MulAction.orbit G ω.out)]
    [AddCommMonoid R] (f : X → R) :
    ∑ x : X, f x =
      ∑ ω : MulAction.orbitRel.Quotient G X,
        ∑ y : MulAction.orbit G ω.out, f y := by
  classical
  let e := MulAction.selfEquivSigmaOrbits G X
  calc
    ∑ x : X, f x = ∑ x : X, f ((e x).2 : X) := by rfl
    _ = ∑ y : (ω : MulAction.orbitRel.Quotient G X) ×
        MulAction.orbit G ω.out, f (y.2 : X) :=
      Equiv.sum_comp e (fun y ↦ f (y.2 : X))
    _ = ∑ ω : MulAction.orbitRel.Quotient G X,
        ∑ y : MulAction.orbit G ω.out, f y := Fintype.sum_sigma _

private theorem sum_eq_sum_orbit_card_nsmul
    {G X R : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X]
    [Fintype (MulAction.orbitRel.Quotient G X)]
    [∀ ω : MulAction.orbitRel.Quotient G X,
      Fintype (MulAction.orbit G ω.out)]
    [CommRing R] (f : X → R) (hf : ∀ (g : G) (x : X), f (g • x) = f x) :
    ∑ x : X, f x =
      ∑ ω : MulAction.orbitRel.Quotient G X,
        Fintype.card (MulAction.orbit G ω.out) • f ω.out := by
  classical
  rw [sum_eq_sum_orbit_sums (G := G)]
  apply Fintype.sum_congr
  intro ω
  have hconstant (y : MulAction.orbit G ω.out) : f y = f ω.out := by
    obtain ⟨g, hg⟩ := y.property
    rw [← hg, hf]
  simp_rw [hconstant]
  simp

private theorem mapDomain_to_unit
    {G : Type*} [Fintype G] (d : G →₀ ℕ) :
    d.mapDomain (fun _ : G ↦ ()) = Finsupp.single () d.degree := by
  apply Finsupp.ext
  intro u
  cases u
  have hdegree := Finsupp.degree_mapDomain (fun _ : G ↦ ()) d
  calc
    (d.mapDomain (fun _ : G ↦ ())) () =
        (d.mapDomain (fun _ : G ↦ ())).degree := by
      rw [Finsupp.degree_eq_sum]
      simp
    _ = d.degree := hdegree
    _ = (Finsupp.single () d.degree) () := by simp

private theorem coeff_diagonal_rename
    {R G : Type*} [CommRing R] [Fintype G]
    (Q : MvPolynomial G R) (N : ℕ) :
    MvPolynomial.coeff (Finsupp.single () N)
        (MvPolynomial.rename (fun _ : G ↦ ()) Q) =
      ∑ d ∈ Q.support with d.degree = N, Q.coeff d := by
  classical
  conv_lhs => rw [Q.as_sum]
  rw [map_sum, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.rename_monomial, mapDomain_to_unit,
    MvPolynomial.coeff_monomial]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  simp

private theorem rename_integralUniversalNormLogDefect_to_unit
    (F G : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Fintype G]
    (p : ℕ) (hchar : residueCharacteristic F = p) :
    MvPolynomial.rename (fun _ : G ↦ ())
        (integralUniversalNormLogDefect F G p hchar) =
      integralTruncatedLogMv F p hchar
          (1 - (1 - MvPolynomial.X ()) ^ Fintype.card G) -
        Fintype.card G •
          integralTruncatedLogMv F p hchar (MvPolynomial.X ()) -
        integralTruncatedLogMv F p hchar (MvPolynomial.X ()) ^ Fintype.card G := by
  classical
  have hrenameP (x : MvPolynomial G (ringOfIntegers F)) :
      MvPolynomial.rename (fun _ : G ↦ ())
          (integralTruncatedLogMv F p hchar x) =
        integralTruncatedLogMv F p hchar
          (MvPolynomial.rename (fun _ : G ↦ ()) x) := by
    simp [integralTruncatedLogMv]
  simp only [integralUniversalNormLogDefect, universalNormArgument,
    map_sub, map_sum, map_prod, hrenameP, map_one, MvPolynomial.rename_X]
  rw [Finset.sum_const, Finset.prod_const, Finset.prod_const, Finset.card_univ]

private theorem diagonal_polynomial_identity
    (G S : Type*) [Fintype G] [CommRing S]
    (p : ℕ) (hp : p.Prime) [CharP S p]
    (hcard : Fintype.card G = p)
    (c : ℕ → S)
    (hc_pow : ∀ j ∈ Finset.Ico 1 p, c j ^ p = c j) :
    let P (x : MvPolynomial Unit S) : MvPolynomial Unit S :=
      ∑ j ∈ Finset.Ico 1 p, MvPolynomial.C (c j) * x ^ j
    P (1 - (1 - MvPolynomial.X ()) ^ Fintype.card G) -
        Fintype.card G • P (MvPolynomial.X ()) -
        P (MvPolynomial.X ()) ^ Fintype.card G = 0 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let P (x : MvPolynomial Unit S) : MvPolynomial Unit S :=
    ∑ j ∈ Finset.Ico 1 p, MvPolynomial.C (c j) * x ^ j
  have hPpow (x : MvPolynomial Unit S) : P x ^ p = P (x ^ p) := by
    dsimp only [P]
    rw [sum_pow_char]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_pow, ← MvPolynomial.C_pow, hc_pow j hj,
      ← pow_mul, ← pow_mul]
    rw [Nat.mul_comm]
  have hnormarg :
      1 - (1 - MvPolynomial.X () : MvPolynomial Unit S) ^ Fintype.card G =
        MvPolynomial.X () ^ p := by
    rw [hcard]
    have hsub : (1 - MvPolynomial.X () : MvPolynomial Unit S) ^ p =
        1 - MvPolynomial.X () ^ p :=
      by simpa using
        (sub_pow_char (1 : MvPolynomial Unit S) (MvPolynomial.X ()))
    rw [hsub]
    ring
  change P (1 - (1 - MvPolynomial.X ()) ^ Fintype.card G) -
      Fintype.card G • P (MvPolynomial.X ()) -
      P (MvPolynomial.X ()) ^ Fintype.card G = 0
  rw [hnormarg, hcard, ← hPpow]
  have hpzero : p • P (MvPolynomial.X ()) = 0 := by
    rw [nsmul_eq_mul]
    change MvPolynomial.C (p : S) * P (MvPolynomial.X ()) = 0
    rw [CharP.cast_eq_zero, map_zero, zero_mul]
  rw [hpzero]
  ring

private theorem residueCharacteristic_natCast_nonunit
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) (hchar : residueCharacteristic F = p) :
    (p : ringOfIntegers F) ∈ nonunits (ringOfIntegers F) := by
  rw [← IsLocalRing.mem_maximalIdeal]
  rw [← IsLocalRing.residue_eq_zero_iff]
  change residueMap F (p : ringOfIntegers F) = 0
  rw [map_natCast]
  simp [← hchar, CharP.cast_eq_zero]

private theorem normLogCoefficient_pow_mod_residueCharacteristic
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) (hp : p.Prime)
    (hchar : residueCharacteristic F = p)
    (j : ℕ) (hj : j ∈ Finset.Ico 1 p) :
    let I : Ideal (ringOfIntegers F) :=
      Ideal.span {(p : ringOfIntegers F)}
    let q : ringOfIntegers F →+* HasQuotient.Quotient (ringOfIntegers F) I :=
      Ideal.Quotient.mk I
    q (normLogCoefficient F p hchar j) ^ p =
      q (normLogCoefficient F p hchar j) := by
  classical
  let R := ringOfIntegers F
  let I : Ideal R := Ideal.span {(p : R)}
  let S := R ⧸ I
  let q : R →+* S := Ideal.Quotient.mk I
  letI : Fact p.Prime := ⟨hp⟩
  letI : CharP S p := CharP.quotient R p
    (residueCharacteristic_natCast_nonunit F p hchar)
  have hcastpow (n : ℕ) : (n : S) ^ p = (n : S) := by
    induction n with
    | zero => simp [hp.ne_zero]
    | succ n ih =>
        rw [Nat.cast_succ, add_pow_char, ih]
        simp
  have hj' := Finset.mem_Ico.mp hj
  have hR : normLogCoefficient F p hchar j * (j : R) = 1 := by
    apply Subtype.ext
    simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one]
    rw [coe_normLogCoefficient F p hchar j (by omega) hj'.2]
    rw [inv_mul_cancel₀]
    intro hjzero
    have hord := ord_natCast_eq_zero_of_lt_residueCharacteristic F
      (by omega) (hchar.symm ▸ hj'.2)
    rw [hjzero, ord_zero] at hord
    simp at hord
  have hc_mul : q (normLogCoefficient F p hchar j) * (j : S) = 1 :=
    by exact_mod_cast congrArg q hR
  have hjunit : IsUnit (j : S) :=
    (CharP.isUnit_natCast_iff hp).2 (Nat.not_dvd_of_pos_of_lt hj'.1 hj'.2)
  apply hjunit.mul_right_cancel
  have hpow := congrArg (fun x : S ↦ x ^ p) hc_mul
  rw [mul_pow, hcastpow, one_pow] at hpow
  rw [hpow, hc_mul]

private theorem diagonal_integralUniversalNormLogDefect_mod_degree
    (F G : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Fintype G]
    (p : ℕ) (hp : p.Prime)
    (hcard : Fintype.card G = p)
    (hchar : residueCharacteristic F = p) :
    MvPolynomial.rename (fun _ : G ↦ ())
      (MvPolynomial.map
        (Ideal.Quotient.mk (Ideal.span {(p : ringOfIntegers F)}))
        (integralUniversalNormLogDefect F G p hchar)) = 0 := by
  classical
  let R := ringOfIntegers F
  let I : Ideal R := Ideal.span {(p : R)}
  let S := R ⧸ I
  let q : R →+* S := Ideal.Quotient.mk I
  letI : Fact p.Prime := ⟨hp⟩
  letI : CharP S p := CharP.quotient R p
    (residueCharacteristic_natCast_nonunit F p hchar)
  let c (j : ℕ) : S := q (normLogCoefficient F p hchar j)
  have hc_pow (j : ℕ) (hj : j ∈ Finset.Ico 1 p) : (c j) ^ p = c j := by
    exact normLogCoefficient_pow_mod_residueCharacteristic F p hp hchar j hj
  have hmapP (x : MvPolynomial Unit R) :
      MvPolynomial.map q (integralTruncatedLogMv F p hchar x) =
        ∑ j ∈ Finset.Ico 1 p,
          MvPolynomial.C (c j) * MvPolynomial.map q x ^ j := by
    simp [integralTruncatedLogMv, c]
  change MvPolynomial.rename (fun _ : G ↦ ())
      (MvPolynomial.map q (integralUniversalNormLogDefect F G p hchar)) = 0
  rw [← MvPolynomial.map_rename,
    rename_integralUniversalNormLogDefect_to_unit F G p hchar]
  simp only [map_sub, map_nsmul, map_pow, hmapP, map_one,
    MvPolynomial.map_X]
  exact diagonal_polynomial_identity G S p hp hcard c hc_pow

private theorem fixed_coefficient_mem_degree_span
    (F G : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Group G] [Fintype G]
    (p : ℕ) (hp : p.Prime) (hcard : Fintype.card G = p)
    (hsubgroups : ∀ H : Subgroup G, H = ⊥ ∨ H = ⊤)
    (hchar : residueCharacteristic F = p)
    (d : G →₀ ℕ)
    (hfixed : ∀ g : G, Finsupp.equivMapDomain (Equiv.mulLeft g) d = d) :
    MvPolynomial.coeff d (integralUniversalNormLogDefect F G p hchar) ∈
      Ideal.span {(p : ringOfIntegers F)} := by
  classical
  let R := ringOfIntegers F
  let I : Ideal R := Ideal.span {(p : R)}
  let S := R ⧸ I
  let q : R →+* S := Ideal.Quotient.mk I
  let Q : MvPolynomial G R := integralUniversalNormLogDefect F G p hchar
  apply (Ideal.Quotient.eq_zero_iff_mem.mp :
    q (MvPolynomial.coeff d Q) = 0 → MvPolynomial.coeff d Q ∈ I)
  by_contra hdq
  let N : ℕ := d.degree
  let s : Finset (G →₀ ℕ) := Q.support.filter fun e ↦ e.degree = N
  have hdcoeff : MvPolynomial.coeff d Q ≠ 0 := by
    intro hd
    apply hdq
    simp [hd]
  have hdmem : d ∈ s := by
    rw [Finset.mem_filter]
    exact ⟨MvPolynomial.mem_support_iff.mpr hdcoeff, rfl⟩
  let X := ↑s
  letI ambientAction : MulAction G (G →₀ ℕ) := exponentMulAction G
  have hsmul_mem (g : G) (x : X) : g • (x : G →₀ ℕ) ∈ s := by
    have hx := x.property
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨?_, ?_⟩
    · rw [MvPolynomial.mem_support_iff]
      change MvPolynomial.coeff
        (Finsupp.equivMapDomain (Equiv.mulLeft g) (x : G →₀ ℕ)) Q ≠ 0
      rw [coeff_exponent_translate F G p hchar]
      exact MvPolynomial.mem_support_iff.mp hx.1
    · change (Finsupp.equivMapDomain
        (Equiv.mulLeft g) (x : G →₀ ℕ)).degree = N
      rw [degree_exponent_translate]
      exact hx.2
  letI : MulAction G X := {
    smul := fun g x ↦ ⟨g • (x : G →₀ ℕ), hsmul_mem g x⟩
    one_smul := fun x ↦ Subtype.ext (one_smul G (x : G →₀ ℕ))
    mul_smul := fun g h x ↦ Subtype.ext (mul_smul g h (x : G →₀ ℕ)) }
  let xd : X := ⟨d, hdmem⟩
  let f : X → S := fun x ↦ q (MvPolynomial.coeff (x : G →₀ ℕ) Q)
  have hf (g : G) (x : X) : f (g • x) = f x := by
    change q (MvPolynomial.coeff
        (Finsupp.equivMapDomain (Equiv.mulLeft g) (x : G →₀ ℕ)) Q) =
      q (MvPolynomial.coeff (x : G →₀ ℕ) Q)
    rw [coeff_exponent_translate F G p hchar]
  let Ω := MulAction.orbitRel.Quotient G X
  let orbitMap : X → Ω := fun x ↦ Quotient.mk'' x
  letI : Fintype Ω := Fintype.ofFinite Ω
  letI orbitFintype (ω : Ω) : Fintype (MulAction.orbit G ω.out) :=
    Fintype.ofFinite (MulAction.orbit G ω.out)
  have horbits := sum_eq_sum_orbit_card_nsmul f hf
  have hdiagPoly : MvPolynomial.map q
      (MvPolynomial.rename (fun _ : G ↦ ()) Q) = 0 := by
    rw [MvPolynomial.map_rename]
    exact diagonal_integralUniversalNormLogDefect_mod_degree
      F G p hp hcard hchar
  have hdiag := congrArg (MvPolynomial.coeff (Finsupp.single () N)) hdiagPoly
  rw [MvPolynomial.coeff_map, coeff_diagonal_rename Q N,
    MvPolynomial.coeff_zero, map_sum] at hdiag
  have hsumX : ∑ x : X, f x = 0 := by
    change ∑ x ∈ s.attach, q (MvPolynomial.coeff (x : G →₀ ℕ) Q) = 0
    have hdiag' : ∑ x ∈ s, q (MvPolynomial.coeff x Q) = 0 := hdiag
    exact (Finset.sum_attach s
      (fun x : G →₀ ℕ ↦ q (MvPolynomial.coeff x Q))).trans hdiag'
  have hsumOrbits :
      ∑ ω : Ω, Fintype.card (MulAction.orbit G ω.out) • f ω.out = 0 :=
    horbits.symm.trans hsumX
  let ωd : Ω := orbitMap xd
  have hxd_fixed (g : G) : g • xd = xd := by
    apply Subtype.ext
    exact hfixed g
  have hout_eq_xd : ωd.out = xd := by
    have hq : orbitMap ωd.out = orbitMap xd := by
      exact (Quotient.out_eq' ωd).trans rfl
    have horbit : ωd.out ∈ MulAction.orbit G xd :=
      MulAction.orbitRel_apply.mp ((Quotient.eq'').mp hq)
    rcases MulAction.mem_orbit_iff.mp horbit with ⟨g, hg⟩
    rw [← hg, hxd_fixed]
  have hcardOrbitXd : Fintype.card (MulAction.orbit G ωd.out) = 1 := by
    apply MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mp
    rw [MulAction.mem_fixedPoints]
    intro g
    rw [hout_eq_xd, hxd_fixed]
  have hother (ω : Ω) (hω : ω ≠ ωd) :
      Fintype.card (MulAction.orbit G ω.out) • f ω.out = 0 := by
    rcases hsubgroups (MulAction.stabilizer G ω.out) with hstab | hstab
    · have hcardOrbit : Fintype.card (MulAction.orbit G ω.out) = p := by
        have hc := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G ω.out
        have hcardStabilizer :
            Fintype.card (MulAction.stabilizer G ω.out) = 1 := by
          rw [← Nat.card_eq_fintype_card, hstab, Subgroup.card_bot]
        rw [hcardStabilizer, hcard, mul_one] at hc
        exact hc
      rw [hcardOrbit, nsmul_eq_mul]
      change (p : S) * f ω.out = 0
      letI : Fact p.Prime := ⟨hp⟩
      letI : CharP S p := CharP.quotient R p
        (residueCharacteristic_natCast_nonunit F p hchar)
      rw [CharP.cast_eq_zero, zero_mul]
    · exfalso
      apply hω
      have hout_fixed (g : G) :
          Finsupp.equivMapDomain (Equiv.mulLeft g)
              (ω.out : G →₀ ℕ) = (ω.out : G →₀ ℕ) := by
        have hxsub : g • (ω.out : X) = (ω.out : X) := by
          apply MulAction.mem_stabilizer_iff.mp
          rw [hstab]
          exact Subgroup.mem_top g
        exact congrArg (fun x : X ↦ (x : G →₀ ℕ)) hxsub
      have hout_degree : (ω.out : G →₀ ℕ).degree = d.degree := by
        have hout_mem : (ω.out : G →₀ ℕ) ∈ s :=
          Subtype.property (ω.out : X)
        exact (Finset.mem_filter.mp hout_mem).2
      have houtd : (ω.out : G →₀ ℕ) = d :=
        fixed_exponent_eq_of_degree_eq _ _ hout_fixed hfixed hout_degree
      calc
        ω = orbitMap ω.out := (Quotient.out_eq' ω).symm
        _ = orbitMap xd := by congr 1; exact Subtype.ext houtd
        _ = ωd := rfl
  have hsingle :
      ∑ ω : Ω, Fintype.card (MulAction.orbit G ω.out) • f ω.out = f xd := by
    rw [Finset.sum_eq_single ωd]
    · rw [hcardOrbitXd, one_nsmul, hout_eq_xd]
    · intro ω _ hω
      exact hother ω hω
    · simp
  have : f xd = 0 := hsingle.symm.trans hsumOrbits
  exact hdq this

private theorem pow_mem_lattice_nat
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {x : K} {r : ℕ}
    (hx : x ∈ lattice K (r : ℤ)) (n : ℕ) :
    x ^ n ∈ lattice K ((n * r : ℕ) : ℤ) := by
  rw [mem_lattice, ord_pow]
  have h := nsmul_le_nsmul_right
    (show ((r : ℤ) : WithTop ℤ) ≤ ord K x from hx) n
  calc
    ((((n * r : ℕ) : ℤ) : WithTop ℤ)) =
        (((n • (r : ℤ) : ℤ) : WithTop ℤ)) := by congr
    _ = n • (((r : ℤ) : WithTop ℤ)) := by rw [WithTop.coe_nsmul]
    _ ≤ n • ord K x := h

private theorem eval₂_mem_lattice_of_support_degree
    (F K σ : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Fintype σ] [DecidableEq σ]
    (n r : ℕ) (Q : MvPolynomial σ (ringOfIntegers F))
    (hdegree : ∀ d ∈ Q.support, n ≤ d.degree)
    (a : σ → K) (ha : ∀ i, a i ∈ lattice K (r : ℤ)) :
    MvPolynomial.eval₂
        ((algebraMap F K).comp (ValuativeRel.valuation F).integer.subtype)
        a Q ∈ lattice K ((n * r : ℕ) : ℤ) := by
  rw [MvPolynomial.eval₂_eq']
  apply sum_mem_lattice K
  intro d hd
  have hc : algebraMap F K
      ((Q.coeff d : ringOfIntegers F) : F) ∈ lattice K 0 := by
    rw [mem_lattice, ord_algebraMap]
    exact nsmul_nonneg
      ((ord_nonneg_iff_mem_integer F _).2 (Q.coeff d).property)
      (ramificationIndex F K)
  have hpow (i : σ) : a i ^ d i ∈ lattice K (((d i) * r : ℕ) : ℤ) :=
    pow_mem_lattice_nat K (ha i) (d i)
  have hprod : ∏ i : σ, a i ^ d i ∈
      lattice K ((d.degree * r : ℕ) : ℤ) := by
    rw [mem_lattice]
    have hi (i : σ) :
        ((((d i * r : ℕ) : ℤ) : WithTop ℤ)) ≤ ord K (a i ^ d i) :=
      hpow i
    have hordprod (s : Finset σ) :
        ord K (∏ i ∈ s, a i ^ d i) = ∑ i ∈ s, ord K (a i ^ d i) := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s his ih =>
          rw [Finset.prod_insert his, Finset.sum_insert his, ord_mul, ih]
    calc
      ((((d.degree * r : ℕ) : ℤ) : WithTop ℤ)) =
          ∑ i : σ, ((((d i * r : ℕ) : ℤ) : WithTop ℤ)) := by
        norm_cast
        rw [Finsupp.degree_eq_sum, Finset.sum_mul]
      _ ≤ ∑ i : σ, ord K (a i ^ d i) := Finset.sum_le_sum fun i _ ↦ hi i
      _ = ord K (∏ i : σ, a i ^ d i) := by
        symm
        simpa using hordprod Finset.univ
  have hterm := mul_mem_lattice K hc hprod
  have hterm' : algebraMap F K ((Q.coeff d : ringOfIntegers F) : F) *
      ∏ i : σ, a i ^ d i ∈ lattice K ((d.degree * r : ℕ) : ℤ) := by
    simpa using hterm
  have hmapCoeff :
      ((algebraMap F K).comp (ValuativeRel.valuation F).integer.subtype)
          (Q.coeff d) = algebraMap F K ((Q.coeff d : ringOfIntegers F) : F) := rfl
  rw [hmapCoeff]
  exact lattice_antitone K (by
    exact_mod_cast Nat.mul_le_mul_right r (hdegree d hd)) hterm'

private theorem conjugateMonomial_mem_lattice
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {z : K} {a : ℕ} (hz : z ∈ lattice K (a : ℤ))
    (d : Gal(K/F) →₀ ℕ) :
    conjugateMonomial z d ∈ lattice K ((d.degree * a : ℕ) : ℤ) := by
  classical
  rw [conjugateMonomial, mem_lattice]
  have hi (i : Gal(K/F)) :
      ((((d i * a : ℕ) : ℤ) : WithTop ℤ)) ≤ ord K ((i z) ^ d i) := by
    exact pow_mem_lattice_nat K (by simpa [mem_lattice] using hz) (d i)
  have hprod (u : Finset Gal(K/F)) :
      ord K (∏ i ∈ u, (i z) ^ d i) = ∑ i ∈ u, ord K ((i z) ^ d i) := by
    induction u using Finset.induction_on with
    | empty => simp
    | @insert i u hiu ih =>
        rw [Finset.prod_insert hiu, Finset.sum_insert hiu, ord_mul, ih]
  calc
    ((((d.degree * a : ℕ) : ℤ) : WithTop ℤ)) =
        ∑ i : Gal(K/F), ((((d i * a : ℕ) : ℤ) : WithTop ℤ)) := by
      norm_cast
      rw [Finsupp.degree_eq_sum, Finset.sum_mul]
    _ ≤ ∑ i : Gal(K/F), ord K ((i z) ^ d i) :=
      Finset.sum_le_sum fun i _ ↦ hi i
    _ = ord K (∏ i : Gal(K/F), (i z) ^ d i) := by
      symm
      simpa using hprod Finset.univ

private theorem map_truncatedLog
    {K L : Type*} [Field K] [Field L] (f : K →+* L) (p : ℕ) (x : K) :
    f (truncatedLog p x) = truncatedLog p (f x) := by
  simp [truncatedLog_apply]

private theorem eval_integralUniversalNormLogDefect
    (F K σ : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [Algebra F K] [Fintype σ]
    (p : ℕ) (hchar : residueCharacteristic F = p) (hp : 2 ≤ p)
    (a : σ → K) :
    MvPolynomial.eval₂
        ((algebraMap F K).comp (ValuativeRel.valuation F).integer.subtype) a
        (integralUniversalNormLogDefect F σ p hchar) =
      truncatedLog p (1 - ∏ i : σ, (1 - a i)) -
        ∑ i : σ, truncatedLog p (a i) -
        ∏ i : σ, truncatedLog p (a i) := by
  rw [integralUniversalNormLogDefect]
  simp only [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_prod]
  rw [eval_integralTruncatedLogMv_extension F K p hchar hp]
  simp_rw [eval_integralTruncatedLogMv_extension F K p hchar hp]
  rw [eval_universalNormArgument]
  simp

private theorem eval_integralUniversalLogDefectWithoutNorm
    (F K σ : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [Algebra F K] [Fintype σ]
    (p : ℕ) (hchar : residueCharacteristic F = p) (hp : 2 ≤ p)
    (a : σ → K) :
    MvPolynomial.eval₂
        ((algebraMap F K).comp (ValuativeRel.valuation F).integer.subtype) a
        (integralUniversalLogDefectWithoutNorm F σ p hchar) =
      truncatedLog p (1 - ∏ i : σ, (1 - a i)) -
        ∑ i : σ, truncatedLog p (a i) := by
  rw [integralUniversalLogDefectWithoutNorm]
  simp only [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_sum]
  rw [eval_integralTruncatedLogMv_extension F K p hchar hp]
  simp_rw [eval_integralTruncatedLogMv_extension F K p hchar hp]
  rw [eval_universalNormArgument]
  simp

private theorem algebraMap_normLogExpressionWithoutNorm
    (F K : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K]
    [Algebra F K] [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (p : ℕ) (z : K) :
    algebraMap F K
        (truncatedLog p (1 - norm F K (1 - z)) - trace F K (truncatedLog p z)) =
      truncatedLog p (1 - ∏ σ : Gal(K/F), (1 - σ z)) -
        ∑ σ : Gal(K/F), truncatedLog p (σ z) := by
  rw [map_sub, map_truncatedLog, trace_eq_sum_automorphisms]
  simp only [map_sub, map_one]
  rw [Algebra.norm_eq_prod_automorphisms]
  congr 1
  · congr 2
    apply Finset.prod_congr rfl
    intro σ _
    simp
  · apply Finset.sum_congr rfl
    intro σ _
    exact map_truncatedLog σ.toRingEquiv.toRingHom p z

private theorem algebraMap_normLogExpression
    (F K : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K]
    [Algebra F K] [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (p : ℕ) (z : K) :
    algebraMap F K
        (truncatedLog p (1 - norm F K (1 - z)) -
          trace F K (truncatedLog p z) - norm F K (truncatedLog p z)) =
      truncatedLog p (1 - ∏ σ : Gal(K/F), (1 - σ z)) -
        ∑ σ : Gal(K/F), truncatedLog p (σ z) -
        ∏ σ : Gal(K/F), truncatedLog p (σ z) := by
  rw [map_sub, algebraMap_normLogExpressionWithoutNorm]
  rw [Algebra.norm_eq_prod_automorphisms]
  congr 1
  apply Finset.prod_congr rfl
  intro σ _
  exact map_truncatedLog σ.toRingEquiv.toRingHom p z

private theorem support_degree_integralUniversalLogDefectWithoutNorm
    (F σ : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Fintype σ] [DecidableEq σ]
    (p : ℕ) (hp : 2 ≤ p) (hcard : Fintype.card σ = p)
    (hchar : residueCharacteristic F = p) :
    ∀ d ∈ (integralUniversalLogDefectWithoutNorm F σ p hchar).support,
      p ≤ d.degree := by
  intro d hd
  by_contra hdegree
  have hzero := coeff_integralUniversalLogDefectWithoutNorm_eq_zero
    F σ p hp hcard hchar d (Nat.lt_of_not_ge hdegree)
  exact (MvPolynomial.mem_support_iff.mp hd) hzero

private theorem support_degree_integralUniversalNormLogDefect
    (F σ : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Fintype σ] [DecidableEq σ]
    (p : ℕ) (hp : 2 ≤ p) (hcard : Fintype.card σ = p)
    (hchar : residueCharacteristic F = p) :
    ∀ d ∈ (integralUniversalNormLogDefect F σ p hchar).support,
      p ≤ d.degree := by
  intro d hd
  by_contra hdegree
  exact (MvPolynomial.mem_support_iff.mp hd)
    (coeff_integralUniversalNormLogDefect_eq_zero
      F σ p hp hcard hchar d (Nat.lt_of_not_ge hdegree))

/-- On a free orbit, each group element contributes exactly once. -/
private theorem sum_orbit_eq_sum_group_of_stabilizer_eq_bot
    {G X R : Type*} [Group G] [Fintype G] [MulAction G X]
    [AddCommMonoid R] (f : X → R) (x : X) [Fintype (MulAction.orbit G x)]
    (hstab : MulAction.stabilizer G x = ⊥) :
    ∑ y : MulAction.orbit G x, f y = ∑ g : G, f (g • x) := by
  classical
  let e : G ≃ MulAction.orbit G x :=
    Equiv.ofBijective (fun g ↦ ⟨g • x, MulAction.mem_orbit _ g⟩) ⟨by
      intro g k hgk
      have hgk' : g • x = k • x := congrArg Subtype.val hgk
      have hm : k⁻¹ * g ∈ MulAction.stabilizer G x :=
        MulAction.mem_stabilizer_iff.mpr (by rw [mul_smul, hgk', inv_smul_smul])
      rw [hstab, Subgroup.mem_bot] at hm
      exact (inv_mul_eq_one.mp hm).symm, by
      rintro ⟨y, ⟨g, hg⟩⟩
      exact ⟨g, Subtype.ext hg⟩⟩
  exact (Equiv.sum_comp e (fun y ↦ f y)).symm

/-- The different depth and the ceiling depth add to the required base-field depth. -/
private theorem normLog_base_depth (p T h : ℕ) (hp : 0 < p) :
    (((p - 1) * T : ℕ) : ℤ) / (p : ℤ) + (h + T ⌈/⌉ p : ℕ) =
      (T + h : ℕ) := by
  have hceil : ((T ⌈/⌉ p : ℕ) : ℤ) = integerCeilingDiv (T : ℤ) p := by
    rw [Nat.ceilDiv_eq_add_pred_div, integerCeilingDiv, Int.natCast_div]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ T + p), Nat.cast_add]
    simp
  change wildBaseDepth p T + (h + T ⌈/⌉ p : ℕ) = (T + h : ℕ)
  rw [wildBaseDepth_eq_sub_integerCeilingDiv p T hp, ← hceil]
  push_cast
  ring

/-- A monomial of degree at least `p` acquires the target depth under trace. -/
private theorem normLog_trace_depth_le (p a target n : ℕ) (D : ℤ) (hp : 0 < p)
    (hbase : D / (p : ℤ) + (a : ℤ) = (target : ℤ)) (hn : p ≤ n) :
    (target : ℤ) ≤ (((n * a : ℕ) : ℤ) + D) / (p : ℤ) := by
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  calc
    (target : ℤ) = D / (p : ℤ) + (a : ℤ) := hbase.symm
    _ = (((p * a : ℕ) : ℤ) + D) / (p : ℤ) := by
      simpa [mul_comm, add_comm] using (Int.add_mul_ediv_right D (a : ℤ) hpZ.ne').symm
    _ ≤ (((n * a : ℕ) : ℤ) + D) / (p : ℤ) := by
      apply Int.ediv_le_ediv hpZ
      apply add_le_add_left
      exact_mod_cast Nat.mul_le_mul_right a hn

section NormLogBounds

variable (F K : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]

/-- Extension and descent of lattice membership, including elements of infinite valuation. -/
private theorem algebraMap_mem_lattice_iff (p : ℕ) (hp : 0 < p)
    (hram : ramificationIndex F K = p) (x : F) (r : ℤ) :
    algebraMap F K x ∈ lattice K ((p : ℤ) * r) ↔ x ∈ lattice F r := by
  rw [mem_lattice, mem_lattice, ord_algebraMap, hram]
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  cases hord : ord F x with
  | top =>
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
      simp [succ_nsmul]
  | coe v =>
      rw [← WithTop.coe_nsmul]
      norm_cast
      simp only [nsmul_eq_mul]
      exact mul_le_mul_iff_right₀ hpZ

variable [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]

/-- A translated monomial sum is an integral coefficient times an actual field trace. -/
private theorem normLog_trace_term_mem_lattice
    (p a target : ℕ) (D : ℤ) (hp : 0 < p)
    (hram : ramificationIndex F K = p)
    (hchar : residueCharacteristic F = p) (htrace : TraceIdealLowerBound F K p D)
    (z : K) (hz : z ∈ lattice K (a : ℤ)) (d : Gal(K/F) →₀ ℕ)
    (hdepth : (target : ℤ) ≤ (((d.degree * a : ℕ) : ℤ) + D) / (p : ℤ)) :
    let Q := integralUniversalNormLogDefect F Gal(K/F) p hchar
    ∑ g : Gal(K/F),
      algebraMap F K ↑(Q.coeff (Finsupp.equivMapDomain (Equiv.mulLeft g) d)) *
        conjugateMonomial z (Finsupp.equivMapDomain (Equiv.mulLeft g) d) ∈
      lattice K ((p * target : ℕ) : ℤ) := by
  classical
  dsimp only
  simp_rw [coeff_exponent_translate, conjugateMonomial_translate]
  rw [← Finset.mul_sum, ← trace_eq_sum_automorphisms, ← map_mul]
  apply (algebraMap_mem_lattice_iff F K p hp hram _ (target : ℤ)).2
  have htr := htrace _ _ (conjugateMonomial_mem_lattice F K hz d)
  have hc := (mem_lattice_zero_iff F).2
    ((integralUniversalNormLogDefect F Gal(K/F) p hchar).coeff d).property
  simpa using mul_mem_lattice F hc (lattice_antitone F hdepth htr)

/-- A fixed monomial is a norm power; its coefficient is divisible by the degree. -/
private theorem normLog_fixed_term_mem_lattice
    (p a target : ℕ) (D : ℤ) (hp : p.Prime)
    (hdegree : Module.finrank F K = p) (hcard : Fintype.card Gal(K/F) = p)
    (hram : ramificationIndex F K = p) (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = p) (htrace : TraceIdealLowerBound F K p D)
    (hbase : D / (p : ℤ) + (a : ℤ) = (target : ℤ))
    (z : K) (hz : z ∈ lattice K (a : ℤ)) (d : Gal(K/F) →₀ ℕ)
    (hd : p ≤ d.degree)
    (hfixed : ∀ g, Finsupp.equivMapDomain (Equiv.mulLeft g) d = d) :
    algebraMap F K
        ↑((integralUniversalNormLogDefect F Gal(K/F) p hchar).coeff d) *
      conjugateMonomial z d ∈ lattice K ((p * target : ℕ) : ℤ) := by
  classical
  have hconst := fixed_exponent_eq_constant d hfixed
  have hdeg : d.degree = p * d 1 := by
    rw [Finsupp.degree_eq_sum]
    simp_rw [hconst]
    simp [hcard]
  have hn : 1 ≤ d 1 := by nlinarith [hp.pos]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp
    (fixed_coefficient_mem_degree_span F Gal(K/F) p hp hcard
      (PrimeCyclicExtension.subgroup_eq_bot_or_eq_top F K) hchar d hfixed)
  have hmonomial : conjugateMonomial z d = algebraMap F K (norm F K z ^ d 1) := by
    simp only [conjugateMonomial, hconst]
    rw [Finset.prod_pow, map_pow, Algebra.norm_eq_prod_automorphisms]
  rw [hb, Subring.coe_mul, Subring.coe_natCast, hmonomial, ← map_mul]
  apply (algebraMap_mem_lattice_iff F K p hp.pos hram _ (target : ℤ)).2
  have hpb : (p : F) * (b : F) ∈ lattice F (D / (p : ℤ)) := by
    rw [mem_lattice, ord_mul]
    exact (degree_natCast_ord_bound F K p D hp.pos hdegree htrace).trans
      (le_add_of_nonneg_right ((ord_nonneg_iff_mem_integer F _).2 b.property))
  have hnorm : norm F K z ∈ lattice F (a : ℤ) := by
    rw [mem_lattice, ord_norm, hres, one_nsmul]
    exact hz
  apply lattice_antitone F _ (mul_mem_lattice F hpb (pow_mem_lattice_nat F hnorm (d 1)))
  rw [← hbase]
  apply add_le_add_right
  exact_mod_cast (show a ≤ d 1 * a by simpa using Nat.mul_le_mul_right a hn)

/-- Split the universal defect into free trace orbits and fixed norm monomials. -/
private theorem eval_integralUniversalNormLogDefect_mem_lattice
    (p a target : ℕ) (D : ℤ) (hp : p.Prime)
    (hdegree : Module.finrank F K = p) (hres : residueDegree F K = 1)
    (hram : ramificationIndex F K = p) (hchar : residueCharacteristic F = p)
    (htrace : TraceIdealLowerBound F K p D)
    (hbase : D / (p : ℤ) + (a : ℤ) = (target : ℤ))
    (z : K) (hz : z ∈ lattice K (a : ℤ)) :
    MvPolynomial.eval₂
      ((algebraMap F K).comp (ValuativeRel.valuation F).integer.subtype)
      (fun g : Gal(K/F) ↦ g z) (integralUniversalNormLogDefect F Gal(K/F) p hchar) ∈
      lattice K ((p * target : ℕ) : ℤ) := by
  classical
  have hcard : Fintype.card Gal(K/F) = p := by
    rw [Fintype.card_eq_nat_card, PrimeCyclicExtension.galoisCard_eq_degree, hdegree]
  let Q := integralUniversalNormLogDefect F Gal(K/F) p hchar
  have hsupport : ∀ d ∈ Q.support, p ≤ d.degree :=
    support_degree_integralUniversalNormLogDefect F Gal(K/F) p hp.two_le hcard hchar
  let X := ↑Q.support
  letI : MulAction Gal(K/F) (Gal(K/F) →₀ ℕ) := exponentMulAction Gal(K/F)
  have hsmul_mem (g : Gal(K/F)) (x : X) : g • (x : Gal(K/F) →₀ ℕ) ∈ Q.support := by
    rw [MvPolynomial.mem_support_iff]
    change Q.coeff (Finsupp.equivMapDomain (Equiv.mulLeft g) (x : Gal(K/F) →₀ ℕ)) ≠ 0
    rw [coeff_exponent_translate F Gal(K/F) p hchar]
    exact MvPolynomial.mem_support_iff.mp x.property
  letI : MulAction Gal(K/F) X := {
    smul := fun g x ↦ ⟨g • (x : Gal(K/F) →₀ ℕ), hsmul_mem g x⟩
    one_smul := fun x ↦ Subtype.ext (one_smul Gal(K/F) (x : Gal(K/F) →₀ ℕ))
    mul_smul := fun g k x ↦ Subtype.ext (mul_smul g k (x : Gal(K/F) →₀ ℕ)) }
  let term : X → K := fun x ↦
    algebraMap F K ↑(Q.coeff (x : Gal(K/F) →₀ ℕ)) *
      conjugateMonomial z (x : Gal(K/F) →₀ ℕ)
  let Ω := MulAction.orbitRel.Quotient Gal(K/F) X
  letI : Fintype Ω := Fintype.ofFinite Ω
  letI (ω : Ω) : Fintype (MulAction.orbit Gal(K/F) ω.out) := Fintype.ofFinite _
  have horbit (ω : Ω) :
      ∑ y : MulAction.orbit Gal(K/F) ω.out, term y ∈
        lattice K ((p * target : ℕ) : ℤ) := by
    rcases PrimeCyclicExtension.subgroup_eq_bot_or_eq_top F K
      (MulAction.stabilizer Gal(K/F) ω.out) with hstab | hstab
    · rw [sum_orbit_eq_sum_group_of_stabilizer_eq_bot term ω.out hstab]
      exact normLog_trace_term_mem_lattice F K p a target D hp.pos hram hchar htrace z hz
        (ω.out : Gal(K/F) →₀ ℕ)
        (normLog_trace_depth_le p a target _ D hp.pos hbase (hsupport _ ω.out.property))
    · have hfixed (g : Gal(K/F)) : g • ω.out = ω.out :=
        MulAction.mem_stabilizer_iff.mp (hstab.symm ▸ Subgroup.mem_top g)
      let y₀ : MulAction.orbit Gal(K/F) ω.out := ⟨ω.out, MulAction.mem_orbit_self _⟩
      have heq (y : MulAction.orbit Gal(K/F) ω.out) : y = y₀ := by
        obtain ⟨g, hg⟩ := y.property
        exact Subtype.ext (hg.symm.trans (hfixed g))
      rw [Fintype.sum_eq_single y₀ (fun y hy ↦ (hy (heq y)).elim)]
      exact normLog_fixed_term_mem_lattice F K p a target D hp hdegree hcard hram hres
        hchar htrace hbase z hz _ (hsupport _ ω.out.property)
        (fun g ↦ congrArg (fun x : X ↦ (x : Gal(K/F) →₀ ℕ)) (hfixed g))
  have hsum : ∑ x : X, term x ∈ lattice K ((p * target : ℕ) : ℤ) := by
    rw [sum_eq_sum_orbit_sums (G := Gal(K/F))]
    exact sum_mem_lattice K (fun ω _ ↦ horbit ω)
  rw [MvPolynomial.eval₂_eq']
  change ∑ d ∈ Q.support, algebraMap F K ↑(Q.coeff d) *
    ∏ i : Gal(K/F), (i z) ^ d i ∈ lattice K ((p * target : ℕ) : ℤ)
  rw [← Finset.sum_attach]
  exact hsum

end NormLogBounds

/-- The ramified half of Paper Lemma 6.3 (`O:I:normlogeq`). -/
theorem normLog
    (F K : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t) (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = Module.finrank F K)
    (hodd : Module.finrank F K ≠ 2)
    (h : ℕ) (z : K)
    (hz : z ∈ lattice K
      ((h + (t + 1) ⌈/⌉ Module.finrank F K : ℕ) : ℤ)) :
    truncatedLog (Module.finrank F K) (1 - norm F K (1 - z)) -
        trace F K (truncatedLog (Module.finrank F K) z) -
        norm F K (truncatedLog (Module.finrank F K) z) ∈
      lattice F ((t + 1 + h : ℕ) : ℤ) := by
  classical
  let p := Module.finrank F K
  let T := t + 1
  let a := h + T ⌈/⌉ p
  let target := T + h
  let D : ℤ := (((p - 1) * T : ℕ) : ℤ)
  have hp : p.Prime := PrimeCyclicExtension.degree_prime F K
  have hram : ramificationIndex F K = p := by
    simpa [hres] using (finrank_eq_ramificationIndex_mul_residueDegree F K).symm
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F K hres
  have htrace : TraceIdealLowerBound F K p D :=
    traceIdealLowerBound_of_integralGenerator F K ht hres pi hpi hgen
  have heval := eval_integralUniversalNormLogDefect_mem_lattice F K p a target D hp rfl
    hres hram hchar htrace (normLog_base_depth p T h hp.pos) z hz
  apply (algebraMap_mem_lattice_iff F K p hp.pos hram _ (target : ℤ)).1
  rw [algebraMap_normLogExpression F K p z,
    ← eval_integralUniversalNormLogDefect F K Gal(K/F) p hchar hp.two_le]
  exact heval

/-- The unramified half of Paper Lemma 6.3.  Its depth is the ceiling
`q₀ = ⌈T/p⌉`; the proof is independent of the ramified half. -/
theorem unramifiedNormLog
    (F K : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    (T : ℕ)
    (hchar : residueCharacteristic F = Module.finrank F K)
    (hunramified : ramificationIndex F K = 1)
    (z : K)
    (hz : z ∈ lattice K ((T ⌈/⌉ Module.finrank F K : ℕ) : ℤ)) :
    truncatedLog (Module.finrank F K) (1 - norm F K (1 - z)) -
        trace F K (truncatedLog (Module.finrank F K) z) ∈
      lattice F (T : ℤ) := by
  classical
  let p : ℕ := Module.finrank F K
  let q : ℕ := T ⌈/⌉ p
  have hp : p.Prime := PrimeCyclicExtension.degree_prime F K
  have hcard : Fintype.card Gal(K/F) = p := by
    rw [Fintype.card_eq_nat_card, PrimeCyclicExtension.galoisCard_eq_degree]
  let Q : MvPolynomial Gal(K/F) (ringOfIntegers F) :=
    integralUniversalLogDefectWithoutNorm F Gal(K/F) p hchar
  have hdegree : ∀ d ∈ Q.support, p ≤ d.degree := by
    exact support_degree_integralUniversalLogDefectWithoutNorm
      F Gal(K/F) p hp.two_le hcard hchar
  have hconj (σ : Gal(K/F)) : σ z ∈ lattice K (q : ℤ) := by
    change ((q : ℤ) : WithTop ℤ) ≤ ord K (σ z)
    simpa [q, p, mem_lattice] using hz
  have heval := eval₂_mem_lattice_of_support_degree
    F K Gal(K/F) p q Q hdegree (fun σ ↦ σ z) hconj
  have hdepth : T ≤ p * q := by
    simpa [nsmul_eq_mul, mul_comm] using
      (le_smul_ceilDiv (b := T) (a := p) hp.pos)
  have hevalT : MvPolynomial.eval₂
      ((algebraMap F K).comp (ValuativeRel.valuation F).integer.subtype)
      (fun σ : Gal(K/F) ↦ σ z) Q ∈ lattice K (T : ℤ) :=
    lattice_antitone K (by exact_mod_cast hdepth) heval
  have hevalFormula := eval_integralUniversalLogDefectWithoutNorm
    F K Gal(K/F) p hchar hp.two_le (fun σ ↦ σ z)
  have hmapFormula := algebraMap_normLogExpressionWithoutNorm F K p z
  have hmapMem : algebraMap F K
      (truncatedLog p (1 - norm F K (1 - z)) - trace F K (truncatedLog p z)) ∈
      lattice K (T : ℤ) := by
    rw [hmapFormula, ← hevalFormula]
    exact hevalT
  rw [mem_lattice] at hmapMem ⊢
  rw [ord_algebraMap, hunramified, one_nsmul] at hmapMem
  exact hmapMem

end

end LanglandsSecondMainLemma.Odd
