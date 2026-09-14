import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Total.NormCoefficients
import LanglandsSecondMainLemma.Odd.Total.TraceNorm

/-!
# Odd / Total / Second Defect

Paper Proposition `O:A:prop:g` (7.10). The linear defect is a crossed
trace pairing with the actual norm minus the Artin--Schreier constant.
Its full coefficient expansion gives the nonexceptional estimate,
including exponent zero. The exceptional coefficient defines one fixed
`omega`, and coefficient extraction controls its difference from the
actual symmetric coefficient `s` in the top field.
-/

namespace LanglandsSecondMainLemma.Odd.Total

open LanglandsFirstMainLemma
open scoped BigOperators

noncomputable section

private theorem integral_natCast
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (n : ℕ) : (n : E) ∈ lattice E 0 := by
  rw [mem_lattice]
  exact (ord_nonneg_iff_mem_integer E _).2 (n : ringOfIntegers E).property

/-- Trace transitivity identifies the two genuine lower traces with a
single pairing over the second intermediate field. -/
theorem secondDefect_trace_pairing
    (A E₁ E₂ L : Type*) [Field A] [Field E₁] [Field E₂] [Field L]
    [Algebra A E₁] [Algebra A E₂] [Algebra A L]
    [Algebra E₁ L] [Algebra E₂ L]
    [IsScalarTower A E₁ L] [IsScalarTower A E₂ L]
    [Module.Free A E₁] [Module.Finite A E₁]
    [Module.Free A E₂] [Module.Finite A E₂]
    [Module.Free E₁ L] [Module.Finite E₁ L]
    [Module.Free E₂ L] [Module.Finite E₂ L]
    (b : E₁) (a : E₂) (z : L) :
    trace A E₁ (b * trace E₁ L z) - trace A E₂ (a * trace E₂ L z) =
      trace A E₂ (trace E₂ L ((algebraMap E₁ L b - algebraMap E₂ L a) * z)) := by
  have hlin₁ : trace E₁ L (algebraMap E₁ L b * z) = b * trace E₁ L z := by
    simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self_apply] using
      (map_smul (trace E₁ L) b z)
  have hlin₂ : trace E₂ L (algebraMap E₂ L a * z) = a * trace E₂ L z := by
    simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self_apply] using
      (map_smul (trace E₂ L) a z)
  rw [sub_mul, map_sub, map_sub, hlin₂, ← hlin₁, Algebra.trace_trace,
    Algebra.trace_trace]

section Moments

variable {E L : Type*} [Field E] [Field L] [Algebra E L]

/-- Expanding the crossed pairing keeps every polynomial coefficient. -/
theorem secondDefect_coefficient_pairing
    {p : ℕ} (Delta beta : L) (Z : Fin p → E)
    (hZ : beta = ∑ l : Fin p, algebraMap E L (Z l) * Delta ^ (l : ℕ))
    (x : E) (j : ℕ) :
    trace E L (beta * (algebraMap E L x * Delta ^ j)) =
      ∑ l : Fin p, x * Z l * trace E L (Delta ^ ((l : ℕ) + j)) := by
  rw [hZ, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have heq : algebraMap E L (Z l) * Delta ^ (l : ℕ) *
      (algebraMap E L x * Delta ^ j) =
      algebraMap E L (x * Z l) * Delta ^ ((l : ℕ) + j) := by
    rw [map_mul, pow_add]
    ring
  rw [heq]
  simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self_apply] using
    (map_smul (trace E L) (x * Z l) (Delta ^ ((l : ℕ) + j)))

private theorem subtract_constant_expansion
    {p : ℕ} (hp : 0 < p) (Delta beta : L) (a : E) (Y : Fin p → E)
    (hY : beta = ∑ l : Fin p, algebraMap E L (Y l) * Delta ^ (l : ℕ)) :
    beta - algebraMap E L a =
      ∑ l : Fin p, algebraMap E L (Y l - if (l : ℕ) = 0 then a else 0) *
        Delta ^ (l : ℕ) := by
  classical
  simp only [map_sub, sub_mul, Finset.sum_sub_distrib, ← hY]
  congr 1
  rw [Finset.sum_eq_single (⟨0, hp⟩ : Fin p)]
  · simp
  · intro l hl hne
    have hl0 : (l : ℕ) ≠ 0 := by simpa [Fin.ext_iff] using hne
    simp [hl0]
  · simp

variable [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

private theorem moments_integral
    (pb : PowerBasis E L) {p : ℕ} (hp : 2 < p) (hdim : pb.dim = p)
    (a : E) (hroot : pb.gen ^ p - pb.gen = algebraMap E L a)
    (hpa : (p : E) * a ∈ lattice E 0)
    (k : ℕ) (hk : k ≤ 2 * p - 2) :
    trace E L (pb.gen ^ k) ∈ lattice E 0 := by
  by_cases hk0 : k = 0
  · subst k
    rw [pow_zero, show (1 : L) = algebraMap E L 1 by simp,
      Algebra.trace_algebraMap_of_basis pb.basis]
    simpa [hdim] using integral_natCast E p
  · rw [artinSchreier_powerTraces pb hp hdim a hroot k (by omega) hk]
    apply (lattice E 0).add_mem
    · apply (lattice E 0).add_mem
      · split_ifs <;> simp_all only [integral_natCast, Submodule.zero_mem]
      · split_ifs <;> simp_all only [Submodule.zero_mem]
    · split_ifs <;> simp_all only [integral_natCast, Submodule.zero_mem]

/-- Only the degree-`p` moment can survive at the linear coefficient in a
nonexceptional exponent. Its `p*a` factor is retained in both characteristics. -/
private theorem nonexceptional_linear_moment
    (pb : PowerBasis E L) {p : ℕ} (hp : 2 < p) (hdim : pb.dim = p)
    (a : E) (hroot : pb.gen ^ p - pb.gen = algebraMap E L a)
    (n : ℤ) (hpa : (p : E) * a ∈ lattice E n)
    (j : ℕ) (hj : j < p) (hne : j ≠ p - 2) :
    trace E L (pb.gen ^ (1 + j)) ∈ lattice E n := by
  rw [artinSchreier_powerTraces pb hp hdim a hroot (1 + j) (by omega) (by omega)]
  simp only [if_neg (show 1 + j ≠ p - 1 by omega),
    if_neg (show 1 + j ≠ 2 * p - 2 by omega), zero_add, add_zero]
  split_ifs
  · exact hpa
  · exact (lattice E n).zero_mem

end Moments

section CoefficientEstimates

variable {E L : Type*} [Field E] [Field L] [Algebra E L]
variable [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

/-- All nonexceptional exponents, including zero, follow from the same
full coefficient expansion of `b-a`. -/
theorem secondDefect_nonexceptional_pairing
    (pb : PowerBasis E L) {p : ℕ} (hp : 2 < p) (hdim : pb.dim = p)
    (a : E) (hroot : pb.gen ^ p - pb.gen = algebraMap E L a)
    (n : ℤ) (hn : 0 ≤ n) (hpa : (p : E) * a ∈ lattice E n)
    (beta : L) (Z : Fin p → E)
    (hZ : beta = ∑ l : Fin p, algebraMap E L (Z l) * pb.gen ^ (l : ℕ))
    (hZ₁ : Z ⟨1, by omega⟩ ∈ lattice E 0)
    (hZdeep : ∀ l : Fin p, (l : ℕ) ≠ 1 → Z l ∈ lattice E n)
    (x : E) (hx : x ∈ lattice E 1) (j : ℕ) (hj : j < p)
    (hne : j ≠ p - 2) :
    trace E L (beta * (algebraMap E L x * pb.gen ^ j)) ∈ lattice E (1 + n) := by
  rw [secondDefect_coefficient_pairing pb.gen beta Z hZ x j]
  apply sum_mem_lattice E
  intro l hl
  rw [mul_assoc]
  apply mul_mem_lattice E hx
  by_cases hl1 : (l : ℕ) = 1
  · have heq : l = ⟨1, by omega⟩ := Fin.ext hl1
    rw [heq]
    simpa using mul_mem_lattice E hZ₁
      (nonexceptional_linear_moment pb hp hdim a hroot n hpa j hj hne)
  · simpa using mul_mem_lattice E (hZdeep l hl1)
      (moments_integral pb hp hdim a hroot (lattice_antitone E hn hpa)
        ((l : ℕ) + j) (by have := l.isLt; omega))

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
/-- The exact exceptional trace has precisely the linear and quadratic
coefficients. In particular, the mixed-characteristic term is `p*a*Z₂`. -/
theorem secondDefect_exceptional_pairing
    (pb : PowerBasis E L) {p : ℕ} (hp : 2 < p) (hdim : pb.dim = p)
    (a : E) (hroot : pb.gen ^ p - pb.gen = algebraMap E L a)
    (beta : L) (Z : Fin p → E)
    (hZ : beta = ∑ l : Fin p, algebraMap E L (Z l) * pb.gen ^ (l : ℕ))
    (x : E) :
    trace E L (beta * (algebraMap E L x * pb.gen ^ (p - 2))) =
      x * (((p - 1 : ℕ) : E) * Z ⟨1, by omega⟩ +
        (p : E) * a * Z ⟨2, hp⟩) := by
  classical
  rw [secondDefect_coefficient_pairing pb.gen beta Z hZ x (p - 2)]
  have hm (l : Fin p) : trace E L (pb.gen ^ ((l : ℕ) + (p - 2))) =
      (if l = ⟨1, by omega⟩ then ((p - 1 : ℕ) : E) else 0) +
      (if l = ⟨2, hp⟩ then (p : E) * a else 0) := by
    have hl := l.isLt
    rw [artinSchreier_powerTraces pb hp hdim a hroot _ (by omega) (by omega)]
    have h1 : (l : ℕ) + (p - 2) = p - 1 ↔ l = ⟨1, by omega⟩ := by
      simp only [Fin.ext_iff]; omega
    have h2 : (l : ℕ) + (p - 2) = p ↔ l = ⟨2, hp⟩ := by
      simp only [Fin.ext_iff]; omega
    simp only [h1, h2, if_neg (show (l : ℕ) + (p - 2) ≠ 2 * p - 2 by omega),
      add_zero]
  simp_rw [hm, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

variable [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
variable [ValuativeExtension E L]

private theorem map_mem_lattice {p : ℕ} (hram : ramificationIndex E L = p)
    {n : ℤ} {x : E} (hx : x ∈ lattice E n) :
    algebraMap E L x ∈ lattice L ((p : ℤ) * n) := by
  rw [mem_lattice, ord_algebraMap, hram]
  simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using
    nsmul_le_nsmul_right ((mem_lattice E).mp hx) p

/-- The valuation condition implies a positive downstairs weight and
retains its full, unrounded depth in the top field. Zero is included. -/
private theorem monomial_weight_depth
    {p : ℕ} (hp : 0 < p) (hram : ramificationIndex E L = p)
    (Delta : L) (t d : ℤ) (ht : 0 ≤ t) (hd : 0 ≤ d)
    (hDelta : ord L Delta = ((-t : ℤ) : WithTop ℤ))
    (x : E) (j : ℕ)
    (hx : algebraMap E L x * Delta ^ j ∈ lattice L (1 + d)) :
    x ∈ lattice E 1 ∧ algebraMap E L x ∈ lattice L (1 + d + (j : ℤ) * t) := by
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff E).2 hx0)
  rw [mem_lattice, ord_mul, ord_algebraMap, hram, ← hq, ord_pow, hDelta,
    ← WithTop.coe_nsmul, ← WithTop.coe_nsmul, ← WithTop.coe_add,
    WithTop.coe_le_coe] at hx
  simp only [nsmul_eq_mul] at hx
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  have hjt : 0 ≤ (j : ℤ) * t := mul_nonneg (Int.natCast_nonneg _) ht
  constructor
  · rw [mem_lattice, ← hq, WithTop.coe_le_coe]
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos hpZ.le (show q ≤ 0 by omega)
    nlinarith
  · rw [mem_lattice, ord_algebraMap, hram, ← hq, ← WithTop.coe_nsmul,
      WithTop.coe_le_coe]
    simp only [nsmul_eq_mul]
    nlinarith

/-- Coefficient extraction controls the entire nonconstant part of `s`,
not just one of its character values. -/
theorem secondDefect_nonconstant_mem
    {p : ℕ} (hp : 0 < p) (hram : ramificationIndex E L = p)
    (Delta sigma : L) (t c : ℤ) (ht : 0 ≤ t)
    (hDelta : ord L Delta = ((-t : ℤ) : WithTop ℤ))
    (s : Fin p → E)
    (hs : sigma = ∑ l : Fin p, algebraMap E L (s l) * Delta ^ (l : ℕ))
    (hcoeff : ∀ l : Fin p, s l ∈ lattice E (c + (l : ℤ) * t)) :
    sigma - algebraMap E L (s ⟨0, hp⟩) ∈
      lattice L ((p : ℤ) * c + ((p : ℤ) - 1) * t) := by
  rw [subtract_constant_expansion hp Delta sigma (s ⟨0, hp⟩) s hs]
  apply sum_mem_lattice L
  intro l hl
  by_cases hl0 : (l : ℕ) = 0
  · have heq : l = ⟨0, hp⟩ := Fin.ext hl0
    subst l
    simp
  · simp only [if_neg hl0, sub_zero]
    have hpow : Delta ^ (l : ℕ) ∈ lattice L (-(l : ℤ) * t) := by
      rw [mem_lattice, ord_pow, hDelta, ← WithTop.coe_nsmul]
      simp [neg_mul, mul_neg]
    apply lattice_antitone L _
      (mul_mem_lattice L (map_mem_lattice hram (hcoeff l)) hpow)
    have hpZ : (1 : ℤ) ≤ p := by exact_mod_cast hp
    have hlZ : (1 : ℤ) ≤ l := by omega
    have hprod := mul_nonneg
      (mul_nonneg (show (0 : ℤ) ≤ p - 1 by omega) (show (0 : ℤ) ≤ l - 1 by omega)) ht
    nlinarith

/-- The full coefficient bounds imply the two conclusions of Proposition
7.10 for the supplied coordinate and coefficient expansions. The genuine
diamond constructor below supplies every assumption of this calculation. -/
theorem secondDefect_of_coefficients
    (pb : PowerBasis E L) {p : ℕ} (hp : 2 < p) (hdim : pb.dim = p)
    (hram : ramificationIndex E L = p)
    (a : E) (hroot : pb.gen ^ p - pb.gen = algebraMap E L a)
    (t t₂ d : ℤ) (ht : 0 ≤ t) (hd : 0 ≤ d) (ht₂ : t₂ = t + d)
    (hDelta : ord L pb.gen = ((-t : ℤ) : WithTop ℤ))
    (ha : a ∈ lattice E (-t))
    (hpval : (p : E) ∈ lattice E (((p : ℤ) - 1) * t₂))
    (beta sigma : L) (Y s : Fin p → E)
    (hY : beta = ∑ l : Fin p, algebraMap E L (Y l) * pb.gen ^ (l : ℕ))
    (hs : sigma = ∑ l : Fin p, algebraMap E L (s l) * pb.gen ^ (l : ℕ))
    (hcoeff : ∀ l : Fin p,
      s l ∈ lattice E (((p : ℤ) - 1) * d + (l : ℤ) * t))
    (hYhigh : ∀ l : Fin p, 2 ≤ (l : ℕ) →
      Y l ∈ lattice E (((p : ℤ) - 1) * t₂ - ((p : ℤ) - l) * t))
    (hYzero : Y ⟨0, by omega⟩ - a ∈ lattice E (((p : ℤ) - 1) * t₂ - t))
    (error : E) (hYone : Y ⟨1, by omega⟩ = 1 - s ⟨0, by omega⟩ + error)
    (herror : error ∈ lattice E (((p : ℤ) - 1) * t₂)) :
    let omega : E := 1 + ((p - 1 : ℕ) : E) * Y ⟨1, by omega⟩ +
      (p : E) * a * Y ⟨2, hp⟩
    (∀ (x : E) (j : ℕ), j < p → j ≠ p - 2 →
      algebraMap E L x * pb.gen ^ j ∈ lattice L (1 + d) →
      trace E L ((beta - algebraMap E L a) * (algebraMap E L x * pb.gen ^ j)) ∈
        lattice E (1 + t₂)) ∧
    (∀ x : E, algebraMap E L x * pb.gen ^ (p - 2) ∈ lattice L (1 + d) →
      trace E L ((beta - algebraMap E L a) *
        (algebraMap E L x * pb.gen ^ (p - 2))) = x * (omega - 1) ∧
      algebraMap E L x * algebraMap E L omega - algebraMap E L x * sigma ∈
        lattice L (1 + (p : ℤ) * t₂)) := by
  let C : ℤ := ((p : ℤ) - 1) * t₂
  change (p : E) ∈ lattice E C at hpval
  change error ∈ lattice E C at herror
  change Y ⟨0, by omega⟩ - a ∈ lattice E (C - t) at hYzero
  have hpZ : (3 : ℤ) ≤ p := by omega
  have ht₂0 : 0 ≤ t₂ := by omega
  have ht₂C : t₂ ≤ C := by dsimp [C]; nlinarith
  have ht₂Ct : t₂ ≤ C - t := by dsimp [C]; nlinarith
  have hC0 : 0 ≤ C := ht₂0.trans ht₂C
  have hs0 : s ⟨0, by omega⟩ ∈ lattice E 0 := by
    apply lattice_antitone E _ (hcoeff ⟨0, by omega⟩)
    simp only [Nat.cast_zero, zero_mul, add_zero]
    exact mul_nonneg (by omega) hd
  have h1s : 1 - s ⟨0, by omega⟩ ∈ lattice E 0 :=
    (lattice E 0).sub_mem (by simp) hs0
  have hY1 : Y ⟨1, by omega⟩ ∈ lattice E 0 := by
    rw [hYone]
    exact (lattice E 0).add_mem h1s (lattice_antitone E hC0 herror)
  have hYdeep (l : Fin p) (hl : 2 ≤ (l : ℕ)) : Y l ∈ lattice E t₂ := by
    apply lattice_antitone E _ (hYhigh l hl)
    have hlZ : (2 : ℤ) ≤ l := by omega
    have hprod := mul_nonneg (show (0 : ℤ) ≤ l - 2 by omega) ht
    rw [ht₂]
    nlinarith
  have hpa : (p : E) * a ∈ lattice E t₂ :=
    lattice_antitone E (by simpa [sub_eq_add_neg] using ht₂Ct)
      (mul_mem_lattice E hpval ha)
  let Z (l : Fin p) := Y l - if (l : ℕ) = 0 then a else 0
  have hZ : beta - algebraMap E L a =
      ∑ l : Fin p, algebraMap E L (Z l) * pb.gen ^ (l : ℕ) :=
    subtract_constant_expansion (by omega) pb.gen beta a Y hY
  have hZ1 : Z ⟨1, by omega⟩ ∈ lattice E 0 := by simpa [Z] using hY1
  have hZdeep (l : Fin p) (hl : (l : ℕ) ≠ 1) : Z l ∈ lattice E t₂ := by
    by_cases hl0 : (l : ℕ) = 0
    · have heq : l = ⟨0, by omega⟩ := Fin.ext hl0
      rw [heq]
      exact lattice_antitone E ht₂Ct (by simpa [Z] using hYzero)
    · simpa [Z, hl0] using hYdeep l (by omega)
  dsimp only
  constructor
  · intro x j hj hne hx
    exact secondDefect_nonexceptional_pairing pb hp hdim a hroot t₂ ht₂0 hpa
      (beta - algebraMap E L a) Z hZ hZ1 hZdeep x
      (monomial_weight_depth (by omega) hram pb.gen t d ht hd hDelta x j hx).1 j hj hne
  · intro x hx
    have hweight := monomial_weight_depth (by omega) hram pb.gen t d ht hd hDelta
      x (p - 2) hx
    constructor
    · rw [secondDefect_exceptional_pairing pb hp hdim a hroot
        (beta - algebraMap E L a) Z hZ x]
      dsimp [Z]
      ring
    · let w : E := 1 + ((p - 1 : ℕ) : E) * Y ⟨1, by omega⟩ +
        (p : E) * a * Y ⟨2, hp⟩
      have hpaY : (p : E) * a * Y ⟨2, hp⟩ ∈ lattice E C := by
        apply lattice_antitone E _
          (mul_mem_lattice E (mul_mem_lattice E hpval ha) (hYhigh ⟨2, hp⟩ (by simp)))
        simp only [Nat.cast_ofNat]
        dsimp [C]
        nlinarith
      have hw0 : w - s ⟨0, by omega⟩ ∈ lattice E C := by
        have heq : w - s ⟨0, by omega⟩ =
            (p : E) * (1 - s ⟨0, by omega⟩) +
              ((p - 1 : ℕ) : E) * error + (p : E) * a * Y ⟨2, hp⟩ := by
          dsimp [w]
          rw [hYone, Nat.cast_sub (by omega)]
          push_cast
          ring
        rw [heq]
        apply (lattice E C).add_mem _ hpaY
        exact (lattice E C).add_mem
          (by simpa using mul_mem_lattice E hpval h1s)
          (by simpa using mul_mem_lattice E (integral_natCast E (p - 1)) herror)
      have hfirst : algebraMap E L (x * (w - s ⟨0, by omega⟩)) ∈
          lattice L (1 + (p : ℤ) * t₂) := by
        apply lattice_antitone L _
          (map_mem_lattice hram (mul_mem_lattice E hweight.1 hw0))
        nlinarith
      have hrest := secondDefect_nonconstant_mem (by omega) hram pb.gen sigma t
        (((p : ℤ) - 1) * d) ht hDelta s hs hcoeff
      have hsecond : algebraMap E L x * (sigma - algebraMap E L (s ⟨0, by omega⟩)) ∈
          lattice L (1 + (p : ℤ) * t₂) := by
        apply lattice_antitone L _ (mul_mem_lattice L hweight.2 hrest)
        rw [Nat.cast_sub (by omega), Nat.cast_ofNat, ht₂]
        have hnonneg := mul_nonneg (show (0 : ℤ) ≤ p - 3 by omega) ht
        have hnonneg' := mul_nonneg (sq_nonneg ((p : ℤ) - 1)) hd
        nlinarith
      have heq : algebraMap E L x * algebraMap E L w - algebraMap E L x * sigma =
          algebraMap E L (x * (w - s ⟨0, by omega⟩)) -
            algebraMap E L x * (sigma - algebraMap E L (s ⟨0, by omega⟩)) := by
        simp only [map_mul, map_sub]
        ring
      change algebraMap E L x * algebraMap E L w - algebraMap E L x * sigma ∈ _
      rw [heq]
      exact (lattice L _).sub_mem hfirst hsecond

end CoefficientEstimates

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K]
variable [Module.Free F K] [Module.Finite F K] [IsGalois F K]

set_option maxHeartbeats 800000 in
/-- **Paper Proposition 7.10 (`O:A:prop:g`).** From the actual odd totally
ramified diamond, construct an exact Artin--Schreier coordinate and one
fixed `omega` in `B₂`. The nonexceptional defect has depth `1+t₂` in `F`.
At exponent `p-2`, its trace formula is exact, and `x*omega-x*s` has
depth `K₀ = 1+p*t₂` in `K`, with `s` the actual symmetric coefficient.

The hypothesis on `R` is expressed by membership in an integer-depth
lattice, so it includes zero without excluding infinite valuations.
There is no restriction on the characteristic of the fields. -/
theorem secondDefect {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (D : OddTotalBreakData (F := F) (K := K) hp hG) :
    let B₁ := D.B₁
    let B₂ := D.B₂
    letI := Basic.intermediateFieldValuativeRel B₁
    letI := Basic.intermediateFieldTopology B₁
    letI := Basic.intermediateField_localField B₁
    letI := Basic.intermediateFieldValuativeRel B₂
    letI := Basic.intermediateFieldTopology B₂
    letI := Basic.intermediateField_localField B₂
    ∃ (Delta : K) (a omega : B₂),
      Delta ^ p - Delta = algebraMap B₂ K a ∧
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ¬ p ∣ D.t ∧ Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ ∧
      let g : K → F := fun z =>
        trace F B₁ (norm B₁ K Delta * trace B₁ K z) -
          trace F B₂ (a * trace B₂ K z)
      (∀ (x : B₂) (j : ℕ), j < p → j ≠ p - 2 →
        algebraMap B₂ K x * Delta ^ j ∈ lattice K (1 + (D.delta : ℤ)) →
        g (algebraMap B₂ K x * Delta ^ j) ∈ lattice F (1 + (D.t₂ : ℤ))) ∧
      (∀ x : B₂,
        algebraMap B₂ K x * Delta ^ (p - 2) ∈ lattice K (1 + (D.delta : ℤ)) →
        g (algebraMap B₂ K x * Delta ^ (p - 2)) = trace F B₂ (x * (omega - 1)) ∧
        algebraMap B₂ K x * algebraMap B₂ K omega -
          algebraMap B₂ K x *
            algebraMap B₁ K (-elementarySymmetric B₁ K (p - 1) Delta) ∈
          lattice K (1 + (p : ℤ) * D.t₂)) := by
  dsimp only [OddTotalBreakData.B₁, OddTotalBreakData.B₂]
  let B₁ := IntermediateField.fixedField D.H₁
  let B₂ := IntermediateField.fixedField D.H₂
  letI := Basic.intermediateFieldValuativeRel B₁
  letI := Basic.intermediateFieldTopology B₁
  letI := Basic.intermediateFieldValuativeRel B₂
  letI := Basic.intermediateFieldTopology B₂
  obtain ⟨hLocal₁, hFreeF₁, hFiniteF₁, hFree₁K, hFinite₁K, hScalar₁,
      hValF₁, hVal₁K, _htotal₁, _hdegreeLower₁, _hdegreeUpper₁,
      _hcycF₁, _hcyc₁K⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁
  letI := hLocal₁
  letI := hFreeF₁
  letI := hFiniteF₁
  letI := hFree₁K
  letI := hFinite₁K
  letI := hScalar₁
  letI := hValF₁
  letI := hVal₁K
  obtain ⟨hLocal₂, hFreeF₂, hFiniteF₂, hFree₂K, hFinite₂K, hScalar₂,
      hValF₂, hVal₂K, _htotal₂, hdegreeLower₂, hdegreeUpper₂,
      hcycF₂, _hcyc₂K⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
  letI := hLocal₂
  letI := hFreeF₂
  letI := hFiniteF₂
  letI := hFree₂K
  letI := hFinite₂K
  letI := hScalar₂
  letI := hValF₂
  letI := hVal₂K
  letI : IsGalois F B₂ := hcycF₂.1
  letI : PrimeCyclicExtension F B₂ :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F B₂ hcycF₂
  letI : IsScalarTower (ringOfIntegers F) (ringOfIntegers B₂) (ringOfIntegers K) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap F K (x : F) = algebraMap B₂ K (algebraMap F B₂ (x : F))
      rw [← IsScalarTower.algebraMap_apply F B₂ K])
  letI : IsLocalHom (algebraMap (ringOfIntegers F) (ringOfIntegers B₂)) := inferInstance
  letI : IsLocalHom (algebraMap (ringOfIntegers B₂) (ringOfIntegers K)) := inferInstance
  have hresmul : residueDegree F B₂ * residueDegree B₂ K = 1 := by
    rw [← hres, residueDegree_eq_finrank_residueField,
      residueDegree_eq_finrank_residueField, residueDegree_eq_finrank_residueField]
    exact Module.finrank_mul_finrank (ResidueField F) (ResidueField B₂) (ResidueField K)
  have hresF₂ : residueDegree F B₂ = 1 := (mul_eq_one.mp hresmul).1
  have hres₂K : residueDegree B₂ K = 1 := (mul_eq_one.mp hresmul).2
  have hramF₂ : ramificationIndex F B₂ = p := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F B₂
    simpa [hresF₂, hdegreeLower₂] using h.symm
  have hram₂K : ramificationIndex B₂ K = p := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree B₂ K
    simpa [hres₂K, hdegreeUpper₂] using h.symm
  have hpval : (p : B₂) ∈ lattice B₂ (((p : ℤ) - 1) * D.t₂) := by
    by_cases hpzero : (p : B₂) = 0
    · simp [hpzero]
    obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff B₂).2 hpzero)
    have hbound := oddTotal_primeValuationBound hp hG hres D
    rw [show (p : K) = algebraMap B₂ K (p : B₂) by simp,
      ord_algebraMap, hram₂K, ← hv, ← WithTop.coe_nsmul, WithTop.coe_le_coe] at hbound
    simp only [nsmul_eq_mul] at hbound
    push_cast [Nat.cast_sub hp.one_le] at hbound
    rw [mem_lattice, ← hv, WithTop.coe_le_coe]
    exact le_of_mul_le_mul_left (by simpa only [mul_assoc] using hbound)
      (by exact_mod_cast hp.pos)
  have hbreak₂ : PrimeCyclicExtension.IsLowerBreak F B₂ D.t₂ := by
    simpa only [B₂, Ramification.IntermediateBreakPair] using D.B₂_breaks.1
  have hdiff₂ : (differentExponent F B₂ : ℤ) =
      ((p : ℤ) - 1) * ((D.t₂ : ℤ) + 1) := by
    obtain ⟨pi, hpi, hgen⟩ :=
      exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one F B₂ hresF₂
    rw [differentExponent_eq F B₂ hbreak₂ pi hpi hgen, hdegreeLower₂]
    push_cast [Nat.cast_sub hp.one_le]
    rfl
  have htrace (z : B₂) (hz : z ∈ lattice B₂ (1 + (D.t₂ : ℤ))) :
      trace F B₂ z ∈ lattice F (1 + (D.t₂ : ℤ)) := by
    have hmem : trace F B₂ z ∈ Submodule.map
        ((trace F B₂).restrictScalars (ringOfIntegers F))
        ((lattice B₂ (1 + (D.t₂ : ℤ))).restrictScalars (ringOfIntegers F)) :=
      Submodule.mem_map.mpr ⟨z, hz, rfl⟩
    rw [Local.traceIdeal_eq_fml F B₂ hresF₂, hdiff₂, hramF₂,
      show 1 + (D.t₂ : ℤ) + ((p : ℤ) - 1) * (D.t₂ + 1) =
        (1 + (D.t₂ : ℤ)) * p by ring,
      Int.mul_ediv_cancel _ (by exact_mod_cast hp.ne_zero)] at hmem
    exact hmem
  have hdata := normCoefficients hp hG hres hchar D
  dsimp only [OddTotalBreakData.B₁, OddTotalBreakData.B₂] at hdata
  obtain ⟨Delta, a, Y, s, hroot, hDelta, ha, hprime, hgen, hcoeff, _htr, _hsym,
      _hei, hsord, hY, hs, hYhigh, hYzero, error, hYone, herror⟩ := hdata
  let pb : PowerBasis B₂ K :=
    PowerBasis.ofAdjoinEqTop (IsAlgebraic.of_finite B₂ Delta).isIntegral hgen
  have hpbgen : pb.gen = Delta := PowerBasis.ofAdjoinEqTop_gen _ _
  have hpbdim : pb.dim = p := by rw [← pb.finrank]; exact hdegreeUpper₂
  have hscoeff (l : Fin p) :
      s l ∈ lattice B₂ (((p : ℤ) - 1) * D.delta + (l : ℤ) * D.t) := by
    rw [mem_lattice, WithTop.coe_add]
    have h := add_le_add_right hsord ((((l : ℕ) * D.t : ℕ) : ℤ) : WithTop ℤ)
    have h' := h.trans (by simpa only [add_comm] using hcoeff _ s hs l)
    simpa only [Nat.cast_mul, add_comm] using h'
  have hcalc := secondDefect_of_coefficients pb D.odd_prime hpbdim hram₂K
    a (by simpa only [hpbgen] using hroot) D.t D.t₂ D.delta
    (by positivity) (by positivity) (by exact_mod_cast D.t₂_eq)
    (by simpa only [hpbgen] using hDelta) (by rw [mem_lattice, ha]) hpval
    (algebraMap B₁ K (norm B₁ K Delta))
    (algebraMap B₁ K (-elementarySymmetric B₁ K (p - 1) Delta)) Y s
    (by simpa only [hpbgen] using hY) (by simpa only [hpbgen] using hs) hscoeff
    (by intro l hl; exact (mem_lattice B₂).2 (hYhigh l hl))
    ((mem_lattice B₂).2 hYzero) error hYone ((mem_lattice B₂).2 herror)
  dsimp only at hcalc
  simp only [hpbgen] at hcalc
  let omega : B₂ := 1 + ((p - 1 : ℕ) : B₂) * Y ⟨1, hp.one_lt⟩ +
    (p : B₂) * a * Y ⟨2, D.odd_prime⟩
  refine ⟨Delta, a, omega, hroot, hDelta, ha, hprime, hgen, ?_, ?_⟩
  · intro x j hj hne hx
    rw [secondDefect_trace_pairing F B₁ B₂ K]
    exact htrace _ (hcalc.1 x j hj hne hx)
  · intro x hx
    obtain ⟨heq, hclose⟩ := hcalc.2 x hx
    refine ⟨?_, hclose⟩
    rw [secondDefect_trace_pairing F B₁ B₂ K, heq]

end

end LanglandsSecondMainLemma.Odd.Total
