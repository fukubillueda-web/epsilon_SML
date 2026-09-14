import LanglandsSecondMainLemma.EqualChar.Cartier

/-!
# The rational Cartier identity in equal characteristic two

This file proves Lemma 11.3 (`D:EQ:rationalCartier`) of the corrected
manuscript. A Laurent differential is represented by its Laurent-series
coefficient, so multiplication by `dϖ` is implicit below. The uniformizer
`ϖ` is `HahnSeries.single 1 1`.
-/

open scoped LaurentSeries
open HahnSeries

namespace LanglandsSecondMainLemma.Dyadic.Equal

noncomputable section

variable {k : Type*} [Field k] [Finite k] [CharP k 2]

local instance : Algebra (ZMod 2) k := ZMod.algebra k 2

local notation "ϖ" => (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩)

omit [Finite k] [CharP k 2] in
/-- The denominator `1 + ϖ w²` cannot vanish: otherwise its order would say
that the odd integer `1 + 2 * order w` is zero. -/
private lemma denominator_ne_zero (w : k⸨X⸩) :
    1 + ϖ * w ^ 2 ≠ 0 := by
  intro h
  have hw : w ≠ 0 := by
    intro hw
    subst w
    simp at h
  rw [add_comm] at h
  have hprod : ϖ * w ^ 2 = -1 := add_eq_zero_iff_eq_neg.mp h
  have hϖ : ϖ ≠ (0 : k⸨X⸩) := by
    exact HahnSeries.single_ne_zero (show (1 : k) ≠ 0 from one_ne_zero)
  have horder := congrArg HahnSeries.order hprod
  rw [HahnSeries.order_mul hϖ (pow_ne_zero 2 hw),
    HahnSeries.order_single one_ne_zero, HahnSeries.order_pow,
    HahnSeries.order_neg, HahnSeries.order_one] at horder
  norm_num at horder
  omega

/-- Additivity of Cartier, recorded locally because the corresponding supporting
lemma in `EqualChar.Cartier` is intentionally private. -/
private lemma cartier_add (eta omega : Residues.FormalDifferential k) :
    EqualChar.cartier (eta + omega) =
      EqualChar.cartier eta + EqualChar.cartier omega := by
  ext m
  apply CharTwo.sq_injective
  change (EqualChar.cartier (eta + omega)).coeff m ^ 2 =
    (EqualChar.cartier eta + EqualChar.cartier omega).coeff m ^ 2
  simp [EqualChar.cartier, CharTwo.add_sq]

/-- Cartier sends `ϖ dϖ` to `dϖ`. -/
private lemma cartier_uniformizer :
    EqualChar.cartier ϖ = (1 : k⸨X⸩) := by
  ext m
  apply CharTwo.sq_injective
  change (EqualChar.cartier ϖ).coeff m ^ 2 =
    (1 : k⸨X⸩).coeff m ^ 2
  simp [EqualChar.cartier]
  by_cases hm : m = 0
  · subst m
    simp
  · have hindex : 2 * m + 1 ≠ 1 := by omega
    rw [HahnSeries.coeff_single_of_ne hindex]
    simp [hm]

/-- Cartier kills the differential `dϖ`. -/
private lemma cartier_one :
    EqualChar.cartier (1 : k⸨X⸩) = 0 := by
  ext m
  apply CharTwo.sq_injective
  change (EqualChar.cartier (1 : k⸨X⸩)).coeff m ^ 2 =
    (0 : k⸨X⸩).coeff m ^ 2
  simp [EqualChar.cartier]
  omega

/-- **A local Cartier calculation** (Lemma 11.3,
`D:EQ:rationalCartier`). For `F = k((ϖ))`, the denominator is nonzero and
the absolute traces of the two indicated residues agree. -/
theorem cartierRational (f w : k⸨X⸩) :
    (1 + ϖ * w ^ 2 ≠ 0) ∧
      Algebra.trace (ZMod 2) k
          (Residues.residue (ϖ * f ^ 2 / (1 + ϖ * w ^ 2))) =
        Algebra.trace (ZMod 2) k
          (Residues.residue (f / (1 + ϖ * w ^ 2))) := by
  let H : k⸨X⸩ := 1 + ϖ * w ^ 2
  have hH : H ≠ 0 := denominator_ne_zero w
  refine ⟨hH, ?_⟩
  have hdecomp : ϖ * f ^ 2 / H =
      ϖ * (f / H) ^ 2 + (ϖ * (f * w / H)) ^ 2 := by
    field_simp
    ring
  rw [← EqualChar.cartier_residueTrace (ϖ * f ^ 2 / H)]
  rw [hdecomp, cartier_add]
  have hfirst : EqualChar.cartier (ϖ * (f / H) ^ 2) = f / H := by
    rw [mul_comm]
    rw [EqualChar.cartier_square_mul, cartier_uniformizer, mul_one]
  have hsecond : EqualChar.cartier ((ϖ * (f * w / H)) ^ 2) = 0 := by
    rw [show (ϖ * (f * w / H)) ^ 2 =
      (ϖ * (f * w / H)) ^ 2 * (1 : k⸨X⸩) by simp]
    rw [EqualChar.cartier_square_mul, cartier_one, mul_zero]
  rw [hfirst, hsecond, add_zero]

end

end LanglandsSecondMainLemma.Dyadic.Equal
