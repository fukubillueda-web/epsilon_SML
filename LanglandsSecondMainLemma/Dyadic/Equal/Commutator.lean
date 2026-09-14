import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Dyadic.Equal.Origin
import LanglandsSecondMainLemma.Characters.CrossedNorm
import LanglandsSecondMainLemma.Characters.QuadraticProduct

/-!
# Dyadic / Equal / Commutator

Paper Lemma 11.4, `D:EQ:commmodel`, with its full domain of nonzero
elements whose conjugate quotient lies in the stationary unit subgroup.
The calculations retain the exact simultaneous origin and the actual norm
character. All discarded terms are checked at the integer depth `T₂`.

The rational phase comparison uses the proved Artin--Schreier invariance
of the residue symbol, whose proof already applies Cartier. This avoids
the anonymous-instance collision between `Origin` and `CartierRational`
without changing either dependency.

`commutator_origin_character_reduction` gives the exact rational trace and
the actual norm-character residue value on the full required domain.
`commutator_residue_before_cartier`, `commutator_polar_denominator`, and
`commutator_trace_phase` supply the local reductions and depth estimates.
`commutator_phase_comparison` completes the rational phase comparison;
`commutator` assembles the full compatibility for `Dyadic/Equal/Models`.
-/

open scoped LaurentSeries
open HahnSeries LanglandsFirstMainLemma
namespace LanglandsSecondMainLemma.Dyadic.Equal
noncomputable section

open private laurentDerivative_mul from LanglandsSecondMainLemma.Residues.LogNorm

local instance commutatorLaurentChar (k : Type*) [Field k] [CharP k 2] : CharP (k⸨X⸩) 2 :=
  CharP.of_ringHom_of_ne_zero (HahnSeries.C : k →+* k⸨X⸩) 2 (by norm_num)

section Laurent
variable {k : Type*} [Field k] [Finite k] [CharP k 2]
local instance commutatorLaurentAlgebra : Algebra (ZMod 2) k := ZMod.algebra k 2

omit [Finite k] in
private theorem phase_add (T : ℤ) (x y : k⸨X⸩) :
    scaledResiduePhase T (x + y) = scaledResiduePhase T x * scaledResiduePhase T y := by
  simp [scaledResiduePhase, mul_add, Residues.residue, AddChar.map_add_eq_mul]

omit [Finite k] in
/-- Congruence is tested at the whole actual additive-character modulus. -/
private theorem phase_congr (T : ℤ) (x y : k⸨X⸩)
    (h : (T : WithTop ℤ) ≤ (x - y).orderTop) :
    scaledResiduePhase T x = scaledResiduePhase T y := by
  have hc := HahnSeries.coeff_eq_zero_of_lt_orderTop
    ((WithTop.coe_lt_coe.mpr (by omega : T - 1 < T)).trans_le h)
  rw [HahnSeries.coeff_sub, sub_eq_zero] at hc
  simp only [scaledResiduePhase, Residues.residue, HahnSeries.coeff_single_mul,
    one_mul, show (-1 : ℤ) - -T = T - 1 by omega, hc]

omit [Finite k] [CharP k 2] in
private theorem order_mul_bound {x y : k⸨X⸩} {a b : ℤ}
    (hx : (a : WithTop ℤ) ≤ x.orderTop) (hy : (b : WithTop ℤ) ≤ y.orderTop) :
    ((a + b : ℤ) : WithTop ℤ) ≤ (x * y).orderTop := by
  rw [HahnSeries.orderTop_mul, WithTop.coe_add]
  exact add_le_add hx hy

omit [Finite k] [CharP k 2] in
private theorem order_unit_inv {u : k⸨X⸩} (hu : u.orderTop = 0) :
    u⁻¹.orderTop = 0 := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have h := HahnSeries.orderTop_mul (x := u) (y := u⁻¹)
  rw [mul_inv_cancel₀ hu0, HahnSeries.orderTop_one, hu, zero_add] at h
  exact h.symm

omit [Finite k] [CharP k 2] in
private theorem order_div_unit {x u : k⸨X⸩} (hu : u.orderTop = 0) :
    (x / u).orderTop = x.orderTop := by
  rw [div_eq_mul_inv, HahnSeries.orderTop_mul, order_unit_inv hu, add_zero]

omit [Finite k] [CharP k 2] in
private theorem order_one_add {x : k⸨X⸩} (hx : 0 < x.orderTop) :
    (1 + x).orderTop = 0 := by
  exact (HahnSeries.orderTop_add_eq_left (by simpa using hx)).trans HahnSeries.orderTop_one

omit [Finite k] in
private theorem derivative_square (x : k⸨X⸩) : LaurentSeries.derivative k (x ^ 2) = 0 := by
  rw [pow_two, laurentDerivative_mul, mul_comm x, CharTwo.add_self_eq_zero]

omit [Finite k] [CharP k 2] in
/-- The unit denominators and the final two errors in the proof of
(D:EQ:commmodel). The errors have depth `2r = T₂`, including when the
coefficient or the coordinate is zero. -/
theorem commutator_denominator_depths (r : ℤ) (hr : 0 < r)
    (f w κ B : k⸨X⸩) (hf : ((1 - 2 * r : ℤ) : WithTop ℤ) ≤ f.orderTop)
    (hw : (r : WithTop ℤ) ≤ w.orderTop)
    (hκ : 0 ≤ κ.orderTop) (hB : 0 ≤ B.orderTop) :
    let R := w ^ 2 * f
    let H := 1 + R
    let V := H + w
    (1 : WithTop ℤ) ≤ R.orderTop ∧ H.orderTop = 0 ∧ V.orderTop = 0 ∧
      (r : WithTop ℤ) ≤ (w / H).orderTop ∧
      ((2 * r : ℤ) : WithTop ℤ) ≤ (κ * w / H - κ * w / V).orderTop ∧
      ((2 * r : ℤ) : WithTop ℤ) ≤ (B * w ^ 2 / V).orderTop := by
  let R := w ^ 2 * f
  let H := 1 + R
  let V := H + w
  have hw2 : ((2 * r : ℤ) : WithTop ℤ) ≤ (w ^ 2).orderTop := by
    simpa only [pow_two, two_mul] using order_mul_bound hw hw
  have hR : (1 : WithTop ℤ) ≤ R.orderTop := by
    simpa only [show 2 * r + (1 - 2 * r) = 1 by omega, WithTop.coe_one]
      using order_mul_bound hw2 hf
  have hH : H.orderTop = 0 := order_one_add (lt_of_lt_of_le (by norm_num) hR)
  have hwpos : 0 < w.orderTop := (WithTop.coe_lt_coe.mpr hr).trans_le hw
  have hV : V.orderTop = 0 := by
    exact (HahnSeries.orderTop_add_eq_left (by rw [hH]; exact hwpos)).trans hH
  have hH0 : H ≠ 0 := by intro h; simp [h] at hH
  have hV0 : V ≠ 0 := by intro h; simp [h] at hV
  have hHV : (H * V).orderTop = 0 := by rw [HahnSeries.orderTop_mul, hH, hV, add_zero]
  have hdiff : κ * w / H - κ * w / V = κ * w ^ 2 / (H * V) := by
    field_simp
    dsimp [V]
    ring
  refine ⟨hR, hH, hV, ?_, ?_, ?_⟩
  · rw [order_div_unit hH]
    exact hw
  · rw [hdiff, order_div_unit hHV]
    simpa only [zero_add] using order_mul_bound hκ hw2
  · rw [order_div_unit hV]
    simpa only [zero_add] using order_mul_bound hB hw2

omit [Finite k] in
/-- The affine `B` term and the change from `V` to `H` disappear only
after evaluation at the actual scaled residue character. -/
theorem commutator_trace_phase (r : ℤ) (hr : 0 < r)
    (f w κ B : k⸨X⸩) (hf : ((1 - 2 * r : ℤ) : WithTop ℤ) ≤ f.orderTop)
    (hw : (r : WithTop ℤ) ≤ w.orderTop)
    (hκ : 0 ≤ κ.orderTop) (hB : 0 ≤ B.orderTop) :
    scaledResiduePhase (2 * r) ((κ * w + B * w ^ 2) / (1 + w ^ 2 * f + w)) =
      scaledResiduePhase (2 * r) (κ * w / (1 + w ^ 2 * f)) := by
  obtain ⟨_, _, hV, _, hdiff, hBerr⟩ :=
    commutator_denominator_depths r hr f w κ B hf hw hκ hB
  let H := 1 + w ^ 2 * f
  let V := H + w
  have hremove : scaledResiduePhase (2 * r) ((κ * w + B * w ^ 2) / V) =
      scaledResiduePhase (2 * r) (κ * w / V) := by
    apply phase_congr
    simpa only [add_div, add_sub_cancel_left] using hBerr
  exact hremove.trans (phase_congr (2 * r) _ _ hdiff).symm

omit [Finite k] [CharP k 2] in
/-- The polar replacement used before the rational Cartier calculation.
The square `W²` and the constant error are computed from the full reduced
parameter, and inversion of both unit denominators preserves depth `T₂`. -/
theorem commutator_polar_denominator (r : ℤ) (hr : 0 < r)
    (f d w : k⸨X⸩) (hf : ((1 - 2 * r : ℤ) : WithTop ℤ) ≤ f.orderTop)
    (hd : d ^ 2 = originBeta (2 * r - 1) f) (hdint : 0 ≤ d.orderTop)
    (hw : (r : WithTop ℤ) ≤ w.orderTop) :
    let W := single (-r) 1 * d * w
    let R₀ := single 1 1 * W ^ 2
    let R := w ^ 2 * f
    0 ≤ W.orderTop ∧ R₀ = w ^ 2 * reducedNegativePart f ∧
      (1 : WithTop ℤ) ≤ R₀.orderTop ∧
      ((2 * r : ℤ) : WithTop ℤ) ≤ (R - R₀).orderTop ∧
      (1 + R₀).orderTop = 0 ∧
      ((2 * r : ℤ) : WithTop ℤ) ≤ ((1 + R)⁻¹ - (1 + R₀)⁻¹).orderTop := by
  let W : k⸨X⸩ := single (-r) 1 * d * w
  let R₀ : k⸨X⸩ := single 1 1 * W ^ 2
  let R : k⸨X⸩ := w ^ 2 * f
  have hW : 0 ≤ W.orderTop := by
    have h := order_mul_bound
      (order_mul_bound (HahnSeries.orderTop_single_le (r := (1 : k)) (a := -r)) hdint) hw
    simpa only [add_zero, neg_add_cancel, WithTop.coe_zero] using h
  have heq : R₀ = w ^ 2 * reducedNegativePart f := by
    calc
      R₀ = (single 1 1 * (single (-r) 1 * single (-r) 1) * single (2 * r - 1) 1) *
          reducedNegativePart f * w ^ 2 := by
        dsimp [R₀, W]
        rw [mul_pow, mul_pow, hd, originBeta]
        ring
      _ = _ := by
        simp only [HahnSeries.single_mul_single, one_mul,
          show 1 + (-r + -r) + (2 * r - 1) = 0 by omega,
          HahnSeries.single_zero_one]
        ring
  have hR₀ : (1 : WithTop ℤ) ≤ R₀.orderTop := by
    have h := order_mul_bound (HahnSeries.orderTop_single_le (r := (1 : k)) (a := 1))
      (order_mul_bound hW hW)
    simpa only [zero_add, add_zero, WithTop.coe_one, ← pow_two] using h
  have herr : ((2 * r : ℤ) : WithTop ℤ) ≤ (R - R₀).orderTop := by
    have hdifference : R - R₀ = w ^ 2 * HahnSeries.C (f.coeff 0) := by
      rw [heq]
      dsimp [R, reducedNegativePart]
      ring
    rw [hdifference]
    have h := order_mul_bound (order_mul_bound hw hw)
      (HahnSeries.orderTop_single_le (r := f.coeff 0) (a := 0))
    simpa only [add_zero, ← pow_two, ← two_mul, HahnSeries.C_apply] using h
  have hH₀ : (1 + R₀).orderTop = 0 := order_one_add (lt_of_lt_of_le (by norm_num) hR₀)
  have hH : (1 + R).orderTop = 0 :=
    (commutator_denominator_depths r hr f w 0 0 hf hw (by simp) (by simp)).2.1
  have hH0 : 1 + R ≠ 0 := by intro h; simp [h] at hH
  have hH₀0 : 1 + R₀ ≠ 0 := by intro h; simp [h] at hH₀
  refine ⟨hW, heq, hR₀, herr, hH₀, ?_⟩
  rw [inv_sub_inv hH0 hH₀0]
  have hprod : ((1 + R) * (1 + R₀)).orderTop = 0 := by
    rw [HahnSeries.orderTop_mul, hH, hH₀, add_zero]
  rw [order_div_unit hprod]
  rw [show (1 + R₀) - (1 + R) = -(R - R₀) by ring, HahnSeries.orderTop_neg]
  exact herr

omit [Finite k] in
/-- The independent norm-symbol evaluation up to the rational Cartier
step in (D:EQ:commmodel). The factor `H` is evaluated by the full residue
symbol, and only `1 + w/H` uses the lower stationary chart. -/
theorem commutator_residue_before_cartier (r : ℤ) (hr : 0 < r)
    (f₁ f₂ w : k⸨X⸩) (hred₁ : IsReducedAS f₁) (hred₂ : IsReducedAS f₂)
    (hf₁ : ((1 - 2 * r : ℤ) : WithTop ℤ) ≤ f₁.orderTop)
    (hf₂ : ((1 - 2 * r : ℤ) : WithTop ℤ) ≤ f₂.orderTop)
    (hw : (r : WithTop ℤ) ≤ w.orderTop)
    (hβ₁ : 0 ≤ (originBeta (2 * r - 1) f₁).orderTop)
    (hβ₂ : 0 ≤ (originBeta (2 * r - 1) f₂).orderTop) :
    let β₂ := originBeta (2 * r - 1) f₂
    let R := w ^ 2 * f₁
    let H := 1 + R
    binaryAddChar (EqualChar.residueExponent f₂ (H + w)) =
      scaledResiduePhase (2 * r) ((β₂ * R + β₂ * w) / H) := by
  let β₁ := originBeta (2 * r - 1) f₁
  let β₂ := originBeta (2 * r - 1) f₂
  let B := β₁ * f₂ + β₂ * f₁
  let R := w ^ 2 * f₁
  let H := 1 + R
  let V := H + w
  obtain ⟨_, hH, hV, hwH, _, _⟩ :=
    commutator_denominator_depths r hr f₁ w 0 0 hf₁ hw (by simp) (by simp)
  change H.orderTop = 0 at hH
  change V.orderTop = 0 at hV
  have hH0 : H ≠ 0 := by intro h; simp [h] at hH
  have hV0 : V ≠ 0 := by intro h; simp [h] at hV
  have hfactor : V = H * (1 + w / H) := by field_simp; ring
  have hsecond0 : 1 + w / H ≠ 0 := by
    intro h
    exact hV0 (by rw [hfactor, h, mul_zero])
  have hder : LaurentSeries.derivative k H =
      w ^ 2 * (single (-(2 * r)) 1 * β₁) := by
    dsimp [H, R]
    rw [map_add, laurentDerivative_mul, derivative_square]
    have hD1 : LaurentSeries.derivative k (1 : k⸨X⸩) = 0 := by
      simp [LaurentSeries.derivative_apply, ← HahnSeries.single_zero_one]
    rw [hD1, mul_zero, zero_add, add_zero, derivative_eq_originBeta (2 * r - 1) f₁ hred₁,
      show 2 * r - 1 + 1 = 2 * r by omega]
  have hHphase : binaryAddChar (EqualChar.residueExponent f₂ H) =
      scaledResiduePhase (2 * r) (β₁ * f₂ * w ^ 2 / H) := by
    simp only [EqualChar.residueExponent, EqualChar.logarithmicDerivative,
      scaledResiduePhase, hder]
    congr 3
    ring
  have hchart : binaryAddChar (EqualChar.residueExponent f₂ (1 + w / H)) =
      scaledResiduePhase (2 * r) (β₂ * w / H) := by
    have hc := residueSymbol_lowerChart (2 * r - 1) r (2 * r - 1) f₂ (w / H)
      hred₂ hr (by omega) (by simpa only [neg_sub, sub_zero] using hf₂) hwH
    change binaryAddChar (EqualChar.residueExponent f₂ (1 - w / H)) = _ at hc
    simpa only [CharTwo.sub_eq_add, show 2 * r - 1 + 1 = 2 * r by omega,
      ← mul_div_assoc] using hc
  have hfirst : binaryAddChar (EqualChar.residueExponent f₂ V) =
      scaledResiduePhase (2 * r) (β₁ * f₂ * w ^ 2 / H + β₂ * w / H) := by
    rw [hfactor, EqualChar.residueExponent_mul f₂ H (1 + w / H) hH0 hsecond0,
      AddChar.map_add_eq_mul, hHphase, hchart, phase_add]
  have hB : 0 ≤ B.orderTop := originB_integral (2 * r - 1) f₁ f₂ hβ₁ hβ₂
  have hBerr : ((2 * r : ℤ) : WithTop ℤ) ≤ (B * w ^ 2 / H).orderTop := by
    rw [order_div_unit hH]
    have h := order_mul_bound hB (order_mul_bound hw hw)
    simpa only [zero_add, ← pow_two, ← two_mul] using h
  refine hfirst.trans (phase_congr (2 * r) _ _ ?_)
  have heq : (β₁ * f₂ * w ^ 2 / H + β₂ * w / H) - (β₂ * R + β₂ * w) / H =
      B * w ^ 2 / H := by
    dsimp [B, R]
    rw [CharTwo.sub_eq_add]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
  rw [heq]
  exact hBerr

/-- The polar phase conversion in (D:EQ:commmodel). Apply the existing
Artin--Schreier invariance to `ϖ f` and `ϖ (1 + ϖ W²)`, whose derivative
is one. This reuses the proved Cartier action on logarithmic derivatives. -/
private theorem commutator_polar_phase (r : ℤ) (d₁ d₂ w : k⸨X⸩)
    (hH : 1 + single 1 1 * (single (-r) 1 * d₁ * w) ^ 2 ≠ 0) :
    let W := single (-r) 1 * d₁ * w
    let R₀ := single 1 1 * W ^ 2
    scaledResiduePhase (2 * r) (d₂ ^ 2 * R₀ / (1 + R₀)) =
      scaledResiduePhase (2 * r) (d₁ * d₂ * w / (1 + R₀)) := by
  let π : k⸨X⸩ := single 1 1
  let W : k⸨X⸩ := single (-r) 1 * d₁ * w
  let H := 1 + π * W ^ 2
  let f : k⸨X⸩ := single (-r) 1 * d₂ * W
  have hπ : π ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
  have hder : LaurentSeries.derivative k (π * H) = 1 := by
    rw [show π * H = π + (π * W) ^ 2 by dsimp [H]; ring,
      map_add, derivative_square, add_zero]
    simp [π, LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_single,
      HahnSeries.single_zero_one]
  have hAS := EqualChar.residueExponent_artinSchreier (π * f) (π * H)
    (mul_ne_zero hπ hH)
  have hcalc : ((π * f) ^ 2 + π * f) * EqualChar.logarithmicDerivative (π * H) =
      π * f ^ 2 / H + f / H := by
    rw [EqualChar.logarithmicDerivative, hder, mul_one]
    field_simp
  rw [EqualChar.residueExponent, hcalc] at hAS
  simp only [Residues.residue, HahnSeries.coeff_add, map_add] at hAS
  have htrace := CharTwo.add_eq_zero.mp hAS
  have hscale : single (-(2 * r)) (1 : k) = single (-r) 1 * single (-r) 1 := by
    rw [HahnSeries.single_mul_single, one_mul, show -r + -r = -(2 * r) by omega]
  have hleft : single (-(2 * r)) 1 * (d₂ ^ 2 * (π * W ^ 2) / H) =
      π * f ^ 2 / H := by
    rw [hscale]
    dsimp [f]
    ring
  have hright : single (-(2 * r)) 1 * (d₁ * d₂ * w / H) = f / H := by
    rw [hscale]
    dsimp [f, W]
    ring
  change binaryAddChar (Algebra.trace (ZMod 2) k (Residues.residue
    (single (-(2 * r)) 1 * (d₂ ^ 2 * (π * W ^ 2) / H)))) =
      binaryAddChar (Algebra.trace (ZMod 2) k (Residues.residue
        (single (-(2 * r)) 1 * (d₁ * d₂ * w / H))))
  rw [hleft, hright]
  exact congrArg binaryAddChar htrace

/-- All replacements around the rational Cartier step are evaluated at
depth `2r`, including both changes of denominator. -/
theorem commutator_phase_comparison (r : ℤ) (hr : 0 < r)
    (f d₁ d₂ w : k⸨X⸩) (hf : ((1 - 2 * r : ℤ) : WithTop ℤ) ≤ f.orderTop)
    (hd₁ : d₁ ^ 2 = originBeta (2 * r - 1) f)
    (hd₁int : 0 ≤ d₁.orderTop) (hd₂int : 0 ≤ d₂.orderTop)
    (hw : (r : WithTop ℤ) ≤ w.orderTop) :
    scaledResiduePhase (2 * r) ((d₂ ^ 2 * (w ^ 2 * f) + d₂ ^ 2 * w) /
      (1 + w ^ 2 * f)) =
        scaledResiduePhase (2 * r) ((d₂ ^ 2 + d₁ * d₂) * w / (1 + w ^ 2 * f)) := by
  let W : k⸨X⸩ := single (-r) 1 * d₁ * w
  let R₀ := single 1 1 * W ^ 2
  let R := w ^ 2 * f
  let H₀ := 1 + R₀
  let H := 1 + R
  obtain ⟨_, _, _, _, hH₀, hInv⟩ :=
    commutator_polar_denominator r hr f d₁ w hf hd₁ hd₁int hw
  have hH := (commutator_denominator_depths r hr f w 0 0 hf hw (by simp) (by simp)).2.1
  have hH0 : H ≠ 0 := by intro h; change H.orderTop = 0 at hH; simp [h] at hH
  have hH₀0 : H₀ ≠ 0 := by intro h; change H₀.orderTop = 0 at hH₀; simp [h] at hH₀
  have hβ : (0 : WithTop ℤ) ≤ (d₂ ^ 2).orderTop := by
    simpa only [pow_two, zero_add, WithTop.coe_zero] using order_mul_bound hd₂int hd₂int
  have hnum : (0 : WithTop ℤ) ≤ (d₁ * d₂ * w).orderTop := by
    have hw0 : (0 : WithTop ℤ) ≤ w.orderTop := (WithTop.coe_le_coe.mpr hr.le).trans hw
    simpa only [zero_add, WithTop.coe_zero] using order_mul_bound (order_mul_bound hd₁int hd₂int) hw0
  have hfirst : scaledResiduePhase (2 * r) (d₂ ^ 2 * R / H) =
      scaledResiduePhase (2 * r) (d₂ ^ 2 * R₀ / H₀) := by
    apply phase_congr
    have heq : d₂ ^ 2 * R / H - d₂ ^ 2 * R₀ / H₀ =
        -(d₂ ^ 2 * (H⁻¹ - H₀⁻¹)) := by
      field_simp
      dsimp [H, H₀]
      ring
    rw [heq, HahnSeries.orderTop_neg]
    simpa only [zero_add] using order_mul_bound hβ hInv
  have hlast : scaledResiduePhase (2 * r) (d₁ * d₂ * w / H) =
      scaledResiduePhase (2 * r) (d₁ * d₂ * w / H₀) := by
    apply phase_congr
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_sub]
    simpa only [zero_add] using order_mul_bound hnum hInv
  change scaledResiduePhase (2 * r) ((d₂ ^ 2 * R + d₂ ^ 2 * w) / H) = _
  rw [add_div, phase_add, hfirst, commutator_polar_phase r d₁ d₂ w hH₀0, ← hlast,
    ← phase_add]
  congr 1
  ring

end Laurent

section QuadraticAlgebra
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  [Module.Finite F E] [IsGalois F E]

private theorem quadratic_norm_trace (hdegree : Module.finrank F E = 2)
    (σ : Gal(E/F)) (hσ : σ ≠ 1) (x : E) :
    algebraMap F E (Algebra.norm F x) = x * σ x ∧
      algebraMap F E (Algebra.trace F E x) = x + σ x := by
  classical
  have hc : Fintype.card Gal(E/F) = 2 := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, hdegree]
  have hu : ({1, σ} : Finset Gal(E/F)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simp [hσ.symm, hc]
  constructor
  · rw [Algebra.norm_eq_prod_automorphisms, ← hu, Finset.prod_pair hσ.symm]
    rfl
  · rw [trace_eq_sum_automorphisms, ← hu, Finset.sum_pair hσ.symm]
    rfl

variable [CharP E 2]

/-- The exact quadratic norm of the two coordinates, with no unit assumption. -/
theorem commutator_norm_coordinates (hdegree : Module.finrank F E = 2)
    (σ : Gal(E/F)) (hσ : σ ≠ 1) (z : E) (f : F)
    (hσz : σ z = z + 1) (hz : z ^ 2 + z = algebraMap F E f) (a b : F) :
    Algebra.norm F (algebraMap F E a + algebraMap F E b * z) =
      a ^ 2 + a * b + b ^ 2 * f := by
  apply (algebraMap F E).injective
  rw [(quadratic_norm_trace hdegree σ hσ _).1]
  simp only [map_add, map_mul, map_pow, σ.commutes, hσz]
  rw [← hz]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero]

/-- The first equality in (D:EQ:comm-rational), using the genuine field
trace and norm. Both coordinate coefficients and the full affine constant
are retained. -/
theorem commutator_rational_trace (hdegree : Module.finrank F E = 2)
    (σ : Gal(E/F)) (hσ : σ ≠ 1) (z : E) (hσz : σ z = z + 1)
    (a b κ B : F) (v : E) (hv : v ≠ 0)
    (hcoords : v = algebraMap F E a + algebraMap F E b * z) :
    Algebra.trace F E ((algebraMap F E κ * z + algebraMap F E B) *
      (1 - σ v / v)) = (κ * a * b + B * b ^ 2) / Algebra.norm F v := by
  have hσv : σ v ≠ 0 := (map_ne_zero σ).mpr hv
  have hquot : 1 - σ v / v = algebraMap F E b / v := by
    apply (eq_div_iff hv).mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hv, hcoords]
    simp only [map_add, map_mul, σ.commutes, hσz, CharTwo.sub_eq_add]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero]
  rw [hquot]
  apply (algebraMap F E).injective
  rw [(quadratic_norm_trace hdegree σ hσ _).2]
  simp only [map_div₀, map_add, map_mul, map_pow, σ.commutes, hσz]
  rw [(quadratic_norm_trace hdegree σ hσ v).1]
  apply (eq_div_iff (mul_ne_zero hv hσv)).mpr
  field_simp [hv, hσv]
  rw [hcoords]
  simp only [map_add, map_mul, σ.commutes, hσz]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero]

/-- Passing to `w = b/a` preserves the entire rational trace, without
normalizing the valuation or replacing the representative by a chosen norm. -/
theorem commutator_rational_trace_normalized (hdegree : Module.finrank F E = 2)
    (σ : Gal(E/F)) (hσ : σ ≠ 1) (z : E) (f : F)
    (hσz : σ z = z + 1) (hz : z ^ 2 + z = algebraMap F E f)
    (a b κ B : F) (ha : a ≠ 0) (v : E) (hv : v ≠ 0)
    (hcoords : v = algebraMap F E a + algebraMap F E b * z) :
    Algebra.trace F E ((algebraMap F E κ * z + algebraMap F E B) *
      (1 - σ v / v)) =
        (κ * (b / a) + B * (b / a) ^ 2) / (1 + b / a + (b / a) ^ 2 * f) := by
  rw [commutator_rational_trace hdegree σ hσ z hσz a b κ B v hv hcoords]
  rw [hcoords, commutator_norm_coordinates hdegree σ hσ z f hσz hz]
  field_simp

end QuadraticAlgebra

section QuadraticDepth
variable {F E : Type*} [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E] [CharP E 2]

omit [Module.Finite F E] in
/-- The domain condition forces the scalar coordinate to be nonzero and
the quotient coordinate to have the full required depth. This treats every
nonzero `v` directly; parity excludes the odd-valuation alternative. -/
theorem commutator_domain_coordinates (hdegree : Module.finrank F E = 2)
    (hram : ramificationIndex F E = 2) (σ : Gal(E/F)) (z : E)
    (hσz : σ z = z + 1) (t : ℕ) (hodd : Odd t)
    (hzord : ord E z = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (r s : ℤ) (hts : (t : ℤ) < s) (hrs : 2 * r ≤ s)
    (v : E) (hv : v ≠ 0) (hdepth : 1 - σ v / v ∈ lattice E s) :
    ∃ a b : F, a ≠ 0 ∧ v = algebraMap F E a + algebraMap F E b * z ∧
      b / a ∈ lattice F r := by
  have hgen (a : F) : algebraMap F E a ≠ z := by
    intro ha
    rw [← ha, σ.commutes] at hσz
    exact one_ne_zero (add_eq_left.mp hσz.symm)
  have hLI : LinearIndependent F ![(1 : E), z] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro a
    simpa only [Algebra.smul_def, mul_one] using hgen a
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by simp [hdegree]
  let e := basisOfLinearIndependentOfCardEqFinrank hLI hcard
  have he : (e : Fin 2 → E) = ![(1 : E), z] :=
    coe_basisOfLinearIndependentOfCardEqFinrank hLI hcard
  let a : F := e.equivFun v 0
  let b : F := e.equivFun v 1
  have hcoords : v = algebraMap F E a + algebraMap F E b * z := by
    have h := e.sum_equivFun v
    simpa only [Fin.sum_univ_two, he, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Algebra.smul_def, mul_one, a, b] using h.symm
  have hquot : 1 - σ v / v = algebraMap F E b / v := by
    apply (eq_div_iff hv).mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hv, hcoords]
    simp only [map_add, map_mul, σ.commutes, hσz, CharTwo.sub_eq_add]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero]
  rw [hquot] at hdepth
  by_cases hb : b = 0
  · have ha : a ≠ 0 := by
      intro ha
      simp [ha, hb] at hcoords
      exact hv hcoords
    exact ⟨a, b, ha, hcoords, by simp [hb]⟩
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).mpr hb)
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff E).mpr hv)
  have hbval : ord F b = (n : WithTop ℤ) := hn.symm
  have hvval : ord E v = (q : WithTop ℤ) := hq.symm
  have hbmap : ord E (algebraMap F E b) = ((2 * n : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hram, hbval, ← WithTop.coe_nsmul]
    congr 1
  have hbz : ord E (algebraMap F E b * z) = ((2 * n - t : ℤ) : WithTop ℤ) := by
    rw [ord_mul, hbmap, hzord, ← WithTop.coe_add]
    congr 1
  have hbound : s ≤ 2 * n - q := by
    change (s : WithTop ℤ) ≤ ord E (algebraMap F E b / v) at hdepth
    rw [ord_div, hbmap, hvval, ← WithTop.LinearOrderedAddCommGroup.coe_sub] at hdepth
    exact WithTop.coe_le_coe.mp hdepth
  have ha : a ≠ 0 := by
    intro ha
    rw [ha, map_zero, zero_add] at hcoords
    have h := congrArg (ord E) hcoords
    rw [hvval, hbz] at h
    have h' := WithTop.coe_injective h
    omega
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).mpr ha)
  have haval : ord F a = (m : WithTop ℤ) := hm.symm
  have hamap : ord E (algebraMap F E a) = ((2 * m : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hram, haval, ← WithTop.coe_nsmul]
    congr 1
  have hne : ord E (algebraMap F E a) ≠ ord E (algebraMap F E b * z) := by
    rw [hamap, hbz]
    intro h
    have h' := WithTop.coe_injective h
    obtain ⟨u, hu⟩ := hodd
    have hu' : (t : ℤ) = 2 * (u : ℤ) + 1 := by exact_mod_cast hu
    omega
  have hmin : q = min (2 * m) (2 * n - (t : ℤ)) := by
    have h := congrArg (ord E) hcoords
    rw [hvval, ord_add_eq_min E hne, hamap, hbz, ← WithTop.coe_min] at h
    exact WithTop.coe_injective h
  have hqeq : q = 2 * m := by omega
  refine ⟨a, b, ha, hcoords, ?_⟩
  change (r : WithTop ℤ) ≤ ord F (b / a)
  rw [ord_div, hbval, haval, ← WithTop.LinearOrderedAddCommGroup.coe_sub]
  exact WithTop.coe_le_coe.mpr (by omega)

end QuadraticDepth

open private residueField_charTwo from LanglandsSecondMainLemma.EqualChar.NormCharacter

section ActualNormSymbol
variable (F E : Type) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E] [IsGalois F E] [CharP F 2]
local instance commutatorResidueChar : CharP (ResidueField F) 2 := residueField_charTwo F
local instance commutatorResidueAlgebra : Algebra (ZMod 2) (ResidueField F) := ZMod.algebra _ 2

/-- Removing the scalar square preserves the value of the actual norm
character. Its residue expression is transported to the prescribed Laurent
presentation, so this also applies to the compatible norm uniformizer. -/
theorem commutator_actual_norm_symbol (hdegree : Module.finrank F E = 2)
    (P : Residues.EqualCharacteristicPresentation F) (f : F) (z : E)
    (hz : z ^ 2 + z = algebraMap F E f) (hgen : z ∉ Set.range (algebraMap F E))
    (ω : NormCharacter F E) (hω : ω ≠ 1) (x a : Fˣ) :
    (ω.1 x : ℂ) = binaryAddChar (EqualChar.residueExponent (P.laurentEquiv.symm f)
      (P.laurentEquiv.symm ((x : F) / (a : F) ^ 2))) := by
  have hnorm : normUnits F E (Units.map (algebraMap F E) a) = a ^ 2 := by
    apply Units.ext
    change Algebra.norm F (algebraMap F E (a : F)) = (a : F) ^ 2
    rw [Algebra.norm_algebraMap, hdegree]
  have ha : ω.1 (a ^ 2) = 1 :=
    ω.eq_one_on_normRange F E _ ⟨Units.map (algebraMap F E) a, hnorm⟩
  have hvalue : ω.1 x = ω.1 (x / a ^ 2) := by
    rw [map_div, ha, div_one]
  rw [hvalue, Characters.artinSchreierNormCharacter_eq_normCharacter F E hdegree
    f z hz hgen ω hω]
  change binaryAddChar (EqualChar.residueExponent
    ((Characters.artinSchreierPresentation F).laurentEquiv.symm f)
    ((Characters.artinSchreierPresentation F).laurentEquiv.symm ((x / a ^ 2 : Fˣ) : F))) = _
  rw [residueExponent_changePresentation F (Characters.artinSchreierPresentation F) P]
  simp only [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]

end ActualNormSymbol

open private originLine_degrees origin_residueDegrees from
  LanglandsSecondMainLemma.Dyadic.Equal.Origin

section ActualOrigin
variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  [CharP F 2] [CharP K 2] [IsKleinFour Gal(K/F)]

local instance commutatorOriginResidueChar : CharP (ResidueField F) 2 := residueField_charTwo F
local instance commutatorOriginResidueAlgebra : Algebra (ZMod 2) (ResidueField F) :=
  ZMod.algebra _ 2

local instance commutatorIntermediateValuation (L : IntermediateField F K) : ValuativeRel L :=
  Basic.intermediateFieldValuativeRel L
local instance commutatorIntermediateTopology (L : IntermediateField F K) : TopologicalSpace L :=
  Basic.intermediateFieldTopology L
local instance commutatorIntermediateLocalField (L : IntermediateField F K) :
    IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
local instance commutatorLowerValuativeExtension (L : IntermediateField F K) :
    ValuativeExtension F L := Basic.intermediateField_lowerValuativeExtension L
local instance commutatorUpperValuativeExtension (L : IntermediateField F K) :
    ValuativeExtension L K := Basic.intermediateField_upperValuativeExtension L
local instance commutatorIntermediateGalois (L : IntermediateField F K) : IsGalois F L := by
  letI : IsMulCommutative Gal(K/F) := IsKleinFour.isMulCommutative
  letI : L.fixingSubgroup.Normal := inferInstance
  have h := IsGalois.of_fixedField_normal_subgroup L.fixingSubgroup
  rwa [IsGalois.fixedField_fixingSubgroup L] at h

/-- The exact coordinate reduction and rational trace for the simultaneous
origin constructed from the actual totally ramified diamond. The domain is
the entire subgroup in (D:EQ:commmodel), not a selected family of units. -/
theorem commutator_origin_reduction (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (A : SimultaneousASGenerators F K P) :
    let L := IntermediateField.fixedField (originLine (A.g 0))
    let σ := AlgEquiv.restrictNormalHom L (A.g 1)
    ∀ v : Lˣ, Units.map σ.toMonoidHom v / v ∈ unitFiltration L (A.t 1 + 1) →
      ∃ a b : F, a ≠ 0 ∧
        (v : L) = algebraMap F L a + algebraMap F L b * A.z 0 ∧
        b / a ∈ lattice F (((A.t 1 : ℤ) + 1) / 2) ∧
        Algebra.norm F (v : L) = a ^ 2 + a * b + b ^ 2 * A.f 0 ∧
        Algebra.trace F L (Algebra.norm L A.Y * (1 - σ (v : L) / (v : L))) =
          (A.kappa 0 * (b / a) + A.B * (b / a) ^ 2) /
            (1 + b / a + (b / a) ^ 2 * A.f 0) := by
  let L := IntermediateField.fixedField (originLine (A.g 0))
  let σ := AlgEquiv.restrictNormalHom L (A.g 1)
  have hdegree : Module.finrank F L = 2 :=
    (originLine_degrees F K (A.g 0) (A.nontrivial 0)).1
  have hram : ramificationIndex F L = 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F L
    rw [hdegree, (origin_residueDegrees F K hres L).1, mul_one] at h
    exact h.symm
  have hσz : σ (A.z 0) = A.z 0 + 1 := by
    apply Subtype.ext
    change ((AlgEquiv.restrictNormalHom L (A.g 1)) (A.z 0) : K) = _
    rw [AlgEquiv.restrictNormalHom_apply]
    exact A.second_action
  have hσ : σ ≠ 1 := by
    intro h
    rw [h, AlgEquiv.one_apply] at hσz
    exact one_ne_zero (add_eq_left.mp hσz.symm)
  dsimp only
  intro v hv
  have hdepth : 1 - σ (v : L) / (v : L) ∈ lattice L ((A.t 1 : ℤ) + 1) := by
    have h := (mem_unitFiltration_succ_iff_sub_mem_lattice L (A.t 1) _).mp hv
    have h' := (lattice L ((A.t 1 + 1 : ℕ) : ℤ)).neg_mem h
    simp only [neg_sub, Units.val_div_eq_div_val, Units.coe_map,
      Nat.cast_add, Nat.cast_one] at h'
    change 1 - σ (v : L) / (v : L) ∈ lattice L ((A.t 1 : ℤ) + 1) at h'
    exact h'
  have ht : (A.t 0 : ℤ) < (A.t 1 : ℤ) + 1 := by have h := A.smallest; omega
  have hrs : 2 * (((A.t 1 : ℤ) + 1) / 2) ≤ (A.t 1 : ℤ) + 1 := by omega
  obtain ⟨a, b, ha, hcoords, hw⟩ := commutator_domain_coordinates hdegree hram σ
    (A.z 0) hσz (A.t 0) (A.edge 0).2.2.2.2.1 (A.edge 0).2.2.2.2.2.1
    (((A.t 1 : ℤ) + 1) / 2) ((A.t 1 : ℤ) + 1) ht hrs v v.ne_zero hdepth
  refine ⟨a, b, ha, hcoords, hw, ?_, ?_⟩
  · rw [hcoords]
    exact commutator_norm_coordinates hdegree σ hσ (A.z 0) (A.f 0) hσz (A.edge 0).1 a b
  · rw [(A.exact_origin 0).2.2]
    exact commutator_rational_trace_normalized hdegree σ hσ (A.z 0) (A.f 0) hσz
      (A.edge 0).1 a b (A.kappa 0) A.B ha v v.ne_zero hcoords

/-- Both sides of the desired compatibility are reduced for every `v` in
the original domain, with the same exact coordinates and the actual lower
norm character. The remaining comparison is the local Cartier phase step. -/
theorem commutator_origin_character_reduction (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (A : SimultaneousASGenerators F K P) :
    let L₁ := IntermediateField.fixedField (originLine (A.g 0))
    let L₂ := IntermediateField.fixedField (originLine (A.g 1))
    let σ := AlgEquiv.restrictNormalHom L₁ (A.g 1)
    ∀ (ω₂ : NormCharacter F L₂), ω₂ ≠ 1 →
      ∀ v : L₁ˣ, Units.map σ.toMonoidHom v / v ∈ unitFiltration L₁ (A.t 1 + 1) →
        ∃ a b : F, a ≠ 0 ∧
          (v : L₁) = algebraMap F L₁ a + algebraMap F L₁ b * A.z 0 ∧
          b / a ∈ lattice F (((A.t 1 : ℤ) + 1) / 2) ∧
          Algebra.trace F L₁ (Algebra.norm L₁ A.Y * (1 - σ (v : L₁) / (v : L₁))) =
            (A.kappa 0 * (b / a) + A.B * (b / a) ^ 2) /
              (1 + b / a + (b / a) ^ 2 * A.f 0) ∧
          (ω₂.1 (normUnits F L₁ v) : ℂ) = binaryAddChar
            (EqualChar.residueExponent (P.laurentEquiv.symm (A.f 1))
              (P.laurentEquiv.symm (1 + b / a + (b / a) ^ 2 * A.f 0))) := by
  let L₁ := IntermediateField.fixedField (originLine (A.g 0))
  let L₂ := IntermediateField.fixedField (originLine (A.g 1))
  dsimp only
  intro ω₂ hω₂ v hv
  obtain ⟨a, b, ha, hcoords, hw, hnorm, htrace⟩ :=
    commutator_origin_reduction F K hres P A v hv
  refine ⟨a, b, ha, hcoords, hw, htrace, ?_⟩
  have hvalue := commutator_actual_norm_symbol F L₂
    (originLine_degrees F K (A.g 1) (A.nontrivial 1)).1 P (A.f 1) (A.z 1)
    (A.edge 1).1 (A.edge 1).2.1 ω₂ hω₂ (normUnits F L₁ v) (Units.mk0 a ha)
  have hnormalized : (normUnits F L₁ v : F) / a ^ 2 =
      1 + b / a + (b / a) ^ 2 * A.f 0 := by
    change Algebra.norm F (v : L₁) / a ^ 2 = _
    rw [hnorm]
    field_simp
  simpa only [Units.val_mk0, hnormalized] using hvalue

/-- **The full commutator compatibility** (Lemma 11.4,
`D:EQ:commmodel`). The stationary value at every conjugate quotient in
`U_{L₁}^{t₂+1}` equals the actual crossed norm character `ω₂ ∘ n₁`.
The simultaneous origin is the one constructed by
`simultaneousASGenerators_exists`; no phase identity is an input. -/
theorem commutator (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (A : SimultaneousASGenerators F K P) :
    let L₁ := IntermediateField.fixedField (originLine (A.g 0))
    let L₂ := IntermediateField.fixedField (originLine (A.g 1))
    let σ := AlgEquiv.restrictNormalHom L₁ (A.g 1)
    ∀ (ω₂ : NormCharacter F L₂), ω₂ ≠ 1 →
      ∀ v : L₁ˣ, Units.map σ.toMonoidHom v / v ∈ unitFiltration L₁ (A.t 1 + 1) →
        (originAddChar F P ((A.t 1 : ℤ) + 1)
          (Algebra.trace F L₁ (Algebra.norm L₁ A.Y * (1 - σ (v : L₁) / (v : L₁)))) : ℂ) =
            ((Characters.crossedNormHom F L₁ L₂ K ω₂).1 v : ℂ) := by
  let L₁ := IntermediateField.fixedField (originLine (A.g 0))
  let L₂ := IntermediateField.fixedField (originLine (A.g 1))
  dsimp only
  intro ω₂ hω₂ v hv
  obtain ⟨a, b, _, _, hw, htrace, hvalue⟩ :=
    commutator_origin_character_reduction F K hres P A ω₂ hω₂ v hv
  let r : ℤ := ((A.t 1 : ℤ) + 1) / 2
  have hTr : (A.t 1 : ℤ) + 1 = 2 * r := by
    obtain ⟨n, hn⟩ := (A.edge 1).2.2.2.2.1
    have hn' : (A.t 1 : ℤ) = 2 * (n : ℤ) + 1 := by exact_mod_cast hn
    dsimp [r]
    omega
  have hr : 0 < r := by have ht := (A.edge 1).2.2.2.1; omega
  have ht : (A.t 1 : ℤ) = 2 * r - 1 := by omega
  have horder (x : F) : (P.laurentEquiv.symm x).orderTop = ord F x := by
    simpa only [RingEquiv.apply_symm_apply] using
      (P.laurentEquiv_order (P.laurentEquiv.symm x)).symm
  let f₁ := P.laurentEquiv.symm (A.f 0)
  let f₂ := P.laurentEquiv.symm (A.f 1)
  let d₁ := P.laurentEquiv.symm (A.root 0)
  let d₂ := P.laurentEquiv.symm (A.root 1)
  let w := P.laurentEquiv.symm b / P.laurentEquiv.symm a
  let κ := P.laurentEquiv.symm (A.kappa 0)
  let B := P.laurentEquiv.symm A.B
  have hd₁ : d₁ ^ 2 = originBeta (2 * r - 1) f₁ := by
    dsimp [d₁, f₁]
    rw [← map_pow, (A.scalar_data 0).1, SimultaneousASGenerators.beta,
      RingEquiv.symm_apply_apply, ht]
  have hd₂ : d₂ ^ 2 = originBeta (2 * r - 1) f₂ := by
    dsimp [d₂, f₂]
    rw [← map_pow, (A.scalar_data 1).1, SimultaneousASGenerators.beta,
      RingEquiv.symm_apply_apply, ht]
  have hd₁int : 0 ≤ d₁.orderTop := by
    rw [horder, (A.scalar_data 0).2.1]
    apply WithTop.coe_le_coe.mpr
    have hs := A.smallest
    omega
  have hd₂int : 0 ≤ d₂.orderTop := by
    rw [horder, (A.scalar_data 1).2.1]
    simp
  have hβ₁ : 0 ≤ (originBeta (2 * r - 1) f₁).orderTop := by
    rw [← hd₁, pow_two, HahnSeries.orderTop_mul]
    exact add_nonneg hd₁int hd₁int
  have hβ₂ : 0 ≤ (originBeta (2 * r - 1) f₂).orderTop := by
    rw [← hd₂, pow_two, HahnSeries.orderTop_mul]
    exact add_nonneg hd₂int hd₂int
  have hf₁ : ((1 - 2 * r : ℤ) : WithTop ℤ) ≤ f₁.orderTop := by
    rw [(A.edge 0).2.2.2.2.2.2.1]
    apply WithTop.coe_le_coe.mpr
    have hs := A.smallest
    omega
  have hf₂ : ((1 - 2 * r : ℤ) : WithTop ℤ) ≤ f₂.orderTop := by
    rw [(A.edge 1).2.2.2.2.2.2.1]
    exact WithTop.coe_le_coe.mpr (by omega)
  have hw' : (r : WithTop ℤ) ≤ w.orderTop := by
    dsimp [w]
    rw [← map_div₀, horder]
    exact hw
  have hκ : 0 ≤ κ.orderTop := by
    rw [horder, A.kappa_order]
    simp
  have hB : 0 ≤ B.orderTop := by
    rw [horder]
    exact A.B_integral
  have hκeq : κ = d₂ ^ 2 + d₁ * d₂ := by
    dsimp [κ, d₁, d₂]
    rw [SimultaneousASGenerators.kappa, Matrix.cons_val_zero, A.root_third]
    simp only [map_mul, map_add]
    ring
  have hphase := commutator_residue_before_cartier r hr f₁ f₂ w
    (A.edge 0).2.2.1 (A.edge 1).2.2.1 hf₁ hf₂ hw' hβ₁ hβ₂
  dsimp only at hphase
  rw [← hd₂] at hphase
  have hcompare := commutator_phase_comparison r hr f₁ d₁ d₂ w hf₁ hd₁ hd₁int hd₂int hw'
  have hcompare' := hcompare.trans (congrArg
    (fun c ↦ scaledResiduePhase (2 * r) (c * w / (1 + w ^ 2 * f₁))) hκeq.symm)
  have hremove := commutator_trace_phase r hr f₁ w κ B hf₁ hw' hκ hB
  have htrace' := congrArg
    (fun x : F ↦ scaledResiduePhase (2 * r) (P.laurentEquiv.symm x)) htrace
  simp only [map_div₀, map_add, map_mul, map_pow, map_one] at htrace' hvalue
  have hden : 1 + w + w ^ 2 * f₁ = 1 + w ^ 2 * f₁ + w := by ring
  have hleft := congrArg
    (fun H ↦ scaledResiduePhase (2 * r) ((κ * w + B * w ^ 2) / H)) hden
  have hright := congrArg (fun H ↦ binaryAddChar (EqualChar.residueExponent f₂ H)) hden
  rw [originAddChar_apply, hTr]
  exact htrace'.trans (hleft.trans
    ((hremove.trans (hphase.trans hcompare').symm).trans (hright.symm.trans hvalue.symm)))

end ActualOrigin

end

end LanglandsSecondMainLemma.Dyadic.Equal
