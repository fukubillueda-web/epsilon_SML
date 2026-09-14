import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Dyadic.Mixed.Symbols
import LanglandsSecondMainLemma.Local.Different
import LanglandsSecondMainLemma.Local.Newton

/-!
# Dyadic / Mixed / Unit Symbol

This file proves Paper Lemma 12.2 (`D:MX:unit-symbol`) for the actual
quadratic norm symbol.  The public symbol API deliberately hides the
particular Kummer model used to construct its norm character.  We therefore
use an equivalent local proof which remains entirely on that public API.

The split case is immediate.  Otherwise the Steinberg relation and the
conic change of variables give

`(1 + u, 1 + v) = (1 - u*v, u*(1 + u)*(1 + v))`.

The depth assumption says that the polynomial
`X^2 - (1 - u*v)` satisfies the quantitative Hensel inequality at `1`.
Thus `1 - u*v` is a square, so the transformed symbol is trivial.  This is
the same sufficient depth as the discriminant/conductor proof in the paper,
but avoids exposing a second copy of the private Kummer-extension model.

Blueprint: `blueprint/tasks/Dyadic/Mixed/UnitSymbol.md`.
Paper: lines 6875--6888 of `references/epsilon_SML.tex`.
-/

namespace LanglandsSecondMainLemma.Dyadic.Mixed

open LanglandsFirstMainLemma
open LanglandsSecondMainLemma.Characters
open Polynomial

noncomputable section


variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The canonical field unit `1 + u` attached to an element of positive
integral depth.  The proof argument records the whole-ideal condition
`u ∈ 𝔭_F`; no arbitrary nonzero representative is chosen. -/
noncomputable def oneAddUnit (u : F)
    (hu : ((1 : ℤ) : WithTop ℤ) ≤ ord F u) : Fˣ :=
  principalUnitOf F 0 u (by
    rw [mem_lattice]
    norm_num
    exact hu)

@[simp]
theorem coe_oneAddUnit (u : F)
    (hu : ((1 : ℤ) : WithTop ℤ) ≤ ord F u) :
    (oneAddUnit F u hu : F) = 1 + u := by
  simp [oneAddUnit]

/-- If the product `u*v` lies strictly beyond twice the depth of `2`, then
`1 - u*v` is a square.  This is the quantitative Hensel step used in the
unit-symbol calculation. -/
private theorem one_sub_mul_isSquare
    (hchar : ringChar F ≠ 2) (u v : F)
    (hu : ((1 : ℤ) : WithTop ℤ) ≤ ord F u)
    (hv : ((1 : ℤ) : WithTop ℤ) ≤ ord F v)
    (hdepth : ord F (2 : F) + ord F (2 : F) <
      ord F u + ord F v) :
    IsSquare (1 - u * v) := by
  by_cases hu0 : u = 0
  · subst u
    simp
  by_cases hv0 : v = 0
  · subst v
    simp

  have htwo0 : (2 : F) ≠ 0 := by
    intro htwo
    apply Ring.neg_one_ne_one_of_char_ne_two hchar
    linear_combination -htwo
  obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp
    ((ord_ne_top_iff F).2 htwo0)
  have he' : ord F (2 : F) = (e : WithTop ℤ) := he.symm

  have huInt : u ∈ ringOfIntegers F := by
    apply (ord_nonneg_iff_mem_integer F u).1
    exact (show (0 : WithTop ℤ) ≤ ((1 : ℤ) : WithTop ℤ) by norm_num).trans hu
  have hvInt : v ∈ ringOfIntegers F := by
    apply (ord_nonneg_iff_mem_integer F v).1
    exact (show (0 : WithTop ℤ) ≤ ((1 : ℤ) : WithTop ℤ) by norm_num).trans hv
  let uO : ringOfIntegers F := ⟨u, huInt⟩
  let vO : ringOfIntegers F := ⟨v, hvInt⟩
  let f : (ringOfIntegers F)[X] := X ^ 2 - C (1 - uO * vO)

  have hderiv :
      ord F ((f.derivative.eval 1 : ringOfIntegers F) : F) =
        (e : WithTop ℤ) := by
    have hvalue : ((f.derivative.eval 1 : ringOfIntegers F) : F) = (2 : F) := by
      simp [f]
      norm_num
    rw [hvalue]
    exact he'
  have hres : ((2 * e : ℤ) : WithTop ℤ) <
      ord F ((f.eval 1 : ringOfIntegers F) : F) := by
    have hdepth' : ((2 * e : ℤ) : WithTop ℤ) < ord F (u * v) := by
      rw [ord_mul]
      rw [he'] at hdepth
      simpa only [two_mul, WithTop.coe_add] using hdepth
    simpa [f, uO, vO] using hdepth'

  obtain ⟨z, hz, _hzball, _hzbound, _hzunique⟩ :=
    LanglandsSecondMainLemma.Local.newton f 1 e hderiv hres
  refine ⟨(z : F), ?_⟩
  have hz' : ((f.eval z : ringOfIntegers F) : F) = 0 :=
    congrArg (fun x : ringOfIntegers F ↦ (x : F)) hz
  have hzsq : (z : F) ^ 2 = 1 - u * v := by
    apply sub_eq_zero.mp
    simpa [f, uO, vO] using hz'
  simpa [pow_two] using hzsq.symm

/-- **Paper Lemma 12.2 (`D:MX:unit-symbol`)**.  Let `u` and `v` have
positive integral depth.  If

`v_F(2) + v_F(2) < v_F(u) + v_F(v)`,

then the actual quadratic norm symbol `(1 + u, 1 + v)` is trivial.  In the
paper's notation, where the finite values are `e`, `m`, and `n`, this is
exactly `m ≥ 1`, `n ≥ 1`, and `m + n > 2e`.

The formulation also harmlessly includes `u = 0` or `v = 0`; in those cases
one of the symbol entries is the split unit `1`. -/
theorem unitSymbol
    (hchar : ringChar F ≠ 2) (u v : F)
    (hu : ((1 : ℤ) : WithTop ℤ) ≤ ord F u)
    (hv : ((1 : ℤ) : WithTop ℤ) ≤ ord F v)
    (hdepth : ord F (2 : F) + ord F (2 : F) <
      ord F u + ord F v) :
    quadraticNormSymbol F hchar (oneAddUnit F u hu)
      (oneAddUnit F v hv) = 1 := by
  let a : Fˣ := oneAddUnit F u hu
  let b : Fˣ := oneAddUnit F v hv
  have ha : (a : F) = 1 + u := coe_oneAddUnit F u hu
  have hb : (b : F) = 1 + v := coe_oneAddUnit F v hv
  change quadraticNormSymbol F hchar a b = 1

  -- The split square class is the first branch in the paper.
  by_cases hasquare : IsSquare (1 + u)
  · have hasquare' : IsSquare (a : F) := by simpa only [ha] using hasquare
    unfold quadraticNormSymbol
    rw [quadraticNormCharacter_of_isSquare F hchar a hasquare']
    rfl

  have hu0 : u ≠ 0 := by
    intro hu0
    apply hasquare
    simp [hu0]
  have hane : (a : F) ≠ 1 := by
    rw [ha]
    exact add_ne_left.mpr hu0

  let minusU : Fˣ := Units.mk0 (-u) (neg_ne_zero.mpr hu0)
  have hminusU : (minusU : F) = -(u : F) := rfl
  have hsteinberg : quadraticNormSymbol F hchar a minusU = 1 := by
    have h := quadraticSymbol_one_sub F hchar a hane
    have hunit :
        Units.mk0 (1 - (a : F)) (sub_ne_zero.mpr hane.symm) = minusU := by
      apply Units.ext
      change 1 - (a : F) = -u
      rw [ha]
      ring
    simpa only [hunit] using h

  have hab_mul : quadraticNormSymbol F hchar a b =
      quadraticNormSymbol F hchar a (minusU * b) := by
    have hmul := quadraticSymbol_mul_right F hchar a minusU b
    rw [hsteinberg, one_mul] at hmul
    exact hmul.symm

  have huvpos : (0 : WithTop ℤ) < ord F (u * v) := by
    rw [ord_mul]
    exact (show (0 : WithTop ℤ) <
      ((1 : ℤ) : WithTop ℤ) + ((1 : ℤ) : WithTop ℤ) by norm_num).trans_le
        (add_le_add hu hv)
  have honeSub : 1 - u * v ≠ 0 := by
    intro hzero
    have huvone : u * v = 1 := (sub_eq_zero.mp hzero).symm
    have : ord F (u * v) = 0 := by rw [huvone, ord_one]
    exact (ne_of_gt huvpos) this
  have hasum : (a : F) + ((minusU * b : Fˣ) : F) ≠ 0 := by
    rw [Units.val_mul, ha, hminusU, hb]
    convert honeSub using 1
    ring

  have htransform := quadraticSymbol_transform F hchar a (minusU * b) hasum
  rw [hab_mul]
  rw [htransform]
  unfold quadraticNormSymbol
  rw [quadraticNormCharacter_of_isSquare F hchar
    (Units.mk0 ((a : F) + ((minusU * b : Fˣ) : F)) hasum)]
  · rfl
  · have hsquare := one_sub_mul_isSquare F hchar u v hu hv hdepth
    simp only [Units.val_mk0, Units.val_mul, ha, hminusU, hb]
    rw [show 1 + u + -u * (1 + v) = 1 - u * v by ring]
    exact hsquare

end

end LanglandsSecondMainLemma.Dyadic.Mixed
