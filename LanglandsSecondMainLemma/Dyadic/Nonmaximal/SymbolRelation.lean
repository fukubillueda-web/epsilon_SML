import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.Origin
import LanglandsSecondMainLemma.Dyadic.Mixed.UnitSymbol

/-!
# Dyadic / Nonmaximal / Symbol Relation

The square-class calculation for `D:NM:character-relation` is proved below,
including the full ideal domain and every application of `D:MX:unit-symbol`.
The input valuations and alignment error are exactly `D:NM:xy` and
`D:NM:align`, as supplied by the accepted origin constructor.

The public theorem `dyadicNonmaximal_symbolRelation` concerns supplied
nontrivial actual norm characters. The origin generators construct algebra
isomorphisms from the quadratic algebras with parameters `U`, `V`, and `U*V`
to the three actual fields. Mathlib's determinant formula and invariance of
norm under algebra isomorphisms turn the public conic criterion into actual
norms. Kernel inclusion and order two then identify the given characters
with the canonical symbols. This construction uses the existing dependencies
and supplies every field-to-symbol identification in the proof.

Controlling source: `references/epsilon_SML.tex`, lines 7405--7458,
7500--7555, and 7567--7591, especially `D:NM:character-relation`.
-/

namespace LanglandsSecondMainLemma.Dyadic.Nonmaximal

open LanglandsFirstMainLemma
open LanglandsSecondMainLemma.Characters
open LanglandsSecondMainLemma.Dyadic.Mixed

noncomputable section

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private theorem symbol_square_right (hchar : ringChar F ≠ 2) (A B : Fˣ) :
    quadraticNormSymbol F hchar A (B ^ 2) = 1 := by
  rw [quadraticSymbol_symmetric]
  change quadraticNormCharacter F hchar (B ^ 2) A = 1
  rw [quadraticNormCharacter_of_isSquare F hchar (B ^ 2) (by
    simpa only [Units.val_pow_eq_pow_val] using IsSquare.sq (B : F))]
  rfl

private theorem symbol_unit_depth (hchar : ringChar F ≠ 2)
    (e m n : ℤ) (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : 2 * e < m + n)
    (A B : Fˣ) (hA : (A : F) - 1 ∈ lattice F m)
    (hB : (B : F) - 1 ∈ lattice F n) :
    quadraticNormSymbol F hchar A B = 1 := by
  have hAone : ((1 : ℤ) : WithTop ℤ) ≤ ord F ((A : F) - 1) :=
    (WithTop.coe_le_coe.mpr hm).trans ((mem_lattice F).mp hA)
  have hBone : ((1 : ℤ) : WithTop ℤ) ≤ ord F ((B : F) - 1) :=
    (WithTop.coe_le_coe.mpr hn).trans ((mem_lattice F).mp hB)
  have h := unitSymbol F hchar ((A : F) - 1) ((B : F) - 1) hAone hBone (by
    rw [htwo]
    calc
      (e : WithTop ℤ) + e < (m : WithTop ℤ) + n := by
        exact_mod_cast (show e + e < m + n by omega)
      _ ≤ ord F ((A : F) - 1) + ord F ((B : F) - 1) :=
        add_le_add ((mem_lattice F).mp hA) ((mem_lattice F).mp hB))
  have hAU : oneAddUnit F ((A : F) - 1) hAone = A := by ext; simp
  have hBU : oneAddUnit F ((B : F) - 1) hBone = B := by ext; simp
  simpa only [hAU, hBU] using h

/-- The conic transformation used twice in `D:NM:character-relation`.
The removed factor `4` is a square; the norm factor is exactly `-4*f`. -/
private theorem symbol_one_sub_transform (hchar : ringChar F ≠ 2)
    (f : Fˣ) (u : F) (A B C : Fˣ)
    (hA : (A : F) = 1 + 4 * (f : F))
    (hB : (B : F) = 1 - u)
    (hC : (C : F) = 1 + 4 * (f : F) * u) :
    quadraticNormSymbol F hchar A B =
      quadraticNormSymbol F hchar C (f * B * A) := by
  have htwo : (2 : F) ≠ 0 := by
    intro h
    apply Ring.neg_one_ne_one_of_char_ne_two hchar
    linear_combination -h
  let two : Fˣ := Units.mk0 2 htwo
  let minusFourF : Fˣ := -(two ^ 2 * f)
  have hAne : (A : F) ≠ 1 := by
    rw [hA]
    intro h
    have : (4 : F) * (f : F) = 0 := by linear_combination h
    exact (mul_ne_zero (by
      simpa only [show (4 : F) = 2 * 2 by norm_num] using mul_ne_zero htwo htwo)
        f.ne_zero) this
  have hnorm : quadraticNormSymbol F hchar A minusFourF = 1 := by
    have h := quadraticSymbol_one_sub F hchar A hAne
    have heq : Units.mk0 (1 - (A : F)) (sub_ne_zero.mpr hAne.symm) = minusFourF := by
      ext
      simp only [Units.val_mk0, Units.val_neg, Units.val_mul,
        Units.val_pow_eq_pow_val, hA, minusFourF, two]
      ring
    simpa only [heq] using h
  have hsum : (A : F) + ((minusFourF * B : Fˣ) : F) = (C : F) := by
    simp only [Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val,
      Units.val_mk0, hA, hB, hC, minusFourF, two]
    ring
  have hsum0 : (A : F) + ((minusFourF * B : Fˣ) : F) ≠ 0 := by
    rw [hsum]
    exact C.ne_zero
  have hfirst : Units.mk0 ((A : F) + ((minusFourF * B : Fˣ) : F)) hsum0 = C :=
    Units.ext hsum
  have hsecond : -(A * (minusFourF * B)) = two ^ 2 * (f * B * A) := by
    ext
    simp only [Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val,
      Units.val_mk0, minusFourF, two]
    ring
  calc
    quadraticNormSymbol F hchar A B =
        quadraticNormSymbol F hchar A (minusFourF * B) := by
      rw [quadraticSymbol_mul_right, hnorm, one_mul]
    _ = quadraticNormSymbol F hchar C (two ^ 2 * (f * B * A)) := by
      rw [quadraticSymbol_transform F hchar A (minusFourF * B) hsum0,
        hfirst, hsecond]
    _ = quadraticNormSymbol F hchar C (f * B * A) := by
      rw [quadraticSymbol_mul_right, symbol_square_right, one_mul]

/-- All depth estimates used in the nonmaximal character relation.  In
particular the alignment error is divided by its actual, possibly
nonintegral denominator. -/
theorem dyadicNonmaximal_symbolDepths
    (e a r : ℤ) (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (f g d u : F) (hf : ord F f = ((1 - 2 * a : ℤ) : WithTop ℤ))
    (hg : ord F g = ((1 - 2 * r : ℤ) : WithTop ℤ))
    (hd : ord F d = ((r - a : ℤ) : WithTop ℤ))
    (hE : f + d ^ 2 * g ∈ lattice F (1 - a))
    (hu : u ∈ lattice F a) :
    4 * f * u ∈ lattice F (2 * e - a + 1) ∧
      (f / g) * u ∈ lattice F (2 * r - a) ∧
      f / (-d ^ 2 * g) - 1 ∈ lattice F a := by
  have hfour : ord F (4 : F) = ((2 * e : ℤ) : WithTop ℤ) := by
    rw [show (4 : F) = 2 * 2 by norm_num, ord_mul, htwo]
    exact_mod_cast (show e + e = 2 * e by ring)
  have hfourf : 4 * f ∈ lattice F (2 * e + 1 - 2 * a) := by
    rw [mem_lattice, ord_mul, hfour, hf]
    exact_mod_cast (show 2 * e + 1 - 2 * a ≤ 2 * e + (1 - 2 * a) by omega)
  have hfu : 4 * f * u ∈ lattice F (2 * e - a + 1) := by
    convert mul_mem_lattice F hfourf hu using 1
    congr 1
    omega
  have hfg : f / g ∈ lattice F (2 * r - 2 * a) := by
    rw [mem_lattice, ord_div, hf, hg]
    exact_mod_cast (show 2 * r - 2 * a ≤ (1 - 2 * a) - (1 - 2 * r) by omega)
  have hw : (f / g) * u ∈ lattice F (2 * r - a) := by
    convert mul_mem_lattice F hfg hu using 1
    congr 1
    omega
  have hden : ord F (-d ^ 2 * g) = ((1 - 2 * a : ℤ) : WithTop ℤ) := by
    rw [ord_mul, ord_neg, ord_pow, hd, hg]
    exact_mod_cast (show 2 • (r - a) + (1 - 2 * r) = 1 - 2 * a by simp only [two_nsmul]; omega)
  have hden0 : -d ^ 2 * g ≠ 0 := (ord_ne_top_iff F).mp (by
    rw [hden]
    exact WithTop.coe_ne_top)
  have hratio : f / (-d ^ 2 * g) - 1 ∈ lattice F a := by
    rw [show f / (-d ^ 2 * g) - 1 = (f + d ^ 2 * g) / (-d ^ 2 * g) by
      rw [div_sub_one hden0]
      congr 1
      ring]
    rw [div_mem_lattice_iff F (-d ^ 2 * g) (f + d ^ 2 * g) (1 - 2 * a) a hden]
    convert hE using 1
    congr 1
    omega
  exact ⟨hfu, hw, hratio⟩

/-- The exact square-class calculation in `D:NM:character-relation`.
Every unit below is identified by its field value.  No vanishing of a
symbol is supplied as an assumption. -/
theorem dyadicNonmaximal_symbolRelation_squareClasses
    (hchar : ringChar F ≠ 2) (e a r : ℤ)
    (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (f g d : Fˣ)
    (hf : ord F (f : F) = ((1 - 2 * a : ℤ) : WithTop ℤ))
    (hg : ord F (g : F) = ((1 - 2 * r : ℤ) : WithTop ℤ))
    (hd : ord F (d : F) = ((r - a : ℤ) : WithTop ℤ))
    (hE : (f : F) + (d : F) ^ 2 * (g : F) ∈ lattice F (1 - a))
    (u : F) (hu : u ∈ lattice F a)
    (U V B₁ B₂ C : Fˣ)
    (hU : (U : F) = 1 + 4 * (f : F))
    (hV : (V : F) = 1 + 4 * (g : F))
    (hB₁ : (B₁ : F) = 1 - u)
    (hB₂ : (B₂ : F) = 1 - ((f : F) / (g : F)) * u)
    (hC : (C : F) = 1 + 4 * (f : F) * u) :
    quadraticNormSymbol F hchar U B₁ =
      quadraticNormSymbol F hchar V B₂ *
        quadraticNormSymbol F hchar (U * V) C := by
  obtain ⟨hCu, hwu, hRu⟩ :=
    dyadicNonmaximal_symbolDepths F e a r htwo (f : F) g d u hf hg hd hE hu
  have hCdepth : (C : F) - 1 ∈ lattice F (2 * e - a + 1) := by
    simpa only [hC, add_sub_cancel_left] using hCu
  have hB₁depth : (B₁ : F) - 1 ∈ lattice F a := by
    simpa only [hB₁, sub_sub_cancel_left] using neg_mem_lattice F hu
  have hB₂depth : (B₂ : F) - 1 ∈ lattice F (2 * r - a) := by
    simpa only [hB₂, sub_sub_cancel_left] using neg_mem_lattice F hwu
  let R : Fˣ := f / (-(d ^ 2) * g)
  have hRdepth : (R : F) - 1 ∈ lattice F a := by
    simpa only [R, Units.val_div_eq_div_val, Units.val_neg, Units.val_mul,
      Units.val_pow_eq_pow_val] using hRu
  have hCpositive : 1 ≤ 2 * e - a + 1 := by omega
  have hCB₁ : quadraticNormSymbol F hchar C B₁ = 1 :=
    symbol_unit_depth F hchar e (2 * e - a + 1) a htwo
      hCpositive ha (by omega) C B₁ hCdepth hB₁depth
  have hCB₂ : quadraticNormSymbol F hchar C B₂ = 1 :=
    symbol_unit_depth F hchar e (2 * e - a + 1) (2 * r - a) htwo
      hCpositive (by omega) (by omega) C B₂ hCdepth hB₂depth
  have hCR : quadraticNormSymbol F hchar C R = 1 :=
    symbol_unit_depth F hchar e (2 * e - a + 1) a htwo
      hCpositive ha (by omega) C R hCdepth hRdepth
  have hminusOneDepth : ((-1 : Fˣ) : F) - 1 ∈ lattice F e := by
    rw [mem_lattice]
    change (e : WithTop ℤ) ≤ ord F ((-1 : F) - 1)
    rw [show (-1 : F) - 1 = -2 by ring, ord_neg, htwo]
  have hCminusOne : quadraticNormSymbol F hchar C (-1) = 1 :=
    symbol_unit_depth F hchar e (2 * e - a + 1) e htwo
      hCpositive (by omega) (by omega) C (-1) hCdepth hminusOneDepth
  have hfR : f = R * (d ^ 2 * (-g)) := by
    dsimp only [R]
    rw [show d ^ 2 * (-g) = -(d ^ 2) * g by simp]
    exact (div_mul_cancel f (-(d ^ 2) * g)).symm
  have hCf : quadraticNormSymbol F hchar C f =
      quadraticNormSymbol F hchar C g := by
    conv_lhs => rw [hfR]
    rw [quadraticSymbol_mul_right, hCR, one_mul,
      quadraticSymbol_mul_right, symbol_square_right, one_mul]
    rw [show -g = (-1 : Fˣ) * g by simp, quadraticSymbol_mul_right,
      hCminusOne, one_mul]
  have hfirst : quadraticNormSymbol F hchar U B₁ =
      quadraticNormSymbol F hchar C g * quadraticNormSymbol F hchar C U := by
    rw [symbol_one_sub_transform F hchar f u U B₁ C hU hB₁ hC,
      quadraticSymbol_mul_right, quadraticSymbol_mul_right, hCB₁, mul_one, hCf]
  have hsecond : quadraticNormSymbol F hchar V B₂ =
      quadraticNormSymbol F hchar C g * quadraticNormSymbol F hchar C V := by
    have hC' : (C : F) = 1 + 4 * (g : F) * (((f : F) / (g : F)) * u) := by
      rw [hC]
      field_simp
    rw [symbol_one_sub_transform F hchar g (((f : F) / (g : F)) * u)
      V B₂ C hV hB₂ hC', quadraticSymbol_mul_right,
      quadraticSymbol_mul_right, hCB₂, mul_one]
  rw [hfirst, hsecond, quadraticSymbol_mul_left,
    quadraticSymbol_symmetric F hchar U C, quadraticSymbol_symmetric F hchar V C]
  symm
  calc
    (quadraticNormSymbol F hchar C g * quadraticNormSymbol F hchar C V) *
        (quadraticNormSymbol F hchar C U * quadraticNormSymbol F hchar C V) =
        (quadraticNormSymbol F hchar C g * quadraticNormSymbol F hchar C U) *
          quadraticNormSymbol F hchar C V ^ 2 := by rw [pow_two]; ac_rfl
    _ = _ := by rw [quadraticNormSymbol_sq, mul_one]

/-- Construct every character argument, uniformly for the whole ideal.
The second and third perturbations also lie in `𝔭_F^r`, as required by
the subsequent full stationary formulas. -/
theorem dyadicNonmaximal_symbolRelation_onIdeal
    (hchar : ringChar F ≠ 2) (e a r : ℤ)
    (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (f g d : F)
    (hf : ord F f = ((1 - 2 * a : ℤ) : WithTop ℤ))
    (hg : ord F g = ((1 - 2 * r : ℤ) : WithTop ℤ))
    (hd : ord F d = ((r - a : ℤ) : WithTop ℤ))
    (hE : f + d ^ 2 * g ∈ lattice F (1 - a)) :
    ∃ U V : Fˣ, (U : F) = 1 + 4 * f ∧ (V : F) = 1 + 4 * g ∧
      ∀ u ∈ lattice F a, ∃ B₁ B₂ C : Fˣ,
        (B₁ : F) = 1 - u ∧ (B₂ : F) = 1 - (f / g) * u ∧
        (C : F) = 1 + 4 * f * u ∧
        (B₂ : F) - 1 ∈ lattice F r ∧ (C : F) - 1 ∈ lattice F r ∧
        quadraticNormSymbol F hchar U B₁ =
          quadraticNormSymbol F hchar V B₂ *
            quadraticNormSymbol F hchar (U * V) C := by
  have hfour : ord F (4 : F) = ((2 * e : ℤ) : WithTop ℤ) := by
    rw [show (4 : F) = 2 * 2 by norm_num, ord_mul, htwo]
    exact_mod_cast (show e + e = 2 * e by ring)
  have hfpos : ((1 : ℤ) : WithTop ℤ) ≤ ord F (4 * f) := by
    rw [ord_mul, hfour, hf]
    exact_mod_cast (show 1 ≤ 2 * e + (1 - 2 * a) by omega)
  have hgpos : ((1 : ℤ) : WithTop ℤ) ≤ ord F (4 * g) := by
    rw [ord_mul, hfour, hg]
    exact_mod_cast (show 1 ≤ 2 * e + (1 - 2 * r) by omega)
  let U := oneAddUnit F (4 * f) hfpos
  let V := oneAddUnit F (4 * g) hgpos
  refine ⟨U, V, coe_oneAddUnit F _ _, coe_oneAddUnit F _ _, ?_⟩
  intro u hu
  obtain ⟨hCu, hwu, _⟩ := dyadicNonmaximal_symbolDepths F e a r htwo f g d u hf hg hd hE hu
  have hu1 : ((1 : ℤ) : WithTop ℤ) ≤ ord F (-u) := by
    rw [ord_neg]
    exact (WithTop.coe_le_coe.mpr ha).trans ((mem_lattice F).mp hu)
  have hw1 : ((1 : ℤ) : WithTop ℤ) ≤ ord F (-((f / g) * u)) := by
    rw [ord_neg]
    exact (WithTop.coe_le_coe.mpr (show 1 ≤ 2 * r - a by omega)).trans
      ((mem_lattice F).mp hwu)
  have hC1 : ((1 : ℤ) : WithTop ℤ) ≤ ord F (4 * f * u) :=
    (WithTop.coe_le_coe.mpr (show 1 ≤ 2 * e - a + 1 by omega)).trans
      ((mem_lattice F).mp hCu)
  let B₁ := oneAddUnit F (-u) hu1
  let B₂ := oneAddUnit F (-((f / g) * u)) hw1
  let C := oneAddUnit F (4 * f * u) hC1
  have hB₁ : (B₁ : F) = 1 - u := by simp only [B₁, coe_oneAddUnit, sub_eq_add_neg]
  have hB₂ : (B₂ : F) = 1 - (f / g) * u := by
    simp only [B₂, coe_oneAddUnit, sub_eq_add_neg]
  have hC : (C : F) = 1 + 4 * f * u := coe_oneAddUnit F _ _
  have hf0 : f ≠ 0 := (ord_ne_top_iff F).mp (by rw [hf]; exact WithTop.coe_ne_top)
  have hg0 : g ≠ 0 := (ord_ne_top_iff F).mp (by rw [hg]; exact WithTop.coe_ne_top)
  have hd0 : d ≠ 0 := (ord_ne_top_iff F).mp (by rw [hd]; exact WithTop.coe_ne_top)
  refine ⟨B₁, B₂, C, hB₁, hB₂, hC, ?_, ?_, ?_⟩
  · rw [hB₂, sub_sub_cancel_left]
    exact neg_mem_lattice F (lattice_antitone F (by omega) hwu)
  · rw [hC, add_sub_cancel_left]
    exact lattice_antitone F (by omega) hCu
  · exact dyadicNonmaximal_symbolRelation_squareClasses F hchar e a r ha har hre htwo
      (Units.mk0 f hf0) (Units.mk0 g hg0) (Units.mk0 d hd0)
      hf hg hd hE u hu U V B₁ B₂ C (coe_oneAddUnit F _ _)
      (coe_oneAddUnit F _ _) hB₁ hB₂ hC

/-- Apply the full-ideal calculation to the proved aligned origin data.
The canonical symbols here are identified with the supplied actual norm
characters in `dyadicNonmaximal_symbolRelation` below. -/
theorem dyadicNonmaximal_symbolRelation_from_origin
    {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [Module.Finite F K]
    (L₁ L₂ L₃ : IntermediateField F K)
    [ValuativeRel L₁] [TopologicalSpace L₁] [IsNonarchimedeanLocalField L₁]
    [ValuativeRel L₂] [TopologicalSpace L₂] [IsNonarchimedeanLocalField L₂]
    [ValuativeRel L₃] [TopologicalSpace L₃] [IsNonarchimedeanLocalField L₃]
    [ValuativeExtension F L₁] [ValuativeExtension L₁ K]
    [ValuativeExtension F L₂] [ValuativeExtension L₂ K]
    [ValuativeExtension F L₃] [ValuativeExtension L₃ K]
    [Module.Finite F L₁] [Module.Finite L₁ K]
    [Module.Finite F L₂] [Module.Finite L₂ K]
    [Module.Finite F L₃] [Module.Finite L₃ K]
    (hchar : ringChar F ≠ 2)
    (e a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (x : L₁) (y : L₂) (z : L₃) (f g d : F)
    (O : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d) :
    ∃ U V : Fˣ, (U : F) = 1 + 4 * f ∧ (V : F) = 1 + 4 * g ∧
      ∀ u ∈ lattice F (a : ℤ), ∃ B₁ B₂ C : Fˣ,
        (B₁ : F) = 1 - u ∧ (B₂ : F) = 1 - (f / g) * u ∧
        (C : F) = 1 + 4 * f * u ∧
        (B₂ : F) - 1 ∈ lattice F (r : ℤ) ∧ (C : F) - 1 ∈ lattice F (r : ℤ) ∧
        quadraticNormSymbol F hchar U B₁ =
          quadraticNormSymbol F hchar V B₂ *
            quadraticNormSymbol F hchar (U * V) C := by
  exact dyadicNonmaximal_symbolRelation_onIdeal F hchar e a r
    (by exact_mod_cast ha) (by exact_mod_cast har) (by exact_mod_cast hre)
    htwo f g d O.f_order O.g_order O.d_order (by rw [← O.E_eq]; exact O.E_lattice)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The actual generator identifies its field with the quadratic algebra.
Surjectivity follows from generation, and injectivity from degree two. -/
private noncomputable def artinSchreierKummerEquiv
    {E : Type*} [Field E] [Algebra F E] [Module.Finite F E]
    [Algebra.IsQuadraticExtension F E]
    (htwo : (2 : F) ≠ 0) (x : E) (f : F)
    (hx : x ^ 2 + x = algebraMap F E f)
    (hgen : Algebra.adjoin F ({x} : Set E) = ⊤)
    (A : Fˣ) (hA : (A : F) = 1 + 4 * f) :
    QuadraticAlgebra F (A : F) 0 ≃ₐ[F] E := by
  have htwoE : (2 : E) ≠ 0 := by
    intro h
    apply htwo
    apply (algebraMap F E).injective
    simpa only [map_ofNat, map_zero] using h
  let s : E := 1 + 2 * x
  have hs : s * s = (A : F) • (1 : E) + (0 : F) • s := by
    simp only [Algebra.smul_def, map_zero, zero_mul, add_zero, mul_one, hA,
      map_add, map_one, map_mul, map_ofNat]
    dsimp only [s]
    linear_combination 4 * hx
  let φ : QuadraticAlgebra F (A : F) 0 →ₐ[F] E := QuadraticAlgebra.lift ⟨s, hs⟩
  have hxrange : x ∈ φ.range := by
    refine ⟨⟨-(2 : F)⁻¹, (2 : F)⁻¹⟩, ?_⟩
    change -(2 : F)⁻¹ • (1 : E) + (2 : F)⁻¹ • s = x
    simp only [Algebra.smul_def, map_neg, map_inv₀, map_ofNat, mul_one, s]
    field_simp
    ring
  have hsurj : Function.Surjective φ := by
    have hle : Algebra.adjoin F ({x} : Set E) ≤ φ.range :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr hxrange)
    rw [hgen] at hle
    intro y
    exact hle (show y ∈ (⊤ : Subalgebra F E) from trivial)
  have hinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := φ.toLinearMap) (by
      rw [QuadraticAlgebra.finrank_eq_two,
        Algebra.IsQuadraticExtension.finrank_eq_two F E])).mpr hsurj
  exact AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩

/-- A conic solution produces a norm in the supplied field, via the actual
algebra isomorphism. In particular its projective denominator cannot vanish. -/
private theorem normCharacter_one_of_symbol_one
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [ValuativeExtension F E]
    [Module.Finite F E]
    (hchar : ringChar F ≠ 2) (A : Fˣ)
    (T : QuadraticAlgebra F (A : F) 0 ≃ₐ[F] E)
    (τ : NormCharacter F E) (b : Fˣ)
    (hb : quadraticNormCharacter F hchar A b = 1) : τ.1 b = 1 := by
  obtain ⟨c, d, t, hne, hconic⟩ :=
    (quadraticNormCharacter_eq_one_iff_conic F hchar A b).mp hb
  have normFormula (w : QuadraticAlgebra F (A : F) 0) :
      norm F E (T w) = w.re ^ 2 - (A : F) * w.im ^ 2 := by
    rw [Algebra.norm_eq_of_algEquiv, Algebra.norm_apply]
    change (DistribSMul.toLinearMap F (QuadraticAlgebra F (A : F) 0) w).det = _
    rw [QuadraticAlgebra.det_toLinearMap_eq_norm]
    simp only [QuadraticAlgebra.norm_def, zero_mul, add_zero, pow_two]
    ring
  let w : QuadraticAlgebra F (A : F) 0 := ⟨c, d⟩
  have hnorm : norm F E (T w) = (b : F) * t ^ 2 := by
    rw [normFormula]
    change c ^ 2 - (A : F) * d ^ 2 = (b : F) * t ^ 2
    linear_combination hconic
  have ht : t ≠ 0 := by
    intro ht
    have hn0 : norm F E (T w) = 0 := by rw [hnorm, ht]; simp
    have hw0 : w = 0 := T.injective (by
      simpa only [map_zero] using (Algebra.norm_eq_zero_iff).mp hn0)
    have hc0 : c = 0 := congrArg QuadraticAlgebra.re hw0
    have hd0 : d = 0 := congrArg QuadraticAlgebra.im hw0
    exact hne.elim (fun h ↦ h hc0) (fun h ↦ h.elim (fun h ↦ h hd0) (fun h ↦ h ht))
  let v : E := T ⟨c / t, d / t⟩
  have hvnorm : norm F E v = (b : F) := by
    rw [normFormula]
    change (c / t) ^ 2 - (A : F) * (d / t) ^ 2 = (b : F)
    field_simp
    linear_combination hconic
  have hv0 : v ≠ 0 := (Algebra.norm_ne_zero_iff).mp (by rw [hvnorm]; exact b.ne_zero)
  exact τ.eq_one_on_normRange F E b ⟨Units.mk0 v hv0, Units.ext hvnorm⟩

/-- Kernel inclusion in a nontrivial norm character suffices: the conic
character has order two, so both characters have the same two fibers.
This uses no ramification-index or norm-character-cardinality hypothesis. -/
private theorem normCharacter_eq_symbol_of_equiv
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [ValuativeExtension F E]
    [Module.Finite F E]
    (hchar : ringChar F ≠ 2) (A : Fˣ)
    (T : QuadraticAlgebra F (A : F) 0 ≃ₐ[F] E)
    (τ : NormCharacter F E) (hτ : τ ≠ 1) :
    τ.1 = quadraticNormCharacter F hchar A := by
  have hk := normCharacter_one_of_symbol_one F hchar A T τ
  have hsq (b : Fˣ) : τ.1 b ^ 2 = 1 := by
    rw [← map_pow]
    apply hk
    rw [map_pow]
    exact quadraticNormSymbol_sq F hchar A b
  have neg_value (c : ℂˣ) (hc : c ^ 2 = 1) (hne : c ≠ 1) : c = -1 := by
    apply Units.ext
    exact (sq_eq_one_iff.mp (show (c : ℂ) ^ 2 = 1 by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hc)).resolve_left
        (fun h ↦ hne (Units.ext h))
  obtain ⟨t, ht⟩ : ∃ t : Fˣ, τ.1 t ≠ 1 := by
    by_contra! h
    apply hτ
    apply NormCharacter.ext
    exact ContinuousMonoidHom.ext h
  have hτt : τ.1 t = -1 := neg_value _ (hsq t) ht
  have hAt : quadraticNormCharacter F hchar A t = -1 :=
    neg_value _ (quadraticNormSymbol_sq F hchar A t) (fun h ↦ ht (hk t h))
  apply ContinuousMonoidHom.ext
  intro b
  by_cases hb : quadraticNormCharacter F hchar A b = 1
  · exact (hk b hb).trans hb.symm
  · have hAb : quadraticNormCharacter F hchar A b = -1 :=
      neg_value _ (quadraticNormSymbol_sq F hchar A b) hb
    have hm : τ.1 b * τ.1 t = 1 := by
      rw [← map_mul]
      apply hk
      rw [map_mul, hAb, hAt]
      simp
    calc
      τ.1 b = τ.1 b * (τ.1 t * τ.1 t) := by rw [← pow_two, hsq, mul_one]
      _ = τ.1 t := by rw [← mul_assoc, hm, one_mul]
      _ = -1 := hτt
      _ = quadraticNormCharacter F hchar A b := hAb.symm

/-- **The actual lower-character identity, `D:NM:character-relation`.**
For every `u ∈ 𝔭_F^a`, all three character arguments are constructed as
field units. The second and third perturbations lie in `𝔭_F^r`.
The given nontrivial continuous norm characters are identified with the
symbols by the proved generators in the origin data. -/
theorem dyadicNonmaximal_symbolRelation
    {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [Module.Finite F K]
    (L₁ L₂ L₃ : IntermediateField F K)
    [ValuativeRel L₁] [TopologicalSpace L₁] [IsNonarchimedeanLocalField L₁]
    [ValuativeRel L₂] [TopologicalSpace L₂] [IsNonarchimedeanLocalField L₂]
    [ValuativeRel L₃] [TopologicalSpace L₃] [IsNonarchimedeanLocalField L₃]
    [ValuativeExtension F L₁] [ValuativeExtension L₁ K]
    [ValuativeExtension F L₂] [ValuativeExtension L₂ K]
    [ValuativeExtension F L₃] [ValuativeExtension L₃ K]
    [Module.Finite F L₁] [Module.Finite L₁ K]
    [Module.Finite F L₂] [Module.Finite L₂ K]
    [Module.Finite F L₃] [Module.Finite L₃ K]
    [Algebra.IsQuadraticExtension F L₁]
    [Algebra.IsQuadraticExtension F L₂]
    [Algebra.IsQuadraticExtension F L₃]
    (hchar : ringChar F ≠ 2)
    (e a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (x : L₁) (y : L₂) (z : L₃) (f g d : F)
    (O : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂) (ω₃ : NormCharacter F L₃)
    (hω₁ : ω₁ ≠ 1) (hω₂ : ω₂ ≠ 1) (hω₃ : ω₃ ≠ 1) :
    ∀ u ∈ lattice F (a : ℤ), ∃ B₁ B₂ C : Fˣ,
      (B₁ : F) = 1 - u ∧ (B₂ : F) = 1 - (f / g) * u ∧
      (C : F) = 1 + 4 * f * u ∧
      (B₂ : F) - 1 ∈ lattice F (r : ℤ) ∧ (C : F) - 1 ∈ lattice F (r : ℤ) ∧
      ω₁.1 B₁ = ω₂.1 B₂ * ω₃.1 C := by
  obtain ⟨U, V, hU, hV, hsymbols⟩ :=
    dyadicNonmaximal_symbolRelation_from_origin F L₁ L₂ L₃ hchar e a r
      ha har hre htwo x y z f g d O
  have htwo0 : (2 : F) ≠ 0 := (ord_ne_top_iff F).mp (by
    rw [htwo]
    exact WithTop.coe_ne_top)
  have hUV : ((U * V : Fˣ) : F) = 1 + 4 * (f + g + 4 * f * g) := by
    rw [Units.val_mul, hU, hV]
    ring
  have h₁ := normCharacter_eq_symbol_of_equiv F hchar U
    (artinSchreierKummerEquiv F htwo0 x f O.x_polynomial O.x_generates U hU) ω₁ hω₁
  have h₂ := normCharacter_eq_symbol_of_equiv F hchar V
    (artinSchreierKummerEquiv F htwo0 y g O.y_polynomial O.y_generates V hV) ω₂ hω₂
  have h₃ := normCharacter_eq_symbol_of_equiv F hchar (U * V)
    (artinSchreierKummerEquiv F htwo0 z (f + g + 4 * f * g)
      O.z_polynomial O.z_generates (U * V) hUV) ω₃ hω₃
  intro u hu
  obtain ⟨B₁, B₂, C, hB₁, hB₂, hC, hB₂depth, hCdepth, hrelation⟩ := hsymbols u hu
  refine ⟨B₁, B₂, C, hB₁, hB₂, hC, hB₂depth, hCdepth, ?_⟩
  rw [h₁, h₂, h₃]
  exact hrelation

end
end LanglandsSecondMainLemma.Dyadic.Nonmaximal
