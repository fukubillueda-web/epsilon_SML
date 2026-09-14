import LanglandsSecondMainLemma.Characters.QuadraticSymbolProduct

/-!
# Dyadic / Mixed / Symbols

The quadratic symbol here is the actual norm symbol constructed in
`Characters.QuadraticSymbolProduct`: its first argument determines the Kummer
quadratic extension (with the split square case interpreted as the trivial
character), and its second argument is evaluated by the resulting continuous
norm character.

This file records the symmetry and bilinearity used in the mixed dyadic
argument, proves the Steinberg relation `(A, 1 - A) = 1` with its necessary
nonvanishing hypothesis, and proves the change-of-variables identity
`(A, B) = (A + B, -A B)` when `A + B` is nonzero.

The last proof follows the symmetric conic in the controlling source.  In the
coordinates used by `QuadraticConicSolvable`, the forward linear change is

`(x, y, z) ↦ (A y + B z, x, y - z)`.

Its inverse divides by `A + B`, explaining precisely why that hypothesis is
present in the public theorem.

Blueprint: `blueprint/tasks/Dyadic/Mixed/Symbols.md`.
Paper: lines 6852--6874 of `references/epsilon_SML.tex`.
-/

namespace LanglandsSecondMainLemma.Dyadic.Mixed

open LanglandsSecondMainLemma.Characters

noncomputable section


variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Symmetry of the actual quadratic norm symbol, obtained from the symmetric
projective conic criterion. -/
theorem quadraticSymbol_symmetric (hchar : ringChar F ≠ 2)
    (a b : Fˣ) :
    quadraticNormSymbol F hchar a b =
      quadraticNormSymbol F hchar b a :=
  quadraticNormSymbol_symmetric F hchar a b

/-- Multiplicativity of the actual quadratic norm symbol in its second
argument.  This is the group-homomorphism property of the norm character. -/
theorem quadraticSymbol_mul_right (hchar : ringChar F ≠ 2)
    (a b c : Fˣ) :
    quadraticNormSymbol F hchar a (b * c) =
      quadraticNormSymbol F hchar a b *
        quadraticNormSymbol F hchar a c := by
  exact map_mul (quadraticNormCharacter F hchar a) b c

/-- Multiplicativity of the actual quadratic norm symbol in its first
argument.  It follows from conic symmetry and multiplicativity in the second
argument. -/
theorem quadraticSymbol_mul_left (hchar : ringChar F ≠ 2)
    (a b c : Fˣ) :
    quadraticNormSymbol F hchar (a * b) c =
      quadraticNormSymbol F hchar a c *
        quadraticNormSymbol F hchar b c := by
  change quadraticNormCharacter F hchar (a * b) c =
    (quadraticNormCharacter F hchar a *
      quadraticNormCharacter F hchar b) c
  rw [quadraticNormCharacter_mul F hchar a b]

/-- The Steinberg relation `(A, 1 - A) = 1`.  The assumption `A ≠ 1`
is exactly what makes `1 - A` a unit.  Conically, the point `(1, 1, 1)`
witnesses the relation. -/
theorem quadraticSymbol_one_sub (hchar : ringChar F ≠ 2)
    (a : Fˣ) (ha : (a : F) ≠ 1) :
    quadraticNormSymbol F hchar a
        (Units.mk0 (1 - (a : F)) (sub_ne_zero.mpr ha.symm)) = 1 := by
  apply (quadraticNormCharacter_eq_one_iff_conic F hchar a
    (Units.mk0 (1 - (a : F)) (sub_ne_zero.mpr ha.symm))).2
  refine ⟨1, 1, 1, Or.inl one_ne_zero, ?_⟩
  simp

omit [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] in
/-- The conic change of variables underlying
`quadraticSymbol_transform`. -/
private theorem quadraticConicSolvable_transform (a b : Fˣ)
    (hab : (a : F) + (b : F) ≠ 0) :
    QuadraticConicSolvable F a b ↔
      QuadraticConicSolvable F
        (Units.mk0 ((a : F) + (b : F)) hab) (-(a * b)) := by
  constructor
  · rintro ⟨x, y, z, hnonzero, hconic⟩
    refine ⟨(a : F) * y + (b : F) * z, x, y - z, ?_, ?_⟩
    · by_contra hzero
      push Not at hzero
      rcases hzero with ⟨hu, hx, hv⟩
      have hyz : y = z := sub_eq_zero.mp hv
      have hsumy : ((a : F) + (b : F)) * y = 0 := by
        calc
          ((a : F) + (b : F)) * y =
              (a : F) * y + (b : F) * z := by rw [hyz]; ring
          _ = 0 := hu
      have hy : y = 0 := (mul_eq_zero.mp hsumy).resolve_left hab
      have hz : z = 0 := by simpa [hyz] using hy
      rcases hnonzero with hx' | hy' | hz'
      · exact hx' hx
      · exact hy' hy
      · exact hz' hz
    · simp only [Units.val_mk0, Units.val_neg, Units.val_mul]
      change ((a : F) * y + (b : F) * z) ^ 2 =
        ((a : F) + (b : F)) * x ^ 2 +
          (-((a : F) * (b : F))) * (y - z) ^ 2
      linear_combination -((a : F) + (b : F)) * hconic
  · rintro ⟨u, x, v, hnonzero, hconic⟩
    simp only [Units.val_mk0, Units.val_neg, Units.val_mul] at hconic
    refine ⟨x,
      (u + (b : F) * v) / ((a : F) + (b : F)),
      (u - (a : F) * v) / ((a : F) + (b : F)), ?_, ?_⟩
    · by_contra hzero
      push Not at hzero
      rcases hzero with ⟨hx, hy, hz⟩
      have hu_identity :
          (a : F) * ((u + (b : F) * v) / ((a : F) + (b : F))) +
              (b : F) * ((u - (a : F) * v) /
                ((a : F) + (b : F))) = u := by
        field_simp [hab]
        ring
      have hv_identity :
          (u + (b : F) * v) / ((a : F) + (b : F)) -
              (u - (a : F) * v) / ((a : F) + (b : F)) = v := by
        field_simp [hab]
        ring
      have hu : u = 0 := by rw [← hu_identity, hy, hz]; simp
      have hv : v = 0 := by rw [← hv_identity, hy, hz]; simp
      rcases hnonzero with hu' | hx' | hv'
      · exact hu' hu
      · exact hx' hx
      · exact hv' hv
    · field_simp [hab]
      linear_combination -((a : F) + (b : F)) * hconic

private theorem complexUnits_eq_of_sq_eq_one
    (u v : ℂˣ) (hu : u ^ 2 = 1) (hv : v ^ 2 = 1)
    (hone : u = 1 ↔ v = 1) : u = v := by
  by_cases huone : u = 1
  · exact huone.trans (hone.mp huone).symm
  · have hvone : v ≠ 1 := fun h ↦ huone (hone.mpr h)
    have huval : (u : ℂ) ^ 2 = 1 := by
      simpa using congrArg Units.val hu
    have hvval : (v : ℂ) ^ 2 = 1 := by
      simpa using congrArg Units.val hv
    have huminus : (u : ℂ) = -1 :=
      (sq_eq_one_iff.mp huval).resolve_left
        (fun h ↦ huone (Units.ext h))
    have hvminus : (v : ℂ) = -1 :=
      (sq_eq_one_iff.mp hvval).resolve_left
        (fun h ↦ hvone (Units.ext h))
    exact Units.ext (huminus.trans hvminus.symm)

/-- The mixed-dyadic quadratic-symbol transform
`(A, B) = (A + B, -A B)`.  The assumption `A + B ≠ 0` is the
nondegeneracy condition for the inverse conic change of variables. -/
theorem quadraticSymbol_transform (hchar : ringChar F ≠ 2)
    (a b : Fˣ) (hab : (a : F) + (b : F) ≠ 0) :
    quadraticNormSymbol F hchar a b =
      quadraticNormSymbol F hchar
        (Units.mk0 ((a : F) + (b : F)) hab) (-(a * b)) := by
  apply complexUnits_eq_of_sq_eq_one
  · exact quadraticNormSymbol_sq F hchar a b
  · exact quadraticNormSymbol_sq F hchar
      (Units.mk0 ((a : F) + (b : F)) hab) (-(a * b))
  · simp only [quadraticNormSymbol,
      quadraticNormCharacter_eq_one_iff_conic F hchar]
    exact quadraticConicSolvable_transform F a b hab

end

end LanglandsSecondMainLemma.Dyadic.Mixed
