import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.LocalField.Lattices
import LanglandsFirstMainLemma.LocalField.MonogenicUniformizer
import LanglandsFirstMainLemma.LocalField.Valuation
import LanglandsSecondMainLemma.Basic.Fields

/-!
# Basic / Norm Trace

Blueprint: `blueprint/tasks/Basic/NormTrace.md`.
Paper: setup lines 121–155 and 277–337, especially the explicit upper and lower
maps in lines 304–314.

This file gives the paper-facing forms of the standard field norm and trace
identities.  In a tower `F ⊂ L ⊂ K`, the inner operation in the transitivity
statements is the upper map `K → L` and the outer operation is the lower map
`L → F`.  The right-hand side is the direct map `K → F` supplied by the
scalar tower.

The conjugation statements quantify over an actual `F`-algebra automorphism
of the extension field.  Thus the fact that norm and trace are unchanged is a
proved property of the genuine field operations, not a commutation hypothesis
attached to an abstract map.
-/

namespace LanglandsSecondMainLemma.Basic

noncomputable section

section Tower

variable {F L K : Type*} [Field F] [Field L] [Field K]
variable [Algebra F L] [Algebra L K] [Algebra F K]
variable [IsScalarTower F L K]

/-- Field norms are transitive through the named intermediate field.

The inner norm is `N_{K/L}`, the outer norm is `N_{L/F}`, and the right-hand
side is the direct norm `N_{K/F}`.  The freeness assumptions are exactly those
used by Mathlib's determinant definition of the field norm in a tower. -/
theorem norm_tower [Module.Free F L] [Module.Free L K] (x : K) :
    Algebra.norm F (Algebra.norm L x) = Algebra.norm F x :=
  Algebra.norm_norm

/-- Field traces are transitive through the named intermediate field.

The inner trace is `Tr_{K/L}`, the outer trace is `Tr_{L/F}`, and the
right-hand side is the direct trace `Tr_{K/F}`. -/
theorem trace_tower
    [Module.Free F L] [Module.Finite F L]
    [Module.Free L K] [Module.Finite L K]
    (x : K) :
    Algebra.trace F L (Algebra.trace L K x) = Algebra.trace F K x :=
  Algebra.trace_trace x

end Tower

section Conjugation

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The field norm is invariant under an actual `F`-algebra automorphism of
the extension field. -/
@[simp]
theorem norm_conjugate (sigma : K ≃ₐ[F] K) (x : K) :
    Algebra.norm F (sigma x) = Algebra.norm F x :=
  Algebra.norm_eq_of_algEquiv sigma x

/-- The field trace is invariant under an actual `F`-algebra automorphism of
the extension field. -/
@[simp]
theorem trace_conjugate (sigma : K ≃ₐ[F] K) (x : K) :
    Algebra.trace F K (sigma x) = Algebra.trace F K x :=
  Algebra.trace_eq_of_algEquiv sigma x

end Conjugation

end

end LanglandsSecondMainLemma.Basic
