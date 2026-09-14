import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.LocalField.Lattices
import LanglandsFirstMainLemma.LocalField.MonogenicUniformizer
import LanglandsFirstMainLemma.LocalField.Valuation

/-!
# Basic / Intermediate Valuation

Blueprint: blueprint/tasks/Basic/IntermediateValuation.md
Paper: setup lines 121–155 and 277–337; extracted construction lines 121–136 and 277–314.

An intermediate field inherits the restriction of the top field's canonical valuation.  The
resulting valuative relation simultaneously makes the intermediate field a valuative extension
of the base and makes the top field a valuative extension of the intermediate field.  We also
record the restriction of the top field's normalized additive order and its integer subring.

The intermediate field is deliberately *not* assumed to be a nonarchimedean local field here.
Constructing that instance is the responsibility of `Basic.IntermediateCompleteness`.
-/

namespace LanglandsSecondMainLemma.Basic

open LanglandsFirstMainLemma

noncomputable section

section Restriction

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel K] [Algebra F K]

/-- The canonical valuation of the top field, restricted to an intermediate field.

Keeping the top field's value group at this stage avoids assuming a local-field structure on the
intermediate field.  Its canonical valuation for the induced valuative relation is equivalent to
this valuation; see `intermediateField_valuation_restriction` below. -/
noncomputable def intermediateFieldRestrictedValuation (L : IntermediateField F K) :
    Valuation L (ValuativeRel.ValueGroupWithZero K) :=
  (ValuativeRel.valuation K).comap (algebraMap L K)

/-- The valuative relation on an intermediate field induced by restricting the top-field
valuation.  It is kept explicit rather than installed globally, so callers control where the
new local instance enters a tower argument. -/
@[implicit_reducible]
noncomputable def intermediateFieldValuativeRel (L : IntermediateField F K) :
    ValuativeRel L :=
  ValuativeRel.ofValuation (intermediateFieldRestrictedValuation L)

@[simp]
theorem intermediateFieldRestrictedValuation_apply
    (L : IntermediateField F K) (x : L) :
    intermediateFieldRestrictedValuation L x =
      ValuativeRel.valuation K (x : K) :=
  rfl

/-- With the restricted relation, the top field is a valuative extension of the intermediate
field.  This is the upper edge of the valuation-compatible tower `F → L → K`. -/
theorem intermediateField_upperValuativeExtension (L : IntermediateField F K) :
    letI := intermediateFieldValuativeRel L
    ValuativeExtension L K := by
  letI := intermediateFieldValuativeRel L
  constructor
  intro x y
  rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K)]
  exact Iff.rfl

/-- The canonical valuation belonging to the induced relation is equivalent to the literal
restriction of the top-field valuation. -/
theorem intermediateField_canonicalValuation_isEquiv
    (L : IntermediateField F K) :
    letI := intermediateFieldValuativeRel L
    (ValuativeRel.valuation L).IsEquiv
      (intermediateFieldRestrictedValuation L) := by
  letI := intermediateFieldValuativeRel L
  letI : (intermediateFieldRestrictedValuation L).Compatible :=
    Valuation.Compatible.ofValuation _
  exact ValuativeRel.isEquiv _ _

/-- The subring of intermediate-field elements integral for the restricted top valuation. -/
noncomputable def intermediateFieldRingOfIntegers (L : IntermediateField F K) :
    Subring L :=
  (intermediateFieldRestrictedValuation L).integer

@[simp]
theorem mem_intermediateFieldRingOfIntegers_iff
    (L : IntermediateField F K) (x : L) :
    x ∈ intermediateFieldRingOfIntegers L ↔ (x : K) ∈ ringOfIntegers K :=
  Iff.rfl

/-- The FML integer ring for the induced relation is exactly the preimage of the top-field
integer ring. -/
theorem mem_intermediateField_canonicalRingOfIntegers_iff
    (L : IntermediateField F K) (x : L) :
    letI := intermediateFieldValuativeRel L
    x ∈ ringOfIntegers L ↔ (x : K) ∈ ringOfIntegers K := by
  letI := intermediateFieldValuativeRel L
  letI : ValuativeExtension L K := intermediateField_upperValuativeExtension L
  change ValuativeRel.valuation L x ≤ 1 ↔
    ValuativeRel.valuation K (x : K) ≤ 1
  rw [← map_one (ValuativeRel.valuation L),
    ← map_one (ValuativeRel.valuation K),
    ← Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation L),
    ← Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K)]
  simpa using
    (ValuativeExtension.vle_iff_vle (A := L) (B := K) x 1).symm

/-- The explicit restricted integer subring agrees with FML's canonical integer ring for the
induced valuative relation. -/
theorem intermediateFieldRingOfIntegers_eq_canonical
    (L : IntermediateField F K) :
    letI := intermediateFieldValuativeRel L
    intermediateFieldRingOfIntegers L = ringOfIntegers L := by
  letI := intermediateFieldValuativeRel L
  ext x
  rw [mem_intermediateFieldRingOfIntegers_iff,
    mem_intermediateField_canonicalRingOfIntegers_iff]

section NormalizedOrder

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The normalized additive order of the top local field, restricted to an intermediate field.

This is not advertised as the intrinsic normalized order of `L`: before the completeness step,
the restricted image can be a nontrivial subgroup of `ℤ`.  It nevertheless gives the exact
order comparison and integer ring needed to construct the intrinsic local-field structure. -/
noncomputable def intermediateFieldRestrictedOrder (L : IntermediateField F K) :
    AddValuation L (WithTop ℤ) :=
  (ord K).comap (algebraMap L K)

@[simp]
theorem intermediateFieldRestrictedOrder_apply
    (L : IntermediateField F K) (x : L) :
    intermediateFieldRestrictedOrder L x = ord K (x : K) :=
  rfl

end NormalizedOrder

end Restriction

section Tower

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [ValuativeRel K] [Algebra F K]
variable [ValuativeExtension F K]

/-- With the restricted relation, the intermediate field is a valuative extension of the base
field.  This is the lower edge of the valuation-compatible tower `F → L → K`. -/
theorem intermediateField_lowerValuativeExtension (L : IntermediateField F K) :
    letI := intermediateFieldValuativeRel L
    ValuativeExtension F L := by
  letI := intermediateFieldValuativeRel L
  constructor
  intro x y
  change ValuativeRel.valuation K
      (algebraMap L K (algebraMap F L x)) ≤
        ValuativeRel.valuation K (algebraMap L K (algebraMap F L y)) ↔ x ≤ᵥ y
  simp only [IntermediateField.algebraMap_apply,
    IntermediateField.coe_algebraMap_apply]
  rw [← Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K)]
  exact ValuativeExtension.vle_iff_vle x y

/-- Restricting the top valuation supplies both valuation-compatible edges through an actual
intermediate field, and the canonical valuation of the induced relation represents precisely
that restriction.

This is the foundation used by the subsequent completeness construction.  In particular, its
statement assumes no topology or local-field instance on `L`. -/
theorem intermediateField_valuation_restriction (L : IntermediateField F K) :
    letI := intermediateFieldValuativeRel L
    (ValuativeRel.valuation L).IsEquiv
        (intermediateFieldRestrictedValuation L) ∧
      ValuativeExtension F L ∧ ValuativeExtension L K := by
  letI := intermediateFieldValuativeRel L
  exact ⟨intermediateField_canonicalValuation_isEquiv L,
    intermediateField_lowerValuativeExtension L,
    intermediateField_upperValuativeExtension L⟩

end Tower

end

end LanglandsSecondMainLemma.Basic
