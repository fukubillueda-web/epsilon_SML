import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.LocalField.Lattices
import LanglandsFirstMainLemma.LocalField.MonogenicUniformizer
import LanglandsFirstMainLemma.LocalField.Valuation
import LanglandsSecondMainLemma.Basic.IntermediateValuation

/-!
# Basic / Intermediate Completeness

Blueprint: blueprint/tasks/Basic/IntermediateCompleteness.md
Paper: setup lines 121–155 and 277–337; extracted construction lines 121–136 and 277–314.

Starting from the valuation restriction constructed in `Basic.IntermediateValuation`, this file
equips an actual intermediate finite extension with its valuation topology and proves that it is
a nonarchimedean local field.  The proof obtains local compactness from Mathlib's theorem for a
finite-dimensional space over a complete locally compact field.  It does not assume a local-field
instance on the intermediate field.

Once the resulting instance is installed, Mathlib supplies completeness, discreteness of the
valuation, the discrete valuation ring structure on the integers, and finiteness of the residue
field.
-/

namespace LanglandsSecondMainLemma.Basic

open LanglandsFirstMainLemma
open scoped Topology

noncomputable section

section Topology

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel K] [Algebra F K]

/-- The valuation topology on an intermediate field, formed from the valuative relation induced
by the accepted restriction construction.

This definition is explicit rather than a global instance, so a caller can install the relation
and topology together without creating a topology diamond. -/
@[implicit_reducible]
noncomputable def intermediateFieldTopology (L : IntermediateField F K) :
    TopologicalSpace L :=
  letI := intermediateFieldValuativeRel L
  (ValuativeRel.valuation L).subgroups_basis.topology

/-- The topology constructed above is the canonical valuative topology for the restricted
relation. -/
theorem intermediateField_isValuativeTopology (L : IntermediateField F K) :
    letI := intermediateFieldValuativeRel L
    letI := intermediateFieldTopology L
    IsValuativeTopology L := by
  letI := intermediateFieldValuativeRel L
  letI := intermediateFieldTopology L
  exact ValuativeRel.isValuativeTopology L

end Topology

/-- Continuity of a valuation-preserving algebra map into a rank-one valuative field.

FML's `continuous_algebraMap` assumes that both fields are already local fields.  During the
intermediate-field construction the target local-field instance is exactly what is being proved,
so we use the same valuation-basis argument with only the target properties it actually needs:
a valuative topology and rank at most one. -/
private theorem continuous_algebraMap_to_rankOneValuativeField
    (A B : Type*) [Field A] [Field B]
    [ValuativeRel A] [TopologicalSpace A] [IsNonarchimedeanLocalField A]
    [ValuativeRel B] [TopologicalSpace B] [IsValuativeTopology B]
    [ValuativeRel.IsRankLeOne B]
    [Algebra A B] [ValuativeExtension A B] :
    Continuous (algebraMap A B) := by
  apply continuous_of_continuousAt_zero (algebraMap A B)
  rw [ContinuousAt, map_zero]
  rw [(IsValuativeTopology.hasBasis_nhds_zero A).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero B)]
  intro gammaB _
  obtain ⟨pi, hpi⟩ := ValuativeRel.valuation_surjective
    (ValuativeRel.uniformizer A)
  have hpiA : ValuativeRel.valuation A pi < 1 := by
    rw [hpi]
    exact ValuativeRel.uniformizer_lt_one
  have hpiB : ValuativeRel.valuation B (algebraMap A B pi) < 1 := by
    simpa only [map_one] using
      (Valuation.HasExtension.val_map_lt_iff
        (ValuativeRel.valuation A) (ValuativeRel.valuation B) pi 1).2 hpiA
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hpiB gammaB
  have hpi0 : ValuativeRel.valuation A pi ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    intro hzero
    subst pi
    exact ValuativeRel.uniformizer_ne_zero (R := A) hpi.symm
  refine ⟨Units.mk0 (ValuativeRel.valuation A pi ^ n) (pow_ne_zero n hpi0), trivial, ?_⟩
  intro x hx
  have hlt : ValuativeRel.valuation B (algebraMap A B x) <
      ValuativeRel.valuation B (algebraMap A B (pi ^ n)) :=
    (Valuation.HasExtension.val_map_lt_iff
      (ValuativeRel.valuation A) (ValuativeRel.valuation B) x (pi ^ n)).2 (by
        simpa using hx)
  rw [map_pow, map_pow] at hlt
  exact hlt.trans hn

section LocalField

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]

/-- Every actual intermediate field of a finite valuative extension of nonarchimedean local
fields is itself a nonarchimedean local field for the restricted valuation and its valuation
topology.

The conclusion packages the topology, local compactness, and nontriviality.  After installing it,
Mathlib derives `CompleteSpace L`, `ValuativeRel.IsDiscrete L`,
`IsDiscreteValuationRing (ringOfIntegers L)`, and `Finite (ResidueField L)` using the canonical
additive uniformity.  No one of those conclusions is assumed here. -/
theorem intermediateField_isNonarchimedeanLocalField (L : IntermediateField F K) :
    letI := intermediateFieldValuativeRel L
    letI := intermediateFieldTopology L
    IsNonarchimedeanLocalField L := by
  letI := intermediateFieldValuativeRel L
  letI := intermediateFieldTopology L
  letI : IsValuativeTopology L := intermediateField_isValuativeTopology L

  have hrestriction := intermediateField_valuation_restriction L
  letI : ValuativeExtension F L := hrestriction.2.1
  letI : ValuativeExtension L K := hrestriction.2.2
  letI : ValuativeRel.IsRankLeOne L :=
    ValuativeRel.IsRankLeOne.of_valuativeExtension (A := L) (B := K)

  letI : ContinuousSMul F L :=
    continuousSMul_of_algebraMap F L
      (continuous_algebraMap_to_rankOneValuativeField F L)

  -- Present the complete rank-one valued topology on the base as its equivalent normed-field
  -- topology so that Mathlib's finite-dimensional local-compactness theorem applies.
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  letI : Valued F (ValuativeRel.ValueGroupWithZero F) := inferInstance
  letI : (Valued.v : Valuation F (ValuativeRel.ValueGroupWithZero F)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := F).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField F := Valued.toNontriviallyNormedField F _
  letI : CompleteSpace F := inferInstance
  letI : LocallyCompactSpace L :=
    LocallyCompactSpace.of_finiteDimensional_of_complete F L

  have hnontrivial : ValuativeRel.IsNontrivial L := by
    rw [ValuativeRel.isNontrivial_iff_isNontrivial (ValuativeRel.valuation L)]
    obtain ⟨pi, hpi⟩ := ValuativeRel.valuation_surjective
      (ValuativeRel.uniformizer F)
    have hpiF : ValuativeRel.valuation F pi < 1 := by
      rw [hpi]
      exact ValuativeRel.uniformizer_lt_one
    have hpiL : ValuativeRel.valuation L (algebraMap F L pi) < 1 := by
      simpa only [map_one] using
        (Valuation.HasExtension.val_map_lt_iff
          (ValuativeRel.valuation F) (ValuativeRel.valuation L) pi 1).2 hpiF
    refine ⟨⟨algebraMap F L pi, ?_, hpiL.ne⟩⟩
    rw [Valuation.ne_zero_iff]
    intro hzero
    have hpi0 : pi ≠ 0 := by
      intro hpiZero
      subst pi
      exact ValuativeRel.uniformizer_ne_zero (R := F) hpi.symm
    apply hpi0
    apply FaithfulSMul.algebraMap_injective F L
    simpa only [map_zero] using hzero

  exact
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := hnontrivial }

end LocalField

end

end LanglandsSecondMainLemma.Basic
