import LanglandsFirstMainLemma.Delta.FirstMainStatement
import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.LocalField.Lattices
import LanglandsFirstMainLemma.LocalField.MonogenicUniformizer
import LanglandsFirstMainLemma.LocalField.Valuation
import LanglandsSecondMainLemma.Basic.IntermediateCompleteness
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Basic / Fields

Blueprint: `blueprint/tasks/Basic/Fields.md`.
Paper: setup lines 121–155 and 277–337; extracted construction lines 121–136 and
277–314.

This file completes the field-theoretic interface for the local diamond. An actual intermediate
field uses the valuation relation and topology constructed in `Basic.IntermediateValuation` and
`Basic.IntermediateCompleteness`. Mathlib then supplies the finite/free module structures and
the scalar tower on both sides of the intermediate field.

For the Galois part, the input is the existence of an equivalence from the *actual* group `Gal(K/F)` to
`C_ℓ × C_ℓ`, represented by two copies of `Multiplicative (ZMod ℓ)`. Thus the lower edge is
proved Galois from normality of its genuine fixing subgroup, while the upper edge is the usual
top edge of a Galois tower. Their common degree `ℓ` and cyclicity are derived rather than
assumed.
-/

namespace LanglandsSecondMainLemma.Basic

open LanglandsFirstMainLemma

noncomputable section

section IntermediateLocalField

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]

/-- An actual intermediate field, equipped with the restricted valuation relation and its
valuation topology, is a nonarchimedean local field.

This is the public installation point for downstream tower arguments. The topology and
valuation are exactly the constructions accepted in `Basic.IntermediateCompleteness`; this
theorem does not construct a second topology or valuation. -/
theorem intermediateField_localField (L : IntermediateField F K) :
    letI := intermediateFieldValuativeRel L
    letI := intermediateFieldTopology L
    IsNonarchimedeanLocalField L := by
  letI := intermediateFieldValuativeRel L
  letI := intermediateFieldTopology L
  exact intermediateField_isNonarchimedeanLocalField L

end IntermediateLocalField

section PrimeSquareAlgebra

variable {F K : Type*} [Field F] [Field K]
variable [Algebra F K]

/-- An equivalence with `C_ℓ × C_ℓ` makes the actual Galois group commutative. This is
kept private because the public result exposes the resulting field extensions, not an auxiliary
group-theoretic typeclass. -/
private theorem actualGaloisGroup_isMulCommutative
    {ℓ : ℕ}
    (hG : Gal(K/F) ≃* (Multiplicative (ZMod ℓ) × Multiplicative (ZMod ℓ))) :
    IsMulCommutative Gal(K/F) := by
  apply IsMulCommutative.of_comm
  intro σ τ
  apply hG.injective
  simpa only [map_mul] using mul_comm (hG σ) (hG τ)

variable [Module.Finite F K]

/-- Every intermediate field of the actual `C_ℓ × C_ℓ` Galois extension is Galois over
the base. The proof uses the genuine fixing subgroup and Galois correspondence: commutativity
makes that subgroup normal. -/
private theorem intermediateField_lower_isGalois
    {ℓ : ℕ} [IsGalois F K]
    (hG : Gal(K/F) ≃* (Multiplicative (ZMod ℓ) × Multiplicative (ZMod ℓ)))
    (L : IntermediateField F K) : IsGalois F L := by
  letI : IsMulCommutative Gal(K/F) := actualGaloisGroup_isMulCommutative hG
  letI : L.fixingSubgroup.Normal := inferInstance
  have hfixed : IsGalois F (IntermediateField.fixedField L.fixingSubgroup) :=
    IsGalois.of_fixedField_normal_subgroup L.fixingSubgroup
  rw [IsGalois.fixedField_fixingSubgroup L] at hfixed
  exact hfixed

/-- The equivalence with `C_ℓ × C_ℓ` computes the total degree of the actual finite
Galois extension. -/
private theorem primeSquare_totalDegree
    {ℓ : ℕ} [IsGalois F K]
    (hG : Gal(K/F) ≃* (Multiplicative (ZMod ℓ) × Multiplicative (ZMod ℓ))) :
    Module.finrank F K = ℓ * ℓ := by
  rw [← IsGalois.card_aut_eq_finrank F K, Nat.card_congr hG.toEquiv]
  have hcard : Nat.card (Multiplicative (ZMod ℓ)) = ℓ :=
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod ℓ)
  rw [Nat.card_prod, hcard]

/-- If a lower intermediate edge has degree `ℓ`, tower multiplicativity and the actual total
Galois-group cardinality force the upper edge to have degree `ℓ` as well. -/
private theorem intermediateField_upperDegree
    {ℓ : ℕ} (hℓ : ℓ.Prime) [IsGalois F K]
    (hG : Gal(K/F) ≃* (Multiplicative (ZMod ℓ) × Multiplicative (ZMod ℓ)))
    (L : IntermediateField F K) (hL : Module.finrank F L = ℓ) :
    Module.finrank L K = ℓ := by
  have htower := Module.finrank_mul_finrank F L K
  rw [hL, primeSquare_totalDegree hG] at htower
  exact Nat.mul_left_cancel hℓ.pos htower

/-- The lower edge is an FML cyclic prime extension. Galoisness comes from the actual fixing
subgroup above, and cyclicity comes from the prime cardinality of its actual automorphism
group. -/
private theorem intermediateField_lower_cyclicPrime
    {ℓ : ℕ} (hℓ : ℓ.Prime) [IsGalois F K]
    (hG : Gal(K/F) ≃* (Multiplicative (ZMod ℓ) × Multiplicative (ZMod ℓ)))
    (L : IntermediateField F K) (hL : Module.finrank F L = ℓ) :
    CyclicPrimeExtension F L := by
  letI : IsGalois F L := intermediateField_lower_isGalois hG L
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  refine ⟨inferInstance, ?_, hL.symm ▸ hℓ⟩
  apply isCyclic_of_prime_card (p := ℓ)
  rw [IsGalois.card_aut_eq_finrank F L, hL]

/-- The upper edge is an FML cyclic prime extension. It is the top edge of the genuine Galois
tower, and its degree is derived from tower multiplicativity rather than postulated. -/
private theorem intermediateField_upper_cyclicPrime
    {ℓ : ℕ} (hℓ : ℓ.Prime) [IsGalois F K]
    (hG : Gal(K/F) ≃* (Multiplicative (ZMod ℓ) × Multiplicative (ZMod ℓ)))
    (L : IntermediateField F K) (hL : Module.finrank F L = ℓ) :
    CyclicPrimeExtension L K := by
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  have hdegree : Module.finrank L K = ℓ :=
    intermediateField_upperDegree hℓ hG L hL
  refine ⟨inferInstance, ?_, hdegree.symm ▸ hℓ⟩
  apply isCyclic_of_prime_card (p := ℓ)
  rw [IsGalois.card_aut_eq_finrank L K, hdegree]

end PrimeSquareAlgebra

section CompatibleTower

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

/-- The complete field interface for a degree-`ℓ` intermediate field in an actual
`C_ℓ × C_ℓ` local Galois extension.

After installing the accepted restricted valuation and topology, both algebra edges are finite
and free, `F → L → K` is the canonical scalar tower, and both valuation restrictions are
compatible. The actual Galois-group equivalence computes the total and upper degrees and proves
that both edges satisfy FML's `CyclicPrimeExtension` predicate. In particular, no Galoisness,
cyclicity, or prime degree is assumed separately for either edge. -/
theorem intermediateField_tower_compatible
    {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod ℓ) × Multiplicative (ZMod ℓ))))
    (L : IntermediateField F K) (hL : Module.finrank F L = ℓ) :
    letI := intermediateFieldValuativeRel L
    letI := intermediateFieldTopology L
    IsNonarchimedeanLocalField L ∧
      Module.Free F L ∧ Module.Finite F L ∧
      Module.Free L K ∧ Module.Finite L K ∧
      IsScalarTower F L K ∧
      ValuativeExtension F L ∧ ValuativeExtension L K ∧
      Module.finrank F K = ℓ * ℓ ∧
      Module.finrank F L = ℓ ∧ Module.finrank L K = ℓ ∧
      CyclicPrimeExtension F L ∧ CyclicPrimeExtension L K := by
  letI := intermediateFieldValuativeRel L
  letI := intermediateFieldTopology L
  let hG' := Classical.choice hG
  have htotal : Module.finrank F K = ℓ * ℓ := primeSquare_totalDegree hG'
  have hupper : Module.finrank L K = ℓ := intermediateField_upperDegree hℓ hG' L hL
  exact ⟨intermediateField_localField L,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    intermediateField_lowerValuativeExtension L,
    intermediateField_upperValuativeExtension L,
    htotal, hL, hupper,
    intermediateField_lower_cyclicPrime hℓ hG' L hL,
    intermediateField_upper_cyclicPrime hℓ hG' L hL⟩

end CompatibleTower

end

end LanglandsSecondMainLemma.Basic
