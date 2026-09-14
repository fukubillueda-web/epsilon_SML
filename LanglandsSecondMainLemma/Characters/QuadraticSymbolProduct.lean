import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Basic.Characters
import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# Characters / Quadratic Symbol Product

This file constructs the quadratic norm character attached to every square
class of a nonarchimedean local field of characteristic different from two.
For a nonsquare parameter, the extension is the actual Kummer quadratic
algebra, equipped with its spectral valuative topology; FML's index-two norm
theorem then supplies the unique nontrivial character trivial on its norms.

The norm formula gives the conic criterion from the paper.  Symmetry of that
conic makes the norm symbol symmetric, which in turn proves multiplicativity
in its parameter and yields an injective homomorphism from square classes to
continuous quadratic characters.

Blueprint: `blueprint/tasks/Characters/QuadraticSymbolProduct.md`.
Paper: lines 8978--8992 of `references/epsilon_SML.tex`.
-/

namespace LanglandsSecondMainLemma.Characters

open LanglandsFirstMainLemma
open Polynomial

noncomputable section


variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

@[implicit_reducible] private noncomputable def baseNormedField : NontriviallyNormedField F := by
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  letI : Valued F (ValuativeRel.ValueGroupWithZero F) := inferInstance
  letI : (Valued.v : Valuation F (ValuativeRel.ValueGroupWithZero F)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := F).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  exact Valued.toNontriviallyNormedField F _

private abbrev Q (a : Fˣ) := QuadraticAlgebra F (a : F) 0

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem nonsquareFact (a : Fˣ) (ha : ¬ IsSquare (a : F)) :
    ∀ r : F, r ^ 2 ≠ (a : F) + 0 * r := by
  intro r hr
  apply ha
  refine ⟨r, ?_⟩
  simpa [pow_two] using hr.symm

@[implicit_reducible] private noncomputable def qField
    (a : Fˣ) (ha : ¬ IsSquare (a : F)) : Field (Q F a) := by
  letI : Fact (∀ r : F, r ^ 2 ≠ (a : F) + 0 * r) := ⟨nonsquareFact F a ha⟩
  exact inferInstance

@[implicit_reducible] private noncomputable def qNormedField
    (a : Fˣ) (ha : ¬ IsSquare (a : F)) :
    NormedField (Q F a) := by
  letI : Field (Q F a) := qField F a ha
  letI : NontriviallyNormedField F := baseNormedField F
  letI : Algebra.IsAlgebraic F (Q F a) := Algebra.IsIntegral.isAlgebraic
  exact spectralNorm.normedField F (Q F a)

@[implicit_reducible] private noncomputable def qTopology
    (a : Fˣ) (ha : ¬ IsSquare (a : F)) : TopologicalSpace (Q F a) := by
  letI : Field (Q F a) := qField F a ha
  letI : NormedField (Q F a) := qNormedField F a ha
  exact inferInstance

private theorem qIsUltrametric (a : Fˣ) (ha : ¬ IsSquare (a : F)) :
    letI : Field (Q F a) := qField F a ha
    letI : NormedField (Q F a) := qNormedField F a ha
    IsUltrametricDist (Q F a) := by
  letI : Field (Q F a) := qField F a ha
  letI : NontriviallyNormedField F := baseNormedField F
  letI : Algebra.IsAlgebraic F (Q F a) := Algebra.IsIntegral.isAlgebraic
  letI : NormedField (Q F a) := qNormedField F a ha
  refine ⟨?_⟩
  intro x y z
  change spectralNorm F (Q F a) (x - z) ≤
    max (spectralNorm F (Q F a) (x - y))
      (spectralNorm F (Q F a) (y - z))
  rw [← sub_add_sub_cancel x y z]
  exact isNonarchimedean_spectralNorm (x - y) (y - z)

@[implicit_reducible] private noncomputable def qValuativeRel
    (a : Fˣ) (ha : ¬ IsSquare (a : F)) :
    ValuativeRel (Q F a) := by
  letI : Field (Q F a) := qField F a ha
  letI : NormedField (Q F a) := qNormedField F a ha
  letI : IsUltrametricDist (Q F a) := qIsUltrametric F a ha
  exact ValuativeRel.ofValuation (NormedField.valuation (K := Q F a))

private theorem qIsValuativeTopology (a : Fˣ) (ha : ¬ IsSquare (a : F)) :
    letI : Field (Q F a) := qField F a ha
    letI : TopologicalSpace (Q F a) := qTopology F a ha
    letI : ValuativeRel (Q F a) := qValuativeRel F a ha
    IsValuativeTopology (Q F a) := by
  letI : Field (Q F a) := qField F a ha
  letI : NormedField (Q F a) := qNormedField F a ha
  letI : IsUltrametricDist (Q F a) := qIsUltrametric F a ha
  letI : TopologicalSpace (Q F a) := qTopology F a ha
  letI : ValuativeRel (Q F a) := qValuativeRel F a ha
  letI : Valued (Q F a) NNReal := NormedField.toValued
  letI : (NormedField.valuation (K := Q F a)).Compatible :=
    Valuation.Compatible.ofValuation _
  exact IsValuativeTopology.of_mem_nhds_zero_iff_vle
    (NormedField.valuation (K := Q F a))
    Valued.mem_nhds_zero

private theorem qLocalField (a : Fˣ) (ha : ¬ IsSquare (a : F)) :
    letI : Field (Q F a) := qField F a ha
    letI : TopologicalSpace (Q F a) := qTopology F a ha
    letI : ValuativeRel (Q F a) := qValuativeRel F a ha
    IsNonarchimedeanLocalField (Q F a) := by
  letI : Field (Q F a) := qField F a ha
  letI : NontriviallyNormedField F := baseNormedField F
  letI : Algebra.IsAlgebraic F (Q F a) := Algebra.IsIntegral.isAlgebraic
  letI : NormedField (Q F a) := qNormedField F a ha
  letI : IsUltrametricDist (Q F a) := qIsUltrametric F a ha
  letI : NontriviallyNormedField (Q F a) :=
    spectralNorm.nontriviallyNormedField F (Q F a)
  letI : TopologicalSpace (Q F a) := qTopology F a ha
  letI : ValuativeRel (Q F a) := qValuativeRel F a ha
  letI : IsValuativeTopology (Q F a) := qIsValuativeTopology F a ha
  letI : NormedSpace F (Q F a) := spectralNorm.normedSpace F (Q F a)
  letI : NormedAlgebra F (Q F a) := spectralNorm.normedAlgebra F (Q F a)
  letI : LocallyCompactSpace (Q F a) :=
    LocallyCompactSpace.of_finiteDimensional_of_complete F (Q F a)
  letI : (NormedField.valuation (K := Q F a)).Compatible :=
    Valuation.Compatible.ofValuation _
  have hnontrivial : ValuativeRel.IsNontrivial (Q F a) := by
    exact (ValuativeRel.isNontrivial_iff_isNontrivial
      (NormedField.valuation (K := Q F a))).2 (by infer_instance)
  exact
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := hnontrivial }

private theorem qValuativeExtension (a : Fˣ) (ha : ¬ IsSquare (a : F)) :
    letI : Field (Q F a) := qField F a ha
    letI : TopologicalSpace (Q F a) := qTopology F a ha
    letI : ValuativeRel (Q F a) := qValuativeRel F a ha
    ValuativeExtension F (Q F a) := by
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  letI : Valued F (ValuativeRel.ValueGroupWithZero F) := inferInstance
  letI : (Valued.v : Valuation F (ValuativeRel.ValueGroupWithZero F)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := F).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField F := baseNormedField F
  letI : Field (Q F a) := qField F a ha
  letI : Algebra.IsAlgebraic F (Q F a) := Algebra.IsIntegral.isAlgebraic
  letI : NormedField (Q F a) := qNormedField F a ha
  letI : IsUltrametricDist (Q F a) := qIsUltrametric F a ha
  letI : TopologicalSpace (Q F a) := qTopology F a ha
  letI : ValuativeRel (Q F a) := qValuativeRel F a ha
  refine ⟨fun x y ↦ ?_⟩
  change ‖algebraMap F (Q F a) x‖₊ ≤ ‖algebraMap F (Q F a) y‖₊ ↔ x ≤ᵥ y
  rw [← NNReal.coe_le_coe]
  change spectralNorm F (Q F a) (algebraMap F (Q F a) x) ≤
      spectralNorm F (Q F a) (algebraMap F (Q F a) y) ↔ x ≤ᵥ y
  rw [spectralNorm_extends, spectralNorm_extends]
  rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F)]
  exact Valued.toNormedField.norm_le_iff

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem qSeparable (hchar : ringChar F ≠ 2)
    (a : Fˣ) (ha : ¬ IsSquare (a : F)) :
    letI : Field (Q F a) := qField F a ha
    Algebra.IsSeparable F (Q F a) := by
  letI : Field (Q F a) := qField F a ha
  let i : Q F a := ⟨0, 1⟩
  have htwo : (2 : F) ≠ 0 := by
    intro h
    apply Ring.neg_one_ne_one_of_char_ne_two hchar
    linear_combination -h
  have hpoly : (X ^ 2 - C (a : F)).Separable :=
    Polynomial.separable_X_pow_sub_C (a : F) htwo a.ne_zero
  have hiroot : Polynomial.aeval i (X ^ 2 - C (a : F)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C]
    ext <;> simp [pow_two, i]
  have hi : IsSeparable F i :=
    Polynomial.Separable.of_dvd hpoly (minpoly.dvd F i hiroot)
  refine ⟨fun z ↦ ?_⟩
  have hre : IsSeparable F (algebraMap F (Q F a) z.re) :=
    isSeparable_algebraMap z.re
  have him : IsSeparable F (algebraMap F (Q F a) z.im * i) :=
    Field.isSeparable_mul (isSeparable_algebraMap z.im) hi
  have hz : z = algebraMap F (Q F a) z.re +
      algebraMap F (Q F a) z.im * i := by
    ext <;> simp [i]
  rw [hz]
  exact Field.isSeparable_add hre him

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem qQuadraticExtension (a : Fˣ) (ha : ¬ IsSquare (a : F)) :
    letI : Field (Q F a) := qField F a ha
    Algebra.IsQuadraticExtension F (Q F a) := by
  letI : Field (Q F a) := qField F a ha
  exact ⟨QuadraticAlgebra.finrank_eq_two (a : F) 0⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem qPrimeCyclic (hchar : ringChar F ≠ 2)
    (a : Fˣ) (ha : ¬ IsSquare (a : F)) :
    letI : Field (Q F a) := qField F a ha
    PrimeCyclicExtension F (Q F a) := by
  letI : Field (Q F a) := qField F a ha
  letI : Algebra.IsQuadraticExtension F (Q F a) := qQuadraticExtension F a ha
  letI : Algebra.IsSeparable F (Q F a) := qSeparable F hchar a ha
  apply PrimeCyclicExtension.ofCyclicPrimeExtension
  exact ⟨inferInstance, inferInstance,
    QuadraticAlgebra.finrank_eq_two (a : F) 0 ▸ Nat.prime_two⟩

private theorem qNormQuotient_card (hchar : ringChar F ≠ 2)
    (a : Fˣ) (ha : ¬ IsSquare (a : F)) :
    letI : Field (Q F a) := qField F a ha
    letI : TopologicalSpace (Q F a) := qTopology F a ha
    letI : ValuativeRel (Q F a) := qValuativeRel F a ha
    Nat.card (NormQuotient F (Q F a)) = 2 := by
  letI : Field (Q F a) := qField F a ha
  letI : TopologicalSpace (Q F a) := qTopology F a ha
  letI : ValuativeRel (Q F a) := qValuativeRel F a ha
  letI : IsNonarchimedeanLocalField (Q F a) := qLocalField F a ha
  letI : ValuativeExtension F (Q F a) := qValuativeExtension F a ha
  letI : PrimeCyclicExtension F (Q F a) := qPrimeCyclic F hchar a ha
  by_cases hunr : ramificationIndex F (Q F a) = 1
  · simpa [QuadraticAlgebra.finrank_eq_two] using
      unramifiedNormQuotient_card F (Q F a) hunr
  · let P := primeCyclicPreparation F (Q F a) hunr
    simpa [QuadraticAlgebra.finrank_eq_two] using
      normQuotient_card F (Q F a) P.ht P.hres P.piK P.hpiK P.hgen

private theorem qNormCharacter_card (hchar : ringChar F ≠ 2)
    (a : Fˣ) (ha : ¬ IsSquare (a : F)) :
    letI : Field (Q F a) := qField F a ha
    letI : TopologicalSpace (Q F a) := qTopology F a ha
    letI : ValuativeRel (Q F a) := qValuativeRel F a ha
    letI : IsNonarchimedeanLocalField (Q F a) := qLocalField F a ha
    letI : ValuativeExtension F (Q F a) := qValuativeExtension F a ha
    Nat.card (NormCharacter F (Q F a)) = 2 := by
  letI : Field (Q F a) := qField F a ha
  letI : TopologicalSpace (Q F a) := qTopology F a ha
  letI : ValuativeRel (Q F a) := qValuativeRel F a ha
  letI : IsNonarchimedeanLocalField (Q F a) := qLocalField F a ha
  letI : ValuativeExtension F (Q F a) := qValuativeExtension F a ha
  letI : PrimeCyclicExtension F (Q F a) := qPrimeCyclic F hchar a ha
  by_cases hunr : ramificationIndex F (Q F a) = 1
  · simpa [QuadraticAlgebra.finrank_eq_two] using
      unramifiedNormCharacter_card F (Q F a) hunr
  · let P := primeCyclicPreparation F (Q F a) hunr
    simpa [QuadraticAlgebra.finrank_eq_two] using
      ramifiedNormCharacter_card F (Q F a) P.ht P.hres P.piK P.hpiK P.hgen

private theorem qNormCharacter_existsUnique (hchar : ringChar F ≠ 2)
    (a : Fˣ) (ha : ¬ IsSquare (a : F)) :
    letI : Field (Q F a) := qField F a ha
    letI : TopologicalSpace (Q F a) := qTopology F a ha
    letI : ValuativeRel (Q F a) := qValuativeRel F a ha
    letI : IsNonarchimedeanLocalField (Q F a) := qLocalField F a ha
    letI : ValuativeExtension F (Q F a) := qValuativeExtension F a ha
    ∃! μ : NormCharacter F (Q F a), μ ≠ 1 := by
  letI : Field (Q F a) := qField F a ha
  letI : TopologicalSpace (Q F a) := qTopology F a ha
  letI : ValuativeRel (Q F a) := qValuativeRel F a ha
  letI : IsNonarchimedeanLocalField (Q F a) := qLocalField F a ha
  letI : ValuativeExtension F (Q F a) := qValuativeExtension F a ha
  exact (Nat.card_eq_two_iff' (1 : NormCharacter F (Q F a))).mp
    (qNormCharacter_card F hchar a ha)

private noncomputable def qNormCharacter (hchar : ringChar F ≠ 2)
    (a : Fˣ) (ha : ¬ IsSquare (a : F)) :
    letI : Field (Q F a) := qField F a ha
    letI : TopologicalSpace (Q F a) := qTopology F a ha
    letI : ValuativeRel (Q F a) := qValuativeRel F a ha
    letI : IsNonarchimedeanLocalField (Q F a) := qLocalField F a ha
    letI : ValuativeExtension F (Q F a) := qValuativeExtension F a ha
    NormCharacter F (Q F a) := by
  letI : Field (Q F a) := qField F a ha
  letI : TopologicalSpace (Q F a) := qTopology F a ha
  letI : ValuativeRel (Q F a) := qValuativeRel F a ha
  letI : IsNonarchimedeanLocalField (Q F a) := qLocalField F a ha
  letI : ValuativeExtension F (Q F a) := qValuativeExtension F a ha
  exact (qNormCharacter_existsUnique F hchar a ha).choose

private theorem qNormCharacter_ne_one (hchar : ringChar F ≠ 2)
    (a : Fˣ) (ha : ¬ IsSquare (a : F)) :
    letI : Field (Q F a) := qField F a ha
    letI : TopologicalSpace (Q F a) := qTopology F a ha
    letI : ValuativeRel (Q F a) := qValuativeRel F a ha
    letI : IsNonarchimedeanLocalField (Q F a) := qLocalField F a ha
    letI : ValuativeExtension F (Q F a) := qValuativeExtension F a ha
    qNormCharacter F hchar a ha ≠ 1 := by
  letI : Field (Q F a) := qField F a ha
  letI : TopologicalSpace (Q F a) := qTopology F a ha
  letI : ValuativeRel (Q F a) := qValuativeRel F a ha
  letI : IsNonarchimedeanLocalField (Q F a) := qLocalField F a ha
  letI : ValuativeExtension F (Q F a) := qValuativeExtension F a ha
  exact (qNormCharacter_existsUnique F hchar a ha).choose_spec.1

private theorem qNormCharacter_eq_one_iff (hchar : ringChar F ≠ 2)
    (a b : Fˣ) (ha : ¬ IsSquare (a : F)) :
    letI : Field (Q F a) := qField F a ha
    letI : TopologicalSpace (Q F a) := qTopology F a ha
    letI : ValuativeRel (Q F a) := qValuativeRel F a ha
    letI : IsNonarchimedeanLocalField (Q F a) := qLocalField F a ha
    letI : ValuativeExtension F (Q F a) := qValuativeExtension F a ha
    (qNormCharacter F hchar a ha).1 b = 1 ↔
      b ∈ (normUnits F (Q F a)).range := by
  letI : Field (Q F a) := qField F a ha
  letI : TopologicalSpace (Q F a) := qTopology F a ha
  letI : ValuativeRel (Q F a) := qValuativeRel F a ha
  letI : IsNonarchimedeanLocalField (Q F a) := qLocalField F a ha
  letI : ValuativeExtension F (Q F a) := qValuativeExtension F a ha
  let μ := qNormCharacter F hchar a ha
  constructor
  · intro hμb
    by_contra hb
    have hμco : μ.1 ≠ 1 := by
      intro h
      exact qNormCharacter_ne_one F hchar a ha (NormCharacter.ext h)
    obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hμco
    have hx1 : μ.1 x ≠ 1 := by simpa using hx
    have hqx : (QuotientGroup.mk x : NormQuotient F (Q F a)) ≠ 1 := by
      intro hqx
      exact hx1 (μ.eq_one_on_normRange F (Q F a) x
        ((QuotientGroup.eq_one_iff _).mp hqx))
    have hqb : (QuotientGroup.mk b : NormQuotient F (Q F a)) ≠ 1 := by
      intro hqb
      exact hb ((QuotientGroup.eq_one_iff _).mp hqb)
    have huniq := (Nat.card_eq_two_iff'
      (1 : NormQuotient F (Q F a))).mp (qNormQuotient_card F hchar a ha)
    have heq : (QuotientGroup.mk b : NormQuotient F (Q F a)) =
        QuotientGroup.mk x :=
      huniq.unique hqb hqx
    have hvalues : μ.1 b = μ.1 x := by
      change μ.toQuotientCharacter F (Q F a) (QuotientGroup.mk b) =
        μ.toQuotientCharacter F (Q F a) (QuotientGroup.mk x)
      rw [heq]
    exact hx1 (hvalues.symm.trans hμb)
  · exact μ.eq_one_on_normRange F (Q F a) b

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem qAlgebraNorm (a : Fˣ) (ha : ¬ IsSquare (a : F))
    (z : Q F a) :
    letI : Field (Q F a) := qField F a ha
    Algebra.norm F z = z.re ^ 2 - (a : F) * z.im ^ 2 := by
  letI : Field (Q F a) := qField F a ha
  rw [Algebra.norm_apply]
  change (DistribSMul.toLinearMap F (Q F a) z).det = _
  rw [QuadraticAlgebra.det_toLinearMap_eq_norm]
  simp only [QuadraticAlgebra.norm_def, zero_mul, add_zero, pow_two]
  ring

/-- The projective conic used to characterize the quadratic norm symbol. -/
def QuadraticConicSolvable (a b : Fˣ) : Prop :=
  ∃ x y z : F, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
    x ^ 2 = (a : F) * y ^ 2 + (b : F) * z ^ 2

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem qNormRange_iff_conic (a b : Fˣ)
    (ha : ¬ IsSquare (a : F)) :
    letI : Field (Q F a) := qField F a ha
    b ∈ (normUnits F (Q F a)).range ↔ QuadraticConicSolvable F a b := by
  letI : Field (Q F a) := qField F a ha
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨w.val.re, w.val.im, 1, Or.inr (Or.inr one_ne_zero), ?_⟩
    change w.val.re ^ 2 = (a : F) * w.val.im ^ 2 +
      Algebra.norm F (w : Q F a) * 1 ^ 2
    rw [qAlgebraNorm F a ha]
    ring
  · rintro ⟨x, y, z, hnonzero, hconic⟩
    have hz : z ≠ 0 := by
      intro hz
      subst z
      simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hconic
      by_cases hy : y = 0
      · subst y
        have hx : x = 0 := by
          simpa using hconic
        rcases hnonzero with hx' | hy' | hz'
        · exact hx' hx
        · exact hy' rfl
        · exact hz' rfl
      · apply ha
        refine ⟨x / y, ?_⟩
        rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hy hy)]
        calc
          (a : F) * (y * y) = (a : F) * y ^ 2 := by ring
          _ = x ^ 2 := hconic.symm
          _ = x * x := by ring
    let w : Q F a := ⟨x / z, y / z⟩
    have hnorm : Algebra.norm F w = (b : F) := by
      rw [qAlgebraNorm F a ha]
      dsimp [w]
      field_simp [hz]
      linear_combination hconic
    have hw : w ≠ 0 := by
      intro hw
      have hbzero : (b : F) = 0 := by
        rw [← hnorm, qAlgebraNorm F a ha, hw]
        simp
      exact b.ne_zero hbzero
    refine ⟨Units.mk0 w hw, Units.ext ?_⟩
    exact hnorm

/-- The quadratic norm character associated to a unit square class.  On a
square parameter it is trivial; otherwise it is the unique nontrivial
character trivial on norms from the actual Kummer quadratic extension. -/
noncomputable def quadraticNormCharacter (hchar : ringChar F ≠ 2)
    (a : Fˣ) : ContinuousQuasiChar F := by
  classical
  exact if ha : IsSquare (a : F) then 1 else
      letI : Field (Q F a) := qField F a ha
      letI : TopologicalSpace (Q F a) := qTopology F a ha
      letI : ValuativeRel (Q F a) := qValuativeRel F a ha
      letI : IsNonarchimedeanLocalField (Q F a) := qLocalField F a ha
      letI : ValuativeExtension F (Q F a) := qValuativeExtension F a ha
      (qNormCharacter F hchar a ha).1

theorem quadraticNormCharacter_of_isSquare (hchar : ringChar F ≠ 2)
    (a : Fˣ) (ha : IsSquare (a : F)) :
    quadraticNormCharacter F hchar a = 1 := by
  simp [quadraticNormCharacter, ha]

private theorem quadraticNormCharacter_of_not_isSquare
    (hchar : ringChar F ≠ 2) (a : Fˣ) (ha : ¬ IsSquare (a : F)) :
    quadraticNormCharacter F hchar a =
      letI : Field (Q F a) := qField F a ha
      letI : TopologicalSpace (Q F a) := qTopology F a ha
      letI : ValuativeRel (Q F a) := qValuativeRel F a ha
      letI : IsNonarchimedeanLocalField (Q F a) := qLocalField F a ha
      letI : ValuativeExtension F (Q F a) := qValuativeExtension F a ha
      (qNormCharacter F hchar a ha).1 := by
  simp [quadraticNormCharacter, ha]

theorem quadraticNormCharacter_eq_one_iff_isSquare
    (hchar : ringChar F ≠ 2) (a : Fˣ) :
    quadraticNormCharacter F hchar a = 1 ↔ IsSquare (a : F) := by
  by_cases ha : IsSquare (a : F)
  · simp [ha, quadraticNormCharacter_of_isSquare F hchar a]
  · simp only [ha, iff_false]
    rw [quadraticNormCharacter_of_not_isSquare F hchar a ha]
    letI : Field (Q F a) := qField F a ha
    letI : TopologicalSpace (Q F a) := qTopology F a ha
    letI : ValuativeRel (Q F a) := qValuativeRel F a ha
    letI : IsNonarchimedeanLocalField (Q F a) := qLocalField F a ha
    letI : ValuativeExtension F (Q F a) := qValuativeExtension F a ha
    intro h
    exact qNormCharacter_ne_one F hchar a ha (NormCharacter.ext h)

theorem quadraticNormCharacter_eq_one_iff_conic
    (hchar : ringChar F ≠ 2) (a b : Fˣ) :
    quadraticNormCharacter F hchar a b = 1 ↔
      QuadraticConicSolvable F a b := by
  by_cases ha : IsSquare (a : F)
  · have ha' := ha
    obtain ⟨r, hr⟩ := ha'
    have hr0 : r ≠ 0 := by
      intro hr0
      subst r
      simp at hr
    rw [quadraticNormCharacter_of_isSquare F hchar a ha]
    simp only [ContinuousQuasiChar.one_apply, true_iff]
    refine ⟨r, 1, 0, Or.inl hr0, ?_⟩
    simp [hr, pow_two]
  · rw [quadraticNormCharacter_of_not_isSquare F hchar a ha]
    letI : Field (Q F a) := qField F a ha
    letI : TopologicalSpace (Q F a) := qTopology F a ha
    letI : ValuativeRel (Q F a) := qValuativeRel F a ha
    letI : IsNonarchimedeanLocalField (Q F a) := qLocalField F a ha
    letI : ValuativeExtension F (Q F a) := qValuativeExtension F a ha
    rw [qNormCharacter_eq_one_iff F hchar a b ha,
      qNormRange_iff_conic F a b ha]

theorem quadraticNormCharacter_sq (hchar : ringChar F ≠ 2) (a : Fˣ) :
    quadraticNormCharacter F hchar a ^ 2 = 1 := by
  by_cases ha : IsSquare (a : F)
  · rw [quadraticNormCharacter_of_isSquare F hchar a ha]
    exact one_pow (M := ContinuousQuasiChar F) 2
  · rw [quadraticNormCharacter_of_not_isSquare F hchar a ha]
    letI : Field (Q F a) := qField F a ha
    letI : TopologicalSpace (Q F a) := qTopology F a ha
    letI : ValuativeRel (Q F a) := qValuativeRel F a ha
    letI : IsNonarchimedeanLocalField (Q F a) := qLocalField F a ha
    letI : ValuativeExtension F (Q F a) := qValuativeExtension F a ha
    have hpow : qNormCharacter F hchar a ha ^ 2 = 1 := by
      have h := pow_card_eq_one' (x := qNormCharacter F hchar a ha)
      simpa [qNormCharacter_card F hchar a ha] using h
    exact congrArg Subtype.val hpow

/-- The quadratic norm symbol `(a,b)` obtained from the actual quadratic
norm character attached to `a`. -/
noncomputable def quadraticNormSymbol (hchar : ringChar F ≠ 2)
    (a b : Fˣ) : ℂˣ := quadraticNormCharacter F hchar a b

theorem quadraticNormSymbol_sq (hchar : ringChar F ≠ 2) (a b : Fˣ) :
    quadraticNormSymbol F hchar a b ^ 2 = 1 := by
  have h := congrArg (fun χ : ContinuousQuasiChar F ↦ χ b)
    (quadraticNormCharacter_sq F hchar a)
  simpa [quadraticNormSymbol] using h

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem quadraticConicSolvable_comm (a b : Fˣ) :
    QuadraticConicSolvable F a b ↔ QuadraticConicSolvable F b a := by
  constructor
  · rintro ⟨x, y, z, hnonzero, hconic⟩
    refine ⟨x, z, y, ?_, ?_⟩
    · rcases hnonzero with hx | hy | hz
      · exact Or.inl hx
      · exact Or.inr (Or.inr hy)
      · exact Or.inr (Or.inl hz)
    · simpa [add_comm] using hconic
  · rintro ⟨x, y, z, hnonzero, hconic⟩
    refine ⟨x, z, y, ?_, ?_⟩
    · rcases hnonzero with hx | hy | hz
      · exact Or.inl hx
      · exact Or.inr (Or.inr hy)
      · exact Or.inr (Or.inl hz)
    · simpa [add_comm] using hconic

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
      (sq_eq_one_iff.mp huval).resolve_left (fun h ↦ huone (Units.ext h))
    have hvminus : (v : ℂ) = -1 :=
      (sq_eq_one_iff.mp hvval).resolve_left (fun h ↦ hvone (Units.ext h))
    exact Units.ext (huminus.trans hvminus.symm)

theorem quadraticNormSymbol_symmetric (hchar : ringChar F ≠ 2)
    (a b : Fˣ) :
    quadraticNormSymbol F hchar a b = quadraticNormSymbol F hchar b a := by
  apply complexUnits_eq_of_sq_eq_one
  · exact quadraticNormSymbol_sq F hchar a b
  · exact quadraticNormSymbol_sq F hchar b a
  · simp only [quadraticNormSymbol,
      quadraticNormCharacter_eq_one_iff_conic F hchar]
    exact quadraticConicSolvable_comm F a b

theorem quadraticNormCharacter_mul (hchar : ringChar F ≠ 2)
    (a b : Fˣ) :
    quadraticNormCharacter F hchar (a * b) =
      quadraticNormCharacter F hchar a * quadraticNormCharacter F hchar b := by
  apply ContinuousMonoidHom.ext
  intro c
  change quadraticNormSymbol F hchar (a * b) c =
    quadraticNormSymbol F hchar a c * quadraticNormSymbol F hchar b c
  calc
    quadraticNormSymbol F hchar (a * b) c =
        quadraticNormSymbol F hchar c (a * b) :=
      quadraticNormSymbol_symmetric F hchar (a * b) c
    _ = quadraticNormSymbol F hchar c a *
        quadraticNormSymbol F hchar c b := by
      exact map_mul (quadraticNormCharacter F hchar c) a b
    _ = quadraticNormSymbol F hchar a c *
        quadraticNormSymbol F hchar b c := by
      rw [quadraticNormSymbol_symmetric F hchar c a,
        quadraticNormSymbol_symmetric F hchar c b]

/-- The parameter-to-character map.  Multiplicativity is proved from the
conic symmetry of the actual norm symbol. -/
noncomputable def quadraticNormCharacterHom (hchar : ringChar F ≠ 2) :
    Fˣ →* ContinuousQuasiChar F where
  toFun := quadraticNormCharacter F hchar
  map_one' := by
    apply quadraticNormCharacter_of_isSquare F hchar
    exact ⟨1, by simp⟩
  map_mul' := quadraticNormCharacter_mul F hchar

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem isSquare_coe_unit_iff_isSquare (a : Fˣ) :
    IsSquare (a : F) ↔ IsSquare a := by
  constructor
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      intro hr0
      subst r
      simp at hr
    refine ⟨Units.mk0 r hr0, Units.ext ?_⟩
    exact hr
  · rintro ⟨u, hu⟩
    refine ⟨(u : F), ?_⟩
    exact congrArg Units.val hu

/-- Square classes of `F` as the quotient of `Fˣ` by its subgroup of
squares. -/
abbrev QuadraticSquareClass := Fˣ ⧸ Subgroup.square Fˣ

private theorem square_le_quadraticNormCharacterHom_ker
    (hchar : ringChar F ≠ 2) :
    Subgroup.square Fˣ ≤ (quadraticNormCharacterHom F hchar).ker := by
  intro a ha
  change quadraticNormCharacter F hchar a = 1
  exact (quadraticNormCharacter_eq_one_iff_isSquare F hchar a).2
    ((isSquare_coe_unit_iff_isSquare F a).2
      (Subgroup.mem_square.mp ha))

/-- The quadratic norm-character homomorphism descended to square classes. -/
noncomputable def squareClassToQuadraticCharacter
    (hchar : ringChar F ≠ 2) :
    QuadraticSquareClass F →* ContinuousQuasiChar F :=
  QuotientGroup.lift (Subgroup.square Fˣ)
    (quadraticNormCharacterHom F hchar)
    (square_le_quadraticNormCharacterHom_ker F hchar)

/-- In residue characteristic different from two, distinct square classes
give distinct quadratic norm characters. -/
theorem squareClassToQuadraticCharacter_injective
    (hchar : ringChar F ≠ 2) :
    Function.Injective (squareClassToQuadraticCharacter F hchar) := by
  apply (QuotientGroup.injective_lift_iff
    (Subgroup.square Fˣ) (quadraticNormCharacterHom F hchar)
    (square_le_quadraticNormCharacterHom_ker F hchar)).2
  ext a
  change IsSquare a ↔ quadraticNormCharacter F hchar a = 1
  rw [← isSquare_coe_unit_iff_isSquare F a,
    quadraticNormCharacter_eq_one_iff_isSquare F hchar a]

/-- The characteristic-not-two quadratic norm-character result: the actual
Kummer norm characters form an injective homomorphism from square classes. -/
theorem quadraticNormCharacters_char_ne_two
    (hchar : ringChar F ≠ 2) :
    Function.Injective (squareClassToQuadraticCharacter F hchar) :=
  squareClassToQuadraticCharacter_injective F hchar

end

end LanglandsSecondMainLemma.Characters
