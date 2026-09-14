import LanglandsFirstMainLemma.Basic.CharacterConductorExistence
import LanglandsFirstMainLemma.Basic.CharacterConductors
import LanglandsFirstMainLemma.Basic.CharacterTypes
import LanglandsFirstMainLemma.Basic.StandardCharacterBridge
import LanglandsFirstMainLemma.Delta.Elementary
import LanglandsFirstMainLemma.Delta.LocalConstantRealization
import LanglandsSecondMainLemma.Basic.Characters
import LanglandsSecondMainLemma.Basic.LocalConstants

/-!
# Basic / Second Main Statement

This file gives the exact public interface for Theorem `U:main` in the
corrected manuscript.  The extension is an actual finite Galois extension
whose Galois group is `C_ℓ × C_ℓ`.  A compatible family supplies an inducing
character on every actual degree-`ℓ` intermediate field, all with the same
primitive invariant pullback to the top field.

The induction expression uses only
`LanglandsFirstMainLemma.localConstant`, FML's canonical local constant.  Its
lower product is indexed by the complete type `NormCharacter F L`, so the
trivial norm character is present.  No unitary hypothesis, characteristic
hypothesis, stationary model, denominator, representative, or branch datum
is part of this interface.

Blueprint: `blueprint/tasks/Basic/SecondMainStatement.md`.
Paper: lines 121--155 and 277--337, especially Theorem `U:main`.
-/

namespace LanglandsSecondMainLemma.Basic

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

/-! ## The actual prime-square extension -/

/-- The algebraic datum that the actual finite extension `K/F` has Galois
group `C_ℓ × C_ℓ`, for a prime `ℓ`.

The ambient `Algebra`, `Module.Free`, and `Module.Finite` instances are the
genuine field extension.  Galoisness and the displayed group equivalence are
properties of that same extension; no abstract replacement group is used.
`Nonempty` records the condition without choosing a preferred labelling of
the two cyclic factors. -/
structure PrimeSquareExtension
    (F K : Type) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K] (ℓ : ℕ) : Prop where
  prime : ℓ.Prime
  isGalois : IsGalois F K
  galoisGroupEquiv : Nonempty
    (Gal(K/F) ≃* (Multiplicative (ZMod ℓ) × Multiplicative (ZMod ℓ)))

/-! ## Compatible primitive characters -/

section Characters

variable (F K : Type)
variable [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
variable {ℓ : ℕ}

/-- The actual character family in Theorem `U:main`.

`topCharacter` is the manuscript's `Θ`.  It is invariant under the actual
group `Gal(K/F)` and is not a norm pullback from `F`.  For every actual
intermediate subfield `L` of degree `ℓ` over `F`, `inducingCharacter L hL`
is a continuous group homomorphism `Lˣ → ℂˣ`, and `compatible` is precisely

`θ_L ∘ N_{K/L} = Θ`.

The valuation relation and topology on `L` are the accepted restrictions
constructed in `Basic.IntermediateValuation` and
`Basic.IntermediateCompleteness`.  This structure requires a supplied
family; it deliberately makes no assertion that such a family exists. -/
structure PrimitiveCompatibleFamily
    (extension : PrimeSquareExtension F K ℓ) where
  topCharacter : ContinuousQuasiChar K
  invariant : ∀ σ : Gal(K/F),
    conjugateQuasiChar F K σ topCharacter = topCharacter
  not_normPullback :
    ¬ ∃ χF : ContinuousQuasiChar F,
      normQuasiChar F K χF = topCharacter
  inducingCharacter : ∀ (L : IntermediateField F K),
    Module.finrank F L = ℓ →
      letI := intermediateFieldValuativeRel L
      letI := intermediateFieldTopology L
      ContinuousQuasiChar L
  compatible : ∀ (L : IntermediateField F K)
      (hL : Module.finrank F L = ℓ),
    letI := intermediateFieldValuativeRel L
    letI := intermediateFieldTopology L
    letI : IsNonarchimedeanLocalField L := intermediateField_localField L
    letI : ValuativeExtension L K :=
      intermediateField_upperValuativeExtension L
    normQuasiChar L K (inducingCharacter L hL) = topCharacter

end Characters

/-! ## The complete induction expression -/

section InductionExpression

variable (F K : Type)
variable [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
variable {ℓ : ℕ}

/-- The complete normalized induction expression

`A_L(θ_L) = Δ_L(θ_L, ψ_F ∘ Tr_{L/F})
              * ∏_{ν ∈ S(L/F)} Δ_F(ν, ψ_F)`.

Both `Δ` factors are definitionally FML's canonical `localConstant`.  The
finite product ranges over the entire subtype `NormCharacter F L`; in
particular it includes its identity element.  The instances needed for the
actual intermediate local field and the finiteness of its norm-character
group are derived from `extension`, not assumed as auxiliary input. -/
def inductionExpression
    (extension : PrimeSquareExtension F K ℓ)
    (family : PrimitiveCompatibleFamily F K extension)
    (ψF : ContinuousAddChar F)
    (L : IntermediateField F K) (hL : Module.finrank F L = ℓ) : ℂ := by
  letI := intermediateFieldValuativeRel L
  letI := intermediateFieldTopology L
  letI : IsGalois F K := extension.isGalois
  obtain ⟨hLocal, hFreeFL, hFiniteFL, hFreeLK, hFiniteLK, hScalar,
      hValFL, hValLK, _hTotalDegree, _hLowerDegree, _hUpperDegree,
      hCyclicFL, _hCyclicLK⟩ :=
    intermediateField_tower_compatible extension.prime
      extension.galoisGroupEquiv L hL
  letI : IsNonarchimedeanLocalField L := hLocal
  letI : Module.Free F L := hFreeFL
  letI : Module.Finite F L := hFiniteFL
  letI : Module.Free L K := hFreeLK
  letI : Module.Finite L K := hFiniteLK
  letI : IsScalarTower F L K := hScalar
  letI : ValuativeExtension F L := hValFL
  letI : ValuativeExtension L K := hValLK
  letI : PrimeCyclicExtension F L :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F L hCyclicFL
  letI : Finite (NormCharacter F L) :=
    primeCyclicNormCharacter_finite F L
  letI := Fintype.ofFinite (NormCharacter F L)
  exact
    LanglandsFirstMainLemma.localConstant L
        (family.inducingCharacter L hL)
        (tracePullbackAddChar F L ψF) *
      ∏ ν : NormCharacter F L,
        LanglandsFirstMainLemma.localConstant F ν.1 ψF

/-! ## The Second Main identity -/

/-- The proposition asserted by Theorem `U:main` for a fixed nontrivial
continuous additive character.

It compares every pair of actual degree-`ℓ` intermediate fields.  Thus it is
the family formulation of independence of `L`; no distinguished pair and no
conclusion-equivalent comparison hypothesis occurs in the statement. -/
def SecondMainIdentity
    (extension : PrimeSquareExtension F K ℓ)
    (family : PrimitiveCompatibleFamily F K extension)
    (ψF : ContinuousAddChar F) (_hψF : ψF ≠ 1) : Prop :=
  ∀ (L₁ L₂ : IntermediateField F K)
    (hL₁ : Module.finrank F L₁ = ℓ)
    (hL₂ : Module.finrank F L₂ = ℓ),
      inductionExpression F K extension family ψF L₁ hL₁ =
        inductionExpression F K extension family ψF L₂ hL₂

end InductionExpression

end

end LanglandsSecondMainLemma.Basic
