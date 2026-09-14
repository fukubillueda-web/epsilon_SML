import LanglandsFirstMainLemma.Basic.CharacterConductorExistence
import LanglandsFirstMainLemma.Basic.CharacterConductors
import LanglandsFirstMainLemma.Basic.CharacterTypes
import LanglandsFirstMainLemma.Basic.StandardCharacterBridge
import LanglandsSecondMainLemma.Basic.Fields
import LanglandsSecondMainLemma.Basic.NormTrace

/-!
# Basic / Characters

Blueprint: `blueprint/tasks/Basic/Characters.md`.
Paper: setup lines 121–155 and 277–337, especially the definition of
`S(L/F)` in lines 133–136 and the norm/trace pullbacks in lines 317–324.

This file identifies FML's `NormCharacter` with the manuscript's literal
continuous-group-homomorphism condition on the actual field norm.  It also
records that FML's canonical exact-conductor packages do not alter the
characters obtained by the norm and trace pullbacks.

The additive nontriviality needed by the canonical package over the upper
field is proved from surjectivity of trace in a separable extension; it is
not added as a compatibility hypothesis.
-/

namespace LanglandsSecondMainLemma.Basic

noncomputable section

open LanglandsFirstMainLemma

section NormCharacters

variable (F K : Type*)
variable [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]

/-- FML's `NormCharacter F K` is exactly the manuscript's `S(K/F)`:
continuous group homomorphisms `Fˣ → ℂˣ` which are trivial on every
value of the actual field norm `N_{K/F}`.

The right-hand side retains the `ContinuousMonoidHom` object itself.  Since
both its source and target are groups, this is a continuous *group*
homomorphism, rather than an arbitrary continuous function. -/
theorem normCharacter_eq_continuousHom :
    NormCharacter F K =
      { μ : ContinuousMonoidHom Fˣ ℂˣ //
        ∀ x : Kˣ, μ (Units.map (Algebra.norm F) x) = 1 } := by
  unfold NormCharacter
  congr 1
  funext μ
  apply propext
  constructor
  · intro h x
    have hx := DFunLike.congr_fun h x
    rw [normQuasiChar_apply, ContinuousQuasiChar.one_apply] at hx
    rw [show continuousNormUnits F K x =
      Units.map (Algebra.norm F) x from rfl] at hx
    exact hx
  · intro h
    apply ContinuousMonoidHom.ext
    intro x
    rw [normQuasiChar_apply, ContinuousQuasiChar.one_apply]
    exact h x

end NormCharacters

section CanonicalCharacters

variable (F K : Type*)
variable [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K]
  [Module.Finite F K]

/-- Pullback of a nontrivial additive character along the actual field
trace remains nontrivial for a finite separable extension. -/
theorem tracePullbackAddChar_ne_one [Algebra.IsSeparable F K]
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1) :
    tracePullbackAddChar F K ψ ≠ 1 := by
  intro hpullback
  apply hψ
  apply ContinuousAddChar.ext
  intro y
  obtain ⟨x, hx⟩ := Algebra.trace_surjective F K y
  have hvalue := DFunLike.congr_fun hpullback x
  rw [tracePullbackAddChar_apply, ContinuousAddChar.one_apply, hx] at hvalue
  exact hvalue

/-- The canonical exact-conductor wrappers preserve the two characters
used by the First Main Lemma interface.

On the multiplicative side, the packaged upper-field character is the norm
pullback of the packaged lower-field character.  On the additive side it is
the corresponding trace pullback.  The equalities are equalities of the
full continuous character objects on `Kˣ` and `K`, respectively, and also
bridge FML's public `normQuasiChar`/`tracePullbackAddChar` names to its
`compNorm`/`compTrace` character API. -/
theorem canonicalCharacters_compatible [Algebra.IsSeparable F K]
    (χ : ContinuousQuasiChar F) (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1) :
    (canonicalLocalQuasiCharData K (normQuasiChar F K χ)).character =
        (canonicalLocalQuasiCharData F χ).character.compNorm ∧
      (canonicalLocalAddCharData K (tracePullbackAddChar F K ψ)
          (tracePullbackAddChar_ne_one F K ψ hψ)).character =
        (canonicalLocalAddCharData F ψ hψ).character.compTrace := by
  constructor <;> rfl

end CanonicalCharacters

end

end LanglandsSecondMainLemma.Basic
