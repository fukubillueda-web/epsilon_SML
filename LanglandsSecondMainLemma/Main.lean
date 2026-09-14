import LanglandsFirstMainLemma.Delta.FirstMainStatement
import LanglandsFirstMainLemma.Main
import LanglandsSecondMainLemma.Dispatch

/-!
# Main

The public Second Main Lemma, assembled from the exhaustive local dispatch.

Blueprint: `blueprint/tasks/Main.md`.
Paper: Theorem `U:main`, setup lines 121–155 and proof lines 8185–8219.
-/

namespace LanglandsSecondMainLemma

noncomputable section

open LanglandsFirstMainLemma

/-- **Langlands's Second Main Lemma.**

For an actual local Galois extension with group `C_ℓ × C_ℓ` and a primitive
compatible family of continuous quasi-characters, the expression

`Δ_L(θ_L, ψ_F ∘ Tr_{L/F}) * ∏ ν : S(L/F), Δ_F(ν, ψ_F)`

is independent of the degree-`ℓ` intermediate field `L`. Both factors use
FML's canonical `localConstant`; `S(L/F)` is the complete group of continuous
group homomorphisms trivial on norms, including the trivial character.

The supplied family has a Galois-invariant common top character which does
not descend by norm to `F`. No unitarity or field-characteristic restriction
is imposed. The dispatch constructs the auxiliary data for every prime and
every conductor from these actual field and character inputs.

Source: Theorem `U:main` and its proof in the completion section. -/
theorem secondMainLemma
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K]
    {ℓ : ℕ} (extension : Basic.PrimeSquareExtension F K ℓ)
    (family : Basic.PrimitiveCompatibleFamily F K extension)
    (ψF : ContinuousAddChar F) (hψF : ψF ≠ 1) :
    Basic.SecondMainIdentity F K extension family ψF hψF :=
  secondMainIdentity_of_actualData F K extension family ψF hψF

end

end LanglandsSecondMainLemma
