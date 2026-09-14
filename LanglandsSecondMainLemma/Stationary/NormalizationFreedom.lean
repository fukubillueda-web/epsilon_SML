import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsSecondMainLemma.Basic.Characters

/-!
# Stationary / Normalization Freedom

Blueprint: blueprint/tasks/Stationary/NormalizationFreedom.md
Paper: Lemma 4.9, `U:normalization`.

This module formalizes the final choice in the paper's normalization
argument.  The subgroup on which changing the auxiliary normalization
preserves the already established formulas, and the proof of that
preservation, remain explicit inputs.  The conclusion chooses an element
of that subgroup, an actual norm representative upstairs, and records the
unchanged raw coefficient.

Normal planning range: 80–400 lines; review splitting at 1200.
-/

namespace LanglandsSecondMainLemma.Stationary

noncomputable section

open LanglandsFirstMainLemma

variable {F L : Type}
variable [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
variable [Algebra F L] [ValuativeExtension F L]
  [Module.Free F L] [Module.Finite F L]

/-- A nontrivial norm character of a cyclic prime-degree local-field
extension has exactly the field norm image as its kernel.

`NormCharacter` directly gives one inclusion.  For the reverse inclusion,
factor through the actual norm quotient.  FML computes that quotient to
have the prime cardinality `[L : F]`, in both its unramified and ramified
branches, so the kernel of a nontrivial quotient character is trivial. -/
private theorem nontrivialNormCharacter_ker_eq_normRange
    (hcyclic : CyclicPrimeExtension F L)
    (omega : NormCharacter F L) (homega : omega.1 ≠ 1) :
    omega.1.toMonoidHom.ker = (normUnits F L).range := by
  letI : PrimeCyclicExtension F L :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F L hcyclic
  let Q := NormQuotient F L
  letI : Finite Q := by
    by_cases hunr : ramificationIndex F L = 1
    · exact unramifiedNormQuotient_finite F L hunr
    · let P : PrimeCyclicPreparation F L := primeCyclicPreparation F L hunr
      exact normQuotient_finite F L P.ht P.hres P.piK P.hpiK P.hgen
  have hQcard : Nat.card Q = Module.finrank F L := by
    by_cases hunr : ramificationIndex F L = 1
    · exact unramifiedNormQuotient_card F L hunr
    · let P : PrimeCyclicPreparation F L := primeCyclicPreparation F L hunr
      exact normQuotient_card F L P.ht P.hres P.piK P.hpiK P.hgen
  letI : Fact (Nat.card Q).Prime :=
    ⟨hQcard ▸ PrimeCyclicExtension.degree_prime F L⟩
  let rho : NormQuotientCharacter F L := omega.toQuotientCharacter F L
  have hrho : rho ≠ 1 := by
    intro hrhoOne
    apply homega
    apply ContinuousMonoidHom.ext
    intro a
    exact DFunLike.congr_fun hrhoOne (QuotientGroup.mk a)
  have hrhoKer : rho.toMonoidHom.ker = ⊥ := by
    rcases rho.toMonoidHom.ker.eq_bot_or_eq_top_of_prime_card with hbot | htop
    · exact hbot
    · exfalso
      apply hrho
      apply ContinuousMonoidHom.ext
      intro q
      exact DFunLike.congr_fun (MonoidHom.ker_eq_top_iff.mp htop) q
  apply le_antisymm
  · intro a ha
    have hqa : (QuotientGroup.mk a : Q) ∈ rho.toMonoidHom.ker := by
      rw [MonoidHom.mem_ker]
      exact ha
    rw [hrhoKer] at hqa
    exact (QuotientGroup.eq_one_iff a).mp (Subgroup.mem_bot.mp hqa)
  · exact fun a ha => omega.eq_one_on_normRange F L a ha

/-- **Norm choice within a proven normalization freedom** (Paper Lemma 4.9,
`U:normalization`).

Let `H` be the subgroup of changes under which the already fixed formulas
are preserved.  If the image of `H` under the nontrivial norm character
`omega` is its full image, then one can change `alpha` to `alpha * u` with
`u ∈ H` so that `Astar / u` is the norm of an actual element of `Lˣ`.
The last equality records exactly that the raw coefficient `alpha * Astar`
has not changed.

The hypothesis `hpreserves` is deliberately abstract: a branch applying
this lemma must first prove preservation of its complete family of
character formulas.  The exact kernel condition in the manuscript follows
here from the cyclic prime-degree hypothesis and FML's norm-quotient
theorem; it is not added as a further assumption. -/
theorem normalizationFreedom
    (hcyclic : CyclicPrimeExtension F L)
    (omega : NormCharacter F L) (homega : omega.1 ≠ 1)
    (H : Subgroup Fˣ)
    (FixedFormulas : Fˣ → Prop)
    (alpha Astar : Fˣ)
    (hpreserves : ∀ u : H,
      FixedFormulas (alpha * (u : Fˣ)) ↔ FixedFormulas alpha)
    (himage : H.map omega.1.toMonoidHom = omega.1.toMonoidHom.range) :
    ∃ (u : H) (x : Lˣ),
      Astar / (u : Fˣ) = normUnits F L x ∧
        (FixedFormulas (alpha * (u : Fˣ)) ↔ FixedFormulas alpha) ∧
        (alpha * (u : Fˣ)) * (Astar / (u : Fˣ)) = alpha * Astar := by
  have hAstar : omega.1 Astar ∈ omega.1.toMonoidHom.range :=
    ⟨Astar, rfl⟩
  rw [← himage] at hAstar
  obtain ⟨u, huH, huomega⟩ := hAstar
  let uH : H := ⟨u, huH⟩
  have hker :=
    nontrivialNormCharacter_ker_eq_normRange hcyclic omega homega
  have hratioKer : Astar / u ∈ omega.1.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    change omega.1 (Astar / u) = 1
    rw [map_div]
    have huomega' : omega.1 u = omega.1 Astar := huomega
    rw [huomega']
    change omega.1 Astar * (omega.1 Astar)⁻¹ = 1
    exact mul_inv_cancel (omega.1 Astar)
  rw [hker] at hratioKer
  obtain ⟨x, hx⟩ := hratioKer
  refine ⟨uH, x, hx.symm, hpreserves uH, ?_⟩
  simp only [uH]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

end

end LanglandsSecondMainLemma.Stationary
