import LanglandsFirstMainLemma.Delta.Elementary
import LanglandsFirstMainLemma.Delta.FirstMainStatement
import LanglandsFirstMainLemma.Delta.LocalConstantRealization
import LanglandsFirstMainLemma.Main
import LanglandsSecondMainLemma.Characters.Conjugacy

/-!
# The odd-degree common power

Paper Corollary 4.3 (`U:odd-power`), lines 591–608 of the corrected
`references/epsilon_SML.tex`, in the full setup of Lemma `U:conjugacy`.

FML's odd-prime character-product theorem cancels the complete upper and
lower norm-character products. The accepted conjugacy theorem identifies
all upper twists with field conjugates, whose canonical local constants
agree by trace-invariance. Applying FML on each upper edge gives the common
power. Nonvanishing of the canonical local constant justifies the ratio.
-/

open LanglandsFirstMainLemma
open scoped BigOperators
namespace LanglandsSecondMainLemma.Characters
noncomputable section

section Product
variable (F E : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [Fintype (NormCharacter F E)]

/-- Apply FML's inverse-pairing product theorem to its actual norm-character
subgroup, using the canonical exact-conductor data and admissible denominators. -/
private theorem localConstant_normCharacter_product_odd
    (hprime : (Nat.card (NormCharacter F E)).Prime)
    (hodd : Odd (Nat.card (NormCharacter F E)))
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1) :
    (∏ μ : NormCharacter F E, localConstant F μ.1 ψ) = 1 := by
  letI : Fintype (normCharacterSubgroup F E) :=
    inferInstanceAs (Fintype (NormCharacter F E))
  let ψData := canonicalLocalAddCharData F ψ hψ
  let χData : NormCharacter F E → LocalQuasiCharData F := fun μ => canonicalLocalQuasiCharData F μ.1
  let γ : ∀ μ, AdmissibleGamma F (χData μ) ψData := fun _ =>
    Classical.choice AdmissibleGamma.exists_admissible
  have hcard : Nat.card (NormCharacter F E) =
      Fintype.card (normCharacterSubgroup F E) := by
    change Nat.card (normCharacterSubgroup F E) = _
    exact Nat.card_eq_fintype_card
  have h := delta_odd_prime_character_product F (normCharacterSubgroup F E)
    (hcard ▸ hprime) (hcard ▸ hodd)
    ψData χData (fun _ => rfl) γ
  calc
    (∏ μ : NormCharacter F E, localConstant F μ.1 ψ) =
        ∏ μ : NormCharacter F E, deltaFinite (χData μ) ψData (γ μ) := by
      apply Finset.prod_congr rfl
      intro μ _
      exact localConstant_isDeltaFinite F (χData μ) ψData (γ μ)
    _ = 1 := h
end Product

section Edge
variable (F E K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F E] [Algebra E K]
  [ValuativeExtension F E] [ValuativeExtension E K]
  [Module.Finite F E] [Module.Finite E K] [IsGalois F E]

/-- The accepted orbit equivalence computes the full upper character count
without repeating the ramified and unramified norm-index arguments. -/
private theorem conjugateTwist_card {θ : ContinuousQuasiChar E}
    (D : ConjugateTwistData F E K θ) :
    Nat.card (NormCharacter E K) = Module.finrank F E :=
  (Nat.card_congr D.quotientEquiv.toEquiv).symm.trans (IsGalois.card_aut_eq_finrank F E)

/-- FML on an upper edge with its conjugate-twist data. The additive character
is the actual lower trace pullback, so automorphism invariance is proved. -/
private theorem conjugateTwist_localConstant_pow
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hE : Module.finrank F E = p)
    (hcyclic : CyclicPrimeExtension E K)
    (θ : ContinuousQuasiChar E) (D : ConjugateTwistData F E K θ)
    (ψF : ContinuousAddChar F) (hψF : ψF ≠ 1) :
    localConstant E θ (tracePullbackAddChar F E ψF) ^ p =
      localConstant K (normQuasiChar E K θ)
        (tracePullbackAddChar E K (tracePullbackAddChar F E ψF)) := by
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension E K hcyclic
  letI := primeCyclicNormCharacter_finite E K
  letI := Fintype.ofFinite (NormCharacter E K)
  have hcard := (conjugateTwist_card F E K D).trans hE
  have hψ := Basic.tracePullbackAddChar_ne_one F E ψF hψF
  have hfml := firstMainLemma E K hcyclic θ (tracePullbackAddChar F E ψF) hψ
  change localConstant K (normQuasiChar E K θ)
    (tracePullbackAddChar E K (tracePullbackAddChar F E ψF)) *
      (∏ μ : NormCharacter E K, localConstant E μ.1 (tracePullbackAddChar F E ψF)) =
      ∏ μ : NormCharacter E K, localConstant E (μ.1 * θ) (tracePullbackAddChar F E ψF)
    at hfml
  rw [localConstant_normCharacter_product_odd E K (hcard ▸ hp) (hcard ▸ hodd)
    _ hψ, mul_one] at hfml
  rw [hfml]
  symm
  calc
    (∏ μ : NormCharacter E K, localConstant E (μ.1 * θ) (tracePullbackAddChar F E ψF)) =
        ∏ _μ : NormCharacter E K, localConstant E θ (tracePullbackAddChar F E ψF) := by
      apply Finset.prod_congr rfl
      intro μ _
      obtain ⟨σ, rfl⟩ := D.quotientEquiv.surjective μ
      have hχ : (D.quotientEquiv σ).1 * θ = Basic.conjugateQuasiChar F E σ θ :=
        (mul_comm (D.quotientEquiv σ).1 θ).trans (D.conjugate_eq_twist σ).symm
      exact (congrArg (fun χ => localConstant E χ (tracePullbackAddChar F E ψF)) hχ).trans
        (Basic.localConstant_conjugate F E σ θ _ hψ (fun x => by
          simp only [tracePullbackAddChar_apply, trace, Algebra.trace_eq_of_algEquiv]))
    _ = localConstant E θ (tracePullbackAddChar F E ψF) ^ p := by
      simp only [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
end Edge

section Diamond
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

/-- **Paper Corollary 4.3 (`U:odd-power`), lines 591–608.**
For an odd prime and a primitive compatible pair on distinct lower norm
subgroups in the actual prime-square diamond, both upper local constants
have the common `p`th power, both complete lower correction products are
one, and the ratio of the complete induction expressions has `p`th power
one. All additive characters are pullbacks of the same nontrivial `ψF`.

Conjugate-twist data and cyclic edge structures are constructed from the
actual pair. The proof uses the First Main Lemma, its odd character-product
theorem, and automorphism invariance; it imposes no conductor, ramification,
residue-characteristic, field-characteristic, or unitarity restriction. -/
theorem oddPower
    {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (I J : IntermediateField F K)
    (hI : Module.finrank F I = p) (hJ : Module.finrank F J = p)
    (hne : Ramification.intermediateNormRange I ≠ Ramification.intermediateNormRange J) :
    letI := Basic.intermediateFieldValuativeRel I
    letI := Basic.intermediateFieldTopology I
    letI := Basic.intermediateField_localField I
    letI := Basic.intermediateField_lowerValuativeExtension I
    letI := Basic.intermediateField_upperValuativeExtension I
    letI := Basic.intermediateFieldValuativeRel J
    letI := Basic.intermediateFieldTopology J
    letI := Basic.intermediateField_localField J
    letI := Basic.intermediateField_lowerValuativeExtension J
    letI := Basic.intermediateField_upperValuativeExtension J
    letI := PrimeCyclicExtension.ofCyclicPrimeExtension F I
      (Basic.intermediateField_tower_compatible hp hG I hI).2.2.2.2.2.2.2.2.2.2.2.1
    letI := PrimeCyclicExtension.ofCyclicPrimeExtension F J
      (Basic.intermediateField_tower_compatible hp hG J hJ).2.2.2.2.2.2.2.2.2.2.2.1
    letI := primeCyclicNormCharacter_finite F I
    letI := primeCyclicNormCharacter_finite F J
    letI := Fintype.ofFinite (NormCharacter F I)
    letI := Fintype.ofFinite (NormCharacter F J)
    ∀ (θI : ContinuousQuasiChar I) (θJ : ContinuousQuasiChar J) (Θ : ContinuousQuasiChar K),
      normQuasiChar I K θI = Θ → normQuasiChar J K θJ = Θ →
      (¬ ∃ χ : ContinuousQuasiChar F, normQuasiChar F K χ = Θ) →
      ∀ (ψF : ContinuousAddChar F), ψF ≠ 1 →
      localConstant I θI (tracePullbackAddChar F I ψF) ^ p =
        localConstant K Θ (tracePullbackAddChar F K ψF) ∧
      localConstant J θJ (tracePullbackAddChar F J ψF) ^ p =
        localConstant K Θ (tracePullbackAddChar F K ψF) ∧
      (∏ ω : NormCharacter F I, localConstant F ω.1 ψF) = 1 ∧
      (∏ ω : NormCharacter F J, localConstant F ω.1 ψF) = 1 ∧
      ((localConstant I θI (tracePullbackAddChar F I ψF) *
          ∏ ω : NormCharacter F I, localConstant F ω.1 ψF) /
        (localConstant J θJ (tracePullbackAddChar F J ψF) *
          ∏ ω : NormCharacter F J, localConstant F ω.1 ψF)) ^ p = 1 := by
  letI := Basic.intermediateFieldValuativeRel I
  letI := Basic.intermediateFieldTopology I
  letI := Basic.intermediateField_localField I
  letI := Basic.intermediateField_lowerValuativeExtension I
  letI := Basic.intermediateField_upperValuativeExtension I
  letI := Basic.intermediateFieldValuativeRel J
  letI := Basic.intermediateFieldTopology J
  letI := Basic.intermediateField_localField J
  letI := Basic.intermediateField_lowerValuativeExtension J
  letI := Basic.intermediateField_upperValuativeExtension J
  have hdataI := Basic.intermediateField_tower_compatible hp hG I hI
  have hdataJ := Basic.intermediateField_tower_compatible hp hG J hJ
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F I hdataI.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F J hdataJ.2.2.2.2.2.2.2.2.2.2.2.1
  letI := primeCyclicNormCharacter_finite F I
  letI := primeCyclicNormCharacter_finite F J
  letI := Fintype.ofFinite (NormCharacter F I)
  letI := Fintype.ofFinite (NormCharacter F J)
  intro θI θJ Θ hcI hcJ hprimitive ψF hψF
  obtain ⟨⟨DI⟩, ⟨DJ⟩, _⟩ := conjugacy hp hG I J hI hJ hne θI θJ Θ hcI hcJ hprimitive
  have hcardIK := (conjugateTwist_card F I K DI).trans hI
  have hcardJK := (conjugateTwist_card F J K DJ).trans hJ
  -- Reuse the accepted crossed-norm equivalences for the lower cardinalities.
  have hcardFI := (Nat.card_congr (crossedNorm hp hG J I hJ hI hne.symm).toEquiv).trans hcardJK
  have hcardFJ := (Nat.card_congr (crossedNorm hp hG I J hI hJ hne).toEquiv).trans hcardIK
  have hprodI := localConstant_normCharacter_product_odd F I
    (hcardFI ▸ hp) (hcardFI ▸ hodd) ψF hψF
  have hprodJ := localConstant_normCharacter_product_odd F J
    (hcardFJ ▸ hp) (hcardFJ ▸ hodd) ψF hψF
  have htraceI : tracePullbackAddChar I K (tracePullbackAddChar F I ψF) =
      tracePullbackAddChar F K ψF := by
    apply ContinuousAddChar.ext
    intro x
    simp only [tracePullbackAddChar_apply, trace, Algebra.trace_trace]
  have htraceJ : tracePullbackAddChar J K (tracePullbackAddChar F J ψF) =
      tracePullbackAddChar F K ψF := by
    apply ContinuousAddChar.ext
    intro x
    simp only [tracePullbackAddChar_apply, trace, Algebra.trace_trace]
  have hpowI := conjugateTwist_localConstant_pow F I K hp hodd hI
    hdataI.2.2.2.2.2.2.2.2.2.2.2.2 θI DI ψF hψF
  have hpowJ := conjugateTwist_localConstant_pow F J K hp hodd hJ
    hdataJ.2.2.2.2.2.2.2.2.2.2.2.2 θJ DJ ψF hψF
  rw [hcI, htraceI] at hpowI
  rw [hcJ, htraceJ] at hpowJ
  refine ⟨hpowI, hpowJ, hprodI, hprodJ, ?_⟩
  rw [hprodI, hprodJ, mul_one, mul_one, div_pow, hpowI, hpowJ]
  apply div_self
  exact (localConstant_isDeltaFinite K).apply_ne_zero
    (canonicalLocalQuasiCharData K Θ)
    (canonicalLocalAddCharData K (tracePullbackAddChar F K ψF)
      (Basic.tracePullbackAddChar_ne_one F K ψF hψF))

end Diamond

end
end LanglandsSecondMainLemma.Characters
