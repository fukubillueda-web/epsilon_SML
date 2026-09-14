import LanglandsFirstMainLemma.Delta.Elementary
import LanglandsFirstMainLemma.Delta.LocalConstantRealization
import LanglandsSecondMainLemma.Characters.Conjugacy
import LanglandsSecondMainLemma.Local.NormDescent

/-!
# Independence of inducing choices and distinguished comparisons

The setup is `U:main` (lines 123–139): the actual continuous character Θ
is Galois invariant and does not descend from the base field. The choice
argument uses `U:conjugacy` (lines 545–589), with its distinct lower norm
kernels, and the automorphism change of variables in `U:interface`.
The family assembly is the last step of `O:G:totalbranch` (lines 5109–5128)
and of the proof of `U:main` (lines 8185–8220).

All factors below use FML's canonical local constant and the complete lower
norm-character product. No conductor, residue characteristic, or unitarity
restriction is imposed. Cyclic norm descent constructs the inducing
characters; conjugate-twist data are obtained from the accepted constructor.
-/

namespace LanglandsSecondMainLemma.Characters

open LanglandsFirstMainLemma
open scoped BigOperators

noncomputable section

section Edge

variable {F E K : Type} [Field F] [Field E] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F E] [Algebra E K]
  [ValuativeExtension F E] [ValuativeExtension E K]
  [Module.Finite F E] [Module.Finite E K]

/-- The quotient of two inducing choices is an actual upper norm character. -/
def inducingChoiceQuotient (θ θ' : ContinuousQuasiChar E)
    (hc : normQuasiChar E K θ' = normQuasiChar E K θ) : NormCharacter E K :=
  ⟨θ' / θ, by
    apply ContinuousMonoidHom.ext
    intro x
    change θ' (normUnits E K x) / θ (normUnits E K x) = 1
    exact div_eq_one.mpr (DFunLike.congr_fun hc x)⟩

/-- The accepted orbit parametrization turns equality of norm pullbacks
into equality of the canonical local constants for trace additive characters. -/
theorem ConjugateTwistData.localConstant_eq_of_norm_eq
    [Algebra.IsSeparable F E] {θ : ContinuousQuasiChar E}
    (D : ConjugateTwistData F E K θ) (θ' : ContinuousQuasiChar E)
    (hc : normQuasiChar E K θ' = normQuasiChar E K θ)
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1) :
    localConstant E θ' (tracePullbackAddChar F E ψ) =
      localConstant E θ (tracePullbackAddChar F E ψ) := by
  let μ := inducingChoiceQuotient θ θ' hc
  obtain ⟨σ, hσ⟩ := D.quotientEquiv.surjective μ
  have hconj : Basic.conjugateQuasiChar F E σ θ = θ' := by
    rw [D.conjugate_eq_twist, hσ]
    change θ * (θ' / θ) = θ'
    simp [div_eq_mul_inv]
  rw [← hconj]
  apply Basic.localConstant_conjugate F E σ θ (tracePullbackAddChar F E ψ)
    (Basic.tracePullbackAddChar_ne_one F E ψ hψ)
  intro x
  change ψ (Algebra.trace F E (σ x)) = ψ (Algebra.trace F E x)
  rw [Algebra.trace_eq_of_algEquiv]

end Edge

section Diamond

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

-- These are exactly the accepted restrictions to actual intermediate fields.
attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

/-- The complete induction factor for one inducing character, before choosing
an entire family. The finite product includes the trivial lower character. -/
def inducingFactor {p : ℕ} (hp : p.Prime)
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (ψ : ContinuousAddChar F) (L : IntermediateField F K)
    (hL : Module.finrank F L = p) (θ : ContinuousQuasiChar L) : ℂ := by
  have hdata := Basic.intermediateField_tower_compatible hp hG L hL
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F L hdata.2.2.2.2.2.2.2.2.2.2.2.1
  letI := primeCyclicNormCharacter_finite F L
  exact localConstant L θ (tracePullbackAddChar F L ψ) *
    (normCharacterFinset F L).prod (fun ν => localConstant F ν.1 ψ)

/-- **Independence of the inducing choice on a fixed lower field.**
The other compatible character and the distinct lower norm kernels are the
precise hypotheses of `U:conjugacy`. The orbit data used in the proof are
constructed from these genuine inputs. The conclusion keeps the whole
normalized expression, including every lower norm-character factor. -/
theorem inducingChoice_independent {p : ℕ} (hp : p.Prime)
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (I J : IntermediateField F K)
    (hI : Module.finrank F I = p) (hJ : Module.finrank F J = p)
    (hne : Ramification.intermediateNormRange I ≠ Ramification.intermediateNormRange J)
    (θI θI' : ContinuousQuasiChar I) (θJ : ContinuousQuasiChar J)
    (Θ : ContinuousQuasiChar K)
    (hcI : normQuasiChar I K θI = Θ) (hcI' : normQuasiChar I K θI' = Θ)
    (hcJ : normQuasiChar J K θJ = Θ)
    (hprimitive : ¬ ∃ χ : ContinuousQuasiChar F, normQuasiChar F K χ = Θ)
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1) :
    inducingFactor hp hG ψ I hI θI' = inducingFactor hp hG ψ I hI θI := by
  obtain ⟨⟨D⟩, _⟩ := conjugacy hp hG I J hI hJ hne θI θJ Θ hcI hcJ hprimitive
  have hdata := Basic.intermediateField_tower_compatible hp hG I hI
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F I hdata.2.2.2.2.2.2.2.2.2.2.2.1
  have heq := D.localConstant_eq_of_norm_eq θI' (hcI'.trans hcI.symm) ψ hψ
  unfold inducingFactor
  rw [heq]

/-- Cyclic Hilbert 90 and continuous norm descent supply an inducing
character on any degree-`p` intermediate field, in particular the distinguished
one. The invariance hypothesis is the actual `U:main` hypothesis on Θ. -/
theorem invariantCharacter_inducing_exists {p : ℕ} (hp : p.Prime)
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (Θ : ContinuousQuasiChar K)
    (hinv : ∀ σ : Gal(K/F), Basic.conjugateQuasiChar F K σ Θ = Θ)
    (L : IntermediateField F K) (hL : Module.finrank F L = p) :
    ∃ θ : ContinuousQuasiChar L, normQuasiChar L K θ = Θ := by
  have hdata := Basic.intermediateField_tower_compatible hp hG L hL
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension L K hdata.2.2.2.2.2.2.2.2.2.2.2.2
  apply Local.invariantCharacter_descends L K Θ
  intro σ x
  have h := DFunLike.congr_fun (hinv (σ.restrictScalars F).symm) x
  exact h

/-- **Distinguished comparisons give independence of the entire family.**

The branch input `hcompare` concerns only comparisons with the distinguished
field `L₀` and a different field. `J₀` is any degree-`p` field with a separated
lower norm kernel, as supplied by `D:norm-separation` for distinguished pairs.
It is used only to prove independence between two inducing choices on `L₀`.

Cyclic descent constructs a simultaneous family from the invariant Θ. The
conclusion compares *arbitrary* compatible inducing characters, so existing
choices on any pair of fields are retained, even when both fields coincide.
This is a conditional assembly lemma: its branch comparison is an input,
whereas character existence and choice independence are proved here. -/
theorem distinguishedComparisons_imply_family {p : ℕ} (hp : p.Prime)
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (L₀ J₀ : IntermediateField F K)
    (hL₀ : Module.finrank F L₀ = p) (hJ₀ : Module.finrank F J₀ = p)
    (hsep : Ramification.intermediateNormRange L₀ ≠ Ramification.intermediateNormRange J₀)
    (Θ : ContinuousQuasiChar K)
    (hinv : ∀ σ : Gal(K/F), Basic.conjugateQuasiChar F K σ Θ = Θ)
    (hprimitive : ¬ ∃ χ : ContinuousQuasiChar F, normQuasiChar F K χ = Θ)
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1)
    (hcompare : ∀ (L : IntermediateField F K) (hL : Module.finrank F L = p),
      L ≠ L₀ → ∀ (θ₀ : ContinuousQuasiChar L₀) (θL : ContinuousQuasiChar L),
        normQuasiChar L₀ K θ₀ = Θ → normQuasiChar L K θL = Θ →
        inducingFactor hp hG ψ L₀ hL₀ θ₀ = inducingFactor hp hG ψ L hL θL) :
    ∃ θ : ∀ (L : IntermediateField F K),
        Module.finrank F L = p → ContinuousQuasiChar L,
      (∀ (L : IntermediateField F K) (hL : Module.finrank F L = p),
        normQuasiChar L K (θ L hL) = Θ) ∧
      (∀ (I J : IntermediateField F K)
          (hI : Module.finrank F I = p) (hJ : Module.finrank F J = p)
          (χI : ContinuousQuasiChar I) (χJ : ContinuousQuasiChar J),
        normQuasiChar I K χI = Θ → normQuasiChar J K χJ = Θ →
        inducingFactor hp hG ψ I hI χI = inducingFactor hp hG ψ J hJ χJ) := by
  classical
  choose θ hθ using invariantCharacter_inducing_exists hp hG Θ hinv
  refine ⟨θ, hθ, ?_⟩
  have hto : ∀ (L : IntermediateField F K) (hL : Module.finrank F L = p)
      (χ : ContinuousQuasiChar L), normQuasiChar L K χ = Θ →
      inducingFactor hp hG ψ L hL χ = inducingFactor hp hG ψ L₀ hL₀ (θ L₀ hL₀) := by
    intro L hL χ hc
    by_cases heq : L = L₀
    · subst L
      exact inducingChoice_independent hp hG L₀ J₀ hL₀ hJ₀ hsep
        (θ L₀ hL₀) χ (θ J₀ hJ₀) Θ (hθ L₀ hL₀) hc (hθ J₀ hJ₀) hprimitive ψ hψ
    · exact (hcompare L hL heq (θ L₀ hL₀) χ (hθ L₀ hL₀) hc).symm
  intro I J hI hJ χI χJ hcI hcJ
  exact (hto I hI χI hcI).trans (hto J hJ χJ hcJ).symm

end Diamond
end
end LanglandsSecondMainLemma.Characters
