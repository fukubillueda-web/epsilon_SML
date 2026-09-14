import LanglandsFirstMainLemma.Delta.Elementary
import LanglandsFirstMainLemma.Delta.FirstMainStatement
import LanglandsFirstMainLemma.Delta.LocalConstantRealization
import LanglandsFirstMainLemma.Main
import LanglandsSecondMainLemma.Characters.Conjugacy
import LanglandsSecondMainLemma.Characters.QuadraticProduct

/-!
# The biquadratic common square

Paper Proposition 4.4 (`U:quadratic-square`), lines 610–626, in the
primitive compatible setup of `U:conjugacy`. FML is applied on both edges
of each quadratic tower. The three lower correction factors are retained;
the resulting common square determines the comparison only up to sign.
-/

open LanglandsFirstMainLemma
open scoped BigOperators
namespace LanglandsSecondMainLemma.Characters
noncomputable section

open private primeNormCharacter_card from LanglandsSecondMainLemma.Characters.Conjugacy

private theorem prod_card_two {G M : Type*} [One G] [Fintype G] [CommMonoid M]
    (hcard : Nat.card G = 2) (a : G) (ha : a ≠ 1) (f : G → M) :
    ∏ x, f x = f 1 * f a := by
  classical
  have huniv : (Finset.univ : Finset G) = {1, a} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hx : x = 1
    · exact Or.inl hx
    · exact Or.inr (((Nat.card_eq_two_iff' (1 : G)).mp hcard).unique hx ha)
  rw [huniv, Finset.prod_pair ha.symm]

private theorem quadratic_localConstant_one
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1) :
    localConstant F 1 ψ = 1 := by
  let ψd := canonicalLocalAddCharData F ψ hψ
  let γ : AdmissibleGamma F (trivialQuasiCharData F) ψd :=
    Classical.choice AdmissibleGamma.exists_admissible
  exact (localConstant_isDeltaFinite F (trivialQuasiCharData F) ψd γ).trans
    (delta_trivial_character F ψd γ)

section Edge
variable (F E : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]

/-- FML with the complete order-two norm-character products evaluated. -/
private theorem quadratic_firstMain
    (hcyclic : CyclicPrimeExtension F E) (hdegree : Module.finrank F E = 2)
    (ω : NormCharacter F E) (hω : ω ≠ 1)
    (χ : ContinuousQuasiChar F) (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1) :
    localConstant E (normQuasiChar F E χ) (tracePullbackAddChar F E ψ) *
        localConstant F ω.1 ψ =
      localConstant F χ ψ * localConstant F (ω.1 * χ) ψ := by
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E hcyclic
  letI := primeCyclicNormCharacter_finite F E
  letI := Fintype.ofFinite (NormCharacter F E)
  have hcard := (primeNormCharacter_card F E).trans hdegree
  have h := firstMainLemma F E hcyclic χ ψ hψ
  change localConstant E (normQuasiChar F E χ) (tracePullbackAddChar F E ψ) *
    (∏ ν : NormCharacter F E, localConstant F ν.1 ψ) =
      ∏ ν : NormCharacter F E, localConstant F (ν.1 * χ) ψ at h
  rw [prod_card_two hcard ω hω, prod_card_two hcard ω hω] at h
  change localConstant E (normQuasiChar F E χ) (tracePullbackAddChar F E ψ) *
    (localConstant F 1 ψ * localConstant F ω.1 ψ) =
      localConstant F (1 * χ) ψ * localConstant F (ω.1 * χ) ψ at h
  rw [one_mul χ] at h
  simpa only [one_mul, quadratic_localConstant_one F ψ hψ] using h
end Edge

section Tower
variable (F E K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F E] [Algebra E K]
  [ValuativeExtension F E] [ValuativeExtension E K]
  [Module.Finite F E] [Module.Finite E K] [IsGalois F E]

/-- On an upper quadratic edge the nontrivial twist is a field conjugate. -/
private theorem quadratic_upper_square
    (hcyclic : CyclicPrimeExtension E K) (hdegree : Module.finrank E K = 2)
    (θ : ContinuousQuasiChar E) (D : ConjugateTwistData F E K θ)
    (μ : NormCharacter E K) (hμ : μ ≠ 1)
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1) :
    localConstant E θ (tracePullbackAddChar F E ψ) ^ 2 =
      localConstant K (normQuasiChar E K θ)
        (tracePullbackAddChar E K (tracePullbackAddChar F E ψ)) *
      localConstant E μ.1 (tracePullbackAddChar F E ψ) := by
  have hψE := Basic.tracePullbackAddChar_ne_one F E ψ hψ
  have h := quadratic_firstMain E K hcyclic hdegree μ hμ θ _ hψE
  obtain ⟨σ, hσ⟩ := D.quotientEquiv.surjective μ
  have htwist : μ.1 * θ = Basic.conjugateQuasiChar F E σ θ := by
    exact (mul_comm μ.1 θ).trans
      ((congrArg (fun ν : NormCharacter E K => θ * ν.1) hσ).symm.trans
        (D.conjugate_eq_twist σ).symm)
  rw [htwist, Basic.localConstant_conjugate F E σ θ _ hψE (fun x => by
    simp only [tracePullbackAddChar_apply, trace, Algebra.trace_eq_of_algEquiv]),
    ← pow_two] at h
  exact h.symm
end Tower

section Diamond
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

set_option maxHeartbeats 800000 in
/-- **Paper Proposition 4.4 (`U:quadratic-square`).** For the three distinct
quadratic intermediate fields and primitive compatible continuous characters,
the complete induction expressions have the displayed common square. Their
ratios are `1` or `-1`; no choice of that sign is asserted.

The nontrivial lower norm characters, all edge structures, and conjugate-twist
data are constructed from the genuine biquadratic input. The full lower
norm-character products are explicitly identified with the quadratic factors.
All additive characters are actual trace pullbacks of the same nontrivial
base character. There is no characteristic, conductor, ramification, or
unitarity restriction. -/
theorem quadraticSquare
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (L : Fin 3 → IntermediateField F K)
    (hdegree : ∀ i, Module.finrank F (L i) = 2) (hdistinct : Function.Injective L) :
    letI : ∀ i, ValuativeRel (L i) := fun i => Basic.intermediateFieldValuativeRel (L i)
    letI : ∀ i, TopologicalSpace (L i) := fun i => Basic.intermediateFieldTopology (L i)
    letI : ∀ i, IsNonarchimedeanLocalField (L i) := fun i => Basic.intermediateField_localField (L i)
    letI : ∀ i, ValuativeExtension F (L i) := fun i => Basic.intermediateField_lowerValuativeExtension (L i)
    letI : ∀ i, ValuativeExtension (L i) K := fun i => Basic.intermediateField_upperValuativeExtension (L i)
    letI : ∀ i, PrimeCyclicExtension F (L i) := fun i =>
      PrimeCyclicExtension.ofCyclicPrimeExtension F (L i)
        (Basic.intermediateField_tower_compatible Nat.prime_two hG (L i) (hdegree i)).2.2.2.2.2.2.2.2.2.2.2.1
    letI : ∀ i, Finite (NormCharacter F (L i)) := fun i => primeCyclicNormCharacter_finite F (L i)
    letI : ∀ i, Fintype (NormCharacter F (L i)) := fun i => Fintype.ofFinite (NormCharacter F (L i))
    ∀ (θ : (i : Fin 3) → ContinuousQuasiChar (L i)) (Θ : ContinuousQuasiChar K),
      (∀ i, normQuasiChar (L i) K (θ i) = Θ) →
      (¬ ∃ χ : ContinuousQuasiChar F, normQuasiChar F K χ = Θ) →
      ∀ (ψ : ContinuousAddChar F), ψ ≠ 1 →
      ∃ ω : (i : Fin 3) → NormCharacter F (L i),
        (∀ i, ω i ≠ 1) ∧
        (∀ i, (∏ ν : NormCharacter F (L i), localConstant F ν.1 ψ) =
          localConstant F (ω i).1 ψ) ∧
        (let A := fun i => localConstant (L i) (θ i) (tracePullbackAddChar F (L i) ψ) *
            localConstant F (ω i).1 ψ
         (∀ i, A i ^ 2 = localConstant K Θ (tracePullbackAddChar F K ψ) *
           ∏ j : Fin 3, localConstant F (ω j).1 ψ) ∧
         ∀ i j, A i / A j = 1 ∨ A i / A j = -1) := by
  classical
  letI : ∀ i, ValuativeRel (L i) := fun i => Basic.intermediateFieldValuativeRel (L i)
  letI : ∀ i, TopologicalSpace (L i) := fun i => Basic.intermediateFieldTopology (L i)
  letI : ∀ i, IsNonarchimedeanLocalField (L i) := fun i => Basic.intermediateField_localField (L i)
  letI : ∀ i, ValuativeExtension F (L i) := fun i => Basic.intermediateField_lowerValuativeExtension (L i)
  letI : ∀ i, ValuativeExtension (L i) K := fun i => Basic.intermediateField_upperValuativeExtension (L i)
  have hdata i := Basic.intermediateField_tower_compatible Nat.prime_two hG (L i) (hdegree i)
  letI : ∀ i, PrimeCyclicExtension F (L i) := fun i =>
    PrimeCyclicExtension.ofCyclicPrimeExtension F (L i) (hdata i).2.2.2.2.2.2.2.2.2.2.2.1
  letI : ∀ i, Finite (NormCharacter F (L i)) := fun i => primeCyclicNormCharacter_finite F (L i)
  letI : ∀ i, Fintype (NormCharacter F (L i)) := fun i => Fintype.ofFinite (NormCharacter F (L i))
  intro θ Θ hc hprimitive ψ hψ
  obtain ⟨ω, hω, hωprod, _, hnorms, hcross⟩ := quadraticProduct F hG L hdegree hdistinct
  have hcard i : Nat.card (NormCharacter F (L i)) = 2 :=
    (primeNormCharacter_card F (L i)).trans (hdegree i)
  have hsq i : (ω i).1 ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := ω i)
    rw [hcard i] at h
    exact congrArg Subtype.val h
  let next : Fin 3 → Fin 3 := ![1, 2, 0]
  let third : Fin 3 → Fin 3 := ![2, 0, 1]
  have hnext i : i ≠ next i := by fin_cases i <;> decide
  have hωmul i : (ω i).1 * (ω (next i)).1 = (ω (third i)).1 := by
    have h0 := hsq 0
    have h1 := hsq 1
    fin_cases i
    · exact hωprod.symm
    · change (ω 1).1 * (ω 2).1 = (ω 0).1
      calc
        _ = (ω 1).1 * ((ω 0).1 * (ω 1).1) := congrArg (fun χ => (ω 1).1 * χ) hωprod
        _ = (ω 0).1 * ((ω 1).1 * (ω 1).1) := mul_left_comm (ω 1).1 (ω 0).1 (ω 1).1
        _ = (ω 0).1 * 1 := congrArg (fun χ => (ω 0).1 * χ) ((pow_two _).symm.trans h1)
        _ = _ := mul_one ((ω 0).1)
    · change (ω 2).1 * (ω 0).1 = (ω 1).1
      calc
        _ = ((ω 0).1 * (ω 1).1) * (ω 0).1 := congrArg (fun χ => χ * (ω 0).1) hωprod
        _ = ((ω 0).1 * (ω 0).1) * (ω 1).1 := mul_right_comm (ω 0).1 (ω 1).1 (ω 0).1
        _ = 1 * (ω 1).1 := congrArg (fun χ => χ * (ω 1).1) ((pow_two _).symm.trans h0)
        _ = _ := one_mul ((ω 1).1)
  let A := fun i => localConstant (L i) (θ i) (tracePullbackAddChar F (L i) ψ) *
    localConstant F (ω i).1 ψ
  have hA i : A i ^ 2 = localConstant K Θ (tracePullbackAddChar F K ψ) *
      ∏ j : Fin 3, localConstant F (ω j).1 ψ := by
    obtain ⟨⟨D⟩, _⟩ := conjugacy Nat.prime_two hG (L i) (L (next i))
      (hdegree i) (hdegree (next i)) (fun h => hnext i (hnorms h))
      (θ i) (θ (next i)) Θ (hc i) (hc (next i)) hprimitive
    obtain ⟨e, he⟩ := hcross i (next i) (hnext i)
    have heω : (e (ω (next i))).1 = normQuasiChar F (L i) (ω (next i)).1 := by
      apply ContinuousMonoidHom.ext
      intro x
      exact he (ω (next i)) x
    have he_ne : e (ω (next i)) ≠ 1 := by
      intro h
      exact hω (next i) (e.injective (h.trans e.map_one.symm))
    have hu := quadratic_upper_square F (L i) K
      (hdata i).2.2.2.2.2.2.2.2.2.2.2.2 (hdata i).2.2.2.2.2.2.2.2.2.2.1
      (θ i) D (e (ω (next i))) he_ne ψ hψ
    have htrace : tracePullbackAddChar (L i) K (tracePullbackAddChar F (L i) ψ) =
        tracePullbackAddChar F K ψ := by
      apply ContinuousAddChar.ext
      intro x
      simp only [tracePullbackAddChar_apply, trace, Algebra.trace_trace]
    rw [hc i, htrace, heω] at hu
    have hl := quadratic_firstMain F (L i) (hdata i).2.2.2.2.2.2.2.2.2.2.2.1
      (hdegree i) (ω i) (hω i) (ω (next i)).1 ψ hψ
    rw [hωmul i] at hl
    have hp : (∏ j : Fin 3, localConstant F (ω j).1 ψ) =
        localConstant F (ω (next i)).1 ψ * localConstant F (ω (third i)).1 ψ *
        localConstant F (ω i).1 ψ := by
      fin_cases i <;> simp [next, third, Fin.prod_univ_succ] <;> ring
    change (localConstant (L i) (θ i) (tracePullbackAddChar F (L i) ψ) *
      localConstant F (ω i).1 ψ) ^ 2 = _
    rw [mul_pow, hu, hp, pow_two]
    calc
      _ = localConstant K Θ (tracePullbackAddChar F K ψ) *
          (localConstant (L i) (normQuasiChar F (L i) (ω (next i)).1)
              (tracePullbackAddChar F (L i) ψ) * localConstant F (ω i).1 ψ) *
          localConstant F (ω i).1 ψ := by ring
      _ = _ := by rw [hl]; ring
  refine ⟨ω, hω, ?_, hA, ?_⟩
  · intro i
    rw [prod_card_two (hcard i) (ω i) (hω i)]
    change localConstant F 1 ψ * localConstant F (ω i).1 ψ = _
    rw [quadratic_localConstant_one F ψ hψ, one_mul]
  · intro i j
    apply sq_eq_one_iff.mp
    have hne : A j ≠ 0 := mul_ne_zero
      ((localConstant_isDeltaFinite (L j)).apply_ne_zero
        (canonicalLocalQuasiCharData (L j) (θ j))
        (canonicalLocalAddCharData (L j) (tracePullbackAddChar F (L j) ψ)
          (Basic.tracePullbackAddChar_ne_one F (L j) ψ hψ)))
      ((localConstant_isDeltaFinite F).apply_ne_zero
        (canonicalLocalQuasiCharData F (ω j).1) (canonicalLocalAddCharData F ψ hψ))
    change (A i / A j) ^ 2 = 1
    rw [div_pow, (hA i).trans (hA j).symm, div_self (pow_ne_zero 2 hne)]
end Diamond

end
end LanglandsSecondMainLemma.Characters
