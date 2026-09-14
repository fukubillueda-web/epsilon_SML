import LanglandsFirstMainLemma.Delta.FirstMainStatement
import LanglandsFirstMainLemma.Main
import LanglandsSecondMainLemma.Dyadic.UR.Minimal
import LanglandsSecondMainLemma.Dyadic.UR.CriticalComparison
import LanglandsSecondMainLemma.Dyadic.UR.Stable
import LanglandsSecondMainLemma.Characters.InducingChoice

/-!
# Complete dyadic unramified--ramified comparison

Paper Theorem 10.20 (`D:UR:URall`), with the ambient setup at lines
5131–5178 and proof at lines 5936–5948 of `references/epsilon_SML.tex`.
The actual-pair realization supplies a nonnegative height. The minimal,
positive critical, and stable results exhaust its possible values.
All additive charts and generators are constructed from genuine input data.
The conclusion uses canonical local constants and the entire lower product.
-/

namespace LanglandsSecondMainLemma.Dyadic.UR

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators
open private primeNormCharacter_card inf_eq_bot_of_prime_degree
  from LanglandsSecondMainLemma.Characters.Conjugacy

section Edge
variable (F L : Type) [Field F] [Field L]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra F L] [ValuativeExtension F L] [Module.Finite F L]
  [PrimeCyclicExtension F L]

/-- Evaluate the complete lower product in degree two, retaining its identity
factor until the finite local-constant formula proves that factor is one. -/
private theorem comparisonFactor_quadratic
    (hL : Module.finrank F L = 2) (omega : NormCharacter F L) (homega : omega ≠ 1)
    (theta : ContinuousQuasiChar L) (psi : LocalAddCharData F) :
    stableComparisonFactor F L theta psi.character =
      localConstant L theta (tracePullbackAddChar F L psi.character) *
        localConstant F omega.1 psi.character := by
  classical
  letI := primeCyclicNormCharacter_finite F L
  letI := Fintype.ofFinite (NormCharacter F L)
  have hcard := (primeNormCharacter_card F L).trans hL
  have huniv : (Finset.univ : Finset (NormCharacter F L)) = {1, omega} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hx : x = 1
    · exact Or.inl hx
    · exact Or.inr (((Nat.card_eq_two_iff' (1 : NormCharacter F L)).mp hcard).unique
        hx homega)
  let gamma : AdmissibleGamma F (trivialQuasiCharData F) psi :=
    Classical.choice AdmissibleGamma.exists_admissible
  have hone : localConstant F 1 psi.character = 1 :=
    (localConstant_isDeltaFinite F (trivialQuasiCharData F) psi gamma).trans
      (delta_trivial_character F psi gamma)
  unfold stableComparisonFactor
  rw [huniv, Finset.prod_pair homega.symm]
  change _ = _
  simp only [show (1 : NormCharacter F L).1 = 1 from rfl, hone, one_mul]

end Edge

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

/-- Exhaust the three consecutive conductor ranges after constructing the
normalization and the actual height. No chart or height is assumed. -/
private theorem comparison_of_ramified
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (U E : IntermediateField F K)
    (hU : Module.finrank F U = 2) (hE : Module.finrank F E = 2)
    (hsup : U ⊔ E = ⊤) (hchar : residueCharacteristic F = 2)
    (hunr : ramificationIndex F U = 1) (hram : ramificationIndex F E ≠ 1)
    (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
    (hcomp : normQuasiChar U K thetaU = normQuasiChar E K thetaE)
    (hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F,
      normQuasiChar F K lambda = normQuasiChar U K thetaU)
    (psi : ContinuousAddChar F) (hpsi : psi ≠ 1) :
    Characters.inducingFactor Nat.prime_two hG psi U hU thetaU =
      Characters.inducingFactor Nat.prime_two hG psi E hE thetaE := by
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F U
    (Basic.intermediateField_tower_compatible Nat.prime_two hG U hU).2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E
    (Basic.intermediateField_tower_compatible Nat.prime_two hG E hE).2.2.2.2.2.2.2.2.2.2.2.1
  have hres := totallyRamified_of_ramified F E hram
  have hramTwo : ramificationIndex F E = 2 := by
    have he := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa only [hE, hres, mul_one] using he.symm
  let P := wildPrimeCyclicPreparation F E hram (by
    change residueCharacteristic F ∣ ramificationIndex F E
    rw [hchar, hramTwo])
  obtain ⟨eta, heta, _⟩ := (Nat.card_eq_two_iff' (1 : NormCharacter F U)).mp
    ((primeNormCharacter_card F U).trans hU)
  obtain ⟨tau, htau, _⟩ := (Nat.card_eq_two_iff' (1 : NormCharacter F E)).mp
    ((primeNormCharacter_card F E).trans hE)
  let psiF := canonicalLocalAddCharData F psi hpsi
  let tauData : LocalQuasiCharData F := ⟨tau.1, P.t + 1,
    ramifiedNormCharacter_conductor F E P.ht P.hres P.piK P.hpiK P.hgen tau htau⟩
  obtain ⟨alpha, hconductor, hchart⟩ := minimal_normalization F tauData psiF P.htpos rfl
  let Psi := scaleAddCharData F psiF alpha
  have hPsi : IsAdditiveConductor F Psi.character (-((P.t + 1 : ℕ) : ℤ)) :=
    hconductor ▸ Psi.isConductor
  obtain ⟨sigma, c, d, hsigma, hc, hd, hdc, hconj, hc0, hcTrace⟩ :=
    minimal_generator F U hunr hU hchar
  obtain ⟨_, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, hcondU, hcondE, _⟩ :=
    twist hG U E hU hE hunr P.t P.ht P.htpos P.hres tau htau Psi.character hPsi
      hchart sigma hsigma c hc d hd hdc hconj thetaU thetaE hcomp hprimitive
  change stableComparisonFactor F U thetaU psiF.character =
    stableComparisonFactor F E thetaE psiF.character
  by_cases hzero : h = 0
  · rw [comparisonFactor_quadratic F U hU eta heta thetaU psiF,
      comparisonFactor_quadratic F E hE tau htau thetaE psiF]
    exact minimal hG U E hU hE hsup hchar hunr P.t P.ht P.htpos P.hres eta heta tau htau
      (canonicalLocalQuasiCharData U thetaU) (canonicalLocalQuasiCharData E thetaE)
      (by have := (canonicalLocalQuasiCharData U thetaU).isConductor.unique hcondU
          simpa only [hzero, add_zero] using this)
      (by have := (canonicalLocalQuasiCharData E thetaE).isConductor.unique hcondE
          simpa only [hzero, mul_zero, add_zero] using this)
      (normQuasiChar U K thetaU) rfl hcomp.symm hprimitive psiF
  · by_cases hcritical : h ≤ P.t
    · rw [comparisonFactor_quadratic F U hU eta heta thetaU psiF,
        comparisonFactor_quadratic F E hE tau htau thetaE psiF]
      let psiU := canonicalLocalAddCharData U (tracePullbackAddChar F U psi)
        (Basic.tracePullbackAddChar_ne_one F U psi hpsi)
      let psiE := canonicalLocalAddCharData E (tracePullbackAddChar F E psi)
        (Basic.tracePullbackAddChar_ne_one F E psi hpsi)
      exact criticalComparison hchar hG U E hU hE hunr P.t h (Nat.pos_of_ne_zero hzero)
        hcritical P.ht P.hres eta heta tau htau psiF psiU psiE rfl rfl alpha hconductor
        hchart sigma hsigma ⟨c, (mem_lattice_zero_iff F).mp hc0⟩ hc hcTrace d hd hdc hconj
        thetaU thetaE hcomp hprimitive hcondU
    · exact stable hG U E hU hE hunr P.t P.ht P.htpos P.hres tau htau Psi.character hPsi
        hchart sigma hsigma c hc d hd hdc hconj thetaU thetaE hcomp hprimitive h hcondU
        (by omega) psi psiF.conductor psiF.isConductor


/-- Inertia acts trivially on every unramified intermediate field. -/
private theorem inertia_le_fixing_unramified
    (L : IntermediateField F K) [IsGalois F L]
    (hunr : ramificationIndex F L = 1) :
    Ramification.inertiaSubgroup (F := F) (K := K) ≤ L.fixingSubgroup := by
  letI : Module.Finite (ResidueField F) (ResidueField L) := Module.Finite.of_finite
  letI : IsGalois (ResidueField F) (ResidueField L) := GaloisField.instIsGaloisOfFinite
  have hinj : Function.Injective (Ramification.residueAction (F := F) (K := L)) := by
    apply ((Nat.bijective_iff_surjective_and_card _).mpr
      ⟨Ramification.residueAction_surjective, ?_⟩).1
    rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
      ← residueDegree_eq_finrank_residueField,
      finrank_eq_ramificationIndex_mul_residueDegree F L, hunr, one_mul]
  have hbot : lowerRamificationGroup F L 0 = ⊥ := by
    rw [← Ramification.inertiaSubgroup_eq_lowerRamificationGroup_zero]
    exact (Ramification.residueAction (F := F) (K := L)).ker_eq_bot hinj
  intro sigma hsigma
  have hrestrict : sigma.restrictNormal L ∈ lowerRamificationGroup F L 0 := by
    rw [mem_lowerRamificationGroup_iff_ord]
    intro x
    have hx := (mem_lowerRamificationGroup_iff_ord F K sigma 0).mp
      ((Ramification.inertiaSubgroup_eq_lowerRamificationGroup_zero (F := F) (K := K)) ▸ hsigma)
      (algebraMap (ringOfIntegers L) (ringOfIntegers K) x)
    change (1 : WithTop ℤ) ≤ ord K (sigma (algebraMap L K (x : L)) -
      algebraMap L K (x : L)) at hx
    rw [← sigma.restrictNormal_commutes L (x : L), ← map_sub, ord_algebraMap] at hx
    have hpos : (0 : WithTop ℤ) < ord L (sigma.restrictNormal L (x : L) - (x : L)) := by
      by_contra hn
      have hh := nsmul_nonpos (le_of_not_gt hn) (ramificationIndex L K)
      exact (not_le_of_gt (by norm_num : (0 : WithTop ℤ) < 1)) (hx.trans hh)
    generalize ord L (sigma.restrictNormal L (x : L) - (x : L)) = v at *
    cases v with
    | top => exact le_top
    | coe v =>
      exact_mod_cast (show (1 : ℤ) ≤ v from
        Int.add_one_le_iff.mpr (by exact_mod_cast hpos))
  rw [hbot, Subgroup.mem_bot] at hrestrict
  exact (IntermediateField.mem_fixingSubgroup_iff L sigma).mpr
    ((AlgEquiv.restrictNormal_eq_one_iff L sigma).mp hrestrict)

/-- A biquadratic local extension cannot be generated by two unramified
quadratic subfields: inertia would be trivial and the Galois group cyclic. -/
private theorem other_quadratic_ramified
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (U E : IntermediateField F K) [IsGalois F U] [IsGalois F E]
    (hsup : U ⊔ E = ⊤) (hunr : ramificationIndex F U = 1) :
    ramificationIndex F E ≠ 1 := by
  intro hunrE
  have hbot : Ramification.inertiaSubgroup (F := F) (K := K) = ⊥ := by
    apply le_antisymm _ bot_le
    have hh := le_inf (inertia_le_fixing_unramified U hunr)
      (inertia_le_fixing_unramified E hunrE)
    rwa [← IntermediateField.fixingSubgroup_sup, hsup,
      IntermediateField.fixingSubgroup_top] at hh
  have hinj : Function.Injective (Ramification.residueAction (F := F) (K := K)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hbot
  letI : Module.Finite (ResidueField F) (ResidueField K) := Module.Finite.of_finite
  letI : IsCyclic Gal(K/F) := isCyclic_of_injective
    (Ramification.residueAction (F := F) (K := K)) hinj
  letI : IsCyclic (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    isCyclic_of_surjective hG.some.toMonoidHom hG.some.surjective
  have hc := coprime_card_of_isCyclic_prod
    (Multiplicative (ZMod 2)) (Multiplicative (ZMod 2))
  norm_num [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at hc

/-- Distinct quadratic fields in the biquadratic extension generate it. -/
private theorem comparison_sup
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (U E : IntermediateField F K)
    (hU : Module.finrank F U = 2) (hE : Module.finrank F E = 2) (hne : U ≠ E) :
    U ⊔ E = ⊤ := by
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F U
    (Basic.intermediateField_tower_compatible Nat.prime_two hG U hU).2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E
    (Basic.intermediateField_tower_compatible Nat.prime_two hG E hE).2.2.2.2.2.2.2.2.2.2.2.1
  have hinf := inf_eq_bot_of_prime_degree Nat.prime_two U E hU hE hne
  have hdisjoint : U.LinearDisjoint E := IntermediateField.LinearDisjoint.of_inf_eq_bot hinf
  apply IntermediateField.eq_of_le_of_finrank_eq le_top
  rw [hdisjoint.finrank_sup, IntermediateField.finrank_top', hU, hE]
  exact (Basic.intermediateField_tower_compatible Nat.prime_two hG U hU).2.2.2.2.2.2.2.2.1.symm

/-- **Paper Theorem 10.20 (`D:UR:URall`).** Every primitive compatible pair
on an unramified quadratic field and any other quadratic intermediate field
has equal complete induction factors. There is no conductor restriction,
no chosen stationary data, and no restriction to unitary characters or to
one field characteristic. The actual full lower product includes the trivial
character. -/
theorem comparison
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (U E : IntermediateField F K)
    (hU : Module.finrank F U = 2) (hE : Module.finrank F E = 2) (hne : U ≠ E)
    (hchar : residueCharacteristic F = 2) (hunr : ramificationIndex F U = 1)
    (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
    (hcomp : normQuasiChar U K thetaU = normQuasiChar E K thetaE)
    (hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F,
      normQuasiChar F K lambda = normQuasiChar U K thetaU)
    (psi : ContinuousAddChar F) (hpsi : psi ≠ 1) :
    Characters.inducingFactor Nat.prime_two hG psi U hU thetaU =
      Characters.inducingFactor Nat.prime_two hG psi E hE thetaE := by
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F U
    (Basic.intermediateField_tower_compatible Nat.prime_two hG U hU).2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E
    (Basic.intermediateField_tower_compatible Nat.prime_two hG E hE).2.2.2.2.2.2.2.2.2.2.2.1
  have hsup := comparison_sup hG U E hU hE hne
  exact comparison_of_ramified hG U E hU hE hsup hchar hunr
    (other_quadratic_ramified hG U E hsup hunr) thetaU thetaE hcomp hprimitive psi hpsi

open private compatible_invariant from LanglandsSecondMainLemma.Characters.Conjugacy
open private unramified_normRange_ne_ramified from LanglandsSecondMainLemma.Ramification.NormSeparation

/-- The final paragraph of `D:UR:URall`: the given primitive pair supplies
an invariant upstairs character, which induces on every quadratic field.
The complete expression is independent of the field and of every inducing
choice, including two different choices on the same field. -/
theorem comparison_family
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (U E : IntermediateField F K)
    (hU : Module.finrank F U = 2) (hE : Module.finrank F E = 2) (hne : U ≠ E)
    (hchar : residueCharacteristic F = 2) (hunr : ramificationIndex F U = 1)
    (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
    (hcomp : normQuasiChar U K thetaU = normQuasiChar E K thetaE)
    (hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F,
      normQuasiChar F K lambda = normQuasiChar U K thetaU)
    (psi : ContinuousAddChar F) (hpsi : psi ≠ 1) :
    ∃ theta : ∀ (L : IntermediateField F K),
        Module.finrank F L = 2 → ContinuousQuasiChar L,
      (∀ (L : IntermediateField F K) (hL : Module.finrank F L = 2),
        normQuasiChar L K (theta L hL) = normQuasiChar U K thetaU) ∧
      (∀ (I J : IntermediateField F K)
          (hI : Module.finrank F I = 2) (hJ : Module.finrank F J = 2)
          (chiI : ContinuousQuasiChar I) (chiJ : ContinuousQuasiChar J),
        normQuasiChar I K chiI = normQuasiChar U K thetaU →
        normQuasiChar J K chiJ = normQuasiChar U K thetaU →
        Characters.inducingFactor Nat.prime_two hG psi I hI chiI =
          Characters.inducingFactor Nat.prime_two hG psi J hJ chiJ) := by
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F U
    (Basic.intermediateField_tower_compatible Nat.prime_two hG U hU).2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E
    (Basic.intermediateField_tower_compatible Nat.prime_two hG E hE).2.2.2.2.2.2.2.2.2.2.2.1
  have hinf := inf_eq_bot_of_prime_degree Nat.prime_two U E hU hE hne
  have hinv := compatible_invariant U E hinf thetaU thetaE
    (normQuasiChar U K thetaU) rfl hcomp.symm
  let P := primeCyclicPreparation F E
    (other_quadratic_ramified hG U E (comparison_sup hG U E hU hE hne) hunr)
  have hsep : Ramification.intermediateNormRange U ≠ Ramification.intermediateNormRange E :=
    unramified_normRange_ne_ramified Nat.prime_two hU hunr P.ht P.hres
  refine Characters.distinguishedComparisons_imply_family Nat.prime_two hG U E hU hE hsep
    (normQuasiChar U K thetaU) ?_ hprimitive psi hpsi ?_
  · intro sigma
    apply ContinuousMonoidHom.ext
    intro x
    exact hinv sigma.symm x
  · intro L hL hneL chiU chiL hcU hcL
    apply comparison hG U L hU hL (Ne.symm hneL) hchar hunr chiU chiL
      (hcU.trans hcL.symm) _ psi hpsi
    simpa only [hcU] using hprimitive


end
end LanglandsSecondMainLemma.Dyadic.UR
