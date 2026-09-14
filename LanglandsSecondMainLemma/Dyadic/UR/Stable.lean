import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Dyadic.StableComparison
import LanglandsSecondMainLemma.Dyadic.UR.Twist

/-!
# Stable unramified--ramified comparison

Paper Corollary 10.19 (`D:UR:URstable`). The actual realization from
`twist` supplies the minimal characters and their common base twist.
Conductor uniqueness identifies its height with the height in
`D:UR:conductors`. At `h ≥ T`, the base conductor is at least `2 * T`,
so the exact stable comparison applies, including every lower norm-character
factor. The stationary chart inputs below are the ambient choices of
`D:UR:tauchart` and `D:UR:dchoice`, as in the accepted realization theorem.
-/

namespace LanglandsSecondMainLemma.Dyadic.UR

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

/-- Every actual primitive compatible UR pair of height `h ≥ t + 1`
satisfies the complete Second Main comparison. The minimal pair, its
unramified adjustment, and the base twist are constructed by `twist`.
Only the conductor on `U` is needed to specify the height: realization
also proves the conductor on `E`. The additive character for the comparison
is arbitrary and nontrivial, specified by its exact integer conductor.
There is no unitarity or field-characteristic restriction. -/
theorem stable
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (U E : IntermediateField F K)
    (hU : Module.finrank F U = 2) (hE : Module.finrank F E = 2) :
    letI := Basic.intermediateFieldValuativeRel U
    letI := Basic.intermediateFieldTopology U
    letI := Basic.intermediateField_localField U
    letI := Basic.intermediateField_lowerValuativeExtension U
    letI := Basic.intermediateField_upperValuativeExtension U
    letI := Basic.intermediateFieldValuativeRel E
    letI := Basic.intermediateFieldTopology E
    letI := Basic.intermediateField_localField E
    letI := Basic.intermediateField_lowerValuativeExtension E
    letI := Basic.intermediateField_upperValuativeExtension E
    letI := PrimeCyclicExtension.ofCyclicPrimeExtension F U
      (Basic.intermediateField_tower_compatible Nat.prime_two hG U hU).2.2.2.2.2.2.2.2.2.2.2.1
    letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E
      (Basic.intermediateField_tower_compatible Nat.prime_two hG E hE).2.2.2.2.2.2.2.2.2.2.2.1
    ∀ (_hunr : ramificationIndex F U = 1)
      (t : ℕ) (_ht : PrimeCyclicExtension.IsLowerBreak F E t)
      (_htpos : 0 < t) (_hres : residueDegree F E = 1)
      (tau : NormCharacter F E) (_htau : tau ≠ 1)
      (Psi : ContinuousAddChar F)
      (_hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
      (_hchart : ∀ (x : F) (hx : x ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
        tau.1 (principalUnitOf F (t / 2) (-x) (neg_mem_lattice F hx)) = Psi x)
      (sigma : Gal(U/F)) (_hsigma : sigma ≠ 1)
      (c : F) (_hc : ord F c = 0) (d : U) (_hd : ord U d = 0)
      (_hdc : d ^ 2 - d = algebraMap F U c) (_hconj : sigma d = 1 - d)
      (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
      (_hcomp : normQuasiChar U K thetaU = normQuasiChar E K thetaE)
      (_hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F,
        normQuasiChar F K lambda = normQuasiChar U K thetaU)
      (h : ℕ) (_hheight : IsMultiplicativeConductor U thetaU (t + 1 + h))
      (_hstable : t + 1 ≤ h)
      (psi : ContinuousAddChar F) (npsi : ℤ)
      (_hpsi : IsAdditiveConductor F psi npsi),
      stableComparisonFactor F U thetaU psi = stableComparisonFactor F E thetaE psi := by
  letI := Basic.intermediateFieldValuativeRel U
  letI := Basic.intermediateFieldTopology U
  letI := Basic.intermediateField_localField U
  letI := Basic.intermediateField_lowerValuativeExtension U
  letI := Basic.intermediateField_upperValuativeExtension U
  letI := Basic.intermediateFieldValuativeRel E
  letI := Basic.intermediateFieldTopology E
  letI := Basic.intermediateField_localField E
  letI := Basic.intermediateField_lowerValuativeExtension E
  letI := Basic.intermediateField_upperValuativeExtension E
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F U
    (Basic.intermediateField_tower_compatible Nat.prime_two hG U hU).2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E
    (Basic.intermediateField_tower_compatible Nat.prime_two hG E hE).2.2.2.2.2.2.2.2.2.2.2.1
  intro hunr t ht htpos hres tau htau Psi hPsi hchart sigma hsigma c hc d hd hdc hconj
    thetaU thetaE hcomp hprimitive h hheight hstable psi npsi hpsi
  have hram : ramificationIndex F E = 2 := by
    have he := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa only [hE, hres, mul_one] using he.symm
  have hne : U ≠ E := by
    intro heq
    subst E
    omega
  obtain ⟨chiU, chiE, lambda, nu, h', hcU, _hcE, _hnu, hcE', hc0, hp0,
      _hcomm, _hchartU, _hchartE, hrealU, hrealE, hthetaU, _hthetaE, hlambda, _hlow⟩ :=
    twist hG U E hU hE hunr t ht htpos hres tau htau Psi hPsi hchart
      sigma hsigma c hc d hd hdc hconj thetaU thetaE hcomp hprimitive
  have heighth : h' = h := by have := hthetaU.unique hheight; omega
  subst h'
  have hlambda' := hlambda (by omega : 0 < h)
  -- The full lower product is itself a norm character. Its conductor is
  -- zero on U/F and at most T on E/F, which suffices for all stable bounds.
  letI := primeCyclicNormCharacter_finite F U
  letI := primeCyclicNormCharacter_finite F E
  letI := normCharacterFintype F U
  letI := normCharacterFintype F E
  let omegaU : NormCharacter F U := ∏ mu : NormCharacter F U, mu
  let omegaE : NormCharacter F E := ∏ mu : NormCharacter F E, mu
  have hdU : IsMultiplicativeConductor F
      (Characters.intermediateNormCharacterProduct Nat.prime_two hG U hU) 0 :=
    unramifiedNormCharacter_conductor F U hunr omegaU
  let delta := multiplicativeConductorExponent F
    (Characters.intermediateNormCharacterProduct Nat.prime_two hG E hE)
  have hdE : IsMultiplicativeConductor F
      (Characters.intermediateNormCharacterProduct Nat.prime_two hG E hE) delta :=
    multiplicativeConductorExponent_isConductor F _
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have hdelta : delta ≤ t + 1 := hdE.minimal _
    (ramifiedNormCharacter_trivialOn_break_succ F E ht hres pi hpi hgen omegaE)
  obtain ⟨bF, hbF, hfactorU, hfactorE, hcomparison⟩ :=
    stableComparison hG U E hU hE hne chiU (chiE * nu.1)
      (normQuasiChar U K chiU) rfl hc0.symm hp0 lambda psi
      (t + 1) (t + 1) 0 delta (t + 1 + h) npsi hcU hcE' hdU hdE hlambda' hpsi
      (by omega) (by intro hramU; exact (hramU hunr).elim)
      (by intro _; omega) (by intro _; omega) (by intro hunrE; omega)
  simpa only [← hrealU, ← hrealE] using hcomparison

end

end LanglandsSecondMainLemma.Dyadic.UR
