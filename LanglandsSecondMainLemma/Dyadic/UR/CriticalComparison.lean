import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Dyadic.UR.UnramifiedSum
import LanglandsSecondMainLemma.Dyadic.UR.RamifiedSum

/-!
# Every positive critical unramified--ramified row

Paper `D:UR:criticalcomplete`. The assembly uses the actual ratio and the
complete residual factors. Whole-ideal duality transports the base chart to
the representative retained by that ratio.
-/

namespace LanglandsSecondMainLemma.Dyadic.UR
noncomputable section
open LanglandsFirstMainLemma

/-- Exact critical elements exist at every integer order. -/
private theorem criticalComparison_element (L : Type*) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] (n : ℕ) :
    ∃ delta : Lˣ, ord L (delta : L) = ((n : ℕ) : WithTop ℤ) := by
  obtain ⟨z, hz⟩ := exists_ord_eq L (n : ℤ)
  exact ⟨Units.mk0 z ((ord_ne_top_iff L).mp (by rw [hz]; simp)), hz⟩

/-- Nonvanishing of the canonical constant with an exact additive conductor. -/
private theorem criticalComparison_nonzero (L : Type*) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (theta : ContinuousQuasiChar L) (psi : LocalAddCharData L) :
    localConstant L theta psi.character ≠ 0 := by
  let chi := canonicalLocalQuasiCharData L theta
  let gamma : AdmissibleGamma L chi psi := Classical.choice AdmissibleGamma.exists_admissible
  change localConstant L chi.character psi.character ≠ 0
  rw [localConstant_isDeltaFinite L chi psi gamma, deltaFinite]
  exact mul_ne_zero (Units.ne_zero _) (phase_ne_zero _)

section ChartTransport
variable (F U E : Type) [Field F] [Field U] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

/-- Recover the base chart for the ratio's actual `x`. The auxiliary `y`
only supplies a proved chart; whole-ideal duality identifies its coefficient
class with that of `x`. No exact norm choice is replaced without proof. -/
private theorem criticalComparison_baseChart
    (hunr : ramificationIndex F U = 1) (hdegree : Module.finrank F E = 2)
    {t h : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hh : h ≤ t)
    (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
    (Psi : LocalAddCharData F) (hPsi : Psi.conductor = -((t + 1 : ℕ) : ℤ))
    (c : F) (hc : c ∈ lattice F 0) (d : U) (hd : d ∈ lattice U 0)
    (x : E) (hx : ord E x = ((-(h : ℤ)) : WithTop ℤ))
    (R : ConjugatedNormData F U E thetaU thetaE Psi.character c d x t h)
    (lambda : ContinuousQuasiChar F) (y : E)
    (hybase : ∀ (z : F) (hz : z ∈ lattice F (((t + h) / 2 + 1 : ℕ) : ℤ)),
      lambda (principalUnitOf F ((t + h) / 2) (-z) (neg_mem_lattice F hz)) =
        Psi.character (norm F E y * z))
    (hychart : ∀ (z : U) (hz : z ∈ lattice U (((t + h) / 2 + 1 : ℕ) : ℤ)),
      thetaU (principalUnitOf U ((t + h) / 2) (-z) (neg_mem_lattice U hz)) =
        tracePullbackAddChar F U Psi.character
          ((algebraMap F U (norm F E y) + d ^ 2) * z)) :
    ∀ (z : F) (hz : z ∈ lattice F (((t + h) / 2 + 1 : ℕ) : ℤ)),
      lambda (principalUnitOf F ((t + h) / 2) (-z) (neg_mem_lattice F hz)) =
        Psi.character (norm F E x * z) := by
  let PsiU : LocalAddCharData U := ⟨tracePullbackAddChar F U Psi.character,
    -((t + 1 : ℕ) : ℤ), R.additiveConductorU⟩
  have hdiff : (R.ZU : U) - (algebraMap F U (norm F E y) + d ^ 2) ∈
      lattice U (((t + 1 : ℕ) : ℤ) - (((t + h) / 2 + 1 : ℕ) : ℤ)) := by
    apply (lamprechtAnnihilatorLeft U PsiU (Γ := 1)
      (by simp [PsiU])).mp
    intro z hz
    have hs := R.stationaryU ⟨z, hz⟩
    have hu : (positiveUnitOfLattice U (by omega : 0 < (t + h) / 2 + 1)
        (-⟨z, hz⟩) : Uˣ) =
        principalUnitOf U ((t + h) / 2) (-z) (neg_mem_lattice U hz) := by
      apply Units.ext
      simp only [coe_positiveUnitOfLattice, coe_principalUnitOf, Submodule.coe_neg]
    change thetaU _ = PsiU.character ((R.ZU : U) * z) at hs
    rw [hu, hychart z hz] at hs
    simp only [div_one, sub_mul]
    change PsiU.character ((R.ZU : U) * z -
      (algebraMap F U (norm F E y) + d ^ 2) * z) = 1
    have hsub (a b : U) : PsiU.character (a - b) =
        PsiU.character a / PsiU.character b := PsiU.character.toAddChar.map_sub_eq_div a b
    rw [hsub, ← hs, div_self']
  have herr := (conjugatedNorm_error_bounds F U E hunr hdegree ht hres hh
    x hx c hc d hd).1
  rw [← R.errorU] at herr
  have hdiffU : algebraMap F U (norm F E x - norm F E y) ∈
      lattice U (((t + 1 : ℕ) : ℤ) - (((t + h) / 2 + 1 : ℕ) : ℤ)) := by
    convert sub_mem_lattice U hdiff herr using 1
    rw [map_sub]
    ring
  have hdiffF : norm F E x - norm F E y ∈
      lattice F (((t + 1 : ℕ) : ℤ) - (((t + h) / 2 + 1 : ℕ) : ℤ)) := by
    rw [mem_lattice, ord_algebraMap, hunr, one_nsmul] at hdiffU
    exact hdiffU
  intro z hz
  rw [hybase z hz]
  symm
  apply eq_of_div_eq_one
  have hsub (a b : F) : Psi.character (a - b) =
      Psi.character a / Psi.character b := Psi.character.toAddChar.map_sub_eq_div a b
  rw [← hsub]
  apply Psi.isConductor.trivial
  rw [← sub_mul, hPsi, neg_neg]
  convert mul_mem_lattice F hdiffF hz using 1
  congr 1
  omega
end ChartTransport

section ActualPair
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Every positive critical row** (`D:UR:criticalcomplete`).

For the genuine primitive compatible pair, the canonical local constants
including both lower quadratic factors agree. The choices `alpha`, `c`, and
`d` are precisely the ambient choices of `D:UR:tauchart` and `D:UR:dchoice`.
The norm representatives, base twist, and residual cancellations are proved
internally, in both field characteristics and for nonunitary characters. -/
theorem criticalComparison
    (hchar : residueCharacteristic F = 2)
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
    ∀ (_hunr : ramificationIndex F U = 1)
      (t h : ℕ) (_hhpos : 0 < h) (_hh : h ≤ t)
      (_ht : PrimeCyclicExtension.IsLowerBreak F E t) (_hres : residueDegree F E = 1)
      (eta : NormCharacter F U) (_heta : eta ≠ 1)
      (tau : NormCharacter F E) (_htau : tau ≠ 1)
      (psiF : LocalAddCharData F) (psiU : LocalAddCharData U) (psiE : LocalAddCharData E)
      (_hpsiU : psiU.character = tracePullbackAddChar F U psiF.character)
      (_hpsiE : psiE.character = tracePullbackAddChar F E psiF.character)
      (alpha : Fˣ)
      (_hPsi : (scaleAddCharData F psiF alpha).conductor = -((t + 1 : ℕ) : ℤ))
      (_htauchart : ∀ (z : F) (hz : z ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
        tau.1 (principalUnitOf F (t / 2) (-z) (neg_mem_lattice F hz)) =
          (scaleAddCharData F psiF alpha).character z)
      (sigma : Gal(U/F)) (_hsigma : sigma ≠ 1)
      (c : ringOfIntegers F) (_hc : ord F (c : F) = 0)
      (_htracec : (@absoluteTraceTwo (ResidueField F) _ (ringChar.of_eq hchar))
        (residueMap F c) = 1)
      (d : U) (_hd : ord U d = 0)
      (_hdc : d ^ 2 - d = algebraMap F U (c : F)) (_hconj : sigma d = 1 - d)
      (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
      (_hcomp : normQuasiChar U K thetaU = normQuasiChar E K thetaE)
      (_hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F,
        normQuasiChar F K lambda = normQuasiChar U K thetaU)
      (_hcondU : IsMultiplicativeConductor U thetaU (t + 1 + h)),
      localConstant U thetaU psiU.character * localConstant F eta.1 psiF.character =
        localConstant E thetaE psiE.character * localConstant F tau.1 psiF.character := by
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
  intro hunr t h hhpos hh ht hres eta heta tau htau psiF psiU psiE
    hpsiU hpsiE alpha hPsi htauchart sigma hsigma c hc htracec d hd hdc hconj
    thetaU thetaE hcomp hprimitive hcondU
  have dataE := Basic.intermediateField_tower_compatible Nat.prime_two hG E hE
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E dataE.2.2.2.2.2.2.2.2.2.2.2.1
  let Psi := scaleAddCharData F psiF alpha
  have hPsiData : IsAdditiveConductor F Psi.character (-((t + 1 : ℕ) : ℤ)) := by
    rw [← hPsi]
    exact Psi.isConductor
  have hrepresentatives :
      IsMultiplicativeConductor E thetaE (t + 1 + 2 * h) ∧
      ∃ x : E, ord E x = ((-(h : ℤ)) : WithTop ℤ) ∧
      ∃ R : ConjugatedNormData F U E thetaU thetaE Psi.character (c : F) d x t h,
        CriticalRatioIdentity F U E eta tau thetaU thetaE psiF psiU psiE alpha
          (c : F) d x t h R ∧
        ((t + 1 + h) % 2 = 1 →
          UnramifiedSumIdentity F U (canonicalLocalQuasiCharData U thetaU) psiU
            (Units.map (algebraMap F U).toMonoidHom alpha) R.ZU) := by
    by_cases hodd : (t + 1 + h) % 2 = 1
    · obtain ⟨hcondE, x, hx, R, hratio, hsum⟩ := unramifiedSum hchar hG U E hU hE
        hunr t h hhpos hh hodd ht hres eta heta tau htau psiF psiU psiE hpsiU hpsiE
        alpha hPsi htauchart sigma hsigma c hc htracec d hd hdc hconj thetaU thetaE
        hcomp hprimitive hcondU
      exact ⟨hcondE, x, hx, R, hratio, fun _ => hsum⟩
    · obtain ⟨hcondE, x, hx, R, hratio⟩ := criticalRatio hchar hG U E hU hE
        hunr t h hhpos hh ht hres eta heta tau htau psiF psiU psiE hpsiU hpsiE
        alpha hPsi htauchart sigma hsigma c hc htracec d hd hdc hconj thetaU thetaE
        hcomp hprimitive hcondU
      exact ⟨hcondE, x, hx, R, hratio, fun ho => (hodd ho).elim⟩
  obtain ⟨hcondE, x, hx, R, hratio, hsum⟩ := hrepresentatives
  let chiU := canonicalLocalQuasiCharData U thetaU
  let chiE := canonicalLocalQuasiCharData E thetaE
  let chiTau := canonicalLocalQuasiCharData F tau.1
  have hmU : chiU.conductor = t + 1 + h := chiU.isConductor.unique hcondU
  have hmE : chiE.conductor = t + 1 + 2 * h := chiE.isConductor.unique hcondE
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have hmTau : chiTau.conductor = t + 1 := chiTau.isConductor.unique
    (ramifiedNormCharacter_conductor F E ht hres pi hpi hgen tau htau)
  obtain ⟨delta, hdelta⟩ := criticalComparison_element F (chiU.conductor / 2)
  let deltaU := Units.map (algebraMap F U).toMonoidHom delta
  have hdeltaU : ord U (deltaU : U) = ((chiU.conductor / 2 : ℕ) : WithTop ℤ) := by
    change ord U (algebraMap F U (delta : F)) = _
    rw [ord_algebraMap, hunr, one_nsmul, hdelta]
  obtain ⟨deltaE, hdeltaE⟩ := criticalComparison_element E (chiE.conductor / 2)
  obtain ⟨deltaTau, hdeltaTau⟩ := criticalComparison_element F (chiTau.conductor / 2)
  obtain ⟨largeU, largeE, largeTau, _, _, hr⟩ :=
    hratio deltaU deltaE deltaTau hdeltaU hdeltaE hdeltaTau
  have hgU : criticalResidualFactor U chiU psiU
      (Units.map (algebraMap F U).toMonoidHom alpha) R.ZU largeU deltaU hdeltaU = 1 := by
    by_cases heven : chiU.conductor % 2 = 0
    · simp only [criticalResidualFactor, dif_pos heven]
    · obtain ⟨_, _, _, _, hs⟩ := hsum (by omega) delta hdelta
      exact hs
  have hnU := criticalComparison_nonzero U thetaU psiU
  have hnEta := criticalComparison_nonzero F eta.1 psiF
  have hnE := criticalComparison_nonzero E thetaE psiE
  have hnTau := criticalComparison_nonzero F tau.1 psiF
  have hnratio := div_ne_zero (mul_ne_zero hnU hnEta) (mul_ne_zero hnE hnTau)
  have hgTau : criticalResidualFactor F chiTau psiF alpha 1 largeTau deltaTau hdeltaTau ≠ 0 := by
    intro hz
    apply hnratio
    rw [hr, hz, mul_zero, div_zero]
  have hgETau : criticalResidualFactor E chiE psiE
      (Units.map (algebraMap F E).toMonoidHom alpha) R.ZE largeE deltaE hdeltaE *
      criticalResidualFactor F chiTau psiF alpha 1 largeTau deltaTau hdeltaTau = 1 := by
    by_cases heven : (t + 1) % 2 = 0
    · have hevE : chiE.conductor % 2 = 0 := by omega
      have hevTau : chiTau.conductor % 2 = 0 := by omega
      simp only [criticalResidualFactor, dif_pos hevE, dif_pos hevTau, mul_one]
    · obtain ⟨chiU0, chiE0, lambda, nu, k, _, _, _, _, _, _, _, hmodelU, hmodelE,
          hrealU, hrealE, hcondU', hcondE', hlambda, hlambdazero⟩ :=
        twist hG U E hU hE hunr t ht (by omega) hres tau htau Psi.character hPsiData
          htauchart sigma hsigma (c : F) hc d hd hdc hconj thetaU thetaE hcomp hprimitive
      have hk : k = h := by have heq := hcondU'.unique hcondU; omega
      subst k
      obtain ⟨y, hybase, _, _, _, hychart, _⟩ :=
        coefficients_exists F U E hunr hU hE ht (by omega) hres hh tau htau
          Psi.character hPsiData htauchart (c : F) d chiU0 thetaU (chiE0 * nu.1)
          thetaE lambda hmodelU hmodelE hrealU hrealE hcondU hcondE hlambda hlambdazero
      have hc0 : (c : F) ∈ lattice F 0 := (mem_lattice_zero_iff F).mpr c.property
      have hd0 : d ∈ lattice U 0 := (mem_lattice U).mpr (by rw [hd]; rfl)
      have hbase := criticalComparison_baseChart F U E hunr hE ht hres hh thetaU thetaE
        Psi hPsi (c : F) hc0 d hd0 x hx R lambda y hybase hychart
      obtain ⟨_, _, hs⟩ := ramifiedSum F U E hchar ht hres hE hhpos hh
        (Nat.odd_iff.mpr (by omega)) tau htau psiF psiE hpsiE alpha hPsi htauchart
        (c : F) hc0 d x hx thetaU (chiE0 * nu.1) thetaE lambda hmodelE hrealE
        hbase hcondE R deltaE deltaTau hdeltaE hdeltaTau
      rw [hs, inv_mul_cancel₀ hgTau]
  apply (div_eq_one_iff_eq (mul_ne_zero hnE hnTau)).mp
  rw [hr, hgU, hgETau, div_one]
end ActualPair

end
end LanglandsSecondMainLemma.Dyadic.UR
