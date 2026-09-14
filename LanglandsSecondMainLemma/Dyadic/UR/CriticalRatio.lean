import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Dyadic.UR.TraceParity
import LanglandsSecondMainLemma.Dyadic.UR.ConjugatedNorm

/-!
# Reduction to the actual critical residual factors

Paper Proposition `D:UR:criticalratio`, equations `D:UR:newratio`.
The critical elements remain arbitrary, so subsequent computations can use
their specified uniformizers. The odd factors retain the full affine sum.
The elementary factor is evaluated using the actual corrected restriction,
the conductor-zero formula, and `traceParity`.
-/

namespace LanglandsSecondMainLemma.Dyadic.UR

noncomputable section
open LanglandsFirstMainLemma

section Residual
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- The full residual factor for a specified critical element. Unlike a
chosen-scale wrapper, this permits the base-field critical element used in
`D:UR:resU`. In even conductor it is literally one. -/
def criticalResidualFactor
    (theta : LocalQuasiCharData L) (psi : LocalAddCharData L)
    (alpha Z : Lˣ) (hlarge : 1 < theta.conductor)
    (delta : Lˣ)
    (hdelta : ord L (delta : L) = ((theta.conductor / 2 : ℕ) : WithTop ℤ)) : ℂ :=
  if heven : theta.conductor % 2 = 0 then 1 else
    Stationary.normalizedResidualFactor L theta psi alpha Z (theta.conductor / 2)
      (by omega) hlarge delta hdelta

/-- Insert the specified critical element in the two parity clauses of the
accepted normalized Lamprecht formula. -/
private theorem criticalRatio_factor
    (theta : LocalQuasiCharData L) (psi : LocalAddCharData L)
    (alpha Z : Lˣ) (hlarge : 1 < theta.conductor)
    (hZ : ord L (Z : L) =
      ((-(scaleAddCharData L psi alpha).conductor - (theta.conductor : ℤ)) : WithTop ℤ))
    (hstationary : Stationary.IsNormalizedStationaryCoefficientAtDepth L theta
      (scaleAddCharData L psi alpha) Z
      (theta.conductor / 2 + theta.conductor % 2) (by omega))
    (delta : Lˣ)
    (hdelta : ord L (delta : L) = ((theta.conductor / 2 : ℕ) : WithTop ℤ)) :
    localConstant L theta.character psi.character =
      (theta.character ((-alpha * Z)⁻¹) : ℂ) *
        ((scaleAddCharData L psi alpha).character (-(Z : L)) : ℂ) *
        criticalResidualFactor L theta psi alpha Z hlarge delta hdelta := by
  have hf := Stationary.normalizedFactor L theta psi alpha Z
    (theta.conductor / 2) (theta.conductor % 2) (by omega) (by omega)
    hlarge hZ hstationary
  by_cases heven : theta.conductor % 2 = 0
  · simpa only [criticalResidualFactor, dif_pos heven, mul_one] using hf.1 heven
  · exact (hf.2 (by omega) delta hdelta).trans (by
      simp only [criticalResidualFactor, dif_neg heven])
end Residual

section Unramified
variable (F U : Type*) [Field F] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U]

/-- Evaluate the combined unramified factor without restricting the integer
additive conductor: `Gamma / (-alpha⁻¹)` has order exactly `-T`. -/
private theorem criticalRatio_unramified
    (hunr : ramificationIndex F U = 1) (hdegree : Module.finrank F U = 2)
    (eta : NormCharacter F U) (heta : eta ≠ 1)
    (psi : LocalAddCharData F) (alpha : Fˣ) (T : ℕ)
    (hPsi : (scaleAddCharData F psi alpha).conductor = -(T : ℤ)) :
    localConstant F eta.1 psi.character / (eta.1 (-alpha⁻¹) : ℂ) = (-1 : ℂ) ^ T := by
  let chi := canonicalLocalQuasiCharData F eta.1
  have hchi : chi.conductor = 0 :=
    chi.isConductor.unique (unramifiedNormCharacter_conductor F U hunr eta)
  let Gamma : AdmissibleGamma F chi psi :=
    Classical.choice (AdmissibleGamma.exists_admissible (F := F))
  have hgamma : ord F ((Gamma : Fˣ) : F) = (psi.conductor : WithTop ℤ) := by
    simpa only [hchi, Nat.cast_zero, zero_add] using Gamma.property
  let c0 : Fˣ := -alpha⁻¹
  have hord : ord F (((Gamma : Fˣ) / c0 : Fˣ) : F) =
      ((-(T : ℤ)) : WithTop ℤ) := by
    simp only [Units.val_div_eq_div_val, c0, Units.val_neg, Units.val_inv_eq_inv_val,
      ord_div, ord_neg, ord_inv, hgamma, ord_coe_eq_unitOrder]
    rw [scaleAddCharData_conductor] at hPsi
    norm_cast
    omega
  have hsign := conjugatedNorm_unramified_sign F U hunr hdegree eta heta
    ((Gamma : Fˣ) / c0) T hord
  change localConstant F chi.character psi.character / (eta.1 c0 : ℂ) = _
  rw [localConstant_isDeltaFinite F chi psi Gamma,
    deltaFinite_conductor_zero F chi hchi psi Gamma]
  simpa only [map_div, Units.val_div_eq_div_val, chi,
    canonicalLocalQuasiCharData_character] using hsign
end Unramified

section TraceScaling
variable (F L : Type*) [Field F] [Field L]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra F L] [ValuativeExtension F L] [Module.Finite F L]

/-- Scaling commutes with the actual trace pullback. -/
private theorem criticalRatio_traceScale
    (psiF : LocalAddCharData F) (psiL : LocalAddCharData L)
    (hpsi : psiL.character = tracePullbackAddChar F L psiF.character)
    (alpha : Fˣ) :
    (scaleAddCharData L psiL (Units.map (algebraMap F L).toMonoidHom alpha)).character =
      tracePullbackAddChar F L (scaleAddCharData F psiF alpha).character := by
  ext z
  simp only [scaleAddCharData_character_apply, hpsi, tracePullbackAddChar_apply,
    Units.coe_map]
  congr 2
  change trace F L (algebraMap F L (alpha : F) * z) = (alpha : F) * trace F L z
  simpa only [smul_eq_mul, Algebra.smul_def, Algebra.algebraMap_self] using (trace F L).map_smul (alpha : F) z
end TraceScaling

section Representatives
variable (F U E : Type) [Field F] [Field U] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]

/-- The two exact ratio equalities and the intervening prefactor evaluation,
for every choice of the three critical elements. This transparent proposition
keeps the complete residual sums and the canonical local constants visible. -/
def CriticalRatioIdentity
    (eta : NormCharacter F U) (tau : NormCharacter F E)
    (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
    (psiF : LocalAddCharData F) (psiU : LocalAddCharData U) (psiE : LocalAddCharData E)
    (alpha : Fˣ) (c : F) (d : U) (x : E) (t h : ℕ)
    (R : ConjugatedNormData F U E thetaU thetaE
      (scaleAddCharData F psiF alpha).character c d x t h) : Prop :=
  ∀ (deltaU : Uˣ) (deltaE : Eˣ) (deltaTau : Fˣ)
    (hdeltaU : ord U (deltaU : U) =
      (((canonicalLocalQuasiCharData U thetaU).conductor / 2 : ℕ) : WithTop ℤ))
    (hdeltaE : ord E (deltaE : E) =
      (((canonicalLocalQuasiCharData E thetaE).conductor / 2 : ℕ) : WithTop ℤ))
    (hdeltaTau : ord F (deltaTau : F) =
      (((canonicalLocalQuasiCharData F tau.1).conductor / 2 : ℕ) : WithTop ℤ)),
  let chiU := canonicalLocalQuasiCharData U thetaU
  let chiE := canonicalLocalQuasiCharData E thetaE
  let chiTau := canonicalLocalQuasiCharData F tau.1
  ∃ (largeU : 1 < chiU.conductor) (largeE : 1 < chiE.conductor)
    (largeTau : 1 < chiTau.conductor),
  let gU := criticalResidualFactor U chiU psiU (Units.map (algebraMap F U).toMonoidHom alpha)
    R.ZU largeU deltaU hdeltaU
  let gE := criticalResidualFactor E chiE psiE (Units.map (algebraMap F E).toMonoidHom alpha)
    R.ZE largeE deltaE hdeltaE
  let gTau := criticalResidualFactor F chiTau psiF alpha 1 largeTau deltaTau hdeltaTau
  let ratio := localConstant U thetaU psiU.character * localConstant F eta.1 psiF.character /
    (localConstant E thetaE psiE.character * localConstant F tau.1 psiF.character)
  let prefactor := (-1 : ℂ) ^ (t + 1 + h) *
    ((scaleAddCharData F psiF alpha).character
      (-c * (trace F E x ^ 2 / norm F E x)) : ℂ)
  ratio = prefactor * (gU / (gE * gTau)) ∧
    prefactor = 1 ∧ ratio = gU / (gE * gTau)

/-- Substitute the constructed representatives and the coefficient one for
the lower ramified character. The corrected restriction is supplied here;
the genuine-pair theorem below obtains it from `Characters.conjugacy`. -/
private theorem criticalRatio_of_representatives
    [PrimeCyclicExtension F E]
    (hunr : ramificationIndex F U = 1) (hU : Module.finrank F U = 2)
    (_hE : Module.finrank F E = 2) {t h : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hres : residueDegree F E = 1)
    (hhpos : 0 < h) (hh : h ≤ t)
    (eta : NormCharacter F U) (heta : eta ≠ 1)
    (tau : NormCharacter F E) (htau : tau ≠ 1)
    (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
    (hcondU : IsMultiplicativeConductor U thetaU (t + 1 + h))
    (hcondE : IsMultiplicativeConductor E thetaE (t + 1 + 2 * h))
    (hdet : Characters.restrictQuasiChar F U thetaU * eta.1 =
      Characters.restrictQuasiChar F E thetaE * tau.1)
    (psiF : LocalAddCharData F) (psiU : LocalAddCharData U) (psiE : LocalAddCharData E)
    (hpsiU : psiU.character = tracePullbackAddChar F U psiF.character)
    (hpsiE : psiE.character = tracePullbackAddChar F E psiF.character)
    (alpha : Fˣ)
    (hPsi : (scaleAddCharData F psiF alpha).conductor = -((t + 1 : ℕ) : ℤ))
    (htauchart : ∀ (z : F) (hz : z ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
      tau.1 (principalUnitOf F (t / 2) (-z) (neg_mem_lattice F hz)) =
        (scaleAddCharData F psiF alpha).character z)
    (c : F) (d : U) (x : E)
    (R : ConjugatedNormData F U E thetaU thetaE
      (scaleAddCharData F psiF alpha).character c d x t h)
    (deltaU : Uˣ) (deltaE : Eˣ) (deltaTau : Fˣ)
    (hdeltaU : ord U (deltaU : U) =
      (((canonicalLocalQuasiCharData U thetaU).conductor / 2 : ℕ) : WithTop ℤ))
    (hdeltaE : ord E (deltaE : E) =
      (((canonicalLocalQuasiCharData E thetaE).conductor / 2 : ℕ) : WithTop ℤ))
    (hdeltaTau : ord F (deltaTau : F) =
      (((canonicalLocalQuasiCharData F tau.1).conductor / 2 : ℕ) : WithTop ℤ)) :
    let chiU := canonicalLocalQuasiCharData U thetaU
    let chiE := canonicalLocalQuasiCharData E thetaE
    let chiTau := canonicalLocalQuasiCharData F tau.1
    ∃ (largeU : 1 < chiU.conductor) (largeE : 1 < chiE.conductor)
      (largeTau : 1 < chiTau.conductor),
      localConstant U thetaU psiU.character * localConstant F eta.1 psiF.character /
          (localConstant E thetaE psiE.character * localConstant F tau.1 psiF.character) =
        ((-1 : ℂ) ^ (t + 1 + h) *
          ((scaleAddCharData F psiF alpha).character
            (-c * (trace F E x ^ 2 / norm F E x)) : ℂ)) *
        (criticalResidualFactor U chiU psiU (Units.map (algebraMap F U).toMonoidHom alpha)
            R.ZU largeU deltaU hdeltaU /
          (criticalResidualFactor E chiE psiE (Units.map (algebraMap F E).toMonoidHom alpha)
              R.ZE largeE deltaE hdeltaE *
            criticalResidualFactor F chiTau psiF alpha 1 largeTau deltaTau hdeltaTau)) := by
  let chiU := canonicalLocalQuasiCharData U thetaU
  let chiE := canonicalLocalQuasiCharData E thetaE
  let chiTau := canonicalLocalQuasiCharData F tau.1
  let Psi := scaleAddCharData F psiF alpha
  let alphaU := Units.map (algebraMap F U).toMonoidHom alpha
  let alphaE := Units.map (algebraMap F E).toMonoidHom alpha
  have hmU : chiU.conductor = t + 1 + h := chiU.isConductor.unique hcondU
  have hmE : chiE.conductor = t + 1 + 2 * h := chiE.isConductor.unique hcondE
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have hmTau : chiTau.conductor = t + 1 := chiTau.isConductor.unique
    (ramifiedNormCharacter_conductor F E ht hres pi hpi hgen tau htau)
  have largeU : 1 < chiU.conductor := by omega
  have largeE : 1 < chiE.conductor := by omega
  have largeTau : 1 < chiTau.conductor := by omega
  refine ⟨largeU, largeE, largeTau, ?_⟩
  have hscaleU : scaleAddCharData U psiU alphaU =
      ⟨tracePullbackAddChar F U Psi.character, -((t + 1 : ℕ) : ℤ),
        R.additiveConductorU⟩ :=
    LocalAddCharData.eq_of_character_eq (criticalRatio_traceScale F U psiF psiU hpsiU alpha)
  have hscaleE : scaleAddCharData E psiE alphaE =
      ⟨tracePullbackAddChar F E Psi.character, -((t + 1 : ℕ) : ℤ),
        R.additiveConductorE⟩ :=
    LocalAddCharData.eq_of_character_eq (criticalRatio_traceScale F E psiF psiE hpsiE alpha)
  have hZU : ord U (R.ZU : U) =
      ((-(scaleAddCharData U psiU alphaU).conductor - (chiU.conductor : ℤ)) : WithTop ℤ) := by
    rw [hscaleU, hmU, R.orderU]
    congr 1
    simp
  have hZE : ord E (R.ZE : E) =
      ((-(scaleAddCharData E psiE alphaE).conductor - (chiE.conductor : ℤ)) : WithTop ℤ) := by
    rw [hscaleE, hmE, R.orderE]
    congr 1
    push_cast
    ring
  have hZTau : ord F ((1 : Fˣ) : F) =
      ((-Psi.conductor - (chiTau.conductor : ℤ)) : WithTop ℤ) := by
    rw [hmTau, hPsi]
    simp only [Units.val_one, ord_one]
    norm_cast
    omega
  have hstationaryU : Stationary.IsNormalizedStationaryCoefficientAtDepth U chiU
      (scaleAddCharData U psiU alphaU) R.ZU
      (chiU.conductor / 2 + chiU.conductor % 2) (by omega) := by
    rw [hscaleU]
    convert R.stationaryU using 1; omega
  have hstationaryE : Stationary.IsNormalizedStationaryCoefficientAtDepth E chiE
      (scaleAddCharData E psiE alphaE) R.ZE
      (chiE.conductor / 2 + chiE.conductor % 2) (by omega) := by
    rw [hscaleE]
    convert R.stationaryE using 1; omega
  have hstationaryTau : Stationary.IsNormalizedStationaryCoefficientAtDepth F chiTau Psi 1
      (chiTau.conductor / 2 + chiTau.conductor % 2) (by omega) := by
    have heq : chiTau.conductor / 2 + chiTau.conductor % 2 = t / 2 + 1 := by omega
    intro z
    have hz : (z : F) ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ) := by
      simpa only [heq] using z.property
    have hu : positiveUnitOfLattice F (show 0 < chiTau.conductor / 2 +
        chiTau.conductor % 2 by omega) (-z) =
        principalUnitOf F (t / 2) (-(z : F)) (neg_mem_lattice F hz) := by
      apply Units.ext
      simp only [coe_positiveUnitOfLattice, Submodule.coe_neg, coe_principalUnitOf]
    simpa only [hu, Units.val_one, one_mul, chiTau, Psi,
      canonicalLocalQuasiCharData_character] using htauchart (z : F) hz
  have hfU := criticalRatio_factor U chiU psiU alphaU R.ZU largeU hZU hstationaryU
    deltaU hdeltaU
  have hfE := criticalRatio_factor E chiE psiE alphaE R.ZE largeE hZE hstationaryE
    deltaE hdeltaE
  have hfTau := criticalRatio_factor F chiTau psiF alpha 1 largeTau hZTau hstationaryTau
    deltaTau hdeltaTau
  let c0 : Fˣ := -alpha⁻¹
  have huU : (-alphaU * R.ZU)⁻¹ = Units.map (algebraMap F U).toMonoidHom c0 * R.ZU⁻¹ := by
    simp [alphaU, c0, mul_comm]
  have huE : (-alphaE * R.ZE)⁻¹ = Units.map (algebraMap F E).toMonoidHom c0 * R.ZE⁻¹ := by
    simp [alphaE, c0, mul_comm]
  have hdet0 := congrArg (fun chi : ContinuousQuasiChar F => (chi c0 : ℂ)) hdet
  change (thetaU (Units.map (algebraMap F U).toMonoidHom c0) : ℂ) * (eta.1 c0 : ℂ) =
    (thetaE (Units.map (algebraMap F E).toMonoidHom c0) : ℂ) * (tau.1 c0 : ℂ) at hdet0
  have hbase : (thetaU (Units.map (algebraMap F U).toMonoidHom c0) : ℂ) *
      localConstant F eta.1 psiF.character /
      ((thetaE (Units.map (algebraMap F E).toMonoidHom c0) : ℂ) * (tau.1 c0 : ℂ)) =
      (-1 : ℂ) ^ (t + 1) := by
    rw [← hdet0, mul_div_mul_left _ _ (Units.ne_zero _)]
    exact criticalRatio_unramified F U hunr hU eta heta psiF alpha (t + 1) hPsi
  have hadd : ((tracePullbackAddChar F U Psi.character) (-(R.ZU : U)) : ℂ) /
      (((tracePullbackAddChar F E Psi.character) (-(R.ZE : E)) : ℂ) *
        (Psi.character (-1) : ℂ)) =
      (Psi.character (-c * (trace F E x ^ 2 / norm F E x)) : ℂ) := by
    simp only [tracePullbackAddChar_apply, map_neg]
    rw [← Units.val_mul, ← ContinuousAddChar.map_add_eq_mul, ← Units.val_div_eq_div_val]
    apply congrArg (Units.val : ℂˣ → ℂ)
    change Psi.character.toAddChar (-trace F U (R.ZU : U)) /
      Psi.character.toAddChar (-trace F E (R.ZE : E) + -1) = _
    rw [← AddChar.map_sub_eq_div]
    change Psi.character.toAddChar (-trace F U (R.ZU : U) -
      (-trace F E (R.ZE : E) + -1)) =
      Psi.character.toAddChar (-c * (trace F E x ^ 2 / norm F E x))
    apply congrArg Psi.character.toAddChar
    linear_combination -R.trace_difference
  simp only [chiU, chiE, chiTau, canonicalLocalQuasiCharData_character] at hfU hfE hfTau
  have huTau : (-alpha * (1 : Fˣ))⁻¹ = c0 := by simp [c0]
  rw [hfU, hfE, hfTau]
  rw [huU, huE, huTau]
  simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [hscaleU, hscaleE]
  simp only [Units.val_one]
  change _ = ((-1 : ℂ) ^ (t + 1 + h) * _) * _
  calc
    _ = ((thetaU (Units.map (algebraMap F U).toMonoidHom c0) : ℂ) *
          localConstant F eta.1 psiF.character /
          ((thetaE (Units.map (algebraMap F E).toMonoidHom c0) : ℂ) * (tau.1 c0 : ℂ))) *
        ((thetaE R.ZE : ℂ) / (thetaU R.ZU : ℂ)) *
        (((tracePullbackAddChar F U Psi.character) (-(R.ZU : U)) : ℂ) /
          (((tracePullbackAddChar F E Psi.character) (-(R.ZE : E)) : ℂ) *
            (Psi.character (-1) : ℂ))) *
        (criticalResidualFactor U chiU psiU alphaU R.ZU largeU deltaU hdeltaU /
          (criticalResidualFactor E chiE psiE alphaE R.ZE largeE deltaE hdeltaE *
            criticalResidualFactor F chiTau psiF alpha 1 largeTau deltaTau hdeltaTau)) := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    _ = _ := by rw [hbase, R.character_ratio, hadd, ← pow_add]
end Representatives

section ActualPair
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

/-- **Paper Proposition `D:UR:criticalratio`.** For the genuine primitive
compatible pair at positive critical height, construct the corrected
representatives and retain the full three residual factors, using coefficient
one for the actual lower ramified norm character.

The conclusion gives both equalities of `D:UR:newratio` and the intervening
exact sign evaluation. All critical elements are arbitrary with their exact
orders. `criticalResidualFactor` is one in even conductor and the complete
normalized affine sum in odd conductor. The nontrivial additive character is
packaged with its exact integer conductor; its two upper characters are the
actual trace pullbacks. No stationary model, norm representative, corrected
restriction, or phase cancellation is a hypothesis. Both field
characteristics and nonunitary continuous quasi-characters are retained. -/
theorem criticalRatio
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
      IsMultiplicativeConductor E thetaE (t + 1 + 2 * h) ∧
      ∃ x : E, ord E x = ((-(h : ℤ)) : WithTop ℤ) ∧
      ∃ R : ConjugatedNormData F U E thetaU thetaE
          (scaleAddCharData F psiF alpha).character (c : F) d x t h,
      CriticalRatioIdentity F U E eta tau thetaU thetaE psiF psiU psiE alpha
        (c : F) d x t h R := by
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
  have dataU := Basic.intermediateField_tower_compatible Nat.prime_two hG U hU
  have dataE := Basic.intermediateField_tower_compatible Nat.prime_two hG E hE
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F U dataU.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E dataE.2.2.2.2.2.2.2.2.2.2.2.1
  let Psi := scaleAddCharData F psiF alpha
  have hPsiData : IsAdditiveConductor F Psi.character (-((t + 1 : ℕ) : ℤ)) := by
    rw [← hPsi]
    exact Psi.isConductor
  obtain ⟨hcondE, x, hx, ⟨R⟩⟩ := conjugatedNorm hG U E hU hE hunr t h hhpos hh ht hres
    tau htau Psi.character hPsiData htauchart sigma hsigma (c : F) hc d hd hdc hconj
    thetaU thetaE hcomp hprimitive hcondU
  have hne : Ramification.intermediateNormRange U ≠ Ramification.intermediateNormRange E := by
    change (normUnits F U).range ≠ (normUnits F E).range
    intro heq
    obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
    have hct := ramifiedNormCharacter_conductor F E ht hres pi hpi hgen tau htau
    have hzero : QuasiCharTrivialOnUnitFiltration F tau.1 0 := by
      intro u hu
      apply tau.eq_one_on_normRange F E
      rw [← heq]
      obtain ⟨v, _, hv⟩ := (unramified_norm_unitFiltration F U hunr 0).2 u hu
      exact ⟨v, hv⟩
    have hb := hct.minimal 0 hzero
    omega
  obtain ⟨_, _, hdet, _, htwo⟩ := Characters.conjugacy Nat.prime_two hG U E hU hE hne
    thetaU thetaE (normQuasiChar U K thetaU) rfl hcomp.symm hprimitive
  obtain ⟨eta', tau', heta', htau', hprodU, hprodE⟩ := htwo rfl
  have heqEta : eta' = eta :=
    ((Nat.card_eq_two_iff' (1 : NormCharacter F U)).mp
      ((unramifiedNormCharacter_card F U hunr).trans hU)).unique heta' heta
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have heqTau : tau' = tau :=
    ((Nat.card_eq_two_iff' (1 : NormCharacter F E)).mp
      ((ramifiedNormCharacter_card F E ht hres pi hpi hgen).trans hE)).unique htau' htau
  subst eta' tau'
  rw [hprodU, hprodE] at hdet
  have hparity := (traceParity F E hchar ht hres hE tau htau Psi.character hPsiData
    htauchart hhpos hh x hx c htracec).2.2
  dsimp only [Psi] at hparity
  refine ⟨hcondE, x, hx, R, ?_⟩
  intro deltaU deltaE deltaTau hdeltaU hdeltaE hdeltaTau
  obtain ⟨largeU, largeE, largeTau, hratio⟩ := criticalRatio_of_representatives F U E
    hunr hU hE ht hres hhpos hh eta heta tau htau thetaU thetaE hcondU hcondE hdet
    psiF psiU psiE hpsiU hpsiE alpha hPsi htauchart (c : F) d x R
    deltaU deltaE deltaTau hdeltaU hdeltaE hdeltaTau
  exact ⟨largeU, largeE, largeTau, hratio, hparity, by simpa only [hparity, one_mul] using hratio⟩
end ActualPair

end

end LanglandsSecondMainLemma.Dyadic.UR
