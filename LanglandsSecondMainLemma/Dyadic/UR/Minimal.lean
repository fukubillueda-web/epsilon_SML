import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Dyadic.UR.MinimalFunctions

/-!
# Minimal-conductor comparison in the unramified/ramified dyadic diamond

Paper Theorem 10.8 (`D:UR:minimal`), including both parity rows and
`D:UR:actualHidentity`. The actual affine residual functions are summed
with their full cardinality normalization. The lower unramified quadratic
factor is evaluated before the elementary sign cancels.

The final theorem starts with genuine local fields and a primitive pair.
Integral trace-surjectivity constructs the unramified generator; stationary
duality constructs the additive normalization. The accepted model, twist
and origin constructors then supply all comparison data, and additive
scaling returns the identity to the original character.
-/

namespace LanglandsSecondMainLemma.Dyadic.UR

noncomputable section
open LanglandsFirstMainLemma
open scoped BigOperators

/-- Summing the pointwise identity uses both actual coordinate bijections.
The cardinality identity also proves the normalization, so no Gauss-sum
sign or square-root choice is assumed. -/
theorem minimal_residual_sum
    (k kappa l : Type*) [Fintype k] [Fintype kappa] [Fintype l]
    (square : kappa → kappa) (hsquare : Function.Bijective square)
    (coordinates : kappa → k × k) (hcoordinates : Function.Bijective coordinates)
    (i : k → l) (hi : Function.Bijective i)
    (HU : kappa → ℂ) (HE : l → ℂ) (Htau : k → ℂ)
    (hpoint : ∀ z, HU (square z) = HE (i (coordinates z).1) * Htau (coordinates z).2) :
    (Real.sqrt (Fintype.card kappa : ℝ) : ℂ)⁻¹ * ∑ z, HU z =
      ((Real.sqrt (Fintype.card l : ℝ) : ℂ)⁻¹ * ∑ z, HE z) *
      ((Real.sqrt (Fintype.card k : ℝ) : ℂ)⁻¹ * ∑ z, Htau z) := by
  have hsum : ∑ z, HU z = (∑ z, HE z) * ∑ z, Htau z := by
    rw [← hsquare.sum_comp HU]
    calc
      _ = ∑ z : k × k, HE (i z.1) * Htau z.2 :=
        Fintype.sum_bijective coordinates hcoordinates _ _ hpoint
      _ = (∑ z : k, HE (i z)) * ∑ z : k, Htau z := by
        rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
      _ = _ := by rw [hi.sum_comp HE]
  have hcard : Fintype.card kappa = Fintype.card k * Fintype.card k := by
    rw [Fintype.card_congr (Equiv.ofBijective coordinates hcoordinates), Fintype.card_prod]
  have hcardl : Fintype.card l = Fintype.card k :=
    (Fintype.card_congr (Equiv.ofBijective i hi)).symm
  have hsqrt : Real.sqrt (Fintype.card kappa : ℝ) =
      Real.sqrt (Fintype.card l : ℝ) * Real.sqrt (Fintype.card k : ℝ) := by
    rw [hcard, hcardl, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
  rw [hsum, hsqrt, Complex.ofReal_mul, mul_inv]
  ring

section UnramifiedFactor
variable (F U : Type*) [Field F] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U]
  [PrimeCyclicExtension F U]
/-- A nontrivial unramified quadratic norm character has value minus one
on an actual uniformizer. -/
theorem minimal_unramified_uniformizer
    (hunr : ramificationIndex F U = 1) (hdegree : Module.finrank F U = 2)
    (eta : NormCharacter F U) (heta : eta ≠ 1)
    (pi : Fˣ) (hpi : ord F (pi : F) = 1) : (eta.1 pi : ℂ) = -1 := by
  have hp := (ord_eq_one_iff_isUniformizer F (pi : F)).mp hpi
  let ev := unramifiedNormCharacterEvaluationEquivCard F U hunr pi hp
  have hne : (eta.1 pi : ℂ) ≠ 1 := by
    intro h
    apply heta
    apply ev.injective
    apply Subtype.ext
    apply Units.ext
    rw [map_one]
    simpa only [ev, unramifiedNormCharacterEvaluationEquivCard_coe,
      OneMemClass.coe_one, Units.val_one] using h
  have hnorm : normUnits F U (Units.map (algebraMap F U).toMonoidHom pi) = pi ^ 2 := by
    apply Units.ext
    change norm F U (algebraMap F U pi.val) = pi.val ^ 2
    rw [LanglandsFirstMainLemma.norm_algebraMap, hdegree]
  have hs : (eta.1 pi : ℂ) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← hnorm,
      eta.eq_one_on_normRange F U _ ⟨_, rfl⟩, Units.val_one]
  exact (sq_eq_one_iff.mp hs).resolve_left hne

/-- The lower unramified quadratic factor in the normalized additive
convention is exactly `(-1)^T`; it is retained in both parity rows. -/
theorem minimal_unramified_localConstant
    (hunr : ramificationIndex F U = 1) (hdegree : Module.finrank F U = 2)
    (eta : NormCharacter F U) (heta : eta ≠ 1)
    (Psi : LocalAddCharData F) (T : ℕ) (hPsi : Psi.conductor = -(T : ℤ)) :
    localConstant F eta.1 Psi.character = (-1 : ℂ) ^ T := by
  obtain ⟨p, hp⟩ := exists_ord_eq F 1
  have hpne : p ≠ 0 := (ord_ne_top_iff F).mp (by rw [hp]; simp)
  let pi := Units.mk0 p hpne
  let etaData : LocalQuasiCharData F :=
    ⟨eta.1, 0, unramifiedNormCharacter_conductor F U hunr eta⟩
  let gamma : AdmissibleGamma F etaData Psi := ⟨pi ^ (-(T : ℤ)), by
    change ord F ((pi ^ (-(T : ℤ)) : Fˣ) : F) = _
    rw [Units.val_zpow_eq_zpow_val, ord_zpow, show ord F (pi : F) = 1 from hp]
    simp only [etaData, Nat.cast_zero, zero_add, hPsi]
    rw [neg_zsmul, natCast_zsmul, nsmul_one, ← WithTop.coe_natCast]
    rfl⟩
  rw [localConstant_isDeltaFinite F etaData Psi gamma,
    deltaFinite_conductor_zero F etaData rfl Psi gamma]
  change (eta.1 (pi ^ (-(T : ℤ))) : ℂ) = _
  rw [map_zpow, Units.val_zpow_eq_zpow_val, minimal_unramified_uniformizer F U hunr hdegree eta heta pi hp]
  rw [zpow_neg, zpow_natCast, ← inv_pow, inv_neg, inv_one]
end UnramifiedFactor

section LamprechtFactors
open private critical_scale_one from LanglandsSecondMainLemma.Dyadic.UR.MinimalFunctions
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
private theorem minimal_factor_odd (theta : LocalQuasiCharData L) (Psi : LocalAddCharData L)
    (Z : Lˣ) (e : ℕ) (hm : theta.conductor = 2 * e + 1)
    (hlarge : 1 < theta.conductor)
    (hs : Stationary.IsOrdinaryStationaryCoefficient L theta Psi Z hlarge)
    (a : Lˣ) (ha : ord L (a : L) = ((e : ℤ) : WithTop ℤ)) :
    localConstant L theta.character Psi.character =
      (theta.character ((-Z)⁻¹) : ℂ) * (Psi.character (-(Z : L)) : ℂ) *
      Stationary.normalizedResidualFactor L theta Psi 1 Z e hm hlarge a ha := by
  have hdepth : theta.conductor / 2 + theta.conductor % 2 = e + 1 := by omega
  have horder : ord L (Z : L) =
      ((-(scaleAddCharData L Psi 1).conductor - (theta.conductor : ℤ) : ℤ) : WithTop ℤ) := by
    rw [critical_scale_one]
    exact hs.1
  have hstationary : Stationary.IsNormalizedStationaryCoefficientAtDepth L theta
      (scaleAddCharData L Psi 1) Z (e + 1) (by omega) := by
    rw [critical_scale_one]
    simpa only [hdepth] using hs.2
  simpa only [neg_mul, one_mul, critical_scale_one] using
    (Stationary.normalizedFactor L theta Psi 1 Z e 1 (by omega) hm hlarge
      horder hstationary).2 rfl a ha

private theorem minimal_factor_even (theta : LocalQuasiCharData L) (Psi : LocalAddCharData L)
    (Z : Lˣ) (hlarge : 1 < theta.conductor)
    (hs : Stationary.IsOrdinaryStationaryCoefficient L theta Psi Z hlarge)
    (heven : Even theta.conductor) :
    localConstant L theta.character Psi.character =
      (theta.character ((-Z)⁻¹) : ℂ) * (Psi.character (-(Z : L)) : ℂ) := by
  have hs' : Stationary.IsOrdinaryStationaryCoefficient L theta
      (scaleAddCharData L Psi 1) Z hlarge := by rwa [critical_scale_one]
  have h := Stationary.completeNormalizedFactor L theta Psi 1 Z hlarge hs'
  simpa only [neg_mul, one_mul, critical_scale_one,
    Stationary.completeNormalizedResidualFactor_even L theta Psi 1 Z hlarge
      (Nat.even_iff.mp heven), mul_one] using h
end LamprechtFactors

section ActualCharacters
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  [IsKleinFour Gal(K/F)]
  (U E : IntermediateField F K)
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeExtension F U] [ValuativeExtension U K]
  [ValuativeExtension F E] [ValuativeExtension E K]
  [Algebra.IsQuadraticExtension F U] [Algebra.IsQuadraticExtension U K]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsQuadraticExtension E K]

/-- The complete normalized residual factors in the odd row of
`D:UR:minimal` satisfy `g_U = g_E g_tau`. The identity of the three actual
affine functions and the bijectivity of their coordinates are supplied by
`dyadicUR_minimal_critical_identity`, not imposed as hypotheses. -/
theorem minimal_odd_residual_factors [PrimeCyclicExtension F E]
    (hunr : ramificationIndex F U = 1) (hsup : U ⊔ E = ⊤)
    (hchar : residueCharacteristic F = 2)
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1)
    {c : F} {d : U} {x : E}
    (hd : d ∈ lattice U 0) (hx : x ∈ lattice E 0)
    (thetaU : LocalQuasiCharData U) (thetaE : LocalQuasiCharData E)
    (hcondU : thetaU.conductor = t + 1) (hcondE : thetaE.conductor = t + 1)
    (Theta : ContinuousQuasiChar K)
    (hcU : normQuasiChar U K thetaU.character = Theta)
    (hcE : normQuasiChar E K thetaE.character = Theta)
    (tau : NormCharacter F E) (Psi : ContinuousAddChar F)
    (O : MinimalOriginData U E c d x t thetaU thetaE Psi)
    (D : MinimalOddElementaryData U E x t tau Psi O.origin)
    (a : Eˣ) (ha : ord E (a : E) = ((D.e : ℤ) : WithTop ℤ)) :
    let deltaF := normUnits F E a
    let deltaU := Units.map (algebraMap F U).toMonoidHom deltaF
    let hdeltaF : ord F (deltaF : F) = ((D.e : ℤ) : WithTop ℤ) := by
      change ord F (norm F E (a : E)) = _
      rw [ord_norm, hres, one_nsmul, ha]
    let hdeltaU : ord U (deltaU : U) = ((D.e : ℤ) : WithTop ℤ) := by
      change ord U (algebraMap F U (deltaF : F)) = _
      rw [ord_algebraMap, hunr, one_nsmul, hdeltaF]
    Stationary.normalizedResidualFactor U thetaU O.psiU 1
      (normUnits U K O.origin) D.e (by rw [hcondU, D.conductor_eq]) O.largeU deltaU hdeltaU =
    Stationary.normalizedResidualFactor E thetaE O.psiE 1
      (normUnits E K O.origin) D.e (by rw [hcondE, D.conductor_eq]) O.largeE a ha *
    Stationary.normalizedResidualFactor F D.tauData D.psiData 1
      (Stationary.commonOriginLowerCoefficient E O.origin D.traceE_ne_zero) D.e
      (by rw [D.tau_conductor, D.conductor_eq]) D.large deltaF hdeltaF := by
  letI := residueFieldFintype F
  letI := residueFieldFintype U
  letI := residueFieldFintype E
  letI : CharP (ResidueField F) 2 := ringChar.of_eq hchar
  letI : CharP (ResidueField U) 2 :=
    charP_of_injective_algebraMap (algebraMap (ResidueField F) (ResidueField U)).injective 2
  obtain ⟨X, _, hbij, hpoint⟩ := dyadicUR_minimal_critical_identity U E
    hunr hsup hchar ht hres hd hx thetaU thetaE hcondU hcondE Theta hcU hcE tau Psi O D a ha
  dsimp only
  unfold Stationary.normalizedResidualFactor
  exact minimal_residual_sum (ResidueField F) (ResidueField U) (ResidueField E)
    (fun z => z ^ 2) (PerfectRing.bijective_frobenius (R := ResidueField U) (p := 2))
    _ hbij (extensionResidueMap F E)
    ⟨(extensionResidueMap F E).injective,
      extensionResidueMap_surjective_of_residueDegree_eq_one F E hres⟩
    _ _ _ hpoint

omit [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [ValuativeExtension F K] [IsKleinFour Gal(K/F)]
  [ValuativeExtension F U] [ValuativeExtension F E]
  [Algebra.IsQuadraticExtension F U] [Algebra.IsQuadraticExtension F E] in
/-- The multiplicative factors at a common origin use compatibility and
only the corrected restriction at minus one. The lower argument is kept
as an actual unit with its proved norm-character value. -/
private theorem minimal_multiplicative_factor
    (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
    (Theta : ContinuousQuasiChar K)
    (hcU : normQuasiChar U K thetaU = Theta)
    (hcE : normQuasiChar E K thetaE = Theta)
    (tau : ContinuousQuasiChar F)
    (hdet : thetaU (-1) = thetaE (-1) * tau (-1))
    (C : Kˣ) (W : Fˣ) (hW : tau W = 1) :
    (thetaU ((-normUnits U K C)⁻¹) : ℂ) =
      (thetaE ((-normUnits E K C)⁻¹) : ℂ) * (tau ((-W)⁻¹) : ℂ) := by
  have hZU : thetaU (normUnits U K C) = Theta C := DFunLike.congr_fun hcU C
  have hZE : thetaE (normUnits E K C) = Theta C := DFunLike.congr_fun hcE C
  have hunit {L : Type} [Field L] (z : Lˣ) : (-z)⁻¹ = (-1 : Lˣ) * z⁻¹ := by simp
  rw [hunit (normUnits U K C), hunit (normUnits E K C), hunit W,
    map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, hZU, hZE,
    hW, inv_one, mul_one, hdet]
  push_cast
  ring

/-- Odd-conductor assembly at a constructed genuine origin. The lower
unramified factor, the lower ramified factor and all three complete affine
residual sums occur in the canonical local-constant equality. -/
theorem minimal_odd_of_origin [PrimeCyclicExtension F U] [PrimeCyclicExtension F E]
    (hunr : ramificationIndex F U = 1) (hsup : U ⊔ E = ⊤)
    (hchar : residueCharacteristic F = 2)
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1)
    {c : F} {d : U} {x : E}
    (hd : d ∈ lattice U 0) (hx : x ∈ lattice E 0)
    (thetaU : LocalQuasiCharData U) (thetaE : LocalQuasiCharData E)
    (hcondU : thetaU.conductor = t + 1) (hcondE : thetaE.conductor = t + 1)
    (Theta : ContinuousQuasiChar K)
    (hcU : normQuasiChar U K thetaU.character = Theta)
    (hcE : normQuasiChar E K thetaE.character = Theta)
    (eta : NormCharacter F U) (heta : eta ≠ 1)
    (tau : NormCharacter F E) (Psi : ContinuousAddChar F)
    (hdet : thetaU.character (-1) = thetaE.character (-1) * tau.1 (-1))
    (O : MinimalOriginData U E c d x t thetaU thetaE Psi)
    (D : MinimalOddElementaryData U E x t tau Psi O.origin) :
    localConstant U thetaU.character O.psiU.character * localConstant F eta.1 Psi =
      localConstant E thetaE.character O.psiE.character * localConstant F tau.1 Psi := by
  let ZU := normUnits U K O.origin
  let ZE := normUnits E K O.origin
  let W := Stationary.commonOriginLowerCoefficient E O.origin D.traceE_ne_zero
  have hmultiplicative : (thetaU.character ((-ZU)⁻¹) : ℂ) =
      (thetaE.character ((-ZE)⁻¹) : ℂ) * (D.tauData.character ((-W)⁻¹) : ℂ) := by
    rw [D.tau_character]
    exact minimal_multiplicative_factor U E thetaU.character thetaE.character Theta hcU hcE
      tau.1 hdet O.origin W D.norm_character_value
  have hadditive : (O.psiU.character (-(ZU : U)) : ℂ) =
      (O.psiE.character (-(ZE : E)) : ℂ) * (D.psiData.character (-(W : F)) : ℂ) *
      (Psi (norm F U (trace U K (O.origin : K))) : ℂ) := by
    rw [O.psiU_character, O.psiE_character, D.psi_character]
    change (Psi (trace F U (-(ZU : U))) : ℂ) =
      (Psi (trace F E (-(ZE : E))) : ℂ) * (Psi (-(W : F)) : ℂ) * _
    rw [← Units.val_mul, ← ContinuousAddChar.map_add_eq_mul,
      ← Units.val_mul, ← ContinuousAddChar.map_add_eq_mul]
    congr 2
    rw [map_neg, map_neg]
    have hU := Algebra.biquadraticE2 F K U (O.origin : K)
    have hE := Algebra.biquadraticE2 F K E (O.origin : K)
    change -trace F U (norm U K (O.origin : K)) =
      -trace F E (norm E K (O.origin : K)) +
        -norm F E (trace E K (O.origin : K)) + norm F U (trace U K (O.origin : K))
    linear_combination hU - hE
  obtain ⟨a0, ha0⟩ := exists_ord_eq E (D.e : ℤ)
  have hane : a0 ≠ 0 := (ord_ne_top_iff E).mp (by rw [ha0]; simp)
  let a := Units.mk0 a0 hane
  have ha : ord E (a : E) = ((D.e : ℤ) : WithTop ℤ) := ha0
  let deltaF := normUnits F E a
  let deltaU := Units.map (algebraMap F U).toMonoidHom deltaF
  have hdeltaF : ord F (deltaF : F) = ((D.e : ℤ) : WithTop ℤ) := by
    change ord F (norm F E (a : E)) = _
    rw [ord_norm, hres, one_nsmul, ha]
  have hdeltaU : ord U (deltaU : U) = ((D.e : ℤ) : WithTop ℤ) := by
    change ord U (algebraMap F U (deltaF : F)) = _
    rw [ord_algebraMap, hunr, one_nsmul, hdeltaF]
  have hmU : thetaU.conductor = 2 * D.e + 1 := hcondU.trans D.conductor_eq
  have hmE : thetaE.conductor = 2 * D.e + 1 := hcondE.trans D.conductor_eq
  have hmF : D.tauData.conductor = 2 * D.e + 1 := D.tau_conductor.trans D.conductor_eq
  have hU := minimal_factor_odd U thetaU O.psiU ZU D.e hmU O.largeU
    O.stationaryU deltaU hdeltaU
  have hE := minimal_factor_odd E thetaE O.psiE ZE D.e hmE O.largeE O.stationaryE a ha
  have hF := minimal_factor_odd F D.tauData D.psiData W D.e hmF D.large
    D.stationary deltaF hdeltaF
  have hresidual := minimal_odd_residual_factors U E hunr hsup hchar ht hres hd hx
    thetaU thetaE hcondU hcondE Theta hcU hcE tau Psi O D a ha
  have hetaF := minimal_unramified_localConstant F U hunr
    (Algebra.IsQuadraticExtension.finrank_eq_two F U) eta heta D.psiData (t + 1)
    D.psi_conductor
  rw [D.psi_character] at hetaF
  rw [D.tau_character, D.psi_character] at hF
  rw [hU, hE, hF, hetaF, hmultiplicative, hadditive]
  change (_ * (_ * _ * _) *
    Stationary.normalizedResidualFactor U thetaU O.psiU 1 ZU D.e hmU O.largeU deltaU hdeltaU) *
      (-1 : ℂ) ^ (t + 1) = _
  rw [hresidual]
  simp only [D.tau_character, D.psi_character]
  have hsign := D.elementary_sign
  linear_combination
    ((thetaE.character ((-ZE)⁻¹) : ℂ) * (tau.1 ((-W)⁻¹) : ℂ) *
      (O.psiE.character (-(ZE : E)) : ℂ) * (Psi (-(W : F)) : ℂ) *
      Stationary.normalizedResidualFactor E thetaE O.psiE 1 ZE D.e hmE O.largeE a ha *
      Stationary.normalizedResidualFactor F D.tauData D.psiData 1 W D.e hmF D.large
        deltaF hdeltaF) * hsign

open private minimal_stationary from LanglandsSecondMainLemma.Dyadic.UR.MinimalOrigin

/-- Even-conductor assembly at the actual common norm origin. The lower
ramified stationary coefficient is constructed from its whole-ideal chart,
and the elementary phase is evaluated by `minimal_even_elementary`. -/
theorem minimal_even_of_origin [PrimeCyclicExtension F U] [PrimeCyclicExtension F E]
    (hunr : ramificationIndex F U = 1)
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (htpos : 0 < t) (hres : residueDegree F E = 1)
    (eta : NormCharacter F U) (heta : eta ≠ 1)
    (tau : NormCharacter F E) (htau : tau ≠ 1)
    (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (htauchart : ∀ (z : F) (hz : z ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
      tau.1 (principalUnitOf F (t / 2) (-z) (neg_mem_lattice F hz)) = Psi z)
    (c : F) (hc : c ∈ lattice F 0) (d : U) (x : E) (hx : x ∈ lattice E 0)
    (thetaU : LocalQuasiCharData U) (thetaE : LocalQuasiCharData E)
    (hcondU : thetaU.conductor = t + 1) (hcondE : thetaE.conductor = t + 1)
    (Theta : ContinuousQuasiChar K)
    (hcU : normQuasiChar U K thetaU.character = Theta)
    (hcE : normQuasiChar E K thetaE.character = Theta)
    (hdet : thetaU.character (-1) = thetaE.character (-1) * tau.1 (-1))
    (O : MinimalOriginData U E c d x t thetaU thetaE Psi)
    (heven : Even (t + 1)) :
    localConstant U thetaU.character O.psiU.character * localConstant F eta.1 Psi =
      localConstant E thetaE.character O.psiE.character * localConstant F tau.1 Psi := by
  have hUdegree := Algebra.IsQuadraticExtension.finrank_eq_two F U
  have hEdegree := Algebra.IsQuadraticExtension.finrank_eq_two F E
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  let tauData : LocalQuasiCharData F := ⟨tau.1, t + 1,
    ramifiedNormCharacter_conductor F E ht hres pi hpi hgen tau htau⟩
  let psiData : LocalAddCharData F := ⟨Psi, -((t + 1 : ℕ) : ℤ), hPsi⟩
  have hlarge : 1 < tauData.conductor := by change 1 < t + 1; omega
  have htauStationary : Stationary.IsOrdinaryStationaryCoefficient F tauData psiData 1
      hlarge := minimal_stationary F tauData psiData htpos rfl rfl 1 1 (ord_one F)
        (by simpa only [one_mul] using htauchart)
        (by simp only [Units.val_one, sub_self]; exact (lattice F _).zero_mem)
  let ZU := normUnits U K O.origin
  let ZE := normUnits E K O.origin
  have hU := minimal_factor_even U thetaU O.psiU ZU O.largeU O.stationaryU
    (hcondU.symm ▸ heven)
  have hE := minimal_factor_even E thetaE O.psiE ZE O.largeE O.stationaryE
    (hcondE.symm ▸ heven)
  have hF := minimal_factor_even F tauData psiData 1 hlarge htauStationary heven
  have hetaF := minimal_unramified_localConstant F U hunr hUdegree eta heta psiData (t + 1) rfl
  have hmultiplicative := minimal_multiplicative_factor U E thetaU.character thetaE.character
    Theta hcU hcE tau.1 hdet O.origin 1 (map_one tau.1)
  have hsign := minimal_even_elementary U E hUdegree hEdegree ht htpos hres tau htau
    Psi hPsi htauchart c hc d x hx thetaU thetaE O heven
  let R := 1 - (trace F U (ZU : U) - trace F E (ZE : E))
  change (-1 : ℂ) ^ (t + 1) * (Psi R : ℂ) = 1 at hsign
  have hadditive : (O.psiU.character (-(ZU : U)) : ℂ) =
      (O.psiE.character (-(ZE : E)) : ℂ) * (Psi (-1) : ℂ) * (Psi R : ℂ) := by
    rw [O.psiU_character, O.psiE_character]
    change (Psi (trace F U (-(ZU : U))) : ℂ) =
      (Psi (trace F E (-(ZE : E))) : ℂ) * (Psi (-1) : ℂ) * _
    rw [← Units.val_mul, ← ContinuousAddChar.map_add_eq_mul,
      ← Units.val_mul, ← ContinuousAddChar.map_add_eq_mul]
    congr 2
    rw [map_neg, map_neg]
    dsimp only [R]
    ring
  change localConstant F tau.1 Psi = _ at hF
  change localConstant F eta.1 Psi = _ at hetaF
  rw [hU, hE, hF, hetaF, hmultiplicative, hadditive]
  change (_ * _ * (_ * _ * _)) * (-1 : ℂ) ^ (t + 1) =
    (_ * _) * ((tau.1 ((-(1 : Fˣ))⁻¹) : ℂ) * (Psi (-1) : ℂ))
  linear_combination
    ((thetaE.character ((-ZE)⁻¹) : ℂ) * (tau.1 ((-(1 : Fˣ))⁻¹) : ℂ) *
      (O.psiE.character (-(ZE : E)) : ℂ) * (Psi (-1) : ℂ)) * hsign

/-- Assembly from the full model and twist charts. The norm representative,
common origin, odd elementary data and residual-coordinate identity are all
constructed in the proof. This is an intermediate result: normalization of
an arbitrary primitive pair is not assumed to be part of this statement. -/
theorem minimal_of_charts [PrimeCyclicExtension F U] [PrimeCyclicExtension F E]
    (hunr : ramificationIndex F U = 1) (hsup : U ⊔ E = ⊤)
    (hchar : residueCharacteristic F = 2)
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (htpos : 0 < t) (hres : residueDegree F E = 1)
    (eta : NormCharacter F U) (heta : eta ≠ 1)
    (tau : NormCharacter F E) (htau : tau ≠ 1)
    (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (htauchart : ∀ (z : F) (hz : z ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
      tau.1 (principalUnitOf F (t / 2) (-z) (neg_mem_lattice F hz)) = Psi z)
    (sigma : Gal(U/F)) (hsigma : sigma ≠ 1)
    (c : F) (hc : ord F c = 0) (d : U) (hd : ord U d = 0)
    (hdc : d ^ 2 - d = algebraMap F U c) (hconj : sigma d = 1 - d)
    (hcTrace : (@absoluteTraceTwo (ResidueField F) _ (ringChar.of_eq hchar))
      (reduce F c (by rw [mem_lattice, hc]; simp)) = 1)
    (chiU : ContinuousQuasiChar U) (chiE : ContinuousQuasiChar E)
    (thetaU : LocalQuasiCharData U) (thetaE : LocalQuasiCharData E)
    (lambda : ContinuousQuasiChar F)
    (hmodelU : ∀ (z : U) (hz : z ∈ lattice U ((t / 2 + 1 : ℕ) : ℤ)),
      chiU (principalUnitOf U (t / 2) (-z) (neg_mem_lattice U hz)) =
        tracePullbackAddChar F U Psi (d ^ 2 * z))
    (hmodelE : ∀ (z : E) (hz : z ∈ lattice E ((t / 2 + 1 : ℕ) : ℤ)),
      chiE (principalUnitOf E (t / 2) (-z) (neg_mem_lattice E hz)) =
        tracePullbackAddChar F E Psi (algebraMap F E c * z))
    (htwistU : thetaU.character = chiU * normQuasiChar F U lambda)
    (htwistE : thetaE.character = chiE * normQuasiChar F E lambda)
    (hlambda : multiplicativeConductorExponent F lambda ≤ t + 1)
    (hcondU : thetaU.conductor = t + 1) (hcondE : thetaE.conductor = t + 1)
    (Theta : ContinuousQuasiChar K)
    (hcU : normQuasiChar U K thetaU.character = Theta)
    (hcE : normQuasiChar E K thetaE.character = Theta)
    (hdet : thetaU.character (-1) = thetaE.character (-1) * tau.1 (-1)) :
    localConstant U thetaU.character (tracePullbackAddChar F U Psi) * localConstant F eta.1 Psi =
      localConstant E thetaE.character (tracePullbackAddChar F E Psi) * localConstant F tau.1 Psi := by
  have hK : Module.finrank F K = 4 := by
    rw [← IsGalois.card_aut_eq_finrank, IsKleinFour.card_four]
  have hU := Algebra.IsQuadraticExtension.finrank_eq_two F U
  have hE := Algebra.IsQuadraticExtension.finrank_eq_two F E
  have hc0 : c ∈ lattice F 0 := by rw [mem_lattice, hc]; simp
  have hd0 : d ∈ lattice U 0 := by rw [mem_lattice, hd]; simp
  obtain ⟨x, hxchart, _, hxintegral, _⟩ := normChoice F E (h := 0) ht htpos hres
    (Nat.zero_le t) lambda Psi hPsi (by omega) (fun _ => hlambda)
  have hx := hxintegral rfl
  simp only [add_zero] at hxchart
  obtain ⟨O⟩ := dyadicUR_minimal_origin U E hK hunr hU hE hsup ht htpos hres tau htau
    Psi hPsi htauchart sigma hsigma c hc d hd hdc hconj chiU chiE thetaU thetaE lambda
    hmodelU hmodelE htwistU htwistE hcondU hcondE x hx hxchart
  rcases Nat.even_or_odd (t + 1) with heven | hodd
  · have h := minimal_even_of_origin U E hunr ht htpos hres eta heta tau htau Psi hPsi
      htauchart c hc0 d x hx thetaU thetaE hcondU hcondE Theta hcU hcE hdet O heven
    simpa only [O.psiU_character, O.psiE_character] using h
  · obtain ⟨_, ⟨D⟩⟩ := dyadicUR_minimal_elementary U E hU hE hchar ht htpos hres
      tau htau Psi hPsi htauchart c hc0 hcTrace d x hx thetaU thetaE O hodd
    have h := minimal_odd_of_origin U E hunr hsup hchar ht hres hd0 hx thetaU thetaE
      hcondU hcondE Theta hcU hcE eta heta tau Psi hdet O D
    simpa only [O.psiU_character, O.psiE_character] using h

end ActualCharacters

section InitialNormalization
private theorem minimal_parameter_trace
    (k l : Type*) [Field k] [Field l] [Finite k] [Finite l]
    [CharP k 2] [Algebra k l] (hdegree : Module.finrank k l = 2)
    (d : l) (hd : trace k l d = 1) (c : k)
    (hrel : d ^ 2 - d = algebraMap k l c) : absoluteTraceTwo k c = 1 := by
  letI : Fintype k := Fintype.ofFinite k
  letI : CharP l 2 := charP_of_injective_algebraMap (algebraMap k l).injective 2
  have hne : absoluteTraceTwo k c ≠ 0 := by
    intro hz
    obtain ⟨b, hb⟩ := (absoluteTraceTwo_eq_zero_iff k c).mp hz
    have hroot : (d - algebraMap k l b) * (d - algebraMap k l b - 1) = 0 := by
      rw [hb, map_add, map_pow] at hrel
      linear_combination hrel + CharTwo.add_self_eq_zero (algebraMap k l b) +
        CharTwo.add_self_eq_zero (algebraMap k l b ^ 2) -
        CharTwo.add_self_eq_zero (d * algebraMap k l b)
    rcases mul_eq_zero.mp hroot with h | h
    · have heq : d = algebraMap k l b := sub_eq_zero.mp h
      rw [heq, trace_algebraMap, hdegree, two_smul, CharTwo.add_self_eq_zero] at hd
      exact zero_ne_one hd
    · have heq : d = algebraMap k l (b + 1) := by
        rw [map_add, map_one]
        linear_combination h
      rw [heq, trace_algebraMap, hdegree, two_smul, CharTwo.add_self_eq_zero] at hd
      exact zero_ne_one hd
  have hval : (absoluteTraceTwo k c).val < 2 := ZMod.val_lt _
  have hvalne : (absoluteTraceTwo k c).val ≠ 0 := by simpa using hne
  have hvalone : (absoluteTraceTwo k c).val = 1 := by omega
  apply ZMod.val_injective 2
  exact hvalone

open private critical_residue_map from LanglandsSecondMainLemma.Dyadic.UR.MinimalFunctions
open private minimal_quadratic_relation minimal_conjugates
  from LanglandsSecondMainLemma.Dyadic.UR.MinimalOrigin

/-- Construct the paper's unramified quadratic generator by lifting trace
one through the integral trace map. Its parameter has absolute trace one;
no characteristic-zero Hensel root or supplied generator is required. -/
theorem minimal_generator
    (F U : Type) [Field F] [Field U]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
    [Algebra F U] [ValuativeExtension F U] [Module.Finite F U] [IsGalois F U]
    (hunr : ramificationIndex F U = 1) (hU : Module.finrank F U = 2)
    (hchar : residueCharacteristic F = 2) :
    ∃ (sigma : Gal(U/F)) (c : F) (d : U), sigma ≠ 1 ∧
      ord F c = 0 ∧ ord U d = 0 ∧ d ^ 2 - d = algebraMap F U c ∧ sigma d = 1 - d ∧
      ∃ hc : c ∈ lattice F 0,
        (@absoluteTraceTwo (ResidueField F) _ (ringChar.of_eq hchar)) (reduce F c hc) = 1 := by
  letI : CharP (ResidueField F) 2 := ringChar.of_eq hchar
  letI : CharP (ResidueField U) 2 :=
    charP_of_injective_algebraMap (algebraMap (ResidueField F) (ResidueField U)).injective 2
  obtain ⟨dO, hdO⟩ := integralTrace_surjective F U hunr 1
  have hdtrace : trace F U (dO : U) = 1 := by
    rw [← coe_integralTrace, hdO, Subring.coe_one]
  have hrdtrace : trace (ResidueField F) (ResidueField U) (residueMap U dO) = 1 := by
    rw [residue_trace F U hunr, hdO, map_one]
  have hrdne : residueMap U dO ≠ 0 := by
    intro h
    rw [h, map_zero] at hrdtrace
    exact zero_ne_one hrdtrace
  have hdord : ord U (dO : U) = 0 := by
    apply le_antisymm
    · apply le_of_not_gt
      intro h
      exact hrdne ((IsLocalRing.residue_eq_zero_iff dO).mpr
        ((ord_pos_iff_mem_maximalIdeal U dO).mp h))
    · exact (ord_nonneg_iff_mem_integer U _).mpr dO.property
  let c := -norm F U (dO : U)
  have hc : ord F c = 0 := by rw [ord_neg, ord_norm, hdord, nsmul_zero]
  have hc0 : c ∈ lattice F 0 := by rw [mem_lattice, hc]; simp
  let cO : ringOfIntegers F := ⟨c, (mem_lattice_zero_iff F).mp hc0⟩
  have hdc : (dO : U) ^ 2 - (dO : U) = algebraMap F U c := by
    have h := minimal_quadratic_relation F U hU (dO : U)
    rw [hdtrace, map_one, one_mul] at h
    dsimp only [c]
    rw [map_neg]
    linear_combination h
  have hdcO : dO ^ 2 - dO = algebraMap (ringOfIntegers F) (ringOfIntegers U) cO := by
    apply Subtype.ext
    exact hdc
  have hdcres : residueMap U dO ^ 2 - residueMap U dO =
      algebraMap (ResidueField F) (ResidueField U) (residueMap F cO) := by
    have h := congrArg (residueMap U) hdcO
    rw [map_sub, map_pow, critical_residue_map F U cO] at h
    exact h
  have hrdeg : Module.finrank (ResidueField F) (ResidueField U) = 2 := by
    rw [← residueDegree_eq_finrank_residueField]
    have h := finrank_eq_ramificationIndex_mul_residueDegree F U
    simpa only [hunr, hU, one_mul] using h.symm
  have hctrace := minimal_parameter_trace (ResidueField F) (ResidueField U) hrdeg
    (residueMap U dO) hrdtrace (residueMap F cO) hdcres
  obtain ⟨sigma, hsigma⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, hU]; omega) (1 : Gal(U/F))
  have hconj : sigma (dO : U) = 1 - (dO : U) := by
    have h := (minimal_conjugates F U hU sigma hsigma (dO : U)).1
    rw [hdtrace, map_one] at h
    linear_combination -h
  exact ⟨sigma, c, (dO : U), hsigma, hc, hdord, hdc, hconj, hc0, hctrace⟩
end InitialNormalization

section AdditiveNormalization
open private normChoice_coefficient_at_depth from LanglandsSecondMainLemma.Dyadic.UR.NormChoice
variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
/-- Construct the scaled additive chart from the actual ramified norm
character, using its full ordinary stationary ideal. -/
theorem minimal_normalization (tau : LocalQuasiCharData F)
    (psi : LocalAddCharData F) {t : ℕ} (htpos : 0 < t) (ht : tau.conductor = t + 1) :
    ∃ alpha : Fˣ, (scaleAddCharData F psi alpha).conductor = -((t + 1 : ℕ) : ℤ) ∧
      ∀ (z : F) (hz : z ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
        tau.character (principalUnitOf F (t / 2) (-z) (neg_mem_lattice F hz)) =
          (scaleAddCharData F psi alpha).character z := by
  let m := tau.conductor
  let hs := lamprechtFormula_stationaryDepth F tau (m / 2) (m % 2)
    (by omega) (by omega) (by omega)
  obtain ⟨a, ha, hchart⟩ := normChoice_coefficient_at_depth F tau.character psi tau.isConductor hs
  have hane : a ≠ 0 := (ord_ne_top_iff F).mp (by rw [ha]; simp)
  let alpha := Units.mk0 a hane
  have horder : unitOrder F alpha = -psi.conductor - (tau.conductor : ℤ) := by
    apply WithTop.coe_injective
    rw [← ord_coe_eq_unitOrder]
    exact ha
  refine ⟨alpha, ?_, ?_⟩
  · rw [scaleAddCharData_conductor, horder, ht]
    omega
  · intro z hz
    rw [scaleAddCharData_character_apply]
    have hdepth : tau.conductor / 2 + tau.conductor % 2 = t / 2 + 1 := by omega
    apply hchart z (by simpa only [m, hdepth] using hz) _
    simp [coe_principalUnitOf, sub_eq_add_neg]

private theorem minimal_additive_scale (theta : LocalQuasiCharData F) (psi : LocalAddCharData F) (a : Fˣ) :
    localConstant F theta.character (scaleAddCharData F psi a).character =
      (theta.character a : ℂ) * localConstant F theta.character psi.character := by
  let gamma : AdmissibleGamma F theta psi := Classical.choice (AdmissibleGamma.exists_admissible (F := F))
  let gammaa : AdmissibleGamma F theta (scaleAddCharData F psi a) :=
    Classical.choice (AdmissibleGamma.exists_admissible (F := F))
  rw [localConstant_isDeltaFinite F theta (scaleAddCharData F psi a) gammaa,
    localConstant_isDeltaFinite F theta psi gamma]
  exact delta_additive_scale F theta psi a gamma gammaa
end AdditiveNormalization


private theorem minimal_trace_scale
    (F L : Type) [Field F] [Field L]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra F L] [ValuativeExtension F L] [Module.Finite F L]
    (psiF : LocalAddCharData F) (psiL : LocalAddCharData L)
    (hpsi : psiL.character = tracePullbackAddChar F L psiF.character) (alpha : Fˣ) :
    tracePullbackAddChar F L (scaleAddCharData F psiF alpha).character =
      (scaleAddCharData L psiL (Units.map (algebraMap F L).toMonoidHom alpha)).character := by
  apply ContinuousAddChar.ext
  intro z
  rw [scaleAddCharData_character_apply, hpsi]
  change psiF.character ((alpha : F) * trace F L z) =
    psiF.character (trace F L (algebraMap F L (alpha : F) * z))
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

section PrimitivePair
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

open private commonOrigin_kleinFour from LanglandsSecondMainLemma.Stationary.CommonOrigin
open private twist_ramified_edge from LanglandsSecondMainLemma.Dyadic.UR.Twist
open private normCharacterProduct_two primeNormCharacter_card
  from LanglandsSecondMainLemma.Characters.Conjugacy

/-- The minimal comparison for an arbitrary primitive pair in the paper's
normalized setup. `twist` constructs the full models and base character,
`conjugacy` proves the corrected restriction, and `minimal_of_charts`
constructs all stationary and residual data. The initial additive chart
and unramified generator are still explicit ambient data here. -/
theorem minimal_normalized
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (U E : IntermediateField F K)
    (hU : Module.finrank F U = 2) (hE : Module.finrank F E = 2)
    (hsup : U ⊔ E = ⊤) (hchar : residueCharacteristic F = 2) :
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
      (t : ℕ) (_ht : PrimeCyclicExtension.IsLowerBreak F E t)
      (htpos : 0 < t) (_hres : residueDegree F E = 1)
      (eta : NormCharacter F U) (_heta : eta ≠ 1)
      (tau : NormCharacter F E) (_htau : tau ≠ 1)
      (Psi : ContinuousAddChar F)
      (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
      (_hchart : ∀ (z : F) (hz : z ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
        tau.1 (principalUnitOf F (t / 2) (-z) (neg_mem_lattice F hz)) = Psi z)
      (sigma : Gal(U/F)) (hsigma : sigma ≠ 1)
      (c : F) (hc : ord F c = 0) (d : U) (_hd : ord U d = 0)
      (_hdc : d ^ 2 - d = algebraMap F U c) (_hconj : sigma d = 1 - d)
      (_hcTrace : (@absoluteTraceTwo (ResidueField F) _ (ringChar.of_eq hchar))
        (reduce F c (by rw [mem_lattice, hc]; simp)) = 1)
      (thetaU : LocalQuasiCharData U) (thetaE : LocalQuasiCharData E)
      (_hcondU : thetaU.conductor = t + 1) (_hcondE : thetaE.conductor = t + 1)
      (Theta : ContinuousQuasiChar K)
      (_hcU : normQuasiChar U K thetaU.character = Theta)
      (_hcE : normQuasiChar E K thetaE.character = Theta)
      (_hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Theta),
    Characters.restrictQuasiChar F U thetaU.character * eta.1 =
      Characters.restrictQuasiChar F E thetaE.character * tau.1 ∧
    localConstant U thetaU.character (tracePullbackAddChar F U Psi) * localConstant F eta.1 Psi =
      localConstant E thetaE.character (tracePullbackAddChar F E Psi) * localConstant F tau.1 Psi := by
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
  intro hunr t ht htpos hres eta heta tau htau Psi hPsi hchart sigma hsigma c hc d hd hdc
    hconj hcTrace thetaU thetaE hcondU hcondE Theta hcU hcE hprimitive
  have dataU := Basic.intermediateField_tower_compatible Nat.prime_two hG U hU
  have dataE := Basic.intermediateField_tower_compatible Nat.prime_two hG E hE
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F U dataU.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension U K dataU.2.2.2.2.2.2.2.2.2.2.2.2
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E dataE.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension E K dataE.2.2.2.2.2.2.2.2.2.2.2.2
  letI : IsKleinFour Gal(K/F) := commonOrigin_kleinFour hG
  letI : Algebra.IsQuadraticExtension F U := ⟨hU⟩
  letI : Algebra.IsQuadraticExtension F E := ⟨hE⟩
  letI : Algebra.IsQuadraticExtension U K := ⟨dataU.2.2.2.2.2.2.2.2.2.2.1⟩
  letI : Algebra.IsQuadraticExtension E K := ⟨dataE.2.2.2.2.2.2.2.2.2.2.1⟩
  have hcomp := hcU.trans hcE.symm
  have hprimitive' : ¬ ∃ lambda : ContinuousQuasiChar F,
      normQuasiChar F K lambda = normQuasiChar U K thetaU.character := by
    simpa only [hcU] using hprimitive
  obtain ⟨chiU, chiE, lambda, nu, h, _, _, _, _, _, _, _, hmodelU, hmodelE,
    htwistU, htwistE, hthetaU, _, _, hlambda⟩ :=
    twist hG U E hU hE hunr t ht htpos hres tau htau Psi hPsi hchart sigma hsigma
      c hc d hd hdc hconj thetaU.character thetaE.character hcomp hprimitive'
  have hh : h = 0 := by
    have heq := hthetaU.unique thetaU.isConductor
    rw [hcondU] at heq
    omega
  have hlambda' : multiplicativeConductorExponent F lambda ≤ t + 1 := hlambda hh
  obtain ⟨hne, _, _, _⟩ := twist_ramified_edge F U E K hunr ht hres tau htau
  have hrestriction := (Characters.conjugacy Nat.prime_two hG U E hU hE hne
    thetaU.character thetaE.character Theta hcU hcE hprimitive).2.2.1
  letI := primeCyclicNormCharacter_finite F U
  letI := primeCyclicNormCharacter_finite F E
  change Characters.restrictQuasiChar F U thetaU.character * Characters.normCharacterProduct F U =
    Characters.restrictQuasiChar F E thetaE.character * Characters.normCharacterProduct F E
    at hrestriction
  rw [normCharacterProduct_two F U ((primeNormCharacter_card F U).trans hU) eta heta,
    normCharacterProduct_two F E ((primeNormCharacter_card F E).trans hE) tau htau]
    at hrestriction
  have hminus := DFunLike.congr_fun hrestriction (-1)
  have hetaMinus : eta.1 (-1) = 1 :=
    (unramifiedNormCharacter_conductor F U hunr eta).trivial (-1)
      (by rw [mem_unitFiltration_zero]; simp)
  change thetaU.character (Units.map (algebraMap F U).toMonoidHom (-1)) * eta.1 (-1) =
    thetaE.character (Units.map (algebraMap F E).toMonoidHom (-1)) * tau.1 (-1) at hminus
  have hmap {L : Type} [Field L] [Algebra F L] :
      Units.map (algebraMap F L).toMonoidHom (-1 : Fˣ) = (-1 : Lˣ) := by
    ext
    simp
  rw [hmap, hmap, hetaMinus, mul_one] at hminus
  refine ⟨hrestriction, ?_⟩
  exact minimal_of_charts U E hunr hsup hchar ht htpos hres eta heta tau htau Psi hPsi
    hchart sigma hsigma c hc d hd hdc hconj hcTrace chiU (chiE * nu.1) thetaU thetaE
    lambda hmodelU hmodelE htwistU htwistE hlambda' hcondU hcondE Theta hcU hcE hminus

/-- **Paper Theorem 10.8 (`D:UR:minimal`).** Every primitive compatible
pair of conductor `T = t+1` in the actual unramified/ramified biquadratic
diamond has equal complete local-constant products.

The additive character is arbitrary and nontrivial. Its normalization,
the unramified generator, the full model characters, the common twist,
the norm representatives, and the odd residual data are constructed.
Both field characteristics and nonunitary quasi-characters are retained.
The unramified quadratic factor is included before its sign cancels. -/
theorem minimal
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (U E : IntermediateField F K)
    (hU : Module.finrank F U = 2) (hE : Module.finrank F E = 2)
    (hsup : U ⊔ E = ⊤) (hchar : residueCharacteristic F = 2) :
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
      (t : ℕ) (_ht : PrimeCyclicExtension.IsLowerBreak F E t)
      (_htpos : 0 < t) (_hres : residueDegree F E = 1)
      (eta : NormCharacter F U) (_heta : eta ≠ 1)
      (tau : NormCharacter F E) (_htau : tau ≠ 1)
      (thetaU : LocalQuasiCharData U) (thetaE : LocalQuasiCharData E)
      (_hcondU : thetaU.conductor = t + 1) (_hcondE : thetaE.conductor = t + 1)
      (Theta : ContinuousQuasiChar K)
      (_hcU : normQuasiChar U K thetaU.character = Theta)
      (_hcE : normQuasiChar E K thetaE.character = Theta)
      (_hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Theta)
      (psiF : LocalAddCharData F),
    localConstant U thetaU.character (tracePullbackAddChar F U psiF.character) *
        localConstant F eta.1 psiF.character =
      localConstant E thetaE.character (tracePullbackAddChar F E psiF.character) *
        localConstant F tau.1 psiF.character := by
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
  intro hunr t ht htpos hres eta heta tau htau thetaU thetaE hcondU hcondE Theta
    hcU hcE hprimitive psiF
  have dataU := Basic.intermediateField_tower_compatible Nat.prime_two hG U hU
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F U dataU.2.2.2.2.2.2.2.2.2.2.2.1
  have dataE := Basic.intermediateField_tower_compatible Nat.prime_two hG E hE
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E dataE.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  let tauData : LocalQuasiCharData F := ⟨tau.1, t + 1,
    ramifiedNormCharacter_conductor F E ht hres pi hpi hgen tau htau⟩
  let etaData := canonicalLocalQuasiCharData F eta.1
  obtain ⟨alpha, hconductor, hchart⟩ := minimal_normalization F tauData psiF htpos rfl
  let Psi := scaleAddCharData F psiF alpha
  have hPsi : IsAdditiveConductor F Psi.character (-((t + 1 : ℕ) : ℤ)) :=
    hconductor ▸ Psi.isConductor
  obtain ⟨sigma, c, d, hsigma, hc, hd, hdc, hconj, hc0, hcTrace⟩ :=
    minimal_generator F U hunr hU hchar
  obtain ⟨hrestriction, hnormalized⟩ := minimal_normalized hG U E hU hE hsup hchar hunr t ht
    htpos hres eta heta tau htau Psi.character hPsi hchart sigma hsigma c hc d hd hdc hconj
    hcTrace thetaU thetaE hcondU hcondE Theta hcU hcE hprimitive
  let psiU := canonicalLocalAddCharData U (tracePullbackAddChar F U psiF.character)
    (Basic.tracePullbackAddChar_ne_one F U psiF.character psiF.character_ne_one)
  let psiE := canonicalLocalAddCharData E (tracePullbackAddChar F E psiF.character)
    (Basic.tracePullbackAddChar_ne_one F E psiF.character psiF.character_ne_one)
  have hscaleU := minimal_additive_scale U thetaU psiU
    (Units.map (algebraMap F U).toMonoidHom alpha)
  have hscaleE := minimal_additive_scale E thetaE psiE
    (Units.map (algebraMap F E).toMonoidHom alpha)
  have hscaleEta := minimal_additive_scale F etaData psiF alpha
  have hscaleTau := minimal_additive_scale F tauData psiF alpha
  have htraceU := minimal_trace_scale F U psiF psiU rfl alpha
  have htraceE := minimal_trace_scale F E psiF psiE rfl alpha
  change localConstant U thetaU.character (tracePullbackAddChar F U Psi.character) *
      localConstant F etaData.character Psi.character =
    localConstant E thetaE.character (tracePullbackAddChar F E Psi.character) *
      localConstant F tauData.character Psi.character at hnormalized
  rw [htraceU, htraceE, hscaleU, hscaleE, hscaleEta, hscaleTau] at hnormalized
  let A := thetaU.character (Units.map (algebraMap F U).toMonoidHom alpha)
  let B := thetaE.character (Units.map (algebraMap F E).toMonoidHom alpha)
  have hcoef : (A : ℂ) * (eta.1 alpha : ℂ) = (B : ℂ) * (tau.1 alpha : ℂ) := by
    have h := DFunLike.congr_fun hrestriction alpha
    exact congrArg (fun z : ℂˣ => (z : ℂ)) h
  have hproduct : ((A : ℂ) * (eta.1 alpha : ℂ)) *
      (localConstant U thetaU.character psiU.character * localConstant F eta.1 psiF.character) =
    ((A : ℂ) * (eta.1 alpha : ℂ)) *
      (localConstant E thetaE.character psiE.character * localConstant F tau.1 psiF.character) := by
    calc
      _ = ((A : ℂ) * localConstant U thetaU.character psiU.character) *
          ((eta.1 alpha : ℂ) * localConstant F eta.1 psiF.character) := by ring
      _ = ((B : ℂ) * localConstant E thetaE.character psiE.character) *
          ((tau.1 alpha : ℂ) * localConstant F tau.1 psiF.character) := hnormalized
      _ = ((B : ℂ) * (tau.1 alpha : ℂ)) *
          (localConstant E thetaE.character psiE.character *
            localConstant F tau.1 psiF.character) := by ring
      _ = _ := by rw [← hcoef]
  exact mul_left_cancel₀ (mul_ne_zero A.ne_zero (eta.1 alpha).ne_zero) hproduct

end PrimitivePair

end
end LanglandsSecondMainLemma.Dyadic.UR
