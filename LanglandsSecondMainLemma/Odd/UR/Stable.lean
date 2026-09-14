import LanglandsFirstMainLemma.Delta.FirstMainStatement
import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsFirstMainLemma.Main
import LanglandsFirstMainLemma.Parameters.High
import LanglandsFirstMainLemma.Parameters.StationaryClassUnderNorm
import LanglandsSecondMainLemma.Odd.UR.Twist
import LanglandsSecondMainLemma.Characters.Conjugacy

/-!
# Odd / UR / Stable

The stable range in `references/epsilon_SML.tex`, lines 1749--1781, in the
setup of `O:I:main` and `O:I:actualtwist`. All local constants below are FML's
canonical constants. The common denominator and coefficient are constructed
from FML's high parameter table, including the different on the ramified edge.
-/

namespace LanglandsSecondMainLemma.Odd.UR
noncomputable section
open LanglandsFirstMainLemma
open scoped BigOperators

private theorem halfDecomposition {m : ℕ} (hm : 1 < m) :
    IsStationaryConductorDecomposition m (m / 2) (m % 2) :=
  ⟨hm, by omega, by omega⟩

section OneField
variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private theorem stationaryRepresentative_exists
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {d e : ℕ} (h : IsStationaryConductorDecomposition chi.conductor d e)
    (Gamma : AdmissibleGamma F chi psi) :
    Nonempty (StationaryClassRepresentative F chi psi h Gamma Gamma.property) := by
  obtain ⟨c, hc⟩ := latticeQuotientMk_surjective F (Int.natCast_nonneg d)
    (stationaryCoefficientClass F chi psi h Gamma Gamma.property)
  exact ⟨⟨c, hc⟩⟩

/-- Exact stable twist, with the supplied coefficient and the canonical
local constant. No unitarity hypothesis is used. -/
theorem localConstant_stableTwist
    (nu chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {d e : ℕ} (h : IsStationaryConductorDecomposition chi.conductor d e)
    (hnu : nu.conductor ≤ d) (Gamma : AdmissibleGamma F chi psi)
    (R : StationaryClassRepresentative F chi psi h Gamma Gamma.property) :
    localConstant F (nu.character * chi.character) psi.character =
      (nu.character ((Gamma : Fˣ) / R.unit) : ℂ) *
        localConstant F chi.character psi.character := by
  have hs := stableTwist F nu chi psi d e h.epsilon_le_one h.conductor_eq
    h.conductor_gt_one hnu Gamma R.toLamprecht R.toLamprecht_represents
  have he : stableStationaryRepresentativeUnit F chi psi
      (stableTwist_stationaryDepth F chi d e h.epsilon_le_one h.conductor_eq
        h.conductor_gt_one) Gamma R.toLamprecht R.toLamprecht_represents = R.unit := by
    apply Units.ext
    rfl
  dsimp only at hs
  rw [he] at hs
  rw [← localConstant_isDeltaFinite F, ← localConstant_isDeltaFinite F] at hs
  exact hs
end OneField

section Edge
variable (F L : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra F L] [ValuativeExtension F L] [Module.Finite F L]
  [PrimeCyclicExtension F L]

private theorem normCharacter_card : Nat.card (NormCharacter F L) = Module.finrank F L := by
  by_cases hu : ramificationIndex F L = 1
  · exact unramifiedNormCharacter_card F L hu
  · let P := primeCyclicPreparation F L hu
    exact ramifiedNormCharacter_card F L P.ht P.hres P.piK P.hpiK P.hgen

private theorem normCharacter_values_product [Fintype (NormCharacter F L)]
    (hodd : Odd (Module.finrank F L)) (x : Fˣ) :
    (∏ nu : NormCharacter F L, (nu.1 x : ℂ)) = 1 := by
  have hc : Odd (Nat.card (NormCharacter F L)) := (normCharacter_card F L).symm ▸ hodd
  have hp : (∏ nu : NormCharacter F L, nu) = 1 := by
    apply Finset.prod_ninvolution Inv.inv
    · intro nu; exact mul_inv_cancel nu
    · intro nu hnu hi
      have hs : nu ^ 2 = 1 := by simpa only [hi, pow_two] using inv_mul_cancel nu
      have hn := pow_card_eq_one' (x := nu)
      obtain ⟨k, hk⟩ := hc
      rw [hk, pow_add, pow_mul, hs, one_pow, pow_one, one_mul] at hn
      exact hnu hn
    · intro nu; exact Finset.mem_univ _
    · intro nu; exact inv_inv nu
  let ev : NormCharacter F L →* ℂˣ :=
    { toFun := fun nu => nu.1 x, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have he := congrArg (fun nu => (ev nu : ℂ)) hp
  simpa [map_prod, Units.coe_prod, ev] using he

private theorem normCharacter_constants_product [Fintype (NormCharacter F L)]
    (hodd : Odd (Module.finrank F L)) (psi : LocalAddCharData F) :
    (∏ nu : NormCharacter F L, localConstant F nu.1 psi.character) = 1 := by
  letI : Fintype (normCharacterSubgroup F L) :=
    inferInstanceAs (Fintype (NormCharacter F L))
  have hc : Fintype.card (normCharacterSubgroup F L) = Module.finrank F L :=
    (Nat.card_eq_fintype_card.symm).trans (normCharacter_card F L)
  let data := fun nu : NormCharacter F L => canonicalLocalQuasiCharData F nu.1
  let gam := fun nu => Classical.choice (AdmissibleGamma.exists_admissible
    (F := F) (χ := data nu) (ψ := psi))
  have hp := delta_odd_prime_character_product F (normCharacterSubgroup F L)
    (hc.symm ▸ PrimeCyclicExtension.degree_prime F L) (hc.symm ▸ hodd)
    psi data (fun _ => rfl) gam
  convert hp using 1
  apply Finset.prod_congr rfl
  intro nu _
  exact localConstant_isDeltaFinite F (data nu) psi (gam nu)

/-- FML and all lower norm-character stable twists. The complete correction
product and the complete twist product are both retained in the proof. -/
private theorem stable_normPullback_power
    (hodd : Odd (Module.finrank F L))
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {d e : ℕ} (h : IsStationaryConductorDecomposition chi.conductor d e)
    (hbound : ∀ nu : NormCharacter F L, multiplicativeConductorExponent F nu.1 ≤ d)
    (Gamma : AdmissibleGamma F chi psi)
    (R : StationaryClassRepresentative F chi psi h Gamma Gamma.property) :
    localConstant L (normQuasiChar F L chi.character)
        (tracePullbackAddChar F L psi.character) =
      localConstant F chi.character psi.character ^ Module.finrank F L := by
  letI := primeCyclicNormCharacter_finite F L
  letI := Fintype.ofFinite (NormCharacter F L)
  have hf := firstMainLemma F L (PrimeCyclicExtension.toCyclicPrimeExtension (F := F) (K := L))
    chi.character psi.character psi.character_ne_one
  change localConstant L (normQuasiChar F L chi.character)
      (tracePullbackAddChar F L psi.character) *
      (∏ nu : NormCharacter F L, localConstant F nu.1 psi.character) =
    (∏ nu : NormCharacter F L, localConstant F (nu.1 * chi.character) psi.character) at hf
  rw [normCharacter_constants_product F L hodd psi, mul_one] at hf
  rw [hf]
  calc
    _ = ∏ nu : NormCharacter F L,
        (nu.1 ((Gamma : Fˣ) / R.unit) : ℂ) * localConstant F chi.character psi.character := by
      apply Finset.prod_congr rfl
      intro nu _
      exact localConstant_stableTwist F (canonicalLocalQuasiCharData F nu.1)
        chi psi h (hbound nu) Gamma R
    _ = _ := by
      rw [Finset.prod_mul_distrib, normCharacter_values_product F L hodd,
        one_mul, Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
        normCharacter_card F L]

/-- The unramified high row carries the chosen base coefficient literally
through field inclusion, at its actual coefficient depth. -/
private def unramifiedRepresentative
    (chiF : LocalQuasiCharData F) (chiL : LocalQuasiCharData L)
    (psiF : LocalAddCharData F) (psiL : LocalAddCharData L)
    {d e : ℕ} (h : IsStationaryConductorDecomposition chiF.conductor d e)
    (hchi : chiL.character = chiF.character.compNorm)
    (hpsi : psiL.character = psiF.character.compTrace)
    (hunr : ramificationIndex F L = 1) (Gamma : AdmissibleGamma F chiF psiF)
    (R : StationaryClassRepresentative F chiF psiF h Gamma Gamma.property) :
    StationaryClassRepresentative L chiL psiL
      (highParameter_unramified_sourceDecomposition F L chiF chiL h hchi hunr)
      (Units.map (algebraMap F L) (Gamma : Fˣ))
      (highParameter_unramified_commonDenominator F L chiF chiL psiF psiL
        hchi hpsi hunr Gamma Gamma.property) := by
  let c : lattice L 0 := ⟨algebraMap F L (R.representative : F), by
    rw [mem_lattice, ord_algebraMap, hunr, one_nsmul]
    exact R.representative.property⟩
  refine ⟨c, ?_⟩
  rw [highParameter_unramified F L chiF chiL psiF psiL h hchi hpsi hunr
    Gamma Gamma.property, ← R.represents, denominatorScaledAlgebraMap_common_mk]

end Edge

section CommonCovector
variable (F E U : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Field U] [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F E] [Algebra F U] [ValuativeExtension F E] [ValuativeExtension F U]
  [Module.Finite F E] [Module.Finite F U]
  [PrimeCyclicExtension F E] [PrimeCyclicExtension F U]

/-- The exact stable bounds, including `h = T`. The natural conductors here
are nonnegative; all valuation and ideal exponents remain integers. -/
theorem stable_core_bounds {p t h : ℕ} (hp : 1 ≤ p) (hh : t + 1 ≤ h) :
    t + 1 ≤ (t + 1 + h) / 2 ∧ t + 1 ≤ (t + 1 + p * h) / 2 := by
  have hm : h ≤ p * h := by nlinarith
  omega

/-- Construct a single base covector for both actual lower-field twists.
The ramified denominator includes the different, and the coefficient is
transported by the proved FML stable high row. -/
theorem stable_common_covector
    {p t h : ℕ} (hp : p.Prime) (hodd : Odd p) (htpos : 0 < t)
    (hE : Module.finrank F E = p) (hU : Module.finrank F U = p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hunr : ramificationIndex F U = 1)
    (hh : t + 1 ≤ h)
    (lambda : ContinuousQuasiChar F)
    (hlambda : IsMultiplicativeConductor F lambda (t + 1 + h))
    (nuU : LocalQuasiCharData U) (nuE : LocalQuasiCharData E)
    (hnuU : nuU.conductor ≤ t + 1) (hnuE : nuE.conductor ≤ t + 1)
    (psi : LocalAddCharData F) :
    ∃ a : Fˣ,
      localConstant U (nuU.character * normQuasiChar F U lambda)
          (tracePullbackAddChar F U psi.character) =
        (nuU.character (Units.map (algebraMap F U) a) : ℂ) *
          localConstant F lambda psi.character ^ p ∧
      localConstant E (nuE.character * normQuasiChar F E lambda)
          (tracePullbackAddChar F E psi.character) =
        (nuE.character (Units.map (algebraMap F E) a) : ℂ) *
          localConstant F lambda psi.character ^ p := by
  obtain ⟨pi, hpi, hgen⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one F E hres
  have hb := stable_core_bounds hp.one_lt.le hh
  let chiF : LocalQuasiCharData F := ⟨lambda, t + 1 + h, hlambda⟩
  let chiU : LocalQuasiCharData U := ⟨normQuasiChar F U lambda, t + 1 + h,
    (unramified_multiplicativeConductor_compNorm F U hunr lambda _).2 hlambda⟩
  have hcE : IsMultiplicativeConductor E (normQuasiChar F E lambda) (t + 1 + p * h) := by
    have hc := multiplicativeConductor_compNorm_high F E ht hres pi hpi hgen
      (by omega : t + 1 < t + 1 + h) hlambda
    have ha : herbrandPsiNat t (Module.finrank F E) (t + 1 + h - 1) + 1 =
        t + 1 + p * h := by
      rw [hE, herbrandPsiNat, min_eq_right (by omega)]
      have he : t + 1 + h - 1 - t = h := by omega
      rw [he]
      omega
    exact ha ▸ hc
  let chiE : LocalQuasiCharData E := ⟨normQuasiChar F E lambda, t + 1 + p * h, hcE⟩
  let psiU := canonicalLocalAddCharData U (tracePullbackAddChar F U psi.character)
    (Basic.tracePullbackAddChar_ne_one F U psi.character psi.character_ne_one)
  let psiE := canonicalLocalAddCharData E (tracePullbackAddChar F E psi.character)
    (Basic.tracePullbackAddChar_ne_one F E psi.character psi.character_ne_one)
  have hF := halfDecomposition (show 1 < chiF.conductor by dsimp [chiF]; omega)
  have hEE := halfDecomposition (show 1 < chiE.conductor by dsimp [chiE]; omega)
  let Gamma : AdmissibleGamma F chiF psi := Classical.choice AdmissibleGamma.exists_admissible
  obtain ⟨R⟩ := stationaryRepresentative_exists F chiF psi hF Gamma
  let HU := highConductorParameter_unramified F U chiF chiU psi psiU hF rfl rfl
    hunr Gamma Gamma.property
  let HE := highConductorParameter_stableOdd F E ht hres pi hpi hgen chiF chiE psi psiE
    hF hEE rfl rfl (hE.symm ▸ hodd) hb.1 Gamma Gamma.property
  let GammaU : AdmissibleGamma U chiU psiU :=
    ⟨Units.map (algebraMap F U) (Gamma : Fˣ), HU.commonDenominator⟩
  let GammaE : AdmissibleGamma E chiE psiE :=
    ⟨Units.map (algebraMap F E) (Gamma : Fˣ), HE.commonDenominator⟩
  let RU := unramifiedRepresentative F U chiF chiU psi psiU hF rfl rfl hunr Gamma R
  let RE := HE.upstairsRepresentative F E ht hres pi hpi hgen chiF chiE psi psiE
    hF hEE rfl rfl (hE.symm ▸ hodd) hb.1 Gamma Gamma.property R
  have hRU : RU.unit = Units.map (algebraMap F U) R.unit := by apply Units.ext; rfl
  have hRE : RE.unit = Units.map (algebraMap F E) R.unit := by apply Units.ext; rfl
  have hpowerU := stable_normPullback_power F U (hU.symm ▸ hodd) chiF psi hF (by
    intro nu
    have hc := unramifiedNormCharacter_conductor F U hunr nu
    have he := (multiplicativeConductorExponent_isConductor F nu.1).unique hc
    rw [he]; exact Nat.zero_le _) Gamma R
  have hpowerE := stable_normPullback_power F E (hE.symm ▸ hodd) chiF psi hF (by
    intro nu
    by_cases hn : nu = 1
    · subst nu
      have hc : IsMultiplicativeConductor F (1 : ContinuousQuasiChar F) 0 :=
        IsMultiplicativeConductor.of_zero (fun _ _ => rfl)
      have he := (multiplicativeConductorExponent_isConductor F
        (1 : ContinuousQuasiChar F)).unique hc
      change multiplicativeConductorExponent F (1 : ContinuousQuasiChar F) ≤ _
      rw [he]; exact Nat.zero_le _
    · have hc := ramifiedNormCharacter_conductor F E ht hres pi hpi hgen nu hn
      rw [(multiplicativeConductorExponent_isConductor F nu.1).unique hc]
      exact hb.1) Gamma R
  rw [hU] at hpowerU
  rw [hE] at hpowerE
  change localConstant U chiU.character psiU.character =
    localConstant F lambda psi.character ^ p at hpowerU
  change localConstant E chiE.character psiE.character =
    localConstant F lambda psi.character ^ p at hpowerE
  refine ⟨(Gamma : Fˣ) / R.unit, ?_, ?_⟩
  · have hs := localConstant_stableTwist U nuU chiU psiU HU.sourceDecomposition
      (hnuU.trans hb.1) GammaU RU
    rw [hRU, hpowerU] at hs
    simpa only [GammaU, ← map_div, chiU, psiU, canonicalLocalAddCharData_character] using hs
  · have hs := localConstant_stableTwist E nuE chiE psiE hEE
      (hnuE.trans hb.2) GammaE RE
    rw [hRE, hpowerE] at hs
    simpa only [GammaE, ← map_div, chiE, psiE, canonicalLocalAddCharData_character] using hs
end CommonCovector

section ActualPair
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

/-- Stable part of `O:I:main` (paper lines 1749--1781).

`M` and `D` are the actual models and twist constructed by `models` and
`twist`; no stationary representative, common restriction, or phase identity
is assumed. The conductor condition is exactly `h ≥ T`, with `T = t+1`.
The two complete lower correction products are also proved to be one. -/
theorem oddUR_stable_comparison
    {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (U E : IntermediateField F K)
    (hU : Module.finrank F U = p) (hE : Module.finrank F E = p)
    (hne : Ramification.intermediateNormRange U ≠ Ramification.intermediateNormRange E) :
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
      (Basic.intermediateField_tower_compatible hp hG U hU).2.2.2.2.2.2.2.2.2.2.2.1
    letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E
      (Basic.intermediateField_tower_compatible hp hG E hE).2.2.2.2.2.2.2.2.2.2.2.1
    letI := primeCyclicNormCharacter_finite F U
    letI := primeCyclicNormCharacter_finite F E
    ∀ {t q : ℕ} (_htpos : 0 < t) (hq : 0 < q)
      (_ht : PrimeCyclicExtension.IsLowerBreak F E t)
      (_hres : residueDegree F E = 1) (_hunr : ramificationIndex F U = 1)
      (tau : ContinuousQuasiChar F) (Psi : ContinuousAddChar F) (c : F) (d : U)
      (M : CompatibleModels F E U K p (t + 1) q hq tau Psi c d)
      (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
      (D : ActualTwist F E U K M thetaU thetaE),
      t + 1 ≤ D.h → ∀ (psiF : ContinuousAddChar F), psiF ≠ 1 →
      localConstant U thetaU (tracePullbackAddChar F U psiF) =
        localConstant E thetaE (tracePullbackAddChar F E psiF) ∧
      (normCharacterFinset F U).prod (fun nu => localConstant F nu.1 psiF) = 1 ∧
      (normCharacterFinset F E).prod (fun nu => localConstant F nu.1 psiF) = 1 := by
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
    (Basic.intermediateField_tower_compatible hp hG U hU).2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E
    (Basic.intermediateField_tower_compatible hp hG E hE).2.2.2.2.2.2.2.2.2.2.2.1
  letI := primeCyclicNormCharacter_finite F U
  letI := primeCyclicNormCharacter_finite F E
  intro t q htpos hq ht hres hunr tau Psi c d M thetaU thetaE D hh psiF hpsiF
  let psi := canonicalLocalAddCharData F psiF hpsiF
  let nuU : LocalQuasiCharData U := ⟨M.chiU, t + 1, M.conductorU⟩
  let nuE : LocalQuasiCharData E := ⟨M.chiE * D.rho.1, t + 1, D.adjusted_conductor⟩
  obtain ⟨a, haU, haE⟩ := stable_common_covector F E U hp hodd htpos hE hU
    ht hres hunr hh D.lambda (D.lambda_high (by omega)) nuU nuE le_rfl le_rfl psi
  have hconj := Characters.conjugacy hp hG U E hU hE hne
    M.chiU (M.chiE * D.rho.1) (normQuasiChar U K M.chiU)
    rfl D.adjusted_compatible M.primitive
  obtain ⟨hprodU, hprodE⟩ := hconj.2.2.2.1 hodd
  have ha : nuU.character (Units.map (algebraMap F U) a) =
      nuE.character (Units.map (algebraMap F E) a) := by
    have hr := DFunLike.congr_fun hconj.2.2.1 a
    change nuU.character (Units.map (algebraMap F U) a) *
        Characters.intermediateNormCharacterProduct hp hG U hU a =
      nuE.character (Units.map (algebraMap F E) a) *
        Characters.intermediateNormCharacterProduct hp hG E hE a at hr
    rw [hprodU, hprodE] at hr
    exact mul_right_cancel hr
  refine ⟨?_, ?_, ?_⟩
  · have hleft := congrArg (fun chi => localConstant U chi
      (tracePullbackAddChar F U psiF)) D.twistU
    have hright := congrArg (fun chi => localConstant E chi
      (tracePullbackAddChar F E psiF)) D.twistE
    apply hleft.trans
    apply haU.trans
    apply Eq.trans _ (haE.symm.trans hright.symm)
    exact congrArg (fun z : ℂˣ => (z : ℂ) * localConstant F D.lambda psiF ^ p) ha
  · letI := normCharacterFintype F U
    exact normCharacter_constants_product F U (hU.symm ▸ hodd) psi
  · letI := normCharacterFintype F E
    exact normCharacter_constants_product F E (hE.symm ▸ hodd) psi
end ActualPair

end
end LanglandsSecondMainLemma.Odd.UR
