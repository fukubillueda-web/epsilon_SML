import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Stationary.NormalizedFactor
import LanglandsSecondMainLemma.Characters.Conjugacy
import LanglandsSecondMainLemma.Algebra.BiquadraticE2

/-!
# The complete factor at a genuine common origin

Paper Lemma 4.6 (`U:common-origin`), lines 646–682, with the stationary
conventions at lines 461–507 and the corrected restriction `U:determinant`.

The origin is supplied, not constructed. Its upper norms and the lower norms
of its nonzero upper traces must have their exact stationary orders and satisfy
the character identities on the entire ordinary stationary ideals. The residual
factors retain the full affine functions of `NormalizedFactor` in odd conductor
and equal one in even conductor.
-/

namespace LanglandsSecondMainLemma.Stationary

noncomputable section
open LanglandsFirstMainLemma

section Residual
variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- An element generating the depth-`d` ideal, chosen only to take the complete
residue-field sum. This is not a choice of stationary coefficient. -/
private def residualScale (d : ℕ) : {delta : Eˣ //
    ord E (delta : E) = ((d : ℤ) : WithTop ℤ)} := by
  apply Classical.choice
  obtain ⟨x, hx⟩ := exists_ord_eq E (d : ℤ)
  have hne : x ≠ 0 := (ord_ne_top_iff E).1 (by rw [hx]; simp)
  exact ⟨⟨Units.mk0 x hne, hx⟩⟩

/-- The exact coefficient order and the minus-sign character identity on
`𝓅_E^(m/2 + m%2)`, the full ordinary stationary ideal for `m > 1`.
All ideal exponents and coefficient orders retain their integer values. -/
def IsOrdinaryStationaryCoefficient
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (Z : Eˣ) (hlarge : 1 < theta.conductor) : Prop :=
  ord E (Z : E) =
      ((-Psi.conductor - (theta.conductor : ℤ) : ℤ) : WithTop ℤ) ∧
    IsNormalizedStationaryCoefficientAtDepth E theta Psi Z
      (theta.conductor / 2 + theta.conductor % 2) (by omega)

/-- The complete normalized residual sum in both parities. In odd conductor
this is literally the full normalized sum from `normalizedResidualFactor`;
in even conductor it is one. -/
def completeNormalizedResidualFactor
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (alpha Z : Eˣ) (hlarge : 1 < theta.conductor) : ℂ :=
  if heven : theta.conductor % 2 = 0 then 1 else
    normalizedResidualFactor E theta psi alpha Z (theta.conductor / 2)
      (by omega) hlarge (residualScale E (theta.conductor / 2)).1
      (residualScale E (theta.conductor / 2)).2

/-- The even-conductor residual factor has exactly the value one. -/
@[simp]
theorem completeNormalizedResidualFactor_even
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (alpha Z : Eˣ) (hlarge : 1 < theta.conductor)
    (heven : theta.conductor % 2 = 0) :
    completeNormalizedResidualFactor E theta psi alpha Z hlarge = 1 := by
  simp [completeNormalizedResidualFactor, heven]

/-- The normalized Lamprecht identity with its complete residual factor,
without a parity case in the conclusion. -/
theorem completeNormalizedFactor
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (alpha Z : Eˣ) (hlarge : 1 < theta.conductor)
    (hstationary : IsOrdinaryStationaryCoefficient E theta
      (scaleAddCharData E psi alpha) Z hlarge) :
    LanglandsFirstMainLemma.localConstant E theta.character psi.character =
      (theta.character ((-alpha * Z)⁻¹) : ℂ) *
        ((scaleAddCharData E psi alpha).character (-(Z : E)) : ℂ) *
        completeNormalizedResidualFactor E theta psi alpha Z hlarge := by
  have h := normalizedFactor E theta psi alpha Z
    (theta.conductor / 2) (theta.conductor % 2) (by omega) (by omega)
    hlarge hstationary.1 hstationary.2
  by_cases heven : theta.conductor % 2 = 0
  · rw [completeNormalizedResidualFactor_even E theta psi alpha Z hlarge heven,
      mul_one]
    exact h.1 heven
  · simpa only [completeNormalizedResidualFactor, dif_neg heven] using
      h.2 (by omega) (residualScale E (theta.conductor / 2)).1
        (residualScale E (theta.conductor / 2)).2

end Residual

section Edge
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [Module.Finite F K] [IsGalois F K]
  [IsKleinFour Gal(K/F)]
  (L : IntermediateField F K)
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension F L] [ValuativeExtension L K]
  [Algebra.IsQuadraticExtension F L] [Algebra.IsQuadraticExtension L K]

/-- The lower coefficient is the literal norm of the nonzero upper trace. -/
def commonOriginLowerCoefficient (C : Kˣ) (htrace : trace L K (C : K) ≠ 0) : Fˣ :=
  normUnits F L (Units.mk0 (trace L K (C : K)) htrace)

/-- The product of both complete residual sums at this origin. -/
def commonOriginResidualProduct
    (theta : LocalQuasiCharData L) (omega : LocalQuasiCharData F)
    (psiF : LocalAddCharData F) (psiL : LocalAddCharData L)
    (alpha : Fˣ) (C : Kˣ) (htrace : trace L K (C : K) ≠ 0)
    (htheta : 1 < theta.conductor) (homega : 1 < omega.conductor) : ℂ :=
  completeNormalizedResidualFactor L theta psiL
      (Units.map (algebraMap F L).toMonoidHom alpha) (normUnits L K C) htheta *
    completeNormalizedResidualFactor F omega psiF alpha
      (commonOriginLowerCoefficient L C htrace) homega

/-- Multiplication of the two genuine Lamprecht formulas. The lower norm
character is evaluated at an actual norm; the two additive terms combine by
`U:e2`. No comparison identity is assumed here. -/
private theorem commonOrigin_edge
    (theta : LocalQuasiCharData L) (omega : LocalQuasiCharData F)
    (omegaNorm : NormCharacter F L) (homegaChar : omega.character = omegaNorm.1)
    (Theta : ContinuousQuasiChar K) (hcompatible : normQuasiChar L K theta.character = Theta)
    (psiF : LocalAddCharData F) (psiL : LocalAddCharData L)
    (hpsi : psiL.character = psiF.character.compTrace)
    (alpha : Fˣ) (C : Kˣ) (htrace : trace L K (C : K) ≠ 0)
    (htheta : 1 < theta.conductor) (homega : 1 < omega.conductor)
    (hZ : IsOrdinaryStationaryCoefficient L theta
      (scaleAddCharData L psiL (Units.map (algebraMap F L).toMonoidHom alpha))
      (normUnits L K C) htheta)
    (hW : IsOrdinaryStationaryCoefficient F omega
      (scaleAddCharData F psiF alpha) (commonOriginLowerCoefficient L C htrace) homega) :
    LanglandsFirstMainLemma.localConstant L theta.character psiL.character *
        LanglandsFirstMainLemma.localConstant F omega.character psiF.character =
      ((Characters.restrictQuasiChar F L theta.character * omega.character)
        (-alpha⁻¹) : ℂ) * (Theta C : ℂ)⁻¹ *
        ((scaleAddCharData F psiF alpha).character
          (-elementarySymmetric F K 2 (C : K)) : ℂ) *
        commonOriginResidualProduct L theta omega psiF psiL alpha C htrace htheta homega := by
  let alphaL := Units.map (algebraMap F L).toMonoidHom alpha
  let Z := normUnits L K C
  let W := commonOriginLowerCoefficient L C htrace
  have hthetaZ : theta.character Z = Theta C := DFunLike.congr_fun hcompatible C
  have homegaW : omega.character W = 1 := by
    rw [homegaChar]
    exact omegaNorm.eq_one_on_normRange F L W
      ⟨Units.mk0 (trace L K (C : K)) htrace, rfl⟩
  have hunitL : (-alphaL * Z)⁻¹ =
      Units.map (algebraMap F L).toMonoidHom (-alpha⁻¹) * Z⁻¹ := by
    simp [alphaL, mul_comm]
  have hunitF : (-alpha * W)⁻¹ = -alpha⁻¹ * W⁻¹ := by
    simp [mul_comm]
  have hmult :
      (theta.character ((-alphaL * Z)⁻¹) : ℂ) *
          (omega.character ((-alpha * W)⁻¹) : ℂ) =
        ((Characters.restrictQuasiChar F L theta.character * omega.character)
          (-alpha⁻¹) : ℂ) * (Theta C : ℂ)⁻¹ := by
    change _ = (theta.character (Units.map (algebraMap F L).toMonoidHom (-alpha⁻¹)) *
      omega.character (-alpha⁻¹) : ℂˣ) * (Theta C : ℂ)⁻¹
    rw [hunitL, hunitF, map_mul, map_mul, map_inv, map_inv, hthetaZ, homegaW]
    push_cast
    ring
  have hadd :
      ((scaleAddCharData L psiL alphaL).character (-(Z : L)) : ℂ) *
          ((scaleAddCharData F psiF alpha).character (-(W : F)) : ℂ) =
        ((scaleAddCharData F psiF alpha).character
          (-elementarySymmetric F K 2 (C : K)) : ℂ) := by
    have htraceAlpha : trace F L ((alphaL : L) * -(Z : L)) =
        (alpha : F) * -trace F L (Z : L) := by
      change trace F L (algebraMap F L (alpha : F) * -(Z : L)) = _
      rw [← Algebra.smul_def, map_smul, map_neg, smul_eq_mul]
    rw [scaleAddCharData_character_apply, hpsi, ContinuousAddChar.compTrace_apply,
      htraceAlpha, ← scaleAddCharData_character_apply]
    rw [← Units.val_mul, ← ContinuousAddChar.map_add_eq_mul]
    congr 2
    rw [Algebra.biquadraticE2 F K L]
    change -trace F L (norm L K (C : K)) + -norm F L (trace L K (C : K)) = _
    ring
  rw [completeNormalizedFactor L theta psiL _ _ htheta hZ,
    completeNormalizedFactor F omega psiF _ _ homega hW]
  change (_ * _ * _) * (_ * _ * _) = _
  dsimp only [commonOriginResidualProduct]
  calc
    _ = ((theta.character ((-alphaL * Z)⁻¹) : ℂ) *
          (omega.character ((-alpha * W)⁻¹) : ℂ)) *
        (((scaleAddCharData L psiL alphaL).character (-(Z : L)) : ℂ) *
          ((scaleAddCharData F psiF alpha).character (-(W : F)) : ℂ)) *
        (completeNormalizedResidualFactor L theta psiL alphaL Z htheta *
          completeNormalizedResidualFactor F omega psiF alpha W homega) := by ring
    _ = _ := by rw [hmult, hadd]

end Edge

section Pair
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K] in
/-- The actual Galois-group equivalence supplies the Klein-four structure
required by the characteristic-free symmetric identity. -/
private theorem commonOrigin_kleinFour
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))) :
    IsKleinFour Gal(K/F) := by
  let e := Classical.choice hG
  constructor
  · rw [Nat.card_congr e.toEquiv]
    simp
  · rw [Monoid.exponent_eq_of_mulEquiv e]
    simp [Monoid.exponent_prod]

/-- **Paper Lemma 4.6 (`U:common-origin`).** For a primitive compatible pair
in the genuine biquadratic diamond, a supplied simultaneous stationary origin
has one complete elementary factor
`D (-alpha⁻¹) * Theta C ⁻¹ * PsiF (-E₂ C)`.

The lower characters are the complete lower norm-character products, proved
by `Characters.conjugacy` to be the nontrivial quadratic norm characters.
The same theorem proves equality of the corrected restrictions defining `D`.
Both upper traces are explicitly nonzero. Each of the four stationary
hypotheses includes its exact order and the identity on its whole ordinary
stationary ideal, and all four conductors exceed one.

The conclusions give the corrected common restriction, both complete factors,
and the resulting comparison when the complete residual products agree.
The canonical FML `localConstant` is used throughout; neither unitarity nor a
restriction on either field characteristic is imposed. -/
theorem commonOrigin
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (I J : IntermediateField F K)
    (hI : Module.finrank F I = 2) (hJ : Module.finrank F J = 2)
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
    let omegaI := canonicalLocalQuasiCharData F
      (Characters.intermediateNormCharacterProduct Nat.prime_two hG I hI)
    let omegaJ := canonicalLocalQuasiCharData F
      (Characters.intermediateNormCharacterProduct Nat.prime_two hG J hJ)
    ∀ (thetaI : LocalQuasiCharData I) (thetaJ : LocalQuasiCharData J)
      (Theta : ContinuousQuasiChar K),
      normQuasiChar I K thetaI.character = Theta →
      normQuasiChar J K thetaJ.character = Theta →
      (¬ ∃ chi : ContinuousQuasiChar F, normQuasiChar F K chi = Theta) →
    ∀ (psiF : LocalAddCharData F) (psiI : LocalAddCharData I) (psiJ : LocalAddCharData J),
      psiI.character = psiF.character.compTrace →
      psiJ.character = psiF.character.compTrace →
    ∀ (alpha : Fˣ) (C : Kˣ)
      (htraceI : trace I K (C : K) ≠ 0) (htraceJ : trace J K (C : K) ≠ 0)
      (hthetaI : 1 < thetaI.conductor) (hthetaJ : 1 < thetaJ.conductor)
      (homegaI : 1 < omegaI.conductor) (homegaJ : 1 < omegaJ.conductor),
      IsOrdinaryStationaryCoefficient I thetaI
        (scaleAddCharData I psiI (Units.map (algebraMap F I).toMonoidHom alpha))
        (normUnits I K C) hthetaI →
      IsOrdinaryStationaryCoefficient J thetaJ
        (scaleAddCharData J psiJ (Units.map (algebraMap F J).toMonoidHom alpha))
        (normUnits J K C) hthetaJ →
      IsOrdinaryStationaryCoefficient F omegaI (scaleAddCharData F psiF alpha)
        (commonOriginLowerCoefficient I C htraceI) homegaI →
      IsOrdinaryStationaryCoefficient F omegaJ (scaleAddCharData F psiF alpha)
        (commonOriginLowerCoefficient J C htraceJ) homegaJ →
    let D := Characters.restrictQuasiChar F I thetaI.character * omegaI.character
    let A := (D (-alpha⁻¹) : ℂ) * (Theta C : ℂ)⁻¹ *
      ((scaleAddCharData F psiF alpha).character (-elementarySymmetric F K 2 (C : K)) : ℂ)
    let RI := commonOriginResidualProduct I thetaI omegaI psiF psiI alpha C
      htraceI hthetaI homegaI
    let RJ := commonOriginResidualProduct J thetaJ omegaJ psiF psiJ alpha C
      htraceJ hthetaJ homegaJ
    D = Characters.restrictQuasiChar F J thetaJ.character * omegaJ.character ∧
    LanglandsFirstMainLemma.localConstant I thetaI.character psiI.character *
        LanglandsFirstMainLemma.localConstant F omegaI.character psiF.character = A * RI ∧
    LanglandsFirstMainLemma.localConstant J thetaJ.character psiJ.character *
        LanglandsFirstMainLemma.localConstant F omegaJ.character psiF.character = A * RJ ∧
    (RI = RJ →
      LanglandsFirstMainLemma.localConstant I thetaI.character psiI.character *
          LanglandsFirstMainLemma.localConstant F omegaI.character psiF.character =
        LanglandsFirstMainLemma.localConstant J thetaJ.character psiJ.character *
          LanglandsFirstMainLemma.localConstant F omegaJ.character psiF.character) := by
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
  dsimp only
  intro thetaI thetaJ Theta hcI hcJ hprimitive psiF psiI psiJ hpsiI hpsiJ
    alpha C htraceI htraceJ hthetaI hthetaJ homegaI homegaJ hZI hZJ hWI hWJ
  let omegaI := canonicalLocalQuasiCharData F
    (Characters.intermediateNormCharacterProduct Nat.prime_two hG I hI)
  let omegaJ := canonicalLocalQuasiCharData F
    (Characters.intermediateNormCharacterProduct Nat.prime_two hG J hJ)
  have hconj := Characters.conjugacy Nat.prime_two hG I J hI hJ hne
    thetaI.character thetaJ.character Theta hcI hcJ hprimitive
  have hD := hconj.2.2.1
  obtain ⟨nuI, nuJ, _, _, hnuI, hnuJ⟩ := hconj.2.2.2.2 rfl
  letI : IsKleinFour Gal(K/F) := commonOrigin_kleinFour hG
  have hdataI := Basic.intermediateField_tower_compatible Nat.prime_two hG I hI
  have hdataJ := Basic.intermediateField_tower_compatible Nat.prime_two hG J hJ
  letI : Algebra.IsQuadraticExtension F I := { finrank_eq_two' := hI }
  letI : Algebra.IsQuadraticExtension F J := { finrank_eq_two' := hJ }
  letI : Algebra.IsQuadraticExtension I K :=
    { finrank_eq_two' := hdataI.2.2.2.2.2.2.2.2.2.2.1 }
  letI : Algebra.IsQuadraticExtension J K :=
    { finrank_eq_two' := hdataJ.2.2.2.2.2.2.2.2.2.2.1 }
  have hfactorI := commonOrigin_edge I thetaI omegaI nuI hnuI Theta hcI
    psiF psiI hpsiI alpha C htraceI hthetaI homegaI hZI hWI
  have hfactorJ := commonOrigin_edge J thetaJ omegaJ nuJ hnuJ Theta hcJ
    psiF psiJ hpsiJ alpha C htraceJ hthetaJ homegaJ hZJ hWJ
  change Characters.restrictQuasiChar F I thetaI.character * omegaI.character =
    Characters.restrictQuasiChar F J thetaJ.character * omegaJ.character at hD
  rw [← hD] at hfactorJ
  refine ⟨hD, hfactorI, hfactorJ, ?_⟩
  intro hres
  rw [hfactorI, hfactorJ, hres]

end Pair

end
end LanglandsSecondMainLemma.Stationary
