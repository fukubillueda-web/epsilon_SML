import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Stationary.CommonOrigin
import LanglandsSecondMainLemma.Basic.NormTrace

/-!
# The common function before residual summation

Paper Lemma 4.7 (`U:common-function`), lines 684–713, in the common-origin
setting of Lemma 4.6 and the stationary conventions at lines 461–507.

The pointwise product uses the actual upper norm and lower trace-norm quotients.
Compatibility and whole-domain norm triviality remove its multiplicative terms;
`U:e2` combines the additive increments without any division by two. The final
theorem uses the genuine biquadratic pair, its complete lower character products,
and the common origin's full stationary conditions. At terminal depth it gives
the identity of the full affine critical functions before any summation.
-/

namespace LanglandsSecondMainLemma.Stationary

noncomputable section
open LanglandsFirstMainLemma

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

/-- The literal pointwise product in `U:common-function`. The two unit
arguments are the upper norm quotient and the lower trace-norm quotient;
subtracting one gives the paper's increments `z` and `w`. -/
def commonFunctionProduct
    (theta : LocalQuasiCharData L) (omega : LocalQuasiCharData F)
    (psiF : LocalAddCharData F) (psiL : LocalAddCharData L)
    (alpha : Fˣ) (C C' : Kˣ)
    (htrace : trace L K (C : K) ≠ 0) (htrace' : trace L K (C' : K) ≠ 0) : ℂ :=
  let Z := normUnits L K C
  let W := commonOriginLowerCoefficient L C htrace
  let r := normUnits L K C' / Z
  let s := commonOriginLowerCoefficient L C' htrace' / W
  ((scaleAddCharData L psiL (Units.map (algebraMap F L).toMonoidHom alpha)).character
      (-(Z : L) * ((r : L) - 1)) : ℂ) * (theta.character r : ℂ)⁻¹ *
    ((scaleAddCharData F psiF alpha).character (-(W : F) * ((s : F) - 1)) : ℂ) *
      (omega.character s : ℂ)⁻¹

private theorem neg_mul_unit_increment {E : Type*} [Field E] (Z Z' : Eˣ) :
    -(Z : E) * (((Z' / Z : Eˣ) : E) - 1) = -(Z' : E) + (Z : E) := by
  rw [Units.val_div_eq_div_val]
  field_simp
  ring

/-- The algebraic identity on one actual quadratic flag. The lower character
is trivial on the whole norm range, so the trace quotient itself is a witness;
no surjectivity of a critical norm map is required. -/
theorem commonFunctionProduct_eq
    (theta : LocalQuasiCharData L) (omega : LocalQuasiCharData F)
    (omegaNorm : NormCharacter F L) (homegaChar : omega.character = omegaNorm.1)
    (Theta : ContinuousQuasiChar K) (hcompatible : normQuasiChar L K theta.character = Theta)
    (psiF : LocalAddCharData F) (psiL : LocalAddCharData L)
    (hpsi : psiL.character = psiF.character.compTrace)
    (alpha : Fˣ) (C C' : Kˣ)
    (htrace : trace L K (C : K) ≠ 0) (htrace' : trace L K (C' : K) ≠ 0) :
    commonFunctionProduct L theta omega psiF psiL alpha C C' htrace htrace' =
      (Theta (C' / C) : ℂ)⁻¹ *
        ((scaleAddCharData F psiF alpha).character
          (-elementarySymmetric F K 2 (C' : K) + elementarySymmetric F K 2 (C : K)) : ℂ) := by
  let alphaL := Units.map (algebraMap F L).toMonoidHom alpha
  let Z := normUnits L K C
  let Z' := normUnits L K C'
  let W := commonOriginLowerCoefficient L C htrace
  let W' := commonOriginLowerCoefficient L C' htrace'
  have htheta : theta.character (Z' / Z) = Theta (C' / C) := by
    have h := DFunLike.congr_fun hcompatible (C' / C)
    change theta.character (normUnits L K (C' / C)) = _ at h
    simpa only [map_div] using h
  have homega : omega.character (W' / W) = 1 := by
    rw [homegaChar]
    apply omegaNorm.eq_one_on_normRange F L
    exact ⟨Units.mk0 (trace L K (C' : K)) htrace' /
      Units.mk0 (trace L K (C : K)) htrace, map_div _ _ _⟩
  have hadd :
      ((scaleAddCharData L psiL alphaL).character (-(Z' : L) + (Z : L)) : ℂ) *
          ((scaleAddCharData F psiF alpha).character (-(W' : F) + (W : F)) : ℂ) =
        ((scaleAddCharData F psiF alpha).character
          (-elementarySymmetric F K 2 (C' : K) + elementarySymmetric F K 2 (C : K)) : ℂ) := by
    have htraceAlpha : trace F L ((alphaL : L) * (-(Z' : L) + (Z : L))) =
        (alpha : F) * (-trace F L (Z' : L) + trace F L (Z : L)) := by
      change trace F L (algebraMap F L (alpha : F) * (-(Z' : L) + (Z : L))) = _
      rw [← Algebra.smul_def, map_smul, map_add, map_neg, smul_eq_mul]
    rw [scaleAddCharData_character_apply, hpsi, ContinuousAddChar.compTrace_apply,
      htraceAlpha, ← scaleAddCharData_character_apply]
    rw [← Units.val_mul, ← ContinuousAddChar.map_add_eq_mul]
    congr 2
    rw [Algebra.biquadraticE2 F K L, Algebra.biquadraticE2 F K L]
    change -trace F L (norm L K (C' : K)) + trace F L (norm L K (C : K)) +
      (-norm F L (trace L K (C' : K)) + norm F L (trace L K (C : K))) = _
    ring
  change _ * (theta.character (Z' / Z) : ℂ)⁻¹ * _ *
    (omega.character (W' / W) : ℂ)⁻¹ = _
  rw [htheta, homega]
  simp only [Units.val_one, inv_one, mul_one]
  rw [neg_mul_unit_increment, neg_mul_unit_increment]
  calc
    _ = (Theta (C' / C) : ℂ)⁻¹ *
        (((scaleAddCharData L psiL alphaL).character (-(Z' : L) + (Z : L)) : ℂ) *
          ((scaleAddCharData F psiF alpha).character (-(W' : F) + (W : F)) : ℂ)) := by ring
    _ = _ := by rw [hadd]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Module.Finite F K] [IsGalois F K] [IsKleinFour Gal(K/F)]
  [ValuativeExtension F L] [ValuativeExtension L K]
  [Algebra.IsQuadraticExtension F L] [Algebra.IsQuadraticExtension L K] in
/-- On positive-depth lattices the literal product is the product of the two
full normalized critical values, including their affine terms. The coordinate
equations identify the actual increments and do not assert norm surjectivity. -/
theorem commonFunctionProduct_eq_criticalValues
    (theta : LocalQuasiCharData L) (omega : LocalQuasiCharData F)
    (psiF : LocalAddCharData F) (psiL : LocalAddCharData L)
    (alpha : Fˣ) (C C' : Kˣ)
    (htrace : trace L K (C : K) ≠ 0) (htrace' : trace L K (C' : K) ≠ 0)
    (dL dF : ℕ) (hdL : 0 < dL) (hdF : 0 < dF)
    (z : lattice L (dL : ℤ)) (w : lattice F (dF : ℤ))
    (hz : 1 + (z : L) = ((normUnits L K C' / normUnits L K C : Lˣ) : L))
    (hw : 1 + (w : F) = ((commonOriginLowerCoefficient L C' htrace' /
      commonOriginLowerCoefficient L C htrace : Fˣ) : F)) :
    commonFunctionProduct L theta omega psiF psiL alpha C C' htrace htrace' =
      normalizedCriticalValue L theta
        (scaleAddCharData L psiL (Units.map (algebraMap F L).toMonoidHom alpha))
        (normUnits L K C) dL hdL z *
      normalizedCriticalValue F omega (scaleAddCharData F psiF alpha)
        (commonOriginLowerCoefficient L C htrace) dF hdF w := by
  have hunitL : positiveUnitOfLattice L hdL z = normUnits L K C' / normUnits L K C := by
    apply Units.ext
    exact hz
  have hunitF : positiveUnitOfLattice F hdF w = commonOriginLowerCoefficient L C' htrace' /
      commonOriginLowerCoefficient L C htrace := by
    apply Units.ext
    exact hw
  dsimp only [commonFunctionProduct, normalizedCriticalValue]
  rw [← hz, ← hw, ← hunitL, ← hunitF]
  have hz' : 1 + (z : L) - 1 = (z : L) := by ring
  have hw' : 1 + (w : F) - 1 = (w : F) := by ring
  rw [hz', hw']
  ring

end Edge

section Pair
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

/-- **Paper Lemma 4.7 (`U:common-function`).** In the genuine biquadratic
setting and with the common-origin hypotheses of `commonOrigin`, the two
literal pointwise products have the common value
`Theta (C' / C)⁻¹ * PsiF (-E₂ C' + E₂ C)`.

The lower characters are the complete canonical lower norm-character products.
Both traces of each origin are nonzero. The four stationary hypotheses retain
their exact coefficient orders and their character identities on the whole
ordinary stationary ideals. The pointwise calculation itself holds without
stationarity, as proved in `commonFunctionProduct_eq`.

The last two conclusions identify the full critical functions at the actual
terminal depths `conductor / 2` whenever their lattice coordinates give the
specified norm quotients. Membership is supplied only for this interpretation;
it is neither inferred from a valuation of a norm nor from norm surjectivity.
Both field characteristics and nonunitary quasi-characters are allowed. -/
theorem commonFunction
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
    ∀ (C' : Kˣ) (htraceI' : trace I K (C' : K) ≠ 0)
      (htraceJ' : trace J K (C' : K) ≠ 0),
    let Q := (Theta (C' / C) : ℂ)⁻¹ *
      ((scaleAddCharData F psiF alpha).character
        (-elementarySymmetric F K 2 (C' : K) + elementarySymmetric F K 2 (C : K)) : ℂ)
    let PI := commonFunctionProduct I thetaI omegaI psiF psiI alpha C C' htraceI htraceI'
    let PJ := commonFunctionProduct J thetaJ omegaJ psiF psiJ alpha C C' htraceJ htraceJ'
    PI = Q ∧ PJ = Q ∧ PI = PJ ∧
    (∀ (z : lattice I ((thetaI.conductor / 2 : ℕ) : ℤ))
      (w : lattice F ((omegaI.conductor / 2 : ℕ) : ℤ)),
      1 + (z : I) = ((normUnits I K C' / normUnits I K C : Iˣ) : I) →
      1 + (w : F) = ((commonOriginLowerCoefficient I C' htraceI' /
        commonOriginLowerCoefficient I C htraceI : Fˣ) : F) →
      normalizedCriticalValue I thetaI
        (scaleAddCharData I psiI (Units.map (algebraMap F I).toMonoidHom alpha))
        (normUnits I K C) (thetaI.conductor / 2) (by omega) z *
      normalizedCriticalValue F omegaI (scaleAddCharData F psiF alpha)
        (commonOriginLowerCoefficient I C htraceI) (omegaI.conductor / 2) (by omega) w = Q) ∧
    (∀ (z : lattice J ((thetaJ.conductor / 2 : ℕ) : ℤ))
      (w : lattice F ((omegaJ.conductor / 2 : ℕ) : ℤ)),
      1 + (z : J) = ((normUnits J K C' / normUnits J K C : Jˣ) : J) →
      1 + (w : F) = ((commonOriginLowerCoefficient J C' htraceJ' /
        commonOriginLowerCoefficient J C htraceJ : Fˣ) : F) →
      normalizedCriticalValue J thetaJ
        (scaleAddCharData J psiJ (Units.map (algebraMap F J).toMonoidHom alpha))
        (normUnits J K C) (thetaJ.conductor / 2) (by omega) z *
      normalizedCriticalValue F omegaJ (scaleAddCharData F psiF alpha)
        (commonOriginLowerCoefficient J C htraceJ) (omegaJ.conductor / 2) (by omega) w = Q) := by
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
    alpha C htraceI htraceJ hthetaI hthetaJ homegaI homegaJ _hZI _hZJ _hWI _hWJ
    C' htraceI' htraceJ'
  let omegaI := canonicalLocalQuasiCharData F
    (Characters.intermediateNormCharacterProduct Nat.prime_two hG I hI)
  let omegaJ := canonicalLocalQuasiCharData F
    (Characters.intermediateNormCharacterProduct Nat.prime_two hG J hJ)
  change 1 < omegaI.conductor at homegaI
  change 1 < omegaJ.conductor at homegaJ
  have hconj := Characters.conjugacy Nat.prime_two hG I J hI hJ hne
    thetaI.character thetaJ.character Theta hcI hcJ hprimitive
  obtain ⟨nuI, nuJ, _, _, hnuI, hnuJ⟩ := hconj.2.2.2.2 rfl
  letI : IsKleinFour Gal(K/F) := by
    let e := Classical.choice hG
    constructor
    · rw [Nat.card_congr e.toEquiv]
      simp
    · rw [Monoid.exponent_eq_of_mulEquiv e]
      simp [Monoid.exponent_prod]
  have hdataI := Basic.intermediateField_tower_compatible Nat.prime_two hG I hI
  have hdataJ := Basic.intermediateField_tower_compatible Nat.prime_two hG J hJ
  letI : Algebra.IsQuadraticExtension F I := { finrank_eq_two' := hI }
  letI : Algebra.IsQuadraticExtension F J := { finrank_eq_two' := hJ }
  letI : Algebra.IsQuadraticExtension I K :=
    { finrank_eq_two' := hdataI.2.2.2.2.2.2.2.2.2.2.1 }
  letI : Algebra.IsQuadraticExtension J K :=
    { finrank_eq_two' := hdataJ.2.2.2.2.2.2.2.2.2.2.1 }
  have hpointI := commonFunctionProduct_eq I thetaI omegaI nuI hnuI Theta hcI
    psiF psiI hpsiI alpha C C' htraceI htraceI'
  have hpointJ := commonFunctionProduct_eq J thetaJ omegaJ nuJ hnuJ Theta hcJ
    psiF psiJ hpsiJ alpha C C' htraceJ htraceJ'
  refine ⟨hpointI, hpointJ, hpointI.trans hpointJ.symm, ?_, ?_⟩
  · intro z w hz hw
    exact (commonFunctionProduct_eq_criticalValues I thetaI omegaI psiF psiI alpha C C'
      htraceI htraceI' (thetaI.conductor / 2) (omegaI.conductor / 2) (by omega) (by omega)
      z w hz hw).symm.trans hpointI
  · intro z w hz hw
    exact (commonFunctionProduct_eq_criticalValues J thetaJ omegaJ psiF psiJ alpha C C'
      htraceJ htraceJ' (thetaJ.conductor / 2) (omegaJ.conductor / 2) (by omega) (by omega)
      z w hz hw).symm.trans hpointJ

end Pair
end
end LanglandsSecondMainLemma.Stationary
