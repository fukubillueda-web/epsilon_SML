import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Odd.UR.NormDepths
import LanglandsSecondMainLemma.Characters.Conjugacy

/-!
# Odd / UR / Scalar Phase

Paper Lemma 6.11 (`O:I:scalarphase`), source lines 1576--1611, in the
setup of lines 1060--1128 and 1416--1451. The actual common norm and both
affine corrections are retained, including the last odd-conductor row.
-/

namespace LanglandsSecondMainLemma.Odd.UR

noncomputable section

open LanglandsFirstMainLemma
open LanglandsSecondMainLemma.Stationary
open scoped BigOperators

section SingleField
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- Apply the complete enhanced formula to the supplied enhanced coefficient
and the literal displaced numerator. No representative is reselected. -/
theorem NormDepthRepresentative.localConstant_eq
    (theta : LocalQuasiCharData L) (psi : LocalAddCharData L)
    (alpha B Z : Lˣ) {p : ℕ} {J : ℤ}
    (hchar : residueCharacteristic L = p) (hp : p ≠ 2)
    (hJ : J = -(scaleAddCharData L psi alpha).conductor)
    (R : NormDepthRepresentative L theta.character
      (scaleAddCharData L psi alpha).character p theta.conductor J B Z) :
    ∃ g : ℂ, g ^ 4 = 1 ∧
      LanglandsFirstMainLemma.localConstant L theta.character psi.character =
        (theta.character ((-alpha * Z)⁻¹) : ℂ) *
          ((scaleAddCharData L psi alpha).character (-(Z : L)) : ℂ) *
          ((scaleAddCharData L psi alpha).character
            (((Z : L) - B) ^ 2 / ((2 : L) * B)) : ℂ) * g := by
  let m := theta.conductor
  let d := m / 2
  let e := m % 2
  have he : e ≤ 1 := by dsimp [e]; omega
  have hm : theta.conductor = 2 * d + e := by dsimp [d, e, m]; omega
  have hd : 0 < d := by have := R.large; dsimp [d, m]; omega
  have hs : d + e = (theta.conductor + 1) / 2 := by dsimp [d, e, m]; omega
  let Psi := scaleAddCharData L psi alpha
  have hB : IsEnhancedStationaryCoefficient L theta Psi p d hd J B :=
    ⟨R.coefficient_order, R.coefficient_chart⟩
  have hZ : ord L (Z : L) =
      ((-Psi.conductor - (theta.conductor : ℤ) : ℤ) : WithTop ℤ) :=
    hJ ▸ R.numerator_order
  have hstat : IsNormalizedStationaryCoefficientAtDepth L theta Psi Z (d + e)
      (lamprechtFormula_stationaryDepth L theta d e he hm R.large).pos := by
    intro z
    let z' : lattice L (((theta.conductor + 1) / 2 : ℕ) : ℤ) :=
      ⟨(z : L), by rw [← hs]; exact z.property⟩
    exact R.ordinary z'
  have hn := normalizedFactor L theta psi alpha Z d e he hm R.large hZ hstat
  by_cases heven : e = 0
  · have hdeep : (Z : L) - B ∈ lattice L (J - (d : ℤ)) := by
      simpa only [← hs, heven, add_zero] using R.displacement
    have hc := congrArg Units.val (enhancedCorrection_eq_one L theta Psi p d e hd
      J B hchar hp he hm hJ hB ((Z : L) - B) hdeep)
    refine ⟨1, by norm_num, ?_⟩
    rw [hc, Units.val_one, mul_one, mul_one]
    exact hn.1 heven
  · have heodd : e = 1 := by omega
    have hm' : theta.conductor = 2 * d + 1 := by omega
    have heta : (Z : L) - B ∈ lattice L (J - (d + 1 : ℕ)) := by
      simpa only [← hs, heodd] using R.displacement
    obtain ⟨delta0, hdelta0⟩ := exists_ord_eq L (d : ℤ)
    let delta : Lˣ := Units.mk0 delta0 ((ord_ne_top_iff L).1 (by rw [hdelta0]; simp))
    have hdelta : ord L (delta : L) = ((d : ℤ) : WithTop ℤ) := hdelta0
    letI := residueFieldFintype L
    let psi0 := enhancedResidualAddChar L theta Psi p d hd J B delta hm' hJ hB hdelta
    let b0 := enhancedResidualShift L theta Psi p d hd J B delta hm' hB hdelta
      ((Z : L) - B) heta
    have hnontriv : psi0 ≠ 1 :=
      enhancedResidualAddChar_ne_one L theta Psi p d hd J B delta hm' hJ hB hdelta
    have hodd : ringChar (ResidueField L) ≠ 2 := by
      change residueCharacteristic L ≠ 2
      rwa [hchar]
    have hres := enhancedNormalizedResidualFactor_eq_quadraticPhase L theta psi alpha
      p d hd J B Z hchar hp hm' R.large hJ hB ((Z : L) - B) heta
      (by simp) delta hdelta
    have hc := enhancedResidualAffineCorrection L theta Psi p d hd J B delta hchar hp
      hm' hJ hB hdelta ((Z : L) - B) heta
    have hg2 := quadraticPhase_basic_sq hodd hnontriv
    refine ⟨quadraticPhase psi0 1 0, ?_, ?_⟩
    · calc
        quadraticPhase psi0 1 0 ^ 4 = (quadraticPhase psi0 1 0 ^ 2) ^ 2 := by ring
        _ = finiteQuadraticChar (ResidueField L) (-1) ^ 2 := by rw [hg2]
        _ = 1 := finiteQuadraticChar_sq (ResidueField L) (neg_ne_zero.mpr one_ne_zero)
    · rw [hn.2 heodd delta hdelta, hres,
        quadraticPhase_completeSquare hodd hnontriv one_ne_zero b0]
      simp only [mul_one] at *
      rw [hc]
      ring

end SingleField

section Pair
variable (F E U : Type*) [Field F] [Field E] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F E] [Algebra F U] [ValuativeExtension F E] [ValuativeExtension F U]
  [Module.Finite F E] [Module.Finite F U]

/-- Scaling commutes with the actual field trace. -/
private theorem scalarPhase_scale_trace
    (psiF : LocalAddCharData F) (psiL : LocalAddCharData E)
    (hpsi : psiL.character = tracePullbackAddChar F E psiF.character) (alpha : Fˣ) :
    (scaleAddCharData E psiL (Units.map (algebraMap F E).toMonoidHom alpha)).character =
      tracePullbackAddChar F E (scaleAddCharData F psiF alpha).character := by
  apply ContinuousAddChar.ext
  intro z
  simp only [scaleAddCharData_character_apply, hpsi, tracePullbackAddChar_apply,
    Units.coe_map]
  congr 1
  change trace F E (algebraMap F E (alpha : F) * z) = _
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-- Cancel the two complete factors, retaining the original denominators
`2 B_U` and `2 B_E` in the affine corrections. -/
private theorem scalarPhase_quotient
    (thetaU : LocalQuasiCharData U) (thetaE : LocalQuasiCharData E)
    (psiU : LocalAddCharData U) (psiE : LocalAddCharData E)
    (Psi : ContinuousAddChar F) (alphaU BU ZU : Uˣ) (alphaE BE ZE : Eˣ)
    {p : ℕ} {J : ℤ} (hp : p ≠ 2)
    (hcharU : residueCharacteristic U = p) (hcharE : residueCharacteristic E = p)
    (hJU : J = -(scaleAddCharData U psiU alphaU).conductor)
    (hJE : J = -(scaleAddCharData E psiE alphaE).conductor)
    (hPsiU : (scaleAddCharData U psiU alphaU).character = tracePullbackAddChar F U Psi)
    (hPsiE : (scaleAddCharData E psiE alphaE).character = tracePullbackAddChar F E Psi)
    (RU : NormDepthRepresentative U thetaU.character
      (scaleAddCharData U psiU alphaU).character p thetaU.conductor J BU ZU)
    (RE : NormDepthRepresentative E thetaE.character
      (scaleAddCharData E psiE alphaE).character p thetaE.conductor J BE ZE)
    (ha : thetaU.character (-alphaU) = thetaE.character (-alphaE))
    (hZ : thetaU.character ZU = thetaE.character ZE) :
    ∃ g : ℂ, g ^ 4 = 1 ∧
      LanglandsFirstMainLemma.localConstant U thetaU.character psiU.character /
        LanglandsFirstMainLemma.localConstant E thetaE.character psiE.character =
      g * (Psi (-(trace F U (ZU : U) - trace F E (ZE : E))) : ℂ) *
        (tracePullbackAddChar F U Psi (((ZU : U) - BU) ^ 2 / ((2 : U) * BU)) : ℂ) /
        (tracePullbackAddChar F E Psi (((ZE : E) - BE) ^ 2 / ((2 : E) * BE)) : ℂ) := by
  obtain ⟨gU, hgU, hU⟩ := RU.localConstant_eq U thetaU psiU alphaU BU ZU hcharU hp hJU
  obtain ⟨gE, hgE, hE⟩ := RE.localConstant_eq E thetaE psiE alphaE BE ZE hcharE hp hJE
  have hvalue : thetaU.character ((-alphaU * ZU)⁻¹) =
      thetaE.character ((-alphaE * ZE)⁻¹) := by
    rw [map_inv, map_inv, map_mul, map_mul, ha, hZ]
  have hphase :
      (tracePullbackAddChar F U Psi (-(ZU : U)) : ℂ) /
        (tracePullbackAddChar F E Psi (-(ZE : E)) : ℂ) =
      (Psi (-(trace F U (ZU : U) - trace F E (ZE : E))) : ℂ) := by
    have hu : tracePullbackAddChar F U Psi (-(ZU : U)) /
        tracePullbackAddChar F E Psi (-(ZE : E)) =
        Psi (-(trace F U (ZU : U) - trace F E (ZE : E))) := by
      rw [tracePullbackAddChar_apply, tracePullbackAddChar_apply,
        (trace F U).map_neg, (trace F E).map_neg]
      exact (Psi.toAddChar.map_sub_eq_div _ _).symm.trans (congrArg Psi (by ring))
    simpa only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val] using
      congrArg Units.val hu
  refine ⟨gU / gE, by rw [div_pow, hgU, hgE, div_one], ?_⟩
  rw [hU, hE, hvalue, hPsiU, hPsiE]
  calc
    _ = (gU / gE) *
        ((tracePullbackAddChar F U Psi (-(ZU : U)) : ℂ) /
          (tracePullbackAddChar F E Psi (-(ZE : E)) : ℂ)) *
        (tracePullbackAddChar F U Psi (((ZU : U) - BU) ^ 2 / ((2 : U) * BU)) : ℂ) /
        (tracePullbackAddChar F E Psi (((ZE : E) - BE) ^ 2 / ((2 : E) * BE)) : ℂ) := by
      have hnonzero := (thetaE.character ((-alphaE * ZE)⁻¹)).ne_zero
      field_simp
    _ = _ := by rw [hphase]

end Pair

section Traces
variable (F U : Type*) [Field F] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra F U] [Module.Finite F U] [IsGalois F U]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A monic annihilator of full degree is the characteristic polynomial
when its root generates the extension. -/
private theorem scalarPhase_charpoly (d : U) (f : Polynomial F)
    (hf : f.Monic) (hroot : Polynomial.aeval d f = 0)
    (hdegree : f.natDegree = Module.finrank F U)
    (hgen : IntermediateField.adjoin F {d} = ⊤) :
    (Algebra.lmul F U d).charpoly = f := by
  have hint : IsIntegral F d := Algebra.IsIntegral.isIntegral d
  have hd : (minpoly F d).natDegree = Module.finrank F U := by
    rw [← IntermediateField.adjoin.finrank hint, hgen, IntermediateField.finrank_top']
  have hc : (Algebra.lmul F U d).charpoly = minpoly F d :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
      (LinearMap.charpoly_monic _) (minpoly.dvd F d (Algebra.aeval_self_charpoly_lmul d))
      (by rw [LinearMap.charpoly_natDegree, hd])
  exact hc.trans (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic hint) hf (minpoly.dvd F d hroot) (by rw [hdegree, hd])).symm

/-- The Newton sums of the exact Artin--Schreier polynomial, in either
field characteristic. In particular these are not sums of translated roots. -/
theorem scalarPhase_powerTraces {p : ℕ} (hp : Odd p) (hodd : 2 < p)
    (hdegree : Module.finrank F U = p) (c : F) (d : U)
    (hd : d ^ p - d = algebraMap F U c)
    (hgen : IntermediateField.adjoin F {d} = ⊤) :
    (∀ j : ℕ, 1 ≤ j → j < p →
      trace F U (d ^ j) = if j = p - 1 then ((p - 1 : ℕ) : F) else 0) ∧
    trace F U (d ^ p) = (p : F) * c := by
  classical
  let f : Polynomial F := Polynomial.X ^ p - (Polynomial.X + Polynomial.C c)
  have hlower : (Polynomial.X + Polynomial.C c : Polynomial F).degree < (p : WithBot ℕ) := by
    apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
    apply max_lt
    · simpa using (show 1 < p by omega)
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by simp; omega)
  have hf : f.Monic := Polynomial.monic_X_pow_sub hlower
  have hfdeg : f.natDegree = p := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    change (Polynomial.X ^ p - (Polynomial.X + Polynomial.C c) : Polynomial F).degree = _
    rw [Polynomial.degree_sub_eq_left_of_degree_lt (by simpa using hlower), Polynomial.degree_X_pow]
  have hpoly := scalarPhase_charpoly F U d f hf
    (by simpa [f, sub_eq_zero, sub_eq_iff_eq_add, add_comm] using hd)
    (hfdeg.trans hdegree.symm) hgen
  have he {i : ℕ} (hi : 1 ≤ i) (hip : i < p) :
      elementarySymmetric F U i d = if i = p - 1 then -1 else 0 := by
    rw [elementarySymmetric, hdegree, if_pos (by omega), hpoly]
    by_cases heq : i = p - 1
    · subst i
      have hev : Even (p - 1) := by obtain ⟨k, hk⟩ := hp; exact ⟨k, by omega⟩
      simp [f, show p - (p - 1) = 1 by omega, hev.neg_one_pow, show (1 : ℕ) ≠ p by omega]
    · have h0 : p - i ≠ 0 := by omega
      have h1 : p - i ≠ 1 := by omega
      have hp' : p - i ≠ p := by omega
      simp [f, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
        h0, Ne.symm h1, hp', heq]
  have htr (j : ℕ) (hj : 1 ≤ j) (hjp : j < p) :
      trace F U (d ^ j) = if j = p - 1 then ((p - 1 : ℕ) : F) else 0 := by
    have hn := elementarySymmetric_newton_identity F U d j
    have hsum : (∑ a ∈ Finset.HasAntidiagonal.antidiagonal j with a.1 < j,
        (-1 : F) ^ a.1 * elementarySymmetric F U a.1 d * galoisPowerSum F U a.2 d) =
        trace F U (d ^ j) := by
      rw [Finset.sum_eq_single (0, j)]
      · simp [galoisPowerSum, elementarySymmetric_zero]
      · intro a ha hne
        obtain ⟨ha, haj⟩ := Finset.mem_filter.mp ha
        have hasum := Finset.HasAntidiagonal.mem_antidiagonal.mp ha
        have ha0 : 1 ≤ a.1 := by
          by_contra hz
          have : a.1 = 0 := by omega
          have : a = (0, j) := Prod.ext this (by omega)
          exact hne this
        rw [he ha0 (by omega), if_neg (by omega), mul_zero, zero_mul]
      · intro ha
        exact (ha (Finset.mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega), hj⟩)).elim
    rw [hsum, he hj hjp] at hn
    by_cases heq : j = p - 1
    · subst j
      rw [if_pos rfl, show p - 1 + 1 = p by omega, hp.neg_one_pow] at hn
      rw [if_pos rfl]
      linear_combination hn
    · rw [if_neg heq, mul_zero] at hn
      rw [if_neg heq]
      exact (mul_eq_zero.mp hn.symm).resolve_left (pow_ne_zero _ (by norm_num))
  refine ⟨htr, ?_⟩
  have ht1 : trace F U d = 0 := by
    simpa only [pow_one, if_neg (show (1 : ℕ) ≠ p - 1 by omega)] using htr 1 (by omega) (by omega)
  have htrace := congrArg (trace F U) hd
  rw [map_sub, ht1, sub_zero, Algebra.trace_algebraMap, hdegree, nsmul_eq_mul] at htrace
  exact htrace

end Traces

section TraceDifference
variable (F E U : Type*) [Field F] [Field E] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra F E] [Algebra F U] [Module.Finite F E] [Module.Finite F U] [IsGalois F U]

/-- Trace both literal norm expansions before taking any character value
(`O:I:Sexact`). The boundary error is absent because the norms are exact. -/
private theorem scalarPhase_trace_difference {p : ℕ} (hp : Odd p) (hodd : 2 < p)
    (hFE : Module.finrank F E = p) (hFU : Module.finrank F U = p)
    (c : F) (d : U) (x : E) (ZU : U) (ZE : E)
    (hd : d ^ p - d = algebraMap F U c)
    (hgen : IntermediateField.adjoin F {d} = ⊤)
    (hZU : ZU = d ^ p +
      (∑ i ∈ Finset.Ico 1 p, algebraMap F U (elementarySymmetric F E i x) * d ^ (p - i)) +
        algebraMap F U (norm F E x))
    (hZE : ZE = x ^ p - x + algebraMap F E c) :
    trace F U ZU - trace F E ZE =
      (p : F) * norm F E x - trace F E (x ^ p) + (p : F) * trace F E x := by
  classical
  obtain ⟨htr, htrp⟩ := scalarPhase_powerTraces F U hp hodd hFU c d hd hgen
  have hsum : trace F U
      (∑ i ∈ Finset.Ico 1 p, algebraMap F U (elementarySymmetric F E i x) * d ^ (p - i)) =
        ((p - 1 : ℕ) : F) * trace F E x := by
    rw [map_sum]
    simp_rw [← Algebra.smul_def, map_smul, smul_eq_mul]
    rw [Finset.sum_eq_single 1]
    · rw [htr (p - 1) (by omega) (by omega), if_pos rfl, elementarySymmetric_one]
      ring
    · intro i hi hne
      obtain ⟨hi, hip⟩ := Finset.mem_Ico.mp hi
      rw [htr (p - i) (by omega) (by omega), if_neg (by omega), mul_zero]
    · intro hnot
      exact (hnot (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)).elim
  rw [hZU, hZE, map_add, map_add, map_add, map_sub, hsum, htrp,
    Algebra.trace_algebraMap, Algebra.trace_algebraMap, hFE, hFU]
  simp only [nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  ring

end TraceDifference

/-- The two assertions of `O:I:scalarphase`, for the literal common
norms and the original enhanced coefficients. Membership in the displayed
`mu_4` coset is expressed by an explicit complex fourth root of unity. -/
def ScalarPhaseAt
    (F E U K : Type*) [Field F] [Field E] [Field U] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
    [Algebra F E] [Algebra F U] [Algebra E K] [Algebra U K]
    [ValuativeExtension F E] [ValuativeExtension F U]
    [Module.Finite F E] [Module.Finite F U]
    (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
    (psiF Psi : ContinuousAddChar F) (p : ℕ) (c : F) (d : U) (x : E) (epsilon : F) : Prop :=
  let C := algebraMap E K x + algebraMap U K d
  let A := norm F E x
  let BU := algebraMap F U A + d ^ p + algebraMap F U epsilon
  let BE := algebraMap F E A - x + algebraMap F E c
  let ZU := norm U K C
  let ZE := norm E K C
  let S := trace F U ZU - trace F E ZE
  (∃ g : ℂ, g ^ 4 = 1 ∧
    LanglandsFirstMainLemma.localConstant U thetaU (tracePullbackAddChar F U psiF) /
      LanglandsFirstMainLemma.localConstant E thetaE (tracePullbackAddChar F E psiF) =
    g * (Psi (-S) : ℂ) *
      (tracePullbackAddChar F U Psi ((ZU - BU) ^ 2 / ((2 : U) * BU)) : ℂ) /
      (tracePullbackAddChar F E Psi ((ZE - BE) ^ 2 / ((2 : E) * BE)) : ℂ)) ∧
  S = (p : F) * A - trace F E (x ^ p) + (p : F) * trace F E x

section AtNormDepths
variable (F E U K : Type) [Field F] [Field E] [Field U] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F E] [Algebra F U] [Algebra E K] [Algebra U K]
  [ValuativeExtension F E] [ValuativeExtension F U]
  [ValuativeExtension E K] [ValuativeExtension U K]
  [Module.Finite F E] [Module.Finite F U] [Module.Finite E K] [Module.Finite U K]
  [PrimeCyclicExtension F E] [IsGalois F U]

local instance : IsGalois F E := PrimeCyclicExtension.instIsGalois F E

/-- Apply the scalar comparison to the data constructed by `normDepths`.
The public constructor below supplies the common restriction via conjugacy. -/
private theorem scalarPhase_at
    {p t h : ℕ} (hp : p.Prime) (hodd : 2 < p)
    (hFE : Module.finrank F E = p) (hFU : Module.finrank F U = p)
    (hchar : residueCharacteristic F = p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hres : residueDegree F E = 1)
    (hunr : ramificationIndex F U = 1)
    (psiF : LocalAddCharData F) (alpha : Fˣ)
    (hPsi : (scaleAddCharData F psiF alpha).conductor = -((t + 1 : ℕ) : ℤ))
    (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
    (hcondU : IsMultiplicativeConductor U thetaU (t + 1 + h))
    (hcondE : IsMultiplicativeConductor E thetaE (t + 1 + p * h))
    (hcomp : normQuasiChar U K thetaU = normQuasiChar E K thetaE)
    (hrestrict : Characters.restrictQuasiChar F U thetaU = Characters.restrictQuasiChar F E thetaE)
    (c : F) (d : U) (x : E) (epsilon : F)
    (hd : d ^ p - d = algebraMap F U c)
    (hgen : IntermediateField.adjoin F {d} = ⊤)
    (R : NormDepthsAt F E U K thetaU thetaE (scaleAddCharData F psiF alpha).character
      p t h c d x epsilon) :
    ScalarPhaseAt F E U K thetaU thetaE psiF.character (scaleAddCharData F psiF alpha).character
      p c d x epsilon := by
  let Psi := scaleAddCharData F psiF alpha
  let psiU := canonicalLocalAddCharData U (tracePullbackAddChar F U psiF.character)
    (Basic.tracePullbackAddChar_ne_one F U psiF.character psiF.character_ne_one)
  let psiE := canonicalLocalAddCharData E (tracePullbackAddChar F E psiF.character)
    (Basic.tracePullbackAddChar_ne_one F E psiF.character psiF.character_ne_one)
  let alphaU := Units.map (algebraMap F U).toMonoidHom alpha
  let alphaE := Units.map (algebraMap F E).toMonoidHom alpha
  have hPsiU := scalarPhase_scale_trace F U psiF psiU rfl alpha
  have hPsiE := scalarPhase_scale_trace F E psiF psiE rfl alpha
  have hPsiF : IsAdditiveConductor F Psi.character (-((t + 1 : ℕ) : ℤ)) :=
    hPsi ▸ Psi.isConductor
  have hnU : IsAdditiveConductor U (tracePullbackAddChar F U Psi.character) (-((t : ℤ) + 1)) :=
    (unramified_additiveConductor_compTrace F U hunr Psi.character _).2 hPsiF
  have hnE : IsAdditiveConductor E (tracePullbackAddChar F E Psi.character) (-((t : ℤ) + 1)) := by
    obtain ⟨pi, hpi, hg⟩ := monogenicUniformizer F E hres
    have hn := additiveConductor_compTrace_cyclicPrime F E ht hres pi hpi hg hPsiF
    change IsAdditiveConductor E Psi.character.compTrace _
    convert hn using 1
    rw [hFE]
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    push_cast
    ring
  have hJU : (t : ℤ) + 1 = -(scaleAddCharData U psiU alphaU).conductor := by
    have hn := (hPsiU ▸ (scaleAddCharData U psiU alphaU).isConductor).unique hnU
    omega
  have hJE : (t : ℤ) + 1 = -(scaleAddCharData E psiE alphaE).conductor := by
    have hn := (hPsiE ▸ (scaleAddCharData E psiE alphaE).isConductor).unique hnE
    omega
  rcases R with ⟨hC, hZU, hZE, _, _, RU, RE, _⟩
  let C : Kˣ := Units.mk0 (algebraMap E K x + algebraMap U K d) hC
  let ZU := normUnits U K C
  let ZE := normUnits E K C
  let BU : Uˣ := Units.mk0 (algebraMap F U (norm F E x) + d ^ p + algebraMap F U epsilon)
    ((ord_ne_top_iff U).1 (by rw [RU.coefficient_order]; exact WithTop.coe_ne_top))
  let BE : Eˣ := Units.mk0 (algebraMap F E (norm F E x) - x + algebraMap F E c)
    ((ord_ne_top_iff E).1 (by rw [RE.coefficient_order]; exact WithTop.coe_ne_top))
  have ha : thetaU (-alphaU) = thetaE (-alphaE) := by
    have heq := DFunLike.congr_fun hrestrict (-alpha)
    change thetaU (Units.map (algebraMap F U).toMonoidHom (-alpha)) =
      thetaE (Units.map (algebraMap F E).toMonoidHom (-alpha)) at heq
    convert heq using 1 <;> congr 1 <;> apply Units.ext <;> simp [alphaU, alphaE]
  have hz : thetaU ZU = thetaE ZE := DFunLike.congr_fun hcomp C
  constructor
  · exact scalarPhase_quotient F E U ⟨thetaU, t + 1 + h, hcondU⟩
      ⟨thetaE, t + 1 + p * h, hcondE⟩ psiU psiE Psi.character alphaU BU ZU alphaE BE ZE
      (by omega) ((residueCharacteristic_extension_eq F U).trans hchar)
      ((residueCharacteristic_extension_eq F E).trans hchar) hJU hJE hPsiU hPsiE
      (hPsiU.symm ▸ RU) (hPsiE.symm ▸ RE) ha hz
  · exact scalarPhase_trace_difference F E U (hp.odd_of_ne_two (by omega)) hodd hFE hFU
      c d x (ZU : U) (ZE : E) hd hgen hZU hZE

end AtNormDepths

section Assembly
variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  (E U : IntermediateField F K)

local instance : ValuativeRel E := Basic.intermediateFieldValuativeRel E
local instance : TopologicalSpace E := Basic.intermediateFieldTopology E
local instance : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E
local instance : ValuativeExtension F E := Basic.intermediateField_lowerValuativeExtension E
local instance : ValuativeExtension E K := Basic.intermediateField_upperValuativeExtension E
local instance : ValuativeRel U := Basic.intermediateFieldValuativeRel U
local instance : TopologicalSpace U := Basic.intermediateFieldTopology U
local instance : IsNonarchimedeanLocalField U := Basic.intermediateField_localField U
local instance : ValuativeExtension F U := Basic.intermediateField_lowerValuativeExtension U
local instance : ValuativeExtension U K := Basic.intermediateField_upperValuativeExtension U

variable {p : ℕ} (hp : p.Prime)
  (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
  (hFE : Module.finrank F E = p) (hFU : Module.finrank F U = p)

include hp hG hFE hFU

set_option maxHeartbeats 800000 in
/-- **Paper Lemma 6.11 (`O:I:scalarphase`).**

For the actual primitive compatible pair in the unramified--ramified
prime-square diamond, construct the exact norm witness using `normDepths`
and compare the canonical FML local constants at the original additive
character. `ScalarPhaseAt` contains both `O:I:ratioformula`, with the two
complete affine corrections, and the exact trace identity `O:I:Sexact`.

The common restriction is proved by `Characters.conjugacy`, including the
triviality of both full lower norm-character products in odd degree. The
models and actual twist are the constructed outputs of `models`/`twist`;
no stationary coefficient, exact norm choice, or cancellation is assumed.
Both field characteristics, nonunitary quasi-characters, `h = 0`, and the
boundary `h = t` are retained. -/
theorem scalarPhase
    {t q : ℕ} (hodd : 2 < p) (htpos : 0 < t)
    (hchar : residueCharacteristic F = p) :
  letI : IsGalois F E :=
    (Basic.intermediateField_tower_compatible hp hG E hFE).2.2.2.2.2.2.2.2.2.2.2.1.1
  letI : IsGalois F U :=
    (Basic.intermediateField_tower_compatible hp hG U hFU).2.2.2.2.2.2.2.2.2.2.2.1.1
  ∀ (_ht : PrimeCyclicExtension.IsLowerBreak F E t) (_hres : residueDegree F E = 1)
    (_hunr : ramificationIndex F U = 1) (_hsup : E ⊔ U = ⊤)
    (_hne : Ramification.intermediateNormRange U ≠ Ramification.intermediateNormRange E)
    (_hq : q = (t + 1) ⌈/⌉ p) {hqpos : 0 < q}
    (tau : NormCharacter F E) (_htaune : tau ≠ 1)
    (psiF : LocalAddCharData F) (alpha : Fˣ)
    (_hPsi : (scaleAddCharData F psiF alpha).conductor = -((t + 1 : ℕ) : ℤ))
    (_htau : ∀ z : lattice F (q : ℤ),
      tau.1 (positiveUnitOfLattice F hqpos (-z)) =
        (scaleAddCharData F psiF alpha).character (truncatedLog p (z : F)))
    (c : ringOfIntegers F) (d : ringOfIntegers U)
    (_hd : (d : U) ^ p - (d : U) = algebraMap F U (c : F))
    (_hgen : IntermediateField.adjoin F {(d : U)} = ⊤)
    {M : CompatibleModels F E U K p (t + 1) q hqpos tau.1
      (scaleAddCharData F psiF alpha).character (c : F) (d : U)}
    {thetaU : ContinuousQuasiChar U} {thetaE : ContinuousQuasiChar E}
    (_hcomp : normQuasiChar U K thetaU = normQuasiChar E K thetaE)
    (_hprimitive : ¬ ∃ chi : ContinuousQuasiChar F, normQuasiChar F K chi = normQuasiChar U K thetaU)
    (D : ActualTwist F E U K M thetaU thetaE) (_hh : D.h ≤ t),
    ∃ (x : E) (epsilon : F),
      epsilon ∈ lattice F 0 ∧
      (D.h < t → epsilon = 0) ∧
      (∀ z : lattice F (((t + 1 + D.h) / 2 : ℕ) : ℤ),
        D.lambda (positiveUnitOfLattice F (normChoice_depths hodd htpos).1 (-z)) =
          (scaleAddCharData F psiF alpha).character
            ((norm F E x + epsilon) * truncatedLog p (z : F))) ∧
      (0 < D.h → ord E x = ((-(D.h : ℤ) : ℤ) : WithTop ℤ) ∧
        ord F (norm F E x) = ((-(D.h : ℤ) : ℤ) : WithTop ℤ)) ∧
      (D.h = 0 → x ∈ lattice E 0) ∧
      (QuasiCharTrivialOnUnitFiltration F D.lambda ((t + 1 + D.h) / 2) →
        x = 0 ∧ norm F E x = 0 ∧ epsilon = 0) ∧
      NormDepthsAt F E U K thetaU thetaE (scaleAddCharData F psiF alpha).character
        p t D.h (c : F) (d : U) x epsilon ∧
      ScalarPhaseAt F E U K thetaU thetaE psiF.character (scaleAddCharData F psiF alpha).character
        p (c : F) (d : U) x epsilon := by
  letI : PrimeCyclicExtension F E :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F E
      (Basic.intermediateField_tower_compatible hp hG E hFE).2.2.2.2.2.2.2.2.2.2.2.1
  letI : PrimeCyclicExtension F U :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F U
      (Basic.intermediateField_tower_compatible hp hG U hFU).2.2.2.2.2.2.2.2.2.2.2.1
  letI : PrimeCyclicExtension E K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension E K
      (Basic.intermediateField_tower_compatible hp hG E hFE).2.2.2.2.2.2.2.2.2.2.2.2
  letI : PrimeCyclicExtension U K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension U K
      (Basic.intermediateField_tower_compatible hp hG U hFU).2.2.2.2.2.2.2.2.2.2.2.2
  letI : IsGalois F E := PrimeCyclicExtension.instIsGalois F E
  letI : IsGalois F U := PrimeCyclicExtension.instIsGalois F U
  intro ht hres hunr hsup hne hq hqpos tau htaune psiF alpha hPsi htau c d hd hgen
    M thetaU thetaE hcomp hprimitive D hh
  have hEK := (Basic.intermediateField_tower_compatible hp hG E hFE).2.2.2.2.2.2.2.2.2.2.1
  have hUK := (Basic.intermediateField_tower_compatible hp hG U hFU).2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨x, epsilon, hepsilon, hepsilon_zero, hchart, horder, hintegral, hzero, R⟩ :=
    normDepths F K E U hp hodd htpos hFE hFU hEK hUK hchar ht hres hunr hsup hq tau htaune
      (scaleAddCharData F psiF alpha) hPsi htau c d hd hgen D hh
  obtain ⟨_, _, hrestrict, hproducts, _⟩ :=
    Characters.conjugacy hp hG U E hFU hFE hne thetaU thetaE
      (normQuasiChar U K thetaU) rfl hcomp.symm hprimitive
  obtain ⟨hprodU, hprodE⟩ := hproducts (hp.odd_of_ne_two (by omega))
  have hrestriction : Characters.restrictQuasiChar F U thetaU =
      Characters.restrictQuasiChar F E thetaE := by
    apply ContinuousMonoidHom.ext
    intro z
    have hz := DFunLike.congr_fun hrestrict z
    simpa only [hprodU, hprodE, ContinuousQuasiChar.mul_apply,
      ContinuousQuasiChar.one_apply, mul_one] using hz
  refine ⟨x, epsilon, hepsilon, hepsilon_zero, hchart, horder, hintegral, hzero, R, ?_⟩
  exact scalarPhase_at F E U K hp hodd hFE hFU hchar ht hres hunr psiF alpha hPsi
    thetaU thetaE D.conductorU D.conductorE hcomp hrestriction (c : F) (d : U) x epsilon hd hgen R

end Assembly

end

end LanglandsSecondMainLemma.Odd.UR
