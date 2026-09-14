import LanglandsSecondMainLemma.Odd.Models.Realization
import LanglandsSecondMainLemma.Odd.Total.TraceNorm
import LanglandsSecondMainLemma.Odd.Parameters.Lamprecht
import LanglandsSecondMainLemma.Characters.OddPower

/-!
# The minimal-conductor row

Paper Theorem 9.35 (`O:G:minimal`), with the local setup at lines 4962--4982
and proof at lines 5082--5103 of the corrected manuscript.

The norm-character chart is constructed from the actual additive character.
Realization supplies the exact coordinate and an allowed conjugate of the
first endpoint. The full Lamprecht formulas, the trace--norm bound for that
same coordinate, and the independently proved odd common power then compare
the complete factors, including both lower norm-character products.
-/

namespace LanglandsSecondMainLemma.Odd.Conductors

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

open private additiveConductor_of_normCharacterChart from
  LanglandsSecondMainLemma.Odd.Models.Setup
open private norm_tower_residueDegrees from
  LanglandsSecondMainLemma.Odd.Models.PolynomialCoefficients
open private twistNormRanges_ne from
  LanglandsSecondMainLemma.Odd.Models.TwistFormula

/-- Apply the complete Lamprecht formula to a full unit model, retaining
 the product of the actual scalar and norm coefficient. Exactness of the
 scaled additive conductor proves the required coefficient order. -/
private theorem fullModel_lamprecht
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    {p q t T : ℕ} (hchar : residueCharacteristic E = p) (hodd : p ≠ 2)
    (hm : theta.conductor = t + T) (hlarge : 1 < theta.conductor)
    (hq : q = theta.conductor ⌈/⌉ p) (hqpos : 0 < q)
    (alpha b : Eˣ) (hb : ord E (b : E) = ((-(t : ℤ)) : WithTop ℤ))
    (hPsi : IsAdditiveConductor E (scaleAddCharData E psi alpha).character (-(T : ℤ)))
    (hmodel : ∀ u : unitFiltration E q,
      theta.character u = (scaleAddCharData E psi alpha).character
        ((b : E) * truncatedLog p (1 - ((u : Eˣ) : E)))) :
    ∃ g : ℂ, g ^ 4 = 1 ∧
      localConstant E theta.character psi.character =
        (theta.character ((-(alpha * b))⁻¹) : ℂ) *
          (psi.character (-((alpha * b : Eˣ) : E)) : ℂ) * g := by
  have hcond := (scaleAddCharData E psi alpha).isConductor.unique hPsi
  have hC : IsEnhancedStationaryCoefficient E theta psi p q hqpos
      (-psi.conductor) (alpha * b) := by
    constructor
    · rw [Units.val_mul, ord_mul, ord_coe_eq_unitOrder, hb]
      norm_cast
      simp only [scaleAddCharData_conductor] at hcond
      rw [hm, Nat.cast_add]
      omega
    · intro z
      have h := hmodel (positiveUnitOfLattice E hqpos (-z))
      simpa [scaleAddCharData_character_apply, mul_assoc] using h
  obtain ⟨g, hg, hformula, _⟩ := Parameters.lamprecht E theta psi
    p q (theta.conductor / 2) (theta.conductor % 2) hchar hodd
    (by omega) (by omega) hlarge hq hqpos (alpha * b) hC
  exact ⟨g, hg, hformula⟩

section Diamond

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]
  {p : ℕ} (hp : p.Prime)
  (hG : Nonempty
    (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
  (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
  (D : Total.OddTotalBreakData (F := F) (K := K) hp hG)

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

local notation "B₁" => D.B₁
local notation "B₂" => D.B₂

local instance : PrimeCyclicExtension F B₁ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₁
    (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.2.2.2.1
local instance : PrimeCyclicExtension B₁ K :=
  PrimeCyclicExtension.ofCyclicPrimeExtension B₁ K
    (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.2.2.2.2
local instance : PrimeCyclicExtension F B₂ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₂
    (Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.1
local instance : PrimeCyclicExtension B₂ K :=
  PrimeCyclicExtension.ofCyclicPrimeExtension B₂ K
    (Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.2

include hp hG hres hchar D in
/-- The actual minimal quotient has fourth power one. All full coefficients
and the trace--norm cancellation are constructed within the proof. -/
private theorem minimal_fourthPower
    (phi₁ : ContinuousQuasiChar B₁) (phi₂ : ContinuousQuasiChar B₂)
    (hcompat : normQuasiChar B₁ K phi₁ = normQuasiChar B₂ K phi₂)
    (hprimitive : ¬ ∃ chi : ContinuousQuasiChar F,
      normQuasiChar F K chi = normQuasiChar B₂ K phi₂)
    (hc₂ : IsMultiplicativeConductor B₂ phi₂ (Models.secondModelConductor D))
    (psiF : ContinuousAddChar F) (hpsiF : psiF ≠ 1) :
    (localConstant B₁ phi₁ (tracePullbackAddChar F B₁ psiF) /
      localConstant B₂ phi₂ (tracePullbackAddChar F B₂ psiF)) ^ 4 = 1 := by
  classical
  have hodd : Odd p := hp.odd_of_ne_two (by have := D.odd_prime; omega)
  have ht₂ : 0 < D.t₂ := D.t_pos.trans_le D.t_le_t₂
  have hd₁ : Module.finrank F B₁ = p := D.degree_B₁
  have hd₂ : Module.finrank F B₂ = p := D.degree_B₂
  obtain ⟨hrF₁, hr₁K⟩ := norm_tower_residueDegrees B₁ hres
  obtain ⟨hrF₂, _⟩ := norm_tower_residueDegrees B₂ hres
  obtain ⟨pi₁, hpi₁, hgen₁⟩ := monogenicUniformizer F B₁ hrF₁
  obtain ⟨pi₂, hpi₂, hgen₂⟩ := monogenicUniformizer F B₂ hrF₂
  letI := primeCyclicNormCharacter_finite F B₂
  letI : Nontrivial (NormCharacter F B₂) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [ramifiedNormCharacter_card F B₂ D.B₂_breaks.1 hrF₂ pi₂ hpi₂ hgen₂,
        hd₂]
      exact hp.one_lt)
  obtain ⟨tau, htau⟩ := exists_ne (1 : NormCharacter F B₂)
  have htauC := ramifiedNormCharacter_conductor F B₂ D.B₂_breaks.1 hrF₂
    pi₂ hpi₂ hgen₂ tau htau
  let psi := canonicalLocalAddCharData F psiF hpsiF
  let tauData : LocalQuasiCharData F := ⟨tau.1, D.t₂ + 1, htauC⟩
  let c := (D.t₂ + 1) ⌈/⌉ p
  have hcover : D.t₂ + 1 ≤ p * c := le_smul_ceilDiv hp.pos
  have hcpos : 0 < c := by
    by_contra h
    have : c = 0 := by omega
    simp only [this, mul_zero] at hcover
    omega
  have hct : c ≤ D.t₂ := by
    apply (ceilDiv_le_iff_le_mul hp.pos).2
    calc
      D.t₂ + 1 ≤ 2 * D.t₂ := by omega
      _ ≤ p * D.t₂ := Nat.mul_le_mul_right _ hp.two_le
  obtain ⟨alpha₀, halpha₀, _⟩ := enhancedCoefficient_exists_unique_mod F tauData psi
    p c (-psi.conductor) hchar hp hcpos (by change c ≤ D.t₂ + 1; omega)
    hcover rfl (by change 1 < D.t₂ + 1; omega)
    (by change c + 1 ≤ D.t₂ + 1; omega)
  let Psi := (scaleAddCharData F psi alpha₀).character
  have hchart : ∀ z : lattice F (c : ℤ),
      tau.1 (positiveUnitOfLattice F hcpos (-z)) = Psi (truncatedLog p (z : F)) :=
    halpha₀.2
  obtain ⟨j, Delta, a, _hjpos, _hjp, htauj, hchartj, hpower, hroot, hDelta, ha,
      hprime, hgen, hnorm, M, hext₂, hc₂', sigma, hext₁, hpull, hc₁', hconstant⟩ :=
    Models.realization hp hG hres hchar D phi₁ phi₂ hcompat hprimitive hc₂.trivial
      c rfl hcpos tau htau Psi hchart
  have hPsi := additiveConductor_of_normCharacterChart F B₂ hp D.odd_prime hchar
    D.degree_B₂ D.B₂_breaks.1 ht₂ hrF₂ rfl hcpos (tau ^ j) htauj (Psi ^ j) hchartj
  have hphase : ∀ x : F, (Psi ^ j) x = psiF (((j : F) * (alpha₀ : F)) * x) :=
    hpower psiF alpha₀ (fun _ => rfl)
  have halpha : (j : F) * (alpha₀ : F) ≠ 0 := by
    intro hz
    apply hPsi.character_ne_one
    apply ContinuousAddChar.ext
    intro x
    rw [hphase, hz, zero_mul]
    exact psiF.toAddChar.map_zero_eq_one
  let alpha : Fˣ := Units.mk0 ((j : F) * (alpha₀ : F)) halpha
  have hphase' : ∀ x : F, (Psi ^ j) x = psiF ((alpha : F) * x) := hphase
  let alpha₁ : B₁ˣ := Units.map (algebraMap F B₁) alpha
  let alpha₂ : B₂ˣ := Units.map (algebraMap F B₂) alpha
  let psi₁ := canonicalLocalAddCharData B₁ (tracePullbackAddChar F B₁ psiF)
    (Basic.tracePullbackAddChar_ne_one F B₁ psiF hpsiF)
  let psi₂ := canonicalLocalAddCharData B₂ (tracePullbackAddChar F B₂ psiF)
    (Basic.tracePullbackAddChar_ne_one F B₂ psiF hpsiF)
  have hscale₁ : (scaleAddCharData B₁ psi₁ alpha₁).character =
      tracePullbackAddChar F B₁ (Psi ^ j) := by
    apply ContinuousAddChar.ext
    intro x
    simp only [scaleAddCharData_character_apply, psi₁,
      canonicalLocalAddCharData_character, tracePullbackAddChar_apply, hphase']
    congr 1
    change trace F B₁ (algebraMap F B₁ (alpha : F) * x) = (alpha : F) * trace F B₁ x
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hscale₂ : (scaleAddCharData B₂ psi₂ alpha₂).character =
      tracePullbackAddChar F B₂ (Psi ^ j) := by
    apply ContinuousAddChar.ext
    intro x
    simp only [scaleAddCharData_character_apply, psi₂,
      canonicalLocalAddCharData_character, tracePullbackAddChar_apply, hphase']
    congr 1
    change trace F B₂ (algebraMap F B₂ (alpha : F) * x) = (alpha : F) * trace F B₂ x
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hPsi₁ := additiveConductor_compTrace_cyclicPrime F B₁ D.B₁_breaks.1
    hrF₁ pi₁ hpi₁ hgen₁ hPsi
  have hPsi₂ := additiveConductor_compTrace_cyclicPrime F B₂ D.B₂_breaks.1
    hrF₂ pi₂ hpi₂ hgen₂ hPsi
  have hcond₁ : (p : ℤ) * (-((D.t₂ + 1 : ℕ) : ℤ)) +
      (((p - 1) * (D.t + 1) : ℕ) : ℤ) = -((D.tPrime + 1 : ℕ) : ℤ) := by
    simp only [D.t₂_eq, D.tPrime_eq, Nat.cast_add, Nat.cast_mul,
      Nat.cast_sub hp.one_le, Nat.cast_one]
    ring
  have hcond₂ : (p : ℤ) * (-((D.t₂ + 1 : ℕ) : ℤ)) +
      (((p - 1) * (D.t₂ + 1) : ℕ) : ℤ) = -((D.t₂ + 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hp.one_le]
    ring
  rw [hd₁, hcond₁] at hPsi₁
  rw [hd₂, hcond₂] at hPsi₂
  have hDelta0 : Delta ≠ 0 := (ord_ne_top_iff K).1 (by rw [hDelta]; simp)
  let DeltaU : Kˣ := Units.mk0 Delta hDelta0
  let bU : B₁ˣ := normUnits B₁ K DeltaU
  let aU : B₂ˣ := normUnits B₂ K DeltaU
  have hbU : (bU : B₁) = norm B₁ K Delta := rfl
  have haU : (aU : B₂) = a := hnorm
  have hb : ord B₁ (bU : B₁) = ((-(D.t : ℤ)) : WithTop ℤ) := by
    rw [hbU, ord_norm, hr₁K, one_nsmul, hDelta]
    norm_cast
  let theta₁ := Basic.conjugateQuasiChar F B₁ sigma phi₁
  let thetaData₁ : LocalQuasiCharData B₁ := ⟨theta₁, Models.firstModelConductor D, hc₁'⟩
  let thetaData₂ : LocalQuasiCharData B₂ := ⟨phi₂, Models.secondModelConductor D, hc₂'⟩
  obtain ⟨hq₁, hq₂, _⟩ := Models.domains_original D hres
  have hmodel₁ : ∀ u : unitFiltration B₁ (Models.firstModelDepth D),
      thetaData₁.character u = (scaleAddCharData B₁ psi₁ alpha₁).character
        ((bU : B₁) * truncatedLog p (1 - ((u : B₁ˣ) : B₁))) := by
    intro u
    rw [hscale₁]
    exact (DFunLike.congr_fun hext₁ u).trans (M.R₁_apply u)
  have hmodel₂ : ∀ u : unitFiltration B₂ (Models.secondModelDepth D),
      thetaData₂.character u = (scaleAddCharData B₂ psi₂ alpha₂).character
        ((aU : B₂) * truncatedLog p (1 - ((u : B₂ˣ) : B₂))) := by
    intro u
    rw [hscale₂, haU]
    exact (DFunLike.congr_fun hext₂ u).trans (M.R₂_apply u)
  obtain ⟨g₁, hg₁, hf₁⟩ := fullModel_lamprecht B₁ thetaData₁ psi₁
    ((residueCharacteristic_extension_eq F B₁).trans hchar) (by have := D.odd_prime; omega)
    (t := D.t) (T := D.tPrime + 1)
    (by dsimp [thetaData₁, Models.firstModelConductor]; omega)
    (by dsimp [thetaData₁, Models.firstModelConductor]; have := D.t_pos; omega)
    rfl hq₁ alpha₁ bU hb (by rw [hscale₁]; exact hPsi₁) hmodel₁
  obtain ⟨g₂, hg₂, hf₂⟩ := fullModel_lamprecht B₂ thetaData₂ psi₂
    ((residueCharacteristic_extension_eq F B₂).trans hchar) (by have := D.odd_prime; omega)
    (t := D.t) (T := D.t₂ + 1)
    (by dsimp [thetaData₂, Models.secondModelConductor]; omega)
    (by dsimp [thetaData₂, Models.secondModelConductor]; have := D.t_pos; omega)
    rfl hq₂ alpha₂ aU (by rw [haU]; exact ha)
    (by rw [hscale₂]; exact hPsi₂) hmodel₂
  have hne := twistNormRanges_ne hp hG hres hchar D
  obtain ⟨_, _, hrestrict, hproducts, _⟩ := Characters.conjugacy hp hG B₁ B₂
    D.degree_B₁ D.degree_B₂ hne theta₁ phi₂ (normQuasiChar B₂ K phi₂)
    hpull rfl hprimitive
  obtain ⟨hprod₁, hprod₂⟩ := hproducts hodd
  have hnormValue : theta₁ bU = phi₂ aU := DFunLike.congr_fun hpull DeltaU
  have hscalar : theta₁ (Units.map (algebraMap F B₁) (-alpha)) =
      phi₂ (Units.map (algebraMap F B₂) (-alpha)) := by
    have h := DFunLike.congr_fun hrestrict (-alpha)
    change theta₁ (Units.map (algebraMap F B₁) (-alpha)) *
        Characters.intermediateNormCharacterProduct hp hG B₁ D.degree_B₁ (-alpha) =
      phi₂ (Units.map (algebraMap F B₂) (-alpha)) *
        Characters.intermediateNormCharacterProduct hp hG B₂ D.degree_B₂ (-alpha) at h
    rw [hprod₁, hprod₂, ContinuousQuasiChar.one_apply, mul_one, mul_one] at h
    exact h
  have hneg₁ : -(alpha₁ * bU) = Units.map (algebraMap F B₁) (-alpha) * bU := by
    apply Units.ext
    simp [alpha₁]
  have hneg₂ : -(alpha₂ * aU) = Units.map (algebraMap F B₂) (-alpha) * aU := by
    apply Units.ext
    simp [alpha₂]
  have hvalue : theta₁ ((-(alpha₁ * bU))⁻¹) = phi₂ ((-(alpha₂ * aU))⁻¹) := by
    rw [map_inv, map_inv, hneg₁, hneg₂, map_mul, map_mul, hscalar, hnormValue]
  have hei := (Models.realization_twistedEstimates_of_coordinate hp hG hres hchar D
    Delta a hroot hDelta hprime hgen).2.2.1
  have htrace := Total.traceNorm hp hG hres hchar D Delta a hroot hgen hei
  have hphaseZero : (Psi ^ j) (trace F B₁ (norm B₁ K Delta) - trace F B₂ a) = 1 :=
    hPsi.trivial _ (by simpa only [neg_neg, Nat.cast_add, Nat.cast_one, add_comm] using htrace)
  have htraceValue : (Psi ^ j) (trace F B₁ (bU : B₁)) =
      (Psi ^ j) (trace F B₂ (aU : B₂)) := by
    rw [hbU, haU]
    change (Psi ^ j).toAddChar _ = 1 at hphaseZero
    rw [AddChar.map_sub_eq_div] at hphaseZero
    exact div_eq_one.mp hphaseZero
  have hnegTraceValue : (Psi ^ j) (-trace F B₁ (bU : B₁)) =
      (Psi ^ j) (-trace F B₂ (aU : B₂)) := by
    change (Psi ^ j).toAddChar _ = (Psi ^ j).toAddChar _
    rw [AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv]
    exact congrArg Inv.inv htraceValue
  have hadd : psi₁.character (-((alpha₁ * bU : B₁ˣ) : B₁)) =
      psi₂.character (-((alpha₂ * aU : B₂ˣ) : B₂)) := by
    have h₁ := DFunLike.congr_fun hscale₁ (-(bU : B₁))
    have h₂ := DFunLike.congr_fun hscale₂ (-(aU : B₂))
    simp only [scaleAddCharData_character_apply, tracePullbackAddChar_apply,
      map_neg] at h₁ h₂
    rw [hnegTraceValue] at h₁
    simpa only [Units.val_mul, mul_neg] using h₁.trans h₂.symm
  change localConstant B₁ theta₁ (tracePullbackAddChar F B₁ psiF) = _ at hf₁
  change localConstant B₂ phi₂ (tracePullbackAddChar F B₂ psiF) = _ at hf₂
  rw [hconstant psiF hpsiF] at hf₁
  have hcommon : (thetaData₂.character ((-(alpha₂ * aU))⁻¹) : ℂ) *
      (psi₂.character (-((alpha₂ * aU : B₂ˣ) : B₂)) : ℂ) ≠ 0 :=
    mul_ne_zero (ContinuousQuasiChar.apply_ne_zero _ _) (ContinuousAddChar.apply_ne_zero _ _)
  rw [hf₁, hf₂]
  change (((theta₁ ((-(alpha₁ * bU))⁻¹) : ℂ) * _ * g₁) /
    ((phi₂ ((-(alpha₂ * aU))⁻¹) : ℂ) * _ * g₂)) ^ 4 = 1
  rw [hvalue, hadd, mul_div_mul_left _ _ hcommon, div_pow, hg₁, hg₂, div_self one_ne_zero]

include hp hG hres hchar D in
/-- **Paper Theorem 9.35 (`O:G:minimal`).** For the actual distinguished
fields of the totally ramified odd prime-square diamond, a primitive
compatible pair with conductors `m₁ = 1+t+t'` and `m₂ = 1+t+t₂` has equal
complete Second-Main-Lemma factors. Both lower products range over every
continuous group character trivial on the corresponding norm subgroup.

The additive character is arbitrary and nontrivial. Both field
characteristics and nonunitary quasi-characters are retained. No coordinate,
stationary model, phase cancellation, or local-constant comparison is assumed. -/
theorem minimal :
    letI := primeCyclicNormCharacter_finite F B₁
    letI := primeCyclicNormCharacter_finite F B₂
    letI := Fintype.ofFinite (NormCharacter F B₁)
    letI := Fintype.ofFinite (NormCharacter F B₂)
    ∀ (phi₁ : ContinuousQuasiChar B₁) (phi₂ : ContinuousQuasiChar B₂),
      normQuasiChar B₁ K phi₁ = normQuasiChar B₂ K phi₂ →
      (¬ ∃ chi : ContinuousQuasiChar F,
        normQuasiChar F K chi = normQuasiChar B₂ K phi₂) →
      IsMultiplicativeConductor B₁ phi₁ (Models.firstModelConductor D) →
      IsMultiplicativeConductor B₂ phi₂ (Models.secondModelConductor D) →
      ∀ (psiF : ContinuousAddChar F), psiF ≠ 1 →
      localConstant B₁ phi₁ (tracePullbackAddChar F B₁ psiF) *
          (∏ omega : NormCharacter F B₁, localConstant F omega.1 psiF) =
        localConstant B₂ phi₂ (tracePullbackAddChar F B₂ psiF) *
          (∏ omega : NormCharacter F B₂, localConstant F omega.1 psiF) := by
  letI := primeCyclicNormCharacter_finite F B₁
  letI := primeCyclicNormCharacter_finite F B₂
  letI := Fintype.ofFinite (NormCharacter F B₁)
  letI := Fintype.ofFinite (NormCharacter F B₂)
  intro phi₁ phi₂ hcompat hprimitive _hc₁ hc₂ psiF hpsiF
  have hodd : Odd p := hp.odd_of_ne_two (by have := D.odd_prime; omega)
  obtain ⟨_, _, hprod₁, hprod₂, hpower⟩ := Characters.oddPower hp hodd hG
    B₁ B₂ D.degree_B₁ D.degree_B₂ (twistNormRanges_ne hp hG hres hchar D)
    phi₁ phi₂ (normQuasiChar B₂ K phi₂) hcompat rfl hprimitive psiF hpsiF
  rw [hprod₁, hprod₂, mul_one, mul_one] at hpower ⊢
  have hfour := minimal_fourthPower hp hG hres hchar D
    phi₁ phi₂ hcompat hprimitive hc₂ psiF hpsiF
  have hcoprime : p.Coprime 4 := hodd.coprime_two_right.pow_right 2
  have hratio : localConstant B₁ phi₁ (tracePullbackAddChar F B₁ psiF) /
      localConstant B₂ phi₂ (tracePullbackAddChar F B₂ psiF) = 1 :=
    (pow_eq_one_iff_of_coprime hcoprime).mp ⟨hpower, hfour⟩
  apply (div_eq_one_iff_eq _).mp hratio
  exact (localConstant_isDeltaFinite B₂).apply_ne_zero
    (canonicalLocalQuasiCharData B₂ phi₂)
    (canonicalLocalAddCharData B₂ (tracePullbackAddChar F B₂ psiF)
      (Basic.tracePullbackAddChar_ne_one F B₂ psiF hpsiF))

end Diamond

end

end LanglandsSecondMainLemma.Odd.Conductors
