import LanglandsFirstMainLemma.Delta.FirstMainStatement
import LanglandsFirstMainLemma.Main
import LanglandsSecondMainLemma.Odd.UR.TraceDepth
import LanglandsSecondMainLemma.Odd.UR.CubicPhase
import LanglandsSecondMainLemma.Odd.UR.Stable
import LanglandsSecondMainLemma.Characters.OddPower

/-!
# The odd unramified--ramified comparison

Paper Theorem 6.1 (`O:I:main`), in the full setup of lines 1060--1128.
The public `comparison` constructs the setup and actual twist from the
primitive compatible pair. For `h ≤ t`, the noncubic rows use `traceDepth`
and the boundary correction below, while `p = 3, h = t` uses `cubicIdentity`
and its proved phase cancellation. For `h ≥ t + 1`, the accepted stable
comparison applies. The common odd power removes the fourth-root ambiguity,
and both complete lower norm-character products are retained.

The noncubic boundary calculation (`O:I:Uboundarycorrection`, lines
1659--1671) preserves the original admissible denominator and integral
critical error. No model, exact norm choice, or phase cancellation is an
unproved hypothesis of the public theorem.
-/

open LanglandsFirstMainLemma
open scoped BigOperators

namespace LanglandsSecondMainLemma.Odd.UR
noncomputable section

section Boundary
variable (F U : Type*) [Field F] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U] [IsGalois F U]

/-- Paper `O:I:Uboundarycorrection`, including the integral critical error.
For `p > 3` the first two power traces vanish, and the remaining constant
term has trace `p * epsilon²`, which lies in the actual character kernel. -/
theorem unramifiedBoundaryCorrection {p t : ℕ} (hodd : Odd p) (hp : 3 < p)
    (ht : 0 < t) (hdegree : Module.finrank F U = p)
    (hunr : ramificationIndex F U = 1) (hchar : residueCharacteristic F = p)
    (Psi : ContinuousAddChar F) (hPsi : IsAdditiveConductor F Psi (-((t : ℤ) + 1)))
    (c : F) (d : ringOfIntegers U)
    (hd : (d : U) ^ p - (d : U) = algebraMap F U c)
    (hgen : IntermediateField.adjoin F {(d : U)} = ⊤)
    (A b epsilon : F) (eta : U)
    (hA : ord F A = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hb : b ∈ lattice F 0) (hepsilon : epsilon ∈ lattice F 0)
    (hB : ord U (algebraMap F U A + (d : U) ^ p + algebraMap F U epsilon) =
      ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (heta : eta ∈ lattice U 0)
    (hdiff : eta - (algebraMap F U b * (d : U) - algebraMap F U epsilon) ∈ lattice U 1) :
    tracePullbackAddChar F U Psi
      (eta ^ 2 / (2 * (algebraMap F U A + (d : U) ^ p + algebraMap F U epsilon))) = 1 := by
  let eta0 := algebraMap F U b * (d : U) - algebraMap F U epsilon
  let B := algebraMap F U A + (d : U) ^ p + algebraMap F U epsilon
  have hmap {z : F} (hz : z ∈ lattice F 0) : algebraMap F U z ∈ lattice U 0 := by
    simpa only [mem_lattice, ord_algebraMap, hunr, one_nsmul] using hz
  have hd0 : (d : U) ∈ lattice U 0 := (mem_lattice_zero_iff U).mpr d.property
  have hdp : (d : U) ^ p ∈ lattice U 0 := (mem_lattice_zero_iff U).mpr (pow_mem d.property p)
  have heta0 : eta0 ∈ lattice U 0 :=
    sub_mem_lattice U (by simpa using mul_mem_lattice U (hmap hb) hd0) (hmap hepsilon)
  have hBA : B - algebraMap F U A ∈ lattice U 0 := by
    convert add_mem_lattice U hdp (hmap hepsilon) using 1
    dsimp [B]
    ring
  have hAU : ord U (algebraMap F U A) = ((-(t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hunr, one_nsmul, hA]
  have htwoF : ord F (2 : F) = 0 :=
    ord_natCast_eq_zero_of_lt_residueCharacteristic F (j := 2) (by decide) (by omega)
  have htwoU : ord U (2 : U) = 0 := by
    rw [← map_ofNat (algebraMap F U) 2, ord_algebraMap, hunr, one_nsmul, htwoF]
  have hA0 := (ord_ne_top_iff U).1 (hAU ▸ WithTop.coe_ne_top)
  have hB0 : B ≠ 0 := (ord_ne_top_iff U).1 (hB ▸ WithTop.coe_ne_top)
  have h20 : (2 : U) ≠ 0 := (ord_ne_top_iff U).1 (htwoU ▸ (by simp))
  have hprec : eta ^ 2 / (2 * B) - eta0 ^ 2 / (2 * algebraMap F U A) ∈
      lattice U ((t : ℤ) + 1) := by
    have he : eta ^ 2 / (2 * B) - eta0 ^ 2 / (2 * algebraMap F U A) =
        (eta - eta0) * (eta + eta0) / (2 * B) +
          eta0 ^ 2 * (algebraMap F U A - B) / (2 * B * algebraMap F U A) := by
      field_simp [hB0]
      ring
    rw [he]
    apply add_mem_lattice U
    · apply (div_mem_lattice_iff U _ _ (-(t : ℤ)) ((t : ℤ) + 1)
        (by rw [ord_mul, htwoU, hB, zero_add])).2
      simpa using mul_mem_lattice U hdiff (add_mem_lattice U heta heta0)
    · apply (div_mem_lattice_iff U _ _ (-(t : ℤ) + -(t : ℤ)) ((t : ℤ) + 1)
        (by rw [ord_mul, ord_mul, htwoU, hB, hAU, zero_add, WithTop.coe_add])).2
      apply lattice_antitone U (n := 0) (by omega)
      have hn := mul_mem_lattice U (mul_mem_lattice U heta0 heta0)
        (neg_mem_lattice U hBA)
      simpa only [neg_sub, pow_two, add_zero] using hn
  have hkernel : AddCharTrivialOnLattice U (tracePullbackAddChar F U Psi) ((t : ℤ) + 1) := by
    have hc := (unramified_additiveConductor_compTrace F U hunr Psi _).2 hPsi
    simpa only [neg_neg] using (show AddCharTrivialOnLattice U
      (tracePullbackAddChar F U Psi) (-(-((t : ℤ) + 1))) from hc.trivial)
  have heq : tracePullbackAddChar F U Psi (eta ^ 2 / (2 * B)) =
      tracePullbackAddChar F U Psi (eta0 ^ 2 / (2 * algebraMap F U A)) := by
    apply div_eq_one.mp
    exact ((tracePullbackAddChar F U Psi).toAddChar.map_sub_eq_div _ _).symm.trans
      (hkernel _ hprec)
  change tracePullbackAddChar F U Psi (eta ^ 2 / (2 * B)) = 1
  rw [heq, tracePullbackAddChar_apply,
    show (2 : U) * algebraMap F U A = algebraMap F U (2 * A) by simp only [map_mul, map_ofNat]]
  have hdiv (z : U) (a : F) : trace F U (z / algebraMap F U a) = trace F U z / a := by
    rw [div_eq_mul_inv, ← map_inv₀, mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
    ring
  rw [hdiv]
  obtain ⟨htr, _⟩ := scalarPhase_powerTraces F U hodd (by omega) hdegree c (d : U) hd hgen
  have ht1 : trace F U (d : U) = 0 := by simpa [show 1 ≠ p - 1 by omega] using htr 1 (by omega) (by omega)
  have ht2 : trace F U ((d : U) ^ 2) = 0 := by simpa [show 2 ≠ p - 1 by omega] using htr 2 (by omega) (by omega)
  have hexp : eta0 ^ 2 = algebraMap F U (b ^ 2) * (d : U) ^ 2 -
      algebraMap F U (2 * b * epsilon) * (d : U) + algebraMap F U (epsilon ^ 2) := by
    dsimp [eta0]
    simp only [map_pow, map_mul, map_ofNat]
    ring
  have heval : trace F U (eta0 ^ 2) = (p : F) * epsilon ^ 2 := by
    rw [hexp, map_add, map_sub, Algebra.trace_algebraMap, hdegree]
    simp_rw [← Algebra.smul_def, map_smul, smul_eq_mul]
    rw [ht1, ht2]
    simp [nsmul_eq_mul]
  rw [heval]
  apply hPsi.trivial
  have hp0 : (p : F) ∈ lattice F 1 := by
    apply (residueMap_eq_zero_iff F (p : ringOfIntegers F)).1
    change (p : ResidueField F) = 0
    simpa only [hchar] using CharP.cast_eq_zero (ResidueField F) (residueCharacteristic F)
  apply (div_mem_lattice_iff F _ _ (-(t : ℤ)) (-(-((t : ℤ) + 1)))
    (by rw [ord_mul, htwoF, hA, zero_add])).2
  simpa only [neg_neg, neg_add_cancel_left, pow_two, add_zero] using
    mul_mem_lattice F hp0 (mul_mem_lattice F hepsilon hepsilon)

end Boundary

section NoncubicPhase
variable (F E U K : Type*) [Field F] [Field E] [Field U] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F E] [Algebra F U] [Algebra E K] [Algebra U K]
  [ValuativeExtension F E] [ValuativeExtension F U]
  [Module.Finite F E] [Module.Finite F U] [IsGalois F U]

/-- The noncubic rows in the proof of `O:I:main` (paper lines 1656--1673).
Combine the literal common norms and scalar ratio with `O:I:Sdepth`,
retaining the original denominator and both affine corrections. The records
have constructors `normDepths` and `scalarPhase`; the scalar depth is supplied
by `traceDepth`. This is a supporting result, not the primitive-family theorem. -/
theorem ScalarPhaseAt.ratio_pow_four_eq_one_of_trace_mem
    {p t h : ℕ} (hodd : Odd p) (ht : 0 < t) (hh : h ≤ t)
    (hrow : h < t ∨ 3 < p)
    (hdegree : Module.finrank F U = p) (hunr : ramificationIndex F U = 1)
    (hchar : residueCharacteristic F = p)
    {thetaU : ContinuousQuasiChar U} {thetaE : ContinuousQuasiChar E}
    {psiF Psi : ContinuousAddChar F}
    (hPsi : IsAdditiveConductor F Psi (-((t : ℤ) + 1)))
    (c : F) (d : ringOfIntegers U)
    (hd : (d : U) ^ p - (d : U) = algebraMap F U c)
    (hgen : IntermediateField.adjoin F {(d : U)} = ⊤)
    (x : E) (epsilon : F) (hepsilon : epsilon ∈ lattice F 0)
    (hA : h = t → ord F (norm F E x) = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (R : NormDepthsAt F E U K thetaU thetaE Psi p t h c (d : U) x epsilon)
    (P : ScalarPhaseAt F E U K thetaU thetaE psiF Psi p c (d : U) x epsilon)
    (hS : trace F U (norm U K (algebraMap E K x + algebraMap U K (d : U))) -
      trace F E (norm E K (algebraMap E K x + algebraMap U K (d : U))) ∈
        lattice F ((t : ℤ) + 1)) :
    (localConstant U thetaU (tracePullbackAddChar F U psiF) /
      localConstant E thetaE (tracePullbackAddChar F E psiF)) ^ 4 = 1 := by
  let A := norm F E x
  let C := algebraMap E K x + algebraMap U K (d : U)
  let BU := algebraMap F U A + (d : U) ^ p + algebraMap F U epsilon
  let BE := algebraMap F E A - x + algebraMap F E c
  let ZU := norm U K C
  let ZE := norm E K C
  let S := trace F U ZU - trace F E ZE
  obtain ⟨_, _, _, hEtaU, _, RU, RE, hstrict, hlarge, hboundary⟩ := R
  have hcorrections :
      tracePullbackAddChar F U Psi ((ZU - BU) ^ 2 / (2 * BU)) = 1 ∧
      tracePullbackAddChar F E Psi ((ZE - BE) ^ 2 / (2 * BE)) = 1 := by
    by_cases hlt : h < t
    · exact (hstrict hlt).2.2
    · have heq : h = t := by omega
      have hp : 3 < p := hrow.resolve_left hlt
      obtain ⟨hb, hresidue⟩ := hboundary heq
      have hBU : ord U BU = ((-(t : ℤ) : ℤ) : WithTop ℤ) := by
        have he : (t : ℤ) + 1 - ((t + 1 + h : ℕ) : ℤ) = -(t : ℤ) := by
          rw [heq]
          push_cast
          ring
        simpa only [he] using RU.coefficient_order
      have hetaU : ZU - BU ∈ lattice U 0 := by
        have hdepth : (((p : ℤ) - 1) * (t + 1 - h)) / p = 0 := by
          rw [heq]
          have hpZ : (0 : ℤ) < p := by omega
          have hnum : (t : ℤ) + 1 - t = 1 := by ring
          rw [hnum, mul_one]
          exact Int.ediv_eq_zero_of_lt (by omega) (by omega)
        simpa only [hdepth] using hEtaU
      exact ⟨unramifiedBoundaryCorrection F U hodd hp ht hdegree hunr hchar Psi hPsi
        c d hd hgen A (elementarySymmetric F E (p - 1) x) epsilon (ZU - BU)
        (hA heq) hb hepsilon hBU hetaU hresidue, (RE.enhanced (hlarge hp)).2⟩
  obtain ⟨hcU, hcE⟩ := hcorrections
  obtain ⟨⟨g, hg, hratio⟩, _⟩ := P
  have hphase : Psi (-S) = 1 := by
    apply hPsi.trivial
    simpa only [neg_neg] using neg_mem_lattice F hS
  change _ = g * (Psi (-S) : ℂ) *
    (tracePullbackAddChar F U Psi ((ZU - BU) ^ 2 / (2 * BU)) : ℂ) /
    (tracePullbackAddChar F E Psi ((ZE - BE) ^ 2 / (2 * BE)) : ℂ) at hratio
  rw [hratio, hphase, hcU, hcE]
  simpa only [Units.val_one, mul_one, div_one] using hg

end NoncubicPhase

section CommonPower
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

/-- The final reduction in the proof of `O:I:main` (paper lines 1792--1800).
The fourth-power assertion remains an explicit premise of this supporting
lemma; the conductor branches must prove it before the public comparison can
be assembled. The common odd power and both complete lower products follow
from `Characters.oddPower` for the actual primitive compatible pair. -/
theorem comparison_of_ratio_pow_four_eq_one
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
    letI := Fintype.ofFinite (NormCharacter F U)
    letI := Fintype.ofFinite (NormCharacter F E)
    ∀ (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
      (Theta : ContinuousQuasiChar K),
      normQuasiChar U K thetaU = Theta → normQuasiChar E K thetaE = Theta →
      (¬ ∃ chi : ContinuousQuasiChar F, normQuasiChar F K chi = Theta) →
      ∀ (psiF : ContinuousAddChar F), psiF ≠ 1 →
      (localConstant U thetaU (tracePullbackAddChar F U psiF) /
        localConstant E thetaE (tracePullbackAddChar F E psiF)) ^ 4 = 1 →
      localConstant U thetaU (tracePullbackAddChar F U psiF) =
        localConstant E thetaE (tracePullbackAddChar F E psiF) ∧
      (∏ nu : NormCharacter F U, localConstant F nu.1 psiF) = 1 ∧
      (∏ nu : NormCharacter F E, localConstant F nu.1 psiF) = 1 ∧
      localConstant U thetaU (tracePullbackAddChar F U psiF) *
          (∏ nu : NormCharacter F U, localConstant F nu.1 psiF) =
        localConstant E thetaE (tracePullbackAddChar F E psiF) *
          (∏ nu : NormCharacter F E, localConstant F nu.1 psiF) := by
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
  letI := Fintype.ofFinite (NormCharacter F U)
  letI := Fintype.ofFinite (NormCharacter F E)
  intro thetaU thetaE Theta hcompU hcompE hprimitive psiF hpsiF hfour
  obtain ⟨_, _, hprodU, hprodE, hpower⟩ :=
    Characters.oddPower hp hodd hG U E hU hE hne
      thetaU thetaE Theta hcompU hcompE hprimitive psiF hpsiF
  rw [hprodU, hprodE, mul_one, mul_one] at hpower
  have hcoprime : p.Coprime 4 := hodd.coprime_two_right.pow_right 2
  have hratio : localConstant U thetaU (tracePullbackAddChar F U psiF) /
      localConstant E thetaE (tracePullbackAddChar F E psiF) = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.dvd_one.mp
    simpa only [hcoprime.gcd_eq_one] using
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpower) (orderOf_dvd_of_pow_eq_one hfour)
  have hnonzero : localConstant E thetaE (tracePullbackAddChar F E psiF) ≠ 0 :=
    (localConstant_isDeltaFinite E).apply_ne_zero
    (canonicalLocalQuasiCharData E thetaE)
    (canonicalLocalAddCharData E (tracePullbackAddChar F E psiF)
      (Basic.tracePullbackAddChar_ne_one F E psiF hpsiF))
  have heq := (div_eq_one_iff_eq hnonzero).mp hratio
  refine ⟨heq, hprodU, hprodE, ?_⟩
  rw [hprodU, hprodE, mul_one, mul_one, heq]

end CommonPower

section ConductorDispatch
variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  (E U : IntermediateField F K)

local instance comparisonValuativeRelE : ValuativeRel E := Basic.intermediateFieldValuativeRel E
local instance comparisonTopologyE : TopologicalSpace E := Basic.intermediateFieldTopology E
local instance comparisonLocalFieldE : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E
local instance comparisonLowerExtensionE : ValuativeExtension F E := Basic.intermediateField_lowerValuativeExtension E
local instance comparisonUpperExtensionE : ValuativeExtension E K := Basic.intermediateField_upperValuativeExtension E
local instance comparisonValuativeRelU : ValuativeRel U := Basic.intermediateFieldValuativeRel U
local instance comparisonTopologyU : TopologicalSpace U := Basic.intermediateFieldTopology U
local instance comparisonLocalFieldU : IsNonarchimedeanLocalField U := Basic.intermediateField_localField U
local instance comparisonLowerExtensionU : ValuativeExtension F U := Basic.intermediateField_lowerValuativeExtension U
local instance comparisonUpperExtensionU : ValuativeExtension U K := Basic.intermediateField_upperValuativeExtension U

variable {p : ℕ} (hp : p.Prime)
  (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
  (hFE : Module.finrank F E = p) (hFU : Module.finrank F U = p)

include hp hG hFE hFU

/-- Exhaust the low conductors using the literal norm witnesses returned by
`traceDepth` and `cubicIdentity`, with the terminal cubic phase evaluated by
`CubicIdentityAt.ratio_pow_four_eq_one`. -/
private theorem comparison_low_conductor
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
    (localConstant U thetaU (tracePullbackAddChar F U psiF.character) /
      localConstant E thetaE (tracePullbackAddChar F E psiF.character)) ^ 4 = 1 := by
  letI : PrimeCyclicExtension F E :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F E
      (Basic.intermediateField_tower_compatible hp hG E hFE).2.2.2.2.2.2.2.2.2.2.2.1
  letI : PrimeCyclicExtension F U :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F U
      (Basic.intermediateField_tower_compatible hp hG U hFU).2.2.2.2.2.2.2.2.2.2.2.1
  letI : IsGalois F E := PrimeCyclicExtension.instIsGalois F E
  letI : IsGalois F U := PrimeCyclicExtension.instIsGalois F U
  intro ht hres hunr hsup hne hq hqpos tau htaune psiF alpha hPsi htau c d hd hgen
    M thetaU thetaE hcomp hprimitive D hh
  have hc : IsAdditiveConductor F (scaleAddCharData F psiF alpha).character
      (-((t : ℤ) + 1)) := by
    simpa only [hPsi, Nat.cast_add, Nat.cast_one] using
      (scaleAddCharData F psiF alpha).isConductor
  by_cases hrow : D.h < t ∨ 3 < p
  · obtain ⟨x, epsilon, hepsilon, _, _, horder, _, _, R, P, hS⟩ :=
      traceDepth F K E U hp hG hFE hFU hodd htpos hchar ht hres hunr hsup hne hq
        tau htaune psiF alpha hPsi htau c d hd hgen hcomp hprimitive D hh hrow
    exact P.ratio_pow_four_eq_one_of_trace_mem F E U K
      (hp.odd_of_ne_two (by omega)) htpos hh hrow hFU hunr hchar hc (c : F) d hd hgen
      x epsilon hepsilon (fun heq => by simpa only [heq] using (horder (by omega)).2)
      R hS
  · have hp3 : p = 3 := by omega
    subst hp3
    have hboundary : D.h = t := by omega
    obtain ⟨x, epsilon, _, _, _, horder, _, _, _, _, C⟩ :=
      cubicIdentity F K E U hG hFE hFU htpos hchar ht hres hunr hsup hne hq
        tau htaune psiF alpha hPsi htau c d hd hgen hcomp hprimitive D hboundary
    exact C.ratio_pow_four_eq_one F E U K hFE ht htpos hres hchar hq hqpos
      tau htaune (scaleAddCharData F psiF alpha).character
      (by simpa only [Nat.cast_add, Nat.cast_one] using hc) htau
      (by simpa only [hboundary] using (horder (by omega)).1)

end ConductorDispatch

section PublicComparison
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] in
private theorem comparison_fixedField_degree
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p) :
    Module.finrank F (IntermediateField.fixedField H) = p := by
  have htower := Module.finrank_mul_finrank F (IntermediateField.fixedField H) K
  rw [IntermediateField.finrank_fixedField_eq_card H, hH,
    ← IsGalois.card_aut_eq_finrank F K, Nat.card_congr (Classical.choice hG).toEquiv,
    Nat.card_prod] at htower
  have hcard : Nat.card (Multiplicative (ZMod p)) = p :=
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod p)
  rw [hcard] at htower
  exact Nat.mul_right_cancel hp.pos htower

set_option maxHeartbeats 800000 in
/-- **Paper Theorem 6.1 (`O:I:main`).**
For every primitive compatible pair on the unramified and ramified lower
fields of the actual wild odd diamond, the canonical local constants agree.
Both complete lower norm-character products are one, so the complete
normalized induction expressions agree as well. All setup, model, and twist
data are constructed from these inputs, in either field characteristic. -/
theorem comparison
    {p : ℕ} (hp : p.Prime) (hodd : 2 < p)
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hchar : residueCharacteristic F = p)
    (hI : Nat.card (Ramification.inertiaSubgroup (F := F) (K := K)) = p)
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p)
    (hne : H ≠ Ramification.inertiaSubgroup) :
    let U := UnramifiedField F K
    let E := RamifiedField F K H
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
      (Basic.intermediateField_tower_compatible hp hG U
        (comparison_fixedField_degree hp hG _ hI)).2.2.2.2.2.2.2.2.2.2.2.1
    letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E
      (Basic.intermediateField_tower_compatible hp hG E
        (comparison_fixedField_degree hp hG H hH)).2.2.2.2.2.2.2.2.2.2.2.1
    letI := primeCyclicNormCharacter_finite F U
    letI := primeCyclicNormCharacter_finite F E
    letI := Fintype.ofFinite (NormCharacter F U)
    letI := Fintype.ofFinite (NormCharacter F E)
    ∀ (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
      (Theta : ContinuousQuasiChar K),
      normQuasiChar U K thetaU = Theta → normQuasiChar E K thetaE = Theta →
      (¬ ∃ chi : ContinuousQuasiChar F, normQuasiChar F K chi = Theta) →
      ∀ (psiF : ContinuousAddChar F), psiF ≠ 1 →
      localConstant U thetaU (tracePullbackAddChar F U psiF) =
        localConstant E thetaE (tracePullbackAddChar F E psiF) ∧
      (∏ nu : NormCharacter F U, localConstant F nu.1 psiF) = 1 ∧
      (∏ nu : NormCharacter F E, localConstant F nu.1 psiF) = 1 ∧
      localConstant U thetaU (tracePullbackAddChar F U psiF) *
          (∏ nu : NormCharacter F U, localConstant F nu.1 psiF) =
        localConstant E thetaE (tracePullbackAddChar F E psiF) *
          (∏ nu : NormCharacter F E, localConstant F nu.1 psiF) := by
  let U := UnramifiedField F K
  let E := RamifiedField F K H
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
    (Basic.intermediateField_tower_compatible hp hG U
        (comparison_fixedField_degree hp hG _ hI)).2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E
    (Basic.intermediateField_tower_compatible hp hG E
        (comparison_fixedField_degree hp hG H hH)).2.2.2.2.2.2.2.2.2.2.2.1
  letI := primeCyclicNormCharacter_finite F U
  letI := primeCyclicNormCharacter_finite F E
  letI := Fintype.ofFinite (NormCharacter F U)
  letI := Fintype.ofFinite (NormCharacter F E)
  change ∀ (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
    (Theta : ContinuousQuasiChar K), _
  intro thetaU thetaE Theta hcompU hcompE hprimitive psiF hpsiF
  have hU : Module.finrank F U = p := comparison_fixedField_degree hp hG _ hI
  have hE : Module.finrank F E = p := comparison_fixedField_degree hp hG H hH
  have hsep : Ramification.intermediateNormRange U ≠ Ramification.intermediateNormRange E :=
    (Ramification.normSeparation hp hG).unramified_lower hI H hH hne
  have hcomp : normQuasiChar U K thetaU = normQuasiChar E K thetaE :=
    hcompU.trans hcompE.symm
  have hprim : ¬ ∃ chi : ContinuousQuasiChar F,
      normQuasiChar F K chi = normQuasiChar U K thetaU := by
    rintro ⟨chi, hchi⟩
    exact hprimitive ⟨chi, hchi.trans hcompU⟩
  obtain ⟨s⟩ := oddURSetup_exists hp hodd hG hchar hI H hH hne
  obtain ⟨tau, alpha, htaune, _, _, hPsi, htau, M, _, ⟨D⟩⟩ :=
    twist hp hG hI H hH hne hchar s psiF hpsiF thetaU thetaE hcomp hprim
  have hb : residueDegree F E = 1 ∧ ramificationIndex E K = 1 ∧
      PrimeCyclicExtension.IsLowerBreak F E s.t ∧
      PrimeCyclicExtension.IsLowerBreak U K s.t := s.breaks
  have hunr : ramificationIndex F U = 1 :=
    ((Ramification.diamondBreaks hp hG hchar).2 hI).unramified_lower.1
  have hq : s.q0 = (s.t + 1) ⌈/⌉ p := by rw [s.q0_eq, s.T_eq]
  -- Normalize T once, transporting the actual models and their twist together.
  generalize hTeq : s.T = T at M D hPsi
  have hT : T = s.t + 1 := hTeq.symm.trans s.T_eq
  subst hT
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  by_cases hh : D.h ≤ s.t
  · have hEU : E ≠ U := fun heq => hsep (congrArg Ramification.intermediateNormRange heq.symm)
    letI : IsGalois F E := PrimeCyclicExtension.instIsGalois F E
    have hinf : E ⊓ U = ⊥ := by
      have hdiv := IntermediateField.finrank_dvd_of_le_right (show E ⊓ U ≤ E from inf_le_left)
      rw [hE] at hdiv
      rcases (Nat.dvd_prime hp).mp hdiv with hdim | hdim
      · exact IntermediateField.finrank_eq_one_iff.mp hdim
      · have hi : E ⊓ U = E :=
          IntermediateField.eq_of_le_of_finrank_eq inf_le_left (hdim.trans hE.symm)
        have hle : E ≤ U := by rw [← hi]; exact inf_le_right
        exact (hEU (IntermediateField.eq_of_le_of_finrank_eq hle (hE.trans hU.symm))).elim
    have hdisjoint : E.LinearDisjoint U := IntermediateField.LinearDisjoint.of_inf_eq_bot hinf
    have hsup : E ⊔ U = ⊤ := by
      apply IntermediateField.eq_of_le_of_finrank_eq le_top
      rw [hdisjoint.finrank_sup, IntermediateField.finrank_top', hE, hU]
      exact (Basic.intermediateField_tower_compatible hp hG U hU).2.2.2.2.2.2.2.2.1.symm
    have hfour := comparison_low_conductor F K E U hp hG hE hU hodd s.t_pos hchar
      hb.2.2.1 hb.1 hunr hsup hsep hq tau htaune
      (canonicalLocalAddCharData F psiF hpsiF) alpha hPsi htau s.c s.d
      s.artinSchreier.2.2.1 s.artinSchreier.2.2.2 hcomp hprim D hh
    exact comparison_of_ratio_pow_four_eq_one hp hpodd hG U E hU hE hsep
      thetaU thetaE Theta hcompU hcompE hprimitive psiF hpsiF hfour
  · obtain ⟨heq, hprodU, hprodE⟩ := oddUR_stable_comparison hp hpodd hG U E hU hE hsep
      s.t_pos s.q0_pos hb.2.2.1 hb.1 hunr tau.1
      (scaleAddCharData F (canonicalLocalAddCharData F psiF hpsiF) alpha).character
      (s.c : F) (s.d : U) M thetaU thetaE D (by omega) psiF hpsiF
    change (∏ nu : NormCharacter F U, localConstant F nu.1 psiF) = 1 at hprodU
    change (∏ nu : NormCharacter F E, localConstant F nu.1 psiF) = 1 at hprodE
    refine ⟨heq, hprodU, hprodE, ?_⟩
    rw [hprodU, hprodE, mul_one, mul_one, heq]

end PublicComparison

end
end LanglandsSecondMainLemma.Odd.UR
