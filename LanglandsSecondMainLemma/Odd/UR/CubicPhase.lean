import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.UR.CubicIdentity
import LanglandsSecondMainLemma.Odd.NormPhase

/-!
# Odd / UR / Cubic Phase

Paper Lemma 6.13 (`O:I:cubicidentity`), the phase assertion after
`O:I:Lambdaexact`, source lines 1731–1749. The setup is in lines
1060–1128, 1204–1248, and 1408–1430.

The two nonintegral groups are evaluated using the actual norm character
on its full logarithm chart. Their arguments upstairs are the base trace
`a` and the literal quotient `b/x`; both lie in the proved domain of
`normPhase`. Only the last rational summand is put in the character's
triviality ideal. No ideal membership is inferred from a character value.
-/

namespace LanglandsSecondMainLemma.Odd.UR

noncomputable section

open LanglandsFirstMainLemma

section Algebra
variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra F E] [Module.Finite F E] [IsGalois F E]

/-- The reciprocal trace used in the second genuine norm-phase application.
The characteristic-polynomial argument also covers elements in the base field. -/
theorem cubic_reciprocal_trace (hdegree : Module.finrank F E = 3)
    (x : E) (hA : norm F E x ≠ 0) :
    trace F E (algebraMap F E (elementarySymmetric F E 2 x) / x) =
      elementarySymmetric F E 2 x ^ 2 / norm F E x := by
  let a := trace F E x
  let b := elementarySymmetric F E 2 x
  let A := norm F E x
  have hx : x ≠ 0 := by
    intro hx
    simp [hx] at hA
  have hpoly := cubic_displacement F E hdegree x
  have hrecip : algebraMap F E A / x =
      x ^ 2 - algebraMap F E a * x + algebraMap F E b := by
    apply (div_eq_iff hx).2
    dsimp [a, b, A]
    linear_combination -hpoly
  have htrace := congrArg (trace F E) hrecip
  simp only [div_eq_mul_inv, map_add, map_sub, ← Algebra.smul_def,
    map_smul, smul_eq_mul, trace_algebraMap, hdegree, nsmul_eq_mul] at htrace
  rw [(cubic_powerTraces F E hdegree x).1] at htrace
  have hinv : trace F E x⁻¹ = b / A := by
    apply (eq_div_iff hA).2
    dsimp [a, b] at htrace ⊢
    linear_combination htrace
  change trace F E (algebraMap F E b / x) = b ^ 2 / A
  rw [div_eq_mul_inv, ← Algebra.smul_def, map_smul, smul_eq_mul, hinv]
  ring

end Algebra

section NormCharacter
variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]
local instance : IsGalois F E := PrimeCyclicExtension.instIsGalois F E

/-- Both norm-character cancellations, with the two domain bounds proved
from `O:I:cubicbounds`. The reciprocal argument is the actual element `b/x`. -/
theorem cubic_normPhases
    (hdegree : Module.finrank F E = 3)
    {t q : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
    (hres : residueDegree F E = 1) (hchar : residueCharacteristic F = 3)
    (hq : q = (t + 1) ⌈/⌉ 3) (hqpos : 0 < q)
    (tau : NormCharacter F E) (htaune : tau ≠ 1)
    (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (hchart : ∀ z : lattice F (q : ℤ),
      tau.1 (positiveUnitOfLattice F hqpos (-z)) = Psi (truncatedLog 3 (z : F)))
    (x : E) (hx : ord E x = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (ha : trace F E x ∈ lattice F (((t : ℤ) + 2) / 3))
    (hb : elementarySymmetric F E 2 x ∈ lattice F 0) :
    Psi (3 * trace F E x + trace F E x ^ 3) = 1 ∧
      Psi ((elementarySymmetric F E 2 x ^ 2 + elementarySymmetric F E 2 x ^ 3) /
        norm F E x) = 1 := by
  have hram : ramificationIndex F E = 3 := by
    have he := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa only [hdegree, hres, mul_one] using he.symm
  have hqt : q ≤ t := by
    rw [hq, ceilDiv_le_iff_le_mul (by decide : 0 < 3)]
    omega
  have hmapa : algebraMap F E (trace F E x) ∈ lattice E (q : ℤ) := by
    rw [mem_lattice, ord_algebraMap, hram]
    have hbound := nsmul_le_nsmul_right ((mem_lattice F).1 ha) 3
    apply le_trans _ hbound
    rw [← WithTop.coe_nsmul, WithTop.coe_le_coe, nsmul_eq_mul]
    omega
  have hmapb : algebraMap F E (elementarySymmetric F E 2 x) ∈ lattice E 0 := by
    rw [mem_lattice, ord_algebraMap, hram]
    simpa using nsmul_le_nsmul_right ((mem_lattice F).1 hb) 3
  have hquot : algebraMap F E (elementarySymmetric F E 2 x) / x ∈
      lattice E (q : ℤ) := by
    apply (div_mem_lattice_iff E x _ (-(t : ℤ)) (q : ℤ) hx).2
    exact lattice_antitone E (by omega) hmapb
  have hconvert (w : E) (hw : w ∈ lattice E (q : ℤ)) :
      Psi (trace F E w + norm F E w) = 1 := by
    exact (normPhase F E ht htpos hres (by simpa only [hdegree] using hchar)
      (by omega) q (by simpa only [hdegree] using hq) hqpos tau htaune Psi hPsi
      (by simpa only [hdegree] using hchart) w hw).1
  constructor
  · simpa only [trace_algebraMap, LanglandsFirstMainLemma.norm_algebraMap, hdegree, nsmul_eq_mul,
      Nat.cast_ofNat] using hconvert _ hmapa
  · have hA : norm F E x ≠ 0 := by
      apply (ord_ne_top_iff F).1
      rw [ord_norm, hres, one_nsmul, hx]
      exact WithTop.coe_ne_top
    have h := hconvert _ hquot
    rw [cubic_reciprocal_trace F E hdegree x hA] at h
    simp only [div_eq_mul_inv, map_mul, LanglandsFirstMainLemma.norm_algebraMap,
      hdegree, Algebra.norm_inv] at h
    simpa only [div_eq_mul_inv, add_mul] using h

/-- The final summand of `O:I:Lambdaexact` lies in the whole triviality ideal.
This estimate uses only integral depths, including the negative order of `A`. -/
theorem cubic_lastSummand_mem_lattice
    {t : ℕ} (htpos : 0 < t) (hchar : residueCharacteristic F = 3)
    (a b A : F) (ha : a ∈ lattice F (((t : ℤ) + 2) / 3))
    (hb : b ∈ lattice F 0)
    (hA : ord F A = ((-(t : ℤ) : ℤ) : WithTop ℤ)) :
    a ^ 2 * (a ^ 2 - 3 * b) ^ 2 / (2 * A) ∈ lattice F ((t : ℤ) + 1) := by
  have ha1 : a ∈ lattice F 1 := lattice_antitone F (by omega) ha
  have ha2 : a ^ 2 ∈ lattice F 2 := by
    simpa only [pow_two, Int.reduceAdd] using mul_mem_lattice F ha1 ha1
  have h31 : (3 : F) ∈ lattice F 1 := by
    apply (residueMap_eq_zero_iff F (3 : ringOfIntegers F)).1
    change (3 : ResidueField F) = 0
    simpa only [hchar, Nat.cast_ofNat] using
      CharP.cast_eq_zero (ResidueField F) (residueCharacteristic F)
  have hdiff : a ^ 2 - 3 * b ∈ lattice F 1 :=
    sub_mem_lattice F (lattice_antitone F (by omega) ha2)
      (by simpa only [add_zero] using mul_mem_lattice F h31 hb)
  have hnum : a ^ 2 * (a ^ 2 - 3 * b) ^ 2 ∈ lattice F 4 := by
    simpa only [pow_two, Int.reduceAdd] using
      mul_mem_lattice F ha2 (mul_mem_lattice F hdiff hdiff)
  have htwo : ord F (2 : F) = 0 :=
    ord_natCast_eq_zero_of_lt_residueCharacteristic F (j := 2) (by decide) (by omega)
  apply (div_mem_lattice_iff F _ _ (-(t : ℤ)) ((t : ℤ) + 1)
    (by rw [ord_mul, htwo, hA, zero_add])).2
  exact lattice_antitone F (by omega) hnum

/-- Cancellation of the exact completed cubic expression. The two phase
identities come from `normPhase`; the last term comes from ideal triviality. -/
theorem cubic_completedPhase_eq_one
    (hdegree : Module.finrank F E = 3)
    {t q : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
    (hres : residueDegree F E = 1) (hchar : residueCharacteristic F = 3)
    (hq : q = (t + 1) ⌈/⌉ 3) (hqpos : 0 < q)
    (tau : NormCharacter F E) (htaune : tau ≠ 1)
    (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (hchart : ∀ z : lattice F (q : ℤ),
      tau.1 (positiveUnitOfLattice F hqpos (-z)) = Psi (truncatedLog 3 (z : F)))
    (x : E) (hx : ord E x = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (ha : trace F E x ∈ lattice F (((t : ℤ) + 2) / 3))
    (hb : elementarySymmetric F E 2 x ∈ lattice F 0) :
    let a := trace F E x
    let b := elementarySymmetric F E 2 x
    let A := norm F E x
    Psi (3 * a + a ^ 3 - (b ^ 2 + b ^ 3) / A +
      a ^ 2 * (a ^ 2 - 3 * b) ^ 2 / (2 * A)) = 1 := by
  obtain ⟨hfirst, hsecond⟩ := cubic_normPhases F E hdegree ht htpos hres hchar
    hq hqpos tau htaune Psi hPsi hchart x hx ha hb
  have hA : ord F (norm F E x) = ((-(t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_norm, hres, one_nsmul, hx]
  have hkernel : AddCharTrivialOnLattice F Psi ((t : ℤ) + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one, neg_neg] using hPsi.trivial
  have hlast := hkernel _ (cubic_lastSummand_mem_lattice F htpos hchar
    (trace F E x) (elementarySymmetric F E 2 x) (norm F E x) ha hb hA)
  dsimp
  rw [Psi.map_add_eq_mul, hlast]
  change Psi.toAddChar _ * 1 = 1
  rw [Psi.toAddChar.map_sub_eq_div]
  change Psi _ / Psi _ * 1 = 1
  rw [hfirst, hsecond]
  simp

/-- **Paper Lemma 6.13, phase assertion (`O:I:cubicidentity`).**

For an actual totally ramified cubic edge with positive lower break `t`,
let `x` have order `-t`, and let `Psi` realize the actual nontrivial norm
character on its prescribed logarithm chart. The exact cubic phase is one.
The trace and symmetric-coefficient bounds are derived from FML's ramification
estimates. Both field characteristics and every positive break are retained. -/
theorem oddUR_cubicPhase_eq_one
    (hdegree : Module.finrank F E = 3)
    {t q : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
    (hres : residueDegree F E = 1) (hchar : residueCharacteristic F = 3)
    (hq : q = (t + 1) ⌈/⌉ 3) (hqpos : 0 < q)
    (tau : NormCharacter F E) (htaune : tau ≠ 1)
    (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (hchart : ∀ z : lattice F (q : ℤ),
      tau.1 (positiveUnitOfLattice F hqpos (-z)) = Psi (truncatedLog 3 (z : F)))
    (x : E) (hx : ord E x = ((-(t : ℤ) : ℤ) : WithTop ℤ)) :
    let a := trace F E x
    let b := elementarySymmetric F E 2 x
    let A := norm F E x
    let eta := x ^ 3 - algebraMap F E A
    let S := 3 * A - trace F E (x ^ 3) + 3 * a
    Psi (S - b ^ 2 / A + trace F E (eta ^ 2) / (2 * A)) = 1 := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have htrace := traceIdealLowerBound_of_integralGenerator F E ht hres pi hpi hgen
  have ha : trace F E x ∈ lattice F (((t : ℤ) + 2) / 3) := by
    have h := htrace (-(t : ℤ)) x (by rw [hx])
    rw [hdegree] at h
    norm_num only [Nat.reduceSub, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_one] at h
    rw [mem_lattice]
    convert h using 1
    congr 2
    ring
  have hram : ramificationIndex F E = Module.finrank F E := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa only [hres, mul_one] using h.symm
  have hsym := (wild_symmetric_bound F E t ht htpos
    (by simpa only [hdegree] using hchar) hram htrace (-(t : ℤ))
    (by rw [hx])).1 (j := 2) (by decide) (by omega)
  have hb : elementarySymmetric F E 2 x ∈ lattice F 0 := by
    rw [mem_lattice]
    rw [hdegree, wildDifferentContribution] at hsym
    norm_num only [Nat.reduceSub, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_one] at hsym
    convert hsym using 1
    congr 1
    omega
  have htwoord : ord F (2 : F) = 0 :=
    ord_natCast_eq_zero_of_lt_residueCharacteristic F (j := 2) (by decide) (by omega)
  have htwo : (2 : F) ≠ 0 := (ord_ne_top_iff F).1 (htwoord ▸ (by simp))
  have hA : norm F E x ≠ 0 := by
    apply (ord_ne_top_iff F).1
    rw [ord_norm, hres, one_nsmul, hx]
    exact WithTop.coe_ne_top
  dsimp
  rw [cubic_completion F E hdegree htwo x hA]
  exact cubic_completedPhase_eq_one F E hdegree ht htpos hres hchar hq hqpos
    tau htaune Psi hPsi hchart x hx ha hb

end NormCharacter

section ActualNorms
variable (F E U K : Type*) [Field F] [Field E] [Field U] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F E] [Algebra F U] [Algebra E K] [Algebra U K]
  [ValuativeExtension F E] [ValuativeExtension F U]
  [Module.Finite F E] [Module.Finite F U] [PrimeCyclicExtension F E]
local instance : IsGalois F E := PrimeCyclicExtension.instIsGalois F E

variable (hdegree : Module.finrank F E = 3)
  {t q : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
  (hres : residueDegree F E = 1) (hchar : residueCharacteristic F = 3)
  (hq : q = (t + 1) ⌈/⌉ 3) (hqpos : 0 < q)
  (tau : NormCharacter F E) (htaune : tau ≠ 1)
  (Psi : ContinuousAddChar F)
  (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
  (hchart : ∀ z : lattice F (q : ℤ),
    tau.1 (positiveUnitOfLattice F hqpos (-z)) = Psi (truncatedLog 3 (z : F)))
  {thetaU : ContinuousQuasiChar U} {thetaE : ContinuousQuasiChar E}
  {psiF : ContinuousAddChar F} {c epsilon : F} {d : U} {x : E}
  (hx : ord E x = ((-(t : ℤ) : ℤ) : WithTop ℤ))

include hdegree ht htpos hres hchar hq hqpos tau htaune hPsi hchart hx

/-- Apply the cancellation to the literal stationary numerator supplied by
`cubicIdentity`. This keeps its original common norm witness and affine error;
`CubicIdentityAt` has its proved constructor in the prerequisite. -/
theorem CubicIdentityAt.phase_eq_one
    (R : CubicIdentityAt F E U K thetaU thetaE psiF Psi t c d x epsilon) :
    let C := algebraMap E K x + algebraMap U K d
    let A := norm F E x
    let b := elementarySymmetric F E 2 x
    let etaE := norm E K C - (algebraMap F E A - x + algebraMap F E c)
    let S := trace F U (norm U K C) - trace F E (norm E K C)
    Psi (S - b ^ 2 / A + trace F E (etaE ^ 2) / (2 * A)) = 1 := by
  obtain ⟨ha, hb, _, _, _, hLambda, _⟩ := R
  dsimp only
  rw [hLambda]
  exact cubic_completedPhase_eq_one F E hdegree ht htpos hres hchar hq hqpos
    tau htaune Psi hPsi hchart x hx ha hb

/-- The cubic boundary ratio belongs to `μ₄`, after both affine corrections
and the genuine norm-character cancellations. The constants are FML's canonical
ones, with the original continuous quasi-characters and trace characters. -/
theorem CubicIdentityAt.ratio_pow_four_eq_one
    (R : CubicIdentityAt F E U K thetaU thetaE psiF Psi t c d x epsilon) :
    (LanglandsFirstMainLemma.localConstant U thetaU (tracePullbackAddChar F U psiF) /
      LanglandsFirstMainLemma.localConstant E thetaE (tracePullbackAddChar F E psiF)) ^ 4 = 1 := by
  have hphase := R.phase_eq_one F E U K hdegree ht htpos hres hchar hq hqpos
    tau htaune Psi hPsi hchart hx
  obtain ⟨_, _, _, _, _, _, g, hg, hratio⟩ := R
  rw [hratio]
  have hneg : ∀ z : F, Psi z = 1 → Psi (-z) = 1 := by
    intro z hz
    have h : Psi (-z) * Psi z = 1 := by
      rw [← Psi.map_add_eq_mul]
      simp
    simpa only [hz, mul_one] using h
  rw [hneg _ hphase]
  simpa only [Units.val_one, mul_one] using hg

end ActualNorms

end

end LanglandsSecondMainLemma.Odd.UR
