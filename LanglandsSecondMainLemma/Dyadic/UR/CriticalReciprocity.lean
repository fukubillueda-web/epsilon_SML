import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Dyadic.UR.OddConductor

/-!
# Dyadic / UR / Critical Reciprocity

Blueprint: `blueprint/tasks/Dyadic/UR/CriticalReciprocity.md`.
Paper: Lemma `D:UR:resreciprocity` and equations
`D:UR:taureciprocity`, `D:UR:Htaucritical`.

For an odd ramified quadratic conductor, write `t + 1 = 2e + 1`.
The norm character has a second reciprocity formula at the shallower
critical depth `e`:

`tau (1 + N(w)) = PsiE(w)` for `w in p_E^e`.

This is not an invocation of `normPhase`, whose input starts only at depth
`e + 1`.  Instead, the proof factors the exact norm of `1 + w`.  Its trace
quotient is deep enough for the given chart, and the resulting upper-field
argument differs from `w` by an element of `p_E^(2e+1)`.
-/

namespace LanglandsSecondMainLemma.Dyadic.UR

noncomputable section

open LanglandsFirstMainLemma

/-- In degree two, the exact norm of `1 + z` is
`1 + Tr(z) + N(z)`. -/
private theorem quadraticNormOneAdd
    (F E : Type*)
    [Field F] [Field E] [Algebra F E]
    [Module.Free F E] [Module.Finite F E]
    (hdegree : Module.finrank F E = 2) (z : E) :
    norm F E (1 + z) = 1 + trace F E z + norm F E z := by
  have h := norm_one_add_eq_one_add_sum_elementarySymmetric F E z
  rw [hdegree] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h
  rw [elementarySymmetric_one] at h
  have hfin : elementarySymmetric F E 2 z = norm F E z := by
    rw [← hdegree]
    exact elementarySymmetric_finrank F E z
  rw [hfin] at h
  simpa only [add_assoc] using h

/-- At residue degree one the field norm carries an element of
`p_E^e` canonically to an element of `p_F^e`.

This constructor keeps the ideal membership used by the critical residual
function in the type; no norm-surjectivity assertion is involved. -/
noncomputable def criticalNormLattice
    (F E : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Finite F E]
    (hres : residueDegree F E = 1)
    {e : ℕ} (w : lattice E (e : ℤ)) : lattice F (e : ℤ) :=
  ⟨norm F E (w : E), by
    rw [mem_lattice, ord_norm, hres, one_nsmul]
    exact w.property⟩

/-- The literal principal unit `1 + N(w)` at critical depth. -/
noncomputable def criticalNormUnit
    (F E : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Finite F E]
    (hres : residueDegree F E = 1)
    {e : ℕ} (he : 0 < e) (w : lattice E (e : ℤ)) :
    unitFiltration F e :=
  positiveUnitOfLattice F he (criticalNormLattice F E hres w)

@[simp]
theorem criticalNormUnit_coe
    (F E : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Finite F E]
    (hres : residueDegree F E = 1)
    {e : ℕ} (he : 0 < e) (w : lattice E (e : ℤ)) :
    (((criticalNormUnit F E hres he w : unitFiltration F e) : Fˣ) : F) =
      1 + norm F E (w : E) := by
  simp only [criticalNormUnit, coe_positiveUnitOfLattice,
    criticalNormLattice]

/-- The paper's actual norm-character residual function
`H_tau(z) = PsiF(-z) tau(1+z)^(-1)` at the critical depth. -/
noncomputable def criticalNormResidual
    (F : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (tau : ContinuousQuasiChar F) (PsiF : ContinuousAddChar F)
    {e : ℕ} (he : 0 < e) (z : lattice F (e : ℤ)) : ℂˣ :=
  PsiF (-(z : F)) *
    (tau (positiveUnitOfLattice F he z : Fˣ))⁻¹

open private additiveConductor_of_chart from
  LanglandsSecondMainLemma.Dyadic.UR.OddConductor

section CriticalReciprocityProof

variable (F E : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E]
  [Module.Finite F E]

/-- The denominator `1 + N(w)` is a valuation unit at positive critical depth. -/
private theorem criticalNormUnit_ord
    (hres : residueDegree F E = 1) {e : ℕ} (he : 0 < e)
    (w : lattice E (e : ℤ)) :
    ord F ((criticalNormUnit F E hres he w : Fˣ) : F) = 0 :=
  (mem_unitGroup_iff_ord_eq_zero F _).1
    (unitFiltration_le_unitGroup F e (criticalNormUnit F E hres he w).property)

variable [Module.Free F E]

/-- FML's trace-ideal bound specialized to a ramified quadratic edge. -/
private theorem quadraticTrace_mem_lattice
    [PrimeCyclicExtension F E]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hdegree : Module.finrank F E = 2)
    (pi : ringOfIntegers E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers E)) = ⊤)
    {a : ℤ} {x : E} (hx : x ∈ lattice E a) :
    trace F E x ∈ lattice F ((a + (t + 1 : ℕ)) / 2) := by
  have hram : ramificationIndex F E = 2 := by
    simpa only [hdegree, hres, mul_one] using
      (finrank_eq_ramificationIndex_mul_residueDegree F E).symm
  have htrace := trace_mem_lattice_floor F E pi hpi hgen a hx
  simpa only [cyclicPrime_differentExponent_eq F E ht hres pi hpi hgen,
    hdegree, hram, Nat.reduceSub, one_mul, Nat.cast_ofNat] using htrace

/-- The chart and norm-character conductor give the whole conductor lattice
in the kernel of the actual trace pullback. -/
private theorem criticalChart_tracePullback_trivial
    [PrimeCyclicExtension F E]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
    (hres : residueDegree F E = 1) (hdegree : Module.finrank F E = 2)
    (pi : ringOfIntegers E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers E)) = ⊤)
    (tau : NormCharacter F E) (htau : tau ≠ 1)
    (PsiF : ContinuousAddChar F)
    (hchart : ∀ (x : F)
      (hx : x ∈ lattice F (((t / 2 + 1 : ℕ) : ℤ))),
      tau.1 (principalUnitOf F (t / 2) (-x)
        (neg_mem_lattice F hx)) = PsiF x) :
    AddCharTrivialOnLattice E (tracePullbackAddChar F E PsiF) (t + 1 : ℕ) := by
  have hconductor := additiveConductor_of_chart F htpos tau.1 PsiF
    (ramifiedNormCharacter_conductor F E ht hres pi hpi hgen tau htau) hchart
  have htrivial : AddCharTrivialOnLattice F PsiF (t + 1 : ℕ) := by
    simpa only [neg_neg] using hconductor.trivial
  intro x hx
  rw [tracePullbackAddChar_apply]
  apply htrivial
  have htrace := quadraticTrace_mem_lattice F E ht hres hdegree pi hpi hgen hx
  have hdepth : (((t + 1 : ℕ) : ℤ) + ((t + 1 : ℕ) : ℤ)) / 2 =
      ((t + 1 : ℕ) : ℤ) := by omega
  simpa only [hdepth] using htrace

/-- Only the trace quotient is passed to the chart: it lies at depth `e + 1`. -/
private theorem criticalTraceQuotient_mem_lattice
    [PrimeCyclicExtension F E]
    {t e : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hdegree : Module.finrank F E = 2)
    (pi : ringOfIntegers E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers E)) = ⊤)
    (he : 0 < e) (hT : t + 1 = 2 * e + 1) (w : lattice E (e : ℤ)) :
    trace F E (w : E) / ((criticalNormUnit F E hres he w : Fˣ) : F) ∈
      lattice F ((e + 1 : ℕ) : ℤ) := by
  apply (div_mem_lattice_iff F _ _ 0 ((e + 1 : ℕ) : ℤ)
    (criticalNormUnit_ord F E hres he w)).2
  rw [zero_add]
  exact lattice_antitone F (by omega)
    (quadraticTrace_mem_lattice F E ht hres hdegree pi hpi hgen w.property)

/-- Evaluating the exact factorization of `N(1 + w)` by the norm character
identifies `tau(1 + N(w))` with the phase of the trace quotient. -/
private theorem normCharacter_criticalNormUnit_eq_traceQuotient
    (hres : residueDegree F E = 1) (hdegree : Module.finrank F E = 2)
    {t e : ℕ} (he : 0 < e) (hq : t / 2 + 1 = e + 1)
    (tau : NormCharacter F E) (PsiF : ContinuousAddChar F)
    (hchart : ∀ (x : F)
      (hx : x ∈ lattice F (((t / 2 + 1 : ℕ) : ℤ))),
      tau.1 (principalUnitOf F (t / 2) (-x)
        (neg_mem_lattice F hx)) = PsiF x)
    (w : lattice E (e : ℤ))
    (hr : trace F E (w : E) / ((criticalNormUnit F E hres he w : Fˣ) : F) ∈
      lattice F ((e + 1 : ℕ) : ℤ)) :
    tau.1 (criticalNormUnit F E hres he w : Fˣ) =
      PsiF (trace F E (w : E) / ((criticalNormUnit F E hres he w : Fˣ) : F)) := by
  let uN : Fˣ := (criticalNormUnit F E hres he w : Fˣ)
  let uW : Eˣ := (positiveUnitOfLattice E he w : Eˣ)
  let r : F := trace F E (w : E) / (uN : F)
  let rLat : lattice F ((e + 1 : ℕ) : ℤ) := ⟨r, hr⟩
  let uR : Fˣ := (positiveUnitOfLattice F (by omega : 0 < e + 1) rLat : Fˣ)
  have hnormUnits : normUnits F E uW = uN * uR := by
    apply Units.ext
    simp only [coe_normUnits, uW, coe_positiveUnitOfLattice,
      Units.val_mul, uR, rLat, r]
    rw [quadraticNormOneAdd F E hdegree]
    field_simp [Units.ne_zero uN]
    rw [show (uN : F) = 1 + norm F E (w : E) from
      criticalNormUnit_coe F E hres he w]
    ring
  have hrq : r ∈ lattice F (((t / 2 + 1 : ℕ) : ℤ)) := by
    simpa only [hq] using hr
  have huRChart :
      uR = principalUnitOf F (t / 2) (-(-r))
        (neg_mem_lattice F (neg_mem_lattice F hrq)) := by
    apply Units.ext
    simp only [uR, coe_positiveUnitOfLattice, rLat, coe_principalUnitOf, neg_neg]
  have htauR : tau.1 uR = PsiF (-r) := by
    rw [huRChart]
    exact hchart (-r) (neg_mem_lattice F hrq)
  have htauNorm := tau.eq_one_on_normRange F E (normUnits F E uW) ⟨uW, rfl⟩
  have hnegPhase : PsiF (-r) = (PsiF r)⁻¹ := PsiF.toAddChar.map_neg_eq_inv r
  rw [hnormUnits, map_mul, htauR, hnegPhase] at htauNorm
  change tau.1 uN = PsiF r
  apply div_eq_one.mp
  simpa only [div_eq_mul_inv] using htauNorm

omit [Module.Free F E] in
/-- Removing the norm denominator changes the upper argument only in `p_E^(3e)`. -/
private theorem criticalNormQuotient_sub_mem_lattice
    (hres : residueDegree F E = 1) (hdegree : Module.finrank F E = 2)
    {e : ℕ} (he : 0 < e) (w : lattice E (e : ℤ)) :
    (w : E) / algebraMap F E ((criticalNormUnit F E hres he w : Fˣ) : F) -
        (w : E) ∈ lattice E ((3 * e : ℕ) : ℤ) := by
  let uN : Fˣ := (criticalNormUnit F E hres he w : Fˣ)
  have hram : ramificationIndex F E = 2 := by
    simpa only [hdegree, hres, mul_one] using
      (finrank_eq_ramificationIndex_mul_residueDegree F E).symm
  have hnMap : algebraMap F E (norm F E (w : E)) ∈
      lattice E ((2 * e : ℕ) : ℤ) := by
    rw [mem_lattice, ord_algebraMap, hram]
    have hn := (criticalNormLattice F E hres w).property
    change norm F E (w : E) ∈ lattice F (e : ℤ) at hn
    rw [mem_lattice] at hn
    have hcast : ((((2 * e : ℕ) : ℤ)) : WithTop ℤ) =
        (((e : ℤ)) : WithTop ℤ) + (((e : ℤ)) : WithTop ℤ) := by
      norm_cast
      omega
    rw [hcast, two_nsmul]
    exact add_le_add hn hn
  have hproduct : (w : E) * algebraMap F E (norm F E (w : E)) ∈
      lattice E ((3 * e : ℕ) : ℤ) := by
    convert mul_mem_lattice E w.property hnMap using 1
    norm_num
    ring
  have huNMapOrd : ord E (algebraMap F E (uN : F)) = 0 := by
    rw [ord_algebraMap, hram, criticalNormUnit_ord F E hres he w, nsmul_zero]
  have hquotient :
      ((w : E) * algebraMap F E (norm F E (w : E))) /
          algebraMap F E (uN : F) ∈ lattice E ((3 * e : ℕ) : ℤ) := by
    apply (div_mem_lattice_iff E _ _ 0 ((3 * e : ℕ) : ℤ) huNMapOrd).2
    simpa only [zero_add] using hproduct
  have hdiffFormula :
      (w : E) / algebraMap F E (uN : F) - (w : E) =
        -(((w : E) * algebraMap F E (norm F E (w : E))) /
          algebraMap F E (uN : F)) := by
    field_simp [(map_ne_zero (algebraMap F E)).2 (Units.ne_zero uN)]
    rw [show (uN : F) = 1 + norm F E (w : E) from
      criticalNormUnit_coe F E hres he w, map_add, map_one]
    ring
  rw [hdiffFormula]
  exact neg_mem_lattice E hquotient

omit [Module.Free F E] in
/-- Trace linearity and `3e ≥ 2e + 1` remove the denominator from the phase,
including the endpoint `e = 1`. -/
private theorem criticalTraceQuotient_phase
    (hres : residueDegree F E = 1) (hdegree : Module.finrank F E = 2)
    {t e : ℕ} (he : 0 < e) (hT : t + 1 = 2 * e + 1)
    (PsiF : ContinuousAddChar F)
    (htrivial : AddCharTrivialOnLattice E (tracePullbackAddChar F E PsiF) (t + 1 : ℕ))
    (w : lattice E (e : ℤ)) :
    PsiF (trace F E (w : E) / ((criticalNormUnit F E hres he w : Fˣ) : F)) =
      tracePullbackAddChar F E PsiF (w : E) := by
  let uN : Fˣ := (criticalNormUnit F E hres he w : Fˣ)
  let x : E := (w : E) / algebraMap F E (uN : F)
  have htraceX : trace F E x = trace F E (w : E) / (uN : F) := by
    have hs := (Algebra.trace F E).map_smul ((uN : F)⁻¹) (w : E)
    simpa [x, Algebra.smul_def, div_eq_mul_inv, mul_comm] using hs
  have hdiff : x - (w : E) ∈ lattice E (t + 1 : ℕ) :=
    lattice_antitone E (by omega)
      (criticalNormQuotient_sub_mem_lattice F E hres hdegree he w)
  have hphaseDiff := htrivial (x - (w : E)) hdiff
  calc
    PsiF (trace F E (w : E) / (uN : F)) =
        tracePullbackAddChar F E PsiF x := by
      rw [tracePullbackAddChar_apply, htraceX]
    _ = tracePullbackAddChar F E PsiF (w : E) := by
      apply div_eq_one.mp
      change (tracePullbackAddChar F E PsiF).toAddChar x /
        (tracePullbackAddChar F E PsiF).toAddChar (w : E) = 1
      rw [← AddChar.map_sub_eq_div]
      exact hphaseDiff

end CriticalReciprocityProof

/-- Inverting the actual residual function separates its two character factors. -/
private theorem criticalNormResidual_inv
    (F : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (tau : ContinuousQuasiChar F) (PsiF : ContinuousAddChar F)
    {e : ℕ} (he : 0 < e) (z : lattice F (e : ℤ)) :
    (criticalNormResidual F tau PsiF he z)⁻¹ =
      tau (positiveUnitOfLattice F he z : Fˣ) * PsiF (z : F) := by
  have hneg : PsiF (-(z : F)) = (PsiF (z : F))⁻¹ := PsiF.toAddChar.map_neg_eq_inv _
  simp only [criticalNormResidual, hneg, mul_inv_rev, inv_inv]

/-- **Critical quadratic norm reciprocity** (paper Lemma
`D:UR:resreciprocity`).

Let `E/F` be the ramified quadratic edge of positive lower break `t`, and
suppose `T = t + 1` is odd.  The exponent `e = ord_F(2)` and the identity
`T = 2e + 1` are obtained from `oddConductor`; they are not additional
hypotheses.  For every `w in p_E^e`, the two conclusions are exactly

* `tau(1 + N(w)) = PsiE(w)`, and
* `H_tau(N(w))^(-1) = PsiE(w) PsiF(N(w))`.

Here `PsiE` is the actual trace pullback and `H_tau` is
`criticalNormResidual`.  Only the deeper trace quotient is passed to the
chart at depth `e+1`; in particular this proof does not extend
`normPhase` below its stated domain. -/
theorem criticalReciprocity
    (F E : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Free F E] [Module.Finite F E]
    [PrimeCyclicExtension F E]
    (hchar : residueCharacteristic F = 2)
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (htpos : 0 < t) (hres : residueDegree F E = 1)
    (hdegree : Module.finrank F E = 2)
    (pi : ringOfIntegers E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers E)) = ⊤)
    (tau : NormCharacter F E) (htau : tau ≠ 1)
    (PsiF : ContinuousAddChar F)
    (hchart : ∀ (x : F)
      (hx : x ∈ lattice F (((t / 2 + 1 : ℕ) : ℤ))),
      tau.1 (principalUnitOf F (t / 2) (-x)
        (neg_mem_lattice F hx)) = PsiF x)
    (hodd : Odd (t + 1)) :
    ∃ (e : ℕ) (he : 0 < e),
      ord F (2 : F) = ((e : ℤ) : WithTop ℤ) ∧
      t + 1 = 2 * e + 1 ∧
      ∀ w : lattice E (e : ℤ),
        tau.1 (criticalNormUnit F E hres he w : Fˣ) =
            tracePullbackAddChar F E PsiF (w : E) ∧
        (criticalNormResidual F tau.1 PsiF he
            (criticalNormLattice F E hres w))⁻¹ =
          tracePullbackAddChar F E PsiF (w : E) *
            PsiF (norm F E (w : E)) := by
  obtain ⟨_, e, hordTwo, hT, _⟩ :=
    oddConductor F E hchar ht htpos hres hdegree pi hpi hgen tau htau
      PsiF hchart hodd
  have he : 0 < e := by omega
  have hq : t / 2 + 1 = e + 1 := by omega
  have hPsiETrivial := criticalChart_tracePullback_trivial F E ht htpos hres hdegree
    pi hpi hgen tau htau PsiF hchart
  refine ⟨e, he, hordTwo, hT, ?_⟩
  intro w
  have hr := criticalTraceQuotient_mem_lattice F E ht hres hdegree pi hpi hgen he hT w
  have hreciprocity :
      tau.1 (criticalNormUnit F E hres he w : Fˣ) =
        tracePullbackAddChar F E PsiF (w : E) :=
    (normCharacter_criticalNormUnit_eq_traceQuotient F E hres hdegree he hq tau PsiF
      hchart w hr).trans
      (criticalTraceQuotient_phase F E hres hdegree he hT PsiF hPsiETrivial w)
  refine ⟨hreciprocity, ?_⟩
  rw [criticalNormResidual_inv]
  change tau.1 (criticalNormUnit F E hres he w : Fˣ) * PsiF (norm F E (w : E)) = _
  rw [hreciprocity]

end

end LanglandsSecondMainLemma.Dyadic.UR
