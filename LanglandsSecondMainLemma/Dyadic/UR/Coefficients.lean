import LanglandsFirstMainLemma.Parameters.HighQuadratic
import LanglandsSecondMainLemma.Dyadic.UR.NormChoice
import LanglandsSecondMainLemma.Dyadic.UR.NormPhase


/-!
# Actual half-conductor coefficients for the dyadic UR pair

Paper Lemma `D:UR:coeffs`, equations `D:UR:actualcoeffs` and `D:UR:BCdefs`.
The actual decomposition and conductor data come from `twist`; the exact
norm representative and preservation of its entire base chart come from
`normChoice`. On the ramified side `normPhase` is applied to `x*z` on its
full allowed ideal, with the positive norm sign.

The coefficient valuations are deduced from the already-proved actual
conductors using FML's whole-ideal annihilator theorem. Thus the proof
also covers height zero without introducing extra residue hypotheses.
No common upper norm is asserted to be stationary in this file.
-/

namespace LanglandsSecondMainLemma.Dyadic.UR
noncomputable section
open LanglandsFirstMainLemma

private theorem coefficients_map_sub {L : Type*} [AddCommGroup L] [TopologicalSpace L]
    (Psi : ContinuousAddChar L) (x y : L) :
    Psi (x - y) = Psi x / Psi y := Psi.toAddChar.map_sub_eq_div x y

/-- An actual full chart and the exact multiplicative conductor determine
its coefficient order by whole-ideal duality, including the zero-height row. -/
private theorem coefficients_chart_order
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    (theta : ContinuousQuasiChar L) (Psi : ContinuousAddChar L)
    {m r : ℕ} {J : ℤ} (hrm : r + 1 < m)
    (htheta : IsMultiplicativeConductor L theta m)
    (hPsi : IsAdditiveConductor L Psi (-J)) (B : L)
    (hchart : ∀ (z : L) (hz : z ∈ lattice L ((r + 1 : ℕ) : ℤ)),
      theta (principalUnitOf L r (-z) (neg_mem_lattice L hz)) = Psi (B * z)) :
    ord L B = ((J - (m : ℤ) : ℤ) : WithTop ℤ) := by
  let psi : LocalAddCharData L := ⟨Psi, -J, hPsi⟩
  have hGamma : ord L (1 : L) = ((J + psi.conductor : ℤ) : WithTop ℤ) := by
    simp [psi]
  have hB : B ∈ lattice L (J - (m : ℤ)) := by
    apply (lamprechtAnnihilatorLeft L psi hGamma).mp
    intro z hz
    have hz' : z ∈ lattice L ((r + 1 : ℕ) : ℤ) :=
      lattice_antitone L (by omega) hz
    have hunit : principalUnitOf L r (-z) (neg_mem_lattice L hz') ∈
        unitFiltration L m := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
      rw [mem_unitFiltration_succ_iff_sub_mem_lattice, coe_principalUnitOf]
      simpa only [add_sub_cancel_left] using neg_mem_lattice L hz
    simpa only [div_one] using (hchart z hz').symm.trans (htheta.trivial _ hunit)
  rw [← mem_lattice_and_not_mem_succ_iff]
  refine ⟨hB, ?_⟩
  intro hdeep
  have htriv : QuasiCharTrivialOnUnitFiltration L theta (m - 1) := by
    intro u hu
    have hp : 0 < m - 1 := by omega
    let z := -(positiveUnitDisplacement L hp ⟨u, hu⟩ : L)
    have hz : z ∈ lattice L ((m - 1 : ℕ) : ℤ) :=
      neg_mem_lattice L (positiveUnitDisplacement L hp ⟨u, hu⟩).property
    have hz' : z ∈ lattice L ((r + 1 : ℕ) : ℤ) :=
      lattice_antitone L (by omega) hz
    have hu' : principalUnitOf L r (-z) (neg_mem_lattice L hz') = u := by
      apply Units.ext
      simp [z, coe_principalUnitOf, positiveUnitDisplacement]
    rw [← hu', hchart z hz']
    apply hPsi.trivial
    have hprod := mul_mem_lattice L hdeep hz
    have heq : J - (m : ℤ) + 1 + ((m - 1 : ℕ) : ℤ) = - -J := by omega
    simpa only [heq] using hprod
  exact (htheta.not_trivialOnUnitFiltration_iff.mpr (by omega)) htriv

/-- The unit-base specialization of FML's exact quadratic norm identity. -/
private theorem coefficients_norm_one_sub
    (F L : Type*) [Field F] [Field L]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra F L] [ValuativeExtension F L] [Module.Finite F L]
    (hdegree : Module.finrank F L = 2) (z : L) :
    norm F L (1 - z) = 1 - trace F L z + norm F L z := by
  simpa only [Units.val_one, map_one, one_pow, one_mul] using
    wildQuadratic_norm_sub F L hdegree 1 z

/-- Read the same principal-unit chart using any unit with value `1-z`. -/
private theorem coefficients_chart_apply
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    (theta : ContinuousQuasiChar L) (Psi : ContinuousAddChar L)
    (B : L) (r : ℕ)
    (hchart : ∀ (z : L) (hz : z ∈ lattice L ((r + 1 : ℕ) : ℤ)),
      theta (principalUnitOf L r (-z) (neg_mem_lattice L hz)) = Psi (B * z))
    (z : L) (hz : z ∈ lattice L ((r + 1 : ℕ) : ℤ))
    (u : Lˣ) (hu : (u : L) = 1 - z) : theta u = Psi (B * z) := by
  have heq : u = principalUnitOf L r (-z) (neg_mem_lattice L hz) := by
    apply Units.ext
    simpa only [coe_principalUnitOf, sub_eq_add_neg] using hu
  rw [heq, hchart z hz]

section Unramified
variable (F U : Type*) [Field F] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U]

/-- The unramified norm error is killed after multiplying by the actual
base coefficient, whose valuation can be negative. -/
private theorem coefficients_unramified_chart
    (hunr : ramificationIndex F U = 1) (hdegree : Module.finrank F U = 2)
    {t h : ℕ} (lambda : ContinuousQuasiChar F) (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (A : F) (hA : A ∈ lattice F (-(h : ℤ)))
    (hchart : ∀ (z : F) (hz : z ∈ lattice F (((t + h) / 2 + 1 : ℕ) : ℤ)),
      lambda (principalUnitOf F ((t + h) / 2) (-z) (neg_mem_lattice F hz)) =
        Psi (A * z))
    (z : U) (hz : z ∈ lattice U (((t + h) / 2 + 1 : ℕ) : ℤ))
    (u : Uˣ) (hu : (u : U) = 1 - z) :
    normQuasiChar F U lambda u =
      tracePullbackAddChar F U Psi (algebraMap F U A * z) := by
  have htrace := trace_mem_lattice F U hunr _ hz
  have hres : residueDegree F U = 2 := by
    have hdeg := finrank_eq_ramificationIndex_mul_residueDegree F U
    simpa only [hunr, one_mul, hdegree] using hdeg.symm
  have hnorm : norm F U z ∈ lattice F (2 * (((t + h) / 2 + 1 : ℕ) : ℤ)) := by
    rw [mem_lattice, ord_norm, hres]
    have hbound := add_le_add ((mem_lattice U).mp hz) ((mem_lattice U).mp hz)
    simpa only [two_nsmul, two_mul, WithTop.coe_add] using hbound
  have hy : trace F U z - norm F U z ∈
      lattice F (((t + h) / 2 + 1 : ℕ) : ℤ) :=
    sub_mem_lattice F htrace (lattice_antitone F (by omega) hnorm)
  have hvalue := coefficients_chart_apply F lambda Psi A ((t + h) / 2) hchart
    _ hy (normUnits F U u) (by
      rw [coe_normUnits, hu, coefficients_norm_one_sub F U hdegree]
      ring)
  have herror : Psi (A * norm F U z) = 1 := by
    apply hPsi.trivial
    exact lattice_antitone F (by push_cast; omega) (mul_mem_lattice F hA hnorm)
  change lambda (normUnits F U u) = Psi (trace F U (algebraMap F U A * z))
  rw [hvalue, mul_sub, coefficients_map_sub, herror, div_one]
  congr 1
  simpa [Algebra.smul_def] using ((trace F U).map_smul A z).symm
end Unramified


section Ramified
variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

/-- On the ramified side, the exact phase at `x*z` changes the norm
coefficient `A` into `A-x`. No approximation of `x` is made here. -/
private theorem coefficients_ramified_chart
    (hdegree : Module.finrank F E = 2)
    {t h : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (htpos : 0 < t) (hres : residueDegree F E = 1) (hh : h ≤ t)
    (tau : NormCharacter F E) (htau : tau ≠ 1)
    (Psi : ContinuousAddChar F)
    (htauchart : ∀ (z : F) (hz : z ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
      tau.1 (principalUnitOf F (t / 2) (-z) (neg_mem_lattice F hz)) = Psi z)
    (lambda : ContinuousQuasiChar F) (x : E) (hx : x ∈ lattice E (-(h : ℤ)))
    (hchart : ∀ (z : F) (hz : z ∈ lattice F (((t + h) / 2 + 1 : ℕ) : ℤ)),
      lambda (principalUnitOf F ((t + h) / 2) (-z) (neg_mem_lattice F hz)) =
        Psi (norm F E x * z))
    (z : E) (hz : z ∈ lattice E ((t / 2 + h + 1 : ℕ) : ℤ))
    (u : Eˣ) (hu : (u : E) = 1 - z) :
    normQuasiChar F E lambda u = tracePullbackAddChar F E Psi
      ((algebraMap F E (norm F E x) - x) * z) := by
  have htrace : trace F E z ∈ lattice F (((t + h) / 2 + 1 : ℕ) : ℤ) := by
    obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
    have hmem : trace F E z ∈
        Submodule.map ((trace F E).restrictScalars (ringOfIntegers F))
          ((lattice E ((t / 2 + h + 1 : ℕ) : ℤ)).restrictScalars (ringOfIntegers F)) :=
      Submodule.mem_map.mpr ⟨z, hz, rfl⟩
    rw [cyclicPrime_trace_lattice_image_eq F E ht hres pi hpi hgen, hdegree] at hmem
    apply lattice_antitone F (show (((t + h) / 2 + 1 : ℕ) : ℤ) ≤
      (((t / 2 + h + 1 : ℕ) : ℤ) + (((2 - 1) * (t + 1) : ℕ) : ℤ)) / 2
      by norm_num; omega) hmem
  have hnorm : norm F E z ∈ lattice F (((t + h) / 2 + 1 : ℕ) : ℤ) := by
    rw [mem_lattice, ord_norm, hres, one_nsmul]
    exact (mem_lattice E).mp (lattice_antitone E (by omega) hz)
  have hy := sub_mem_lattice F htrace hnorm
  have hvalue := coefficients_chart_apply F lambda Psi (norm F E x)
    ((t + h) / 2) hchart _ hy (normUnits F E u) (by
      rw [coe_normUnits, hu, coefficients_norm_one_sub F E hdegree]
      ring)
  have hxz : x * z ∈ lattice E ((t / 2 + 1 : ℕ) : ℤ) := by
    exact lattice_antitone E (by push_cast; omega) (mul_mem_lattice E hx hz)
  have hphase := normPhase F E ht htpos hres hdegree tau htau Psi htauchart (x * z) hxz
  rw [map_mul (norm F E)] at hphase
  change lambda (normUnits F E u) = Psi (trace F E
    ((algebraMap F E (norm F E x) - x) * z))
  rw [hvalue, mul_sub, coefficients_map_sub, ← hphase]
  rw [sub_mul, map_sub, coefficients_map_sub]
  congr 1
  congr 1
  simpa [Algebra.smul_def] using
    ((trace F E).map_smul (norm F E x) z).symm
end Ramified


section ActualCoefficients
variable (F U E : Type) [Field F] [Field U] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

/-- **The actual coefficients**, paper Lemma `D:UR:coeffs`.

For the actual twist decomposition furnished by `twist`, and the same
representative `x` furnished by `normChoice`, the coefficients are literally
`B_U = N(x)+d²` and `B_E = N(x)-x+c`. The hypotheses on the model charts
and the actual conductors are conclusions of `twist`; the hypotheses on
`x` are conclusions of `normChoice`. In particular neither displayed
coefficient formula nor a stationary common upper norm is assumed.

Here `s_U = (t+h)/2+1` and `s_E = t/2+h+1`. Every ideal uses an integer
exponent, including the lower bound `-h` on the actual representative.
The exact coefficient orders follow from the full chart and exact
conductor by FML whole-ideal duality. This also proves the height-zero
orders, without needing a separate residue argument or excluding `x=0`.
The ramified model character includes the unramified adjustment in `twist`.
-/
theorem coefficients
    (hunr : ramificationIndex F U = 1)
    (hUdegree : Module.finrank F U = 2) (hEdegree : Module.finrank F E = 2)
    {t h : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (htpos : 0 < t) (hres : residueDegree F E = 1) (hh : h ≤ t)
    (tau : NormCharacter F E) (htau : tau ≠ 1)
    (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (htauchart : ∀ (z : F) (hz : z ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
      tau.1 (principalUnitOf F (t / 2) (-z) (neg_mem_lattice F hz)) = Psi z)
    (c : F) (d : U)
    (chiU thetaU : ContinuousQuasiChar U) (chiE thetaE : ContinuousQuasiChar E)
    (lambda : ContinuousQuasiChar F)
    (hmodelU : ∀ (z : U) (hz : z ∈ lattice U ((t / 2 + 1 : ℕ) : ℤ)),
      chiU (principalUnitOf U (t / 2) (-z) (neg_mem_lattice U hz)) =
        tracePullbackAddChar F U Psi (d ^ 2 * z))
    (hmodelE : ∀ (z : E) (hz : z ∈ lattice E ((t / 2 + 1 : ℕ) : ℤ)),
      chiE (principalUnitOf E (t / 2) (-z) (neg_mem_lattice E hz)) =
        tracePullbackAddChar F E Psi (algebraMap F E c * z))
    (htwistU : thetaU = chiU * normQuasiChar F U lambda)
    (htwistE : thetaE = chiE * normQuasiChar F E lambda)
    (hcondU : IsMultiplicativeConductor U thetaU (t + 1 + h))
    (hcondE : IsMultiplicativeConductor E thetaE (t + 1 + 2 * h))
    (x : E)
    (hxchart : ∀ (z : F) (hz : z ∈ lattice F (((t + h) / 2 + 1 : ℕ) : ℤ)),
      lambda (principalUnitOf F ((t + h) / 2) (-z) (neg_mem_lattice F hz)) =
        Psi (norm F E x * z))
    (hxorder : 0 < h → ord E x = ((-(h : ℤ) : ℤ) : WithTop ℤ))
    (hxintegral : h = 0 → x ∈ lattice E 0) :
    (∀ (z : U) (hz : z ∈ lattice U (((t + h) / 2 + 1 : ℕ) : ℤ)),
      thetaU (principalUnitOf U ((t + h) / 2) (-z) (neg_mem_lattice U hz)) =
        tracePullbackAddChar F U Psi ((algebraMap F U (norm F E x) + d ^ 2) * z)) ∧
    (∀ (z : E) (hz : z ∈ lattice E ((t / 2 + h + 1 : ℕ) : ℤ)),
      thetaE (principalUnitOf E (t / 2 + h) (-z) (neg_mem_lattice E hz)) =
        tracePullbackAddChar F E Psi
          ((algebraMap F E (norm F E x) - x + algebraMap F E c) * z)) ∧
    ord U (algebraMap F U (norm F E x) + d ^ 2) =
      ((-(h : ℤ) : ℤ) : WithTop ℤ) ∧
    ord E (algebraMap F E (norm F E x) - x + algebraMap F E c) =
      ((-2 * (h : ℤ) : ℤ) : WithTop ℤ) := by
  have hx : x ∈ lattice E (-(h : ℤ)) := by
    by_cases hz : h = 0
    · simpa only [hz, Nat.cast_zero, neg_zero] using hxintegral hz
    · rw [mem_lattice, hxorder (by omega)]
  have hA : norm F E x ∈ lattice F (-(h : ℤ)) := by
    rw [mem_lattice, ord_norm, hres, one_nsmul]
    exact (mem_lattice E).mp hx
  have hchartU (z : U) (hz : z ∈ lattice U (((t + h) / 2 + 1 : ℕ) : ℤ)) :
      thetaU (principalUnitOf U ((t + h) / 2) (-z) (neg_mem_lattice U hz)) =
        tracePullbackAddChar F U Psi ((algebraMap F U (norm F E x) + d ^ 2) * z) := by
    let u := principalUnitOf U ((t + h) / 2) (-z) (neg_mem_lattice U hz)
    have hu : (u : U) = 1 - z := by simp only [u, coe_principalUnitOf, sub_eq_add_neg]
    have hm := coefficients_chart_apply U chiU (tracePullbackAddChar F U Psi)
      (d ^ 2) (t / 2) hmodelU z (lattice_antitone U (by omega) hz) u hu
    have hn := coefficients_unramified_chart F U hunr hUdegree lambda Psi hPsi
      (norm F E x) hA hxchart z hz u hu
    change thetaU u = _
    rw [htwistU, ContinuousMonoidHom.mul_apply, hm, hn,
      ← ContinuousAddChar.map_add_eq_mul]
    congr 1
    ring
  have hchartE (z : E) (hz : z ∈ lattice E ((t / 2 + h + 1 : ℕ) : ℤ)) :
      thetaE (principalUnitOf E (t / 2 + h) (-z) (neg_mem_lattice E hz)) =
        tracePullbackAddChar F E Psi
          ((algebraMap F E (norm F E x) - x + algebraMap F E c) * z) := by
    let u := principalUnitOf E (t / 2 + h) (-z) (neg_mem_lattice E hz)
    have hu : (u : E) = 1 - z := by simp only [u, coe_principalUnitOf, sub_eq_add_neg]
    have hm := coefficients_chart_apply E chiE (tracePullbackAddChar F E Psi)
      (algebraMap F E c) (t / 2) hmodelE z (lattice_antitone E (by omega) hz) u hu
    have hn := coefficients_ramified_chart F E hEdegree ht htpos hres hh tau htau
      Psi htauchart lambda x hx hxchart z hz u hu
    change thetaE u = _
    rw [htwistE, ContinuousMonoidHom.mul_apply, hm, hn,
      ← ContinuousAddChar.map_add_eq_mul]
    congr 1
    ring
  have hPsiU : IsAdditiveConductor U (tracePullbackAddChar F U Psi)
      (-((t + 1 : ℕ) : ℤ)) :=
    (unramified_additiveConductor_compTrace F U hunr Psi _).mpr hPsi
  have hPsiE : IsAdditiveConductor E (tracePullbackAddChar F E Psi)
      (-((t + 1 : ℕ) : ℤ)) := by
    obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
    have h := additiveConductor_compTrace_cyclicPrime F E ht hres pi hpi hgen hPsi
    rw [hEdegree] at h
    have heq : (2 : ℤ) * (-((t + 1 : ℕ) : ℤ)) +
        (((2 - 1) * (t + 1) : ℕ) : ℤ) = -((t + 1 : ℕ) : ℤ) := by
      norm_num
      omega
    exact heq ▸ h
  refine ⟨hchartU, hchartE, ?_, ?_⟩
  · have horder := coefficients_chart_order U thetaU (tracePullbackAddChar F U Psi)
      (by omega) hcondU hPsiU _ hchartU
    convert horder using 2
    push_cast
    ring
  · have horder := coefficients_chart_order E thetaE (tracePullbackAddChar F E Psi)
      (by omega) hcondE hPsiE _ hchartE
    convert horder using 2
    push_cast
    ring

/-- Construct the actual norm representative and both coefficients in one
application, using the base-conductor conclusions of `twist`. The zero
coefficient class is still represented by zero, and the chart and order
properties of the selected `x` remain available for later common-norm
calculations. -/
theorem coefficients_exists
    (hunr : ramificationIndex F U = 1)
    (hUdegree : Module.finrank F U = 2) (hEdegree : Module.finrank F E = 2)
    {t h : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (htpos : 0 < t) (hres : residueDegree F E = 1) (hh : h ≤ t)
    (tau : NormCharacter F E) (htau : tau ≠ 1)
    (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (htauchart : ∀ (z : F) (hz : z ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
      tau.1 (principalUnitOf F (t / 2) (-z) (neg_mem_lattice F hz)) = Psi z)
    (c : F) (d : U)
    (chiU thetaU : ContinuousQuasiChar U) (chiE thetaE : ContinuousQuasiChar E)
    (lambda : ContinuousQuasiChar F)
    (hmodelU : ∀ (z : U) (hz : z ∈ lattice U ((t / 2 + 1 : ℕ) : ℤ)),
      chiU (principalUnitOf U (t / 2) (-z) (neg_mem_lattice U hz)) =
        tracePullbackAddChar F U Psi (d ^ 2 * z))
    (hmodelE : ∀ (z : E) (hz : z ∈ lattice E ((t / 2 + 1 : ℕ) : ℤ)),
      chiE (principalUnitOf E (t / 2) (-z) (neg_mem_lattice E hz)) =
        tracePullbackAddChar F E Psi (algebraMap F E c * z))
    (htwistU : thetaU = chiU * normQuasiChar F U lambda)
    (htwistE : thetaE = chiE * normQuasiChar F E lambda)
    (hcondU : IsMultiplicativeConductor U thetaU (t + 1 + h))
    (hcondE : IsMultiplicativeConductor E thetaE (t + 1 + 2 * h))
    (hlambdapos : 0 < h → IsMultiplicativeConductor F lambda (t + 1 + h))
    (hlambdazero : h = 0 → multiplicativeConductorExponent F lambda ≤ t + 1) :
    ∃ x : E,
      (∀ (z : F) (hz : z ∈ lattice F (((t + h) / 2 + 1 : ℕ) : ℤ)),
        lambda (principalUnitOf F ((t + h) / 2) (-z) (neg_mem_lattice F hz)) =
          Psi (norm F E x * z)) ∧
      (0 < h → ord E x = ((-(h : ℤ) : ℤ) : WithTop ℤ)) ∧
      (h = 0 → x ∈ lattice E 0) ∧
      (QuasiCharTrivialOnUnitFiltration F lambda ((t + h) / 2 + 1) → x = 0) ∧
      (∀ (z : U) (hz : z ∈ lattice U (((t + h) / 2 + 1 : ℕ) : ℤ)),
        thetaU (principalUnitOf U ((t + h) / 2) (-z) (neg_mem_lattice U hz)) =
          tracePullbackAddChar F U Psi
            ((algebraMap F U (norm F E x) + d ^ 2) * z)) ∧
      (∀ (z : E) (hz : z ∈ lattice E ((t / 2 + h + 1 : ℕ) : ℤ)),
        thetaE (principalUnitOf E (t / 2 + h) (-z) (neg_mem_lattice E hz)) =
          tracePullbackAddChar F E Psi
            ((algebraMap F E (norm F E x) - x + algebraMap F E c) * z)) ∧
      ord U (algebraMap F U (norm F E x) + d ^ 2) =
        ((-(h : ℤ) : ℤ) : WithTop ℤ) ∧
      ord E (algebraMap F E (norm F E x) - x + algebraMap F E c) =
        ((-2 * (h : ℤ) : ℤ) : WithTop ℤ) := by
  obtain ⟨x, hxchart, hxorder, hxintegral, hxzero⟩ :=
    normChoice F E ht htpos hres hh lambda Psi hPsi hlambdapos hlambdazero
  exact ⟨x, hxchart, hxorder, hxintegral, hxzero,
    coefficients F U E hunr hUdegree hEdegree ht htpos hres hh tau htau Psi hPsi
      htauchart c d chiU thetaU chiE thetaE lambda hmodelU hmodelE htwistU htwistE
      hcondU hcondE x hxchart hxorder hxintegral⟩

end ActualCoefficients

end
end LanglandsSecondMainLemma.Dyadic.UR
