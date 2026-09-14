import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsSecondMainLemma.Dyadic.UR.CriticalRatio

/-!
# Dyadic / UR / Unramified Sum

Blueprint: blueprint/tasks/Dyadic/UR/UnramifiedSum.md
Paper: D:UR:resU

The finite calculation uses the complete Hasse function, with its affine
term intact. Its trivial restriction to the residue subfield determines
the full normalized sum by character orthogonality.
-/

namespace LanglandsSecondMainLemma.Dyadic.UR

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

/-- Orthogonality for a quadratic extension and the full quadratic
refinement. Triviality on the subfield supplies its self-annihilator;
no homogeneity of the refinement is required. -/
private theorem unramifiedSum_finite
    (k l : Type*) [Field k] [Field l] [Fintype k] [Fintype l] [Algebra k l]
    (hdegree : Module.finrank k l = 2)
    (psi : FiniteAddChar l) (hpsi : psi ≠ 1) (H : HasseFunction l psi)
    (hH : ∀ a : k, H (algebraMap k l a) = 1) :
    H.sum = (Fintype.card k : ℂ) := by
  classical
  let i := algebraMap k l
  have hbase (a : k) : psi (i a) = 1 := by
    have hh := H.map_add (i 1) (i a)
    rw [← map_add, hH, hH, hH, map_one, one_mul, one_mul, one_mul] at hh
    exact hh.symm
  obtain ⟨z, hz⟩ : ∃ z : l, psi z ≠ 1 := by
    by_contra! hn
    exact hpsi (DFunLike.ext _ _ hn)
  have hzbase : ∀ a : k, z ≠ i a := by
    intro a ha
    exact hz (ha ▸ hbase a)
  let f : k × k → l := fun ab => i ab.1 + z * i ab.2
  have hinj : Function.Injective f := by
    intro a b hab
    have heq : i a.1 + z * i a.2 = i b.1 + z * i b.2 := hab
    have hs : a.2 = b.2 := by
      by_contra hne
      have hden : i (a.2 - b.2) ≠ 0 := (map_ne_zero i).2 (sub_ne_zero.mpr hne)
      apply hzbase ((b.1 - a.1) / (a.2 - b.2))
      rw [map_div₀, i.map_sub, i.map_sub]
      apply (eq_div_iff (by simpa only [map_sub] using hden)).2
      linear_combination heq
    apply Prod.ext
    · apply i.injective
      rw [hs] at heq
      exact add_right_cancel heq
    · exact hs
  have hbij : Function.Bijective f := by
    apply (Fintype.bijective_iff_injective_and_card f).2
    refine ⟨hinj, ?_⟩
    rw [Fintype.card_prod, Module.card_eq_pow_finrank (K := k) (V := l), hdegree, pow_two]
  let xi : FiniteAddChar k := (psi.mulShift z).compAddMonoidHom i.toAddMonoidHom
  have hxi : xi ≠ 1 := by
    intro heq
    have h := DFunLike.congr_fun heq (1 : k)
    exact hz (by simpa [xi] using h)
  have hinner (b : k) :
      (∑ a : k, H (i a + z * i b)) =
        if b = 0 then (Fintype.card k : ℂ) else 0 := by
    by_cases hb : b = 0
    · subst b
      simp [hH, i]
    · have hzero : (∑ a : k, (xi.mulShift b) a) = 0 :=
        finiteAddChar_sum_eq_zero ((AddChar.IsPrimitive.of_ne_one hxi) hb)
      calc
        (∑ a : k, H (i a + z * i b)) =
            H (z * i b) * ∑ a : k, (xi.mulShift b) a := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          rw [H.map_add, hH, one_mul]
          congr 1
          change psi (i a * (z * i b)) = psi (z * i (b * a))
          rw [i.map_mul]
          congr 1
          ring
        _ = _ := by rw [hzero]; simp [hb]
  calc
    H.sum = ∑ ab : k × k, H (f ab) := by
      exact (Fintype.sum_bijective f hbij _ _ (fun _ => rfl)).symm
    _ = ∑ b : k, ∑ a : k, H (i a + z * i b) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = (Fintype.card k : ℂ) := by simp_rw [hinner]; simp

section Hasse
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- Use the admissible denominator `(-alpha * Z)⁻¹`, for which the
stationary numerator is one. This constructs FML's Hasse function directly
from the actual coefficient, and retains evaluation on every integral lift. -/
private theorem unramifiedSum_hasse
    (theta : LocalQuasiCharData L) (psi : LocalAddCharData L)
    (alpha Z : Lˣ) (a : ℕ) (hm : theta.conductor = 2 * a + 1)
    (hlarge : 1 < theta.conductor)
    (hZ : ord L (Z : L) =
      ((-(scaleAddCharData L psi alpha).conductor - (theta.conductor : ℤ)) : WithTop ℤ))
    (hstat : Stationary.IsNormalizedStationaryCoefficientAtDepth L theta
      (scaleAddCharData L psi alpha) Z (a + 1) (by omega))
    (delta : Lˣ) (hdelta : ord L (delta : L) = ((a : ℤ) : WithTop ℤ)) :
    ∃ (xi : FiniteAddChar (ResidueField L)) (H : HasseFunction (ResidueField L) xi),
      xi ≠ 1 ∧
      (∀ z : ResidueField L, H z =
        Stationary.normalizedResidualFunction L theta psi alpha Z a hm hlarge
          delta hdelta z) ∧
      ∀ (z : L) (hz : z ∈ lattice L 0),
        H (reduce L z hz) =
          ((scaleAddCharData L psi alpha).character (-(Z : L) * (delta : L) * z) : ℂ) *
            (theta.character (lamprechtHasseUnit L theta a hm hlarge delta hdelta z hz) : ℂ)⁻¹ := by
  let Gamma : AdmissibleGamma L theta psi := ⟨(-alpha * Z)⁻¹, by
    simp only [Units.val_inv_eq_inv_val, Units.val_mul, Units.val_neg,
      ord_inv, ord_mul, ord_neg, ord_coe_eq_unitOrder L alpha, hZ,
      scaleAddCharData_conductor]
    norm_cast
    ring⟩
  let beta : lattice L ((theta.conductor : ℤ) - (theta.conductor : ℤ)) :=
    ⟨1, by simp⟩
  let hr := lamprechtFormula_stationaryDepth L theta a 1 (by omega) hm hlarge
  have hbeta : latticeQuotientMk L
      (sub_le_sub_left hr.int_le_conductor (theta.conductor : ℤ)) beta =
      stationaryNumeratorClass L theta psi (theta.conductor : ℤ) hr Gamma Gamma.property := by
    apply (latticeQuotientMk_eq_stationaryNumeratorClass_iff L theta psi
      (theta.conductor : ℤ) hr Gamma Gamma.property beta).2
    intro z
    have hs := hstat (-z)
    change theta.character (positiveUnitOfLattice L _ (- -z)) =
      (scaleAddCharData L psi alpha).character ((Z : L) * ((-z : lattice L ((a + 1 : ℕ) : ℤ)) : L)) at hs
    rw [neg_neg, Submodule.coe_neg] at hs
    simpa [scaleAddCharData_character_apply, beta, Gamma, div_eq_mul_inv,
      mul_assoc, mul_comm, mul_left_comm] using hs
  let xi := lamprechtResidualAddChar L theta psi a hm hlarge Gamma delta hdelta
  let H := lamprechtHasseFunction L theta psi a hm hlarge Gamma delta hdelta beta hbeta
  have heval (z : L) (hz : z ∈ lattice L 0) :
      lamprechtHasseValue L theta psi a hm hlarge Gamma delta hdelta beta z hz =
        ((scaleAddCharData L psi alpha).character (-(Z : L) * (delta : L) * z) : ℂ) *
          (theta.character (lamprechtHasseUnit L theta a hm hlarge delta hdelta z hz) : ℂ)⁻¹ := by
    simp only [lamprechtHasseValue, scaleAddCharData_character_apply]
    congr 2
    simp [beta, Gamma, div_eq_mul_inv, mul_comm, mul_left_comm]
  refine ⟨xi, H, lamprechtResidualAddChar_ne_one L theta psi a hm hlarge
    Gamma delta hdelta beta hbeta, ?_, ?_⟩
  · intro z
    exact heval (teichmuller L z : L) ((mem_lattice_zero_iff L).2 (teichmuller L z).property)
  · intro z hz
    exact (lamprechtHasseFunction_integral_lift L theta psi a hm hlarge Gamma
      delta hdelta beta hbeta z hz).trans (heval z hz)
end Hasse

section BaseValue
variable (F U E : Type) [Field F] [Field U] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

/-- The determinant restriction and the two legitimate stationary charts
evaluate the complete critical value on the base-field lattice. The final
phase is killed by its ideal depth, including when the trace is zero. -/
private theorem unramifiedSum_baseValue
    (hchar : residueCharacteristic F = 2)
    (hunr : ramificationIndex F U = 1) (hE : Module.finrank F E = 2)
    {t h : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hhpos : 0 < h) (hh : h ≤ t)
    (hodd : (t + 1 + h) % 2 = 1)
    (eta : NormCharacter F U) (tau : NormCharacter F E) (htau : tau ≠ 1)
    (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
    (hdet : Characters.restrictQuasiChar F U thetaU * eta.1 =
      Characters.restrictQuasiChar F E thetaE * tau.1)
    (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (hchart : ∀ (z : F) (hz : z ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
      tau.1 (principalUnitOf F (t / 2) (-z) (neg_mem_lattice F hz)) = Psi z)
    (c : ringOfIntegers F)
    (hc : (@absoluteTraceTwo (ResidueField F) _ (ringChar.of_eq hchar))
      (residueMap F c) = 1)
    (d : U) (x : E) (hx : ord E x = ((-(h : ℤ)) : WithTop ℤ))
    (R : ConjugatedNormData F U E thetaU thetaE Psi (c : F) d x t h)
    (v : lattice F (((t + h) / 2 : ℕ) : ℤ)) :
    (tracePullbackAddChar F U Psi (-(R.ZU : U) * algebraMap F U (v : F)) : ℂ) *
      (thetaU (Units.map (algebraMap F U).toMonoidHom
        (positiveUnitOfLattice F (by omega) v)) : ℂ)⁻¹ = 1 := by
  let a := (t + h) / 2
  have ha : 0 < a := by dsimp [a]; omega
  have haq : t / 2 + 1 ≤ a := by dsimp [a]; omega
  have haE : t / 2 + h + 1 ≤ 2 * a := by dsimp [a]; omega
  have hram : ramificationIndex F E = 2 := by
    have hf := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa only [hE, hres, mul_one] using hf.symm
  let u : Fˣ := positiveUnitOfLattice F ha v
  have heta : eta.1 u = 1 :=
    (unramifiedNormCharacter_conductor F U hunr eta).trivial u
      (unitFiltration_antitone F (Nat.zero_le a) (positiveUnitOfLattice F ha v).property)
  have hvq : (v : F) ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ) :=
    lattice_antitone F (by exact_mod_cast haq) v.property
  have htauval : tau.1 u = Psi (-(v : F)) := by
    have hv := hchart (-(v : F)) (neg_mem_lattice F hvq)
    convert hv using 1
    congr 1
    apply Units.ext
    simp only [u, coe_positiveUnitOfLattice, coe_principalUnitOf, neg_neg]
  have hvE : algebraMap F E (v : F) ∈
      lattice E ((t / 2 + h + 1 : ℕ) : ℤ) := by
    apply lattice_antitone E (show ((t / 2 + h + 1 : ℕ) : ℤ) ≤ 2 * (a : ℤ) by omega)
    rw [mem_lattice, ord_algebraMap, hram, two_nsmul]
    simpa only [two_mul, WithTop.coe_add] using
      add_le_add ((mem_lattice F).1 v.property) ((mem_lattice F).1 v.property)
  have hEval : thetaE (Units.map (algebraMap F E).toMonoidHom u) =
      Psi (-(trace F E (R.ZE : E)) * (v : F)) := by
    have hs := R.stationaryE ⟨-algebraMap F E (v : F), neg_mem_lattice E hvE⟩
    change thetaE (positiveUnitOfLattice E _
      (-⟨-algebraMap F E (v : F), neg_mem_lattice E hvE⟩)) =
        tracePullbackAddChar F E Psi ((R.ZE : E) * -algebraMap F E (v : F)) at hs
    have huE : (positiveUnitOfLattice E (by omega)
        (-⟨-algebraMap F E (v : F), neg_mem_lattice E hvE⟩) : Eˣ) =
        Units.map (algebraMap F E).toMonoidHom u := by
      apply Units.ext
      simp only [coe_positiveUnitOfLattice, Submodule.coe_neg, neg_neg, Units.coe_map,
        u, coe_positiveUnitOfLattice]
      change 1 + algebraMap F E (v : F) = algebraMap F E (1 + (v : F))
      rw [map_add, map_one]
    rw [huE, tracePullbackAddChar_apply] at hs
    convert hs using 1
    congr 1
    simp only [mul_neg, map_neg, neg_mul]
    congr 1
    simpa only [smul_eq_mul, Algebra.smul_def, Algebra.algebraMap_self, mul_comm] using
      ((trace F E).map_smul (v : F) (R.ZE : E)).symm
  have hUval : thetaU (Units.map (algebraMap F U).toMonoidHom u) =
      Psi (-(trace F E (R.ZE : E)) * (v : F) - (v : F)) := by
    have hd := DFunLike.congr_fun hdet u
    change thetaU (Units.map (algebraMap F U).toMonoidHom u) * eta.1 u =
      thetaE (Units.map (algebraMap F E).toMonoidHom u) * tau.1 u at hd
    rw [heta, mul_one, hEval, htauval] at hd
    simpa only [← Psi.map_add_eq_mul, sub_eq_add_neg] using hd
  have htraceU : trace F U (-(R.ZU : U) * algebraMap F U (v : F)) =
      -(trace F U (R.ZU : U)) * (v : F) := by
    simp only [neg_mul, map_neg]
    congr 1
    simpa only [smul_eq_mul, Algebra.smul_def, Algebra.algebraMap_self, mul_comm] using
      (trace F U).map_smul (v : F) (R.ZU : U)
  have huord : ord F (trace F E x ^ 2 / norm F E x) = ((t : ℤ) : WithTop ℤ) :=
    ((traceParity F E hchar ht hres hE tau htau Psi hPsi hchart hhpos hh
      x hx c hc).2.1 (by omega)).1
  have hphase : Psi (-(c : F) * (trace F E x ^ 2 / norm F E x) * (v : F)) = 1 := by
    apply hPsi.trivial
    have hm := mul_mem_lattice F
      (mul_mem_lattice F (neg_mem_lattice F ((mem_lattice_zero_iff F).2 c.property))
        ((mem_lattice F).2 (by rw [huord]))) v.property
    apply lattice_antitone F (show -(-((t + 1 : ℕ) : ℤ)) ≤ 0 + (t : ℤ) + a by omega) hm
  have harg : -(trace F U (R.ZU : U)) * (v : F) -
      (-(trace F E (R.ZE : E)) * (v : F) - (v : F)) =
        -(c : F) * (trace F E x ^ 2 / norm F E x) * (v : F) := by
    linear_combination -(v : F) * R.trace_difference
  change (tracePullbackAddChar F U Psi _ : ℂ) *
    (thetaU (Units.map (algebraMap F U).toMonoidHom u) : ℂ)⁻¹ = 1
  rw [hUval, tracePullbackAddChar_apply, htraceU]
  have hp := congrArg (Units.val : ℂˣ → ℂ)
    (Psi.toAddChar.map_sub_eq_div (-(trace F U (R.ZU : U)) * (v : F))
      (-(trace F E (R.ZE : E)) * (v : F) - (v : F)))
  change (Psi (-(trace F U (R.ZU : U)) * (v : F) -
      (-(trace F E (R.ZE : E)) * (v : F) - (v : F))) : ℂ) =
    ((Psi (-(trace F U (R.ZU : U)) * (v : F)) /
      Psi (-(trace F E (R.ZE : E)) * (v : F) - (v : F)) : ℂˣ) : ℂ) at hp
  rw [harg, hphase] at hp
  simpa only [Units.val_one, Units.val_div_eq_div_val, div_eq_mul_inv,
    Units.val_mul, Units.val_inv_eq_inv_val] using hp.symm
end BaseValue

section Evaluation
variable (F U : Type) [Field F] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U]

/-- The paper's two conclusions, for every base-field critical element of
the exact half-conductor order. The residue function is the actual complete
function, and the sum is the same `criticalResidualFactor` as in the ratio. -/
def UnramifiedSumIdentity
    (theta : LocalQuasiCharData U) (psi : LocalAddCharData U) (alpha Z : Uˣ) : Prop :=
  ∀ (delta : Fˣ)
    (_hdelta : ord F (delta : F) = ((theta.conductor / 2 : ℕ) : WithTop ℤ)),
  let deltaU := Units.map (algebraMap F U).toMonoidHom delta
  ∃ (hm : theta.conductor = 2 * (theta.conductor / 2) + 1)
    (hlarge : 1 < theta.conductor)
    (hdeltaU : ord U (deltaU : U) = ((theta.conductor / 2 : ℕ) : WithTop ℤ)),
    (∀ z : ResidueField F,
      Stationary.normalizedResidualFunction U theta psi alpha Z
        (theta.conductor / 2) hm hlarge deltaU hdeltaU
        (algebraMap (ResidueField F) (ResidueField U) z) = 1) ∧
    criticalResidualFactor U theta psi alpha Z hlarge deltaU hdeltaU = 1

variable (E : Type) [Field E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

private theorem unramifiedSum_of_representatives
    (hchar : residueCharacteristic F = 2)
    (hunr : ramificationIndex F U = 1) (hU : Module.finrank F U = 2)
    (hE : Module.finrank F E = 2)
    {t h : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hhpos : 0 < h) (hh : h ≤ t)
    (hodd : (t + 1 + h) % 2 = 1)
    (eta : NormCharacter F U) (tau : NormCharacter F E) (htau : tau ≠ 1)
    (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
    (hcondU : IsMultiplicativeConductor U thetaU (t + 1 + h))
    (hdet : Characters.restrictQuasiChar F U thetaU * eta.1 =
      Characters.restrictQuasiChar F E thetaE * tau.1)
    (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (hchart : ∀ (z : F) (hz : z ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
      tau.1 (principalUnitOf F (t / 2) (-z) (neg_mem_lattice F hz)) = Psi z)
    (c : ringOfIntegers F)
    (hc : (@absoluteTraceTwo (ResidueField F) _ (ringChar.of_eq hchar))
      (residueMap F c) = 1)
    (d : U) (x : E) (hx : ord E x = ((-(h : ℤ)) : WithTop ℤ))
    (R : ConjugatedNormData F U E thetaU thetaE Psi (c : F) d x t h)
    (psiU : LocalAddCharData U) (alphaU : Uˣ)
    (hscale : (scaleAddCharData U psiU alphaU).character = tracePullbackAddChar F U Psi) :
    UnramifiedSumIdentity F U (canonicalLocalQuasiCharData U thetaU) psiU alphaU R.ZU := by
  let chi := canonicalLocalQuasiCharData U thetaU
  have hmU : chi.conductor = t + 1 + h := chi.isConductor.unique hcondU
  have hhalf : chi.conductor / 2 = (t + h) / 2 := by omega
  have hm : chi.conductor = 2 * (chi.conductor / 2) + 1 := by omega
  have hlarge : 1 < chi.conductor := by omega
  have hscaleData : scaleAddCharData U psiU alphaU =
      ⟨tracePullbackAddChar F U Psi, -((t + 1 : ℕ) : ℤ), R.additiveConductorU⟩ :=
    LocalAddCharData.eq_of_character_eq hscale
  have hZ : ord U (R.ZU : U) =
      ((-(scaleAddCharData U psiU alphaU).conductor - (chi.conductor : ℤ)) : WithTop ℤ) := by
    rw [hscaleData, R.orderU, hmU]
    congr 1
    push_cast
    ring
  have hstat : Stationary.IsNormalizedStationaryCoefficientAtDepth U chi
      (scaleAddCharData U psiU alphaU) R.ZU (chi.conductor / 2 + 1) (by omega) := by
    simpa only [hscaleData, hhalf] using R.stationaryU
  intro delta hdelta
  let deltaU := Units.map (algebraMap F U).toMonoidHom delta
  have hdeltaU : ord U (deltaU : U) = ((chi.conductor / 2 : ℕ) : WithTop ℤ) := by
    change ord U (algebraMap F U (delta : F)) = _
    rw [ord_algebraMap, hunr, one_nsmul, hdelta]
  refine ⟨hm, hlarge, hdeltaU, ?_⟩
  obtain ⟨xi, H, hxi, hH, hlift⟩ := unramifiedSum_hasse U chi psiU alphaU R.ZU
    (chi.conductor / 2) hm hlarge hZ hstat deltaU hdeltaU
  have hbase (z : ResidueField F) :
      H (algebraMap (ResidueField F) (ResidueField U) z) = 1 := by
    let zF := teichmuller F z
    let zU := algebraMap (ringOfIntegers F) (ringOfIntegers U) zF
    have hzU : (zU : U) ∈ lattice U 0 := (mem_lattice_zero_iff U).2 zU.property
    have hzval : (zU : U) = algebraMap F U (zF : F) :=
      Valuation.HasExtension.val_algebraMap zF
    have hzred : reduce U (zU : U) hzU =
        algebraMap (ResidueField F) (ResidueField U) z := by
      change residueMap U zU = _
      have heq : algebraMap (ResidueField F) (ResidueField U) (residueMap F zF) =
          residueMap U zU :=
        Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
          (ValuativeRel.valuation F) (ValuativeRel.valuation U) zF
      simpa only [zF, residueMap_teichmuller] using heq.symm
    let v : lattice F (((t + h) / 2 : ℕ) : ℤ) := ⟨(delta : F) * (zF : F), by
      have hdmem : (delta : F) ∈ lattice F ((chi.conductor / 2 : ℕ) : ℤ) :=
        (mem_lattice F).2 (by rw [hdelta]; norm_cast)
      have hv := mul_mem_lattice F hdmem ((mem_lattice_zero_iff F).2 zF.property)
      simpa only [add_zero, hhalf] using hv⟩
    have hmul : (deltaU : U) * (zU : U) = algebraMap F U (v : F) := by
      change algebraMap F U (delta : F) * (zU : U) =
        algebraMap F U ((delta : F) * (zF : F))
      rw [hzval, map_mul]
    have hu : (lamprechtHasseUnit U chi (chi.conductor / 2) hm hlarge
        deltaU hdeltaU (zU : U) hzU : Uˣ) =
        Units.map (algebraMap F U).toMonoidHom (positiveUnitOfLattice F (by omega) v) := by
      apply Units.ext
      rw [lamprechtHasseUnit_coe, hmul]
      change 1 + algebraMap F U (v : F) =
        algebraMap F U ((positiveUnitOfLattice F (by omega) v : Fˣ) : F)
      rw [coe_positiveUnitOfLattice, map_add, map_one]
    rw [← hzred, hlift, hscale, mul_assoc, hmul, hu]
    exact unramifiedSum_baseValue F U E hchar hunr hE ht hres hhpos hh hodd
      eta tau htau thetaU thetaE hdet Psi hPsi hchart c hc d x hx R v
  refine ⟨fun z => (hH _).symm.trans (hbase z), ?_⟩
  letI := residueFieldFintype F
  letI := residueFieldFintype U
  have hdegree : Module.finrank (ResidueField F) (ResidueField U) = 2 := by
    rw [← residueDegree_eq_finrank_residueField]
    have hf := finrank_eq_ramificationIndex_mul_residueDegree F U
    simpa only [hU, hunr, one_mul] using hf.symm
  have hsum := unramifiedSum_finite (ResidueField F) (ResidueField U) hdegree xi hxi H hbase
  have hcard : residueCard U = residueCard F ^ 2 := by
    simpa only [residueCard, hdegree] using
      (Module.card_eq_pow_finrank (K := ResidueField F) (V := ResidueField U))
  have hsqrt : Real.sqrt (residueCard U : ℝ) = (residueCard F : ℝ) := by
    rw [hcard, Nat.cast_pow, Real.sqrt_sq (by positivity)]
  rw [criticalResidualFactor, dif_neg (show ¬chi.conductor % 2 = 0 by omega)]
  change Stationary.normalizedResidualFactor U chi psiU alphaU R.ZU
    (chi.conductor / 2) hm hlarge deltaU hdeltaU = 1
  change (Real.sqrt (residueCard U : ℝ) : ℂ)⁻¹ *
    (∑ z : ResidueField U, Stationary.normalizedResidualFunction U chi psiU alphaU R.ZU
      (chi.conductor / 2) hm hlarge deltaU hdeltaU z) = 1
  simp_rw [← hH]
  change (Real.sqrt (residueCard U : ℝ) : ℂ)⁻¹ * H.sum = 1
  rw [hsum, hsqrt]
  have hcardF : Fintype.card (ResidueField F) = residueCard F :=
    Fintype.card_congr (Equiv.refl _)
  rw [hcardF]
  simpa only [Complex.ofReal_natCast] using inv_mul_cancel₀
    (show (residueCard F : ℂ) ≠ 0 by exact_mod_cast (Nat.zero_lt_of_lt (one_lt_residueCard F)).ne')
end Evaluation

section ActualPair
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

/-- **Paper Lemma `D:UR:resU`.** For a genuine primitive compatible pair
at positive critical height with odd unramified conductor, construct the
corrected representatives from `criticalRatio`. The actual unramified
residual function is one on the base residue field, and its complete
normalized sum is one. The accompanying ratio retains every lower factor.
Both field characteristics and arbitrary continuous quasi-characters are
included; no representative, restriction identity, or residual cancellation
is an additional hypothesis. -/
theorem unramifiedSum
    (hchar : residueCharacteristic F = 2)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (U E : IntermediateField F K)
    (hU : Module.finrank F U = 2) (hE : Module.finrank F E = 2) :
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
      (t h : ℕ) (_hhpos : 0 < h) (_hh : h ≤ t)
      (_hodd : (t + 1 + h) % 2 = 1)
      (_ht : PrimeCyclicExtension.IsLowerBreak F E t) (_hres : residueDegree F E = 1)
      (eta : NormCharacter F U) (_heta : eta ≠ 1)
      (tau : NormCharacter F E) (_htau : tau ≠ 1)
      (psiF : LocalAddCharData F) (psiU : LocalAddCharData U) (psiE : LocalAddCharData E)
      (_hpsiU : psiU.character = tracePullbackAddChar F U psiF.character)
      (_hpsiE : psiE.character = tracePullbackAddChar F E psiF.character)
      (alpha : Fˣ)
      (_hPsi : (scaleAddCharData F psiF alpha).conductor = -((t + 1 : ℕ) : ℤ))
      (_htauchart : ∀ (z : F) (hz : z ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
        tau.1 (principalUnitOf F (t / 2) (-z) (neg_mem_lattice F hz)) =
          (scaleAddCharData F psiF alpha).character z)
      (sigma : Gal(U/F)) (_hsigma : sigma ≠ 1)
      (c : ringOfIntegers F) (_hc : ord F (c : F) = 0)
      (_htracec : (@absoluteTraceTwo (ResidueField F) _ (ringChar.of_eq hchar))
        (residueMap F c) = 1)
      (d : U) (_hd : ord U d = 0)
      (_hdc : d ^ 2 - d = algebraMap F U (c : F)) (_hconj : sigma d = 1 - d)
      (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
      (_hcomp : normQuasiChar U K thetaU = normQuasiChar E K thetaE)
      (_hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F,
        normQuasiChar F K lambda = normQuasiChar U K thetaU)
      (_hcondU : IsMultiplicativeConductor U thetaU (t + 1 + h)),
      IsMultiplicativeConductor E thetaE (t + 1 + 2 * h) ∧
      ∃ x : E, ord E x = ((-(h : ℤ)) : WithTop ℤ) ∧
      ∃ R : ConjugatedNormData F U E thetaU thetaE
          (scaleAddCharData F psiF alpha).character (c : F) d x t h,
      CriticalRatioIdentity F U E eta tau thetaU thetaE psiF psiU psiE alpha
        (c : F) d x t h R ∧
      UnramifiedSumIdentity F U (canonicalLocalQuasiCharData U thetaU) psiU
        (Units.map (algebraMap F U).toMonoidHom alpha) R.ZU := by
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
  intro hunr t h hhpos hh hodd ht hres eta heta tau htau psiF psiU psiE
    hpsiU hpsiE alpha hPsi htauchart sigma hsigma c hc htracec d hd hdc hconj
    thetaU thetaE hcomp hprimitive hcondU
  obtain ⟨hcondE, x, hx, R, hratio⟩ := criticalRatio hchar hG U E hU hE
    hunr t h hhpos hh ht hres eta heta tau htau psiF psiU psiE hpsiU hpsiE
    alpha hPsi htauchart sigma hsigma c hc htracec d hd hdc hconj thetaU thetaE
    hcomp hprimitive hcondU
  have dataE := Basic.intermediateField_tower_compatible Nat.prime_two hG E hE
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E dataE.2.2.2.2.2.2.2.2.2.2.2.1
  have hne : Ramification.intermediateNormRange U ≠ Ramification.intermediateNormRange E := by
    change (normUnits F U).range ≠ (normUnits F E).range
    intro heq
    obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
    have hct := ramifiedNormCharacter_conductor F E ht hres pi hpi hgen tau htau
    have hzero : QuasiCharTrivialOnUnitFiltration F tau.1 0 := by
      intro u hu
      apply tau.eq_one_on_normRange F E
      rw [← heq]
      obtain ⟨v, _, hv⟩ := (unramified_norm_unitFiltration F U hunr 0).2 u hu
      exact ⟨v, hv⟩
    have hb := hct.minimal 0 hzero
    omega
  obtain ⟨_, _, hdet, _, htwo⟩ := Characters.conjugacy Nat.prime_two hG U E hU hE hne
    thetaU thetaE (normQuasiChar U K thetaU) rfl hcomp.symm hprimitive
  obtain ⟨eta', tau', heta', htau', hprodU, hprodE⟩ := htwo rfl
  have heqEta : eta' = eta :=
    ((Nat.card_eq_two_iff' (1 : NormCharacter F U)).mp
      ((unramifiedNormCharacter_card F U hunr).trans hU)).unique heta' heta
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have heqTau : tau' = tau :=
    ((Nat.card_eq_two_iff' (1 : NormCharacter F E)).mp
      ((ramifiedNormCharacter_card F E ht hres pi hpi hgen).trans hE)).unique htau' htau
  subst eta' tau'
  rw [hprodU, hprodE] at hdet
  refine ⟨hcondE, x, hx, R, hratio, ?_⟩
  apply unramifiedSum_of_representatives F U E hchar hunr hU hE ht hres hhpos hh
    hodd eta tau htau thetaU thetaE hcondU hdet (scaleAddCharData F psiF alpha).character
    (by rw [← hPsi]; exact (scaleAddCharData F psiF alpha).isConductor)
    htauchart c htracec d x hx R psiU (Units.map (algebraMap F U).toMonoidHom alpha)
  ext z
  simp only [scaleAddCharData_character_apply, hpsiU, tracePullbackAddChar_apply,
    Units.coe_map]
  congr 2
  change trace F U (algebraMap F U (alpha : F) * z) = (alpha : F) * trace F U z
  simpa only [smul_eq_mul, Algebra.smul_def, Algebra.algebraMap_self] using
    (trace F U).map_smul (alpha : F) z
end ActualPair

end

end LanglandsSecondMainLemma.Dyadic.UR
