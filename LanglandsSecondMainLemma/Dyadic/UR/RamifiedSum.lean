import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsSecondMainLemma.Dyadic.UR.CriticalRatio
import LanglandsSecondMainLemma.Dyadic.UR.CriticalReciprocity

/-!
# The ramified critical residual function

Paper `D:UR:resE`, including the full affine term in `D:UR:Ecriticalchar`.
The core and base charts used below are the outputs of `twist` and
`normChoice`. All their ideal domains are retained.
-/

namespace LanglandsSecondMainLemma.Dyadic.UR

noncomputable section
open LanglandsFirstMainLemma
open scoped BigOperators

private theorem ramifiedSum_map_neg {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    (Psi : ContinuousAddChar A) (a : A) : Psi (-a) = (Psi a)⁻¹ :=
  Psi.toAddChar.map_neg_eq_inv a

private theorem ramifiedSum_map_sub {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    (Psi : ContinuousAddChar A) (a b : A) : Psi (a - b) = Psi a / Psi b :=
  Psi.toAddChar.map_sub_eq_div a b

section CriticalCharacter
variable (F E : Type) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

/-- Paper `D:UR:Ecriticalchar`: the actual character on the critical ideal,
where the ordinary half-conductor chart for `thetaE` does not apply.
The two legal inputs are the core chart at depth `e+1` and the base chart
at depth `e + ceil((h+1)/2)`. -/
private theorem ramifiedSum_criticalCharacter
    {t e h : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hdegree : Module.finrank F E = 2)
    (hT : t + 1 = 2 * e + 1) (he : 0 < e) (hh : 0 < h)
    (Psi : ContinuousAddChar F) (c : F) (x : E)
    (chiE thetaE : ContinuousQuasiChar E) (lambda : ContinuousQuasiChar F)
    (hmodel : ∀ (z : E) (hz : z ∈ lattice E ((t / 2 + 1 : ℕ) : ℤ)),
      chiE (principalUnitOf E (t / 2) (-z) (neg_mem_lattice E hz)) =
        tracePullbackAddChar F E Psi (algebraMap F E c * z))
    (htwist : thetaE = chiE * normQuasiChar F E lambda)
    (hbase : ∀ (z : F) (hz : z ∈ lattice F (((t + h) / 2 + 1 : ℕ) : ℤ)),
      lambda (principalUnitOf F ((t + h) / 2) (-z) (neg_mem_lattice F hz)) =
        Psi (norm F E x * z))
    (v : lattice E ((e + h : ℕ) : ℤ)) :
    thetaE (positiveUnitOfLattice E (by omega : 0 < e + h) v) =
      tracePullbackAddChar F E Psi
          (-(algebraMap F E (norm F E x) + algebraMap F E c) * (v : E)) *
        Psi (-norm F E x * norm F E (v : E)) := by
  have htval : t = 2 * e := by omega
  have hvq : -(v : E) ∈ lattice E ((t / 2 + 1 : ℕ) : ℤ) :=
    neg_mem_lattice E (lattice_antitone E (by omega) v.property)
  have hcoreUnit : (positiveUnitOfLattice E (by omega : 0 < e + h) v : Eˣ) =
      principalUnitOf E (t / 2) (-(-(v : E))) (neg_mem_lattice E hvq) := by
    apply Units.ext
    simp only [coe_positiveUnitOfLattice, coe_principalUnitOf, neg_neg]
  have hcore := hmodel (-(v : E)) hvq
  rw [← hcoreUnit] at hcore
  have htrace : trace F E (v : E) ∈
      lattice F (((t + h) / 2 + 1 : ℕ) : ℤ) := by
    obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
    have hv : trace F E (v : E) ∈
        Submodule.map ((trace F E).restrictScalars (ringOfIntegers F))
          ((lattice E ((e + h : ℕ) : ℤ)).restrictScalars (ringOfIntegers F)) :=
      Submodule.mem_map.mpr ⟨(v : E), v.property, rfl⟩
    rw [cyclicPrime_trace_lattice_image_eq F E ht hres pi hpi hgen, hdegree] at hv
    exact lattice_antitone F (by norm_num; omega) hv
  have hnorm : norm F E (v : E) ∈
      lattice F (((t + h) / 2 + 1 : ℕ) : ℤ) := by
    rw [mem_lattice, ord_norm, hres, one_nsmul]
    exact (mem_lattice E).mp (lattice_antitone E (by omega) v.property)
  let y : F := -(trace F E (v : E) + norm F E (v : E))
  have hy : y ∈ lattice F (((t + h) / 2 + 1 : ℕ) : ℤ) :=
    neg_mem_lattice F (add_mem_lattice F htrace hnorm)
  have hnormFormula : norm F E (1 + (v : E)) =
      1 + trace F E (v : E) + norm F E (v : E) := by
    have hn := wildQuadratic_norm_sub F E hdegree 1 (-(v : E))
    have hneg : norm F E (-(v : E)) = norm F E (v : E) := by
      rw [show -(v : E) = algebraMap F E (-1 : F) * (v : E) by simp,
        map_mul, LanglandsFirstMainLemma.norm_algebraMap, hdegree]
      norm_num
    rw [hneg] at hn
    simpa only [Units.val_one, map_one, one_pow, one_mul, sub_neg_eq_add,
      map_neg] using hn
  have hnormUnit : normUnits F E
      (positiveUnitOfLattice E (by omega : 0 < e + h) v : Eˣ) =
      principalUnitOf F ((t + h) / 2) (-y) (neg_mem_lattice F hy) := by
    apply Units.ext
    rw [coe_normUnits, coe_positiveUnitOfLattice, hnormFormula, coe_principalUnitOf]
    dsimp [y]
    ring
  rw [htwist, ContinuousQuasiChar.mul_apply]
  change chiE (positiveUnitOfLattice E (by omega : 0 < e + h) v : Eˣ) *
    lambda (normUnits F E (positiveUnitOfLattice E (by omega : 0 < e + h) v : Eˣ)) = _
  rw [hcore, hnormUnit, hbase y hy]
  simp only [tracePullbackAddChar_apply]
  have htraceScalar (a : F) : trace F E (algebraMap F E a * (v : E)) =
      a * trace F E (v : E) := by
    simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply]
      using (trace F E).map_smul a (v : E)
  rw [← ContinuousAddChar.map_add_eq_mul, ← ContinuousAddChar.map_add_eq_mul]
  congr 1
  simp only [neg_mul, add_mul, map_neg, map_add, mul_neg, htraceScalar]
  dsimp only [y]
  ring

/-- Multiplication by the actual representative carries the critical upper
ideal to the critical norm-reciprocity ideal, with its negative order intact. -/
private def ramifiedCriticalProduct {e h : ℕ} (x : E)
    (hx : ord E x = ((-(h : ℤ)) : WithTop ℤ))
    (v : lattice E ((e + h : ℕ) : ℤ)) : lattice E (e : ℤ) :=
  ⟨x * (v : E), by
    have hxmem : x ∈ lattice E (-(h : ℤ)) := (mem_lattice E).mpr (by rw [hx]; norm_cast)
    exact lattice_antitone E (by push_cast; omega) (mul_mem_lattice E hxmem v.property)⟩

/-- The correction to the ramified stationary coefficient is invisible
on the *critical* ideal. The bound is `3e + h % 2 ≥ 2e+1`, including `e=1`. -/
private theorem ramifiedSum_error
    {t e h : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hdegree : Module.finrank F E = 2)
    (hT : t + 1 = 2 * e + 1) (he : 0 < e)
    (x : E) (hx : ord E x = ((-(h : ℤ)) : WithTop ℤ))
    (c : F) (hc : c ∈ lattice F 0)
    (v : lattice E ((e + h : ℕ) : ℤ)) :
    (algebraMap F E (trace F E x) * (1 - algebraMap F E c / x)) * (v : E) ∈
      lattice E ((t + 1 : ℕ) : ℤ) := by
  let B : ℤ := (((t + 1 : ℕ) : ℤ) - (h : ℤ)) / 2
  have hram : ramificationIndex F E = 2 := by
    have hf := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa only [hdegree, hres, mul_one] using hf.symm
  have hb : trace F E x ∈ lattice F B := by
    obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
    have hb : trace F E x ∈
        Submodule.map ((trace F E).restrictScalars (ringOfIntegers F))
          ((lattice E (-(h : ℤ))).restrictScalars (ringOfIntegers F)) :=
      Submodule.mem_map.mpr ⟨x, (mem_lattice E).mpr (by rw [hx]; norm_cast), rfl⟩
    rw [cyclicPrime_trace_lattice_image_eq F E ht hres pi hpi hgen, hdegree] at hb
    convert hb using 1
    dsimp only [B]
    congr 1
    norm_num
    omega
  have hbE : algebraMap F E (trace F E x) ∈ lattice E (2 * B) := by
    rw [mem_lattice, ord_algebraMap, hram]
    have hb' := add_le_add ((mem_lattice F).mp hb) ((mem_lattice F).mp hb)
    simpa only [two_nsmul, two_mul, WithTop.coe_add] using hb'
  have hcE : algebraMap F E c ∈ lattice E 0 := by
    rw [mem_lattice, ord_algebraMap, hram]
    have hc' := add_le_add ((mem_lattice F).mp hc) ((mem_lattice F).mp hc)
    simpa only [two_nsmul, WithTop.coe_zero, add_zero] using hc'
  have hquot : algebraMap F E c / x ∈ lattice E (h : ℤ) := by
    apply (div_mem_lattice_iff E x _ (-(h : ℤ)) (h : ℤ) hx).mpr
    simpa only [neg_add_cancel] using hcE
  have hu : 1 - algebraMap F E c / x ∈ lattice E 0 :=
    sub_mem_lattice E (by simp) (lattice_antitone E (by omega) hquot)
  exact lattice_antitone E (by dsimp only [B]; push_cast; omega)
    (mul_mem_lattice E (mul_mem_lattice E hbE hu) v.property)

/-- Pointwise comparison in `D:UR:resE` before taking residue sums.
Both sides are the actual critical functions, so their affine terms survive. -/
private theorem ramifiedSum_criticalValue
    {t e h : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hdegree : Module.finrank F E = 2)
    (hchar : residueCharacteristic F = 2)
    (hT : t + 1 = 2 * e + 1) (he : 0 < e) (hh : 0 < h)
    (tau : NormCharacter F E) (htau : tau ≠ 1)
    (Psi : LocalAddCharData F) (PsiE : LocalAddCharData E)
    (hPsiE : PsiE.character = tracePullbackAddChar F E Psi.character)
    (hcondPsiE : PsiE.conductor = -((t + 1 : ℕ) : ℤ))
    (htauchart : ∀ (z : F) (hz : z ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
      tau.1 (principalUnitOf F (t / 2) (-z) (neg_mem_lattice F hz)) = Psi.character z)
    (c : F) (hc : c ∈ lattice F 0) (x : E)
    (hx : ord E x = ((-(h : ℤ)) : WithTop ℤ))
    (chiE thetaE : ContinuousQuasiChar E) (lambda : ContinuousQuasiChar F)
    (hmodel : ∀ (z : E) (hz : z ∈ lattice E ((t / 2 + 1 : ℕ) : ℤ)),
      chiE (principalUnitOf E (t / 2) (-z) (neg_mem_lattice E hz)) =
        tracePullbackAddChar F E Psi.character (algebraMap F E c * z))
    (htwist : thetaE = chiE * normQuasiChar F E lambda)
    (hbase : ∀ (z : F) (hz : z ∈ lattice F (((t + h) / 2 + 1 : ℕ) : ℤ)),
      lambda (principalUnitOf F ((t + h) / 2) (-z) (neg_mem_lattice F hz)) =
        Psi.character (norm F E x * z))
    (Z : Eˣ)
    (herror : (Z : E) - (algebraMap F E (norm F E x) - x + algebraMap F E c) =
      algebraMap F E (trace F E x) * (1 - algebraMap F E c / x))
    (v : lattice E ((e + h : ℕ) : ℤ)) :
    Stationary.normalizedCriticalValue E (canonicalLocalQuasiCharData E thetaE)
        PsiE Z (e + h) (by omega) v =
      ((criticalNormResidual F tau.1 Psi.character he
        (criticalNormLattice F E hres (ramifiedCriticalProduct E x hx v)) : ℂ))⁻¹ := by
  have hcharValue := ramifiedSum_criticalCharacter F E ht hres hdegree hT he hh
    Psi.character c x chiE thetaE lambda hmodel htwist hbase v
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  obtain ⟨e', he', htwo, hT', hrec⟩ := criticalReciprocity F E hchar ht (by omega)
    hres hdegree pi hpi hgen tau htau Psi.character htauchart
      (by rw [hT]; exact ⟨e, by omega⟩)
  have heq : e' = e := by omega
  subst e'
  have hrecValue := (hrec (ramifiedCriticalProduct E x hx v)).2
  have herrorPhase : PsiE.character
      (((Z : E) - (algebraMap F E (norm F E x) - x + algebraMap F E c)) * (v : E)) = 1 := by
    apply PsiE.isConductor.trivial
    rw [hcondPsiE, neg_neg, herror]
    exact ramifiedSum_error F E ht hres hdegree hT he x hx c hc v
  have hphase : PsiE.character (-(Z : E) * (v : E)) =
      PsiE.character (-(algebraMap F E (norm F E x) - x + algebraMap F E c) * (v : E)) := by
    apply div_eq_one.mp
    rw [← ramifiedSum_map_sub]
    have halg : -(Z : E) * (v : E) -
        -(algebraMap F E (norm F E x) - x + algebraMap F E c) * (v : E) =
        -(((Z : E) - (algebraMap F E (norm F E x) - x + algebraMap F E c)) * (v : E)) := by ring
    rw [halg, ramifiedSum_map_neg, herrorPhase, inv_one]
  rw [← Units.val_inv_eq_inv_val, hrecValue]
  simp only [ramifiedCriticalProduct, Units.val_mul, map_mul]
  rw [Stationary.normalizedCriticalValue, canonicalLocalQuasiCharData_character,
    hphase, hcharValue, hPsiE]
  simp only [Units.val_mul, mul_inv_rev]
  have hsplit : tracePullbackAddChar F E Psi.character
      (-(algebraMap F E (norm F E x) - x + algebraMap F E c) * (v : E)) =
      tracePullbackAddChar F E Psi.character (x * (v : E)) *
        tracePullbackAddChar F E Psi.character
          (-(algebraMap F E (norm F E x) + algebraMap F E c) * (v : E)) := by
    rw [← ContinuousAddChar.map_add_eq_mul]
    congr 1
    ring
  rw [hsplit, Units.val_mul]
  simp only [neg_mul, ramifiedSum_map_neg, Units.val_inv_eq_inv_val, inv_inv]
  field_simp

end CriticalCharacter

section ResidualTransport
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

private theorem ramifiedSum_scale_one (Psi : LocalAddCharData L) :
    scaleAddCharData L Psi 1 = Psi := by
  apply LocalAddCharData.eq_of_character_eq
  ext z
  simp only [scaleAddCharData_character_apply, Units.val_one, one_mul]

/-- Evaluate the complete residual function using any integral lift of its
residue coordinate, by the accepted terminal-coset invariance theorem. -/
private theorem ramifiedSum_residual_lift
    (theta : LocalQuasiCharData L) (Psi : LocalAddCharData L)
    (Z : Lˣ) (d : ℕ) (hm : theta.conductor = 2 * d + 1)
    (hlarge : 1 < theta.conductor)
    (hZ : ord L (Z : L) = ((-Psi.conductor - (theta.conductor : ℤ)) : WithTop ℤ))
    (hstationary : Stationary.IsNormalizedStationaryCoefficientAtDepth L theta Psi Z
      (d + 1) (by omega))
    (delta : Lˣ) (hdelta : ord L (delta : L) = ((d : ℤ) : WithTop ℤ))
    (z : ResidueField L) (y : ringOfIntegers L) (hy : residueMap L y = z) :
    Stationary.normalizedResidualFunction L theta Psi 1 Z d hm hlarge delta hdelta z =
      Stationary.normalizedCriticalValue L theta Psi Z d (by omega)
        ⟨(delta : L) * (y : L), by
          have hdmem : (delta : L) ∈ lattice L (d : ℤ) := (mem_lattice L).mpr (by rw [hdelta])
          simpa only [add_zero] using mul_mem_lattice L hdmem ((mem_lattice_zero_iff L).mpr y.property)⟩ := by
  have hdmem : (delta : L) ∈ lattice L (d : ℤ) := (mem_lattice L).mpr (by rw [hdelta])
  let v : lattice L (d : ℤ) := ⟨(delta : L) * (teichmuller L z : L), by
    simpa only [add_zero] using mul_mem_lattice L hdmem
      ((mem_lattice_zero_iff L).mpr (teichmuller L z).property)⟩
  let v' : lattice L (d : ℤ) := ⟨(delta : L) * (y : L), by
    simpa only [add_zero] using mul_mem_lattice L hdmem ((mem_lattice_zero_iff L).mpr y.property)⟩
  have hcongr : CongruentAtDepth ((d + 1 : ℕ) : ℤ) (v : L) (v' : L) := by
    apply (congruentAtDepth_iff_sub_mem_lattice L _ _ _).mpr
    have hdiff : (teichmuller L z : L) - (y : L) ∈ lattice L 1 :=
      (residueMap_eq_residueMap_iff L _ _).mp ((residueMap_teichmuller L z).trans hy.symm)
    have hp := mul_mem_lattice L hdmem hdiff
    simpa only [v, v', mul_sub, Nat.cast_add, Nat.cast_one] using hp
  have hst : Stationary.IsNormalizedStationaryCoefficientAtDepth L theta
      (scaleAddCharData L Psi 1) Z (d + 1) (by omega) := by
    simpa only [ramifiedSum_scale_one] using hstationary
  have hZ' : ord L (Z : L) =
      ((-(scaleAddCharData L Psi 1).conductor - (theta.conductor : ℤ)) : WithTop ℤ) := by
    simpa only [ramifiedSum_scale_one] using hZ
  have heq := Stationary.normalizedCriticalValue_odd_eq_of_congruent L theta Psi 1 Z d
    hm hlarge hZ' hst v v' hcongr
  rw [ramifiedSum_scale_one] at heq
  have hu : (lamprechtHasseUnit L theta d hm hlarge delta hdelta
      (teichmuller L z : L) ((mem_lattice_zero_iff L).mpr (teichmuller L z).property) : Lˣ) =
      positiveUnitOfLattice L (by omega : 0 < d) v := by
    apply Units.ext
    simp only [lamprechtHasseUnit_coe, coe_positiveUnitOfLattice, v]
  simpa only [Stationary.normalizedResidualFunction, ramifiedSum_scale_one,
    Stationary.normalizedCriticalValue, hu, v, v', mul_assoc] using heq

/-- A change of critical element preserves the full residual factor. -/
private theorem ramifiedSum_residual_independent
    (theta : LocalQuasiCharData L) (Psi : LocalAddCharData L)
    (Z : Lˣ) (d : ℕ) (hm : theta.conductor = 2 * d + 1)
    (hlarge : 1 < theta.conductor)
    (hZ : ord L (Z : L) = ((-Psi.conductor - (theta.conductor : ℤ)) : WithTop ℤ))
    (hstationary : Stationary.IsNormalizedStationaryCoefficientAtDepth L theta Psi Z
      (d + 1) (by omega))
    (delta delta' : Lˣ)
    (hdelta : ord L (delta : L) = ((d : ℤ) : WithTop ℤ))
    (hdelta' : ord L (delta' : L) = ((d : ℤ) : WithTop ℤ)) :
    Stationary.normalizedResidualFactor L theta Psi 1 Z d hm hlarge delta hdelta =
      Stationary.normalizedResidualFactor L theta Psi 1 Z d hm hlarge delta' hdelta' := by
  have hst : Stationary.IsNormalizedStationaryCoefficientAtDepth L theta
      (scaleAddCharData L Psi 1) Z (d + 1) (by omega) := by
    simpa only [ramifiedSum_scale_one] using hstationary
  have hZ' : ord L (Z : L) =
      ((-(scaleAddCharData L Psi 1).conductor - (theta.conductor : ℤ)) : WithTop ℤ) := by
    simpa only [ramifiedSum_scale_one] using hZ
  have hf := (Stationary.normalizedFactor L theta Psi 1 Z d 1 (by omega) hm hlarge hZ' hst).2 rfl
  exact mul_left_cancel₀ (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))
    ((hf delta hdelta).symm.trans (hf delta' hdelta'))

/-- With coefficient one and opposite additive/multiplicative conductors,
the full normalized lower sum has unit magnitude. No Gauss-factor value is
assumed, and quasi-characters need only be unitary on local units. -/
private theorem ramifiedSum_lower_norm
    (theta : LocalQuasiCharData L) (Psi : LocalAddCharData L)
    (d : ℕ) (hm : theta.conductor = 2 * d + 1)
    (hlarge : 1 < theta.conductor) (hPsi : Psi.conductor = -(theta.conductor : ℤ))
    (hstationary : Stationary.IsNormalizedStationaryCoefficientAtDepth L theta Psi 1
      (d + 1) (by omega))
    (delta : Lˣ) (hdelta : ord L (delta : L) = ((d : ℤ) : WithTop ℤ)) :
    ‖Stationary.normalizedResidualFactor L theta Psi 1 1 d hm hlarge delta hdelta‖ = 1 := by
  let Gamma : AdmissibleGamma L theta Psi := ⟨1, by simp [hPsi]⟩
  have hlocal : ‖localConstant L theta.character Psi.character‖ = 1 := by
    rw [localConstant_isDeltaFinite L theta Psi Gamma, deltaFinite]
    simp only [Gamma, map_one, Units.val_one, one_mul, phase_norm]
  have hZ : ord L ((1 : Lˣ) : L) =
      ((-(scaleAddCharData L Psi 1).conductor - (theta.conductor : ℤ)) : WithTop ℤ) := by
    rw [ramifiedSum_scale_one, hPsi]
    norm_cast
    simp
  have hst : Stationary.IsNormalizedStationaryCoefficientAtDepth L theta
      (scaleAddCharData L Psi 1) 1 (d + 1) (by omega) := by
    simpa only [ramifiedSum_scale_one] using hstationary
  have hf := (Stationary.normalizedFactor L theta Psi 1 1 d 1 (by omega) hm hlarge hZ hst).2
    rfl delta hdelta
  rw [hf, norm_mul, norm_mul, ramifiedSum_scale_one, localAddChar_norm_eq_one, mul_one] at hlocal
  have hu : ((- (1 : Lˣ) * 1)⁻¹) ∈ unitFiltration L 0 := by
    rw [mem_unitFiltration_zero]
    simp
  rw [quasiChar_norm_eq_one_of_mem_unitFiltration_zero theta ⟨_, hu⟩, one_mul] at hlocal
  exact hlocal

end ResidualTransport

section ResidueNormTransport
variable (F E : Type) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
/-- Sum a proved pointwise comparison by the residue norm bijection. The
critical elements are constructed together, and the exact norm identity
uses multiplicativity of Teichmüller lifts. -/
private theorem ramifiedSum_sum_of_pointwise
    {e h : ℕ} (he : 0 < e)
    (hres : residueDegree F E = 1) (hdegree : Module.finrank F E = 2)
    (hchar : residueCharacteristic F = 2)
    (thetaE : LocalQuasiCharData E) (thetaTau : LocalQuasiCharData F)
    (PsiE : LocalAddCharData E) (Psi : LocalAddCharData F)
    (hmE : thetaE.conductor = 2 * (e + h) + 1)
    (hmTau : thetaTau.conductor = 2 * e + 1)
    (hPsi : Psi.conductor = -(thetaTau.conductor : ℤ))
    (Z : Eˣ)
    (hZ : ord E (Z : E) = ((-PsiE.conductor - (thetaE.conductor : ℤ)) : WithTop ℤ))
    (hstationaryE : Stationary.IsNormalizedStationaryCoefficientAtDepth E thetaE PsiE Z
      (e + h + 1) (by omega))
    (hstationaryTau : Stationary.IsNormalizedStationaryCoefficientAtDepth F thetaTau Psi 1
      (e + 1) (by omega))
    (x : E) (hx : ord E x = ((-(h : ℤ)) : WithTop ℤ))
    (hpoint : ∀ v : lattice E ((e + h : ℕ) : ℤ),
      Stationary.normalizedCriticalValue E thetaE PsiE Z (e + h) (by omega) v =
        (Stationary.normalizedCriticalValue F thetaTau Psi 1 e he
          (criticalNormLattice F E hres (ramifiedCriticalProduct E x hx v)))⁻¹)
    (deltaE : Eˣ) (deltaTau : Fˣ)
    (hdeltaE : ord E (deltaE : E) = (((e + h : ℕ) : ℤ) : WithTop ℤ))
    (hdeltaTau : ord F (deltaTau : F) = ((e : ℤ) : WithTop ℤ)) :
    Stationary.normalizedResidualFactor E thetaE PsiE 1 Z (e + h) hmE (by omega)
        deltaE hdeltaE =
      (Stationary.normalizedResidualFactor F thetaTau Psi 1 1 e hmTau (by omega)
        deltaTau hdeltaTau)⁻¹ := by
  letI := residueFieldFintype F
  letI := residueFieldFintype E
  letI : CharP (ResidueField F) 2 := ringChar.of_eq hchar
  let r := criticalNormResidueEquiv F E hres
  let fr := frobeniusEquiv (ResidueField F) 2
  have hx0 : x ≠ 0 := (ord_ne_top_iff E).mp (by rw [hx]; simp)
  let xu : Eˣ := Units.mk0 x hx0
  obtain ⟨w, hw⟩ := exists_ord_eq E (e : ℤ)
  have hw0 : w ≠ 0 := (ord_ne_top_iff E).mp (by rw [hw]; simp)
  let wu : Eˣ := Units.mk0 w hw0
  let D : Eˣ := wu / xu
  let Dtau : Fˣ := normUnits F E wu
  have hD : ord E (D : E) = (((e + h : ℕ) : ℤ) : WithTop ℤ) := by
    simp only [D, Units.val_div_eq_div_val, wu, xu, Units.val_mk0, ord_div, hw, hx]
    norm_cast
    omega
  have hDtau : ord F (Dtau : F) = ((e : ℤ) : WithTop ℤ) := by
    dsimp only [Dtau]
    rw [coe_normUnits, ord_norm, hres, one_nsmul]
    exact hw
  have hZtau : ord F ((1 : Fˣ) : F) =
      ((-Psi.conductor - (thetaTau.conductor : ℤ)) : WithTop ℤ) := by
    rw [hPsi]
    norm_cast
    simp
  let HE := Stationary.normalizedResidualFunction E thetaE PsiE 1 Z (e + h) hmE
    (by omega) D hD
  let HT := Stationary.normalizedResidualFunction F thetaTau Psi 1 1 e hmTau
    (by omega) Dtau hDtau
  have hvalues (z : ResidueField F) : HE (r z) = (HT (fr z))⁻¹ := by
    let y : ringOfIntegers E := algebraMap (ringOfIntegers F) (ringOfIntegers E)
      (teichmuller F z)
    have hy : residueMap E y = r z := by
      change residueMap E (algebraMap (ringOfIntegers F) (ringOfIntegers E) (teichmuller F z)) =
        extensionResidueMap F E z
      rw [← IsLocalRing.ResidueField.algebraMap_residue, residueMap_teichmuller]
    have hDy : (D : E) * (y : E) ∈ lattice E ((e + h : ℕ) : ℤ) := by
      have hd : (D : E) ∈ lattice E ((e + h : ℕ) : ℤ) := (mem_lattice E).mpr (by rw [hD])
      simpa only [add_zero] using mul_mem_lattice E hd ((mem_lattice_zero_iff E).mpr y.property)
    let v : lattice E ((e + h : ℕ) : ℤ) := ⟨(D : E) * (y : E), hDy⟩
    have hnorm : norm F E (x * (v : E)) = (Dtau : F) * (teichmuller F (fr z) : F) := by
      have hycoe : (y : E) = algebraMap F E (teichmuller F z : F) := by
        change algebraMap (ringOfIntegers E) E
          (algebraMap (ringOfIntegers F) (ringOfIntegers E) (teichmuller F z)) =
          algebraMap F E (algebraMap (ringOfIntegers F) F (teichmuller F z))
        rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      have hxv : x * (v : E) = w * algebraMap F E (teichmuller F z : F) := by
        dsimp only [v]
        rw [hycoe]
        simp only [D, Units.val_div_eq_div_val, wu, xu, Units.val_mk0]
        field_simp
      rw [hxv, map_mul, LanglandsFirstMainLemma.norm_algebraMap, hdegree]
      simp only [Dtau, coe_normUnits, wu, Units.val_mk0]
      congr 1
      simp only [fr, frobeniusEquiv_def, map_pow, SubmonoidClass.coe_pow]
    have hE := ramifiedSum_residual_lift E thetaE PsiE Z (e + h) hmE (by omega)
      hZ hstationaryE D hD (r z) y hy
    have hF := ramifiedSum_residual_lift F thetaTau Psi 1 e hmTau (by omega)
      hZtau hstationaryTau Dtau hDtau (fr z) (teichmuller F (fr z))
      (residueMap_teichmuller F (fr z))
    change HE (r z) = _ at hE
    change HT (fr z) = _ at hF
    rw [hE, hpoint, hF]
    congr 2
    apply Subtype.ext
    exact hnorm
  have hsum : (∑ z : ResidueField E, HE z) = ∑ z : ResidueField F, (HT z)⁻¹ := by
    calc
      _ = ∑ z : ResidueField F, HE (r z) := (r.toEquiv.sum_comp HE).symm
      _ = ∑ z : ResidueField F, (HT (fr z))⁻¹ := Finset.sum_congr rfl (fun z _ => hvalues z)
      _ = _ := fr.toEquiv.sum_comp (fun z => (HT z)⁻¹)
  have hHTnorm (z : ResidueField F) : ‖HT z‖ = 1 := by
    dsimp only [HT, Stationary.normalizedResidualFunction]
    rw [ramifiedSum_scale_one, norm_mul, localAddChar_norm_eq_one, one_mul, norm_inv]
    have hu := (lamprechtHasseUnit F thetaTau e hmTau (by omega) Dtau hDtau
      (teichmuller F z : F) ((mem_lattice_zero_iff F).mpr (teichmuller F z).property)).property
    rw [quasiChar_norm_eq_one_of_mem_unitFiltration_zero thetaTau
      ⟨_, unitFiltration_antitone F (Nat.zero_le e) hu⟩, inv_one]
  have hfactor : Stationary.normalizedResidualFactor E thetaE PsiE 1 Z (e + h) hmE
      (by omega) D hD =
      (starRingEnd ℂ) (Stationary.normalizedResidualFactor F thetaTau Psi 1 1 e hmTau
        (by omega) Dtau hDtau) := by
    rw [Stationary.normalizedResidualFactor, Stationary.normalizedResidualFactor,
      residueCard_eq_of_residueDegree_eq_one F E hres]
    change _ * (∑ z : ResidueField E, HE z) = (starRingEnd ℂ) (_ * ∑ z : ResidueField F, HT z)
    rw [hsum, map_mul, map_inv₀, Complex.conj_ofReal, map_sum]
    congr 1
    exact Finset.sum_congr rfl (fun z _ => Complex.inv_eq_conj (hHTnorm z))
  have hnorm := ramifiedSum_lower_norm F thetaTau Psi e hmTau (by omega) hPsi
    hstationaryTau Dtau hDtau
  rw [← Complex.inv_eq_conj hnorm] at hfactor
  rw [ramifiedSum_residual_independent E thetaE PsiE Z (e + h) hmE (by omega)
    hZ hstationaryE deltaE D hdeltaE hD]
  rw [ramifiedSum_residual_independent F thetaTau Psi 1 e hmTau (by omega)
    hZtau hstationaryTau deltaTau Dtau hdeltaTau hDtau]
  exact hfactor

end ResidueNormTransport

section ActualFactors
variable (F U E : Type) [Field F] [Field U] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The ramified residual factor is the reciprocal** (`D:UR:resE`).

The core decomposition is the one constructed by `twist`; the full base
chart for the *same* `x` is furnished by `coefficients_exists`, and its
corrected representatives by `conjugatedNorm_of_coefficients`. The charts
are used on their original ideals. `R` is the accepted actual-representative
record, not a new stationary model or an assumed residual identity.

This compares exactly the two factors in `CriticalRatioIdentity`, for
arbitrary critical elements and the original trace-compatible additive
characters. Both affine terms are retained by `ramifiedSum_criticalValue`.
No value of either Gauss factor is prescribed. -/
theorem ramifiedSum
    (hchar : residueCharacteristic F = 2)
    {t h : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hdegree : Module.finrank F E = 2)
    (hhpos : 0 < h) (hh : h ≤ t) (hodd : Odd (t + 1))
    (tau : NormCharacter F E) (htau : tau ≠ 1)
    (psiF : LocalAddCharData F) (psiE : LocalAddCharData E)
    (hpsiE : psiE.character = tracePullbackAddChar F E psiF.character)
    (alpha : Fˣ)
    (hPsi : (scaleAddCharData F psiF alpha).conductor = -((t + 1 : ℕ) : ℤ))
    (htauchart : ∀ (z : F) (hz : z ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
      tau.1 (principalUnitOf F (t / 2) (-z) (neg_mem_lattice F hz)) =
        (scaleAddCharData F psiF alpha).character z)
    (c : F) (hc : c ∈ lattice F 0) (d : U) (x : E)
    (hx : ord E x = ((-(h : ℤ)) : WithTop ℤ))
    (thetaU : ContinuousQuasiChar U) (chiE thetaE : ContinuousQuasiChar E)
    (lambda : ContinuousQuasiChar F)
    (hmodel : ∀ (z : E) (hz : z ∈ lattice E ((t / 2 + 1 : ℕ) : ℤ)),
      chiE (principalUnitOf E (t / 2) (-z) (neg_mem_lattice E hz)) =
        tracePullbackAddChar F E (scaleAddCharData F psiF alpha).character
          (algebraMap F E c * z))
    (htwist : thetaE = chiE * normQuasiChar F E lambda)
    (hbase : ∀ (z : F) (hz : z ∈ lattice F (((t + h) / 2 + 1 : ℕ) : ℤ)),
      lambda (principalUnitOf F ((t + h) / 2) (-z) (neg_mem_lattice F hz)) =
        (scaleAddCharData F psiF alpha).character (norm F E x * z))
    (hcondE : IsMultiplicativeConductor E thetaE (t + 1 + 2 * h))
    (R : ConjugatedNormData F U E thetaU thetaE
      (scaleAddCharData F psiF alpha).character c d x t h)
    (deltaE : Eˣ) (deltaTau : Fˣ)
    (hdeltaE : ord E (deltaE : E) =
      (((canonicalLocalQuasiCharData E thetaE).conductor / 2 : ℕ) : WithTop ℤ))
    (hdeltaTau : ord F (deltaTau : F) =
      (((canonicalLocalQuasiCharData F tau.1).conductor / 2 : ℕ) : WithTop ℤ)) :
    ∃ (largeE : 1 < (canonicalLocalQuasiCharData E thetaE).conductor)
      (largeTau : 1 < (canonicalLocalQuasiCharData F tau.1).conductor),
    criticalResidualFactor E (canonicalLocalQuasiCharData E thetaE) psiE
        (Units.map (algebraMap F E).toMonoidHom alpha) R.ZE largeE deltaE hdeltaE =
      (criticalResidualFactor F (canonicalLocalQuasiCharData F tau.1) psiF alpha 1
        largeTau deltaTau hdeltaTau)⁻¹ := by
  let Psi := scaleAddCharData F psiF alpha
  let alphaE := Units.map (algebraMap F E).toMonoidHom alpha
  let PsiE := scaleAddCharData E psiE alphaE
  let chi := canonicalLocalQuasiCharData E thetaE
  let chiTau := canonicalLocalQuasiCharData F tau.1
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  obtain ⟨e, he, _, hT, _⟩ := criticalReciprocity F E hchar ht (by omega)
    hres hdegree pi hpi hgen tau htau Psi.character htauchart hodd
  have hmE : chi.conductor = 2 * (e + h) + 1 := by
    have hm := chi.isConductor.unique hcondE
    omega
  have hmTau : chiTau.conductor = 2 * e + 1 :=
    (chiTau.isConductor.unique
      (ramifiedNormCharacter_conductor F E ht hres pi hpi hgen tau htau)).trans hT
  have largeE : 1 < chi.conductor := by omega
  have largeTau : 1 < chiTau.conductor := by omega
  refine ⟨largeE, largeTau, ?_⟩
  have htrace : PsiE.character = tracePullbackAddChar F E Psi.character := by
    ext z
    simp only [PsiE, Psi, scaleAddCharData_character_apply, hpsiE,
      tracePullbackAddChar_apply, alphaE, Units.coe_map]
    congr 2
    change trace F E (algebraMap F E (alpha : F) * z) = (alpha : F) * trace F E z
    simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply]
      using (trace F E).map_smul (alpha : F) z
  have hPsiEeq : PsiE = ⟨tracePullbackAddChar F E Psi.character,
      -((t + 1 : ℕ) : ℤ), R.additiveConductorE⟩ :=
    LocalAddCharData.eq_of_character_eq htrace
  have hPsiEcond : PsiE.conductor = -((t + 1 : ℕ) : ℤ) := by rw [hPsiEeq]
  have hstationaryE : Stationary.IsNormalizedStationaryCoefficientAtDepth E chi PsiE R.ZE
      (e + h + 1) (by omega) := by
    rw [hPsiEeq]
    convert R.stationaryE using 1
    omega
  have hstationaryTau : Stationary.IsNormalizedStationaryCoefficientAtDepth F chiTau Psi 1
      (e + 1) (by omega) := by
    intro z
    have hz : (z : F) ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ) := by
      have hq : t / 2 + 1 = e + 1 := by omega
      simpa only [hq] using z.property
    have hu : (positiveUnitOfLattice F (by omega : 0 < e + 1) (-z) : Fˣ) =
        principalUnitOf F (t / 2) (-(z : F)) (neg_mem_lattice F hz) := by
      apply Units.ext
      simp only [coe_positiveUnitOfLattice, Submodule.coe_neg, coe_principalUnitOf]
    simpa only [hu, Units.val_one, one_mul, chiTau, canonicalLocalQuasiCharData_character]
      using htauchart (z : F) hz
  have hZ : ord E (R.ZE : E) =
      ((-PsiE.conductor - (chi.conductor : ℤ)) : WithTop ℤ) := by
    rw [R.orderE, hPsiEcond, hmE]
    norm_cast
    omega
  have hPsiTau : Psi.conductor = -(chiTau.conductor : ℤ) := by
    rw [hmTau]
    exact hPsi.trans (by congr 1; omega)
  have hdE : ord E (deltaE : E) = (((e + h : ℕ) : ℤ) : WithTop ℤ) := by
    have hd : chi.conductor / 2 = e + h := by omega
    change ord E (deltaE : E) = ((chi.conductor / 2 : ℕ) : WithTop ℤ) at hdeltaE
    rw [hd] at hdeltaE
    exact_mod_cast hdeltaE
  have hdTau : ord F (deltaTau : F) = ((e : ℤ) : WithTop ℤ) := by
    have hd : chiTau.conductor / 2 = e := by omega
    change ord F (deltaTau : F) = ((chiTau.conductor / 2 : ℕ) : WithTop ℤ) at hdeltaTau
    rw [hd] at hdeltaTau
    exact_mod_cast hdeltaTau
  have hpoint (v : lattice E ((e + h : ℕ) : ℤ)) :
      Stationary.normalizedCriticalValue E chi PsiE R.ZE (e + h) (by omega) v =
        (Stationary.normalizedCriticalValue F chiTau Psi 1 e he
          (criticalNormLattice F E hres (ramifiedCriticalProduct E x hx v)))⁻¹ := by
    have hp := ramifiedSum_criticalValue F E ht hres hdegree hchar hT he hhpos tau htau
      Psi PsiE htrace hPsiEcond htauchart c hc x hx chiE thetaE lambda hmodel htwist
      hbase R.ZE R.errorE v
    simpa only [Stationary.normalizedCriticalValue, criticalNormResidual, chi, chiTau,
      canonicalLocalQuasiCharData_character, Units.val_one, neg_one_mul, Units.val_mul,
      Units.val_inv_eq_inv_val] using hp
  have hs := ramifiedSum_sum_of_pointwise F E he hres hdegree hchar chi chiTau PsiE Psi
    hmE hmTau hPsiTau R.ZE hZ hstationaryE hstationaryTau x hx hpoint
    deltaE deltaTau hdE hdTau
  have hparE : chi.conductor % 2 ≠ 0 := by omega
  have hparTau : chiTau.conductor % 2 ≠ 0 := by omega
  have hhalfE : chi.conductor / 2 = e + h := by omega
  have hhalfTau : chiTau.conductor / 2 = e := by omega
  change criticalResidualFactor E chi psiE alphaE R.ZE largeE deltaE hdeltaE =
    (criticalResidualFactor F chiTau psiF alpha 1 largeTau deltaTau hdeltaTau)⁻¹
  simp only [criticalResidualFactor, dif_neg hparE, dif_neg hparTau, hhalfE, hhalfTau]
  simpa only [Stationary.normalizedResidualFactor, Stationary.normalizedResidualFunction,
    ramifiedSum_scale_one, PsiE, Psi] using hs

end ActualFactors

end
end LanglandsSecondMainLemma.Dyadic.UR
