import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.PrimeCyclicPreparation
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Local.TraceIdeals
import LanglandsSecondMainLemma.Basic.Characters

namespace LanglandsSecondMainLemma.Dyadic

open LanglandsFirstMainLemma

noncomputable section

/-- The least integral stationary depth, `ceil(q/2)`. -/
def stationaryCovectorDepth (q : ℕ) : ℕ := (q + 1) / 2

private theorem stationaryCovectorDepth_spec {q : ℕ} (hq : 1 < q) :
    IsLamprechtStationaryDepth q (stationaryCovectorDepth q) := by
  constructor
  · exact hq
  · simp only [stationaryCovectorDepth]
    omega
  · simp only [stationaryCovectorDepth]
    omega

/-- A field-valued stationary covector at a named multiplicative and
additive conductor.  The exact order is retained together with the
linearization on the whole stationary lattice. -/
structure IsStationaryCovectorAtDepth
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : ContinuousQuasiChar E) (psi : ContinuousAddChar E)
    (q : ℕ) (npsi : ℤ) (r : ℕ) (b : Eˣ) : Prop where
  multiplicativeConductor : IsMultiplicativeConductor E chi q
  additiveConductor : IsAdditiveConductor E psi npsi
  depth : IsLamprechtStationaryDepth q r
  order : ord E (b : E) = ((-(q : ℤ) - npsi : ℤ) : WithTop ℤ)
  linearization : ∀ z : lattice E (r : ℤ),
    chi (positiveUnitOfLattice E depth.pos z) =
      psi ((b : E) * (z : E))

/-- An actual representative of FML's stationary numerator class, divided
by its admissible denominator, gives a stationary covector in the
field-valued sense above.  Thus the covector predicate is a bridge from the
released FML quotient class, not an independent stationary model. -/
theorem isStationaryCovectorAtDepth_of_stationaryNumeratorClass
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    {r : ℕ} (hr : IsLamprechtStationaryDepth chi.conductor r)
    (Gamma : Eˣ)
    (hGamma : ord E (Gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (c : lattice E ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk E
        (sub_le_sub_left hr.int_le_conductor (chi.conductor : ℤ)) c =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        hr Gamma hGamma)
    (b : Eˣ) (hb : (b : E) = (c : E) / (Gamma : E)) :
    IsStationaryCovectorAtDepth E chi.character psi.character
      chi.conductor psi.conductor r b := by
  refine
    { multiplicativeConductor := chi.isConductor
      additiveConductor := psi.isConductor
      depth := hr
      order := ?_
      linearization := ?_ }
  · have hcOrder := stationaryNumeratorClass_representative_ord
      E chi psi (chi.conductor : ℤ) hr Gamma hGamma c hc
    norm_num at hcOrder
    rw [hb, ord_div, hcOrder, hGamma]
    norm_num
    rw [sub_eq_add_neg]
    ac_rfl
  · intro z
    have hlin := stationaryNumeratorClass_linearization
      E chi psi (chi.conductor : ℤ) hr Gamma hGamma c hc z
    rw [hlin]
    congr 1
    rw [hb]
    field_simp [Units.ne_zero Gamma]

private theorem additive_annihilator
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (psi : ContinuousAddChar E) (npsi r : ℤ)
    (hpsi : IsAdditiveConductor E psi npsi) {c : E}
    (hc : ∀ z : E, z ∈ lattice E r → psi (c * z) = 1) :
    c ∈ lattice E (-npsi - r) := by
  let psiData : LocalAddCharData E :=
    continuousAddChar_toData E psi npsi hpsi
  have hGamma : ord E (1 : E) =
      (((-npsi) + psiData.conductor : ℤ) : WithTop ℤ) := by
    simp [psiData]
  apply (lamprechtAnnihilatorLeft E psiData hGamma).1
  intro z hz
  simpa [psiData] using hc z hz

private theorem quadratic_norm_one_add
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K]
    (hdegree : Module.finrank F K = 2) (z : K) :
    Algebra.norm F (1 + z) =
      1 + Algebra.trace F K z + Algebra.norm F z := by
  rw [norm_one_add_eq_one_add_sum_elementarySymmetric, hdegree]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, elementarySymmetric_one]
  change 1 + (Algebra.trace F K z + elementarySymmetric F K 2 z) = _
  rw [← hdegree, elementarySymmetric_finrank]
  ring

/-- Ramified clause of Paper 10.17.  The two stationary hypotheses retain
their exact covector orders and quantify over the complete half-conductor
lattices. -/
theorem highCovectors
    (F L : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra F L] [ValuativeExtension F L]
    [Module.Free F L] [Module.Finite F L] [PrimeCyclicExtension F L]
    (chi : ContinuousQuasiChar F) (psi : ContinuousAddChar F)
    (n : ℕ) (npsi : ℤ)
    (hdegree : Module.finrank F L = 2)
    (hram : ramificationIndex F L = 2)
    (hhigh : differentExponent F L < n)
    (bF : Fˣ) (bL : Lˣ)
    (hbF : IsStationaryCovectorAtDepth F chi psi n npsi
      (stationaryCovectorDepth n) bF)
    (hbL : IsStationaryCovectorAtDepth L
      (normQuasiChar F L chi) (tracePullbackAddChar F L psi)
      (2 * n - differentExponent F L)
      (2 * npsi + (differentExponent F L : ℤ))
      (stationaryCovectorDepth (2 * n - differentExponent F L)) bL) :
    bL / Units.map (algebraMap F L) bF ∈
      unitFiltration L (n - differentExponent F L) := by
  let P : PrimeCyclicPreparation F L :=
    primeCyclicPreparation F L (by omega)
  have hdeltaPos : 0 < differentExponent F L := by
    rw [differentExponent_wildQuadratic_eq F L P.ht hdegree
      P.piK P.hpiK P.hgen]
    omega
  have hnPos : 0 < n := by omega
  have hnLarge : 1 < n := by omega
  let sF : ℕ := stationaryCovectorDepth n
  let qL : ℕ := 2 * n - differentExponent F L
  let sL : ℕ := stationaryCovectorDepth qL
  have hsFPos : 0 < sF := (stationaryCovectorDepth_spec hnLarge).pos
  have hqLLarge : 1 < qL := by
    dsimp only [qL]
    omega
  have hsL_le_n : sL ≤ n := by
    dsimp only [sL, qL, stationaryCovectorDepth]
    omega
  have hpsiL : IsAdditiveConductor L (tracePullbackAddChar F L psi)
      (2 * npsi + (differentExponent F L : ℤ)) := by
    have h := Local.additiveConductor_trace_fml F L P.hres
      hbF.additiveConductor
    rw [hram] at h
    change IsAdditiveConductor L psi.compTrace
      (2 * npsi + (differentExponent F L : ℤ))
    simpa using h
  have hwhole : ∀ z : L, z ∈ lattice L (n : ℤ) →
      tracePullbackAddChar F L psi
        (((bL : L) - algebraMap F L (bF : F)) * z) = 1 := by
    intro z hz
    let zN : lattice L (n : ℤ) := ⟨z, hz⟩
    have htraceImage : Algebra.trace F L z ∈
        lattice F (((n : ℤ) + (differentExponent F L : ℤ)) / 2) := by
      have hzImage : Algebra.trace F L z ∈
          Submodule.map
            ((Algebra.trace F L).restrictScalars (ringOfIntegers F))
            ((lattice L (n : ℤ)).restrictScalars (ringOfIntegers F)) :=
        Submodule.mem_map.mpr ⟨z, hz, rfl⟩
      rw [Local.traceIdeal_eq_fml F L P.hres, hram] at hzImage
      simpa using hzImage
    have hsFTrace : (sF : ℤ) ≤
        ((n : ℤ) + (differentExponent F L : ℤ)) / 2 := by
      dsimp only [sF, stationaryCovectorDepth]
      omega
    have htrace : Algebra.trace F L z ∈ lattice F (sF : ℤ) :=
      lattice_antitone F hsFTrace htraceImage
    have hnormN : Algebra.norm F z ∈ lattice F (n : ℤ) := by
      rw [mem_lattice, ord_norm, P.hres, one_nsmul]
      exact hz
    have hsF_le_n : (sF : ℤ) ≤ (n : ℤ) := by
      dsimp only [sF, stationaryCovectorDepth]
      omega
    have hnorm : Algebra.norm F z ∈ lattice F (sF : ℤ) :=
      lattice_antitone F hsF_le_n hnormN
    let w : lattice F (sF : ℤ) :=
      ⟨Algebra.trace F L z + Algebra.norm F z,
        add_mem_lattice F htrace hnorm⟩
    have hnormUnit :
        continuousNormUnits F L
            (positiveUnitOfLattice L hnPos zN) =
          positiveUnitOfLattice F hsFPos w := by
      apply Units.ext
      simp only [coe_continuousNormUnits, coe_positiveUnitOfLattice]
      rw [quadratic_norm_one_add F L hdegree]
      simp [w, zN]
      ring
    have hnormTerm :
        psi ((bF : F) * Algebra.norm F z) = 1 := by
      apply hbF.additiveConductor.trivial
      have hbFLattice : (bF : F) ∈ lattice F (-(n : ℤ) - npsi) := by
        rw [mem_lattice, hbF.order]
      have hprod := mul_mem_lattice F hbFLattice hnormN
      simpa only [show (-(n : ℤ) - npsi) + (n : ℤ) = -npsi by omega]
        using hprod
    have hbase :
        normQuasiChar F L chi (positiveUnitOfLattice L hnPos zN) =
          tracePullbackAddChar F L psi
            (algebraMap F L (bF : F) * z) := by
      rw [normQuasiChar_apply, hnormUnit]
      have hlin := hbF.linearization w
      rw [hlin]
      rw [tracePullbackAddChar_apply]
      have htraceMul : Algebra.trace F L (algebraMap F L (bF : F) * z) =
          (bF : F) * Algebra.trace F L z := by
        rw [← Algebra.smul_def, map_smul]
        simp
      rw [htraceMul]
      change psi ((bF : F) *
          (Algebra.trace F L z + Algebra.norm F z)) = _
      rw [mul_add, ContinuousAddChar.map_add_eq_mul, hnormTerm, mul_one]
    have hzL : z ∈ lattice L (sL : ℤ) :=
      lattice_antitone L (by exact_mod_cast hsL_le_n) hz
    let zL : lattice L (sL : ℤ) := ⟨z, hzL⟩
    have hupper := hbL.linearization zL
    have hunitEq :
        (positiveUnitOfLattice L hbL.depth.pos zL : Lˣ) =
          (positiveUnitOfLattice L hnPos zN : Lˣ) := by
      apply Units.ext
      simp [zL, zN]
    have hupper' :
        normQuasiChar F L chi (positiveUnitOfLattice L hnPos zN) =
          tracePullbackAddChar F L psi ((bL : L) * z) := by
      rw [← hunitEq]
      exact hupper
    rw [hbase] at hupper'
    rw [sub_mul]
    change (tracePullbackAddChar F L psi).toAddChar
      ((bL : L) * z - algebraMap F L (bF : F) * z) = 1
    rw [
      (tracePullbackAddChar F L psi).toAddChar.map_sub_eq_div]
    change (tracePullbackAddChar F L psi).toAddChar
      (algebraMap F L (bF : F) * z) =
        (tracePullbackAddChar F L psi).toAddChar ((bL : L) * z) at hupper'
    rw [← hupper']
    simp
  have hdiff : (bL : L) - algebraMap F L (bF : F) ∈
      lattice L (-(2 * npsi + (differentExponent F L : ℤ)) - (n : ℤ)) :=
    additive_annihilator L (tracePullbackAddChar F L psi)
      (2 * npsi + (differentExponent F L : ℤ))
      (n : ℤ) hpsiL hwhole
  have hbFMapOrder : ord L (algebraMap F L (bF : F)) =
      ((-2 * (n : ℤ) - 2 * npsi : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hram, hbF.order]
    rw [← WithTop.coe_nsmul]
    congr 1
    norm_num [nsmul_eq_mul]
    ring
  have hratio :
      ((bL : L) - algebraMap F L (bF : F)) /
          algebraMap F L (bF : F) ∈
            lattice L ((n - differentExponent F L : ℕ) : ℤ) := by
    apply (div_mem_lattice_iff L (algebraMap F L (bF : F))
      ((bL : L) - algebraMap F L (bF : F))
      (-2 * (n : ℤ) - 2 * npsi)
      ((n - differentExponent F L : ℕ) : ℤ)
      hbFMapOrder).2
    have hdepth :
        (-2 * (n : ℤ) - 2 * npsi) +
            ((n - differentExponent F L : ℕ) : ℤ) =
          -(2 * npsi + (differentExponent F L : ℤ)) - (n : ℤ) := by
      rw [Nat.cast_sub hhigh.le]
      ring
    simpa only [hdepth] using hdiff
  have hkPos : 0 < n - differentExponent F L := by omega
  rw [show n - differentExponent F L =
      (n - differentExponent F L - 1) + 1 by omega,
    mem_unitFiltration_succ_iff_sub_mem_lattice]
  have hbFMapNe : algebraMap F L (bF : F) ≠ 0 := by simp
  simpa only [Nat.sub_add_cancel
      (show 1 ≤ n - differentExponent F L by omega),
    Units.val_div_eq_div_val, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    div_sub_one hbFMapNe] using hratio

/-- Unramified clause of Paper 10.17: the literal scalar extension of the
base covector is stationary for the norm/trace pullback at the full
half-conductor depth. -/
theorem highCovectors_unramified
    (F L : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra F L] [ValuativeExtension F L]
    [Module.Free F L] [Module.Finite F L]
    (chi : ContinuousQuasiChar F) (psi : ContinuousAddChar F)
    (n : ℕ) (npsi : ℤ)
    (hdegree : Module.finrank F L = 2)
    (hunr : ramificationIndex F L = 1)
    (bF : Fˣ)
    (hbF : IsStationaryCovectorAtDepth F chi psi n npsi
      (stationaryCovectorDepth n) bF) :
    IsStationaryCovectorAtDepth L
      (normQuasiChar F L chi) (tracePullbackAddChar F L psi)
      n npsi (stationaryCovectorDepth n)
      (Units.map (algebraMap F L) bF) := by
  have hnLarge : 1 < n := hbF.depth.conductor_gt_one
  let s : ℕ := stationaryCovectorDepth n
  have hsPos : 0 < s := hbF.depth.pos
  have hs_le_n : s ≤ n := hbF.depth.le_conductor
  have hresDegree : residueDegree F L = 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F L
    rw [hdegree, hunr, one_mul] at h
    exact h.symm
  refine
    { multiplicativeConductor := ?_
      additiveConductor := ?_
      depth := hbF.depth
      order := ?_
      linearization := ?_ }
  · change IsMultiplicativeConductor L chi.compNorm n
    exact (unramified_multiplicativeConductor_compNorm F L hunr chi n).2
      hbF.multiplicativeConductor
  · change IsAdditiveConductor L psi.compTrace npsi
    exact (unramified_additiveConductor_compTrace F L hunr psi npsi).2
      hbF.additiveConductor
  · simp only [Units.coe_map, MonoidHom.coe_coe, ord_algebraMap,
      hunr, one_nsmul]
    exact hbF.order
  · intro z
    have htrace : Algebra.trace F L (z : L) ∈ lattice F (s : ℤ) :=
      trace_mem_lattice F L hunr (s : ℤ) z.property
    have hnormN : Algebra.norm F (z : L) ∈ lattice F (n : ℤ) := by
      rw [mem_lattice, ord_norm, hresDegree]
      have hzord : (((s : ℤ) : WithTop ℤ)) ≤ ord L (z : L) := by
        rw [← mem_lattice]
        exact z.property
      have htwo := nsmul_le_nsmul_right hzord 2
      have hhalf : ((n : ℤ) : WithTop ℤ) ≤
          2 • (((s : ℤ) : WithTop ℤ)) := by
        rw [← WithTop.coe_nsmul]
        apply WithTop.coe_le_coe.mpr
        dsimp only [s]
        norm_num [nsmul_eq_mul]
        exact_mod_cast hbF.depth.half_le
      exact hhalf.trans htwo
    have hnorm : Algebra.norm F (z : L) ∈ lattice F (s : ℤ) :=
      lattice_antitone F (by exact_mod_cast hs_le_n) hnormN
    let w : lattice F (s : ℤ) :=
      ⟨Algebra.trace F L (z : L) + Algebra.norm F (z : L),
        add_mem_lattice F htrace hnorm⟩
    have hnormUnit :
        continuousNormUnits F L
            (positiveUnitOfLattice L hsPos z) =
          positiveUnitOfLattice F hsPos w := by
      apply Units.ext
      simp only [coe_continuousNormUnits, coe_positiveUnitOfLattice]
      rw [quadratic_norm_one_add F L hdegree]
      simp [w]
      ring
    rw [normQuasiChar_apply, hnormUnit]
    have hlin := hbF.linearization w
    rw [hlin, tracePullbackAddChar_apply]
    simp only [Units.coe_map, MonoidHom.coe_coe]
    have htraceMul :
        Algebra.trace F L
            (algebraMap F L (bF : F) * (z : L)) =
          (bF : F) * Algebra.trace F L (z : L) := by
      rw [← Algebra.smul_def, map_smul]
      rfl
    rw [htraceMul]
    change psi ((bF : F) *
      (Algebra.trace F L (z : L) + Algebra.norm F (z : L))) = _
    rw [mul_add, ContinuousAddChar.map_add_eq_mul]
    have hnormTerm : psi ((bF : F) * Algebra.norm F (z : L)) = 1 := by
      apply hbF.additiveConductor.trivial
      have hbFLattice : (bF : F) ∈ lattice F (-(n : ℤ) - npsi) := by
        rw [mem_lattice, hbF.order]
      have hprod := mul_mem_lattice F hbFLattice hnormN
      simpa only [show (-(n : ℤ) - npsi) + (n : ℤ) = -npsi by omega]
        using hprod
    rw [hnormTerm, mul_one]

end

end LanglandsSecondMainLemma.Dyadic
