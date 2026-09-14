import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsSecondMainLemma.Dyadic.UR.MinimalOrigin
import LanglandsSecondMainLemma.Stationary.CommonFunction

/-!
# Dyadic / UR / Minimal Functions

The odd-conductor calculation in `D:UR:critmaps`, `D:UR:extraUconstant`,
and `D:UR:actualHidentity`. All critical values retain their affine terms.
-/

namespace LanglandsSecondMainLemma.Dyadic.UR

noncomputable section
open LanglandsFirstMainLemma

/-- The coordinate pair in `D:UR:actualHidentity` is bijective. The second
coordinate is the square of the actual weighted trace. A trace-one element
supplies two independent trace coordinates, and finite-field Frobenius
supplies the final square. -/
theorem minimal_trace_coordinates_bijective
    (k kappa : Type*) [Field k] [Field kappa] [Finite k] [Finite kappa]
    [CharP k 2] [Algebra k kappa]
    (hdegree : Module.finrank k kappa = 2)
    (C : kappa) (hC : trace k kappa C = 1) :
    Function.Bijective (fun z : kappa =>
      (trace k kappa z, (trace k kappa (C * z)) ^ 2)) := by
  let f : kappa →ₗ[k] k × k :=
    (trace k kappa).prod ((trace k kappa).comp (LinearMap.mulLeft k C))
  have htrace1 : trace k kappa 1 = 0 := by
    rw [← map_one (algebraMap k kappa), trace_algebraMap, hdegree, two_smul,
      CharTwo.add_self_eq_zero]
  have hsurj : Function.Surjective f := by
    rintro ⟨a, b⟩
    refine ⟨algebraMap k kappa (b - a * trace k kappa (C * C)) +
      algebraMap k kappa a * C, ?_⟩
    apply Prod.ext
    · change trace k kappa _ = a
      rw [map_add, trace_algebraMap, hdegree, two_smul,
        CharTwo.add_self_eq_zero, zero_add, ← Algebra.smul_def,
        map_smul, hC, smul_eq_mul, mul_one]
    · change trace k kappa (C * _) = b
      rw [mul_add, mul_left_comm C, mul_comm C (algebraMap k kappa _),
        map_add, ← Algebra.smul_def, map_smul, hC, smul_eq_mul, mul_one,
        ← Algebra.smul_def, map_smul, smul_eq_mul]
      ring
  have hdim : Module.finrank k kappa = Module.finrank k (k × k) := by
    simp [Module.finrank_prod, hdegree]
  have hf : Function.Bijective f :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩
  exact (Function.bijective_id.prodMap
    (PerfectRing.bijective_frobenius (R := k) (p := 2))).comp hf

section LocalEstimates
variable (F L : Type*) [Field F] [Field L]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra F L] [ValuativeExtension F L] [Module.Finite F L]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension F L] in
/-- The exact quadratic expansion, specialized from FML's full symmetric
expansion, including the trace term. -/
private theorem critical_norm_one_add (hdegree : Module.finrank F L = 2) (y : L) :
    norm F L (1 + y) = 1 + trace F L y + norm F L y := by
  rw [norm_one_add_eq_sum_elementarySymmetric, hdegree]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    elementarySymmetric_zero, elementarySymmetric_one]
  rw [← hdegree, elementarySymmetric_finrank]

/-- The lower ramified trace estimate, with an integer depth and the exact
floor from `D:UR:localledger`. -/
private theorem critical_trace_mem [PrimeCyclicExtension F L]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F L t)
    (hres : residueDegree F L = 1) (hdegree : Module.finrank F L = 2)
    {j : ℤ} {y : L} (hy : y ∈ lattice L j) :
    trace F L y ∈ lattice F ((j + (t + 1 : ℕ)) / 2) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F L hres
  have hmap : trace F L y ∈
      Submodule.map ((trace F L).restrictScalars (ringOfIntegers F))
        ((lattice L j).restrictScalars (ringOfIntegers F)) :=
    Submodule.mem_map.mpr ⟨y, hy, rfl⟩
  rw [cyclicPrime_trace_lattice_image_eq F L ht hres pi hpi hgen, hdegree] at hmap
  simpa using hmap

/-- Both the first and third rows of `D:UR:critmaps` use this same ramified
calculation. The trace term is retained, then proved to lie one layer deeper;
this includes `e = 1`. -/
theorem minimal_ramified_norm_increment [PrimeCyclicExtension F L]
    (hdegree : Module.finrank F L = 2) {t e : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F L t)
    (hres : residueDegree F L = 1) (hT : t + 1 = 2 * e + 1) (he : 0 < e)
    (a z : L) (ha : ord L a = ((e : ℤ) : WithTop ℤ))
    (hz : z ∈ lattice L 0) :
    norm F L (1 + a * z) - 1 ∈ lattice F (e : ℤ) ∧
    norm F L (1 + a * z) - 1 - norm F L a * norm F L z ∈
      lattice F ((e : ℤ) + 1) := by
  have hay : a * z ∈ lattice L (e : ℤ) := by
    simpa only [add_zero] using mul_mem_lattice L
      (show a ∈ lattice L (e : ℤ) by rw [mem_lattice, ha]) hz
  have htr : trace F L (a * z) ∈ lattice F ((e : ℤ) + 1) :=
    lattice_antitone F (by omega) (critical_trace_mem F L ht hres hdegree hay)
  have hn : norm F L (a * z) ∈ lattice F (e : ℤ) := by
    rwa [mem_lattice, ord_norm, hres, one_nsmul, ← mem_lattice]
  rw [critical_norm_one_add F L hdegree]
  constructor
  · convert add_mem_lattice F (lattice_antitone F (by omega) htr) hn using 1; ring
  · rw [map_mul (norm F L)]
    convert htr using 1; ring

/-- The unramified second row of `D:UR:critmaps`: its quadratic norm term
has depth `2e`, hence disappears modulo depth `e+1`. -/
theorem minimal_unramified_norm_increment
    (hunr : ramificationIndex F L = 1) (hdegree : Module.finrank F L = 2)
    {e : ℕ} (he : 0 < e) (a : F) (ha : ord F a = ((e : ℤ) : WithTop ℤ))
    (z : L) (hz : z ∈ lattice L 0) :
    norm F L (1 + algebraMap F L a * z) - 1 ∈ lattice F (e : ℤ) ∧
    norm F L (1 + algebraMap F L a * z) - 1 - a * trace F L z ∈
      lattice F ((e : ℤ) + 1) := by
  have haz : algebraMap F L a * z ∈ lattice L (e : ℤ) := by
    simpa only [add_zero] using mul_mem_lattice L
      (show algebraMap F L a ∈ lattice L (e : ℤ) by
        rw [mem_lattice, ord_algebraMap, hunr, one_nsmul, ha]) hz
  have hres : residueDegree F L = 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F L
    simpa only [hunr, hdegree, one_mul] using h.symm
  have hn : norm F L (algebraMap F L a * z) ∈ lattice F (2 * (e : ℤ)) := by
    rw [mem_lattice, ord_norm, hres, two_nsmul]
    simpa only [two_mul, WithTop.coe_add] using
      add_le_add ((mem_lattice L).mp haz) ((mem_lattice L).mp haz)
  have htr : trace F L (algebraMap F L a * z) = a * trace F L z := by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [critical_norm_one_add F L hdegree]
  constructor
  · convert add_mem_lattice F (trace_mem_lattice F L hunr (e : ℤ) haz)
      (lattice_antitone F (by omega) hn) using 1; ring
  · rw [htr]
    convert lattice_antitone F (by omega : (e : ℤ) + 1 ≤ 2 * e) hn using 1; ring

/-- The extra unramified norm is constant modulo depth `2e+1` when its
trace input of order `e` changes by depth `e+1`. -/
theorem minimal_extra_norm_deep
    (hunr : ramificationIndex F L = 1) (hdegree : Module.finrank F L = 2)
    {e : ℕ} (Q D : L) (hQ : ord L Q = ((e : ℤ) : WithTop ℤ))
    (hD : D ∈ lattice L ((e : ℤ) + 1)) :
    norm F L (Q + D) - norm F L Q ∈ lattice F (2 * (e : ℤ) + 1) := by
  have hQne : Q ≠ 0 := (ord_ne_top_iff L).mp (by rw [hQ]; simp)
  have hquot : D / Q ∈ lattice L 1 :=
    (div_mem_lattice_iff L Q D (e : ℤ) 1 hQ).mpr hD
  let u := principalUnitOf L 0 (D / Q) (by simpa using hquot)
  have hu : u ∈ unitFiltration L 1 := principalUnitOf_mem L 0 _ _
  have hnorm := unramified_norm_mem_unitFiltration F L hunr 1 hu
  rw [mem_unitFiltration_succ_iff_sub_mem_lattice] at hnorm
  have hres : residueDegree F L = 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F L
    simpa only [hunr, hdegree, one_mul] using h.symm
  have hnQ : norm F L Q ∈ lattice F (2 * (e : ℤ)) := by
    rw [mem_lattice, ord_norm, hres, hQ]
    norm_cast
  have hfactor : Q + D = Q * (u : L) := by
    change Q + D = Q * (1 + D / Q)
    field_simp
  have hexact : norm F L (Q + D) - norm F L Q =
      norm F L Q * ((normUnits F L u : F) - 1) := by
    rw [hfactor, map_mul, coe_normUnits]
    ring
  rw [hexact]
  exact mul_mem_lattice F hnQ hnorm

omit [Module.Finite F L] in
private theorem critical_map_integral {y : F} (hy : y ∈ lattice F 0) :
    algebraMap F L y ∈ lattice L 0 := by
  rw [mem_lattice, ord_algebraMap]
  simpa only [WithTop.coe_zero] using
    nsmul_nonneg ((mem_lattice F).mp hy) (ramificationIndex F L)

omit [Module.Finite F L] in
private theorem critical_residue_map (z : ringOfIntegers F) :
    residueMap L (algebraMap (ringOfIntegers F) (ringOfIntegers L) z) =
      extensionResidueMap F L (residueMap F z) :=
  (Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
    (ValuativeRel.valuation F) (ValuativeRel.valuation L) z).symm

private theorem critical_norm_integral {y : L} (hy : y ∈ lattice L 0) :
    norm F L y ∈ lattice F 0 := by
  rw [mem_lattice, ord_norm]
  simpa only [WithTop.coe_zero] using
    nsmul_nonneg ((mem_lattice L).mp hy) (residueDegree F L)

omit [Module.Finite F L] in
private theorem critical_map_positive {r : ℕ} (hr : 0 < r)
    {y : F} (hy : ord F y = ((r : ℤ) : WithTop ℤ)) :
    algebraMap F L y ∈ lattice L 1 := by
  rw [mem_lattice, ord_algebraMap, hy]
  norm_cast
  simp only [nsmul_eq_mul]
  exact_mod_cast Nat.mul_pos (ramificationIndex_pos F L) hr

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension F L] in
private theorem critical_norm_translate (hdegree : Module.finrank F L = 2)
    (y : L) (b : F) :
    norm F L (y + algebraMap F L b) = norm F L y + b * trace F L y + b ^ 2 := by
  by_cases hb : b = 0
  · simp [hb]
  have hbL : algebraMap F L b ≠ 0 := (map_ne_zero (algebraMap F L)).mpr hb
  have heq : y + algebraMap F L b =
      algebraMap F L b * (1 + (algebraMap F L b)⁻¹ * y) := by field_simp; ring
  have htr : trace F L ((algebraMap F L b)⁻¹ * y) = b⁻¹ * trace F L y := by
    rw [← map_inv₀, ← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [heq, map_mul (norm F L), LanglandsFirstMainLemma.norm_algebraMap, hdegree,
    critical_norm_one_add F L hdegree, htr, map_mul (norm F L),
    Algebra.norm_inv, LanglandsFirstMainLemma.norm_algebraMap, hdegree]
  field_simp
  ring

/-- Reduction of the ramified norm is the square of the actual lower
residue representative, including the case where that residue is zero. -/
theorem minimal_ramified_norm_residue [PrimeCyclicExtension F L]
    (hdegree : Module.finrank F L = 2) {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F L t) (htpos : 0 < t)
    (hres : residueDegree F L = 1)
    (y : L) (b : F) (hb : b ∈ lattice F 0)
    (hyb : y - algebraMap F L b ∈ lattice L 1) :
    norm F L y - b ^ 2 ∈ lattice F 1 := by
  have hn : norm F L (y - algebraMap F L b) ∈ lattice F 1 := by
    rwa [mem_lattice, ord_norm, hres, one_nsmul, ← mem_lattice]
  have ht' : trace F L (y - algebraMap F L b) ∈ lattice F 1 :=
    lattice_antitone F (by omega) (critical_trace_mem F L ht hres hdegree hyb)
  have heq := critical_norm_translate F L hdegree (y - algebraMap F L b) b
  rw [sub_add_cancel] at heq
  rw [heq, add_sub_cancel_right]
  exact add_mem_lattice F hn (by simpa only [zero_add] using mul_mem_lattice F hb ht')

/-- The third critical coordinate. Dividing by the actual trace unit `P`
preserves its residue because `P ≡ 1`; the final lower norm then squares
the weighted trace coordinate. -/
theorem minimal_lower_norm_coordinate [PrimeCyclicExtension F L]
    (hdegree : Module.finrank F L = 2) {t e : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F L t)
    (hres : residueDegree F L = 1) (hT : t + 1 = 2 * e + 1) (he : 0 < e)
    (a x P : L) (X m n : F)
    (ha : ord L a = ((e : ℤ) : WithTop ℤ))
    (hx : x ∈ lattice L 0) (hX : X ∈ lattice F 0)
    (hm : m ∈ lattice F 0) (hn : n ∈ lattice F 0)
    (hxX : x - algebraMap F L X ∈ lattice L 1)
    (hP : ord L P = 0) (hP1 : P - 1 ∈ lattice L 1) :
    let v := (x * algebraMap F L m + algebraMap F L n) / P
    v ∈ lattice L 0 ∧
    norm F L (1 + a * v) - 1 ∈ lattice F (e : ℤ) ∧
    norm F L (1 + a * v) - 1 - norm F L a * (X * m + n) ^ 2 ∈
      lattice F ((e : ℤ) + 1) := by
  let v := (x * algebraMap F L m + algebraMap F L n) / P
  have hmL := critical_map_integral F L hm
  have hnL := critical_map_integral F L hn
  have hb : X * m + n ∈ lattice F 0 := add_mem_lattice F
    (by simpa only [zero_add] using mul_mem_lattice F hX hm) hn
  have hbL := critical_map_integral F L hb
  have hnum : x * algebraMap F L m + algebraMap F L n ∈ lattice L 0 :=
    add_mem_lattice L (by simpa only [zero_add] using mul_mem_lattice L hx hmL) hnL
  have hv : v ∈ lattice L 0 :=
    (div_mem_lattice_iff L P _ 0 0 hP).mpr (by simpa using hnum)
  have hPne : P ≠ 0 := (ord_ne_top_iff L).mp (by rw [hP]; simp)
  have hvb : v - algebraMap F L (X * m + n) ∈ lattice L 1 := by
    have heq : v - algebraMap F L (X * m + n) =
        ((x - algebraMap F L X) * algebraMap F L m -
          algebraMap F L (X * m + n) * (P - 1)) / P := by
      dsimp only [v]
      simp only [map_add, map_mul]
      field_simp
      ring
    rw [heq]
    apply (div_mem_lattice_iff L P _ 0 1 hP).mpr
    simp only [zero_add]
    exact sub_mem_lattice L
      (by simpa only [add_zero] using mul_mem_lattice L hxX hmL)
      (by simpa only [zero_add] using mul_mem_lattice L hbL hP1)
  have hnv := minimal_ramified_norm_residue F L hdegree ht (by omega) hres
    v (X * m + n) hb hvb
  have hbeta : norm F L a ∈ lattice F (e : ℤ) := by
    rw [mem_lattice, ord_norm, hres, one_nsmul, ha]
  obtain ⟨hinc, herr⟩ := minimal_ramified_norm_increment F L hdegree ht hres hT he a v ha hv
  refine ⟨hv, hinc, ?_⟩
  have h := add_mem_lattice F herr (mul_mem_lattice F hbeta hnv)
  convert h using 1; ring

end LocalEstimates

section ResidualValues
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

private theorem critical_order_add {n : ℤ} {Q D : L}
    (hQ : ord L Q = (n : WithTop ℤ)) (hD : D ∈ lattice L (n + 1)) :
    ord L (Q + D) = (n : WithTop ℤ) := by
  have hlt : (n : WithTop ℤ) < ord L D :=
    (WithTop.coe_lt_coe.mpr (by omega : n < n + 1)).trans_le ((mem_lattice L).mp hD)
  rw [ord_add_eq_min L (by rw [hQ]; exact ne_of_lt hlt), hQ, min_eq_left hlt.le]

private theorem critical_scale_one (psi : LocalAddCharData L) :
    scaleAddCharData L psi 1 = psi := by
  have hc : (scaleAddCharData L psi 1).character = psi.character := by
    ext y
    simp only [scaleAddCharData_character_apply, Units.val_one, one_mul]
  have hn : (scaleAddCharData L psi 1).conductor = psi.conductor :=
    ((hc ▸ (scaleAddCharData L psi 1).isConductor) :
      IsAdditiveConductor L psi.character _).unique psi.isConductor
  cases h : scaleAddCharData L psi 1
  cases psi
  simp only [LocalAddCharData.mk.injEq]
  exact ⟨by simpa only [h] using hc, by simpa only [h] using hn⟩

/-- Terminal-coset transport for the full normalized residual function.
The error is a whole-ideal congruence, and the same coefficient is kept. -/
theorem minimal_criticalValue_eq_residual
    (theta : LocalQuasiCharData L) (psi : LocalAddCharData L) (Z : Lˣ)
    (e : ℕ) (he : 0 < e) (hm : theta.conductor = 2 * e + 1)
    (hs : Stationary.IsOrdinaryStationaryCoefficient L theta psi Z (by omega))
    (delta : Lˣ) (hdelta : ord L (delta : L) = ((e : ℤ) : WithTop ℤ))
    (v : lattice L (e : ℤ)) (z : ringOfIntegers L)
    (hcongr : (v : L) - (delta : L) * (z : L) ∈ lattice L ((e : ℤ) + 1)) :
    Stationary.normalizedCriticalValue L theta psi Z e he v =
      Stationary.normalizedResidualFunction L theta psi 1 Z e hm (by omega)
        delta hdelta (residueMap L z) := by
  let w := teichmuller L (residueMap L z)
  have hdeltaMem : (delta : L) ∈ lattice L (e : ℤ) := by rw [mem_lattice, hdelta]
  have hw : (w : L) ∈ lattice L 0 := (mem_lattice_zero_iff L).mpr w.property
  let v' : lattice L (e : ℤ) :=
    ⟨(delta : L) * (w : L), by simpa only [add_zero] using mul_mem_lattice L hdeltaMem hw⟩
  have hzw : (z : L) - (w : L) ∈ lattice L 1 :=
    (residueMap_eq_residueMap_iff L z w).mp (by simp [w])
  have hvv' : CongruentAtDepth ((e + 1 : ℕ) : ℤ) (v : L) (v' : L) := by
    apply (congruentAtDepth_iff_sub_mem_lattice L _ _ _).mpr
    change (v : L) - (delta : L) * (w : L) ∈ lattice L ((e : ℤ) + 1)
    have heq : (v : L) - (delta : L) * (w : L) =
        ((v : L) - (delta : L) * (z : L)) +
          (delta : L) * ((z : L) - (w : L)) := by ring
    rw [heq]
    exact add_mem_lattice L hcongr (mul_mem_lattice L hdeltaMem hzw)
  have hstat : Stationary.IsNormalizedStationaryCoefficientAtDepth L theta
      (scaleAddCharData L psi 1) Z (e + 1) (by omega) := by
    rw [critical_scale_one]
    have heq : theta.conductor / 2 + theta.conductor % 2 = e + 1 := by omega
    simpa only [heq] using hs.2
  have hval := Stationary.normalizedCriticalValue_odd_eq_of_congruent L theta psi 1 Z e hm
    (by omega) (by simpa only [critical_scale_one] using hs.1) hstat v v' hvv'
  rw [critical_scale_one] at hval
  rw [hval]
  have hunit : (lamprechtHasseUnit L theta e hm (by omega) delta hdelta (w : L) hw : Lˣ) =
      positiveUnitOfLattice L he v' := by
    apply Units.ext
    rw [lamprechtHasseUnit_coe, coe_positiveUnitOfLattice]
  dsimp only [Stationary.normalizedCriticalValue, Stationary.normalizedResidualFunction]
  rw [critical_scale_one, hunit]
  simp only [v', w, mul_assoc]

end ResidualValues

section DiamondTraces
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  (U E : IntermediateField F K)
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeExtension F U] [ValuativeExtension U K]
  [ValuativeExtension F E] [ValuativeExtension E K]
  [PrimeCyclicExtension F E]

/-- The first two critical maps, before reduction. The scale on `U` is the
literal lower norm of the chosen scale on `E`. -/
theorem minimal_upper_norm_coordinates
    (hdisj : U.LinearDisjoint E) (hsup : U ⊔ E = ⊤)
    (hunr : ramificationIndex F U = 1)
    (hU : Module.finrank F U = 2) (hE : Module.finrank F E = 2)
    {t e : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hT : t + 1 = 2 * e + 1) (he : 0 < e)
    (a : E) (ha : ord E a = ((e : ℤ) : WithTop ℤ))
    (z : U) (hz : z ∈ lattice U 0) :
    let u : K := 1 + (a : K) * (z : K)
    norm U K u - 1 ∈ lattice U (e : ℤ) ∧
    norm U K u - 1 - algebraMap F U (norm F E a) * z ^ 2 ∈
      lattice U ((e : ℤ) + 1) ∧
    norm E K u - 1 ∈ lattice E (e : ℤ) ∧
    norm E K u - 1 - a * algebraMap F E (trace F U z) ∈
      lattice E ((e : ℤ) + 1) := by
  have hsup' : E ⊔ U = ⊤ := sup_comm U E ▸ hsup
  have hUK : Module.finrank U K = 2 := (hdisj.finrank_left_eq_finrank hsup).trans hE
  have hEK : Module.finrank E K = 2 := (hdisj.symm.finrank_left_eq_finrank hsup').trans hU
  have hnUa : norm U K (a : K) = algebraMap F U (norm F E a) :=
    hdisj.norm_algebraMap hsup a
  have htUa : trace U K (a : K) = algebraMap F U (trace F E a) :=
    hdisj.trace_algebraMap hsup a
  have hnEz : norm E K (z : K) = algebraMap F E (norm F U z) :=
    hdisj.symm.norm_algebraMap hsup' z
  have htEz : trace E K (z : K) = algebraMap F E (trace F U z) :=
    hdisj.symm.trace_algebraMap hsup' z
  have htU : trace U K ((a : K) * (z : K)) = z * algebraMap F U (trace F E a) := by
    change trace U K ((a : K) * algebraMap U K z) = _
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, htUa]
  have htE : trace E K ((a : K) * (z : K)) = a * algebraMap F E (trace F U z) := by
    change trace E K (algebraMap E K a * (z : K)) = _
    rw [← Algebra.smul_def, map_smul, smul_eq_mul, htEz]
  have hnUz : norm U K (z : K) = z ^ 2 := by
    change norm U K (algebraMap U K z) = _
    rw [LanglandsFirstMainLemma.norm_algebraMap, hUK]
  have hnEa : norm E K (a : K) = a ^ 2 := by
    change norm E K (algebraMap E K a) = _
    rw [LanglandsFirstMainLemma.norm_algebraMap, hEK]
  have hat : a ∈ lattice E (e : ℤ) := by rw [mem_lattice, ha]
  have hta : algebraMap F U (trace F E a) ∈ lattice U ((e : ℤ) + 1) := by
    rw [mem_lattice, ord_algebraMap, hunr, one_nsmul, ← mem_lattice]
    exact lattice_antitone F (by omega) (critical_trace_mem F E ht hres hE hat)
  have htraceU : z * algebraMap F U (trace F E a) ∈ lattice U ((e : ℤ) + 1) := by
    simpa only [zero_add] using mul_mem_lattice U hz hta
  have hbeta : algebraMap F U (norm F E a) ∈ lattice U (e : ℤ) := by
    rw [mem_lattice, ord_algebraMap, hunr, one_nsmul, ord_norm, hres, one_nsmul, ha]
  have hnormU : algebraMap F U (norm F E a) * z ^ 2 ∈ lattice U (e : ℤ) := by
    simpa only [add_zero, pow_two] using mul_mem_lattice U hbeta
      (show z * z ∈ lattice U 0 by simpa using mul_mem_lattice U hz hz)
  have htraceE : a * algebraMap F E (trace F U z) ∈ lattice E (e : ℤ) := by
    simpa only [add_zero] using mul_mem_lattice E hat
      (critical_map_integral F E (trace_mem_lattice F U hunr 0 hz))
  have hnormE : a ^ 2 * algebraMap F E (norm F U z) ∈ lattice E (2 * (e : ℤ)) := by
    have haa : a ^ 2 ∈ lattice E (2 * (e : ℤ)) := by
      simpa only [pow_two, two_mul] using mul_mem_lattice E hat hat
    simpa only [add_zero] using mul_mem_lattice E haa
      (critical_map_integral F E (critical_norm_integral F U hz))
  dsimp only
  rw [critical_norm_one_add U K hUK, critical_norm_one_add E K hEK,
    htU, htE, map_mul (norm U K), map_mul (norm E K), hnUa, hnUz, hnEa, hnEz]
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert add_mem_lattice U (lattice_antitone U (by omega) htraceU) hnormU using 1; ring
  · convert htraceU using 1; ring
  · convert add_mem_lattice E htraceE (lattice_antitone E (by omega) hnormE) using 1; ring
  · convert lattice_antitone E (by omega : (e : ℤ) + 1 ≤ 2 * e) hnormE using 1; ring

/-- With lifts from the unramified field, the actual change in the upper
trace has depth `e+1`. Only the lower ramified trace ledger is needed. -/
theorem minimal_upper_trace_change
    (hdisj : U.LinearDisjoint E) (hsup : U ⊔ E = ⊤)
    (hunr : ramificationIndex F U = 1) (hE : Module.finrank F E = 2)
    {t e : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hT : t + 1 = 2 * e + 1) (he : 0 < e)
    (x : E) (d : U) (hx : x ∈ lattice E 0) (hd : d ∈ lattice U 0)
    (a : E) (ha : ord E a = ((e : ℤ) : WithTop ℤ))
    (z : U) (hz : z ∈ lattice U 0) :
    trace U K (((x : K) + (d : K)) * ((a : K) * (z : K))) ∈
      lattice U ((e : ℤ) + 1) := by
  have hat : a ∈ lattice E (e : ℤ) := by rw [mem_lattice, ha]
  have hxa : x * a ∈ lattice E (e : ℤ) := by
    simpa only [zero_add] using mul_mem_lattice E hx hat
  have htr {y : E} (hy : y ∈ lattice E (e : ℤ)) :
      algebraMap F U (trace F E y) ∈ lattice U ((e : ℤ) + 1) := by
    rw [mem_lattice, ord_algebraMap, hunr, one_nsmul, ← mem_lattice]
    exact lattice_antitone F (by omega) (critical_trace_mem F E ht hres hE hy)
  have heq : trace U K (((x : K) + (d : K)) * ((a : K) * (z : K))) =
      z * algebraMap F U (trace F E (x * a)) +
        (d * z) * algebraMap F U (trace F E a) := by
    have hdist : ((x : K) + (d : K)) * ((a : K) * (z : K)) =
        algebraMap U K z * ((x * a : E) : K) +
          algebraMap U K (d * z) * (a : K) := by
      simp only [map_mul, IntermediateField.algebraMap_apply, IntermediateField.coe_mul]
      ring
    have hbase (y : E) : trace U K (y : K) = algebraMap F U (trace F E y) :=
      hdisj.trace_algebraMap hsup y
    rw [hdist, map_add, ← Algebra.smul_def, map_smul, smul_eq_mul,
      ← Algebra.smul_def, map_smul, smul_eq_mul, hbase, hbase]
  rw [heq]
  have hdz : d * z ∈ lattice U 0 := by simpa using mul_mem_lattice U hd hz
  exact add_mem_lattice U
    (by simpa only [zero_add] using mul_mem_lattice U hz (htr hxa))
    (by simpa only [zero_add] using mul_mem_lattice U hdz (htr hat))

/-- The actual `U`-trace has order `e`. Integrality gives the lower bound;
the already proved elementary phase rules out a deeper trace. -/
theorem MinimalOddElementaryData.traceU_order
    (hunr : ramificationIndex F U = 1)
    (hU : Module.finrank F U = 2) (hE : Module.finrank F E = 2)
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1)
    {c : F} {d : U} {x : E}
    (hd : d ∈ lattice U 0) (hx : x ∈ lattice E 0)
    {thetaU : LocalQuasiCharData U} {thetaE : LocalQuasiCharData E}
    {tau : NormCharacter F E} {Psi : ContinuousAddChar F}
    (O : MinimalOriginData U E c d x t thetaU thetaE Psi)
    (D : MinimalOddElementaryData U E x t tau Psi O.origin) :
    ord U (trace U K (O.origin : K)) = ((D.e : ℤ) : WithTop ℤ) := by
  have htrace : trace F E x ∈ lattice F (D.e : ℤ) :=
    lattice_antitone F (by have := D.conductor_eq; omega)
      (critical_trace_mem F E ht hres hE hx)
  have hb : algebraMap F U (trace F E x) ∈ lattice U (D.e : ℤ) := by
    rwa [mem_lattice, ord_algebraMap, hunr, one_nsmul, ← mem_lattice]
  have htwo : (2 : U) ∈ lattice U (D.e : ℤ) := by
    rw [mem_lattice, ← map_ofNat (algebraMap F U) 2,
      ord_algebraMap, hunr, one_nsmul, D.order_two]
  have hQ : trace U K (O.origin : K) ∈ lattice U (D.e : ℤ) := by
    rw [O.traceU_eq]
    exact add_mem_lattice U hb (by simpa using mul_mem_lattice U htwo hd)
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp
    ((ord_ne_top_iff U).mpr D.traceU_ne_zero)
  rw [mem_lattice, ← hv, WithTop.coe_le_coe] at hQ
  have hresU : residueDegree F U = 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F U
    simpa only [hunr, hU, one_mul] using h.symm
  have hvle : v ≤ D.e := by
    by_contra h
    have hn : norm F U (trace U K (O.origin : K)) ∈ lattice F (-D.psiData.conductor) := by
      rw [D.psi_conductor, neg_neg, mem_lattice, ord_norm, hresU, ← hv]
      have he := D.conductor_eq
      norm_cast
      simp only [nsmul_eq_mul]
      omega
    have hp := D.psiData.isConductor.trivial _ hn
    rw [D.psi_character] at hp
    have hpC := congrArg (Units.val : ℂˣ → ℂ) hp
    rw [D.traceU_phase, Units.val_one] at hpC
    norm_num at hpC
  rw [← hv, show v = D.e by omega]

/-- `D:UR:extraUconstant` for the same origin and perturbation used in the
critical calculation. Its conductor-depth membership is proved from the
origin data and the ramified trace ledger. -/
theorem minimal_extra_trace_norm_increment
    (hdisj : U.LinearDisjoint E) (hsup : U ⊔ E = ⊤)
    (hunr : ramificationIndex F U = 1)
    (hU : Module.finrank F U = 2) (hE : Module.finrank F E = 2)
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1)
    {c : F} {d : U} {x : E}
    (hd : d ∈ lattice U 0) (hx : x ∈ lattice E 0)
    {thetaU : LocalQuasiCharData U} {thetaE : LocalQuasiCharData E}
    {tau : NormCharacter F E} {Psi : ContinuousAddChar F}
    (O : MinimalOriginData U E c d x t thetaU thetaE Psi)
    (D : MinimalOddElementaryData U E x t tau Psi O.origin)
    (a : E) (ha : ord E a = ((D.e : ℤ) : WithTop ℤ))
    (z : U) (hz : z ∈ lattice U 0) :
    norm F U (trace U K ((O.origin : K) * (1 + (a : K) * (z : K)))) -
        norm F U (trace U K (O.origin : K)) ∈ lattice F ((t + 1 : ℕ) : ℤ) := by
  have hchange : trace U K ((O.origin : K) * ((a : K) * (z : K))) ∈
      lattice U ((D.e : ℤ) + 1) := by
    rw [O.origin_eq]
    exact minimal_upper_trace_change U E hdisj hsup hunr hE ht hres
      D.conductor_eq D.e_pos x d hx hd a ha z hz
  have hQ := D.traceU_order U E hunr hU hE ht hres hd hx O
  have hnorm := minimal_extra_norm_deep F U hunr hU _ _ hQ hchange
  rw [mul_add, mul_one, map_add]
  simpa only [D.conductor_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one] using hnorm

/-- Actual lift data for the three critical maps. The constructor below
proves every field from the same origin and the perturbation `C(1+az)`. -/
structure MinimalCriticalLiftData (e : ℕ) (C : Kˣ)
    (hCE : trace E K (C : K) ≠ 0) (d : U) (X : F) (a : E) (z : U) where
  point : Kˣ
  point_eq : (point : K) = (C : K) * (1 + (a : K) * (z : K))
  traceU_order : ord U (trace U K (point : K)) = ((e : ℤ) : WithTop ℤ)
  traceE_order : ord E (trace E K (point : K)) = 0
  traceU_ne_zero : trace U K (point : K) ≠ 0
  traceE_ne_zero : trace E K (point : K) ≠ 0
  vU : lattice U (e : ℤ)
  vE : lattice E (e : ℤ)
  w : lattice F (e : ℤ)
  normU_eq : 1 + (vU : U) = ((normUnits U K point / normUnits U K C : Uˣ) : U)
  normE_eq : 1 + (vE : E) = ((normUnits E K point / normUnits E K C : Eˣ) : E)
  lower_eq : 1 + (w : F) = ((Stationary.commonOriginLowerCoefficient E point traceE_ne_zero /
    Stationary.commonOriginLowerCoefficient E C hCE : Fˣ) : F)
  coordinateU : (vU : U) - algebraMap F U (norm F E a) * z ^ 2 ∈
    lattice U ((e : ℤ) + 1)
  coordinateE : (vE : E) - a * algebraMap F E (trace F U z) ∈
    lattice E ((e : ℤ) + 1)
  coordinateF : (w : F) - norm F E a * (X * trace F U z + trace F U (d * z)) ^ 2 ∈
    lattice F ((e : ℤ) + 1)
  extra_deep : norm F U (trace U K (point : K)) - norm F U (trace U K (C : K)) ∈
    lattice F (2 * (e : ℤ) + 1)

/-- Construct all three literal norm increments, prove their critical
coordinates, and prove that both traces remain nonzero. The lower lift `X`
is only a residue representative for `x`; it never replaces the origin. -/
def minimalCriticalLift
    (hdisj : U.LinearDisjoint E) (hsup : U ⊔ E = ⊤)
    (hunr : ramificationIndex F U = 1)
    (hU : Module.finrank F U = 2) (hE : Module.finrank F E = 2)
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1)
    {c : F} {d : U} {x : E}
    (hd : d ∈ lattice U 0) (hx : x ∈ lattice E 0)
    {thetaU : LocalQuasiCharData U} {thetaE : LocalQuasiCharData E}
    {tau : NormCharacter F E} {Psi : ContinuousAddChar F}
    (O : MinimalOriginData U E c d x t thetaU thetaE Psi)
    (D : MinimalOddElementaryData U E x t tau Psi O.origin)
    (X : F) (hX : X ∈ lattice F 0) (hxX : x - algebraMap F E X ∈ lattice E 1)
    (a : E) (ha : ord E a = ((D.e : ℤ) : WithTop ℤ))
    (z : U) (hz : z ∈ lattice U 0) :
    MinimalCriticalLiftData U E D.e O.origin D.traceE_ne_zero d X a z := by
  have he := D.e_pos
  have hT := D.conductor_eq
  have hwK : (a : K) * (z : K) ∈ lattice K 1 := by
    have haK : (a : K) ∈ lattice K 1 := critical_map_positive E K he ha
    have hzK : (z : K) ∈ lattice K 0 := critical_map_integral U K hz
    simpa only [add_zero] using mul_mem_lattice K haK hzK
  let R : Kˣ := principalUnitOf K 0 ((a : K) * (z : K)) (by simpa using hwK)
  let Y : Kˣ := O.origin * R
  have hY : (Y : K) = (O.origin : K) * (1 + (a : K) * (z : K)) := rfl
  obtain ⟨hNU, hcoU, hNE, hcoE⟩ := minimal_upper_norm_coordinates U E hdisj hsup hunr
    hU hE ht hres hT he a ha z hz
  let vU : lattice U (D.e : ℤ) := ⟨norm U K (R : K) - 1, hNU⟩
  let vE : lattice E (D.e : ℤ) := ⟨norm E K (R : K) - 1, hNE⟩
  let P := trace E K (O.origin : K)
  let m := trace F U z
  let n := trace F U (d * z)
  let v := (x * algebraMap F E m + algebraMap F E n) / P
  have hm : m ∈ lattice F 0 := trace_mem_lattice F U hunr 0 hz
  have hn : n ∈ lattice F 0 := trace_mem_lattice F U hunr 0
    (by simpa only [zero_add] using mul_mem_lattice U hd hz)
  have hP1 : P - 1 ∈ lattice E 1 := by
    have htwo : (2 : E) ∈ lattice E 1 := by
      simpa only [map_ofNat] using critical_map_positive F E he D.order_two
    change trace E K (O.origin : K) - 1 ∈ lattice E 1
    rw [O.traceE_eq, add_sub_cancel_right]
    simpa only [add_zero] using mul_mem_lattice E htwo hx
  obtain ⟨hv, hwF, hcoF⟩ := minimal_lower_norm_coordinate F E hE ht hres hT he
    a x P X m n ha hx hX hm hn hxX D.traceE_order hP1
  let w : lattice F (D.e : ℤ) := ⟨norm F E (1 + a * v) - 1, hwF⟩
  have htraceE : trace E K (Y : K) = P * (1 + a * v) := by
    have hsup' : E ⊔ U = ⊤ := sup_comm U E ▸ hsup
    have hbase (b : U) : trace E K (b : K) = algebraMap F E (trace F U b) :=
      hdisj.symm.trace_algebraMap hsup' b
    have hprod : (O.origin : K) * ((a : K) * (z : K)) =
        algebraMap E K (a * x) * (z : K) + algebraMap E K a * ((d * z : U) : K) := by
      rw [O.origin_eq]
      simp only [map_mul, IntermediateField.algebraMap_apply, IntermediateField.coe_mul]
      ring
    rw [hY, mul_add, mul_one, map_add, hprod, map_add,
      ← Algebra.smul_def, map_smul, smul_eq_mul,
      ← Algebra.smul_def, map_smul, smul_eq_mul, hbase, hbase]
    change P + (a * x * algebraMap F E m + a * algebraMap F E n) = P * (1 + a * v)
    dsimp only [v]
    have hPne : P ≠ 0 := D.traceE_ne_zero
    field_simp
  have hav : a * v ∈ lattice E (D.e : ℤ) := by
    simpa only [add_zero] using mul_mem_lattice E
      (show a ∈ lattice E (D.e : ℤ) by rw [mem_lattice, ha]) hv
  have htraceEord : ord E (trace E K (Y : K)) = 0 := by
    rw [htraceE, ord_mul, D.traceE_order,
      critical_order_add E (ord_one E) (lattice_antitone E (by omega) hav), zero_add]
    rfl
  have htraceEne : trace E K (Y : K) ≠ 0 :=
    (ord_ne_top_iff E).mp (by rw [htraceEord]; simp)
  have hchange : trace U K ((O.origin : K) * ((a : K) * (z : K))) ∈
      lattice U ((D.e : ℤ) + 1) := by
    rw [O.origin_eq]
    exact minimal_upper_trace_change U E hdisj hsup hunr hE ht hres hT he x d hx hd a ha z hz
  have htraceUord : ord U (trace U K (Y : K)) = ((D.e : ℤ) : WithTop ℤ) := by
    rw [hY, mul_add, mul_one, map_add]
    exact critical_order_add U (D.traceU_order U E hunr hU hE ht hres hd hx O) hchange
  have htraceUne : trace U K (Y : K) ≠ 0 :=
    (ord_ne_top_iff U).mp (by rw [htraceUord]; simp)
  refine {
    point := Y
    point_eq := hY
    traceU_order := htraceUord
    traceE_order := htraceEord
    traceU_ne_zero := htraceUne
    traceE_ne_zero := htraceEne
    vU := vU
    vE := vE
    w := w
    normU_eq := ?_
    normE_eq := ?_
    lower_eq := ?_
    coordinateU := hcoU
    coordinateE := hcoE
    coordinateF := hcoF
    extra_deep := ?_ }
  · simp only [Y, map_mul, mul_div_cancel_left, coe_normUnits, vU, add_sub_cancel]
  · simp only [Y, map_mul, mul_div_cancel_left, coe_normUnits, vE, add_sub_cancel]
  · rw [Units.val_div_eq_div_val]
    change 1 + (norm F E (1 + a * v) - 1) =
      norm F E (trace E K (Y : K)) / norm F E P
    rw [htraceE, map_mul (norm F E), mul_div_cancel_left₀]
    · ring
    · exact Algebra.norm_ne_zero_iff.mpr D.traceE_ne_zero
  · rw [hY]
    have h := minimal_extra_trace_norm_increment U E hdisj hsup hunr hU hE ht hres
      hd hx O D a ha z hz
    simpa only [hT, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h

end DiamondTraces

section ActualCharacters
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  [IsKleinFour Gal(K/F)]
  (U E : IntermediateField F K)
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeExtension F U] [ValuativeExtension U K]
  [ValuativeExtension F E] [ValuativeExtension E K]
  [Algebra.IsQuadraticExtension F U] [Algebra.IsQuadraticExtension U K]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsQuadraticExtension E K]

/-- The full character calculation behind `D:UR:actualHidentity`, at the
literal norm increments. The depth hypothesis is the precise conclusion
of `D:UR:extraUconstant`; residue-coordinate transport is a separate step.
No equality of polar forms or cancellation of an unknown character is used. -/
theorem minimal_actual_critical_values
    (thetaU : LocalQuasiCharData U) (thetaE : LocalQuasiCharData E)
    (Theta : ContinuousQuasiChar K)
    (hcU : normQuasiChar U K thetaU.character = Theta)
    (hcE : normQuasiChar E K thetaE.character = Theta)
    (tau : NormCharacter F E) (tauData : LocalQuasiCharData F)
    (htau : tauData.character = tau.1)
    (psiF : LocalAddCharData F) (psiU : LocalAddCharData U) (psiE : LocalAddCharData E)
    (hpsiU : psiU.character = psiF.character.compTrace)
    (hpsiE : psiE.character = psiF.character.compTrace)
    (C Y : Kˣ)
    (hCU : trace U K (C : K) ≠ 0) (hYU : trace U K (Y : K) ≠ 0)
    (hCE : trace E K (C : K) ≠ 0) (hYE : trace E K (Y : K) ≠ 0)
    (hdeep : norm F U (trace U K (Y : K)) - norm F U (trace U K (C : K)) ∈
      lattice F (-psiF.conductor))
    (e : ℕ) (he : 0 < e)
    (zU : lattice U (e : ℤ)) (zE : lattice E (e : ℤ)) (w : lattice F (e : ℤ))
    (hzU : 1 + (zU : U) = ((normUnits U K Y / normUnits U K C : Uˣ) : U))
    (hzE : 1 + (zE : E) = ((normUnits E K Y / normUnits E K C : Eˣ) : E))
    (hw : 1 + (w : F) = ((Stationary.commonOriginLowerCoefficient E Y hYE /
      Stationary.commonOriginLowerCoefficient E C hCE : Fˣ) : F)) :
    Stationary.normalizedCriticalValue U thetaU psiU (normUnits U K C) e he zU =
      Stationary.normalizedCriticalValue E thetaE psiE (normUnits E K C) e he zE *
        Stationary.normalizedCriticalValue F tauData psiF
          (Stationary.commonOriginLowerCoefficient E C hCE) e he w := by
  have hU := Stationary.commonFunctionProduct_eq U thetaU (trivialQuasiCharData F)
    (1 : NormCharacter F U) rfl Theta hcU psiF psiU hpsiU 1 C Y hCU hYU
  have hE := Stationary.commonFunctionProduct_eq E thetaE tauData
    tau htau Theta hcE psiF psiE hpsiE 1 C Y hCE hYE
  have hcritE := Stationary.commonFunctionProduct_eq_criticalValues E thetaE tauData
    psiF psiE 1 C Y hCE hYE e e he he zE w hzE hw
  have hunit : positiveUnitOfLattice U he zU = normUnits U K Y / normUnits U K C :=
    Units.ext hzU
  let W := Stationary.commonOriginLowerCoefficient U C hCU
  let W' := Stationary.commonOriginLowerCoefficient U Y hYU
  have harg : -(W : F) * (((W' / W : Fˣ) : F) - 1) =
      -(norm F U (trace U K (Y : K)) - norm F U (trace U K (C : K))) := by
    change -(W : F) * (((W' / W : Fˣ) : F) - 1) = -((W' : F) - (W : F))
    rw [Units.val_div_eq_div_val]
    field_simp
  have hphase : psiF.character (-(W : F) * (((W' / W : Fˣ) : F) - 1)) = 1 := by
    apply psiF.isConductor.trivial
    rw [harg]
    exact neg_mem_lattice F hdeep
  have hcritU : Stationary.commonFunctionProduct U thetaU (trivialQuasiCharData F)
      psiF psiU 1 C Y hCU hYU =
        Stationary.normalizedCriticalValue U thetaU psiU (normUnits U K C) e he zU := by
    dsimp only [Stationary.commonFunctionProduct]
    simp only [map_one, scaleAddCharData_character_apply, Units.val_one, one_mul]
    change _ * _ * (psiF.character (-(W : F) * (((W' / W : Fˣ) : F) - 1)) : ℂ) * _ = _
    rw [hphase, Units.val_one, mul_one]
    have htrivial (v : Fˣ) : (trivialQuasiCharData F).character v = 1 := rfl
    rw [htrivial, Units.val_one, inv_one, mul_one]
    rw [← hzU, ← hunit]
    simp only [add_sub_cancel_left, Stationary.normalizedCriticalValue]
  have hpoint := hU.trans hE.symm
  rw [hcritU, hcritE] at hpoint
  simpa only [Stationary.normalizedCriticalValue, map_one,
    scaleAddCharData_character_apply, Units.val_one, one_mul] using hpoint

set_option maxHeartbeats 1000000 in
/-- **The pointwise identity of the three actual residual functions**
(`D:UR:actualHidentity`). The residue field `kappa` is represented by that of
`U`; the upper edge over `U` is ramified. The scale on `F` is the actual norm
of the scale on `E`, and the scale on `U` is its actual image.

The theorem constructs a lower residue representative `X` for the same `x`
in the origin. The weighted coordinate uses `Cbar = Xbar + dbar`. Both
trace coordinates are actual field traces, and their pair is proved
bijective. `minimalCriticalLift` proves the three coordinate congruences,
nonvanishing of the perturbed traces, and `D:UR:extraUconstant` before the
full critical values are transported to residues. -/
theorem dyadicUR_minimal_critical_identity [PrimeCyclicExtension F E]
    (hunr : ramificationIndex F U = 1) (hsup : U ⊔ E = ⊤)
    (hchar : residueCharacteristic F = 2)
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1)
    {c : F} {d : U} {x : E}
    (hd : d ∈ lattice U 0) (hx : x ∈ lattice E 0)
    (thetaU : LocalQuasiCharData U) (thetaE : LocalQuasiCharData E)
    (hcondU : thetaU.conductor = t + 1) (hcondE : thetaE.conductor = t + 1)
    (Theta : ContinuousQuasiChar K)
    (hcU : normQuasiChar U K thetaU.character = Theta)
    (hcE : normQuasiChar E K thetaE.character = Theta)
    (tau : NormCharacter F E) (Psi : ContinuousAddChar F)
    (O : MinimalOriginData U E c d x t thetaU thetaE Psi)
    (D : MinimalOddElementaryData U E x t tau Psi O.origin)
    (a : Eˣ) (ha : ord E (a : E) = ((D.e : ℤ) : WithTop ℤ)) :
    let deltaF := normUnits F E a
    let deltaU := Units.map (algebraMap F U).toMonoidHom deltaF
    let hdeltaF : ord F (deltaF : F) = ((D.e : ℤ) : WithTop ℤ) := by
      change ord F (norm F E (a : E)) = _
      rw [ord_norm, hres, one_nsmul, ha]
    let hdeltaU : ord U (deltaU : U) = ((D.e : ℤ) : WithTop ℤ) := by
      change ord U (algebraMap F U (deltaF : F)) = _
      rw [ord_algebraMap, hunr, one_nsmul, hdeltaF]
    let HU := Stationary.normalizedResidualFunction U thetaU O.psiU 1
      (normUnits U K O.origin) D.e (by rw [hcondU, D.conductor_eq]) O.largeU deltaU hdeltaU
    let HE := Stationary.normalizedResidualFunction E thetaE O.psiE 1
      (normUnits E K O.origin) D.e (by rw [hcondE, D.conductor_eq]) O.largeE a ha
    let Htau := Stationary.normalizedResidualFunction F D.tauData D.psiData 1
      (Stationary.commonOriginLowerCoefficient E O.origin D.traceE_ne_zero) D.e
      (by rw [D.tau_conductor, D.conductor_eq]) D.large deltaF hdeltaF
    ∃ X : ringOfIntegers F,
      x - algebraMap F E (X : F) ∈ lattice E 1 ∧
      let Cbar := extensionResidueMap F U (residueMap F X) + reduce U d hd
      Function.Bijective (fun z : ResidueField U =>
        (trace (ResidueField F) (ResidueField U) z,
          (trace (ResidueField F) (ResidueField U) (Cbar * z)) ^ 2)) ∧
      ∀ z : ResidueField U,
        HU (z ^ 2) = HE (extensionResidueMap F E
          (trace (ResidueField F) (ResidueField U) z)) *
          Htau ((trace (ResidueField F) (ResidueField U) (Cbar * z)) ^ 2) := by
  letI : CharP (ResidueField F) 2 := ringChar.of_eq hchar
  have hU : Module.finrank F U = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F U
  have hE : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  have hK : Module.finrank F K = 4 := by
    rw [← IsGalois.card_aut_eq_finrank, IsKleinFour.card_four]
  have hdisj : U.LinearDisjoint E := by
    apply IntermediateField.LinearDisjoint.of_finrank_sup
    rw [hsup, IntermediateField.finrank_top', hK, hU, hE]
  let xO : ringOfIntegers E := ⟨x, (mem_lattice_zero_iff E).mp hx⟩
  obtain ⟨X, hX⟩ := exists_ringOfIntegers_sub_mem_maximalIdeal_of_residueDegree_eq_one F E hres xO
  have hxX : x - algebraMap F E (X : F) ∈ lattice E 1 :=
    (mem_lattice_one_iff_mem_maximalIdeal E
      (xO - algebraMap (ringOfIntegers F) (ringOfIntegers E) X)).mpr hX
  dsimp only
  refine ⟨X, hxX, ?_, ?_⟩
  · have hresU : Module.finrank (ResidueField F) (ResidueField U) = 2 := by
      rw [← residueDegree_eq_finrank_residueField]
      have h := finrank_eq_ramificationIndex_mul_residueDegree F U
      simpa only [hunr, hU, one_mul] using h.symm
    apply minimal_trace_coordinates_bijective (ResidueField F) (ResidueField U) hresU
    rw [map_add, trace_algebraMap, hresU, two_smul, CharTwo.add_self_eq_zero, zero_add]
    let dO : ringOfIntegers U := ⟨d, (mem_lattice_zero_iff U).mp hd⟩
    have hdtrace : integralTrace F U dO = 1 := by
      apply Subtype.ext
      rw [coe_integralTrace]
      exact O.d_trace
    change trace (ResidueField F) (ResidueField U) (residueMap U dO) = 1
    rw [residue_trace F U hunr, hdtrace, map_one]
  · intro r
    let z : ringOfIntegers U := teichmuller U r
    have hz : (z : U) ∈ lattice U 0 := (mem_lattice_zero_iff U).mpr z.property
    let dO : ringOfIntegers U := ⟨d, (mem_lattice_zero_iff U).mp hd⟩
    obtain ⟨V⟩ : Nonempty (MinimalCriticalLiftData U E D.e O.origin D.traceE_ne_zero
        d (X : F) (a : E) (z : U)) :=
      ⟨minimalCriticalLift U E hdisj hsup hunr hU hE ht hres hd hx O D
        (X : F) ((mem_lattice_zero_iff F).mpr X.property) hxX (a : E) ha (z : U) hz⟩
    let deltaF := normUnits F E a
    let deltaU := Units.map (algebraMap F U).toMonoidHom deltaF
    have hdeltaF : ord F (deltaF : F) = ((D.e : ℤ) : WithTop ℤ) := by
      change ord F (norm F E (a : E)) = _
      rw [ord_norm, hres, one_nsmul, ha]
    have hdeltaU : ord U (deltaU : U) = ((D.e : ℤ) : WithTop ℤ) := by
      change ord U (algebraMap F U (deltaF : F)) = _
      rw [ord_algebraMap, hunr, one_nsmul, hdeltaF]
    have hmU : thetaU.conductor = 2 * D.e + 1 := hcondU.trans D.conductor_eq
    have hmE : thetaE.conductor = 2 * D.e + 1 := hcondE.trans D.conductor_eq
    have hmF : D.tauData.conductor = 2 * D.e + 1 := D.tau_conductor.trans D.conductor_eq
    have hpsiU : O.psiU.character = D.psiData.character.compTrace := by
      rw [O.psiU_character, D.psi_character]
      rfl
    have hpsiE : O.psiE.character = D.psiData.character.compTrace := by
      rw [O.psiE_character, D.psi_character]
      rfl
    have hdeep : norm F U (trace U K (V.point : K)) -
        norm F U (trace U K (O.origin : K)) ∈ lattice F (-D.psiData.conductor) := by
      simpa only [D.psi_conductor, neg_neg, D.conductor_eq, Nat.cast_add,
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using V.extra_deep
    have hpoint := minimal_actual_critical_values U E thetaU thetaE Theta hcU hcE
      tau D.tauData D.tau_character D.psiData O.psiU O.psiE hpsiU hpsiE
      O.origin V.point D.traceU_ne_zero V.traceU_ne_zero D.traceE_ne_zero V.traceE_ne_zero
      hdeep D.e D.e_pos V.vU V.vE V.w V.normU_eq V.normE_eq V.lower_eq
    let zE : ringOfIntegers E :=
      algebraMap (ringOfIntegers F) (ringOfIntegers E) (integralTrace F U z)
    let zF : ringOfIntegers F := (X * integralTrace F U z + integralTrace F U (dO * z)) ^ 2
    have hzEcoe : (zE : E) = algebraMap F E (trace F U (z : U)) := by
      change algebraMap F E (integralTrace F U z : F) = _
      rw [coe_integralTrace]
    have hzFcoe : (zF : F) = ((X : F) * trace F U (z : U) + trace F U (d * (z : U))) ^ 2 := by
      change ((X : F) * (integralTrace F U z : F) + (integralTrace F U (dO * z) : F)) ^ 2 = _
      simp only [coe_integralTrace, Subring.coe_mul]
      rfl
    have hcoordU : (V.vU : U) - (deltaU : U) * ((z ^ 2 : ringOfIntegers U) : U) ∈
        lattice U ((D.e : ℤ) + 1) := by
      change (V.vU : U) - algebraMap F U (norm F E (a : E)) *
        ((z ^ 2 : ringOfIntegers U) : U) ∈ _
      rw [Subring.coe_pow]
      exact V.coordinateU
    have hvU := minimal_criticalValue_eq_residual U thetaU O.psiU (normUnits U K O.origin)
      D.e D.e_pos hmU O.stationaryU deltaU hdeltaU V.vU (z ^ 2) hcoordU
    have hvE := minimal_criticalValue_eq_residual E thetaE O.psiE (normUnits E K O.origin)
      D.e D.e_pos hmE O.stationaryE a ha V.vE zE (by rw [hzEcoe]; exact V.coordinateE)
    have hvF := minimal_criticalValue_eq_residual F D.tauData D.psiData
      (Stationary.commonOriginLowerCoefficient E O.origin D.traceE_ne_zero)
      D.e D.e_pos hmF D.stationary deltaF hdeltaF V.w zF (by rw [hzFcoe]; exact V.coordinateF)
    rw [hvU, hvE, hvF] at hpoint
    have htr (b : ringOfIntegers U) : residueMap F (integralTrace F U b) =
        trace (ResidueField F) (ResidueField U) (residueMap U b) :=
      (residue_trace F U hunr b).symm
    have hzEres : residueMap E zE = extensionResidueMap F E
        (trace (ResidueField F) (ResidueField U) r) := by
      rw [critical_residue_map, htr]
      simp only [z, residueMap_teichmuller]
    have hzFres : residueMap F zF =
        (trace (ResidueField F) (ResidueField U)
          ((extensionResidueMap F U (residueMap F X) + reduce U d hd) * r)) ^ 2 := by
      change residueMap F ((X * integralTrace F U z + integralTrace F U (dO * z)) ^ 2) = _
      rw [map_pow, map_add, map_mul, htr, htr, map_mul]
      simp only [z, residueMap_teichmuller]
      congr 1
      rw [add_mul, map_add, ← Algebra.smul_def, map_smul, smul_eq_mul]
      rfl
    rw [map_pow, show residueMap U z = r from residueMap_teichmuller U r,
      hzEres, hzFres] at hpoint
    exact hpoint

end ActualCharacters

end
end LanglandsSecondMainLemma.Dyadic.UR
