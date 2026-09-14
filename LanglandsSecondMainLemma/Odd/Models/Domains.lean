import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Odd.Models.Setup
import LanglandsFirstMainLemma.Ramification.PrimeCyclicPreparation
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Odd / Models / Domains

Paper Lemma `O:M:domains`: full minimal-character depths and norm domains.
The second depth uses `1+t+t₂`, including the lower-field conductor.

The unramified clause is stated for an arbitrary finite local-field compositum
square. Its two intermediate fields are constructed by adjoining the embedded
original fields to the new base. Degrees, total ramification and all four
breaks are proved to persist; no base-changed norm assertion is assumed.
-/

namespace LanglandsSecondMainLemma.Odd.Models

noncomputable section
open LanglandsFirstMainLemma

/-- The numerical part of Paper Lemma 8.1, before specializing to a diamond. -/
theorem modelDepth_bounds {p t δ : ℕ} (hp : 2 < p) (ht : 0 < t) :
    let q := (1 + t + (t + p * δ)) ⌈/⌉ p
    let q₂ := (1 + t + (t + δ)) ⌈/⌉ p
    0 < q ∧ 0 < q₂ ∧ q ≤ t + p * δ ∧ q₂ ≤ t + δ ∧
      q₂ ≤ q ∧ q₂ ≤ (q + (p - 1) * (t + 1)) / p := by
  dsimp only
  have hp0 : 0 < p := by omega
  have hpt : 2 * t + 1 ≤ p * t := by nlinarith
  have hδ : δ ≤ p * δ := by nlinarith
  have hq := le_smul_ceilDiv (b := 1 + t + (t + p * δ)) hp0
  have hq₂ := le_smul_ceilDiv (b := 1 + t + (t + δ)) hp0
  simp only [smul_eq_mul] at hq hq₂
  have hpos : 0 < (1 + t + (t + p * δ)) ⌈/⌉ p := by
    by_contra h; have hz : (1 + t + (t + p * δ)) ⌈/⌉ p = 0 := by omega
    rw [hz, mul_zero] at hq; omega
  have hpos₂ : 0 < (1 + t + (t + δ)) ⌈/⌉ p := by
    by_contra h; have hz : (1 + t + (t + δ)) ⌈/⌉ p = 0 := by omega
    rw [hz, mul_zero] at hq₂; omega
  refine ⟨hpos, hpos₂, ?_, ?_, ?_, ?_⟩
  · rw [ceilDiv_le_iff_le_mul hp0]
    nlinarith
  · rw [ceilDiv_le_iff_le_mul hp0]
    nlinarith
  · rw [ceilDiv_le_iff_le_mul hp0]
    omega
  · have hround : p * ((1 + t + (t + δ)) ⌈/⌉ p) ≤ 2 * t + δ + p := by
      rw [Nat.ceilDiv_eq_add_pred_div]
      have := Nat.div_mul_le_self (1 + t + (t + δ) + p - 1) p
      have he : 1 + t + (t + δ) + p - 1 = 2 * t + δ + p := by omega
      rw [he] at this ⊢
      simpa only [Nat.mul_comm] using this
    have hqδ : δ + 1 ≤ (1 + t + (t + p * δ)) ⌈/⌉ p := by
      by_contra h
      have hle : (1 + t + (t + p * δ)) ⌈/⌉ p ≤ δ := by omega
      have := Nat.mul_le_mul_left p hle
      omega
    rw [Nat.le_div_iff_mul_le hp0]
    have hpred : p - 1 + 1 = p := by omega
    nlinarith

section Cyclic
variable (E L : Type*) [Field E] [Field L]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra E L] [ValuativeExtension E L]
  [Module.Free E L] [Module.Finite E L] [PrimeCyclicExtension E L]

/-- Detection on every layer up to and including the break, for all nonzero
field elements (not only for elements already known to be principal units). -/
theorem norm_preimage_unitFiltration {t q : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak E L t)
    (hres : residueDegree E L = 1) (hq : q ≤ t) :
    (unitFiltration E q).comap (normUnits E L) = unitFiltration L q := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer E L hres
  ext u
  change normUnits E L u ∈ unitFiltration E q ↔ u ∈ unitFiltration L q
  constructor
  · intro hnu
    have hu0 : u ∈ unitFiltration L 0 := by
      have hn0 := unitFiltration_antitone E (Nat.zero_le q) hnu
      rw [mem_unitFiltration_zero] at hn0 ⊢
      simpa only [coe_normUnits, ord_norm, hres, one_nsmul] using hn0
    exact mem_unitFiltration_of_norm_mem_of_graded_injective E L (Nat.zero_le q)
      (fun i _ hi ↦ normMapsUnitFiltration_belowBreak E L ht (hi.trans hq)
        hres pi hpi hgen)
      (fun i _ hi ↦ (gradedNorm_bijective_belowBreak E L ht (hi.trans_le hq)
        hres pi hpi hgen).1) u hu0 hnu
  · exact normMapsUnitFiltration_belowBreak E L ht hq hres pi hpi hgen u

/-- The two numerical bounds used in the paper imply the second norm-domain
inclusion, by the successor form of FML's norm filtration. -/
theorem norm_maps_modelDepth {t q r : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak E L t)
    (hres : residueDegree E L = 1) (hr : 0 < r) (hrq : r ≤ q)
    (hfloor : r ≤ (q + (Module.finrank E L - 1) * (t + 1)) /
      Module.finrank E L) :
    NormMapsUnitFiltration E L q r := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer E L hres
  have hp : 0 < Module.finrank E L := Module.finrank_pos
  have hsource : herbrandPsiNat t (Module.finrank E L) (r - 1) + 1 ≤ q := by
    by_cases hrt : r - 1 ≤ t
    · rw [herbrandPsiNat_of_le_break _ _ hrt]
      omega
    · rw [herbrandPsiNat_of_break_le _ _ (by omega)]
      have hmul := (Nat.le_div_iff_mul_le hp).1 hfloor
      have he : Module.finrank E L - 1 + 1 = Module.finrank E L := by omega
      have hs : r - 1 - t + t + 1 = r := by omega
      nlinarith
  intro u hu
  have h := normMapsUnitFiltration_herbrand_succ E L ht hres pi hpi hgen (r - 1)
    u (unitFiltration_antitone L hsource hu)
  simpa only [Nat.sub_add_cancel hr] using h
end Cyclic

section Diamond
variable {F K : Type*} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]

omit [Module.Free F K] in
/-- Total ramification on both edges follows from transitivity of the
actual field norms, evaluated on an element of normalized order one. -/
private theorem intermediate_residueDegrees_one (L : IntermediateField F K)
    (hres : residueDegree F K = 1) :
    letI := Basic.intermediateFieldValuativeRel L
    letI := Basic.intermediateFieldTopology L
    letI := Basic.intermediateField_localField L
    letI := Basic.intermediateField_upperValuativeExtension L
    letI := Basic.intermediateField_lowerValuativeExtension L
    residueDegree F L = 1 ∧ residueDegree L K = 1 := by
  letI := Basic.intermediateFieldValuativeRel L
  letI := Basic.intermediateFieldTopology L
  letI := Basic.intermediateField_localField L
  letI := Basic.intermediateField_lowerValuativeExtension L
  letI := Basic.intermediateField_upperValuativeExtension L
  obtain ⟨x, hx⟩ := exists_ord_eq K 1
  have h := congrArg (ord F) (norm_trans F L K x)
  rw [ord_norm, ord_norm, ord_norm, hx, hres] at h
  norm_cast at h
  simp only [nsmul_eq_mul, mul_one, Nat.cast_one] at h
  have hn : residueDegree F L * residueDegree L K = 1 := by exact_mod_cast h
  exact mul_eq_one.mp hn

/-- Paper Lemma 8.1 (`O:M:domains`, `O:M:preimage`) for the actual two
intermediate fields of the totally ramified odd-degree diamond. The preimage
is taken in the full multiplicative group. No model character or choice of
norm representatives is assumed. -/
theorem domains_original {p : ℕ} {hp : p.Prime} {hG}
    (D : Total.OddTotalBreakData (F := F) (K := K) hp hG)
    (hres : residueDegree F K = 1) :
    let B₁ := D.B₁
    let B₂ := D.B₂
    letI := Basic.intermediateFieldValuativeRel B₁
    letI := Basic.intermediateFieldTopology B₁
    letI := Basic.intermediateField_localField B₁
    letI := Basic.intermediateFieldValuativeRel B₂
    letI := Basic.intermediateFieldTopology B₂
    letI := Basic.intermediateField_localField B₂
    0 < firstModelDepth D ∧ 0 < secondModelDepth D ∧
      firstModelDepth D ≤ D.tPrime ∧ secondModelDepth D ≤ D.t₂ ∧
      secondModelDepth D ≤ firstModelDepth D ∧
      secondModelDepth D ≤ (firstModelDepth D + (p - 1) * (D.t + 1)) / p ∧
      (unitFiltration B₁ (firstModelDepth D)).comap (normUnits B₁ K) =
        unitFiltration K (firstModelDepth D) ∧
      (unitFiltration K (firstModelDepth D)).map (normUnits B₂ K) ≤
        unitFiltration B₂ (secondModelDepth D) := by
  let B₁ := D.B₁
  let B₂ := D.B₂
  letI := Basic.intermediateFieldValuativeRel B₁
  letI := Basic.intermediateFieldTopology B₁
  letI := Basic.intermediateField_localField B₁
  letI := Basic.intermediateFieldValuativeRel B₂
  letI := Basic.intermediateFieldTopology B₂
  letI := Basic.intermediateField_localField B₂
  letI := Basic.intermediateField_upperValuativeExtension B₁
  letI := Basic.intermediateField_upperValuativeExtension B₂
  let E₁ := Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁
  let E₂ := Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
  letI : PrimeCyclicExtension B₁ K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension B₁ K E₁.2.2.2.2.2.2.2.2.2.2.2.2
  letI : PrimeCyclicExtension B₂ K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension B₂ K E₂.2.2.2.2.2.2.2.2.2.2.2.2
  have hb₁ : PrimeCyclicExtension.IsLowerBreak B₁ K D.tPrime := D.B₁_breaks.2
  have hb₂ : PrimeCyclicExtension.IsLowerBreak B₂ K D.t := D.B₂_breaks.2
  have hr₁ : residueDegree B₁ K = 1 := (intermediate_residueDegrees_one B₁ hres).2
  have hr₂ : residueDegree B₂ K = 1 := (intermediate_residueDegrees_one B₂ hres).2
  have hdeg₂ : Module.finrank B₂ K = p := E₂.2.2.2.2.2.2.2.2.2.2.1
  have hn := modelDepth_bounds (δ := D.delta) D.odd_prime D.t_pos
  change 0 < firstModelDepth D ∧ _
  have hnum :
      0 < firstModelDepth D ∧ 0 < secondModelDepth D ∧
      firstModelDepth D ≤ D.tPrime ∧ secondModelDepth D ≤ D.t₂ ∧
      secondModelDepth D ≤ firstModelDepth D ∧
      secondModelDepth D ≤ (firstModelDepth D + (p - 1) * (D.t + 1)) / p := by
    simpa only [firstModelDepth, secondModelDepth, firstModelConductor,
      secondModelConductor, D.tPrime_eq, D.t₂_eq] using hn
  obtain ⟨hqpos, hq₂pos, hqt, hq₂t₂, hq₂q, hfloor⟩ := hnum
  refine ⟨hqpos, hq₂pos, hqt, hq₂t₂, hq₂q, hfloor,
    norm_preimage_unitFiltration B₁ K hb₁ hr₁ hqt, ?_⟩
  have hmap := norm_maps_modelDepth B₂ K hb₂ hr₂ hq₂pos hq₂q
    (by simpa only [hdeg₂] using hfloor)
  rintro _ ⟨u, hu, rfl⟩
  exact hmap u hu
end Diamond

namespace BaseChange

open scoped TensorProduct

section Algebra
variable (E L E' L' : Type*) [Field E] [Field L] [Field E'] [Field L']
  [Algebra E L] [Algebra E E'] [Algebra E L']
  [Algebra L L'] [Algebra E' L']
  [IsScalarTower E L L'] [IsScalarTower E E' L']
  [Module.Finite E L]

theorem compositum_finrank_le
    (hgen : Algebra.adjoin E' (Set.range (algebraMap L L')) = ⊤) :
    Module.finrank E' L' ≤ Module.finrank E L := by
  let f : E' ⊗[E] L →ₐ[E'] L' :=
    AlgHom.liftEquiv E E' L L' (IsScalarTower.toAlgHom E L L')
  have hsur : Function.Surjective f := by
    rw [← AlgHom.range_eq_top]
    apply top_le_iff.mp
    rw [← hgen]
    apply Algebra.adjoin_le
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ[E] x, by simp [f]⟩
  have hle := LinearMap.finrank_le_finrank_of_surjective (f := f.toLinearMap) hsur
  simpa only [Module.finrank_baseChange] using hle
end Algebra

section Local
variable (E L E' L' : Type*) [Field E] [Field L] [Field E'] [Field L']
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel E'] [TopologicalSpace E'] [IsNonarchimedeanLocalField E']
  [ValuativeRel L'] [TopologicalSpace L'] [IsNonarchimedeanLocalField L']
  [Algebra E L] [Algebra E E'] [Algebra E L']
  [Algebra L L'] [Algebra E' L']
  [ValuativeExtension E L] [ValuativeExtension E E']
  [ValuativeExtension L L'] [ValuativeExtension E' L']
  [IsScalarTower E L L'] [IsScalarTower E E' L']
  [Module.Finite E L] [Module.Finite E' L']

theorem unramified_compositum_invariants
    (hgen : Algebra.adjoin E' (Set.range (algebraMap L L')) = ⊤)
    (hres : residueDegree E L = 1) (hunr : ramificationIndex E E' = 1) :
    Module.finrank E' L' = Module.finrank E L ∧
    ramificationIndex L L' = 1 ∧ residueDegree E' L' = 1 := by
  have hle := compositum_finrank_le E L E' L' hgen
  have he : ramificationIndex E L = Module.finrank E L := by
    simpa only [hres, mul_one] using (finrank_eq_ramificationIndex_mul_residueDegree E L).symm
  obtain ⟨x, hx⟩ := exists_ord_eq E 1
  have hmap : algebraMap L L' (algebraMap E L x) =
      algebraMap E' L' (algebraMap E E' x) := by
    rw [← IsScalarTower.algebraMap_apply E L L', ← IsScalarTower.algebraMap_apply E E' L']
  have ho := congrArg (ord L') hmap
  simp only [ord_algebraMap, hx, hunr, one_nsmul] at ho
  have hemul : ramificationIndex L L' * ramificationIndex E L =
      ramificationIndex E' L' := by
    norm_cast at ho
    simp only [nsmul_eq_mul, mul_one] at ho
    exact_mod_cast ho
  have hn := finrank_eq_ramificationIndex_mul_residueDegree E' L'
  rw [← hemul, he] at hn
  have hnpos : 0 < Module.finrank E L := Module.finrank_pos
  have hapos := ramificationIndex_pos L L'
  have hfpos := residueDegree_pos E' L'
  have hprod : ramificationIndex L L' * residueDegree E' L' = 1 := by
    have : Module.finrank E L *
        (ramificationIndex L L' * residueDegree E' L') ≤ Module.finrank E L := by
      nlinarith [hle]
    nlinarith
  obtain ⟨ha, hf⟩ := mul_eq_one.mp hprod
  exact ⟨by simpa only [ha, hf, one_mul, mul_one] using hn, ha, hf⟩
end Local

section Galois
variable (E L E' L' : Type*) [Field E] [Field L] [Field E'] [Field L']
  [Algebra E L] [Algebra E E'] [Algebra E L'] [Algebra L L'] [Algebra E' L']
  [IsScalarTower E L L'] [IsScalarTower E E' L']
  [FiniteDimensional E L] [IsGalois E L]

include E in
theorem galois_square (hgen : Algebra.adjoin E' (Set.range (algebraMap L L')) = ⊤) :
    IsGalois E' L' := by
  obtain ⟨p, hp, hsp⟩ := IsGalois.is_separable_splitting_field E L
  letI := hsp
  letI : Polynomial.IsSplittingField E' L' (p.map (algebraMap E E')) := by
    constructor
    · rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
      exact (Polynomial.IsSplittingField.splits L p).of_algHom (IsScalarTower.toAlgHom E L L')
    · have hr : (p.map (algebraMap E E')).rootSet L' = p.rootSet L' := by
        simp [Set.ext_iff, Polynomial.mem_rootSet']
      rw [hr, ← Algebra.adjoin_adjoin_of_tower E (S := E'),
        Polynomial.IsSplittingField.adjoin_rootSet_eq_range L p
          (IsScalarTower.toAlgHom E L L')]
      exact hgen
  exact IsGalois.of_separable_splitting_field (p := p.map (algebraMap E E')) hp.map


omit [FiniteDimensional E L] in
theorem restriction_square_injective
    (hgen : Algebra.adjoin E' (Set.range (algebraMap L L')) = ⊤) :
    Function.Injective (IntermediateField.restrictRestrictAlgEquivMapHom E L E' L') := by
  intro σ τ h
  apply AlgEquiv.coe_toAlgHom_injective
  apply AlgHom.ext_of_adjoin_eq_top hgen
  rintro _ ⟨x, rfl⟩
  change σ (algebraMap L L' x) = τ (algebraMap L L' x)
  have hx := congrArg (fun a : L ≃ₐ[E] L => algebraMap L L' (a x)) h
  simpa only [IntermediateField.restrictRestrictAlgEquivMapHom, MonoidHom.comp_apply,
    AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply, AlgEquiv.restrictNormal_commutes,
    MulSemiringAction.toAlgAut_apply, MulSemiringAction.toAlgEquiv_apply,
    AlgEquiv.smul_def] using hx

variable [FiniteDimensional E' L']
include E in
theorem primeCyclic_square [PrimeCyclicExtension E L]
    (hgen : Algebra.adjoin E' (Set.range (algebraMap L L')) = ⊤)
    (hdeg : Module.finrank E' L' = Module.finrank E L) :
    PrimeCyclicExtension E' L' := by
  exact ⟨galois_square E L E' L' hgen,
    isCyclic_of_injective (IntermediateField.restrictRestrictAlgEquivMapHom E L E' L')
      (restriction_square_injective E L E' L' hgen),
    hdeg ▸ PrimeCyclicExtension.degree_prime E L⟩

end Galois

section Break
variable (E L E' L' : Type*) [Field E] [Field L] [Field E'] [Field L']
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel E'] [TopologicalSpace E'] [IsNonarchimedeanLocalField E']
  [ValuativeRel L'] [TopologicalSpace L'] [IsNonarchimedeanLocalField L']
  [Algebra E L] [Algebra E E'] [Algebra E L'] [Algebra L L'] [Algebra E' L']
  [IsScalarTower E L L'] [IsScalarTower E E' L']
  [ValuativeExtension E L] [ValuativeExtension L L'] [ValuativeExtension E' L']
  [Module.Finite E L] [Module.Finite E' L']
  [PrimeCyclicExtension E L] [PrimeCyclicExtension E' L']

 theorem lowerBreak_of_unramified_square {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak E L t)
    (hres : residueDegree E L = 1) (hres' : residueDegree E' L' = 1)
    (hunr : ramificationIndex L L' = 1)
    (hinj : Function.Injective
      (IntermediateField.restrictRestrictAlgEquivMapHom E L E' L')) :
    PrimeCyclicExtension.IsLowerBreak E' L' t := by
  have hzero := lowerRamificationGroup_zero_eq_top_of_residueDegree_eq_one E' L' hres'
  let s := PrimeCyclicExtension.lowerBreakIndex E' L' hzero
  have hs := PrimeCyclicExtension.lowerBreakIndex_isLowerBreak E' L' hzero
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer E L hres
  let pi' : ringOfIntegers L' := algebraMap (ringOfIntegers L) (ringOfIntegers L') pi
  have hpi' : (ValuativeRel.valuation L').IsUniformizer (pi' : L') := by
    change (ValuativeRel.valuation L').IsUniformizer (algebraMap L L' (pi : L))
    rw [← ord_eq_one_iff_isUniformizer L', ord_algebraMap, hunr, one_nsmul,
      ord_uniformizer L hpi]
  have hgen' : Algebra.adjoin (ringOfIntegers E') ({pi'} : Set (ringOfIntegers L')) = ⊤ :=
    algebra_adjoin_uniformizer_eq_top_of_residueDegree_eq_one E' L' hres' pi' hpi'
  let tau' := PrimeCyclicExtension.generator E' L'
  let tau := IntermediateField.restrictRestrictAlgEquivMapHom E L E' L' tau'
  have htau' : tau' ≠ 1 := PrimeCyclicExtension.generator_ne_one E' L'
  have htau : tau ≠ 1 := by
    intro h
    apply htau'
    apply hinj
    simpa only [map_one] using h
  have hord := ord_galois_uniformizer_sub_eq_of_isLowerBreak E L ht pi hpi hgen htau
  have hord' := ord_galois_uniformizer_sub_eq_of_isLowerBreak E' L' hs pi' hpi' hgen' htau'
  have heq : tau' (pi' : L') - (pi' : L') =
      algebraMap L L' (tau (pi : L) - (pi : L)) := by
    rw [map_sub]
    change tau' (algebraMap L L' (pi : L)) - algebraMap L L' (pi : L) =
      algebraMap L L' (((MulSemiringAction.toAlgAut Gal(L'/E') E L') tau').restrictNormal L (pi : L)) -
        algebraMap L L' (pi : L)
    rw [AlgEquiv.restrictNormal_commutes]
    rfl
  rw [heq, ord_algebraMap, hunr, one_nsmul, hord] at hord'
  have hst : t = s := by
    have : t + 1 = s + 1 := by exact_mod_cast hord'
    omega
  exact hst.symm ▸ hs
end Break
end BaseChange

namespace BaseChange
section Fields
variable (L E' L' : Type*) [Field L] [Field E'] [Field L']
  [Algebra L L'] [Algebra E' L']
/-- The actual compositum of the embedded field with the new base. -/
def field : IntermediateField E' L' :=
  IntermediateField.adjoin E' (Set.range (algebraMap L L'))

def map : L →+* field L E' L' :=
  (algebraMap L L').codRestrict (field L E' L') fun x ↦
    IntermediateField.subset_adjoin E' _ (Set.mem_range_self x)
instance fieldAlgebra : Algebra L (field L E' L') := (map L E' L').toAlgebra
instance fieldTower : IsScalarTower L (field L E' L') L' :=
  IsScalarTower.of_algebraMap_eq' rfl

variable {E : Type*} [Field E] [Algebra E L] [Algebra E E'] [Algebra E L']
  [IsScalarTower E L L'] [IsScalarTower E E' L']
instance fieldLowerTower : IsScalarTower E L (field L E' L') := by
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  exact IsScalarTower.algebraMap_apply E L L' x

variable [ValuativeRel L] [ValuativeRel L'] [ValuativeExtension L L']
theorem fieldValuativeExtension :
    letI := Basic.intermediateFieldValuativeRel (field L E' L')
    ValuativeExtension L (field L E' L') := by
  letI := Basic.intermediateFieldValuativeRel (field L E' L')
  letI := Basic.intermediateField_upperValuativeExtension (field L E' L')
  constructor
  intro x y
  rw [← ValuativeExtension.vle_iff_vle (A := field L E' L') (B := L')]
  change algebraMap L L' x ≤ᵥ algebraMap L L' y ↔ x ≤ᵥ y
  exact ValuativeExtension.vle_iff_vle x y
end Fields
section Generation
variable (L E' L' : Type*) [Field L] [Field E'] [Field L']
  [Algebra L L'] [Algebra E' L'] [Module.Finite E' L']

theorem field_generation :
    Algebra.adjoin E' (Set.range (algebraMap L (field L E' L'))) = ⊤ := by
  rw [← IntermediateField.adjoin_eq_top_iff]
  apply IntermediateField.map_injective (field L E' L').val
  rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map,
    IntermediateField.fieldRange_val]
  change IntermediateField.adjoin E' (_ '' Set.range _) =
    IntermediateField.adjoin E' (Set.range (algebraMap L L'))
  congr 1
  rw [← Set.range_comp]
  rfl

variable (E : Type*) [Field E] [Algebra E L'] [Algebra E E'] [IsScalarTower E E' L']

omit [Module.Finite E' L'] in
theorem upper_generation (s : Set L') (hgen : Algebra.adjoin E' s = ⊤) :
    Algebra.adjoin (field L E' L') s = ⊤ := by
  let C := Algebra.adjoin (field L E' L') s
  have hle : Algebra.adjoin E' s ≤ C.restrictScalars E' := by
    exact Algebra.adjoin_le Algebra.subset_adjoin
  rw [hgen] at hle
  exact SetLike.ext fun x ↦ ⟨fun _ ↦ trivial, fun _ ↦ hle trivial⟩
end Generation
end BaseChange

section BaseChangeDiamond
variable {F K : Type*} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Finite F K] [IsGalois F K]
variable (F' K' : Type*) [Field F'] [Field K']
  [ValuativeRel F'] [TopologicalSpace F'] [IsNonarchimedeanLocalField F']
  [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
  [Algebra F F'] [Algebra F K'] [Algebra K K'] [Algebra F' K']
  [IsScalarTower F K K'] [IsScalarTower F F' K']
  [ValuativeExtension F F'] [ValuativeExtension K K'] [ValuativeExtension F' K']
  [Module.Finite F F'] [Module.Finite F' K']

/-- An induced intermediate tower has both original degrees and both original
breaks. Unramifiedness of its base extension is a conclusion of the construction. -/
theorem baseChange_intermediate {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (B : IntermediateField F K) (hB : Module.finrank F B = p)
    (hres : residueDegree F K = 1)
    (hunr : ramificationIndex F F' = 1)
    (hgen : Algebra.adjoin F' (Set.range (algebraMap K K')) = ⊤) :
    letI := Basic.intermediateFieldValuativeRel B
    letI := Basic.intermediateFieldTopology B
    letI := Basic.intermediateField_localField B
    letI := Basic.intermediateField_lowerValuativeExtension B
    letI := Basic.intermediateField_upperValuativeExtension B
    ∀ {s t : ℕ}, PrimeCyclicExtension.IsLowerBreak F B s →
      PrimeCyclicExtension.IsLowerBreak B K t →
    let B' := BaseChange.field B F' K'
    letI := Basic.intermediateFieldValuativeRel B'
    letI := Basic.intermediateFieldTopology B'
    letI := Basic.intermediateField_localField B'
    letI := Basic.intermediateField_lowerValuativeExtension B'
    letI := Basic.intermediateField_upperValuativeExtension B'
    Module.finrank F' B' = p ∧ Module.finrank B' K' = p ∧
      CyclicPrimeExtension F' B' ∧ CyclicPrimeExtension B' K' ∧
      residueDegree F' B' = 1 ∧ residueDegree B' K' = 1 ∧
      PrimeCyclicExtension.IsLowerBreak F' B' s ∧
      PrimeCyclicExtension.IsLowerBreak B' K' t := by
  letI := Basic.intermediateFieldValuativeRel B
  letI := Basic.intermediateFieldTopology B
  letI := Basic.intermediateField_localField B
  letI := Basic.intermediateField_lowerValuativeExtension B
  letI := Basic.intermediateField_upperValuativeExtension B
  intro s t hs ht
  let data := Basic.intermediateField_tower_compatible hp hG B hB
  letI : PrimeCyclicExtension F B :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F B data.2.2.2.2.2.2.2.2.2.2.2.1
  letI : PrimeCyclicExtension B K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension B K data.2.2.2.2.2.2.2.2.2.2.2.2
  letI : ValuativeExtension B K' := ⟨fun x y ↦ by
    rw [IsScalarTower.algebraMap_apply B K K', IsScalarTower.algebraMap_apply B K K',
      ValuativeExtension.vle_iff_vle, ValuativeExtension.vle_iff_vle]⟩
  let B' := BaseChange.field B F' K'
  letI := Basic.intermediateFieldValuativeRel B'
  letI := Basic.intermediateFieldTopology B'
  letI := Basic.intermediateField_localField B'
  letI := Basic.intermediateField_lowerValuativeExtension B'
  letI := Basic.intermediateField_upperValuativeExtension B'
  letI := BaseChange.fieldValuativeExtension B F' K'
  have hr := intermediate_residueDegrees_one B hres
  have hg₀ := BaseChange.field_generation B F' K'
  have hg₁ := BaseChange.upper_generation B F' K' (Set.range (algebraMap K K')) hgen
  have hlower := BaseChange.unramified_compositum_invariants F B F' B' hg₀ hr.1 hunr
  have hupper := BaseChange.unramified_compositum_invariants B K B' K' hg₁ hr.2 hlower.2.1
  letI := BaseChange.primeCyclic_square F B F' B' hg₀ hlower.1
  letI := BaseChange.primeCyclic_square B K B' K' hg₁ hupper.1
  exact ⟨hlower.1.trans hB, hupper.1.trans data.2.2.2.2.2.2.2.2.2.2.1,
    PrimeCyclicExtension.toCyclicPrimeExtension, PrimeCyclicExtension.toCyclicPrimeExtension,
    hlower.2.2, hupper.2.2,
    BaseChange.lowerBreak_of_unramified_square F B F' B' hs hr.1 hlower.2.2 hlower.2.1
      (BaseChange.restriction_square_injective F B F' B' hg₀),
    BaseChange.lowerBreak_of_unramified_square B K B' K' ht hr.2 hupper.2.2 hupper.2.1
      (BaseChange.restriction_square_injective B K B' K' hg₁)⟩

/-- The eight assertions of `O:M:domains` for three specified actual fields.
The two depths are explicit, so a base change uses exactly the original depths. -/
def DomainAssertions (B₁ B₂ L : Type*) [Field B₁] [Field B₂] [Field L]
    [ValuativeRel B₁] [TopologicalSpace B₁] [IsNonarchimedeanLocalField B₁]
    [ValuativeRel B₂] [TopologicalSpace B₂] [IsNonarchimedeanLocalField B₂]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra B₁ L] [Algebra B₂ L]
    (p t t₂ tPrime q q₂ : ℕ) : Prop :=
  0 < q ∧ 0 < q₂ ∧ q ≤ tPrime ∧ q₂ ≤ t₂ ∧ q₂ ≤ q ∧
    q₂ ≤ (q + (p - 1) * (t + 1)) / p ∧
    (unitFiltration B₁ q).comap (normUnits B₁ L) = unitFiltration L q ∧
    (unitFiltration L q).map (normUnits B₂ L) ≤ unitFiltration B₂ q₂

/-- Paper Lemma `O:M:domains`, including its final unramified-base clause.

`F'` is any finite unramified extension of `F`, and `K'` is any genuine local
realization of the compositum `F'K`. The hypothesis `hgen` expresses only that
compositum, not a ramification or norm conclusion. The two induced fields are
constructed as `F'[Bᵢ]` inside `K'`. Both original and induced norm assertions
use `firstModelDepth D` and `secondModelDepth D`, hence the complete second
conductor `1 + D.t + D.t₂`. All four induced breaks are proved equal to the
original ones. This formulation does not separately construct an ambient
local compositum from an abstract extension `F'/F`. -/
theorem domains {p : ℕ} {hp : p.Prime} {hG}
    (D : Total.OddTotalBreakData (F := F) (K := K) hp hG)
    (hres : residueDegree F K = 1)
    (hunr : ramificationIndex F F' = 1)
    (hgen : Algebra.adjoin F' (Set.range (algebraMap K K')) = ⊤) :
    let B₁ := D.B₁
    let B₂ := D.B₂
    letI := Basic.intermediateFieldValuativeRel B₁
    letI := Basic.intermediateFieldTopology B₁
    letI := Basic.intermediateField_localField B₁
    letI := Basic.intermediateFieldValuativeRel B₂
    letI := Basic.intermediateFieldTopology B₂
    letI := Basic.intermediateField_localField B₂
    let B₁' := BaseChange.field B₁ F' K'
    let B₂' := BaseChange.field B₂ F' K'
    letI := Basic.intermediateFieldValuativeRel B₁'
    letI := Basic.intermediateFieldTopology B₁'
    letI := Basic.intermediateField_localField B₁'
    letI := Basic.intermediateField_lowerValuativeExtension B₁'
    letI := Basic.intermediateField_upperValuativeExtension B₁'
    letI := Basic.intermediateFieldValuativeRel B₂'
    letI := Basic.intermediateFieldTopology B₂'
    letI := Basic.intermediateField_localField B₂'
    letI := Basic.intermediateField_lowerValuativeExtension B₂'
    letI := Basic.intermediateField_upperValuativeExtension B₂'
    DomainAssertions B₁ B₂ K p D.t D.t₂ D.tPrime
      (firstModelDepth D) (secondModelDepth D) ∧
    DomainAssertions B₁' B₂' K' p D.t D.t₂ D.tPrime
      (firstModelDepth D) (secondModelDepth D) ∧
    PrimeCyclicExtension.IsLowerBreak F' B₁' D.t ∧
    PrimeCyclicExtension.IsLowerBreak B₁' K' D.tPrime ∧
    PrimeCyclicExtension.IsLowerBreak F' B₂' D.t₂ ∧
    PrimeCyclicExtension.IsLowerBreak B₂' K' D.t := by
  let B₁ := D.B₁
  let B₂ := D.B₂
  letI := Basic.intermediateFieldValuativeRel B₁
  letI := Basic.intermediateFieldTopology B₁
  letI := Basic.intermediateField_localField B₁
  letI := Basic.intermediateField_lowerValuativeExtension B₁
  letI := Basic.intermediateField_upperValuativeExtension B₁
  letI := Basic.intermediateFieldValuativeRel B₂
  letI := Basic.intermediateFieldTopology B₂
  letI := Basic.intermediateField_localField B₂
  letI := Basic.intermediateField_lowerValuativeExtension B₂
  letI := Basic.intermediateField_upperValuativeExtension B₂
  let B₁' := BaseChange.field B₁ F' K'
  let B₂' := BaseChange.field B₂ F' K'
  letI := Basic.intermediateFieldValuativeRel B₁'
  letI := Basic.intermediateFieldTopology B₁'
  letI := Basic.intermediateField_localField B₁'
  letI := Basic.intermediateField_lowerValuativeExtension B₁'
  letI := Basic.intermediateField_upperValuativeExtension B₁'
  letI := Basic.intermediateFieldValuativeRel B₂'
  letI := Basic.intermediateFieldTopology B₂'
  letI := Basic.intermediateField_localField B₂'
  letI := Basic.intermediateField_lowerValuativeExtension B₂'
  letI := Basic.intermediateField_upperValuativeExtension B₂'
  have h₁ := baseChange_intermediate F' K' hp hG B₁ D.degree_B₁ hres hunr hgen
    D.B₁_breaks.1 D.B₁_breaks.2
  have h₂ := baseChange_intermediate F' K' hp hG B₂ D.degree_B₂ hres hunr hgen
    D.B₂_breaks.1 D.B₂_breaks.2
  rcases h₁ with ⟨_, _, hc₁, hu₁, _, hr₁, hs₁, ht₁⟩
  rcases h₂ with ⟨_, hd₂, hc₂, hu₂, _, hr₂, hs₂, ht₂⟩
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension B₁' K' hu₁
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension B₂' K' hu₂
  have hOriginal := domains_original D hres
  refine ⟨hOriginal, ?_, hs₁, ht₁, hs₂, ht₂⟩
  rcases hOriginal with ⟨hq, hq₂, hqt, hq₂t₂, hq₂q, hfloor, _, _⟩
  refine ⟨hq, hq₂, hqt, hq₂t₂, hq₂q, hfloor,
    norm_preimage_unitFiltration B₁' K' ht₁ hr₁ hqt, ?_⟩
  have hdegree₂ : Module.finrank B₂' K' = p := hd₂
  have hmap := norm_maps_modelDepth B₂' K' ht₂ hr₂ hq₂ hq₂q
    (by simpa only [hdegree₂] using hfloor)
  rintro _ ⟨u, hu, rfl⟩
  exact hmap u hu

end BaseChangeDiamond

end
end LanglandsSecondMainLemma.Odd.Models
