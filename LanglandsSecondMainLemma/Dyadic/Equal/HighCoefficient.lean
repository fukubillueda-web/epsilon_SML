import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsFirstMainLemma.Ramification.NormRepresentatives
import LanglandsSecondMainLemma.Dyadic.Equal.Origin
import LanglandsSecondMainLemma.Dyadic.Equal.Twist

/-!
# Dyadic / Equal / High Coefficient

Paper Lemma 11.12, `D:EQ:highcoef` and `D:EQ:highcorrection`.
The norm representatives are only accurate through the lower break.
All depths below are integers, including the orders of the representatives.
-/

namespace LanglandsSecondMainLemma.Dyadic.Equal

noncomputable section

open LanglandsFirstMainLemma
open private originLine_degrees origin_residueDegrees from
  LanglandsSecondMainLemma.Dyadic.Equal.Origin
open private depth_ledger edge_ramification norm_one_sub_charTwo from
  LanglandsSecondMainLemma.Dyadic.Equal.Compatibility
open private lowerCyclic pullback_conductors from
  LanglandsSecondMainLemma.Dyadic.Equal.Twist

private theorem phase_eq_of_sub_mem {E : Type} [Field E]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    (ψ : ContinuousAddChar E) {J : ℤ} (hψ : IsAdditiveConductor E ψ (-J))
    {x y : E} (hxy : x - y ∈ lattice E J) : ψ x = ψ y := by
  have h := hψ.trivial (x - y) (by simpa using hxy)
  have he : x = (x - y) + y := by ring
  rw [he, ContinuousAddChar.map_add_eq_mul, h, one_mul]

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  [CharP F 2] [CharP K 2] [IsKleinFour Gal(K/F)]

local instance highCoefficientValuativeRel (L : IntermediateField F K) : ValuativeRel L :=
  Basic.intermediateFieldValuativeRel L
local instance highCoefficientTopology (L : IntermediateField F K) : TopologicalSpace L :=
  Basic.intermediateFieldTopology L
local instance highCoefficientLocalField (L : IntermediateField F K) : IsNonarchimedeanLocalField L :=
  Basic.intermediateField_localField L
local instance highCoefficientLowerExtension (L : IntermediateField F K) : ValuativeExtension F L :=
  Basic.intermediateField_lowerValuativeExtension L
local instance highCoefficientUpperExtension (L : IntermediateField F K) : ValuativeExtension L K :=
  Basic.intermediateField_upperValuativeExtension L
local instance highCoefficientIsGalois (L : IntermediateField F K) : IsGalois F L := by
  letI : IsMulCommutative Gal(K/F) := IsKleinFour.isMulCommutative
  letI : L.fixingSubgroup.Normal := inferInstance
  have h := IsGalois.of_fixedField_normal_subgroup L.fixingSubgroup
  rwa [IsGalois.fixedField_fixingSubgroup L] at h

namespace SimultaneousASGenerators
variable {P : Residues.EqualCharacteristicPresentation F}
  (G : SimultaneousASGenerators F K P)

/-- The full nonzero lower coefficient, with its constructed square root. -/
def betaUnit (i : Fin 3) : Fˣ := Units.mk0 (G.beta i) (by
  intro hz
  have h := (G.scalar_data i).2.2.1
  rw [hz, ord_zero] at h
  exact WithTop.top_ne_coe h)

/-- `h₀ = r₁ + 2r₂ - 1`. -/
def highThreshold : ℤ := G.lowerDepth 0 + (G.t 1 : ℤ)

/-- The complete upstairs stationary depth `bᵢ = n - rᵢ`. -/
def highDepth (h : ℤ) (i : Fin 3) : ℤ :=
  (G.t 1 : ℤ) + 1 + h - G.lowerDepth i

omit [IsGalois F K] [CharP F 2] [CharP K 2] in
private theorem high_ledger {h : ℤ} (hh : G.highThreshold ≤ h) (i : Fin 3) :
    let T : ℤ := (G.t 1 : ℤ) + 1
    let r := G.lowerDepth i
    let b := G.highDepth h i
    0 < r ∧ 2 * r = (G.t i : ℤ) + 1 ∧ (G.t i : ℤ) + 1 ≤ T ∧
      0 < h + T - ((G.t i : ℤ) + 1) ∧
      (G.stationaryDepth i : ℤ) ≤ h + T - ((G.t i : ℤ) + 1) ∧
      r ≤ h - (G.t 0 : ℤ) - (T - ((G.t i : ℤ) + 1)) ∧
      T ≤ h - (G.t 0 : ℤ) + (G.t i : ℤ) ∧
      (T + h + 1) / 2 ≤ b ∧
      (T + h + 1) / 2 ≤ (b + ((G.t i : ℤ) + 1)) / 2 ∧
      T ≤ -h + (G.t i : ℤ) + b := by
  have hd := depth_ledger G i
  have hsmall := G.smallest
  have hle : G.t i ≤ G.t 1 := by
    fin_cases i
    · exact G.smallest
    · exact le_rfl
    · exact G.third_break.le
  obtain ⟨a, ha⟩ := (G.edge 0).2.2.2.2.1
  obtain ⟨b, hb⟩ := (G.edge i).2.2.2.2.1
  have hpos := (G.edge 0).2.2.2.1
  dsimp only [highThreshold, highDepth, lowerDepth] at *
  omega

omit [CharP K 2] in
/-- Apply the proved whole-ideal phase conversion to the retained AS edge. -/
private theorem high_normPhase (hres : residueDegree F K = 1) (i : Fin 3)
    (z : G.field i) (hz : z ∈ lattice (G.field i) (G.lowerDepth i)) :
    tracePullbackAddChar F (G.field i) (originAddChar F P ((G.t 1 : ℤ) + 1))
        (algebraMap F (G.field i) (G.beta i) * z) =
      originAddChar F P ((G.t 1 : ℤ) + 1) (G.beta i * Algebra.norm F z) := by
  obtain ⟨heq, _, hred, ht, hodd, _, hf, _, hdiff⟩ := G.edge i
  have hf' : ord F (G.f i) = ((-(G.t i : ℤ) : ℤ) : WithTop ℤ) := by
    rw [← P.laurentEquiv.apply_symm_apply (G.f i), P.laurentEquiv_order]
    exact hf
  have hr := (depth_ledger G i).2.2.1
  have hdepth : (G.t i : ℤ) + 1 ≤ 2 * G.lowerDepth i := by
    obtain ⟨r, hr⟩ := hodd
    dsimp [lowerDepth]
    omega
  exact originAddChar_normPhase F (G.field i)
    (originLine_degrees F K (G.g i) (G.nontrivial i)).1
    (origin_residueDegrees F K hres (G.field i)).1 P (G.f i) (G.z i) heq
    (G.t i) (G.lowerDepth i) (G.t 1) hr hdepth
    (by rw [hdiff]; dsimp [lowerDepth]; omega) hred hf'.ge z hz

/-- FML constructs the actual element at precision `tᵢ`; no exact norm
equation or approximation at `tᵢ + 1` is requested. -/
theorem highApproximation_exists (hres : residueDegree F K = 1)
    {h : ℤ} (a : Fˣ) (ha : ord F (a : F) = ((-h : ℤ) : WithTop ℤ))
    (i : Fin 3) :
    ∃ x : (G.field i)ˣ,
      IsSubcriticalNormRepresentative F (G.field i)
        (-h - ((G.t 1 : ℤ) - (G.t i : ℤ))) (G.t i) (a / G.betaUnit i) x := by
  letI := lowerCyclic G i
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F (G.field i)
    (origin_residueDegrees F K hres (G.field i)).1
  apply normRepresentative_subcritical F (G.field i) (G.edge i).2.2.2.2.2.2.2.1
    (origin_residueDegrees F K hres (G.field i)).1 pi hpi hgen le_rfl
  rw [Units.val_div_eq_div_val]
  change ord F ((a : F) / G.beta i) = _
  rw [ord_div, ha, (G.scalar_data i).2.2.1,
    ← WithTop.LinearOrderedAddCommGroup.coe_sub]

private theorem high_error {h : ℤ} (a : Fˣ) (i : Fin 3) (x : (G.field i)ˣ)
    (hx : IsSubcriticalNormRepresentative F (G.field i)
      (-h - ((G.t 1 : ℤ) - (G.t i : ℤ))) (G.t i) (a / G.betaUnit i) x) :
    (a : F) - G.beta i * Algebra.norm F (x : G.field i) ∈
      lattice F (-h + (G.t i : ℤ)) := by
  have he := mul_mem_lattice F (G.scalar_data i).2.2.1.ge hx.norm_congruent
  have hβ : G.beta i ≠ 0 := (G.betaUnit i).ne_zero
  have heq : G.beta i * ((a : F) / G.beta i - Algebra.norm F (x : G.field i)) =
      (a : F) - G.beta i * Algebra.norm F (x : G.field i) := by
    field_simp
  simp only [Units.val_div_eq_div_val, betaUnit, Units.val_mk0] at he
  change G.beta i * ((a : F) / G.beta i - Algebra.norm F (x : G.field i)) ∈
    lattice F ((G.t 1 : ℤ) - (G.t i : ℤ) +
      (-h - ((G.t 1 : ℤ) - (G.t i : ℤ)) + (G.t i : ℤ))) at he
  rw [heq] at he
  have hd : (G.t 1 : ℤ) - (G.t i : ℤ) +
      (-h - ((G.t 1 : ℤ) - (G.t i : ℤ)) + (G.t i : ℤ)) =
      -h + (G.t i : ℤ) := by ring
  rwa [hd] at he

private theorem high_orders (hres : residueDegree F K = 1)
    {h : ℤ} (hh : G.highThreshold ≤ h) (a : Fˣ)
    (ha : ord F (a : F) = ((-h : ℤ) : WithTop ℤ)) (i : Fin 3)
    (x : (G.field i)ˣ)
    (hx : IsSubcriticalNormRepresentative F (G.field i)
      (-h - ((G.t 1 : ℤ) - (G.t i : ℤ))) (G.t i) (a / G.betaUnit i) x) :
    let L := G.field i
    let v := algebraMap F L (G.beta i) * (x : L) / algebraMap F L (a : F)
    ord L (algebraMap F L (a : F) + algebraMap F L (G.beta i) * (x : L)) =
        ((-2 * h : ℤ) : WithTop ℤ) ∧
      ord L v = ((h + (G.t 1 : ℤ) - (G.t i : ℤ) : ℤ) : WithTop ℤ) ∧
      ord L (Algebra.norm L G.Y * (x : L) / algebraMap F L (a : F)) =
        ((h - (G.t 0 : ℤ) - ((G.t 1 : ℤ) - (G.t i : ℤ)) : ℤ) : WithTop ℤ) := by
  have haL : ord (G.field i) (algebraMap F (G.field i) (a : F)) =
      ((-2 * h : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, (edge_ramification G hres i).1, ha,
      ← WithTop.coe_nsmul]
    congr 1
    simp
  have hbx : ord (G.field i) (algebraMap F (G.field i) (G.beta i) * (x : G.field i)) =
      (((G.t 1 : ℤ) - (G.t i : ℤ) - h : ℤ) : WithTop ℤ) := by
    rw [ord_mul, ord_algebraMap, (edge_ramification G hres i).1,
      (G.scalar_data i).2.2.1, hx.source_order, ← WithTop.coe_nsmul,
      ← WithTop.coe_add]
    congr 1
    simp
    ring
  have hlt : ord (G.field i) (algebraMap F (G.field i) (a : F)) <
      ord (G.field i) (algebraMap F (G.field i) (G.beta i) * (x : G.field i)) := by
    rw [haL, hbx]
    apply WithTop.coe_lt_coe.mpr
    have hb := (G.high_ledger hh i).2.2.2.1
    omega
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [ord_add_eq_min _ hlt.ne, min_eq_left hlt.le, haL]
  · rw [ord_div, hbx, haL, ← WithTop.LinearOrderedAddCommGroup.coe_sub]
    congr 1
    ring
  · rw [ord_div, ord_mul, ((G.origin_orders hres).2.1 i).1,
      hx.source_order, haL, ← WithTop.coe_add,
      ← WithTop.LinearOrderedAddCommGroup.coe_sub]
    congr 1
    ring

/-- The coefficient formula holds on the entire half-conductor ideal.
The error estimate uses the approximate norm only at its supplied precision. -/
private theorem high_stationary (hres : residueDegree F K = 1)
    {h : ℤ} (hh : G.highThreshold ≤ h) (a : Fˣ)
    (lambda : ContinuousQuasiChar F)
    (hbase : ∀ u : Fˣ,
      1 - (u : F) ∈ lattice F (((G.t 1 : ℤ) + 1 + h + 1) / 2) →
        lambda u = originAddChar F P ((G.t 1 : ℤ) + 1) ((a : F) * (1 - (u : F))))
    (i : Fin 3) (x : (G.field i)ˣ)
    (hx : IsSubcriticalNormRepresentative F (G.field i)
      (-h - ((G.t 1 : ℤ) - (G.t i : ℤ))) (G.t i) (a / G.betaUnit i) x)
    (u : (G.field i)ˣ) (hu : 1 - (u : G.field i) ∈ lattice (G.field i) (G.highDepth h i)) :
    normQuasiChar F (G.field i) lambda u =
      tracePullbackAddChar F (G.field i) (originAddChar F P ((G.t 1 : ℤ) + 1))
        ((algebraMap F (G.field i) (a : F) +
          algebraMap F (G.field i) (G.beta i) * (x : G.field i)) *
          (1 - (u : G.field i))) := by
  let L := G.field i
  let Ψ := originAddChar F P ((G.t 1 : ℤ) + 1)
  let ΨL := tracePullbackAddChar F L Ψ
  let z : L := 1 - (u : L)
  obtain ⟨hr, hr2, _, _, _, _, _, hbn, hbt, herr⟩ := G.high_ledger hh i
  have hn : Algebra.norm F z ∈ lattice F (G.highDepth h i) := by
    change (G.highDepth h i : WithTop ℤ) ≤ ord F (norm F L z)
    rw [ord_norm, (origin_residueDegrees F K hres L).1, one_nsmul]
    exact hu
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F L
    (origin_residueDegrees F K hres L).1
  have ht := trace_mem_lattice_floor F L pi hpi hgen (G.highDepth h i) hu
  rw [(edge_ramification G hres i).1, (G.edge i).2.2.2.2.2.2.2.2] at ht
  have hinc : 1 - (normUnits F L u : F) = Algebra.trace F L z + Algebra.norm F z := by
    have he := norm_one_sub_charTwo F L
      (originLine_degrees F K (G.g i) (G.nontrivial i)).1 z
    have hz : 1 - z = (u : L) := by dsimp [z]; ring
    rw [hz] at he
    change 1 - Algebra.norm F (u : L) = _
    rw [he, CharTwo.sub_eq_add]
    simp only [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hincmem : 1 - (normUnits F L u : F) ∈
      lattice F (((G.t 1 : ℤ) + 1 + h + 1) / 2) := by
    rw [hinc]
    exact add_mem_lattice F (lattice_antitone F hbt ht) (lattice_antitone F hbn hn)
  have hxz : (x : L) * z ∈ lattice L (G.lowerDepth i) := by
    have he := mul_mem_lattice L hx.source_order.ge hu
    have hd : -h - ((G.t 1 : ℤ) - (G.t i : ℤ)) + G.highDepth h i =
        G.lowerDepth i := by dsimp [highDepth]; omega
    rwa [hd] at he
  have hp := G.high_normPhase hres i ((x : L) * z) hxz
  change ΨL (algebraMap F L (G.beta i) * ((x : L) * z)) =
    Ψ (G.beta i * Algebra.norm F ((x : L) * z)) at hp
  rw [map_mul (Algebra.norm F) (x : L) z] at hp
  have he : Ψ ((a : F) * Algebra.norm F z) =
      Ψ (G.beta i * (Algebra.norm F (x : L) * Algebra.norm F z)) := by
    apply phase_eq_of_sub_mem Ψ (originAddChar_conductor F P ((G.t 1 : ℤ) + 1))
    have he := mul_mem_lattice F (G.high_error a i x hx) hn
    have he' := lattice_antitone F herr he
    convert he' using 1
    ring
  have htrace : ΨL (algebraMap F L (a : F) * z) = Ψ ((a : F) * Algebra.trace F L z) := by
    change Ψ (Algebra.trace F L (algebraMap F L (a : F) * z)) = _
    rw [← Algebra.smul_def, map_smul, Algebra.smul_def, Algebra.algebraMap_self_apply]
  change lambda (normUnits F L u) = ΨL (_ * z)
  rw [hbase _ hincmem, hinc, mul_add, ContinuousAddChar.map_add_eq_mul]
  rw [add_mul, ContinuousAddChar.map_add_eq_mul, htrace, mul_assoc, hp, he]

/-- The second use of the phase conversion retains the full actual norm
of `Y`. Deleting the approximation error is justified at depth `T₂`. -/
private theorem high_corePhase (hres : residueDegree F K = 1)
    {h : ℤ} (hh : G.highThreshold ≤ h) (a : Fˣ)
    (ha : ord F (a : F) = ((-h : ℤ) : WithTop ℤ)) (i : Fin 3)
    (x : (G.field i)ˣ)
    (hx : IsSubcriticalNormRepresentative F (G.field i)
      (-h - ((G.t 1 : ℤ) - (G.t i : ℤ))) (G.t i) (a / G.betaUnit i) x) :
    tracePullbackAddChar F (G.field i) (originAddChar F P ((G.t 1 : ℤ) + 1))
      (Algebra.norm (G.field i) G.Y *
        (algebraMap F (G.field i) (G.beta i) * (x : G.field i) /
          algebraMap F (G.field i) (a : F))) =
      originAddChar F P ((G.t 1 : ℤ) + 1) (Algebra.norm F G.Y / (a : F)) := by
  let L := G.field i
  let Ψ := originAddChar F P ((G.t 1 : ℤ) + 1)
  let ΨL := tracePullbackAddChar F L Ψ
  let q : L := Algebra.norm L G.Y * (x : L) / algebraMap F L (a : F)
  obtain ⟨_, _, _, _, _, hq, herr, _, _, _⟩ := G.high_ledger hh i
  have hqmem : q ∈ lattice L (G.lowerDepth i) := by
    change (G.lowerDepth i : WithTop ℤ) ≤ ord L q
    rw [(G.high_orders hres hh a ha i x hx).2.2]
    exact WithTop.coe_le_coe.mpr (by omega)
  have hp := G.high_normPhase hres i q hqmem
  have hnq : Algebra.norm F q =
      Algebra.norm F G.Y * Algebra.norm F (x : L) / (a : F) ^ 2 := by
    dsimp [q]
    rw [div_eq_mul_inv, map_mul, map_mul, Algebra.norm_inv, Algebra.norm_algebraMap,
      (originLine_degrees F K (G.g i) (G.nontrivial i)).1,
      ((G.origin_orders hres).2.1 i).2]
    rw [div_eq_mul_inv]
  change ΨL (algebraMap F L (G.beta i) * q) = Ψ (G.beta i * Algebra.norm F q) at hp
  rw [hnq] at hp
  have hm : ord F (Algebra.norm F G.Y / (a : F) ^ 2) =
      ((2 * h - (G.t 0 : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_div, (G.origin_orders hres).2.2, ord_pow, ha,
      ← WithTop.coe_nsmul, ← WithTop.LinearOrderedAddCommGroup.coe_sub]
    congr 1
    simp
    ring
  have he : Ψ (Algebra.norm F G.Y / (a : F)) =
      Ψ (G.beta i * (Algebra.norm F G.Y * Algebra.norm F (x : L) / (a : F) ^ 2)) := by
    apply phase_eq_of_sub_mem Ψ (originAddChar_conductor F P ((G.t 1 : ℤ) + 1))
    have hd : (G.t 1 : ℤ) + 1 ≤
        (2 * h - (G.t 0 : ℤ)) + (-h + (G.t i : ℤ)) := by omega
    have hbound := lattice_antitone F hd (mul_mem_lattice F hm.ge (G.high_error a i x hx))
    have heq : Algebra.norm F G.Y / (a : F) -
        G.beta i * (Algebra.norm F G.Y * Algebra.norm F (x : L) / (a : F) ^ 2) =
        (Algebra.norm F G.Y / (a : F) ^ 2) *
          ((a : F) - G.beta i * Algebra.norm F (x : L)) := by
      field_simp
    rwa [heq]
  change ΨL _ = Ψ _
  rw [show Algebra.norm L G.Y *
      (algebraMap F L (G.beta i) * (x : L) / algebraMap F L (a : F)) =
      algebraMap F L (G.beta i) * q by dsimp [q]; ring, hp, ← he]

/-- Evaluate the actual continuous core character at the same denominator
as the proved stationary coefficient. The scalar `α` cancels in the ratio. -/
private theorem high_coreValue (hres : residueDegree F K = 1)
    {h : ℤ} (hh : G.highThreshold ≤ h) (a : Fˣ)
    (ha : ord F (a : F) = ((-h : ℤ) : WithTop ℤ)) (i : Fin 3)
    (χ : ContinuousQuasiChar (G.field i))
    (hcore : ∀ u, u ∈ unitFiltration (G.field i) (G.stationaryDepth i) →
      χ u = G.modelValue i u)
    (x : (G.field i)ˣ)
    (hx : IsSubcriticalNormRepresentative F (G.field i)
      (-h - ((G.t 1 : ℤ) - (G.t i : ℤ))) (G.t i) (a / G.betaUnit i) x)
    (Z : (G.field i)ˣ)
    (hZ : (Z : G.field i) = algebraMap F (G.field i) (a : F) +
      algebraMap F (G.field i) (G.beta i) * (x : G.field i)) (α : Fˣ) :
    χ ((Units.map (algebraMap F (G.field i)).toMonoidHom α * Z)⁻¹) =
      χ (Units.map (algebraMap F (G.field i)).toMonoidHom ((α * a)⁻¹)) *
        originAddChar F P ((G.t 1 : ℤ) + 1) (Algebra.norm F G.Y / (a : F)) := by
  let L := G.field i
  let Ψ := originAddChar F P ((G.t 1 : ℤ) + 1)
  let ΨL := tracePullbackAddChar F L Ψ
  let v : L := algebraMap F L (G.beta i) * (x : L) / algebraMap F L (a : F)
  let w : Lˣ := Z / Units.map (algebraMap F L).toMonoidHom a
  have haL : algebraMap F L (a : F) ≠ 0 := (map_ne_zero _).2 a.ne_zero
  have hw : (w : L) - 1 = v := by
    dsimp [w]
    rw [Units.val_div_eq_div_val, Units.coe_map, hZ]
    dsimp [v]
    field_simp
    ring
  have hv : v ∈ lattice L (G.stationaryDepth i : ℤ) := by
    change (G.stationaryDepth i : WithTop ℤ) ≤ ord L v
    rw [(G.high_orders hres hh a ha i x hx).2.1]
    apply WithTop.coe_le_coe.mpr
    have hs := (G.high_ledger hh i).2.2.2.2.1
    omega
  have hwmem : w ∈ unitFiltration L (G.stationaryDepth i) := by
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (depth_ledger G i).1.ne'
    rw [hs, mem_unitFiltration_succ_iff_sub_mem_lattice]
    rw [hw]
    simpa only [hs] using hv
  have hwvalue : χ w = ΨL (Algebra.norm L G.Y * v) := by
    rw [hcore w hwmem]
    change ΨL (Algebra.norm L G.Y * (1 - (w : L))) = _
    rw [show 1 - (w : L) = v by rw [← neg_sub, hw, CharTwo.neg_eq]]
  have hinv : (ΨL (Algebra.norm L G.Y * v))⁻¹ = ΨL (Algebra.norm L G.Y * v) := by
    apply mul_right_cancel (b := ΨL (Algebra.norm L G.Y * v))
    rw [inv_mul_cancel, ← ContinuousAddChar.map_add_eq_mul,
      CharTwo.add_self_eq_zero, ContinuousAddChar.map_zero_eq_one]
  have hden : (Units.map (algebraMap F L).toMonoidHom α * Z)⁻¹ =
      Units.map (algebraMap F L).toMonoidHom ((α * a)⁻¹) * w⁻¹ := by
    dsimp [w]
    simp [map_inv, map_mul, div_eq_mul_inv, mul_assoc, mul_comm]
  rw [hden, map_mul χ, map_inv χ w, hwvalue, hinv]
  rw [G.high_corePhase hres hh a ha i x hx]

omit [IsGalois F K] [CharP K 2] in
/-- Construct a full base stationary coefficient directly from FML's
stationary numerator class. Its order is exactly `-h`. -/
theorem highBaseCoefficient_exists {h : ℤ} (hh : G.highThreshold ≤ h)
    (lambda : ContinuousQuasiChar F)
    (hn : (multiplicativeConductorExponent F lambda : ℤ) = (G.t 1 : ℤ) + 1 + h) :
    ∃ a : Fˣ, ord F (a : F) = ((-h : ℤ) : WithTop ℤ) ∧
      ∀ u : Fˣ, 1 - (u : F) ∈ lattice F (((G.t 1 : ℤ) + 1 + h + 1) / 2) →
        lambda u = originAddChar F P ((G.t 1 : ℤ) + 1) ((a : F) * (1 - (u : F))) := by
  let n := multiplicativeConductorExponent F lambda
  let T : ℤ := (G.t 1 : ℤ) + 1
  let r := (n + 1) / 2
  let chi : LocalQuasiCharData F :=
    ⟨lambda, n, multiplicativeConductorExponent_isConductor F lambda⟩
  let psi : LocalAddCharData F :=
    ⟨originAddChar F P T, -T, originAddChar_conductor F P T⟩
  have hn2 : 1 < n := by
    have hr := (depth_ledger G 0).2.2.1
    dsimp only [highThreshold] at hh
    dsimp only [n]
    omega
  have hr : IsLamprechtStationaryDepth chi.conductor r := by
    constructor <;> dsimp [chi, r] <;> omega
  have hGamma : ord F ((1 : Fˣ) : F) = ((T + psi.conductor : ℤ) : WithTop ℤ) := by
    simp [psi]
  obtain ⟨c, hc⟩ := latticeQuotientMk_surjective F
    (sub_le_sub_left hr.int_le_conductor T)
    (stationaryNumeratorClass F chi psi T hr 1 hGamma)
  have hcOrder := stationaryNumeratorClass_representative_ord F chi psi T hr 1 hGamma c hc
  have horder : ord F (c : F) = ((-h : ℤ) : WithTop ℤ) := by
    rw [hcOrder]
    congr 1
    change (G.t 1 : ℤ) + 1 - (n : ℤ) = -h
    omega
  have hc0 : (c : F) ≠ 0 := by
    intro hz
    rw [hz, ord_zero] at horder
    exact WithTop.top_ne_coe horder
  refine ⟨Units.mk0 (c : F) hc0, horder, ?_⟩
  intro u hu
  have hdepth : (r : ℤ) = ((G.t 1 : ℤ) + 1 + h + 1) / 2 := by
    dsimp [r]
    omega
  let z : lattice F (r : ℤ) := ⟨1 - (u : F), hdepth ▸ hu⟩
  have hunit : (positiveUnitOfLattice F hr.pos z : Fˣ) = u := by
    apply Units.ext
    rw [coe_positiveUnitOfLattice]
    change 1 + (1 - (u : F)) = (u : F)
    rw [CharTwo.sub_eq_add, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have he := stationaryNumeratorClass_linearization F chi psi T hr 1 hGamma c hc z
  rw [hunit] at he
  simpa only [chi, psi, T, Units.val_one, div_one, z, Units.val_mk0] using he

end SimultaneousASGenerators

/-- The representatives and conclusions of Lemma 11.12 on the actual
three quadratic fixed fields. `epsilon` records precisely the relative
norm error, and `coefficient` is the nonzero sum `A + βᵢxᵢ`.

The constructor is `highCoefficient`. The required core charts are the
proved charts of `twist`, and a base coefficient is constructed by
`SimultaneousASGenerators.highBaseCoefficient_exists`. -/
structure HighCoefficientData {P : Residues.EqualCharacteristicPresentation F}
    (G : SimultaneousASGenerators F K P) (h : ℤ) (a : Fˣ)
    (lambda : ContinuousQuasiChar F)
    (χ : (i : Fin 3) → ContinuousQuasiChar (G.field i)) where
  x : (i : Fin 3) → (G.field i)ˣ
  x_order : ∀ i, ord (G.field i) (x i : G.field i) =
    ((-h - ((G.t 1 : ℤ) - (G.t i : ℤ)) : ℤ) : WithTop ℤ)
  epsilon : Fin 3 → Fˣ
  epsilon_mem : ∀ i, epsilon i ∈ unitFiltration F (G.t i)
  norm_eq : ∀ i, normUnits F (G.field i) (x i) = (a / G.betaUnit i) * epsilon i
  coefficient : (i : Fin 3) → (G.field i)ˣ
  coefficient_eq : ∀ i, (coefficient i : G.field i) =
    algebraMap F (G.field i) (a : F) +
      algebraMap F (G.field i) (G.beta i) * (x i : G.field i)
  coefficient_order : ∀ i, ord (G.field i) (coefficient i : G.field i) =
    ((-2 * h : ℤ) : WithTop ℤ)
  pullback_conductor : ∀ i,
    (multiplicativeConductorExponent (G.field i) (normQuasiChar F (G.field i) lambda) : ℤ) =
      2 * G.highDepth h i
  stationary : ∀ i (u : (G.field i)ˣ),
    1 - (u : G.field i) ∈ lattice (G.field i) (G.highDepth h i) →
      normQuasiChar F (G.field i) lambda u =
        tracePullbackAddChar F (G.field i) (originAddChar F P ((G.t 1 : ℤ) + 1))
          ((coefficient i : G.field i) * (1 - (u : G.field i)))
  core_value : ∀ i (α : Fˣ),
    χ i ((Units.map (algebraMap F (G.field i)).toMonoidHom α * coefficient i)⁻¹) =
      χ i (Units.map (algebraMap F (G.field i)).toMonoidHom ((α * a)⁻¹)) *
        originAddChar F P ((G.t 1 : ℤ) + 1) (Algebra.norm F G.Y / (a : F))
  denominator_order : ∀ i (α : Fˣ),
    ord F (α : F) = ((-((G.t 1 : ℤ) + 1) : ℤ) : WithTop ℤ) →
      ord (G.field i)
        (((Units.map (algebraMap F (G.field i)).toMonoidHom α * coefficient i)⁻¹ :
          (G.field i)ˣ) : G.field i) =
        ((2 * (multiplicativeConductorExponent F lambda : ℤ) : ℤ) : WithTop ℤ)

/-- **The high stationary coefficient and common core value**, paper
Lemma 11.12 (`D:EQ:highcoef`). For every actual base stationary coefficient
`a`, construct only the subcritical norm approximations, and prove the
whole stationary identity and the value of the actual core character.

Here `G` is constructed by `simultaneousASGenerators_exists`, and `hcore`
is the full chart supplied by `twist` for the actual compatible family.
No exact norm choice is required. The correction is literally the same
`Ψ_F(N_{K/F}(Y)/a)` for all three fields, including the first two in the
paper. Quasi-characters need not be unitary. -/
theorem highCoefficient (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (G : SimultaneousASGenerators F K P)
    (lambda : ContinuousQuasiChar F)
    (χ : (i : Fin 3) → ContinuousQuasiChar (G.field i))
    (hcore : ∀ i u, u ∈ unitFiltration (G.field i) (G.stationaryDepth i) →
      χ i u = G.modelValue i u)
    {h : ℤ} (hh : G.highThreshold ≤ h)
    (hn : (multiplicativeConductorExponent F lambda : ℤ) = (G.t 1 : ℤ) + 1 + h)
    (a : Fˣ) (ha : ord F (a : F) = ((-h : ℤ) : WithTop ℤ))
    (hbase : ∀ u : Fˣ,
      1 - (u : F) ∈ lattice F (((G.t 1 : ℤ) + 1 + h + 1) / 2) →
        lambda u = originAddChar F P ((G.t 1 : ℤ) + 1) ((a : F) * (1 - (u : F)))) :
    Nonempty (HighCoefficientData G h a lambda χ) := by
  classical
  choose x hx using G.highApproximation_exists hres a ha
  let epsilon (i : Fin 3) : Fˣ := normUnits F (G.field i) (x i) / (a / G.betaUnit i)
  have horder (i : Fin 3) := (G.high_orders hres hh a ha i (x i) (hx i)).1
  let Z (i : Fin 3) : (G.field i)ˣ := Units.mk0
    (algebraMap F (G.field i) (a : F) +
      algebraMap F (G.field i) (G.beta i) * (x i : G.field i)) (by
        intro hz
        have he := horder i
        rw [hz, ord_zero] at he
        exact WithTop.top_ne_coe he)
  refine ⟨{
    x := x
    x_order := fun i ↦ (hx i).source_order
    epsilon := epsilon
    epsilon_mem := ?_
    norm_eq := ?_
    coefficient := Z
    coefficient_eq := fun _ ↦ rfl
    coefficient_order := horder
    pullback_conductor := ?_
    stationary := fun i u hu ↦ G.high_stationary hres hh a lambda hbase i (x i) (hx i) u hu
    core_value := fun i α ↦ G.high_coreValue hres hh a ha i (χ i) (hcore i)
      (x i) (hx i) (Z i) rfl α
    denominator_order := ?_
  }⟩
  · intro i
    exact div_mem_unitFiltration_of_exactOrder_congruentAtDepth
      (normUnits F (G.field i) (x i)) (a / G.betaUnit i)
      (hx i).norm_order (hx i).coefficient_order (hx i).congruentAtDepth.symm
  · intro i
    dsimp [epsilon]
    simp
  · intro i
    have hd := G.high_ledger hh i
    have hhigh : G.t i + 1 < multiplicativeConductorExponent F lambda := by
      have ht : 0 < (G.t 1 : ℤ) := by exact_mod_cast (G.edge 1).2.2.2.1
      have hr := (depth_ledger G 0).2.2.1
      dsimp only [SimultaneousASGenerators.highThreshold] at hh
      omega
    have he := (pullback_conductors G hres lambda i).2 hhigh
    rw [he]
    dsimp [SimultaneousASGenerators.highDepth]
    omega
  · intro i α hα
    simp only [Units.val_inv_eq_inv_val, Units.val_mul, Units.coe_map,
      ord_inv, ord_mul]
    change -(ord (G.field i) (algebraMap F (G.field i) (α : F)) +
      ord (G.field i) (Z i : G.field i)) = _
    have hZi : ord (G.field i) (Z i : G.field i) = ((-2 * h : ℤ) : WithTop ℤ) := horder i
    rw [ord_algebraMap, (edge_ramification G hres i).1, hα, hZi,
      ← WithTop.coe_nsmul, ← WithTop.coe_add, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
    congr 1
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    omega

/-- Both the base stationary coefficient and its high pullback data can
be constructed from the actual base twist and the proved core charts. -/
theorem highCoefficient_exists (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (G : SimultaneousASGenerators F K P)
    (lambda : ContinuousQuasiChar F)
    (χ : (i : Fin 3) → ContinuousQuasiChar (G.field i))
    (hcore : ∀ i u, u ∈ unitFiltration (G.field i) (G.stationaryDepth i) →
      χ i u = G.modelValue i u)
    {h : ℤ} (hh : G.highThreshold ≤ h)
    (hn : (multiplicativeConductorExponent F lambda : ℤ) = (G.t 1 : ℤ) + 1 + h) :
    ∃ a : Fˣ, ord F (a : F) = ((-h : ℤ) : WithTop ℤ) ∧
      (∀ u : Fˣ, 1 - (u : F) ∈ lattice F (((G.t 1 : ℤ) + 1 + h + 1) / 2) →
        lambda u = originAddChar F P ((G.t 1 : ℤ) + 1) ((a : F) * (1 - (u : F)))) ∧
      Nonempty (HighCoefficientData G h a lambda χ) := by
  obtain ⟨a, ha, hbase⟩ := G.highBaseCoefficient_exists hh lambda hn
  exact ⟨a, ha, hbase, highCoefficient hres P G lambda χ hcore hh hn a ha hbase⟩

end

end LanglandsSecondMainLemma.Dyadic.Equal
