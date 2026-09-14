import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Dyadic.Maximal.Normalization
import LanglandsSecondMainLemma.Dyadic.Maximal.CommonError

/-!
# Minimal origins in the maximal dyadic branch

Paper `D:MX:minimal-origin`, with the setup `D:MX:minimal-range`.
The base coefficient is obtained from FML's stationary numerator class.
All error estimates below use integer lattice exponents.
-/

namespace LanglandsSecondMainLemma.Dyadic.Maximal

open LanglandsFirstMainLemma

noncomputable section

section OneField

variable (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

private theorem minimal_displacement {d : ℕ} (hd : 0 < d)
    (u : unitFiltration E d) :
    1 - ((u : Eˣ) : E) ∈ lattice E (d : ℤ) := by
  cases d with
  | zero => omega
  | succ d =>
    simpa only [neg_sub] using neg_mem_lattice E
      ((mem_unitFiltration_succ_iff_sub_mem_lattice E d _).1 u.property)

private theorem minimal_oneSub_mem {d : ℕ} (hd : 0 < d)
    (z : E) (hz : z ∈ lattice E (d : ℤ)) :
    lowerOneSubUnit E d hd z hz ∈ unitFiltration E d := by
  cases d with
  | zero => omega
  | succ d =>
    apply (mem_unitFiltration_succ_iff_sub_mem_lattice E d _).2
    simpa using neg_mem_lattice E hz

/-- The minus-sign chart, extracted from the actual FML quotient class. -/
private theorem minimal_base_coefficient
    (lambda : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    {r : ℕ} (hr : IsLamprechtStationaryDepth lambda.conductor r) :
    ∃ A : Eˣ,
      ord E (A : E) = ((-Psi.conductor - (lambda.conductor : ℤ) : ℤ) : WithTop ℤ) ∧
      ∀ u : unitFiltration E r,
        lambda.character (u : Eˣ) = corePhaseValue E Psi.character (A : E) (u : Eˣ) := by
  let M := -Psi.conductor
  have hGamma : ord E ((1 : Eˣ) : E) = ((M + Psi.conductor : ℤ) : WithTop ℤ) := by
    simp [M]
  obtain ⟨c, hc⟩ := latticeQuotientMk_surjective E
    (sub_le_sub_left hr.int_le_conductor M)
    (stationaryNumeratorClass E lambda Psi M hr 1 hGamma)
  have hcorder := stationaryNumeratorClass_representative_ord
    E lambda Psi M hr 1 hGamma c hc
  have hc0 : -(c : E) ≠ 0 := neg_ne_zero.mpr
    ((ord_ne_top_iff E).1 (by rw [hcorder]; exact WithTop.coe_ne_top))
  refine ⟨Units.mk0 (-(c : E)) hc0, ?_, ?_⟩
  · simpa only [Units.val_mk0, ord_neg, M] using hcorder
  · intro u
    let x : lattice E (r : ℤ) :=
      ⟨((u : Eˣ) : E) - 1, by
        simpa only [neg_sub] using neg_mem_lattice E (minimal_displacement E hr.pos u)⟩
    have hu : positiveUnitOfLattice E hr.pos x = (u : Eˣ) := by
      apply Units.ext
      simp [x, positiveUnitOfLattice]
    have h := stationaryNumeratorClass_linearization
      E lambda Psi M hr 1 hGamma c hc x
    rw [hu] at h
    convert h using 1
    dsimp [corePhaseValue, x]
    congr 1
    ring

private theorem minimal_map_sub (E : Type) [Field E] [TopologicalSpace E]
    [IsTopologicalRing E] (Psi : ContinuousAddChar E) (x y : E) :
    Psi (x - y) = Psi x / Psi y := Psi.toAddChar.map_sub_eq_div x y

private theorem minimal_scaled_conductor (psi : LocalAddCharData E) (alpha : Eˣ)
    {J : ℤ} (halpha : ord E (alpha : E) = ((-psi.conductor - J : ℤ) : WithTop ℤ)) :
    (scaleAddCharData E psi alpha).conductor = -J := by
  have hu : unitOrder E alpha = -psi.conductor - J :=
    WithTop.coe_injective ((ord_coe_eq_unitOrder E alpha).symm.trans halpha)
  rw [scaleAddCharData_conductor, hu]
  ring

private theorem minimal_sub_order {x y : E} (h : ord E x < ord E y) :
    ord E (x - y) = ord E x := by
  rw [sub_eq_add_neg, ord_add_eq_min E (by simpa only [ord_neg] using ne_of_lt h),
    ord_neg, min_eq_left h.le]

end OneField

section Edge

variable (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]

omit [Module.Finite F E] in
private theorem minimal_algebraMap_mem (hram : ramificationIndex F E = 2)
    {j : ℤ} {x : F} (hx : x ∈ lattice F j) :
    algebraMap F E x ∈ lattice E (2 * j) := by
  rw [mem_lattice, ord_algebraMap, hram]
  have h := (mem_lattice F).1 hx
  simpa only [two_nsmul, ← WithTop.coe_add, ← two_mul] using add_le_add h h

private theorem minimal_trace_mem [PrimeCyclicExtension F E]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hdeg : Module.finrank F E = 2)
    {j r : ℤ} (hdepth : r ≤ (j + (t + 1 : ℕ)) / 2)
    {x : E} (hx : x ∈ lattice E j) : trace F E x ∈ lattice F r := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have hmap : trace F E x ∈
      Submodule.map ((trace F E).restrictScalars (ringOfIntegers F))
        ((lattice E j).restrictScalars (ringOfIntegers F)) :=
    Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  rw [cyclicPrime_trace_lattice_image_eq F E ht hres pi hpi hgen, hdeg] at hmap
  apply lattice_antitone F hdepth
  simpa only [Nat.reduceSub, one_mul, Nat.cast_ofNat] using hmap

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeExtension F E] in
private theorem minimal_norm_oneSub (hdeg : Module.finrank F E = 2) (z : E) :
    norm F E (1 - z) = 1 - trace F E z + norm F E z := by
  have h := norm_one_add_eq_one_add_sum_elementarySymmetric F E (-z)
  rw [hdeg] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd] at h
  rw [elementarySymmetric_one] at h
  have hn : elementarySymmetric F E 2 (-z) = norm F E (-z) := by
    rw [← hdeg]
    exact elementarySymmetric_finrank F E (-z)
  have hneg : norm F E (-z) = norm F E z := by
    rw [show -z = algebraMap F E (-1 : F) * z by simp, map_mul,
      LanglandsFirstMainLemma.norm_algebraMap, hdeg]
    norm_num
  simpa only [hn, map_neg, hneg, sub_eq_add_neg, add_assoc] using h

/-- Whole-ideal cancellation of the weighted error in `D:MX:Qphase`. -/
private theorem minimal_crossed_phase
    (hdeg : Module.finrank F E = 2) (hres : residueDegree F E = 1)
    (hram : ramificationIndex F E = 2)
    (Psi : ContinuousAddChar F) {J k l v : ℤ} {q s : ℕ}
    (htrivial : AddCharTrivialOnLattice F Psi J)
    (hdepth : 2 * k + q ≤ l + s) (herrdepth : J + k ≤ v + s)
    (beta A err : F) (hbeta : ord F beta = (k : WithTop ℤ))
    (Q : E) (hQ : Q ∈ lattice E l) (herr : err ∈ lattice F v)
    (hnorm : norm F E Q = beta * A + err)
    (hphase : ∀ x : E, x ∈ lattice E (q : ℤ) →
      tracePullbackAddChar F E Psi (algebraMap F E beta * x) =
        Psi (beta * norm F E x))
    (z : E) (hz : z ∈ lattice E (s : ℤ)) :
    tracePullbackAddChar F E Psi (Q * z) = Psi (A * norm F E z) := by
  have hb0 : beta ≠ 0 := (ord_ne_top_iff F).1
    (by rw [hbeta]; exact WithTop.coe_ne_top)
  have hbE0 : algebraMap F E beta ≠ 0 := (map_ne_zero (algebraMap F E)).2 hb0
  have hbE : ord E (algebraMap F E beta) = ((2 * k : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hram, hbeta, ← WithTop.coe_nsmul]
    simp [two_mul]
  have hx : Q * z / algebraMap F E beta ∈ lattice E (q : ℤ) := by
    apply (div_mem_lattice_iff E _ _ _ _ hbE).2
    exact lattice_antitone E hdepth (mul_mem_lattice E hQ hz)
  have hp := hphase _ hx
  have harg : algebraMap F E beta * (Q * z / algebraMap F E beta) = Q * z := by
    field_simp
  have hdiv : norm F E (Q * z / algebraMap F E beta) =
      norm F E Q * norm F E z / beta ^ 2 := by
    simp only [div_eq_mul_inv, map_mul, Algebra.norm_inv,
      LanglandsFirstMainLemma.norm_algebraMap, hdeg]
  rw [harg, hdiv, hnorm] at hp
  have harg' : beta * ((beta * A + err) * norm F E z / beta ^ 2) =
      A * norm F E z + err * norm F E z / beta := by
    field_simp
  rw [harg', ContinuousAddChar.map_add_eq_mul] at hp
  have hnz : norm F E z ∈ lattice F (s : ℤ) := by
    simpa only [mem_lattice, ord_norm, hres, one_nsmul] using hz
  have hekill : Psi (err * norm F E z / beta) = 1 := by
    apply htrivial
    apply (div_mem_lattice_iff F _ _ _ _ hbeta).2
    exact lattice_antitone F (by omega) (mul_mem_lattice F herr hnz)
  simpa only [hekill, mul_one] using hp

/-- Evaluate the actual norm pullback on its complete stationary group. -/
private theorem minimal_twist_phase [PrimeCyclicExtension F E]
    {t r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hdeg : Module.finrank F E = 2)
    (htrace : (r : ℤ) ≤ ((s : ℤ) + (t + 1 : ℕ)) / 2) (hnorm : r ≤ s)
    (Psi : ContinuousAddChar F) (lambda : ContinuousQuasiChar F) (A : F) (Q : E)
    (hbase : ∀ u : unitFiltration F r,
      lambda (u : Fˣ) = corePhaseValue F Psi A (u : Fˣ))
    (hQ : ∀ z : E, z ∈ lattice E (s : ℤ) →
      tracePullbackAddChar F E Psi (Q * z) = Psi (A * norm F E z))
    (u : unitFiltration E s) :
    normQuasiChar F E lambda (u : Eˣ) =
      corePhaseValue E (tracePullbackAddChar F E Psi)
        (algebraMap F E A - Q) (u : Eˣ) := by
  let z : E := 1 - ((u : Eˣ) : E)
  have hz : z ∈ lattice E (s : ℤ) := minimal_displacement E hs u
  have htz := minimal_trace_mem F E ht hres hdeg htrace hz
  have hnz : norm F E z ∈ lattice F (r : ℤ) := by
    apply lattice_antitone F (show (r : ℤ) ≤ (s : ℤ) by exact_mod_cast hnorm)
    simpa only [mem_lattice, ord_norm, hres, one_nsmul] using hz
  let y := trace F E z - norm F E z
  have hy : y ∈ lattice F (r : ℤ) := sub_mem_lattice F htz hnz
  have hu : normUnits F E (u : Eˣ) = lowerOneSubUnit F r hr y hy := by
    apply Units.ext
    rw [coe_normUnits, coe_lowerOneSubUnit]
    have hz' : ((u : Eˣ) : E) = 1 - z := by dsimp [z]; ring
    rw [hz', minimal_norm_oneSub F E hdeg]
    dsimp [y]
    ring
  have h := hbase ⟨_, minimal_oneSub_mem F hr y hy⟩
  change lambda (normUnits F E (u : Eˣ)) = _
  rw [hu, h]
  simp only [corePhaseValue, coe_lowerOneSubUnit, sub_sub_cancel]
  change Psi (A * y) = tracePullbackAddChar F E Psi ((algebraMap F E A - Q) * z)
  rw [sub_mul, minimal_map_sub, hQ z hz]
  rw [tracePullbackAddChar_apply, show trace F E (algebraMap F E A * z) =
    A * trace F E z by simpa [Algebra.smul_def] using (trace F E).map_smul A z]
  rw [← minimal_map_sub]
  congr 1
  dsimp [y]
  ring

private theorem minimal_ramification_two (hdeg : Module.finrank F E = 2)
    (hres : residueDegree F E = 1) : ramificationIndex F E = 2 := by
  have h := finrank_eq_ramificationIndex_mul_residueDegree F E
  rw [hdeg, hres, mul_one] at h
  exact h.symm

end Edge

section Diagram

variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]

local instance minimal_valuation (L : IntermediateField F K) : ValuativeRel L :=
  Basic.intermediateFieldValuativeRel L
local instance minimal_topology (L : IntermediateField F K) : TopologicalSpace L :=
  Basic.intermediateFieldTopology L
local instance minimal_localField (L : IntermediateField F K) : IsNonarchimedeanLocalField L :=
  Basic.intermediateField_localField L
local instance minimal_lowerValuation (L : IntermediateField F K) : ValuativeExtension F L :=
  Basic.intermediateField_lowerValuativeExtension L
local instance minimal_upperValuation (L : IntermediateField F K) : ValuativeExtension L K :=
  Basic.intermediateField_upperValuativeExtension L

omit [Module.Free F K] in
private theorem minimal_residueDegrees (L : IntermediateField F K)
    (hres : residueDegree F K = 1) :
    residueDegree F L = 1 ∧ residueDegree L K = 1 := by
  obtain ⟨x, hx⟩ := exists_ord_eq K 1
  have h := congrArg (ord F) (Basic.norm_tower (F := F) (L := L) x)
  rw [ord_norm, ord_norm, ord_norm, hres, hx] at h
  have hz : residueDegree F L • residueDegree L K • (1 : ℤ) = 1 • (1 : ℤ) := by
    exact_mod_cast h
  have hz' : (residueDegree F L : ℤ) * (residueDegree L K : ℤ) = 1 := by
    simpa [nsmul_eq_mul] using hz
  have hm : residueDegree F L * residueDegree L K = 1 := by exact_mod_cast hz'
  exact mul_eq_one.mp hm

variable {pi : ringOfIntegers F} {e a b : ℕ}
  {u0 w0 : (ringOfIntegers F)ˣ} {s R0 : K}

/-- The full formulas at a common origin, with the actual upper norms,
actual lower trace norms, and the unchanged nonzero trace valuations.
The unit formulation of each upper formula evaluates `theta(1-z)` for
all `z` in the indicated stationary ideal. -/
structure MinimalOriginData (D : AlignmentData pi e a b u0 w0 s R0)
    (tau₁ : NormCharacter F D.firstField) (tau₂ : NormCharacter F D.secondField)
    (Psi : ContinuousAddChar F)
    (theta₁ : ContinuousQuasiChar D.firstField)
    (theta₂ : ContinuousQuasiChar D.secondField) (C : K) : Prop where
  origin_order : ord K C = ((1 - 2 * (a : ℤ) : ℤ) : WithTop ℤ)
  origin_ne_zero : C ≠ 0
  first_trace_order : ord D.firstField (trace D.firstField K C) = (b : WithTop ℤ)
  second_trace_order : ord D.secondField (trace D.secondField K C) = 0
  first_trace_ne_zero : trace D.firstField K C ≠ 0
  second_trace_ne_zero : trace D.secondField K C ≠ 0
  first_formula : ∀ u : unitFiltration D.firstField (2 * e + 1),
    theta₁ (u : D.firstFieldˣ) = corePhaseValue D.firstField
      (tracePullbackAddChar F D.firstField Psi) (norm D.firstField K C) (u : D.firstFieldˣ)
  second_formula : ∀ u : unitFiltration D.secondField (e + a),
    theta₂ (u : D.secondFieldˣ) = corePhaseValue D.secondField
      (tracePullbackAddChar F D.secondField Psi) (norm D.secondField K C) (u : D.secondFieldˣ)
  first_lower : ∀ (ha : 0 < a) (z : F) (hz : z ∈ lattice F (a : ℤ)),
    tau₁.1 (lowerOneSubUnit F a ha z hz) =
      Psi (norm F D.firstField (trace D.firstField K C) * z)
  second_lower : ∀ (z : F) (hz : z ∈ lattice F ((e + 1 : ℕ) : ℤ)),
    tau₂.1 (lowerOneSubUnit F (e + 1) (by omega) z hz) =
      Psi (norm F D.secondField (trace D.secondField K C) * z)

variable (hG : Nonempty
  (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
  (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)

include hG O in
private theorem minimal_lowerCyclic1 : CyclicPrimeExtension F D.firstField :=
  (Basic.intermediateField_tower_compatible Nat.prime_two hG
    D.firstField O.first_degree).2.2.2.2.2.2.2.2.2.2.2.1
private abbrev minimal_lowerPrime1 : PrimeCyclicExtension F D.firstField :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F D.firstField
    (minimal_lowerCyclic1 hG D O)

include hG O in
private theorem minimal_lowerCyclic2 : CyclicPrimeExtension F D.secondField :=
  (Basic.intermediateField_tower_compatible Nat.prime_two hG
    D.secondField O.second_degree).2.2.2.2.2.2.2.2.2.2.2.1
private abbrev minimal_lowerPrime2 : PrimeCyclicExtension F D.secondField :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F D.secondField
    (minimal_lowerCyclic2 hG D O)

include hG O in
private theorem minimal_lowerCyclic3 : CyclicPrimeExtension F D.thirdField :=
  (Basic.intermediateField_tower_compatible Nat.prime_two hG
    D.thirdField O.third_degree).2.2.2.2.2.2.2.2.2.2.2.1
private abbrev minimal_lowerPrime3 : PrimeCyclicExtension F D.thirdField :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F D.thirdField
    (minimal_lowerCyclic3 hG D O)

omit [Module.Free F K] in
private theorem minimal_zero_error
    (g1 : Gal(K/D.firstField)) (g2 : Gal(K/D.secondField))
    (q3 : Gal(D.thirdField/F)) : CommonErrorData D g1 g2 q3 0 0 := by
  constructor <;>
    simp [AlignmentData.adjustedOrigin, AlignmentData.adjustmentNorm,
      AlignmentData.adjustmentTrace, AlignmentData.firstCrossedTrace,
      AlignmentData.secondCrossedTrace, AlignmentData.commonErrorTerm,
      AlignmentData.traceNormIncrement, AlignmentData.a1, AlignmentData.a2,
      AlignmentData.h1, AlignmentData.h2, AlignmentData.beta1,
      AlignmentData.beta2, intermediateOrder]

set_option maxHeartbeats 1200000 in
private theorem minimal_adjusted_data
    (hres : residueDegree F K = 1)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (ha : 1 ≤ a) (hae : a ≤ e) (hb : b = 2 * e - 2 * a + 1)
    (ht₁ : actualLowerBreak hG D.firstField O.first_degree (2 * a - 1))
    (ht₂ : actualLowerBreak hG D.secondField O.second_degree (2 * e))
    (tau₁ : NormCharacter F D.firstField) (tau₂ : NormCharacter F D.secondField)
    (tau₃ : NormCharacter F D.thirdField)
    (Psi : ContinuousAddChar F)
    (H : LowerCharacterData F D.firstField D.secondField D.thirdField
      a e ha tau₁ tau₂ tau₃ Psi D.beta1 D.beta2 D.beta3 D.h1 D.h2 D.h3)
    (chi₁ : ContinuousQuasiChar D.firstField) (chi₂ : ContinuousQuasiChar D.secondField)
    (hchi₁ : ∀ u : unitFiltration D.firstField (2 * e + 1),
      chi₁ (u : D.firstFieldˣ) = corePhaseValue D.firstField
        (tracePullbackAddChar F D.firstField Psi) D.a1 (u : D.firstFieldˣ))
    (hchi₂ : ∀ u : unitFiltration D.secondField (e + a),
      chi₂ (u : D.secondFieldˣ) = corePhaseValue D.secondField
        (tracePullbackAddChar F D.secondField Psi) D.a2 (u : D.secondFieldˣ))
    (lambda : ContinuousQuasiChar F)
    (htrivial : AddCharTrivialOnLattice F Psi (2 * (e : ℤ) + 1))
    (g1 : Gal(K/D.firstField)) (g2 : Gal(K/D.secondField))
    (q3 : Gal(D.thirdField/F)) (X : D.thirdField) (h : ℤ)
    (hh : h ≤ (a : ℤ) - 1) (hX : X ∈ lattice D.thirdField (-h))
    (E : CommonErrorData D g1 g2 q3 X h)
    (hbase : ∀ u : unitFiltration F (e + a),
      lambda (u : Fˣ) = corePhaseValue F Psi (D.adjustmentNorm X) (u : Fˣ)) :
    MinimalOriginData D tau₁ tau₂ Psi
      (chi₁ * normQuasiChar F D.firstField lambda)
      (chi₂ * normQuasiChar F D.secondField lambda) (D.adjustedOrigin X) := by
  letI : PrimeCyclicExtension F D.firstField := minimal_lowerPrime1 hG D O
  letI : PrimeCyclicExtension F D.secondField := minimal_lowerPrime2 hG D O
  have ht₁' : PrimeCyclicExtension.IsLowerBreak F D.firstField (2 * a - 1) := by
    simpa [actualLowerBreak] using ht₁
  have ht₂' : PrimeCyclicExtension.IsLowerBreak F D.secondField (2 * e) := by
    simpa [actualLowerBreak] using ht₂
  have hb' : (b : ℤ) = 2 * (e : ℤ) - 2 * (a : ℤ) + 1 := by omega
  have hres₁ := (minimal_residueDegrees D.firstField hres).1
  have hres₂ := (minimal_residueDegrees D.secondField hres).1
  have hres₃K := (minimal_residueDegrees D.thirdField hres).2
  have hram₁ := minimal_ramification_two F D.firstField O.first_degree hres₁
  have hram₂ := minimal_ramification_two F D.secondField O.second_degree hres₂
  have hdeg₃K : Module.finrank D.thirdField K = 2 :=
    (Basic.intermediateField_tower_compatible Nat.prime_two hG
      D.thirdField O.third_degree).2.2.2.2.2.2.2.2.2.2.1
  have hram₃K := minimal_ramification_two D.thirdField K hdeg₃K hres₃K
  have hXK := minimal_algebraMap_mem D.thirdField K hram₃K hX
  have hC : ord K (D.adjustedOrigin X) = ((1 - 2 * (a : ℤ) : ℤ) : WithTop ℤ) := by
    rw [AlignmentData.adjustedOrigin, minimal_sub_order, O.origin_order]
    rw [O.origin_order]
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) ((mem_lattice K).1 hXK)
  have hp : D.adjustmentTrace X ∈ lattice F ((e : ℤ) - h / 2) :=
    (mem_lattice F).2 E.trace_bound
  have hp₁ := minimal_algebraMap_mem F D.firstField hram₁ hp
  have hp₂ := minimal_algebraMap_mem F D.secondField hram₂ hp
  have hs₁ : ord D.firstField (trace D.firstField K (D.adjustedOrigin X)) =
      (b : WithTop ℤ) := by
    rw [E.first_trace, minimal_sub_order]
    · exact O.h1_order
    · change intermediateOrder D.firstField D.h1 < _
      rw [O.h1_order]
      exact lt_of_lt_of_le (by exact_mod_cast (show (b : ℤ) < 2 * ((e : ℤ) - h / 2) by omega))
        ((mem_lattice D.firstField).1 hp₁)
  have hs₂ : ord D.secondField (trace D.secondField K (D.adjustedOrigin X)) = 0 := by
    rw [E.second_trace, minimal_sub_order]
    · exact O.h2_order
    · change intermediateOrder D.secondField D.h2 < _
      rw [O.h2_order]
      exact lt_of_lt_of_le (by exact_mod_cast (show (0 : ℤ) < 2 * ((e : ℤ) - h / 2) by omega))
        ((mem_lattice D.secondField).1 hp₂)
  have hDelta : D.traceNormIncrement X ∈ lattice F (2 * (e : ℤ) + 1 - a) := by
    apply add_mem_lattice F
    · apply lattice_antitone F (show 2 * (e : ℤ) + 1 - a ≤
          ((e : ℤ) - h / 2) + ((e : ℤ) - h / 2) by omega)
      simpa only [AlignmentData.traceNormIncrement, pow_two] using mul_mem_lattice F hp hp
    · apply lattice_antitone F (show 2 * (e : ℤ) + 1 - a ≤
          (e : ℤ) + ((e : ℤ) - h / 2) by omega)
      exact mul_mem_lattice F ((mem_lattice F).2 (by rw [htwo]; norm_cast)) hp
  have herr : D.commonErrorTerm g1 X ∈ lattice F (2 * (e : ℤ) + 1 - a - h) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      (mem_lattice F).2 E.error_bound
  have hQ₁ : D.firstCrossedTrace g1 X ∈ lattice D.firstField ((b : ℤ) - h) :=
    (mem_lattice D.firstField).2 E.first_crossed_bound
  have hQ₂ : D.secondCrossedTrace g2 X ∈ lattice D.secondField (-h) :=
    (mem_lattice D.secondField).2 E.second_crossed_bound
  have hpQ₁ := minimal_crossed_phase F D.firstField O.first_degree hres₁ hram₁
    Psi htrivial (k := (b : ℤ)) (q := a) (s := 2 * e + 1) (by omega) (by omega)
    D.beta1 (D.adjustmentNorm X) (D.commonErrorTerm g1 X)
    (by exact O.beta1_order) _ hQ₁ herr E.first_weighted_norm H.first_phase
  have hpQ₂ := minimal_crossed_phase F D.secondField O.second_degree hres₂ hram₂
    Psi htrivial (k := 0) (q := e + 1) (s := e + a) (by omega) (by omega)
    D.beta2 (D.adjustmentNorm X) (D.commonErrorTerm g1 X)
    O.beta2_order _ hQ₂ herr E.second_weighted_norm H.second_phase
  refine ⟨hC, (ord_ne_top_iff K).1 (by rw [hC]; exact WithTop.coe_ne_top), hs₁, hs₂,
    (ord_ne_top_iff D.firstField).1 (by rw [hs₁]; exact WithTop.coe_ne_top),
    (ord_ne_top_iff D.secondField).1 (by rw [hs₂]; simp), ?_, ?_, ?_, ?_⟩
  · intro u
    have ht := minimal_twist_phase F D.firstField (by omega) (by omega)
      ht₁' hres₁ O.first_degree (r := e + a) (s := 2 * e + 1)
      (by omega) (by omega) Psi lambda _ _ hbase hpQ₁ u
    change chi₁ (u : D.firstFieldˣ) * normQuasiChar F D.firstField lambda (u : D.firstFieldˣ) = _
    rw [hchi₁ u, ht, E.first_norm]
    simp only [corePhaseValue, ← ContinuousAddChar.map_add_eq_mul]
    congr 1
    ring
  · intro u
    have ht := minimal_twist_phase F D.secondField (by omega) (by omega)
      ht₂' hres₂ O.second_degree (r := e + a) (s := e + a)
      (by omega) (by omega) Psi lambda _ _ hbase hpQ₂ u
    change chi₂ (u : D.secondFieldˣ) * normQuasiChar F D.secondField lambda (u : D.secondFieldˣ) = _
    rw [hchi₂ u, ht, E.second_norm]
    simp only [corePhaseValue, ← ContinuousAddChar.map_add_eq_mul]
    congr 1
    ring
  · intro ha' z hz
    rw [H.first_formula z hz, E.first_trace_norm, add_mul, ContinuousAddChar.map_add_eq_mul]
    have hkill : Psi (D.traceNormIncrement X * z) = 1 := by
      apply htrivial
      convert mul_mem_lattice F hDelta hz using 1
      congr 1
      omega
    rw [hkill, mul_one]
  · intro z hz
    rw [H.second_formula z hz, E.second_trace_norm, add_mul, ContinuousAddChar.map_add_eq_mul]
    have hkill : Psi (D.traceNormIncrement X * z) = 1 := by
      apply htrivial
      apply lattice_antitone F (show 2 * (e : ℤ) + 1 ≤
        (2 * (e : ℤ) + 1 - a) + ((e + 1 : ℕ) : ℤ) by omega)
      exact mul_mem_lattice F hDelta hz
    rw [hkill, mul_one]

set_option maxHeartbeats 1600000 in
/-- **Full stationary formulas for the given minimal characters**
(`D:MX:minimal-origin`, paper Lemma 12.10).

The characters are in the common-twist form `D:MX:twisted`, supplied by
`twist`; the fixed lower and core charts are those preserved by
`normalization`. For every base twist of conductor at most `2e+a`, this
constructs the permitted normalization and the actual element `C=Y-X`.
The result includes the whole upper and lower stationary formulas and
both nonzero traces with their original valuations.

The small-conductor case chooses `X=0`. Otherwise the coefficient and
its exact third-field norm representative are constructed here using
FML additive duality and `normalization`. The weighted errors are proved
by `commonError`; no stationary formula for the given `theta_i`, exact
norm representative, or error bound is assumed. -/
theorem minimalOrigin
    (hres : residueDegree F K = 1)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (ha : 1 ≤ a) (hae : a ≤ e) (hb : b = 2 * e - 2 * a + 1)
    (ht₁ : actualLowerBreak hG D.firstField O.first_degree (2 * a - 1))
    (ht₂ : actualLowerBreak hG D.secondField O.second_degree (2 * e))
    (ht₃ : actualLowerBreak hG D.thirdField O.third_degree (2 * e))
    (hU₁ : actualUpperBreak hG D.firstField O.first_degree (4 * e - 2 * a + 1))
    (hU₂ : actualUpperBreak hG D.secondField O.second_degree (2 * a - 1))
    (g1 : Gal(K/D.firstField)) (hg1 : g1 ≠ 1) (hg1R : g1 D.R = -D.R)
    (g2 : Gal(K/D.secondField)) (hg2 : g2 ≠ 1) (hg2S : g2 D.S = -D.S)
    (q1 : Gal(D.firstField/F)) (hq1 : q1 ≠ 1)
    (hq1S : q1 D.firstGenerator = -D.firstGenerator)
    (q2 : Gal(D.secondField/F)) (hq2 : q2 ≠ 1)
    (hq2R : q2 D.secondGenerator = -D.secondGenerator)
    (q3 : Gal(D.thirdField/F)) (hq3 : q3 ≠ 1)
    (hq3SR : q3 D.thirdGenerator = -D.thirdGenerator)
    (tau₁ : NormCharacter F D.firstField) (htau₁ : tau₁ ≠ 1)
    (tau₂ : NormCharacter F D.secondField) (htau₂ : tau₂ ≠ 1)
    (tau₃ : NormCharacter F D.thirdField) (htau₃ : tau₃ ≠ 1)
    (psi : LocalAddCharData F) (alpha : Fˣ)
    (halpha : ord F (alpha : F) =
      ((-psi.conductor - (2 * (e : ℤ) + 1) : ℤ) : WithTop ℤ))
    (chi₁ : ContinuousQuasiChar D.firstField) (chi₂ : ContinuousQuasiChar D.secondField)
    (chi₃ : ContinuousQuasiChar D.thirdField)
    (H : NormalizationFormulas F D.firstField D.secondField D.thirdField
      a e ha tau₁ tau₂ tau₃ psi D.beta1 D.beta2 D.beta3 D.h1 D.h2 D.h3
      D.a1 D.a2 D.a3 chi₁ chi₂ chi₃ alpha)
    (lambda : LocalQuasiCharData F) (hn : lambda.conductor ≤ 2 * e + a)
    (theta₁ : ContinuousQuasiChar D.firstField) (theta₂ : ContinuousQuasiChar D.secondField)
    (htheta₁ : theta₁ = chi₁ * normQuasiChar F D.firstField lambda.character)
    (htheta₂ : theta₂ = chi₂ * normQuasiChar F D.secondField lambda.character) :
    ∃ (u : unitFiltration F (2 * e)) (X : D.thirdField),
      ord F ((alpha * (u : Fˣ) : Fˣ) : F) = ord F (alpha : F) ∧
      NormalizationFormulas F D.firstField D.secondField D.thirdField
        a e ha tau₁ tau₂ tau₃ psi D.beta1 D.beta2 D.beta3 D.h1 D.h2 D.h3
        D.a1 D.a2 D.a3 chi₁ chi₂ chi₃ (alpha * (u : Fˣ)) ∧
      X ∈ lattice D.thirdField (1 - (a : ℤ)) ∧
      MinimalOriginData D tau₁ tau₂ (scaleAddCharData F psi (alpha * (u : Fˣ))).character
        theta₁ theta₂ (D.adjustedOrigin X) := by
  letI : PrimeCyclicExtension F D.firstField := minimal_lowerPrime1 hG D O
  letI : PrimeCyclicExtension F D.secondField := minimal_lowerPrime2 hG D O
  letI : PrimeCyclicExtension F D.thirdField := minimal_lowerPrime3 hG D O
  have ht₁' : PrimeCyclicExtension.IsLowerBreak F D.firstField (2 * a - 1) := by
    simpa [actualLowerBreak] using ht₁
  have ht₂' : PrimeCyclicExtension.IsLowerBreak F D.secondField (2 * e) := by
    simpa [actualLowerBreak] using ht₂
  have ht₃' : PrimeCyclicExtension.IsLowerBreak F D.thirdField (2 * e) := by
    simpa [actualLowerBreak] using ht₃
  have hPsi := minimal_scaled_conductor F psi alpha halpha
  have htrivial : AddCharTrivialOnLattice F
      (scaleAddCharData F psi alpha).character (2 * (e : ℤ) + 1) := by
    simpa only [hPsi, neg_neg] using (scaleAddCharData F psi alpha).isConductor.trivial
  subst theta₁ theta₂
  by_cases hsmall : lambda.conductor ≤ e + a
  · have hbase : ∀ v : unitFiltration F (e + a),
        lambda.character (v : Fˣ) = corePhaseValue F
          (scaleAddCharData F psi alpha).character (D.adjustmentNorm 0) (v : Fˣ) := by
      intro v
      rw [lambda.isConductor.trivial _ (unitFiltration_antitone F hsmall v.property)]
      simp [corePhaseValue, AlignmentData.adjustmentNorm]
    have hresult := minimal_adjusted_data hG D O hres htwo ha hae hb ht₁ ht₂
      tau₁ tau₂ tau₃ _ H.1 chi₁ chi₂ H.2.1 H.2.2.1 lambda.character htrivial
      g1 g2 q3 0 0 (by omega) (by simp) (minimal_zero_error D g1 g2 q3) hbase
    refine ⟨1, 0, ?_, ?_, by simp, ?_⟩
    · simp
    · simpa only [OneMemClass.coe_one, mul_one] using H
    · simpa only [OneMemClass.coe_one, mul_one] using hresult
  · have hr : IsLamprechtStationaryDepth lambda.conductor (e + a) :=
      ⟨by omega, by omega, by omega⟩
    obtain ⟨Astar, hAstar, hbase⟩ := minimal_base_coefficient F lambda
      (scaleAddCharData F psi alpha) hr
    have Hnorm := normalization hG hres htwo ha hae hb D O
      ht₁' ht₂' ht₃' tau₁ htau₁ tau₂ htau₂ tau₃ htau₃
      psi alpha halpha chi₁ chi₂ chi₃ H
    obtain ⟨u, X, hnorm, Hu, halphaU, hXord, _hraw, hphase⟩ := Hnorm.2 Astar
    let h : ℤ := (lambda.conductor : ℤ) - (2 * (e : ℤ) + 1)
    have hh : h ≤ (a : ℤ) - 1 := by dsimp [h]; omega
    have huord : ord F ((u : Fˣ) : F) = 0 :=
      (mem_unitFiltration_zero F _).1
        (unitFiltration_antitone F (Nat.zero_le _) u.property)
    have hAord : ord F (((Astar / (u : Fˣ)) : Fˣ) : F) = ((-h : ℤ) : WithTop ℤ) := by
      rw [Units.val_div_eq_div_val, ord_div, huord, sub_zero, hAstar, hPsi]
      congr 1
      dsimp [h]
      ring
    have hX : intermediateOrder D.thirdField (X : D.thirdField) =
        ((-h : ℤ) : WithTop ℤ) := hXord.trans hAord
    have hXmem : (X : D.thirdField) ∈ lattice D.thirdField (-h) :=
      (mem_lattice D.thirdField).2 (le_of_eq hX.symm)
    have hnormVal : ((Astar / (u : Fˣ) : Fˣ) : F) = D.adjustmentNorm (X : D.thirdField) := by
      simpa only [coe_normUnits, AlignmentData.adjustmentNorm] using
        congrArg (fun w : Fˣ => (w : F)) hnorm
    have hbaseNew : ∀ v : unitFiltration F (e + a),
        lambda.character (v : Fˣ) = corePhaseValue F
          (scaleAddCharData F psi (alpha * (u : Fˣ))).character
          (D.adjustmentNorm (X : D.thirdField)) (v : Fˣ) := by
      intro v
      rw [hbase v]
      unfold corePhaseValue
      rw [← hnormVal, hphase]
    have hPsiNew := minimal_scaled_conductor F psi (alpha * (u : Fˣ))
      (halphaU.trans halpha)
    have htrivialNew : AddCharTrivialOnLattice F
        (scaleAddCharData F psi (alpha * (u : Fˣ))).character (2 * (e : ℤ) + 1) := by
      simpa only [hPsiNew, neg_neg] using
        (scaleAddCharData F psi (alpha * (u : Fˣ))).isConductor.trivial
    have E := commonError hG hres htwo ha hae hb D O
      g1 hg1 hg1R g2 hg2 hg2S q1 hq1 hq1S q2 hq2 hq2R q3 hq3 hq3SR
      ht₃ hU₁ hU₂ (X : D.thirdField) h hX
    refine ⟨u, (X : D.thirdField), halphaU, Hu,
      lattice_antitone D.thirdField (by omega) hXmem, ?_⟩
    exact minimal_adjusted_data hG D O hres htwo ha hae hb ht₁ ht₂
      tau₁ tau₂ tau₃ _ Hu.1 chi₁ chi₂ Hu.2.1 Hu.2.2.1 lambda.character htrivialNew
      g1 g2 q3 (X : D.thirdField) h hh hXmem E hbaseNew

end Diagram

end
end LanglandsSecondMainLemma.Dyadic.Maximal
