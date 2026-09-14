import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Dyadic.Maximal.Normalization
import LanglandsSecondMainLemma.Dyadic.Maximal.CommonError

/-!
# Higher stationary coefficients in the maximal dyadic case

Paper Lemma 12.12 (`D:MX:higher-coeff`). The weighted error is retained
until its product with the actual lower norm lies in the additive kernel.
All stationary identities below quantify over the whole indicated ideal.
-/

namespace LanglandsSecondMainLemma.Dyadic.Maximal

open LanglandsFirstMainLemma

noncomputable section

/-- The quadratic norm expansion, with the sign used by the manuscript. -/
private theorem higher_norm_one_sub
    (F E : Type) [Field F] [Field E] [Algebra F E]
    [Module.Free F E] [Module.Finite F E]
    (hdeg : Module.finrank F E = 2) (z : E) :
    norm F E (1 - z) = 1 - trace F E z + norm F E z := by
  have hn := norm_one_add_eq_one_add_sum_elementarySymmetric F E (-z)
  rw [hdeg] at hn
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at hn
  rw [elementarySymmetric_one] at hn
  have he : elementarySymmetric F E 2 (-z) = norm F E (-z) := by
    rw [← hdeg]
    exact elementarySymmetric_finrank F E (-z)
  rw [he, map_neg] at hn
  have hnneg : norm F E (-z) = norm F E z := by
    rw [show -z = algebraMap F E (-1 : F) * z by simp, map_mul,
      LanglandsFirstMainLemma.norm_algebraMap, hdeg]
    norm_num
  simpa only [hnneg, sub_eq_add_neg, add_assoc] using hn

/-- `D:MX:Qphase`, including its weighted error, on the complete ideal.
The two integer inequalities are precisely the argument depth and the
weighted-error depth; no surjectivity of a critical norm map is used. -/
private theorem higher_crossed_phase
    (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
    (hdeg : Module.finrank F E = 2) (hres : residueDegree F E = 1)
    (Psi : ContinuousAddChar F) (T q d k r j : ℤ)
    (htriv : AddCharTrivialOnLattice F Psi T)
    (beta A err : F) (Q : E)
    (hbeta : ord F beta = (k : WithTop ℤ))
    (hQ : Q ∈ lattice E r) (herr : err ∈ lattice F j)
    (hweighted : norm F E Q = beta * A + err)
    (hphase : ∀ x ∈ lattice E q,
      tracePullbackAddChar F E Psi (algebraMap F E beta * x) =
        Psi (beta * norm F E x))
    (harg : q ≤ r + d - 2 * k) (herror : T ≤ j - k + d)
    (z : E) (hz : z ∈ lattice E d) :
    tracePullbackAddChar F E Psi (Q * z) = Psi (A * norm F E z) := by
  have hram : ramificationIndex F E = 2 := by
    have hh := finrank_eq_ramificationIndex_mul_residueDegree F E
    rw [hdeg, hres, mul_one] at hh
    exact hh.symm
  have hb0 : beta ≠ 0 := (ord_ne_top_iff F).1 (by
    rw [hbeta]; exact WithTop.coe_ne_top)
  have hbE0 : algebraMap F E beta ≠ 0 := (map_ne_zero (algebraMap F E)).2 hb0
  have hbE : ord E (algebraMap F E beta) = ((2 * k : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hram, hbeta, ← WithTop.coe_nsmul]
    simp
  have hx : Q * z / algebraMap F E beta ∈ lattice E q := by
    apply lattice_antitone E harg
    apply (div_mem_lattice_iff E _ _ (2 * k) (r + d - 2 * k) hbE).2
    convert mul_mem_lattice E hQ hz using 1
    congr 1
    ring
  have hp := hphase _ hx
  rw [show algebraMap F E beta * (Q * z / algebraMap F E beta) = Q * z by
    field_simp] at hp
  have hn : norm F E (Q * z / algebraMap F E beta) =
      (beta * A + err) * norm F E z / beta ^ 2 := by
    rw [div_eq_mul_inv, map_mul, Algebra.norm_inv,
      map_mul, LanglandsFirstMainLemma.norm_algebraMap, hdeg, hweighted]
    rw [div_eq_mul_inv]
  rw [hn] at hp
  have halg : beta * ((beta * A + err) * norm F E z / beta ^ 2) =
      A * norm F E z + (err / beta) * norm F E z := by
    field_simp
  rw [halg, ContinuousAddChar.map_add_eq_mul] at hp
  have hediv : err / beta ∈ lattice F (j - k) := by
    apply (div_mem_lattice_iff F _ _ k (j - k) hbeta).2
    simpa only [show k + (j - k) = j by ring] using herr
  have hnz : norm F E z ∈ lattice F d := by
    rw [mem_lattice, ord_norm, hres, one_nsmul]
    exact (mem_lattice E).1 hz
  rw [htriv _ (lattice_antitone F herror (mul_mem_lattice F hediv hnz)), mul_one] at hp
  exact hp

/-- Exact quadratic expansion transfers a base stationary chart and its
crossed phase to the actual twisted character on the whole upper ideal. -/
private theorem higher_twisted_chart
    (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
    [PrimeCyclicExtension F E]
    {t d s q : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hdeg : Module.finrank F E = 2) (hres : residueDegree F E = 1)
    (hd : 0 < d) (hq : 0 < q) (hs : 0 < s) (hsd : s ≤ d)
    (hqd : q ≤ d) (htrace : (q : ℤ) ≤ ((d : ℤ) + (t + 1 : ℕ)) / 2)
    (Psi : ContinuousAddChar F) (lambda : ContinuousQuasiChar F)
    (chi : ContinuousQuasiChar E) (A : F) (c Q Z : E)
    (hbase : ∀ (x : F) (hx : x ∈ lattice F (q : ℤ)),
      lambda (lowerOneSubUnit F q hq x hx) = Psi (A * x))
    (hcore : ∀ u : unitFiltration E s,
      chi (u : Eˣ) = corePhaseValue E (tracePullbackAddChar F E Psi) c (u : Eˣ))
    (hphase : ∀ z ∈ lattice E (d : ℤ),
      tracePullbackAddChar F E Psi (Q * z) = Psi (A * norm F E z))
    (hZ : Z = c + algebraMap F E A - Q)
    (z : E) (hz : z ∈ lattice E (d : ℤ)) :
    (chi * normQuasiChar F E lambda) (lowerOneSubUnit E d hd z hz) =
      tracePullbackAddChar F E Psi (Z * z) := by
  have hzq : z ∈ lattice E (q : ℤ) := lattice_antitone E (by omega) hz
  have hnz : norm F E z ∈ lattice F (q : ℤ) := by
    rw [mem_lattice, ord_norm, hres, one_nsmul]
    exact (mem_lattice E).1 hzq
  have htz : trace F E z ∈ lattice F (q : ℤ) := by
    obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
    have hm : trace F E z ∈ Submodule.map
        ((trace F E).restrictScalars (ringOfIntegers F))
        ((lattice E (d : ℤ)).restrictScalars (ringOfIntegers F)) :=
      Submodule.mem_map.mpr ⟨z, hz, rfl⟩
    rw [cyclicPrime_trace_lattice_image_eq F E ht hres pi hpi hgen, hdeg] at hm
    apply lattice_antitone F htrace
    simpa only [Nat.reduceSub, one_mul, Nat.cast_ofNat] using hm
  have hdiff := sub_mem_lattice F htz hnz
  have hnunit : normUnits F E (lowerOneSubUnit E d hd z hz) =
      lowerOneSubUnit F q hq (trace F E z - norm F E z) hdiff := by
    apply Units.ext
    simp only [coe_normUnits, coe_lowerOneSubUnit]
    rw [higher_norm_one_sub F E hdeg]
    ring
  have humem : lowerOneSubUnit E d hd z hz ∈ unitFiltration E s := by
    cases s with
    | zero => omega
    | succ s =>
      apply (mem_unitFiltration_succ_iff_sub_mem_lattice E s _).2
      simp only [coe_lowerOneSubUnit, sub_sub_cancel_left]
      exact neg_mem_lattice E (lattice_antitone E (by omega) hz)
  have hc := hcore ⟨_, humem⟩
  simp only [corePhaseValue, coe_lowerOneSubUnit, sub_sub_cancel] at hc
  rw [ContinuousQuasiChar.mul_apply, normQuasiChar_apply]
  change chi (lowerOneSubUnit E d hd z hz) *
    lambda (normUnits F E (lowerOneSubUnit E d hd z hz)) = _
  rw [hnunit, hbase, hc]
  rw [hZ, show (c + algebraMap F E A - Q) * z =
    c * z + (algebraMap F E A * z - Q * z) by ring,
    ContinuousAddChar.map_add_eq_mul]
  congr 1
  have hsub (x y : E) : tracePullbackAddChar F E Psi (x - y) =
      tracePullbackAddChar F E Psi x / tracePullbackAddChar F E Psi y :=
    (tracePullbackAddChar F E Psi).toAddChar.map_sub_eq_div x y
  rw [hsub, hphase z hz]
  have htA : tracePullbackAddChar F E Psi (algebraMap F E A * z) =
      Psi (A * trace F E z) := by
    rw [tracePullbackAddChar_apply]
    congr 1
    simpa [Algebra.smul_def] using (trace F E).map_smul A z
  rw [htA, mul_sub]
  exact Psi.toAddChar.map_sub_eq_div _ _

/-- Select an actual nonzero base coefficient from FML's full stationary
quotient class. The minus sign converts its `1+x` chart to `1-x`. -/
private theorem higher_base_coefficient
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (lambda : ContinuousQuasiChar F) (psi : LocalAddCharData F)
    (T : ℤ) (hpsi : psi.conductor = -T)
    (n : ℕ) (hn : multiplicativeConductorExponent F lambda = n) (hnpos : 1 < n) :
    ∃ A : Fˣ, ord F (A : F) = ((T - (n : ℤ) : ℤ) : WithTop ℤ) ∧
      ∀ (x : F) (hx : x ∈ lattice F (((n + 1) / 2 : ℕ) : ℤ)),
        lambda (lowerOneSubUnit F ((n + 1) / 2) (by omega) x hx) =
          psi.character ((A : F) * x) := by
  let chi := canonicalLocalQuasiCharData F lambda
  have hcn : chi.conductor = n := hn
  have hr : IsLamprechtStationaryDepth chi.conductor ((n + 1) / 2) := by
    rw [hcn]
    constructor <;> omega
  have hGamma : ord F ((1 : Fˣ) : F) = ((T + psi.conductor : ℤ) : WithTop ℤ) := by
    simp [hpsi]
  obtain ⟨c, hc⟩ := latticeQuotientMk_surjective F
    (sub_le_sub_left hr.int_le_conductor T)
    (stationaryNumeratorClass F chi psi T hr 1 hGamma)
  have hcord := stationaryNumeratorClass_representative_ord F chi psi T hr 1 hGamma c hc
  have hc0 : -(c : F) ≠ 0 := by
    apply neg_ne_zero.mpr
    exact (ord_ne_top_iff F).1 (by rw [hcord]; exact WithTop.coe_ne_top)
  refine ⟨Units.mk0 (-(c : F)) hc0, ?_, ?_⟩
  · simpa only [Units.val_mk0, ord_neg, hcn] using hcord
  · intro x hx
    have hlin := stationaryNumeratorClass_linearization F chi psi T hr 1 hGamma c hc
      ⟨-x, neg_mem_lattice F hx⟩
    have hu : (positiveUnitOfLattice F hr.pos ⟨-x, neg_mem_lattice F hx⟩ : Fˣ) =
        lowerOneSubUnit F ((n + 1) / 2) (by omega) x hx := by
      apply Units.ext
      simp only [coe_positiveUnitOfLattice, coe_lowerOneSubUnit]
      ring
    rw [hu] at hlin
    simpa only [chi, canonicalLocalQuasiCharData_character, Units.val_one,
      div_one, mul_neg, Units.val_mk0, neg_mul] using hlin

section ActualFields

variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]

local instance (L : IntermediateField F K) : ValuativeRel L :=
  Basic.intermediateFieldValuativeRel L
local instance (L : IntermediateField F K) : TopologicalSpace L :=
  Basic.intermediateFieldTopology L
local instance (L : IntermediateField F K) : IsNonarchimedeanLocalField L :=
  Basic.intermediateField_localField L
local instance (L : IntermediateField F K) : ValuativeExtension F L :=
  Basic.intermediateField_lowerValuativeExtension L
local instance (L : IntermediateField F K) : ValuativeExtension L K :=
  Basic.intermediateField_upperValuativeExtension L

omit [Module.Free F K] in
/-- Total ramification of the actual tower forces residue degree one on
both edges, by norm transitivity evaluated at a top uniformizer. -/
private theorem higher_residue_degrees
    (L : IntermediateField F K) (hres : residueDegree F K = 1) :
    residueDegree F L = 1 ∧ residueDegree L K = 1 := by
  obtain ⟨x, hx⟩ := exists_ord_eq K 1
  have heq := congrArg (ord F) (Basic.norm_tower (F := F) (L := L) x)
  rw [ord_norm, ord_norm, ord_norm, hres, hx] at heq
  have hm : residueDegree F L * residueDegree L K = 1 := by
    have hz : residueDegree F L • residueDegree L K • (1 : ℤ) = 1 • (1 : ℤ) := by
      exact_mod_cast heq
    have hz' : (residueDegree F L : ℤ) * (residueDegree L K : ℤ) = 1 := by
      simpa [nsmul_eq_mul] using hz
    exact_mod_cast hz'
  exact mul_eq_one.mp hm

variable {pi : ringOfIntegers F} {e a b : ℕ}
  {u0 w0 : (ringOfIntegers F)ˣ} {s R0 : K}

set_option maxHeartbeats 1200000 in
/-- **The actual higher coefficients (`D:MX:higher-coeff`).**

Use the normalization and exact third-field element already supplied by
`normalization`: `H` is its preserved lower/core data and `hbase` is the
preserved chart of the same continuous base character. `CE` is the
constructed `commonError` data for this actual element, rather than an
assumption of upper stationarity. The conclusion proves both whole-ideal
formulas, their precise conductors, and the valuation of the actual top
origin and each of its two norms.

Here `h` is nonnegative because this branch has `a ≤ h` and `1 ≤ a`.
The first depth's natural subtraction is proved to equal the integer
expression `T+h-a` before any valuation calculation. -/
theorem higherCoefficients_of_normalized
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (hres : residueDegree F K = 1)
    (ha : 1 ≤ a) (hae : a ≤ e) (hb : b = 2 * e - 2 * a + 1)
    (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)
    (ht₁ : actualLowerBreak hG D.firstField O.first_degree (2 * a - 1))
    (ht₂ : actualLowerBreak hG D.secondField O.second_degree (2 * e))
    (tau₁ : NormCharacter F D.firstField) (tau₂ : NormCharacter F D.secondField)
    (tau₃ : NormCharacter F D.thirdField)
    (psi : LocalAddCharData F) (alpha : Fˣ)
    (halpha : ord F (alpha : F) =
      ((-psi.conductor - (2 * (e : ℤ) + 1) : ℤ) : WithTop ℤ))
    (chi₁ : ContinuousQuasiChar D.firstField)
    (chi₂ : ContinuousQuasiChar D.secondField)
    (chi₃ : ContinuousQuasiChar D.thirdField)
    (hc₁ : IsMultiplicativeConductor D.firstField chi₁ (4 * e + 1))
    (hc₂ : IsMultiplicativeConductor D.secondField chi₂ (2 * e + 2 * a))
    (H : NormalizationFormulas F D.firstField D.secondField D.thirdField
      a e ha tau₁ tau₂ tau₃ psi D.beta1 D.beta2 D.beta3 D.h1 D.h2 D.h3
      D.a1 D.a2 D.a3 chi₁ chi₂ chi₃ alpha)
    (lambda : ContinuousQuasiChar F) (h : ℕ) (hah : a ≤ h)
    (hn : multiplicativeConductorExponent F lambda = 2 * e + 1 + h)
    (g1 : Gal(K/D.firstField)) (g2 : Gal(K/D.secondField))
    (q3 : Gal(D.thirdField/F)) (X : D.thirdField)
    (hX : intermediateOrder D.thirdField X = ((-(h : ℤ) : ℤ) : WithTop ℤ))
    (CE : CommonErrorData D g1 g2 q3 X (h : ℤ))
    (hbase : ∀ (x : F)
      (hx : x ∈ lattice F (((2 * e + 1 + h + 1) / 2 : ℕ) : ℤ)),
      lambda (lowerOneSubUnit F ((2 * e + 1 + h + 1) / 2) (by omega) x hx) =
        (scaleAddCharData F psi alpha).character (D.adjustmentNorm X * x)) :
    let b₁ := 2 * e + 1 + h - a
    let b₂ := e + 1 + h
    let theta₁ := chi₁ * normQuasiChar F D.firstField lambda
    let theta₂ := chi₂ * normQuasiChar F D.secondField lambda
    multiplicativeConductorExponent D.firstField theta₁ = 2 * b₁ ∧
    multiplicativeConductorExponent D.secondField theta₂ = 2 * b₂ - 1 ∧
    (∀ (z : D.firstField) (hz : z ∈ lattice D.firstField (b₁ : ℤ)),
      theta₁ (lowerOneSubUnit D.firstField b₁ (by dsimp only [b₁]; omega) z hz) =
        tracePullbackAddChar F D.firstField (scaleAddCharData F psi alpha).character
          (norm D.firstField K (D.adjustedOrigin X) * z)) ∧
    (∀ (z : D.secondField) (hz : z ∈ lattice D.secondField (b₂ : ℤ)),
      theta₂ (lowerOneSubUnit D.secondField b₂ (by dsimp only [b₂]; omega) z hz) =
        tracePullbackAddChar F D.secondField (scaleAddCharData F psi alpha).character
          (norm D.secondField K (D.adjustedOrigin X) * z)) ∧
    ord K (D.adjustedOrigin X) = ((-2 * (h : ℤ) : ℤ) : WithTop ℤ) ∧
    intermediateOrder D.firstField (norm D.firstField K (D.adjustedOrigin X)) =
      ((-2 * (h : ℤ) : ℤ) : WithTop ℤ) ∧
    intermediateOrder D.secondField (norm D.secondField K (D.adjustedOrigin X)) =
      ((-2 * (h : ℤ) : ℤ) : WithTop ℤ) := by
  let E₁ := Basic.intermediateField_tower_compatible Nat.prime_two hG
    D.firstField O.first_degree
  let E₂ := Basic.intermediateField_tower_compatible Nat.prime_two hG
    D.secondField O.second_degree
  let E₃ := Basic.intermediateField_tower_compatible Nat.prime_two hG
    D.thirdField O.third_degree
  letI : PrimeCyclicExtension F D.firstField :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F D.firstField E₁.2.2.2.2.2.2.2.2.2.2.2.1
  letI : PrimeCyclicExtension F D.secondField :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F D.secondField E₂.2.2.2.2.2.2.2.2.2.2.2.1
  have ht₁' : PrimeCyclicExtension.IsLowerBreak F D.firstField (2 * a - 1) := by
    simpa [actualLowerBreak] using ht₁
  have ht₂' : PrimeCyclicExtension.IsLowerBreak F D.secondField (2 * e) := by
    simpa [actualLowerBreak] using ht₂
  have hr₁ := higher_residue_degrees D.firstField hres
  have hr₂ := higher_residue_degrees D.secondField hres
  have hr₃ := higher_residue_degrees D.thirdField hres
  have hb₁ : ((2 * e + 1 + h - a : ℕ) : ℤ) =
      2 * (e : ℤ) + 1 + (h : ℤ) - (a : ℤ) := by omega
  have hb' : (b : ℤ) = 2 * (e : ℤ) - 2 * (a : ℤ) + 1 := by omega
  have hcond := (twist_conductors F D.firstField D.secondField ha hae ht₁' ht₂'
    hr₁.1 hr₂.1 O.first_degree O.second_degree chi₁ chi₂ hc₁ hc₂ lambda).2 (by omega)
  have htriv : AddCharTrivialOnLattice F
      (scaleAddCharData F psi alpha).character (2 * (e : ℤ) + 1) := by
    intro x hx
    rw [scaleAddCharData_character_apply]
    apply psi.isConductor.trivial
    have haMem : (alpha : F) ∈ lattice F (-psi.conductor - (2 * (e : ℤ) + 1)) := by
      rw [mem_lattice, halpha]
    simpa only [sub_add_cancel] using mul_mem_lattice F haMem hx
  have herr : D.commonErrorTerm g1 X ∈ lattice F
      (2 * (e : ℤ) + 1 - (a : ℤ) - (h : ℤ)) := by
    exact (mem_lattice F).2 (by simpa only [Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one] using CE.error_bound)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hh := hcond.1
    rw [hn] at hh
    omega
  · have hh := hcond.2.1
    rw [hn] at hh
    omega
  · intro z hz
    have hQ : D.firstCrossedTrace g1 X ∈ lattice D.firstField ((b : ℤ) - (h : ℤ)) :=
      (mem_lattice D.firstField).2 CE.first_crossed_bound
    have hp := higher_crossed_phase F D.firstField O.first_degree hr₁.1
      (scaleAddCharData F psi alpha).character (2 * (e : ℤ) + 1) (a : ℤ)
      ((2 * e + 1 + h - a : ℕ) : ℤ) (b : ℤ) ((b : ℤ) - (h : ℤ))
      (2 * (e : ℤ) + 1 - (a : ℤ) - (h : ℤ)) htriv
      D.beta1 (D.adjustmentNorm X) (D.commonErrorTerm g1 X)
      (D.firstCrossedTrace g1 X) O.beta1_order hQ herr CE.first_weighted_norm
      H.1.first_phase (by omega) (by omega)
    exact higher_twisted_chart F D.firstField ht₁' O.first_degree hr₁.1
      (by omega) (by omega) (by omega) (by omega) (by omega) (by
        have htcast : ((2 * a - 1 + 1 : ℕ) : ℤ) = 2 * (a : ℤ) := by omega
        rw [htcast, hb₁]
        omega)
      (scaleAddCharData F psi alpha).character lambda chi₁ (D.adjustmentNorm X)
      D.a1 (D.firstCrossedTrace g1 X) (norm D.firstField K (D.adjustedOrigin X))
      hbase H.2.1 hp CE.first_norm z hz
  · intro z hz
    have hQ : D.secondCrossedTrace g2 X ∈ lattice D.secondField (-(h : ℤ)) :=
      (mem_lattice D.secondField).2 CE.second_crossed_bound
    have hp := higher_crossed_phase F D.secondField O.second_degree hr₂.1
      (scaleAddCharData F psi alpha).character (2 * (e : ℤ) + 1) ((e + 1 : ℕ) : ℤ)
      ((e + 1 + h : ℕ) : ℤ) 0 (-(h : ℤ))
      (2 * (e : ℤ) + 1 - (a : ℤ) - (h : ℤ)) htriv
      D.beta2 (D.adjustmentNorm X) (D.commonErrorTerm g1 X)
      (D.secondCrossedTrace g2 X) O.beta2_order hQ herr CE.second_weighted_norm
      H.1.second_phase (by omega) (by omega)
    exact higher_twisted_chart F D.secondField ht₂' O.second_degree hr₂.1
      (by omega) (by omega) (by omega) (by omega) (by omega) (by
        push_cast
        omega)
      (scaleAddCharData F psi alpha).character lambda chi₂ (D.adjustmentNorm X)
      D.a2 (D.secondCrossedTrace g2 X) (norm D.secondField K (D.adjustedOrigin X))
      hbase H.2.2.1 hp CE.second_norm z hz
  · have hram : ramificationIndex D.thirdField K = 2 := by
      have hh := finrank_eq_ramificationIndex_mul_residueDegree D.thirdField K
      rw [E₃.2.2.2.2.2.2.2.2.2.2.1, hr₃.2, mul_one] at hh
      exact hh.symm
    have hxK : ord K (algebraMap D.thirdField K X) =
        ((-2 * (h : ℤ) : ℤ) : WithTop ℤ) := by
      rw [ord_algebraMap, hram]
      change 2 • intermediateOrder D.thirdField X = _
      rw [hX, ← WithTop.coe_nsmul]
      congr 1
      simp
    have hord : ord K (D.adjustedOrigin X) =
        ((-2 * (h : ℤ) : ℤ) : WithTop ℤ) := by
      change ord K (D.origin - algebraMap D.thirdField K X) = _
      rw [sub_eq_add_neg, ord_add_eq_min K (by
        rw [ord_neg, hxK, O.origin_order]
        exact ne_of_gt (WithTop.coe_lt_coe.mpr (by omega))),
        ord_neg, hxK, O.origin_order, min_eq_right]
      exact WithTop.coe_le_coe.mpr (by omega)
    refine ⟨hord, ?_, ?_⟩
    · change ord D.firstField (norm D.firstField K (D.adjustedOrigin X)) = _
      rw [ord_norm, hr₁.2, one_nsmul, hord]
    · change ord D.secondField (norm D.secondField K (D.adjustedOrigin X)) = _
      rw [ord_norm, hr₂.2, one_nsmul, hord]

set_option maxHeartbeats 1200000 in
/-- **Constructed higher stationary origins (`D:MX:higher-coeff`).**

For every actual continuous base twist of conductor `T+h`, `h ≥ a`, FML
supplies its whole-ideal stationary coefficient. The proved normalization
change then makes that coefficient an exact third-field norm while
preserving the given lower characters and all three core formulas.
`commonError` constructs the weighted estimates for the chosen element.
The resulting two norms are stationary on their complete half-conductor
ideals, with the exact conductors and valuation `-2h`.

The automorphisms, their generator actions, and the lower/upper break
hypotheses are the genuine diagram data used by `commonError`. No
stationary coefficient, norm representative, or error bound is an input.
-/
theorem higherCoefficients
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (hres : residueDegree F K = 1)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (ha : 1 ≤ a) (hae : a ≤ e) (hb : b = 2 * e - 2 * a + 1)
    (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)
    (ht₁ : actualLowerBreak hG D.firstField O.first_degree (2 * a - 1))
    (ht₂ : actualLowerBreak hG D.secondField O.second_degree (2 * e))
    (ht₃ : actualLowerBreak hG D.thirdField O.third_degree (2 * e))
    (htK₁ : actualUpperBreak hG D.firstField O.first_degree (4 * e - 2 * a + 1))
    (htK₂ : actualUpperBreak hG D.secondField O.second_degree (2 * a - 1))
    (tau₁ : NormCharacter F D.firstField) (htau₁ : tau₁ ≠ 1)
    (tau₂ : NormCharacter F D.secondField) (htau₂ : tau₂ ≠ 1)
    (tau₃ : NormCharacter F D.thirdField) (htau₃ : tau₃ ≠ 1)
    (psi : LocalAddCharData F) (alpha : Fˣ)
    (halpha : ord F (alpha : F) =
      ((-psi.conductor - (2 * (e : ℤ) + 1) : ℤ) : WithTop ℤ))
    (chi₁ : ContinuousQuasiChar D.firstField)
    (chi₂ : ContinuousQuasiChar D.secondField)
    (chi₃ : ContinuousQuasiChar D.thirdField)
    (hc₁ : IsMultiplicativeConductor D.firstField chi₁ (4 * e + 1))
    (hc₂ : IsMultiplicativeConductor D.secondField chi₂ (2 * e + 2 * a))
    (H : NormalizationFormulas F D.firstField D.secondField D.thirdField
      a e ha tau₁ tau₂ tau₃ psi D.beta1 D.beta2 D.beta3 D.h1 D.h2 D.h3
      D.a1 D.a2 D.a3 chi₁ chi₂ chi₃ alpha)
    (lambda : ContinuousQuasiChar F) (h : ℕ) (hah : a ≤ h)
    (hn : multiplicativeConductorExponent F lambda = 2 * e + 1 + h)
    (g1 : Gal(K/D.firstField)) (hg1 : g1 ≠ 1) (hg1R : g1 D.R = -D.R)
    (g2 : Gal(K/D.secondField)) (hg2 : g2 ≠ 1) (hg2S : g2 D.S = -D.S)
    (q1 : Gal(D.firstField/F)) (hq1 : q1 ≠ 1)
    (hq1S : q1 D.firstGenerator = -D.firstGenerator)
    (q2 : Gal(D.secondField/F)) (hq2 : q2 ≠ 1)
    (hq2R : q2 D.secondGenerator = -D.secondGenerator)
    (q3 : Gal(D.thirdField/F)) (hq3 : q3 ≠ 1)
    (hq3SR : q3 D.thirdGenerator = -D.thirdGenerator) :
    ∃ (u : unitFiltration F (2 * e)) (X : D.thirdFieldˣ),
      NormalizationFormulas F D.firstField D.secondField D.thirdField
        a e ha tau₁ tau₂ tau₃ psi D.beta1 D.beta2 D.beta3 D.h1 D.h2 D.h3
        D.a1 D.a2 D.a3 chi₁ chi₂ chi₃ (alpha * (u : Fˣ)) ∧
      ord F ((alpha * (u : Fˣ) : Fˣ) : F) = ord F (alpha : F) ∧
      intermediateOrder D.thirdField (X : D.thirdField) =
        ((-(h : ℤ) : ℤ) : WithTop ℤ) ∧
      (∀ (x : F) (hx : x ∈ lattice F (((2 * e + 1 + h + 1) / 2 : ℕ) : ℤ)),
        lambda (lowerOneSubUnit F ((2 * e + 1 + h + 1) / 2) (by omega) x hx) =
          (scaleAddCharData F psi (alpha * (u : Fˣ))).character
            (D.adjustmentNorm (X : D.thirdField) * x)) ∧
    let b₁ := 2 * e + 1 + h - a
    let b₂ := e + 1 + h
    let theta₁ := chi₁ * normQuasiChar F D.firstField lambda
    let theta₂ := chi₂ * normQuasiChar F D.secondField lambda
    multiplicativeConductorExponent D.firstField theta₁ = 2 * b₁ ∧
    multiplicativeConductorExponent D.secondField theta₂ = 2 * b₂ - 1 ∧
    (∀ (z : D.firstField) (hz : z ∈ lattice D.firstField (b₁ : ℤ)),
      theta₁ (lowerOneSubUnit D.firstField b₁ (by dsimp only [b₁]; omega) z hz) =
        tracePullbackAddChar F D.firstField (scaleAddCharData F psi (alpha * (u : Fˣ))).character
          (norm D.firstField K (D.adjustedOrigin X) * z)) ∧
    (∀ (z : D.secondField) (hz : z ∈ lattice D.secondField (b₂ : ℤ)),
      theta₂ (lowerOneSubUnit D.secondField b₂ (by dsimp only [b₂]; omega) z hz) =
        tracePullbackAddChar F D.secondField (scaleAddCharData F psi (alpha * (u : Fˣ))).character
          (norm D.secondField K (D.adjustedOrigin X) * z)) ∧
    ord K (D.adjustedOrigin X) = ((-2 * (h : ℤ) : ℤ) : WithTop ℤ) ∧
    intermediateOrder D.firstField (norm D.firstField K (D.adjustedOrigin X)) =
      ((-2 * (h : ℤ) : ℤ) : WithTop ℤ) ∧
    intermediateOrder D.secondField (norm D.secondField K (D.adjustedOrigin X)) =
      ((-2 * (h : ℤ) : ℤ) : WithTop ℤ) := by
  let E₁ := Basic.intermediateField_tower_compatible Nat.prime_two hG
    D.firstField O.first_degree
  let E₂ := Basic.intermediateField_tower_compatible Nat.prime_two hG
    D.secondField O.second_degree
  let E₃ := Basic.intermediateField_tower_compatible Nat.prime_two hG
    D.thirdField O.third_degree
  letI : PrimeCyclicExtension F D.firstField :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F D.firstField E₁.2.2.2.2.2.2.2.2.2.2.2.1
  letI : PrimeCyclicExtension F D.secondField :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F D.secondField E₂.2.2.2.2.2.2.2.2.2.2.2.1
  letI : PrimeCyclicExtension F D.thirdField :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F D.thirdField E₃.2.2.2.2.2.2.2.2.2.2.2.1
  have ht₁' : PrimeCyclicExtension.IsLowerBreak F D.firstField (2 * a - 1) := by
    simpa [actualLowerBreak] using ht₁
  have ht₂' : PrimeCyclicExtension.IsLowerBreak F D.secondField (2 * e) := by
    simpa [actualLowerBreak] using ht₂
  have ht₃' : PrimeCyclicExtension.IsLowerBreak F D.thirdField (2 * e) := by
    simpa [actualLowerBreak] using ht₃
  have hpsi : (scaleAddCharData F psi alpha).conductor = -(2 * (e : ℤ) + 1) := by
    have huord := ord_coe_eq_unitOrder F alpha
    rw [halpha] at huord
    have hu : unitOrder F alpha = -psi.conductor - (2 * (e : ℤ) + 1) :=
      (WithTop.coe_eq_coe.mp huord).symm
    rw [scaleAddCharData_conductor, hu]
    omega
  obtain ⟨Astar, hAord, hAchart⟩ := higher_base_coefficient F lambda
    (scaleAddCharData F psi alpha) (2 * (e : ℤ) + 1) hpsi (2 * e + 1 + h) hn (by omega)
  have hAord' : ord F (Astar : F) = ((-(h : ℤ) : ℤ) : WithTop ℤ) := by
    rw [hAord]
    congr 1
    push_cast
    omega
  obtain ⟨u, X, hnorm, Hnew, halphaNew, hXord, _hraw, hvalues⟩ :=
    (normalization hG hres htwo ha hae hb D O ht₁' ht₂' ht₃'
      tau₁ htau₁ tau₂ htau₂ tau₃ htau₃ psi alpha halpha chi₁ chi₂ chi₃ H).2 Astar
  have hu0 : ord F ((u : Fˣ) : F) = 0 :=
    (mem_unitFiltration_zero F _).1
      (unitFiltration_antitone F (Nat.zero_le _) u.property)
  have hquot : ord F ((Astar / (u : Fˣ) : Fˣ) : F) =
      ((-(h : ℤ) : ℤ) : WithTop ℤ) := by
    rw [Units.val_div_eq_div_val, ord_div, hAord', hu0, sub_zero]
  have hX : intermediateOrder D.thirdField (X : D.thirdField) =
      ((-(h : ℤ) : ℤ) : WithTop ℤ) := hXord.trans hquot
  have hnormVal : ((Astar / (u : Fˣ) : Fˣ) : F) =
      D.adjustmentNorm (X : D.thirdField) := congrArg Units.val hnorm
  have hbase : ∀ (x : F)
      (hx : x ∈ lattice F (((2 * e + 1 + h + 1) / 2 : ℕ) : ℤ)),
      lambda (lowerOneSubUnit F ((2 * e + 1 + h + 1) / 2) (by omega) x hx) =
        (scaleAddCharData F psi (alpha * (u : Fˣ))).character
          (D.adjustmentNorm (X : D.thirdField) * x) := by
    intro x hx
    rw [hAchart x hx]
    simpa only [hnormVal] using (hvalues x).symm
  have CE := commonError hG hres htwo ha hae hb D O
    g1 hg1 hg1R g2 hg2 hg2S q1 hq1 hq1S q2 hq2 hq2R q3 hq3 hq3SR
    ht₃ htK₁ htK₂ (X : D.thirdField) (h : ℤ) hX
  refine ⟨u, X, Hnew, halphaNew, hX, hbase, ?_⟩
  exact higherCoefficients_of_normalized hG hres ha hae hb D O ht₁ ht₂
    tau₁ tau₂ tau₃ psi (alpha * (u : Fˣ)) (halphaNew.trans halpha)
    chi₁ chi₂ chi₃ hc₁ hc₂ Hnew lambda h hah hn g1 g2 q3 (X : D.thirdField) hX CE hbase

end ActualFields

end

end LanglandsSecondMainLemma.Dyadic.Maximal
