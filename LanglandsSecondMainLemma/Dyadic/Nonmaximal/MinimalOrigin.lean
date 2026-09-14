import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.Normalization
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.CommonError

/-!
# Minimal origins in the nonmaximal dyadic branch

Paper Lemma 13.10 (`D:NM:minimal-origin`), including the construction in
lines 7853–7871 and the third index when the breaks are equal.
All perturbation bounds use integer lattice exponents.
-/

namespace LanglandsSecondMainLemma.Dyadic.Nonmaximal

open LanglandsFirstMainLemma

open private additive_eq_of_sub_mem from
  LanglandsSecondMainLemma.Dyadic.Nonmaximal.LowerCharacters
open private quadratic_map_mem_lattice quadratic_card trace_eq_self_add_nontrivial
  norm_eq_self_mul_nontrivial from LanglandsSecondMainLemma.Dyadic.Nonmaximal.CommonError

noncomputable section

set_option maxHeartbeats 1000000

section OneField

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private theorem oneSub_mem_filtration {q : ℕ} (hq : 0 < q)
    {v : F} (hv : v ∈ lattice F (q : ℤ)) (B : Fˣ) (hB : (B : F) = 1 - v) :
    B ∈ unitFiltration F q := by
  cases q with
  | zero => omega
  | succ q =>
    rw [mem_unitFiltration_succ_iff_sub_mem_lattice, hB]
    simpa only [sub_sub_cancel_left] using neg_mem_lattice F hv

private theorem displacement_mem {q : ℕ} (hq : 0 < q)
    (B : unitFiltration F q) : 1 - ((B : Fˣ) : F) ∈ lattice F (q : ℤ) := by
  cases q with
  | zero => omega
  | succ q =>
    simpa only [neg_sub] using neg_mem_lattice F
      ((mem_unitFiltration_succ_iff_sub_mem_lattice F q _).mp B.property)

/-- FML's stationary numerator class at the requested full base depth,
with the manuscript's minus-sign convention. -/
private theorem base_covector (χ : LocalQuasiCharData F) (Ψ : LocalAddCharData F)
    {q : ℕ} (hq : IsLamprechtStationaryDepth χ.conductor q) :
    ∃ A : Fˣ,
      ord F (A : F) = ((-Ψ.conductor - (χ.conductor : ℤ) : ℤ) : WithTop ℤ) ∧
      ∀ v ∈ lattice F (q : ℤ), ∀ B : Fˣ, (B : F) = 1 - v →
        χ.character B = Ψ.character ((A : F) * v) := by
  have hΓ : ord F ((1 : Fˣ) : F) =
      (((-Ψ.conductor) + Ψ.conductor : ℤ) : WithTop ℤ) := by simp
  obtain ⟨c, hc⟩ := latticeQuotientMk_surjective F
    (sub_le_sub_left hq.int_le_conductor (-Ψ.conductor))
    (stationaryNumeratorClass F χ Ψ (-Ψ.conductor) hq 1 hΓ)
  have hcOrd := stationaryNumeratorClass_representative_ord F χ Ψ (-Ψ.conductor)
    hq 1 hΓ c hc
  have hc0 : -(c : F) ≠ 0 := (ord_ne_top_iff F).mp
    (by rw [ord_neg, hcOrd]; exact WithTop.coe_ne_top)
  refine ⟨Units.mk0 (-(c : F)) hc0, by simpa using hcOrd, ?_⟩
  intro v hv B hB
  have hlin := stationaryNumeratorClass_linearization F χ Ψ (-Ψ.conductor)
    hq 1 hΓ c hc ⟨-v, neg_mem_lattice F hv⟩
  have hunit : positiveUnitOfLattice F hq.pos ⟨-v, neg_mem_lattice F hv⟩ = B := by
    apply Units.ext
    simp only [coe_positiveUnitOfLattice, hB, sub_eq_add_neg]
  rw [hunit] at hlin
  simpa only [Units.val_one, div_one, mul_neg, neg_mul, Units.val_mk0] using hlin

private theorem sub_order_of_deeper {x y : F} (h : ord F x < ord F y) :
    ord F (x - y) = ord F x := by
  rw [sub_eq_add_neg, ord_add_eq_min F (by simpa only [ord_neg] using ne_of_lt h),
    ord_neg, min_eq_left h.le]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
private theorem phase_sub (Ψ : ContinuousAddChar F) (x y : F) :
    Ψ (x - y) = Ψ x / Ψ y := Ψ.toAddChar.map_sub_eq_div x y

end OneField

section Edge

variable (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra F L] [ValuativeExtension F L] [Module.Finite F L]
  [Algebra.IsQuadraticExtension F L] [PrimeCyclicExtension F L]

omit [PrimeCyclicExtension F L] in
private theorem ramification_two (hres : residueDegree F L = 1) :
    ramificationIndex F L = 2 := by
  have h := finrank_eq_ramificationIndex_mul_residueDegree F L
  rw [hres, mul_one, Algebra.IsQuadraticExtension.finrank_eq_two F L] at h
  exact h.symm

private theorem trace_mem_of_depth {q : ℕ} (hq : 1 ≤ q)
    (ht : PrimeCyclicExtension.IsLowerBreak F L (2 * q - 1))
    (hres : residueDegree F L = 1) {s b : ℤ} (hb : b ≤ (s + 2 * q) / 2)
    {v : L} (hv : v ∈ lattice L s) : trace F L v ∈ lattice F b := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F L hres
  have hmap : trace F L v ∈
      Submodule.map ((trace F L).restrictScalars (ringOfIntegers F))
        ((lattice L s).restrictScalars (ringOfIntegers F)) :=
    Submodule.mem_map.mpr ⟨v, hv, rfl⟩
  rw [cyclicPrime_trace_lattice_image_eq F L ht hres pi hpi hgen,
    Algebra.IsQuadraticExtension.finrank_eq_two F L] at hmap
  simp only [Nat.reduceSub, one_mul,
    Nat.sub_add_cancel (show 1 ≤ 2 * q by omega), Nat.cast_mul, Nat.cast_ofNat] at hmap
  exact lattice_antitone F hb hmap

/-- Evaluate the actual twisted character by the exact quadratic norm.
The crossed term is converted by the lower norm phase on its whole ideal;
the weighted error is killed at the additive conductor, including zero. -/
private theorem adjusted_upper
    {q s b : ℕ} (hq : 1 ≤ q) (hs : 0 < s)
    (ht : PrimeCyclicExtension.IsLowerBreak F L (2 * q - 1))
    (hres : residueDegree F L = 1)
    (htrace : (b : ℤ) ≤ ((s : ℤ) + 2 * q) / 2) (hnorm : b ≤ s)
    (Ψ : LocalAddCharData F) (χ : ContinuousQuasiChar L) (lambda : ContinuousQuasiChar F)
    (β : Fˣ) (A err : F) (c Q : L) {k l j : ℤ}
    (hβ : ord F (β : F) = (k : WithTop ℤ))
    (hQ : Q ∈ lattice L l) (herr : err ∈ lattice F j)
    (hdepth : 2 * k + q ≤ l + s) (herror : -Ψ.conductor + k ≤ j + s)
    (hweight : norm F L Q = (β : F) * A + err)
    (hphase : ∀ v ∈ lattice L (q : ℤ),
      tracePullbackAddChar F L Ψ.character (algebraMap F L (β : F) * v) =
        Ψ.character ((β : F) * norm F L v))
    (hcore : ∀ B : unitFiltration L s, χ (B : Lˣ) =
      tracePullbackAddChar F L Ψ.character (c * (1 - ((B : Lˣ) : L))))
    (hbase : ∀ v ∈ lattice F (b : ℤ), ∀ B : Fˣ, (B : F) = 1 - v →
      lambda B = Ψ.character (A * v))
    (v : L) (hv : v ∈ lattice L (s : ℤ)) (B : Lˣ) (hB : (B : L) = 1 - v) :
    (χ * normQuasiChar F L lambda) B =
      tracePullbackAddChar F L Ψ.character ((c + algebraMap F L A - Q) * v) := by
  have hvnorm : norm F L v ∈ lattice F (s : ℤ) := by
    simpa only [mem_lattice, ord_norm, hres, one_nsmul] using hv
  have hbmap : ord L (algebraMap F L (β : F)) = ((2 * k : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, ramification_two F L hres, hβ, ← WithTop.coe_nsmul]
    simp [two_mul]
  have hdiv : Q * v / algebraMap F L (β : F) ∈ lattice L (q : ℤ) := by
    apply (div_mem_lattice_iff L _ _ _ _ hbmap).mpr
    exact lattice_antitone L hdepth (mul_mem_lattice L hQ hv)
  have hp := hphase _ hdiv
  have hcancel : algebraMap F L (β : F) * (Q * v / algebraMap F L (β : F)) =
      Q * v := by field_simp
  rw [hcancel] at hp
  have hn : norm F L (Q * v / algebraMap F L (β : F)) =
      ((β : F) * A + err) * norm F L v / (β : F) ^ 2 := by
    simp only [div_eq_mul_inv, map_mul, Algebra.norm_inv,
      LanglandsFirstMainLemma.norm_algebraMap,
      Algebra.IsQuadraticExtension.finrank_eq_two F L, hweight]
  rw [hn] at hp
  have hQphase : tracePullbackAddChar F L Ψ.character (Q * v) =
      Ψ.character (A * norm F L v) := by
    apply hp.trans
    apply additive_eq_of_sub_mem F Ψ
    rw [show (β : F) * (((β : F) * A + err) * norm F L v / (β : F) ^ 2) -
        A * norm F L v = err * norm F L v / (β : F) by field_simp; ring]
    apply (div_mem_lattice_iff F _ _ _ _ hβ).mpr
    exact lattice_antitone F (by omega) (mul_mem_lattice F herr hvnorm)
  have htmem := trace_mem_of_depth F L hq ht hres htrace hv
  have hnmem := lattice_antitone F (show (b : ℤ) ≤ s by exact_mod_cast hnorm) hvnorm
  have hNB : ((normUnits F L B : Fˣ) : F) =
      1 - (trace F L v - norm F L v) := by
    rw [coe_normUnits, hB]
    have hexact := wildQuadratic_norm_sub F L
      (Algebra.IsQuadraticExtension.finrank_eq_two F L) 1 v
    simpa only [Units.val_one, map_one, one_pow, one_mul, sub_sub_eq_add_sub,
      sub_add_eq_add_sub] using hexact
  have hbaseValue := hbase _ (sub_mem_lattice F htmem hnmem) (normUnits F L B) hNB
  have hχ := hcore ⟨B, oneSub_mem_filtration L hs hv B hB⟩
  simp only [hB, sub_sub_cancel] at hχ
  change χ B * lambda (normUnits F L B) = _
  rw [hχ, hbaseValue, show (c + algebraMap F L A - Q) * v =
    c * v + (algebraMap F L A * v - Q * v) by ring,
    ContinuousAddChar.map_add_eq_mul]
  congr 1
  rw [phase_sub, hQphase,
    tracePullbackAddChar_apply]
  have htA : trace F L (algebraMap F L A * v) = A * trace F L v := by
    simpa [Algebra.smul_def] using (trace F L).map_smul A v
  rw [htA, mul_sub, phase_sub]

end Edge

section ActualFields

variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  (L₁ L₂ L₃ : IntermediateField F K)

attribute [local instance] Basic.intermediateFieldValuativeRel
  Basic.intermediateFieldTopology Basic.intermediateField_localField
  Basic.intermediateField_lowerValuativeExtension Basic.intermediateField_upperValuativeExtension

/-- Full stationary identities at the actual norm and trace norm of `C`.
The units `B` make the nonzero multiplicative-character arguments explicit;
`v` ranges over the entire indicated ideal, including zero. -/
structure MinimalOriginSide (L : IntermediateField F K)
    (q s : ℕ) (w : ℤ) (ω : NormCharacter F L) (Ψ : ContinuousAddChar F)
    (θ : ContinuousQuasiChar L) (C : K) : Prop where
  trace_order : ord L (trace L K C) = (w : WithTop ℤ)
  trace_ne_zero : trace L K C ≠ 0
  upper_formula : ∀ v ∈ lattice L (s : ℤ), ∀ B : Lˣ, (B : L) = 1 - v →
    θ B = tracePullbackAddChar F L Ψ (norm L K C * v)
  lower_formula : ∀ v ∈ lattice F (q : ℤ), ∀ B : Fˣ, (B : F) = 1 - v →
    ω.1 B = Ψ (norm F L (trace L K C) * v)

variable [Algebra.IsQuadraticExtension F L₁] [Algebra.IsQuadraticExtension L₁ K]
  [Algebra.IsQuadraticExtension F L₂] [Algebra.IsQuadraticExtension L₂ K]
  [Algebra.IsQuadraticExtension F L₃] [Algebra.IsQuadraticExtension L₃ K]
  [PrimeCyclicExtension F L₁] [PrimeCyclicExtension L₁ K]
  [PrimeCyclicExtension F L₂] [PrimeCyclicExtension L₂ K]
  [PrimeCyclicExtension F L₃] [PrimeCyclicExtension L₃ K]
  {a r : ℕ} {x : L₁} {y : L₂} {z : L₃} {f g d : F}
  (O : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)

set_option quotPrecheck false
local notation "β₁" => normUnits F L₁
  (Units.mk0 (trace L₁ K O.Y) O.upperTraces_ne_zero.1)
local notation "β₂" => normUnits F L₂
  (Units.mk0 (trace L₂ K O.Y) O.upperTraces_ne_zero.2.1)
local notation "β₃" => normUnits F L₃
  (Units.mk0 (trace L₃ K O.Y) O.upperTraces_ne_zero.2.2)
set_option quotPrecheck true

omit [Algebra.IsQuadraticExtension F L₁] [Algebra.IsQuadraticExtension L₁ K]
  [Algebra.IsQuadraticExtension F L₂] [Algebra.IsQuadraticExtension L₂ K]
  [PrimeCyclicExtension F L₁] [PrimeCyclicExtension L₁ K]
  [PrimeCyclicExtension F L₂] [PrimeCyclicExtension L₂ K]
  [PrimeCyclicExtension F L₃] in
/-- Exact identities for the third side, where the adjustment belongs to
that same intermediate field. In particular its affine terms are retained. -/
private theorem third_adjustment (X : L₃) :
    norm L₃ K (O.adjustedOrigin X) = norm L₃ K O.Y + X ^ 2 +
      algebraMap F L₃ O.k₀ * X ∧
    trace L₃ K (O.adjustedOrigin X) =
      -algebraMap F L₃ O.k₀ - 2 * X ∧
    norm F L₃ (trace L₃ K (O.adjustedOrigin X)) - (β₃ : F) =
      2 * O.k₀ * O.adjustmentTrace X + 4 * O.adjustmentNorm X := by
  classical
  obtain ⟨σ, hσ⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [quadratic_card L₃ K]; omega) (1 : Gal(K/L₃))
  have ht : trace L₃ K (O.adjustedOrigin X) =
      -algebraMap F L₃ O.k₀ - 2 * X := by
    rw [DyadicNonmaximalOriginData.adjustedOrigin, map_sub, O.upperTrace₃]
    change _ - trace L₃ K (algebraMap L₃ K X) = _
    rw [LanglandsFirstMainLemma.trace_algebraMap,
      Algebra.IsQuadraticExtension.finrank_eq_two L₃ K, two_smul]
    ring
  have hn : norm L₃ K (O.adjustedOrigin X) = norm L₃ K O.Y + X ^ 2 +
      algebraMap F L₃ O.k₀ * X := by
    have hσX : σ (X : K) = (X : K) := σ.commutes X
    apply (algebraMap L₃ K).injective
    rw [DyadicNonmaximalOriginData.adjustedOrigin,
      norm_eq_self_mul_nontrivial σ hσ (quadratic_card L₃ K)]
    simp only [map_sub, hσX, map_add, map_pow, map_mul]
    rw [norm_eq_self_mul_nontrivial σ hσ (quadratic_card L₃ K)]
    have htrace := trace_eq_self_add_nontrivial σ hσ (quadratic_card L₃ K) O.Y
    rw [O.upperTrace₃, map_neg] at htrace
    change (O.Y - (X : K)) * (σ O.Y - (X : K)) = O.Y * σ O.Y +
      (X : K) ^ 2 + algebraMap L₃ K (algebraMap F L₃ O.k₀) * (X : K)
    linear_combination (X : K) * htrace
  refine ⟨hn, ht, ?_⟩
  have hk0 : O.k₀ ≠ 0 := (ord_ne_top_iff F).mp (by rw [O.k₀_order]; simp)
  have hn' := wildQuadratic_norm_sub F L₃
    (Algebra.IsQuadraticExtension.finrank_eq_two F L₃)
    (Units.mk0 (-O.k₀) (neg_ne_zero.mpr hk0)) (2 * X)
  have ht2 : trace F L₃ (2 * X) = 2 * trace F L₃ X := by
    rw [two_mul, map_add, two_mul]
  have hn2 : norm F L₃ (2 * X) = 4 * norm F L₃ X := by
    rw [show (2 : L₃) = algebraMap F L₃ (2 : F) from (map_ofNat _ 2).symm, map_mul,
      LanglandsFirstMainLemma.norm_algebraMap,
      Algebra.IsQuadraticExtension.finrank_eq_two F L₃]
    norm_num
  change norm F L₃ (trace L₃ K (O.adjustedOrigin X)) -
    norm F L₃ (trace L₃ K O.Y) = _
  rw [ht, O.lowerNormTrace₃]
  simp only [Units.val_mk0, map_neg, ht2, hn2] at hn'
  rw [hn']
  dsimp [DyadicNonmaximalOriginData.adjustmentTrace, DyadicNonmaximalOriginData.adjustmentNorm]
  ring

omit [PrimeCyclicExtension L₃ K] in
/-- The two compared sides, uniformly for every adjustment of depth
`1-a`. This includes the zero adjustment and the paper's negative `h`. -/
private theorem adjusted_two_sides
    (e : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (ht₁ : PrimeCyclicExtension.IsLowerBreak F L₁ (2 * a - 1))
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F L₂ (2 * r - 1))
    (hres₁ : residueDegree F L₁ = 1) (hres₂ : residueDegree F L₂ = 1)
    (hres₃ : residueDegree F L₃ = 1) (hres₃K : residueDegree L₃ K = 1)
    (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂) (ω₃ : NormCharacter F L₃)
    (ψ : LocalAddCharData F) (α : Fˣ)
    (χ₁ : ContinuousQuasiChar L₁) (χ₂ : ContinuousQuasiChar L₂)
    (χ₃ : ContinuousQuasiChar L₃)
    (H : NormalizationFormulas F L₁ L₂ L₃ a r ω₁ ω₂ ω₃ ψ β₁ β₂ β₃
      (norm L₁ K O.Y) (norm L₂ K O.Y) (norm L₃ K O.Y) χ₁ χ₂ χ₃ α)
    (lambda : ContinuousQuasiChar F) (X : L₃) (hX : X ∈ lattice L₃ (1 - (a : ℤ)))
    (hbase : ∀ v ∈ lattice F ((a + r : ℕ) : ℤ), ∀ B : Fˣ, (B : F) = 1 - v →
      lambda B = (scaleAddCharData F ψ α).character (O.adjustmentNorm X * v)) :
    ord K (O.adjustedOrigin X) = ((1 - 2 * (a : ℤ) : ℤ) : WithTop ℤ) ∧
    MinimalOriginSide L₁ a (2 * r) (2 * ((r : ℤ) - a)) ω₁
      (scaleAddCharData F ψ α).character (χ₁ * normQuasiChar F L₁ lambda)
      (O.adjustedOrigin X) ∧
    MinimalOriginSide L₂ r (a + r) 0 ω₂
      (scaleAddCharData F ψ α).character (χ₂ * normQuasiChar F L₂ lambda)
      (O.adjustedOrigin X) := by
  classical
  obtain ⟨g₁, hg₁⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [quadratic_card L₁ K]; omega) (1 : Gal(K/L₁))
  obtain ⟨g₂, hg₂⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [quadratic_card L₂ K]; omega) (1 : Gal(K/L₂))
  obtain ⟨q₃, hq₃⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [quadratic_card F L₃]; omega) (1 : Gal(L₃/F))
  obtain ⟨HI, HB⟩ := commonError O e ha har hre htwo hres₁ hres₂ hres₃
    g₁ hg₁ g₂ hg₂ q₃ hq₃ X
  have HX : X ∈ lattice L₃ (-((a : ℤ) - 1)) := by simpa only [neg_sub] using hX
  have hb := HB ((a : ℤ) - 1) HX
  have hp : O.adjustmentTrace X ∈ lattice F ((r : ℤ) - (a : ℤ) / 2) := by
    rw [mem_lattice]
    simpa only [sub_add_cancel] using hb.trace_bound
  have he : O.commonErrorTerm g₁ X ∈ lattice F (2 * (r : ℤ) - 2 * a + 1) := by
    rw [mem_lattice]
    convert hb.error_bound using 1
    congr 1
    ring
  have hQ₁ : O.firstCrossedTrace g₁ X ∈
      lattice L₁ (2 * ((r : ℤ) - a) + 1 - a) := by
    rw [mem_lattice]
    convert hb.first_crossed_bound using 1
    congr 1
    ring
  have hQ₂ : O.secondCrossedTrace g₂ X ∈ lattice L₂ (1 - (a : ℤ)) := by
    simpa only [mem_lattice, neg_sub] using hb.second_crossed_bound
  have htwoLat : (2 : F) ∈ lattice F (e : ℤ) := by rw [mem_lattice, htwo]; norm_cast
  have hk : O.k₀ ∈ lattice F 0 := by rw [mem_lattice, O.k₀_order]; rfl
  have hΔ : O.traceNormIncrement X ∈ lattice F (2 * (r : ℤ) - a) := by
    dsimp [DyadicNonmaximalOriginData.traceNormIncrement]
    rw [pow_two]
    apply add_mem_lattice F
    · exact lattice_antitone F (by omega) (mul_mem_lattice F hp hp)
    · exact lattice_antitone F (by omega)
        (mul_mem_lattice F (mul_mem_lattice F htwoLat hk) hp)
  have hC : ord K (O.adjustedOrigin X) =
      ((1 - 2 * (a : ℤ) : ℤ) : WithTop ℤ) := by
    rw [DyadicNonmaximalOriginData.adjustedOrigin, sub_order_of_deeper K, O.Y_order]
    rw [O.Y_order]
    have hm := quadratic_map_mem_lattice L₃ K (ramification_two L₃ K hres₃K) hX
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) ((mem_lattice K).mp hm)
  have htrace₁ : ord L₁ (trace L₁ K (O.adjustedOrigin X)) =
      ((2 * ((r : ℤ) - a) : ℤ) : WithTop ℤ) := by
    rw [HI.first_trace, sub_order_of_deeper L₁, O.upperTrace₁_order]
    rw [O.upperTrace₁_order]
    have hm := quadratic_map_mem_lattice F L₁ (ramification_two F L₁ hres₁) hp
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) ((mem_lattice L₁).mp hm)
  have htrace₂ : ord L₂ (trace L₂ K (O.adjustedOrigin X)) = (0 : WithTop ℤ) := by
    rw [HI.second_trace, sub_order_of_deeper L₂, O.upperTrace₂_order]
    rw [O.upperTrace₂_order]
    have hm := quadratic_map_mem_lattice F L₂ (ramification_two F L₂ hres₂) hp
    exact lt_of_lt_of_le (show (0 : WithTop ℤ) <
      ((2 * ((r : ℤ) - (a : ℤ) / 2) : ℤ) : WithTop ℤ) by exact_mod_cast (show
        0 < 2 * ((r : ℤ) - (a : ℤ) / 2) by omega)) ((mem_lattice L₂).mp hm)
  refine ⟨hC, ⟨htrace₁, ?_, ?_, ?_⟩, ⟨htrace₂, ?_, ?_, ?_⟩⟩
  · exact (ord_ne_top_iff L₁).mp (by rw [htrace₁]; exact WithTop.coe_ne_top)
  · intro v hv B hB
    rw [HI.first_norm]
    exact adjusted_upper F L₁ ha (by omega) ht₁ hres₁ (by push_cast; omega) (by omega)
      (scaleAddCharData F ψ α) χ₁ lambda β₁ (O.adjustmentNorm X)
      (O.commonErrorTerm g₁ X) (norm L₁ K O.Y) (O.firstCrossedTrace g₁ X)
      O.lowerNormTrace₁_order hQ₁ he (by push_cast; omega)
      (by rw [H.1.base_conductor]; push_cast; omega) HI.first_weighted_norm
      H.1.first_phase H.2.1 hbase v hv B hB
  · intro v hv B hB
    refine (H.1.first_formula v hv B hB).trans ?_
    change (scaleAddCharData F ψ α).character
      (norm F L₁ (trace L₁ K O.Y) * v) = _
    apply additive_eq_of_sub_mem F (scaleAddCharData F ψ α)
    rw [HI.first_trace_norm, show norm F L₁ (trace L₁ K O.Y) * v -
      (norm F L₁ (trace L₁ K O.Y) + O.traceNormIncrement X) * v =
      -(O.traceNormIncrement X * v) by ring, H.1.base_conductor]
    exact neg_mem_lattice F (lattice_antitone F (by omega) (mul_mem_lattice F hΔ hv))
  · exact (ord_ne_top_iff L₂).mp (by rw [htrace₂]; simp)
  · intro v hv B hB
    rw [HI.second_norm]
    exact adjusted_upper F L₂ (ha.trans har) (by omega) ht₂ hres₂
      (by push_cast; omega) (by omega) (scaleAddCharData F ψ α) χ₂ lambda β₂
      (O.adjustmentNorm X) (O.commonErrorTerm g₁ X) (norm L₂ K O.Y)
      (O.secondCrossedTrace g₂ X) (k := 0) O.lowerNormTrace₂_order hQ₂ he
      (by push_cast; omega) (by rw [H.1.base_conductor]; push_cast; omega)
      HI.second_weighted_norm H.1.second_phase H.2.2.1 hbase v hv B hB
  · intro v hv B hB
    refine (H.1.second_formula v hv B hB).trans ?_
    change (scaleAddCharData F ψ α).character
      (norm F L₂ (trace L₂ K O.Y) * v) = _
    apply additive_eq_of_sub_mem F (scaleAddCharData F ψ α)
    rw [HI.second_trace_norm, show norm F L₂ (trace L₂ K O.Y) * v -
      (norm F L₂ (trace L₂ K O.Y) + O.traceNormIncrement X) * v =
      -(O.traceNormIncrement X * v) by ring, H.1.base_conductor]
    exact neg_mem_lattice F (lattice_antitone F (by omega) (mul_mem_lattice F hΔ hv))

omit [Algebra.IsQuadraticExtension L₁ K] [Algebra.IsQuadraticExtension L₂ K]
  [PrimeCyclicExtension F L₁] [PrimeCyclicExtension L₁ K]
  [PrimeCyclicExtension F L₂] [PrimeCyclicExtension L₂ K] in
/-- The same origin also works on the third side when all breaks agree. -/
private theorem adjusted_third_side
    (e : ℕ) (ha : 1 ≤ a) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (ht₃ : PrimeCyclicExtension.IsLowerBreak F L₃ (2 * r - 1))
    (hres₃ : residueDegree F L₃ = 1)
    (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂) (ω₃ : NormCharacter F L₃)
    (ψ : LocalAddCharData F) (α : Fˣ)
    (χ₁ : ContinuousQuasiChar L₁) (χ₂ : ContinuousQuasiChar L₂)
    (χ₃ : ContinuousQuasiChar L₃)
    (H : NormalizationFormulas F L₁ L₂ L₃ a r ω₁ ω₂ ω₃ ψ β₁ β₂ β₃
      (norm L₁ K O.Y) (norm L₂ K O.Y) (norm L₃ K O.Y) χ₁ χ₂ χ₃ α)
    (lambda : ContinuousQuasiChar F) (X : L₃) (hX : X ∈ lattice L₃ (1 - (a : ℤ)))
    (hbase : ∀ v ∈ lattice F ((a + r : ℕ) : ℤ), ∀ B : Fˣ, (B : F) = 1 - v →
      lambda B = (scaleAddCharData F ψ α).character (O.adjustmentNorm X * v))
    (hequal : a = r) :
    MinimalOriginSide L₃ r (a + r) 0 ω₃
      (scaleAddCharData F ψ α).character (χ₃ * normQuasiChar F L₃ lambda)
      (O.adjustedOrigin X) := by
  classical
  obtain ⟨hnC, htC, hnS⟩ := third_adjustment L₁ L₂ L₃ O X
  have hXr : X ∈ lattice L₃ (1 - (r : ℤ)) := by simpa only [hequal] using hX
  have hram := ramification_two F L₃ hres₃
  have hp : O.adjustmentTrace X ∈ lattice F ((r : ℤ) - (r : ℤ) / 2) :=
    trace_mem_of_depth F L₃ (by omega) ht₃ hres₃ (by omega) hXr
  have hA : O.adjustmentNorm X ∈ lattice F (1 - (r : ℤ)) := by
    simpa only [DyadicNonmaximalOriginData.adjustmentNorm, mem_lattice,
      ord_norm, hres₃, one_nsmul] using hXr
  have hk : O.k₀ ∈ lattice F 0 := by rw [mem_lattice, O.k₀_order]; rfl
  have hkL : algebraMap F L₃ O.k₀ ∈ lattice L₃ 0 := by
    simpa only [mul_zero] using quadratic_map_mem_lattice F L₃ hram hk
  have htwoLat : (2 : F) ∈ lattice F (e : ℤ) := by rw [mem_lattice, htwo]; norm_cast
  have htwoL : (2 : L₃) ∈ lattice L₃ (2 * (e : ℤ)) := by
    simpa only [map_ofNat] using quadratic_map_mem_lattice F L₃ hram htwoLat
  have htrace : ord L₃ (trace L₃ K (O.adjustedOrigin X)) = (0 : WithTop ℤ) := by
    rw [htC, sub_order_of_deeper L₃, ord_neg, ord_algebraMap, O.k₀_order, nsmul_zero]
    have hfirst : ord L₃ (-algebraMap F L₃ O.k₀) = 0 := by
      rw [ord_neg, ord_algebraMap, O.k₀_order, nsmul_zero]
    rw [hfirst]
    have hm := mul_mem_lattice L₃ htwoL hXr
    exact lt_of_lt_of_le (show (0 : WithTop ℤ) <
      ((2 * (e : ℤ) + (1 - (r : ℤ)) : ℤ) : WithTop ℤ) by
        exact_mod_cast (show 0 < 2 * (e : ℤ) + (1 - (r : ℤ)) by omega))
      ((mem_lattice L₃).mp hm)
  have hQ : algebraMap F L₃ O.k₀ * X ∈ lattice L₃ (1 - (r : ℤ)) := by
    simpa only [zero_add] using mul_mem_lattice L₃ hkL hXr
  have hweight : norm F L₃ (algebraMap F L₃ O.k₀ * X) =
      (β₃ : F) * O.adjustmentNorm X + 0 := by
    change _ = norm F L₃ (trace L₃ K O.Y) * O.adjustmentNorm X + 0
    rw [map_mul, LanglandsFirstMainLemma.norm_algebraMap,
      Algebra.IsQuadraticExtension.finrank_eq_two F L₃, O.lowerNormTrace₃, add_zero]
    rfl
  have hgap : norm L₃ K (O.adjustedOrigin X) -
      (norm L₃ K O.Y + algebraMap F L₃ (O.adjustmentNorm X) -
        algebraMap F L₃ O.k₀ * X) ∈ lattice L₃ 0 := by
    obtain ⟨σ, hσ⟩ := Fintype.exists_ne_of_one_lt_card
      (by rw [quadratic_card F L₃]; omega) (1 : Gal(L₃/F))
    have hpoly : X ^ 2 = algebraMap F L₃ (O.adjustmentTrace X) * X -
        algebraMap F L₃ (O.adjustmentNorm X) := by
      rw [DyadicNonmaximalOriginData.adjustmentTrace,
        DyadicNonmaximalOriginData.adjustmentNorm,
        trace_eq_self_add_nontrivial σ hσ (quadratic_card F L₃),
        norm_eq_self_mul_nontrivial σ hσ (quadratic_card F L₃)]
      ring
    rw [hnC, hpoly, show norm L₃ K O.Y +
      (algebraMap F L₃ (O.adjustmentTrace X) * X - algebraMap F L₃ (O.adjustmentNorm X)) +
      algebraMap F L₃ O.k₀ * X -
      (norm L₃ K O.Y + algebraMap F L₃ (O.adjustmentNorm X) -
        algebraMap F L₃ O.k₀ * X) =
      algebraMap F L₃ (O.adjustmentTrace X) * X -
        algebraMap F L₃ (2 * O.adjustmentNorm X) +
        2 * algebraMap F L₃ O.k₀ * X by simp only [map_mul, map_ofNat]; ring]
    apply add_mem_lattice L₃
    · apply sub_mem_lattice L₃
      · exact lattice_antitone L₃ (by omega)
          (mul_mem_lattice L₃ (quadratic_map_mem_lattice F L₃ hram hp) hXr)
      · exact lattice_antitone L₃ (by omega)
          (quadratic_map_mem_lattice F L₃ hram (mul_mem_lattice F htwoLat hA))
    · exact lattice_antitone L₃ (by omega)
        (mul_mem_lattice L₃ (mul_mem_lattice L₃ htwoL hkL) hX)
  refine ⟨htrace, (ord_ne_top_iff L₃).mp (by rw [htrace]; simp), ?_, ?_⟩
  · intro v hv B hB
    have hu := adjusted_upper F L₃ (by omega) (by omega) ht₃ hres₃
      (by push_cast; omega) (by omega) (scaleAddCharData F ψ α) χ₃ lambda β₃
      (O.adjustmentNorm X) 0 (norm L₃ K O.Y) (algebraMap F L₃ O.k₀ * X)
      (k := 0) (j := 0) O.lowerNormTrace₃_order hQ (by simp)
      (by push_cast; omega) (by rw [H.1.base_conductor]; push_cast; omega)
      hweight H.1.third_phase H.2.2.2 hbase v hv B hB
    refine hu.trans ?_
    let ΨL : LocalAddCharData L₃ := ⟨_, -2 * (r : ℤ), H.1.third_conductor⟩
    apply additive_eq_of_sub_mem L₃ ΨL
    change _ ∈ lattice L₃ (-(-2 * (r : ℤ)))
    rw [show (norm L₃ K O.Y + algebraMap F L₃ (O.adjustmentNorm X) -
      algebraMap F L₃ O.k₀ * X) * v - norm L₃ K (O.adjustedOrigin X) * v =
      -((norm L₃ K (O.adjustedOrigin X) - (norm L₃ K O.Y +
        algebraMap F L₃ (O.adjustmentNorm X) - algebraMap F L₃ O.k₀ * X)) * v) by ring]
    exact neg_mem_lattice L₃ (lattice_antitone L₃ (by push_cast; omega)
      (mul_mem_lattice L₃ hgap hv))
  · intro v hv B hB
    refine (H.1.third_formula v hv B hB).trans ?_
    apply additive_eq_of_sub_mem F (scaleAddCharData F ψ α)
    rw [show (β₃ : F) * v - norm F L₃ (trace L₃ K (O.adjustedOrigin X)) * v =
      -(norm F L₃ (trace L₃ K (O.adjustedOrigin X)) - (β₃ : F)) * v by ring,
      hnS, H.1.base_conductor]
    have hinc : 2 * O.k₀ * O.adjustmentTrace X + 4 * O.adjustmentNorm X ∈
        lattice F (r : ℤ) := by
      apply add_mem_lattice F
      · exact lattice_antitone F (by omega)
          (mul_mem_lattice F (mul_mem_lattice F htwoLat hk) hp)
      · rw [show (4 : F) = 2 * 2 by norm_num]
        exact lattice_antitone F (by omega)
          (mul_mem_lattice F (mul_mem_lattice F htwoLat htwoLat) hA)
    exact lattice_antitone F (by omega) (mul_mem_lattice F (neg_mem_lattice F hinc) hv)

omit [Algebra.IsQuadraticExtension L₁ K] [Algebra.IsQuadraticExtension L₂ K]
  [Algebra.IsQuadraticExtension L₃ K] [PrimeCyclicExtension L₁ K]
  [PrimeCyclicExtension L₂ K] [PrimeCyclicExtension L₃ K] in
/-- Construct the adjustment from the actual base character. The shallow
case uses zero; otherwise FML duality and the proved normalization freedom
supply an exact third-field norm without changing the base character. -/
private theorem choose_minimal_adjustment
    (ha : 1 ≤ a) (har : a ≤ r)
    (ht₁ : PrimeCyclicExtension.IsLowerBreak F L₁ (2 * a - 1))
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F L₂ (2 * r - 1))
    (ht₃ : PrimeCyclicExtension.IsLowerBreak F L₃ (2 * r - 1))
    (hres₁ : residueDegree F L₁ = 1) (hres₂ : residueDegree F L₂ = 1)
    (hres₃ : residueDegree F L₃ = 1)
    (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂) (ω₃ : NormCharacter F L₃)
    (hω₃ : ω₃ ≠ 1) (ψ : LocalAddCharData F) (α : Fˣ)
    (χ₁ : ContinuousQuasiChar L₁) (χ₂ : ContinuousQuasiChar L₂)
    (χ₃ : ContinuousQuasiChar L₃)
    (H : NormalizationFormulas F L₁ L₂ L₃ a r ω₁ ω₂ ω₃ ψ β₁ β₂ β₃
      (norm L₁ K O.Y) (norm L₂ K O.Y) (norm L₃ K O.Y) χ₁ χ₂ χ₃ α)
    (lambda : LocalQuasiCharData F) (hn : lambda.conductor ≤ 2 * r + a - 1) :
    ∃ (u : unitFiltration F (2 * r - 1)) (X : L₃),
      ord F ((α * (u : Fˣ) : Fˣ) : F) = ord F (α : F) ∧
      NormalizationFormulas F L₁ L₂ L₃ a r ω₁ ω₂ ω₃ ψ β₁ β₂ β₃
        (norm L₁ K O.Y) (norm L₂ K O.Y) (norm L₃ K O.Y) χ₁ χ₂ χ₃ (α * (u : Fˣ)) ∧
      X ∈ lattice L₃ (1 - (a : ℤ)) ∧
      ∀ v ∈ lattice F ((a + r : ℕ) : ℤ), ∀ B : Fˣ, (B : F) = 1 - v →
        lambda.character B = (scaleAddCharData F ψ (α * (u : Fˣ))).character
          (O.adjustmentNorm X * v) := by
  by_cases hsmall : lambda.conductor ≤ a + r
  · refine ⟨1, 0, by simp, ?_, by simp, ?_⟩
    · simpa only [OneMemClass.coe_one, mul_one] using H
    · intro v hv B hB
      rw [lambda.isConductor.trivial B (unitFiltration_antitone F hsmall
        (oneSub_mem_filtration F (by omega) hv B hB))]
      simp [DyadicNonmaximalOriginData.adjustmentNorm]
  · have hdepth : IsLamprechtStationaryDepth lambda.conductor (a + r) :=
      ⟨by omega, by omega, by omega⟩
    obtain ⟨Astar, hAstar, hbase⟩ := base_covector F lambda (scaleAddCharData F ψ α) hdepth
    obtain ⟨_, hchoice⟩ := normalization L₁ L₂ L₃ a r ha har ht₁ ht₂ ht₃
      hres₁ hres₂ hres₃ x y z f g d O ω₁ ω₂ ω₃ hω₃ ψ α χ₁ χ₂ χ₃ H
    obtain ⟨u, X, hnorm, HU, hu, hXord, _, hphase⟩ := hchoice Astar
    have hXmem : (X : L₃) ∈ lattice L₃ (1 - (a : ℤ)) := by
      rw [mem_lattice, hXord, hAstar, H.1.base_conductor]
      exact WithTop.coe_le_coe.mpr (by omega)
    refine ⟨u, X, hu, HU, hXmem, ?_⟩
    intro v hv B hB
    refine (hbase v hv B hB).trans ?_
    rw [hnorm] at hphase
    exact (hphase v).symm

/-- **Paper Lemma 13.10 (`D:NM:minimal-origin`).**

For the already realized actual family `θᵢ = χᵢ (lambda ∘ nᵢ)` in the
minimal conductor range, construct one adjusted origin `C = Y - X`.
`O` has the proved constructors in `Origin`; `H` is exactly the full lower
and core data provided by `lowerCharacters` and `twist`. No stationary
property of `C`, exact norm choice, or phase cancellation is an input.

The allowed normalization unit preserves those same fixed characters and
the order of the normalizing coefficient. Both stationary formulas hold
on their entire ideals. The traces are nonzero with their original orders.
When `a = r`, this single origin supplies all three indices.
-/
theorem minimalOrigin
    (e : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (ht₁ : PrimeCyclicExtension.IsLowerBreak F L₁ (2 * a - 1))
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F L₂ (2 * r - 1))
    (ht₃ : PrimeCyclicExtension.IsLowerBreak F L₃ (2 * r - 1))
    (hres₁ : residueDegree F L₁ = 1) (hres₂ : residueDegree F L₂ = 1)
    (hres₃ : residueDegree F L₃ = 1) (hres₃K : residueDegree L₃ K = 1)
    (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂) (ω₃ : NormCharacter F L₃)
    (hω₃ : ω₃ ≠ 1) (ψ : LocalAddCharData F) (α : Fˣ)
    (χ₁ : ContinuousQuasiChar L₁) (χ₂ : ContinuousQuasiChar L₂)
    (χ₃ : ContinuousQuasiChar L₃)
    (H : NormalizationFormulas F L₁ L₂ L₃ a r ω₁ ω₂ ω₃ ψ β₁ β₂ β₃
      (norm L₁ K O.Y) (norm L₂ K O.Y) (norm L₃ K O.Y) χ₁ χ₂ χ₃ α)
    (lambda : LocalQuasiCharData F) (hn : lambda.conductor ≤ 2 * r + a - 1)
    (θ₁ : ContinuousQuasiChar L₁) (θ₂ : ContinuousQuasiChar L₂)
    (θ₃ : ContinuousQuasiChar L₃)
    (hθ₁ : θ₁ = χ₁ * normQuasiChar F L₁ lambda.character)
    (hθ₂ : θ₂ = χ₂ * normQuasiChar F L₂ lambda.character)
    (hθ₃ : θ₃ = χ₃ * normQuasiChar F L₃ lambda.character) :
    ∃ (u : unitFiltration F (2 * r - 1)) (X : L₃),
      ord F ((α * (u : Fˣ) : Fˣ) : F) = ord F (α : F) ∧
      NormalizationFormulas F L₁ L₂ L₃ a r ω₁ ω₂ ω₃ ψ β₁ β₂ β₃
        (norm L₁ K O.Y) (norm L₂ K O.Y) (norm L₃ K O.Y) χ₁ χ₂ χ₃ (α * (u : Fˣ)) ∧
      X ∈ lattice L₃ (1 - (a : ℤ)) ∧
      ord K (O.adjustedOrigin X) = ((1 - 2 * (a : ℤ) : ℤ) : WithTop ℤ) ∧
      O.adjustedOrigin X ≠ 0 ∧
      MinimalOriginSide L₁ a (2 * r) (2 * ((r : ℤ) - a)) ω₁
        (scaleAddCharData F ψ (α * (u : Fˣ))).character θ₁ (O.adjustedOrigin X) ∧
      MinimalOriginSide L₂ r (a + r) 0 ω₂
        (scaleAddCharData F ψ (α * (u : Fˣ))).character θ₂ (O.adjustedOrigin X) ∧
      (a = r → MinimalOriginSide L₃ r (a + r) 0 ω₃
        (scaleAddCharData F ψ (α * (u : Fˣ))).character θ₃ (O.adjustedOrigin X)) := by
  obtain ⟨u, X, hu, HU, hX, hbase⟩ := choose_minimal_adjustment L₁ L₂ L₃ O
    ha har ht₁ ht₂ ht₃ hres₁ hres₂ hres₃ ω₁ ω₂ ω₃ hω₃ ψ α χ₁ χ₂ χ₃ H lambda hn
  subst θ₁ θ₂ θ₃
  obtain ⟨hC, H₁, H₂⟩ := adjusted_two_sides L₁ L₂ L₃ O e ha har hre htwo ht₁ ht₂
    hres₁ hres₂ hres₃ hres₃K ω₁ ω₂ ω₃ ψ (α * (u : Fˣ)) χ₁ χ₂ χ₃ HU
    lambda.character X hX hbase
  refine ⟨u, X, hu, HU, hX, hC,
    (ord_ne_top_iff K).mp (by rw [hC]; exact WithTop.coe_ne_top), H₁, H₂, ?_⟩
  exact adjusted_third_side L₁ L₂ L₃ O e ha hre htwo ht₃ hres₃
    ω₁ ω₂ ω₃ ψ (α * (u : Fˣ)) χ₁ χ₂ χ₃ HU lambda.character X hX hbase

end ActualFields

end

end LanglandsSecondMainLemma.Dyadic.Nonmaximal
