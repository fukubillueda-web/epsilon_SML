import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.Twist
import LanglandsSecondMainLemma.Stationary.NormalizationFreedom

/-!
# Dyadic / Nonmaximal / Normalization

Paper Lemma 13.8 (`D:NM:freedom`), with the full lower data
`D:NM:lowerformula`, `D:NM:normphase`, and the core charts `D:NM:Rcharts`.
The allowed change has depth `2r-1`. All ideal exponents in the error
estimates are integers, including the endpoint `a = r = 1`.
-/

namespace LanglandsSecondMainLemma.Dyadic.Nonmaximal

noncomputable section

open LanglandsFirstMainLemma

open private additive_eq_of_sub_mem even_trace_conductor even_normPhase
  from LanglandsSecondMainLemma.Dyadic.Nonmaximal.LowerCharacters

/-- The integer depth of the permitted normalization error. -/
private theorem normalization_error_mem
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {r : ℕ} (hr : 1 ≤ r) (u : unitFiltration F (2 * r - 1)) :
    ((u : Fˣ) : F) - 1 ∈ lattice F (2 * (r : ℤ) - 1) := by
  have hstep : 2 * r - 1 = (2 * r - 2) + 1 := by omega
  have h : (u : Fˣ) ∈ unitFiltration F ((2 * r - 2) + 1) := by
    simpa only [← hstep] using u.property
  rw [mem_unitFiltration_succ_iff_sub_mem_lattice] at h
  convert h using 1
  congr 1
  omega

/-- On a lower ideal, the raw error has depth
`-n_F - 2r + (2r-1) + v_F(beta) + q`. -/
private theorem normalization_lower_value
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (ψ : LocalAddCharData F) (α : Fˣ) {r : ℕ} (hr : 1 ≤ r)
    (hα : ord F (α : F) = ((-ψ.conductor - 2 * (r : ℤ) : ℤ) : WithTop ℤ))
    {b q : ℤ} (hdepth : 1 ≤ b + q)
    (β : F) (hβ : β ∈ lattice F b)
    (u : unitFiltration F (2 * r - 1)) (v : F) (hv : v ∈ lattice F q) :
    (scaleAddCharData F ψ (α * (u : Fˣ))).character (β * v) =
      (scaleAddCharData F ψ α).character (β * v) := by
  simp only [scaleAddCharData_character_apply, Units.val_mul]
  apply additive_eq_of_sub_mem F ψ
  have hαmem : (α : F) ∈ lattice F (-ψ.conductor - 2 * (r : ℤ)) := by
    rw [mem_lattice, hα]
  have herr := mul_mem_lattice F hαmem
    (mul_mem_lattice F (normalization_error_mem F hr u) (mul_mem_lattice F hβ hv))
  rw [show (α : F) * ((u : Fˣ) : F) * (β * v) - (α : F) * (β * v) =
    (α : F) * ((((u : Fˣ) : F) - 1) * (β * v)) by ring]
  exact lattice_antitone F (by omega) herr

/-- On a quadratic core ideal, the normalized error has depth
`2(2r-1) + (1-2a) + s`. The conductor is that of the actual trace
pullback; no phase cancellation is assumed. -/
private theorem normalization_core_value
    (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
    (hram : ramificationIndex F E = 2)
    (ψ : LocalAddCharData F) (α : Fˣ) {a r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    {J : ℤ}
    (hΨ : IsAdditiveConductor E
      (tracePullbackAddChar F E (scaleAddCharData F ψ α).character) (-J))
    (hdepth : J ≤ 2 * (2 * (r : ℤ) - 1) + (1 - 2 * (a : ℤ)) + (s : ℤ))
    (c : E) (hc : c ∈ lattice E (1 - 2 * (a : ℤ)))
    (u : unitFiltration F (2 * r - 1)) (v : unitFiltration E s) :
    tracePullbackAddChar F E (scaleAddCharData F ψ (α * (u : Fˣ))).character
        (c * (1 - ((v : Eˣ) : E))) =
      tracePullbackAddChar F E (scaleAddCharData F ψ α).character
        (c * (1 - ((v : Eˣ) : E))) := by
  let Ψ : LocalAddCharData E := ⟨_, -J, hΨ⟩
  have hscale (w : E) :
      tracePullbackAddChar F E (scaleAddCharData F ψ (α * (u : Fˣ))).character w =
        Ψ.character (algebraMap F E ((u : Fˣ) : F) * w) := by
    have ht : trace F E (algebraMap F E ((u : Fˣ) : F) * w) =
        ((u : Fˣ) : F) * trace F E w := by
      simpa [Algebra.smul_def] using (trace F E).map_smul ((u : Fˣ) : F) w
    simp only [Ψ, tracePullbackAddChar_apply, scaleAddCharData_character_apply,
      Units.val_mul, ht, mul_assoc]
  rw [hscale]
  change Ψ.character _ = Ψ.character _
  apply additive_eq_of_sub_mem E Ψ
  have hv : 1 - ((v : Eˣ) : E) ∈ lattice E (s : ℤ) := by
    have hstep : s = (s - 1) + 1 := by omega
    have h : (v : Eˣ) ∈ unitFiltration E ((s - 1) + 1) := by
      simpa only [← hstep] using v.property
    rw [mem_unitFiltration_succ_iff_sub_mem_lattice] at h
    simpa only [← hstep, neg_sub] using neg_mem_lattice E h
  have hu : algebraMap F E (((u : Fˣ) : F) - 1) ∈
      lattice E (2 * (2 * (r : ℤ) - 1)) := by
    rw [mem_lattice, ord_algebraMap, hram]
    have h := (mem_lattice F).1 (normalization_error_mem F hr u)
    simpa only [two_nsmul, ← WithTop.coe_add, two_mul] using add_le_add h h
  have herr := mul_mem_lattice E hu (mul_mem_lattice E hc hv)
  change _ ∈ lattice E (- -J)
  rw [neg_neg, show algebraMap F E ((u : Fˣ) : F) * (c * (1 - ((v : Eˣ) : E))) -
      c * (1 - ((v : Eˣ) : E)) =
      algebraMap F E (((u : Fˣ) : F) - 1) * (c * (1 - ((v : Eˣ) : E))) by
        rw [map_sub, map_one]; ring]
  exact lattice_antitone E (by omega) herr

/-- The complete fixed formulas from `lowerCharacters` and `twist`.
All norm-phase identities, exact additive conductors, and full core
domains are retained; the three continuous characters are parameters. -/
def NormalizationFormulas
    (F L₁ L₂ L₃ : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Field L₁] [ValuativeRel L₁] [TopologicalSpace L₁] [IsNonarchimedeanLocalField L₁]
    [Field L₂] [ValuativeRel L₂] [TopologicalSpace L₂] [IsNonarchimedeanLocalField L₂]
    [Field L₃] [ValuativeRel L₃] [TopologicalSpace L₃] [IsNonarchimedeanLocalField L₃]
    [Algebra F L₁] [ValuativeExtension F L₁] [Module.Finite F L₁]
    [Algebra F L₂] [ValuativeExtension F L₂] [Module.Finite F L₂]
    [Algebra F L₃] [ValuativeExtension F L₃] [Module.Finite F L₃]
    (a r : ℕ) (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂)
    (ω₃ : NormCharacter F L₃) (ψ : LocalAddCharData F) (β₁ β₂ β₃ : Fˣ)
    (c₁ : L₁) (c₂ : L₂) (c₃ : L₃)
    (χ₁ : ContinuousQuasiChar L₁) (χ₂ : ContinuousQuasiChar L₂)
    (χ₃ : ContinuousQuasiChar L₃) (α : Fˣ) : Prop :=
  LowerCharacterData F L₁ L₂ L₃ a r ω₁ ω₂ ω₃ ψ α β₁ β₂ β₃ ∧
    (∀ v : unitFiltration L₁ (2 * r), χ₁ (v : L₁ˣ) =
      tracePullbackAddChar F L₁ (scaleAddCharData F ψ α).character
        (c₁ * (1 - ((v : L₁ˣ) : L₁)))) ∧
    (∀ v : unitFiltration L₂ (a + r), χ₂ (v : L₂ˣ) =
      tracePullbackAddChar F L₂ (scaleAddCharData F ψ α).character
        (c₂ * (1 - ((v : L₂ˣ) : L₂)))) ∧
    (∀ v : unitFiltration L₃ (a + r), χ₃ (v : L₃ˣ) =
      tracePullbackAddChar F L₃ (scaleAddCharData F ψ α).character
        (c₃ * (1 - ((v : L₃ˣ) : L₃))))

section ActualFields

variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]
  (L₁ L₂ L₃ : IntermediateField F K)

attribute [local instance] Basic.intermediateFieldValuativeRel
  Basic.intermediateFieldTopology Basic.intermediateField_localField
  Basic.intermediateField_lowerValuativeExtension Basic.intermediateField_upperValuativeExtension

variable [Algebra.IsQuadraticExtension F L₁] [PrimeCyclicExtension F L₁]
  [Algebra.IsQuadraticExtension F L₂] [PrimeCyclicExtension F L₂]
  [Algebra.IsQuadraticExtension F L₃] [PrimeCyclicExtension F L₃]

set_option maxHeartbeats 1000000 in
/-- **Normalization freedom after realization**, Paper Lemma 13.8
(`D:NM:freedom`).

The coefficients are the actual norms and trace norms of the constructed
origin. `H` consists of the lower data and the three full charts already
realized by `lowerCharacters` and `twist`. Every allowed unit preserves
these formulas for the same characters, including the norm-phase identities
and the exact conductor ledger. Preservation is proved below from the
integer depth inequalities, rather than supplied as a hypothesis.

For every nonzero base coefficient, an allowed unit produces an actual
third-field norm. The last identity holds on all of `F`, so any coefficient
formula for any fixed continuous base quasi-character retains that character
and its entire domain. Neither the raw covector nor the base character is
changed. No surjectivity of a critical norm map is asserted.
-/
theorem normalization
    (a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r)
    (ht₁ : PrimeCyclicExtension.IsLowerBreak F L₁ (2 * a - 1))
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F L₂ (2 * r - 1))
    (ht₃ : PrimeCyclicExtension.IsLowerBreak F L₃ (2 * r - 1))
    (hres₁ : residueDegree F L₁ = 1) (hres₂ : residueDegree F L₂ = 1)
    (hres₃ : residueDegree F L₃ = 1)
    (x : L₁) (y : L₂) (z : L₃) (f g d : F)
    (O : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂) (ω₃ : NormCharacter F L₃)
    (hω₃ : ω₃ ≠ 1) (ψ : LocalAddCharData F) (α : Fˣ)
    (χ₁ : ContinuousQuasiChar L₁) (χ₂ : ContinuousQuasiChar L₂)
    (χ₃ : ContinuousQuasiChar L₃) :
    let β₁ := normUnits F L₁ (Units.mk0 (trace L₁ K O.Y) O.upperTraces_ne_zero.1)
    let β₂ := normUnits F L₂ (Units.mk0 (trace L₂ K O.Y) O.upperTraces_ne_zero.2.1)
    let β₃ := normUnits F L₃ (Units.mk0 (trace L₃ K O.Y) O.upperTraces_ne_zero.2.2)
    let FixedFormulas := NormalizationFormulas F L₁ L₂ L₃ a r ω₁ ω₂ ω₃ ψ β₁ β₂ β₃
      (norm L₁ K O.Y) (norm L₂ K O.Y) (norm L₃ K O.Y) χ₁ χ₂ χ₃
    FixedFormulas α →
      (∀ u : unitFiltration F (2 * r - 1), FixedFormulas (α * (u : Fˣ))) ∧
      ∀ Astar : Fˣ, ∃ (u : unitFiltration F (2 * r - 1)) (X : L₃ˣ),
        Astar / (u : Fˣ) = normUnits F L₃ X ∧
        FixedFormulas (α * (u : Fˣ)) ∧
        ord F ((α * (u : Fˣ) : Fˣ) : F) = ord F (α : F) ∧
        ord L₃ (X : L₃) = ord F (Astar : F) ∧
        (α * (u : Fˣ)) * (Astar / (u : Fˣ)) = α * Astar ∧
        (∀ w : F,
          (scaleAddCharData F ψ (α * (u : Fˣ))).character
              (((Astar / (u : Fˣ) : Fˣ) : F) * w) =
            (scaleAddCharData F ψ α).character ((Astar : F) * w)) := by
  let β₁ := normUnits F L₁ (Units.mk0 (trace L₁ K O.Y) O.upperTraces_ne_zero.1)
  let β₂ := normUnits F L₂ (Units.mk0 (trace L₂ K O.Y) O.upperTraces_ne_zero.2.1)
  let β₃ := normUnits F L₃ (Units.mk0 (trace L₃ K O.Y) O.upperTraces_ne_zero.2.2)
  let FixedFormulas := NormalizationFormulas F L₁ L₂ L₃ a r ω₁ ω₂ ω₃ ψ β₁ β₂ β₃
    (norm L₁ K O.Y) (norm L₂ K O.Y) (norm L₃ K O.Y) χ₁ χ₂ χ₃
  change FixedFormulas α → _
  intro H
  have hr : 1 ≤ r := ha.trans har
  have huord (u : unitFiltration F (2 * r - 1)) : ord F ((u : Fˣ) : F) = 0 :=
    (mem_unitFiltration_zero F _).mp (unitFiltration_antitone F (Nat.zero_le _) u.property)
  have hαord (u : unitFiltration F (2 * r - 1)) :
      ord F ((α * (u : Fˣ) : Fˣ) : F) = ord F (α : F) := by
    rw [Units.val_mul, ord_mul, huord u, add_zero]
  have hβ₁ : (β₁ : F) ∈ lattice F (2 * ((r : ℤ) - a)) := by
    change norm F L₁ (trace L₁ K O.Y) ∈ _
    rw [mem_lattice, O.lowerNormTrace₁_order]
  have hβ₂ : (β₂ : F) ∈ lattice F 0 := by
    change norm F L₂ (trace L₂ K O.Y) ∈ _
    rw [mem_lattice, O.lowerNormTrace₂_order]; rfl
  have hβ₃ : (β₃ : F) ∈ lattice F 0 := by
    change norm F L₃ (trace L₃ K O.Y) ∈ _
    rw [mem_lattice, O.lowerNormTrace₃_order]; rfl
  have hram (E : IntermediateField F K) [Algebra.IsQuadraticExtension F E]
      (hres : residueDegree F E = 1) : ramificationIndex F E = 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F E
    rw [hres, mul_one, Algebra.IsQuadraticExtension.finrank_eq_two F E] at h
    exact h.symm
  have hpreserved (u : unitFiltration F (2 * r - 1)) : FixedFormulas (α * (u : Fˣ)) := by
    have hcond : (scaleAddCharData F ψ (α * (u : Fˣ))).conductor = -2 * (r : ℤ) := by
      rw [scaleAddCharData_conductor, unitOrder, hαord]
      exact H.1.base_conductor
    have hΨ : IsAdditiveConductor F
        (scaleAddCharData F ψ (α * (u : Fˣ))).character (-2 * (r : ℤ)) := by
      rw [← hcond]
      exact (scaleAddCharData F ψ (α * (u : Fˣ))).isConductor
    have hlower₁ : ∀ v ∈ lattice F (a : ℤ), ∀ B : Fˣ, (B : F) = 1 - v →
        ω₁.1 B = (scaleAddCharData F ψ (α * (u : Fˣ))).character ((β₁ : F) * v) := by
      intro v hv B hB
      exact (H.1.first_formula v hv B hB).trans
        (normalization_lower_value F ψ α hr H.1.normalizing_order
          (by omega) β₁ hβ₁ u v hv).symm
    have hlower₂ : ∀ v ∈ lattice F (r : ℤ), ∀ B : Fˣ, (B : F) = 1 - v →
        ω₂.1 B = (scaleAddCharData F ψ (α * (u : Fˣ))).character ((β₂ : F) * v) := by
      intro v hv B hB
      exact (H.1.second_formula v hv B hB).trans
        (normalization_lower_value F ψ α hr H.1.normalizing_order
          (by omega) β₂ hβ₂ u v hv).symm
    have hlower₃ : ∀ v ∈ lattice F (r : ℤ), ∀ B : Fˣ, (B : F) = 1 - v →
        ω₃.1 B = (scaleAddCharData F ψ (α * (u : Fˣ))).character ((β₃ : F) * v) := by
      intro v hv B hB
      exact (H.1.third_formula v hv B hB).trans
        (normalization_lower_value F ψ α hr H.1.normalizing_order
          (by omega) β₃ hβ₃ u v hv).symm
    refine ⟨{
      normalizing_order := (hαord u).trans H.1.normalizing_order
      base_conductor := hcond
      first_conductor := ?_
      second_conductor := ?_
      third_conductor := ?_
      first_formula := hlower₁
      second_formula := hlower₂
      third_formula := hlower₃
      first_norm_value := H.1.first_norm_value
      second_norm_value := H.1.second_norm_value
      third_norm_value := H.1.third_norm_value
      first_phase := even_normPhase F L₁ a ha ht₁ hres₁ ω₁ _ β₁ hlower₁
      second_phase := even_normPhase F L₂ r hr ht₂ hres₂ ω₂ _ β₂ hlower₂
      third_phase := even_normPhase F L₃ r hr ht₃ hres₃ ω₃ _ β₃ hlower₃ }, ?_, ?_, ?_⟩
    · convert even_trace_conductor F L₁ a ha ht₁ hres₁ _ _ hΨ using 1
      ring
    · convert even_trace_conductor F L₂ r hr ht₂ hres₂ _ _ hΨ using 1
      ring
    · convert even_trace_conductor F L₃ r hr ht₃ hres₃ _ _ hΨ using 1
      ring
    · intro v
      exact (H.2.1 v).trans (normalization_core_value F L₁ (hram L₁ hres₁)
        ψ α (a := a) (s := 2 * r) hr (by omega) H.1.first_conductor (by push_cast; omega)
        (norm L₁ K O.Y) (by rw [mem_lattice, O.upperNorm₁_order]) u v).symm
    · intro v
      exact (H.2.2.1 v).trans (normalization_core_value F L₂ (hram L₂ hres₂)
        ψ α (a := a) (s := a + r) (J := 2 * (r : ℤ)) hr (by omega)
        (by simpa only [neg_mul] using H.1.second_conductor) (by push_cast; omega)
        (norm L₂ K O.Y) (by rw [mem_lattice, O.upperNorm₂_order]) u v).symm
    · intro v
      exact (H.2.2.2 v).trans (normalization_core_value F L₃ (hram L₃ hres₃)
        ψ α (a := a) (s := a + r) (J := 2 * (r : ℤ)) hr (by omega)
        (by simpa only [neg_mul] using H.1.third_conductor) (by push_cast; omega)
        (norm L₃ K O.Y) (by rw [mem_lattice, O.upperNorm₃_order]) u v).symm
  refine ⟨hpreserved, ?_⟩
  intro Astar
  -- FML's join of the actual norm range with the critical unit layer
  -- gives the full character image, via norm-triviality and subgroup algebra.
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F L₃ hres₃
  have himage : (unitFiltration F (2 * r - 1)).map ω₃.1.toMonoidHom =
      ω₃.1.toMonoidHom.range := by
    rw [Subgroup.map_eq_range_iff, codisjoint_iff]
    apply top_unique
    rw [← (cyclicPrimeNormFiltration F L₃ ht₃ hres₃ pi hpi hgen).field_image_sup]
    apply sup_le
    · exact le_sup_of_le_right (fun v hv => ω₃.eq_one_on_normRange F L₃ v hv)
    · exact le_sup_left
  have hωval : ω₃.1 ≠ 1 := fun h => hω₃ (Subtype.ext h)
  obtain ⟨u, X, hnorm, _, hraw⟩ := Stationary.normalizationFreedom
    (PrimeCyclicExtension.toCyclicPrimeExtension (F := F) (K := L₃))
    ω₃ hωval (unitFiltration F (2 * r - 1)) FixedFormulas α Astar
    (fun u => iff_of_true (hpreserved u) H) himage
  refine ⟨u, X, hnorm, hpreserved u, hαord u, ?_, hraw, ?_⟩
  · have h := congrArg (fun v : Fˣ => ord F (v : F)) hnorm
    rw [coe_normUnits, ord_norm, hres₃, one_nsmul,
      Units.val_div_eq_div_val, ord_div, huord u, sub_zero] at h
    exact h.symm
  · intro w
    simp only [scaleAddCharData_character_apply]
    have h := congrArg (fun v : Fˣ => (v : F)) hraw
    simp only [Units.val_mul] at h
    exact congrArg ψ.character (by
      simpa only [Units.val_mul, mul_assoc] using congrArg (fun v : F => v * w) h)

end ActualFields

end

end LanglandsSecondMainLemma.Dyadic.Nonmaximal
