import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsFirstMainLemma.Parameters.HighQuadratic
import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.Origin
import LanglandsSecondMainLemma.Dyadic.Mixed.UnitSymbol
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.CovectorRatio

/-!
# Dyadic / Nonmaximal / Lower Characters

Paper Lemma 13.3, `D:NM:lower`, with the normalization `D:NM:normalization`
and the exact additive conductor ledger `D:NM:J`.

The accepted covector-ratio theorem constructs the ordinary covectors and
proves the whole-ideal error estimate. We transport that estimate to the
actual norm coefficients from the accepted origin, prove the third lower
formula using `β₃ - β₁ - β₂ = -2d + 4E`, and evaluate the actual norms.
FML's exact quadratic norm identity and trace-ideal formula give the
positive norm-phase conversion on each source ideal.

Controlling source: `references/epsilon_SML.tex`, lines 7405--7458 and
7500--7624. The supplied origin record has proved constructors in `Origin`;
no stationary formula, norm representative, or phase cancellation is
assumed in the constructor `lowerCharacters`.
-/

namespace LanglandsSecondMainLemma.Dyadic.Nonmaximal

open LanglandsFirstMainLemma
open LanglandsSecondMainLemma.Characters

noncomputable section

private theorem additive_eq_of_sub_mem
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (ψ : LocalAddCharData F) {c d : F}
    (h : c - d ∈ lattice F (-ψ.conductor)) :
    ψ.character c = ψ.character d := by
  apply div_eq_one.mp
  exact (ψ.character.toAddChar.map_sub_eq_div c d).symm.trans
    (ψ.isConductor.trivial _ h)

section QuadraticEdge

variable (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [Algebra.IsQuadraticExtension F E] [PrimeCyclicExtension F E]

private theorem even_normCharacter_conductor
    (q : ℕ) (hq : 1 ≤ q)
    (ht : PrimeCyclicExtension.IsLowerBreak F E (2 * q - 1))
    (hres : residueDegree F E = 1)
    (ω : NormCharacter F E) (hω : ω ≠ 1) :
    IsMultiplicativeConductor F ω.1 (2 * q) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  simpa only [Nat.sub_add_cancel (show 1 ≤ 2 * q by omega)] using
    ramifiedNormCharacter_conductor F E ht hres pi hpi hgen ω hω

private theorem even_trace_conductor
    (q : ℕ) (hq : 1 ≤ q)
    (ht : PrimeCyclicExtension.IsLowerBreak F E (2 * q - 1))
    (hres : residueDegree F E = 1)
    (Ψ : ContinuousAddChar F) (n : ℤ)
    (hΨ : IsAdditiveConductor F Ψ n) :
    IsAdditiveConductor E (tracePullbackAddChar F E Ψ)
      (2 * n + 2 * (q : ℤ)) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  change IsAdditiveConductor E Ψ.compTrace (2 * n + 2 * (q : ℤ))
  simpa only [Algebra.IsQuadraticExtension.finrank_eq_two F E,
    Nat.sub_add_cancel (show 1 ≤ 2 * q by omega),
    Nat.reduceSub, one_mul, Nat.cast_mul, Nat.cast_ofNat] using
    additiveConductor_compTrace_cyclicPrime F E ht hres pi hpi hgen hΨ

/-- Evaluate the exact norm of `1-v`. Its character is one, so the
trace phase equals the norm phase with a positive sign. -/
private theorem even_normPhase
    (q : ℕ) (hq : 1 ≤ q)
    (ht : PrimeCyclicExtension.IsLowerBreak F E (2 * q - 1))
    (hres : residueDegree F E = 1)
    (ω : NormCharacter F E) (Ψ : ContinuousAddChar F) (β : F)
    (hformula : ∀ u ∈ lattice F (q : ℤ), ∀ B : Fˣ, (B : F) = 1 - u →
      ω.1 B = Ψ (β * u))
    (v : E) (hv : v ∈ lattice E (q : ℤ)) :
    tracePullbackAddChar F E Ψ (algebraMap F E β * v) =
      Ψ (β * norm F E v) := by
  have htrace : trace F E v ∈ lattice F (q : ℤ) := by
    obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
    have hmap : trace F E v ∈
        Submodule.map ((trace F E).restrictScalars (ringOfIntegers F))
          ((lattice E (q : ℤ)).restrictScalars (ringOfIntegers F)) :=
      Submodule.mem_map.mpr ⟨v, hv, rfl⟩
    rw [cyclicPrime_trace_lattice_image_eq F E ht hres pi hpi hgen,
      Algebra.IsQuadraticExtension.finrank_eq_two F E] at hmap
    simp only [Nat.reduceSub, one_mul,
      Nat.sub_add_cancel (show 1 ≤ 2 * q by omega),
      Nat.cast_mul, Nat.cast_ofNat] at hmap
    exact lattice_antitone F (by omega) hmap
  have hnorm : norm F E v ∈ lattice F (q : ℤ) := by
    rw [mem_lattice, ord_norm, hres, one_nsmul]
    exact hv
  have hnegv : -v ∈ lattice E 1 :=
    neg_mem_lattice E (lattice_antitone E (by exact_mod_cast hq) hv)
  let V : Eˣ := Dyadic.Mixed.oneAddUnit E (-v) hnegv
  have hV : (V : E) = 1 - v := by simp [V, sub_eq_add_neg]
  have hnormV : (normUnits F E V : F) =
      1 - (trace F E v - norm F E v) := by
    rw [coe_normUnits, hV]
    have hid := wildQuadratic_norm_sub F E
      (Algebra.IsQuadraticExtension.finrank_eq_two F E) 1 v
    calc
      _ = 1 - trace F E v + norm F E v := by simpa using hid
      _ = _ := by ring
  have hphase : Ψ (β * (trace F E v - norm F E v)) = 1 := by
    rw [← hformula _ (sub_mem_lattice F htrace hnorm) (normUnits F E V) hnormV]
    exact ω.eq_one_on_normRange F E _ ⟨V, rfl⟩
  have htraceMul : trace F E (algebraMap F E β * v) = β * trace F E v := by
    simpa [Algebra.smul_def] using (trace F E).map_smul β v
  rw [tracePullbackAddChar_apply, htraceMul]
  apply div_eq_one.mp
  calc
    _ = Ψ (β * trace F E v - β * norm F E v) :=
      (Ψ.toAddChar.map_sub_eq_div _ _).symm
    _ = 1 := by rw [← mul_sub]; exact hphase

end QuadraticEdge

/-- The complete conclusion of `D:NM:lower`, including the normalization
and the largest trivial ideals `D:NM:J`. The arguments `βᵢ` are field
units; in `lowerCharacters` they are the actual norms of the upper traces.
Each chart quantifies over every element of its entire integer-indexed ideal. -/
structure LowerCharacterData
    (F L₁ L₂ L₃ : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Field L₁] [ValuativeRel L₁] [TopologicalSpace L₁] [IsNonarchimedeanLocalField L₁]
    [Field L₂] [ValuativeRel L₂] [TopologicalSpace L₂] [IsNonarchimedeanLocalField L₂]
    [Field L₃] [ValuativeRel L₃] [TopologicalSpace L₃] [IsNonarchimedeanLocalField L₃]
    [Algebra F L₁] [ValuativeExtension F L₁] [Module.Finite F L₁]
    [Algebra F L₂] [ValuativeExtension F L₂] [Module.Finite F L₂]
    [Algebra F L₃] [ValuativeExtension F L₃] [Module.Finite F L₃]
    (a r : ℕ) (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂)
    (ω₃ : NormCharacter F L₃) (ψ : LocalAddCharData F)
    (α β₁ β₂ β₃ : Fˣ) : Prop where
  normalizing_order : ord F (α : F) =
    ((-ψ.conductor - 2 * (r : ℤ) : ℤ) : WithTop ℤ)
  base_conductor : (scaleAddCharData F ψ α).conductor = -2 * (r : ℤ)
  first_conductor : IsAdditiveConductor L₁
    (tracePullbackAddChar F L₁ (scaleAddCharData F ψ α).character)
    (-(4 * (r : ℤ) - 2 * (a : ℤ)))
  second_conductor : IsAdditiveConductor L₂
    (tracePullbackAddChar F L₂ (scaleAddCharData F ψ α).character) (-2 * (r : ℤ))
  third_conductor : IsAdditiveConductor L₃
    (tracePullbackAddChar F L₃ (scaleAddCharData F ψ α).character) (-2 * (r : ℤ))
  first_formula : ∀ u ∈ lattice F (a : ℤ), ∀ B : Fˣ, (B : F) = 1 - u →
    ω₁.1 B = (scaleAddCharData F ψ α).character ((β₁ : F) * u)
  second_formula : ∀ u ∈ lattice F (r : ℤ), ∀ B : Fˣ, (B : F) = 1 - u →
    ω₂.1 B = (scaleAddCharData F ψ α).character ((β₂ : F) * u)
  third_formula : ∀ u ∈ lattice F (r : ℤ), ∀ B : Fˣ, (B : F) = 1 - u →
    ω₃.1 B = (scaleAddCharData F ψ α).character ((β₃ : F) * u)
  first_norm_value : ω₁.1 β₁ = 1
  second_norm_value : ω₂.1 β₂ = 1
  third_norm_value : ω₃.1 β₃ = 1
  first_phase : ∀ v ∈ lattice L₁ (a : ℤ),
    tracePullbackAddChar F L₁ (scaleAddCharData F ψ α).character
        (algebraMap F L₁ (β₁ : F) * v) =
      (scaleAddCharData F ψ α).character ((β₁ : F) * norm F L₁ v)
  second_phase : ∀ v ∈ lattice L₂ (r : ℤ),
    tracePullbackAddChar F L₂ (scaleAddCharData F ψ α).character
        (algebraMap F L₂ (β₂ : F) * v) =
      (scaleAddCharData F ψ α).character ((β₂ : F) * norm F L₂ v)
  third_phase : ∀ v ∈ lattice L₃ (r : ℤ),
    tracePullbackAddChar F L₃ (scaleAddCharData F ψ α).character
        (algebraMap F L₃ (β₃ : F) * v) =
      (scaleAddCharData F ψ α).character ((β₃ : F) * norm F L₃ v)

section ActualFields

variable (F K : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [Module.Finite F K]
  (L₁ L₂ L₃ : IntermediateField F K)
  [ValuativeRel L₁] [TopologicalSpace L₁] [IsNonarchimedeanLocalField L₁]
  [ValuativeRel L₂] [TopologicalSpace L₂] [IsNonarchimedeanLocalField L₂]
  [ValuativeRel L₃] [TopologicalSpace L₃] [IsNonarchimedeanLocalField L₃]
  [ValuativeExtension F L₁] [ValuativeExtension L₁ K]
  [ValuativeExtension F L₂] [ValuativeExtension L₂ K]
  [ValuativeExtension F L₃] [ValuativeExtension L₃ K]
  [Module.Finite F L₁] [Module.Finite L₁ K]
  [Module.Finite F L₂] [Module.Finite L₂ K]
  [Module.Finite F L₃] [Module.Finite L₃ K]
  [Algebra.IsQuadraticExtension F L₁] [PrimeCyclicExtension F L₁]
  [Algebra.IsQuadraticExtension F L₂] [PrimeCyclicExtension F L₂]
  [Algebra.IsQuadraticExtension F L₃] [PrimeCyclicExtension F L₃]

/-- **All three full lower formulas**, Paper Lemma 13.3 (`D:NM:lower`).

Start with the accepted aligned origin in the actual quadratic fields,
their lower breaks, and their nontrivial continuous norm characters. The
product relation is exactly the lower-character relation in the ambient
setup used by `dyadicNonmaximal_covectorRatio`.

FML constructs the ordinary covector `b₂`; the normalized character is
`Ψ_F(u) = ψ_F((b₂/β₂)u)`. The returned data proves all three whole-ideal
charts, all three actual norm-character values, the exact additive
conductors, and all three positive norm-phase identities. No covector
error or phase identity is assumed. -/
theorem lowerCharacters
    (hchar : ringChar F ≠ 2)
    (e a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (ht₁ : PrimeCyclicExtension.IsLowerBreak F L₁ (2 * a - 1))
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F L₂ (2 * r - 1))
    (ht₃ : PrimeCyclicExtension.IsLowerBreak F L₃ (2 * r - 1))
    (hres₁ : residueDegree F L₁ = 1) (hres₂ : residueDegree F L₂ = 1)
    (hres₃ : residueDegree F L₃ = 1)
    (x : L₁) (y : L₂) (z : L₃) (f g d : F)
    (O : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂) (ω₃ : NormCharacter F L₃)
    (hω₁ : ω₁ ≠ 1) (hω₂ : ω₂ ≠ 1) (hω₃ : ω₃ ≠ 1)
    (hproduct : ω₃.1 = ω₁.1 * ω₂.1)
    (ψ : LocalAddCharData F) :
    let β₁ := normUnits F L₁ (Units.mk0 (trace L₁ K O.Y) O.upperTraces_ne_zero.1)
    let β₂ := normUnits F L₂ (Units.mk0 (trace L₂ K O.Y) O.upperTraces_ne_zero.2.1)
    let β₃ := normUnits F L₃ (Units.mk0 (trace L₃ K O.Y) O.upperTraces_ne_zero.2.2)
    ∃ b₂ : Fˣ,
      ord F (b₂ : F) = ((-ψ.conductor - 2 * (r : ℤ) : ℤ) : WithTop ℤ) ∧
      (∀ u ∈ lattice F (r : ℤ), ∀ B : Fˣ, (B : F) = 1 - u →
        ω₂.1 B = ψ.character ((b₂ : F) * u)) ∧
      LowerCharacterData F L₁ L₂ L₃ a r ω₁ ω₂ ω₃ ψ (b₂ / β₂) β₁ β₂ β₃ := by
  let β₁ := normUnits F L₁ (Units.mk0 (trace L₁ K O.Y) O.upperTraces_ne_zero.1)
  let β₂ := normUnits F L₂ (Units.mk0 (trace L₂ K O.Y) O.upperTraces_ne_zero.2.1)
  let β₃ := normUnits F L₃ (Units.mk0 (trace L₃ K O.Y) O.upperTraces_ne_zero.2.2)
  have hr : 1 ≤ r := ha.trans har
  have hconductor₁ := even_normCharacter_conductor F L₁ a ha ht₁ hres₁ ω₁ hω₁
  have hconductor₂ := even_normCharacter_conductor F L₂ r hr ht₂ hres₂ ω₂ hω₂
  obtain ⟨b₁, b₂, _, hb₂ord, hb₁, hb₂, _, _, _, herror⟩ :=
    dyadicNonmaximal_covectorRatio F L₁ L₂ L₃ hchar e a r ha har hre htwo
      x y z f g d O ω₁ ω₂ ω₃ hω₁ hω₂ hω₃ hproduct hconductor₁ hconductor₂ ψ
  let α : Fˣ := b₂ / β₂
  let Ψ := scaleAddCharData F ψ α
  have hαord : ord F (α : F) =
      ((-ψ.conductor - 2 * (r : ℤ) : ℤ) : WithTop ℤ) := by
    simp only [α, Units.val_div_eq_div_val, β₂, coe_normUnits, Units.val_mk0]
    rw [ord_div, hb₂ord, O.lowerNormTrace₂_order, sub_zero]
  have hαorder : unitOrder F α = -ψ.conductor - 2 * (r : ℤ) := by
    apply WithTop.coe_injective
    rw [← ord_coe_eq_unitOrder F α, hαord]
  have hΨcond : Ψ.conductor = -2 * (r : ℤ) := by
    change ψ.conductor + unitOrder F α = _
    rw [hαorder]
    omega
  have hΨ : IsAdditiveConductor F Ψ.character (-2 * (r : ℤ)) := by
    rw [← hΨcond]
    exact Ψ.isConductor
  have hformula₁ : ∀ u ∈ lattice F (a : ℤ), ∀ B : Fˣ, (B : F) = 1 - u →
      ω₁.1 B = Ψ.character ((β₁ : F) * u) := by
    intro u hu B hB
    rw [hb₁ u hu B hB]
    change ψ.character ((b₁ : F) * u) = ψ.character ((α : F) * ((β₁ : F) * u))
    apply additive_eq_of_sub_mem F ψ
    have herr : (b₁ : F) - (α : F) * (β₁ : F) ∈
        lattice F (-ψ.conductor - (a : ℤ)) := by
      simpa only [α, Units.val_div_eq_div_val, β₁, β₂, coe_normUnits,
        Units.val_mk0] using herror
    simpa only [sub_mul, mul_assoc, sub_add_cancel] using mul_mem_lattice F herr hu
  have hformula₂ : ∀ u ∈ lattice F (r : ℤ), ∀ B : Fˣ, (B : F) = 1 - u →
      ω₂.1 B = Ψ.character ((β₂ : F) * u) := by
    intro u hu B hB
    rw [hb₂ u hu B hB]
    simp only [Ψ, scaleAddCharData_character_apply, α, Units.val_div_eq_div_val]
    congr 1
    field_simp
  have hsum : (β₃ : F) - (β₁ : F) - (β₂ : F) ∈ lattice F (r : ℤ) := by
    have htwoD : 2 * d ∈ lattice F (r : ℤ) := by
      rw [mem_lattice, ord_mul, htwo, O.d_order]
      exact_mod_cast (show (r : ℤ) ≤ (e : ℤ) + ((r : ℤ) - a) by omega)
    have hfour : (4 : F) ∈ lattice F (2 * (e : ℤ)) := by
      rw [mem_lattice, show (4 : F) = 2 * 2 by norm_num, ord_mul, htwo]
      exact_mod_cast (show 2 * (e : ℤ) ≤ (e : ℤ) + e by omega)
    have hfourE : 4 * O.E ∈ lattice F (r : ℤ) :=
      lattice_antitone F (by omega) (mul_mem_lattice F hfour O.E_lattice)
    have hid : (β₃ : F) - (β₁ : F) - (β₂ : F) = -(2 * d) + 4 * O.E := by
      change norm F L₃ (trace L₃ K O.Y) - norm F L₁ (trace L₁ K O.Y) -
        norm F L₂ (trace L₂ K O.Y) = _
      rw [O.lowerNormTrace₁, O.lowerNormTrace₂, O.lowerNormTrace₃, O.k₀_eq, O.E_eq]
      ring
    rw [hid]
    exact add_mem_lattice F (neg_mem_lattice F htwoD) hfourE
  have hformula₃ : ∀ u ∈ lattice F (r : ℤ), ∀ B : Fˣ, (B : F) = 1 - u →
      ω₃.1 B = Ψ.character ((β₃ : F) * u) := by
    intro u hu B hB
    have hua : u ∈ lattice F (a : ℤ) := lattice_antitone F (by exact_mod_cast har) hu
    rw [hproduct, ContinuousQuasiChar.mul_apply, hformula₁ u hua B hB,
      hformula₂ u hu B hB, ← ContinuousAddChar.map_add_eq_mul]
    apply additive_eq_of_sub_mem F Ψ
    have hmul := mul_mem_lattice F (neg_mem_lattice F hsum) hu
    rw [hΨcond]
    convert hmul using 1
    · congr 1
      ring
    · ring
  refine ⟨b₂, hb₂ord, hb₂, {
    normalizing_order := hαord
    base_conductor := hΨcond
    first_conductor := ?_
    second_conductor := ?_
    third_conductor := ?_
    first_formula := hformula₁
    second_formula := hformula₂
    third_formula := hformula₃
    first_norm_value := ω₁.eq_one_on_normRange F L₁ _ ⟨_, rfl⟩
    second_norm_value := ω₂.eq_one_on_normRange F L₂ _ ⟨_, rfl⟩
    third_norm_value := ω₃.eq_one_on_normRange F L₃ _ ⟨_, rfl⟩
    first_phase := even_normPhase F L₁ a ha ht₁ hres₁ ω₁ Ψ.character β₁ hformula₁
    second_phase := even_normPhase F L₂ r hr ht₂ hres₂ ω₂ Ψ.character β₂ hformula₂
    third_phase := even_normPhase F L₃ r hr ht₃ hres₃ ω₃ Ψ.character β₃ hformula₃ }⟩
  · convert even_trace_conductor F L₁ a ha ht₁ hres₁ Ψ.character (-2 * (r : ℤ)) hΨ using 1
    ring
  · convert even_trace_conductor F L₂ r hr ht₂ hres₂ Ψ.character (-2 * (r : ℤ)) hΨ using 1
    ring
  · convert even_trace_conductor F L₃ r hr ht₃ hres₃ Ψ.character (-2 * (r : ℤ)) hΨ using 1
    ring

end ActualFields

end
end LanglandsSecondMainLemma.Dyadic.Nonmaximal
