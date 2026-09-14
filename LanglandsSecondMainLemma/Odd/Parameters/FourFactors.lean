import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Odd.Parameters.Pullback
import LanglandsSecondMainLemma.Odd.Parameters.Lamprecht
import LanglandsSecondMainLemma.Characters.OddPower

/-!
# Odd / Parameters / Four Factors

Blueprint: blueprint/tasks/Odd/Parameters/FourFactors.md
Paper: Proposition 8.20 (`O:P:four`), with the transition setup
`O:P:parameters` and `O:P:C`, corrected source lines 3149--3251.

The full minimal charts and the preserved, exact norm choices are the
inputs at this stage. The descending pullback theorem constructs the full
transition charts; unequal conductors and strict coefficient orders rule
out cancellation. Lamprecht supplies the actual residual factors, including
their entire odd Gauss sums. The final identity retains the trace--norm
phase and does not assert its cancellation.
-/

namespace LanglandsSecondMainLemma.Odd.Parameters

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

section OneField

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- The complete factor from `O:P:lamprecht`, including its actual odd sum.
The complex local constant is FML's canonical `localConstant`. -/
def IsFourFactorGauss (theta : ContinuousQuasiChar E) (psi : ContinuousAddChar E)
    (n : ℕ) (C : Eˣ) (g : ℂ) : Prop :=
  g ^ 4 = 1 ∧
  localConstant E theta psi =
    (theta ((-C)⁻¹) : ℂ) * (psi (-(C : E)) : ℂ) * g ∧
  (n % 2 = 0 → g = 1) ∧
  (n % 2 = 1 → ∀ delta : Eˣ,
    ord E (delta : E) = (((n / 2 : ℕ) : ℤ) : WithTop ℤ) →
    g = (Real.sqrt (residueCard E : ℝ) : ℂ)⁻¹ *
      ∑ x ∈ @Finset.univ (ResidueField E) (residueFieldFintype E),
        (psi (-(C : E) * (delta : E) ^ 2 *
          (teichmuller E x : E) ^ 2 / (2 : E)) : ℂ))

/-- The denominator `g₁` in the four-factor ratio cannot vanish. -/
theorem IsFourFactorGauss.gauss_ne_zero
    {theta : ContinuousQuasiChar E} {psi : ContinuousAddChar E}
    {n : ℕ} {C : Eˣ} {g : ℂ} (h : IsFourFactorGauss E theta psi n C g) :
    g ≠ 0 := by
  intro hz
  have hfour := h.1
  simp only [hz, zero_pow (by decide : 4 ≠ 0), zero_ne_one] at hfour

/-- The actual local constant used as a denominator is nonzero, by its
proved full Lamprecht formula and unit-valued character evaluations. -/
theorem IsFourFactorGauss.localConstant_ne_zero
    {theta : ContinuousQuasiChar E} {psi : ContinuousAddChar E}
    {n : ℕ} {C : Eˣ} {g : ℂ} (h : IsFourFactorGauss E theta psi n C g) :
    localConstant E theta psi ≠ 0 := by
  rw [h.2.1]
  exact mul_ne_zero (mul_ne_zero (ContinuousQuasiChar.apply_ne_zero _ _)
    (ContinuousAddChar.apply_ne_zero _ _)) (h.gauss_ne_zero E)

end OneField

section Edge

variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E]
  [Module.Free F E] [Module.Finite F E] [PrimeCyclicExtension F E]

/-- Add a lower-conductor full minimal model to the actual descending
pullback. Both sums are proved nonzero before they are used as units. -/
private theorem transition_factors
    {p t r k : ℕ} (hdegree : Module.finrank F E = p) (hodd : 2 < p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
    (hr : t < r) (hres : residueDegree F E = 1)
    (lambda : ContinuousQuasiChar F)
    (phi : ContinuousQuasiChar E)
    (hlambda : IsMultiplicativeConductor F lambda (r + 1))
    (hphi : IsMultiplicativeConductor E phi k)
    (hk : k < 1 + t + p * (r - t))
    (e : LocalAddCharData F) (gamma a : Fˣ)
    (hgamma : ord F (gamma : F) =
      ((-e.conductor - (r : ℤ) - 1 : ℤ) : WithTop ℤ))
    (hlambdaFormula : ∀ u : unitFiltration F ((r + 1) ⌈/⌉ p),
      lambda u = e.character ((gamma : F) *
        truncatedLog p (1 - ((u : Fˣ) : F))))
    (nu : NormCharacter F E) (hnu : nu ≠ 1)
    (ha : ord F (a : F) =
      ((-e.conductor - (t : ℤ) - 1 : ℤ) : WithTop ℤ))
    (hnuFormula : ∀ u : unitFiltration F ((t + 1) ⌈/⌉ p),
      nu.1 u = e.character ((a : F) *
        truncatedLog p (1 - ((u : Fˣ) : F))))
    (w : Eˣ) (hw : normUnits F E w = gamma / a)
    (b : E) (hb : p • ord F (gamma : F) < ord E b)
    (hphiFormula : ∀ u : unitFiltration E (k ⌈/⌉ p),
      phi u = tracePullbackAddChar F E e.character
        (b * truncatedLog p (1 - ((u : Eˣ) : E)))) :
    let n := 1 + t + p * (r - t)
    let theta := phi * lambda.compNorm (S := E)
    IsMultiplicativeConductor E theta n ∧
    ∃ A C : Eˣ,
      (A : E) = algebraMap F E (gamma : F) + b ∧
      (C : E) = algebraMap F E (gamma : F) -
        algebraMap F E (a : F) * (w : E) + b ∧
      ord E (A : E) = p • ord F (gamma : F) ∧
      ord E (C : E) = p • ord F (gamma : F) ∧
      ∃ g : ℂ, IsFourFactorGauss E theta
        (tracePullbackAddChar F E e.character) n C g := by
  dsimp only
  obtain ⟨hq, hcond, hadd, hbase, hbaseOrder, hfull⟩ :=
    pullback F E hdegree hodd ht htpos hr hres lambda hlambda e gamma a
      hgamma hlambdaFormula nu hnu ha hnuFormula w hw
  have htheta := hphi.mul_of_lt hcond hk
  have hram : ramificationIndex F E = p := by
    simpa only [hdegree, hres, mul_one] using
      (finrank_eq_ramificationIndex_mul_residueDegree F E).symm
  have hAord : ord E (algebraMap F E (gamma : F) + b) =
      p • ord F (gamma : F) := by
    rw [(ord E).map_add_eq_of_lt_left (by simpa [ord_algebraMap, hram] using hb)]
    rw [ord_algebraMap, hram]
  have hCord : ord E (algebraMap F E (gamma : F) -
      algebraMap F E (a : F) * (w : E) + b) = p • ord F (gamma : F) := by
    rw [(ord E).map_add_eq_of_lt_left (by simpa only [hbase] using hb), hbase]
  have hfinite : p • ord F (gamma : F) ≠ ⊤ := by
    rw [hgamma, ← WithTop.coe_nsmul]
    exact WithTop.coe_ne_top
  let A : Eˣ := Units.mk0 (algebraMap F E (gamma : F) + b) (by
    intro h
    apply hfinite
    rw [← hAord, h, ord_zero])
  let C : Eˣ := Units.mk0 (algebraMap F E (gamma : F) -
      algebraMap F E (a : F) * (w : E) + b) (by
    intro h
    apply hfinite
    rw [← hCord, h, ord_zero])
  let theta : LocalQuasiCharData E := ⟨phi * lambda.compNorm, _, htheta⟩
  let psi : LocalAddCharData E := ⟨tracePullbackAddChar F E e.character, _, hadd⟩
  have hn : 1 < theta.conductor := by change 1 < 1 + t + p * (r - t); omega
  have hqpos : 0 < theta.conductor ⌈/⌉ p := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_pos (by omega) (by omega)
  have hkp : k ⌈/⌉ p ≤ theta.conductor ⌈/⌉ p := by
    rw [ceilDiv_le_iff_le_mul (by omega : 0 < p)]
    exact hk.le.trans ((ceilDiv_le_iff_le_mul (by omega : 0 < p)).1 le_rfl)
  have hC : IsEnhancedStationaryCoefficient E theta psi p
      (theta.conductor ⌈/⌉ p) hqpos (-psi.conductor) C := by
    refine ⟨hCord.trans (hbase.symm.trans hbaseOrder), ?_⟩
    intro z
    let u := positiveUnitOfLattice E hqpos (-z)
    let u0 : unitFiltration E (k ⌈/⌉ p) :=
      ⟨(u : Eˣ), unitFiltration_antitone E hkp u.property⟩
    have hu : 1 - ((u : Eˣ) : E) = (z : E) := by simp [u]
    have hpull := hfull ⟨(u : Eˣ), by simpa only [hq] using u.property⟩
    have hminimal := hphiFormula u0
    change (phi * lambda.compNorm (S := E)) (u : Eˣ) = _
    rw [ContinuousQuasiChar.mul_apply, hminimal, hpull]
    simp only [u0, hu]
    rw [← ContinuousAddChar.map_add_eq_mul]
    congr 1
    change b * truncatedLog p (z : E) +
      (algebraMap F E (gamma : F) - algebraMap F E (a : F) * (w : E)) *
        truncatedLog p (z : E) = _
    dsimp only [C, Units.val_mk0, psi]
    ring
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have hchar : ringChar (ResidueField E) = p :=
    (residueCharacteristic_extension_eq F E).trans
      ((residueCharacteristic_eq_degree_of_positive_isLowerBreak F E
        ht htpos pi hpi hgen).trans hdegree)
  obtain ⟨g, hg⟩ := lamprecht E theta psi p (theta.conductor ⌈/⌉ p)
    (theta.conductor / 2) (theta.conductor % 2) hchar (by omega)
    (by omega) (by omega) hn rfl hqpos C hC
  exact ⟨htheta, A, C, rfl, rfl, hAord, hCord, g, hg⟩

end Edge

/-- The four factors are units of `ℂ`: every character value and every
division in their definition is therefore nonzero. -/
structure FourFactorValues where
  Q₁ : ℂˣ
  Q₂ : ℂˣ
  Q₃ : ℂˣ
  Q₄ : ℂˣ

/-- The ordered product appearing in `O:P:ratio`. -/
def FourFactorValues.product (Q : FourFactorValues) : ℂˣ :=
  Q.Q₁ * Q.Q₂ * Q.Q₃ * Q.Q₄

section TwoFields

variable (F E₁ E₂ : Type*) [Field F] [Field E₁] [Field E₂]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E₁] [TopologicalSpace E₁] [IsNonarchimedeanLocalField E₁]
  [ValuativeRel E₂] [TopologicalSpace E₂] [IsNonarchimedeanLocalField E₂]
  [Algebra F E₁] [ValuativeExtension F E₁] [Module.Finite F E₁]
  [Algebra F E₂] [ValuativeExtension F E₂] [Module.Finite F E₂]

/-- The literal corrected factors of Proposition 8.20. `A₁,C₁,w₁` belong
to the first lower field, `C₂,w₂` to the second, and both lower norms
in `Q₂` belong to `Fˣ`. -/
def fourFactorValues (chi : ContinuousQuasiChar E₁) (phi : ContinuousQuasiChar E₂)
    (lambda : ContinuousQuasiChar F) (e : ContinuousAddChar F)
    (alpha beta : Fˣ) (w₁ A₁ C₁ : E₁ˣ) (w₂ C₂ : E₂ˣ) : FourFactorValues where
  Q₁ := chi A₁ / phi C₂
  Q₂ := lambda (normUnits F E₁ A₁ / normUnits F E₂ C₂)
  Q₃ := tracePullbackAddChar F E₁ e
    (-algebraMap F E₁ (beta : F) * (w₁ : E₁)) *
      (chi * lambda.compNorm (S := E₁)) (C₁ / A₁)
  Q₄ := tracePullbackAddChar F E₂ e
    (algebraMap F E₂ (alpha : F) * (w₂ : E₂))

/-- Algebra of the complete Lamprecht formulas. The equal value at `-1`
will be proved from the actual common norm pullback in the diamond. -/
private theorem fourFactors_identity
    (chi : ContinuousQuasiChar E₁) (phi : ContinuousQuasiChar E₂)
    (lambda : ContinuousQuasiChar F) (e : ContinuousAddChar F)
    (alpha beta gamma : Fˣ) (w₁ A₁ C₁ : E₁ˣ) (w₂ C₂ : E₂ˣ)
    (b₁ : E₁) (b₂ : E₂)
    (hdegree : Module.finrank F E₁ = Module.finrank F E₂)
    (hC₁ : (C₁ : E₁) = algebraMap F E₁ (gamma : F) -
      algebraMap F E₁ (beta : F) * (w₁ : E₁) +
        algebraMap F E₁ (alpha : F) * b₁)
    (hC₂ : (C₂ : E₂) = algebraMap F E₂ (gamma : F) -
      algebraMap F E₂ (alpha : F) * (w₂ : E₂) +
        algebraMap F E₂ (alpha : F) * b₂)
    (hminus : (chi * lambda.compNorm (S := E₁)) (-1) =
      (phi * lambda.compNorm (S := E₂)) (-1))
    {n₁ n₂ : ℕ} {g₁ g₂ : ℂ}
    (hg₁ : IsFourFactorGauss E₁ (chi * lambda.compNorm)
      (tracePullbackAddChar F E₁ e) n₁ C₁ g₁)
    (hg₂ : IsFourFactorGauss E₂ (phi * lambda.compNorm)
      (tracePullbackAddChar F E₂ e) n₂ C₂ g₂) :
    localConstant E₂ (phi * lambda.compNorm) (tracePullbackAddChar F E₂ e) /
      localConstant E₁ (chi * lambda.compNorm) (tracePullbackAddChar F E₁ e) =
    g₂ / g₁ *
      ((fourFactorValues F E₁ E₂ chi phi lambda e alpha beta w₁ A₁ C₁ w₂ C₂).product : ℂ) *
      (e ((alpha : F) * (trace F E₁ b₁ - trace F E₂ b₂)) : ℂ) := by
  let theta₁ := chi * lambda.compNorm (S := E₁)
  let theta₂ := phi * lambda.compNorm (S := E₂)
  let psi₁ := tracePullbackAddChar F E₁ e
  let psi₂ := tracePullbackAddChar F E₂ e
  let Q := fourFactorValues F E₁ E₂ chi phi lambda e alpha beta w₁ A₁ C₁ w₂ C₂
  change theta₁ (-1) = theta₂ (-1) at hminus
  have hmult : Q.Q₁ * Q.Q₂ * theta₁ (C₁ / A₁) =
      theta₁ C₁ / theta₂ C₂ := by
    dsimp only [Q, fourFactorValues, theta₁, theta₂]
    simp only [map_div, ContinuousQuasiChar.mul_apply, ContinuousQuasiChar.compNorm_apply,
      normUnits, LanglandsFirstMainLemma.norm]
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul]
    field_simp
  have htrace : trace F E₁ (C₁ : E₁) + trace F E₂ (-(C₂ : E₂)) =
      trace F E₁ (-algebraMap F E₁ (beta : F) * (w₁ : E₁)) +
      trace F E₂ (algebraMap F E₂ (alpha : F) * (w₂ : E₂)) +
      (alpha : F) * (trace F E₁ b₁ - trace F E₂ b₂) := by
    rw [hC₁, hC₂]
    simp only [map_add, map_sub, map_neg, trace_algebraMap, hdegree, neg_mul]
    simp only [← Algebra.smul_def, map_smul, smul_eq_mul]
    ring
  have hadd : psi₁ (C₁ : E₁) * psi₂ (-(C₂ : E₂)) =
      psi₁ (-algebraMap F E₁ (beta : F) * (w₁ : E₁)) *
      psi₂ (algebraMap F E₂ (alpha : F) * (w₂ : E₂)) *
      e ((alpha : F) * (trace F E₁ b₁ - trace F E₂ b₂)) := by
    simp only [psi₁, psi₂, tracePullbackAddChar_apply,
      ← ContinuousAddChar.map_add_eq_mul, htrace]
  have hQ : theta₁ C₁ / theta₂ C₂ *
      psi₁ (C₁ : E₁) * psi₂ (-(C₂ : E₂)) =
      Q.product * e ((alpha : F) * (trace F E₁ b₁ - trace F E₂ b₂)) := by
    rw [mul_assoc, hadd, ← hmult]
    dsimp only [FourFactorValues.product, Q, fourFactorValues, theta₁, psi₁, psi₂]
    ac_rfl
  have hnegative₁ : theta₁ ((-C₁)⁻¹) =
      (theta₁ (-1) * theta₁ C₁)⁻¹ := by
    rw [show -C₁ = (-1 : E₁ˣ) * C₁ by simp, map_inv, map_mul]
  have hnegative₂ : theta₂ ((-C₂)⁻¹) =
      (theta₂ (-1) * theta₂ C₂)⁻¹ := by
    rw [show -C₂ = (-1 : E₂ˣ) * C₂ by simp, map_inv, map_mul]
  have hpsi₁ : psi₁ (-(C₁ : E₁)) = (psi₁ (C₁ : E₁))⁻¹ :=
    psi₁.toAddChar.map_neg_eq_inv _
  have hratio :
      (theta₂ ((-C₂)⁻¹) * psi₂ (-(C₂ : E₂))) /
        (theta₁ ((-C₁)⁻¹) * psi₁ (-(C₁ : E₁))) =
      Q.product * e ((alpha : F) * (trace F E₁ b₁ - trace F E₂ b₂)) := by
    rw [hnegative₁, hnegative₂, hpsi₁, hminus, ← hQ]
    simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  calc
    _ = g₂ / g₁ *
        (((theta₂ ((-C₂)⁻¹) * psi₂ (-(C₂ : E₂))) /
          (theta₁ ((-C₁)⁻¹) * psi₁ (-(C₁ : E₁))) : ℂˣ) : ℂ) := by
      rw [hg₁.2.1, hg₂.2.1]
      dsimp only [theta₁, theta₂, psi₁, psi₂]
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [hratio, Units.val_mul]; exact (mul_assoc _ _ _).symm

end TwoFields

private theorem normUnits_neg_one
    (F E : Type*) [Field F] [Field E] [Algebra F E] [Module.Free F E]
    {p : ℕ} (hdegree : Module.finrank F E = p) (hodd : Odd p) :
    normUnits F E (-1) = -1 := by
  apply Units.ext
  change norm F E (-1) = -1
  rw [show (-1 : E) = algebraMap F E (-1) by simp,
    LanglandsFirstMainLemma.norm_algebraMap, hdegree, hodd.neg_one_pow]

open private realization_tower_data from
  LanglandsSecondMainLemma.Odd.Models.Realization

section Diamond

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]
  {p : ℕ} (hp : p.Prime)
  (hG : Nonempty
    (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
  (hres : residueDegree F K = 1)
  (D : Total.OddTotalBreakData (F := F) (K := K) hp hG)

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

local notation "B₁" => D.B₁
local notation "B₂" => D.B₂

local instance : PrimeCyclicExtension F B₁ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₁
    (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.2.2.2.1
local instance : PrimeCyclicExtension F B₂ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₂
    (Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.1

include hres

set_option maxHeartbeats 600000 in
/-- **The four actual factors, Paper Proposition 8.20 (`O:P:four`).**

The input is the actual compatible minimal pair after realization and
preservation of its full models, together with the exact norm witnesses
of `normChoice`. No stationary formula for the twisted pair is assumed:
`pullback` and the lower minimal conductors supply it here.

The two `A`'s and two `C`'s are constructed as field units with their exact
orders. The output gives the actual conductors `1+t'+pm` and `1+t₂+pm`,
both complete Lamprecht factors, and the corrected oriented identity.
The last implication is conditional on the two subsequent cancellations;
neither the trace--norm estimate nor phase cancellation is assumed in
the identity. Both field characteristics and nonunitary quasi-characters
are retained. -/
theorem fourFactors
    (e : LocalAddCharData F) (alpha beta gamma : Fˣ)
    (Delta : K) (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (chi : ContinuousQuasiChar B₁) (phi : ContinuousQuasiChar B₂)
    (hchi : IsMultiplicativeConductor B₁ chi (Models.firstModelConductor D))
    (hphi : IsMultiplicativeConductor B₂ phi (Models.secondModelConductor D))
    (hcompat : chi.compNorm (S := K) = phi.compNorm (S := K))
    (hchiFormula : ∀ u : unitFiltration B₁ (Models.firstModelDepth D),
      chi u = tracePullbackAddChar F B₁ e.character
        (algebraMap F B₁ (alpha : F) * norm B₁ K Delta *
          truncatedLog p (1 - ((u : B₁ˣ) : B₁))))
    (hphiFormula : ∀ u : unitFiltration B₂ (Models.secondModelDepth D),
      phi u = tracePullbackAddChar F B₂ e.character
        (algebraMap F B₂ (alpha : F) * norm B₂ K Delta *
          truncatedLog p (1 - ((u : B₂ˣ) : B₂))))
    {r : ℕ} (htransition : D.t < p * (r - D.t₂))
    (lambda : ContinuousQuasiChar F)
    (hlambda : IsMultiplicativeConductor F lambda (r + 1))
    (hgamma : ord F (gamma : F) =
      ((-e.conductor - (r : ℤ) - 1 : ℤ) : WithTop ℤ))
    (hlambdaFormula : ∀ u : unitFiltration F ((r + 1) ⌈/⌉ p),
      lambda u = e.character ((gamma : F) *
        truncatedLog p (1 - ((u : Fˣ) : F))))
    (nu₁ : NormCharacter F B₁) (hnu₁ : nu₁ ≠ 1)
    (nu₂ : NormCharacter F B₂) (hnu₂ : nu₂ ≠ 1)
    (hbeta : ord F (beta : F) =
      ((-e.conductor - (D.t : ℤ) - 1 : ℤ) : WithTop ℤ))
    (halpha : ord F (alpha : F) =
      ((-e.conductor - (D.t₂ : ℤ) - 1 : ℤ) : WithTop ℤ))
    (hnu₁Formula : ∀ u : unitFiltration F ((D.t + 1) ⌈/⌉ p),
      nu₁.1 u = e.character ((beta : F) *
        truncatedLog p (1 - ((u : Fˣ) : F))))
    (hnu₂Formula : ∀ u : unitFiltration F ((D.t₂ + 1) ⌈/⌉ p),
      nu₂.1 u = e.character ((alpha : F) *
        truncatedLog p (1 - ((u : Fˣ) : F))))
    (w₁ : B₁ˣ) (hw₁ : normUnits F B₁ w₁ = gamma / beta)
    (w₂ : B₂ˣ) (hw₂ : normUnits F B₂ w₂ = gamma / alpha) :
    let m := r - D.t₂
    let n₁ := 1 + D.tPrime + p * m
    let n₂ := 1 + D.t₂ + p * m
    let theta₁ := chi * lambda.compNorm (S := B₁)
    let theta₂ := phi * lambda.compNorm (S := B₂)
    let psi₁ := tracePullbackAddChar F B₁ e.character
    let psi₂ := tracePullbackAddChar F B₂ e.character
    IsMultiplicativeConductor B₁ theta₁ n₁ ∧
    IsMultiplicativeConductor B₂ theta₂ n₂ ∧
    ∃ A₁ C₁ : B₁ˣ, ∃ A₂ C₂ : B₂ˣ,
      (A₁ : B₁) = algebraMap F B₁ (gamma : F) +
        algebraMap F B₁ (alpha : F) * norm B₁ K Delta ∧
      (C₁ : B₁) = algebraMap F B₁ (gamma : F) -
        algebraMap F B₁ (beta : F) * (w₁ : B₁) +
          algebraMap F B₁ (alpha : F) * norm B₁ K Delta ∧
      (A₂ : B₂) = algebraMap F B₂ (gamma : F) +
        algebraMap F B₂ (alpha : F) * norm B₂ K Delta ∧
      (C₂ : B₂) = algebraMap F B₂ (gamma : F) -
        algebraMap F B₂ (alpha : F) * (w₂ : B₂) +
          algebraMap F B₂ (alpha : F) * norm B₂ K Delta ∧
      ord B₁ (A₁ : B₁) = p • ord F (gamma : F) ∧
      ord B₁ (C₁ : B₁) = p • ord F (gamma : F) ∧
      ord B₂ (A₂ : B₂) = p • ord F (gamma : F) ∧
      ord B₂ (C₂ : B₂) = p • ord F (gamma : F) ∧
      ∃ g₁ g₂ : ℂ,
        IsFourFactorGauss B₁ theta₁ psi₁ n₁ C₁ g₁ ∧
        IsFourFactorGauss B₂ theta₂ psi₂ n₂ C₂ g₂ ∧
        let Q := fourFactorValues F B₁ B₂ chi phi lambda e.character
          alpha beta w₁ A₁ C₁ w₂ C₂
        let residual := e.character ((alpha : F) *
          (trace F B₁ (norm B₁ K Delta) - trace F B₂ (norm B₂ K Delta)))
        localConstant B₂ theta₂ psi₂ / localConstant B₁ theta₁ psi₁ =
          g₂ / g₁ * (Q.product : ℂ) * (residual : ℂ) ∧
        (residual = 1 → Q.product⁻¹ = 1 →
          (localConstant B₂ theta₂ psi₂ / localConstant B₁ theta₁ psi₁) ^ 4 = 1) := by
  dsimp only
  have hr₂ : D.t₂ < r := by
    by_contra h
    have : r - D.t₂ = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp only [this, mul_zero] at htransition
    omega
  have hr₁ : D.t < r := D.t_le_t₂.trans_lt hr₂
  have ht₂ : 0 < D.t₂ := D.t_pos.trans_le D.t_le_t₂
  obtain ⟨hd₁, hrF₁, hrK₁, he₁, _⟩ :=
    realization_tower_data hp hG hres B₁ D.degree_B₁
  obtain ⟨hd₂, hrF₂, hrK₂, he₂, _⟩ :=
    realization_tower_data hp hG hres B₂ D.degree_B₂
  have hn₁ : 1 + D.t + p * (r - D.t) =
      1 + D.tPrime + p * (r - D.t₂) := by
    have hs : r - D.t = r - D.t₂ + D.delta := by have := D.t₂_eq; omega
    rw [hs, D.tPrime_eq]
    ring
  have hk₁ : Models.firstModelConductor D < 1 + D.t + p * (r - D.t) := by
    rw [hn₁]
    change 1 + D.t + D.tPrime < _
    omega
  have hk₂ : Models.secondModelConductor D < 1 + D.t₂ + p * (r - D.t₂) := by
    change 1 + D.t + D.t₂ < _
    omega
  have hbound : (p : ℤ) * (-e.conductor - (r : ℤ) - 1) <
      (p : ℤ) * (-e.conductor - (D.t₂ : ℤ) - 1) - D.t := by
    have hm : (D.t : ℤ) < (p : ℤ) * ((r : ℤ) - D.t₂) := by
      have h : (D.t : ℤ) < (p : ℤ) * ((r - D.t₂ : ℕ) : ℤ) := by
        exact_mod_cast htransition
      simpa only [Nat.cast_sub hr₂.le] using h
    nlinarith
  have hb₁ : p • ord F (gamma : F) <
      ord B₁ (algebraMap F B₁ (alpha : F) * norm B₁ K Delta) := by
    rw [ord_mul, ord_algebraMap, he₁, ord_norm, hrK₁, one_nsmul,
      hDelta, hgamma, halpha]
    simp only [← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_lt_coe,
      nsmul_eq_mul]
    exact hbound
  have hb₂ : p • ord F (gamma : F) <
      ord B₂ (algebraMap F B₂ (alpha : F) * norm B₂ K Delta) := by
    rw [ord_mul, ord_algebraMap, he₂, ord_norm, hrK₂, one_nsmul,
      hDelta, hgamma, halpha]
    simp only [← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_lt_coe,
      nsmul_eq_mul]
    exact hbound
  obtain ⟨hc₁, A₁, C₁, hA₁, hC₁, hAo₁, hCo₁, g₁, hg₁⟩ :=
    transition_factors F B₁ D.degree_B₁ D.odd_prime D.B₁_breaks.1 D.t_pos
      hr₁ hrF₁ lambda chi hlambda hchi hk₁ e gamma beta hgamma hlambdaFormula
      nu₁ hnu₁ hbeta hnu₁Formula w₁ hw₁
      (algebraMap F B₁ (alpha : F) * norm B₁ K Delta) hb₁ hchiFormula
  obtain ⟨hc₂, A₂, C₂, hA₂, hC₂, hAo₂, hCo₂, g₂, hg₂⟩ :=
    transition_factors F B₂ D.degree_B₂ D.odd_prime D.B₂_breaks.1 ht₂
      hr₂ hrF₂ lambda phi hlambda hphi hk₂ e gamma alpha hgamma hlambdaFormula
      nu₂ hnu₂ halpha hnu₂Formula w₂ hw₂
      (algebraMap F B₂ (alpha : F) * norm B₂ K Delta) hb₂ hphiFormula
  rw [hn₁] at hc₁ hg₁
  have hodd : Odd p := hp.odd_of_ne_two (by have := D.odd_prime; omega)
  have hsign : chi (-1) = phi (-1) := by
    have h := congrArg (fun theta : ContinuousQuasiChar K ↦ theta (-1)) hcompat
    change chi (normUnits B₁ K (-1)) = phi (normUnits B₂ K (-1)) at h
    simpa only [normUnits_neg_one B₁ K hd₁ hodd,
      normUnits_neg_one B₂ K hd₂ hodd] using h
  have hminus : (chi * lambda.compNorm (S := B₁)) (-1) =
      (phi * lambda.compNorm (S := B₂)) (-1) := by
    simp only [ContinuousQuasiChar.mul_apply, ContinuousQuasiChar.compNorm_apply]
    change chi (-1) * lambda (normUnits F B₁ (-1)) =
      phi (-1) * lambda (normUnits F B₂ (-1))
    rw [normUnits_neg_one F B₁ D.degree_B₁ hodd,
      normUnits_neg_one F B₂ D.degree_B₂ hodd, hsign]
  have hratio := fourFactors_identity F B₁ B₂ chi phi lambda e.character
    alpha beta gamma w₁ A₁ C₁ w₂ C₂ (norm B₁ K Delta) (norm B₂ K Delta)
    (D.degree_B₁.trans D.degree_B₂.symm) hC₁ hC₂ hminus hg₁ hg₂
  refine ⟨hc₁, hc₂, A₁, C₁, A₂, C₂, hA₁, hC₁, hA₂, hC₂,
    hAo₁, hCo₁, hAo₂, hCo₂, g₁, g₂, hg₁, hg₂, hratio, ?_⟩
  intro hresidual hproduct
  have hproduct' := inv_eq_one.mp hproduct
  rw [hratio, hproduct', hresidual, Units.val_one, mul_one, mul_one,
    div_pow, hg₁.1, hg₂.1, div_self one_ne_zero]

end Diamond

end

end LanglandsSecondMainLemma.Odd.Parameters
