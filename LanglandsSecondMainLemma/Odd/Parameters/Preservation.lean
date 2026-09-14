import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsSecondMainLemma.Odd.Parameters.NormChoice
import LanglandsSecondMainLemma.Odd.Total.TraceNorm

/-!
# Odd / Parameters / Preservation

Blueprint: blueprint/tasks/Odd/Parameters/Preservation.md
Paper: Lemma 8.16 (`O:P:preserve`), lines 3041--3064, in the full
minimal-model setup of lines 2367--2445.

`preservation` keeps the actual two continuous quasi-characters, the actual
coordinate and both of its norms, and the same lower norm character. It
changes only `alpha` to `alpha * h`, for every `h ∈ U_F^{t₂}`. All three
formulas hold on their entire original truncated-log domains.

The exact additive conductors are derived from the chart of the nontrivial
lower norm character and FML's trace-conductor theorem. The two upper errors
have integer depths `p*t₂-t+qᵢ`. The lower error uses the accepted coefficient
estimate from `NormChoice`. No exact norm equation or change of norm-character
generator is made here: the given full formulas are those obtained after
actual realization, and subsequent norm choices may use this preservation.
-/

namespace LanglandsSecondMainLemma.Odd.Parameters

noncomputable section

open LanglandsFirstMainLemma
open Models

set_option backward.isDefEq.respectTransparency false

open private lamprechtAddChar_eq_of_sub_mem from
  LanglandsFirstMainLemma.Lamprecht.Formula
open private additiveConductor_of_normCharacterChart from
  LanglandsSecondMainLemma.Odd.Models.Setup
open private realization_tower_data from
  LanglandsSecondMainLemma.Odd.Models.Realization

private theorem unit_displacement
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {q : ℕ} (hq : 0 < q)
    (u : unitFiltration E q) :
    1 - ((u : Eˣ) : E) ∈ lattice E (q : ℤ) := by
  have hu := (mem_unitFiltration_succ_iff_sub_mem_lattice E (q - 1)
    (u : Eˣ)).1 (by simpa only [Nat.sub_add_cancel hq] using u.property)
  simpa only [Nat.sub_add_cancel hq, neg_sub] using neg_mem_lattice E hu

/-- The error estimate on a whole positive ideal. All depths, including
the coefficient order and additive conductor, are integers. -/
private theorem fullPhase_mul_unit
    (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
    {p r q : ℕ} {t J : ℤ} (hchar : residueCharacteristic E = p)
    (hram : ramificationIndex F E = p) (hr : 0 < r) (hq : 0 < q)
    (Psi : ContinuousAddChar E) (hPsi : IsAdditiveConductor E Psi (-J))
    (b : E) (hb : ord E b = (-(t : ℤ) : WithTop ℤ))
    (hdepth : J ≤ (p : ℤ) * r - t + q)
    (h : unitFiltration F r) (u : unitFiltration E q) :
    Psi (algebraMap F E ((h : Fˣ) : F) * b *
        truncatedLog p (1 - ((u : Eˣ) : E))) =
      Psi (b * truncatedLog p (1 - ((u : Eˣ) : E))) := by
  have hh : ((h : Fˣ) : F) - 1 ∈ lattice F (r : ℤ) := by
    simpa only [neg_sub] using neg_mem_lattice F (unit_displacement F hr h)
  have hhE : algebraMap F E ((h : Fˣ) : F) - 1 ∈
      lattice E ((p : ℤ) * r) := by
    rw [← map_one (algebraMap F E), ← map_sub, mem_lattice, ord_algebraMap, hram]
    simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using
      nsmul_le_nsmul_right ((mem_lattice F).1 hh) p
  have hP := (truncatedLogOnLattice E p q hchar hq
    ⟨_, unit_displacement E hq u⟩).property
  change truncatedLog p (1 - ((u : Eˣ) : E)) ∈ lattice E (q : ℤ) at hP
  have hbmem : b ∈ lattice E (-t) := (mem_lattice E).2 hb.ge
  have herr := mul_mem_lattice E (mul_mem_lattice E hhE hbmem) hP
  have hdiff : algebraMap F E ((h : Fˣ) : F) * b *
        truncatedLog p (1 - ((u : Eˣ) : E)) -
      b * truncatedLog p (1 - ((u : Eˣ) : E)) ∈ lattice E J := by
    convert lattice_antitone E (by omega : J ≤ (p : ℤ) * r + -t + q) herr using 1
    ring
  exact lamprechtAddChar_eq_of_sub_mem E ⟨Psi, -J, hPsi⟩
    (by simpa only [neg_neg] using hdiff)

/-- FML's additive scaling commutes with the actual trace. -/
private theorem scaledTrace_apply
    (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
    (e : LocalAddCharData F) (alpha : Fˣ) (x : E) :
    tracePullbackAddChar F E (scaleAddCharData F e alpha).character x =
      tracePullbackAddChar F E e.character (algebraMap F E (alpha : F) * x) := by
  simp only [tracePullbackAddChar_apply, scaleAddCharData_character_apply]
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

section Diamond

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]
  {p : ℕ} (hp : p.Prime)
  (hG : Nonempty
    (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
  (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
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

include hres hchar

set_option maxHeartbeats 400000 in
/-- **Preservation of the full minimal models, Paper 8.16 (`O:P:preserve`).**
The two given continuous quasi-characters already have the full models with
coefficients `alpha * N₁(Delta)` and `alpha * N₂(Delta)`, as supplied by actual
realization (including its allowed first conjugate). Multiplying `alpha` by
any depth-`t₂` unit preserves both formulas and the chart of the very same
nontrivial norm character `tau`. It also preserves the coefficient's order.

The proof only needs the order of the realized coordinate and the displayed
full formulas; compatibility, primitivity and the Artin--Schreier equation
need not be assumed again. Both field characteristics and arbitrary continuous
quasi-characters are allowed. The domains are exactly `⌈mᵢ/p⌉` and
`⌈(t₂+1)/p⌉`, with no restriction to half-conductor subgroups. -/
theorem preservation
    (e : LocalAddCharData F) (alpha : Fˣ)
    (tau : NormCharacter F B₂) (htau : tau ≠ 1)
    (htauFormula : ∀ u : unitFiltration F ((D.t₂ + 1) ⌈/⌉ p),
      tau.1 u = e.character ((alpha : F) *
        truncatedLog p (1 - ((u : Fˣ) : F))))
    (Delta : K) (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (phi₁ : ContinuousQuasiChar B₁) (phi₂ : ContinuousQuasiChar B₂)
    (hphi₁ : ∀ u : unitFiltration B₁ (firstModelDepth D),
      phi₁ u = tracePullbackAddChar F B₁ e.character
        (algebraMap F B₁ (alpha : F) * norm B₁ K Delta *
          truncatedLog p (1 - ((u : B₁ˣ) : B₁))))
    (hphi₂ : ∀ u : unitFiltration B₂ (secondModelDepth D),
      phi₂ u = tracePullbackAddChar F B₂ e.character
        (algebraMap F B₂ (alpha : F) * norm B₂ K Delta *
          truncatedLog p (1 - ((u : B₂ˣ) : B₂))))
    (h : unitFiltration F D.t₂) :
    (∀ u : unitFiltration B₁ (firstModelDepth D),
      phi₁ u = tracePullbackAddChar F B₁ e.character
        (algebraMap F B₁ ((alpha * (h : Fˣ) : Fˣ) : F) * norm B₁ K Delta *
          truncatedLog p (1 - ((u : B₁ˣ) : B₁)))) ∧
    (∀ u : unitFiltration B₂ (secondModelDepth D),
      phi₂ u = tracePullbackAddChar F B₂ e.character
        (algebraMap F B₂ ((alpha * (h : Fˣ) : Fˣ) : F) * norm B₂ K Delta *
          truncatedLog p (1 - ((u : B₂ˣ) : B₂)))) ∧
    (∀ u : unitFiltration F ((D.t₂ + 1) ⌈/⌉ p),
      tau.1 u = e.character (((alpha * (h : Fˣ) : Fˣ) : F) *
        truncatedLog p (1 - ((u : Fˣ) : F)))) ∧
    ord F ((alpha * (h : Fˣ) : Fˣ) : F) = ord F (alpha : F) := by
  let Psi := (scaleAddCharData F e alpha).character
  have hc : 0 < (D.t₂ + 1) ⌈/⌉ p := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_pos (by omega) hp.pos
  have hchart : ∀ z : lattice F (((D.t₂ + 1) ⌈/⌉ p : ℕ) : ℤ),
      tau.1 (positiveUnitOfLattice F hc (-z)) = Psi (truncatedLog p (z : F)) := by
    intro z
    simpa [Psi] using htauFormula (positiveUnitOfLattice F hc (-z))
  obtain ⟨_, hrF₁, hr₁, he₁, _⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  obtain ⟨_, hrF₂, hr₂, he₂, _⟩ := realization_tower_data hp hG hres B₂ D.degree_B₂
  have ht₂ : 0 < D.t₂ := D.t_pos.trans_le D.t_le_t₂
  have hPsi := additiveConductor_of_normCharacterChart F B₂ hp D.odd_prime hchar
    D.degree_B₂ D.B₂_breaks.1 ht₂ hrF₂ rfl hc tau htau Psi hchart
  obtain ⟨pi₁, hpi₁, hgen₁⟩ := monogenicUniformizer F B₁ hrF₁
  obtain ⟨pi₂, hpi₂, hgen₂⟩ := monogenicUniformizer F B₂ hrF₂
  have hPsi₁ := additiveConductor_compTrace_cyclicPrime F B₁
    D.B₁_breaks.1 hrF₁ pi₁ hpi₁ hgen₁ hPsi
  have hPsi₂ := additiveConductor_compTrace_cyclicPrime F B₂
    D.B₂_breaks.1 hrF₂ pi₂ hpi₂ hgen₂ hPsi
  have hc₁ : (p : ℤ) * (-((D.t₂ + 1 : ℕ) : ℤ)) +
      (((p - 1) * (D.t + 1) : ℕ) : ℤ) = -((D.tPrime + 1 : ℕ) : ℤ) := by
    simp only [D.t₂_eq, D.tPrime_eq, Nat.cast_add, Nat.cast_mul,
      Nat.cast_sub hp.one_le, Nat.cast_one]
    ring
  have hc₂ : (p : ℤ) * (-((D.t₂ + 1 : ℕ) : ℤ)) +
      (((p - 1) * (D.t₂ + 1) : ℕ) : ℤ) = -((D.t₂ + 1 : ℕ) : ℤ) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one]
    ring
  have hd₁ : Module.finrank F B₁ = p := D.degree_B₁
  have hd₂ : Module.finrank F B₂ = p := D.degree_B₂
  rw [hd₁, hc₁] at hPsi₁
  rw [hd₂, hc₂] at hPsi₂
  have hb : ord B₁ (norm B₁ K Delta) = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_norm, hr₁, one_nsmul, hDelta]
  have ha : ord B₂ (norm B₂ K Delta) = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_norm, hr₂, one_nsmul, hDelta]
  obtain ⟨hq₁, hq₂, _⟩ := domains_original D hres
  have hbound₁ : ((D.tPrime + 1 : ℕ) : ℤ) ≤
      (p : ℤ) * D.t₂ - D.t + firstModelDepth D := by
    have hp3 : (3 : ℤ) ≤ p := by exact_mod_cast D.odd_prime
    have ht1 : (1 : ℤ) ≤ D.t := by exact_mod_cast D.t_pos
    rw [D.t₂_eq, D.tPrime_eq]
    push_cast
    nlinarith only [hp3, ht1,
      (show (0 : ℤ) ≤ (firstModelDepth D : ℤ) from Nat.cast_nonneg _)]
  have hbound₂ : ((D.t₂ + 1 : ℕ) : ℤ) ≤
      (p : ℤ) * D.t₂ - D.t + secondModelDepth D := by
    have hp3 : (3 : ℤ) ≤ p := by exact_mod_cast D.odd_prime
    have ht1 : (1 : ℤ) ≤ D.t := by exact_mod_cast D.t_pos
    have htt : (D.t : ℤ) ≤ D.t₂ := by exact_mod_cast D.t_le_t₂
    push_cast
    nlinarith only [hp3, ht1, htt,
      (show (0 : ℤ) ≤ (secondModelDepth D : ℤ) from Nat.cast_nonneg _)]
  have hphase₁ := fullPhase_mul_unit F B₁
    ((residueCharacteristic_extension_eq F B₁).trans hchar) he₁ ht₂ hq₁
    (tracePullbackAddChar F B₁ Psi) hPsi₁ (norm B₁ K Delta) hb hbound₁ h
  have hphase₂ := fullPhase_mul_unit F B₂
    ((residueCharacteristic_extension_eq F B₂).trans hchar) he₂ ht₂ hq₂
    (tracePullbackAddChar F B₂ Psi) hPsi₂ (norm B₂ K Delta) ha hbound₂ h
  have halphaOrder : ord F (alpha : F) =
      ((-e.conductor - (D.t₂ : ℤ) - 1 : ℤ) : WithTop ℤ) := by
    have heq := (scaleAddCharData F e alpha).isConductor.unique hPsi
    rw [scaleAddCharData_conductor] at heq
    rw [ord_coe_eq_unitOrder]
    congr 1
    push_cast at heq
    omega
  obtain ⟨horder, _, hphaseF⟩ := normChoice_coefficient_mul F hchar ht₂ hc
    e alpha halphaOrder h
  refine ⟨?_, ?_, ?_, horder.trans halphaOrder.symm⟩
  · intro u
    have hv := hphase₁ u
    simp only [Psi, scaledTrace_apply, mul_assoc] at hv
    rw [hphi₁ u, Units.val_mul, map_mul (algebraMap F B₁)]
    simpa only [mul_assoc] using hv.symm
  · intro u
    have hv := hphase₂ u
    simp only [Psi, scaledTrace_apply, mul_assoc] at hv
    rw [hphi₂ u, Units.val_mul, map_mul (algebraMap F B₂)]
    simpa only [mul_assoc] using hv.symm
  · intro u
    exact (htauFormula u).trans
      (hphaseF ⟨_, unit_displacement F hc u⟩).symm

end Diamond

end

end LanglandsSecondMainLemma.Odd.Parameters
