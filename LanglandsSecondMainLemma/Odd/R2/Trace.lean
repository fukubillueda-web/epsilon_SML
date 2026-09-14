import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.R2.Shift
import LanglandsSecondMainLemma.Odd.Total.TwistedEstimates

/-!
# Odd / R2 / Trace

Blueprint: blueprint/tasks/Odd/R2/Trace.md
Paper: Lemma 8.11 (`O:R:T`), with normalization at lines 2782--2810
and the approximate norm choice `O:R:approx`.

The denominator is an actual element of the first intermediate field.
Its norm differs from the coefficient ratio by a unit of depth `t`.
The proof retains this error and applies norm-phase conversion on the
entire ideal of depth `ceil((t+1)/p)`.
-/

namespace LanglandsSecondMainLemma.Odd.R2

noncomputable section

open LanglandsFirstMainLemma

set_option backward.isDefEq.respectTransparency false

open private additivePhase_sub from LanglandsSecondMainLemma.Odd.Models.TwistFormula
open private additiveConductor_of_normCharacterChart from
  LanglandsSecondMainLemma.Odd.Models.Setup
open private realization_tower_data from LanglandsSecondMainLemma.Odd.Models.Realization

/-- The shallow ideal maps into the full chart for the second lower
character, including when its depth is beyond the first lower break. -/
private theorem trace_depths {p t d : ℕ} (hp : 2 < p) (ht : 0 < t) :
    0 < (t + 1) ⌈/⌉ p ∧
    0 < (t + d + 1) ⌈/⌉ p ∧
    (t + d + 1) ⌈/⌉ p ≤ d + (t + 1) ⌈/⌉ p ∧
    (t + d + 1) ⌈/⌉ p ≤
      (d + (t + 1) ⌈/⌉ p + (p - 1) * (t + 1)) / p ∧
    t + d + 1 ≤ d + (t + 1) ⌈/⌉ p + t := by
  have hct : t + 1 ≤ p * ((t + 1) ⌈/⌉ p) := le_smul_ceilDiv (show 0 < p by omega)
  have hcpos : 0 < (t + 1) ⌈/⌉ p := by
    by_contra h
    have hz : (t + 1) ⌈/⌉ p = 0 := by omega
    rw [hz, mul_zero] at hct
    omega
  have hrt : t + d + 1 ≤ p * ((t + d + 1) ⌈/⌉ p) :=
    le_smul_ceilDiv (show 0 < p by omega)
  have hrpos : 0 < (t + d + 1) ⌈/⌉ p := by
    by_contra h
    have hz : (t + d + 1) ⌈/⌉ p = 0 := by omega
    rw [hz, mul_zero] at hrt
    omega
  refine ⟨hcpos, hrpos, ?_, ?_, by omega⟩
  · rw [ceilDiv_le_iff_le_mul (by omega : 0 < p)]
    have := Nat.le_mul_of_pos_left d (by omega : 0 < p)
    nlinarith
  · rw [Nat.le_div_iff_mul_le (by omega : 0 < p)]
    have hupper : p * ((t + d + 1) ⌈/⌉ p) ≤ t + d + p := by
      rw [Nat.ceilDiv_eq_add_pred_div]
      have h := Nat.mul_div_le (t + d + 1 + p - 1) p
      omega
    have hpt : 2 * t ≤ (p - 1) * t :=
      Nat.mul_le_mul_right t (by omega)
    have hpred : p - 1 + 1 = p := by omega
    nlinarith

section Approximation

variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

/-- Construct `O:R:approx` from the ordinary subcritical norm filtration.
No surjectivity at the critical layer and no exact norm equation for
`rho` is required. The order is any integer. -/
theorem trace_approximateNorm
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1)
    (rho : Fˣ) (d : ℤ) (hrho : ord F (rho : F) = (d : WithTop ℤ)) :
    ∃ (c : Eˣ) (epsilon : unitFiltration F t),
      normUnits F E c = rho * (epsilon : Fˣ) ∧
      ord E (c : E) = (d : WithTop ℤ) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  obtain ⟨c, hc⟩ := exists_norm_representative_mod_break F E ht hres pi hpi hgen rho
  let epsilon : unitFiltration F t := ⟨(rho / normUnits F E c)⁻¹,
    (unitFiltration F t).inv_mem hc⟩
  have hnorm : normUnits F E c = rho * (epsilon : Fˣ) := by
    simp [epsilon, div_eq_mul_inv, mul_comm]
  have heord : ord F ((epsilon : Fˣ) : F) = 0 :=
    (mem_unitFiltration_zero F _).1
      (unitFiltration_antitone F (Nat.zero_le t) epsilon.property)
  refine ⟨c, epsilon, hnorm, ?_⟩
  calc
    ord E (c : E) = ord F (normUnits F E c : F) := by
      rw [coe_normUnits, ord_norm, hres, one_nsmul]
    _ = (d : WithTop ℤ) := by rw [hnorm, Units.val_mul, ord_mul, hrho, heord, add_zero]

end Approximation

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

include hp hG hres hchar D

/-- Lemma 8.11 (`O:R:T`) for every actual approximate norm denominator.
Here `Psi(z) = e_F(alpha*z)` and `rho = beta/alpha`; the second full
chart is written as `Psi(rho*P(z))`. Thus both charts use the same
additive character. Their exact additive conductors are proved from
the nontrivial norm characters, rather than assumed.

The only norm equality is `N(c) = rho*epsilon`, with the actual error
unit `epsilon ∈ U_F^t`. The source order of `c` is deduced from it.
The formula holds on the entire shallow ideal, in either characteristic. -/
theorem trace
    (r₁ r₂ : ℕ) (hr₁ : r₁ = (D.t + 1) ⌈/⌉ p)
    (hr₂ : r₂ = (D.t₂ + 1) ⌈/⌉ p) (hr₁pos : 0 < r₁) (hr₂pos : 0 < r₂)
    (tau₁ : NormCharacter F B₁) (htau₁ : tau₁ ≠ 1)
    (tau₂ : NormCharacter F B₂) (htau₂ : tau₂ ≠ 1)
    (Psi : ContinuousAddChar F) (rho : Fˣ)
    (hrho : ord F (rho : F) = ((D.delta : ℤ) : WithTop ℤ))
    (hchart₁ : ∀ z : lattice F (r₁ : ℤ),
      tau₁.1 (positiveUnitOfLattice F hr₁pos (-z)) =
        Psi ((rho : F) * truncatedLog p (z : F)))
    (hchart₂ : ∀ z : lattice F (r₂ : ℤ),
      tau₂.1 (positiveUnitOfLattice F hr₂pos (-z)) = Psi (truncatedLog p (z : F)))
    (c : B₁ˣ) (epsilon : unitFiltration F D.t)
    (hnorm : normUnits F B₁ c = rho * (epsilon : Fˣ))
    (x : lattice B₁ ((D.delta + (D.t + 1) ⌈/⌉ p : ℕ) : ℤ)) :
    normQuasiChar F B₁ tau₂.1
        (positiveUnitOfLattice B₁ (commutator_depths hp hG D).1 (-x)) =
      tracePullbackAddChar F B₁ Psi
        ((1 - algebraMap F B₁ (rho : F) / (c : B₁)) * truncatedLog p (x : B₁)) := by
  obtain ⟨_, hres₁, _, _, _⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  obtain ⟨_, hres₂, _, _, _⟩ := realization_tower_data hp hG hres B₂ D.degree_B₂
  have hdegree : Module.finrank F B₁ = p := D.degree_B₁
  have hodd : Module.finrank F B₁ ≠ 2 := by rw [hdegree]; have := D.odd_prime; omega
  have hPsi := additiveConductor_of_normCharacterChart F B₂ hp D.odd_prime hchar
    D.degree_B₂ D.B₂_breaks.1 (D.t_pos.trans_le D.t_le_t₂) hres₂
    hr₂ hr₂pos tau₂ htau₂ Psi hchart₂
  have hPsiTriv : AddCharTrivialOnLattice F Psi ((D.t₂ + 1 : ℕ) : ℤ) := by
    simpa only [neg_neg] using hPsi.trivial
  let PsiRho : ContinuousAddChar F :=
    Psi.pullback ⟨AddMonoidHom.mulLeft (rho : F), continuous_const_mul (rho : F)⟩
  have hPsiRho := additiveConductor_of_normCharacterChart F B₁ hp D.odd_prime hchar
    hdegree D.B₁_breaks.1 D.t_pos hres₁ hr₁ hr₁pos tau₁ htau₁ PsiRho hchart₁
  have hdepth := trace_depths (d := D.delta) D.odd_prime D.t_pos
  rw [← D.t₂_eq, ← hr₁, ← hr₂] at hdepth
  let q := D.delta + (D.t + 1) ⌈/⌉ p
  have hqpos : 0 < q := (commutator_depths hp hG D).1
  let ux := positiveUnitOfLattice B₁ hqpos (-x)
  have hnormUnit : normUnits F B₁ (ux : B₁ˣ) ∈ unitFiltration F r₂ := by
    apply Models.norm_maps_modelDepth F B₁ D.B₁_breaks.1 hres₁ hr₂pos
      (by simpa only [q, hr₁] using hdepth.2.2.1)
      (by simpa only [q, hdegree, hr₁] using hdepth.2.2.2.1)
    exact ux.property
  have hnormCoe : (normUnits F B₁ (ux : B₁ˣ) : F) =
      norm F B₁ (1 - (x : B₁)) := by simp [ux, sub_eq_add_neg]
  let u : F := 1 - norm F B₁ (1 - (x : B₁))
  have hu : u ∈ lattice F (r₂ : ℤ) := by
    have hd := (mem_unitFiltration_succ_iff_sub_mem_lattice F (r₂ - 1)
      (normUnits F B₁ (ux : B₁ˣ))).1
      (by simpa only [Nat.sub_add_cancel hr₂pos] using hnormUnit)
    rw [Nat.sub_add_cancel hr₂pos, hnormCoe] at hd
    simpa only [u, neg_sub] using neg_mem_lattice F hd
  let ur : lattice F (r₂ : ℤ) := ⟨u, hu⟩
  have huUnit : (positiveUnitOfLattice F hr₂pos (-ur) : Fˣ) =
      normUnits F B₁ (ux : B₁ˣ) := by
    apply Units.ext
    simp only [coe_positiveUnitOfLattice, Submodule.coe_neg, ur]
    rw [hnormCoe]
    simp [u]
  have hchart : normQuasiChar F B₁ tau₂.1 (ux : B₁ˣ) =
      Psi (truncatedLog p u) := by
    change tau₂.1 (normUnits F B₁ (ux : B₁ˣ)) = _
    rw [← huUnit]
    exact hchart₂ ur
  let w := truncatedLog p (x : B₁)
  have hw : w ∈ lattice B₁ (q : ℤ) :=
    (truncatedLogOnLattice B₁ p q
      ((residueCharacteristic_extension_eq F B₁).trans hchar) hqpos x).property
  have hlog := normLog F B₁ D.B₁_breaks.1 D.t_pos hres₁
    (hchar.trans hdegree.symm) hodd D.delta (x : B₁)
    (by simpa only [hdegree] using x.property)
  rw [hdegree, show D.t + 1 + D.delta = D.t₂ + 1 by rw [D.t₂_eq]; omega] at hlog
  have hlogPhase : Psi (truncatedLog p u) =
      Psi (LanglandsFirstMainLemma.trace F B₁ w + norm F B₁ w) := by
    apply div_eq_one.mp
    rw [← additivePhase_sub]
    apply hPsiTriv
    convert hlog using 1
    dsimp only [u, w]
    ring
  have heord : ord F ((epsilon : Fˣ) : F) = 0 :=
    (mem_unitFiltration_zero F _).1
      (unitFiltration_antitone F (Nat.zero_le D.t) epsilon.property)
  have hc : ord B₁ (c : B₁) = ((D.delta : ℤ) : WithTop ℤ) := by
    calc
      ord B₁ (c : B₁) = ord F (normUnits F B₁ c : F) := by
        rw [coe_normUnits, ord_norm, hres₁, one_nsmul]
      _ = _ := by rw [hnorm, Units.val_mul, ord_mul, hrho, heord, add_zero]
  have hwc : w / (c : B₁) ∈ lattice B₁ (r₁ : ℤ) := by
    apply (div_mem_lattice_iff B₁ (c : B₁) w (D.delta : ℤ) (r₁ : ℤ) hc).2
    simpa only [q, ← hr₁, Nat.cast_add] using hw
  have hconversion := (normPhase F B₁ D.B₁_breaks.1 D.t_pos hres₁
    (hchar.trans hdegree.symm) hodd r₁ (by simpa only [hdegree] using hr₁)
    hr₁pos tau₁ htau₁ PsiRho hPsiRho
    (by
      intro z
      change tau₁.1 (positiveUnitOfLattice F hr₁pos (-z)) =
        Psi ((rho : F) * truncatedLog (Module.finrank F B₁) (z : F))
      simpa only [hdegree] using hchart₁ z) (w / (c : B₁)) hwc).1
  have hnc : norm F B₁ (c : B₁) = (rho : F) * ((epsilon : Fˣ) : F) := by
    simpa only [coe_normUnits, Units.val_mul] using congrArg Units.val hnorm
  have hscaled : (rho : F) * norm F B₁ (w / (c : B₁)) =
      norm F B₁ w * (((epsilon : Fˣ) : F)⁻¹) := by
    have hmul : norm F B₁ (w / (c : B₁)) * norm F B₁ (c : B₁) = norm F B₁ w := by
      rw [← map_mul, div_mul_cancel₀ _ (Units.ne_zero c)]
    rw [hnc] at hmul
    calc
      (rho : F) * norm F B₁ (w / (c : B₁)) =
          (norm F B₁ (w / (c : B₁)) * ((rho : F) * ((epsilon : Fˣ) : F))) *
            (((epsilon : Fˣ) : F)⁻¹) := by
              field_simp
      _ = _ := by rw [hmul]
  have heinv : (((epsilon : Fˣ) : F)⁻¹) - 1 ∈ lattice F (D.t : ℤ) := by
    have h := (mem_unitFiltration_succ_iff_sub_mem_lattice F (D.t - 1)
      (epsilon : Fˣ)⁻¹).1 (by
        simpa only [Nat.sub_add_cancel D.t_pos] using
          (unitFiltration F D.t).inv_mem epsilon.property)
    simpa only [Nat.sub_add_cancel D.t_pos, Units.val_inv_eq_inv_val] using h
  have hnw : norm F B₁ w ∈ lattice F (q : ℤ) := by
    rw [mem_lattice, ord_norm, hres₁, one_nsmul]
    exact hw
  have hreplace : Psi (norm F B₁ w) = Psi ((rho : F) * norm F B₁ (w / (c : B₁))) := by
    apply Eq.symm
    apply div_eq_one.mp
    rw [← additivePhase_sub, hscaled, ← mul_sub_one]
    apply hPsiTriv
    apply lattice_antitone F _ (mul_mem_lattice F hnw heinv)
    have h := hdepth.2.2.2.2
    dsimp only [q]
    rw [← hr₁]
    exact_mod_cast h
  have htr (z : B₁) : LanglandsFirstMainLemma.trace F B₁ (algebraMap F B₁ (rho : F) * z) =
      (rho : F) * LanglandsFirstMainLemma.trace F B₁ z := by
    simpa [Algebra.smul_def] using map_smul (LanglandsFirstMainLemma.trace F B₁) (rho : F) z
  have hnormConvert : Psi ((rho : F) * norm F B₁ (w / (c : B₁))) =
      tracePullbackAddChar F B₁ Psi (-(algebraMap F B₁ (rho : F) * (w / (c : B₁)))) := by
    apply div_eq_one.mp
    rw [tracePullbackAddChar_apply, map_neg, htr, ← additivePhase_sub]
    change Psi ((rho : F) *
      (LanglandsFirstMainLemma.trace F B₁ (w / (c : B₁)) + norm F B₁ (w / (c : B₁)))) = 1
      at hconversion
    convert hconversion using 1
    congr 1
    ring
  change normQuasiChar F B₁ tau₂.1 (ux : B₁ˣ) = _
  rw [hchart, hlogPhase, ContinuousAddChar.map_add_eq_mul, hreplace, hnormConvert]
  rw [← tracePullbackAddChar_apply F B₁ Psi w, ← ContinuousAddChar.map_add_eq_mul]
  congr 1
  dsimp only [w]
  ring

/-- Construct the denominator and its permitted norm error from the
genuine diamond data, then evaluate the full shallow-unit formula.
This supplies all auxiliary data used by `trace`. -/
theorem trace_realization
    (r₁ r₂ : ℕ) (hr₁ : r₁ = (D.t + 1) ⌈/⌉ p)
    (hr₂ : r₂ = (D.t₂ + 1) ⌈/⌉ p) (hr₁pos : 0 < r₁) (hr₂pos : 0 < r₂)
    (tau₁ : NormCharacter F B₁) (htau₁ : tau₁ ≠ 1)
    (tau₂ : NormCharacter F B₂) (htau₂ : tau₂ ≠ 1)
    (Psi : ContinuousAddChar F) (rho : Fˣ)
    (hrho : ord F (rho : F) = ((D.delta : ℤ) : WithTop ℤ))
    (hchart₁ : ∀ z : lattice F (r₁ : ℤ),
      tau₁.1 (positiveUnitOfLattice F hr₁pos (-z)) =
        Psi ((rho : F) * truncatedLog p (z : F)))
    (hchart₂ : ∀ z : lattice F (r₂ : ℤ),
      tau₂.1 (positiveUnitOfLattice F hr₂pos (-z)) = Psi (truncatedLog p (z : F))) :
    ∃ (c : B₁ˣ) (epsilon : unitFiltration F D.t),
      normUnits F B₁ c = rho * (epsilon : Fˣ) ∧
      ord B₁ (c : B₁) = ((D.delta : ℤ) : WithTop ℤ) ∧
      ∀ x : lattice B₁ ((D.delta + (D.t + 1) ⌈/⌉ p : ℕ) : ℤ),
        normQuasiChar F B₁ tau₂.1
            (positiveUnitOfLattice B₁ (commutator_depths hp hG D).1 (-x)) =
          tracePullbackAddChar F B₁ Psi
            ((1 - algebraMap F B₁ (rho : F) / (c : B₁)) * truncatedLog p (x : B₁)) := by
  obtain ⟨_, hres₁, _, _, _⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  obtain ⟨c, epsilon, hnorm, hc⟩ :=
    trace_approximateNorm F B₁ D.B₁_breaks.1 hres₁ rho (D.delta : ℤ) hrho
  exact ⟨c, epsilon, hnorm, hc, trace hp hG hres hchar D r₁ r₂ hr₁ hr₂ hr₁pos hr₂pos
    tau₁ htau₁ tau₂ htau₂ Psi rho hrho hchart₁ hchart₂ c epsilon hnorm⟩

end Diamond

end

end LanglandsSecondMainLemma.Odd.R2
