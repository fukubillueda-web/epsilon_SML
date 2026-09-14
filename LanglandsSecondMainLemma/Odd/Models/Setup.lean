import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Odd.Total.ASCoordinate
import LanglandsSecondMainLemma.Basic.Characters
import LanglandsSecondMainLemma.Odd.TruncatedLog

/-!
# Odd / Models / Setup

This file constructs the two characters in Paper (8.1) on their full
principal-unit domains.  The character over the ground field is an actual
nontrivial norm character for `B₂/F`; its supplied truncated-log chart first
forces the exact additive conductor of the chart character.  Trace pullback
then gives the two additive characters in the intermediate fields with their
paper conductors.

For a coefficient `c` of order `-t`, an additive character trivial exactly on
`𝔭^T`, and `m = t + T`, the formula

`u ↦ Ψ (c * P(1-u))`

is multiplicative on `U^q`, where `q = ⌈m/p⌉`.  Its exact unit-filtration
conductor is `m`.  Both assertions use the complete subgroup, not a choice of
representatives modulo its conductor layer.
-/

namespace LanglandsSecondMainLemma.Odd.Models

noncomputable section

open LanglandsFirstMainLemma
open Polynomial

/-- Exact conductor data for a character whose domain is a positive
unit-filtration subgroup.  Minimality ranges over every deeper subgroup on
which the character is defined. -/
structure IsUnitFiltrationConductor
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {q : ℕ} (R : unitFiltration E q →* ℂˣ) (m : ℕ) : Prop where
  domain_le : q ≤ m
  trivial :
    R.comp (Subgroup.inclusion (unitFiltration_antitone E domain_le)) = 1
  minimal : ∀ (r : ℕ) (hqr : q ≤ r),
    R.comp (Subgroup.inclusion (unitFiltration_antitone E hqr)) = 1 → m ≤ r

namespace IsUnitFiltrationConductor

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- The adjacent boundary criterion for a character on `U^q`. -/
theorem of_boundary {q m : ℕ} (R : unitFiltration E q →* ℂˣ)
    (hqm : q ≤ m) (hqpred : q ≤ m - 1)
    (htriv :
      R.comp (Subgroup.inclusion (unitFiltration_antitone E hqm)) = 1)
    (hpred :
      R.comp (Subgroup.inclusion
        (unitFiltration_antitone E hqpred)) ≠ 1) :
    IsUnitFiltrationConductor E R m := by
  refine ⟨hqm, htriv, ?_⟩
  intro r hqr hr
  by_contra hmr
  have hrpred : r ≤ m - 1 := by omega
  apply hpred
  apply MonoidHom.ext
  intro u
  let ur : unitFiltration E r :=
    ⟨(u : Eˣ), unitFiltration_antitone E hrpred u.property⟩
  have hu := DFunLike.congr_fun hr ur
  simp only [MonoidHom.comp_apply, MonoidHom.one_apply] at hu ⊢
  calc
    R ((Subgroup.inclusion (unitFiltration_antitone E hqpred)) u) =
        R ((Subgroup.inclusion (unitFiltration_antitone E hqr)) ur) := by
          congr 1
    _ = 1 := hu

/-- Exactness gives the expected nontriviality on the preceding layer. -/
theorem not_trivialOnPredecessor {q m : ℕ}
    {R : unitFiltration E q →* ℂˣ}
    (hR : IsUnitFiltrationConductor E R m) (hm : 0 < m)
    (hqpred : q ≤ m - 1) :
    R.comp (Subgroup.inclusion
      (unitFiltration_antitone E hqpred)) ≠ 1 := by
  intro h
  have := hR.minimal (m - 1) hqpred h
  omega

end IsUnitFiltrationConductor

/-- The first minimal conductor `m₁ = 1+t+t'`. -/
def firstModelConductor {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} {hp : p.Prime} {hG}
    (D : Total.OddTotalBreakData (F := F) (K := K) hp hG) : ℕ :=
  1 + D.t + D.tPrime

/-- The second minimal conductor `m₂ = 1+t+t₂`. -/
def secondModelConductor {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} {hp : p.Prime} {hG}
    (D : Total.OddTotalBreakData (F := F) (K := K) hp hG) : ℕ :=
  1 + D.t + D.t₂

/-- The full domain depth `q₁ = ⌈m₁/p⌉`. -/
def firstModelDepth {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} {hp : p.Prime} {hG}
    (D : Total.OddTotalBreakData (F := F) (K := K) hp hG) : ℕ :=
  firstModelConductor D ⌈/⌉ p

/-- The full domain depth `q₂ = ⌈m₂/p⌉`. -/
def secondModelDepth {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} {hp : p.Prime} {hG}
    (D : Total.OddTotalBreakData (F := F) (K := K) hp hG) : ℕ :=
  secondModelConductor D ⌈/⌉ p

/-- The proof-bearing pair of the paper's two minimal characters. -/
structure OddMinimalCharacterModels
    (B₁ B₂ : Type*)
    [Field B₁] [ValuativeRel B₁] [TopologicalSpace B₁]
    [IsNonarchimedeanLocalField B₁]
    [Field B₂] [ValuativeRel B₂] [TopologicalSpace B₂]
    [IsNonarchimedeanLocalField B₂]
    (p q₁ m₁ q₂ m₂ : ℕ)
    (Psi₁ : ContinuousAddChar B₁) (Psi₂ : ContinuousAddChar B₂)
    (b : B₁) (a : B₂) where
  R₁ : unitFiltration B₁ q₁ →* ℂˣ
  R₂ : unitFiltration B₂ q₂ →* ℂˣ
  R₁_apply : ∀ u : unitFiltration B₁ q₁,
    R₁ u = Psi₁ (b * truncatedLog p (1 - ((u : B₁ˣ) : B₁)))
  R₂_apply : ∀ u : unitFiltration B₂ q₂,
    R₂ u = Psi₂ (a * truncatedLog p (1 - ((u : B₂ˣ) : B₂)))
  R₁_conductor : IsUnitFiltrationConductor B₁ R₁ m₁
  R₂_conductor : IsUnitFiltrationConductor B₂ R₂ m₂

/-- A reusable one-field construction underlying both `R₁` and `R₂`.
The hypotheses retain the integer order of the coefficient and the whole
additive conductor lattice. -/
private theorem truncatedLogUnitCharacter_exists
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {p q t T m : ℕ} (hp : p.Prime)
    (hchar : residueCharacteristic E = p)
    (ht : 0 < t) (hT : 0 < T) (hm : m = t + T)
    (hq : 0 < q) (hqpred : q ≤ m - 1) (hbound : m ≤ p * q)
    (c : E) (hc : ord E c = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (Psi : ContinuousAddChar E)
    (hPsi : IsAdditiveConductor E Psi (-((T : ℕ) : ℤ))) :
    ∃ R : unitFiltration E q →* ℂˣ,
      (∀ u : unitFiltration E q,
        R u = Psi (c * truncatedLog p (1 - ((u : Eˣ) : E)))) ∧
      IsUnitFiltrationConductor E R m := by
  classical
  have hqm : q ≤ m := hqpred.trans (Nat.sub_le m 1)
  have hmpos : 0 < m := by rw [hm]; omega
  have hcMem : c ∈ lattice E (-(t : ℤ)) := by
    rw [mem_lattice, hc]
  let R : unitFiltration E q →* ℂˣ :=
    { toFun := fun u ↦ Psi (c * truncatedLog p (1 - ((u : Eˣ) : E)))
      map_one' := by
        change Psi (c * truncatedLog p (1 - (1 : E))) = 1
        rw [truncatedLog_apply]
        simp only [sub_self, zero_add]
        have hsum : ∑ j ∈ Finset.Ico 2 p, (0 : E) ^ j / (j : E) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          rw [zero_pow (by have := (Finset.mem_Ico.mp hj).1; omega), zero_div]
        rw [hsum, mul_zero]
        exact ContinuousAddChar.map_zero_eq_one Psi
      map_mul' := by
        intro u v
        let z : E := 1 - ((u : Eˣ) : E)
        let w : E := 1 - ((v : Eˣ) : E)
        have huDisp : ((u : Eˣ) : E) - 1 ∈ lattice E (q : ℤ) := by
          have hu := (mem_unitFiltration_succ_iff_sub_mem_lattice E (q - 1)
            (u : Eˣ)).1 (by
              simpa only [Nat.sub_add_cancel hq] using u.property)
          simpa only [Nat.sub_add_cancel hq] using hu
        have hvDisp : ((v : Eˣ) : E) - 1 ∈ lattice E (q : ℤ) := by
          have hv := (mem_unitFiltration_succ_iff_sub_mem_lattice E (q - 1)
            (v : Eˣ)).1 (by
              simpa only [Nat.sub_add_cancel hq] using v.property)
          simpa only [Nat.sub_add_cancel hq] using hv
        have hz : z ∈ lattice E (q : ℤ) := by
          simpa only [z, neg_sub] using neg_mem_lattice E huDisp
        have hw : w ∈ lattice E (q : ℤ) := by
          simpa only [w, neg_sub] using neg_mem_lattice E hvDisp
        have hdefect :=
          truncatedLog_defect_mem_lattice E p q hchar hp hz hw
        have hcdefect :
            c * (truncatedLog p (z + w - z * w) -
              truncatedLog p z - truncatedLog p w) ∈
                lattice E (T : ℤ) := by
          have hdepth : (T : ℤ) ≤ -(t : ℤ) + (p * q : ℕ) := by
            rw [hm] at hbound
            exact_mod_cast (show T ≤ -(t : ℤ) + (p * q : ℕ) by omega)
          exact lattice_antitone E hdepth
            (mul_mem_lattice E hcMem hdefect)
        have hphase :
            Psi (c * (truncatedLog p (z + w - z * w) -
              truncatedLog p z - truncatedLog p w)) = 1 := by
          exact hPsi.trivial _ (by simpa only [neg_neg] using hcdefect)
        change Psi (c * truncatedLog p
            (1 - (((u * v : unitFiltration E q) : Eˣ) : E))) =
          Psi (c * truncatedLog p (1 - ((u : Eˣ) : E))) *
            Psi (c * truncatedLog p (1 - ((v : Eˣ) : E)))
        have harg : 1 - (((u * v : unitFiltration E q) : Eˣ) : E) =
            z + w - z * w := by
          dsimp only [z, w]
          change 1 - (((u : Eˣ) : E) * ((v : Eˣ) : E)) = _
          ring
        rw [harg]
        have hdecomp :
            c * truncatedLog p (z + w - z * w) =
              c * (truncatedLog p (z + w - z * w) -
                truncatedLog p z - truncatedLog p w) +
                (c * truncatedLog p z + c * truncatedLog p w) := by ring
        rw [hdecomp, ContinuousAddChar.map_add_eq_mul, hphase, one_mul,
          ContinuousAddChar.map_add_eq_mul]
        }
  refine ⟨R, fun _ ↦ rfl, ?_⟩
  have htriv :
      R.comp (Subgroup.inclusion (unitFiltration_antitone E hqm)) = 1 := by
    apply MonoidHom.ext
    intro u
    simp only [MonoidHom.comp_apply, MonoidHom.one_apply]
    change Psi (c * truncatedLog p (1 - ((u : Eˣ) : E))) = 1
    have huDisp : ((u : Eˣ) : E) - 1 ∈ lattice E (m : ℤ) := by
      have hu := (mem_unitFiltration_succ_iff_sub_mem_lattice E (m - 1)
        (u : Eˣ)).1 (by
          simpa only [Nat.sub_add_cancel hmpos] using u.property)
      simpa only [Nat.sub_add_cancel hmpos] using hu
    have hz : 1 - ((u : Eˣ) : E) ∈ lattice E (m : ℤ) := by
      simpa only [neg_sub] using neg_mem_lattice E huDisp
    have hzOne : 1 - ((u : Eˣ) : E) ∈ lattice E 1 :=
      lattice_antitone E (by exact_mod_cast (show 1 ≤ m by omega)) hz
    have hPz : truncatedLog p (1 - ((u : Eˣ) : E)) ∈ lattice E (m : ℤ) := by
      rw [mem_lattice, ord_truncatedLog E p hchar hzOne]
      exact hz
    have hcP : c * truncatedLog p (1 - ((u : Eˣ) : E)) ∈ lattice E (T : ℤ) := by
      have hdepth : -(t : ℤ) + (m : ℤ) = (T : ℤ) := by
        rw [hm]
        push_cast
        ring
      simpa only [hdepth] using mul_mem_lattice E hcMem hPz
    exact hPsi.trivial _ (by simpa only [neg_neg] using hcP)
  have hpred :
      R.comp (Subgroup.inclusion
        (unitFiltration_antitone E hqpred)) ≠ 1 := by
    obtain ⟨y, hyord, hyne⟩ := hPsi.exists_ord_eq_predecessor
    have hcne : c ≠ 0 :=
      (ord_ne_top_iff E).1 (hc.trans_ne WithTop.coe_ne_top)
    let w : E := c⁻¹ * y
    have hword : ord E w = (((m - 1 : ℕ) : ℤ) : WithTop ℤ) := by
      dsimp only [w]
      rw [ord_mul, ord_inv, hc, hyord]
      simp only [neg_neg]
      rw [show m - 1 = t + T - 1 by rw [hm]]
      rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add]
      congr 1
      rw [Nat.cast_sub (by omega : 1 ≤ t + T)]
      push_cast
      ring
    have hw : w ∈ lattice E ((m - 1 : ℕ) : ℤ) := by
      rw [mem_lattice, hword]
    have hpredpos : 0 < m - 1 := by rw [hm]; omega
    obtain ⟨z, hz⟩ :=
      (truncatedLogOnLattice_bijective E p (m - 1) hchar hp hpredpos).2
        (⟨w, hw⟩ : lattice E ((m - 1 : ℕ) : ℤ))
    have hPz : truncatedLog p (z : E) = w := congrArg Subtype.val hz
    let uPred : unitFiltration E (m - 1) :=
      positiveUnitOfLattice E hpredpos (-z)
    let uQ : unitFiltration E q :=
      ⟨(uPred : Eˣ), unitFiltration_antitone E hqpred uPred.property⟩
    have hRne : R uQ ≠ 1 := by
      intro hR
      apply hyne
      calc
        Psi y = Psi (c * truncatedLog p (z : E)) := by
          congr 1
          rw [hPz]
          dsimp only [w]
          field_simp
        _ = R uQ := by
          change Psi (c * truncatedLog p (z : E)) =
            Psi (c * truncatedLog p (1 - ((uQ : Eˣ) : E)))
          congr 2
          dsimp only [uQ, uPred]
          simp
        _ = 1 := hR
    intro hEq
    apply hRne
    have hv := DFunLike.congr_fun hEq uPred
    simp only [MonoidHom.comp_apply, MonoidHom.one_apply] at hv
    calc
      R uQ = R ((Subgroup.inclusion
          (unitFiltration_antitone E hqpred)) uPred) := by
            congr 1
      _ = 1 := hv
  exact IsUnitFiltrationConductor.of_boundary R hqm hqpred htriv hpred

/-- At the ceiling depth, the one-field construction's domain bounds follow
from positivity of the coefficient depth and additive conductor depth. -/
private theorem truncatedLogUnitCharacter_ceilDepth_exists
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {p t T m : ℕ} (hp : p.Prime)
    (hchar : residueCharacteristic E = p)
    (ht : 0 < t) (hT : 0 < T) (hm : m = t + T)
    (c : E) (hc : ord E c = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (Psi : ContinuousAddChar E)
    (hPsi : IsAdditiveConductor E Psi (-((T : ℕ) : ℤ))) :
    ∃ R : unitFiltration E (m ⌈/⌉ p) →* ℂˣ,
      (∀ u : unitFiltration E (m ⌈/⌉ p),
        R u = Psi (c * truncatedLog p (1 - ((u : Eˣ) : E)))) ∧
      IsUnitFiltrationConductor E R m := by
  have hmpos : 2 ≤ m := by omega
  have hbound : m ≤ p * (m ⌈/⌉ p) := (ceilDiv_le_iff_le_mul hp.pos).1 le_rfl
  have hqpos : 0 < m ⌈/⌉ p := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero, mul_zero] at hbound
    omega
  have hqpred : m ⌈/⌉ p ≤ m - 1 := by
    rw [ceilDiv_le_iff_le_mul hp.pos]
    calc
      m ≤ 2 * (m - 1) := by omega
      _ ≤ p * (m - 1) := Nat.mul_le_mul_right _ hp.two_le
  exact truncatedLogUnitCharacter_exists E hp hchar ht hT hm
    hqpos hqpred hbound c hc Psi hPsi

/-- A truncated-log chart for a nontrivial actual norm character forces the
chart's additive character to have the same exact boundary ideal. -/
private theorem additiveConductor_of_normCharacterChart
    (F E : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Free F E] [Module.Finite F E] [PrimeCyclicExtension F E]
    {p t q : ℕ} (hp : p.Prime) (hodd : 2 < p)
    (hchar : residueCharacteristic F = p)
    (hdegree : Module.finrank F E = p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
    (hres : residueDegree F E = 1)
    (hq : q = (t + 1) ⌈/⌉ p) (hqpos : 0 < q)
    (tau : NormCharacter F E) (htau : tau ≠ 1)
    (Psi : ContinuousAddChar F)
    (hchart : ∀ x : lattice F (q : ℤ),
      tau.1 (positiveUnitOfLattice F hqpos (-x)) =
        Psi (truncatedLog p (x : F))) :
    IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)) := by
  classical
  have hqle : q ≤ t := by
    rw [hq, ceilDiv_le_iff_le_mul hp.pos]
    have hp3 : 3 ≤ p := by omega
    calc
      t + 1 ≤ 3 * t := by omega
      _ ≤ p * t := Nat.mul_le_mul_right t hp3
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have hTau : IsMultiplicativeConductor F tau.1 (t + 1) :=
    ramifiedNormCharacter_conductor F E ht hres pi hpi hgen tau htau
  have hPsiTrivial :
      AddCharTrivialOnLattice F Psi ((t + 1 : ℕ) : ℤ) := by
    intro y hy
    obtain ⟨z, hz⟩ :=
      (truncatedLogOnLattice_bijective F p (t + 1) hchar hp (by omega)).2
        (⟨y, hy⟩ : lattice F ((t + 1 : ℕ) : ℤ))
    have hPz : truncatedLog p (z : F) = y := congrArg Subtype.val hz
    let zq : lattice F (q : ℤ) :=
      ⟨(z : F), lattice_antitone F (by exact_mod_cast hqle.trans (Nat.le_succ t))
        z.property⟩
    let uq : unitFiltration F q := positiveUnitOfLattice F hqpos (-zq)
    let uT : unitFiltration F (t + 1) :=
      positiveUnitOfLattice F (by omega) (-z)
    have hu : (uq : Fˣ) = (uT : Fˣ) := by
      apply Units.ext
      change 1 + -(z : F) = 1 + -(z : F)
      rfl
    calc
      Psi y = Psi (truncatedLog p (zq : F)) := by rw [hPz]
      _ = tau.1 uq := (hchart zq).symm
      _ = tau.1 uT := congrArg tau.1 hu
      _ = 1 := hTau.trivial (uT : Fˣ) uT.property
  have hPsiNontrivial :
      ¬ AddCharTrivialOnLattice F Psi (t : ℤ) := by
    intro htriv
    apply hTau.not_trivialOnPredecessor
    intro u hu
    have huDisp : (u : F) - 1 ∈ lattice F (t : ℤ) := by
      have hu' := (mem_unitFiltration_succ_iff_sub_mem_lattice F (t - 1) u).1
        (by simpa only [Nat.sub_add_cancel htpos] using hu)
      simpa only [Nat.sub_add_cancel htpos] using hu'
    let x : F := 1 - (u : F)
    have hx : x ∈ lattice F (t : ℤ) := by
      simpa only [x, neg_sub] using neg_mem_lattice F huDisp
    let xq : lattice F (q : ℤ) :=
      ⟨x, lattice_antitone F (by exact_mod_cast hqle) hx⟩
    have hxOne : x ∈ lattice F 1 :=
      lattice_antitone F (by exact_mod_cast htpos) hx
    have hPx : truncatedLog p x ∈ lattice F (t : ℤ) := by
      rw [mem_lattice, ord_truncatedLog F p hchar hxOne]
      exact hx
    have hunit : (positiveUnitOfLattice F hqpos (-xq) : Fˣ) = u := by
      apply Units.ext
      simp [xq, x]
    calc
      tau.1 u = tau.1 (positiveUnitOfLattice F hqpos (-xq) : Fˣ) :=
        congrArg tau.1 hunit.symm
      _ = Psi (truncatedLog p (xq : F)) := hchart xq
      _ = 1 := htriv _ (by simpa only [xq] using hPx)
  apply IsAdditiveConductor.of_boundary
  · simpa only [neg_neg] using hPsiTrivial
  · have hdepth : -(-((t + 1 : ℕ) : ℤ)) - 1 = (t : ℤ) := by
      push_cast
      omega
    rw [hdepth]
    exact hPsiNontrivial

/-- Multiplicativity of residue degrees for an actual intermediate local
field, with the canonical valuation and topology installed. -/
private theorem residueDegree_mul_intermediate
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (L : IntermediateField F K) :
    letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
    letI : TopologicalSpace L := Basic.intermediateFieldTopology L
    letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
    letI : ValuativeExtension F L :=
      Basic.intermediateField_lowerValuativeExtension L
    letI : ValuativeExtension L K :=
      Basic.intermediateField_upperValuativeExtension L
    residueDegree F L * residueDegree L K = residueDegree F K := by
  letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
  letI : TopologicalSpace L := Basic.intermediateFieldTopology L
  letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
  letI : ValuativeExtension F L :=
    Basic.intermediateField_lowerValuativeExtension L
  letI : ValuativeExtension L K :=
    Basic.intermediateField_upperValuativeExtension L
  letI : IsScalarTower
      (ringOfIntegers F) (ringOfIntegers L) (ringOfIntegers K) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap F K (x : F) = algebraMap L K (algebraMap F L (x : F))
      rw [← IsScalarTower.algebraMap_apply F L K])
  letI : IsLocalHom
      (algebraMap (ringOfIntegers F) (ringOfIntegers L)) := inferInstance
  letI : IsLocalHom
      (algebraMap (ringOfIntegers L) (ringOfIntegers K)) := inferInstance
  rw [residueDegree_eq_finrank_residueField,
    residueDegree_eq_finrank_residueField,
    residueDegree_eq_finrank_residueField]
  exact Module.finrank_mul_finrank
    (ResidueField F) (ResidueField L) (ResidueField K)

/-- For odd prime degree, an exact Artin--Schreier coordinate has lower
coefficient equal to its field norm.  This keeps the paper's choice
`a = N₂(Δ)`, rather than retaining only the polynomial equation. -/
private theorem norm_artinSchreierCoordinate
    (E L : Type*) [Field E] [Field L]
    [Algebra E L] [Module.Free E L] [Module.Finite E L]
    {p : ℕ} (hp : p.Prime) (hodd : 2 < p)
    (hdegree : Module.finrank E L = p)
    (Δ : L) (a : E)
    (hroot : Δ ^ p - Δ = algebraMap E L a)
    (hgen : Algebra.adjoin E ({Δ} : Set L) = ⊤) :
    norm E L Δ = a := by
  let f : E[X] := X ^ p - X - C a
  have hp0 : p ≠ 0 := hp.ne_zero
  have hauxDegree : (X + C a : E[X]).degree < (X ^ p : E[X]).degree := by
    rw [degree_X_pow]
    calc
      (X + C a : E[X]).degree ≤ 1 := by
        simp
      _ < (p : WithBot ℕ) := by exact_mod_cast hp.one_lt
  have hfmonic : f.Monic := by
    have h := (monic_X_pow p).sub_of_left hauxDegree
    simpa only [f, sub_sub] using h
  have hfDegree : f.natDegree = p := by
    have hauxNatDegree :
        (X + C a : E[X]).natDegree < (X ^ p : E[X]).natDegree := by
      rw [natDegree_X_pow]
      calc
        (X + C a : E[X]).natDegree ≤ 1 := by
          exact (natDegree_add_le _ _).trans
            (max_le (by simp) (by simp))
        _ < p := hp.one_lt
    have h := natDegree_sub_eq_left_of_natDegree_lt hauxNatDegree
    rw [natDegree_X_pow] at h
    simpa only [f, sub_sub] using h
  have hi : IsIntegral E Δ := Algebra.IsIntegral.isIntegral Δ
  have hfeval : (aeval Δ) f = 0 := by
    simp only [f, map_sub, map_pow, aeval_X, aeval_C]
    rw [hroot]
    exact sub_self _
  have hfDvd : minpoly E Δ ∣ f := minpoly.dvd E Δ hfeval
  let pb : PowerBasis E L := PowerBasis.ofAdjoinEqTop hi hgen
  have hminDegree : (minpoly E Δ).natDegree = p := by
    calc
      (minpoly E Δ).natDegree = pb.dim := by
        simpa only [pb, PowerBasis.ofAdjoinEqTop_gen] using
          pb.natDegree_minpoly
      _ = Module.finrank E L := pb.finrank.symm
      _ = p := hdegree
  have hmin : minpoly E Δ = f := by
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic hi) hfmonic hfDvd (by rw [hfDegree, hminDegree])).symm
  calc
    norm E L Δ = norm E L pb.gen := by
      rw [PowerBasis.ofAdjoinEqTop_gen]
    _ = (-1 : E) ^ pb.dim * (minpoly E pb.gen).coeff 0 :=
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
    _ = a := by
      have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
      have hpbdim : pb.dim = p := by rw [← pb.finrank, hdegree]
      rw [PowerBasis.ofAdjoinEqTop_gen, hmin, hpbdim, hpOdd.neg_one_pow]
      simp [f, hp0.symm]

section MinimalCharacters

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]
  {p : ℕ} (hp : p.Prime)
  (hG : Nonempty
    (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
  (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
  (D : Total.OddTotalBreakData (F := F) (K := K) hp hG)

-- Reuse the canonical intermediate-field structures from the public statement.
attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

local notation "B₁" => D.B₁
local notation "B₂" => D.B₂

include hres hchar in
/-- The actual lower norm-character chart determines both exact trace-pullback
conductors in Paper (8.1). -/
private theorem minimalCharacters_additiveConductors
    (q₀ : ℕ) (hq₀ : q₀ = (D.t₂ + 1) ⌈/⌉ p) (hq₀pos : 0 < q₀)
    (tau : NormCharacter F B₂) (htau : tau ≠ 1)
    (PsiF : ContinuousAddChar F)
    (hchart : ∀ x : lattice F (q₀ : ℤ),
      tau.1 (positiveUnitOfLattice F hq₀pos (-x)) =
        PsiF (truncatedLog p (x : F))) :
    IsAdditiveConductor B₁ (tracePullbackAddChar F B₁ PsiF)
        (-((D.tPrime + 1 : ℕ) : ℤ)) ∧
      IsAdditiveConductor B₂ (tracePullbackAddChar F B₂ PsiF)
        (-((D.t₂ + 1 : ℕ) : ℤ)) := by
  let E₁ := Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁
  let E₂ := Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
  letI : PrimeCyclicExtension F B₁ :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F B₁ E₁.2.2.2.2.2.2.2.2.2.2.2.1
  letI : PrimeCyclicExtension F B₂ :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F B₂ E₂.2.2.2.2.2.2.2.2.2.2.2.1
  have hresF₁ : residueDegree F B₁ = 1 :=
    (mul_eq_one.mp ((residueDegree_mul_intermediate B₁).trans hres)).1
  have hresF₂ : residueDegree F B₂ = 1 :=
    (mul_eq_one.mp ((residueDegree_mul_intermediate B₂).trans hres)).1
  have hbreakF₁ : PrimeCyclicExtension.IsLowerBreak F B₁ D.t := D.B₁_breaks.1
  have hbreakF₂ : PrimeCyclicExtension.IsLowerBreak F B₂ D.t₂ := D.B₂_breaks.1
  have hdegreeF₁ : Module.finrank F B₁ = p := D.degree_B₁
  have hdegreeF₂ : Module.finrank F B₂ = p := D.degree_B₂
  have hPsiF := additiveConductor_of_normCharacterChart F B₂ hp D.odd_prime hchar
    D.degree_B₂ hbreakF₂ (D.t_pos.trans_le D.t_le_t₂) hresF₂
    hq₀ hq₀pos tau htau PsiF hchart
  obtain ⟨pi₁, hpi₁, hgen₁⟩ := monogenicUniformizer F B₁ hresF₁
  obtain ⟨pi₂, hpi₂, hgen₂⟩ := monogenicUniformizer F B₂ hresF₂
  have hPsi₁ := additiveConductor_compTrace_cyclicPrime F B₁
    hbreakF₁ hresF₁ pi₁ hpi₁ hgen₁ hPsiF
  have hPsi₂ := additiveConductor_compTrace_cyclicPrime F B₂
    hbreakF₂ hresF₂ pi₂ hpi₂ hgen₂ hPsiF
  have hcondEq₁ :
      (p : ℤ) * (-((D.t₂ + 1 : ℕ) : ℤ)) +
          (((p - 1) * (D.t + 1) : ℕ) : ℤ) =
        -((D.tPrime + 1 : ℕ) : ℤ) := by
    norm_num [D.t₂_eq, D.tPrime_eq, Nat.cast_sub hp.one_le]
    ring
  have hcondEq₂ :
      (p : ℤ) * (-((D.t₂ + 1 : ℕ) : ℤ)) +
          (((p - 1) * (D.t₂ + 1) : ℕ) : ℤ) =
        -((D.t₂ + 1 : ℕ) : ℤ) := by
    norm_num [Nat.cast_sub hp.one_le]
    ring
  constructor
  · rw [show tracePullbackAddChar F B₁ PsiF = PsiF.compTrace from rfl]
    simpa only [hdegreeF₁, hcondEq₁] using hPsi₁
  · rw [show tracePullbackAddChar F B₂ PsiF = PsiF.compTrace from rfl]
    simpa only [hdegreeF₂, hcondEq₂] using hPsi₂

include hres hchar in
/-- Complete the Artin--Schreier coordinate with its two actual norm
coefficients and their orders in the respective intermediate fields. -/
private theorem minimalCharacters_normCoefficients :
    ∃ (Δ : K) (a : B₂) (b : B₁),
      Δ ^ p - Δ = algebraMap B₂ K a ∧
      ord K Δ = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ¬ p ∣ D.t ∧
      Algebra.adjoin B₂ ({Δ} : Set K) = ⊤ ∧
      a = norm B₂ K Δ ∧
      b = norm B₁ K Δ ∧
      ord B₁ b = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) := by
  obtain ⟨Δ, a, hroot, hΔ, ha, hprime, hgen⟩ :=
    Total.aSCoordinate hp hG hres hchar D
  have hdegree₂K : Module.finrank B₂ K = p :=
    (Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂).2.2.2.2.2.2.2.2.2.2.1
  have hnorm₂ : a = norm B₂ K Δ :=
    (norm_artinSchreierCoordinate B₂ K hp D.odd_prime hdegree₂K
      Δ a hroot hgen).symm
  have hres₁K : residueDegree B₁ K = 1 :=
    (mul_eq_one.mp ((residueDegree_mul_intermediate B₁).trans hres)).2
  refine ⟨Δ, a, norm B₁ K Δ, hroot, hΔ, ha, hprime, hgen, hnorm₂, rfl, ?_⟩
  rw [ord_norm, hres₁K, one_nsmul, hΔ]

include hchar in
/-- Apply the one-field construction to both norm coefficients on the full
ceiling-depth domains and package their exact conductors. -/
private theorem minimalCharacters_models
    (PsiF : ContinuousAddChar F) (b : B₁) (a : B₂)
    (hb : ord B₁ b = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (ha : ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hPsi₁ : IsAdditiveConductor B₁ (tracePullbackAddChar F B₁ PsiF)
      (-((D.tPrime + 1 : ℕ) : ℤ)))
    (hPsi₂ : IsAdditiveConductor B₂ (tracePullbackAddChar F B₂ PsiF)
      (-((D.t₂ + 1 : ℕ) : ℤ))) :
    Nonempty (OddMinimalCharacterModels B₁ B₂ p
      (firstModelDepth D) (firstModelConductor D)
      (secondModelDepth D) (secondModelConductor D)
      (tracePullbackAddChar F B₁ PsiF) (tracePullbackAddChar F B₂ PsiF) b a) := by
  have hchar₁ : residueCharacteristic B₁ = p :=
    (residueCharacteristic_extension_eq F B₁).trans hchar
  have hchar₂ : residueCharacteristic B₂ = p :=
    (residueCharacteristic_extension_eq F B₂).trans hchar
  have hm₁ : firstModelConductor D = D.t + (D.tPrime + 1) := by
    simp only [firstModelConductor]
    omega
  have hm₂ : secondModelConductor D = D.t + (D.t₂ + 1) := by
    simp only [secondModelConductor]
    omega
  obtain ⟨R₁, hR₁, hR₁cond⟩ := truncatedLogUnitCharacter_ceilDepth_exists B₁ hp
    hchar₁ D.t_pos (Nat.succ_pos _) hm₁ b hb (tracePullbackAddChar F B₁ PsiF) hPsi₁
  obtain ⟨R₂, hR₂, hR₂cond⟩ := truncatedLogUnitCharacter_ceilDepth_exists B₂ hp
    hchar₂ D.t_pos (Nat.succ_pos _) hm₂ a ha (tracePullbackAddChar F B₂ PsiF) hPsi₂
  exact ⟨{
    R₁ := R₁
    R₂ := R₂
    R₁_apply := hR₁
    R₂_apply := hR₂
    R₁_conductor := hR₁cond
    R₂_conductor := hR₂cond }⟩

end MinimalCharacters

/-- **Odd minimal characters on their full unit domains** (Paper (8.1)).

Starting from the actual lower norm character `tau : S(B₂/F)` and its
truncated-log duality chart, this theorem constructs the exact
Artin--Schreier coordinate `Δ`, its two coefficients `a=N₂(Δ)` and
`b=N₁(Δ)`,
and the two genuine group homomorphisms

`R₁ : U_{B₁}^{⌈(1+t+t')/p⌉} →* ℂˣ`,
`R₂ : U_{B₂}^{⌈(1+t+t₂)/p⌉} →* ℂˣ`.

Their evaluation fields are the literal formulas
`R₁(1-z)=Ψ₁(b P(z))` and `R₂(1-z)=Ψ₂(a P(z))`, and their
proof-bearing conductors are exactly `1+t+t'` and `1+t+t₂`. -/
theorem oddMinimalCharacters_onUnits
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = p)
    (D : Total.OddTotalBreakData (F := F) (K := K) hp hG) :
    let B₁ := D.B₁
    let B₂ := D.B₂
    letI : ValuativeRel B₁ := Basic.intermediateFieldValuativeRel B₁
    letI : TopologicalSpace B₁ := Basic.intermediateFieldTopology B₁
    letI : ValuativeRel B₂ := Basic.intermediateFieldValuativeRel B₂
    letI : TopologicalSpace B₂ := Basic.intermediateFieldTopology B₂
    let E₁ := Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁
    let E₂ := Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
    letI : IsNonarchimedeanLocalField B₁ :=
      Basic.intermediateField_localField B₁
    letI : Module.Free F B₁ := E₁.2.1
    letI : Module.Finite F B₁ := E₁.2.2.1
    letI : Module.Free B₁ K := E₁.2.2.2.1
    letI : Module.Finite B₁ K := E₁.2.2.2.2.1
    letI : IsScalarTower F B₁ K := E₁.2.2.2.2.2.1
    letI : ValuativeExtension F B₁ :=
      Basic.intermediateField_lowerValuativeExtension B₁
    letI : ValuativeExtension B₁ K :=
      Basic.intermediateField_upperValuativeExtension B₁
    letI : CyclicPrimeExtension F B₁ := E₁.2.2.2.2.2.2.2.2.2.2.2.1
    letI : IsNonarchimedeanLocalField B₂ :=
      Basic.intermediateField_localField B₂
    letI : Module.Free F B₂ := E₂.2.1
    letI : Module.Finite F B₂ := E₂.2.2.1
    letI : Module.Free B₂ K := E₂.2.2.2.1
    letI : Module.Finite B₂ K := E₂.2.2.2.2.1
    letI : IsScalarTower F B₂ K := E₂.2.2.2.2.2.1
    letI : ValuativeExtension F B₂ :=
      Basic.intermediateField_lowerValuativeExtension B₂
    letI : ValuativeExtension B₂ K :=
      Basic.intermediateField_upperValuativeExtension B₂
    letI : CyclicPrimeExtension F B₂ := E₂.2.2.2.2.2.2.2.2.2.2.2.1
    ∀ (q₀ : ℕ) (hq₀ : q₀ = (D.t₂ + 1) ⌈/⌉ p) (hq₀pos : 0 < q₀)
      (tau : NormCharacter F B₂) (htau : tau ≠ 1)
      (PsiF : ContinuousAddChar F)
      (hchart : ∀ x : lattice F (q₀ : ℤ),
        tau.1 (positiveUnitOfLattice F hq₀pos (-x)) =
          PsiF (truncatedLog p (x : F))),
      ∃ (Δ : K) (a : B₂) (b : B₁),
        Δ ^ p - Δ = algebraMap B₂ K a ∧
        ord K Δ = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
        ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
        ¬ p ∣ D.t ∧
        Algebra.adjoin B₂ ({Δ} : Set K) = ⊤ ∧
        a = norm B₂ K Δ ∧
        b = norm B₁ K Δ ∧
        ord B₁ b = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
        IsAdditiveConductor B₁ (tracePullbackAddChar F B₁ PsiF)
          (-((D.tPrime + 1 : ℕ) : ℤ)) ∧
        IsAdditiveConductor B₂ (tracePullbackAddChar F B₂ PsiF)
          (-((D.t₂ + 1 : ℕ) : ℤ)) ∧
        Nonempty (OddMinimalCharacterModels B₁ B₂ p
          (firstModelDepth D) (firstModelConductor D)
          (secondModelDepth D) (secondModelConductor D)
          (tracePullbackAddChar F B₁ PsiF)
          (tracePullbackAddChar F B₂ PsiF) b a) := by
  dsimp only
  letI : ValuativeRel D.B₁ := Basic.intermediateFieldValuativeRel D.B₁
  letI : TopologicalSpace D.B₁ := Basic.intermediateFieldTopology D.B₁
  letI : ValuativeRel D.B₂ := Basic.intermediateFieldValuativeRel D.B₂
  letI : TopologicalSpace D.B₂ := Basic.intermediateFieldTopology D.B₂
  letI : IsNonarchimedeanLocalField D.B₁ := Basic.intermediateField_localField D.B₁
  letI : IsNonarchimedeanLocalField D.B₂ := Basic.intermediateField_localField D.B₂
  letI : ValuativeExtension F D.B₁ := Basic.intermediateField_lowerValuativeExtension D.B₁
  letI : ValuativeExtension F D.B₂ := Basic.intermediateField_lowerValuativeExtension D.B₂
  intro q₀ hq₀ hq₀pos tau htau PsiF hchart
  obtain ⟨hPsi₁, hPsi₂⟩ := minimalCharacters_additiveConductors hp hG hres hchar D
    q₀ hq₀ hq₀pos tau htau PsiF hchart
  obtain ⟨Δ, a, b, hroot, hΔ, ha, hprime, hgen, hnorm₂, hnorm₁, hb⟩ :=
    minimalCharacters_normCoefficients hp hG hres hchar D
  exact ⟨Δ, a, b, hroot, hΔ, ha, hprime, hgen, hnorm₂, hnorm₁, hb, hPsi₁, hPsi₂,
    minimalCharacters_models hp hG hchar D PsiF b a hb ha hPsi₁ hPsi₂⟩

end

end LanglandsSecondMainLemma.Odd.Models
