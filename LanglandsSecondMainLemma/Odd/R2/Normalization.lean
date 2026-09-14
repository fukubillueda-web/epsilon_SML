import LanglandsSecondMainLemma.Odd.R2.Reciprocal

/-!
# Odd / R2 / Normalization

Paper Proposition 8.13 (`O:R:normalize`), with the setup at lines 2782--2810.
The two actual norm characters are compared on their entire critical unit
layer. In the one-break case the integral numerators in `O:R:reciprocal`
cover that layer, using residue degree one and the truncated-logarithm
bijection and isometry. FML's norm-filtration join then gives global equality.
-/

namespace LanglandsSecondMainLemma.Odd.R2

noncomputable section
open LanglandsFirstMainLemma
set_option backward.isDefEq.respectTransparency false

open private additivePhase_sub from LanglandsSecondMainLemma.Odd.Models.TwistFormula

section CriticalLayer
variable (E L : Type) [Field E] [Field L]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra E L] [ValuativeExtension E L] [Module.Finite E L]
  [PrimeCyclicExtension E L]

/-- Agreement on the whole last nonzero unit subgroup determines a norm
character. This uses the norm-filtration join, without choosing a generator. -/
private theorem normalization_ext {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak E L t) (hres : residueDegree E L = 1)
    (mu nu : NormCharacter E L)
    (heq : ∀ u : unitFiltration E t, mu.1 u = nu.1 u) : mu = nu := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer E L hres
  apply div_eq_one.mp
  apply NormCharacter.eq_one_of_trivialOn_break E L ht hres pi hpi hgen
  intro u hu
  change mu.1 u / nu.1 u = 1
  exact div_eq_one.mpr (heq ⟨u, hu⟩)

end CriticalLayer

section ResidueLift
variable (F E : Type) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]

/-- Every class of the entire critical ideal has the paper's numerator
`Y/b`, with `Y` integral in the base field and the actual denominator `b`. -/
private theorem normalization_lift (hres : residueDegree F E = 1)
    (t : ℤ) (b : E) (hb : ord E b = (-t : WithTop ℤ))
    (x : E) (hx : x ∈ lattice E t) :
    ∃ Y : ringOfIntegers F,
      algebraMap F E (Y : F) / b ∈ lattice E t ∧
      x - algebraMap F E (Y : F) / b ∈ lattice E (t + 1) := by
  have hbne : b ≠ 0 := (ord_ne_top_iff E).1 (by rw [hb]; exact WithTop.coe_ne_top)
  have hxb : x * b ∈ lattice E 0 := by
    simpa using mul_mem_lattice E hx ((mem_lattice E).2 hb.ge)
  let xb : ringOfIntegers E := ⟨x * b, (mem_lattice_zero_iff E).1 hxb⟩
  obtain ⟨Y, hY⟩ :=
    exists_ringOfIntegers_sub_mem_maximalIdeal_of_residueDegree_eq_one F E hres xb
  have herr : x * b - algebraMap F E (Y : F) ∈ lattice E 1 := by
    exact (mem_lattice_one_iff_mem_maximalIdeal E _).2 hY
  have hquot : x - algebraMap F E (Y : F) / b ∈ lattice E (t + 1) := by
    have h := (div_mem_lattice_iff E b (x * b - algebraMap F E (Y : F))
      (-t) (t + 1) hb).2 (by simpa using herr)
    simpa only [sub_div, mul_div_cancel_right₀ _ hbne] using h
  refine ⟨Y, ?_, hquot⟩
  have h := (lattice E t).sub_mem hx (lattice_antitone E (by omega) hquot)
  simpa only [sub_sub_cancel] using h

end ResidueLift

section Units
variable (E : Type) [Field E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

/-- A character trivial on the successor layer has the same value on any
two critical units whose additive arguments differ in that successor ideal. -/
private theorem normalization_unit_congr {t : ℕ} (ht : 0 < t)
    (chi : ContinuousQuasiChar E)
    (hchi : QuasiCharTrivialOnUnitFiltration E chi (t + 1))
    (x y : lattice E (t : ℤ))
    (hxy : (x : E) - (y : E) ∈ lattice E ((t + 1 : ℕ) : ℤ)) :
    chi (positiveUnitOfLattice E ht (-x)) =
      chi (positiveUnitOfLattice E ht (-y)) := by
  let ux := positiveUnitOfLattice E ht (-x)
  let uy := positiveUnitOfLattice E ht (-y)
  apply div_eq_one.mp
  rw [← map_div]
  apply hchi
  apply (mem_unitFiltration_succ_iff_sub_mem_lattice E t _).2
  have huy : ord E (uy : Eˣ) = 0 :=
    (mem_unitFiltration_zero E _).1
      (unitFiltration_antitone E (Nat.zero_le t) uy.property)
  have hd : ((ux : Eˣ) : E) / ((uy : Eˣ) : E) - 1 =
      -((x : E) - (y : E)) / ((uy : Eˣ) : E) := by
    have hn := Units.ne_zero (uy : Eˣ)
    have hux : ((ux : Eˣ) : E) = 1 - (x : E) := by simp [ux, sub_eq_add_neg]
    have huy' : ((uy : Eˣ) : E) = 1 - (y : E) := by simp [uy, sub_eq_add_neg]
    rw [div_sub_one hn, hux, huy']
    congr 1
    ring
  simp only [Units.val_div_eq_div_val]
  change ((ux : Eˣ) : E) / ((uy : Eˣ) : E) - 1 ∈ lattice E ((t + 1 : ℕ) : ℤ)
  rw [hd]
  exact (div_mem_lattice_iff E ((uy : Eˣ) : E) _ 0 _ huy).2
    (by simpa using neg_mem_lattice E hxy)

end Units

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
local instance : PrimeCyclicExtension B₁ K :=
  PrimeCyclicExtension.ofCyclicPrimeExtension B₁ K
    (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.2.2.2.2
local instance : PrimeCyclicExtension F B₂ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₂
    (Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.1

open private realization_tower_data from LanglandsSecondMainLemma.Odd.Models.Realization
open private additiveConductor_of_normCharacterChart from LanglandsSecondMainLemma.Odd.Models.Setup
open private trace_depths from LanglandsSecondMainLemma.Odd.R2.Trace
open private commutator_additiveConductor from LanglandsSecondMainLemma.Odd.R2.Commutator

include hp hG hres hchar D

/-- The first equality in the proof of `O:R:T`, before any approximate
norm denominator is introduced. Both trace and norm phases are retained. -/
private theorem normalization_norm_phase
    (r : ℕ) (hr : r = (D.t₂ + 1) ⌈/⌉ p) (hrpos : 0 < r)
    (tau : NormCharacter F B₂) (htau : tau ≠ 1) (Psi : ContinuousAddChar F)
    (hchart : ∀ z : lattice F (r : ℤ),
      tau.1 (positiveUnitOfLattice F hrpos (-z)) = Psi (truncatedLog p (z : F)))
    (x : lattice B₁ ((D.delta + (D.t + 1) ⌈/⌉ p : ℕ) : ℤ)) :
    normQuasiChar F B₁ tau.1
        (positiveUnitOfLattice B₁ (commutator_depths hp hG D).1 (-x)) =
      tracePullbackAddChar F B₁ Psi (truncatedLog p (x : B₁)) *
        Psi (norm F B₁ (truncatedLog p (x : B₁))) := by
  obtain ⟨_, hres₁, _, _, _⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  obtain ⟨_, hres₂, _, _, _⟩ := realization_tower_data hp hG hres B₂ D.degree_B₂
  have hdegree : Module.finrank F B₁ = p := D.degree_B₁
  have hPsi := additiveConductor_of_normCharacterChart F B₂ hp D.odd_prime hchar
    D.degree_B₂ D.B₂_breaks.1 (D.t_pos.trans_le D.t_le_t₂) hres₂
    hr hrpos tau htau Psi hchart
  have hdepth := trace_depths (d := D.delta) D.odd_prime D.t_pos
  rw [← D.t₂_eq, ← hr] at hdepth
  let ux := positiveUnitOfLattice B₁ (commutator_depths hp hG D).1 (-x)
  have hn : normUnits F B₁ (ux : B₁ˣ) ∈ unitFiltration F r := by
    apply Models.norm_maps_modelDepth F B₁ D.B₁_breaks.1 hres₁ hrpos
      hdepth.2.2.1 (by simpa only [hdegree] using hdepth.2.2.2.1)
    exact ux.property
  have hncoe : (normUnits F B₁ (ux : B₁ˣ) : F) = norm F B₁ (1 - (x : B₁)) := by
    simp [ux, sub_eq_add_neg]
  let u := 1 - norm F B₁ (1 - (x : B₁))
  have hu : u ∈ lattice F (r : ℤ) := by
    have h := (mem_unitFiltration_succ_iff_sub_mem_lattice F (r - 1) _).1
      (by simpa only [Nat.sub_add_cancel hrpos] using hn)
    rw [Nat.sub_add_cancel hrpos, hncoe] at h
    simpa only [u, neg_sub] using neg_mem_lattice F h
  have hunit : (positiveUnitOfLattice F hrpos (-⟨u, hu⟩) : Fˣ) =
      normUnits F B₁ (ux : B₁ˣ) := by
    apply Units.ext
    simp only [coe_positiveUnitOfLattice, Submodule.coe_neg]
    rw [hncoe]
    simp [u]
  change tau.1 (normUnits F B₁ (ux : B₁ˣ)) = _
  rw [← hunit, hchart]
  rw [tracePullbackAddChar_apply, ← ContinuousAddChar.map_add_eq_mul]
  apply div_eq_one.mp
  rw [← additivePhase_sub]
  apply hPsi.trivial
  have hlog := normLog F B₁ D.B₁_breaks.1 D.t_pos hres₁
    (hchar.trans hdegree.symm) (by rw [hdegree]; have := D.odd_prime; omega)
    D.delta (x : B₁) (by simpa only [hdegree] using x.property)
  rw [hdegree, show D.t + 1 + D.delta = D.t₂ + 1 by rw [D.t₂_eq]; omega] at hlog
  simpa only [neg_neg, u, sub_add_eq_sub_sub] using hlog

/-- The lower pullback is an actual upper norm character, by norm
transitivity through the two intermediate fields. -/
private def normalization_pullback (tau : NormCharacter F B₂) : NormCharacter B₁ K :=
  ⟨normQuasiChar F B₁ tau.1, by
    apply ContinuousMonoidHom.ext
    intro x
    change tau.1 (normUnits F B₁ (normUnits B₁ K x)) = 1
    have hn : normUnits F B₁ (normUnits B₁ K x) = normUnits F B₂ (normUnits B₂ K x) := by
      apply Units.ext
      simp only [coe_normUnits, norm_trans]
    rw [hn]
    exact tau.eq_one_on_normRange F B₂ _ ⟨_, rfl⟩⟩

set_option maxHeartbeats 800000 in
/-- Compare the actual shallow commutator formula with the lower pullback
on the whole critical layer. The formula hypothesis is discharged by
`shift_commutator` in the public theorem below. -/
private theorem normalization_of_shallow_phase
    (r : ℕ) (hr : r = (D.t₂ + 1) ⌈/⌉ p) (hrpos : 0 < r)
    (tau : NormCharacter F B₂) (htau : tau ≠ 1) (Psi : ContinuousAddChar F)
    (hchart : ∀ z : lattice F (r : ℤ),
      tau.1 (positiveUnitOfLattice F hrpos (-z)) = Psi (truncatedLog p (z : F)))
    (Delta : K) (a : B₂)
    (hroot : Delta ^ p - Delta = algebraMap B₂ K a)
    (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ D.t) (hgen : Algebra.adjoin B₂ ({Delta} : Set K) = ⊤)
    (mu : NormCharacter B₁ K)
    (hmu : ∀ x : lattice B₁ ((D.delta + (D.t + 1) ⌈/⌉ p : ℕ) : ℤ),
      mu.1 (positiveUnitOfLattice B₁ (commutator_depths hp hG D).1 (-x)) =
        tracePullbackAddChar F B₁ Psi
          ((1 - (-elementarySymmetric B₁ K (p - 1) Delta)) * truncatedLog p (x : B₁))) :
    mu.1 = normQuasiChar F B₁ tau.1 := by
  classical
  obtain ⟨_, hres₁, hres₁K, _, _⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  obtain ⟨_, hres₂, _, _, _⟩ := realization_tower_data hp hG hres B₂ D.degree_B₂
  let nu := normalization_pullback hp hG D tau
  suffices heq : mu = nu by exact congrArg Subtype.val heq
  have hPsi := additiveConductor_of_normCharacterChart F B₂ hp D.odd_prime hchar
    D.degree_B₂ D.B₂_breaks.1 (D.t_pos.trans_le D.t_le_t₂) hres₂
    hr hrpos tau htau Psi hchart
  have hPsi₁ := commutator_additiveConductor hp hG hres hchar D r hr hrpos tau htau Psi hchart
  let s := -elementarySymmetric B₁ K (p - 1) Delta
  have hs : s ∈ lattice B₁ (((p : ℤ) - 1) * D.delta) :=
    (Models.realization_twistedEstimates_of_coordinate hp hG hres hchar D
      Delta a hroot hDelta hprime hgen).2.2.2
  have hct : (D.t + 1) ⌈/⌉ p ≤ D.t := by
    rw [ceilDiv_le_iff_le_mul hp.pos]
    have := Nat.mul_le_mul_right D.t hp.two_le
    have := D.t_pos
    omega
  have hq : D.delta + (D.t + 1) ⌈/⌉ p ≤ D.tPrime := by
    rw [D.tPrime_eq]
    have := Nat.le_mul_of_pos_left D.delta hp.pos
    omega
  have htPrime : 0 < D.tPrime := by rw [D.tPrime_eq]; have := D.t_pos; omega
  have hchar₁ : residueCharacteristic B₁ = p :=
    (residueCharacteristic_extension_eq F B₁).trans hchar
  let shallow (x : lattice B₁ (D.tPrime : ℤ)) :
      lattice B₁ ((D.delta + (D.t + 1) ⌈/⌉ p : ℕ) : ℤ) :=
    ⟨x, lattice_antitone B₁ (by exact_mod_cast hq) x.property⟩
  have hmuPhase (x : lattice B₁ (D.tPrime : ℤ)) :
      mu.1 (positiveUnitOfLattice B₁ htPrime (-x)) =
        tracePullbackAddChar F B₁ Psi ((1 - s) * truncatedLog p (x : B₁)) := by
    convert hmu (shallow x) using 1
    apply congrArg mu.1
    apply Units.ext
    rfl
  have hnuPhase (x : lattice B₁ (D.tPrime : ℤ)) :
      nu.1 (positiveUnitOfLattice B₁ htPrime (-x)) =
        tracePullbackAddChar F B₁ Psi (truncatedLog p (x : B₁)) *
          Psi (norm F B₁ (truncatedLog p (x : B₁))) := by
    convert normalization_norm_phase hp hG hres hchar D r hr hrpos tau htau Psi
      hchart (shallow x) using 1
    apply congrArg (normQuasiChar F B₁ tau.1)
    apply Units.ext
    rfl
  apply normalization_ext B₁ K D.B₁_breaks.2 hres₁K mu nu
  intro u
  let x := truncatedLogUnitArgument B₁ htPrime u
  have hux : (positiveUnitOfLattice B₁ htPrime (-x) : B₁ˣ) = (u : B₁ˣ) := by
    apply Units.ext
    simp [x, coe_positiveUnitOfLattice]
  rw [← hux]
  by_cases hd : D.delta = 0
  · have ht : D.tPrime = D.t := by rw [D.tPrime_eq, hd, mul_zero, add_zero]
    have hb : ord B₁ (norm B₁ K Delta) = (-(D.t : ℤ) : WithTop ℤ) := by
      rw [ord_norm, hres₁K, one_nsmul, hDelta]
      simp only [WithTop.LinearOrderedAddCommGroup.coe_neg]
    have hxlog : truncatedLog p (x : B₁) ∈ lattice B₁ (D.t : ℤ) := by
      rw [← ht]
      exact (truncatedLogOnLattice B₁ p D.tPrime hchar₁ htPrime x).property
    obtain ⟨Y, hY, hdiff⟩ := normalization_lift F B₁ hres₁ (D.t : ℤ)
      (norm B₁ K Delta) hb (truncatedLog p (x : B₁)) hxlog
    have hY' : algebraMap F B₁ (Y : F) / norm B₁ K Delta ∈ lattice B₁ (D.tPrime : ℤ) := by
      simpa only [ht] using hY
    obtain ⟨y, hy⟩ := (truncatedLogOnLattice_bijective B₁ p D.tPrime hchar₁ hp htPrime).2
      ⟨_, hY'⟩
    have hyval : truncatedLog p (y : B₁) = algebraMap F B₁ (Y : F) / norm B₁ K Delta :=
      congrArg Subtype.val hy
    have hxy : (x : B₁) - (y : B₁) ∈ lattice B₁ ((D.tPrime + 1 : ℕ) : ℤ) := by
      rw [mem_lattice, ← ord_truncatedLog_sub B₁ p hchar₁
        (lattice_antitone B₁ (by exact_mod_cast htPrime) x.property)
        (lattice_antitone B₁ (by exact_mod_cast htPrime) y.property), hyval]
      simpa only [ht, Nat.cast_add, Nat.cast_one] using (mem_lattice B₁).1 hdiff
    obtain ⟨pi, hpi, hpiGen⟩ := monogenicUniformizer B₁ K hres₁K
    rw [normalization_unit_congr B₁ htPrime mu.1
      (ramifiedNormCharacter_trivialOn_break_succ B₁ K D.B₁_breaks.2 hres₁K pi hpi hpiGen mu)
      x y hxy]
    rw [normalization_unit_congr B₁ htPrime nu.1
      (ramifiedNormCharacter_trivialOn_break_succ B₁ K D.B₁_breaks.2 hres₁K pi hpi hpiGen nu)
      x y hxy]
    rw [hmuPhase, hnuPhase, hyval]
    have hrec := ((reciprocal hp hG hres hchar D hd r hr hrpos tau htau Psi hchart
      Delta a hroot hDelta hgen).2.2 Y)
    have hsY : tracePullbackAddChar F B₁ Psi
        (s * (algebraMap F B₁ (Y : F) / norm B₁ K Delta)) =
        Psi (-norm F B₁ (algebraMap F B₁ (Y : F) / norm B₁ K Delta)) := by
      simpa only [s, mul_div_assoc] using hrec.1.trans hrec.2
    rw [sub_mul, one_mul, additivePhase_sub, hsY]
    have hneg : Psi (-norm F B₁ (algebraMap F B₁ (Y : F) / norm B₁ K Delta)) =
        (Psi (norm F B₁ (algebraMap F B₁ (Y : F) / norm B₁ K Delta)))⁻¹ :=
      AddChar.map_neg_eq_inv Psi.toAddChar _
    rw [hneg, div_inv_eq_mul]
  · have hdpos : (1 : ℤ) ≤ D.delta := by omega
    have hs1 : s ∈ lattice B₁ 1 := by
      apply lattice_antitone B₁ _ hs
      have hpZ : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
      nlinarith
    have hxlog : truncatedLog p (x : B₁) ∈ lattice B₁ (D.tPrime : ℤ) :=
      (truncatedLogOnLattice B₁ p D.tPrime hchar₁ htPrime x).property
    have hkill : tracePullbackAddChar F B₁ Psi ((1 - s) * truncatedLog p (x : B₁)) =
        tracePullbackAddChar F B₁ Psi (truncatedLog p (x : B₁)) := by
      apply div_eq_one.mp
      rw [← additivePhase_sub]
      apply hPsi₁.trivial
      rw [show (1 - s) * truncatedLog p (x : B₁) - truncatedLog p (x : B₁) =
        -(s * truncatedLog p (x : B₁)) by ring]
      simpa only [neg_neg, Nat.cast_add, Nat.cast_one, add_comm] using
        neg_mem_lattice B₁ (mul_mem_lattice B₁ hs1 hxlog)
    have hnkill : Psi (norm F B₁ (truncatedLog p (x : B₁))) = 1 := by
      apply hPsi.trivial
      apply lattice_antitone F _
        ((mem_lattice F).2 (by
          rw [ord_norm, hres₁, one_nsmul]
          exact hxlog))
      simp only [neg_neg, Nat.cast_add, Nat.cast_one]
      rw [D.t₂_eq, D.tPrime_eq]
      push_cast
      have hpZ : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
      have hmul := mul_le_mul_of_nonneg_right hpZ (show (0 : ℤ) ≤ D.delta by positivity)
      linarith only [hmul, hdpos]
    rw [hmuPhase, hnuPhase, hkill, hnkill, mul_one]

/-- **Paper Proposition 8.13 (`O:R:normalize`).** The actual translating
automorphism has commutator exactly `tau₂ ∘ n₁`, for both break configurations
and both field characteristics. The coordinate and full first model are
those constructed by `Models.realization`. In particular the shallow
commutator formula and its generator normalization are proved, not assumed.

The constructor `normalization_realization` below supplies all coordinate
and model inputs from the prescribed primitive compatible pair. -/
theorem normalization
    (r : ℕ) (hr : r = (D.t₂ + 1) ⌈/⌉ p) (hrpos : 0 < r)
    (tau : NormCharacter F B₂) (htau : tau ≠ 1) (Psi : ContinuousAddChar F)
    (hchart : ∀ z : lattice F (r : ℤ),
      tau.1 (positiveUnitOfLattice F hrpos (-z)) = Psi (truncatedLog p (z : F)))
    (Delta : K) (a : B₂)
    (hroot : Delta ^ p - Delta = algebraMap B₂ K a)
    (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ D.t) (hgen : Algebra.adjoin B₂ ({Delta} : Set K) = ⊤)
    (chi : ContinuousQuasiChar B₁) (phi₂ : ContinuousQuasiChar B₂)
    (hcompat : normQuasiChar B₁ K chi = normQuasiChar B₂ K phi₂)
    (hprimitive : ¬ ∃ theta : ContinuousQuasiChar F,
      normQuasiChar F K theta = normQuasiChar B₂ K phi₂)
    (hmodel : ∀ u : unitFiltration B₁ (Models.firstModelDepth D),
      chi u = tracePullbackAddChar F B₁ Psi
        (norm B₁ K Delta * truncatedLog p (1 - ((u : B₁ˣ) : B₁)))) :
    ∃ sigma : Gal(K/B₂),
      sigma Delta - (Delta + 1) ∈ lattice K 1 ∧
      let sigma₁ := IntermediateField.restrictRestrictAlgEquivMapHom F B₁ B₂ K sigma
      Basic.conjugateQuasiChar F B₁ sigma₁ chi / chi = normQuasiChar F B₁ tau.1 := by
  obtain ⟨sigma, hnear, hphase⟩ := shift_commutator hp hG hres hchar D
    r hr hrpos tau htau Psi hchart Delta a hroot hDelta hprime hgen chi hmodel
  let sigma₁ := IntermediateField.restrictRestrictAlgEquivMapHom F B₁ B₂ K sigma
  obtain ⟨mu, hmu, _⟩ := commutator_normCharacter hp hG hres hchar D
    chi phi₂ hcompat hprimitive sigma₁
  refine ⟨sigma, hnear, ?_⟩
  change Basic.conjugateQuasiChar F B₁ sigma₁ chi / chi = _
  rw [← hmu]
  apply normalization_of_shallow_phase hp hG hres hchar D
    r hr hrpos tau htau Psi hchart Delta a hroot hDelta hprime hgen mu
  intro x
  rw [hmu]
  exact hphase x

/-- Construct the normalized coordinate, allowed first conjugate, full
model, and the exact commutator from the genuine primitive compatible pair.
The actual lower character and phase are powered together, and the
canonical local constant of the first character is preserved. -/
theorem normalization_realization
    (phi₁ : ContinuousQuasiChar B₁) (phi₂ : ContinuousQuasiChar B₂)
    (hcompat : normQuasiChar B₁ K phi₁ = normQuasiChar B₂ K phi₂)
    (hprimitive : ¬ ∃ theta : ContinuousQuasiChar F,
      normQuasiChar F K theta = normQuasiChar B₂ K phi₂)
    (hphi : QuasiCharTrivialOnUnitFiltration B₂ phi₂ (Models.secondModelConductor D))
    (r : ℕ) (hr : r = (D.t₂ + 1) ⌈/⌉ p) (hrpos : 0 < r)
    (tau : NormCharacter F B₂) (htau : tau ≠ 1) (Psi : ContinuousAddChar F)
    (hchart : ∀ z : lattice F (r : ℤ),
      tau.1 (positiveUnitOfLattice F hrpos (-z)) = Psi (truncatedLog p (z : F))) :
    ∃ (j : ℕ) (Delta : K) (a : B₂) (chi : ContinuousQuasiChar B₁) (rho : Gal(B₁/F)),
      0 < j ∧ j < p ∧ tau ^ j ≠ 1 ∧
      (∀ z : lattice F (r : ℤ),
        (tau ^ j).1 (positiveUnitOfLattice F hrpos (-z)) = (Psi ^ j) (truncatedLog p (z : F))) ∧
      Delta ^ p - Delta = algebraMap B₂ K a ∧
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ¬ p ∣ D.t ∧ Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ ∧ norm B₂ K Delta = a ∧
      chi = Basic.conjugateQuasiChar F B₁ rho phi₁ ∧
      normQuasiChar B₁ K chi = normQuasiChar B₂ K phi₂ ∧
      IsMultiplicativeConductor B₁ chi (Models.firstModelConductor D) ∧
      (∀ u : unitFiltration B₁ (Models.firstModelDepth D),
        chi u = tracePullbackAddChar F B₁ (Psi ^ j)
          (norm B₁ K Delta * truncatedLog p (1 - ((u : B₁ˣ) : B₁)))) ∧
      (∀ psi : ContinuousAddChar F, psi ≠ 1 →
        localConstant B₁ chi (tracePullbackAddChar F B₁ psi) =
          localConstant B₁ phi₁ (tracePullbackAddChar F B₁ psi)) ∧
      ∃ sigma : Gal(K/B₂),
        sigma Delta - (Delta + 1) ∈ lattice K 1 ∧
        let sigma₁ := IntermediateField.restrictRestrictAlgEquivMapHom F B₁ B₂ K sigma
        Basic.conjugateQuasiChar F B₁ sigma₁ chi / chi = normQuasiChar F B₁ (tau ^ j).1 := by
  obtain ⟨j, Delta, a, hjpos, hjp, htauj, hchartj, _hphase, hroot, hDelta, _ha,
      hprime, hgen, hnorm, M, _hext₂, _hc₂, rho, hext₁, hpull, hc₁, hconstant⟩ :=
    Models.realization hp hG hres hchar D phi₁ phi₂ hcompat hprimitive hphi
      r hr hrpos tau htau Psi hchart
  let chi := Basic.conjugateQuasiChar F B₁ rho phi₁
  have hmodel : ∀ u : unitFiltration B₁ (Models.firstModelDepth D),
      chi u = tracePullbackAddChar F B₁ (Psi ^ j)
        (norm B₁ K Delta * truncatedLog p (1 - ((u : B₁ˣ) : B₁))) := by
    intro u
    exact (DFunLike.congr_fun hext₁ u).trans (M.R₁_apply u)
  refine ⟨j, Delta, a, chi, rho, hjpos, hjp, htauj, hchartj, hroot, hDelta,
    hprime, hgen, hnorm, rfl, hpull, hc₁, hmodel, hconstant, ?_⟩
  exact normalization hp hG hres hchar D r hr hrpos (tau ^ j) htauj (Psi ^ j)
    hchartj Delta a hroot hDelta hprime hgen chi phi₂ hpull hprimitive hmodel

end Diamond
end
end LanglandsSecondMainLemma.Odd.R2
