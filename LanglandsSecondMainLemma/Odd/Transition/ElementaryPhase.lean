import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Odd.Transition.Rational

/-!
# Odd / Transition / Elementary Phase

Paper Lemma 9.23 (`O:T:theta0`), corrected source lines 4619–4634,
with the stationary setup at lines 4438–4518.

The exact rational identity is followed by its bound in the actual field
`B₂`. The preserved norm equation for `w` supplies both its order and the
norm--power error. The final depth is `1 + t₂`, with integer exponents
and orders in `WithTop ℤ`, in both field characteristics.
-/

open LanglandsFirstMainLemma

namespace LanglandsSecondMainLemma.Odd.Transition

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The exact identity `O:T:Theta0`, before taking valuations. -/
private theorem elementaryPhase_identity {E : Type*} [Field E]
    {p : ℕ} (hp : 0 < p) (u w a : E)
    (hu : u ≠ 0) (hw : w ≠ 0) (hC : 1 + u * a ≠ 0) :
    u⁻¹ * (u * w / (1 + u * a) * (1 - u⁻¹ / w ^ p) +
        (w ^ (p - 1))⁻¹) - w =
      a / (w ^ (p - 1) * (1 + u * a)) * (1 - u * w ^ p) := by
  have hpow : w ^ p = w ^ (p - 1) * w := by
    rw [← pow_succ, Nat.sub_add_cancel hp]
  rw [hpow]
  field_simp
  ring

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
  (R : Total.OddTotalBreakData (F := F) (K := K) hp hG)

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

local notation "B₂" => R.B₂

local instance : PrimeCyclicExtension F B₂ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₂
    (Basic.intermediateField_tower_compatible hp hG B₂ R.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.1

/-- **Paper Lemma 9.23 (`O:T:theta0`).** The remaining elementary
rational expression is exactly `a / (w^(p-1) C) * (1 - u w^p)` and
belongs to the whole ideal of depth `1 + t₂` in the actual second
intermediate field.

Here `a = N_{K/B₂}(Delta)`, `u = alpha/gamma` in the stationary setup,
and `w` retains its exact norm `N_{B₂/F}(w) = u⁻¹`. The denominator is
proved nonzero, and the norm--power estimate is derived from this lower
cyclic extension. This field identity and ideal membership require no
additional character hypotheses: they apply in particular to the actual
stationary characters, whose additive phase is trivial on this ideal.
The element itself is not asserted to be zero. -/
theorem elementaryPhase
    (hres : residueDegree F K = 1)
    {m : ℕ} (hmt : R.t < p * m)
    (Delta : K) (hDelta : ord K Delta = ((-(R.t : ℤ) : ℤ) : WithTop ℤ))
    (u : Fˣ) (hu : ord F (u : F) = ((m : ℤ) : WithTop ℤ))
    (w : B₂ˣ) (hw : normUnits F B₂ w = u⁻¹) :
    let a := norm B₂ K Delta
    let U := algebraMap F B₂ (u : F)
    let W := U⁻¹
    let C := 1 + U * a
    let k := U * (w : B₂) / C
    let eta := W / (w : B₂) ^ p
    W * (k * (1 - eta) + (w : B₂) ^ (-((p : ℤ) - 1))) - (w : B₂) =
        a / ((w : B₂) ^ (p - 1) * C) * (1 - U * (w : B₂) ^ p) ∧
      a / ((w : B₂) ^ (p - 1) * C) * (1 - U * (w : B₂) ^ p) ∈
        lattice B₂ (1 + (R.t₂ : ℤ)) := by
  let a := norm B₂ K Delta
  let U := algebraMap F B₂ (u : F)
  let W := U⁻¹
  let C := 1 + U * a
  let b : ℤ := ((p : ℤ) - 1) * R.t₂
  obtain ⟨_, hrF₂, hrK₂, heF₂, _⟩ :=
    realization_tower_data hp hG hres B₂ R.degree_B₂
  have ha : ord B₂ a = ((-(R.t : ℤ) : ℤ) : WithTop ℤ) := by
    dsimp only [a]
    rw [ord_norm, hrK₂, one_nsmul, hDelta]
  have hbreak : PrimeCyclicExtension.IsLowerBreak F B₂ (R.t + R.delta) := by
    rw [← R.t₂_eq]
    exact R.B₂_breaks.1
  have hC : ord B₂ C = 0 :=
    (denominator_congruences F B₂ R.odd_prime R.t_pos R.degree_B₂ hrF₂ hbreak hmt
      (u : F) a hu ha).1
  have hCne : C ≠ 0 := by
    intro h
    simp [h] at hC
  have hUne : U ≠ 0 := (map_ne_zero (algebraMap F B₂)).2 u.ne_zero
  constructor
  · have hexp : -((p : ℤ) - 1) = -((p - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub hp.one_le, Nat.cast_one]
    simpa only [hexp, zpow_neg, zpow_natCast] using
      elementaryPhase_identity hp.pos U (w : B₂) a hUne w.ne_zero hCne
  have hU : ord B₂ U = (((p : ℤ) * m : ℤ) : WithTop ℤ) := by
    dsimp only [U]
    rw [ord_algebraMap, heF₂, hu, ← WithTop.coe_nsmul]
    rfl
  have hwNorm : norm F B₂ (w : B₂) = (u : F)⁻¹ := by
    simpa only [coe_normUnits, Units.val_inv_eq_inv_val] using congrArg Units.val hw
  have hwOrd : ord B₂ (w : B₂) = ((-(m : ℤ) : ℤ) : WithTop ℤ) := by
    have hn := congrArg (ord F) hwNorm
    simpa only [ord_norm, hrF₂, one_nsmul, ord_inv, hu,
      WithTop.LinearOrderedAddCommGroup.coe_neg] using hn
  have hdiff : (w : B₂) ^ p - W ∈ lattice B₂ (-(p : ℤ) * m + b) := by
    have h := Total.powerNorm F B₂ p R.t₂ R.degree_B₂ R.odd_prime
      R.B₂_breaks.1 (by have := R.t_pos; have := R.t_le_t₂; omega) hrF₂ (w : B₂)
    rw [hwOrd, hwNorm, map_inv₀] at h
    apply (mem_lattice B₂).2
    simpa only [← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul,
      Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one, mul_neg, neg_mul,
      b, W, U] using h
  have herror : 1 - U * (w : B₂) ^ p ∈ lattice B₂ b := by
    have hscaled : U * ((w : B₂) ^ p - W) ∈ lattice B₂ b := by
      have hcancel : (p : ℤ) * m + (-(p : ℤ) * m + b) = b := by ring
      simpa only [hcancel] using
        mul_mem_lattice B₂ ((mem_lattice B₂).2 hU.ge) hdiff
    have heq : 1 - U * (w : B₂) ^ p = -(U * ((w : B₂) ^ p - W)) := by
      dsimp only [W]
      rw [mul_sub, mul_inv_cancel₀ hUne]
      ring
    rw [heq]
    exact (lattice B₂ b).neg_mem hscaled
  have hweight : a / ((w : B₂) ^ (p - 1) * C) ∈
      lattice B₂ (-(R.t : ℤ) + ((p : ℤ) - 1) * m) := by
    rw [mem_lattice, ord_div, ord_mul, ord_pow, hC, add_zero, ha, hwOrd]
    simp only [← WithTop.coe_nsmul, ← WithTop.LinearOrderedAddCommGroup.coe_sub,
      nsmul_eq_mul, Nat.cast_sub hp.one_le, Nat.cast_one]
    apply WithTop.coe_le_coe.mpr
    ring_nf
    rfl
  have hdepth : 1 + (R.t₂ : ℤ) ≤ -(R.t : ℤ) + ((p : ℤ) - 1) * m + b := by
    have hpZ : 3 ≤ (p : ℤ) := by have := R.odd_prime; omega
    have hm : 1 ≤ (m : ℤ) := by
      have : 0 < m := by nlinarith [R.t_pos]
      omega
    have ht : 0 ≤ (R.t : ℤ) := by omega
    have hd : 0 ≤ (R.delta : ℤ) := by omega
    have h₁ : 0 ≤ ((p : ℤ) - 3) * R.t := mul_nonneg (by omega) ht
    have h₂ : 0 ≤ ((p : ℤ) - 2) * R.delta := mul_nonneg (by omega) hd
    have h₃ : 2 ≤ ((p : ℤ) - 1) * m := by nlinarith
    dsimp only [b]
    rw [R.t₂_eq]
    push_cast
    nlinarith
  exact lattice_antitone B₂ hdepth (mul_mem_lattice B₂ hweight herror)

end Diamond

end

end LanglandsSecondMainLemma.Odd.Transition
