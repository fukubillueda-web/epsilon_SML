import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Odd.Transition.Q124
import LanglandsSecondMainLemma.Odd.Transition.Q3

/-!
# Odd / Transition / Phase

Paper Theorem 9.29 (`O:T:phase`, `O:T:phidef`) and the algebraic identity
`O:T:factorphase`. The actual factors are assembled using `q124` and `q3`.
The factorization is a separate field identity; no cancellation estimate
or equality of local constants is used in the assembly.
-/

namespace LanglandsSecondMainLemma.Odd.Transition

noncomputable section

open LanglandsFirstMainLemma

set_option backward.isDefEq.respectTransparency false

/-- **Paper `O:T:factorphase`.** Exact factorization of the four-term
terminal exponent. `u` is nonzero and the rational half is defined in
characteristic different from two. The identity also holds when `D = 0`;
in the actual transition data `D` is a unit by the denominator estimates.
No norm, trace, or character value is replaced in this algebraic step. -/
theorem phase_factorization {F : Type*} [Field F] {p : ℕ}
    (hp : 2 ≤ p) (u v A₀ H J : F) (hu : u ≠ 0) (htwo : (2 : F) ≠ 0) :
    let W := u⁻¹
    let D := 1 + u ^ p * A₀
    (-W / 2 * (v * u) ^ (p - 1) / D + W * u ^ (p - 1) * H / D -
        u ^ (p - 2) * H / (2 * D ^ 2) + u ^ (p - 1) * A₀ * J / (2 * D ^ 2)) =
      u ^ (p - 1) * A₀ * (J + u ^ (p - 1) * H) / (2 * D ^ 2) +
        u ^ (p - 2) / (2 * D) * (H - v ^ (p - 1)) := by
  dsimp only
  by_cases hD : 1 + u ^ p * A₀ = 0
  · simp only [hD, zero_pow (by decide : 2 ≠ 0), mul_zero, div_zero, add_zero,
      sub_zero, zero_mul]
  have hp₁ : u ^ (p - 1) = u ^ (p - 2) * u := by
    rw [show p - 1 = p - 2 + 1 by omega, pow_succ]
  have hp₂ : u ^ p = u ^ (p - 2) * u ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel hp]
  rw [mul_pow, hp₁, hp₂]
  rw [hp₂] at hD
  field_simp
  ring

section Diamond

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]
  {p : ℕ} {hp : p.Prime}
  {hG : Nonempty
    (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))}
  (R : Total.OddTotalBreakData (F := F) (K := K) hp hG)

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

local notation "B₁" => R.B₁
local notation "B₂" => R.B₂

/-- **Paper Theorem 9.29 (`O:T:phase`, `O:T:phaseeq`, `O:T:phidef`).**

The inverse ordered product of the four actual character factors equals
`Psi` of the displayed four-term exponent. The inputs are the actual
compatible primitive minimal characters, their full coefficient charts,
the descending base quasi-character, and the two nontrivial norm-character
charts. Both exact lower norm choices and all three stationary units retain
their prescribed equations.

The integer transition depth is proved positive before using the natural
depth interface of `q3`. The two accepted factor evaluations are then
combined by additivity of `Psi`. This includes every odd prime, both field
characteristics, and nonunitary quasi-characters. -/
theorem phase
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (Delta : K) (hDelta : ord K Delta = ((-(R.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ R.t)
    (hroot : Delta ^ p - Delta = algebraMap B₂ K (norm B₂ K Delta))
    (e : LocalAddCharData F) (alpha beta gamma : Fˣ)
    (halpha : ord F (alpha : F) =
      ((-e.conductor - (R.t₂ : ℤ) - 1 : ℤ) : WithTop ℤ))
    (chi : ContinuousQuasiChar B₁) (phi : ContinuousQuasiChar B₂)
    (hphi : IsMultiplicativeConductor B₂ phi (Models.secondModelConductor R))
    (hcompat : chi.compNorm (S := K) = phi.compNorm (S := K))
    (hprimitive : ¬ ∃ theta : ContinuousQuasiChar F,
      theta.compNorm (S := K) = phi.compNorm (S := K))
    (hchiFormula : ∀ z : unitFiltration B₁ (Models.firstModelDepth R),
      chi z = tracePullbackAddChar F B₁ e.character
        (algebraMap F B₁ (alpha : F) * norm B₁ K Delta *
          truncatedLog p (1 - ((z : B₁ˣ) : B₁))))
    (m : ℤ)
    (hmt : (R.t : ℤ) < (p : ℤ) * m)
    (lambda : LocalQuasiCharData F)
    (hn : (lambda.conductor : ℤ) = (R.t₂ : ℤ) + m + 1)
    (hgamma : ord F (gamma : F) =
      ((-e.conductor - (lambda.conductor : ℤ) : ℤ) : WithTop ℤ))
    (hlambdaFormula : ∀ z : unitFiltration F (lambda.conductor ⌈/⌉ p),
      lambda.character z = e.character
        ((gamma : F) * truncatedLog p (1 - ((z : Fˣ) : F))))
    (tau : NormCharacter F B₂) (htau : tau ≠ 1)
    (htauFormula : ∀ z : unitFiltration F ((R.t₂ + 1) ⌈/⌉ p),
      tau.1 z = e.character ((alpha : F) * truncatedLog p (1 - ((z : Fˣ) : F))))
    (nu : NormCharacter F B₁) (hnu : nu ≠ 1)
    (hbeta : ord F (beta : F) =
      ((-e.conductor - (R.t : ℤ) - 1 : ℤ) : WithTop ℤ))
    (hnuFormula : ∀ z : unitFiltration F ((R.t + 1) ⌈/⌉ p),
      nu.1 z = e.character ((beta : F) * truncatedLog p (1 - ((z : Fˣ) : F))))
    (w₁ : B₁ˣ) (hw₁ : normUnits F B₁ w₁ = gamma / beta)
    (w : B₂ˣ) (hw : normUnits F B₂ w = gamma / alpha)
    (A₁ C₁ : B₁ˣ) (C₂ : B₂ˣ)
    (hA₁ : (A₁ : B₁) = algebraMap F B₁ (gamma : F) +
      algebraMap F B₁ (alpha : F) * norm B₁ K Delta)
    (hC₁ : (C₁ : B₁) = (A₁ : B₁) -
      algebraMap F B₁ (beta : F) * (w₁ : B₁))
    (hC₂ : (C₂ : B₂) = algebraMap F B₂ (gamma : F) -
      algebraMap F B₂ (alpha : F) * (w : B₂) +
      algebraMap F B₂ (alpha : F) * norm B₂ K Delta) :
    let u := (alpha : F) / (gamma : F)
    let W := u⁻¹
    let v := (beta : F) / (alpha : F)
    let A₀ := norm F B₂ (norm B₂ K Delta)
    let D := 1 + u ^ p * A₀
    let H := norm F B₁ (-elementarySymmetric B₁ K (p - 1) Delta)
    let J := norm F B₁ (trace B₁ K ((Delta / algebraMap B₂ K (w : B₂)) ^ (p - 1)))
    let Psi := (scaleAddCharData F e alpha).character
    let Q := Parameters.fourFactorValues F B₁ B₂ chi phi lambda.character e.character
      alpha beta w₁ A₁ C₁ w C₂
    Q.product⁻¹ = Psi (-W / 2 * (v * u) ^ (p - 1) / D +
      W * u ^ (p - 1) * H / D - u ^ (p - 2) * H / (2 * D ^ 2) +
        u ^ (p - 1) * A₀ * J / (2 * D ^ 2)) := by
  dsimp only
  let u := (alpha : F) / (gamma : F)
  let W := u⁻¹
  let v := (beta : F) / (alpha : F)
  let A₀ := norm F B₂ (norm B₂ K Delta)
  let D := 1 + u ^ p * A₀
  let H := norm F B₁ (-elementarySymmetric B₁ K (p - 1) Delta)
  let J := norm F B₁ (trace B₁ K ((Delta / algebraMap B₂ K (w : B₂)) ^ (p - 1)))
  let Psi := (scaleAddCharData F e alpha).character
  let Q := Parameters.fourFactorValues F B₁ B₂ chi phi lambda.character e.character
    alpha beta w₁ A₁ C₁ w C₂
  have hu : ord F ((alpha / gamma : Fˣ) : F) = (m : WithTop ℤ) := by
    rw [Units.val_div_eq_div_val, ord_div, halpha, hgamma,
      ← WithTop.LinearOrderedAddCommGroup.coe_sub, hn]
    congr 1
    ring
  have hmpos : 0 < m := by
    have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
    nlinarith [Int.natCast_nonneg R.t]
  have hmNat : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hmpos.le
  have hmtNat : R.t < p * m.toNat := by
    exact_mod_cast (show (R.t : ℤ) < (p : ℤ) * (m.toNat : ℤ) by
      rw [hmNat]
      exact hmt)
  have hnNat : lambda.conductor = R.t₂ + m.toNat + 1 := by omega
  have hgammaNat : ord F (gamma : F) =
      ((-e.conductor - ((R.t₂ + m.toNat : ℕ) : ℤ) - 1 : ℤ) : WithTop ℤ) := by
    rw [hgamma, hnNat]
    simp only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub]
  have hthird := q3 hp hG R hres e alpha beta gamma Delta hDelta chi phi hchiFormula
    hmtNat lambda.character (by rw [← hnNat]; exact lambda.isConductor)
    hgammaNat (by rw [← hnNat]; exact hlambdaFormula)
    nu hnu hbeta halpha hnuFormula w₁ A₁ C₁ w C₂ hw₁ hA₁ hC₁
  change Q.Q₃⁻¹ = Psi (-W / 2 * (v * u) ^ (p - 1) / D) at hthird
  have hrest := q124 R hres hchar Delta hDelta hprime hroot e alpha gamma halpha
    chi phi hphi hcompat hprimitive hchiFormula m hu hmt lambda hn hgamma
    hlambdaFormula tau htau htauFormula w hw A₁ C₂ hA₁ hC₂
  have hfourth : Q.Q₄ = tracePullbackAddChar F B₂ Psi (w : B₂) := by
    dsimp only [Q, Parameters.fourFactorValues, Psi]
    simp only [tracePullbackAddChar_apply, scaleAddCharData_character_apply,
      ← Algebra.smul_def, map_smul, smul_eq_mul]
  have hrest' : (Q.Q₁ * Q.Q₂ * Q.Q₄)⁻¹ =
      Psi (W * u ^ (p - 1) * H / D - u ^ (p - 2) * H / (2 * D ^ 2) +
        u ^ (p - 1) * A₀ * J / (2 * D ^ 2)) := by
    rw [hfourth]
    dsimp only [Q, Parameters.fourFactorValues, Psi, W, u, H, D, A₀, J]
    simpa only [Units.val_div_eq_div_val] using hrest
  change Q.product⁻¹ = _
  calc
    _ = Q.Q₃⁻¹ * (Q.Q₁ * Q.Q₂ * Q.Q₄)⁻¹ := by
      simp only [Parameters.FourFactorValues.product, mul_inv_rev,
        mul_comm, mul_left_comm]
    _ = _ := by
      rw [hthird, hrest', ← Psi.map_add_eq_mul]
      congr 1
      ring

end Diamond

end

end LanglandsSecondMainLemma.Odd.Transition
