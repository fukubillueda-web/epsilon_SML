import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Odd.Parameters.FourFactors
import LanglandsSecondMainLemma.Odd.Transition.Denominators
import LanglandsSecondMainLemma.Odd.Transition.NormHalf

/-!
# Odd / Transition / Q3

Paper Lemma 9.28 (`O:T:Q3`). The full coefficient chart first reduces
Q3 to its quadratic term. The rational half of the actual norm phase
on the first lower edge then gives the base-field expression. The
weighted denominator congruence is used at the additive conductor.
-/

namespace LanglandsSecondMainLemma.Odd.Transition

noncomputable section

open LanglandsFirstMainLemma

open private truncatedLog_sub_quadratic_mem pow_mem_lattice from
  LanglandsSecondMainLemma.Odd.EnhancedStationary
open private normPhase_half half_mem_lattice from
  LanglandsSecondMainLemma.Odd.Transition.NormHalf
open private weighted_depths from
  LanglandsSecondMainLemma.Odd.Transition.Denominators
open private realization_tower_data from
  LanglandsSecondMainLemma.Odd.Models.Realization

set_option backward.isDefEq.respectTransparency false

/-- Both the full-chart depth and the cubic remainder depth follow from
`pm > t`; the equality boundary at `p = 3` is retained. -/
private theorem q3_depths {p t m delta : ℕ} (hp : 2 < p)
    (hmt : t < p * m) :
    (1 + t + p * (m + delta)) ⌈/⌉ p ≤ (p - 1) * (m + delta) ∧
    1 + t + p * (m + delta) ≤ 3 * ((p - 1) * (m + delta)) ∧
    (t + 1) ⌈/⌉ p ≤ (p - 2) * (m + delta) := by
  have hm : 0 < m := by nlinarith
  have hp1 : p - 1 + 1 = p := by omega
  have hp2 : p - 2 + 2 = p := by omega
  have hsmall : t + 1 ≤ p * (m + delta) := by nlinarith
  have htwo : 2 ≤ p - 1 := by omega
  have hthree : 2 * p ≤ 3 * (p - 1) := by omega
  have hmul := Nat.mul_le_mul_right (m + delta) hthree
  refine ⟨?_, by nlinarith, ?_⟩
  · rw [ceilDiv_le_iff_le_mul (by omega : 0 < p)]
    have h := Nat.mul_le_mul_right (m + delta) htwo
    nlinarith
  · apply le_trans ((ceilDiv_le_iff_le_mul (by omega : 0 < p)).2
      (show t + 1 ≤ p * m by nlinarith))
    have h := Nat.mul_le_mul_right (m + delta) (show 1 ≤ p - 2 by omega)
    nlinarith

section OneField

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- Multiplying the full logarithm by `1-z` leaves `-z²/2` modulo
`3 ord(z)`. In degree three the term `-z³/2` is explicitly included. -/
private theorem q3_log_remainder {p d : ℕ}
    (hchar : residueCharacteristic E = p) (hp : 2 < p)
    {z : E} (hz : z ∈ lattice E (d : ℤ)) :
    (1 - z) * truncatedLog p z - z + z ^ 2 / 2 ∈
      lattice E ((3 * d : ℕ) : ℤ) := by
  have hrem := truncatedLog_sub_quadratic_mem E p d hchar (by omega) hz
  have hz0 := lattice_antitone E (show (0 : ℤ) ≤ d by omega) hz
  have hone : 1 - z ∈ lattice E 0 := (lattice E 0).sub_mem (by simp) hz0
  have hprod := mul_mem_lattice E hone hrem
  have hcubic := half_mem_lattice E hchar hp (pow_mem_lattice E hz 3)
  rw [zero_add] at hprod
  have htwo : (2 : E) ≠ 0 := (ord_ne_top_iff E).1 (by
    have ho := ord_natCast_eq_zero_of_lt_residueCharacteristic E (j := 2)
      (by omega) (by omega : 2 < residueCharacteristic E)
    norm_num only [Nat.cast_ofNat] at ho
    rw [ho]
    simp)
  convert (lattice E ((3 * d : ℕ) : ℤ)).sub_mem hprod hcubic using 1
  field_simp
  ring

/-- Evaluation using a full coefficient chart. The caller constructs that
chart from the minimal character and the actual descending pullback. -/
private theorem q3_quadratic
    {p n d : ℕ} (hchar : residueCharacteristic E = p) (hp : 2 < p)
    (hq : n ⌈/⌉ p ≤ d) (hcubic : n ≤ 3 * d) (hqpos : 0 < n ⌈/⌉ p)
    (theta : ContinuousQuasiChar E) (psi : LocalAddCharData E)
    (A C : Eˣ) (v : E) (hC : (C : E) = (A : E) - v)
    (hA : ord E (A : E) = ((-psi.conductor - (n : ℤ) : ℤ) : WithTop ℤ))
    (hz : v / (A : E) ∈ lattice E (d : ℤ))
    (hchart : ∀ x : unitFiltration E (n ⌈/⌉ p),
      theta x = psi.character ((C : E) *
        truncatedLog p (1 - ((x : Eˣ) : E)))) :
    (psi.character (-v) * theta (C / A))⁻¹ =
      psi.character (v ^ 2 / (2 * (A : E))) := by
  let z := v / (A : E)
  have hzq : z ∈ lattice E ((n ⌈/⌉ p : ℕ) : ℤ) :=
    lattice_antitone E (by exact_mod_cast hq) hz
  let x := positiveUnitOfLattice E hqpos (-⟨z, hzq⟩)
  have hx : (x : Eˣ) = C / A := by
    apply Units.ext
    simp only [x, coe_positiveUnitOfLattice, Submodule.coe_neg, Units.val_div_eq_div_val]
    change 1 + -z = (C : E) / (A : E)
    rw [hC]
    dsimp only [z]
    field_simp
    ring
  have hxz : 1 - ((x : Eˣ) : E) = z := by simp [x]
  have htheta := hchart x
  rw [hxz, hx] at htheta
  have hlog := q3_log_remainder E hchar hp hz
  have herr := mul_mem_lattice E ((mem_lattice E).2 hA.ge) hlog
  have htriv : psi.character
      ((-v + (C : E) * truncatedLog p z) -
        (-(v ^ 2 / (2 * (A : E))))) = 1 := by
    apply psi.isConductor.trivial
    apply lattice_antitone E (show -psi.conductor ≤
      (-psi.conductor - (n : ℤ)) + ((3 * d : ℕ) : ℤ) by omega)
    convert herr using 1
    rw [hC]
    dsimp only [z]
    field_simp
    ring
  have heq : psi.character (-v + (C : E) * truncatedLog p z) =
      psi.character (-(v ^ 2 / (2 * (A : E)))) := by
    apply div_eq_one.mp
    exact (psi.character.toAddChar.map_sub_eq_div _ _).symm.trans htriv
  rw [htheta, ← ContinuousAddChar.map_add_eq_mul, heq]
  change (psi.character.toAddChar (-_))⁻¹ = _
  rw [AddChar.map_neg_eq_inv, inv_inv]
  rfl

end OneField

section Edge

variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E]
  [Module.Free F E] [Module.Finite F E] [PrimeCyclicExtension F E]

/-- The first-edge norm phase with the exact norm of `w`, followed by
replacement of the actual norm denominator at its weighted precision. -/
private theorem q3_norm_denominator
    {p t m delta : ℕ} (hodd : 2 < p) (htpos : 0 < t)
    (hdegree : Module.finrank F E = p) (hres : residueDegree F E = 1)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hchar : residueCharacteristic F = p) (hmt : t < p * m)
    (e : LocalAddCharData F) (beta : Fˣ)
    (hbeta : ord F (beta : F) = ((-e.conductor - (t : ℤ) - 1 : ℤ) : WithTop ℤ))
    (nu : NormCharacter F E) (hnu : nu ≠ 1)
    (hnuFormula : ∀ x : unitFiltration F ((t + 1) ⌈/⌉ p),
      nu.1 x = e.character ((beta : F) *
        truncatedLog p (1 - ((x : Fˣ) : F))))
    (u k : Fˣ) (hu : ord F (u : F) = ((m : ℤ) : WithTop ℤ))
    (hk : ord F (k : F) = (((m + delta : ℕ) : ℤ) : WithTop ℤ))
    (b : E) (hb : ord E b = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (w : Eˣ) (hw : normUnits F E w = k⁻¹) :
    let B := 1 + algebraMap F E (u : F) * b
    let D := 1 + (u : F) ^ p * norm F E b
    let y := algebraMap F E (k : F) * (w : E) ^ 2 / B
    tracePullbackAddChar F E e.character (algebraMap F E (beta : F) * (y / 2)) =
      e.character (-(beta : F) * (k : F) ^ (p - 2) / (2 * D)) := by
  dsimp only
  let B := 1 + algebraMap F E (u : F) * b
  let D := 1 + (u : F) ^ p * norm F E b
  let P := norm F E B
  let y := algebraMap F E (k : F) * (w : E) ^ 2 / B
  obtain ⟨hB, hD, hP, _, hi, _⟩ := denominator_congruences F E
    (p := p) (t := t) (delta := 0) (m := m) hodd htpos hdegree hres
    (by simpa using ht) hmt (u : F) b hu hb
  change ord E B = 0 at hB
  change P⁻¹ - D⁻¹ ∈ lattice F ((m : ℤ) +
    (((p : ℤ) - 2) * t + ((p : ℤ) - 1) * (0 + 1)) / p) at hi
  have he : ramificationIndex F E = p := by
    simpa only [hdegree, hres, mul_one] using
      (finrank_eq_ramificationIndex_mul_residueDegree F E).symm
  have hwn : norm F E (w : E) = (k : F)⁻¹ := by
    simpa only [coe_normUnits, Units.val_inv_eq_inv_val] using congrArg Units.val hw
  have hwOrd : ord E (w : E) = ((-((m + delta : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
    have h := congrArg (ord F) hwn
    simpa only [ord_norm, hres, one_nsmul, ord_inv, hk,
      WithTop.LinearOrderedAddCommGroup.coe_neg] using h
  have hyOrd : ord E y = ((((p - 2) * (m + delta) : ℕ) : ℤ) : WithTop ℤ) := by
    dsimp only [y]
    rw [ord_div, ord_mul, ord_algebraMap, he, hk, ord_pow, hwOrd, hB, sub_zero]
    simp only [← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul,
      Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ p), Nat.cast_ofNat]
    congr 1
    ring
  have hqpos : 0 < (t + 1) ⌈/⌉ p := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_pos (by omega) (by omega)
  have hy : y ∈ lattice E (((t + 1) ⌈/⌉ p : ℕ) : ℤ) := by
    rw [mem_lattice, hyOrd, WithTop.coe_le_coe]
    exact_mod_cast (q3_depths (delta := delta) hodd hmt).2.2
  have hbetaInt : unitOrder F beta = -e.conductor - (t : ℤ) - 1 := by
    rw [ord_coe_eq_unitOrder] at hbeta
    exact WithTop.coe_injective hbeta
  have hPsi : IsAdditiveConductor F (scaleAddCharData F e beta).character
      (-((t + 1 : ℕ) : ℤ)) := by
    convert (scaleAddCharData F e beta).isConductor using 1
    rw [scaleAddCharData_conductor, hbetaInt]
    push_cast
    ring
  have hchart : ∀ z : lattice F (((t + 1) ⌈/⌉ p : ℕ) : ℤ),
      nu.1 (positiveUnitOfLattice F hqpos (-z)) =
        (scaleAddCharData F e beta).character (truncatedLog p (z : F)) := by
    intro z
    simpa using hnuFormula (positiveUnitOfLattice F hqpos (-z))
  have hphase := (normPhase_half F E ht htpos hres
    (hchar.trans hdegree.symm) (by omega) ((t + 1) ⌈/⌉ p)
    (by rw [hdegree]) hqpos nu hnu (scaleAddCharData F e beta).character
    hPsi (by simpa only [hdegree] using hchart) y hy).1
  have hnorm : norm F E y = (k : F) ^ (p - 2) / P := by
    dsimp only [y, P]
    rw [div_eq_mul_inv, map_mul, map_mul, map_pow,
      LanglandsFirstMainLemma.norm_algebraMap, hdegree, hwn, Algebra.norm_inv,
      pow_sub₀ (k : F) (Units.ne_zero k) (by omega : 2 ≤ p)]
    simp only [div_eq_mul_inv, inv_pow]
  have hweight : (k : F) ^ (p - 2) * (P⁻¹ - D⁻¹) ∈ lattice F (1 + (t : ℤ)) := by
    have hwgt : (k : F) ^ (p - 2) ∈ lattice F (((p : ℤ) - 2) * m) := by
      rw [mem_lattice, ord_pow, hk, ← WithTop.coe_nsmul, WithTop.coe_le_coe,
        nsmul_eq_mul, Nat.cast_sub (by omega : 2 ≤ p), Nat.cast_ofNat, Nat.cast_add]
      have h := mul_nonneg (show (0 : ℤ) ≤ p - 2 by omega) (show (0 : ℤ) ≤ delta by omega)
      nlinarith
    have hd := (weighted_depths (p : ℤ) t 0 m (by omega)
      (by omega) (by omega) (by exact_mod_cast hmt)).1
    apply lattice_antitone F (by simpa using hd)
    simpa only [zero_add, mul_one] using mul_mem_lattice F hwgt hi
  have herror := mul_mem_lattice F ((mem_lattice F).2 hbeta.ge)
    (half_mem_lattice F hchar hodd hweight)
  have heq : e.character ((beta : F) * (-norm F E y / 2)) =
      e.character (-(beta : F) * (k : F) ^ (p - 2) / (2 * D)) := by
    apply div_eq_one.mp
    change e.character.toAddChar _ / e.character.toAddChar _ = 1
    rw [← AddChar.map_sub_eq_div]
    apply e.isConductor.trivial
    convert (lattice F _).neg_mem herror using 1
    · congr 1
      omega
    · rw [hnorm]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
  change tracePullbackAddChar F E e.character (algebraMap F E (beta : F) * (y / 2)) = _
  rw [tracePullbackAddChar_apply, scaleAddCharData_character_apply,
    scaleAddCharData_character_apply] at hphase
  rw [tracePullbackAddChar_apply, ← Algebra.smul_def, map_smul, smul_eq_mul,
    hphase, heq]

end Edge

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

local notation "B₁" => R.B₁
local notation "B₂" => R.B₂

local instance : PrimeCyclicExtension F B₁ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₁
    (Basic.intermediateField_tower_compatible hp hG B₁ R.degree_B₁).2.2.2.2.2.2.2.2.2.2.2.1

set_option maxHeartbeats 800000 in
/-- **Paper Lemma 9.28 (`O:T:Q3`, `O:T:Q3phase`).**

Evaluate the literal third factor of `fourFactorValues` for the actual
odd totally ramified diamond. The first minimal chart and the descending
base-character chart construct the full chart of the twisted character.
`A₁` and `C₁` have the exact equations supplied by `fourFactors`; the
exact lower norm of `w₁` is the preserved choice of `normChoice`.

The norm phase and the weighted denominator replacement are proved at
their whole-ideal moduli. The rational half stays outside the norm, and
both field characteristics and the boundary `p = 3` are included.
Only the first-edge data are needed: `phi`, `w₂`, and `C₂` merely identify
the same four-factor record as in Proposition 8.20. -/
theorem q3
    (hres : residueDegree F K = 1)
    (e : LocalAddCharData F) (alpha beta gamma : Fˣ)
    (Delta : K) (hDelta : ord K Delta = ((-(R.t : ℤ) : ℤ) : WithTop ℤ))
    (chi : ContinuousQuasiChar B₁) (phi : ContinuousQuasiChar B₂)
    (hchiFormula : ∀ x : unitFiltration B₁ (Models.firstModelDepth R),
      chi x = tracePullbackAddChar F B₁ e.character
        (algebraMap F B₁ (alpha : F) * norm B₁ K Delta *
          truncatedLog p (1 - ((x : B₁ˣ) : B₁))))
    {m : ℕ} (hmt : R.t < p * m)
    (lambda : ContinuousQuasiChar F)
    (hlambda : IsMultiplicativeConductor F lambda (R.t₂ + m + 1))
    (hgamma : ord F (gamma : F) =
      ((-e.conductor - ((R.t₂ + m : ℕ) : ℤ) - 1 : ℤ) : WithTop ℤ))
    (hlambdaFormula : ∀ x : unitFiltration F ((R.t₂ + m + 1) ⌈/⌉ p),
      lambda x = e.character ((gamma : F) *
        truncatedLog p (1 - ((x : Fˣ) : F))))
    (nu : NormCharacter F B₁) (hnu : nu ≠ 1)
    (hbeta : ord F (beta : F) =
      ((-e.conductor - (R.t : ℤ) - 1 : ℤ) : WithTop ℤ))
    (halpha : ord F (alpha : F) =
      ((-e.conductor - (R.t₂ : ℤ) - 1 : ℤ) : WithTop ℤ))
    (hnuFormula : ∀ x : unitFiltration F ((R.t + 1) ⌈/⌉ p),
      nu.1 x = e.character ((beta : F) *
        truncatedLog p (1 - ((x : Fˣ) : F))))
    (w₁ A₁ C₁ : B₁ˣ) (w₂ C₂ : B₂ˣ)
    (hw₁ : normUnits F B₁ w₁ = gamma / beta)
    (hA₁ : (A₁ : B₁) = algebraMap F B₁ (gamma : F) +
      algebraMap F B₁ (alpha : F) * norm B₁ K Delta)
    (hC₁ : (C₁ : B₁) = (A₁ : B₁) -
      algebraMap F B₁ (beta : F) * (w₁ : B₁)) :
    let u := (alpha : F) / (gamma : F)
    let W := u⁻¹
    let v := (beta : F) / (alpha : F)
    let A₀ := norm F B₂ (norm B₂ K Delta)
    let D := 1 + u ^ p * A₀
    let Psi := (scaleAddCharData F e alpha).character
    let Q := Parameters.fourFactorValues F B₁ B₂ chi phi lambda e.character
      alpha beta w₁ A₁ C₁ w₂ C₂
    Q.Q₃⁻¹ = Psi (-W / 2 * (v * u) ^ (p - 1) / D) := by
  dsimp only
  let u : Fˣ := alpha / gamma
  let k : Fˣ := beta / gamma
  let b := norm B₁ K Delta
  let B := 1 + algebraMap F B₁ (u : F) * b
  let n := 1 + R.t + p * (m + R.delta)
  let d := (p - 1) * (m + R.delta)
  obtain ⟨_, hrF, hrK, he, _⟩ :=
    realization_tower_data hp hG hres B₁ R.degree_B₁
  have hm : 0 < m := by have := R.t_pos; nlinarith
  have hr : R.t < R.t₂ + m := by have := R.t_le_t₂; omega
  have hh : R.t₂ + m - R.t = m + R.delta := by have := R.t₂_eq; omega
  obtain ⟨hqe, _, hadd, hbase, hbaseOrder, hpull⟩ := Parameters.pullback F B₁
    R.degree_B₁ R.odd_prime R.B₁_breaks.1 R.t_pos hr hrF
    lambda hlambda e gamma beta hgamma hlambdaFormula nu hnu hbeta hnuFormula w₁ hw₁
  rw [hh] at hqe hbaseOrder hpull
  rw [hqe] at hpull
  let psi : LocalAddCharData B₁ := ⟨tracePullbackAddChar F B₁ e.character, _, hadd⟩
  have hchar : residueCharacteristic F = p := by
    obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F B₁ hrF
    exact (residueCharacteristic_eq_degree_of_positive_isLowerBreak F B₁
      R.B₁_breaks.1 R.t_pos pi hpi hgen).trans R.degree_B₁
  have hchar₁ : residueCharacteristic B₁ = p :=
    (residueCharacteristic_extension_eq F B₁).trans hchar
  have hu : ord F (u : F) = ((m : ℤ) : WithTop ℤ) := by
    simp only [u, Units.val_div_eq_div_val]
    rw [ord_div, halpha, hgamma, ← WithTop.LinearOrderedAddCommGroup.coe_sub]
    congr 1
    push_cast
    ring
  have hk : ord F (k : F) = (((m + R.delta : ℕ) : ℤ) : WithTop ℤ) := by
    simp only [k, Units.val_div_eq_div_val]
    rw [ord_div, hbeta, hgamma, ← WithTop.LinearOrderedAddCommGroup.coe_sub]
    congr 1
    rw [R.t₂_eq]
    push_cast
    ring
  have hb : ord B₁ b = ((-(R.t : ℤ) : ℤ) : WithTop ℤ) := by
    dsimp only [b]
    rw [ord_norm, hrK, one_nsmul, hDelta]
  obtain ⟨hB, _, _, _, _, _⟩ := denominator_congruences F B₁
    (p := p) (t := R.t) (delta := 0) (m := m) R.odd_prime R.t_pos R.degree_B₁
    hrF R.B₁_breaks.1 hmt (u : F) b hu hb
  change ord B₁ B = 0 at hB
  have hAfac : (A₁ : B₁) = algebraMap F B₁ (gamma : F) * B := by
    rw [hA₁]
    simp only [B, b, u, Units.val_div_eq_div_val]
    rw [map_div₀]
    field_simp
  have hAo : ord B₁ (A₁ : B₁) = p • ord F (gamma : F) := by
    rw [hAfac, ord_mul, ord_algebraMap, he, hB, add_zero]
  have hAord : ord B₁ (A₁ : B₁) = ((-psi.conductor - (n : ℤ) : ℤ) : WithTop ℤ) :=
    hAo.trans (hbase.symm.trans hbaseOrder)
  have hwk : normUnits F B₁ w₁ = k⁻¹ := by
    rw [hw₁]
    simp only [k, inv_div]
  have hwOrd : ord B₁ (w₁ : B₁) = ((-((m + R.delta : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
    have hwn := congrArg (fun x : Fˣ ↦ ord F (x : F)) hwk
    simpa only [coe_normUnits, ord_norm, hrF, one_nsmul, Units.val_inv_eq_inv_val,
      ord_inv, hk, WithTop.LinearOrderedAddCommGroup.coe_neg] using hwn
  have hz : algebraMap F B₁ (beta : F) * (w₁ : B₁) / (A₁ : B₁) ∈
      lattice B₁ (d : ℤ) := by
    rw [mem_lattice, ord_div, ord_mul, ord_algebraMap, he, hAo,
      hbeta, hgamma, hwOrd]
    simp only [← WithTop.coe_nsmul, ← WithTop.coe_add,
      ← WithTop.LinearOrderedAddCommGroup.coe_sub, WithTop.coe_le_coe, nsmul_eq_mul]
    dsimp only [d]
    rw [R.t₂_eq]
    push_cast [Nat.cast_sub hp.one_le]
    nlinarith
  have hdepth := q3_depths (delta := R.delta) R.odd_prime hmt
  have hqpos : 0 < n ⌈/⌉ p := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    apply Nat.div_pos (by dsimp only [n]; omega) hp.pos
  have hchiDepth : Models.firstModelDepth R ≤ n ⌈/⌉ p := by
    change Models.firstModelConductor R ⌈/⌉ p ≤ n ⌈/⌉ p
    apply (ceilDiv_le_iff_le_mul hp.pos).2
    have hn : Models.firstModelConductor R ≤ n := by
      dsimp only [Models.firstModelConductor, n]
      rw [R.tPrime_eq]
      nlinarith
    exact hn.trans ((ceilDiv_le_iff_le_mul hp.pos).1 le_rfl)
  have hfull : ∀ x : unitFiltration B₁ (n ⌈/⌉ p),
      (chi * lambda.compNorm (S := B₁)) x = psi.character ((C₁ : B₁) *
        truncatedLog p (1 - ((x : B₁ˣ) : B₁))) := by
    intro x
    let x₀ : unitFiltration B₁ (Models.firstModelDepth R) :=
      ⟨(x : B₁ˣ), unitFiltration_antitone B₁ hchiDepth x.property⟩
    have hchi := hchiFormula x₀
    have hl := hpull x
    rw [ContinuousQuasiChar.mul_apply, hchi, hl]
    rw [← ContinuousAddChar.map_add_eq_mul]
    congr 1
    rw [hC₁, hA₁]
    dsimp only [x₀]
    ring
  have hquad := q3_quadratic B₁ hchar₁ R.odd_prime hdepth.1 hdepth.2.1 hqpos
    (chi * lambda.compNorm (S := B₁)) psi A₁ C₁
    (algebraMap F B₁ (beta : F) * (w₁ : B₁)) hC₁ hAord hz hfull
  have hnorm := q3_norm_denominator F B₁ R.odd_prime R.t_pos R.degree_B₁ hrF
    R.B₁_breaks.1 hchar hmt e beta hbeta nu hnu hnuFormula u k hu hk b hb w₁ hwk
  have harg : (algebraMap F B₁ (beta : F) * (w₁ : B₁)) ^ 2 / (2 * (A₁ : B₁)) =
      algebraMap F B₁ (beta : F) *
        ((algebraMap F B₁ (k : F) * (w₁ : B₁) ^ 2 / B) / 2) := by
    rw [hAfac]
    simp only [k, Units.val_div_eq_div_val]
    rw [map_div₀]
    field_simp
  change (tracePullbackAddChar F B₁ e.character
      (-algebraMap F B₁ (beta : F) * (w₁ : B₁)) *
        (chi * lambda.compNorm (S := B₁)) (C₁ / A₁))⁻¹ = _
  rw [neg_mul, hquad, harg, hnorm, scaleAddCharData_character_apply]
  congr 1
  have hnormb : norm F B₁ b = norm F B₂ (norm B₂ K Delta) := by
    dsimp only [b]
    rw [norm_trans, norm_trans]
  rw [hnormb]
  simp only [u, k, Units.val_div_eq_div_val]
  have hexp : p - 1 = p - 2 + 1 := by have := R.odd_prime; omega
  rw [hexp, pow_succ]
  field_simp

end Diamond

end

end LanglandsSecondMainLemma.Odd.Transition
