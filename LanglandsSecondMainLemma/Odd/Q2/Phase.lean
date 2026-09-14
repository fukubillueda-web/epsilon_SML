import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Odd.Q2.ZCongruence

/-!
# The actual second phase

Paper Theorem 9.17 (`O:N:Q2`). The norm quotient and the inverse of `Z`
use separate conductor bounds. All norms and character arguments retain
their actual fields, and `W = gamma / alpha` supplies the base normalization.
-/
namespace LanglandsSecondMainLemma.Odd.Q2

open LanglandsFirstMainLemma
noncomputable section

/-- The floor estimate in `O:N:Q2`, including the smallest conductor. -/
theorem phase_floor_bound (p n : ℤ) (hp : 3 ≤ p) (hn : 2 ≤ n) :
    n ≤ 2 * (((p - 1) * n) / p) := by
  have hp0 : 0 < p := by omega
  have hhalf : (n + 1) / 2 ≤ ((p - 1) * n) / p := by
    apply (Int.le_ediv_iff_mul_le hp0).2
    have hdiv := Int.mul_ediv_add_emod (n + 1) 2
    have hmod := Int.emod_nonneg (n + 1) (by omega : (2 : ℤ) ≠ 0)
    by_cases hn2 : n = 2
    · subst n
      norm_num
      omega
    · have hprod : 0 ≤ (p - 3) * (n - 1) := mul_nonneg (by omega) (by omega)
      nlinarith
  have hrem := Int.emod_lt_of_pos (n + 1) (by omega : (0 : ℤ) < 2)
  have heq := Int.mul_ediv_add_emod (n + 1) 2
  omega

/-- The depth of the first small argument, independent of the floor bound. -/
theorem phase_linear_bound (p t d m : ℤ)
    (hp : 3 ≤ p) (ht : 1 ≤ t) (hd : 0 ≤ d) (hm : t < p * m) :
    1 ≤ m ∧ 1 ≤ (p - 1) * (m + d) ∧
      t + d + m + 1 ≤ 2 * ((p - 1) * (m + d)) := by
  have hmpos : 1 ≤ m := by nlinarith
  have hprod : 0 ≤ (p - 3) * m := mul_nonneg (by omega) (by omega)
  have hdprod : 0 ≤ (2 * p - 3) * d := mul_nonneg (by omega) hd
  constructor
  · exact hmpos
  constructor <;> nlinarith

open private truncatedLog_sub_linear_mem from
  LanglandsSecondMainLemma.Odd.EnhancedStationary
open private lamprechtAddChar_eq_of_sub_mem from
  LanglandsFirstMainLemma.Lamprecht.Formula

/-- Evaluate the inverse at the full conductor. The input congruence is
additive; the proof uses the full logarithm on `Z` itself, so no shallow
individual-factor linearization is invoked. -/
theorem phase_inverse_of_congruence
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {p : ℕ} (hp : 2 < p) (hchar : residueCharacteristic F = p)
    (lambda : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (hn : 2 ≤ lambda.conductor) (gamma : Fˣ)
    (hgamma : ord F (gamma : F) =
      ((-psi.conductor - (lambda.conductor : ℤ) : ℤ) : WithTop ℤ))
    (hformula : ∀ u : unitFiltration F (lambda.conductor ⌈/⌉ p),
      lambda.character u = psi.character
        ((gamma : F) * truncatedLog p (1 - ((u : Fˣ) : F))))
    (Z : Fˣ) (x : F) (L : ℤ) (hL : 1 ≤ L)
    (hdepth : (lambda.conductor : ℤ) ≤ 2 * L)
    (hx : x ∈ lattice F L)
    (hZ : (Z : F) - (1 + x) ∈ lattice F (lambda.conductor : ℤ)) :
    (lambda.character Z)⁻¹ = psi.character ((gamma : F) * x) := by
  let b : ℕ := lambda.conductor ⌈/⌉ 2
  have hbpos : 0 < b := by
    dsimp only [b]
    rw [Nat.ceilDiv_eq_add_pred_div]
    omega
  have hnb : lambda.conductor ≤ 2 * b :=
    (ceilDiv_le_iff_le_mul (by omega : 0 < 2)).1 le_rfl
  have hbL : (b : ℤ) ≤ L := by
    have hLnat : (L.toNat : ℤ) = L := Int.toNat_of_nonneg (by omega)
    have h : b ≤ L.toNat := (ceilDiv_le_iff_le_mul (by omega : 0 < 2)).2 (by
      exact_mod_cast (show (lambda.conductor : ℤ) ≤ 2 * (L.toNat : ℤ) by
        simpa [hLnat] using hdepth))
    exact_mod_cast (show (b : ℤ) ≤ L by simpa [hLnat] using (Int.ofNat_le.mpr h))
  have hbn : b ≤ lambda.conductor := by
    apply (ceilDiv_le_iff_le_mul (by omega : 0 < 2)).2
    omega
  have hsmall : (Z : F) - 1 ∈ lattice F (b : ℤ) := by
    convert add_mem_lattice F
      (lattice_antitone F (Int.ofNat_le.mpr hbn) hZ)
      (lattice_antitone F hbL hx) using 1
    ring
  have hZu : Z ∈ unitFiltration F b := by
    rw [← Nat.sub_add_cancel hbpos, mem_unitFiltration_succ_iff_sub_mem_lattice,
      Nat.sub_add_cancel hbpos]
    exact hsmall
  have hceil : lambda.conductor ⌈/⌉ p ≤ b :=
    (ceilDiv_le_iff_le_mul (by omega : 0 < p)).2
      (hnb.trans (Nat.mul_le_mul_right b (by omega)))
  have hlog := truncatedLog_sub_linear_mem F p b hchar (neg_mem_lattice F hsmall)
  have herr : truncatedLog p (1 - (Z : F)) - -x ∈
      lattice F (lambda.conductor : ℤ) := by
    have hlog' : truncatedLog p (1 - (Z : F)) - (1 - (Z : F)) ∈
        lattice F (lambda.conductor : ℤ) := by
      apply lattice_antitone F (Int.ofNat_le.mpr hnb)
      simpa only [neg_sub] using hlog
    convert add_mem_lattice F hlog' (neg_mem_lattice F hZ) using 1
    ring
  have heq : lambda.character Z = psi.character (-((gamma : F) * x)) := by
    rw [hformula ⟨Z, unitFiltration_antitone F hceil hZu⟩]
    apply lamprechtAddChar_eq_of_sub_mem F psi
    have h := mul_mem_lattice F ((mem_lattice F).2 hgamma.ge) herr
    simpa only [mul_sub, mul_neg, sub_neg_eq_add, mul_add, sub_add_cancel] using h
  rw [heq]
  have hneg : psi.character (-((gamma : F) * x)) =
      (psi.character ((gamma : F) * x))⁻¹ := psi.character.toAddChar.map_neg_eq_inv _
  rw [hneg, inv_inv]

set_option backward.isDefEq.respectTransparency false

open private realization_tower_data from LanglandsSecondMainLemma.Odd.Models.Realization
open private exact_coordinate_orders_and_generation from
  LanglandsSecondMainLemma.Odd.Total.ASCoordinate
open private ord_eq_zero_of_sub_one from LanglandsSecondMainLemma.Odd.Q2.ZCongruence

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
local instance : PrimeCyclicExtension B₁ K :=
  PrimeCyclicExtension.ofCyclicPrimeExtension B₁ K
    (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.2.2.2.2
local instance : PrimeCyclicExtension B₂ K :=
  PrimeCyclicExtension.ofCyclicPrimeExtension B₂ K
    (Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.2

include hres hchar

set_option maxHeartbeats 1000000 in
/-- **Paper Theorem 9.17 (`O:N:Q2`).** The literal second factor, with the
actual units `A₁,C₂` supplied by `fourFactors` and the same coordinate and
exact norm witness as `zCongruence`. The only character formula assumed is
its full base chart, as in the paper's setup and `fourFactors`; no phase
identity or shallow-factor evaluation is assumed. `u = alpha/gamma` and
`W = gamma/alpha` implement the base normalization explicitly. -/
theorem phase
    (Delta : K)
    (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ D.t)
    (hroot : Delta ^ p - Delta = algebraMap B₂ K (norm B₂ K Delta))
    (lambda : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (alpha gamma : Fˣ) (m : ℤ)
    (hu : ord F ((alpha / gamma : Fˣ) : F) = (m : WithTop ℤ))
    (hm : (D.t : ℤ) < (p : ℤ) * m)
    (hn : (lambda.conductor : ℤ) = (D.t₂ : ℤ) + m + 1)
    (hgamma : ord F (gamma : F) =
      ((-psi.conductor - (lambda.conductor : ℤ) : ℤ) : WithTop ℤ))
    (hformula : ∀ u : unitFiltration F (lambda.conductor ⌈/⌉ p),
      lambda.character u = psi.character
        ((gamma : F) * truncatedLog p (1 - ((u : Fˣ) : F))))
    (w : B₂ˣ) (hw : normUnits F B₂ w = gamma / alpha)
    (A₁ : B₁ˣ) (C₂ : B₂ˣ)
    (hA₁ : (A₁ : B₁) = algebraMap F B₁ (gamma : F) +
      algebraMap F B₁ (alpha : F) * norm B₁ K Delta)
    (hC₂ : (C₂ : B₂) = algebraMap F B₂ (gamma : F) -
      algebraMap F B₂ (alpha : F) * (w : B₂) +
      algebraMap F B₂ (alpha : F) * norm B₂ K Delta) :
    let u : F := ((alpha / gamma : Fˣ) : F)
    let W : F := ((gamma / alpha : Fˣ) : F)
    let a := norm B₂ K Delta
    let H := norm F B₁ (-elementarySymmetric B₁ K (p - 1) Delta)
    let C := 1 + algebraMap F B₂ u * a
    let Pstar := norm F B₂ C
    let Y := Pstar - u ^ (p - 1)
    let D₀ := 1 + u ^ p * norm F B₂ a
    let k := algebraMap F B₂ u * (w : B₂) / C
    let Fstar := Pstar / Y
    (lambda.character (normUnits F B₁ A₁ / normUnits F B₂ C₂))⁻¹ =
      psi.character ((alpha : F) * (W * u ^ (p - 1) * H / D₀)) *
      tracePullbackAddChar F B₂ psi.character
        (algebraMap F B₂ (alpha : F) *
          (algebraMap F B₂ (W * Fstar) * truncatedLog p k)) := by
  classical
  let u : Fˣ := alpha / gamma
  let a := norm B₂ K Delta
  let b₀ := norm B₁ K Delta
  let s := -elementarySymmetric B₁ K (p - 1) Delta
  let H := norm F B₁ s
  let C := 1 + algebraMap F B₂ (u : F) * a
  let Pstar := norm F B₂ C
  let q := (u : F) ^ (p - 1)
  let Y := Pstar - q
  let D₀ := 1 + (u : F) ^ p * norm F B₂ a
  let k := algebraMap F B₂ (u : F) * (w : B₂) / C
  let N := norm F B₁ (1 + algebraMap F B₁ (u : F) * b₀)
  let L : ℤ := ((p : ℤ) - 1) * (m + D.delta)
  change ord F (u : F) = (m : WithTop ℤ) at hu
  have hwu : normUnits F B₂ w = u⁻¹ := by simpa only [u, inv_div] using hw
  have hpZ : (3 : ℤ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := D.odd_prime; omega)
  have htZ : (1 : ℤ) ≤ D.t := by exact_mod_cast D.t_pos
  have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
  obtain ⟨hmpos, hLpos, hLdepth⟩ := phase_linear_bound p D.t D.delta m
    hpZ htZ (by positivity) hm
  change 1 ≤ L at hLpos
  have hdepth : (lambda.conductor : ℤ) ≤ 2 * L := by
    rw [hn, ht₂]
    exact hLdepth
  have hn2 : 2 ≤ lambda.conductor := by have := D.t_le_t₂; omega
  obtain ⟨_, hresF₁, _, _, _⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  obtain ⟨hd₂, hresF₂, hres₂K, he₂, he₂K⟩ :=
    realization_tower_data hp hG hres B₂ D.degree_B₂
  have hCsmall : C - 1 ∈ lattice B₂ 1 := by
    dsimp only [C, a]
    rw [add_sub_cancel_left, mem_lattice, ord_mul, ord_algebraMap, he₂, hu,
      ord_norm, hres₂K, one_nsmul, hDelta, ← WithTop.coe_nsmul,
      ← WithTop.coe_add, WithTop.coe_le_coe, nsmul_eq_mul]
    omega
  have hCo := ord_eq_zero_of_sub_one B₂ hCsmall
  have hCne : C ≠ 0 := (ord_ne_top_iff B₂).1 (by rw [hCo]; exact WithTop.coe_ne_top)
  have hPo : ord F Pstar = 0 := by simp only [Pstar, ord_norm, hresF₂, one_nsmul, hCo]
  have hPne : Pstar ≠ 0 := (ord_ne_top_iff F).1 (by rw [hPo]; exact WithTop.coe_ne_top)
  have hqo : ord F q = ((((p : ℤ) - 1) * m : ℤ) : WithTop ℤ) := by
    simp only [q, ord_pow, hu, ← WithTop.coe_nsmul, nsmul_eq_mul,
      Nat.cast_sub hp.one_le, Nat.cast_one]
  have hYo : ord F Y = 0 := by
    dsimp only [Y]
    rw [(ord F).map_sub_eq_of_lt_left, hPo]
    rw [hPo, hqo]
    exact_mod_cast (show (0 : ℤ) < ((p : ℤ) - 1) * m by nlinarith)
  have hYne : Y ≠ 0 := (ord_ne_top_iff F).1 (by rw [hYo]; exact WithTop.coe_ne_top)
  have hDsmall : D₀ - 1 ∈ lattice F 1 := by
    dsimp only [D₀, a]
    rw [add_sub_cancel_left, mem_lattice, ord_mul, ord_pow, hu,
      ord_norm, hresF₂, one_nsmul, ord_norm, hres₂K, one_nsmul, hDelta,
      ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe, nsmul_eq_mul]
    omega
  have hDo := ord_eq_zero_of_sub_one F hDsmall
  obtain ⟨_, hgen⟩ := exact_coordinate_orders_and_generation B₂ K hp D.t_pos
    hd₂ he₂K Delta a hDelta hprime hroot
  obtain ⟨_, _, _, hs⟩ := Models.realization_twistedEstimates_of_coordinate
    hp hG hres hchar D Delta a hroot hDelta hprime hgen
  have hH : H ∈ lattice F (((p : ℤ) - 1) * D.delta) := by
    simpa only [H, s, mem_lattice, ord_norm, hresF₁, one_nsmul] using hs
  have hx : q * H / D₀ ∈ lattice F L := by
    rw [div_mem_lattice_iff F D₀ _ 0 _ hDo, zero_add]
    simpa only [L, mul_add] using
      mul_mem_lattice F ((mem_lattice F).2 hqo.ge) hH
  let Abar : B₁ˣ := A₁ / Units.map (algebraMap F B₁) gamma
  let Cbar : B₂ˣ := C₂ / Units.map (algebraMap F B₂) gamma
  have hAbar : (Abar : B₁) = 1 + algebraMap F B₁ (u : F) * b₀ := by
    simp only [Abar, Units.val_div_eq_div_val, Units.coe_map]
    change (A₁ : B₁) / algebraMap F B₁ (gamma : F) = _
    rw [hA₁]
    simp only [u, b₀, Units.val_div_eq_div_val, map_div₀]
    field_simp
  have hCbar : (Cbar : B₂) = C * (1 - k) := by
    calc
      (Cbar : B₂) = C - algebraMap F B₂ (u : F) * (w : B₂) := by
        simp only [Cbar, Units.val_div_eq_div_val, Units.coe_map]
        change (C₂ : B₂) / algebraMap F B₂ (gamma : F) = _
        rw [hC₂]
        simp only [C, u, a, Units.val_div_eq_div_val, map_div₀]
        field_simp
        ring
      _ = C * (1 - k) := by
        dsimp only [k]
        field_simp [hCne]
  have hNne : N ≠ 0 := by
    have h := Units.ne_zero (normUnits F B₁ Abar)
    simpa only [coe_normUnits, hAbar] using h
  let Z : Fˣ := Units.mk0 (N / Y) (div_ne_zero hNne hYne)
  have hZ := zCongruence hp hG hres hchar D Delta hDelta hprime hroot
    u w hwu m hu hm
  have hfirst := phase_inverse_of_congruence F D.odd_prime hchar lambda psi hn2 gamma
    hgamma hformula Z (q * H / D₀) L hLpos hdepth hx (by
      simpa only [Z, Units.val_mk0, N, Y, Pstar, C, q, H, s, D₀, a, b₀, hn] using hZ)
  have hwo : ord B₂ (w : B₂) = ((-m : ℤ) : WithTop ℤ) := by
    have h := congrArg (fun x : Fˣ ↦ ord F (x : F)) hwu
    simpa only [coe_normUnits, ord_norm, hresF₂, one_nsmul,
      Units.val_inv_eq_inv_val, ord_inv, hu,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg] using h
  have hko : ord B₂ k = ((((p : ℤ) - 1) * m : ℤ) : WithTop ℤ) := by
    simp only [k, ord_div, ord_mul, ord_algebraMap, he₂, hu, hwo, hCo,
      sub_zero, ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul]
    congr 1
    ring
  have hka : 1 ≤ ((p : ℤ) - 1) * m := by nlinarith
  have hk : k ∈ lattice B₂ (((p : ℤ) - 1) * m) := (mem_lattice B₂).2 hko.ge
  have hNk : norm F B₂ k = q / Pstar := by
    have hdegree : Module.finrank F B₂ = p := D.degree_B₂
    have hwval := congrArg (fun x : Fˣ ↦ (x : F)) hwu
    simp only [coe_normUnits, Units.val_inv_eq_inv_val] at hwval
    have hpower : (u : F) ^ p * (u : F)⁻¹ = (u : F) ^ (p - 1) := by
      rw [show p = (p - 1) + 1 from (Nat.sub_add_cancel hp.one_le).symm, pow_succ]
      simp only [mul_assoc, mul_inv_cancel₀ (Units.ne_zero u), mul_one, Nat.add_sub_cancel]
    calc
      norm F B₂ k = ((u : F) ^ p * (u : F)⁻¹) / Pstar := by
        simp only [k, div_eq_mul_inv, map_mul, LanglandsFirstMainLemma.norm_algebraMap,
          hdegree, Algebra.norm_inv, hwval, Pstar]
      _ = q / Pstar := by rw [hpower]
  have hnormdepth : (lambda.conductor : ℤ) ≤
      2 * ((((p : ℤ) - 1) * m + ((p : ℤ) - 1) * ((D.t₂ : ℤ) + 1)) / p) := by
    have h := phase_floor_bound p lambda.conductor hpZ (by exact_mod_cast hn2)
    convert h using 1
    rw [hn]
    congr 2
    ring
  let R := normQuotientUnit F B₂ hresF₂ hka k hk
  have hsecond := normQuotient F B₂ D.degree_B₂ D.odd_prime D.B₂_breaks.1
    (D.t_pos.trans_le D.t_le_t₂) hresF₂ lambda psi hn2 gamma hgamma
    hformula hka k hk hnormdepth
  have hnormgamma (E : Type) [Field E] [Algebra F E] [Module.Free F E]
      [Module.Finite F E] (hdegree : Module.finrank F E = p) :
      normUnits F E (Units.map (algebraMap F E) gamma) = gamma ^ p := by
    apply Units.ext
    change norm F E (algebraMap F E (gamma : F)) = (gamma : F) ^ p
    rw [LanglandsFirstMainLemma.norm_algebraMap, hdegree]
  have hcancel : normUnits F B₁ A₁ / normUnits F B₂ C₂ =
      normUnits F B₁ Abar / normUnits F B₂ Cbar := by
    simp only [Abar, Cbar, map_div, hnormgamma B₁ D.degree_B₁, hnormgamma B₂ D.degree_B₂]
    exact (div_div_div_cancel_right _ _ _).symm
  have hexact : (normUnits F B₁ A₁ / normUnits F B₂ C₂)⁻¹ = Z⁻¹ * R := by
    rw [hcancel]
    apply Units.ext
    simp only [Units.val_inv_eq_inv_val, Units.val_div_eq_div_val, Units.val_mul,
      coe_normUnits, hAbar, hCbar, map_mul, R, coe_normQuotientUnit, hNk]
    change (N / (Pstar * norm F B₂ (1 - k)))⁻¹ =
      (N / Y)⁻¹ * (norm F B₂ (1 - k) / (1 - q / Pstar))
    dsimp only [Y] at hYne ⊢
    field_simp
  have hphase : (lambda.character (normUnits F B₁ A₁ / normUnits F B₂ C₂))⁻¹ =
      psi.character ((gamma : F) * (q * H / D₀)) *
        tracePullbackAddChar F B₂ psi.character
          (algebraMap F B₂ ((gamma : F) / (1 - norm F B₂ k)) * truncatedLog p k) := by
    rw [← map_inv, hexact, map_mul, map_inv, hfirst, hsecond]
  rw [hphase]
  congr 1
  · congr 1
    dsimp only [q]
    simp only [Units.val_div_eq_div_val]
    field_simp
    simp only [u, H, s, D₀, a, Units.val_div_eq_div_val]
  · congr 1
    have hcoeff : (gamma : F) / (1 - norm F B₂ k) =
        (alpha : F) * (((gamma / alpha : Fˣ) : F) * (Pstar / Y)) := by
      rw [hNk]
      simp only [Units.val_div_eq_div_val, Y]
      field_simp
    rw [hcoeff, map_mul]
    exact mul_assoc _ _ _

end Diamond

end
end LanglandsSecondMainLemma.Odd.Q2
