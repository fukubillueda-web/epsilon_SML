import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Odd.Q1.Logarithm
import LanglandsSecondMainLemma.Odd.Q2.Phase
import LanglandsSecondMainLemma.Odd.Transition.ElementaryPhase
import LanglandsSecondMainLemma.Odd.Transition.NormHalf

/-!
# Odd / Transition / Q124

Paper Proposition 9.27 (`O:T:Q124`). The signed linear packet and the
quadratic trace are combined in the common field before substituting the
literal constant projections in the second lower field. Every discarded
coefficient is controlled in a whole ideal. The rational half stays
outside the lower norm.
-/

namespace LanglandsSecondMainLemma.Odd.Transition

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

section Algebra

variable {E : Type*} [Field E]

/-- Sum the signed packet before reducing any rational coefficient. -/
private theorem packet_sum {p : ℕ} (hp : p.Prime) (hp3 : 2 < p)
    (hq : (p - 1 : ℕ) ≠ (0 : E))
    (Xs V W : E) (f : ℕ → E) :
    (∑ i ∈ Finset.Ico 1 p, (-1 : E) ^ i / (i : E) *
      (-(if i = p - 2 then (p - 1 : ℕ) * Xs else 0) +
        (if i = p - 1 then (p - 1 : ℕ) * V else 0) -
          (p - 1 : ℕ) * W * ((-1 : E) ^ i * f i))) =
    (p - 1 : ℕ) / (p - 2 : ℕ) * Xs + V - W * f (p - 1) -
      (p - 1 : ℕ) * W * (∑ i ∈ Finset.range (p - 2), f (i + 1) / (i + 1 : ℕ)) := by
  classical
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hsign₁ : (-1 : E) ^ (p - 1) = 1 :=
    (Nat.Odd.sub_odd hodd (show Odd (1 : ℕ) by decide)).neg_one_pow
  have hsign₂ : (-1 : E) ^ (p - 2) = -1 :=
    (Nat.Odd.sub_even (by omega) hodd (by decide)).neg_one_pow
  have hmul (i : ℕ) : (-1 : E) ^ i * (-1 : E) ^ i = 1 := by
    rw [← pow_two, ← pow_mul, mul_comm i 2, pow_mul]
    simp
  have hterm (i : ℕ) : (-1 : E) ^ i / (i : E) *
      (-(if i = p - 2 then (p - 1 : ℕ) * Xs else 0) +
        (if i = p - 1 then (p - 1 : ℕ) * V else 0) -
          (p - 1 : ℕ) * W * ((-1 : E) ^ i * f i)) =
      -(if i = p - 2 then (-1 : E) ^ i / (i : E) * ((p - 1 : ℕ) * Xs) else 0) +
        (if i = p - 1 then (-1 : E) ^ i / (i : E) * ((p - 1 : ℕ) * V) else 0) -
          (p - 1 : ℕ) * W * (f i / (i : E)) := by
    split_ifs <;> simp only [div_eq_mul_inv] <;> linear_combination
      -(p - 1 : ℕ) * W * f i * (i : E)⁻¹ * hmul i
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_Ico, show 1 ≤ p - 2 by omega, show p - 2 < p by omega,
    show 1 ≤ p - 1 by omega, show p - 1 < p by omega, and_self, if_true,
    hsign₁, hsign₂]
  rw [← Finset.mul_sum]
  have hsum : (∑ i ∈ Finset.Ico 1 p, f i / (i : E)) =
      (∑ i ∈ Finset.range (p - 2), f (i + 1) / (i + 1 : ℕ)) +
        f (p - 1) / (p - 1 : ℕ) := by
    calc
      _ = (∑ i ∈ Finset.Ico 1 (p - 1), f i / (i : E)) +
          f (p - 1) / (p - 1 : ℕ) := by
        simpa only [Nat.sub_add_cancel hp.one_le] using
          Finset.sum_Ico_succ_top (show 1 ≤ p - 1 by omega) (fun i => f i / (i : E))
      _ = _ := by
        congr 1
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [Nat.sub_sub, Nat.reduceAdd, Nat.add_comm]
  rw [hsum]
  field_simp
  ring

end Algebra

open private div_unit_mem sign_mul_mem from
  LanglandsSecondMainLemma.Odd.Q1.Logarithm
open private realization_tower_data from
  LanglandsSecondMainLemma.Odd.Models.Realization
open private exact_coordinate_orders_and_generation from
  LanglandsSecondMainLemma.Odd.Total.ASCoordinate
open private positive_log_split from LanglandsSecondMainLemma.Odd.Transition.Rational
open private additiveConductor_of_normCharacterChart from LanglandsSecondMainLemma.Odd.Models.Setup
open private trace_scalar from LanglandsSecondMainLemma.Odd.Q1.Logarithm

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

local instance : PrimeCyclicExtension F B₂ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₂
    (Basic.intermediateField_tower_compatible hp hG B₂ R.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.1

variable {Delta : K} {a : R.B₂} {w : R.B₂ˣ} {m : ℤ}
  (L : Linear.OddLinearData R Delta a w m)

include L

omit [Module.Free F K] in
/-- The residue prime itself lies in the common-field error ideal.
The statement also includes equal characteristic, where its order is infinite. -/
private theorem prime_mem : (p : K) ∈ lattice K (1 + (p : ℤ) * R.t₂) := by
  apply lattice_antitone K _ L.prime_order
  have hp3 : (3 : ℤ) ≤ p := by have := R.odd_prime; omega
  have ht : (1 : ℤ) ≤ R.t₂ := by have := R.t_pos.trans_le R.t_le_t₂; omega
  have h := mul_nonneg (by omega : (0 : ℤ) ≤ p - 2) (by omega : (0 : ℤ) ≤ R.t₂ - 1)
  have h' := mul_nonneg (by omega : (0 : ℤ) ≤ p - 3) (by omega : (0 : ℤ) ≤ R.t₂)
  nlinarith

omit [Module.Free F K] in
/-- The outer `W` is retained when bounding the shorter rational sum. -/
private theorem weighted_rational_integral (i : ℕ) (hi : i ≤ p - 2) :
    let W := algebraMap F K (Linear.transitionNorm R w)
    let A := algebraMap B₂ K a
    let v := algebraMap B₂ K (w : B₂)
    W * (W / (W ^ p - W + A ^ p) * ((W + A) / v) ^ i) ∈ lattice K 0 := by
  have hp3 : (3 : ℤ) ≤ p := by have := R.odd_prime; omega
  have hm : 0 ≤ m := by have := L.transition; nlinarith [Int.natCast_nonneg R.t]
  have hWA : ord K (algebraMap F K (Linear.transitionNorm R w) + algebraMap B₂ K a) =
      ((-((p : ℤ) ^ 2 * m) : ℤ) : WithTop ℤ) := by
    rw [(ord K).map_add_eq_of_lt_left, L.W_order_K]
    rw [L.W_order_K, L.a_order_K, WithTop.coe_lt_coe]
    have h := mul_pos (by omega : (0 : ℤ) < p)
      (by have := L.transition; omega : (0 : ℤ) < p * m - R.t)
    nlinarith
  have hden := L.D₀_order
  simp only [Linear.transitionD₀, map_add, map_sub, map_pow,
    ← IsScalarTower.algebraMap_apply F B₂ K] at hden
  dsimp only
  rw [mem_lattice, ord_mul, ord_mul, ord_div, ord_pow, ord_div, L.W_order_K,
    hden, hWA, L.w_order_K]
  simp only [← WithTop.coe_nsmul, ← WithTop.coe_add,
    ← WithTop.LinearOrderedAddCommGroup.coe_sub, WithTop.coe_le_coe, nsmul_eq_mul]
  have hiZ : (0 : ℤ) ≤ p - 2 - i := by omega
  have h := mul_nonneg (mul_nonneg (by omega : (0 : ℤ) ≤ p) hm)
    (add_nonneg (mul_nonneg (by omega : (0 : ℤ) ≤ p - 1) hiZ)
      (by omega : (0 : ℤ) ≤ p - 2))
  convert h using 1
  ring

/-- The actual first exponent in the common field. The two exceptional
coefficients have not yet been replaced by rational halves. -/
private theorem first_exponent_common
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p) :
    let W := algebraMap F K (Linear.transitionNorm R w)
    let A := algebraMap B₂ K a
    let v := algebraMap B₂ K (w : B₂)
    let C := algebraMap B₂ K (Linear.transitionC R a w)
    let Xs := algebraMap B₁ K (Linear.linearS R Delta) / (v ^ (p - 2) * C ^ 2)
    let XT := A * algebraMap B₁ K (Quadratic.quadraticInner R w Delta) /
      (v ^ (p - 1) * C ^ 2)
    let f := fun i : ℕ => W / (W ^ p - W + A ^ p) * ((W + A) / v) ^ i
    algebraMap B₂ K
      ((∑ i ∈ Finset.Ico 1 p, (-1 : B₂) ^ i / (i : B₂) * Linear.linearTrace R Delta w i) +
        Quadratic.quadraticTrace R Delta w / (2 * (p - 1 : ℕ) ^ 2)) -
      (-W * f (p - 1) + W * (∑ i ∈ Finset.range (p - 2), f (i + 1) / (i + 1 : ℕ)) +
        W / v ^ (p - 1) + (p - 1 : ℕ) / (p - 2 : ℕ) * Xs +
        XT / (2 * (p - 1 : ℕ))) ∈ lattice K (1 + (p : ℤ) * R.t₂) := by
  classical
  dsimp only
  let W := algebraMap F K (Linear.transitionNorm R w)
  let A := algebraMap B₂ K a
  let v := algebraMap B₂ K (w : B₂)
  let C := algebraMap B₂ K (Linear.transitionC R a w)
  let Xs := algebraMap B₁ K (Linear.linearS R Delta) / (v ^ (p - 2) * C ^ 2)
  let XT := A * algebraMap B₁ K (Quadratic.quadraticInner R w Delta) /
    (v ^ (p - 1) * C ^ 2)
  let f := fun i : ℕ => W / (W ^ p - W + A ^ p) * ((W + A) / v) ^ i
  let V := W / v ^ (p - 1)
  let short := ∑ i ∈ Finset.range (p - 2), f (i + 1) / (i + 1 : ℕ)
  let packet (i : ℕ) :=
    -(if i = p - 2 then (p - 1 : ℕ) * Xs else 0) +
      (if i = p - 1 then (p - 1 : ℕ) * V else 0) -
        (p - 1 : ℕ) * W * ((-1 : K) ^ i * f i)
  have hcharK : residueCharacteristic K = p := (residueCharacteristic_extension_eq F K).trans hchar
  have ho (i : ℕ) (hi : 1 ≤ i) (hip : i < p) : ord K (i : K) = 0 :=
    ord_natCast_eq_zero_of_lt_residueCharacteristic K hi (by rw [hcharK]; exact hip)
  have htwo : ord K (2 : K) = 0 := by simpa using ho 2 (by omega) R.odd_prime
  have hp3 := R.odd_prime
  have hq := ho (p - 1) (by omega) (by omega)
  have hqne : (p - 1 : ℕ) ≠ (0 : K) := by intro h; simp [h] at hq
  have hlinear (i : ℕ) (hi : i ∈ Finset.Ico 1 p) :
      algebraMap B₂ K (Linear.linearTrace R Delta w i) - packet i ∈
        lattice K (1 + (p : ℤ) * R.t₂) := by
    have h := Linear.final R L hres hchar i (Finset.mem_Ico.mp hi).1
      (by have := (Finset.mem_Ico.mp hi).2; omega)
    convert h using 1
    dsimp only [packet, Xs, V, f, W, A, v, C]
    congr 1
    simp only [div_pow]
    simp only [show -algebraMap B₂ K a - algebraMap F K (Linear.transitionNorm R w) =
      -(algebraMap F K (Linear.transitionNorm R w) + algebraMap B₂ K a) by ring,
      neg_pow (algebraMap F K (Linear.transitionNorm R w) + algebraMap B₂ K a) i,
      div_eq_mul_inv, mul_inv_rev]
    split_ifs <;> ring
  have hsum : (∑ i ∈ Finset.Ico 1 p, (-1 : K) ^ i / (i : K) *
      algebraMap B₂ K (Linear.linearTrace R Delta w i)) -
      ((p - 1 : ℕ) / (p - 2 : ℕ) * Xs + V - W * f (p - 1) -
        (p - 1 : ℕ) * W * short) ∈ lattice K (1 + (p : ℤ) * R.t₂) := by
    rw [← packet_sum hp R.odd_prime hqne Xs V W f]
    rw [← Finset.sum_sub_distrib]
    apply sum_mem_lattice K
    intro i hi
    convert sign_mul_mem K i (div_unit_mem K (hlinear i hi)
      (ho i (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2)) using 1
    ring
  have hshort : W * short ∈ lattice K 0 := by
    rw [Finset.mul_sum]
    apply sum_mem_lattice K
    intro i hi
    have hip : i + 1 ≤ p - 2 := by have := Finset.mem_range.mp hi; omega
    convert div_unit_mem K (weighted_rational_integral R L (i + 1) hip)
      (ho (i + 1) (by omega) (by omega)) using 1
    ring
  have hcorrection : (p : K) * (W * short) ∈ lattice K (1 + (p : ℤ) * R.t₂) := by
    simpa only [add_zero] using mul_mem_lattice K (prime_mem R L) hshort
  have hquadratic := div_unit_mem K (Quadratic.trace L hres hchar)
    (show ord K (2 * (p - 1 : ℕ) ^ 2) = 0 by
      simp only [ord_mul, ord_pow, htwo, hq, smul_zero, add_zero])
  have hquad : algebraMap B₂ K (Quadratic.quadraticTrace R Delta w) /
      (2 * (p - 1 : ℕ) ^ 2) - XT / (2 * (p - 1 : ℕ)) ∈
        lattice K (1 + (p : ℤ) * R.t₂) := by
    convert hquadratic using 1
    dsimp only [XT, A, v, C]
    field_simp
  have h := (lattice K _).add_mem ((lattice K _).sub_mem hsum hcorrection) hquad
  convert h using 1
  simp only [map_add, map_sum, map_mul, map_div₀, map_pow, map_neg, map_one,
    map_natCast, map_ofNat, Nat.cast_sub hp.one_le]
  dsimp only [W, A, v, C, Xs, XT, V, f, short]
  push_cast
  ring

omit L in
/-- Replace the common-field exceptional terms by the literal projections,
then replace their coefficients by `1/2` and `-1/2` in the whole lower ideal. -/
private theorem first_exponent_lower
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (pb : PowerBasis B₂ K) (a : B₂)
    (hroot : pb.gen ^ p - pb.gen = algebraMap B₂ K a)
    (hDelta : ord K pb.gen = ((-(R.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ R.t) (m : ℤ) (hmt : (R.t : ℤ) < (p : ℤ) * m)
    (u : Fˣ) (hu : ord F (u : F) = (m : WithTop ℤ))
    (w : B₂ˣ) (hw : normUnits F B₂ w = u⁻¹) :
    let W := (algebraMap F B₂ (u : F))⁻¹
    let C := 1 + algebraMap F B₂ (u : F) * a
    let s := -elementarySymmetric B₁ K (p - 1) pb.gen
    let T := trace B₁ K ((pb.gen / algebraMap B₂ K (w : B₂)) ^ (p - 1))
    let Xs := algebraMap B₁ K s /
      (algebraMap B₂ K (w : B₂) ^ (p - 2) * algebraMap B₂ K C ^ 2)
    let XT := algebraMap B₂ K a * algebraMap B₁ K T /
      (algebraMap B₂ K (w : B₂) ^ (p - 1) * algebraMap B₂ K C ^ 2)
    let ys := constantProjection pb Xs
    let yT := constantProjection pb XT
    let f := fun i : ℕ => W / (W ^ p - W + a ^ p) * ((W + a) / (w : B₂)) ^ i
    let E₁ := (∑ i ∈ Finset.Ico 1 p,
      (-1 : B₂) ^ i / (i : B₂) * Linear.linearTrace R pb.gen w i) +
        Quadratic.quadraticTrace R pb.gen w / (2 * (p - 1 : ℕ) ^ 2)
    E₁ - (-W * f (p - 1) +
      W * (∑ i ∈ Finset.range (p - 2), f (i + 1) / (i + 1 : ℕ)) +
        W / (w : B₂) ^ (p - 1) + (ys - yT) / 2) ∈ lattice B₂ (1 + (R.t₂ : ℤ)) := by
  classical
  dsimp only
  let W := (algebraMap F B₂ (u : F))⁻¹
  let C := 1 + algebraMap F B₂ (u : F) * a
  let s := -elementarySymmetric B₁ K (p - 1) pb.gen
  let T := trace B₁ K ((pb.gen / algebraMap B₂ K (w : B₂)) ^ (p - 1))
  let Xs := algebraMap B₁ K s /
    (algebraMap B₂ K (w : B₂) ^ (p - 2) * algebraMap B₂ K C ^ 2)
  let XT := algebraMap B₂ K a * algebraMap B₁ K T /
    (algebraMap B₂ K (w : B₂) ^ (p - 1) * algebraMap B₂ K C ^ 2)
  let ys := constantProjection pb Xs
  let yT := constantProjection pb XT
  let f := fun i : ℕ => W / (W ^ p - W + a ^ p) * ((W + a) / (w : B₂)) ^ i
  let rationalPart := -W * f (p - 1) +
    W * (∑ i ∈ Finset.range (p - 2), f (i + 1) / (i + 1 : ℕ)) + W / (w : B₂) ^ (p - 1)
  let E₁ := (∑ i ∈ Finset.Ico 1 p,
    (-1 : B₂) ^ i / (i : B₂) * Linear.linearTrace R pb.gen w i) +
      Quadratic.quadraticTrace R pb.gen w / (2 * (p - 1 : ℕ) ^ 2)
  change E₁ - (rationalPart + (ys - yT) / 2) ∈ lattice B₂ (1 + (R.t₂ : ℤ))
  have hW : Linear.transitionNorm R w = (u : F)⁻¹ := by
    simpa only [Linear.transitionNorm, coe_normUnits, Units.val_inv_eq_inv_val] using
      congrArg Units.val hw
  have L' := Linear.oddLinearData_construct R hres hchar pb.gen a w m
    hroot hDelta hprime pb.adjoin_gen_eq_top (by rw [hW, inv_inv]; exact hu) hmt
  have hC : Linear.transitionC R a w = C := by
    simp only [Linear.transitionC, hW, map_inv₀, div_inv_eq_mul, C, mul_comm]
  obtain ⟨hXs, hXT, _, _, hys, hyT⟩ :=
    representatives hp hG R hres hchar pb a hroot hDelta hprime m hmt u hu w hw
  change Xs - algebraMap B₂ K ys ∈ lattice K (1 + (p : ℤ) * R.t₂) at hXs
  change XT - algebraMap B₂ K yT ∈ lattice K (1 + (p : ℤ) * R.t₂) at hXT
  change ys ∈ lattice B₂ (((1 + R.t₂) ⌈/⌉ p : ℕ) : ℤ) at hys
  change yT ∈ lattice B₂ (((1 + R.t₂) ⌈/⌉ p : ℕ) : ℤ) at hyT
  have hcom : algebraMap B₂ K E₁ - (algebraMap B₂ K rationalPart +
      (p - 1 : ℕ) / (p - 2 : ℕ) * Xs + XT / (2 * (p - 1 : ℕ))) ∈
        lattice K (1 + (p : ℤ) * R.t₂) := by
    convert first_exponent_common R L' hres hchar using 1
    dsimp only [E₁, rationalPart, f, W, Xs, XT, s, T]
    simp only [hW, hC, Linear.linearS, Quadratic.quadraticInner, map_add, map_sub,
      map_mul, map_div₀, map_pow, map_inv₀, map_sum, map_neg, map_one, map_natCast,
      map_ofNat, ← IsScalarTower.algebraMap_apply F B₂ K]
  have hcharK : residueCharacteristic K = p := (residueCharacteristic_extension_eq F K).trans hchar
  have hchar₂ : residueCharacteristic B₂ = p := (residueCharacteristic_extension_eq F B₂).trans hchar
  have hp3 := R.odd_prime
  have hoK (i : ℕ) (hi : 1 ≤ i) (hip : i < p) : ord K (i : K) = 0 :=
    ord_natCast_eq_zero_of_lt_residueCharacteristic K hi (by rw [hcharK]; exact hip)
  have ho₂ (i : ℕ) (hi : 1 ≤ i) (hip : i < p) : ord B₂ (i : B₂) = 0 :=
    ord_natCast_eq_zero_of_lt_residueCharacteristic B₂ hi (by rw [hchar₂]; exact hip)
  have htwoK : ord K (2 : K) = 0 := by simpa using hoK 2 (by omega) hp3
  have htwo₂ : ord B₂ (2 : B₂) = 0 := by simpa using ho₂ 2 (by omega) hp3
  have hqK := hoK (p - 1) (by omega) (by omega)
  have hq₂ := ho₂ (p - 1) (by omega) (by omega)
  have hrK := hoK (p - 2) (by omega) (by omega)
  have hr₂ := ho₂ (p - 2) (by omega) (by omega)
  have hscaledS : (p - 1 : ℕ) / (p - 2 : ℕ) * (Xs - algebraMap B₂ K ys) ∈
      lattice K (1 + (p : ℤ) * R.t₂) := by
    simpa only [zero_add, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_mem_lattice K ((mem_lattice K).2 hqK.ge) (div_unit_mem K hXs hrK)
  have hscaledT := div_unit_mem K hXT (show ord K (2 * (p - 1 : ℕ)) = 0 by
    simp only [ord_mul, htwoK, hqK, add_zero])
  obtain ⟨_, _, _, _, he₂⟩ := realization_tower_data hp hG hres B₂ R.degree_B₂
  have hdesc : E₁ - (rationalPart + (p - 1 : ℕ) / (p - 2 : ℕ) * ys +
      yT / (2 * (p - 1 : ℕ))) ∈ lattice B₂ (1 + (R.t₂ : ℤ)) := by
    rw [add_comm 1 (R.t₂ : ℤ)]
    apply Models.monomialPhase_descend_lattice B₂ K hp.pos he₂
    convert (lattice K _).add_mem ((lattice K _).add_mem hcom hscaledS) hscaledT using 1
    simp only [map_sub, map_add, map_div₀, map_mul, map_natCast, map_ofNat]
    ring
  have hprime₂ : (p : B₂) ∈ lattice B₂ (1 + (R.t₂ : ℤ)) := by
    simpa only [add_comm] using Models.monomialPhase_descend_lattice B₂ K hp.pos he₂
      (by simpa only [map_natCast] using prime_mem R L')
  have herror (y : B₂) (hy : y ∈ lattice B₂ (((1 + R.t₂) ⌈/⌉ p : ℕ) : ℤ))
      (d : B₂) (hd : ord B₂ d = 0) : (p : B₂) * y / d ∈ lattice B₂ (1 + (R.t₂ : ℤ)) := by
    apply div_unit_mem B₂ _ hd
    simpa only [add_zero] using mul_mem_lattice B₂ hprime₂
      (lattice_antitone B₂ (Int.natCast_nonneg _) hy)
  have herrS := herror ys hys (2 * (p - 2 : ℕ)) (by simp only [ord_mul, htwo₂, hr₂, add_zero])
  have herrT := herror yT hyT (2 * (p - 1 : ℕ)) (by simp only [ord_mul, htwo₂, hq₂, add_zero])
  have htwoNe : (2 : B₂) ≠ 0 := by intro h; simp [h] at htwo₂
  have hqNe : (p - 1 : ℕ) ≠ (0 : B₂) := by intro h; simp [h] at hq₂
  have hrNe : (p - 2 : ℕ) ≠ (0 : B₂) := by intro h; simp [h] at hr₂
  convert (lattice B₂ _).add_mem ((lattice B₂ _).add_mem hdesc herrS) herrT using 1
  field_simp
  simp only [Nat.cast_sub hp.one_le, Nat.cast_sub (by omega : 2 ≤ p),
    Nat.cast_one, Nat.cast_ofNat]
  ring

omit L in
set_option maxHeartbeats 1200000 in
/-- **Paper Proposition 9.27 (`O:T:Q124`, `O:T:Q124phase`).**
The literal first, second, and fourth factors of the stationary comparison.
The primitive compatible quasi-characters retain their full logarithm chart;
the base quasi-character and the actual nontrivial norm character retain
their full charts as well. These are the character data constructed before
`fourFactors`. No phase equality or auxiliary stationary model is assumed.

All norms, traces, units, and character evaluations are in their named
fields. The prescribed coordinate constructs its power basis; its literal
constant projections are used internally. Every odd prime, both field
characteristics, and nonunitary quasi-characters are included. -/
theorem q124
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (Delta : K) (hDelta : ord K Delta = ((-(R.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ R.t)
    (hroot : Delta ^ p - Delta = algebraMap B₂ K (norm B₂ K Delta))
    (e : LocalAddCharData F) (alpha gamma : Fˣ)
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
    (m : ℤ) (hu : ord F ((alpha / gamma : Fˣ) : F) = (m : WithTop ℤ))
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
    (w : B₂ˣ) (hw : normUnits F B₂ w = gamma / alpha)
    (A₁ : B₁ˣ) (C₂ : B₂ˣ)
    (hA₁ : (A₁ : B₁) = algebraMap F B₁ (gamma : F) +
      algebraMap F B₁ (alpha : F) * norm B₁ K Delta)
    (hC₂ : (C₂ : B₂) = algebraMap F B₂ (gamma : F) -
      algebraMap F B₂ (alpha : F) * (w : B₂) +
      algebraMap F B₂ (alpha : F) * norm B₂ K Delta) :
    let u : F := ((alpha / gamma : Fˣ) : F)
    let W := u⁻¹
    let A₀ := norm F B₂ (norm B₂ K Delta)
    let D := 1 + u ^ p * A₀
    let H := norm F B₁ (-elementarySymmetric B₁ K (p - 1) Delta)
    let J := norm F B₁ (trace B₁ K ((Delta / algebraMap B₂ K (w : B₂)) ^ (p - 1)))
    let Psi := (scaleAddCharData F e alpha).character
    ((chi A₁ / phi C₂) * lambda.character (normUnits F B₁ A₁ / normUnits F B₂ C₂) *
      tracePullbackAddChar F B₂ Psi (w : B₂))⁻¹ =
        Psi (W * u ^ (p - 1) * H / D - u ^ (p - 2) * H / (2 * D ^ 2) +
          u ^ (p - 1) * A₀ * J / (2 * D ^ 2)) := by
  classical
  let u : Fˣ := alpha / gamma
  let a := norm B₂ K Delta
  let U := algebraMap F B₂ (u : F)
  let W := U⁻¹
  let C := 1 + U * a
  let A₀ := norm F B₂ a
  let D := 1 + (u : F) ^ p * A₀
  let s := -elementarySymmetric B₁ K (p - 1) Delta
  let H := norm F B₁ s
  let T := trace B₁ K ((Delta / algebraMap B₂ K (w : B₂)) ^ (p - 1))
  let J := norm F B₁ T
  let Pstar := norm F B₂ C
  let Fstar := algebraMap F B₂ Pstar /
    (algebraMap F B₂ Pstar - U ^ (p - 1))
  let k := U * (w : B₂) / C
  let eta := W / (w : B₂) ^ p
  let f := fun i : ℕ => W / (W ^ p - W + a ^ p) * ((W + a) / (w : B₂)) ^ i
  let E₁ := (∑ i ∈ Finset.Ico 1 p,
    (-1 : B₂) ^ i / (i : B₂) * Linear.linearTrace R Delta w i) +
      Quadratic.quadraticTrace R Delta w / (2 * (p - 1 : ℕ) ^ 2)
  let E₂ := W * Fstar * truncatedLog p k
  let lead := (u : F)⁻¹ * (u : F) ^ (p - 1) * H / D
  let Psi := (scaleAddCharData F e alpha).character
  let Psi₂ := tracePullbackAddChar F B₂ Psi
  change ord F (u : F) = (m : WithTop ℤ) at hu
  have hwu : normUnits F B₂ w = u⁻¹ := by simpa only [u, inv_div] using hw
  have hmpos : 0 < m := by
    have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
    nlinarith [Int.natCast_nonneg R.t]
  have hmNat : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hmpos.le
  have hmtNat : R.t < p * m.toNat := by
    exact_mod_cast (show (R.t : ℤ) < (p : ℤ) * (m.toNat : ℤ) by rw [hmNat]; exact hmt)
  obtain ⟨hd₂, hrF₂, _, heF₂, he₂⟩ := realization_tower_data hp hG hres B₂ R.degree_B₂
  obtain ⟨_, hgen⟩ := exact_coordinate_orders_and_generation B₂ K hp R.t_pos
    hd₂ he₂ Delta a hDelta hprime hroot
  let pb := PowerBasis.ofAdjoinEqTop (IsAlgebraic.of_finite B₂ Delta).isIntegral hgen
  have hpb : pb.gen = Delta := PowerBasis.ofAdjoinEqTop_gen _ _
  let Xs := algebraMap B₁ K s /
    (algebraMap B₂ K (w : B₂) ^ (p - 2) * algebraMap B₂ K C ^ 2)
  let XT := algebraMap B₂ K a * algebraMap B₁ K T /
    (algebraMap B₂ K (w : B₂) ^ (p - 1) * algebraMap B₂ K C ^ 2)
  let ys := constantProjection pb Xs
  let yT := constantProjection pb XT
  have hlower := first_exponent_lower R hres hchar pb a
    (by rw [hpb]; exact hroot) (by rw [hpb]; exact hDelta) hprime m hmt u hu w hwu
  simp only [hpb] at hlower
  change E₁ - (-W * f (p - 1) +
    W * (∑ i ∈ Finset.range (p - 2), f (i + 1) / (i + 1 : ℕ)) +
      W / (w : B₂) ^ (p - 1) + (ys - yT) / 2) ∈ lattice B₂ (1 + (R.t₂ : ℤ)) at hlower
  have hlog : (∑ j ∈ Finset.range (p - 1), k ^ (j + 1) / (j + 1 : ℕ)) = truncatedLog p k := by
    rw [positive_log_split R.odd_prime, truncatedLog_apply, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_comm]
  have hrat := rational hp hG R hres hmtNat Delta hDelta u
    (by simpa only [hmNat] using hu) w hwu
  change -f (p - 1) + (∑ i ∈ Finset.range (p - 2), f (i + 1) / (i + 1 : ℕ)) +
    Fstar * (∑ j ∈ Finset.range (p - 1), k ^ (j + 1) / (j + 1 : ℕ)) - k * (1 - eta) ∈
      lattice B₂ (1 + (R.t₂ : ℤ) + (p : ℤ) * m.toNat) at hrat
  rw [hlog, hmNat] at hrat
  have hWo : ord B₂ W = ((-((p : ℤ) * m) : ℤ) : WithTop ℤ) := by
    simp only [W, U, ord_inv, ord_algebraMap, heF₂, hu, ← WithTop.coe_nsmul,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg, nsmul_eq_mul]
  have hratW : W * (-f (p - 1) +
      (∑ i ∈ Finset.range (p - 2), f (i + 1) / (i + 1 : ℕ)) +
        Fstar * truncatedLog p k - k * (1 - eta)) ∈ lattice B₂ (1 + (R.t₂ : ℤ)) := by
    have hWmem : W ∈ lattice B₂ (-((p : ℤ) * m)) := hWo.ge
    have hcancel : -((p : ℤ) * m) + (1 + (R.t₂ : ℤ) + (p : ℤ) * m) =
        1 + (R.t₂ : ℤ) := by ring
    simpa only [hcancel] using mul_mem_lattice B₂ hWmem hrat
  obtain ⟨helemEq, helemMem⟩ := elementaryPhase hp hG R hres hmtNat Delta hDelta u
    (by simpa only [hmNat] using hu) w hwu
  have hexp : -((p : ℤ) - 1) = -((p - 1 : ℕ) : ℤ) := by rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  have helem : W * (k * (1 - eta) + ((w : B₂) ^ (p - 1))⁻¹) - (w : B₂) ∈
      lattice B₂ (1 + (R.t₂ : ℤ)) := by
    rw [← helemEq] at helemMem
    simpa only [hexp, zpow_neg, zpow_natCast] using helemMem
  have hcombined : E₁ + E₂ - (w : B₂) - (ys - yT) / 2 ∈ lattice B₂ (1 + (R.t₂ : ℤ)) := by
    convert (lattice B₂ _).add_mem ((lattice B₂ _).add_mem hlower hratW) helem using 1
    dsimp only [E₂]
    ring
  let c := (R.t₂ + 1) ⌈/⌉ p
  have hcpos : 0 < c := by
    have h := le_smul_ceilDiv (b := R.t₂ + 1) hp.pos
    change R.t₂ + 1 ≤ p * c at h
    by_contra hc
    have : c = 0 := by omega
    rw [this, mul_zero] at h
    omega
  have hchart (x : lattice F (c : ℤ)) :
      tau.1 (positiveUnitOfLattice F hcpos (-x)) = Psi (truncatedLog p (x : F)) := by
    have h := htauFormula (positiveUnitOfLattice F hcpos (-x))
    simpa only [coe_positiveUnitOfLattice, Submodule.coe_neg, add_neg_cancel_left,
      show ∀ x : F, 1 - (1 + -x) = x by intro x; ring,
      Psi, scaleAddCharData_character_apply] using h
  have hPsi := additiveConductor_of_normCharacterChart F B₂ hp R.odd_prime hchar
    R.degree_B₂ R.B₂_breaks.1 (R.t_pos.trans_le R.t_le_t₂) hrF₂ rfl hcpos tau htau Psi hchart
  obtain ⟨pi, hpi, hpiGen⟩ := monogenicUniformizer F B₂ hrF₂
  have hPsi₂ := additiveConductor_compTrace_cyclicPrime F B₂ R.B₂_breaks.1 hrF₂ pi hpi hpiGen hPsi
  have hcond : (p : ℤ) * (-((R.t₂ + 1 : ℕ) : ℤ)) +
      (((p - 1) * (R.t₂ + 1) : ℕ) : ℤ) = -((R.t₂ + 1 : ℕ) : ℤ) := by
    simp only [Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one]
    ring
  have hdegree₂ : Module.finrank F B₂ = p := R.degree_B₂
  rw [hdegree₂, hcond] at hPsi₂
  have htriv : AddCharTrivialOnLattice B₂ Psi₂ (1 + (R.t₂ : ℤ)) := by
    intro x hx
    have h := hPsi₂.trivial x (by
      simpa only [neg_neg, Nat.cast_add, Nat.cast_one, add_comm] using hx)
    change Psi (trace F B₂ x) = 1
    simpa only [ContinuousAddChar.compTrace_apply] using h
  have hphase : Psi₂ E₁ * Psi₂ E₂ * (Psi₂ (w : B₂))⁻¹ = Psi₂ ((ys - yT) / 2) := by
    calc
      _ = Psi₂ (E₁ + E₂ - (w : B₂)) := by
        rw [← Psi₂.map_add_eq_mul E₁ E₂, ← div_eq_mul_inv]
        exact (Psi₂.toAddChar.map_sub_eq_div (E₁ + E₂) (w : B₂)).symm
      _ = _ := by
        apply div_eq_one.mp
        change Psi₂.toAddChar _ / Psi₂.toAddChar _ = 1
        rw [← AddChar.map_sub_eq_div]
        exact htriv _ hcombined
  have hhalves := normHalf hp hG R hres hchar pb a
    (by rw [hpb]; exact hroot) (by rw [hpb]; exact hDelta) hprime m hmt u hu w hwu
    c rfl hcpos tau htau Psi hchart
  simp only [hpb] at hhalves
  change Psi₂ (ys / 2) = Psi (-(u : F) ^ (p - 2) * H / (2 * D ^ 2)) ∧
    Psi₂ (-yT / 2) = Psi ((u : F) ^ (p - 1) * A₀ * J / (2 * D ^ 2)) at hhalves
  have hfirst := Q1.logarithm hp hG hres hchar R hprime Delta a hDelta hroot
    e alpha gamma halpha chi phi hphi hcompat hprimitive hchiFormula hu hmt w hw A₁ C₂ hA₁ hC₂
  change (chi A₁ / phi C₂)⁻¹ = Psi₂ E₁ at hfirst
  have hsecondRaw := Q2.phase hp hG hres hchar R Delta hDelta hprime hroot
    lambda e alpha gamma m hu hmt hn hgamma hlambdaFormula w hw A₁ C₂ hA₁ hC₂
  have hsecond : (lambda.character (normUnits F B₁ A₁ / normUnits F B₂ C₂))⁻¹ =
      Psi lead * Psi₂ E₂ := by
    rw [hsecondRaw]
    congr 1
    · dsimp only [Psi, lead, H, s, D, A₀, a, u]
      simp only [scaleAddCharData_character_apply, Units.val_div_eq_div_val, inv_div]
    · simp only [Psi₂, Psi, tracePullbackAddChar_apply, scaleAddCharData_character_apply,
        trace_scalar, map_mul]
      congr 2
      dsimp only [E₂, Fstar, Pstar, C, W, U, k, a, u]
      simp only [map_div₀, map_sub, map_pow, Units.val_div_eq_div_val, inv_div]
  change ((chi A₁ / phi C₂) * lambda.character (normUnits F B₁ A₁ / normUnits F B₂ C₂) *
      Psi₂ (w : B₂))⁻¹ = Psi (lead - (u : F) ^ (p - 2) * H / (2 * D ^ 2) +
        (u : F) ^ (p - 1) * A₀ * J / (2 * D ^ 2))
  calc
    _ = Psi lead * (Psi₂ E₁ * Psi₂ E₂ * (Psi₂ (w : B₂))⁻¹) := by
      rw [mul_inv_rev, mul_inv_rev, hfirst, hsecond]
      ac_rfl
    _ = Psi lead * (Psi₂ (ys / 2) * Psi₂ (-yT / 2)) := by
      rw [hphase, show (ys - yT) / 2 = ys / 2 + -yT / 2 by ring]
      rw [Psi₂.map_add_eq_mul]
    _ = _ := by
      rw [hhalves.1, hhalves.2]
      rw [← Psi.map_add_eq_mul, ← Psi.map_add_eq_mul]
      congr 1
      ring

end Diamond

end

end LanglandsSecondMainLemma.Odd.Transition
