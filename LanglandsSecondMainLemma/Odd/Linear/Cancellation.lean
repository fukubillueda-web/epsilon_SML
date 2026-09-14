import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Linear.Denominator
import LanglandsSecondMainLemma.Odd.Linear.Numerator

/-!
# Odd / Linear / Cancellation

Paper Lemma 9.6 (`O:W:cancel`). The inverse-square replacement retains
`w^(p-2)` and its multiple `Delta/w`. The last numerator correction then
cancels the last exceptional term modulo the full lattice `1+p*t₂`.
The unnormalized binomial remainder avoids division by the residue prime,
so the argument applies in both field characteristics.
-/

namespace LanglandsSecondMainLemma.Odd.Linear

noncomputable section
open LanglandsFirstMainLemma

open private pow_mem_int_lattice natCast_mem_int_lattice_zero from
  LanglandsSecondMainLemma.Odd.Total.TranslatedNorm
open private ne_zero_of_order from LanglandsSecondMainLemma.Odd.Linear.Setup
open private split_div_mem from LanglandsSecondMainLemma.Odd.Linear.Split
open private denominator_binomial denominator_norm_remainder from
  LanglandsSecondMainLemma.Odd.Linear.Denominator

section Estimates

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- The three weighted depths used in `O:W:cancel`, with `u=t+delta`. -/
private theorem cancellation_depths (p t delta M : ℤ)
    (hp : 3 ≤ p) (ht : 1 ≤ t) (hd : 0 ≤ delta) (hM : t + 1 ≤ M) :
    let S := p * (p - 1) * delta
    let K := 1 + p * (t + delta)
    K ≤ S + 2 * (p - 1) * M - t ∧
      K ≤ S - t + (p ^ 2 - 1) * M ∧
      K ≤ S - t + (p - 1) * M + p * (p - 1) * (t + delta) + p * (M - t) := by
  dsimp only
  have ht₁ := mul_nonneg (by omega : 0 ≤ p - 3) (by omega : 0 ≤ t)
  have hd₁ := mul_nonneg (mul_nonneg (by omega : 0 ≤ p)
    (by omega : 0 ≤ p - 2)) hd
  have hM₁ := mul_nonneg (by omega : 0 ≤ p - 1) (sub_nonneg.mpr hM)
  have hM₂ := mul_nonneg (by nlinarith : 0 ≤ p ^ 2 - 1) (sub_nonneg.mpr hM)
  have hM₃ := mul_nonneg (by omega : 0 ≤ 2 * p - 1) (sub_nonneg.mpr hM)
  have ht₂ := mul_nonneg (by nlinarith : 0 ≤ p ^ 2 - p - 2) (by omega : 0 ≤ t)
  have hd₂ := mul_nonneg (mul_nonneg (by omega : 0 ≤ p)
    (by omega : 0 ≤ 2 * p - 3)) hd
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Inverse squares of units differ by the original difference times
an integral factor. The power of `w` is left explicit. -/
private theorem cancellation_inverse_square {p : ℕ} (hp : 2 ≤ p)
    (s w Q C : E) (S M q : ℤ)
    (hs : s ∈ lattice E S) (hw : ord E w = ((-M : ℤ) : WithTop ℤ))
    (hQ : ord E Q = 0) (hC : ord E C = 0)
    (hCQ : C - Q ∈ lattice E q) :
    s / (w ^ (p - 2) * Q ^ 2) - s / (w ^ (p - 2) * C ^ 2) ∈
      lattice E (S + q + ((p : ℤ) - 2) * M) := by
  have hsum : C + Q ∈ lattice E 0 :=
    (lattice E 0).add_mem ((mem_lattice E).2 hC.ge) ((mem_lattice E).2 hQ.ge)
  have hden : ord E (w ^ (p - 2) * Q ^ 2 * C ^ 2) =
      ((-((p : ℤ) - 2) * M : ℤ) : WithTop ℤ) := by
    simp only [ord_mul, ord_pow, hw, hQ, hC, nsmul_zero, add_zero,
      ← WithTop.coe_nsmul, nsmul_eq_mul, Nat.cast_sub hp, Nat.cast_ofNat]
    congr 1
    ring
  have h := split_div_mem E (mul_mem_lattice E (mul_mem_lattice E hs hCQ) hsum) hden
  have hw0 := ne_zero_of_order E hw
  have hQ0 := ne_zero_of_order E (n := 0) hQ
  have hC0 := ne_zero_of_order E (n := 0) hC
  have heq : s / (w ^ (p - 2) * Q ^ 2) - s / (w ^ (p - 2) * C ^ 2) =
      s * (C - Q) * (C + Q) / (w ^ (p - 2) * Q ^ 2 * C ^ 2) := by
    field_simp
    ring
  rw [heq]
  convert h using 1
  ring

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
/-- Exact common-denominator identity for the two linear corrections.
The odd power supplies the sign; no scalar factor is discarded. -/
private theorem cancellation_identity {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p)
    (W a : E) (hW : W ≠ 0) (hD : W ^ p - W + a ^ p ≠ 0)
    (hC : 1 + a / W ≠ 0) :
    -(W ^ 2 * (-a - W) ^ (p - 2) / (W ^ p - W + a ^ p)) -
        1 / (1 + a / W) ^ 2 =
      ((W + a) ^ p - W ^ p - a ^ p + W) /
        ((W ^ p - W + a ^ p) * (1 + a / W) ^ 2) := by
  have hodd : Odd (p - 2) := by
    obtain ⟨k, hk⟩ := hp
    exact ⟨k - 1, by omega⟩
  have hpow : (-a - W) ^ (p - 2) = -(W + a) ^ (p - 2) := by
    rw [show -a - W = -(W + a) by ring, hodd.neg_pow]
  have hprod : (W + a) ^ (p - 2) * (W + a) ^ 2 = (W + a) ^ p := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ p)]
  have hWC : W ^ 2 * (1 + a / W) ^ 2 = (W + a) ^ 2 := by
    field_simp
  rw [hpow, ← neg_div, div_sub_div _ _ hD (pow_ne_zero 2 hC)]
  congr 1
  calc
    -(W ^ 2 * -(W + a) ^ (p - 2)) * (1 + a / W) ^ 2 -
        (W ^ p - W + a ^ p) * 1 =
      (W + a) ^ (p - 2) * (W ^ 2 * (1 + a / W) ^ 2) -
        (W ^ p - W + a ^ p) := by ring
    _ = _ := by rw [hWC, hprod]; ring

end Estimates

section Diamond

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]
  {p : ℕ} {hp : p.Prime}
  {hG : Nonempty
    (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))}
  (D : Total.OddTotalBreakData (F := F) (K := K) hp hG)

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

local notation "B₁" => D.B₁
local notation "B₂" => D.B₂

variable {Delta : K} {a : D.B₂} {w : D.B₂ˣ} {m : ℤ}
  (L : OddLinearData D Delta a w m)

include L

omit [Module.Free F K] in
/-- The inverse-square replacement in `O:W:cancel`, and its multiple
`Delta/w`. In particular the exceptional power is exactly `w^(p-2)`.
Multiplication by the integral signed coefficients preserves both errors. -/
theorem inverseSquare_replacement :
    let wK := algebraMap B₂ K (w : B₂)
    let W := algebraMap F K (transitionNorm D w)
    let b := algebraMap B₁ K (norm B₁ K Delta)
    let s := algebraMap B₁ K (linearS D Delta)
    let C := algebraMap B₂ K (transitionC D a w)
    let e := s / (wK ^ (p - 2) * (1 + b / W) ^ 2) -
      s / (wK ^ (p - 2) * C ^ 2)
    e ∈ lattice K (1 + (p : ℤ) * D.t₂) ∧
      Delta / wK * e ∈ lattice K (1 + (p : ℤ) * D.t₂) := by
  let M : ℤ := (p : ℤ) * m
  let W := algebraMap F K (transitionNorm D w)
  let b := algebraMap B₁ K (norm B₁ K Delta)
  let A := algebraMap B₂ K a
  let s := algebraMap B₁ K (linearS D Delta)
  let wK := algebraMap B₂ K (w : B₂)
  let Q := 1 + b / W
  let C := 1 + A / W
  have hpz : (3 : ℤ) ≤ p := by exact_mod_cast D.odd_prime
  have ht : (1 : ℤ) ≤ D.t := by exact_mod_cast D.t_pos
  have hu : (D.t : ℤ) ≤ D.t₂ := by exact_mod_cast D.t_le_t₂
  have hM : (D.t : ℤ) + 1 ≤ M := L.transition
  have hW : ord K W = ((-(p : ℤ) * M : ℤ) : WithTop ℤ) := by
    convert L.W_order_K using 1; dsimp only [M]; congr 1; ring
  have hQ : ord K Q = 0 := L.denominator_order _ L.b_order_K
  have hC : ord K C = 0 := L.denominator_order _ L.a_order_K
  have hab : A - b ∈ lattice K (-(D.t : ℤ)) := by
    have hr := lattice_antitone K (by nlinarith :
      -(D.t : ℤ) ≤ (p : ℤ) * D.t₂ - (p + 1) * D.t)
      (denominator_norm_remainder D L)
    convert (lattice K _).neg_mem
      ((lattice K _).add_mem hr ((mem_lattice K).2 L.Delta_order.ge)) using 1
    dsimp only [A, b]
    ring
  have hCQ : C - Q ∈ lattice K ((p : ℤ) * M - D.t) := by
    have h := split_div_mem K hab hW
    rw [show C - Q = (A - b) / W by dsimp only [C, Q]; ring]
    convert h using 1
    ring
  have h := cancellation_inverse_square K (p := p) (by have := D.odd_prime; omega)
    s wK Q C ((p : ℤ) * (p - 1) * D.delta) M ((p : ℤ) * M - D.t)
    ((mem_lattice K).2 L.s_order) L.w_order_K hQ hC hCQ
  have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
  have hdepth := (cancellation_depths (p : ℤ) D.t D.delta M hpz ht
    (Int.natCast_nonneg _) hM).1
  rw [← ht₂] at hdepth
  have hfirst : s / (wK ^ (p - 2) * Q ^ 2) - s / (wK ^ (p - 2) * C ^ 2) ∈
      lattice K (1 + (p : ℤ) * D.t₂) := by
    apply lattice_antitone K _ h
    nlinarith only [hdepth]
  have hDelta : Delta / wK ∈ lattice K 0 := by
    apply lattice_antitone K (by omega : (0 : ℤ) ≤ -(D.t : ℤ) - -M)
    exact split_div_mem K ((mem_lattice K).2 L.Delta_order.ge) L.w_order_K
  have hsecond := mul_mem_lattice K hDelta hfirst
  simpa only [transitionC, map_add, map_one, map_div₀,
    ← IsScalarTower.algebraMap_apply F B₂ K, zero_add, W, b, s, wK, Q, C, A] using
    And.intro hfirst hsecond

omit [Module.Free F K] in
/-- The weighted bracket from the proof of `O:W:cancel`. Its two
numerator pieces have exactly the depths displayed in the paper. -/
private theorem cancellation_linear :
    let wK := algebraMap B₂ K (w : B₂)
    let W := algebraMap F K (transitionNorm D w)
    let A := algebraMap B₂ K a
    let s := algebraMap B₁ K (linearS D Delta)
    let d₀ := algebraMap B₂ K (transitionD₀ D a w)
    let C := algebraMap B₂ K (transitionC D a w)
    Delta * s / wK ^ (p - 1) *
      (-(W ^ 2 * (-A - W) ^ (p - 2) / d₀) - 1 / C ^ 2) ∈
      lattice K (1 + (p : ℤ) * D.t₂) := by
  let M : ℤ := (p : ℤ) * m
  let W := algebraMap F K (transitionNorm D w)
  let A := algebraMap B₂ K a
  let s := algebraMap B₁ K (linearS D Delta)
  let wK := algebraMap B₂ K (w : B₂)
  let d₀ := W ^ p - W + A ^ p
  let C := 1 + A / W
  let S : ℤ := (p : ℤ) * (p - 1) * D.delta
  have hp3 := D.odd_prime
  have hpz : (3 : ℤ) ≤ p := by exact_mod_cast hp3
  have ht : (1 : ℤ) ≤ D.t := by exact_mod_cast D.t_pos
  have hM : (D.t : ℤ) + 1 ≤ M := L.transition
  have hW : ord K W = ((-(p : ℤ) * M : ℤ) : WithTop ℤ) := by
    convert L.W_order_K using 1; dsimp only [M]; congr 1; ring
  have hd₀ : ord K d₀ = ((-(p : ℤ) ^ 2 * M : ℤ) : WithTop ℤ) := by
    have h := L.D₀_order
    simp only [transitionD₀, map_add, map_sub, map_pow,
      ← IsScalarTower.algebraMap_apply F B₂ K] at h
    convert h using 1; dsimp only [M]; congr 1; ring
  have hC : ord K C = 0 := L.denominator_order _ L.a_order_K
  have hw : ord K wK = ((-M : ℤ) : WithTop ℤ) := L.w_order_K
  have hden : ord K (wK ^ (p - 1) * d₀ * C ^ 2) =
      ((-((p : ℤ) - 1) * M - (p : ℤ) ^ 2 * M : ℤ) : WithTop ℤ) := by
    simp only [ord_mul, ord_pow, hw, hd₀, hC, nsmul_zero, add_zero,
      ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul,
      Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    congr 1
    dsimp only [M]
    ring
  have hDs : Delta * s ∈ lattice K (S - D.t) := by
    convert mul_mem_lattice K ((mem_lattice K).2 L.Delta_order.ge)
      ((mem_lattice K).2 L.s_order) using 1
    dsimp only [S]
    ring
  have hmix := denominator_binomial K hp
    (by nlinarith : -(p : ℤ) * M ≤ -(p : ℤ) * D.t)
    ((mem_lattice K).2 hW.ge)
    (by simpa only [neg_mul] using (mem_lattice K).2 L.a_order_K.ge)
    ((mem_lattice K).2 L.prime_order)
  have h₁ := split_div_mem K (mul_mem_lattice K hDs ((mem_lattice K).2 hW.ge)) hden
  have h₂ := split_div_mem K (mul_mem_lattice K hDs hmix) hden
  have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
  obtain ⟨_, hdepth₁, hdepth₂⟩ := cancellation_depths (p : ℤ) D.t D.delta M hpz ht
    (Int.natCast_nonneg _) hM
  rw [← ht₂] at hdepth₁ hdepth₂
  have hfirst : Delta * s * W / (wK ^ (p - 1) * d₀ * C ^ 2) ∈
      lattice K (1 + (p : ℤ) * D.t₂) := by
    apply lattice_antitone K _ h₁
    dsimp only [S]
    nlinarith only [hdepth₁]
  have hsecond : Delta * s * ((W + A) ^ p - W ^ p - A ^ p) /
      (wK ^ (p - 1) * d₀ * C ^ 2) ∈ lattice K (1 + (p : ℤ) * D.t₂) := by
    apply lattice_antitone K _ h₂
    dsimp only [S]
    nlinarith only [hdepth₂]
  have hid := cancellation_identity K (hp.odd_of_ne_two (by omega)) hp3 W A
    (ne_zero_of_order K hW) (ne_zero_of_order K hd₀) (ne_zero_of_order K (n := 0) hC)
  simp only [transitionD₀, transitionC, map_add, map_sub, map_pow, map_one, map_div₀,
    ← IsScalarTower.algebraMap_apply F B₂ K]
  change Delta * s / wK ^ (p - 1) *
    (-(W ^ 2 * (-A - W) ^ (p - 2) / d₀) - 1 / C ^ 2) ∈ _
  rw [hid]
  convert (lattice K _).add_mem hsecond hfirst using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

omit [Module.Free F K] in
/-- Paper `O:W:cancel`, applied to the denominator and numerator
replacements. This is the part of `O:W:Wpre` changed by the four
replacements: the unchanged `p`-term and `W/w^(p-1)` term can be added
back by the consumer. The linear `Delta*s` term disappears at `i=p-1`,
whereas the signed `w^(p-2)` term remains at `i=p-2`.

All scalars are the actual norms and coordinate from `OddLinearData`,
whose constructor is `oddLinearData_construct`. No characteristic is
excluded and no phase cancellation is assumed. -/
theorem cancellation (i : ℕ) (hi : 1 ≤ i) (hip : i ≤ p - 1) :
    let wK := algebraMap B₂ K (w : B₂)
    let W := algebraMap F K (transitionNorm D w)
    let Y := algebraMap B₁ K (transitionY D Delta w)
    let b := algebraMap B₁ K (norm B₁ K Delta)
    let s := algebraMap B₁ K (linearS D Delta)
    let d := algebraMap B₁ K (transitionD D Delta w)
    let d₀ := algebraMap B₂ K (transitionD₀ D a w)
    let A₀ := -algebraMap B₂ K a - W
    let C := algebraMap B₂ K (transitionC D a w)
    let c := ((p - 1 : ℕ) : K)
    (-c * (W ^ 2 * (Delta - Y) ^ i / (wK ^ i * d)) -
        (if i = p - 2 then c * s / (wK ^ (p - 2) * (1 + b / W) ^ 2) else 0) -
        (if i = p - 1 then c * (i : K) * Delta * s /
          (wK ^ (p - 1) * (1 + b / W) ^ 2) else 0)) -
      (-c * (W ^ 2 * A₀ ^ i / (wK ^ i * d₀)) -
        (if i = p - 2 then c * s / (wK ^ (p - 2) * C ^ 2) else 0)) ∈
      lattice K (1 + (p : ℤ) * D.t₂) := by
  let wK := algebraMap B₂ K (w : B₂)
  let W := algebraMap F K (transitionNorm D w)
  let Y := algebraMap B₁ K (transitionY D Delta w)
  let b := algebraMap B₁ K (norm B₁ K Delta)
  let s := algebraMap B₁ K (linearS D Delta)
  let d := algebraMap B₁ K (transitionD D Delta w)
  let d₀ := algebraMap B₂ K (transitionD₀ D a w)
  let A₀ := -algebraMap B₂ K a - W
  let C := algebraMap B₂ K (transitionC D a w)
  let Q := 1 + b / W
  let c := ((p - 1 : ℕ) : K)
  let k : ℤ := 1 + (p : ℤ) * D.t₂
  have hc : c ∈ lattice K 0 := natCast_mem_int_lattice_zero K (p - 1)
  have hcsq : c ^ 2 ∈ lattice K 0 := by
    simpa only [Nat.cast_ofNat, mul_zero] using pow_mem_int_lattice K hc 2
  have hreplace : W ^ 2 * (Delta - Y) ^ i / (wK ^ i * d) -
      W ^ 2 / (wK ^ i * d₀) *
        (if i ≤ p - 2 then A₀ ^ i else
          A₀ ^ (p - 1) + c * A₀ ^ (p - 2) * Delta * s) ∈ lattice K k := by
    convert (lattice K k).add_mem (denominator D L i (by omega))
      (numerator D L i hi hip) using 1
    ring
  have hweighted : -c * (W ^ 2 * (Delta - Y) ^ i / (wK ^ i * d) -
      W ^ 2 / (wK ^ i * d₀) *
        (if i ≤ p - 2 then A₀ ^ i else
          A₀ ^ (p - 1) + c * A₀ ^ (p - 2) * Delta * s)) ∈ lattice K k := by
    simpa only [zero_add] using mul_mem_lattice K ((lattice K 0).neg_mem hc) hreplace
  obtain ⟨hinv, hinvDelta⟩ := inverseSquare_replacement D L
  change s / (wK ^ (p - 2) * Q ^ 2) - s / (wK ^ (p - 2) * C ^ 2) ∈
    lattice K k at hinv
  change Delta / wK *
    (s / (wK ^ (p - 2) * Q ^ 2) - s / (wK ^ (p - 2) * C ^ 2)) ∈
    lattice K k at hinvDelta
  change (-c * (W ^ 2 * (Delta - Y) ^ i / (wK ^ i * d)) -
        (if i = p - 2 then c * s / (wK ^ (p - 2) * Q ^ 2) else 0) -
        (if i = p - 1 then c * (i : K) * Delta * s /
          (wK ^ (p - 1) * Q ^ 2) else 0)) -
      (-c * (W ^ 2 * A₀ ^ i / (wK ^ i * d₀)) -
        (if i = p - 2 then c * s / (wK ^ (p - 2) * C ^ 2) else 0)) ∈ lattice K k
  have hp3 := D.odd_prime
  by_cases hilast : i = p - 1
  · subst i
    have hnot : ¬p - 1 ≤ p - 2 := by omega
    have hne : p - 1 ≠ p - 2 := by omega
    simp only [if_neg hnot] at hweighted
    simp only [if_neg hne, ↓reduceIte, sub_zero]
    have hlin := cancellation_linear D L
    change Delta * s / wK ^ (p - 1) *
      (-(W ^ 2 * A₀ ^ (p - 2) / d₀) - 1 / C ^ 2) ∈ lattice K k at hlin
    have hlin' : c ^ 2 * (Delta * s / wK ^ (p - 1) *
        (-(W ^ 2 * A₀ ^ (p - 2) / d₀) - 1 / C ^ 2)) ∈ lattice K k := by
      simpa only [zero_add] using mul_mem_lattice K hcsq hlin
    have hinv' : -(c ^ 2) * (Delta / wK *
        (s / (wK ^ (p - 2) * Q ^ 2) - s / (wK ^ (p - 2) * C ^ 2))) ∈
        lattice K k := by
      simpa only [zero_add] using
        mul_mem_lattice K ((lattice K 0).neg_mem hcsq) hinvDelta
    have hpow : wK ^ (p - 1) = wK ^ (p - 2) * wK := by
      rw [← pow_succ, show p - 2 + 1 = p - 1 by omega]
    convert (lattice K k).add_mem ((lattice K k).add_mem hweighted hlin') hinv' using 1
    simp only [hpow, div_eq_mul_inv, mul_inv_rev]
    dsimp only [c]
    ring
  · have hismall : i ≤ p - 2 := by omega
    simp only [if_pos hismall] at hweighted
    simp only [if_neg hilast, sub_zero]
    by_cases hiex : i = p - 2
    · subst i
      simp only [↓reduceIte]
      have hinv' : -c * (s / (wK ^ (p - 2) * Q ^ 2) -
          s / (wK ^ (p - 2) * C ^ 2)) ∈ lattice K k := by
        simpa only [zero_add] using mul_mem_lattice K ((lattice K 0).neg_mem hc) hinv
      convert (lattice K k).add_mem hweighted hinv' using 1
      ring
    · simp only [if_neg hiex, sub_zero]
      convert hweighted using 1
      ring

end Diamond

end

end LanglandsSecondMainLemma.Odd.Linear
