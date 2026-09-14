import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Linear.Split
import LanglandsSecondMainLemma.Odd.Total.NormCoefficients

/-!
# Odd / Linear / Numerator

Paper: `O:W:numerator` and the second characteristic-polynomial identity
in `O:W:bforms`. The norm remainder is derived for the prescribed genuine
coordinate. The weight retains the actual lower norm and the denominator
`D₀`; the last power retains its linear `Delta*s` correction. All error
depths are integers, and orders may be infinite.
-/

namespace LanglandsSecondMainLemma.Odd.Linear

noncomputable section
open LanglandsFirstMainLemma
open scoped BigOperators

open private pow_mem_int_lattice natCast_mem_int_lattice_zero from
  LanglandsSecondMainLemma.Odd.Total.TranslatedNorm
open private split_div_mem split_pow_sub_mem from
  LanglandsSecondMainLemma.Odd.Linear.Split

section Estimates

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- The quadratic Taylor remainder, allowing poles in both arguments. -/
private theorem numerator_power_remainder {A z : E} {d Z : ℤ}
    (hA : A ∈ lattice E d) (hz : z ∈ lattice E Z) (hdZ : d ≤ Z) (n : ℕ) :
    (A + z) ^ n - (A ^ n + (n : E) * A ^ (n - 1) * z) ∈
      lattice E (2 * Z + ((n : ℤ) - 2) * d) := by
  have hAz := (lattice E d).add_mem hA (lattice_antitone E hdZ hz)
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : n = 0
    · subst n; simp
    have hn1 : 1 ≤ n := by omega
    have hpow : A ^ n = A ^ (n - 1) * A := by
      rw [← pow_succ, Nat.sub_add_cancel hn1]
    have heq : (A + z) ^ (n + 1) -
        (A ^ (n + 1) + ((n + 1 : ℕ) : E) * A ^ (n + 1 - 1) * z) =
        ((A + z) ^ n - (A ^ n + (n : E) * A ^ (n - 1) * z)) * (A + z) +
          (n : E) * A ^ (n - 1) * z ^ 2 := by
      simp only [pow_succ, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      rw [hpow]
      ring
    rw [heq]
    apply (lattice E _).add_mem
    · convert mul_mem_lattice E ih hAz using 1; push_cast; ring
    · have h := mul_mem_lattice E
        (mul_mem_lattice E (natCast_mem_int_lattice_zero E n)
          (pow_mem_int_lattice E hA (n - 1))) (pow_mem_int_lattice E hz 2)
      convert h using 1
      push_cast [Nat.cast_sub hn1]
      ring

/-- The three depth comparisons in the proof, including the cubic boundary.
Here `R = (p-2)*t + S` is the expanded form of the paper's bound. -/
private theorem numerator_depths (p t delta M : ℤ)
    (hp : 3 ≤ p) (ht : 1 ≤ t) (hd : 0 ≤ delta) (hM : t + 1 ≤ M) :
    let S := p * (p - 1) * delta
    let K := 1 + p * (t + delta)
    K ≤ 2 * (p - 1) * M + (S - t) ∧
      K ≤ (p - 1) * M + ((p - 2) * t + S) ∧
      K ≤ (2 * p - 1) * M + 2 * (S - t) := by
  dsimp only
  have hpt := mul_nonneg (by omega : 0 ≤ p - 3) (by omega : 0 ≤ t)
  have hdelta := mul_nonneg (mul_nonneg (by omega : 0 ≤ p)
    (by omega : 0 ≤ p - 2)) hd
  have hdelta' := mul_nonneg (mul_nonneg (by omega : 0 ≤ p)
    (by omega : 0 ≤ 2 * p - 3)) hd
  have hM₁ := mul_nonneg (by omega : 0 ≤ p - 1) (sub_nonneg.mpr hM)
  have hM₂ := mul_nonneg (by omega : 0 ≤ 2 * p - 1) (sub_nonneg.mpr hM)
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Multiply an error by precisely `W²/(wⁱ D₀)`. -/
private theorem numerator_weight_mem {W w D₀ x : E} {p M q : ℤ}
    (hW : ord E W = ((-p * M : ℤ) : WithTop ℤ))
    (hw : ord E w = ((-M : ℤ) : WithTop ℤ))
    (hD₀ : ord E D₀ = ((-p ^ 2 * M : ℤ) : WithTop ℤ))
    (hx : x ∈ lattice E q) (i : ℕ) :
    W ^ 2 / (w ^ i * D₀) * x ∈
      lattice E (q + (p * (p - 2) + (i : ℤ)) * M) := by
  have hden : ord E (w ^ i * D₀) =
      ((-(i : ℤ) * M - p ^ 2 * M : ℤ) : WithTop ℤ) := by
    rw [ord_mul, ord_pow, hw, hD₀, ← WithTop.coe_nsmul, ← WithTop.coe_add]
    congr 1
    simp only [nsmul_eq_mul]
    ring
  have h := split_div_mem E
    (mul_mem_lattice E (pow_mem_int_lattice E ((mem_lattice E).2 hW.ge) 2) hx) hden
  convert h using 1
  · ring
  · ring

/-- Weighted perturbation of a power with precisely the last linear term
retained. The inputs are the coefficient estimates, not the congruence. -/
private theorem numerator_replace {p : ℕ} (hp : 3 ≤ p)
    (t delta M : ℤ) (ht : 1 ≤ t) (hd : 0 ≤ delta) (hM : t + 1 ≤ M)
    (W w D₀ A z rho : E)
    (hW : ord E W = ((-(p : ℤ) * M : ℤ) : WithTop ℤ))
    (hw : ord E w = ((-M : ℤ) : WithTop ℤ))
    (hD₀ : ord E D₀ = ((-(p : ℤ) ^ 2 * M : ℤ) : WithTop ℤ))
    (hA : A ∈ lattice E (-(p : ℤ) * M))
    (hz : z ∈ lattice E ((p : ℤ) * (p - 1) * delta - t))
    (hrho : rho ∈ lattice E (((p : ℤ) - 2) * t + (p : ℤ) * (p - 1) * delta))
    (i : ℕ) (hip : i ≤ p - 1) :
    W ^ 2 / (w ^ i * D₀) *
      ((A + z - rho) ^ i -
        if i ≤ p - 2 then A ^ i else
          A ^ (p - 1) + ((p - 1 : ℕ) : E) * A ^ (p - 2) * z) ∈
      lattice E (1 + (p : ℤ) * (t + delta)) := by
  let S : ℤ := (p : ℤ) * (p - 1) * delta
  let Z : ℤ := S - t
  let R : ℤ := ((p : ℤ) - 2) * t + S
  let d : ℤ := -(p : ℤ) * M
  have hpz : (3 : ℤ) ≤ p := by exact_mod_cast hp
  have hS : 0 ≤ S := mul_nonneg
    (mul_nonneg (by omega : (0 : ℤ) ≤ p) (by omega : (0 : ℤ) ≤ p - 1)) hd
  have hpt := mul_nonneg (by omega : (0 : ℤ) ≤ p - 1) (by omega : 0 ≤ t)
  have hpM := mul_nonneg (by omega : (0 : ℤ) ≤ p) (sub_nonneg.mpr hM)
  have hdZ : d ≤ Z := by dsimp only [d, Z]; nlinarith
  have hZR : Z ≤ R := by dsimp only [Z, R]; nlinarith
  have hAz : A + z ∈ lattice E d :=
    (lattice E d).add_mem hA (lattice_antitone E hdZ hz)
  have hx : A + z - rho ∈ lattice E d :=
    (lattice E d).sub_mem hAz (lattice_antitone E (hdZ.trans hZR) hrho)
  obtain ⟨hsmall, hdelete, hquad⟩ := numerator_depths p t delta M hpz ht hd hM
  split_ifs with hi
  · have hdiff : A + z - rho - A ∈ lattice E Z := by
      convert (lattice E Z).sub_mem hz (lattice_antitone E hZR hrho) using 1
      ring
    have h := numerator_weight_mem E hW hw hD₀ (split_pow_sub_mem E hx hA hdiff i) i
    apply lattice_antitone E _ h
    dsimp only [Z, S, d]
    have hgap := mul_nonneg
      (mul_nonneg (by omega : (0 : ℤ) ≤ p - 1) (by omega : (0 : ℤ) ≤ p - 2 - i))
      (by omega : 0 ≤ M)
    nlinarith
  · have hi : i = p - 1 := by omega
    subst i
    have hdiff : A + z - rho - (A + z) ∈ lattice E R := by
      simpa only [sub_sub_cancel_left] using (lattice E R).neg_mem hrho
    have h₁ := numerator_weight_mem E hW hw hD₀
      (split_pow_sub_mem E hx hAz hdiff (p - 1)) (p - 1)
    have h₂ := numerator_weight_mem E hW hw hD₀
      (numerator_power_remainder E hA hz hdZ (p - 1)) (p - 1)
    have h₁' : W ^ 2 / (w ^ (p - 1) * D₀) *
        ((A + z - rho) ^ (p - 1) - (A + z) ^ (p - 1)) ∈
        lattice E (1 + (p : ℤ) * (t + delta)) := by
      apply lattice_antitone E _ h₁
      dsimp only [R, S, d]
      push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
      nlinarith
    have h₂' : W ^ 2 / (w ^ (p - 1) * D₀) *
        ((A + z) ^ (p - 1) -
          (A ^ (p - 1) + ((p - 1 : ℕ) : E) * A ^ (p - 2) * z)) ∈
        lattice E (1 + (p : ℤ) * (t + delta)) := by
      apply lattice_antitone E _ (by
        simpa only [Nat.sub_sub, show 1 + 1 = 2 by rfl] using h₂)
      push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
      nlinarith
    convert (lattice E _).add_mem h₁' h₂' using 1
    ring

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
/-- The second identity of `O:W:bforms`, for the actual norm and signed
symmetric coefficient. The remainder is constructed by subtraction. -/
private theorem numerator_norm_remainder :
    algebraMap B₁ K (norm B₁ K Delta) -
      (Delta + algebraMap B₂ K a - Delta * algebraMap B₁ K (linearS D Delta)) ∈
      lattice K ((p : ℤ) * (p - 1) * D.t₂ -
        ((p : ℤ) ^ 2 - 2 * p + 2) * D.t) := by
  classical
  have hp3 := D.odd_prime
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hdegree : Module.finrank B₁ K = p :=
    (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.2.2.1
  let f (j : ℕ) : K := (-1 : K) ^ j *
    algebraMap B₁ K (elementarySymmetric B₁ K j Delta) * Delta ^ (p - j)
  have hn := Total.odd_norm_expansion B₁ K hpodd hdegree Delta
  have hlast : p - 1 ∈ Finset.Icc 1 (p - 1) := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hsign : (-1 : K) ^ (p - 1) = 1 := by
    apply Even.neg_one_pow
    obtain ⟨k, hk⟩ := hpodd
    exact ⟨k, by omega⟩
  have hf : f (p - 1) = -Delta * algebraMap B₁ K (linearS D Delta) := by
    simp only [f, hsign, one_mul, show p - (p - 1) = 1 by omega,
      pow_one, linearS, map_neg]
    ring
  have heq : algebraMap B₁ K (norm B₁ K Delta) -
      (Delta + algebraMap B₂ K a - Delta * algebraMap B₁ K (linearS D Delta)) =
      ∑ j ∈ (Finset.Icc 1 (p - 1)).erase (p - 1), f j := by
    rw [hn]
    change Delta ^ p + (∑ j ∈ Finset.Icc 1 (p - 1), f j) - _ = _
    rw [← Finset.sum_erase_add _ f hlast, hf]
    linear_combination L.root
  rw [heq]
  apply sum_mem_lattice K
  intro j hj
  obtain ⟨hne, hj⟩ := Finset.mem_erase.mp hj
  obtain ⟨hj1, hjp⟩ := Finset.mem_Icc.mp hj
  have hj2 : j ≤ p - 2 := by omega
  have hsignmem : (-1 : K) ^ j ∈ lattice K 0 := by
    simp only [mem_lattice, ord_pow, ord_neg, ord_one, nsmul_zero,
      WithTop.coe_zero, le_refl]
  have hterm := mul_mem_lattice K
    (mul_mem_lattice K hsignmem ((mem_lattice K).2 (L.symmetric_order j hj1 (by omega))))
    (pow_mem_int_lattice K ((mem_lattice K).2 L.Delta_order.ge) (p - j))
  apply lattice_antitone K _ hterm
  simp only [zero_add, Nat.cast_sub (by omega : j ≤ p)]
  have hgap := mul_nonneg
    (mul_nonneg (by omega : (0 : ℤ) ≤ p - 1) (by omega : (0 : ℤ) ≤ p - 2 - j))
    (Int.natCast_nonneg D.t)
  nlinarith

omit [Module.Free F K] in
/-- Paper Lemma `O:W:numerator` (9.5), modulo `𝔭_K^(1+p*t₂)`.
The coordinate, `w`, `W = n₂ w`, `Y = W + N₁ Delta`, and `D₀` are the
prescribed genuine data. The setup has the proved constructor
`oddLinearData_construct`. The coefficient `s` is exactly `-e_{p-1}`;
its linear contribution is retained precisely at `i = p-1`. No field
characteristic is excluded and no replacement congruence is assumed. -/
theorem numerator (i : ℕ) (_hi : 1 ≤ i) (hip : i ≤ p - 1) :
    let wK := algebraMap B₂ K (w : B₂)
    let W := algebraMap F K (transitionNorm D w)
    let Y := algebraMap B₁ K (transitionY D Delta w)
    let D₀ := algebraMap B₂ K (transitionD₀ D a w)
    let A₀ := -algebraMap B₂ K a - W
    let s := algebraMap B₁ K (linearS D Delta)
    W ^ 2 * (Delta - Y) ^ i / (wK ^ i * D₀) -
      W ^ 2 / (wK ^ i * D₀) *
        (if i ≤ p - 2 then A₀ ^ i else
          A₀ ^ (p - 1) + ((p - 1 : ℕ) : K) * A₀ ^ (p - 2) * Delta * s) ∈
      lattice K (1 + (p : ℤ) * D.t₂) := by
  let wK := algebraMap B₂ K (w : B₂)
  let W := algebraMap F K (transitionNorm D w)
  let Y := algebraMap B₁ K (transitionY D Delta w)
  let D₀ := algebraMap B₂ K (transitionD₀ D a w)
  let A₀ := -algebraMap B₂ K a - W
  let s := algebraMap B₁ K (linearS D Delta)
  let rho := algebraMap B₁ K (norm B₁ K Delta) -
    (Delta + algebraMap B₂ K a - Delta * s)
  let M : ℤ := (p : ℤ) * m
  have ht : (1 : ℤ) ≤ D.t := by exact_mod_cast D.t_pos
  have hd : (0 : ℤ) ≤ D.delta := Int.natCast_nonneg _
  have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
  have hW : ord K W = ((-(p : ℤ) * M : ℤ) : WithTop ℤ) := by
    convert L.W_order_K using 1; dsimp only [M]; congr 1; ring
  have hw : ord K wK = ((-M : ℤ) : WithTop ℤ) := L.w_order_K
  have hD₀ : ord K D₀ = ((-(p : ℤ) ^ 2 * M : ℤ) : WithTop ℤ) := by
    convert L.D₀_order using 1; dsimp only [M]; congr 1; ring
  have hA : A₀ ∈ lattice K (-(p : ℤ) * M) := by
    apply (lattice K _).sub_mem
    · apply (lattice K _).neg_mem
      apply lattice_antitone K _ ((mem_lattice K).2 L.a_order_K.ge)
      have hpz : (0 : ℤ) ≤ p := Int.natCast_nonneg _
      have htM : (D.t : ℤ) ≤ M := by have := L.transition; dsimp only [M]; omega
      simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_left htM hpz)
    · exact (mem_lattice K).2 hW.ge
  have hz : Delta * s ∈ lattice K ((p : ℤ) * (p - 1) * D.delta - D.t) := by
    convert mul_mem_lattice K ((mem_lattice K).2 L.Delta_order.ge)
      ((mem_lattice K).2 L.s_order) using 1
    ring
  have hrho : rho ∈ lattice K
      (((p : ℤ) - 2) * D.t + (p : ℤ) * (p - 1) * D.delta) := by
    convert numerator_norm_remainder D L using 1
    rw [ht₂]
    ring
  have hxy : Delta - Y = A₀ + Delta * s - rho := by
    dsimp only [Y, A₀, rho, transitionY]
    rw [map_add, ← IsScalarTower.algebraMap_apply F B₁ K]
    ring
  have h := numerator_replace K (by have := D.odd_prime; omega)
    D.t D.delta M ht hd L.transition W wK D₀ A₀ (Delta * s) rho
    hW hw hD₀ hA hz hrho i hip
  change W ^ 2 * (Delta - Y) ^ i / (wK ^ i * D₀) -
    W ^ 2 / (wK ^ i * D₀) * (if i ≤ p - 2 then A₀ ^ i else
      A₀ ^ (p - 1) + ((p - 1 : ℕ) : K) * A₀ ^ (p - 2) * Delta * s) ∈ _
  rw [hxy, ht₂]
  convert h using 1
  split_ifs <;> ring

end Diamond

end

end LanglandsSecondMainLemma.Odd.Linear
