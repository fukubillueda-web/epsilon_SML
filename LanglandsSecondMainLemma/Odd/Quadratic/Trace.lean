import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Quadratic.SingleSum
import LanglandsSecondMainLemma.Finite.Interpolation

/-!
# Quadratic trace at the full modulus

Paper `O:D:quadratic`, with the genuine trace from `O:D:WPdef`.
The finite calculation uses the exact identity and its algebraic derivative
from `Finite.Interpolation`. All error estimates retain the outer factor
`T / w^(p-1)` and use integer lattices in the common field. The resulting
right side is a common-field expression; its character is not evaluated here.
-/

namespace LanglandsSecondMainLemma.Odd.Quadratic

noncomputable section
open LanglandsFirstMainLemma
open scoped BigOperators

open private pow_mem_int_lattice natCast_mem_int_lattice_zero from
  LanglandsSecondMainLemma.Odd.Total.TranslatedNorm
open private pow_sub_pow_mem_lattice from
  LanglandsSecondMainLemma.Odd.Total.CoefficientExtraction
open private inner_mem from LanglandsSecondMainLemma.Odd.Quadratic.Conjugates
open private realization_tower_data from LanglandsSecondMainLemma.Odd.Models.Realization
open private ne_zero_of_order from LanglandsSecondMainLemma.Odd.Linear.Setup
open private nonpole_ne nonpole_zero_ne nonpole_frobenius_sub_ne from
  LanglandsSecondMainLemma.Finite.Interpolation

section Rational

variable {E : Type*} [Field E]

/-- Collecting the exact interpolation formula and its derivative gives
the four terms of `O:D:derivative`; the last term is split at its `p` factor. -/
private theorem quadratic_sum_exact {p : ℕ} {zeta : E}
    (hprime : p.Prime) (hp : 2 < p) (hzeta : IsPrimitiveRoot zeta (p - 1))
    (Delta W b : E) (hW : W ≠ 0)
    (hL : -(W + b) ∉ Finite.teichmullerSet E p) :
    (∑ xi ∈ Finite.teichmullerSet E p,
      (Delta + xi) ^ (p - 1) * ((b + xi) / (1 + (b + xi) / W) ^ 2)) =
      (p - 1 : ℕ) * W ^ 2 * (Delta - (W + b)) ^ (p - 2) * (Delta - b) /
          ((W + b) ^ p - (W + b)) +
        (p : E) * W ^ 2 * Delta ^ (p - 1) * b / (W + b) ^ 2 -
        (p : E) * (p - 1 : ℕ) * W ^ 3 * (Delta - (W + b)) ^ (p - 2) /
          ((W + b) ^ p - (W + b)) -
        (p : E) * (p - 1 : ℕ) * W ^ 3 * (Delta - (W + b)) ^ (p - 1) *
          (W + b) ^ (p - 1) / ((W + b) ^ p - (W + b)) ^ 2 +
        (p - 1 : ℕ) * W ^ 3 * (Delta - (W + b)) ^ (p - 1) /
          ((W + b) ^ p - (W + b)) ^ 2 := by
  have hsum : (∑ xi ∈ Finite.teichmullerSet E p,
      (Delta + xi) ^ (p - 1) * ((b + xi) / (1 + (b + xi) / W) ^ 2)) =
      W ^ 2 * ((∑ xi ∈ Finite.teichmullerSet E p,
        (Delta + xi) ^ (p - 1) / (W + b + xi)) -
        W * ∑ xi ∈ Finite.teichmullerSet E p,
          (Delta + xi) ^ (p - 1) / (W + b + xi) ^ 2) := by
    simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro xi hxi
    have hden := nonpole_ne hL hxi
    rw [show 1 + (b + xi) / W = (W + b + xi) / W by field_simp; ring]
    field_simp [hW, hden]
    ring
  rw [hsum, Finite.interpolation hprime hp hzeta (by omega) Delta (W + b) hL,
    Finite.interpolation_derivative hprime hp hzeta (by omega) Delta (W + b) hL]
  have hLn := nonpole_zero_ne hL
  have hDn := nonpole_frobenius_sub_ne hprime hp hL
  have hpow : (Delta - (W + b)) ^ (p - 1) =
      (Delta - (W + b)) ^ (p - 2) * (Delta - (W + b)) := by
    rw [show p - 1 = p - 2 + 1 by omega, pow_succ]
  rw [show p - 1 - 1 = p - 2 by omega, hpow]
  push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
  field_simp [hLn, hDn]
  ring

end Rational

section Lattices

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

private theorem quotient_mem {x y : E} {n d : ℤ}
    (hx : x ∈ lattice E n) (hy : ord E y = (d : WithTop ℤ)) :
    x / y ∈ lattice E (n - d) := by
  apply (div_mem_lattice_iff E y x d (n - d) hy).2
  simpa only [add_sub_cancel] using hx

/-- Subtraction of fractions at possibly negative depths. -/
private theorem quotient_sub_mem {x y u v : E} {n d H : ℤ}
    (hy : y ∈ lattice E n)
    (hu : ord E u = (d : WithTop ℤ)) (hv : ord E v = (d : WithTop ℤ))
    (hxy : x - y ∈ lattice E (n + H)) (huv : u - v ∈ lattice E (d + H)) :
    x / u - y / v ∈ lattice E (n - d + H) := by
  rw [div_sub_div _ _ (ne_zero_of_order E hu) (ne_zero_of_order E hv)]
  have heq : x * v - u * y = (x - y) * v - y * (u - v) := by ring
  rw [heq]
  have h₁ := mul_mem_lattice E hxy hv.ge
  have h₂ := mul_mem_lattice E hy huv
  have hn : (x - y) * v - y * (u - v) ∈ lattice E (n + H + d) :=
    (lattice E _).sub_mem h₁ (by convert h₂ using 1; congr 1; ring)
  have hd : ord E (u * v) = ((d + d : ℤ) : WithTop ℤ) := by
    rw [ord_mul, hu, hv, ← WithTop.coe_add]
  convert quotient_mem E hn hd using 1
  congr 1
  ring

end Lattices

section Representatives

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra F K] (p : ℕ) [Fact p.Prime]
  (hchar : residueCharacteristic F = p)

local instance : DecidableEq K := Classical.decEq K

private def representativeMap : ZMod p →*₀ K :=
  ((algebraMap F K).comp (algebraMap (ringOfIntegers F) F)).toMonoidWithZeroHom.comp
    (primeTeichmuller F p hchar)

private theorem representative_injective :
    Function.Injective (representativeMap F K p hchar) := by
  apply (algebraMap F K).injective.comp
  apply Subtype.coe_injective.comp
  exact (teichmuller_injective F).comp
    (ZMod.castHom (by simp [hchar]) (ResidueField F)).injective

/-- The actual prime-field Teichmuller representatives enumerate the
entire root set used by exact interpolation, also in mixed characteristic. -/
private theorem representative_set (hp : 2 < p) :
    ∃ zeta : K, IsPrimitiveRoot zeta (p - 1) ∧
      Finset.univ.image (representativeMap F K p hchar) = Finite.teichmullerSet K p := by
  classical
  let c := representativeMap F K p hchar
  have hc : Function.Injective c := representative_injective F K p hchar
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hgprim : IsPrimitiveRoot (g : ZMod p) (p - 1) := by
    apply IsPrimitiveRoot.coe_units_iff.2
    apply IsPrimitiveRoot.iff_orderOf.2
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units] using hg
  have hz : IsPrimitiveRoot (c (g : ZMod p)) (p - 1) := hgprim.map_of_injective hc
  refine ⟨c (g : ZMod p), hz, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    change c j ∈ Finite.teichmullerSet K p
    by_cases hj : c j = 0
    · simp [Finite.teichmullerSet, hj]
    · have hroot : c j ^ p = c j := by
        rw [← map_pow]
        congr 1
        simpa only [ZMod.card] using FiniteField.pow_card j
      have hpow : c j ^ (p - 1) = 1 := by
        apply (mul_eq_right₀ hj).1
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
        exact hroot
      simp [Finite.teichmullerSet, Finite.teichmullerUnits,
        Polynomial.mem_nthRootsFinset (by omega : 0 < p - 1), hpow]
  · have hzero : (0 : K) ∉ Finite.teichmullerUnits K p := by
      simp [Finite.teichmullerUnits,
        Polynomial.mem_nthRootsFinset (by omega : 0 < p - 1),
        zero_pow (by omega : p - 1 ≠ 0)]
    rw [Finite.teichmullerSet, Finset.card_insert_of_notMem hzero,
      Finset.card_image_of_injective _ hc, Finset.card_univ, ZMod.card]
    change (Polynomial.nthRootsFinset (p - 1) (1 : K)).card + 1 ≤ p
    rw [hz.card_nthRootsFinset]
    omega

end Representatives

/-- The five weighted discard bounds of `O:D:quadratic`. The bound on
`p` is finite, so it applies as well when its actual order is infinity. -/
private theorem trace_depths (p t delta M : ℤ)
    (hp : 3 ≤ p) (ht : 0 ≤ t) (hd : 0 ≤ delta) (hM : t + 1 ≤ M) :
    let S := p * (p - 1) * delta
    let E := p * (p - 1) * (t + delta)
    let K := 1 + p * (t + delta)
    K ≤ S + 2 * (p - 1) * M + E - (2 * p - 1) * t ∧
    K ≤ S + 2 * (p - 1) * M + E - p * M ∧
    K ≤ S + 2 * (p - 1) * M + p * (p - 2) * M ∧
    K ≤ S + 2 * (p - 1) * M + p * delta - t ∧
    K ≤ S + 2 * (p - 1) * M - p * t + (p * M - t) := by
  dsimp only
  have hp₁ : 0 ≤ p ^ 2 - 2 * p - 1 := by nlinarith
  have hp₂ : 0 ≤ p ^ 2 - p - 2 := by nlinarith
  have ht₁ := mul_nonneg hp₁ ht
  have ht₂ := mul_nonneg hp₂ ht
  have ht₃ := mul_nonneg (by omega : 0 ≤ p - 3) ht
  have hd₁ := mul_nonneg (mul_nonneg (by omega : 0 ≤ p) (by omega : 0 ≤ 2 * p - 3)) hd
  have hd₂ := mul_nonneg (mul_nonneg (by omega : 0 ≤ p) (by omega : 0 ≤ p - 2)) hd
  have hd₃ := mul_nonneg (mul_nonneg (by omega : 0 ≤ p) (by omega : 0 ≤ p - 1)) hd
  have hM₁ := mul_nonneg (by omega : 0 ≤ 2 * (p - 1)) (by omega : 0 ≤ M - t - 1)
  have hM₂ := mul_nonneg (by omega : 0 ≤ p - 2) (by omega : 0 ≤ M - t - 1)
  have hM₃ := mul_nonneg (by nlinarith : 0 ≤ p ^ 2 - 2) (by omega : 0 ≤ M - t - 1)
  have hM₄ := mul_nonneg (by omega : 0 ≤ 3 * p - 2) (by omega : 0 ≤ M - t - 1)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

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

variable {D} {Delta : K} {a : D.B₂} {w : D.B₂ˣ} {m : ℤ}
  (L : Linear.OddLinearData D Delta a w m)

local notation "P" => (p : ℤ)
local notation "q" => (p - 1 : ℕ)
local notation "M" => ((p : ℤ) * m)
local notation "S" => ((p : ℤ) * (p - 1) * D.delta : ℤ)
local notation "v" => algebraMap B₂ K (w : B₂)
local notation "W" => algebraMap F K (Linear.transitionNorm D w)
local notation "b" => algebraMap B₁ K (norm B₁ K Delta)
local notation "aK" => algebraMap B₂ K a
local notation "T" => algebraMap B₁ K (quadraticInner D w Delta)
local notation "Z" => (W + b)
local notation "A" => (Delta - Z)
local notation "U" => (W + aK)
local notation "C" => (1 + aK / W)
local notation "DZ" => (Z ^ p - Z)
local notation "H" => (P * M - D.t)

include L

omit [Module.Free F K] in
/-- The norm remainder `a*omega` in `O:D:omega` follows from the actual
characteristic polynomial and the supplied proved symmetric bounds. -/
private theorem norm_remainder (hres : residueDegree F K = 1) :
    b - Delta - aK ∈ lattice K (P * D.delta - D.t) := by
  obtain ⟨hdegree, _, _, _, _⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  have hodd := hp.odd_of_ne_two (by have := D.odd_prime; omega)
  have hn := Total.odd_norm_expansion B₁ K hodd hdegree Delta
  have heq : b - Delta - aK = ∑ i ∈ Finset.Icc 1 q,
      (-1 : K) ^ i * algebraMap B₁ K (elementarySymmetric B₁ K i Delta) *
        Delta ^ (p - i) := by
    linear_combination hn + L.root
  rw [heq]
  apply sum_mem_lattice K
  intro i hi
  obtain ⟨hi, hip⟩ := Finset.mem_Icc.mp hi
  have hsign : (-1 : K) ^ i ∈ lattice K 0 := by
    simp only [mem_lattice, ord_pow, ord_neg, ord_one, nsmul_zero, WithTop.coe_zero, le_refl]
  have hterm := mul_mem_lattice K
    (mul_mem_lattice K hsign (L.symmetric_order i hi (by omega)))
    (pow_mem_int_lattice K L.Delta_order.ge (p - i))
  apply lattice_antitone K _ hterm
  have hpZ : (3 : ℤ) ≤ P := by exact_mod_cast D.odd_prime
  have hiZ : (i : ℤ) ≤ P - 1 := by omega
  have ht := Int.natCast_nonneg D.t
  have hd := Int.natCast_nonneg D.delta
  have hb := mul_nonneg (mul_nonneg (by omega : 0 ≤ P - 1)
    (by omega : 0 ≤ P - 1 - i)) ht
  have hb' := mul_nonneg (mul_nonneg (by omega : 0 ≤ P) (by omega : 0 ≤ P - 2)) hd
  rw [D.t₂_eq]
  push_cast [Nat.cast_sub (by omega : i ≤ p)]
  nlinarith

omit [Module.Free F K] in
private theorem common_orders :
    ord K Z = ((- (P * M) : ℤ) : WithTop ℤ) ∧
    ord K A = ((- (P * M) : ℤ) : WithTop ℤ) ∧
    ord K DZ = ((- (P ^ 2 * M) : ℤ) : WithTop ℤ) ∧
    ord K U = ((- (P * M) : ℤ) : WithTop ℤ) := by
  have hpZ : (3 : ℤ) ≤ P := by exact_mod_cast D.odd_prime
  have ht := Int.natCast_nonneg D.t
  have hM := L.transition
  have hgap : -(P * M) < -(D.t : ℤ) := by nlinarith
  have hW : ord K W = ((-(P * M) : ℤ) : WithTop ℤ) := by
    convert L.W_order_K using 1
    congr 1
    ring
  have hZ : ord K Z = ((-(P * M) : ℤ) : WithTop ℤ) := by
    have h := L.Y_order
    simp only [Linear.transitionY, map_add, ← IsScalarTower.algebraMap_apply F B₁ K] at h
    convert h using 1
    congr 1
    ring
  refine ⟨hZ, ?_, ?_, ?_⟩
  · rw [sub_eq_add_neg, (ord K).map_add_eq_of_lt_right (by
      rw [ord_neg, hZ, L.Delta_order]
      exact WithTop.coe_lt_coe.mpr hgap), ord_neg, hZ]
  · have h := L.D_order
    simp only [Linear.transitionD, Linear.transitionY, map_sub, map_pow, map_add,
      ← IsScalarTower.algebraMap_apply F B₁ K] at h
    convert h using 1
    congr 1
    ring
  · rw [(ord K).map_add_eq_of_lt_left (by
      rw [hW, L.a_order_K]
      exact WithTop.coe_lt_coe.mpr (by nlinarith)), hW]

omit [Module.Free F K] in
private theorem weight_mem : T / v ^ q ∈ lattice K (S + 2 * (P - 1) * M) := by
  have hw : ord K (v ^ q) = (((-(P - 1) * M : ℤ)) : WithTop ℤ) := by
    rw [ord_pow, L.w_order_K, ← WithTop.coe_nsmul]
    simp only [nsmul_eq_mul, Nat.cast_sub hp.one_le, Nat.cast_one]
    congr 1
    ring
  have h := quotient_mem K (inner_mem L) hw
  convert h using 1
  congr 1
  ring

omit [Module.Free F K] in
/-- The leading quotient differs from `-C⁻²` at depth `p*M-t`.
Only exact fraction subtraction and power differences are used. -/
private theorem leading_ratio_mem (hres : residueDegree F K = 1) :
    W ^ 2 * A ^ (p - 2) / DZ + 1 / C ^ 2 ∈ lattice K H := by
  have hp3 : 3 ≤ p := by exact D.odd_prime
  have hpZ : (3 : ℤ) ≤ P := by exact_mod_cast hp3
  have ht := Int.natCast_nonneg D.t
  have hd := Int.natCast_nonneg D.delta
  have hM := L.transition
  obtain ⟨hZ, hA, hD, hU⟩ := common_orders L
  have hW : ord K W = ((-(P * M) : ℤ) : WithTop ℤ) := by
    convert L.W_order_K using 1
    congr 1
    ring
  have hWn := ne_zero_of_order K hW
  have hUn := ne_zero_of_order K hU
  have hr : b - Delta - aK ∈ lattice K (-(D.t : ℤ)) :=
    lattice_antitone K (by nlinarith) (norm_remainder L hres)
  have hAU : A - (-U) ∈ lattice K (-(D.t : ℤ)) := by
    convert (lattice K _).neg_mem hr using 1
    ring
  have hZU : Z - U ∈ lattice K (-(D.t : ℤ)) := by
    convert (lattice K _).add_mem hr L.Delta_order.ge using 1
    ring
  have hnegU : ord K (-U) = ((-(P * M) : ℤ) : WithTop ℤ) := by rw [ord_neg, hU]
  have hpowA := pow_sub_pow_mem_lattice K hA.ge hnegU.ge hAU (p - 2)
  have hpowZ := pow_sub_pow_mem_lattice K hZ.ge hU.ge hZU p
  have hWp : W ^ 2 ∈ lattice K (-2 * (P * M)) := by
    convert pow_mem_int_lattice K hW.ge 2 using 1
    norm_num
  have hnum : W ^ 2 * A ^ (p - 2) - W ^ 2 * (-U) ^ (p - 2) ∈
      lattice K (-(P ^ 2 * M) + H) := by
    rw [← mul_sub]
    convert mul_mem_lattice K hWp hpowA using 1
    congr 1
    push_cast [Nat.cast_sub (by omega : 1 ≤ p - 2), Nat.cast_sub (by omega : 2 ≤ p)]
    ring
  have hden : DZ - U ^ p ∈ lattice K (-(P ^ 2 * M) + H) := by
    have hpow : Z ^ p - U ^ p ∈ lattice K (-(P ^ 2 * M) + H) := by
      convert hpowZ using 1
      congr 1
      push_cast [Nat.cast_sub hp.one_le]
      ring
    have hzdeep : Z ∈ lattice K (-(P ^ 2 * M) + H) := by
      apply lattice_antitone K _ hZ.ge
      have hpos : 0 ≤ P * (P - 2) * M :=
        mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
      nlinarith
    convert (lattice K _).sub_mem hpow hzdeep using 1
    ring
  have hnum' : W ^ 2 * (-U) ^ (p - 2) ∈ lattice K (-(P ^ 2 * M)) := by
    convert mul_mem_lattice K hWp (pow_mem_int_lattice K hnegU.ge (p - 2)) using 1
    congr 1
    push_cast [Nat.cast_sub (by omega : 2 ≤ p)]
    ring
  have hUp : ord K (U ^ p) = ((-(P ^ 2 * M) : ℤ) : WithTop ℤ) := by
    rw [ord_pow, hU, ← WithTop.coe_nsmul]
    congr 1
    simp only [nsmul_eq_mul]
    ring
  have hquot := quotient_sub_mem K hnum' hD hUp hnum hden
  have hodd : Odd (p - 2) := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
    use k - 1
    omega
  have heq : W ^ 2 * (-U) ^ (p - 2) / U ^ p = -(1 / C ^ 2) := by
    rw [hodd.neg_pow]
    have hUpow : U ^ p = U ^ (p - 2) * U ^ 2 := by
      rw [← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ p)]
    rw [hUpow, show C = U / W by field_simp]
    field_simp [hUn, hWn]
  rw [heq] at hquot
  simpa only [sub_self, zero_add, sub_neg_eq_add] using hquot

omit [Module.Free F K] in
/-- Both errors in the first term of `O:D:derivative` reach the full
modulus after the original outer weight has been restored. -/
private theorem leading_term (hres : residueDegree F K = 1) :
    T / v ^ q * ((q : K) * W ^ 2 * A ^ (p - 2) * (Delta - b) / DZ) -
      (q : K) * aK * T / (v ^ q * C ^ 2) ∈ lattice K (1 + P * D.t₂) := by
  have hpZ : (3 : ℤ) ≤ P := by exact_mod_cast D.odd_prime
  have depths := trace_depths P D.t D.delta M hpZ
    (Int.natCast_nonneg _) (Int.natCast_nonneg _) L.transition
  dsimp only at depths
  have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
  rw [← ht₂] at depths
  have hq : (q : K) ∈ lattice K 0 := natCast_mem_int_lattice_zero K q
  have hweight : T / v ^ q * (q : K) ∈ lattice K (S + 2 * (P - 1) * M) := by
    simpa only [add_zero] using mul_mem_lattice K (weight_mem L) hq
  have hdb : Delta - b ∈ lattice K (-(P * D.t)) := by
    apply (lattice K _).sub_mem _ L.b_order_K.ge
    apply lattice_antitone K _ L.Delta_order.ge
    nlinarith [Int.natCast_nonneg D.t]
  have hc := L.denominator_order aK L.a_order_K
  have hr : (b - Delta - aK) / C ^ 2 ∈ lattice K (P * D.delta - D.t) := by
    apply (div_mem_lattice_iff K _ _ 0 _ (by
      simp only [ord_pow, hc, nsmul_zero, WithTop.coe_zero])).2
    simpa only [zero_add] using norm_remainder L hres
  have he₁ := mul_mem_lattice K hweight (mul_mem_lattice K (leading_ratio_mem L hres) hdb)
  have he₂ := mul_mem_lattice K hweight hr
  have heq : T / v ^ q * ((q : K) * W ^ 2 * A ^ (p - 2) * (Delta - b) / DZ) -
      (q : K) * aK * T / (v ^ q * C ^ 2) =
      (T / v ^ q * (q : K)) * ((W ^ 2 * A ^ (p - 2) / DZ + 1 / C ^ 2) * (Delta - b)) +
      (T / v ^ q * (q : K)) * ((b - Delta - aK) / C ^ 2) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq]
  apply (lattice K _).add_mem
  · apply lattice_antitone K _ he₁
    convert depths.2.2.2.2 using 1
    ring
  · apply lattice_antitone K _ he₂
    convert depths.2.2.2.1 using 1
    ring

omit [Module.Free F K] in
/-- The remaining four summands are discarded only with the complete
outer weight. No division by the residue characteristic occurs. -/
private theorem discarded_terms :
    T / v ^ q *
      ((p : K) * W ^ 2 * Delta ^ q * b / Z ^ 2 -
        (p : K) * (q : K) * W ^ 3 * A ^ (p - 2) / DZ -
        (p : K) * (q : K) * W ^ 3 * A ^ q * Z ^ q / DZ ^ 2 +
        (q : K) * W ^ 3 * A ^ q / DZ ^ 2) ∈ lattice K (1 + P * D.t₂) := by
  have hpZ : (3 : ℤ) ≤ P := by exact_mod_cast D.odd_prime
  have hp3 : 3 ≤ p := D.odd_prime
  have depths := trace_depths P D.t D.delta M hpZ
    (Int.natCast_nonneg _) (Int.natCast_nonneg _) L.transition
  dsimp only at depths
  have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
  rw [← ht₂] at depths
  obtain ⟨hZ, hA, hD, _⟩ := common_orders L
  have hW : ord K W = ((-(P * M) : ℤ) : WithTop ℤ) := by
    convert L.W_order_K using 1
    congr 1
    ring
  have hZ2 : ord K (Z ^ 2) = ((-2 * (P * M) : ℤ) : WithTop ℤ) := by
    rw [ord_pow, hZ, ← WithTop.coe_nsmul]
    congr 1
    norm_num [nsmul_eq_mul]
  have hD2 : ord K (DZ ^ 2) = ((-2 * (P ^ 2 * M) : ℤ) : WithTop ℤ) := by
    rw [ord_pow, hD, ← WithTop.coe_nsmul]
    congr 1
    norm_num [nsmul_eq_mul]
  have hq := natCast_mem_int_lattice_zero K q
  have hpq : (p : K) * (q : K) ∈ lattice K (P * (P - 1) * D.t₂) := by
    simpa only [add_zero] using mul_mem_lattice K L.prime_order hq
  have hW2 := pow_mem_int_lattice K hW.ge 2
  have hW3 := pow_mem_int_lattice K hW.ge 3
  have hAq := pow_mem_int_lattice K hA.ge q
  have hZq := pow_mem_int_lattice K hZ.ge q
  have hA2 := pow_mem_int_lattice K hA.ge (p - 2)
  have hΔq := pow_mem_int_lattice K L.Delta_order.ge q
  have h₁ : (p : K) * W ^ 2 * Delta ^ q * b / Z ^ 2 ∈
      lattice K (P * (P - 1) * D.t₂ - (2 * P - 1) * D.t) := by
    convert quotient_mem K
      (mul_mem_lattice K (mul_mem_lattice K (mul_mem_lattice K L.prime_order hW2) hΔq)
        L.b_order_K.ge) hZ2 using 1
    congr 1
    push_cast [Nat.cast_sub hp.one_le]
    ring
  have h₂ : (p : K) * (q : K) * W ^ 3 * A ^ (p - 2) / DZ ∈
      lattice K (P * (P - 1) * D.t₂ - P * M) := by
    convert quotient_mem K (mul_mem_lattice K (mul_mem_lattice K hpq hW3) hA2) hD using 1
    congr 1
    push_cast [Nat.cast_sub (by omega : 2 ≤ p)]
    ring
  have h₃ : (p : K) * (q : K) * W ^ 3 * A ^ q * Z ^ q / DZ ^ 2 ∈
      lattice K (P * (P - 1) * D.t₂ - P * M) := by
    convert quotient_mem K
      (mul_mem_lattice K (mul_mem_lattice K (mul_mem_lattice K hpq hW3) hAq) hZq) hD2 using 1
    congr 1
    push_cast [Nat.cast_sub hp.one_le]
    ring
  have h₄ : (q : K) * W ^ 3 * A ^ q / DZ ^ 2 ∈ lattice K (P * (P - 2) * M) := by
    convert quotient_mem K (mul_mem_lattice K (mul_mem_lattice K hq hW3) hAq) hD2 using 1
    congr 1
    push_cast [Nat.cast_sub hp.one_le]
    ring
  have discard (x : K) (n : ℤ) (hx : x ∈ lattice K n)
      (hn : 1 + P * D.t₂ ≤ S + 2 * (P - 1) * M + n) :
      T / v ^ q * x ∈ lattice K (1 + P * D.t₂) :=
    lattice_antitone K hn (mul_mem_lattice K (weight_mem L) hx)
  simp only [mul_add, mul_sub]
  exact (lattice K _).add_mem
    ((lattice K _).sub_mem
      ((lattice K _).sub_mem (discard _ _ h₁ (by convert depths.1 using 1; ring))
        (discard _ _ h₂ (by convert depths.2.1 using 1; ring)))
      (discard _ _ h₃ (by convert depths.2.1 using 1; ring)))
    (discard _ _ h₄ depths.2.2.1)

/-- Paper `O:D:quadratic` (Theorem 9.11). The genuine `B₂` quadratic
trace satisfies the congruence in the common field at the full modulus
`1+p*t₂`, for every odd prime and both field characteristics. The setup
has the proved constructor `Odd.Linear.oddLinearData_construct`.
The right side is only asserted to lie in the common field: constructing
a `B₂` representative remains necessary before applying its character. -/
theorem trace (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = p) :
    algebraMap B₂ K (quadraticTrace D Delta w) -
      (q : K) * aK * T /
        (v ^ q * (algebraMap B₂ K (Linear.transitionC D a w)) ^ 2) ∈
      lattice K (1 + P * D.t₂) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨zeta, hzeta, hset⟩ := representative_set F K p hchar D.odd_prime
  have hnot : -Z ∉ Finite.teichmullerSet K p := by
    intro hz
    rw [← hset] at hz
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hz
    have hint : representativeMap F K p hchar j ∈ lattice K 0 := by
      change algebraMap F K (primeTeichmuller F p hchar j : F) ∈ lattice K 0
      rw [mem_lattice, ord_algebraMap]
      exact nsmul_nonneg ((mem_lattice_zero_iff F).2
        (primeTeichmuller F p hchar j).property) _
    rw [hj, mem_lattice, ord_neg, (common_orders L).1, WithTop.coe_le_coe] at hint
    have hpZ : (3 : ℤ) ≤ P := by exact_mod_cast D.odd_prime
    have ht := Int.natCast_nonneg D.t
    have hM := L.transition
    nlinarith
  have hreindex (f : K → K) :
      (∑ j : ZMod p, f (algebraMap F K (primeTeichmuller F p hchar j : F))) =
        ∑ xi ∈ Finite.teichmullerSet K p, f xi := by
    rw [← hset, Finset.sum_image (representative_injective F K p hchar).injOn]
    rfl
  have hsum := quadratic_sum_exact hp D.odd_prime hzeta Delta W b
    (ne_zero_of_order K L.W_order_K) hnot
  have hs := singleSum L hres hchar
  rw [hreindex (fun xi => (Delta + xi) ^ q * quadraticFunction K W (b + xi))] at hs
  simp only [quadraticFunction] at hs
  rw [hsum] at hs
  have h := (lattice K (1 + P * D.t₂)).add_mem
    ((lattice K (1 + P * D.t₂)).add_mem hs (discarded_terms L)) (leading_term L hres)
  have hC : algebraMap B₂ K (Linear.transitionC D a w) = C := by
    simp only [Linear.transitionC, map_add, map_one, map_div₀,
      ← IsScalarTower.algebraMap_apply F B₂ K]
  rw [hC]
  convert h using 1
  ring

end Diamond


end

end LanglandsSecondMainLemma.Odd.Quadratic
