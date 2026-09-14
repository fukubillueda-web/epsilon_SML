import LanglandsSecondMainLemma.Odd.Linear.Cancellation

/-!
# The verified linear packet

Paper Theorem 9.7 (`O:W:final`), with the actual trace and norm witness
of `O:W:ledger`. Exact interpolation converts `O:W:Wsplit` into
`O:W:Wpre`; the term carrying the residue prime has the required depth.
The accepted cancellation then gives the packet, including `w^(p-2)`.
-/

namespace LanglandsSecondMainLemma.Odd.Linear

noncomputable section
open LanglandsFirstMainLemma
open scoped BigOperators

open private pow_mem_int_lattice from LanglandsSecondMainLemma.Odd.Total.TranslatedNorm
open private exists_primitive_root_prime_subfield from
  LanglandsSecondMainLemma.Odd.Total.CoefficientExtraction
open private ne_zero_of_order from LanglandsSecondMainLemma.Odd.Linear.Setup
open private split_div_mem from LanglandsSecondMainLemma.Odd.Linear.Split

/-- Reindex the actual representatives in the total field. FML's exact
product polynomial identifies the complete root set after embedding. -/
private theorem final_reindex
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F K] (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p)
    (hchar : residueCharacteristic F = p) (f : K → K) :
    (∑ j : ZMod p, f (algebraMap F K (primeTeichmuller F p hchar j : F))) =
      ∑ x ∈ Finite.teichmullerSet K p, f x := by
  classical
  let c (j : ZMod p) := algebraMap F K (primeTeichmuller F p hchar j : F)
  have hc : Function.Injective c :=
    (algebraMap F K).injective.comp (Subtype.coe_injective.comp
      ((teichmuller_injective F).comp
        (ZMod.castHom (by simp [hchar]) (ResidueField F)).injective))
  have hset : Finset.univ.image c = Finite.teichmullerSet K p := by
    ext x
    have hpoly := congrArg
      (Polynomial.eval₂RingHom ((algebraMap F K).comp
        (ValuativeRel.valuation F).integer.subtype) x)
      (primeTeichmullerPolynomial_sub F p hchar)
    simp only [map_prod, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub,
      Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_pow] at hpoly
    have hroot : (∃ j, c j = x) ↔ x ^ p - x = 0 := by
      rw [← hpoly, Finset.prod_eq_zero_iff]
      simp only [Finset.mem_univ, true_and, sub_eq_zero]
      exact exists_congr (fun _ => eq_comm)
    have hfactor : x ^ p - x = x * (x ^ (p - 1) - 1) := by
      rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p)]
    simpa only [Finset.mem_image, Finset.mem_univ, true_and, hfactor,
      mul_eq_zero, sub_eq_zero, Finite.teichmullerSet, Finset.mem_insert,
      Finite.teichmullerUnits, Polynomial.mem_nthRootsFinset (by omega : 0 < p - 1)]
      using hroot
  rw [← hset, Finset.sum_image hc.injOn]

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
/-- The first term in `O:W:Wpre` has depth at least
`v(p)-pt+i(M-t) ≥ 1+pt₂`, including when `v(p)=∞`. -/
private theorem final_prime_term (i : ℕ) (hi : 1 ≤ i) :
    let wK := algebraMap B₂ K (w : B₂)
    let W := algebraMap F K (transitionNorm D w)
    let b := algebraMap B₁ K (norm B₁ K Delta)
    let Y := algebraMap B₁ K (transitionY D Delta w)
    (p : K) * W * b * Delta ^ i / (wK ^ i * Y) ∈
      lattice K (1 + (p : ℤ) * D.t₂) := by
  let M : ℤ := (p : ℤ) * m
  have hW : ord K (algebraMap F K (transitionNorm D w)) =
      ((-(p : ℤ) * M : ℤ) : WithTop ℤ) := by
    convert L.W_order_K using 1; dsimp only [M]; congr 1; ring
  have hden : ord K (algebraMap B₂ K (w : B₂) ^ i *
      algebraMap B₁ K (transitionY D Delta w)) =
      ((-(i : ℤ) * M - (p : ℤ) * M : ℤ) : WithTop ℤ) := by
    rw [ord_mul, ord_pow, L.w_order_K, L.Y_order]
    simp only [← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul]
    congr 1
    dsimp only [M]
    ring
  have h := split_div_mem K
    (mul_mem_lattice K
      (mul_mem_lattice K (mul_mem_lattice K ((mem_lattice K).2 L.prime_order)
        ((mem_lattice K).2 hW.ge)) ((mem_lattice K).2 L.b_order_K.ge))
      (pow_mem_int_lattice K ((mem_lattice K).2 L.Delta_order.ge) i)) hden
  apply lattice_antitone K _ h
  have hpz : (3 : ℤ) ≤ p := by exact_mod_cast D.odd_prime
  have ht : (0 : ℤ) ≤ D.t := Int.natCast_nonneg _
  have hu : (D.t : ℤ) ≤ D.t₂ := by exact_mod_cast D.t_le_t₂
  have hM : (D.t : ℤ) + 1 ≤ M := L.transition
  have hiz : (1 : ℤ) ≤ i := by exact_mod_cast hi
  have hgap := mul_nonneg (by omega : (0 : ℤ) ≤ i - 1)
    (by omega : 0 ≤ M - D.t)
  have hdepth := mul_nonneg (by omega : (0 : ℤ) ≤ p)
    (by nlinarith : 0 ≤ ((p : ℤ) - 2) * D.t₂ - D.t)
  nlinarith

/-- Paper `O:W:Wpre`, before discarding its first term and applying the
four replacements. Both sums are evaluated exactly, with the exceptional
sum kept free of the rational denominator `Y+xi`. -/
private theorem final_pre
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (i : ℕ) (hi : 1 ≤ i) (hip : i ≤ p - 1) :
    let wK := algebraMap B₂ K (w : B₂)
    let W := algebraMap F K (transitionNorm D w)
    let Y := algebraMap B₁ K (transitionY D Delta w)
    let b := algebraMap B₁ K (norm B₁ K Delta)
    let s := algebraMap B₁ K (linearS D Delta)
    let d := algebraMap B₁ K (transitionD D Delta w)
    let c := ((p - 1 : ℕ) : K)
    algebraMap B₂ K (linearTrace D Delta w i) -
      ((p : K) * W * b * Delta ^ i / (wK ^ i * Y) +
        (if i = p - 1 then c * W / wK ^ (p - 1) else 0) -
        c * (W ^ 2 * (Delta - Y) ^ i / (wK ^ i * d)) -
        (if i = p - 2 then c * s / (wK ^ (p - 2) * (1 + b / W) ^ 2) else 0) -
        (if i = p - 1 then c * (i : K) * Delta * s /
          (wK ^ (p - 1) * (1 + b / W) ^ 2) else 0)) ∈
      lattice K (1 + (p : ℤ) * D.t₂) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let wK := algebraMap B₂ K (w : B₂)
  let W := algebraMap F K (transitionNorm D w)
  let b := algebraMap B₁ K (norm B₁ K Delta)
  let Y := W + b
  let s := algebraMap B₁ K (linearS D Delta)
  let c := ((p - 1 : ℕ) : K)
  have hYeq : algebraMap B₁ K (transitionY D Delta w) = Y := by
    simp only [transitionY, map_add, ← IsScalarTower.algebraMap_apply F B₁ K]; rfl
  have hd : algebraMap B₁ K (transitionD D Delta w) = Y ^ p - Y := by
    simp only [transitionD, map_sub, map_pow, hYeq]
  obtain ⟨zeta, hzeta, _⟩ := exists_primitive_root_prime_subfield F hp hchar
  have hz : IsPrimitiveRoot (algebraMap F K zeta) (p - 1) :=
    hzeta.map_of_injective (algebraMap F K).injective
  have hnot : -Y ∉ Finite.teichmullerSet K p := by
    simpa only [hYeq] using denominator_nonpole D L
  have hY0 : Y ≠ 0 := by
    rw [← hYeq]; exact ne_zero_of_order K L.Y_order
  have hsum : (∑ x ∈ Finite.teichmullerSet K p,
      (Delta + x) ^ i * (W * (b + x) / (Y + x))) =
      W * ((p : K) * Delta ^ i + if i = p - 1 then c else 0) -
        W ^ 2 * ((p : K) * Delta ^ i / Y +
          c * (Delta - Y) ^ i / (Y ^ p - Y)) := by
    rw [← Finite.teichmullerSet_shifted_power_sum D.odd_prime hz (by omega) Delta,
      ← Finite.interpolation hp D.odd_prime hz (by omega) Delta Y hnot,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hden : Y + x ≠ 0 := by
      intro heq
      apply hnot
      rw [show -Y = x by exact neg_eq_of_add_eq_zero_right heq]
      exact hx
    dsimp only [Y] at hden ⊢
    field_simp
    ring
  have hs := split D L hres hchar i hi hip
  dsimp only at hs
  have herase : (∑ j ∈ (Finset.univ : Finset (ZMod p)).erase 0,
      algebraMap F K (primeTeichmuller F p hchar j : F) *
        (Delta + algebraMap F K (primeTeichmuller F p hchar j : F)) ^ i) =
      ∑ j : ZMod p, algebraMap F K (primeTeichmuller F p hchar j : F) *
        (Delta + algebraMap F K (primeTeichmuller F p hchar j : F)) ^ i := by
    apply Finset.sum_erase
    simp
  rw [herase, final_reindex F K p D.odd_prime hchar
      (fun x => (Delta + x) ^ i * (W * (b + x) / (Y + x))),
    final_reindex F K p D.odd_prime hchar (fun x => x * (Delta + x) ^ i)] at hs
  change algebraMap B₂ K (linearTrace D Delta w i) -
    ((wK ^ i)⁻¹ * (∑ x ∈ Finite.teichmullerSet K p,
      (Delta + x) ^ i * (W * (b + x) / (Y + x))) -
      s / (wK ^ i * (1 + b / W) ^ 2) *
        (∑ x ∈ Finite.teichmullerSet K p, x * (Delta + x) ^ i)) ∈ _ at hs
  have hzero : (0 : K) ∉ Finite.teichmullerUnits K p := by
    simp [Finite.teichmullerUnits, Polynomial.mem_nthRootsFinset
      (by have := D.odd_prime; omega : 0 < p - 1),
      zero_pow (by have := D.odd_prime; omega : p - 1 ≠ 0)]
  rw [hsum, Finite.teichmullerSet, Finset.sum_insert hzero] at hs
  simp only [zero_mul, zero_add] at hs
  rw [Finite.teichmullerUnits_weighted_shifted_power_sum D.odd_prime hz hi
    (by omega) Delta] at hs
  simp only [hYeq, hd]
  dsimp only [Y, W, b] at hY0
  convert hs using 1
  split_ifs with hlast hex <;> try subst i
  all_goals try omega
  all_goals
    dsimp only [c, Y, wK, W, b, s]
    simp only [div_eq_mul_inv, mul_inv_rev]
    field_simp
    simp only [div_eq_mul_inv]
    ring

/-- The verified linear packet, Paper Theorem 9.7 (`O:W:final`).
The left side is the actual upper trace. All norms and embeddings retain
their fields; `s=-e_(p-1)` and `C=1+a/W`. The modulus is the integer
lattice `1+pt₂`. The setup has the proved constructor
`oddLinearData_construct`, and includes every odd prime and both field
characteristics. -/
theorem final
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (i : ℕ) (hi : 1 ≤ i) (hip : i ≤ p - 1) :
    let wK := algebraMap B₂ K (w : B₂)
    let W := algebraMap F K (transitionNorm D w)
    let s := algebraMap B₁ K (linearS D Delta)
    let A := algebraMap B₂ K a
    let C := algebraMap B₂ K (transitionC D a w)
    let c := ((p - 1 : ℕ) : K)
    algebraMap B₂ K (linearTrace D Delta w i) -
      (-(if i = p - 2 then c * s / (wK ^ (p - 2) * C ^ 2) else 0) +
        (if i = p - 1 then c * W / wK ^ (p - 1) else 0) -
        c * (W ^ 2 * (-A - W) ^ i / (wK ^ i * (W ^ p - W + A ^ p)))) ∈
      lattice K (1 + (p : ℤ) * D.t₂) := by
  have hpre := final_pre D L hres hchar i hi hip
  have hprime := final_prime_term D L i hi
  have hcancel := cancellation D L i hi hip
  dsimp only at hpre hprime hcancel ⊢
  simp only [transitionD₀, map_add, map_sub, map_pow,
    ← IsScalarTower.algebraMap_apply F B₂ K] at hcancel
  convert (lattice K _).add_mem ((lattice K _).add_mem hpre hprime) hcancel using 1
  ring

end Diamond
end

end LanglandsSecondMainLemma.Odd.Linear
