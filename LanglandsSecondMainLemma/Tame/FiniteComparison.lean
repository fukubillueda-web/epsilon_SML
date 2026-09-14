import LanglandsFirstMainLemma.Delta.Elementary
import LanglandsFirstMainLemma.Delta.LocalConstantRealization
import LanglandsFirstMainLemma.FiniteField.HasseDavenportLift
import LanglandsFirstMainLemma.FiniteField.HasseDavenportProduct
import LanglandsSecondMainLemma.Tame.DigitFactorials
import LanglandsSecondMainLemma.Gauss.LeadingTerm
import Mathlib.NumberTheory.Wilson
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Tame / Finite Comparison

Theorem 5.1 (`O:F:finite`) of `epsilon_SML.tex` and its supporting results.
The Hasse--Davenport calculation uses FML's actual complex-valued characters
and its minus-sign normalization. The residue argument takes place in the
coefficient ring constructed for Appendix A.

Proved here: (O:F:Lpower), including the Frobenius-orbit argument from
(O:F:finitecompatible); the full restriction identity and arbitrary additive
scaling in lines 906--912, with the scaling parameter constructed for any
two nontrivial additive characters; and injectivity of prime-to-characteristic
roots under residue reduction. The factorial congruence (O:F:factorials) is
transported to an actual coefficient-ring unit of residue one. The Wilson
step separating multiples of `p`, and the normalization
`-p = uniformizer^(p-1) * u` with residue `u = 1`, are also proved.
`padic_factorial_digits` iterates Wilson with its exact exponent identity.
`coefficient_factorial_blocks` regroups all base-`p` positions, and
`coefficient_groupedLeadingTerm` deduces (O:F:groupedStick) from
`Gauss.leadingTerm`, as an equality with a constructed residue-one unit.
Grouped factorials stay cross-multiplied because they need not be units.

`finiteCharacter_primitiveExponent` constructs the nonzero primitive
exponent relative to any generator character. All characters with the
same primitive norm compatibility are proved Frobenius conjugate.
`finiteComparison_primitiveRepresentative` consequently constructs the
exact numerator exponent for any compatibly realized generator pair,
proving its norm compatibility and its Gauss-sum equality. The complete
lower product is also proved independent of its generator.

`coefficient_extensionMap_exists` constructs the map from the lower
Appendix A ring to the upper one by Hensel lifting. It preserves residue
reduction, the uniformizer, and the primitive additive root.
`coefficient_extensionMap_teichmuller` proves preservation of the actual
Teichmuller sections. The complete lower sum and its grouped leading
congruence are transported by `coefficient_extensionMap_gaussSum` and
`coefficient_extensionMap_groupedLeadingTerm`, retaining the lower trace.
`coefficient_complexEmbedding_exists` constructs an injective complex
embedding of the algebraic-integer subring, and
`coefficient_complexGenerator` proves the realized Teichmuller character
has full order.

`coefficient_compatibleComplexRealization` assembles the maps into one
complex realization of the numerator and every lower sum, with the
generator restriction and trace compatibility proved.
`coefficient_primitiveComparison_unit` combines the transported grouped
congruences and factorial unit to prove the passage to `L ≡ 1` in
lines 898--902. Finally, `finiteComparison` uses `finiteComparison_pow`
and `coefficientRoot_eq_one` to establish the identity for every
nontrivial additive character, including the quadratic lower factor.
-/

open scoped BigOperators
open Finset LanglandsFirstMainLemma

namespace LanglandsSecondMainLemma.Tame

noncomputable section

section FiniteFields

variable {k K : Type*} [Field k] [Fintype k] [Field K] [Fintype K] [Algebra k K]

private def normCharacterHom : FiniteMulChar k →* FiniteMulChar K where
  toFun := normMulChar k K
  map_one' := by
    ext x
    simp [normMulChar_apply, MulChar.one_apply]
  map_mul' χ φ := by
    ext x
    simp [normMulChar_apply, MulChar.mul_apply]

omit [Fintype k] in
private theorem normCharacterHom_injective :
    Function.Injective (normCharacterHom (k := k) (K := K)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro χ hχ
  change normMulChar k K χ = 1 at hχ
  exact not_not.mp fun h ↦ (normMulChar_ne_one_iff k K χ).mpr h hχ

omit [Fintype k] in
private theorem normCharacter_pow (χ : FiniteMulChar k) (n : ℕ) :
    normMulChar k K (χ ^ n) = normMulChar k K χ ^ n :=
  (normCharacterHom (k := k) (K := K)).map_pow χ n

omit [Fintype k] in
private theorem normCharacter_order (χ : FiniteMulChar k) :
    orderOf (normMulChar k K χ) = orderOf χ :=
  orderOf_injective (normCharacterHom (k := k) (K := K))
    normCharacterHom_injective χ

/-- The product appearing in (O:F:finiteidentity), with every lower factor.
In degree two this retains the quadratic Gauss sum. -/
def finiteComparisonDenominator (ell : ℕ) (χ₀ μ : FiniteMulChar k)
    (ψ : FiniteAddChar k) : ℂ :=
  χ₀ (ell : k) * langlandsGaussSum χ₀ ψ *
    ∏ j ∈ Icc 1 (ell - 1), langlandsGaussSum (μ ^ j) ψ

private theorem degree_cast_ne_zero (ell : ℕ) (hdiv : ell ∣ Fintype.card k - 1) :
    (ell : k) ≠ 0 := by
  intro he
  have hc : ringChar k ∣ ell := (CharP.cast_eq_zero_iff k (ringChar k) ell).mp he
  letI : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
  have hq : ringChar k ∣ Fintype.card k :=
    (prime_dvd_char_iff_dvd_card (ringChar k)).mp (dvd_refl _)
  have hcop : Nat.Coprime (Fintype.card k - 1) (Fintype.card k) :=
    (Nat.coprime_self_sub_left Fintype.card_pos).mpr (Nat.coprime_one_left _)
  exact (CharP.prime_ringChar k).ne_one
    (Nat.eq_one_of_dvd_coprimes (hcop.of_dvd_left hdiv) hc hq)

/-- The quotient `L` in Theorem 5.1 has a nonzero denominator for every
nontrivial additive character, without any primitivity assumption. -/
theorem finiteComparisonDenominator_ne_zero (ell : ℕ)
    (hdiv : ell ∣ Fintype.card k - 1) (χ₀ μ : FiniteMulChar k)
    (ψ : FiniteAddChar k) (hψ : ψ ≠ 1) :
    finiteComparisonDenominator ell χ₀ μ ψ ≠ 0 := by
  unfold finiteComparisonDenominator
  exact mul_ne_zero
    (mul_ne_zero ((isUnit_iff_ne_zero.mpr (degree_cast_ne_zero ell hdiv)).map χ₀).ne_zero
      (langlandsGaussSum_ne_zero χ₀ hψ))
    (prod_ne_zero_iff.mpr fun j _ ↦ langlandsGaussSum_ne_zero (μ ^ j) hψ)

/-- The Hasse--Davenport part of (O:F:Lpower), before identifying the
twists with Frobenius conjugates. No equality of the twisted sums is assumed.
The only compatibility input is the paper's `χκ^ell = χ₀ ∘ Norm`.
This holds for arbitrary trace-compatible nontrivial additive characters. -/
theorem finiteComparison_twistProduct (ell : ℕ) (hell : 0 < ell)
    (hdegree : Module.finrank k K = ell)
    (χκ : FiniteMulChar K) (χ₀ μ : FiniteMulChar k)
    (hμ : orderOf μ = ell) (hcompat : χκ ^ ell = normMulChar k K χ₀)
    (ψ : FiniteAddChar k) (hψ : ψ ≠ 1) :
    langlandsGaussSum χκ (traceAddChar k K ψ) *
        (∏ j ∈ Icc 1 (ell - 1),
          langlandsGaussSum (χκ * normMulChar k K μ ^ j) (traceAddChar k K ψ)) =
      finiteComparisonDenominator ell χ₀ μ ψ ^ ell := by
  have hμK : orderOf (normMulChar k K μ) = ell :=
    (normCharacter_order μ).trans hμ
  have hdivK : ell ∣ Fintype.card K - 1 := by
    rw [← hμK]
    exact MulChar.orderOf_dvd_card_sub_one K (normMulChar k K μ)
  have hc : χκ ((ell : K) ^ ell) = χ₀ (ell : k) ^ ell := by
    rw [map_pow, ← MulChar.pow_apply' χκ hell.ne', hcompat, normMulChar_apply,
      show (ell : K) = algebraMap k K (ell : k) by simp,
      residueNorm_algebraMap, hdegree, map_pow]
  have h := hasseDavenportProduct ell hdivK (normMulChar k K μ) χκ hμK
    (traceAddChar k K ψ) ((traceAddChar_ne_one_iff k K ψ).mpr hψ)
  rw [hc, hcompat, hasseDavenportLift χ₀ ψ hψ, hdegree] at h
  have hfactor (j : ℕ) :
      langlandsGaussSum (normMulChar k K μ ^ j) (traceAddChar k K ψ) =
        langlandsGaussSum (μ ^ j) ψ ^ ell := by
    rw [← normCharacter_pow, hasseDavenportLift (μ ^ j) ψ hψ, hdegree]
  simp_rw [hfactor] at h
  rw [prod_pow] at h
  simpa only [finiteComparisonDenominator, mul_pow] using h.symm

/-- Frobenius invariance of the actual Gauss sum for a trace character.
The additive character of the base field may be arbitrary. -/
theorem finiteGaussSum_frobenius (χ : FiniteMulChar K) (ψ : FiniteAddChar k) :
    langlandsGaussSum (χ ^ Fintype.card k) (traceAddChar k K ψ) =
      langlandsGaussSum χ (traceAddChar k K ψ) := by
  classical
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k K
  have hσ (x : K) : σ x = x ^ Fintype.card k := rfl
  unfold langlandsGaussSum gaussSum
  congr 1
  calc
    _ = ∑ x : K, χ⁻¹ (σ x) * traceAddChar k K ψ (σ x) := by
      apply sum_congr rfl
      intro x _
      rw [traceAddChar_apply, traceAddChar_apply,
        Algebra.trace_eq_of_algEquiv σ, hσ, map_pow]
      simp [← inv_pow, MulChar.pow_apply' _ Fintype.card_pos.ne']
    _ = _ := Equiv.sum_comp σ.toEquiv
      (fun x : K ↦ χ⁻¹ x * traceAddChar k K ψ x)

private theorem finiteGaussSum_frobenius_iterate
    (χ : FiniteMulChar K) (ψ : FiniteAddChar k) (n : ℕ) :
    langlandsGaussSum (χ ^ (Fintype.card k ^ n)) (traceAddChar k K ψ) =
      langlandsGaussSum χ (traceAddChar k K ψ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_mul, finiteGaussSum_frobenius, ih]

private theorem character_root_param (ell : ℕ) (η α : FiniteMulChar k)
    (hη : orderOf η = ell) (hα : α ^ ell = 1) :
    ∃ i < ell, η ^ i = α := by
  classical
  letI : NeZero ell := ⟨hη ▸ (MulChar.orderOf_pos η).ne'⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := kˣ)
  have hr : IsPrimitiveRoot (η (g : k)) ell := by
    constructor
    · rw [← MulChar.pow_apply_coe, ← hη, pow_orderOf_eq_one]
      exact MulChar.one_apply_coe g
    · intro n hn
      rw [← hη, orderOf_dvd_iff_pow_eq_one, MulChar.eq_iff hg]
      simpa [MulChar.pow_apply_coe] using hn
  have ha : α (g : k) ^ ell = 1 := by
    rw [← MulChar.pow_apply_coe, hα]
    exact MulChar.one_apply_coe g
  obtain ⟨i, hi, he⟩ := hr.eq_pow_of_pow_eq_one ha
  refine ⟨i, hi, ?_⟩
  rw [MulChar.eq_iff hg]
  simpa [MulChar.pow_apply_coe] using he

/-- The exponent range and primitivity in the opening paragraph of the
proof of (O:F:finite). This applies to any generator character, including
one obtained from a compatible cyclotomic realization. -/
theorem finiteCharacter_primitiveExponent (ell : ℕ) (ω χ₀ : FiniteMulChar k)
    (hω : orderOf ω = Fintype.card k - 1)
    (hprim : ∃ u : kˣ, u ^ ell = 1 ∧ χ₀ (u : k) ≠ 1) :
    ∃ a : ℕ, 0 < a ∧ a < Fintype.card k - 1 ∧ ¬ ell ∣ a ∧ χ₀ = ω ^ a := by
  classical
  have hχ₀ : χ₀ ^ (Fintype.card k - 1) = 1 := by
    simpa [Fintype.card_units] using χ₀.pow_card_eq_one
  obtain ⟨a, ha, hpower⟩ := character_root_param _ ω χ₀ hω hχ₀
  have hnd : ¬ ell ∣ a := by
    rintro ⟨n, hn⟩
    obtain ⟨u, hu, hχu⟩ := hprim
    have huval : (u : k) ^ ell = 1 := by simpa using congrArg Units.val hu
    apply hχu
    rw [← hpower, MulChar.pow_apply_coe, hn, pow_mul, ← map_pow, huval,
      map_one, one_pow]
  exact ⟨a, Nat.pos_of_ne_zero (fun ha0 ↦ hnd (ha0 ▸ dvd_zero ell)),
    ha, hnd, hpower.symm⟩

/-- The primitivity condition in (O:F:finitecompatible) forces the
Frobenius quotient character to have order `ell`. -/
theorem frobeniusQuotient_order (ell : ℕ) (hell : ell.Prime)
    (hdiv : ell ∣ Fintype.card k - 1)
    (χκ : FiniteMulChar K) (χ₀ : FiniteMulChar k)
    (hcompat : χκ ^ ell = normMulChar k K χ₀)
    (hprim : ∃ u : kˣ, u ^ ell = 1 ∧ χ₀ (u : k) ≠ 1) :
    orderOf (χκ ^ (Fintype.card k - 1)) = ell := by
  classical
  letI : Fact ell.Prime := ⟨hell⟩
  apply orderOf_eq_prime
  · rw [← pow_mul, Nat.mul_comm, pow_mul, hcompat, ← normCharacter_pow]
    have hχ₀ : χ₀ ^ (Fintype.card k - 1) = 1 := by
      simpa [Fintype.card_units] using χ₀.pow_card_eq_one
    rw [hχ₀]
    exact (normCharacterHom (k := k) (K := K)).map_one
  · intro he
    obtain ⟨u, hu, hχu⟩ := hprim
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := kˣ)
    have hgorder : orderOf g = Fintype.card k - 1 := by
      simpa [Nat.card_eq_fintype_card, Fintype.card_units] using hg
    let h := (Fintype.card k - 1) / ell
    have hh : ell * h = Fintype.card k - 1 := Nat.mul_div_cancel' hdiv
    have hgroot : IsPrimitiveRoot ((g ^ h : kˣ) : k) ell := by
      rw [IsPrimitiveRoot.coe_units_iff, IsPrimitiveRoot.iff_orderOf]
      change orderOf (g ^ ((Fintype.card k - 1) / ell)) = ell
      rw [← hgorder]
      exact orderOf_pow_orderOf_div (orderOf_pos g).ne' (hgorder ▸ hdiv)
    have huval : (u : k) ^ ell = 1 := by
      simpa using congrArg Units.val hu
    obtain ⟨i, _, hi⟩ := hgroot.eq_pow_of_pow_eq_one huval
    obtain ⟨x, hx⟩ := FiniteField.unitsMap_norm_surjective k K g
    have hxval : residueNorm k K (x : K) = (g : k) := congrArg Units.val hx
    have hχg : χ₀ (g : k) = χκ (x : K) ^ ell := by
      rw [← MulChar.pow_apply_coe, hcompat, normMulChar_apply, hxval]
    have hχgh : χ₀ (g : k) ^ h = 1 := by
      rw [hχg, ← pow_mul, hh, ← MulChar.pow_apply_coe, he]
      exact MulChar.one_apply_coe x
    apply hχu
    rw [← hi, map_pow, Units.val_pow_eq_pow_val, map_pow, hχgh, one_pow]

omit [Fintype K] [Algebra k K] in
private theorem character_frobenius_iterate (ell : ℕ)
    (hdiv : ell ∣ Fintype.card k - 1) (χ : FiniteMulChar K)
    (hη : (χ ^ (Fintype.card k - 1)) ^ ell = 1) (n : ℕ) :
    χ ^ (Fintype.card k ^ n) = χ * (χ ^ (Fintype.card k - 1)) ^ n := by
  let η := χ ^ (Fintype.card k - 1)
  have hq : Fintype.card k = (Fintype.card k - 1) + 1 := by
    have : 0 < Fintype.card k := Fintype.card_pos
    omega
  have hχ : χ ^ Fintype.card k = χ * η := by
    rw [hq, pow_succ, mul_comm]
  have hηq : η ^ Fintype.card k = η := by
    obtain ⟨h, hh⟩ := hdiv
    rw [hq, hh, pow_succ, pow_mul]
    change (η ^ ell) ^ h * η = η
    rw [hη, one_pow, one_mul]
  change χ ^ (Fintype.card k ^ n) = χ * η ^ n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_mul, ih, mul_pow, hχ,
      show (η ^ n) ^ Fintype.card k = η ^ n by
        rw [← pow_mul, Nat.mul_comm, pow_mul, hηq], pow_succ]
    ac_rfl

/-- Every character satisfying the same primitive norm compatibility is
an actual Frobenius conjugate. In particular the representative used in
the digit calculation can replace the original numerator character. -/
theorem finiteComparison_frobenius_conjugate (ell : ℕ) (hell : ell.Prime)
    (hdiv : ell ∣ Fintype.card k - 1)
    (χκ χκ' : FiniteMulChar K) (χ₀ : FiniteMulChar k)
    (hcompat : χκ ^ ell = normMulChar k K χ₀)
    (hcompat' : χκ' ^ ell = normMulChar k K χ₀)
    (hprim : ∃ u : kˣ, u ^ ell = 1 ∧ χ₀ (u : k) ≠ 1) :
    ∃ i < ell, χκ' = χκ ^ (Fintype.card k ^ i) := by
  have horder := frobeniusQuotient_order ell hell hdiv χκ χ₀ hcompat hprim
  have hη : (χκ ^ (Fintype.card k - 1)) ^ ell = 1 := by
    rw [← horder, pow_orderOf_eq_one]
  have hquot : (χκ' / χκ) ^ ell = 1 := by
    rw [div_pow, hcompat', hcompat, div_self']
  obtain ⟨i, hi, he⟩ := character_root_param ell (χκ ^ (Fintype.card k - 1))
    (χκ' / χκ) horder hquot
  refine ⟨i, hi, ?_⟩
  rw [character_frobenius_iterate ell hdiv χκ hη i, he]
  simp

/-- Numerator independence within the primitive compatibility class,
with the trace character retained. -/
theorem finiteComparison_gaussSum_eq_of_compatible (ell : ℕ) (hell : ell.Prime)
    (hdiv : ell ∣ Fintype.card k - 1)
    (χκ χκ' : FiniteMulChar K) (χ₀ : FiniteMulChar k)
    (hcompat : χκ ^ ell = normMulChar k K χ₀)
    (hcompat' : χκ' ^ ell = normMulChar k K χ₀)
    (hprim : ∃ u : kˣ, u ^ ell = 1 ∧ χ₀ (u : k) ≠ 1)
    (ψ : FiniteAddChar k) :
    langlandsGaussSum χκ' (traceAddChar k K ψ) =
      langlandsGaussSum χκ (traceAddChar k K ψ) := by
  obtain ⟨i, _, hi⟩ := finiteComparison_frobenius_conjugate ell hell hdiv
    χκ χκ' χ₀ hcompat hcompat' hprim
  rw [hi, finiteGaussSum_frobenius_iterate]

/-- Once a generator character has been realized compatibly in both
fields, construct the exact exponent used by (O:F:digits). Its norm
compatibility and equality with the original numerator sum are proved
here, rather than imposed as extra conditions on the representative. -/
theorem finiteComparison_primitiveRepresentative (ell : ℕ) (hell : ell.Prime)
    (hdegree : Module.finrank k K = ell) (hdiv : ell ∣ Fintype.card k - 1)
    (χκ ωκ : FiniteMulChar K) (χ₀ ω₀ : FiniteMulChar k)
    (hω₀ : orderOf ω₀ = Fintype.card k - 1)
    (hrestrict : ∀ x : k, ω₀ x = ωκ (algebraMap k K x))
    (hcompat : χκ ^ ell = normMulChar k K χ₀)
    (hprim : ∃ u : kˣ, u ^ ell = 1 ∧ χ₀ (u : k) ≠ 1) :
    ∃ a : ℕ, 0 < a ∧ a < Fintype.card k - 1 ∧ ¬ ell ∣ a ∧ χ₀ = ω₀ ^ a ∧
      (ωκ ^ primitiveExponent (Fintype.card k) ell a) ^ ell = normMulChar k K χ₀ ∧
      ∀ ψ : FiniteAddChar k,
        langlandsGaussSum χκ (traceAddChar k K ψ) =
          langlandsGaussSum (ωκ ^ primitiveExponent (Fintype.card k) ell a)
            (traceAddChar k K ψ) := by
  obtain ⟨a, ha, haq, haprim, hχ₀⟩ :=
    finiteCharacter_primitiveExponent ell ω₀ χ₀ hω₀ hprim
  have hS : 0 < ∑ i ∈ range ell, Fintype.card k ^ i :=
    sum_pos' (fun _ _ ↦ Nat.zero_le _) ⟨0, mem_range.mpr hell.pos, by simp⟩
  have hnorm : normMulChar k K ω₀ = ωκ ^ (∑ i ∈ range ell, Fintype.card k ^ i) := by
    ext x
    rw [normMulChar_apply, hrestrict, algebraMap_residueNorm_eq_prod_frobenius,
      hdegree, map_prod]
    simp_rw [Nat.card_eq_fintype_card, map_pow]
    rw [prod_pow_eq_pow_sum, MulChar.pow_apply' _ hS.ne']
  obtain ⟨h, hh⟩ := hdiv
  have hq : Fintype.card k = ell * h + 1 := by
    have : 0 < Fintype.card k := Fintype.card_pos
    omega
  have he : (ωκ ^ primitiveExponent (Fintype.card k) ell a) ^ ell =
      normMulChar k K χ₀ := by
    rw [← pow_mul, Nat.mul_comm, hq, primitiveExponent_mul, ← hq,
      Nat.mul_comm, pow_mul, ← hnorm, ← normCharacter_pow, ← hχ₀]
  refine ⟨a, ha, haq, haprim, hχ₀, he, fun ψ ↦ ?_⟩
  exact (finiteComparison_gaussSum_eq_of_compatible ell hell
    (hh ▸ dvd_mul_right ell h) χκ _ χ₀ hcompat he hprim ψ).symm

/-- All lower factors are preserved when replacing the chosen order
`ell` character by another generator. This justifies using the powers of
the Teichmuller character in the factorial calculation, including the
single quadratic factor when `ell = 2`. -/
theorem finiteComparison_lowerProduct_independent (ell : ℕ) (hell : 0 < ell)
    (μ ν : FiniteMulChar k) (hμ : orderOf μ = ell) (hν : orderOf ν = ell)
    (ψ : FiniteAddChar k) (hψ : ψ ≠ 1) :
    (∏ j ∈ Icc 1 (ell - 1), langlandsGaussSum (μ ^ j) ψ) =
      ∏ j ∈ Icc 1 (ell - 1), langlandsGaussSum (ν ^ j) ψ := by
  classical
  have hmem (ω : FiniteMulChar k) (hω : orderOf ω = ell) (α : FiniteMulChar k) :
      α ∈ (range ell).image (ω ^ ·) ↔ α ^ ell = 1 := by
    constructor
    · intro hα
      obtain ⟨i, _, rfl⟩ := mem_image.mp hα
      rw [pow_right_comm, ← hω, pow_orderOf_eq_one, one_pow]
    · intro hα
      obtain ⟨i, hi, he⟩ := character_root_param ell ω α hω hα
      exact mem_image.mpr ⟨i, mem_range.mpr hi, he⟩
  have himages : (range ell).image (μ ^ ·) = (range ell).image (ν ^ ·) := by
    ext α
    rw [hmem μ hμ, hmem ν hν]
  have hprod (ω : FiniteMulChar k) (hω : orderOf ω = ell) :
      (∏ α ∈ (range ell).image (ω ^ ·), langlandsGaussSum α ψ) =
        ∏ j ∈ range ell, langlandsGaussSum (ω ^ j) ψ := by
    apply prod_image
    intro i hi j hj hij
    exact pow_injOn_Iio_orderOf
      (by simpa only [hω, Set.mem_Iio] using mem_range.mp hi)
      (by simpa only [hω, Set.mem_Iio] using mem_range.mp hj) hij
  have he : (∏ j ∈ range ell, langlandsGaussSum (μ ^ j) ψ) =
      ∏ j ∈ range ell, langlandsGaussSum (ν ^ j) ψ := by
    rw [← hprod μ hμ, ← hprod ν hν, himages]
  have hr : range ell = insert 0 (Icc 1 (ell - 1)) := by
    ext j
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  simpa only [hr, prod_insert (by simp : 0 ∉ Icc 1 (ell - 1)), pow_zero,
    langlandsGaussSum_trivial_mulChar hψ, one_mul] using he

/-- All the norm-character twists have the same sum, as asserted just
before (O:F:Lpower). Their Frobenius-conjugacy is deduced from the actual
nontrivial restriction of `χ₀` to the `ell`-th roots of unity. -/
theorem finiteComparison_twist_eq (ell : ℕ) (hell : ell.Prime)
    (hdiv : ell ∣ Fintype.card k - 1)
    (χκ : FiniteMulChar K) (χ₀ μ : FiniteMulChar k)
    (hμ : orderOf μ = ell) (hcompat : χκ ^ ell = normMulChar k K χ₀)
    (hprim : ∃ u : kˣ, u ^ ell = 1 ∧ χ₀ (u : k) ≠ 1)
    (ψ : FiniteAddChar k) (j : ℕ) :
    langlandsGaussSum (χκ * normMulChar k K μ ^ j) (traceAddChar k K ψ) =
      langlandsGaussSum χκ (traceAddChar k K ψ) := by
  have horder := frobeniusQuotient_order ell hell hdiv χκ χ₀ hcompat hprim
  have hη : (χκ ^ (Fintype.card k - 1)) ^ ell = 1 := by
    rw [← horder, pow_orderOf_eq_one]
  have hμK : normMulChar k K μ ^ ell = 1 := by
    rw [← hμ, ← normCharacter_order (K := K) μ, pow_orderOf_eq_one]
  obtain ⟨i, _, hi⟩ := character_root_param ell (χκ ^ (Fintype.card k - 1))
    (normMulChar k K μ) horder hμK
  rw [← hi, ← pow_mul, ← character_frobenius_iterate ell hdiv χκ hη (i * j)]
  exact finiteGaussSum_frobenius_iterate χκ ψ (i * j)

/-- Equation (O:F:Lpower), with all of (O:F:finitecompatible) retained
and the Frobenius-orbit assertion proved from those hypotheses. -/
theorem finiteComparison_pow (ell : ℕ) (hell : ell.Prime)
    (hdegree : Module.finrank k K = ell) (hdiv : ell ∣ Fintype.card k - 1)
    (χκ : FiniteMulChar K) (χ₀ μ : FiniteMulChar k)
    (hμ : orderOf μ = ell) (hcompat : χκ ^ ell = normMulChar k K χ₀)
    (hprim : ∃ u : kˣ, u ^ ell = 1 ∧ χ₀ (u : k) ≠ 1)
    (ψ : FiniteAddChar k) (hψ : ψ ≠ 1) :
    (langlandsGaussSum χκ (traceAddChar k K ψ) /
      finiteComparisonDenominator ell χ₀ μ ψ) ^ ell = 1 := by
  have hp := finiteComparison_twistProduct ell hell.pos hdegree χκ χ₀ μ hμ
    hcompat ψ hψ
  simp_rw [finiteComparison_twist_eq ell hell hdiv χκ χ₀ μ hμ hcompat hprim ψ] at hp
  rw [prod_const, Nat.card_Icc, show ell - 1 + 1 - 1 = ell - 1 by omega,
    ← pow_succ', Nat.sub_add_cancel hell.pos] at hp
  rw [div_pow, hp]
  exact div_self (pow_ne_zero _ (finiteComparisonDenominator_ne_zero ell hdiv χ₀ μ ψ hψ))

private theorem prod_range_powers {M : Type*} [CommMonoid M]
    (ell : ℕ) (hell : 0 < ell) (z : M) :
    (∏ j ∈ range ell, z ^ j) = ∏ j ∈ Icc 1 (ell - 1), z ^ j := by
  have hr : range ell = insert 0 (Icc 1 (ell - 1)) := by
    ext j
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hr, prod_insert (by simp), pow_zero, one_mul]

/-- The complete lower restriction factor: one for odd prime degree,
and the quadratic character itself in degree two. -/
theorem primeCharacterProduct {M : Type*} [CommMonoid M]
    (ell : ℕ) (hell : ell.Prime) (z : M) (hz : z ^ ell = 1) :
    (∏ j ∈ Icc 1 (ell - 1), z ^ j) = if ell = 2 then z else 1 := by
  classical
  by_cases htwo : ell = 2
  · subst ell
    simp
  · rw [if_neg htwo, ← prod_range_powers ell hell.pos, prod_pow_eq_pow_sum]
    have hd : ell ∣ ∑ i ∈ range ell, i := by
      have hd2 : ell ∣ (∑ i ∈ range ell, i) * 2 := by
        rw [sum_range_id_mul_two]
        exact dvd_mul_right _ _
      rcases hell.dvd_mul.mp hd2 with hs | hs
      · exact hs
      · exact (htwo ((Nat.dvd_prime Nat.prime_two).mp hs |>.resolve_left hell.ne_one)).elim
    obtain ⟨n, hn⟩ := hd
    rw [hn, pow_mul, hz, one_pow]

/-- The restriction identity needed for arbitrary additive scaling in the
last paragraph of Theorem 5.1. The entire lower product is present, including
the quadratic factor. -/
theorem finiteComparison_restriction (ell : ℕ) (hell : ell.Prime)
    (hdegree : Module.finrank k K = ell) (hdiv : ell ∣ Fintype.card k - 1)
    (χκ : FiniteMulChar K) (χ₀ μ : FiniteMulChar k)
    (hμ : orderOf μ = ell) (hcompat : χκ ^ ell = normMulChar k K χ₀)
    (hprim : ∃ u : kˣ, u ^ ell = 1 ∧ χ₀ (u : k) ≠ 1) (c : kˣ) :
    χκ (algebraMap k K (c : k)) =
      χ₀ (c : k) * ∏ j ∈ Icc 1 (ell - 1), (μ ^ j) (c : k) := by
  classical
  let η := χκ ^ (Fintype.card k - 1)
  have hηorder : orderOf η = ell :=
    frobeniusQuotient_order ell hell hdiv χκ χ₀ hcompat hprim
  have hη : η ^ ell = 1 := by rw [← hηorder, pow_orderOf_eq_one]
  have hμKorder : orderOf (normMulChar k K μ) = ell := (normCharacter_order μ).trans hμ
  have hμK : normMulChar k K μ ^ ell = 1 := by rw [← hμKorder, pow_orderOf_eq_one]
  have hprods : (∏ j ∈ range ell, η ^ j) =
      ∏ j ∈ Icc 1 (ell - 1), normMulChar k K μ ^ j := by
    rw [prod_range_powers ell hell.pos, primeCharacterProduct ell hell η hη,
      primeCharacterProduct ell hell _ hμK]
    split_ifs with htwo
    · obtain ⟨i, hi, hei⟩ := character_root_param ell η (normMulChar k K μ) hηorder hμK
      have hi0 : i ≠ 0 := by
        intro hzero
        rw [hzero, pow_zero] at hei
        have : orderOf (normMulChar k K μ) = 1 := by rw [← hei, orderOf_one]
        omega
      have : i = 1 := by omega
      simpa [this] using hei
    · rfl
  obtain ⟨x, hx⟩ := FiniteField.unitsMap_norm_surjective k K c
  have hxval : residueNorm k K (x : K) = (c : k) := congrArg Units.val hx
  have hχx : χκ (x : K) ^ ell = χ₀ (c : k) := by
    rw [← MulChar.pow_apply_coe, hcompat, normMulChar_apply, hxval]
  have hterm (j : ℕ) : χκ ((x : K) ^ (Nat.card k ^ j)) =
      χκ (x : K) * η (x : K) ^ j := by
    rw [map_pow, Nat.card_eq_fintype_card, ← MulChar.pow_apply_coe,
      character_frobenius_iterate ell hdiv χκ hη j, MulChar.mul_apply,
      MulChar.pow_apply_coe]
  have heval : (∏ j ∈ range ell, η (x : K) ^ j) =
      ∏ j ∈ Icc 1 (ell - 1), (μ ^ j) (c : k) := by
    let ev : FiniteMulChar K →* ℂ := {
      toFun := fun α ↦ α (x : K)
      map_one' := MulChar.one_apply_coe x
      map_mul' := fun α β ↦ MulChar.mul_apply α β (x : K) }
    have he := congrArg ev hprods
    simp only [map_prod, map_pow] at he
    change (∏ j ∈ range ell, η (x : K) ^ j) =
      ∏ j ∈ Icc 1 (ell - 1), normMulChar k K μ (x : K) ^ j at he
    simpa [← MulChar.pow_apply_coe, ← normCharacter_pow, normMulChar_apply, hxval]
      using he
  rw [← hxval, algebraMap_residueNorm_eq_prod_frobenius, hdegree, map_prod]
  simp_rw [hterm]
  rw [prod_mul_distrib, prod_const, card_range, hχx, heval, hxval]

omit [Fintype k] [Fintype K] in
private theorem traceAddChar_mulShift (ψ : FiniteAddChar k) (c : kˣ) :
    traceAddChar k K (ψ.mulShift (c : k)) =
      (traceAddChar k K ψ).mulShift (algebraMap k K (c : k)) := by
  ext x
  simp only [traceAddChar_apply, AddChar.mulShift_apply]
  congr 1
  simpa [Algebra.smul_def] using
    ((Algebra.trace k K).map_smul (c : k) x).symm

/-- The quotient `L` is unchanged by every nonzero additive scaling. The
restriction factor is proved above from the original primitive input data. -/
theorem finiteComparison_ratio_mulShift (ell : ℕ) (hell : ell.Prime)
    (hdegree : Module.finrank k K = ell) (hdiv : ell ∣ Fintype.card k - 1)
    (χκ : FiniteMulChar K) (χ₀ μ : FiniteMulChar k)
    (hμ : orderOf μ = ell) (hcompat : χκ ^ ell = normMulChar k K χ₀)
    (hprim : ∃ u : kˣ, u ^ ell = 1 ∧ χ₀ (u : k) ≠ 1)
    (ψ : FiniteAddChar k) (c : kˣ) :
    langlandsGaussSum χκ (traceAddChar k K (ψ.mulShift (c : k))) /
        finiteComparisonDenominator ell χ₀ μ (ψ.mulShift (c : k)) =
      langlandsGaussSum χκ (traceAddChar k K ψ) /
        finiteComparisonDenominator ell χ₀ μ ψ := by
  have hscale := finiteComparison_restriction ell hell hdegree hdiv χκ χ₀ μ hμ
    hcompat hprim c
  let cK := Units.map (algebraMap k K).toMonoidHom c
  have hc : χκ (cK : K) ≠ 0 := (cK.isUnit.map χκ).ne_zero
  rw [traceAddChar_mulShift]
  change langlandsGaussSum χκ ((traceAddChar k K ψ).mulShift (cK : K)) / _ = _
  rw [langlandsGaussSum_mulShift_unit χκ _ cK]
  have hd : finiteComparisonDenominator ell χ₀ μ (ψ.mulShift (c : k)) =
      χκ (cK : K) * finiteComparisonDenominator ell χ₀ μ ψ := by
    unfold finiteComparisonDenominator
    simp_rw [langlandsGaussSum_mulShift_unit _ _ c]
    rw [prod_mul_distrib]
    change _ = χκ (algebraMap k K (c : k)) * _
    rw [hscale]
    ring
  rw [hd, mul_div_mul_left _ _ hc]

/-- The last paragraph of Theorem 5.1 for any two nontrivial additive
characters. Their nonzero scaling parameter is constructed from the
perfect character pairing, in every residue characteristic. -/
theorem finiteComparison_ratio_independent (ell : ℕ) (hell : ell.Prime)
    (hdegree : Module.finrank k K = ell) (hdiv : ell ∣ Fintype.card k - 1)
    (χκ : FiniteMulChar K) (χ₀ μ : FiniteMulChar k)
    (hμ : orderOf μ = ell) (hcompat : χκ ^ ell = normMulChar k K χ₀)
    (hprim : ∃ u : kˣ, u ^ ell = 1 ∧ χ₀ (u : k) ≠ 1)
    (ψ₁ ψ₂ : FiniteAddChar k) (hψ₁ : ψ₁ ≠ 1) (hψ₂ : ψ₂ ≠ 1) :
    langlandsGaussSum χκ (traceAddChar k K ψ₂) /
        finiteComparisonDenominator ell χ₀ μ ψ₂ =
      langlandsGaussSum χκ (traceAddChar k K ψ₁) /
        finiteComparisonDenominator ell χ₀ μ ψ₁ := by
  classical
  have hbij : Function.Bijective ψ₁.mulShift := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨AddChar.to_mulShift_inj_of_isPrimitive
      (AddChar.IsPrimitive.of_ne_one hψ₁), AddChar.card_eq.symm⟩
  obtain ⟨c, hc⟩ := hbij.surjective ψ₂
  have hc0 : c ≠ 0 := by
    intro hzero
    apply hψ₂
    rw [← hc, hzero, AddChar.mulShift_zero]
  rw [← hc]
  exact finiteComparison_ratio_mulShift ell hell hdegree hdiv χκ χ₀ μ hμ
    hcompat hprim ψ₁ (Units.mk0 c hc0)

end FiniteFields

/-- One Wilson step in the grouping argument before (O:F:groupedStick).
The multiples of `p` are retained in the displayed power and factorial;
only the remaining factors form the unit. -/
theorem padic_factorial_split (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∃ u : ℤ_[p], IsUnit u ∧
      (n.factorial : ℤ_[p]) = (p : ℤ_[p]) ^ (n / p) * (n / p).factorial * u ∧
      PadicInt.toZMod u = (-1 : ZMod p) ^ (n / p) * (n % p).factorial := by
  induction n with
  | zero => exact ⟨1, isUnit_one, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨u, hu, hfac, hred⟩ := ih
    by_cases hd : p ∣ n + 1
    · have hs : (n + 1) / p = n / p + 1 := Nat.succ_div_of_dvd hd
      have hn : n + 1 = p * (n / p + 1) := by
        rw [← hs, Nat.mul_div_cancel' hd]
      have hr : n % p = p - 1 := by
        have he := Nat.div_add_mod n p
        rw [Nat.mul_add, Nat.mul_one] at hn
        omega
      refine ⟨u, hu, ?_, ?_⟩
      · rw [Nat.factorial_succ, Nat.cast_mul, hfac, hs, Nat.factorial_succ,
          Nat.cast_mul, pow_succ]
        have hn' : ((n + 1 : ℕ) : ℤ_[p]) = (p : ℤ_[p]) * ((n / p : ℕ) + 1) := by
          exact_mod_cast hn
        rw [hn']
        push_cast
        ring
      · rw [hred, hr, Nat.mod_eq_zero_of_dvd hd, hs, Nat.factorial_zero,
          Nat.cast_one, mul_one, ZMod.wilsons_lemma, pow_succ]
    · have hs : (n + 1) / p = n / p := Nat.succ_div_of_not_dvd hd
      have hr : (n + 1) % p = n % p + 1 := by
        have he := Nat.div_add_mod n p
        have he' := Nat.div_add_mod (n + 1) p
        rw [hs] at he'
        omega
      have hnu : IsUnit (n + 1 : ℤ_[p]) := by
        apply PadicInt.isUnit_iff.mpr
        simpa only [Nat.cast_add, Nat.cast_one] using
          (PadicInt.norm_natCast_eq_one_iff (p := p) (n := n + 1)).mpr
            ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hd)
      refine ⟨(n + 1) * u, hnu.mul hu, ?_, ?_⟩
      · rw [Nat.factorial_succ, Nat.cast_mul, hfac, hs]
        push_cast
        ring
      · rw [map_mul, map_add, map_natCast, map_one, hred, hs, hr,
          Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        rw [ZMod.natCast_mod]
        ring

private theorem padic_factorial_split_principal (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∃ u : ℤ_[p], IsUnit u ∧ PadicInt.toZMod u = 1 ∧
      (n.factorial : ℤ_[p]) = (-(p : ℤ_[p])) ^ (n / p) *
        (n / p).factorial * (n % p).factorial * u := by
  obtain ⟨w, hw, hn, hwred⟩ := padic_factorial_split p n
  let d : ℤ_[p] := (n % p).factorial
  have hd : IsUnit d := PadicInt.isUnit_iff.mpr
    ((PadicInt.norm_natCast_eq_one_iff (p := p)).mpr
      ((Fact.out : p.Prime).coprime_factorial_of_lt
        (Nat.mod_lt n (Fact.out : p.Prime).pos)))
  have hsign : (-1 : ℤ_[p]) ^ (n / p) * (-1) ^ (n / p) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  let u := (-1 : ℤ_[p]) ^ (n / p) * w * Ring.inverse d
  have he : d * u = (-1 : ℤ_[p]) ^ (n / p) * w := by
    dsimp [u]
    calc
      _ = ((-1 : ℤ_[p]) ^ (n / p) * w) * (d * Ring.inverse d) := by ring
      _ = _ := by rw [Ring.mul_inverse_cancel d hd, mul_one]
  have hured : PadicInt.toZMod u = 1 := by
    have h := congrArg PadicInt.toZMod he
    simp only [map_mul, map_pow, map_neg, map_one, hwred] at h
    have hs : (-1 : ZMod p) ^ (n / p) * (-1) ^ (n / p) = 1 := by
      simpa only [map_mul, map_pow, map_neg, map_one] using
        congrArg PadicInt.toZMod hsign
    have hright : (-1 : ZMod p) ^ (n / p) *
        ((-1) ^ (n / p) * ((n % p).factorial : ZMod p)) =
          PadicInt.toZMod d := by
      rw [← mul_assoc, hs, one_mul]
      exact (map_natCast PadicInt.toZMod _).symm
    rw [hright] at h
    exact (mul_eq_left₀ (hd.map PadicInt.toZMod).ne_zero).mp h
  refine ⟨u, ((isUnit_neg_one.pow _).mul hw).mul hd.ringInverse,
    hured, ?_⟩
  rw [hn, mul_assoc _ _ u]
  rw [he, neg_eq_neg_one_mul, mul_pow]
  calc
    _ = (p : ℤ_[p]) ^ (n / p) * (n / p).factorial * w := rfl
    _ = ((-1 : ℤ_[p]) ^ (n / p) * (-1) ^ (n / p)) *
        ((p : ℤ_[p]) ^ (n / p) * (n / p).factorial * w) := by rw [hsign, one_mul]
    _ = _ := by ring

private theorem gaussDigits_succ (p f a : ℕ) :
    Gauss.gaussDigitSum p (f + 1) a =
        a % p + Gauss.gaussDigitSum p f (a / p) ∧
      Gauss.gaussDigitFactorial p (f + 1) a =
        (a % p).factorial * Gauss.gaussDigitFactorial p f (a / p) := by
  simp [Gauss.gaussDigitSum, Gauss.gaussDigitFactorial,
    sum_range_succ', prod_range_succ', Gauss.basePDigit, pow_succ,
    Nat.div_div_eq_div_mul, Nat.mul_comm, add_comm]

/-- The iterated Wilson congruence preceding (O:F:groupedStick).
The exponent is accompanied by its exact digit-sum identity, so no
subtraction discards valuation information. -/
theorem padic_factorial_digits (p : ℕ) [Fact p.Prime] (f n : ℕ) (hn : n < p ^ f) :
    ∃ e : ℕ, ∃ u : ℤ_[p], IsUnit u ∧ PadicInt.toZMod u = 1 ∧
      n = (p - 1) * e + Gauss.gaussDigitSum p f n ∧
      (n.factorial : ℤ_[p]) = (-(p : ℤ_[p])) ^ e *
        (Gauss.gaussDigitFactorial p f n : ℤ_[p]) * u := by
  induction f generalizing n with
  | zero =>
    have hn0 : n = 0 := by simpa using hn
    subst n
    exact ⟨0, 1, isUnit_one, by simp,
      by simp [Gauss.gaussDigitSum], by simp [Gauss.gaussDigitFactorial]⟩
  | succ f ih =>
    have hdiv : n / p < p ^ f := by
      rw [Nat.div_lt_iff_lt_mul (Fact.out : p.Prime).pos]
      simpa only [pow_succ] using hn
    obtain ⟨e, u, hu, hured, hsum, hfac⟩ := ih (n / p) hdiv
    obtain ⟨v, hv, hvred, hvfac⟩ := padic_factorial_split_principal p n
    refine ⟨n / p + e, u * v, hu.mul hv, by simp [hured, hvred], ?_, ?_⟩
    · rw [(gaussDigits_succ p f n).1]
      have hsplit := Nat.div_add_mod n p
      have hp : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).pos
      calc
        n = p * (n / p) + n % p := hsplit.symm
        _ = ((p - 1) + 1) * (n / p) + n % p := by rw [hp]
        _ = (p - 1) * (n / p) + (n / p) + n % p := by ring
        _ = _ := by rw [Nat.mul_add]; omega
    · rw [hvfac, hfac, (gaussDigits_succ p f n).2, Nat.cast_mul, pow_add]
      ring

private theorem natRatio_principalUnit (p : ℕ) [Fact p.Prime]
    {R r : Type*} [CommRing R] [CommRing r] [CharP r p]
    (ι : ℤ_[p] →+* R) (φ : R →+* r) (A B : ℕ) (hB : B ≠ 0)
    (h : ‖(A : ℚ_[p]) / (B : ℚ_[p]) - 1‖ < 1) :
    ∃ u : R, IsUnit u ∧ φ u = 1 ∧ (A : R) = u * (B : R) := by
  have hvnorm : ‖(A : ℚ_[p]) / (B : ℚ_[p])‖ = 1 := by
    simpa using Padic.norm_eq_of_norm_sub_lt_right
      (z1 := (A : ℚ_[p]) / (B : ℚ_[p])) (z2 := 1) (by simpa using h)
  let v : ℤ_[p] := ⟨(A : ℚ_[p]) / (B : ℚ_[p]), hvnorm.le⟩
  have hvunit : IsUnit v := PadicInt.isUnit_iff.mpr hvnorm
  have hvred : φ (ι v) = 1 := by
    have hvsmall : ‖v - 1‖ < 1 := h
    obtain ⟨t, ht⟩ := (PadicInt.norm_lt_one_iff_dvd (v - 1)).mp hvsmall
    have he := congrArg (φ.comp ι) ht
    simp only [map_sub, map_one, map_mul, map_natCast,
      CharP.cast_eq_zero r p, zero_mul] at he
    exact sub_eq_zero.mp he
  have he : (A : ℤ_[p]) = v * (B : ℤ_[p]) := by
    apply Subtype.ext
    change (A : ℚ_[p]) = (A : ℚ_[p]) / (B : ℚ_[p]) * (B : ℚ_[p])
    exact (div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hB)).symm
  refine ⟨ι v, hvunit.map ι, hvred, ?_⟩
  simpa only [map_natCast, map_mul] using congrArg ι he

/-- Equation (O:F:factorials) in the actual Appendix A coefficient ring.
The unit and its residue are constructed from the proved `p`-adic bound.
The factorials themselves may be divisible by `p`; the equality is kept
cross-multiplied and never treats these factorials as units. -/
theorem coefficient_primitiveExponent_factorialUnit (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    (C : Gauss.GaussCoefficientField p k) (f ell h a : ℕ)
    (hell : ell.Prime) (hq : ell * h + 1 = p ^ f)
    (ha : a < p ^ f) (hprim : ¬ ell ∣ a) :
    ∃ u : C.IntegerRing, IsUnit u ∧
      Gauss.cyclotomicResidueMap p k C.unramified u = 1 ∧
      (ell : C.IntegerRing) ^ a *
          (Gauss.gaussDigitFactorial (p ^ f) ell
            (primitiveExponent (p ^ f) ell a) : C.IntegerRing) =
        u * ((a.factorial : C.IntegerRing) *
          ∏ j ∈ range ell, ((j * h).factorial : C.IntegerRing)) := by
  classical
  letI : CharP k p := charP_of_injective_algebraMap
    (RingHom.injective (algebraMap (ZMod p) k)) p
  let ι : ℤ_[p] →+* C.IntegerRing :=
    (AdjoinRoot.of (Gauss.cyclotomicUniformizerPolynomial p k C.unramified)).comp
      (AdjoinRoot.of C.unramified.polynomial)
  have hB : a.factorial * (∏ j ∈ range ell, (j * h).factorial) ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero _) (prod_ne_zero_iff.mpr fun j _ ↦
      Nat.factorial_ne_zero _)
  have hunit := natRatio_principalUnit p ι
    (Gauss.cyclotomicResidueMap p k C.unramified)
    (ell ^ a * Gauss.gaussDigitFactorial (p ^ f) ell (primitiveExponent (p ^ f) ell a))
    (a.factorial * (∏ j ∈ range ell, (j * h).factorial)) hB
    (by simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_prod] using
      primitiveExponent_factorialUnit_digits p f ell h a hell hq ha hprim)
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_prod] using hunit

/-- The uniformizer normalization used in (O:F:groupedStick), including
`p = 2`: `-p` is `pi^(p-1)` times an actual unit with residue one.
The unit is constructed from the geometric sums of the primitive root;
Wilson's theorem computes its residue. -/
theorem coefficient_prime_uniformizerUnit (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    (C : Gauss.GaussCoefficientField p k) :
    ∃ u : C.IntegerRing, IsUnit u ∧
      Gauss.cyclotomicResidueMap p k C.unramified u = 1 ∧
      -(p : C.IntegerRing) = C.uniformizer ^ (p - 1) * u := by
  classical
  letI : IsDomain C.IntegerRing := C.coefficientDomain
  letI : IsLocalRing C.IntegerRing := C.coefficientLocalRing
  letI : CharP k p := charP_of_injective_algebraMap
    (RingHom.injective (algebraMap (ZMod p) k)) p
  let φ := Gauss.cyclotomicResidueMap p k C.unramified
  have hp : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).pos
  have hpi : φ C.uniformizer = 0 := by
    unfold φ Gauss.cyclotomicResidueMap Gauss.GaussCoefficientField.uniformizer
    apply AdjoinRoot.lift_root
  have hz : C.zeta - 1 = C.uniformizer := by
    simp [Gauss.GaussCoefficientField.zeta, Gauss.cyclotomicZeta,
      Gauss.GaussCoefficientField.uniformizer]
  have hzred : φ C.zeta = 1 := by
    have he := congrArg φ hz
    exact sub_eq_zero.mp (by simpa [hpi] using he)
  let v : C.IntegerRing := ∏ i ∈ range (p - 1), ∑ j ∈ range (i + 1), C.zeta ^ j
  have hvred : φ v = -1 := by
    have hfac : ((p - 1).factorial : k) = -1 := by
      simpa only [map_natCast, map_neg, map_one] using
        congrArg (algebraMap (ZMod p) k) (ZMod.wilsons_lemma p)
    simpa [v, hzred, ← Nat.cast_prod, ← Nat.cast_add,
      prod_range_add_one_eq_factorial] using hfac
  have hsign : (-1 : k) ^ (p - 1) = 1 := by
    have he := neg_one_pow_char k p
    rw [← hp, pow_succ, mul_neg_one, neg_inj] at he
    exact he
  let u : C.IntegerRing := -((-1) ^ (p - 1) * v)
  have hured : φ u = 1 := by simp [u, hvred, hsign]
  have hu : IsUnit u := by
    rw [← IsLocalRing.notMem_maximalIdeal,
      ← IsLocalRing.ker_eq_maximalIdeal φ (fun x ↦
        ⟨Gauss.teichmuller_lift p k C x, Gauss.teichmuller_lift_reduction p k C x⟩),
      RingHom.mem_ker, hured]
    exact one_ne_zero
  have hroot : IsPrimitiveRoot C.zeta (p - 1 + 1) := by
    simpa only [hp, Gauss.GaussCoefficientField.zeta] using C.zetaPrimitive
  have hprod := hroot.prod_pow_sub_one_eq_order
  have hterm (i : ℕ) : C.zeta ^ (i + 1) - 1 =
      C.uniformizer * ∑ j ∈ range (i + 1), C.zeta ^ j := by
    rw [← geom_sum_mul, hz, mul_comm]
  simp_rw [hterm] at hprod
  rw [prod_mul_distrib, prod_const, card_range] at hprod
  have hcast : (p - 1 : ℕ) + (1 : C.IntegerRing) = p := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (Nat.cast : ℕ → C.IntegerRing) hp
  rw [hcast] at hprod
  refine ⟨u, hu, hured, ?_⟩
  change -(p : C.IntegerRing) = C.uniformizer ^ (p - 1) * -((-1) ^ (p - 1) * v)
  linear_combination hprod

private theorem map_padic_residue_one (p : ℕ) [Fact p.Prime]
    {R r : Type*} [CommRing R] [CommRing r] [CharP r p]
    (ι : ℤ_[p] →+* R) (φ : R →+* r) {u : ℤ_[p]}
    (hu : PadicInt.toZMod u = 1) : φ (ι u) = 1 := by
  have hm : u - 1 ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    simp only [RingHom.mem_ker, map_sub, map_one, hu, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton] at hm
  obtain ⟨b, hb⟩ := hm
  have he := congrArg (φ.comp ι) hb
  simp only [map_sub, map_one, map_mul, map_natCast,
    CharP.cast_eq_zero r p, zero_mul] at he
  exact sub_eq_zero.mp he

/-- Wilson's full digit factorization in the Appendix A ring. This
cross-multiplied form remains valid when `n!` is divisible by `p`. -/
theorem coefficient_factorial_digits (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    (C : Gauss.GaussCoefficientField p k) (f n : ℕ) (hn : n < p ^ f) :
    ∃ u : C.IntegerRing, IsUnit u ∧
      Gauss.cyclotomicResidueMap p k C.unramified u = 1 ∧
      (n.factorial : C.IntegerRing) * C.uniformizer ^ Gauss.gaussDigitSum p f n =
        C.uniformizer ^ n * (Gauss.gaussDigitFactorial p f n : C.IntegerRing) * u := by
  letI : CharP k p := charP_of_injective_algebraMap
    (RingHom.injective (algebraMap (ZMod p) k)) p
  let ι : ℤ_[p] →+* C.IntegerRing :=
    (AdjoinRoot.of (Gauss.cyclotomicUniformizerPolynomial p k C.unramified)).comp
      (AdjoinRoot.of C.unramified.polynomial)
  obtain ⟨e, v, hv, hvred, hsum, hfac⟩ := padic_factorial_digits p f n hn
  obtain ⟨w, hw, hwred, hprime⟩ := coefficient_prime_uniformizerUnit p k C
  refine ⟨w ^ e * ι v, (hw.pow e).mul (hv.map ι), ?_, ?_⟩
  · rw [map_mul, map_pow, hwred, one_pow, one_mul]
    exact map_padic_residue_one p ι _ hvred
  · have hfac' := congrArg ι hfac
    simp only [map_mul, map_pow, map_neg, map_natCast] at hfac'
    have hpow : C.uniformizer ^ n = C.uniformizer ^ ((p - 1) * e) *
        C.uniformizer ^ Gauss.gaussDigitSum p f n := by
      rw [← pow_add, ← hsum]
    rw [hfac', hprime, mul_pow, ← pow_mul, hpow]
    ring

private theorem basePDigit_block (p f a i j : ℕ) (hj : j < f) :
    Gauss.basePDigit p (Gauss.basePDigit (p ^ f) a i) j =
      Gauss.basePDigit p a (f * i + j) := by
  have hf : p ^ f = p ^ j * p ^ (f - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hj.le]
  unfold Gauss.basePDigit
  rw [hf, Nat.mod_mul_right_div_self]
  rw [Nat.mod_mod_of_dvd _ (dvd_pow_self p (by omega : f - j ≠ 0))]
  rw [Nat.div_div_eq_div_mul, ← hf, ← pow_mul, ← pow_add]

private theorem gaussDigits_blocks (p f r a : ℕ) :
    Gauss.gaussDigitSum p (f * r) a =
        ∑ i ∈ range r, Gauss.gaussDigitSum p f (Gauss.basePDigit (p ^ f) a i) ∧
      Gauss.gaussDigitFactorial p (f * r) a =
        ∏ i ∈ range r,
          Gauss.gaussDigitFactorial p f (Gauss.basePDigit (p ^ f) a i) := by
  have hs (i : ℕ) :
      (∑ j ∈ range f, Gauss.basePDigit p a (f * i + j)) =
        Gauss.gaussDigitSum p f (Gauss.basePDigit (p ^ f) a i) :=
    sum_congr rfl fun j hj ↦ (basePDigit_block p f a i j (mem_range.mp hj)).symm
  have hp (i : ℕ) :
      (∏ j ∈ range f, (Gauss.basePDigit p a (f * i + j)).factorial) =
        Gauss.gaussDigitFactorial p f (Gauss.basePDigit (p ^ f) a i) :=
    prod_congr rfl fun j hj ↦ congrArg Nat.factorial
      (basePDigit_block p f a i j (mem_range.mp hj)).symm
  induction r with
  | zero => simp [Gauss.gaussDigitSum, Gauss.gaussDigitFactorial]
  | succ r ih =>
    constructor
    · change (∑ j ∈ range (f * (r + 1)), Gauss.basePDigit p a j) = _
      rw [Nat.mul_succ, sum_range_add, hs]
      change Gauss.gaussDigitSum p (f * r) a + _ = _
      rw [ih.1, sum_range_succ]
    · change (∏ j ∈ range (f * (r + 1)), (Gauss.basePDigit p a j).factorial) = _
      rw [Nat.mul_succ, prod_range_add, hp]
      change Gauss.gaussDigitFactorial p (f * r) a * _ = _
      rw [ih.2, prod_range_succ]

/-- The factorial part of grouping into base `p^f` digits, with all
positions retained. No grouped factorial is assumed to be a unit. -/
theorem coefficient_factorial_blocks (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    (C : Gauss.GaussCoefficientField p k) (f r a : ℕ) :
    ∃ u : C.IntegerRing, IsUnit u ∧
      Gauss.cyclotomicResidueMap p k C.unramified u = 1 ∧
      (Gauss.gaussDigitFactorial (p ^ f) r a : C.IntegerRing) *
          C.uniformizer ^ Gauss.gaussDigitSum p (f * r) a =
        C.uniformizer ^ Gauss.gaussDigitSum (p ^ f) r a *
          (Gauss.gaussDigitFactorial p (f * r) a : C.IntegerRing) * u := by
  classical
  have h (i : ℕ) := coefficient_factorial_digits p k C f
    (Gauss.basePDigit (p ^ f) a i)
    (Nat.mod_lt _ (pow_pos (Fact.out : p.Prime).pos f))
  choose u hu hured he using h
  refine ⟨∏ i ∈ range r, u i, IsUnit.prod_iff.mpr (fun i _ ↦ hu i),
    by simp [hured], ?_⟩
  have hprod := prod_congr rfl (fun i (_ : i ∈ range r) ↦ he i)
  simp only [prod_mul_distrib, prod_pow_eq_pow_sum, ← Nat.cast_prod] at hprod
  rw [← (gaussDigits_blocks p f r a).1, ← (gaussDigits_blocks p f r a).2] at hprod
  exact hprod

/-- Equation (O:F:groupedStick) in the actual Appendix A coefficient
ring, derived from `Gauss.leadingTerm`. The plus-sign coefficient sum is
negated to match the manuscript's convention. All base-`p^f` factorials
are retained by cross-multiplication, including those divisible by `p`. -/
theorem coefficient_groupedLeadingTerm (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    (C : Gauss.GaussCoefficientField p k) (f r a : ℕ)
    (hdegree : Module.finrank (ZMod p) k = f * r)
    (ha : 0 < a) (haq : a < Nat.card k - 1) :
    ∃ u : C.IntegerRing, IsUnit u ∧
      Gauss.cyclotomicResidueMap p k C.unramified u = 1 ∧
      -Gauss.coefficientGaussSum p k C a *
          (Gauss.gaussDigitFactorial (p ^ f) r a : C.IntegerRing) =
        C.uniformizer ^ Gauss.gaussDigitSum (p ^ f) r a * u := by
  letI : IsDomain C.IntegerRing := C.coefficientDomain
  letI : IsLocalRing C.IntegerRing := C.coefficientLocalRing
  let φ := Gauss.cyclotomicResidueMap p k C.unramified
  obtain ⟨hA, _, _, _, t, hG⟩ := Gauss.leadingTerm p k C ha haq
  rw [hdegree] at hA hG
  obtain ⟨v, hv, hvred, hfac⟩ := coefficient_factorial_blocks p k C f r a
  let w : C.IntegerRing := 1 + C.uniformizer * t
  have hpi : φ C.uniformizer = 0 := by
    unfold φ Gauss.cyclotomicResidueMap Gauss.GaussCoefficientField.uniformizer
    apply AdjoinRoot.lift_root
  have hwred : φ w = 1 := by simp [w, hpi]
  have hw : IsUnit w := by
    rw [← IsLocalRing.notMem_maximalIdeal,
      ← IsLocalRing.ker_eq_maximalIdeal φ (fun x ↦
        ⟨Gauss.teichmuller_lift p k C x, Gauss.teichmuller_lift_reduction p k C x⟩),
      RingHom.mem_ker, hwred]
    exact one_ne_zero
  refine ⟨v * w, hv.mul hw, ?_, ?_⟩
  · change φ (v * w) = 1
    rw [map_mul, hwred, mul_one]
    exact hvred
  · let A : C.IntegerRing := Gauss.gaussDigitFactorial p (f * r) a
    rw [hG]
    change (C.uniformizer ^ Gauss.gaussDigitSum p (f * r) a * Ring.inverse A) * w *
        (Gauss.gaussDigitFactorial (p ^ f) r a : C.IntegerRing) = _
    calc
      _ = ((Gauss.gaussDigitFactorial (p ^ f) r a : C.IntegerRing) *
          C.uniformizer ^ Gauss.gaussDigitSum p (f * r) a) * Ring.inverse A * w := by ring
      _ = (C.uniformizer ^ Gauss.gaussDigitSum (p ^ f) r a * A * v) *
          Ring.inverse A * w := by rw [hfac]
      _ = C.uniformizer ^ Gauss.gaussDigitSum (p ^ f) r a *
          (A * Ring.inverse A) * (v * w) := by ring
      _ = _ := by rw [Ring.mul_inverse_cancel A hA, mul_one]

/-- The elementary local root-selection argument used after (O:F:Lpower).
It only needs a domain and a residue map detecting units: the geometric sum
reduces to `ell`, so it is a unit and cannot annihilate `u - 1`. -/
theorem eq_one_of_pow_eq_one_of_residue_eq_one
    {R r : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [Field r]
    (φ : R →+* r) (hφ : RingHom.ker φ = IsLocalRing.maximalIdeal R)
    {ell : ℕ} (hell : (ell : r) ≠ 0) {u : R}
    (hu : u ^ ell = 1) (hred : φ u = 1) : u = 1 := by
  classical
  have hs : φ (∑ j ∈ range ell, u ^ j) = (ell : r) := by
    simp [map_sum, map_pow, hred]
  have hunit : IsUnit (∑ j ∈ range ell, u ^ j) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← hφ, RingHom.mem_ker]
    exact hs ▸ hell
  have hz : (∑ j ∈ range ell, u ^ j) * (u - 1) = 0 := by
    rw [geom_sum_mul, hu, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hunit.ne_zero)

/-- Root selection in the actual Appendix A coefficient ring. In particular
the statement includes residue characteristic two when `ell` is odd. -/
theorem coefficientRoot_eq_one (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    (C : Gauss.GaussCoefficientField p k) {ell : ℕ} (hell : (ell : k) ≠ 0)
    {u : C.IntegerRing} (hu : u ^ ell = 1)
    (hred : Gauss.cyclotomicResidueMap p k C.unramified u = 1) : u = 1 := by
  letI : IsDomain C.IntegerRing := C.coefficientDomain
  letI : IsLocalRing C.IntegerRing := C.coefficientLocalRing
  apply eq_one_of_pow_eq_one_of_residue_eq_one
    (Gauss.cyclotomicResidueMap p k C.unramified) _ hell hu hred
  exact IsLocalRing.ker_eq_maximalIdeal _ fun x ↦
    ⟨Gauss.teichmuller_lift p k C x, Gauss.teichmuller_lift_reduction p k C x⟩

private theorem padic_charP_map (p : ℕ) [Fact p.Prime]
    {r : Type*} [CommRing r] [CharP r p] [Algebra (ZMod p) r]
    (φ : ℤ_[p] →+* r) :
    φ = (algebraMap (ZMod p) r).comp PadicInt.toZMod := by
  ext x
  have hx := PadicInt.toZMod_spec x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hx
  obtain ⟨y, hy⟩ := hx
  have he := congrArg φ hy
  simp only [map_sub, map_mul, map_natCast, CharP.cast_eq_zero r p, zero_mul] at he
  rw [sub_eq_zero] at he
  rw [he, ZMod.cast_eq_val, map_natCast]
  exact (map_natCast (algebraMap (ZMod p) r) (PadicInt.toZMod x).val).symm.trans
    (congrArg (algebraMap (ZMod p) r) (ZMod.natCast_zmod_val _))

private theorem hensel_root_of_residue
    {R r : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field r]
    (φ : R →+* r) (hφ : Function.Surjective φ)
    (f : Polynomial R) (hf : f.Monic) (x : r)
    (hx : f.eval₂ φ x = 0) (hd : f.derivative.eval₂ φ x ≠ 0) :
    ∃ y : R, f.IsRoot y ∧ φ y = x := by
  obtain ⟨a, rfl⟩ := hφ x
  letI : IsLocalHom φ := hφ.isLocalHom
  have ha : f.eval a ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.ker_eq_maximalIdeal φ hφ, RingHom.mem_ker]
    simpa only [Polynomial.eval₂_at_apply] using hx
  have had : IsUnit (f.derivative.eval a) := by
    apply IsUnit.of_map φ
    exact isUnit_iff_ne_zero.mpr (by
      simpa only [Polynomial.eval₂_at_apply] using hd)
  obtain ⟨y, hy, hya⟩ := HenselianRing.is_henselian f hf a ha
    (had.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)))
  refine ⟨y, hy, ?_⟩
  rw [← IsLocalRing.ker_eq_maximalIdeal φ hφ, RingHom.mem_ker,
    map_sub, sub_eq_zero] at hya
  exact hya

/-- Lift the given residue-field inclusion to the unramified coefficient
ring inside the upper cyclotomic ring. Hensel's lemma constructs the map;
compatibility with the specified residue maps is part of the conclusion. -/
theorem coefficient_unramifiedMap_exists (p : ℕ) [Fact p.Prime]
    (k K : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    [Field K] [Finite K] [Algebra (ZMod p) K] [Algebra k K]
    (Ck : Gauss.GaussCoefficientField p k) (CK : Gauss.GaussCoefficientField p K) :
    ∃ ι : Ck.UnramifiedRing →+* CK.IntegerRing,
      (Gauss.cyclotomicResidueMap p K CK.unramified).comp ι =
        (algebraMap k K).comp (Gauss.coefficientResidueMap p k Ck.unramified) := by
  letI : IsDomain CK.IntegerRing := CK.coefficientDomain
  letI : IsLocalRing CK.IntegerRing := CK.coefficientLocalRing
  letI : IsAdicComplete (IsLocalRing.maximalIdeal CK.IntegerRing) CK.IntegerRing :=
    CK.coefficientComplete
  letI : CharP k p := charP_of_injective_algebraMap (algebraMap (ZMod p) k).injective p
  letI : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  let U := Ck.unramified
  let φ := Gauss.cyclotomicResidueMap p K CK.unramified
  let ρ := (algebraMap k K).comp (Gauss.coefficientResidueMap p k U)
  let b : ℤ_[p] →+* CK.IntegerRing :=
    (AdjoinRoot.of (Gauss.cyclotomicUniformizerPolynomial p K CK.unramified)).comp
      (AdjoinRoot.of CK.unramified.polynomial)
  have hbase : φ.comp b = ρ.comp (AdjoinRoot.of U.polynomial) := by
    rw [padic_charP_map p (φ.comp b), padic_charP_map p (ρ.comp _)]
  let x := ρ (AdjoinRoot.root U.polynomial)
  have hx : U.polynomial.eval₂ (φ.comp b) x = 0 := by
    rw [hbase, ← Polynomial.hom_eval₂]
    rw [AdjoinRoot.eval₂_root, map_zero]
  have hsep : (U.polynomial.map (φ.comp b)).Separable := by
    rw [padic_charP_map p (φ.comp b), ← Polynomial.map_map, U.polynomial_reduction]
    exact (PerfectField.separable_of_irreducible (minpoly.irreducible
      (Algebra.IsIntegral.isIntegral U.residuePowerBasis.gen))).map
  have hd : U.polynomial.derivative.eval₂ (φ.comp b) x ≠ 0 := by
    have h := hsep.eval₂_derivative_ne_zero (RingHom.id K)
      (by simpa only [Polynomial.eval₂_map, RingHom.id_comp] using hx)
    simpa only [Polynomial.derivative_map, Polynomial.eval₂_map, RingHom.id_comp] using h
  obtain ⟨y, hy, hyred⟩ := hensel_root_of_residue φ
    (fun z ↦ ⟨Gauss.teichmuller_lift p K CK z,
      Gauss.teichmuller_lift_reduction p K CK z⟩)
    (U.polynomial.map b) (U.polynomial_monic.map b) x
    (by simpa only [Polynomial.eval₂_map] using hx)
    (by simpa only [Polynomial.derivative_map, Polynomial.eval₂_map] using hd)
  have hy' : U.polynomial.eval₂ b y = 0 := by
    simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using hy
  refine ⟨AdjoinRoot.lift b y hy', ?_⟩
  apply AdjoinRoot.ringHom_ext
  · ext a
    simpa only [φ, ρ, U, RingHom.comp_apply, AdjoinRoot.lift_of] using
      DFunLike.congr_fun hbase a
  · simpa only [φ, ρ, x, U, RingHom.comp_apply, AdjoinRoot.lift_root] using hyred

/-- The lower and upper Appendix A rings admit compatible realizations
in the upper ring, with exactly the same cyclotomic uniformizer and
primitive additive root. No choice of a norm representative is involved. -/
theorem coefficient_extensionMap_exists (p : ℕ) [Fact p.Prime]
    (k K : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    [Field K] [Finite K] [Algebra (ZMod p) K] [Algebra k K]
    (Ck : Gauss.GaussCoefficientField p k) (CK : Gauss.GaussCoefficientField p K) :
    ∃ ι : Ck.IntegerRing →+* CK.IntegerRing,
      (Gauss.cyclotomicResidueMap p K CK.unramified).comp ι =
        (algebraMap k K).comp (Gauss.cyclotomicResidueMap p k Ck.unramified) ∧
      ι Ck.uniformizer = CK.uniformizer ∧ ι Ck.zeta = CK.zeta := by
  obtain ⟨b, hb⟩ := coefficient_unramifiedMap_exists p k K Ck CK
  let Q := Gauss.cyclotomicUniformizerPolynomial p k Ck.unramified
  have hroot : Q.eval₂ b CK.uniformizer = 0 := by
    have hbase : b.comp (Int.castRingHom Ck.UnramifiedRing) =
        (AdjoinRoot.of (Gauss.cyclotomicUniformizerPolynomial p K CK.unramified)).comp
          (Int.castRingHom CK.UnramifiedRing) := RingHom.ext_int _ _
    change (((Polynomial.cyclotomic p ℤ).comp (Polynomial.X + 1)).map
      (Int.castRingHom Ck.UnramifiedRing)).eval₂ b CK.uniformizer = 0
    rw [Polynomial.eval₂_map, hbase, ← Polynomial.eval₂_map]
    exact AdjoinRoot.eval₂_root (Gauss.cyclotomicUniformizerPolynomial p K CK.unramified)
  let ι : Ck.IntegerRing →+* CK.IntegerRing := AdjoinRoot.lift b CK.uniformizer hroot
  have hpi : ι Ck.uniformizer = CK.uniformizer := AdjoinRoot.lift_root hroot
  refine ⟨ι, ?_, hpi, ?_⟩
  · apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro a
      simpa only [ι, RingHom.comp_apply, AdjoinRoot.lift_of,
        Gauss.cyclotomicResidueMap] using DFunLike.congr_fun hb a
    · simp only [RingHom.comp_apply, ι, AdjoinRoot.lift_root,
        Gauss.cyclotomicResidueMap, Gauss.GaussCoefficientField.uniformizer, map_zero]
  · simp only [Gauss.GaussCoefficientField.zeta, Gauss.cyclotomicZeta,
      map_add, map_one, ι, AdjoinRoot.lift_root, Gauss.GaussCoefficientField.uniformizer]

/-- Residue-compatible maps preserve the actual Teichmuller sections.
Uniqueness is proved in the upper ramified ring; a single residue value
alone is not used to identify an arbitrary coefficient. -/
theorem coefficient_extensionMap_teichmuller (p : ℕ) [Fact p.Prime]
    (k K : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    [Field K] [Finite K] [Algebra (ZMod p) K] [Algebra k K]
    (Ck : Gauss.GaussCoefficientField p k) (CK : Gauss.GaussCoefficientField p K)
    (ι : Ck.IntegerRing →+* CK.IntegerRing)
    (hι : (Gauss.cyclotomicResidueMap p K CK.unramified).comp ι =
      (algebraMap k K).comp (Gauss.cyclotomicResidueMap p k Ck.unramified)) (x : k) :
    ι (Gauss.teichmuller_lift p k Ck x) =
      Gauss.teichmuller_lift p K CK (algebraMap k K x) := by
  letI : Fintype k := Fintype.ofFinite k
  letI : IsDomain CK.IntegerRing := CK.coefficientDomain
  letI : IsLocalRing CK.IntegerRing := CK.coefficientLocalRing
  let φ := Gauss.cyclotomicResidueMap p K CK.unramified
  have hφ : Function.Surjective φ := fun z ↦
    ⟨Gauss.teichmuller_lift p K CK z, Gauss.teichmuller_lift_reduction p K CK z⟩
  letI : IsLocalHom φ := hφ.isLocalHom
  let f : Polynomial CK.IntegerRing := Polynomial.X ^ Fintype.card k - Polynomial.X
  have hleft : f.eval (ι (Gauss.teichmuller_lift p k Ck x)) = 0 := by
    simp only [f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      ← map_pow, FiniteField.pow_card, sub_self]
  have hright : f.eval (Gauss.teichmuller_lift p K CK (algebraMap k K x)) = 0 := by
    simp only [f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      ← map_pow, FiniteField.pow_card, sub_self]
  have hred : φ (ι (Gauss.teichmuller_lift p k Ck x)) = algebraMap k K x := by
    have h := DFunLike.congr_fun hι (Gauss.teichmuller_lift p k Ck x)
    simpa only [RingHom.comp_apply, Gauss.teichmuller_lift_reduction] using h
  apply IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hleft hright
  · intro hu
    have h := hu.map φ
    rw [map_sub, hred, Gauss.teichmuller_lift_reduction, sub_self] at h
    exact not_isUnit_zero h
  · apply IsUnit.of_map φ
    have hq : (Fintype.card k : K) = 0 := by
      simpa only [map_natCast, map_zero] using
        congrArg (algebraMap k K) (Nat.cast_card_eq_zero k)
    simp [f, Polynomial.derivative_X_pow, hq]

/-- Transport the complete lower Gauss sum to the common upper ring.
The exponent of the additive root is the lower field's absolute trace,
not the upper trace of the included element. -/
theorem coefficient_extensionMap_gaussSum (p : ℕ) [Fact p.Prime]
    (k K : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    [Field K] [Finite K] [Algebra (ZMod p) K] [Algebra k K]
    (Ck : Gauss.GaussCoefficientField p k) (CK : Gauss.GaussCoefficientField p K)
    (ι : Ck.IntegerRing →+* CK.IntegerRing)
    (hι : (Gauss.cyclotomicResidueMap p K CK.unramified).comp ι =
      (algebraMap k K).comp (Gauss.cyclotomicResidueMap p k Ck.unramified))
    (hζ : ι Ck.zeta = CK.zeta) (a : ℕ) :
    ι (Gauss.coefficientGaussSum p k Ck a) =
      ∑ x ∈ Gauss.multiplicativeResidueUnits k,
        Gauss.teichmuller_lift p K CK (algebraMap k K ((x⁻¹ : kˣ) : k)) ^ a *
          CK.zeta ^ (Algebra.trace (ZMod p) k (x : k)).val := by
  classical
  simp only [Gauss.coefficientGaussSum, map_sum, map_mul, map_pow,
    Gauss.coefficientAdditiveFactor, Gauss.absoluteTraceRepresentative, hζ,
    coefficient_extensionMap_teichmuller p k K Ck CK ι hι]

/-- Every lower grouped leading congruence holds in the constructed
common ring. The unit still has residue one and all factorials remain
cross-multiplied, even when they are divisible by `p`. -/
theorem coefficient_extensionMap_groupedLeadingTerm (p : ℕ) [Fact p.Prime]
    (k K : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    [Field K] [Finite K] [Algebra (ZMod p) K] [Algebra k K]
    (Ck : Gauss.GaussCoefficientField p k) (CK : Gauss.GaussCoefficientField p K)
    (ι : Ck.IntegerRing →+* CK.IntegerRing)
    (hι : (Gauss.cyclotomicResidueMap p K CK.unramified).comp ι =
      (algebraMap k K).comp (Gauss.cyclotomicResidueMap p k Ck.unramified))
    (hπ : ι Ck.uniformizer = CK.uniformizer) (f r a : ℕ)
    (hdegree : Module.finrank (ZMod p) k = f * r)
    (ha : 0 < a) (haq : a < Nat.card k - 1) :
    ∃ u : CK.IntegerRing, IsUnit u ∧
      Gauss.cyclotomicResidueMap p K CK.unramified u = 1 ∧
      -ι (Gauss.coefficientGaussSum p k Ck a) *
          (Gauss.gaussDigitFactorial (p ^ f) r a : CK.IntegerRing) =
        CK.uniformizer ^ Gauss.gaussDigitSum (p ^ f) r a * u := by
  obtain ⟨u, hu, hured, he⟩ := coefficient_groupedLeadingTerm p k Ck f r a hdegree ha haq
  refine ⟨ι u, hu.map ι, ?_, ?_⟩
  · have h := DFunLike.congr_fun hι u
    simpa only [RingHom.comp_apply, hured, map_one] using h
  · simpa only [map_mul, map_neg, map_natCast, map_pow, hπ] using congrArg ι he

/-- The algebraic integer values in the coefficient ring have an
injective complex realization. Only this algebraic subring is embedded;
no embedding of the complete `p`-adic field is assumed. -/
theorem coefficient_complexEmbedding_exists (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    (C : Gauss.GaussCoefficientField p k) :
    ∃ e : integralClosure ℤ C.IntegerRing →+* ℂ, Function.Injective e := by
  letI : IsDomain C.IntegerRing := C.coefficientDomain
  letI : IsDomain C.UnramifiedRing := AdjoinRoot.isDomain_of_prime C.unramified.polynomial_prime
  letI : Module.Free ℤ_[p] C.UnramifiedRing := C.unramified.coefficientFree
  letI : CharZero C.UnramifiedRing := Algebra.charZero_of_charZero ℤ_[p] C.UnramifiedRing
  letI : Module.Free C.UnramifiedRing C.IntegerRing :=
    (Gauss.cyclotomicUniformizerPolynomial_monic p k C.unramified).free_adjoinRoot
  letI : CharZero C.IntegerRing := Algebra.charZero_of_charZero C.UnramifiedRing C.IntegerRing
  let A := integralClosure ℤ C.IntegerRing
  let e : A →ₐ[ℤ] ℂ := IsAlgClosed.lift
  letI : Algebra A ℂ := e.toRingHom.toAlgebra
  letI : IsScalarTower ℤ A ℂ := IsScalarTower.of_algHom e
  exact ⟨e.toRingHom, Algebra.IsAlgebraic.injective_tower_top A Int.cast_injective⟩

/-- Teichmuller values lie in the algebraic subring used by the complex
realization, including the zero value of the extended character. -/
theorem coefficient_teichmuller_isIntegral (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    (C : Gauss.GaussCoefficientField p k) (x : k) :
    IsIntegral ℤ (Gauss.teichmuller_lift p k C x) := by
  letI : Fintype k := Fintype.ofFinite k
  by_cases hx : x = 0
  · simp [hx, isIntegral_zero]
  · apply IsIntegral.of_pow (n := Fintype.card k - 1) (by
      have : 1 < Fintype.card k := Fintype.one_lt_card
      omega)
    rw [← map_pow, FiniteField.pow_card_sub_one_eq_one x hx, map_one]
    exact isIntegral_one

private def coefficientIntegralMulChar (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    (C : Gauss.GaussCoefficientField p k) : MulChar k (integralClosure ℤ C.IntegerRing) where
  toFun x := ⟨Gauss.teichmuller_lift p k C x, coefficient_teichmuller_isIntegral p k C x⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x y)
  map_nonunit' x hx := by
    have hx0 : x = 0 := by simpa only [isUnit_iff_ne_zero, Classical.not_not] using hx
    subst x
    exact Subtype.ext (map_zero _)

private theorem finiteCharacter_order_of_injective
    {k : Type*} [Field k] [Fintype k] (χ : FiniteMulChar k)
    (hχ : Function.Injective χ) : orderOf χ = Fintype.card k - 1 := by
  classical
  apply Nat.dvd_antisymm (MulChar.orderOf_dvd_card_sub_one k χ)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := kˣ)
  have hgorder : orderOf g = Fintype.card k - 1 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_units] using hg
  rw [← hgorder, orderOf_dvd_iff_pow_eq_one]
  apply Units.ext
  apply hχ
  rw [Units.val_pow_eq_pow_val, map_pow, ← MulChar.pow_apply_coe, pow_orderOf_eq_one,
    MulChar.one_apply_coe, Units.val_one, map_one]

/-- An injective complex realization of the actual Teichmuller character
is a generator, with its full order proved from reduction. This supplies
the generator-order condition needed by the primitive representative. -/
theorem coefficient_complexGenerator (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Fintype k] [Algebra (ZMod p) k]
    (C : Gauss.GaussCoefficientField p k)
    (e : integralClosure ℤ C.IntegerRing →+* ℂ) (he : Function.Injective e) :
    ∃ ω : FiniteMulChar k, Function.Injective ω ∧ orderOf ω = Fintype.card k - 1 ∧
      ∀ x : k, ω x = e ⟨Gauss.teichmuller_lift p k C x,
        coefficient_teichmuller_isIntegral p k C x⟩ := by
  let ω := (coefficientIntegralMulChar p k C).ringHomComp e
  have hω : Function.Injective ω := by
    intro x y hxy
    have h := congrArg Subtype.val (he hxy)
    exact (Gauss.teichmuller_lift_reduction p k C x).symm.trans
      ((congrArg (Gauss.cyclotomicResidueMap p k C.unramified) h).trans
        (Gauss.teichmuller_lift_reduction p k C y))
  exact ⟨ω, hω, finiteCharacter_order_of_injective ω hω, fun _ ↦ rfl⟩

private def coefficientIntegralZeta (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    (C : Gauss.GaussCoefficientField p k) : integralClosure ℤ C.IntegerRing :=
  ⟨C.zeta, IsIntegral.of_pow (Fact.out : p.Prime).pos
    (by rw [show C.zeta ^ p = 1 from C.zetaPrimitive.pow_eq_one]; exact isIntegral_one)⟩

private theorem coefficientIntegralZeta_pow (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    (C : Gauss.GaussCoefficientField p k) :
    coefficientIntegralZeta p k C ^ p = 1 :=
  Subtype.ext C.zetaPrimitive.pow_eq_one

private def coefficientIntegralGaussSum (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    (C : Gauss.GaussCoefficientField p k) (a : ℕ) : integralClosure ℤ C.IntegerRing :=
  -∑ x ∈ Gauss.multiplicativeResidueUnits k,
    coefficientIntegralMulChar p k C ((x⁻¹ : kˣ) : k) ^ a *
      coefficientIntegralZeta p k C ^ (Algebra.trace (ZMod p) k (x : k)).val

private theorem coefficientIntegralGaussSum_val (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    (C : Gauss.GaussCoefficientField p k) (a : ℕ) :
    (coefficientIntegralGaussSum p k C a : C.IntegerRing) =
      -Gauss.coefficientGaussSum p k C a := by
  change (integralClosure ℤ C.IntegerRing).val (coefficientIntegralGaussSum p k C a) = _
  simp only [coefficientIntegralGaussSum, map_neg, map_sum, map_mul, map_pow]
  rfl

private def coefficientComplexAddChar (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    (C : Gauss.GaussCoefficientField p k)
    (e : integralClosure ℤ C.IntegerRing →+* ℂ) : FiniteAddChar k :=
  traceAddChar (ZMod p) k (AddChar.zmodChar p (by
    rw [← map_pow, coefficientIntegralZeta_pow, map_one] :
      e (coefficientIntegralZeta p k C) ^ p = 1))

/-- The actual coefficient sum realizes FML's minus-sign Gauss sum,
for every exponent. Only algebraic integers are sent to the complex numbers. -/
theorem coefficient_complexGaussSum (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Fintype k] [Algebra (ZMod p) k]
    (C : Gauss.GaussCoefficientField p k)
    (e : integralClosure ℤ C.IntegerRing →+* ℂ) (a : ℕ) :
    e (coefficientIntegralGaussSum p k C a) =
      langlandsGaussSum ((coefficientIntegralMulChar p k C).ringHomComp e ^ a)
        (coefficientComplexAddChar p k C e) := by
  classical
  rw [langlandsGaussSum_eq_neg_sum_units]
  simp only [coefficientIntegralGaussSum, map_neg, map_sum, map_mul, map_pow]
  congr 1
  apply sum_congr (by
    ext x
    simp [Gauss.multiplicativeResidueUnits])
  intro x _
  change ((coefficientIntegralMulChar p k C).ringHomComp e) ((x⁻¹ : kˣ) : k) ^ a * _ = _
  rw [MulChar.inv_apply', ← Units.val_inv_eq_inv_val, MulChar.pow_apply_coe]
  rfl

/-- Restrict the common complex realization along the constructed
coefficient map. Both Teichmuller generators and absolute trace characters
are compatible, and the lower additive character is nontrivial. -/
theorem coefficient_compatibleComplexRealization (p : ℕ) [Fact p.Prime]
    (k K : Type*) [Field k] [Fintype k] [Algebra (ZMod p) k]
    [Field K] [Fintype K] [Algebra (ZMod p) K] [Algebra k K]
    [IsScalarTower (ZMod p) k K]
    (Ck : Gauss.GaussCoefficientField p k) (CK : Gauss.GaussCoefficientField p K) :
    ∃ (ι : Ck.IntegerRing →+* CK.IntegerRing)
      (e : integralClosure ℤ CK.IntegerRing →+* ℂ)
      (ω₀ : FiniteMulChar k) (ωκ : FiniteMulChar K) (ψ : FiniteAddChar k),
      Function.Injective e ∧ orderOf ω₀ = Fintype.card k - 1 ∧
      orderOf ωκ = Fintype.card K - 1 ∧ ψ ≠ 1 ∧
      (∀ x : k, ω₀ x = ωκ (algebraMap k K x)) ∧
      (∀ x : K, ωκ x = e (coefficientIntegralMulChar p K CK x)) ∧
      (Gauss.cyclotomicResidueMap p K CK.unramified).comp ι =
        (algebraMap k K).comp (Gauss.cyclotomicResidueMap p k Ck.unramified) ∧
      ι Ck.uniformizer = CK.uniformizer ∧
      (∀ a, e (ι.toIntAlgHom.mapIntegralClosure (coefficientIntegralGaussSum p k Ck a)) =
        langlandsGaussSum (ω₀ ^ a) ψ) ∧
      (∀ a, e (coefficientIntegralGaussSum p K CK a) =
        langlandsGaussSum (ωκ ^ a) (traceAddChar k K ψ)) := by
  obtain ⟨ι, hι, hπ, hζ⟩ := coefficient_extensionMap_exists p k K Ck CK
  obtain ⟨e, he⟩ := coefficient_complexEmbedding_exists p K CK
  let e₀ := e.comp ι.toIntAlgHom.mapIntegralClosure.toRingHom
  let ω₀ := (coefficientIntegralMulChar p k Ck).ringHomComp e₀
  let ωκ := (coefficientIntegralMulChar p K CK).ringHomComp e
  have hrestrict (x : k) : ω₀ x = ωκ (algebraMap k K x) := by
    apply congrArg e
    apply Subtype.ext
    exact coefficient_extensionMap_teichmuller p k K Ck CK ι hι x
  obtain ⟨ω, hω, hωorder, hωval⟩ := coefficient_complexGenerator p K CK e he
  have hωeq : ω = ωκ := MulChar.ext (fun x ↦ hωval x)
  subst ω
  have hω₀ : Function.Injective ω₀ := by
    intro x y hxy
    exact (algebraMap k K).injective (hω (by simpa only [hrestrict] using hxy))
  have hz : e₀ (coefficientIntegralZeta p k Ck) = e (coefficientIntegralZeta p K CK) := by
    apply congrArg e
    exact Subtype.ext hζ
  have htrace : coefficientComplexAddChar p K CK e =
      traceAddChar k K (coefficientComplexAddChar p k Ck e₀) := by
    ext x
    simp only [coefficientComplexAddChar, traceAddChar_apply, AddChar.zmodChar_apply,
      residueTrace, Algebra.trace_trace]
    change e (coefficientIntegralZeta p K CK) ^ _ =
      e₀ (coefficientIntegralZeta p k Ck) ^ _
    rw [hz]
  have hψ : coefficientComplexAddChar p k Ck e₀ ≠ 1 := by
    apply (traceAddChar_ne_one_iff (ZMod p) k _).mpr
    apply (AddChar.zmod_char_ne_one_iff p _).mpr
    rw [AddChar.zmodChar_apply, ZMod.val_one, pow_one]
    change e₀ (coefficientIntegralZeta p k Ck) ≠ 1
    rw [hz]
    intro h
    have hz1 : CK.zeta = 1 := congrArg Subtype.val (he (h.trans (map_one e).symm))
    exact CK.zetaPrimitive.ne_one (Fact.out : p.Prime).one_lt hz1
  refine ⟨ι, e, ω₀, ωκ, coefficientComplexAddChar p k Ck e₀, he,
    finiteCharacter_order_of_injective ω₀ hω₀, hωorder, hψ, hrestrict, (fun _ ↦ rfl), hι, hπ,
    fun a ↦ coefficient_complexGaussSum p k Ck e₀ a, ?_⟩
  intro a
  rw [coefficient_complexGaussSum, htrace]

private theorem leadingComparison_unit
    {R r : Type*} [CommRing R] [IsDomain R] [Field r]
    (φ : R →+* r) (N D A B P E T : R) (hB : B ≠ 0)
    (hE : IsUnit E) (hT : IsUnit T) (hET : φ E = φ T)
    (u v w : Rˣ) (hu : φ u = 1) (hv : φ v = 1) (hw : φ w = 1)
    (hN : N * A = P * u) (hD : D * B = T * P * v)
    (hfac : E * A = w * B) :
    ∃ t : R, IsUnit t ∧ φ t = 1 ∧ N = D * t := by
  let d : Rˣ := hT.unit * v * w
  let t : Rˣ := hE.unit * u / d
  have hdt : (d : R) * t = E * u := by
    have ht : d * t = hE.unit * u := by dsimp [t]; rw [mul_comm, div_mul_cancel]
    simpa only [Units.val_mul, hE.unit_spec] using congrArg Units.val ht
  have hred : φ (t : R) = 1 := by
    have hdred : φ (d : R) = φ T := by simp [d, hv, hw]
    have htred := congrArg φ hdt
    rw [map_mul, map_mul, hu, mul_one, hdred, hET] at htred
    exact (mul_eq_left₀ (hT.map φ).ne_zero).mp htred
  refine ⟨t, t.isUnit, hred, ?_⟩
  apply mul_right_cancel₀ (mul_ne_zero d.ne_zero hB)
  calc
    N * ((d : R) * B) = (T * (v : R)) * (N * ((w : R) * B)) := by
      simp only [d, Units.val_mul, hT.unit_spec]; ring
    _ = (T * (v : R)) * (E * (P * (u : R))) := by rw [← hfac, mul_left_comm N E, hN]
    _ = (D * B) * (E * (u : R)) := by rw [hD]; ring
    _ = D * (t : R) * ((d : R) * B) := by rw [← hdt]; ring

private theorem coefficient_charZero (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    (C : Gauss.GaussCoefficientField p k) : CharZero C.IntegerRing := by
  letI : IsDomain C.IntegerRing := C.coefficientDomain
  letI : IsDomain C.UnramifiedRing := AdjoinRoot.isDomain_of_prime C.unramified.polynomial_prime
  letI : Module.Free ℤ_[p] C.UnramifiedRing := C.unramified.coefficientFree
  letI : CharZero C.UnramifiedRing := Algebra.charZero_of_charZero ℤ_[p] C.UnramifiedRing
  letI : Module.Free C.UnramifiedRing C.IntegerRing :=
    (Gauss.cyclotomicUniformizerPolynomial_monic p k C.unramified).free_adjoinRoot
  exact Algebra.charZero_of_charZero C.UnramifiedRing C.IntegerRing

set_option maxHeartbeats 600000 in
/-- The passage to `L ≡ 1` in (O:F:finite), before the power identity.
The complete denominator and its actual Teichmuller value occur in the
constructed equality; the factorials are only cancelled as nonzero elements. -/
theorem coefficient_primitiveComparison_unit (p : ℕ) [Fact p.Prime]
    (k K : Type*) [Field k] [Fintype k] [Algebra (ZMod p) k]
    [Field K] [Fintype K] [Algebra (ZMod p) K] [Algebra k K]
    (Ck : Gauss.GaussCoefficientField p k) (CK : Gauss.GaussCoefficientField p K)
    (ι : Ck.IntegerRing →+* CK.IntegerRing)
    (hι : (Gauss.cyclotomicResidueMap p K CK.unramified).comp ι =
      (algebraMap k K).comp (Gauss.cyclotomicResidueMap p k Ck.unramified))
    (hπ : ι Ck.uniformizer = CK.uniformizer) (f ell h a : ℕ)
    (hell : ell.Prime) (hk : Module.finrank (ZMod p) k = f)
    (hK : Module.finrank (ZMod p) K = f * ell)
    (hq : Fintype.card k = p ^ f) (hqh : p ^ f = ell * h + 1)
    (ha : 0 < a) (haq : a < Fintype.card k - 1) (haprim : ¬ ell ∣ a)
    (hApos : 0 < primitiveExponent (p ^ f) ell a)
    (hAq : primitiveExponent (p ^ f) ell a < Nat.card K - 1) :
    ∃ u : CK.IntegerRing, IsUnit u ∧
      Gauss.cyclotomicResidueMap p K CK.unramified u = 1 ∧
      -Gauss.coefficientGaussSum p K CK (primitiveExponent (p ^ f) ell a) =
        (Gauss.teichmuller_lift p K CK (ell : K) ^ a *
          -ι (Gauss.coefficientGaussSum p k Ck a) *
          ∏ j ∈ Icc 1 (ell - 1), -ι (Gauss.coefficientGaussSum p k Ck (j * h))) * u := by
  classical
  letI : IsDomain CK.IntegerRing := CK.coefficientDomain
  letI : IsLocalRing CK.IntegerRing := CK.coefficientLocalRing
  letI : CharZero CK.IntegerRing := coefficient_charZero p K CK
  let φ := Gauss.cyclotomicResidueMap p K CK.unramified
  have hsurj : Function.Surjective φ := fun x ↦
    ⟨Gauss.teichmuller_lift p K CK x, Gauss.teichmuller_lift_reduction p K CK x⟩
  letI : IsLocalHom φ := hsurj.isLocalHom
  have hdiv : ell ∣ Fintype.card k - 1 := by rw [hq, hqh, Nat.add_sub_cancel]; exact dvd_mul_right _ _
  have hellK : (ell : K) ≠ 0 := by
    simpa only [map_natCast] using (map_ne_zero (algebraMap k K)).mpr (degree_cast_ne_zero ell hdiv)
  have hT : IsUnit (Gauss.teichmuller_lift p K CK (ell : K) ^ a) :=
    ((isUnit_iff_ne_zero.mpr hellK).map (Gauss.teichmuller_lift p K CK)).pow a
  have hE : IsUnit ((ell : CK.IntegerRing) ^ a) :=
    IsUnit.of_map φ _ (by simpa using isUnit_iff_ne_zero.mpr (pow_ne_zero a hellK))
  have hfacB : (a.factorial : CK.IntegerRing) *
      (∏ j ∈ Icc 1 (ell - 1), ((j * h).factorial : CK.IntegerRing)) ≠ 0 := by
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      (prod_ne_zero_iff.mpr fun j _ ↦ Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have ha' : a < p ^ f := by omega
  obtain ⟨u, ⟨u, rfl⟩, hured, hN⟩ := coefficient_groupedLeadingTerm p K CK f ell
    (primitiveExponent (p ^ f) ell a) hK hApos hAq
  have hlower (b : ℕ) (hb : 0 < b) (hbq : b < Fintype.card k - 1) :
      ∃ v : CK.IntegerRing, IsUnit v ∧ φ v = 1 ∧
        -ι (Gauss.coefficientGaussSum p k Ck b) * (b.factorial : CK.IntegerRing) =
          CK.uniformizer ^ b * v := by
    have h := coefficient_extensionMap_groupedLeadingTerm p k K Ck CK ι hι hπ f 1 b
      (by simpa using hk) hb (by simpa only [Nat.card_eq_fintype_card] using hbq)
    simpa [Gauss.gaussDigitSum, Gauss.gaussDigitFactorial, Gauss.basePDigit,
      Nat.mod_eq_of_lt (show b < p ^ f by omega)] using h
  obtain ⟨v, ⟨v, rfl⟩, hvred, hva⟩ := hlower a ha haq
  have hj (j : ℕ) (hj : j ∈ Icc 1 (ell - 1)) : 0 < j * h ∧ j * h < Fintype.card k - 1 := by
    have hh : 0 < h := by have := Fintype.one_lt_card (α := k); nlinarith [hq.trans hqh]
    have hbounds := mem_Icc.mp hj
    constructor
    · exact Nat.mul_pos hbounds.1 hh
    · rw [hq, hqh, Nat.add_sub_cancel]; exact Nat.mul_lt_mul_of_pos_right (by omega) hh
  choose w hw hwred hwfac using fun j : Icc 1 (ell - 1) ↦ hlower (j.val * h) (hj _ j.property).1 (hj _ j.property).2
  let w' (j : ℕ) : CK.IntegerRing := if hj : j ∈ Icc 1 (ell - 1) then w ⟨j, hj⟩ else 1
  have hw' (j : ℕ) : IsUnit (w' j) := by
    dsimp [w']; split
    · exact hw _
    · exact isUnit_one
  have hw'red (j : ℕ) : φ (w' j) = 1 := by
    dsimp [w']; split
    · exact hwred _
    · exact map_one φ
  have hterm (j : ℕ) (hj : j ∈ Icc 1 (ell - 1)) :
      -ι (Gauss.coefficientGaussSum p k Ck (j * h)) * ((j * h).factorial : CK.IntegerRing) =
        CK.uniformizer ^ (j * h) * w' j := by
    simpa only [w', dif_pos hj] using hwfac ⟨j, hj⟩
  have hprod := prod_congr rfl hterm
  simp only [prod_mul_distrib, prod_pow_eq_pow_sum] at hprod
  have hD := congrArg₂ (· * ·) hva hprod
  have hI : Ico 1 ell = Icc 1 (ell - 1) := by
    ext j; simp only [mem_Ico, mem_Icc]; omega
  have hsum : Gauss.gaussDigitSum (p ^ f) ell (primitiveExponent (p ^ f) ell a) =
      a + ∑ j ∈ Icc 1 (ell - 1), j * h := by
    rw [hqh, primitiveExponent_digitSum ell h a hell (by omega) haprim]
    congr 1
    rw [sum_range_eq_add_Ico _ hell.pos]
    simp [hI]
  obtain ⟨z, ⟨z, rfl⟩, hzred, hzfac⟩ := coefficient_primitiveExponent_factorialUnit p K CK f ell h a
    hell hqh.symm ha' haprim
  have hfacprod : (∏ j ∈ range ell, ((j * h).factorial : CK.IntegerRing)) =
      ∏ j ∈ Icc 1 (ell - 1), ((j * h).factorial : CK.IntegerRing) := by
    rw [prod_range_eq_mul_Ico _ hell.pos]
    simp [hI]
  rw [hfacprod] at hzfac
  obtain ⟨v', hv', hv'red, hv'fac⟩ := leadingComparison_unit φ _
    (Gauss.teichmuller_lift p K CK (ell : K) ^ a * -ι (Gauss.coefficientGaussSum p k Ck a) *
      ∏ j ∈ Icc 1 (ell - 1), -ι (Gauss.coefficientGaussSum p k Ck (j * h)))
    _ _ _ _ _ hfacB hE hT
    (by simp [φ, Gauss.teichmuller_lift_reduction]) u
    (v * (IsUnit.prod_iff.mpr (fun j (_ : j ∈ Icc 1 (ell - 1)) ↦ hw' j)).unit) z
    hured (by simp [hvred, IsUnit.unit_spec, hw'red]) hzred hN
    (by
      rw [hsum, pow_add]
      simp only [Units.val_mul, IsUnit.unit_spec]
      convert congrArg (Gauss.teichmuller_lift p K CK (ell : K) ^ a * ·) hD using 1 <;> ring)
    hzfac
  exact ⟨v', hv', hv'red, hv'fac⟩

set_option maxHeartbeats 800000 in
/-- The primitive finite-field identity (O:F:finiteidentity), with arbitrary
nontrivial trace-compatible additive characters and the complete lower product.
The coefficient realization and residue-one comparison unit are constructed
from the finite fields; no leading congruence is an additional hypothesis. -/
theorem finiteComparison
    {k K : Type*} [Field k] [Fintype k] [Field K] [Fintype K] [Algebra k K]
    (ell : ℕ) (hell : ell.Prime) (hdegree : Module.finrank k K = ell)
    (hdiv : ell ∣ Fintype.card k - 1)
    (χκ : FiniteMulChar K) (χ₀ μ : FiniteMulChar k)
    (hμ : orderOf μ = ell) (hcompat : χκ ^ ell = normMulChar k K χ₀)
    (hprim : ∃ u : kˣ, u ^ ell = 1 ∧ χ₀ (u : k) ≠ 1)
    (ψ : FiniteAddChar k) (hψ : ψ ≠ 1) :
    langlandsGaussSum χκ (traceAddChar k K ψ) =
      χ₀ (ell : k) * langlandsGaussSum χ₀ ψ *
        ∏ j ∈ Icc 1 (ell - 1), langlandsGaussSum (μ ^ j) ψ := by
  classical
  let p := ringChar k
  letI : Fact p.Prime := ⟨CharP.prime_ringChar k⟩
  letI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  let f := Module.finrank (ZMod p) k
  have hq : Fintype.card k = p ^ f := by
    simpa only [ZMod.card] using (Module.card_eq_pow_finrank (K := ZMod p) (V := k))
  have hK : Module.finrank (ZMod p) K = f * ell := by
    rw [← Module.finrank_mul_finrank (ZMod p) k K, hdegree]
  obtain ⟨h, hh⟩ := hdiv
  have hqh : p ^ f = ell * h + 1 := by have := Fintype.card_pos (α := k); omega
  obtain ⟨Ck⟩ := Gauss.gaussCoefficientField_exists p k
  obtain ⟨CK⟩ := Gauss.gaussCoefficientField_exists p K
  obtain ⟨ι, e, ω₀, ωκ, ψ₀, he, hω₀, hωκ, hψ₀, hrestrict, hωval, hι, hπ, hlow, hupp⟩ :=
    coefficient_compatibleComplexRealization p k K Ck CK
  obtain ⟨a, ha, haq, haprim, hχ₀, _, hrep⟩ := finiteComparison_primitiveRepresentative
    ell hell hdegree (hh ▸ dvd_mul_right ell h) χκ ωκ χ₀ ω₀ hω₀ hrestrict hcompat hprim
  let A := primitiveExponent (p ^ f) ell a
  have hS : 0 < ∑ i ∈ range ell, (p ^ f) ^ i :=
    sum_pos' (fun _ _ ↦ Nat.zero_le _) ⟨0, mem_range.mpr hell.pos, by simp⟩
  have hAmul : ell * A = a * ∑ i ∈ range ell, (p ^ f) ^ i := by
    dsimp [A]; rw [hqh, primitiveExponent_mul]
  have hApos : 0 < A := by nlinarith [Nat.mul_pos ha hS]
  have hcardK : Nat.card K = (p ^ f) ^ ell := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := k), hdegree, hq]
  have hAq : A < Nat.card K - 1 := by
    have hgeom := geom_sum_mul_of_one_le (show 1 ≤ p ^ f by omega) ell
    have hlt := Nat.mul_lt_mul_of_pos_right (show a < p ^ f - 1 by omega) hS
    rw [mul_comm (p ^ f - 1), hgeom, ← hAmul] at hlt
    rw [hcardK]
    exact lt_of_le_of_lt (Nat.le_mul_of_pos_left A hell.pos) hlt
  let ν := ω₀ ^ h
  have hν : orderOf ν = ell := by
    have hd : ell ∣ orderOf ω₀ := by rw [hω₀, hh]; exact dvd_mul_right _ _
    have heq : orderOf ω₀ / ell = h := by rw [hω₀, hh, Nat.mul_div_right h hell.pos]
    simpa only [heq] using orderOf_pow_orderOf_div (MulChar.orderOf_pos ω₀).ne' hd
  let N := coefficientIntegralGaussSum p K CK A
  let J : integralClosure ℤ Ck.IntegerRing →+* integralClosure ℤ CK.IntegerRing :=
    ι.toIntAlgHom.mapIntegralClosure.toRingHom
  let D : integralClosure ℤ CK.IntegerRing := coefficientIntegralMulChar p K CK (ell : K) ^ a *
    J (coefficientIntegralGaussSum p k Ck a) *
      ∏ j ∈ Icc 1 (ell - 1),
        J (coefficientIntegralGaussSum p k Ck (j * h))
  have heN : e N = langlandsGaussSum χκ (traceAddChar k K ψ₀) := by
    rw [hupp, hrep ψ₀, hq]
  have heD : e D = finiteComparisonDenominator ell χ₀ ν ψ₀ := by
    change ∀ b, e (J (coefficientIntegralGaussSum p k Ck b)) = langlandsGaussSum (ω₀ ^ b) ψ₀ at hlow
    dsimp [D]
    simp only [map_mul, map_pow, map_prod, hlow, ← hωval]
    rw [← show algebraMap k K (ell : k) = (ell : K) by simp, ← hrestrict]
    simp only [finiteComparisonDenominator, hχ₀, MulChar.pow_apply' _ ha.ne', ν,
      ← pow_mul, Nat.mul_comm h]
  have hDzero : e D ≠ 0 := by
    rw [heD]
    exact finiteComparisonDenominator_ne_zero ell (hh ▸ dvd_mul_right ell h) χ₀ ν ψ₀ hψ₀
  have hp : N ^ ell = D ^ ell := by
    apply he
    rw [map_pow, map_pow]
    apply (div_eq_one_iff_eq (pow_ne_zero ell hDzero)).mp
    rw [← div_pow, heN, heD]
    exact finiteComparison_pow ell hell hdegree (hh ▸ dvd_mul_right ell h)
      χκ χ₀ ν hν hcompat hprim ψ₀ hψ₀
  letI : IsDomain CK.IntegerRing := CK.coefficientDomain
  have hDval : (D : CK.IntegerRing) ≠ 0 := by
    intro hz
    have : D = 0 := Subtype.ext hz
    exact hDzero (by rw [this, map_zero])
  obtain ⟨u, _, hured, hunit⟩ := coefficient_primitiveComparison_unit p k K Ck CK ι hι hπ
    f ell h a hell rfl hK hq hqh ha haq haprim hApos hAq
  have hND : (N : CK.IntegerRing) = (D : CK.IntegerRing) * u := by
    have hJval (b : ℕ) : (integralClosure ℤ CK.IntegerRing).val
        (J (coefficientIntegralGaussSum p k Ck b)) = -ι (Gauss.coefficientGaussSum p k Ck b) := by
      change ι (coefficientIntegralGaussSum p k Ck b : Ck.IntegerRing) = _
      rw [coefficientIntegralGaussSum_val, map_neg]
    change (integralClosure ℤ CK.IntegerRing).val N =
      (integralClosure ℤ CK.IntegerRing).val D * u
    simp only [D, map_mul, map_pow, map_prod, hJval]
    change (N : CK.IntegerRing) = _
    rw [coefficientIntegralGaussSum_val]
    exact hunit
  have huell : u ^ ell = 1 := by
    have hpval := congrArg Subtype.val hp
    change (N : CK.IntegerRing) ^ ell = (D : CK.IntegerRing) ^ ell at hpval
    rw [hND, mul_pow] at hpval
    exact (mul_eq_left₀ (pow_ne_zero ell hDval)).mp hpval
  have huone : u = 1 := coefficientRoot_eq_one p K CK
    (by simpa only [map_natCast] using
      (map_ne_zero (algebraMap k K)).mpr (degree_cast_ne_zero ell (hh ▸ dvd_mul_right ell h)))
    huell hured
  have hcanonical : langlandsGaussSum χκ (traceAddChar k K ψ₀) =
      finiteComparisonDenominator ell χ₀ μ ψ₀ := by
    have hND' : N = D := Subtype.ext (by simpa only [huone, mul_one] using hND)
    rw [← heN, hND', heD, finiteComparisonDenominator, finiteComparisonDenominator,
      finiteComparison_lowerProduct_independent ell hell.pos ν μ hν hμ ψ₀ hψ₀]
  apply (div_eq_one_iff_eq
    (finiteComparisonDenominator_ne_zero ell (hh ▸ dvd_mul_right ell h) χ₀ μ ψ hψ)).mp
  rw [finiteComparison_ratio_independent ell hell hdegree (hh ▸ dvd_mul_right ell h)
    χκ χ₀ μ hμ hcompat hprim ψ₀ ψ hψ₀ hψ, hcanonical]
  exact div_self (finiteComparisonDenominator_ne_zero ell (hh ▸ dvd_mul_right ell h) χ₀ μ ψ₀ hψ₀)

end

end LanglandsSecondMainLemma.Tame
