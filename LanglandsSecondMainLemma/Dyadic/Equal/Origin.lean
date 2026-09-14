import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Cases.WildQuadratic.EqualCharacteristicBreak
import LanglandsSecondMainLemma.EqualChar.NormCharacter
import LanglandsSecondMainLemma.Basic.NormTrace
import LanglandsSecondMainLemma.Ramification.DiamondBreaks
import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Dyadic / Equal / Origin

The simultaneous origin of the corrected paper, lines 6112–6207.

`quadratic_origin_exists` is a proved constructor from a genuine totally
ramified quadratic local extension. It provides a fully reduced AS generator,
its odd pole and actual ramification break, the actual different and norm
character conductors, exact square roots and their integer orders, the full
lower stationary chart, a genuine norm coefficient, and the whole-ideal
trace-to-norm phase conversion. All these results work in any prescribed base
Laurent presentation: the AS residue symbol's independence of presentation is
proved using formal substitution and its chain rule.

`dyadicEqual_origin_exists` constructs all three actual fixed fields, labels
the smallest break first, and retains the exact third generator `z₁ + z₂`.
The ramification profile supplies both edge breaks. Laurent coordinates are
constructed at the norm of an actual top uniformizer, and the resulting
square roots give the simultaneous numerator, its exact norms and traces,
its valuation and the upper different ledger.

`dyadicEqual_lowerCharts` applies to each retained reduced generator and any
actual nontrivial lower norm character. It proves the additive conductor
ledger, square annihilation, triviality at the full norm coefficient, and
both stationary identities on their whole specified ideals. Its generator
and different hypotheses are provided by the constructed `A.edge` data.

Source labels: `D:EQ:compatiblepi`, `D:EQ:rledger`, `D:EQ:dbeta`,
`D:EQ:origin`, `D:EQ:exact-origin`, `D:EQ:originval`,
`D:EQ:upperdifferent`, `D:EQ:Psis`, `D:EQ:Jledger`,
`D:EQ:lowerchart`, `D:EQ:loweractualnorm`, and `D:EQ:normphase`.
-/

open scoped LaurentSeries PowerSeries
open HahnSeries LanglandsFirstMainLemma
namespace LanglandsSecondMainLemma.Dyadic.Equal
noncomputable section
open private coeff_sq_even coeff_sq_odd from LanglandsSecondMainLemma.EqualChar.Cartier
open private laurentDerivative_mul laurentDerivative_coeff
  laurentDerivative_substitution substitution_powerSeries from
  LanglandsSecondMainLemma.Residues.LogNorm
open private logarithmicDerivative_order next_order_bound from
  LanglandsSecondMainLemma.EqualChar.NormCharacter

local instance (k : Type*) [Field k] [CharP k 2] : CharP (k⸨X⸩) 2 :=
  CharP.of_ringHom_of_ne_zero (HahnSeries.C : k →+* k⸨X⸩) 2 (by norm_num)

section Laurent
variable {k : Type*} [Field k] [Finite k] [CharP k 2]
local instance : Algebra (ZMod 2) k := ZMod.algebra k 2

/-- Reduced AS parameters have only a constant and negative odd powers. -/
def IsReducedAS (f : k⸨X⸩) : Prop :=
  ∀ n : ℤ, n ≠ 0 → (0 < n ∨ Even n) → f.coeff n = 0

/-- The negative part of a reduced parameter. -/
def reducedNegativePart (f : k⸨X⸩) : k⸨X⸩ := f - HahnSeries.C (f.coeff 0)

/-- The exact coefficient β of (D:EQ:dbeta), in Laurent coordinates. -/
def originBeta (t : ℤ) (f : k⸨X⸩) : k⸨X⸩ :=
  single t 1 * reducedNegativePart f

/-- Coefficientwise square roots of the even powers. -/
def evenSquareRoot (f : k⸨X⸩) : k⸨X⸩ :=
  HahnSeries.ofSuppBddBelow
    (fun m : ℤ ↦ (frobeniusEquiv k 2).symm (f.coeff (2 * m))) (by
      refine ⟨min 0 f.order, ?_⟩
      intro m hm
      have hcoeff : f.coeff (2 * m) ≠ 0 := by
        intro hz
        exact hm (by simp [hz])
      have hord := HahnSeries.order_le_of_coeff_ne_zero hcoeff
      omega)

@[simp] theorem evenSquareRoot_coeff (f : k⸨X⸩) (m : ℤ) :
    (evenSquareRoot f).coeff m = (frobeniusEquiv k 2).symm (f.coeff (2 * m)) := rfl

theorem evenSquareRoot_sq (f : k⸨X⸩)
    (hf : ∀ m : ℤ, f.coeff (2 * m + 1) = 0) :
    evenSquareRoot f ^ 2 = f := by
  ext n
  rcases Int.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show n = 2 * m by omega, coeff_sq_even, evenSquareRoot_coeff]
    exact (frobeniusEquiv k 2).apply_symm_apply _
  · rw [hm, coeff_sq_odd, hf]

omit [Finite k] [CharP k 2] in
theorem originBeta_odd_coeff (t : ℤ) (ht : Odd t)
    (f : k⸨X⸩) (hf : IsReducedAS f) (m : ℤ) :
    (originBeta t f).coeff (2 * m + 1) = 0 := by
  simp only [originBeta, HahnSeries.coeff_single_mul, one_mul,
    reducedNegativePart, HahnSeries.coeff_sub]
  by_cases hzero : 2 * m + 1 - t = 0
  · simp [hzero]
  · rw [hf _ hzero (Or.inr (by obtain ⟨r, hr⟩ := ht; exact ⟨m - r, by omega⟩))]
    simp [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hzero]

/-- Exponent parity constructs the full square root, not just a residue lift. -/
theorem originBeta_square (t : ℤ) (ht : Odd t)
    (f : k⸨X⸩) (hf : IsReducedAS f) :
    evenSquareRoot (originBeta t f) ^ 2 = originBeta t f :=
  evenSquareRoot_sq _ (originBeta_odd_coeff t ht f hf)

omit [Finite k] [CharP k 2] in
/-- Multiplication by the common pole power gives the exact order `t₂ - t₁`. -/
theorem originBeta_order (t₁ t₂ : ℤ) (f : k⸨X⸩) (ht₁ : 0 < t₁)
    (hf : f.orderTop = ((-t₁ : ℤ) : WithTop ℤ)) :
    (originBeta t₂ f).orderTop = ((t₂ - t₁ : ℤ) : WithTop ℤ) := by
  have hc : (0 : WithTop ℤ) ≤ (HahnSeries.C (f.coeff 0)).orderTop := by
    exact HahnSeries.orderTop_single_le
  have hneg : f.orderTop < (-(HahnSeries.C (f.coeff 0))).orderTop := by
    simp only [HahnSeries.orderTop_neg]
    rw [hf]
    exact (WithTop.coe_lt_coe.mpr (by omega : -t₁ < 0)).trans_le hc
  rw [originBeta, HahnSeries.orderTop_mul, HahnSeries.orderTop_single one_ne_zero,
    reducedNegativePart, sub_eq_add_neg, HahnSeries.orderTop_add_eq_left hneg, hf,
    ← WithTop.coe_add]
  congr 1

/-- The square root has exactly half the integral valuation, including
positive depth δ and the unit case δ = 0. -/
theorem originSquareRoot_order (t₁ t₂ δ : ℤ) (f : k⸨X⸩) (ht₁ : 0 < t₁)
    (ht₂ : Odd t₂) (hδ : t₂ - t₁ = 2 * δ) (hred : IsReducedAS f)
    (hf : f.orderTop = ((-t₁ : ℤ) : WithTop ℤ)) :
    (evenSquareRoot (originBeta t₂ f)).orderTop = (δ : WithTop ℤ) := by
  have hsquare := originBeta_square t₂ ht₂ f hred
  have hord := originBeta_order t₁ t₂ f ht₁ hf
  have hdouble : (evenSquareRoot (originBeta t₂ f)).orderTop +
      (evenSquareRoot (originBeta t₂ f)).orderTop = ((2 * δ : ℤ) : WithTop ℤ) := by
    rw [← HahnSeries.orderTop_mul, ← pow_two, hsquare, hord, hδ]
  have hfinite : (evenSquareRoot (originBeta t₂ f)).orderTop ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at hdouble
    exact WithTop.top_ne_coe hdouble
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hfinite
  rw [← ha, ← WithTop.coe_add] at hdouble
  have heq : a = δ := by
    have h := WithTop.coe_injective hdouble
    omega
  rw [← ha, heq]

omit [Finite k] [CharP k 2] in
@[simp] theorem originBeta_add (t : ℤ) (f g : k⸨X⸩) :
    originBeta t (f + g) = originBeta t f + originBeta t g := by
  simp only [originBeta, reducedNegativePart, HahnSeries.coeff_add, map_add]
  ring

/-- The third exact square root is the sum of the first two. -/
theorem originSquareRoot_add (t : ℤ) (ht : Odd t)
    (f g : k⸨X⸩) (hf : IsReducedAS f) (hg : IsReducedAS g) :
    evenSquareRoot (originBeta t (f + g)) =
      evenSquareRoot (originBeta t f) + evenSquareRoot (originBeta t g) := by
  have hfg : IsReducedAS (f + g) := by
    intro n hn hc
    simp only [HahnSeries.coeff_add, hf n hn hc, hg n hn hc, add_zero]
  apply CharTwo.sq_injective
  dsimp only
  rw [originBeta_square t ht _ hfg, CharTwo.add_sq,
    originBeta_square t ht _ hf, originBeta_square t ht _ hg, originBeta_add]

omit [Finite k] [CharP k 2] in
private theorem derivative_residue (f : k⸨X⸩) :
    Residues.residue (LaurentSeries.derivative k f) = 0 := by
  simp [Residues.residue]

omit [Finite k] in
/-- Formal integration by parts with the characteristic-two sign. -/
theorem residue_integrationByParts (f z : k⸨X⸩) :
    Residues.residue (f * LaurentSeries.derivative k z) =
      Residues.residue (LaurentSeries.derivative k f * z) := by
  have h := derivative_residue (f * z)
  rw [laurentDerivative_mul] at h
  simp only [Residues.residue, HahnSeries.coeff_add] at h
  simpa only [Residues.residue, mul_comm] using CharTwo.add_eq_zero.mp h

omit [Finite k] in
/-- At stationary depth the entire nonlinear logarithmic error has zero residue. -/
theorem residueExponent_stationary (f z : k⸨X⸩) (t r : ℤ)
    (hr : 0 < r) (hdepth : t + 1 ≤ 2 * r)
    (hf : ((-t : ℤ) : WithTop ℤ) ≤ f.orderTop)
    (hz : (r : WithTop ℤ) ≤ z.orderTop) :
    EqualChar.residueExponent f (1 - z) =
      Algebra.trace (ZMod 2) k
        (Residues.residue (LaurentSeries.derivative k f * z)) := by
  let u : k⸨X⸩ := 1 - z
  have hu : (r : WithTop ℤ) ≤ (u - 1).orderTop := by
    simpa [u] using hz
  have huord : u.orderTop = 0 := by
    have h := HahnSeries.orderTop_add_eq_left (x := (1 : k⸨X⸩))
      (y := -z) (by simpa using (WithTop.coe_lt_coe.mpr hr).trans_le hz)
    simpa [u, sub_eq_add_neg] using h
  have hu0 : u ≠ 0 := by
    intro heq
    simp [heq] at huord
  have hd := logarithmicDerivative_order u r hr hu
  have herr : Residues.residue (f * z * EqualChar.logarithmicDerivative u) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    have h := add_le_add (add_le_add hf hz) hd
    simp only [← HahnSeries.orderTop_mul, ← WithTop.coe_add] at h
    exact (WithTop.coe_lt_coe.mpr (by omega : (-1 : ℤ) < -t + r + (r - 1))).trans_le h
  have hdu : LaurentSeries.derivative k u = LaurentSeries.derivative k z := by
    simp [u, CharTwo.sub_eq_add, LaurentSeries.derivative_apply,
      ← HahnSeries.single_zero_one]
  have heq : f * EqualChar.logarithmicDerivative u +
      f * z * EqualChar.logarithmicDerivative u = f * LaurentSeries.derivative k z := by
    calc
      _ = f * (u * EqualChar.logarithmicDerivative u) := by
        dsimp [u]
        rw [CharTwo.sub_eq_add]
        ring
      _ = _ := by
        rw [EqualChar.logarithmicDerivative, ← mul_assoc u, mul_inv_cancel₀ hu0,
          one_mul, hdu]
  have hres := congrArg Residues.residue heq
  change Residues.residue (f * EqualChar.logarithmicDerivative u) +
    Residues.residue (f * z * EqualChar.logarithmicDerivative u) = _ at hres
  rw [herr, add_zero, residue_integrationByParts] at hres
  exact congrArg (Algebra.trace (ZMod 2) k) hres

omit [Finite k] in
/-- The full differential coefficient used in (D:EQ:lowerchart). -/
theorem derivative_eq_originBeta (t : ℤ) (f : k⸨X⸩) (hf : IsReducedAS f) :
    LaurentSeries.derivative k f = single (-(t + 1)) 1 * originBeta t f := by
  rw [originBeta, ← mul_assoc, HahnSeries.single_mul_single]
  simp only [one_mul, show -(t + 1) + t = (-1 : ℤ) by omega]
  ext n
  rw [laurentDerivative_coeff, HahnSeries.coeff_single_mul, one_mul]
  simp only [reducedNegativePart, HahnSeries.coeff_sub,
    show n - -1 = n + 1 by omega]
  by_cases hn : n + 1 = 0
  · have hn0 : n = -1 := by omega
    simp [hn0]
  · have hc : (HahnSeries.C (f.coeff 0)).coeff (n + 1) = 0 := by
      simp [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hn]
    rw [hc, sub_zero]
    rcases Int.even_or_odd (n + 1) with heven | hodd
    · rw [hf _ hn (Or.inr heven), mul_zero]
    · have hcast : ((n + 1 : ℤ) : k) = 1 := by
        obtain ⟨m, hm⟩ := hodd
        rw [hm]
        push_cast
        rw [CharTwo.two_eq_zero]
        simp
      rw [Int.cast_add, Int.cast_one] at hcast
      rw [hcast, one_mul]

/-- The canonical residue phase with integer scaling exponent `T`. -/
def scaledResiduePhase (T : ℤ) (x : k⸨X⸩) : ℂ :=
  binaryAddChar (Algebra.trace (ZMod 2) k
    (Residues.residue (single (-T) 1 * x)))

omit [Finite k] in
/-- Even scaling exponents annihilate every square, as in (D:EQ:Psis). -/
theorem scaledResiduePhase_square (T : ℤ) (hT : Even T) (x : k⸨X⸩) :
    scaledResiduePhase T (x ^ 2) = 1 := by
  obtain ⟨m, hm⟩ := hT
  have heq : (-1 : ℤ) - -T = 2 * (m - 1) + 1 := by omega
  simp [scaledResiduePhase, Residues.residue, HahnSeries.coeff_single_mul,
    heq, coeff_sq_odd]

omit [Finite k] [CharP k 2] in
/-- Every point of a positive-depth ideal defines a nonzero principal unit. -/
theorem one_sub_ne_zero_of_order (z : k⸨X⸩) (r : ℤ) (hr : 0 < r)
    (hz : (r : WithTop ℤ) ≤ z.orderTop) : 1 - z ≠ 0 := by
  intro hu
  have heq : z = 1 := (sub_eq_zero.mp hu).symm
  rw [heq, HahnSeries.orderTop_one] at hz
  have h := WithTop.coe_le_coe.mp hz
  omega

omit [Finite k] in
/-- The complete lower stationary chart in Laurent coordinates. The depth
condition is on the whole ideal and β retains every coefficient. -/
theorem residueSymbol_lowerChart (t r s : ℤ) (f z : k⸨X⸩)
    (hred : IsReducedAS f) (hr : 0 < r) (hdepth : t + 1 ≤ 2 * r)
    (hf : ((-t : ℤ) : WithTop ℤ) ≤ f.orderTop)
    (hz : (r : WithTop ℤ) ≤ z.orderTop) :
    (EqualChar.residueSymbol f
      (Units.mk0 (1 - z) (one_sub_ne_zero_of_order z r hr hz)) : ℂ) =
      scaledResiduePhase (s + 1) (originBeta s f * z) := by
  change binaryAddChar (EqualChar.residueExponent f (1 - z)) = _
  rw [residueExponent_stationary f z t r hr hdepth hf hz,
    derivative_eq_originBeta s f hred]
  simp only [scaledResiduePhase, mul_assoc]

/-- Finite descent removes every negative even coefficient. -/
theorem exists_no_negative_even_translate (f : k⸨X⸩) :
    ∃ w : k⸨X⸩, ∀ j : ℤ, j < 0 → Even j →
      (f + (w ^ 2 + w)).coeff j = 0 := by
  have aux (n : ℕ) : ∀ f : k⸨X⸩,
      ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ f.orderTop →
      ∃ w : k⸨X⸩, ∀ j : ℤ, j < 0 → Even j →
        (f + (w ^ 2 + w)).coeff j = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hf
      by_cases hn : n = 0
      · refine ⟨0, fun j hj _ ↦ ?_⟩
        simp only [zero_pow (by omega : 2 ≠ 0), add_zero]
        exact HahnSeries.coeff_eq_zero_of_lt_orderTop
          ((WithTop.coe_lt_coe.mpr hj).trans_le (by simpa [hn] using hf))
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      let s : k⸨X⸩ := single (-(n : ℤ)) (f.coeff (-(n : ℤ)))
      have hs : ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ s.orderTop :=
        HahnSeries.orderTop_single_le
      have hfs : ((-(n : ℤ) : ℤ) : WithTop ℤ) < (f + s).orderTop := by
        refine lt_of_le_of_ne
          ((le_min hf hs).trans HahnSeries.min_orderTop_le_orderTop_add) ?_
        exact (HahnSeries.orderTop_ne_of_coeff_eq_zero (by
          simp only [HahnSeries.coeff_add, s, HahnSeries.coeff_single_same]
          exact CharTwo.add_self_eq_zero _)).symm
      have hindex : -((n - 1 : ℕ) : ℤ) = -(n : ℤ) + 1 := by omega
      rcases Nat.even_or_odd n with ⟨q, hq⟩ | hodd
      · let c : k := (frobeniusEquiv k 2).symm (f.coeff (-(n : ℤ)))
        let v : k⸨X⸩ := single (-(q : ℤ)) c
        have hc : c ^ 2 = f.coeff (-(n : ℤ)) :=
          (frobeniusEquiv k 2).apply_symm_apply _
        have hvsq : v ^ 2 = s := by
          dsimp [v, s]
          rw [pow_two, HahnSeries.single_mul_single, ← pow_two, hc]
          rw [show -(q : ℤ) + -(q : ℤ) = -(n : ℤ) by omega]
        have hv : ((-(n : ℤ) : ℤ) : WithTop ℤ) < v.orderTop :=
          (WithTop.coe_lt_coe.mpr (by omega)).trans_le HahnSeries.orderTop_single_le
        have hnext : ((-((n - 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤
            (f + (v ^ 2 + v)).orderTop := by
          rw [hindex]
          apply next_order_bound
          rw [← add_assoc, hvsq]
          exact (lt_min hfs hv).trans_le HahnSeries.min_orderTop_le_orderTop_add
        obtain ⟨w, hw⟩ := ih (n - 1) (by omega) (f + (v ^ 2 + v)) hnext
        refine ⟨v + w, ?_⟩
        have heq : f + ((v + w) ^ 2 + (v + w)) =
            (f + (v ^ 2 + v)) + (w ^ 2 + w) := by
          rw [CharTwo.add_sq]
          abel
        rwa [heq]
      · obtain ⟨w, hw⟩ := ih (n - 1) (by omega) (f + s)
          (by rw [hindex]; exact next_order_bound hfs)
        refine ⟨w, fun j hj heven ↦ ?_⟩
        have hjne : j ≠ -(n : ℤ) := by
          obtain ⟨a, ha⟩ := heven
          obtain ⟨b, hb⟩ := hodd
          omega
        have hs0 : s.coeff j = 0 := HahnSeries.coeff_single_of_ne hjne
        simpa only [HahnSeries.coeff_add, hs0, add_zero] using hw j hj heven
  apply aux f.order.natAbs f
  by_cases hf : f = 0
  · simp [hf]
  · rw [← HahnSeries.order_eq_orderTop_of_ne_zero hf]
    exact WithTop.coe_le_coe.mpr (by
      have := Int.le_natAbs (a := -f.order)
      simp only [Int.natAbs_neg] at this
      omega)

omit [Finite k] in
/-- The polar terms of B cancel exactly, leaving its two constant contributions. -/
theorem originB_constant (s : ℤ) (f g : k⸨X⸩) :
    originBeta s f * g + originBeta s g * f =
      originBeta s f * HahnSeries.C (g.coeff 0) +
        originBeta s g * HahnSeries.C (f.coeff 0) := by
  simp only [originBeta, reducedNegativePart, CharTwo.sub_eq_add]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero]

omit [Finite k] in
/-- Both constant contributions to B are integral when the scaled parameters are. -/
theorem originB_integral (s : ℤ) (f g : k⸨X⸩)
    (hf : 0 ≤ (originBeta s f).orderTop) (hg : 0 ≤ (originBeta s g).orderTop) :
    0 ≤ (originBeta s f * g + originBeta s g * f).orderTop := by
  rw [originB_constant]
  apply le_trans (le_min ?_ ?_) HahnSeries.min_orderTop_le_orderTop_add
  · rw [HahnSeries.orderTop_mul]
    exact add_nonneg hf HahnSeries.orderTop_single_le
  · rw [HahnSeries.orderTop_mul]
    exact add_nonneg hg HahnSeries.orderTop_single_le

end Laurent

section OriginAlgebra
variable {R : Type*} [CommRing R] [CharP R 2]

/-- The paper's simultaneous numerator, with the stated order of the generators. -/
def simultaneousOrigin (d₁ d₂ z₁ z₂ : R) : R := d₁ * z₂ + d₂ * z₁

/-- The square identity underlying (D:EQ:exact-origin). -/
theorem simultaneousOrigin_square (d₁ d₂ z₁ z₂ f₁ f₂ : R)
    (h₁ : z₁ ^ 2 + z₁ = f₁) (h₂ : z₂ ^ 2 + z₂ = f₂) :
    simultaneousOrigin d₁ d₂ z₁ z₂ ^ 2 =
      d₁ ^ 2 * z₂ + d₂ ^ 2 * z₁ + (d₁ ^ 2 * f₂ + d₂ ^ 2 * f₁) := by
  have hz₁ : z₁ ^ 2 = f₁ + z₁ := by
    rw [← h₁, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hz₂ : z₂ ^ 2 = f₂ + z₂ := by
    rw [← h₂, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [simultaneousOrigin, CharTwo.add_sq, mul_pow, mul_pow, hz₁, hz₂]
  ring

/-- The three exact conjugate-product identities, with B and all κ factors.
These are algebraic inputs to identifying the genuine upper field norms. -/
theorem simultaneousOrigin_products (d₁ d₂ z₁ z₂ f₁ f₂ : R)
    (h₁ : z₁ ^ 2 + z₁ = f₁) (h₂ : z₂ ^ 2 + z₂ = f₂) :
    let Y := simultaneousOrigin d₁ d₂ z₁ z₂
    let B := d₁ ^ 2 * f₂ + d₂ ^ 2 * f₁
    Y * (Y + d₁) = d₂ * (d₁ + d₂) * z₁ + B ∧
      Y * (Y + d₂) = d₁ * (d₁ + d₂) * z₂ + B ∧
      Y * (Y + (d₁ + d₂)) = d₁ * d₂ * (z₁ + z₂) + B := by
  dsimp only
  have hs := simultaneousOrigin_square d₁ d₂ z₁ z₂ f₁ f₂ h₁ h₂
  have hprod (d : R) :
      simultaneousOrigin d₁ d₂ z₁ z₂ * (simultaneousOrigin d₁ d₂ z₁ z₂ + d) =
        (d₁ ^ 2 * z₂ + d₂ ^ 2 * z₁ + (d₁ ^ 2 * f₂ + d₂ ^ 2 * f₁)) +
          d * (d₁ * z₂ + d₂ * z₁) := by
    rw [mul_add, ← pow_two, hs, mul_comm _ d]
    rfl
  simp only [hprod]
  constructor
  · ring_nf
    simp [CharTwo.two_eq_zero]
  constructor
  · ring_nf
    simp [CharTwo.two_eq_zero]
  · ring_nf
    simp [CharTwo.two_eq_zero]

/-- The three displacement identities for the actual algebra automorphisms
with the paper's labeling. The third automorphism is their actual product. -/
theorem simultaneousOrigin_displacements
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (d₁ d₂ : F) (z₁ z₂ : K) (g₁ g₂ : Gal(K/F))
    (h₁₁ : g₁ z₁ = z₁) (h₁₂ : g₁ z₂ = z₂ + 1)
    (h₂₁ : g₂ z₁ = z₁ + 1) (h₂₂ : g₂ z₂ = z₂) :
    let Y := simultaneousOrigin (algebraMap F K d₁) (algebraMap F K d₂) z₁ z₂
    g₁ Y - Y = algebraMap F K d₁ ∧
      g₂ Y - Y = algebraMap F K d₂ ∧
      (g₁ * g₂) Y - Y = algebraMap F K (d₁ + d₂) := by
  dsimp only
  have h₁ : g₁ (simultaneousOrigin (algebraMap F K d₁) (algebraMap F K d₂) z₁ z₂) =
      simultaneousOrigin (algebraMap F K d₁) (algebraMap F K d₂) z₁ z₂ +
        algebraMap F K d₁ := by
    simp only [simultaneousOrigin, map_add, map_mul, g₁.commutes, h₁₁, h₁₂]
    ring
  have h₂ : g₂ (simultaneousOrigin (algebraMap F K d₁) (algebraMap F K d₂) z₁ z₂) =
      simultaneousOrigin (algebraMap F K d₁) (algebraMap F K d₂) z₁ z₂ +
        algebraMap F K d₂ := by
    simp only [simultaneousOrigin, map_add, map_mul, g₂.commutes, h₂₁, h₂₂]
    ring
  rw [h₁, h₂, AlgEquiv.mul_apply, h₂, map_add, g₁.commutes, h₁, map_add]
  constructor
  · ring
  constructor <;> ring

end OriginAlgebra

open private constructedNormCharacter_nontrivial from
  LanglandsSecondMainLemma.EqualChar.NormCharacter

open private hasSubst_of_order_eq from LanglandsSecondMainLemma.Residues.Substitution

open private integral_traceZero_is_artinSchreier residueField_charTwo from
  LanglandsSecondMainLemma.EqualChar.NormCharacter

section ActualField
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharP F 2]
local instance : CharP (ResidueField F) 2 := residueField_charTwo F
local instance : Algebra (ZMod 2) (ResidueField F) := ZMod.algebra _ 2

omit [CharP F 2] in
/-- Every fixed Laurent coefficient is locally constant in the actual field. -/
theorem laurentCoeff_locallyConstant (P : Residues.EqualCharacteristicPresentation F)
    (n : ℤ) : IsLocallyConstant (fun x : F ↦ (P.laurentEquiv.symm x).coeff n) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have hlat : (lattice F (n + 1) : Set F) ∈ nhds (0 : F) :=
    (lattice_isOpen F (n + 1)).mem_nhds (by simp)
  have hevent : ∀ᶠ y in nhds x, y - x ∈ lattice F (n + 1) := by
    have htend : Filter.Tendsto (fun y : F ↦ y - x) (nhds x) (nhds 0) := by
      have hcsub : Continuous (fun y : F ↦ y - x) := continuous_id.sub continuous_const
      have hat : ContinuousAt (fun y : F ↦ y - x) x := hcsub.continuousAt
      simpa only [ContinuousAt, sub_self] using hat
    exact htend.eventually hlat
  filter_upwards [hevent] with y hy
  have hord : ((n + 1 : ℤ) : WithTop ℤ) ≤
      (P.laurentEquiv.symm (y - x)).orderTop := by
    rw [← P.laurentEquiv_order, RingEquiv.apply_symm_apply]
    exact hy
  have hcoeff := HahnSeries.coeff_eq_zero_of_lt_orderTop
    ((WithTop.coe_lt_coe.mpr (by omega : n < n + 1)).trans_le hord)
  rw [map_sub, HahnSeries.coeff_sub] at hcoeff
  exact sub_eq_zero.mp hcoeff

/-- The paper's scaled canonical additive character, on the actual local field. -/
def originAddChar (P : Residues.EqualCharacteristicPresentation F) (T : ℤ) :
    ContinuousAddChar F := by
  let χ : AddChar F ℂˣ :=
    { toFun := fun x ↦ Units.mk0 (scaledResiduePhase T (P.laurentEquiv.symm x)) (by
        simp only [scaledResiduePhase, binaryAddChar_apply]
        exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      map_zero_eq_one' := by
        apply Units.ext
        simp [scaledResiduePhase, Residues.residue]
      map_add_eq_mul' := by
        intro x y
        apply Units.ext
        simp [scaledResiduePhase, mul_add, Residues.residue, AddChar.map_add_eq_mul] }
  refine ⟨χ, ?_⟩
  have hc := (laurentCoeff_locallyConstant F P (T - 1)).comp
    (fun a : ResidueField F ↦ Units.mk0
      (binaryAddChar (Algebra.trace (ZMod 2) (ResidueField F) a)) (by
        rw [binaryAddChar_apply]
        exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)))
  convert hc.continuous using 1
  funext x
  apply Units.ext
  simp [χ, scaledResiduePhase, Residues.residue, HahnSeries.coeff_single_mul,
    show (-1 : ℤ) - -T = T - 1 by omega]

@[simp] theorem originAddChar_apply (P : Residues.EqualCharacteristicPresentation F)
    (T : ℤ) (x : F) :
    (originAddChar F P T x : ℂ) = scaledResiduePhase T (P.laurentEquiv.symm x) := rfl

theorem originAddChar_square (P : Residues.EqualCharacteristicPresentation F)
    (T : ℤ) (hT : Even T) (x : F) : originAddChar F P T (x ^ 2) = 1 := by
  apply Units.ext
  simp only [originAddChar_apply, map_pow, scaledResiduePhase_square T hT,
    Units.val_one]

/-- The largest trivial ideal of Ψ is exactly the integer depth `T`. -/
theorem originAddChar_conductor (P : Residues.EqualCharacteristicPresentation F)
    (T : ℤ) : IsAdditiveConductor F (originAddChar F P T) (-T) := by
  have htriv : AddCharTrivialOnLattice F (originAddChar F P T) T := by
    intro x hx
    apply Units.ext
    have hord : (T : WithTop ℤ) ≤ (P.laurentEquiv.symm x).orderTop := by
      rw [← P.laurentEquiv_order, RingEquiv.apply_symm_apply]
      exact hx
    have hc := HahnSeries.coeff_eq_zero_of_lt_orderTop
      ((WithTop.coe_lt_coe.mpr (by omega : T - 1 < T)).trans_le hord)
    simp [originAddChar_apply, scaledResiduePhase, Residues.residue,
      HahnSeries.coeff_single_mul, show (-1 : ℤ) - -T = T - 1 by omega, hc]
  refine ⟨by simpa using htriv, ?_⟩
  intro r hr
  by_contra hle
  have hrT : r ≤ T - 1 := by omega
  letI := residueFieldFintype F
  obtain ⟨c, hc⟩ := exists_absoluteTraceTwo_mul_eq_one (ResidueField F)
    (show (1 : ResidueField F) ≠ 0 from one_ne_zero)
  simp only [one_mul] at hc
  change Algebra.trace (ZMod 2) (ResidueField F) c = 1 at hc
  let x := P.laurentEquiv (single (T - 1) c)
  have hx : x ∈ lattice F r := by
    change (r : WithTop ℤ) ≤ ord F x
    rw [P.laurentEquiv_order]
    exact (WithTop.coe_le_coe.mpr hrT).trans HahnSeries.orderTop_single_le
  have hval := congrArg (fun u : ℂˣ ↦ (u : ℂ)) (hr x hx)
  have hphase : (originAddChar F P T x : ℂ) = -1 := by
    simp only [x, originAddChar_apply, RingEquiv.symm_apply_apply, scaledResiduePhase,
      HahnSeries.single_mul_single, one_mul, show -T + (T - 1) = (-1 : ℤ) by omega,
      Residues.residue, HahnSeries.coeff_single_same, hc]
    norm_num [binaryAddChar_apply, ZMod.val_one]
  rw [hphase, Units.val_one] at hval
  norm_num at hval

/-- The AS residue symbol is independent of the chosen uniformizer. Both
presentations use the canonical coefficient field of the actual local field. -/
theorem residueExponent_changePresentation
    (P Q : Residues.EqualCharacteristicPresentation F) (f v : F) :
    EqualChar.residueExponent (P.laurentEquiv.symm f) (P.laurentEquiv.symm v) =
      EqualChar.residueExponent (Q.laurentEquiv.symm f) (Q.laurentEquiv.symm v) := by
  let φ := P.laurentEquiv.symm.toRingHom.comp Q.laurentEquiv.toRingHom
  have horder (a : (ResidueField F)⸨X⸩) : (φ a).orderTop = a.orderTop := by
    rw [← P.laurentEquiv_order]
    change ord F (P.laurentEquiv (P.laurentEquiv.symm (Q.laurentEquiv a))) = _
    rw [RingEquiv.apply_symm_apply, Q.laurentEquiv_order]
  have hC (a : ResidueField F) : φ (HahnSeries.C a) = HahnSeries.C a := by
    apply P.laurentEquiv.injective
    change P.laurentEquiv (P.laurentEquiv.symm (Q.laurentEquiv (HahnSeries.C a))) = _
    rw [RingEquiv.apply_symm_apply, P.laurentEquiv_C, Q.laurentEquiv_C,
      P.coefficient_eq_teichmuller, Q.coefficient_eq_teichmuller]
  let w := φ (single 1 1)
  have hw : w.orderTop = 1 := by rw [horder]; exact HahnSeries.orderTop_single one_ne_zero
  let u : (ResidueField F)⟦X⟧ := PowerSeries.mk (fun n ↦ w.coeff (n : ℤ))
  have hucoe : (u : (ResidueField F)⸨X⸩) = w := by
    ext n
    rw [PowerSeries.coeff_coe]
    split_ifs with hn
    · exact (HahnSeries.coeff_eq_zero_of_lt_orderTop
        (by rw [hw]; exact WithTop.coe_lt_coe.mpr (by omega))).symm
    · simp [u, abs_of_nonneg (by omega : 0 ≤ n)]
  have hu : u.order = (1 : ℕ) := by
    apply PowerSeries.order_eq_nat.mpr
    constructor
    · simpa [u] using HahnSeries.coeff_orderTop_ne hw
    · intro i hi
      have hi0 : i = 0 := by omega
      subst i
      simp only [u, PowerSeries.coeff_mk, Nat.cast_zero]
      exact HahnSeries.coeff_eq_zero_of_lt_orderTop (by rw [hw]; norm_num)
  have hsubst := hasSubst_of_order_eq u 1 (by omega) hu
  have hφ : Residues.IsLaurentSubstitution 1 (RingHom.id (ResidueField F))
      (u : (ResidueField F)⸨X⸩) φ := by
    refine ⟨fun a ↦ ?_, hucoe.symm, fun a ↦ ?_⟩
    · exact hC a
    · simpa only [one_nsmul] using horder a
  have hformal : φ = Residues.formalSubstitution u 1 (by omega) hu := by
    apply IsFractionRing.ringHom_ext (A := PowerSeries (ResidueField F))
    intro p
    change φ (p : (ResidueField F)⸨X⸩) =
      Residues.formalSubstitution u 1 (by omega) hu (p : (ResidueField F)⸨X⸩)
    rw [substitution_powerSeries 1 (by omega) (RingHom.id _) u hsubst φ hφ p,
      Residues.formalSubstitution_coe]
    simp
  have hchain (a : (ResidueField F)⸨X⸩) :
      EqualChar.logarithmicDerivative (φ a) =
        φ (EqualChar.logarithmicDerivative a) *
          (PowerSeries.derivative (ResidueField F) u : (ResidueField F)⸨X⸩) := by
    rw [EqualChar.logarithmicDerivative,
      laurentDerivative_substitution 1 (by omega) (RingHom.id _) u hsubst φ hφ a,
      EqualChar.logarithmicDerivative, map_mul, map_inv₀]
    ring
  have hcoords (a : F) : φ (Q.laurentEquiv.symm a) = P.laurentEquiv.symm a := by
    simp [φ]
  rw [← hcoords f, ← hcoords v, EqualChar.residueExponent, hchain,
    ← mul_assoc, ← map_mul, hformal, Residues.change_uniformizer]
  rfl

/-- Every AS class of the genuine local field has a fully reduced Laurent
representative. Positive depth is removed by the accepted local Newton theorem. -/
theorem exists_reducedAS_translate (P : Residues.EqualCharacteristicPresentation F)
    (f : (ResidueField F)⸨X⸩) :
    ∃ w : (ResidueField F)⸨X⸩, IsReducedAS (f + (w ^ 2 + w)) := by
  obtain ⟨w, hw⟩ := exists_no_negative_even_translate f
  let g := f + (w ^ 2 + w)
  let h := HahnSeries.truncLT 1 g
  let a := g - h
  have ha : 0 ≤ a.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro n hn
    have hn0 : n < 0 := by exact_mod_cast hn
    simp [a, h, HahnSeries.coeff_truncLT_of_lt (by omega : n < 1)]
  have ha0 : a.coeff 0 = 0 := by
    simp [a, h, HahnSeries.coeff_truncLT_of_lt (by omega : (0 : ℤ) < 1)]
  obtain ⟨b, hb⟩ := integral_traceZero_is_artinSchreier F P a ha (by rw [ha0, map_zero])
  have heq : f + ((w + b) ^ 2 + (w + b)) = h := by
    rw [CharTwo.add_sq]
    calc
      _ = g + (b ^ 2 + b) := by dsimp [g]; abel
      _ = h := by rw [hb]; dsimp [a]; rw [CharTwo.sub_eq_add,
        ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  refine ⟨w + b, ?_⟩
  rw [heq]
  intro n hn hcase
  rcases hcase with hpos | heven
  · exact HahnSeries.coeff_truncLT_of_le (by omega) _
  · by_cases hpos : 0 < n
    · exact HahnSeries.coeff_truncLT_of_le (by omega) _
    · have hneg : n < 0 := by omega
      change (HahnSeries.truncLT 1 g).coeff n = 0
      rw [HahnSeries.coeff_truncLT_of_lt (by omega : n < 1)]
      exact hw n hneg heven

end ActualField

open private exists_artinSchreier_generator artinSchreier_parameter_negative
  automorphism_mem_lowerGroup_at_reducedPole automorphism_not_mem_lowerGroup_after_reducedPole from
  LanglandsFirstMainLemma.Cases.WildQuadratic.EqualCharacteristicBreak

section QuadraticGenerator
variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E]
  [Module.Free F E] [Module.Finite F E] [IsGalois F E] [CharP F 2]
local instance : CharP (ResidueField F) 2 := residueField_charTwo F

omit [CharP F 2] in
/-- The pole of a reduced quadratic generator is its actual ramification
break, and the actual different has exponent `t + 1`. -/
theorem reducedAS_break_different (hdegree : Module.finrank F E = 2)
    (hres : residueDegree F E = 1) (sigma : Gal(E/F)) (hsigma : sigma ≠ 1)
    (z : E) (t : ℕ) (hodd : Odd t) (hz : sigma z = z + 1)
    (hord : ord E z = ((-(t : ℤ) : ℤ) : WithTop ℤ)) :
    PrimeCyclicExtension.IsLowerBreak F E t ∧ differentExponent F E = t + 1 := by
  have hcard : Nat.card Gal(E/F) = 2 := (IsGalois.card_aut_eq_finrank F E).trans hdegree
  obtain ⟨tau, _htau, huniq⟩ := (Nat.card_eq_two_iff' (1 : Gal(E/F))).mp hcard
  have huniq' (g : Gal(E/F)) (hg : g ≠ 1) : g = sigma :=
    (huniq g hg).trans (huniq sigma hsigma).symm
  have hram : ramificationIndex F E = 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa [hdegree, hres] using h.symm
  have hmem := automorphism_mem_lowerGroup_at_reducedPole F E hdegree hram sigma z t
    hodd hz hord
  have hnot := automorphism_not_mem_lowerGroup_after_reducedPole F E hram sigma z t
    hodd hz hord
  have hbreak : PrimeCyclicExtension.IsLowerBreak F E t := by
    constructor
    · apply eq_top_iff.mpr
      intro g _
      by_cases hg : g = 1
      · simp [hg]
      · rw [huniq' g hg]
        exact hmem
    · apply eq_bot_iff.mpr
      intro g hg
      change g = 1
      by_contra hne
      rw [huniq' g hne] at hg
      exact hnot hg
  letI : IsCyclic Gal(E/F) := isCyclic_of_prime_card hcard
  letI : PrimeCyclicExtension F E :=
    ⟨inferInstance, inferInstance, by simpa [hdegree] using Nat.prime_two⟩
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  exact ⟨hbreak, differentExponent_wildQuadratic_eq F E hbreak hdegree pi hpi hgen⟩

/-- Recover the positive odd pole and actual break of a specified reduced
generator. This also applies to the third generator `z₁ + z₂`, without
changing that representative. -/
theorem reducedAS_generator_data (hdegree : Module.finrank F E = 2)
    (hres : residueDegree F E = 1) (P : Residues.EqualCharacteristicPresentation F)
    (sigma : Gal(E/F)) (hsigma : sigma ≠ 1) (z : E) (f : F)
    (hz : sigma z = z + 1) (hf : z ^ 2 + z = algebraMap F E f)
    (hred : IsReducedAS (P.laurentEquiv.symm f)) :
    ∃ t : ℕ, 0 < t ∧ Odd t ∧
      ord E z = ((-(t : ℤ) : ℤ) : WithTop ℤ) ∧
      (P.laurentEquiv.symm f).orderTop = ((-(t : ℤ) : ℤ) : WithTop ℤ) ∧
      PrimeCyclicExtension.IsLowerBreak F E t ∧ differentExponent F E = t + 1 := by
  letI : CharP E 2 := charP_of_injective_algebraMap (algebraMap F E).injective 2
  have hram : ramificationIndex F E = 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa [hdegree, hres] using h.symm
  have hsigma0 : sigma ∈ lowerRamificationGroup F E 0 := by
    rw [lowerRamificationGroup_zero_eq_top_of_residueDegree_eq_one F E hres]
    exact Subgroup.mem_top _
  obtain ⟨n, hn, hzn, hfn⟩ := artinSchreier_parameter_negative F E sigma hram hsigma0
    z f hz (by rwa [CharTwo.sub_eq_add])
  have hcoordOrder : (P.laurentEquiv.symm f).orderTop = (n : WithTop ℤ) := by
    rw [← P.laurentEquiv_order, RingEquiv.apply_symm_apply, hfn]
  have hodd : Odd n := by
    rcases Int.even_or_odd n with heven | hodd
    · exact (HahnSeries.coeff_orderTop_ne hcoordOrder
        (hred n (by omega) (Or.inr heven))).elim
    · exact hodd
  let t := (-n).toNat
  have ht : (t : ℤ) = -n := Int.toNat_of_nonneg (by omega)
  have htodd : Odd t := by
    have h : Odd (t : ℤ) := by rw [ht]; exact hodd.neg
    exact_mod_cast h
  have hzord : ord E z = ((-(t : ℤ) : ℤ) : WithTop ℤ) := by simpa [ht] using hzn
  exact ⟨t, by omega, htodd, hzord, by simpa [ht] using hcoordOrder,
    reducedAS_break_different F E hdegree hres sigma hsigma z t htodd hz hzord⟩

/-- A fully reduced AS generator is constructed from a genuine totally ramified
quadratic local extension, in any chosen base Laurent presentation. Both orders
and the odd positive pole are proved, with no reducedness assumption. -/
theorem exists_reducedAS_generator (hdegree : Module.finrank F E = 2)
    (hres : residueDegree F E = 1) (P : Residues.EqualCharacteristicPresentation F) :
    ∃ (sigma : Gal(E/F)) (z : E) (f : F) (t : ℕ),
      sigma ≠ 1 ∧ sigma z = z + 1 ∧ z ^ 2 + z = algebraMap F E f ∧
      z ∉ Set.range (algebraMap F E) ∧
      IsReducedAS (P.laurentEquiv.symm f) ∧ 0 < t ∧ Odd t ∧
      ord E z = ((-(t : ℤ) : ℤ) : WithTop ℤ) ∧
      (P.laurentEquiv.symm f).orderTop = ((-(t : ℤ) : ℤ) : WithTop ℤ) ∧
      PrimeCyclicExtension.IsLowerBreak F E t ∧ differentExponent F E = t + 1 := by
  letI : CharP E 2 := charP_of_injective_algebraMap (algebraMap F E).injective 2
  obtain ⟨sigma, z₀, f₀, hsigma, hz₀, hf₀⟩ := exists_artinSchreier_generator F E hdegree
  obtain ⟨w, hw⟩ := exists_reducedAS_translate F P (P.laurentEquiv.symm f₀)
  let a := P.laurentEquiv w
  let z := z₀ + algebraMap F E a
  let f := f₀ + (a ^ 2 + a)
  have hz : sigma z = z + 1 := by simp [z, hz₀, add_assoc, add_comm, add_left_comm]
  have hf : z ^ 2 + z = algebraMap F E f := by
    dsimp [z, f]
    rw [CharTwo.add_sq]
    calc
      _ = (z₀ ^ 2 + z₀) + ((algebraMap F E a) ^ 2 + algebraMap F E a) := by abel
      _ = _ := by
        rw [CharTwo.sub_eq_add] at hf₀
        rw [hf₀, map_add, map_add, map_pow]
  have hcoords : P.laurentEquiv.symm f =
      P.laurentEquiv.symm f₀ + (w ^ 2 + w) := by simp [f, a]
  have hred : IsReducedAS (P.laurentEquiv.symm f) := by rwa [hcoords]
  have hgen : z ∉ Set.range (algebraMap F E) := by
    rintro ⟨b, hb⟩
    rw [← hb, sigma.commutes] at hz
    exact one_ne_zero (add_eq_left.mp hz.symm)
  obtain ⟨t, ht⟩ := reducedAS_generator_data F E hdegree hres P sigma hsigma z f hz hf hred
  exact ⟨sigma, z, f, t, hsigma, hz, hf, hgen, hred, ht⟩

end QuadraticGenerator

section QuadraticChart
variable (F E : Type) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E]
  [Module.Free F E] [Module.Finite F E] [IsGalois F E] [CharP F 2]
local instance : CharP (ResidueField F) 2 := residueField_charTwo F

/-- The presentation used by the accepted actual norm-character formula. -/
def quadraticOriginPresentation : Residues.EqualCharacteristicPresentation F :=
  (Classical.choice (Residues.exists_equalCharacteristicExtensionPresentation
    F E (EqualChar.equalCharacteristicTwo F))).base

omit [Module.Free F E] in
/-- The complete stationary chart for the actual continuous quadratic norm
character. The parameter and all of β are retained in the fixed Laurent coordinates. -/
theorem constructedNormCharacter_lowerChart (hdegree : Module.finrank F E = 2)
    (P : Residues.EqualCharacteristicPresentation F)
    (f : F) (z : E) (hz : z ^ 2 + z = algebraMap F E f)
    (t r s : ℤ) (hr : 0 < r) (hdepth : t + 1 ≤ 2 * r)
    (hred : IsReducedAS (P.laurentEquiv.symm f))
    (hf : ((-t : ℤ) : WithTop ℤ) ≤ ord F f)
    (u : Fˣ) (hu : 1 - (u : F) ∈ lattice F r) :
    (EqualChar.constructedNormCharacter F E hdegree f z hz).1 u =
      originAddChar F P (s + 1)
        (P.laurentEquiv
          (originBeta s (P.laurentEquiv.symm f)) *
          (1 - (u : F))) := by
  let x := P.laurentEquiv.symm (1 - (u : F))
  have hx : (r : WithTop ℤ) ≤ x.orderTop := by
    rw [← P.laurentEquiv_order, RingEquiv.apply_symm_apply]
    exact hu
  have hf' : ((-t : ℤ) : WithTop ℤ) ≤ (P.laurentEquiv.symm f).orderTop := by
    rw [← P.laurentEquiv_order, RingEquiv.apply_symm_apply]
    exact hf
  have hchart := residueSymbol_lowerChart t r s (P.laurentEquiv.symm f) x
    hred hr hdepth hf' hx
  have hunit : 1 - x = P.laurentEquiv.symm (u : F) := by simp [x]
  apply Units.ext
  rw [EqualChar.constructedNormCharacter_apply, originAddChar_apply]
  change binaryAddChar (EqualChar.residueExponent
    ((quadraticOriginPresentation F E).laurentEquiv.symm f)
    ((quadraticOriginPresentation F E).laurentEquiv.symm (u : F))) = _
  rw [residueExponent_changePresentation F (quadraticOriginPresentation F E) P f (u : F)]
  change binaryAddChar (EqualChar.residueExponent (P.laurentEquiv.symm f) (1 - x)) = _ at hchart
  rw [hunit] at hchart
  simpa only [map_mul, RingEquiv.symm_apply_apply] using hchart

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeExtension F E] [Module.Finite F E] [IsGalois F E] in
/-- The exact coefficient β is a genuine lower norm, by its constructed
square root and the degree-two norm of a scalar. -/
theorem originBeta_actualNorm (hdegree : Module.finrank F E = 2)
    (P : Residues.EqualCharacteristicPresentation F)
    (s : ℤ) (hs : Odd s) (f : (ResidueField F)⸨X⸩) (hf : IsReducedAS f) :
    Algebra.norm F (algebraMap F E (P.laurentEquiv (evenSquareRoot (originBeta s f)))) =
      P.laurentEquiv (originBeta s f) := by
  rw [Algebra.norm_algebraMap, hdegree, ← map_pow, originBeta_square s hs f hf]

omit [IsGalois F E] in
/-- Triviality of every actual norm character at the full nonzero coefficient β. -/
theorem normCharacter_originBeta (hdegree : Module.finrank F E = 2)
    (P : Residues.EqualCharacteristicPresentation F)
    (s : ℤ) (hs : Odd s) (f : (ResidueField F)⸨X⸩) (hf : IsReducedAS f)
    (hβ : P.laurentEquiv (originBeta s f) ≠ 0) (ω : NormCharacter F E) :
    ω.1 (Units.mk0 (P.laurentEquiv (originBeta s f)) hβ) = 1 := by
  have hnorm := originBeta_actualNorm F E hdegree P s hs f hf
  let d := algebraMap F E (P.laurentEquiv (evenSquareRoot (originBeta s f)))
  have hd : d ≠ 0 := by
    intro hd0
    apply hβ
    rw [← hnorm]
    change Algebra.norm F d = 0
    rw [hd0, Algebra.norm_zero]
  apply ω.eq_one_on_normRange F E
  refine ⟨Units.mk0 d hd, ?_⟩
  apply Units.ext
  exact hnorm

/-- Exact trace-to-norm phase conversion on the whole upper ideal. The
numerical bound uses the actual different exponent; no norm surjectivity is used. -/
theorem originAddChar_normPhase (hdegree : Module.finrank F E = 2)
    (hres : residueDegree F E = 1)
    (P : Residues.EqualCharacteristicPresentation F)
    (f : F) (z : E) (hz : z ^ 2 + z = algebraMap F E f)
    (t r s : ℤ) (hr : 0 < r) (hdepth : t + 1 ≤ 2 * r)
    (hD : r ≤ (differentExponent F E : ℤ))
    (hred : IsReducedAS (P.laurentEquiv.symm f))
    (hf : ((-t : ℤ) : WithTop ℤ) ≤ ord F f)
    (x : E) (hx : x ∈ lattice E r) :
    let β := P.laurentEquiv (originBeta s (P.laurentEquiv.symm f))
    let Ψ := originAddChar F P (s + 1)
    tracePullbackAddChar F E Ψ (algebraMap F E β * x) =
      Ψ (β * Algebra.norm F x) := by
  letI : CharP E 2 := charP_of_injective_algebraMap (algebraMap F E).injective 2
  let β := P.laurentEquiv (originBeta s (P.laurentEquiv.symm f))
  let Ψ := originAddChar F P (s + 1)
  have hram : ramificationIndex F E = 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa [hdegree, hres] using h.symm
  have hn : Algebra.norm F x ∈ lattice F r := by
    change (r : WithTop ℤ) ≤ ord F (norm F E x)
    rw [ord_norm, hres, one_nsmul]
    exact hx
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have ht : Algebra.trace F E x ∈ lattice F r := by
    have h := trace_mem_lattice_floor F E pi hpi hgen r hx
    exact (lattice_antitone F (by rw [hram]; norm_num; omega)) h
  have he₂ : elementarySymmetric F E 2 x = norm F E x := by
    rw [← hdegree, elementarySymmetric_finrank]
  have hnorm : Algebra.norm F (1 - x) = 1 + Algebra.trace F E x + Algebra.norm F x := by
    rw [CharTwo.sub_eq_add]
    change norm F E (1 + x) = _
    rw [norm_one_add_eq_sum_elementarySymmetric, hdegree]
    simp [Finset.sum_range_succ, he₂]
  have hnonzero : 1 - x ≠ 0 := by
    intro hzero
    have heq : x = 1 := (sub_eq_zero.mp hzero).symm
    have h := hx
    change (r : WithTop ℤ) ≤ ord E x at h
    rw [heq, ord_one] at h
    have h' := WithTop.coe_le_coe.mp h
    omega
  let u := normUnits F E (Units.mk0 (1 - x) hnonzero)
  have hu : 1 - (u : F) = Algebra.trace F E x + Algebra.norm F x := by
    change 1 - Algebra.norm F (1 - x) = _
    rw [hnorm, CharTwo.sub_eq_add]
    simp only [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hulat : 1 - (u : F) ∈ lattice F r := by
    rw [hu]
    exact (lattice F r).add_mem ht hn
  have hchart := constructedNormCharacter_lowerChart F E hdegree P f z hz
    t r s hr hdepth hred hf u hulat
  have huone : (EqualChar.constructedNormCharacter F E hdegree f z hz).1 u = 1 :=
    (EqualChar.constructedNormCharacter F E hdegree f z hz).eq_one_on_normRange F E u
      ⟨Units.mk0 (1 - x) hnonzero, rfl⟩
  change _ = Ψ (β * (1 - (u : F))) at hchart
  rw [huone, hu, mul_add, ContinuousAddChar.map_add_eq_mul] at hchart
  have hsquare : Ψ (β * Algebra.norm F x) * Ψ (β * Algebra.norm F x) = 1 := by
    rw [← ContinuousAddChar.map_add_eq_mul, CharTwo.add_self_eq_zero,
      ContinuousAddChar.map_zero_eq_one]
  have hphase : Ψ (β * Algebra.trace F E x) = Ψ (β * Algebra.norm F x) := by
    apply mul_right_cancel (b := Ψ (β * Algebra.norm F x))
    exact hchart.symm.trans hsquare.symm
  change Ψ (Algebra.trace F E (algebraMap F E β * x)) = _
  rw [← Algebra.smul_def, map_smul, Algebra.smul_def, Algebra.algebraMap_self_apply]
  exact hphase

/-- A complete quadratic-edge constructor from the genuine local extension.
It supplies the reduced parameter, actual norm character, exact norm coefficient,
full lower chart, and whole-ideal phase conversion for every larger odd common
pole. The three-edge simultaneous-origin assembly remains separate. -/
theorem quadratic_origin_exists (hdegree : Module.finrank F E = 2)
    (hres : residueDegree F E = 1) (P : Residues.EqualCharacteristicPresentation F) :
    ∃ (f : F) (z : E) (t : ℕ) (ω : NormCharacter F E),
      z ^ 2 + z = algebraMap F E f ∧
      IsReducedAS (P.laurentEquiv.symm f) ∧ 0 < t ∧ Odd t ∧
      ord E z = ((-(t : ℤ) : ℤ) : WithTop ℤ) ∧
      ord F f = ((-(t : ℤ) : ℤ) : WithTop ℤ) ∧
      PrimeCyclicExtension.IsLowerBreak F E t ∧ differentExponent F E = t + 1 ∧
      ω ≠ 1 ∧ IsMultiplicativeConductor F ω.1 (t + 1) ∧
      ∀ s : ℤ, Odd s → (t : ℤ) ≤ s →
        let β := P.laurentEquiv (originBeta s (P.laurentEquiv.symm f))
        let d := P.laurentEquiv (evenSquareRoot (originBeta s (P.laurentEquiv.symm f)))
        let r : ℤ := ((t : ℤ) + 1) / 2
        let Ψ := originAddChar F P (s + 1)
        d ^ 2 = β ∧ ord F d = (((s - (t : ℤ)) / 2 : ℤ) : WithTop ℤ) ∧
        β ∈ lattice F 0 ∧ Algebra.norm F (algebraMap F E d) = β ∧
        (∃ hβ : β ≠ 0, ω.1 (Units.mk0 β hβ) = 1) ∧
        (∀ u : Fˣ, 1 - (u : F) ∈ lattice F r → ω.1 u = Ψ (β * (1 - (u : F)))) ∧
        (∀ x : E, x ∈ lattice E r →
          tracePullbackAddChar F E Ψ (algebraMap F E β * x) = Ψ (β * Algebra.norm F x)) := by
  obtain ⟨sigma, z, f, t, _hsigma, _hsigmaz, hz, hgen, hred, ht, hodd, hzord, hford,
      hbreak, hdiff⟩ := exists_reducedAS_generator F E hdegree hres P
  let ω := EqualChar.constructedNormCharacter F E hdegree f z hz
  have hω : ω ≠ 1 := constructedNormCharacter_nontrivial F E hdegree f z hz hgen
  have hfordF : ord F f = ((-(t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [← hford, ← P.laurentEquiv_order, RingEquiv.apply_symm_apply]
  have hford₀ : ((quadraticOriginPresentation F E).laurentEquiv.symm f).orderTop =
      ((-(t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [← (quadraticOriginPresentation F E).laurentEquiv_order,
      RingEquiv.apply_symm_apply, hfordF]
  have hconductor : IsMultiplicativeConductor F ω.1 (t + 1) :=
    EqualChar.constructedNormCharacter_conductor F E hdegree f z hz t ht hodd hford₀
  refine ⟨f, z, t, ω, hz, hred, ht, hodd, hzord, hfordF, hbreak, hdiff, hω, hconductor, ?_⟩
  intro s hs hts
  let β := P.laurentEquiv (originBeta s (P.laurentEquiv.symm f))
  let d := P.laurentEquiv (evenSquareRoot (originBeta s (P.laurentEquiv.symm f)))
  let r : ℤ := ((t : ℤ) + 1) / 2
  have htodd : Odd (t : ℤ) := by exact_mod_cast hodd
  have hr : 0 < r := by dsimp [r]; omega
  have hdepth : (t : ℤ) + 1 ≤ 2 * r := by
    obtain ⟨a, ha⟩ := htodd
    dsimp [r]
    omega
  have hD : r ≤ (differentExponent F E : ℤ) := by rw [hdiff]; dsimp [r]; omega
  have hdelta : s - (t : ℤ) = 2 * ((s - (t : ℤ)) / 2) := by
    obtain ⟨a, ha⟩ := hs
    obtain ⟨b, hb⟩ := htodd
    omega
  have hβord : ord F β = ((s - (t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [P.laurentEquiv_order]
    exact originBeta_order t s _ (by omega) hford
  have hβ : β ≠ 0 := by
    intro hzβ
    rw [hzβ, ord_zero] at hβord
    exact WithTop.top_ne_coe hβord
  refine ⟨?_, ?_, ?_, originBeta_actualNorm F E hdegree P s hs _ hred,
    ⟨hβ, normCharacter_originBeta F E hdegree P s hs _ hred hβ ω⟩, ?_, ?_⟩
  · change d ^ 2 = β
    rw [← map_pow, originBeta_square s hs _ hred]
  · rw [P.laurentEquiv_order]
    exact originSquareRoot_order t s ((s - (t : ℤ)) / 2) _ (by omega) hs hdelta hred hford
  · change (0 : WithTop ℤ) ≤ ord F β
    rw [hβord]
    exact WithTop.coe_le_coe.mpr (by omega)
  · intro u hu
    exact constructedNormCharacter_lowerChart F E hdegree P f z hz t r s hr hdepth
      hred hfordF.ge u hu
  · intro x hx
    exact originAddChar_normPhase F E hdegree hres P f z hz t r s hr hdepth hD
      hred hfordF.ge x hx

end QuadraticChart

open private quadraticNormCharacter_unique from
  LanglandsSecondMainLemma.EqualChar.NormCharacter

section LowerCharts
variable (F E : Type) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E]
  [Module.Free F E] [Module.Finite F E] [IsGalois F E] [CharP F 2]
local instance : CharP (ResidueField F) 2 := residueField_charTwo F

/-- The full lower charts (D:EQ:lowerchart) and (D:EQ:normphase), for each
actual quadratic edge and its actual nontrivial norm character. The same
odd common pole `s` may be used on all three edges. The additive conductor
is recorded with FML's sign convention: the largest trivial ideals have
depths `s + 1` and `2 * (s + 1) - (t + 1)`, respectively. -/
theorem dyadicEqual_lowerCharts (hdegree : Module.finrank F E = 2)
    (hres : residueDegree F E = 1) (P : Residues.EqualCharacteristicPresentation F)
    (f : F) (z : E) (hz : z ^ 2 + z = algebraMap F E f)
    (hgen : z ∉ Set.range (algebraMap F E))
    (t : ℕ) (ht : 0 < t) (hodd : Odd t)
    (hred : IsReducedAS (P.laurentEquiv.symm f))
    (hf : ord F f = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hdiff : differentExponent F E = t + 1)
    (ω : NormCharacter F E) (hω : ω ≠ 1) (s : ℤ) (hs : Odd s) :
    let β := P.laurentEquiv (originBeta s (P.laurentEquiv.symm f))
    let r : ℤ := ((t : ℤ) + 1) / 2
    let Ψ := originAddChar F P (s + 1)
    IsMultiplicativeConductor F ω.1 (t + 1) ∧
      IsAdditiveConductor F Ψ (-(s + 1)) ∧
      IsAdditiveConductor E (tracePullbackAddChar F E Ψ)
        (-(2 * (s + 1) - ((t : ℤ) + 1))) ∧
      (∀ x : F, Ψ (x ^ 2) = 1) ∧
      (∃ hβ : β ≠ 0, ω.1 (Units.mk0 β hβ) = 1) ∧
      (∀ u : Fˣ, 1 - (u : F) ∈ lattice F r →
        ω.1 u = Ψ (β * (1 - (u : F)))) ∧
      (∀ x : E, x ∈ lattice E r →
        tracePullbackAddChar F E Ψ (algebraMap F E β * x) =
          Ψ (β * Algebra.norm F x)) := by
  have hωeq : ω = EqualChar.constructedNormCharacter F E hdegree f z hz :=
    quadraticNormCharacter_unique F E hdegree _ _ hω
      (constructedNormCharacter_nontrivial F E hdegree f z hz hgen)
  subst ω
  let r : ℤ := ((t : ℤ) + 1) / 2
  have htodd : Odd (t : ℤ) := by exact_mod_cast hodd
  have hr : 0 < r := by dsimp [r]; omega
  have hdepth : (t : ℤ) + 1 ≤ 2 * r := by
    obtain ⟨a, ha⟩ := htodd
    dsimp [r]
    omega
  have hD : r ≤ (differentExponent F E : ℤ) := by rw [hdiff]; dsimp [r]; omega
  have hram : ramificationIndex F E = 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa [hdegree, hres] using h.symm
  have hfP : (P.laurentEquiv.symm f).orderTop = ((-(t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [← P.laurentEquiv_order, RingEquiv.apply_symm_apply, hf]
  have hf₀ : ((quadraticOriginPresentation F E).laurentEquiv.symm f).orderTop =
      ((-(t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [← (quadraticOriginPresentation F E).laurentEquiv_order,
      RingEquiv.apply_symm_apply, hf]
  have hβ : P.laurentEquiv (originBeta s (P.laurentEquiv.symm f)) ≠ 0 := by
    intro hzero
    have hord := originBeta_order t s _ (by omega) hfP
    have heq := P.laurentEquiv_order (originBeta s (P.laurentEquiv.symm f))
    rw [hzero, ord_zero, hord] at heq
    exact WithTop.top_ne_coe heq
  refine ⟨EqualChar.constructedNormCharacter_conductor F E hdegree f z hz
      t ht hodd hf₀, originAddChar_conductor F P (s + 1), ?_, ?_,
    ⟨hβ, normCharacter_originBeta F E hdegree P s hs _ hred hβ _⟩,
    fun u hu ↦ constructedNormCharacter_lowerChart F E hdegree P f z hz
      t r s hr hdepth hred hf.ge u hu,
    fun x hx ↦ originAddChar_normPhase F E hdegree hres P f z hz
      t r s hr hdepth hD hred hf.ge x hx⟩
  · have h := Local.additiveConductor_trace_fml F E hres
      (originAddChar_conductor F P (s + 1))
    rw [hram, hdiff] at h
    convert h using 1 <;> first | rfl | (push_cast; ring)
  · exact originAddChar_square F P (s + 1) (by
      obtain ⟨a, ha⟩ := hs
      exact ⟨a + 1, by omega⟩)

end LowerCharts

section DiamondGroup
variable {G : Type*} [Group G] [IsKleinFour G]

/-- The actual order-two subgroup fixing one quadratic intermediate field. -/
def originLine (g : G) : Subgroup G where
  carrier := {x | x = 1 ∨ x = g}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro x y (rfl | rfl) (rfl | rfl) <;> simp [IsKleinFour.mul_self]
  inv_mem' := by
    rintro x (rfl | rfl) <;> simp [IsKleinFour.inv_eq_self]

@[simp] theorem mem_originLine (g x : G) : x ∈ originLine g ↔ x = 1 ∨ x = g := Iff.rfl

theorem card_originLine (g : G) (hg : g ≠ 1) : Nat.card (originLine g) = 2 := by
  apply (Nat.card_eq_two_iff' (1 : originLine g)).mpr
  refine ⟨⟨g, Or.inr rfl⟩, fun h ↦ hg (congrArg Subtype.val h), ?_⟩
  rintro ⟨x, hx⟩ hne
  apply Subtype.ext
  rcases hx with rfl | rfl
  · exact (hne rfl).elim
  · rfl

/-- Label the first involution by the distinguished ramification line,
and choose a second involution outside it. -/
theorem exists_origin_generators (H : Subgroup G) (hH : Nat.card H = 2) :
    ∃ g₁ g₂ : G, g₁ ≠ 1 ∧ g₂ ≠ 1 ∧ g₁ ≠ g₂ ∧ H = originLine g₁ := by
  obtain ⟨g, hg, huniq⟩ := (Nat.card_eq_two_iff' (1 : H)).mp hH
  have hgval : (g : G) ≠ 1 := fun h ↦ hg (Subtype.ext h)
  have hline : H = originLine (g : G) := by
    ext x
    constructor
    · intro hx
      by_cases h : x = 1
      · exact Or.inl h
      · exact Or.inr (congrArg Subtype.val (huniq ⟨x, hx⟩ (fun e ↦ h (congrArg Subtype.val e))))
    · rintro (rfl | rfl)
      · exact H.one_mem
      · exact g.property
  have hproper : H ≠ ⊤ := by
    intro heq
    have hc : Nat.card H = 4 := by
      rw [heq]
      exact (Nat.card_congr Subgroup.topEquiv.toEquiv).trans IsKleinFour.card_four
    omega
  obtain ⟨g₂, hg₂⟩ : ∃ g₂ : G, g₂ ∉ H := by
    by_contra h
    push Not at h
    exact hproper (eq_top_iff.mpr (fun x _ ↦ h x))
  exact ⟨g, g₂, hgval, fun h ↦ hg₂ (h ▸ H.one_mem),
    fun h ↦ hg₂ (h ▸ g.property), hline⟩

end DiamondGroup

open private finrank_fixedField_line residueDegree_mul from
  LanglandsSecondMainLemma.Ramification.DiamondBreaks

section DiamondFields
variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  [CharP F 2] [CharP K 2] [IsKleinFour Gal(K/F)]
local instance : CharP (ResidueField F) 2 := residueField_charTwo F
local instance (L : IntermediateField F K) : ValuativeRel L := Basic.intermediateFieldValuativeRel L
local instance (L : IntermediateField F K) : TopologicalSpace L := Basic.intermediateFieldTopology L
local instance (L : IntermediateField F K) : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
local instance (L : IntermediateField F K) : ValuativeExtension F L := Basic.intermediateField_lowerValuativeExtension L
local instance (L : IntermediateField F K) : ValuativeExtension L K := Basic.intermediateField_upperValuativeExtension L
local instance (L : IntermediateField F K) : IsGalois F L := by
  letI : IsMulCommutative Gal(K/F) := IsKleinFour.isMulCommutative
  letI : L.fixingSubgroup.Normal := inferInstance
  have h := IsGalois.of_fixedField_normal_subgroup L.fixingSubgroup
  rwa [IsGalois.fixedField_fixingSubgroup L] at h

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K] [CharP F 2] [CharP K 2] in
private theorem origin_group_equiv : Nonempty
    (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  letI : IsKleinFour (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    ⟨by simp, by simp [Monoid.exponent_prod]⟩
  exact IsKleinFour.nonempty_mulEquiv

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] [CharP F 2] [CharP K 2] in
private theorem originLine_degrees (g : Gal(K/F)) (hg : g ≠ 1) :
    Module.finrank F (IntermediateField.fixedField (originLine g)) = 2 ∧
      Module.finrank (IntermediateField.fixedField (originLine g)) K = 2 :=
  ⟨finrank_fixedField_line Nat.prime_two (origin_group_equiv F K) _ (card_originLine g hg),
    (IntermediateField.finrank_fixedField_eq_card _).trans (card_originLine g hg)⟩

omit [CharP F 2] [CharP K 2] [IsKleinFour Gal(K/F)] in
private theorem origin_residueDegrees (hres : residueDegree F K = 1)
    (L : IntermediateField F K) : residueDegree F L = 1 ∧ residueDegree L K = 1 := by
  have h := (residueDegree_mul L).trans hres
  have h₁ := residueDegree_pos F L
  have h₂ := residueDegree_pos L K
  have hle₁ := Nat.le_mul_of_pos_right (residueDegree F L) h₂
  have hle₂ := Nat.le_mul_of_pos_left (residueDegree L K) h₁
  rw [h] at hle₁ hle₂
  omega

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] [CharP F 2] [CharP K 2] in
private theorem originLine_action (g h : Gal(K/F)) (hg : g ≠ 1)
    (hh : h ∉ originLine g)
    (sigma : Gal(IntermediateField.fixedField (originLine g)/F)) (hsigma : sigma ≠ 1)
    (z : IntermediateField.fixedField (originLine g)) (hz : sigma z = z + 1) :
    h (z : K) = (z : K) + 1 := by
  let L := IntermediateField.fixedField (originLine g)
  have hrestrict : AlgEquiv.restrictNormalHom L h ≠ 1 := by
    intro heq
    have hmem : h ∈ (AlgEquiv.restrictNormalHom L).ker := heq
    rw [IntermediateField.restrictNormalHom_ker, IntermediateField.fixingSubgroup_fixedField] at hmem
    exact hh hmem
  have hcard : Nat.card Gal(L/F) = 2 :=
    (IsGalois.card_aut_eq_finrank F L).trans (originLine_degrees F K g hg).1
  obtain ⟨tau, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/F))).mp hcard
  have heq : AlgEquiv.restrictNormalHom L h = sigma :=
    (huniq _ hrestrict).trans (huniq _ hsigma).symm
  have hz' := congrArg (fun x : L ↦ (x : K)) (heq ▸ hz)
  rw [AlgEquiv.restrictNormalHom_apply] at hz'
  exact hz'

omit [CharP F 2] [CharP K 2] in
private theorem originLine_break_unique (g : Gal(K/F)) (hg : g ≠ 1) {s t : ℕ}
    (hs : PrimeCyclicExtension.IsLowerBreak F (IntermediateField.fixedField (originLine g)) s)
    (ht : PrimeCyclicExtension.IsLowerBreak F (IntermediateField.fixedField (originLine g)) t) : s = t := by
  let L := IntermediateField.fixedField (originLine g)
  letI : IsCyclic Gal(L/F) := isCyclic_of_prime_card
    ((IsGalois.card_aut_eq_finrank F L).trans (originLine_degrees F K g hg).1)
  letI : PrimeCyclicExtension F L :=
    ⟨inferInstance, inferInstance, by rw [(originLine_degrees F K g hg).1]; exact Nat.prime_two⟩
  exact PrimeCyclicExtension.isLowerBreak_unique F L hs ht

/-- Reduced generators in the three actual fixed fields, with the smallest
break first and the third generator retained as the exact sum. -/
structure SimultaneousASGenerators (P : Residues.EqualCharacteristicPresentation F) where
  g : Fin 3 → Gal(K/F)
  nontrivial : ∀ i, g i ≠ 1
  distinct : g 0 ≠ g 1
  third_automorphism : g 2 = g 0 * g 1
  z : ∀ i, IntermediateField.fixedField (originLine (g i))
  f : Fin 3 → F
  t : Fin 3 → ℕ
  smallest : t 0 ≤ t 1
  third_break : t 2 = t 1
  third_parameter : f 2 = f 0 + f 1
  third_generator : (z 2 : K) = (z 0 : K) + (z 1 : K)
  first_action : g 0 (z 1 : K) = (z 1 : K) + 1
  second_action : g 1 (z 0 : K) = (z 0 : K) + 1
  edge : ∀ i,
    let L := IntermediateField.fixedField (originLine (g i))
    (z i) ^ 2 + z i = algebraMap F L (f i) ∧
      z i ∉ Set.range (algebraMap F L) ∧ IsReducedAS (P.laurentEquiv.symm (f i)) ∧
      0 < t i ∧ Odd (t i) ∧ ord L (z i) = ((-(t i : ℤ) : ℤ) : WithTop ℤ) ∧
      (P.laurentEquiv.symm (f i)).orderTop = ((-(t i : ℤ) : ℤ) : WithTop ℤ) ∧
      PrimeCyclicExtension.IsLowerBreak F L (t i) ∧ differentExponent F L = t i + 1
  upper_break : ∀ i,
    PrimeCyclicExtension.IsLowerBreak (IntermediateField.fixedField (originLine (g i))) K
      (if i = 0 then t 0 + 2 * (t 1 - t 0) else t 0)

/-- The simultaneous AS data are constructed from the genuine totally
ramified diamond, using its proved ramification profile. -/
theorem simultaneousASGenerators_exists (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) :
    Nonempty (SimultaneousASGenerators F K P) := by
  let hG := origin_group_equiv F K
  obtain ⟨D⟩ := (Ramification.diamondBreaks Nat.prime_two hG
    (show residueCharacteristic F = 2 from ringChar.eq (ResidueField F) 2)).1 hres
  obtain ⟨g₁, g₂, hg₁, hg₂, hne, hline⟩ := exists_origin_generators D.H₀ D.card_H₀
  let g₃ := g₁ * g₂
  have hg₃ : g₃ ≠ 1 := by
    intro h
    apply hne
    simpa only [IsKleinFour.inv_eq_self] using (mul_eq_one_iff_eq_inv.mp h)
  have h₃₁ : g₃ ≠ g₁ := by simpa [g₃] using hg₂
  have h₃₂ : g₃ ≠ g₂ := by simpa [g₃] using hg₁
  let L₁ := IntermediateField.fixedField (originLine g₁)
  let L₂ := IntermediateField.fixedField (originLine g₂)
  let L₃ := IntermediateField.fixedField (originLine g₃)
  have hres₁ := (origin_residueDegrees F K hres L₁).1
  have hres₂ := (origin_residueDegrees F K hres L₂).1
  have hres₃ := (origin_residueDegrees F K hres L₃).1
  obtain ⟨sigma₁, z₁, f₁, t₁, hsigma₁, hsigmaz₁, heq₁, hgen₁, hred₁,
      ht₁, hodd₁, hzord₁, hford₁, hbreak₁, hdiff₁⟩ :=
    exists_reducedAS_generator F L₁ (originLine_degrees F K g₁ hg₁).1 hres₁ P
  obtain ⟨sigma₂, z₂, f₂, t₂, hsigma₂, hsigmaz₂, heq₂, hgen₂, hred₂,
      ht₂, hodd₂, hzord₂, hford₂, hbreak₂, hdiff₂⟩ :=
    exists_reducedAS_generator F L₂ (originLine_degrees F K g₂ hg₂).1 hres₂ P
  have h₁₁ : g₁ (z₁ : K) = z₁ :=
    (IntermediateField.mem_fixedField_iff _ _).mp z₁.property g₁ (Or.inr rfl)
  have h₂₂ : g₂ (z₂ : K) = z₂ :=
    (IntermediateField.mem_fixedField_iff _ _).mp z₂.property g₂ (Or.inr rfl)
  have h₁₂ := originLine_action F K g₂ g₁ hg₂ (by simp [hg₁, hne]) sigma₂ hsigma₂ z₂ hsigmaz₂
  have h₂₁ := originLine_action F K g₁ g₂ hg₁ (by simp [hg₂, hne.symm]) sigma₁ hsigma₁ z₁ hsigmaz₁
  let z₃ : L₃ := ⟨(z₁ : K) + (z₂ : K), by
    apply (IntermediateField.mem_fixedField_iff _ _).mpr
    intro g hg
    rcases hg with rfl | rfl
    · rfl
    · change (g₁ * g₂) ((z₁ : K) + (z₂ : K)) = _
      rw [map_add, AlgEquiv.mul_apply, AlgEquiv.mul_apply, h₂₁, h₂₂,
        map_add, h₁₁, map_one, h₁₂, add_add_add_comm, CharTwo.add_self_eq_zero, add_zero]⟩
  let sigma₃ := AlgEquiv.restrictNormalHom L₃ g₁
  have hsigmaz₃ : sigma₃ z₃ = z₃ + 1 := by
    apply Subtype.ext
    change ((AlgEquiv.restrictNormalHom L₃ g₁) z₃ : K) = _
    rw [AlgEquiv.restrictNormalHom_apply]
    change g₁ ((z₁ : K) + (z₂ : K)) = (z₁ : K) + (z₂ : K) + 1
    rw [map_add, h₁₁, h₁₂, add_assoc]
  have hsigma₃ : sigma₃ ≠ 1 := by
    intro h
    rw [h, AlgEquiv.one_apply] at hsigmaz₃
    exact one_ne_zero (add_eq_left.mp hsigmaz₃.symm)
  have heq₃ : z₃ ^ 2 + z₃ = algebraMap F L₃ (f₁ + f₂) := by
    apply Subtype.ext
    have heq₁' := congrArg (fun z : L₁ ↦ (z : K)) heq₁
    have heq₂' := congrArg (fun z : L₂ ↦ (z : K)) heq₂
    change (z₁ : K) ^ 2 + z₁ = algebraMap F K f₁ at heq₁'
    change (z₂ : K) ^ 2 + z₂ = algebraMap F K f₂ at heq₂'
    change ((z₁ : K) + (z₂ : K)) ^ 2 + ((z₁ : K) + (z₂ : K)) = algebraMap F K (f₁ + f₂)
    rw [CharTwo.add_sq, map_add]
    calc
      _ = ((z₁ : K) ^ 2 + z₁) + ((z₂ : K) ^ 2 + z₂) := by ring
      _ = _ := by rw [heq₁', heq₂']
  have hgen₃ : z₃ ∉ Set.range (algebraMap F L₃) := by
    rintro ⟨a, ha⟩
    rw [← ha, sigma₃.commutes] at hsigmaz₃
    exact one_ne_zero (add_eq_left.mp hsigmaz₃.symm)
  have hred₃ : IsReducedAS (P.laurentEquiv.symm (f₁ + f₂)) := by
    intro n hn hc
    simp only [map_add, HahnSeries.coeff_add, hred₁ n hn hc, hred₂ n hn hc, add_zero]
  obtain ⟨t₃, ht₃, hodd₃, hzord₃, hford₃, hbreak₃, hdiff₃⟩ :=
    reducedAS_generator_data F L₃ (originLine_degrees F K g₃ hg₃).1 hres₃ P
      sigma₃ hsigma₃ z₃ (f₁ + f₂) hsigmaz₃ heq₃ hred₃
  have hp₁ : Ramification.IntermediateBreakPair Nat.prime_two hG
      (originLine g₁) (card_originLine g₁ hg₁) D.t D.b := by
    simpa only [hline] using D.distinguished_breaks
  have hline₂ : originLine g₂ ≠ D.H₀ := by
    rw [hline]
    intro h
    have hm : g₂ ∈ originLine g₁ := h ▸ (Or.inr rfl : g₂ ∈ originLine g₂)
    simp [hg₂, hne.symm] at hm
  have hline₃ : originLine g₃ ≠ D.H₀ := by
    rw [hline]
    intro h
    have hm : g₃ ∈ originLine g₁ := h ▸ (Or.inr rfl : g₃ ∈ originLine g₃)
    simp [hg₃, h₃₁] at hm
  obtain ⟨s₂, hp₂, _, hs₂, hb⟩ := D.other_breaks _ (card_originLine g₂ hg₂) hline₂
  obtain ⟨s₃, hp₃, _, hs₃, _⟩ := D.other_breaks _ (card_originLine g₃ hg₃) hline₃
  have ht₁D := originLine_break_unique F K g₁ hg₁ hbreak₁ hp₁.1
  have ht₂D := originLine_break_unique F K g₂ hg₂ hbreak₂ hp₂.1
  have ht₃D := originLine_break_unique F K g₃ hg₃ hbreak₃ hp₃.1
  refine ⟨{
    g := ![g₁, g₂, g₃], nontrivial := ?_, distinct := hne, third_automorphism := rfl
    z := Fin.cases z₁ (Fin.cases z₂ (Fin.cases z₃ (fun i ↦ Fin.elim0 i)))
    f := ![f₁, f₂, f₁ + f₂], t := ![t₁, t₂, t₃]
    smallest := by dsimp; omega
    third_break := by dsimp; omega
    third_parameter := rfl, third_generator := rfl
    first_action := h₁₂, second_action := h₂₁
    edge := ?_, upper_break := ?_ }⟩
  · intro i
    fin_cases i <;> dsimp <;> assumption
  · intro i
    fin_cases i <;> dsimp
    · exact ⟨heq₁, hgen₁, hred₁, ht₁, hodd₁, hzord₁, hford₁, hbreak₁, hdiff₁⟩
    · exact ⟨heq₂, hgen₂, hred₂, ht₂, hodd₂, hzord₂, hford₂, hbreak₂, hdiff₂⟩
    · exact ⟨heq₃, hgen₃, hred₃, ht₃, hodd₃, hzord₃, hford₃, hbreak₃, hdiff₃⟩
  · intro i
    fin_cases i <;> dsimp
    · convert hp₁.2 using 1 <;> first | rfl | omega
    · rw [ht₁D]
      convert hp₂.2 using 1 <;> rfl
    · rw [ht₁D]
      convert hp₃.2 using 1 <;> rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] [CharP F 2] [CharP K 2] in
private theorem originLine_norm_trace (g : Gal(K/F)) (hg : g ≠ 1) (Y : K) :
    let L := IntermediateField.fixedField (originLine g)
    algebraMap L K (Algebra.norm L Y) = Y * g Y ∧
      algebraMap L K (Algebra.trace L K Y) = Y + g Y := by
  classical
  let L := IntermediateField.fixedField (originLine g)
  let sigma : Gal(K/L) :=
    { g.toRingEquiv with commutes' := fun x ↦
        (IntermediateField.mem_fixedField_iff _ _).mp x.property g (Or.inr rfl) }
  have hsigma : sigma ≠ 1 := by
    intro h
    apply hg
    ext x
    exact congrArg (fun a : Gal(K/L) ↦ a x) h
  have hcard : Fintype.card Gal(K/L) = 2 := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank,
      (originLine_degrees F K g hg).2]
  have huniv : ({1, sigma} : Finset Gal(K/L)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simp [hsigma.symm, hcard]
  constructor
  · rw [Algebra.norm_eq_prod_automorphisms, ← huniv, Finset.prod_pair hsigma.symm]
    rfl
  · rw [trace_eq_sum_automorphisms, ← huniv, Finset.sum_pair hsigma.symm]
    rfl

namespace SimultaneousASGenerators
variable {F K} {P : Residues.EqualCharacteristicPresentation F} (A : SimultaneousASGenerators F K P)

/-- The full coefficient of (D:EQ:dbeta). -/
def beta (i : Fin 3) : F := P.laurentEquiv (originBeta (A.t 1) (P.laurentEquiv.symm (A.f i)))
/-- The exact square root fixed by exponent parity. -/
def root (i : Fin 3) : F := P.laurentEquiv (evenSquareRoot (originBeta (A.t 1) (P.laurentEquiv.symm (A.f i))))
/-- The simultaneous numerator (D:EQ:origin). -/
def Y : K := simultaneousOrigin (algebraMap F K (A.root 0)) (algebraMap F K (A.root 1)) (A.z 0) (A.z 1)
/-- The full integral constant, before its polar terms are cancelled. -/
def B : F := A.beta 0 * A.f 1 + A.beta 1 * A.f 0
/-- The three lower coefficients multiplying the retained generators. -/
def kappa : Fin 3 → F := ![A.root 1 * A.root 2, A.root 0 * A.root 2, A.root 0 * A.root 1]

theorem scalar_data (i : Fin 3) :
    A.root i ^ 2 = A.beta i ∧
      ord F (A.root i) = ((((A.t 1 : ℤ) - A.t i) / 2 : ℤ) : WithTop ℤ) ∧
      ord F (A.beta i) = (((A.t 1 : ℤ) - A.t i : ℤ) : WithTop ℤ) ∧
      A.beta i ∈ lattice F 0 ∧
      Algebra.norm F (algebraMap F (IntermediateField.fixedField (originLine (A.g i))) (A.root i)) = A.beta i := by
  obtain ⟨_, _, hred, ht, hodd, _, hf, _, _⟩ := A.edge i
  have hs : Odd (A.t 1 : ℤ) := by exact_mod_cast (A.edge 1).2.2.2.2.1
  have htodd : Odd (A.t i : ℤ) := by exact_mod_cast hodd
  have hdelta : (A.t 1 : ℤ) - A.t i = 2 * (((A.t 1 : ℤ) - A.t i) / 2) := by
    obtain ⟨a, ha⟩ := hs
    obtain ⟨b, hb⟩ := htodd
    omega
  have hle : A.t i ≤ A.t 1 := by
    fin_cases i
    · exact A.smallest
    · rfl
    · exact A.third_break.le
  have hord : ord F (A.beta i) = (((A.t 1 : ℤ) - A.t i : ℤ) : WithTop ℤ) := by
    rw [beta, P.laurentEquiv_order]
    exact originBeta_order (A.t i) (A.t 1) _ (by omega) hf
  refine ⟨?_, ?_, hord, ?_, originBeta_actualNorm F _
    (originLine_degrees F K (A.g i) (A.nontrivial i)).1 P (A.t 1) hs _ hred⟩
  · rw [root, ← map_pow, originBeta_square (A.t 1) hs _ hred]
    rfl
  · rw [root, P.laurentEquiv_order]
    exact originSquareRoot_order (A.t i) (A.t 1) _ _ (by omega) hs hdelta hred hf
  · change (0 : WithTop ℤ) ≤ ord F (A.beta i)
    rw [hord]
    exact WithTop.coe_le_coe.mpr (by omega)

omit [IsGalois F K] [CharP K 2] in
theorem root_third : A.root 2 = A.root 0 + A.root 1 := by
  have hs : Odd (A.t 1 : ℤ) := by exact_mod_cast (A.edge 1).2.2.2.2.1
  simp only [root, A.third_parameter, map_add]
  rw [originSquareRoot_add (A.t 1) hs _ _ (A.edge 0).2.2.1 (A.edge 1).2.2.1, map_add]

theorem B_integral : A.B ∈ lattice F 0 := by
  have h₀ := (A.scalar_data 0).2.2.2.1
  have h₁ := (A.scalar_data 1).2.2.2.1
  change 0 ≤ ord F (A.beta 0) at h₀
  change 0 ≤ ord F (A.beta 1) at h₁
  rw [beta, P.laurentEquiv_order] at h₀ h₁
  have heq : A.B = P.laurentEquiv
      (originBeta (A.t 1) (P.laurentEquiv.symm (A.f 0)) * P.laurentEquiv.symm (A.f 1) +
        originBeta (A.t 1) (P.laurentEquiv.symm (A.f 1)) * P.laurentEquiv.symm (A.f 0)) := by
    simp [B, beta]
  change (0 : WithTop ℤ) ≤ ord F (A.B)
  rw [heq, P.laurentEquiv_order]
  exact originB_integral (A.t 1) _ _ h₀ h₁

/-- All three identities in (D:EQ:exact-origin), using the actual upper
field norms and traces. -/
theorem exact_origin (i : Fin 3) :
    let L := IntermediateField.fixedField (originLine (A.g i))
    A.g i A.Y - A.Y = algebraMap F K (A.root i) ∧
      Algebra.trace L K A.Y = algebraMap F L (A.root i) ∧
      Algebra.norm L A.Y = algebraMap F L (A.kappa i) * A.z i + algebraMap F L A.B := by
  have hfix (j : Fin 3) : A.g j (A.z j : K) = A.z j :=
    (IntermediateField.mem_fixedField_iff _ _).mp (A.z j).property _ (Or.inr rfl)
  have hd := simultaneousOrigin_displacements (A.root 0) (A.root 1) (A.z 0 : K) (A.z 1 : K)
    (A.g 0) (A.g 1) (hfix 0) A.first_action A.second_action (hfix 1)
  have hdis : A.g i A.Y - A.Y = algebraMap F K (A.root i) := by
    fin_cases i <;> dsimp
    · exact hd.1
    · exact hd.2.1
    · rw [A.third_automorphism, A.root_third]
      exact hd.2.2
  have has (j : Fin 3) : (A.z j : K) ^ 2 + (A.z j : K) = algebraMap F K (A.f j) :=
    congrArg (fun x : IntermediateField.fixedField (originLine (A.g j)) ↦ (x : K)) (A.edge j).1
  have hp := simultaneousOrigin_products (algebraMap F K (A.root 0)) (algebraMap F K (A.root 1))
    (A.z 0 : K) (A.z 1 : K) (algebraMap F K (A.f 0)) (algebraMap F K (A.f 1)) (has 0) (has 1)
  have hB : (algebraMap F K (A.root 0)) ^ 2 * algebraMap F K (A.f 1) +
      (algebraMap F K (A.root 1)) ^ 2 * algebraMap F K (A.f 0) = algebraMap F K A.B := by
    rw [← map_pow, ← map_pow, (A.scalar_data 0).1, (A.scalar_data 1).1]
    simp [B]
  rw [hB] at hp
  have hprod : A.Y * (A.Y + algebraMap F K (A.root i)) =
      algebraMap F K (A.kappa i) * (A.z i : K) + algebraMap F K A.B := by
    fin_cases i <;> dsimp
    · simpa [Y, kappa, A.root_third] using hp.1
    · simpa [Y, kappa, A.root_third] using hp.2.1
    · simpa [Y, kappa, A.root_third, A.third_generator] using hp.2.2
  let L := IntermediateField.fixedField (originLine (A.g i))
  have hnt := originLine_norm_trace F K (A.g i) (A.nontrivial i) A.Y
  refine ⟨hdis, ?_, ?_⟩
  · apply (algebraMap L K).injective
    rw [hnt.2, ← IsScalarTower.algebraMap_apply F L K]
    simpa only [CharTwo.sub_eq_add, add_comm] using hdis
  · apply (algebraMap L K).injective
    rw [hnt.1, map_add, map_mul, ← IsScalarTower.algebraMap_apply F L K,
      ← IsScalarTower.algebraMap_apply F L K]
    have hg : A.g i A.Y = A.Y + algebraMap F K (A.root i) := by
      rw [← hdis]
      ring
    rw [hg]
    exact hprod

theorem kappa_order (i : Fin 3) :
    ord F (A.kappa i) = ((((A.t i : ℤ) - A.t 0) / 2 : ℤ) : WithTop ℤ) := by
  have h₀ := (A.scalar_data 0).2.1
  have h₁ := (A.scalar_data 1).2.1
  have h₂ := (A.scalar_data 2).2.1
  simp only [A.third_break, sub_self, Int.zero_ediv, WithTop.coe_zero] at h₁ h₂
  fin_cases i <;> simp [kappa, h₀, h₁, h₂, A.third_break]

/-- The valuations in (D:EQ:originval), with the common norm retained as
the actual transitive field norm. -/
theorem origin_orders (hres : residueDegree F K = 1) :
    ord K A.Y = ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ) ∧
      (∀ i : Fin 3,
        let L := IntermediateField.fixedField (originLine (A.g i))
        ord L (Algebra.norm L A.Y) = ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ) ∧
          Algebra.norm F (Algebra.norm L A.Y) = Algebra.norm F A.Y) ∧
      ord F (Algebra.norm F A.Y) = ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ) := by
  have hnorm (i : Fin 3) :
      let L := IntermediateField.fixedField (originLine (A.g i))
      ord L (Algebra.norm L A.Y) = ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ) := by
    let L := IntermediateField.fixedField (originLine (A.g i))
    change ord L (Algebra.norm L A.Y) = _
    have hram : ramificationIndex F L = 2 := by
      have h := finrank_eq_ramificationIndex_mul_residueDegree F L
      rw [(originLine_degrees F K (A.g i) (A.nontrivial i)).1,
        (origin_residueDegrees F K hres L).1, mul_one] at h
      exact h.symm
    have hterm : ord L (algebraMap F L (A.kappa i) * A.z i) =
        ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ) := by
      rw [ord_mul, ord_algebraMap, hram, A.kappa_order, (A.edge i).2.2.2.2.2.1,
        ← WithTop.coe_nsmul, ← WithTop.coe_add]
      congr 1
      have hi : Odd (A.t i : ℤ) := by exact_mod_cast (A.edge i).2.2.2.2.1
      have h₀ : Odd (A.t 0 : ℤ) := by exact_mod_cast (A.edge 0).2.2.2.2.1
      obtain ⟨a, ha⟩ := hi
      obtain ⟨b, hb⟩ := h₀
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      omega
    have hB : 0 ≤ ord L (algebraMap F L A.B) := by
      rw [ord_algebraMap, hram, two_nsmul]
      exact add_nonneg A.B_integral A.B_integral
    have hlt : ord L (algebraMap F L (A.kappa i) * A.z i) < ord L (algebraMap F L A.B) := by
      rw [hterm]
      apply lt_of_lt_of_le _ hB
      apply WithTop.coe_lt_coe.mpr
      have ht := (A.edge 0).2.2.2.1
      omega
    rw [(A.exact_origin i).2.2, ord_add_eq_min L hlt.ne, min_eq_left hlt.le, hterm]
  have hY := hnorm 0
  change ord (IntermediateField.fixedField (originLine (A.g 0))) (norm _ K A.Y) = _ at hY
  rw [ord_norm, (origin_residueDegrees F K hres _).2, one_nsmul] at hY
  refine ⟨hY, fun i ↦ ⟨hnorm i, Basic.norm_tower A.Y⟩, ?_⟩
  change ord F (norm F K A.Y) = _
  rw [ord_norm, hres, one_nsmul, hY]

theorem upper_different (hres : residueDegree F K = 1) (i : Fin 3) :
    let L := IntermediateField.fixedField (originLine (A.g i))
    (differentExponent L K : ℤ) =
      if i = 0 then 2 * ((A.t 1 : ℤ) + 1) - ((A.t 0 : ℤ) + 1) else (A.t 0 : ℤ) + 1 := by
  let L := IntermediateField.fixedField (originLine (A.g i))
  change (differentExponent L K : ℤ) = _
  have hdegree := (originLine_degrees F K (A.g i) (A.nontrivial i)).2
  letI : IsCyclic Gal(K/L) := isCyclic_of_prime_card
    ((IsGalois.card_aut_eq_finrank L K).trans hdegree)
  letI : PrimeCyclicExtension L K :=
    ⟨inferInstance, inferInstance, by rw [hdegree]; exact Nat.prime_two⟩
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer L K (origin_residueDegrees F K hres L).2
  rw [differentExponent_wildQuadratic_eq L K (A.upper_break i) hdegree pi hpi hgen]
  split_ifs <;> have h := A.smallest <;> omega

end SimultaneousASGenerators

open private coefficientRingHom coefficientRingHom_residue powerSeriesEquiv
  powerSeriesEval_C powerSeriesEval_X laurentSeriesEquiv laurentSeriesEquiv_C
  laurentSeriesEquiv_X laurentSeriesEquiv_order from
  LanglandsSecondMainLemma.Residues.EqualCharacteristicPresentation

omit [IsGalois F K] [CharP K 2] [IsKleinFour Gal(K/F)] in
/-- Install Laurent coordinates at the norm of an actual top uniformizer.
The coefficient field is the canonical one used by the accepted residue API. -/
theorem normOriginPresentation_exists (hres : residueDegree F K = 1) :
    ∃ (pi : ringOfIntegers K) (P : Residues.EqualCharacteristicPresentation F),
      (ValuativeRel.valuation K).IsUniformizer (pi : K) ∧
      (P.uniformizer : F) = Algebra.norm F (pi : K) := by
  obtain ⟨pi, hpi, _⟩ := monogenicUniformizer F K hres
  have hw : ord F (Algebra.norm F (pi : K)) = 1 := by
    change ord F (norm F K (pi : K)) = 1
    rw [ord_norm, hres, one_nsmul, ord_uniformizer K hpi]
  let s : ringOfIntegers F := ⟨Algebra.norm F (pi : K),
    (ord_nonneg_iff_mem_integer F _).mp (by rw [hw]; norm_num)⟩
  have hsunif : (ValuativeRel.valuation F).IsUniformizer (s : F) :=
    (ord_eq_one_iff_isUniformizer F _).mp hw
  have hspan : IsLocalRing.maximalIdeal (ringOfIntegers F) = Ideal.span {s} := hsunif.is_generator
  have hirr : Irreducible s := (IsDiscreteValuationRing.irreducible_iff_uniformizer s).mpr hspan
  have hs : s ∈ IsLocalRing.maximalIdeal (ringOfIntegers F) := by rw [hspan]; exact Ideal.subset_span rfl
  let hchar := EqualChar.equalCharacteristicTwo F
  refine ⟨pi, {
    equalCharacteristic := hchar
    coefficient := coefficientRingHom F hchar
    coefficient_eq_teichmuller := fun _ ↦ rfl
    coefficient_residue := coefficientRingHom_residue F hchar
    uniformizer := s
    uniformizer_irreducible := hirr
    uniformizer_isUniformizer := hsunif
    powerSeriesEquiv := powerSeriesEquiv F hchar s hs hirr.ne_zero hspan
    powerSeriesEquiv_C := fun a ↦ powerSeriesEval_C F hchar s hs a
    powerSeriesEquiv_X := powerSeriesEval_X F hchar s hs
    laurentEquiv := laurentSeriesEquiv F hchar s hs hirr.ne_zero hspan
    laurentEquiv_C := laurentSeriesEquiv_C F hchar s hs hirr.ne_zero hspan
    laurentEquiv_X := laurentSeriesEquiv_X F hchar s hs hirr.ne_zero hspan
    laurentEquiv_order := laurentSeriesEquiv_order F hchar s hs hirr.ne_zero hspan hirr },
    hpi, rfl⟩

omit [CharP K 2] in
/-- The simultaneous origin of (D:EQ:dbeta)--(D:EQ:upperdifferent),
constructed from the actual totally ramified characteristic-two diamond.
Its Laurent uniformizer is the norm of the retained top uniformizer; every
intermediate norm uniformizer, exact coefficient, norm, trace and valuation
belongs to that same construction. The full lower charts are supplied by
`dyadicEqual_lowerCharts` for the generators in `A.edge`. -/
theorem dyadicEqual_origin_exists (hres : residueDegree F K = 1) :
    ∃ (pi : ringOfIntegers K) (P : Residues.EqualCharacteristicPresentation F)
      (A : SimultaneousASGenerators F K P),
      (ValuativeRel.valuation K).IsUniformizer (pi : K) ∧
      (P.uniformizer : F) = Algebra.norm F (pi : K) ∧
      A.root 2 = A.root 0 + A.root 1 ∧ A.B ∈ lattice F 0 ∧
      ord K A.Y = ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ) ∧
      ord F (Algebra.norm F A.Y) = ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ) ∧
      ∀ i : Fin 3,
        let L := IntermediateField.fixedField (originLine (A.g i))
        (ValuativeRel.valuation L).IsUniformizer (Algebra.norm L (pi : K)) ∧
        Algebra.norm F (Algebra.norm L (pi : K)) = (P.uniformizer : F) ∧
        A.root i ^ 2 = A.beta i ∧
        ord F (A.root i) = ((((A.t 1 : ℤ) - A.t i) / 2 : ℤ) : WithTop ℤ) ∧
        ord F (A.beta i) = (((A.t 1 : ℤ) - A.t i : ℤ) : WithTop ℤ) ∧
        A.beta i ∈ lattice F 0 ∧ Algebra.norm F (algebraMap F L (A.root i)) = A.beta i ∧
        A.g i A.Y - A.Y = algebraMap F K (A.root i) ∧
        Algebra.trace L K A.Y = algebraMap F L (A.root i) ∧
        Algebra.norm L A.Y = algebraMap F L (A.kappa i) * A.z i + algebraMap F L A.B ∧
        ord L (Algebra.norm L A.Y) = ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ) ∧
        Algebra.norm F (Algebra.norm L A.Y) = Algebra.norm F A.Y ∧
        (differentExponent L K : ℤ) =
          if i = 0 then 2 * ((A.t 1 : ℤ) + 1) - ((A.t 0 : ℤ) + 1) else (A.t 0 : ℤ) + 1 := by
  letI : CharP K 2 := charP_of_injective_algebraMap (algebraMap F K).injective 2
  obtain ⟨pi, P, hpi, hP⟩ := normOriginPresentation_exists F K hres
  obtain ⟨A⟩ := simultaneousASGenerators_exists F K hres P
  have ho := A.origin_orders hres
  refine ⟨pi, P, A, hpi, hP, A.root_third, A.B_integral, ho.1, ho.2.2, ?_⟩
  intro i
  let L := IntermediateField.fixedField (originLine (A.g i))
  obtain ⟨hsq, hdord, hβord, hβint, hnormd⟩ := A.scalar_data i
  obtain ⟨hdis, htrace, hnorm⟩ := A.exact_origin i
  refine ⟨?_, (Basic.norm_tower (pi : K)).trans hP.symm,
    hsq, hdord, hβord, hβint, hnormd, hdis, htrace, hnorm,
    (ho.2.1 i).1, (ho.2.1 i).2, A.upper_different hres i⟩
  apply (ord_eq_one_iff_isUniformizer L _).mp
  change ord L (norm L K (pi : K)) = 1
  rw [ord_norm, (origin_residueDegrees F K hres L).2, one_nsmul, ord_uniformizer K hpi]

end DiamondFields
end
end LanglandsSecondMainLemma.Dyadic.Equal
