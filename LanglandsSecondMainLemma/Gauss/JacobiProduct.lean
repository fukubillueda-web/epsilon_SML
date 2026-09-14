import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsSecondMainLemma.Gauss.CoefficientField
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.NumberTheory.JacobiSum.Basic

/-!
# Gauss sums and their Jacobi product

This file proves Appendix A.2 of `epsilon_SML.tex`.  The multiplicative
character is the inverse power of the Teichmuller lift, and the additive
character is obtained from the absolute trace and the chosen primitive
`p`-th root of unity in the coefficient ring.  The exact product is the
standard Gauss--Jacobi convolution.  Reducing the Jacobi sum modulo the
cyclotomic uniformizer leaves one binomial coefficient; Lucas's theorem
then gives the product of the base-`p` digit coefficients.
-/

open scoped BigOperators
open Finset

namespace LanglandsSecondMainLemma.Gauss

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]

noncomputable local instance : Fintype k := Fintype.ofFinite k

/-- The Teichmuller section, regarded as a zero-extended multiplicative
character with values in the coefficient ring. -/
noncomputable def teichmullerMulChar (C : GaussCoefficientField p k) :
    MulChar k C.IntegerRing where
  toFun := teichmuller_lift p k C
  map_one' := map_one (teichmuller_lift p k C)
  map_mul' := map_mul (teichmuller_lift p k C)
  map_nonunit' := by
    intro x hx
    have hx0 : x = 0 := by
      simpa only [isUnit_iff_ne_zero, Classical.not_not] using hx
    subst x
    exact map_zero (teichmuller_lift p k C)

omit [Finite k] in
@[simp]
theorem teichmullerMulChar_apply (C : GaussCoefficientField p k) (x : k) :
    teichmullerMulChar p k C x = teichmuller_lift p k C x :=
  rfl

/-- The character `x |-> [x]^{-a}` used in the plus-sign Gauss sum. -/
noncomputable def inverseTeichmullerPowChar
    (C : GaussCoefficientField p k) (a : ℕ) : MulChar k C.IntegerRing :=
  (teichmullerMulChar p k C)⁻¹ ^ a

/-- The canonical additive character `x |-> zeta ^ Tr(x)` with values in
the coefficient ring. -/
noncomputable def cyclotomicTraceAddChar (C : GaussCoefficientField p k) :
    AddChar k C.IntegerRing :=
  (AddChar.zmodChar p C.zetaPrimitive.pow_eq_one).compAddMonoidHom
    (Algebra.trace (ZMod p) k).toAddMonoidHom

omit [Finite k] in
@[simp]
theorem cyclotomicTraceAddChar_apply (C : GaussCoefficientField p k) (x : k) :
    cyclotomicTraceAddChar p k C x =
      C.zeta ^ (Algebra.trace (ZMod p) k x).val :=
  rfl

/-- The manuscript's plus-sign Gauss sum
`G_a = sum_{x != 0} [x]^{-a} psi(x)`.  Mathlib's multiplicative
characters are zero at `0`, so its all-elements indexing is identical. -/
noncomputable def liftedGaussSum
    (C : GaussCoefficientField p k) (a : ℕ) : C.IntegerRing :=
  gaussSum (inverseTeichmullerPowChar p k C a)
    (cyclotomicTraceAddChar p k C)

/-- The Jacobi sum `J(a,b)` in the coefficient ring.  Its terms at zero
and one vanish, agreeing with the manuscript's punctured indexing. -/
noncomputable def liftedJacobiSum
    (C : GaussCoefficientField p k) (a b : ℕ) : C.IntegerRing :=
  jacobiSum (inverseTeichmullerPowChar p k C a)
    (inverseTeichmullerPowChar p k C b)

/-- The base-`p` digit in position `i`. -/
def basePDigit (p a i : ℕ) : ℕ := a / p ^ i % p

/-- Division with remainder after taking the complement in a full
`P * M`-element interval. -/
private theorem mul_sub_one_sub_decomposition
    {P M n : ℕ} (hP : 0 < P) (hn : n < P * M) :
    P * M - 1 - n =
      (P - 1 - n % P) + P * (M - 1 - n / P) := by
  have hr : n % P < P := Nat.mod_lt n hP
  have hd : n / P < M := by
    rw [Nat.div_lt_iff_lt_mul hP]
    simpa [Nat.mul_comm] using hn
  have hn_split : n = P * (n / P) + n % P := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod n P).symm
  have htop :
      P * (M - 1 - n / P) + P * (n / P + 1) = P * M := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have hsucc : P * (n / P + 1) = P * (n / P) + P := by
    rw [Nat.mul_add, Nat.mul_one]
  omega

/-- Digits of the complement `p^f - 1 - n` are digitwise complements. -/
private theorem basePDigit_pow_sub_one_sub
    {f n i : ℕ} (hn : n < p ^ f) (hi : i < f) :
    basePDigit p (p ^ f - 1 - n) i = p - 1 - basePDigit p n i := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpi : 0 < p ^ i := pow_pos hp i
  have hif : i ≤ f := hi.le
  have hpow : p ^ f = p ^ i * p ^ (f - i) := by
    rw [← pow_add, Nat.add_sub_of_le hif]
  have hfirst := mul_sub_one_sub_decomposition
    (P := p ^ i) (M := p ^ (f - i)) hpi (hpow ▸ hn)
  have hrem : p ^ i - 1 - n % p ^ i < p ^ i := by
    exact lt_of_le_of_lt (Nat.sub_le _ _) (by omega)
  have hquot :
      (p ^ f - 1 - n) / p ^ i = p ^ (f - i) - 1 - n / p ^ i := by
    rw [hpow, hfirst, Nat.add_mul_div_left _ _ hpi,
      Nat.div_eq_of_lt hrem, zero_add]
  have hfis : f - i = (f - i - 1) + 1 := by omega
  have hpow' : p ^ (f - i) = p * p ^ (f - i - 1) := by
    calc
      p ^ (f - i) = p ^ ((f - i - 1) + 1) := congrArg (p ^ ·) hfis
      _ = p ^ (f - i - 1) * p := pow_succ _ _
      _ = p * p ^ (f - i - 1) := Nat.mul_comm _ _
  have hdivlt : n / p ^ i < p ^ (f - i) := by
    rw [Nat.div_lt_iff_lt_mul hpi]
    simpa [hpow, Nat.mul_comm] using hn
  have hsecond := mul_sub_one_sub_decomposition
    (P := p) (M := p ^ (f - i - 1)) hp (hpow' ▸ hdivlt)
  unfold basePDigit
  rw [hquot, hpow', hsecond, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (by omega)]

/-- Reconstruction from the first `f` base-`p` digits. -/
private theorem sum_basePDigit_mul_pow
    {f a : ℕ} (ha : a < p ^ f) :
    (∑ i ∈ range f, basePDigit p a i * p ^ i) = a := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  induction f generalizing a with
  | zero =>
      simp only [pow_zero] at ha
      have : a = 0 := by omega
      subst a
      simp
  | succ f ih =>
      have hdiv : a / p < p ^ f := by
        rw [Nat.div_lt_iff_lt_mul hp]
        simpa [pow_succ, Nat.mul_comm] using ha
      have htail :
          (∑ i ∈ range f,
              basePDigit p a (i + 1) * p ^ (i + 1)) =
            p * ∑ i ∈ range f, basePDigit p (a / p) i * p ^ i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        unfold basePDigit
        simp only [pow_succ, Nat.div_div_eq_div_mul]
        ring_nf
      rw [sum_range_succ', htail, ih hdiv]
      simp only [basePDigit, pow_zero, Nat.div_one, Nat.mul_one]
      simpa [Nat.add_comm] using Nat.mod_add_div a p

omit [Finite k] in
/-- The global sign is the product of the digit signs.  The identity
`(-1)^(p^i) = -1` is valid uniformly, including characteristic two. -/
private theorem neg_one_pow_eq_prod_basePDigit
    {f a : ℕ} (ha : a < p ^ f) :
    (-1 : k) ^ a = ∏ i ∈ range f, (-1 : k) ^ basePDigit p a i := by
  letI : CharP k p := charP_of_injective_algebraMap
    (RingHom.injective (algebraMap (ZMod p) k)) p
  have hsum := sum_basePDigit_mul_pow p ha
  calc
    (-1 : k) ^ a =
        (-1 : k) ^ (∑ i ∈ range f, basePDigit p a i * p ^ i) := by rw [hsum]
    _ = ∏ i ∈ range f, (-1 : k) ^ (basePDigit p a i * p ^ i) :=
      (Finset.prod_pow_eq_pow_sum (range f)
        (fun i ↦ basePDigit p a i * p ^ i) (-1 : k)).symm
    _ = ∏ i ∈ range f, (-1 : k) ^ basePDigit p a i := by
      apply Finset.prod_congr rfl
      intro i _hi
      rw [Nat.mul_comm, pow_mul, neg_one_pow_char_pow]

omit [Finite k] in
/-- The one-digit binomial-complement identity used after Lucas's
theorem. -/
private theorem neg_one_pow_mul_choose_complement
    {r s : ℕ} (hrs : r + s < p) :
    (-1 : k) ^ r * (Nat.choose (p - 1 - s) r : k) =
      (Nat.choose (r + s) r : k) := by
  letI : CharP k p := charP_of_injective_algebraMap
    (RingHom.injective (algebraMap (ZMod p) k)) p
  induction r with
  | zero => simp
  | succ r ih =>
      have hrs' : r + s < p := by omega
      have ihr := ih hrs'
      have hrN : r ≤ p - 1 - s := by omega
      have hcast :
          -((p - 1 - s - r : ℕ) : k) = ((r + s + 1 : ℕ) : k) := by
        have hnat : (p - 1 - s - r) + (r + s + 1) = p := by omega
        have hk := congrArg (fun n : ℕ ↦ (n : k)) hnat
        norm_num only [Nat.cast_add] at hk
        rw [CharP.cast_eq_zero k p] at hk
        norm_num only [Nat.cast_add, Nat.cast_one]
        calc
          -((p - 1 - s - r : ℕ) : k) =
              -((p - 1 - s - r : ℕ) : k) +
                (((p - 1 - s - r : ℕ) : k) + ((r : k) + (s : k) + 1)) := by
            rw [hk, add_zero]
          _ = (r : k) + (s : k) + 1 := by ring
      have hnonzero : ((r + 1 : ℕ) : k) ≠ 0 := by
        intro hzero
        have hdvd : p ∣ r + 1 :=
          (CharP.cast_eq_zero_iff k p (r + 1)).mp hzero
        exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) hdvd
      have hchooseN := congrArg (fun n : ℕ ↦ (n : k))
        (Nat.choose_succ_right_eq (p - 1 - s) r)
      norm_num only [Nat.cast_mul] at hchooseN
      have hchoose := congrArg (fun n : ℕ ↦ (n : k))
        (Nat.add_one_mul_choose_eq (r + s) r)
      norm_num only [Nat.cast_mul] at hchoose
      apply mul_right_cancel₀ hnonzero
      calc
        ((-1 : k) ^ (r + 1) * (Nat.choose (p - 1 - s) (r + 1) : k)) *
            ((r + 1 : ℕ) : k) =
            (-1 : k) ^ (r + 1) *
              ((Nat.choose (p - 1 - s) r : k) *
                ((p - 1 - s - r : ℕ) : k)) := by
          rw [mul_assoc, hchooseN]
        _ = ((-1 : k) ^ r * (Nat.choose (p - 1 - s) r : k)) *
              (-((p - 1 - s - r : ℕ) : k)) := by
          rw [pow_succ]
          ring
        _ = (Nat.choose (r + s) r : k) * ((r + s + 1 : ℕ) : k) := by
          rw [ihr, hcast]
        _ = (Nat.choose (r + s + 1) (r + 1) : k) * ((r + 1 : ℕ) : k) := by
          simpa [mul_comm] using hchoose
        _ = (Nat.choose ((r + 1) + s) (r + 1) : k) * ((r + 1 : ℕ) : k) := by
          rw [show (r + 1) + s = r + s + 1 by omega]

/-- A proper positive inverse power of the Teichmuller character is
nontrivial.  This is the vanishing input for the `x + y = 0` fiber in
the Gauss--Jacobi convolution. -/
theorem inverseTeichmullerPowChar_ne_one
    (C : GaussCoefficientField p k) {a : ℕ}
    (ha : 0 < a) (haq : a < Fintype.card k - 1) :
    inverseTeichmullerPowChar p k C a ≠ 1 := by
  let φ := cyclotomicResidueMap p k C.unramified
  obtain ⟨x, hx⟩ := exists_pow_ne_one_of_isCyclic (G := kˣ) ha.ne' (by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
    exact haq)
  intro hchar
  have happ := congrArg (fun χ : MulChar k C.IntegerRing ↦ χ x) hchar
  have hmap := congrArg φ happ
  have hliftUnit : IsUnit (teichmuller_lift p k C (x : k)) :=
    IsUnit.map (teichmuller_lift p k C) x.isUnit
  have hliftred :
      φ (teichmuller_lift p k C (x : k)) = (x : k) :=
    teichmuller_lift_reduction p k C (x : k)
  have hunitred : Units.map φ.toMonoidHom hliftUnit.unit = x := by
    apply Units.ext
    change φ (↑hliftUnit.unit) = (x : k)
    rw [hliftUnit.unit_spec]
    exact hliftred
  have hinvred :
      φ (Ring.inverse (teichmuller_lift p k C (x : k))) = ((x⁻¹ : kˣ) : k) := by
    rw [← hliftUnit.unit_spec, Ring.inverse_unit]
    calc
      φ (↑(hliftUnit.unit⁻¹) : C.IntegerRing) =
          (↑((Units.map φ.toMonoidHom hliftUnit.unit)⁻¹) : k) :=
        (Units.coe_map_inv φ.toMonoidHom hliftUnit.unit).symm
      _ = (↑(x⁻¹) : k) := by rw [hunitred]
  simp only [inverseTeichmullerPowChar, MulChar.pow_apply_coe,
    MulChar.inv_apply_eq_inv, teichmullerMulChar_apply, map_pow,
    hinvred, MulChar.one_apply_coe, map_one] at hmap
  have hxinv : (x⁻¹ : kˣ) ^ a = 1 := by
    apply Units.ext
    change ((x⁻¹ : kˣ) : k) ^ a = (1 : k)
    exact hmap
  apply hx
  simpa only [inv_pow, inv_eq_one] using hxinv

/-- On reduction, `[x]^{-a}` is the polynomial function
`x^(#k-1-a)` when `0 < a < #k-1`. -/
theorem inverseTeichmullerPowChar_reduction
    (C : GaussCoefficientField p k) {a : ℕ}
    (ha : 0 < a) (haq : a < Fintype.card k - 1) (x : k) :
    cyclotomicResidueMap p k C.unramified
        (inverseTeichmullerPowChar p k C a x) =
      x ^ (Fintype.card k - 1 - a) := by
  let φ := cyclotomicResidueMap p k C.unramified
  by_cases hx : x = 0
  · subst x
    have hexp : Fintype.card k - 1 - a ≠ 0 := (Nat.sub_pos_of_lt haq).ne'
    simp only [inverseTeichmullerPowChar, MulChar.map_zero, map_zero,
      zero_pow hexp]
  · let xu : kˣ := Units.mk0 x hx
    have hliftUnit : IsUnit (teichmuller_lift p k C x) :=
      IsUnit.map (teichmuller_lift p k C) (isUnit_iff_ne_zero.mpr hx)
    have hliftred : φ (teichmuller_lift p k C x) = x :=
      teichmuller_lift_reduction p k C x
    have hunitred : Units.map φ.toMonoidHom hliftUnit.unit = xu := by
      apply Units.ext
      change φ (↑hliftUnit.unit) = x
      rw [hliftUnit.unit_spec]
      exact hliftred
    have hinvred : φ (Ring.inverse (teichmuller_lift p k C x)) = x⁻¹ := by
      rw [← hliftUnit.unit_spec, Ring.inverse_unit]
      calc
        φ (↑(hliftUnit.unit⁻¹) : C.IntegerRing) =
            (↑((Units.map φ.toMonoidHom hliftUnit.unit)⁻¹) : k) :=
          (Units.coe_map_inv φ.toMonoidHom hliftUnit.unit).symm
        _ = (↑(xu⁻¹) : k) := by rw [hunitred]
        _ = x⁻¹ := by rfl
    change φ (((teichmullerMulChar p k C)⁻¹ ^ a) x) = _
    rw [MulChar.pow_apply' _ ha.ne', MulChar.inv_apply_eq_inv,
      teichmullerMulChar_apply, map_pow, hinvred]
    apply mul_right_cancel₀ (pow_ne_zero a hx)
    calc
      (x⁻¹ ^ a) * x ^ a = 1 := by rw [← mul_pow, inv_mul_cancel₀ hx, one_pow]
      _ = x ^ (Fintype.card k - 1) :=
        (FiniteField.pow_card_sub_one_eq_one x hx).symm
      _ = x ^ (Fintype.card k - 1 - a) * x ^ a := by
        rw [pow_sub_mul_pow x (Nat.le_of_lt haq)]

/-- The finite-field power-sum calculation in the proof of Appendix A.2.
The sole surviving exponent is the positive multiple `#k - 1`. -/
private theorem jacobiPowerSum_eq_choose
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (habq : a + b < Fintype.card k - 1) :
    (∑ x : k, x ^ (Fintype.card k - 1 - a) *
        (1 - x) ^ (Fintype.card k - 1 - b)) =
      -(-1 : k) ^ a * (Nat.choose (Fintype.card k - 1 - b) a : k) := by
  classical
  let q := Fintype.card k
  let A := q - 1 - a
  let B := q - 1 - b
  have haA : A + a = q - 1 := by
    dsimp only [A, q]
    omega
  have haB : a ≤ B := by
    dsimp only [B, q]
    omega
  have hBq : B < q := by
    dsimp only [B, q]
    have hqpos := Fintype.card_pos (α := k)
    omega
  have hApos : 0 < A := by
    dsimp only [A, q]
    omega
  have hqm1pos : 0 < q - 1 := by omega
  have hsumq : ∑ x : k, x ^ (q - 1) = -1 := by
    calc
      (∑ x : k, x ^ (q - 1)) = ∑ x : kˣ, ((x : k) ^ (q - 1)) := by
        rw [Fintype.sum_eq_add_sum_subtype_ne _ 0]
        simp only [zero_pow hqm1pos.ne', zero_add]
        simpa using
          (Equiv.sum_comp unitsEquivNeZero
            (fun x : {x : k // x ≠ 0} ↦ (x : k) ^ (q - 1))).symm
      _ = -1 := by
        rw [FiniteField.sum_pow_units k (q - 1), if_pos dvd_rfl]
  calc
    (∑ x : k, x ^ (Fintype.card k - 1 - a) *
        (1 - x) ^ (Fintype.card k - 1 - b)) =
        ∑ x : k, ∑ j ∈ range (B + 1),
          (-1 : k) ^ j * (Nat.choose B j : k) * x ^ (A + j) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [show (1 - x : k) = -x + 1 by ring, add_pow]
      simp only [one_pow, mul_one]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [neg_pow]
      change x ^ A * ((-1 : k) ^ j * x ^ j * (Nat.choose B j : k)) =
        (-1 : k) ^ j * (Nat.choose B j : k) * x ^ (A + j)
      rw [pow_add]
      ring
    _ = ∑ j ∈ range (B + 1),
          (-1 : k) ^ j * (Nat.choose B j : k) *
            (∑ x : k, x ^ (A + j)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.mul_sum]
    _ = -(-1 : k) ^ a * (Nat.choose B a : k) := by
      rw [Finset.sum_eq_single a]
      · rw [haA, hsumq]
        ring
      · intro j hj hja
        rw [mem_range] at hj
        have hpos : 0 < A + j := by omega
        have hlt : A + j < 2 * (q - 1) := by
          dsimp only [A, B, q] at *
          omega
        have hndvd : ¬ q - 1 ∣ A + j := by
          intro hdvd
          have heq : A + j = q - 1 := by
            obtain ⟨c, hc⟩ := hdvd
            have hcpos : 0 < c := by
              by_contra hc0
              simp only [not_lt, nonpos_iff_eq_zero] at hc0
              subst c
              simp at hc
              omega
            have hcle : c < 2 := by
              rw [hc] at hlt
              exact (Nat.mul_lt_mul_right hqm1pos).mp
                (by simpa [Nat.mul_comm] using hlt)
            have hc1 : c = 1 := by omega
            simpa [hc1] using hc
          apply hja
          omega
        have hsum : ∑ x : k, x ^ (A + j) = 0 := by
          calc
            (∑ x : k, x ^ (A + j)) = ∑ x : kˣ, ((x : k) ^ (A + j)) := by
              rw [Fintype.sum_eq_add_sum_subtype_ne _ 0]
              simp only [zero_pow hpos.ne', zero_add]
              simpa using
                (Equiv.sum_comp unitsEquivNeZero
                  (fun x : {x : k // x ≠ 0} ↦ (x : k) ^ (A + j))).symm
            _ = 0 := by
              rw [FiniteField.sum_pow_units k (A + j), if_neg hndvd]
        rw [hsum, mul_zero]
      · rw [mem_range]
        omega
    _ = -(-1 : k) ^ a *
        (Nat.choose (Fintype.card k - 1 - b) a : k) := by rfl

/-- Before the digit calculation, reduction of the Jacobi sum is the
single binomial coefficient occurring in the manuscript proof. -/
theorem liftedJacobiSum_reduction_choose
    (C : GaussCoefficientField p k) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (habq : a + b < Fintype.card k - 1) :
    cyclotomicResidueMap p k C.unramified (liftedJacobiSum p k C a b) =
      -(-1 : k) ^ a *
        (Nat.choose (Fintype.card k - 1 - b) a : k) := by
  let φ := cyclotomicResidueMap p k C.unramified
  have haq : a < Fintype.card k - 1 := by omega
  have hbq : b < Fintype.card k - 1 := by omega
  rw [liftedJacobiSum, ← jacobiSum_ringHomComp]
  rw [jacobiSum]
  calc
    (∑ x : k,
        (inverseTeichmullerPowChar p k C a).ringHomComp φ x *
          (inverseTeichmullerPowChar p k C b).ringHomComp φ (1 - x)) =
        ∑ x : k, x ^ (Fintype.card k - 1 - a) *
          (1 - x) ^ (Fintype.card k - 1 - b) := by
      apply Finset.sum_congr rfl
      intro x _hx
      simp only [MulChar.ringHomComp_apply]
      rw [inverseTeichmullerPowChar_reduction p k C ha haq,
        inverseTeichmullerPowChar_reduction p k C hb hbq]
    _ = _ := jacobiPowerSum_eq_choose (k := k) ha hb habq

/-- The digitwise reduction formula of Appendix A.2. -/
theorem liftedJacobiSum_reduction
    (C : GaussCoefficientField p k) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (habq : a + b < Fintype.card k - 1)
    (hnocarry : ∀ i < Module.finrank (ZMod p) k,
      basePDigit p a i + basePDigit p b i < p) :
    cyclotomicResidueMap p k C.unramified (liftedJacobiSum p k C a b) =
      -∏ i ∈ range (Module.finrank (ZMod p) k),
        (Nat.choose (basePDigit p a i + basePDigit p b i)
          (basePDigit p a i) : k) := by
  letI : CharP k p := charP_of_injective_algebraMap
    (RingHom.injective (algebraMap (ZMod p) k)) p
  let f := Module.finrank (ZMod p) k
  have hq : p ^ f = Fintype.card k := FiniteField.pow_finrank_eq_card p k
  have haPow : a < p ^ f := by rw [hq]; omega
  have hbPow : b < p ^ f := by rw [hq]; omega
  have hnumPow : Fintype.card k - 1 - b < p ^ f := by rw [hq]; omega
  have hcomp (i : ℕ) (hi : i < f) :
      basePDigit p (Fintype.card k - 1 - b) i =
        p - 1 - basePDigit p b i := by
    rw [← hq]
    exact basePDigit_pow_sub_one_sub p hbPow hi
  have hLucas := Choose.choose_modEq_prod_range_choose_nat
    (p := p) (n := Fintype.card k - 1 - b) (k := a)
    (a := f) hnumPow haPow
  have hLucasCast := CharP.natCast_eq_natCast' k p hLucas
  norm_num only [Nat.cast_prod] at hLucasCast
  have hchoose :
      (Nat.choose (Fintype.card k - 1 - b) a : k) =
        ∏ i ∈ range f,
          (Nat.choose (p - 1 - basePDigit p b i)
            (basePDigit p a i) : k) := by
    rw [hLucasCast]
    apply Finset.prod_congr rfl
    intro i hi
    rw [mem_range] at hi
    change
      (Nat.choose (basePDigit p (Fintype.card k - 1 - b) i)
        (basePDigit p a i) : k) = _
    rw [hcomp i hi]
  have hsign := neg_one_pow_eq_prod_basePDigit (p := p) (k := k) haPow
  rw [liftedJacobiSum_reduction_choose p k C ha hb habq, hchoose, hsign]
  change
    (-(∏ i ∈ range f, (-1 : k) ^ basePDigit p a i)) *
        (∏ i ∈ range f,
          (Nat.choose (p - 1 - basePDigit p b i) (basePDigit p a i) : k)) =
      -∏ i ∈ range f,
        (Nat.choose (basePDigit p a i + basePDigit p b i)
          (basePDigit p a i) : k)
  rw [neg_mul, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [mem_range] at hi
  exact neg_one_pow_mul_choose_complement (p := p) (k := k) (hnocarry i hi)

/-- The Jacobi sum is a unit because its digitwise residue is nonzero. -/
theorem liftedJacobiSum_isUnit
    (C : GaussCoefficientField p k) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (habq : a + b < Fintype.card k - 1)
    (hnocarry : ∀ i < Module.finrank (ZMod p) k,
      basePDigit p a i + basePDigit p b i < p) :
    IsUnit (liftedJacobiSum p k C a b) := by
  letI : IsDomain C.IntegerRing := C.coefficientDomain
  letI : IsLocalRing C.IntegerRing := C.coefficientLocalRing
  letI : CharP k p := charP_of_injective_algebraMap
    (RingHom.injective (algebraMap (ZMod p) k)) p
  let φ := cyclotomicResidueMap p k C.unramified
  have hprod :
      (∏ i ∈ range (Module.finrank (ZMod p) k),
        (Nat.choose (basePDigit p a i + basePDigit p b i)
          (basePDigit p a i) : k)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    rw [mem_range] at hi
    intro hzero
    have hdvd : p ∣ Nat.choose
        (basePDigit p a i + basePDigit p b i) (basePDigit p a i) :=
      (CharP.cast_eq_zero_iff k p _).mp hzero
    have hcop := (Fact.out : p.Prime).coprime_choose_of_lt
      (hnocarry i hi) (by omega : basePDigit p a i ≤
        basePDigit p a i + basePDigit p b i)
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hcop) hdvd
  have hmap : φ (liftedJacobiSum p k C a b) ≠ 0 := by
    rw [liftedJacobiSum_reduction p k C ha hb habq hnocarry]
    exact neg_ne_zero.mpr hprod
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hmem
  have hspan : liftedJacobiSum p k C a b ∈ Ideal.span {C.uniformizer} := by
    rw [← cyclotomicUniformizer p k C]
    exact hmem
  rw [Ideal.mem_span_singleton] at hspan
  obtain ⟨t, ht⟩ := hspan
  have hrootzero : φ C.uniformizer = 0 := by
    unfold φ cyclotomicResidueMap GaussCoefficientField.uniformizer
    apply AdjoinRoot.lift_root
  apply hmap
  rw [ht, map_mul, hrootzero, zero_mul]

/-- The exact Gauss--Jacobi product identity. -/
theorem liftedGaussSum_product
    (C : GaussCoefficientField p k) {a b : ℕ}
    (habpos : 0 < a + b) (habq : a + b < Fintype.card k - 1) :
    liftedGaussSum p k C a * liftedGaussSum p k C b =
      liftedJacobiSum p k C a b * liftedGaussSum p k C (a + b) := by
  letI : IsDomain C.IntegerRing := C.coefficientDomain
  have hchar : inverseTeichmullerPowChar p k C a *
      inverseTeichmullerPowChar p k C b ≠ 1 := by
    rw [inverseTeichmullerPowChar, inverseTeichmullerPowChar, ← pow_add]
    exact inverseTeichmullerPowChar_ne_one p k C habpos habq
  have hproduct := jacobiSum_mul_nontrivial hchar
    (cyclotomicTraceAddChar p k C)
  rw [mul_comm (liftedJacobiSum p k C a b)]
  simpa only [liftedGaussSum, liftedJacobiSum,
    ← pow_add, inverseTeichmullerPowChar] using hproduct.symm

/-- Appendix A.2: the exact Gauss--Jacobi product, the Jacobi unit, and
its no-carry digitwise residue. -/
theorem jacobiProduct
    (C : GaussCoefficientField p k) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (habq : a + b < Fintype.card k - 1)
    (hnocarry : ∀ i < Module.finrank (ZMod p) k,
      basePDigit p a i + basePDigit p b i < p) :
    liftedGaussSum p k C a * liftedGaussSum p k C b =
        liftedJacobiSum p k C a b * liftedGaussSum p k C (a + b) ∧
      IsUnit (liftedJacobiSum p k C a b) ∧
      cyclotomicResidueMap p k C.unramified (liftedJacobiSum p k C a b) =
        -∏ i ∈ range (Module.finrank (ZMod p) k),
          (Nat.choose (basePDigit p a i + basePDigit p b i)
            (basePDigit p a i) : k) := by
  refine ⟨liftedGaussSum_product p k C (by omega) habq, ?_, ?_⟩
  · exact liftedJacobiSum_isUnit p k C ha hb habq hnocarry
  · exact liftedJacobiSum_reduction p k C ha hb habq hnocarry

end

end LanglandsSecondMainLemma.Gauss
