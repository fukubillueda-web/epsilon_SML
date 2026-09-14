import LanglandsFirstMainLemma.Basic.CharacterConductorExistence
import LanglandsFirstMainLemma.Basic.CharacterConductors
import LanglandsFirstMainLemma.Basic.CharacterTypes
import LanglandsFirstMainLemma.Basic.StandardCharacterBridge
import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsFirstMainLemma.Ramification.PrimeCyclicExtension
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Basic.Fields

/-!
# Finite-field polynomial rigidity

This is Lemma `O:M:rigidity` (Lemma 8.3) of the controlling manuscript. The
proof is separated into a finite-field core and its local-field specialization.
The finite core uses the weighted sum with weight `x ^ (q - 2)`. After the
absolute trace is expanded into Frobenius conjugates, the degree bound
`D < p ^ 2` and the hypothesis that the absolute residue degree is at least
three leave precisely the exponents `1` and `p`.
-/

namespace LanglandsSecondMainLemma.Finite

open scoped BigOperators Polynomial
open Polynomial
open LanglandsFirstMainLemma

noncomputable section

/-! ## The elementary Frobenius-orbit calculation -/

/-- The only positive exponent below `p²` whose `i`-th Frobenius translate
is congruent to `1` modulo `p^r-1`, for `i<r` and `r≥3`, is `1` (at
`i=0`) or `p` (at `i=r-1`). -/
private theorem frobeniusOrbit_one_or_p
    {p r n i : ℕ} (hp : p.Prime) (hr : 3 ≤ r)
    (hn0 : 0 < n) (hn : n < p ^ 2) (hi : i < r)
    (hdiv : p ^ r - 1 ∣ n * p ^ i - 1) :
    (n = 1 ∧ i = 0) ∨ (n = p ∧ i + 1 = r) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hmul_pos : 0 < n * p ^ i := Nat.mul_pos hn0 (pow_pos hp.pos i)
  have hmod : 1 ≡ n * p ^ i [MOD p ^ r - 1] :=
    (Nat.modEq_iff_dvd' hmul_pos).2 hdiv
  by_cases hilast : i + 1 = r
  · right
    refine ⟨?_, hilast⟩
    have hir : i = r - 1 := by omega
    subst i
    let a := n / p
    let b := n % p
    have hnapb : n = a * p + b := by
      dsimp only [a, b]
      simpa [mul_comm] using (Nat.div_add_mod n p).symm
    have hb : b < p := by
      dsimp only [b]
      exact Nat.mod_lt _ hp.pos
    have ha : a < p := by
      dsimp only [a]
      exact (Nat.div_lt_iff_lt_mul hp.pos).2 (by simpa [pow_two] using hn)
    have hpowr : p ^ r = p ^ (r - 1) * p := by
      rw [← pow_succ]
      congr
      omega
    have hpowMod : p ^ r ≡ 1 [MOD p ^ r - 1] := by
      have heq : p ^ r = (p ^ r - 1) + 1 := by
        have : 0 < p ^ r := pow_pos hp.pos r
        omega
      rw [heq]
      exact Nat.add_modEq_left
    have hrepl : n * p ^ (r - 1) ≡
        a + b * p ^ (r - 1) [MOD p ^ r - 1] := by
      rw [hnapb, add_mul, mul_assoc, mul_comm p (p ^ (r - 1)), ← hpowr]
      simpa only [mul_one, one_mul] using
        (hpowMod.mul_left a).add (Nat.ModEq.rfl (n := p ^ r - 1))
    have hmodB : 1 ≡ a + b * p ^ (r - 1) [MOD p ^ r - 1] :=
      hmod.trans hrepl
    have hsmall : a + b * p ^ (r - 1) < p ^ r - 1 := by
      have hspos : 0 < p ^ (r - 1) := pow_pos hp.pos _
      have hps : p < p ^ (r - 1) := by
        calc
          p = p ^ 1 := by simp
          _ < p ^ (r - 1) := Nat.pow_lt_pow_right hp.one_lt (by omega)
      have hbp : b * p ^ (r - 1) ≤ (p - 1) * p ^ (r - 1) :=
        Nat.mul_le_mul_right _ (by omega)
      have hap : a ≤ p - 1 := by omega
      have hpdecomp : p ^ (r - 1) * p =
          (p - 1) * p ^ (r - 1) + p ^ (r - 1) := by
        calc
          p ^ (r - 1) * p = p * p ^ (r - 1) := by rw [mul_comm]
          _ = ((p - 1) + 1) * p ^ (r - 1) := by
            congr
            omega
          _ = (p - 1) * p ^ (r - 1) + p ^ (r - 1) := by rw [add_mul, one_mul]
      rw [hpowr, hpdecomp]
      omega
    have hmodulus : 1 < p ^ r - 1 := by
      have hpow3 : 2 ^ 3 ≤ p ^ r := by
        exact (Nat.pow_le_pow_left hp2 3).trans
          (Nat.pow_le_pow_right hp.pos hr)
      have hone : 1 ≤ p ^ r := by omega
      have hsub : p ^ r - 1 + 1 = p ^ r := Nat.sub_add_cancel hone
      norm_num at hpow3
      omega
    have hBeq : a + b * p ^ (r - 1) = 1 :=
      (hmodB.eq_of_lt_of_lt hmodulus hsmall).symm
    have hb0 : b = 0 := by
      by_contra hb0
      have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
      have hpowlarge : 2 ≤ p ^ (r - 1) := by
        have hpowp : p ≤ p ^ (r - 1) := by
          calc
            p = p ^ 1 := by simp
            _ ≤ p ^ (r - 1) := Nat.pow_le_pow_right hp.pos (by omega)
        exact hp2.trans hpowp
      have hle : p ^ (r - 1) ≤ b * p ^ (r - 1) :=
        Nat.le_mul_of_pos_left _ hbpos
      have hleone : b * p ^ (r - 1) ≤ 1 := by
        calc
          b * p ^ (r - 1) ≤ a + b * p ^ (r - 1) := Nat.le_add_left _ _
          _ = 1 := hBeq
      have : 2 ≤ 1 := hpowlarge.trans (hle.trans hleone)
      omega
    have ha1 : a = 1 := by simpa [hb0] using hBeq
    calc
      n = a * p + b := hnapb
      _ = p := by simp [ha1, hb0]
  · left
    have hi' : i + 1 < r := by omega
    have hip : i ≤ r - 2 := by omega
    have hmul_lt : n * p ^ i < p ^ r := by
      calc
        n * p ^ i < p ^ 2 * p ^ i := Nat.mul_lt_mul_of_pos_right hn (pow_pos hp.pos i)
        _ = p ^ (2 + i) := by rw [pow_add]
        _ ≤ p ^ r := Nat.pow_le_pow_right hp.pos (by omega)
    have hlt : n * p ^ i - 1 < p ^ r - 1 := by omega
    have hzero := Nat.eq_zero_of_dvd_of_lt hdiv hlt
    have hmul_one : n * p ^ i = 1 := by omega
    have hnle : n ≤ n * p ^ i := Nat.le_mul_of_pos_right n (pow_pos hp.pos i)
    have hpowle : p ^ i ≤ n * p ^ i := by
      rw [mul_comm]
      exact Nat.le_mul_of_pos_right _ hn0
    have hn1 : n = 1 := by omega
    refine ⟨hn1, ?_⟩
    by_contra hi0
    have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
    have : p ≤ p ^ i := by
      calc
        p = p ^ 1 := by simp
        _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos hi_pos
    omega

/-! ## A finite-field weighted power sum -/

private theorem sum_pow_finiteField
    (k : Type*) [Field k] [Fintype k] (e : ℕ) (he : 0 < e) :
    (∑ x : k, x ^ e) = if Fintype.card k - 1 ∣ e then -1 else 0 := by
  classical
  calc
    (∑ x : k, x ^ e) = ∑ x : kˣ, ((x : k) ^ e) := by
      rw [Fintype.sum_eq_add_sum_subtype_ne _ 0, zero_pow he.ne', zero_add]
      simpa using
        (Equiv.sum_comp unitsEquivNeZero
          (fun x : {x : k // x ≠ 0} ↦ (x : k) ^ e)).symm
    _ = if Fintype.card k - 1 ∣ e then -1 else 0 :=
      FiniteField.sum_pow_units k e

private theorem weightedExponent_dvd_iff
    {p r n i : ℕ} (hp : p.Prime) (hr : 3 ≤ r)
    (hn0 : 0 < n) (hn : n < p ^ 2) (hi : i < r) :
    p ^ r - 1 ∣ p ^ r - 2 + n * p ^ i ↔
      (n = 1 ∧ i = 0) ∨ (n = p ∧ i + 1 = r) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hq8 : 8 ≤ p ^ r := by
    exact (show 8 = 2 ^ 3 by norm_num) ▸
      (Nat.pow_le_pow_left hp2 3).trans (Nat.pow_le_pow_right hp.pos hr)
  have hmul : 0 < n * p ^ i := Nat.mul_pos hn0 (pow_pos hp.pos i)
  have hexp : p ^ r - 2 + n * p ^ i =
      (p ^ r - 1) + (n * p ^ i - 1) := by omega
  constructor
  · intro hd
    have hd' : p ^ r - 1 ∣
        (p ^ r - 1) + (n * p ^ i - 1) := by simpa only [hexp] using hd
    exact frobeniusOrbit_one_or_p hp hr hn0 hn hi
      ((Nat.dvd_add_iff_right (dvd_refl (p ^ r - 1))).mpr hd')
  · intro horbit
    have hsmall : p ^ r - 1 ∣ n * p ^ i - 1 := by
      rcases horbit with ⟨hn1, hi0⟩ | ⟨hnp, hilast⟩
      · subst n
        subst i
        simp
      · subst n
        have hir : i = r - 1 := by omega
        subst i
        have hpowr : p * p ^ (r - 1) = p ^ r := by
          rw [mul_comm, ← pow_succ]
          congr
        rw [hpowr]
    rw [hexp]
    exact dvd_add (dvd_refl _) hsmall

/-! ## The finite-field core -/

section FiniteFieldCore

variable {p : ℕ} [Fact p.Prime]
variable {k : Type*} [Field k] [Finite k] [Algebra (ZMod p) k] [CharP k p]

private noncomputable def addCharMulShiftEquiv
    (psi0 : FiniteAddChar k) (hpsi0 : psi0 ≠ 1)
    : k ≃ FiniteAddChar k :=
  Equiv.ofBijective psi0.mulShift <| by
    letI := Fintype.ofFinite k
    rw [Fintype.bijective_iff_injective_and_card, AddChar.card_eq]
    exact ⟨AddChar.to_mulShift_inj_of_isPrimitive
      (AddChar.IsPrimitive.of_ne_one hpsi0), rfl⟩

private noncomputable def addCharCoefficient
    (psi0 : FiniteAddChar k) (hpsi0 : psi0 ≠ 1)
    (phi : FiniteAddChar k) : k :=
  (addCharMulShiftEquiv psi0 hpsi0).symm phi

private theorem addCharCoefficient_spec
    (psi0 : FiniteAddChar k) (hpsi0 : psi0 ≠ 1)
    (phi : FiniteAddChar k) :
    psi0.mulShift (addCharCoefficient psi0 hpsi0 phi) = phi :=
  (addCharMulShiftEquiv psi0 hpsi0).apply_symm_apply phi

private theorem addChar_map_sum
    {A C : Type*} [AddCommMonoid A] [CommMonoid C] {ι : Type*}
    (chi : AddChar A C) (s : Finset ι) (g : ι → A) :
    chi (∑ i ∈ s, g i) = ∏ i ∈ s, chi (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi,
      chi.map_add_eq_mul, ih]

omit [Finite k] [CharP k p] in
private theorem trace_eq_of_traceChar_eq
    (psi : FiniteAddChar (ZMod p)) (hpsi : psi ≠ 1) {x y : k}
    (h : traceAddChar (ZMod p) k psi x = traceAddChar (ZMod p) k psi y) :
    Algebra.trace (ZMod p) k x = Algebra.trace (ZMod p) k y := by
  rw [traceAddChar_apply, traceAddChar_apply] at h
  apply_fun fun z ↦ z / psi (Algebra.trace (ZMod p) k y) at h
  have hone : psi (Algebra.trace (ZMod p) k x -
      Algebra.trace (ZMod p) k y) = 1 := by
    rw [AddChar.map_sub_eq_div, h, div_self]
    exact AddChar.val_isUnit _ _ |>.ne_zero
  exact sub_eq_zero.mp ((AddChar.IsPrimitive.of_ne_one hpsi).zmod_char_eq_one_iff p _ |>.mp hone)

/-- Weighted absolute traces isolate exactly coefficients `1` and `p` below
degree `p²`. This is the purely finite-field content of Lemma 8.3. -/
private theorem weightedTrace_eq_coeff_one_add_p
    (r : ℕ) (hr : r = Module.finrank (ZMod p) k) (hr3 : 3 ≤ r)
    (f : k[X]) (hf0 : f.coeff 0 = 0) (hdeg : f.natDegree < p ^ 2) :
    letI := Fintype.ofFinite k
    ∑ x : k, x ^ (Fintype.card k - 2) *
        algebraMap (ZMod p) k (Algebra.trace (ZMod p) k (f.eval x)) =
      -(f.coeff 1 + (f.coeff p) ^ p ^ (r - 1)) := by
  classical
  letI := Fintype.ofFinite k
  have hcard : Fintype.card k = p ^ r := by
    rw [hr]
    simpa only [ZMod.card] using
      (Module.card_eq_pow_finrank (K := ZMod p) (V := k))
  have hp := (Fact.out : p.Prime)
  have hp2 : 2 ≤ p := hp.two_le
  have hcard8 : 8 ≤ Fintype.card k := by
    rw [hcard]
    exact (show 8 = 2 ^ 3 by norm_num) ▸
      (Nat.pow_le_pow_left hp2 3).trans (Nat.pow_le_pow_right hp.pos hr3)
  calc
    (∑ x : k, x ^ (Fintype.card k - 2) *
        algebraMap (ZMod p) k (Algebra.trace (ZMod p) k (f.eval x))) =
        ∑ x : k, x ^ (Fintype.card k - 2) *
          ∑ i ∈ Finset.range r, (f.eval x) ^ p ^ i := by
      apply Finset.sum_congr rfl
      intro x _hx
      congr 1
      rw [FiniteField.algebraMap_trace_eq_sum_pow (ZMod p) k]
      simp only [Nat.card_zmod, ← hr]
    _ = ∑ x : k, x ^ (Fintype.card k - 2) *
          ∑ i ∈ Finset.range r,
            (∑ n ∈ Finset.range (p ^ 2), f.coeff n * x ^ n) ^ p ^ i := by
      simp_rw [Polynomial.eval_eq_sum_range' hdeg]
    _ = ∑ x : k, x ^ (Fintype.card k - 2) *
          ∑ i ∈ Finset.range r,
            ∑ n ∈ Finset.range (p ^ 2),
              (f.coeff n * x ^ n) ^ p ^ i := by
      simp_rw [sum_pow_char_pow]
    _ = ∑ i ∈ Finset.range r, ∑ n ∈ Finset.range (p ^ 2),
          (f.coeff n) ^ p ^ i *
            ∑ x : k, x ^ (Fintype.card k - 2 + n * p ^ i) := by
      have hterm (x : k) (n i : ℕ) :
          x ^ (Fintype.card k - 2) * (f.coeff n * x ^ n) ^ p ^ i =
            (f.coeff n) ^ p ^ i *
              x ^ (Fintype.card k - 2 + n * p ^ i) := by
        rw [mul_pow, ← pow_mul]
        calc
          x ^ (Fintype.card k - 2) *
                ((f.coeff n) ^ p ^ i * x ^ (n * p ^ i)) =
              (f.coeff n) ^ p ^ i *
                (x ^ (Fintype.card k - 2) * x ^ (n * p ^ i)) := by ring
          _ = (f.coeff n) ^ p ^ i *
                x ^ (Fintype.card k - 2 + n * p ^ i) := by rw [pow_add]
      simp_rw [Finset.mul_sum]
      simp_rw [hterm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_comm]
    _ = -(f.coeff 1 + (f.coeff p) ^ p ^ (r - 1)) := by
      have hweightPos (n i : ℕ) :
          0 < Fintype.card k - 2 + n * p ^ i := by omega
      simp_rw [sum_pow_finiteField k _ (hweightPos _ _), hcard]
      have hinner (i : ℕ) (hi : i < r) :
          (∑ n ∈ Finset.range (p ^ 2),
            f.coeff n ^ p ^ i *
              if p ^ r - 1 ∣ p ^ r - 2 + n * p ^ i then -1 else 0) =
            if i = 0 then -f.coeff 1
            else if i + 1 = r then -(f.coeff p ^ p ^ i)
            else 0 := by
        by_cases hi0 : i = 0
        · subst i
          simp only [if_pos]
          rw [Finset.sum_eq_single 1]
          · have hone : p ^ r - 1 ∣ p ^ r - 2 + 1 * p ^ 0 :=
              (weightedExponent_dvd_iff hp hr3 (by omega) (by nlinarith) (by omega)).2
                (Or.inl ⟨rfl, rfl⟩)
            rw [if_pos hone]
            simp
          · intro n hnmem hn1
            by_cases hn0 : n = 0
            · subst n
              simp [hf0]
            · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
              have hnlt : n < p ^ 2 := Finset.mem_range.mp hnmem
              have hnot : ¬p ^ r - 1 ∣ p ^ r - 2 + n * p ^ 0 := by
                intro hd
                rcases (weightedExponent_dvd_iff hp hr3 hnpos hnlt (by omega)).1 hd with
                  h | h
                · exact hn1 h.1
                · omega
              rw [if_neg hnot, mul_zero]
          · intro hnotmem
            exfalso
            apply hnotmem
            simp only [Finset.mem_range]
            nlinarith
        · rw [if_neg hi0]
          by_cases hilast : i + 1 = r
          · rw [if_pos hilast]
            rw [Finset.sum_eq_single p]
            · have hpMem : p < p ^ 2 := by nlinarith
              have hone : p ^ r - 1 ∣ p ^ r - 2 + p * p ^ i :=
                (weightedExponent_dvd_iff hp hr3 hp.pos hpMem hi).2
                  (Or.inr ⟨rfl, hilast⟩)
              rw [if_pos hone, mul_neg, mul_one]
            · intro n hnmem hnp
              by_cases hn0 : n = 0
              · subst n
                rw [hf0, zero_pow (pow_pos hp.pos i).ne', zero_mul]
              · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
                have hnlt : n < p ^ 2 := Finset.mem_range.mp hnmem
                have hnot : ¬p ^ r - 1 ∣ p ^ r - 2 + n * p ^ i := by
                  intro hd
                  rcases (weightedExponent_dvd_iff hp hr3 hnpos hnlt hi).1 hd with h | h
                  · exact hi0 h.2
                  · exact hnp h.1
                rw [if_neg hnot, mul_zero]
            · intro hnotmem
              exact (hnotmem (Finset.mem_range.mpr (by nlinarith))).elim
          · rw [if_neg hilast]
            apply Finset.sum_eq_zero
            intro n hnmem
            by_cases hn0 : n = 0
            · subst n
              rw [hf0, zero_pow (pow_pos hp.pos i).ne', zero_mul]
            · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
              have hnlt : n < p ^ 2 := Finset.mem_range.mp hnmem
              have hnot : ¬p ^ r - 1 ∣ p ^ r - 2 + n * p ^ i := by
                intro hd
                rcases (weightedExponent_dvd_iff hp hr3 hnpos hnlt hi).1 hd with h | h
                · exact hi0 h.2
                · exact hilast h.2
              rw [if_neg hnot, mul_zero]
      calc
        (∑ i ∈ Finset.range r, ∑ n ∈ Finset.range (p ^ 2),
            f.coeff n ^ p ^ i *
              if p ^ r - 1 ∣ p ^ r - 2 + n * p ^ i then -1 else 0) =
            ∑ i ∈ Finset.range r,
              (if i = 0 then -f.coeff 1
               else if i + 1 = r then -(f.coeff p ^ p ^ i)
               else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hinner i (Finset.mem_range.mp hi)
        _ = -(f.coeff 1 + (f.coeff p) ^ p ^ (r - 1)) := by
          let A : ℕ → k := fun i ↦
            if i = 0 then -f.coeff 1
            else if i + 1 = r then -(f.coeff p ^ p ^ i)
            else 0
          have hzeroMem : 0 ∈ Finset.range r := by simp; omega
          have hlastMem : r - 1 ∈ (Finset.range r).erase 0 := by
            simp only [Finset.mem_erase, Finset.mem_range]
            omega
          calc
            (∑ i ∈ Finset.range r,
                (if i = 0 then -f.coeff 1
                 else if i + 1 = r then -(f.coeff p ^ p ^ i)
                 else 0)) =
                ∑ i ∈ Finset.range r, A i := rfl
            _ = (∑ i ∈ (Finset.range r).erase 0, A i) + A 0 := by
              exact (Finset.sum_erase_add _ A hzeroMem).symm
            _ = A (r - 1) + A 0 := by
              congr 1
              apply Finset.sum_eq_single (r - 1)
              · intro i hi hine
                have hi0 : i ≠ 0 := Finset.ne_of_mem_erase hi
                have hilt : i < r := Finset.mem_range.mp (Finset.mem_of_mem_erase hi)
                have hilast : i + 1 ≠ r := by
                  intro h
                  apply hine
                  omega
                simp [A, hi0, hilast]
              · intro hnotmem
                exact (hnotmem hlastMem).elim
            _ = -(f.coeff 1 + (f.coeff p) ^ p ^ (r - 1)) := by
              have hrminus : r - 1 ≠ 0 := by omega
              have hrsucc : (r - 1) + 1 = r := by omega
              have hAlast : A (r - 1) = -(f.coeff p ^ p ^ (r - 1)) := by
                dsimp only [A]
                rw [if_neg hrminus, if_pos hrsucc]
              have hAzero : A 0 = -f.coeff 1 := by
                dsimp only [A]
                rw [if_pos rfl]
              rw [hAlast, hAzero]
              ring

/-- Pure finite-field polynomial rigidity. The phase of `f` is assumed to be
an actual additive character, and the conclusion retains only the Frobenius
orbit of degrees `1` and `p`. -/
theorem finiteFieldPolynomialRigidity
    (r : ℕ) (hr : r = Module.finrank (ZMod p) k) (hr3 : 3 ≤ r)
    (psi : FiniteAddChar (ZMod p)) (hpsi : psi ≠ 1)
    (f : k[X]) (hf0 : f.coeff 0 = 0) (hdeg : f.natDegree < p ^ 2)
    (phi : FiniteAddChar k)
    (hphase : ∀ x : k, traceAddChar (ZMod p) k psi (f.eval x) = phi x) :
    traceAddChar (ZMod p) k psi (f.eval 1) =
      traceAddChar (ZMod p) k psi (f.coeff 1 + f.coeff p) := by
  classical
  letI := Fintype.ofFinite k
  let psiK : FiniteAddChar k := traceAddChar (ZMod p) k psi
  have hpsiK : psiK ≠ 1 :=
    (traceAddChar_ne_one_iff (ZMod p) k psi).2 hpsi
  let gamma : k := addCharCoefficient psiK hpsiK phi
  have hgamma (x : k) : psiK (gamma * x) = phi x := by
    exact DFunLike.congr_fun (addCharCoefficient_spec psiK hpsiK phi) x
  have htrace (x : k) :
      Algebra.trace (ZMod p) k (f.eval x) =
        Algebra.trace (ZMod p) k (gamma * x) := by
    apply trace_eq_of_traceChar_eq psi hpsi
    exact (hphase x).trans (hgamma x).symm
  let g : k[X] := f - C gamma * X
  have hg0 : g.coeff 0 = 0 := by
    simp [g, hf0]
  have hlin : (C gamma * X : k[X]).natDegree ≤ 1 := by
    calc
      (C gamma * X : k[X]).natDegree ≤
          (C gamma : k[X]).natDegree + X.natDegree := natDegree_mul_le
      _ ≤ 1 := by simp
  have hp := (Fact.out : p.Prime)
  have hpSq : 1 < p ^ 2 := by nlinarith [hp.two_le]
  have hgdeg : g.natDegree < p ^ 2 := by
    exact (natDegree_sub_le f (C gamma * X)).trans_lt
      (max_lt hdeg (hlin.trans_lt hpSq))
  have hweighted := weightedTrace_eq_coeff_one_add_p r hr hr3 g hg0 hgdeg
  have htraceg (x : k) : Algebra.trace (ZMod p) k (g.eval x) = 0 := by
    rw [show g.eval x = f.eval x - gamma * x by simp [g], map_sub, htrace x, sub_self]
  have hsumzero :
      (∑ x : k, x ^ (Fintype.card k - 2) *
        algebraMap (ZMod p) k (Algebra.trace (ZMod p) k (g.eval x))) = 0 := by
    simp_rw [htraceg, map_zero, mul_zero, Finset.sum_const_zero]
  rw [hsumzero] at hweighted
  have hcoeff : g.coeff 1 + (g.coeff p) ^ p ^ (r - 1) = 0 := by
    exact neg_eq_zero.mp hweighted.symm
  have hg1 : g.coeff 1 = f.coeff 1 - gamma := by
    simp [g]
  have hgp : g.coeff p = f.coeff p := by
    have hp1 : p ≠ 1 := hp.ne_one
    dsimp only [g]
    rw [coeff_sub, coeff_C_mul_X, if_neg hp1, sub_zero]
  have htracePow :
      Algebra.trace (ZMod p) k ((f.coeff p) ^ p ^ (r - 1)) =
        Algebra.trace (ZMod p) k (f.coeff p) := by
    let sigma := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k
    have h := Algebra.trace_eq_of_algEquiv (sigma ^ (r - 1)) (f.coeff p)
    rw [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card] at h
    exact h
  have htraceCoeff := congrArg (Algebra.trace (ZMod p) k) hcoeff
  rw [hg1, hgp, map_add, map_sub, htracePow, map_zero] at htraceCoeff
  have htargetTrace :
      Algebra.trace (ZMod p) k (f.coeff 1 + f.coeff p) =
        Algebra.trace (ZMod p) k gamma := by
    rw [map_add]
    linear_combination htraceCoeff
  rw [traceAddChar_apply, traceAddChar_apply]
  apply congrArg psi
  exact (htrace 1).trans (by simpa using htargetTrace.symm)

/-- Character-by-character form of the finite-field core. Each monomial may
carry its own additive coefficient character. -/
private theorem finiteFieldMonomialRigidity
    (r : ℕ) (hr : r = Module.finrank (ZMod p) k) (hr3 : 3 ≤ r)
    (theta : ℕ → FiniteAddChar k) (htheta0 : theta 0 = 1)
    (phi : FiniteAddChar k)
    (hphase : ∀ x : k,
      (∏ n ∈ Finset.range (p ^ 2), theta n (x ^ n)) = phi x) :
    (∏ n ∈ Finset.range (p ^ 2), theta n 1) =
      theta 1 1 * theta p 1 := by
  classical
  let psi : FiniteAddChar (ZMod p) :=
    AddChar.FiniteField.primitiveChar_to_Complex (ZMod p)
  have hpsiPrimitive : psi.IsPrimitive :=
    AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (ZMod p)
  have hpsi : psi ≠ 1 := by
    rw [AddChar.zmod_char_ne_one_iff p]
    intro hone
    have := (hpsiPrimitive.zmod_char_eq_one_iff p 1).mp hone
    simp at this
  let psiK : FiniteAddChar k := traceAddChar (ZMod p) k psi
  have hpsiK : psiK ≠ 1 :=
    (traceAddChar_ne_one_iff (ZMod p) k psi).2 hpsi
  let beta : ℕ → k := fun n ↦ addCharCoefficient psiK hpsiK (theta n)
  have hbeta (n : ℕ) (x : k) : psiK (beta n * x) = theta n x := by
    exact DFunLike.congr_fun (addCharCoefficient_spec psiK hpsiK (theta n)) x
  let P : k[X] := ∑ n ∈ Finset.range (p ^ 2), monomial n (beta n)
  have hPcoeff (m : ℕ) : P.coeff m = if m < p ^ 2 then beta m else 0 := by
    simp [P, coeff_monomial, Finset.sum_ite_eq']
  have hbeta0 : beta 0 = 0 := by
    apply (addCharMulShiftEquiv psiK hpsiK).injective
    change psiK.mulShift (beta 0) = psiK.mulShift 0
    rw [addCharCoefficient_spec, htheta0]
    simp
  have hP0 : P.coeff 0 = 0 := by
    rw [hPcoeff, if_pos]
    · exact hbeta0
    · have hp := (Fact.out : p.Prime)
      nlinarith [hp.two_le]
  have hPdeg : P.natDegree < p ^ 2 := by
    by_cases hPzero : P = 0
    · rw [hPzero, natDegree_zero]
      have hp := (Fact.out : p.Prime)
      nlinarith [hp.two_le]
    · rw [natDegree_lt_iff_degree_lt hPzero, degree_lt_iff_coeff_zero]
      intro m hm
      rw [hPcoeff, if_neg (not_lt_of_ge hm)]
  have hphaseP (x : k) : psiK (P.eval x) = phi x := by
    calc
      psiK (P.eval x) =
          psiK (∑ n ∈ Finset.range (p ^ 2), beta n * x ^ n) := by
            congr 1
            change (evalRingHom x) P = _
            simp [P, eval_monomial]
      _ = ∏ n ∈ Finset.range (p ^ 2), psiK (beta n * x ^ n) :=
        addChar_map_sum psiK _ _
      _ = ∏ n ∈ Finset.range (p ^ 2), theta n (x ^ n) := by
        apply Finset.prod_congr rfl
        intro n _hn
        exact hbeta n (x ^ n)
      _ = phi x := hphase x
  have hrigidity := finiteFieldPolynomialRigidity r hr hr3 psi hpsi P hP0 hPdeg phi hphaseP
  have hp := (Fact.out : p.Prime)
  have honeMem : 1 < p ^ 2 := by nlinarith [hp.two_le]
  have hpMem : p < p ^ 2 := by nlinarith [hp.two_le]
  calc
    (∏ n ∈ Finset.range (p ^ 2), theta n 1) = phi 1 := by
      simpa using hphase 1
    _ = psiK (P.eval 1) := (hphaseP 1).symm
    _ = psiK (P.coeff 1 + P.coeff p) := hrigidity
    _ = theta 1 1 * theta p 1 := by
      rw [psiK.map_add_eq_mul, hPcoeff, if_pos honeMem, hPcoeff, if_pos hpMem,
        show psiK (beta 1) = theta 1 1 by simpa using hbeta 1 1,
        show psiK (beta p) = theta p 1 by simpa using hbeta p 1]

end FiniteFieldCore

/-! ## Teichmüller carries -/

/-- The additive carry of the canonical Teichmüller section is divisible by
the residue characteristic in the valuation ring. The argument works in
mixed and equal characteristic: modulo `p` the carry is Frobenius-fixed,
while its positive valuation forces it to vanish unless it is already in
`p 𝒪_F`. -/
private theorem teichmuller_add_carry
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (x y : ResidueField F) :
    ∃ z : ringOfIntegers F,
      ((teichmuller F (x + y) : ringOfIntegers F) : F) -
          (teichmuller F x : F) - (teichmuller F y : F) =
        (residueCharacteristic F : F) * (z : F) := by
  classical
  let p := residueCharacteristic F
  letI : Fact p.Prime := ⟨residueCharacteristic_prime F⟩
  letI : Algebra (ZMod p) (ResidueField F) := ZMod.algebra _ p
  let r := Module.finrank (ZMod p) (ResidueField F)
  let R := ringOfIntegers F
  let I : Ideal R := Ideal.span {(p : R)}
  let d : R := teichmuller F (x + y) - teichmuller F x - teichmuller F y
  have hpNonunit : (p : R) ∈ nonunits R := by
    rw [← IsLocalRing.mem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]
    change residueMap F (p : R) = 0
    simp [p, residueCharacteristic]
  letI : CharP (R ⧸ I) p := CharP.quotient R p hpNonunit
  have hcard : residueCard F = p ^ r := by
    letI := residueFieldFintype F
    change Fintype.card (ResidueField F) = p ^ r
    simpa only [ZMod.card] using
      (Module.card_eq_pow_finrank (K := ZMod p) (V := ResidueField F))
  have hfix (u : ResidueField F) :
      (Ideal.Quotient.mk I (teichmuller F u)) ^ p ^ r =
        Ideal.Quotient.mk I (teichmuller F u) := by
    rw [← map_pow, ← hcard, teichmuller_pow_residueCard]
  have hdQuot : Ideal.Quotient.mk I (d ^ residueCard F - d) = 0 := by
    rw [map_sub, map_pow, hcard]
    simp only [d, map_sub]
    rw [sub_pow_char_pow (R := R ⧸ I) (p := p) _ _ r,
      sub_pow_char_pow (R := R ⧸ I) (p := p) _ _ r,
      hfix, hfix, hfix]
    ring
  have hdSpan : d ^ residueCard F - d ∈ I :=
    Ideal.Quotient.eq_zero_iff_mem.mp hdQuot
  change d ^ residueCard F - d ∈ Ideal.span {(p : R)} at hdSpan
  rw [Ideal.mem_span_singleton'] at hdSpan
  obtain ⟨z, hz⟩ := hdSpan
  have hdResidue : residueMap F d = 0 := by simp [d]
  have hdLattice : (d : F) ∈ lattice F 1 :=
    (residueMap_eq_zero_iff F d).mp hdResidue
  have hdPos : ((1 : ℤ) : WithTop ℤ) ≤ ord F (d : F) :=
    (mem_lattice F).mp hdLattice
  have hzIntegral : 0 ≤ ord F (z : F) :=
    (ord_nonneg_iff_mem_integer F (z : F)).mpr z.property
  have hfield : (d : F) ^ residueCard F - (d : F) =
      (p : F) * (z : F) := by
    have := congrArg (fun w : R ↦ (w : F)) hz
    simpa [map_sub, map_pow, mul_comm] using this.symm
  have hpOrd : ord F (p : F) ≤ ord F (d : F) := by
    by_contra hnot
    have hlt : ord F (d : F) < ord F (p : F) := lt_of_not_ge hnot
    have hd0 : (d : F) ≠ 0 := by
      intro hdzero
      rw [hdzero, ord_zero] at hlt
      exact (not_lt_of_ge le_top) hlt
    obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp
      ((ord_ne_top_iff F).mpr hd0)
    have hvPos : 1 ≤ v := by
      rw [← hv] at hdPos
      exact_mod_cast hdPos
    have hq2 : 2 ≤ residueCard F := by
      have := one_lt_residueCard F
      omega
    have hpowGt : ord F (d : F) < ord F ((d : F) ^ residueCard F) := by
      rw [ord_pow, ← hv, ← WithTop.coe_nsmul]
      exact_mod_cast (show v < residueCard F • v by
        simp only [nsmul_eq_mul]
        nlinarith)
    have hdiffOrd : ord F ((d : F) ^ residueCard F - (d : F)) =
        ord F (d : F) := by
      rw [sub_eq_add_neg, ord_add_eq_min F, ord_neg,
        min_eq_right hpowGt.le]
      rw [ord_neg]
      exact ne_of_gt hpowGt
    have hpLeRhs : ord F (p : F) ≤ ord F ((p : F) * (z : F)) := by
      rw [ord_mul]
      exact le_add_of_nonneg_right hzIntegral
    rw [hfield] at hdiffOrd
    exact (not_le_of_gt hlt) (hdiffOrd ▸ hpLeRhs)
  by_cases hp0 : (p : F) = 0
  · have htop : (⊤ : WithTop ℤ) ≤ ord F (d : F) := by
      simpa [hp0, ord_zero] using hpOrd
    have hd0 : (d : F) = 0 :=
      (ord_eq_top_iff F).mp (top_unique htop)
    refine ⟨0, ?_⟩
    simpa [d, p, hp0] using hd0
  have hquotIntegral : (d : F) / (p : F) ∈ ringOfIntegers F := by
    rw [← ord_nonneg_iff_mem_integer, ord_div]
    by_cases hd0 : (d : F) = 0
    · simp [hd0]
    obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp
      ((ord_ne_top_iff F).mpr hd0)
    obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp
      ((ord_ne_top_iff F).mpr hp0)
    have hev : e ≤ v := by
      rw [← he, ← hv] at hpOrd
      exact_mod_cast hpOrd
    rw [← hv, ← he]
    change (0 : WithTop ℤ) ≤ ((v - e : ℤ) : WithTop ℤ)
    exact WithTop.coe_le_coe.mpr (sub_nonneg.mpr hev)
  let w : R := ⟨(d : F) / (p : F), hquotIntegral⟩
  have hdp : (d : F) = (p : F) * (w : F) := by
    change (d : F) = (p : F) * ((d : F) / (p : F))
    rw [mul_comm, div_mul_cancel₀ _ hp0]
  refine ⟨w, ?_⟩
  simpa [d, p] using hdp

/-! ## Local-field specialization -/

section LocalFieldRigidity

variable {M M' : Type*} [Field M] [Field M']
variable [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
variable [ValuativeRel M'] [TopologicalSpace M'] [IsNonarchimedeanLocalField M']
variable [Algebra M M'] [ValuativeExtension M M'] [Module.Finite M M']

/-- Polynomial rigidity over a local field (Lemma 8.3, `O:M:rigidity`).
The character upstairs is the actual trace pullback, and the phase is
evaluated on FML's canonical Teichmüller representatives. The cardinality
equation in `habsoluteDegree` is the intrinsic assertion that the absolute
residue degree is some `r ≥ 3`; the prime-field algebra and characteristic
used by the finite-field argument are derived inside the proof. -/
theorem polynomialRigidity
    {p : ℕ}
    (hchar : residueCharacteristic M = p)
    (psi : ContinuousAddChar M) (f : M[X])
    (hf0 : f.coeff 0 = 0) (hdeg : f.natDegree < p ^ 2)
    (hcoeff : ∀ n ∈ f.support, ∀ x : ringOfIntegers M,
      (psi (f.coeff n * (x : M))) ^ p = 1)
    (hunr : ramificationIndex M M' = 1)
    (hdegree : Nat.Coprime (Module.finrank M M') p)
    (habsoluteDegree : ∃ r : ℕ,
      3 ≤ r ∧ residueCard M' = (residueCharacteristic M') ^ r)
    (hphase : ∀ x y : ResidueField M',
      psi.compTrace
          (f.eval₂ (algebraMap M M') (teichmuller M' (x + y) : M')) =
        psi.compTrace (f.eval₂ (algebraMap M M') (teichmuller M' x : M')) *
          psi.compTrace (f.eval₂ (algebraMap M M') (teichmuller M' y : M'))) :
    psi (f.eval 1) = psi (f.coeff 1 + f.coeff p) := by
  classical
  have hchar' : residueCharacteristic M' = p :=
    (residueCharacteristic_extension_eq M M').trans hchar
  letI : Fact p.Prime := ⟨hchar ▸ residueCharacteristic_prime M⟩
  letI : CharP (ResidueField M') p := ringChar.of_eq hchar'
  letI : Algebra (ZMod p) (ResidueField M') := ZMod.algebra _ _
  obtain ⟨r, hr3, hresidueCard⟩ := habsoluteDegree
  have hcardFinrank : residueCard M' =
      p ^ Module.finrank (ZMod p) (ResidueField M') := by
    letI : Fintype (ResidueField M') := residueFieldFintype M'
    change Fintype.card (ResidueField M') = _
    simpa only [ZMod.card] using
      (Module.card_eq_pow_finrank
        (K := ZMod p) (V := ResidueField M'))
  have hr : r = Module.finrank (ZMod p) (ResidueField M') := by
    apply Nat.pow_right_injective ((Fact.out : p.Prime).two_le)
    exact (hchar' ▸ hresidueCard).symm.trans hcardFinrank
  have hr3' : 3 ≤ Module.finrank (ZMod p) (ResidueField M') := hr ▸ hr3
  let psi' : ContinuousAddChar M' := psi.compTrace
  let T : ResidueField M' → M' := fun x ↦ (teichmuller M' x : M')
  have hcoeffAll (n : ℕ) (x : ringOfIntegers M) :
      (psi (f.coeff n * (x : M))) ^ p = 1 := by
    by_cases hn : n ∈ f.support
    · exact hcoeff n hn x
    · rw [mem_support_iff] at hn
      have hzero : f.coeff n = 0 := not_ne_iff.mp hn
      simp [hzero]
  have hcoeffPhaseAdd (n : ℕ) (x y : ResidueField M') :
      (psi' (algebraMap M M' (f.coeff n) * T (x + y)) : ℂ) =
        (psi' (algebraMap M M' (f.coeff n) * T x) : ℂ) *
          (psi' (algebraMap M M' (f.coeff n) * T y) : ℂ) := by
    obtain ⟨z, hz⟩ := teichmuller_add_carry M' x y
    have hchar' : residueCharacteristic M' = p :=
      (residueCharacteristic_extension_eq M M').trans hchar
    have hzM' : (z : M') ∈ lattice M' 0 :=
      (mem_lattice_zero_iff M').2 z.property
    have hzTrace : trace M M' (z : M') ∈ lattice M 0 :=
      trace_mem_lattice M M' hunr 0 hzM'
    let zM : ringOfIntegers M :=
      ⟨trace M M' (z : M'), (mem_lattice_zero_iff M).1 hzTrace⟩
    have hroot : (psi (f.coeff n * (zM : M))) ^ p = 1 :=
      hcoeffAll n zM
    have htraceScalar :
        trace M M'
            ((p : M') * (algebraMap M M' (f.coeff n) * (z : M'))) =
          p • (f.coeff n * (zM : M)) := by
      have hs := (Algebra.trace M M').map_smul
        ((p : M) * f.coeff n) (z : M')
      simpa [zM, Algebra.smul_def, nsmul_eq_mul, mul_assoc, mul_comm,
        mul_left_comm] using hs
    have hkill :
        psi' ((p : M') * (algebraMap M M' (f.coeff n) * (z : M'))) = 1 := by
      change psi.compTrace
        ((p : M') * (algebraMap M M' (f.coeff n) * (z : M'))) = 1
      rw [ContinuousAddChar.compTrace_apply, htraceScalar]
      exact (psi.toAddChar.map_nsmul_eq_pow p (f.coeff n * (zM : M))).trans hroot
    have hz' : T (x + y) = T x + T y + (p : M') * (z : M') := by
      dsimp only [T]
      rw [show residueCharacteristic M' = p from hchar'] at hz
      linear_combination hz
    have harg : algebraMap M M' (f.coeff n) * T (x + y) =
        algebraMap M M' (f.coeff n) * T x +
          algebraMap M M' (f.coeff n) * T y +
            (p : M') * (algebraMap M M' (f.coeff n) * (z : M')) := by
      rw [hz']
      ring
    rw [harg, psi'.map_add_eq_mul, psi'.map_add_eq_mul, hkill]
    simp
  let theta : ℕ → FiniteAddChar (ResidueField M') := fun n ↦
    { toFun := fun x ↦
        (psi' (algebraMap M M' (f.coeff n) * T x) : ℂ)
      map_zero_eq_one' := by simp [T]
      map_add_eq_mul' := hcoeffPhaseAdd n }
  have htheta0 : theta 0 = 1 := by
    ext x
    simp [theta, hf0]
  let phi : FiniteAddChar (ResidueField M') :=
    { toFun := fun x ↦
        (psi' (f.eval₂ (algebraMap M M') (T x)) : ℂ)
      map_zero_eq_one' := by simp [T, hf0]
      map_add_eq_mul' := by
        intro x y
        exact congrArg Units.val (hphase x y) }
  have hfinitePhase (x : ResidueField M') :
      (∏ n ∈ Finset.range (p ^ 2), theta n (x ^ n)) = phi x := by
    have heval :
        f.eval₂ (algebraMap M M') (T x) =
          ∑ n ∈ Finset.range (p ^ 2),
            algebraMap M M' (f.coeff n) * T (x ^ n) := by
      rw [eval₂_eq_sum_range' (algebraMap M M') hdeg]
      apply Finset.sum_congr rfl
      intro n _hn
      rw [show T (x ^ n) = T x ^ n by
        exact congrArg (fun z : ringOfIntegers M' ↦ (z : M'))
          (map_pow (teichmuller M') x n)]
    calc
      (∏ n ∈ Finset.range (p ^ 2), theta n (x ^ n)) =
          psi'.toComplexAddChar
            (∑ n ∈ Finset.range (p ^ 2),
              algebraMap M M' (f.coeff n) * T (x ^ n)) := by
            rw [addChar_map_sum]
            rfl
      _ = phi x := by rw [← heval]; rfl
  have hfinite := finiteFieldMonomialRigidity
    (p := p) (k := ResidueField M')
    (Module.finrank (ZMod p) (ResidueField M')) rfl hr3'
    theta htheta0 phi hfinitePhase
  have hupComplex :
      (psi' (f.eval₂ (algebraMap M M') (T 1)) : ℂ) =
        (psi' (algebraMap M M' (f.coeff 1 + f.coeff p)) : ℂ) := by
    calc
      (psi' (f.eval₂ (algebraMap M M') (T 1)) : ℂ) = phi 1 := rfl
      _ = ∏ n ∈ Finset.range (p ^ 2), theta n 1 := by
        simpa using (hfinitePhase 1).symm
      _ = theta 1 1 * theta p 1 := hfinite
      _ = (psi' (algebraMap M M' (f.coeff 1 + f.coeff p)) : ℂ) := by
        change (psi' (algebraMap M M' (f.coeff 1) * T 1) : ℂ) *
            (psi' (algebraMap M M' (f.coeff p) * T 1) : ℂ) = _
        have hT1 : T 1 = 1 := by simp [T]
        rw [hT1, mul_one, mul_one, map_add]
        exact congrArg Units.val
          (psi'.map_add_eq_mul (algebraMap M M' (f.coeff 1))
            (algebraMap M M' (f.coeff p))).symm
  have hup :
      psi' (f.eval₂ (algebraMap M M') (T 1)) =
        psi' (algebraMap M M' (f.coeff 1 + f.coeff p)) :=
    Units.ext hupComplex
  let d := Module.finrank M M'
  have hupBase :
      psi (d • f.eval 1) = psi (d • (f.coeff 1 + f.coeff p)) := by
    have hevalOne :
        f.eval₂ (algebraMap M M') (T 1) = algebraMap M M' (f.eval 1) := by
      rw [show T 1 = 1 by simp [T], eval₂_at_one]
    rw [hevalOne] at hup
    change psi.compTrace (algebraMap M M' (f.eval 1)) =
      psi.compTrace (algebraMap M M' (f.coeff 1 + f.coeff p)) at hup
    rw [ContinuousAddChar.compTrace_apply, ContinuousAddChar.compTrace_apply,
      trace_algebraMap, trace_algebraMap] at hup
    simpa only [d] using hup
  have hpowDegree :
      (psi (f.eval 1)) ^ d = (psi (f.coeff 1 + f.coeff p)) ^ d := by
    calc
      (psi (f.eval 1)) ^ d = psi (d • f.eval 1) :=
        (psi.toAddChar.map_nsmul_eq_pow d (f.eval 1)).symm
      _ = psi (d • (f.coeff 1 + f.coeff p)) := hupBase
      _ = (psi (f.coeff 1 + f.coeff p)) ^ d :=
        psi.toAddChar.map_nsmul_eq_pow d (f.coeff 1 + f.coeff p)
  let oneO : ringOfIntegers M := ⟨1, by simp⟩
  have hcoefficientRoot (n : ℕ) : (psi (f.coeff n)) ^ p = 1 := by
    simpa [oneO] using hcoeffAll n oneO
  have hphaseRoot : (psi (f.eval 1)) ^ p = 1 := by
    have heval : f.eval 1 = ∑ n ∈ Finset.range (p ^ 2), f.coeff n := by
      simpa using eval_eq_sum_range' hdeg (1 : M)
    have hprod : psi (f.eval 1) =
        ∏ n ∈ Finset.range (p ^ 2), psi (f.coeff n) := by
      rw [heval]
      exact addChar_map_sum psi.toAddChar _ _
    rw [hprod, ← Finset.prod_pow]
    simp only [hcoefficientRoot, Finset.prod_const_one]
  have htargetRoot : (psi (f.coeff 1 + f.coeff p)) ^ p = 1 := by
    rw [psi.map_add_eq_mul, mul_pow, hcoefficientRoot, hcoefficientRoot,
      one_mul]
  let w : ℂˣ := psi (f.eval 1) / psi (f.coeff 1 + f.coeff p)
  have hwDegree : w ^ d = 1 := by
    dsimp only [w]
    rw [div_pow, hpowDegree]
    simp
  have hwPrime : w ^ p = 1 := by
    dsimp only [w]
    rw [div_pow, hphaseRoot, htargetRoot]
    simp
  have horderDegree : orderOf w ∣ d := orderOf_dvd_of_pow_eq_one hwDegree
  have horderPrime : orderOf w ∣ p := orderOf_dvd_of_pow_eq_one hwPrime
  have horderOne : orderOf w ∣ 1 := by
    rw [← hdegree.gcd_eq_one]
    exact Nat.dvd_gcd horderDegree horderPrime
  have hw : w = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp horderOne)
  exact div_eq_one.mp hw

end LocalFieldRigidity

end

end LanglandsSecondMainLemma.Finite
