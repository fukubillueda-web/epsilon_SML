import LanglandsFirstMainLemma.Parameters.Low
import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Total.TwistedEstimates
import LanglandsSecondMainLemma.Local.Newton
import LanglandsSecondMainLemma.Odd.Total.ConjugateRoots

/-!
# Odd / Total / Translated Norm

Supporting calculations for Paper `O:A:lem:translate` and
`O:A:eq:unit-correction`. All corrections below are formed from an actual
root of the Artin--Schreier polynomial. The cubic calculation retains the
second iterate. Lattice depths are integers and orders take values in
`WithTop ℤ`.

The final theorem constructs one genuine coordinate, retains its twisted
estimates, and proves the weighted translated-norm congruence. The norm
correction keeps the linear trace and the cubic affine term. Distinct
Teichmuller representatives enumerate all actual conjugates; restriction
of the actual Galois automorphisms identifies their norm sum with the
lower trace. No congruence or enumeration is assumed.
-/

namespace LanglandsSecondMainLemma.Odd.Total

open LanglandsFirstMainLemma
open Polynomial
open scoped BigOperators

noncomputable section

private theorem pow_mem_int_lattice
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    {x : L} {q : ℤ} (hx : x ∈ lattice L q) (n : ℕ) :
    x ^ n ∈ lattice L ((n : ℤ) * q) := by
  rw [mem_lattice] at hx ⊢
  rw [ord_pow]
  simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using nsmul_le_nsmul_right hx n

private theorem natCast_mem_int_lattice_zero
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (n : ℕ) : (n : L) ∈ lattice L 0 := by
  rw [mem_lattice]
  exact (ord_nonneg_iff_mem_integer L _).2 (n : ringOfIntegers L).property

/-- The multiplicative correction associated to the actual additive
correction `eta`. The denominator is the translated root, in the upper
field. -/
def translatedRootUnit {L : Type*} [Field L] (Delta xi eta : L) : L :=
  eta / (Delta + xi)

/-- Dividing the exact shifted-polynomial residual by the translated
root. Later polynomial estimates must retain this quotient's leading term. -/
def translatedRootResidual {L : Type*} [Field L]
    (p : ℕ) (Delta xi : L) : L :=
  ((Delta + xi) ^ p - (Delta + xi) - (Delta ^ p - Delta)) / (Delta + xi)

/-- The actual additive correction factors multiplicatively, provided the
translated root is nonzero. -/
theorem translatedRoot_factor {L : Type*} [Field L]
    (Delta xi eta : L) (hD : Delta + xi ≠ 0) :
    Delta + xi + eta = (Delta + xi) * (1 + translatedRootUnit Delta xi eta) := by
  dsimp only [translatedRootUnit]
  field_simp

/-- The norm factor is the norm of the genuine multiplicative correction. -/
theorem translatedRoot_norm_factor
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    (Delta xi eta : L) (hD : Delta + xi ≠ 0) :
    norm E L (Delta + xi + eta) =
      norm E L (Delta + xi) * norm E L (1 + translatedRootUnit Delta xi eta) := by
  rw [translatedRoot_factor Delta xi eta hD, map_mul]

/-- The Hensel displacement bound becomes `V-(p-2)t` after division by
`Delta+xi`, whose order is `-t`. No finite order is imposed on `eta`. -/
theorem translatedRootUnit_mem
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    (p : ℕ) (t V : ℤ) (Delta xi eta : L)
    (hD : ord L (Delta + xi) = ((-t : ℤ) : WithTop ℤ))
    (heta : eta ∈ lattice L (V - ((p : ℤ) - 1) * t)) :
    translatedRootUnit Delta xi eta ∈ lattice L (V - ((p : ℤ) - 2) * t) := by
  have hi : (Delta + xi)⁻¹ ∈ lattice L t := by
    rw [mem_lattice, ord_inv, hD, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
    exact WithTop.coe_le_coe.mpr (by omega)
  simp only [translatedRootUnit, div_eq_mul_inv]
  convert mul_mem_lattice L heta hi using 1; ring

/-- Exact correction equation, prior to any valuation estimate. It is
valid in both characteristics and uses the actual root equation. -/
theorem translatedRootUnit_equation
    {L : Type*} [Field L] {p : ℕ} (hp : 0 < p)
    (Delta xi eta : L) (hD : Delta + xi ≠ 0)
    (hroot : (Delta + xi + eta) ^ p - (Delta + xi + eta) = Delta ^ p - Delta) :
    let D := Delta + xi
    let u := translatedRootUnit Delta xi eta
    u = translatedRootResidual p Delta xi +
      D ^ (p - 1) * ((1 + u) ^ p - 1) := by
  dsimp only
  have hmul : (Delta + xi) ^ p = (Delta + xi) * (Delta + xi) ^ (p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hp]
  have h := hroot
  rw [translatedRoot_factor Delta xi eta hD, mul_pow, hmul] at h
  apply (mul_left_cancel₀ hD)
  dsimp only [translatedRootResidual]
  rw [mul_add, mul_div_cancel₀ _ hD]
  linear_combination -h - hmul

/-- A prime power of a principal unit at the precision needed for the
first Newton error. The two numerical assumptions keep both the binomial
terms divisible by `p` and the terminal term `u^p`. -/
theorem translatedUnit_prime_power_mem
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    {p : ℕ} (hp : p.Prime) (V q : ℤ) (hq : 0 ≤ q)
    (hpq : V ≤ ((p : ℤ) - 1) * q)
    (hpval : (p : L) ∈ lattice L V)
    (u : L) (hu : u ∈ lattice L q) :
    (1 + u) ^ p - 1 ∈ lattice L (V + q) := by
  have heq := (Commute.all u (1 : L)).add_pow_prime_eq' hp
  simp only [one_pow, mul_one] at heq
  have hsum : (∑ j ∈ Finset.Ioo 0 p,
      u ^ j * ((p.choose j / p : ℕ) : L)) ∈ lattice L q := by
    apply sum_mem_lattice L
    intro j hj
    have hjpos : 1 ≤ j := (Finset.mem_Ioo.mp hj).1
    have hjq : q ≤ (j : ℤ) * q := by
      have hjZ : (1 : ℤ) ≤ j := by exact_mod_cast hjpos
      nlinarith
    have hpow := lattice_antitone L hjq (pow_mem_int_lattice L hu j)
    simpa using mul_mem_lattice L hpow (natCast_mem_int_lattice_zero L _)
  have hlast : u ^ p ∈ lattice L (V + q) :=
    lattice_antitone L (by nlinarith) (pow_mem_int_lattice L hu p)
  have hformula : (1 + u) ^ p - 1 =
      u ^ p + (p : L) * ∑ j ∈ Finset.Ioo 0 p,
        u ^ j * ((p.choose j / p : ℕ) : L) := by
    rw [add_comm 1 u, heq]
    ring
  rw [hformula]
  exact (lattice L _).add_mem hlast (mul_mem_lattice L hpval hsum)

/-- The first iterate bound `2V-(2p-3)t` for the actual translated root.
The prime coefficient has finite valuation; the correction itself may
vanish. In degree three this estimate is subsequently refined. -/
theorem translatedRootUnit_first_iterate
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    {p : ℕ} (hp : p.Prime) (t V : ℤ) (ht : 0 ≤ t)
    (hVt : ((p : ℤ) - 1) * t ≤ V)
    (Delta xi eta : L)
    (hD : ord L (Delta + xi) = ((-t : ℤ) : WithTop ℤ))
    (hV : ord L (p : L) = (V : WithTop ℤ))
    (heta : eta ∈ lattice L (V - ((p : ℤ) - 1) * t))
    (hroot : (Delta + xi + eta) ^ p - (Delta + xi + eta) = Delta ^ p - Delta) :
    translatedRootUnit Delta xi eta - translatedRootResidual p Delta xi ∈
      lattice L (2 * V - (2 * (p : ℤ) - 3) * t) := by
  let q := V - ((p : ℤ) - 2) * t
  have hpZ : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hq : 0 ≤ q := by dsimp only [q]; nlinarith
  have hpq : V ≤ ((p : ℤ) - 1) * q := by
    have hprod := mul_nonneg (sub_nonneg.mpr hpZ)
      (sub_nonneg.mpr hVt)
    dsimp only [q]
    nlinarith only [hprod]
  have hu := translatedRootUnit_mem L p t V Delta xi eta hD heta
  have hpower := translatedUnit_prime_power_mem L hp V q hq hpq
    (by rw [mem_lattice, hV]) (translatedRootUnit Delta xi eta) hu
  have hDmem : Delta + xi ∈ lattice L (-t) := by rw [mem_lattice, hD]
  have hDpow := pow_mem_int_lattice L hDmem (p - 1)
  have hDne : Delta + xi ≠ 0 := (ord_ne_top_iff L).1 (by
    rw [hD]; exact WithTop.coe_ne_top)
  have heq := translatedRootUnit_equation hp.pos Delta xi eta hDne hroot
  dsimp only at heq
  have hdiff : translatedRootUnit Delta xi eta - translatedRootResidual p Delta xi =
      (Delta + xi) ^ (p - 1) * ((1 + translatedRootUnit Delta xi eta) ^ p - 1) := by
    linear_combination heq
  rw [hdiff]
  convert mul_mem_lattice L hDpow hpower using 1
  simp only [q, Nat.cast_sub hp.one_le, Nat.cast_one]
  ring

/-- Exact polynomial division in the coefficient domain. Factoring the
prime before monic division proves integrality of every divided
coefficient, while retaining the leading coefficient `xi`. -/
theorem translatedRoot_residual_polynomial
    {R : Type*} [CommRing R] [IsDomain R]
    {p : ℕ} (hp : p.Prime) (hpodd : 2 < p)
    (hpne : (p : R) ≠ 0) (xi : R) (hxi : xi ^ (p - 1) = 1) :
    ∃ q : R[X], q.natDegree = p - 2 ∧ q.coeff (p - 2) = xi ∧
      (X + C xi) * (C (p : R) * q) =
        (X + C xi) ^ p - (X + C xi) - (X ^ p - X) := by
  classical
  let P : R[X] := ∑ j ∈ Finset.Ioo 0 p,
    monomial j (xi ^ (p - j) * ((p.choose j / p : ℕ) : R))
  have hcoeff (i : ℕ) : P.coeff i =
      if i ∈ Finset.Ioo 0 p then xi ^ (p - i) * ((p.choose i / p : ℕ) : R) else 0 := by
    simp [P, coeff_monomial]
  have hpchoose : p.choose (p - 1) = p := by
    have h := Nat.choose_succ_self_right (p - 1)
    simpa only [Nat.sub_add_cancel hp.one_le] using h
  have htop : P.coeff (p - 1) = xi := by
    rw [hcoeff, if_pos (Finset.mem_Ioo.mpr ⟨by omega, by omega⟩), hpchoose]
    simp [show p - (p - 1) = 1 by omega, Nat.div_self hp.pos]
  have hxine : xi ≠ 0 := by
    intro h
    simp [h, show p - 1 ≠ 0 by omega] at hxi
  have hPdegree : P.natDegree = p - 1 := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro i hi
      rw [hcoeff, if_neg]
      simp only [Finset.mem_Ioo]
      omega
    · rw [htop]
      exact hxine
  have hxiP : xi ^ p = xi := by
    conv_lhs => rw [show p = (p - 1) + 1 by omega, pow_succ]
    rw [hxi, one_mul]
  have hformula : (X + C xi : R[X]) ^ p - (X + C xi) - (X ^ p - X) = C (p : R) * P := by
    have h := (Commute.all (X : R[X]) (C xi)).add_pow_prime_eq' hp
    have hterms : (∑ j ∈ Finset.Ioo 0 p,
        (X : R[X]) ^ j * C xi ^ (p - j) * ((p.choose j / p : ℕ) : R[X])) = P := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [← C_mul_X_pow_eq_monomial, C_mul, C_pow, C_eq_natCast]
      ring
    rw [hterms, ← C_pow, hxiP] at h
    simp only [C_eq_natCast]
    linear_combination h
  have hPzero : P.eval (-xi) = 0 := by
    have h := congrArg (fun f : R[X] => f.eval (-xi)) hformula
    simp only [eval_sub, eval_add, eval_pow, eval_X, eval_C,
      neg_add_cancel, zero_pow hp.ne_zero, sub_zero, eval_mul] at h
    have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
    rw [hpOdd.neg_pow, hxiP] at h
    have hmul : (p : R) * P.eval (-xi) = 0 := by linear_combination -h
    exact (mul_eq_zero.mp hmul).resolve_left hpne
  let q := P /ₘ (X - C (-xi))
  have hqmul : (X + C xi) * q = P := by
    simpa [q] using (mul_divByMonic_eq_iff_isRoot.mpr hPzero)
  have hqdegree : q.natDegree = p - 2 := by
    dsimp only [q]
    rw [natDegree_divByMonic P (monic_X_sub_C _), hPdegree, natDegree_X_sub_C]
    omega
  have hqtop : q.coeff (p - 2) = xi := by
    rw [← hqdegree, ← leadingCoeff]
    have hdegree : (X - C (-xi) : R[X]).degree ≤ P.degree := by
      rw [degree_X_sub_C, degree_eq_natDegree (by
        intro h; simp [h] at htop; exact hxine htop.symm), hPdegree]
      exact_mod_cast (show 1 ≤ p - 1 by omega)
    dsimp only [q]
    rw [leadingCoeff_divByMonic_of_monic (monic_X_sub_C _) hdegree,
      leadingCoeff, hPdegree, htop]
  refine ⟨q, hqdegree, hqtop, ?_⟩
  rw [hformula, ← hqmul]
  ring

/-- Twisted traces of the lower-degree terms in the exact residual
polynomial leave `p*xi*Tr(Delta^(p-2))`. The coefficient domain is the
actual valuation ring of `E`; all polynomial coefficients are constructed
by monic division, not assumed to have the needed precision. -/
theorem translatedRoot_trace_residual
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra E L]
    {p : ℕ} (hp : p.Prime) (hpodd : 2 < p)
    (t delta : ℤ) (ht : 0 ≤ t) (hd : 0 ≤ delta)
    (Delta : L) (xi : ringOfIntegers E)
    (hpne : (p : E) ≠ 0) (hxi : xi ^ (p - 1) = 1)
    (hD : Delta + algebraMap E L (xi : E) ≠ 0)
    (hpval : (p : E) ∈ lattice E (((p : ℤ) - 1) * (t + delta)))
    (htrace : ∀ i : ℕ, i < p → trace E L (Delta ^ i) ∈
      lattice E (((p : ℤ) - 1) * (t + delta) - (i : ℤ) * t)) :
    trace E L (translatedRootResidual p Delta (algebraMap E L (xi : E))) -
      (xi : E) * ((p : E) * trace E L (Delta ^ (p - 2))) ∈
        lattice E ((p : ℤ) * (t + delta) + t) := by
  let incl : ringOfIntegers E →+* E := (ValuativeRel.valuation E).integer.subtype
  let f : ringOfIntegers E →+* L := (algebraMap E L).comp incl
  have hfc (c : ringOfIntegers E) : f c = algebraMap E L (c : E) := rfl
  have hpInt : (p : ringOfIntegers E) ≠ 0 := by
    intro h
    apply hpne
    simpa using congrArg incl h
  obtain ⟨q, hqdegree, hqtop, hqmul⟩ :=
    translatedRoot_residual_polynomial hp hpodd hpInt xi hxi
  have hqeval := congrArg (fun P : (ringOfIntegers E)[X] => P.eval₂ f Delta) hqmul
  simp only [eval₂_mul, eval₂_add, eval₂_X, eval₂_C, eval₂_pow, eval₂_sub,
    map_natCast, eval₂_natCast, hfc] at hqeval
  have hquot : translatedRootResidual p Delta (algebraMap E L (xi : E)) =
      (p : L) * q.eval₂ f Delta := by
    dsimp only [translatedRootResidual]
    apply (div_eq_iff hD).2
    simpa only [mul_comm] using hqeval.symm
  have hscalar (c : ringOfIntegers E) (i : ℕ) :
      trace E L ((p : L) * (f c * Delta ^ i)) =
        (p : E) * (c : E) * trace E L (Delta ^ i) := by
    have heq : (p : L) * (f c * Delta ^ i) = ((p : E) * (c : E)) • Delta ^ i := by
      rw [Algebra.smul_def, map_mul, map_natCast]
      rw [hfc]
      ring
    rw [heq, map_smul]
    rfl
  have hexpand : trace E L (translatedRootResidual p Delta (algebraMap E L (xi : E))) =
      (∑ i ∈ Finset.range (p - 2),
        (p : E) * (q.coeff i : E) * trace E L (Delta ^ i)) +
      (p : E) * (xi : E) * trace E L (Delta ^ (p - 2)) := by
    rw [hquot, eval₂_eq_sum_range, hqdegree, Finset.sum_range_succ,
      mul_add, Finset.mul_sum, map_add, map_sum]
    simp only [hscalar, hqtop]
  have heq : trace E L (translatedRootResidual p Delta (algebraMap E L (xi : E))) -
      (xi : E) * ((p : E) * trace E L (Delta ^ (p - 2))) =
      ∑ i ∈ Finset.range (p - 2),
        (p : E) * (q.coeff i : E) * trace E L (Delta ^ i) := by
    rw [hexpand]
    ring
  rw [heq]
  apply sum_mem_lattice E
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hc : (q.coeff i : E) ∈ lattice E 0 := by
    rw [mem_lattice]
    exact (ord_nonneg_iff_mem_integer E _).2 (q.coeff i).property
  have hterm := mul_mem_lattice E (mul_mem_lattice E hpval hc)
    (htrace i (by omega))
  apply lattice_antitone E _ hterm
  have hpZ : (3 : ℤ) ≤ p := by exact_mod_cast hpodd
  have hiZ : (i : ℤ) ≤ (p : ℤ) - 3 := by omega
  have h1 := mul_nonneg (sub_nonneg.mpr hiZ) ht
  have h2 := mul_nonneg (show (0 : ℤ) ≤ (p : ℤ) - 2 by omega) hd
  nlinarith only [h1, h2]

/-- In degree three the residual quotient is exactly `3*xi*Delta`;
there is no omitted constant or reciprocal term. -/
theorem translatedRootResidual_cubic
    {L : Type*} [Field L] (Delta xi : L)
    (hxi : xi ^ 2 = 1) (hD : Delta + xi ≠ 0) :
    translatedRootResidual 3 Delta xi = 3 * xi * Delta := by
  dsimp only [translatedRootResidual]
  apply (div_eq_iff hD).2
  linear_combination xi * hxi

/-- The complete cubic correction equation for the actual root. -/
theorem translatedRootUnit_cubic_equation
    {L : Type*} [Field L] (Delta xi eta : L)
    (hxi : xi ^ 2 = 1) (hD : Delta + xi ≠ 0)
    (hroot : (Delta + xi + eta) ^ 3 - (Delta + xi + eta) = Delta ^ 3 - Delta) :
    let D := Delta + xi
    let u := translatedRootUnit Delta xi eta
    u = 3 * xi * Delta + 3 * D ^ 2 * u + 3 * D ^ 2 * u ^ 2 + D ^ 2 * u ^ 3 := by
  have h := translatedRootUnit_equation (by decide : 0 < 3) Delta xi eta hD hroot
  dsimp only at h ⊢
  rw [translatedRootResidual_cubic Delta xi hxi hD] at h
  norm_num at h
  linear_combination h

/-- The two successive cubic residual bounds. The second estimate is
needed at `p=3`: the first iterate alone does not give the required trace
precision. The assumption on `u` is exactly the divided Hensel bound. -/
theorem translatedRootUnit_cubic_iterates
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    (t V : ℤ) (ht : 0 ≤ t) (hVt : 2 * t ≤ V)
    (Delta xi eta : L)
    (hxi : xi ^ 2 = 1)
    (hD : ord L (Delta + xi) = ((-t : ℤ) : WithTop ℤ))
    (hV : ord L (3 : L) = (V : WithTop ℤ))
    (heta : eta ∈ lattice L (V - 2 * t))
    (hroot : (Delta + xi + eta) ^ 3 - (Delta + xi + eta) = Delta ^ 3 - Delta) :
    let D := Delta + xi
    let u := translatedRootUnit Delta xi eta
    let Q := 3 * xi * Delta
    u - Q ∈ lattice L (2 * V - 3 * t) ∧
      u - Q - 3 * D ^ 2 * Q ∈ lattice L (3 * V - 5 * t) := by
  let D := Delta + xi
  let u := translatedRootUnit Delta xi eta
  let Q := 3 * xi * Delta
  have hDne : Delta + xi ≠ 0 := (ord_ne_top_iff L).1 (by
    rw [hD]; exact WithTop.coe_ne_top)
  have heq : u = Q + 3 * D ^ 2 * u + 3 * D ^ 2 * u ^ 2 + D ^ 2 * u ^ 3 :=
    translatedRootUnit_cubic_equation Delta xi eta hxi hDne hroot
  have hu : u ∈ lattice L (V - t) := by
    simpa using translatedRootUnit_mem L 3 t V Delta xi eta hD heta
  have hDmem : D ∈ lattice L (-t) := by rw [mem_lattice]; exact hD.ge
  have hDsq : D ^ 2 ∈ lattice L (-2 * t) := by
    convert pow_mem_int_lattice L hDmem 2 using 1; norm_num
  have hthree : (3 : L) ∈ lattice L V := by rw [mem_lattice, hV]
  have hlin : 3 * D ^ 2 ∈ lattice L (V - 2 * t) := by
    convert mul_mem_lattice L hthree hDsq using 1; ring
  have hfirst : 3 * D ^ 2 * u ∈ lattice L (2 * V - 3 * t) := by
    convert mul_mem_lattice L hlin hu using 1; ring
  have hsecond : 3 * D ^ 2 * u ^ 2 ∈ lattice L (3 * V - 4 * t) := by
    convert mul_mem_lattice L hlin (pow_mem_int_lattice L hu 2) using 1; push_cast; ring
  have hthird : D ^ 2 * u ^ 3 ∈ lattice L (3 * V - 5 * t) := by
    convert mul_mem_lattice L hDsq (pow_mem_int_lattice L hu 3) using 1; push_cast; ring
  have hfirstError : u - Q ∈ lattice L (2 * V - 3 * t) := by
    have herr : u - Q = 3 * D ^ 2 * u + 3 * D ^ 2 * u ^ 2 + D ^ 2 * u ^ 3 := by
      linear_combination heq
    rw [herr]
    exact (lattice L _).add_mem ((lattice L _).add_mem hfirst
      (lattice_antitone L (by omega) hsecond)) (lattice_antitone L (by omega) hthird)
  refine ⟨hfirstError, ?_⟩
  have herr : u - Q - 3 * D ^ 2 * Q =
      3 * D ^ 2 * (u - Q) + 3 * D ^ 2 * u ^ 2 + D ^ 2 * u ^ 3 := by
    linear_combination heq
  change u - Q - 3 * D ^ 2 * Q ∈ _
  rw [herr]
  apply (lattice L _).add_mem _ hthird
  apply (lattice L _).add_mem _ (lattice_antitone L (by omega) hsecond)
  convert mul_mem_lattice L hlin hfirstError using 1; ring

/-- Splitting the actual norm polynomial leaves the linear trace. This
supporting implication only discards symmetric coefficients of degree at
least two. -/
theorem translatedUnit_norm_sub_trace_mem
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra E L] [Module.Free E L] [Module.Finite E L]
    (u : L) (H : ℤ)
    (hcoeff : ∀ i : ℕ, 2 ≤ i → i ≤ Module.finrank E L →
      elementarySymmetric E L i u ∈ lattice E H) :
    norm E L (1 + u) - 1 - trace E L u ∈ lattice E H := by
  have hpos := Module.finrank_pos (R := E) (M := L)
  have hdegree : Module.finrank E L = (Module.finrank E L - 1) + 1 := by omega
  have heq : norm E L (1 + u) - 1 - trace E L u =
      ∑ j ∈ Finset.range (Module.finrank E L - 1), elementarySymmetric E L (j + 2) u := by
    rw [norm_one_add_eq_one_add_sum_elementarySymmetric]
    conv_lhs => arg 1; arg 1; arg 2; rw [hdegree, Finset.sum_range_succ']
    simp only [zero_add, elementarySymmetric_one]
    ring
  rw [heq]
  apply sum_mem_lattice E
  intro j hj
  exact hcoeff (j + 2) (by omega) (by have := Finset.mem_range.mp hj; omega)

/-- Integer arithmetic for the higher norm coefficients in the translated
root calculation. It includes the cubic endpoint and never truncates a
negative depth. -/
theorem translatedNorm_higher_depth
    (p i : ℕ) (hp : 3 ≤ p) (hi : 2 ≤ i)
    (t delta V : ℤ) (ht : 0 ≤ t) (hd : 0 ≤ delta)
    (hV : (p : ℤ) * ((p : ℤ) - 1) * (t + delta) ≤ V) :
    (p : ℤ) * (t + delta) + t ≤ V - ((p : ℤ) - 2) * t ∧
    (p : ℤ) * (t + delta) + t ≤
      ((i : ℤ) * (V - ((p : ℤ) - 2) * t) +
        ((p : ℤ) - 1) * (t + (p : ℤ) * delta + 1)) / (p : ℤ) := by
  have hpZ : (3 : ℤ) ≤ p := by exact_mod_cast hp
  have hiZ : (2 : ℤ) ≤ i := by exact_mod_cast hi
  have hpt : 0 ≤ ((p : ℤ) - 3) * t := mul_nonneg (by omega) ht
  have hpd : 0 ≤ (p : ℤ) * ((p : ℤ) - 2) * delta :=
    mul_nonneg (mul_nonneg (by omega) (by omega)) hd
  have hpoly : 0 ≤ ((p : ℤ) - 3) * ((p : ℤ) - 1) * t :=
    mul_nonneg (mul_nonneg (by omega) (by omega)) ht
  have hpolyD : 0 ≤ (p : ℤ) * (2 * (p : ℤ) - 3) * delta :=
    mul_nonneg (mul_nonneg (by omega) (by omega)) hd
  have hnorm : (p : ℤ) * (t + delta) + t ≤ V - ((p : ℤ) - 2) * t := by
    have hpolyN : 0 ≤ (p : ℤ) * ((p : ℤ) - 3) * t :=
      mul_nonneg (mul_nonneg (by omega) (by omega)) ht
    nlinarith only [hV, hpolyN, hpd, ht]
  refine ⟨hnorm, ?_⟩
  rw [Int.le_ediv_iff_mul_le (by omega : (0 : ℤ) < p)]
  have hu : 0 ≤ V - ((p : ℤ) - 2) * t := by
    have : 0 ≤ (p : ℤ) * (t + delta) := mul_nonneg (by omega) (by omega)
    linarith
  have hiu := mul_nonneg (sub_nonneg.mpr hiZ) hu
  nlinarith only [hV, hiu, hpoly, hpolyD, hpZ]

/-- Strong FML symmetric bounds show that every nonlinear coefficient in
`N(1+u)` is negligible at `H=p*t₂+t`, including `p=3`. The trace remains
explicit. `htrace` is the actual upper-edge trace-ideal lower bound. -/
theorem translatedUnit_norm_linear
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    [Module.Free E L] [Module.Finite E L] [IsGalois E L]
    {p : ℕ} (hp : p.Prime) (hpodd : 2 < p)
    (t delta : ℕ) (ht : 0 < t) (V : ℤ)
    (hV : (p : ℤ) * ((p : ℤ) - 1) * ((t : ℤ) + delta) ≤ V)
    (hchar : residueCharacteristic E = p)
    (hdegree : Module.finrank E L = p) (hram : ramificationIndex E L = p)
    (htrace : TraceIdealLowerBound E L p
      (((p : ℤ) - 1) * ((t : ℤ) + (p : ℤ) * delta + 1)))
    (u : L) (hu : u ∈ lattice L (V - ((p : ℤ) - 2) * t)) :
    norm E L (1 + u) - 1 - trace E L u ∈
      lattice E ((p : ℤ) * ((t : ℤ) + delta) + t) := by
  apply translatedUnit_norm_sub_trace_mem E L
  intro i hi hip
  rw [hdegree] at hip
  have hdepth := translatedNorm_higher_depth p i (by omega) hi t delta V
    (by positivity) (by positivity) hV
  by_cases heq : i = p
  · subst i
    rw [mem_lattice, elementarySymmetric_degree_ord E L p hdegree hram]
    exact (WithTop.coe_le_coe.mpr hdepth.1).trans ((mem_lattice L).1 hu)
  · have htrace' : TraceIdealLowerBound E L p
        (((p - 1) * (t + p * delta + 1) : ℕ) : ℤ) := by
      convert htrace using 1
      push_cast [Nat.cast_sub hp.one_le]
      ring
    have hsym := wild_elementarySymmetric_bound E L p (t + p * delta + 1)
      (V - ((p : ℤ) - 2) * t) hp (by omega) hchar hdegree htrace'
      ((mem_lattice L).1 hu) (j := i) (by omega) (by omega)
    rw [mem_lattice]
    apply (WithTop.coe_le_coe.mpr hdepth.2).trans
    convert hsym using 1
    push_cast [Nat.cast_sub hp.one_le]
    ring

/-- The extra cubic iterate, after using the exact Artin--Schreier
relation. This identity includes its affine `a` term in either
characteristic. -/
theorem translatedRoot_cubic_second_trace
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    (Delta a : L) (xi : E) (hroot : Delta ^ 3 - Delta = a) :
    trace E L (3 * (Delta + algebraMap E L xi) ^ 2 *
      (3 * algebraMap E L xi * Delta)) =
      9 * xi * (trace E L Delta + trace E L a) +
      18 * xi ^ 2 * trace E L (Delta ^ 2) +
      9 * xi ^ 3 * trace E L Delta := by
  have heq : 3 * (Delta + algebraMap E L xi) ^ 2 *
      (3 * algebraMap E L xi * Delta) =
      (9 * xi) • (Delta + a) +
      (18 * xi ^ 2) • (Delta ^ 2) + (9 * xi ^ 3) • Delta := by
    simp only [Algebra.smul_def, map_mul, map_pow, map_ofNat]
    linear_combination 9 * algebraMap E L xi * hroot
  rw [heq]
  simp only [map_add, map_smul, smul_eq_mul]

/-- Twisted traces make the extra cubic iterate negligible. The bound on
`Tr(a)` is retained separately: `a` lies in the other lower field, so its
trace cannot be replaced by scalar multiplication in this field. -/
theorem translatedRoot_cubic_second_trace_mem
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra E L]
    (t delta : ℤ) (ht : 0 ≤ t) (hd : 0 ≤ delta)
    (Delta a : L) (xi : E) (hroot : Delta ^ 3 - Delta = a)
    (hxi : xi ∈ lattice E 0)
    (hthree : (3 : E) ∈ lattice E (2 * (t + delta)))
    (hDelta : trace E L Delta ∈ lattice E (t + 2 * delta))
    (ha : trace E L a ∈ lattice E (t + 2 * delta))
    (hDelta2 : trace E L (Delta ^ 2) ∈ lattice E (2 * delta)) :
    trace E L (3 * (Delta + algebraMap E L xi) ^ 2 *
      (3 * algebraMap E L xi * Delta)) ∈ lattice E (4 * t + 3 * delta) := by
  have hnine : (9 : E) ∈ lattice E (4 * (t + delta)) := by
    have h := mul_mem_lattice E hthree hthree
    norm_num only [show (3 : E) * 3 = 9 by norm_num] at h
    convert h using 1; ring
  have heighteen : (18 : E) ∈ lattice E (4 * (t + delta)) := by
    have h := mul_mem_lattice E (natCast_mem_int_lattice_zero E 2) hnine
    norm_num only [show (2 : E) * 9 = 18 by norm_num, zero_add] at h
    exact h
  have hxi2 : xi ^ 2 ∈ lattice E 0 := by
    simpa using pow_mem_int_lattice E hxi 2
  have hxi3 : xi ^ 3 ∈ lattice E 0 := by
    simpa using pow_mem_int_lattice E hxi 3
  rw [translatedRoot_cubic_second_trace E L Delta a xi hroot]
  apply (lattice E _).add_mem
  · apply (lattice E _).add_mem
    · apply lattice_antitone E (by linarith :
        4 * t + 3 * delta ≤ (4 * (t + delta) + 0) + (t + 2 * delta))
      exact mul_mem_lattice E (mul_mem_lattice E hnine hxi)
        ((lattice E _).add_mem hDelta ha)
    · apply lattice_antitone E (by linarith :
        4 * t + 3 * delta ≤ (4 * (t + delta) + 0) + 2 * delta)
      exact mul_mem_lattice E (mul_mem_lattice E heighteen hxi2) hDelta2
  · apply lattice_antitone E (by linarith :
      4 * t + 3 * delta ≤ (4 * (t + delta) + 0) + (t + 2 * delta))
    exact mul_mem_lattice E (mul_mem_lattice E hnine hxi3) hDelta

/-- For primes at least five the first iterate error is deep enough after
the upper trace. The cubic case is deliberately outside this implication. -/
theorem translatedNorm_first_trace_depth
    (p : ℕ) (hp : 5 ≤ p) (t delta V : ℤ) (ht : 0 ≤ t) (hd : 0 ≤ delta)
    (hV : (p : ℤ) * ((p : ℤ) - 1) * (t + delta) ≤ V) :
    (p : ℤ) * (t + delta) + t ≤
      (2 * V - (2 * (p : ℤ) - 3) * t +
        ((p : ℤ) - 1) * (t + (p : ℤ) * delta + 1)) / (p : ℤ) := by
  have hpZ : (5 : ℤ) ≤ p := by exact_mod_cast hp
  rw [Int.le_ediv_iff_mul_le (by omega : (0 : ℤ) < p)]
  have ht' := mul_nonneg (mul_nonneg (show (0 : ℤ) ≤ p by omega)
    (show (0 : ℤ) ≤ (p : ℤ) - 4 by omega)) ht
  have hd' := mul_nonneg (mul_nonneg (show (0 : ℤ) ≤ p by omega)
    (show (0 : ℤ) ≤ 2 * (p : ℤ) - 3 by omega)) hd
  nlinarith only [hV, hpZ, ht', hd', ht]

/-- The retained cubic iterate reaches the same trace precision. -/
theorem translatedNorm_cubic_trace_depth
    (t delta V : ℤ) (ht : 0 ≤ t) (hd : 0 ≤ delta)
    (hV : 6 * (t + delta) ≤ V) :
    4 * t + 3 * delta ≤ (3 * V - 5 * t + 2 * (t + 3 * delta + 1)) / 3 := by
  omega

/-- In primes at least five the norm-unit correction is the trace of the
exact residual quotient, modulo `H`. This is the step preceding extraction
of the leading coefficient `p*xi`. -/
theorem translatedRoot_norm_first_residual
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    [Module.Free E L] [Module.Finite E L] [IsGalois E L]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (t delta : ℕ) (ht : 0 < t) (V : ℤ)
    (hVbound : (p : ℤ) * ((p : ℤ) - 1) * ((t : ℤ) + delta) ≤ V)
    (hchar : residueCharacteristic E = p)
    (hdegree : Module.finrank E L = p) (hram : ramificationIndex E L = p)
    (htrace : TraceIdealLowerBound E L p
      (((p : ℤ) - 1) * ((t : ℤ) + (p : ℤ) * delta + 1)))
    (Delta xi eta : L)
    (hD : ord L (Delta + xi) = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hV : ord L (p : L) = (V : WithTop ℤ))
    (heta : eta ∈ lattice L (V - ((p : ℤ) - 1) * t))
    (hroot : (Delta + xi + eta) ^ p - (Delta + xi + eta) = Delta ^ p - Delta) :
    norm E L (1 + translatedRootUnit Delta xi eta) - 1 -
      trace E L (translatedRootResidual p Delta xi) ∈
        lattice E ((p : ℤ) * ((t : ℤ) + delta) + t) := by
  have hpZ : (3 : ℤ) ≤ p := by omega
  have hVt : ((p : ℤ) - 1) * t ≤ V := by
    have h1 := mul_nonneg
      (mul_nonneg (show (0 : ℤ) ≤ (p : ℤ) - 1 by omega)
        (show (0 : ℤ) ≤ (p : ℤ) - 1 by omega)) (Int.natCast_nonneg t)
    have h2 := mul_nonneg
      (mul_nonneg (show (0 : ℤ) ≤ p by omega)
        (show (0 : ℤ) ≤ (p : ℤ) - 1 by omega)) (Int.natCast_nonneg delta)
    nlinarith only [hVbound, h1, h2]
  have hu := translatedRootUnit_mem L p t V Delta xi eta hD heta
  have hnorm := translatedUnit_norm_linear E L hp (by omega) t delta ht V
    hVbound hchar hdegree hram htrace _ hu
  have herror := translatedRootUnit_first_iterate L hp t V (by positivity)
    hVt Delta xi eta hD hV heta hroot
  have htraceError := htrace _ _ ((mem_lattice L).1 herror)
  have hdepth := translatedNorm_first_trace_depth p hp5 t delta V
    (by positivity) (by positivity) hVbound
  have htr : trace E L (translatedRootUnit Delta xi eta -
      translatedRootResidual p Delta xi) ∈
        lattice E ((p : ℤ) * ((t : ℤ) + delta) + t) := by
    rw [mem_lattice]
    exact (WithTop.coe_le_coe.mpr hdepth).trans htraceError
  have h := (lattice E _).add_mem hnorm htr
  simpa only [map_sub, sub_add_sub_cancel] using h

/-- The cubic norm correction, including the second iterate and the trace
of the affine term from `Delta^3=Delta+a`. All norms and traces belong to
this actual upper extension. The input trace bounds are precisely the
three twisted estimates used in the paper. -/
theorem translatedRoot_norm_cubic
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    [Module.Free E L] [Module.Finite E L] [IsGalois E L]
    (t delta : ℕ) (ht : 0 < t) (V : ℤ)
    (hVbound : 6 * ((t : ℤ) + delta) ≤ V)
    (hchar : residueCharacteristic E = 3)
    (hdegree : Module.finrank E L = 3) (hram : ramificationIndex E L = 3)
    (htrace : TraceIdealLowerBound E L 3 (2 * ((t : ℤ) + 3 * delta + 1)))
    (Delta a eta : L) (xi : E) (hxi : xi ^ 2 = 1)
    (hxiInt : xi ∈ lattice E 0)
    (hAS : Delta ^ 3 - Delta = a)
    (hD : ord L (Delta + algebraMap E L xi) = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hV : ord L (3 : L) = (V : WithTop ℤ))
    (heta : eta ∈ lattice L (V - 2 * t))
    (hroot : (Delta + algebraMap E L xi + eta) ^ 3 -
      (Delta + algebraMap E L xi + eta) = Delta ^ 3 - Delta)
    (hthree : (3 : E) ∈ lattice E (2 * ((t : ℤ) + delta)))
    (hDelta : trace E L Delta ∈ lattice E ((t : ℤ) + 2 * delta))
    (ha : trace E L a ∈ lattice E ((t : ℤ) + 2 * delta))
    (hDelta2 : trace E L (Delta ^ 2) ∈ lattice E (2 * (delta : ℤ))) :
    norm E L (1 + translatedRootUnit Delta (algebraMap E L xi) eta) - 1 -
      xi * (3 * trace E L Delta) ∈ lattice E (4 * (t : ℤ) + 3 * delta) := by
  let u := translatedRootUnit Delta (algebraMap E L xi) eta
  let Q := 3 * algebraMap E L xi * Delta
  let W := 3 * (Delta + algebraMap E L xi) ^ 2 * Q
  have hu : u ∈ lattice L (V - t) := by
    simpa using translatedRootUnit_mem L 3 t V Delta (algebraMap E L xi) eta hD heta
  have hnorm : norm E L (1 + u) - 1 - trace E L u ∈
      lattice E (4 * (t : ℤ) + 3 * delta) := by
    have h := translatedUnit_norm_linear E L (by decide : Nat.Prime 3)
      (by decide) t delta ht V (by simpa using hVbound) hchar hdegree hram
      (by simpa using htrace) u (by simpa using hu)
    convert h using 1; norm_num; ring
  have hxiL : (algebraMap E L xi) ^ 2 = 1 := by rw [← map_pow, hxi, map_one]
  have herr : u - Q - W ∈ lattice L (3 * V - 5 * t) :=
    (translatedRootUnit_cubic_iterates L t V (by positivity) (by
      have := Int.natCast_nonneg delta
      have := Int.natCast_nonneg t
      linarith) Delta (algebraMap E L xi) eta hxiL hD hV heta hroot).2
  have htrError : trace E L (u - Q - W) ∈ lattice E (4 * (t : ℤ) + 3 * delta) := by
    rw [mem_lattice]
    exact (WithTop.coe_le_coe.mpr (translatedNorm_cubic_trace_depth t delta V
      (by positivity) (by positivity) hVbound)).trans
        (htrace _ _ ((mem_lattice L).1 herr))
  have hW : trace E L W ∈ lattice E (4 * (t : ℤ) + 3 * delta) :=
    translatedRoot_cubic_second_trace_mem E L t delta (by positivity) (by positivity)
      Delta a xi hAS hxiInt hthree hDelta ha hDelta2
  have hQ : trace E L Q = xi * (3 * trace E L Delta) := by
    have hQform : Q = (3 * xi) • Delta := by
      dsimp only [Q]
      rw [Algebra.smul_def, map_mul, map_ofNat]
    rw [hQform, map_smul]
    simp only [smul_eq_mul]
    ring
  have h := (lattice E _).add_mem ((lattice E _).add_mem hnorm htrError) hW
  have heq : norm E L (1 + u) - 1 - trace E L u +
      trace E L (u - Q - W) + trace E L W =
        norm E L (1 + u) - 1 - xi * (3 * trace E L Delta) := by
    rw [map_sub, map_sub, hQ]
    ring
  rw [heq] at h
  exact h

/-- The mixed-characteristic unit correction from `O:A:eq:unit-correction`
for an actual translated root. The proof treats `p=3` separately and uses
the exact residual polynomial for larger primes. The hypotheses are the
upper-edge trace ideal and the twisted power traces, not a norm correction
or a stationary-model assumption. -/
theorem translatedRoot_norm_unit_correction
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    [Module.Free E L] [Module.Finite E L] [IsGalois E L]
    {p : ℕ} (hp : p.Prime) (hpodd : 2 < p)
    (t delta : ℕ) (ht : 0 < t) (V : ℤ)
    (hVbound : (p : ℤ) * ((p : ℤ) - 1) * ((t : ℤ) + delta) ≤ V)
    (hchar : residueCharacteristic E = p)
    (hdegree : Module.finrank E L = p) (hram : ramificationIndex E L = p)
    (htrace : TraceIdealLowerBound E L p
      (((p : ℤ) - 1) * ((t : ℤ) + (p : ℤ) * delta + 1)))
    (Delta eta : L) (xi : ringOfIntegers E) (hxi : xi ^ (p - 1) = 1)
    (hD : ord L (Delta + algebraMap E L (xi : E)) = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hV : ord L (p : L) = (V : WithTop ℤ))
    (heta : eta ∈ lattice L (V - ((p : ℤ) - 1) * t))
    (hroot : (Delta + algebraMap E L (xi : E) + eta) ^ p -
      (Delta + algebraMap E L (xi : E) + eta) = Delta ^ p - Delta)
    (hpval : (p : E) ∈ lattice E (((p : ℤ) - 1) * ((t : ℤ) + delta)))
    (htr : ∀ i : ℕ, i < p → trace E L (Delta ^ i) ∈
      lattice E (((p : ℤ) - 1) * ((t : ℤ) + delta) - (i : ℤ) * t))
    (hA : p = 3 → trace E L (Delta ^ 3 - Delta) ∈ lattice E ((t : ℤ) + 2 * delta)) :
    norm E L (1 + translatedRootUnit Delta (algebraMap E L (xi : E)) eta) - 1 -
      (xi : E) * ((p : E) * trace E L (Delta ^ (p - 2))) ∈
        lattice E ((p : ℤ) * ((t : ℤ) + delta) + t) := by
  by_cases hp3 : p = 3
  · have hchar3 : residueCharacteristic E = 3 := hchar.trans hp3
    clear hchar
    rcases hp3 with rfl
    have hxiE : (xi : E) ^ 2 = 1 := by
      exact_mod_cast hxi
    have hxiInt : (xi : E) ∈ lattice E 0 := by
      rw [mem_lattice]
      exact (ord_nonneg_iff_mem_integer E _).2 xi.property
    have htr1 : trace E L Delta ∈ lattice E ((t : ℤ) + 2 * delta) := by
      have h := htr 1 (by decide)
      simp only [pow_one] at h
      convert h using 1; push_cast; ring
    have htr2 : trace E L (Delta ^ 2) ∈ lattice E (2 * (delta : ℤ)) := by
      have h := htr 2 (by decide)
      convert h using 1; push_cast; ring
    have h := translatedRoot_norm_cubic E L t delta ht V (by simpa using hVbound)
      hchar3 hdegree hram (by simpa using htrace) Delta (Delta ^ 3 - Delta) eta
      (xi : E) hxiE hxiInt rfl hD hV (by simpa using heta) hroot
      (by simpa using hpval) htr1 (hA rfl) htr2
    convert h using 1 <;> norm_num
    ring
  · have hp5 : 5 ≤ p := by
      have hp4 := hp.ne_one
      by_contra h
      have heq : p = 4 := by omega
      exact (by decide : ¬ Nat.Prime 4) (heq ▸ hp)
    have hDne : Delta + algebraMap E L (xi : E) ≠ 0 := (ord_ne_top_iff L).1 (by
      rw [hD]; exact WithTop.coe_ne_top)
    have hpneL : (p : L) ≠ 0 := (ord_ne_top_iff L).1 (by
      rw [hV]; exact WithTop.coe_ne_top)
    have hpneE : (p : E) ≠ 0 := by
      intro h
      apply hpneL
      have heq := congrArg (algebraMap E L) h
      simpa using heq
    have hnorm := translatedRoot_norm_first_residual E L hp hp5 t delta ht V
      hVbound hchar hdegree hram htrace Delta (algebraMap E L (xi : E)) eta
      hD hV heta hroot
    have hresidual := translatedRoot_trace_residual E L hp hpodd t delta
      (by positivity) (by positivity) Delta xi hpneE hxi hDne hpval htr
    have h := (lattice E _).add_mem hnorm hresidual
    simpa only [sub_add_sub_cancel] using h

private theorem translated_root_torsion_ord
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    {n : ℕ} (hn : 0 < n) (xi : L) (hxi : xi ^ n = 1) : ord L xi = 0 := by
  have hxine : xi ≠ 0 := by intro h; simp [h, Nat.ne_of_gt hn] at hxi
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff L).2 hxine)
  have hv := congrArg (ord L) hxi
  rw [ord_pow, ord_one, ← hm, ← WithTop.coe_nsmul] at hv
  have hmzero : m = 0 := by
    have h := WithTop.coe_eq_zero.mp hv
    simp only [nsmul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast Nat.ne_of_gt hn)
  rw [← hm, hmzero]; rfl

private theorem translated_root_center_ord
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    {n : ℕ} (hn : 0 < n) {t : ℤ} (ht : 0 < t)
    (Delta xi : L) (hDelta : ord L Delta = ((-t : ℤ) : WithTop ℤ))
    (hxi : xi ^ n = 1) : ord L (Delta + xi) = ((-t : ℤ) : WithTop ℤ) := by
  have hxiord := translated_root_torsion_ord L hn xi hxi
  have hne : ord L Delta ≠ ord L xi := by
    rw [hDelta, hxiord]
    exact ne_of_lt (WithTop.coe_lt_coe.mpr (by omega))
  rw [ord_add_eq_min L hne, hDelta, hxiord]
  exact min_eq_left (WithTop.coe_le_coe.mpr (by omega))

/-- Construct the actual unit corrections for a supplied genuine
Artin--Schreier coordinate. This preserves its identity when it already
carries twisted estimates. Both characteristic cases and the two Newton
precisions are retained. -/
theorem translatedRoot_actualUnitCorrections_of_coordinate
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = p)
    (D : OddTotalBreakData (F := F) (K := K) hp hG) :
    let B₂ := D.B₂
    letI := Basic.intermediateFieldValuativeRel B₂
    letI := Basic.intermediateFieldTopology B₂
    letI := Basic.intermediateField_localField B₂
    ∀ (Delta : K) (a : B₂),
      Delta ^ p - Delta = algebraMap B₂ K a →
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) →
      Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ →
      ∀ xi : B₂, xi ^ (p - 1) = 1 →
        ∃ (sigma : Gal(K/B₂)) (eta : K),
          sigma Delta = Delta + algebraMap B₂ K xi + eta ∧
          (Delta + algebraMap B₂ K xi + eta) ^ p -
            (Delta + algebraMap B₂ K xi + eta) = algebraMap B₂ K a ∧
          sigma Delta = (Delta + algebraMap B₂ K xi) *
            (1 + translatedRootUnit Delta (algebraMap B₂ K xi) eta) ∧
          norm D.B₁ K (sigma Delta) = norm D.B₁ K (Delta + algebraMap B₂ K xi) *
            norm D.B₁ K (1 + translatedRootUnit Delta (algebraMap B₂ K xi) eta) ∧
          (((p : K) = 0 ∧ translatedRootUnit Delta (algebraMap B₂ K xi) eta = 0) ∨
            ((p : K) ≠ 0 ∧ ∃ V : ℤ,
              ord K (p : K) = (V : WithTop ℤ) ∧
              translatedRootUnit Delta (algebraMap B₂ K xi) eta ∈
                lattice K (V - ((p : ℤ) - 2) * D.t) ∧
              translatedRootUnit Delta (algebraMap B₂ K xi) eta -
                translatedRootResidual p Delta (algebraMap B₂ K xi) ∈
                  lattice K (2 * V - (2 * (p : ℤ) - 3) * D.t) ∧
              (p = 3 →
                translatedRootUnit Delta (algebraMap B₂ K xi) eta -
                  3 * algebraMap B₂ K xi * Delta -
                  3 * (Delta + algebraMap B₂ K xi) ^ 2 *
                    (3 * algebraMap B₂ K xi * Delta) ∈
                      lattice K (3 * V - 5 * D.t)))) := by
  let B₂ := D.B₂
  letI := Basic.intermediateFieldValuativeRel B₂
  letI := Basic.intermediateFieldTopology B₂
  letI := Basic.intermediateField_localField B₂
  dsimp only
  intro Delta a hroot hDelta hgen
  have hconj := oddAS_actualConjugates_of_coordinate hp hG hres hchar D
    Delta a hroot hDelta hgen
  intro xi hxi
  obtain ⟨sigma, eta, hsigma, hetaRoot, _hresidual, hcases⟩ := hconj xi hxi
  have hxiK : (algebraMap B₂ K xi) ^ (p - 1) = 1 := by
    rw [← map_pow, hxi, map_one]
  have hDord : ord K (Delta + algebraMap B₂ K xi) =
      ((-(D.t : ℤ) : ℤ) : WithTop ℤ) :=
    translated_root_center_ord K (by have := hp.one_lt; omega)
      (by exact_mod_cast D.t_pos) Delta (algebraMap B₂ K xi) hDelta hxiK
  have hDne : Delta + algebraMap B₂ K xi ≠ 0 := (ord_ne_top_iff K).1 (by
    rw [hDord]; exact WithTop.coe_ne_top)
  refine ⟨sigma, eta, hsigma, hetaRoot, ?_, ?_, ?_⟩
  · rw [hsigma]
    exact translatedRoot_factor Delta (algebraMap B₂ K xi) eta hDne
  · rw [hsigma]
    exact translatedRoot_norm_factor D.B₁ K Delta (algebraMap B₂ K xi) eta hDne
  · rcases hcases with ⟨hpzero, heta⟩ | ⟨hpne, V, hV, _herror, heta⟩
    · exact Or.inl ⟨hpzero, by simp [heta, translatedRootUnit]⟩
    · have hpZ : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
      have hVbound := oddTotal_primeValuationBound hp hG hres D
      rw [hV, WithTop.coe_le_coe] at hVbound
      push_cast [Nat.cast_sub hp.one_le] at hVbound
      have ht₂ : (D.t : ℤ) ≤ D.t₂ := by exact_mod_cast D.t_le_t₂
      have hVt : ((p : ℤ) - 1) * D.t ≤ V := by
        have h1 := mul_nonneg
          (mul_nonneg (show (0 : ℤ) ≤ (p : ℤ) - 1 by omega)
            (show (0 : ℤ) ≤ (p : ℤ) - 1 by omega)) (Int.natCast_nonneg D.t)
        have h2 := mul_nonneg
          (mul_nonneg (show (0 : ℤ) ≤ p by omega)
            (show (0 : ℤ) ≤ (p : ℤ) - 1 by omega)) (sub_nonneg.mpr ht₂)
        nlinarith only [hVbound, h1, h2]
      have hetaMem : eta ∈ lattice K (V - ((p : ℤ) - 1) * D.t) := by
        rw [mem_lattice]
        simpa only [Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one] using heta
      have hactual : (Delta + algebraMap B₂ K xi + eta) ^ p -
          (Delta + algebraMap B₂ K xi + eta) = Delta ^ p - Delta := hetaRoot.trans hroot.symm
      refine Or.inr ⟨hpne, V, hV,
        translatedRootUnit_mem K p D.t V Delta (algebraMap B₂ K xi) eta hDord hetaMem,
        translatedRootUnit_first_iterate K hp D.t V (by positivity) hVt Delta
          (algebraMap B₂ K xi) eta hDord hV hetaMem hactual, ?_⟩
      intro hp3
      clear hchar
      subst p
      have hxi3 : (algebraMap B₂ K xi) ^ 2 = 1 := by simpa only using hxiK
      exact (translatedRootUnit_cubic_iterates K D.t V (by positivity)
        (by simpa using hVt) Delta (algebraMap B₂ K xi) eta hxi3 hDord
        (by simpa using hV) (by simpa using hetaMem) hactual).2

/-- A constructor from the genuine totally ramified Galois diamond, using
`oddAS_actualConjugates`. The root corrections are actual conjugates;
no stationary model or norm identity is assumed. It preserves the
coordinate, its norm-domain field, the zero correction in equal
characteristic, and both mixed-characteristic Newton precisions. -/
theorem translatedRoot_actualUnitCorrections
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = p)
    (D : OddTotalBreakData (F := F) (K := K) hp hG) :
    let B₂ := D.B₂
    letI := Basic.intermediateFieldValuativeRel B₂
    letI := Basic.intermediateFieldTopology B₂
    letI := Basic.intermediateField_localField B₂
    ∃ (Delta : K) (a : B₂),
      Delta ^ p - Delta = algebraMap B₂ K a ∧
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ¬ p ∣ D.t ∧ Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ ∧
      ∀ xi : B₂, xi ^ (p - 1) = 1 →
        ∃ (sigma : Gal(K/B₂)) (eta : K),
          sigma Delta = Delta + algebraMap B₂ K xi + eta ∧
          (Delta + algebraMap B₂ K xi + eta) ^ p -
            (Delta + algebraMap B₂ K xi + eta) = algebraMap B₂ K a ∧
          sigma Delta = (Delta + algebraMap B₂ K xi) *
            (1 + translatedRootUnit Delta (algebraMap B₂ K xi) eta) ∧
          norm D.B₁ K (sigma Delta) = norm D.B₁ K (Delta + algebraMap B₂ K xi) *
            norm D.B₁ K (1 + translatedRootUnit Delta (algebraMap B₂ K xi) eta) ∧
          (((p : K) = 0 ∧ translatedRootUnit Delta (algebraMap B₂ K xi) eta = 0) ∨
            ((p : K) ≠ 0 ∧ ∃ V : ℤ,
              ord K (p : K) = (V : WithTop ℤ) ∧
              translatedRootUnit Delta (algebraMap B₂ K xi) eta ∈
                lattice K (V - ((p : ℤ) - 2) * D.t) ∧
              translatedRootUnit Delta (algebraMap B₂ K xi) eta -
                translatedRootResidual p Delta (algebraMap B₂ K xi) ∈
                  lattice K (2 * V - (2 * (p : ℤ) - 3) * D.t) ∧
              (p = 3 →
                translatedRootUnit Delta (algebraMap B₂ K xi) eta -
                  3 * algebraMap B₂ K xi * Delta -
                  3 * (Delta + algebraMap B₂ K xi) ^ 2 *
                    (3 * algebraMap B₂ K xi * Delta) ∈
                      lattice K (3 * V - 5 * D.t)))) := by
  letI := Basic.intermediateFieldValuativeRel D.B₂
  letI := Basic.intermediateFieldTopology D.B₂
  letI := Basic.intermediateField_localField D.B₂
  obtain ⟨Delta, a, hroot, hDelta, ha, hprime, hgen, _⟩ :=
    oddAS_actualConjugates hp hG hres hchar D
  exact ⟨Delta, a, hroot, hDelta, ha, hprime, hgen,
    translatedRoot_actualUnitCorrections_of_coordinate hp hG hres hchar D
      Delta a hroot hDelta hgen⟩

/-- Raising a unit congruence to a power retains its linear term. The
square of that term is discarded only with the explicit bound `H ≤ 2q`.
This works for every natural power, including zero. -/
theorem translatedUnit_power_linear
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (y z : E) (q H : ℤ) (hq : 0 ≤ q) (hH : 0 ≤ H) (hHq : H ≤ 2 * q)
    (hz : z ∈ lattice E q) (hy : y - 1 - z ∈ lattice E H) (k : ℕ) :
    y ^ k - 1 - (k : E) * z ∈ lattice E H := by
  have hz0 := lattice_antitone E hq hz
  have hy0 : y ∈ lattice E 0 := by
    have heq : y = 1 + z + (y - 1 - z) := by ring
    rw [heq]
    exact (lattice E 0).add_mem ((lattice E 0).add_mem
      (by simpa only [Nat.cast_one] using natCast_mem_int_lattice_zero E 1) hz0) (lattice_antitone E hH hy)
  have hz2 : z ^ 2 ∈ lattice E H := by
    apply lattice_antitone E hHq
    simpa using pow_mem_int_lattice E hz 2
  induction k with
  | zero => simp
  | succ k ih =>
    have heq : y ^ (k + 1) - 1 - ((k + 1 : ℕ) : E) * z =
        (y ^ k - 1 - (k : E) * z) * y +
        (1 + (k : E) * z) * (y - 1 - z) + (k : E) * z ^ 2 := by
      push_cast
      rw [pow_succ]
      ring
    rw [heq]
    apply (lattice E H).add_mem
    · apply (lattice E H).add_mem
      · simpa using mul_mem_lattice E ih hy0
      · have hkz : (k : E) * z ∈ lattice E 0 := by
          simpa using mul_mem_lattice E (natCast_mem_int_lattice_zero E k) hz0
        have hlin := (lattice E 0).add_mem (by simpa only [Nat.cast_one] using natCast_mem_int_lattice_zero E 1) hkz
        simpa using mul_mem_lattice E hlin hy
    · simpa using mul_mem_lattice E (natCast_mem_int_lattice_zero E k) hz2

/-- The final weighted cancellation step. `A xi` is the translated norm
power and `U xi` its multiplicative correction. The outer weight `X` is
kept in both error estimates, allowing negative valuations of `A xi` and
of `b`. The exact sum of the representatives kills the retained linear
term only after summation. -/
theorem translatedNorm_weighted_cancellation
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {ι : Type*} (s : Finset ι) (xi A U : ι → E)
    (X b L : E) (k : ℕ) (t M R : ℤ)
    (hxi : ∀ j ∈ s, xi j ∈ lattice E 0)
    (hsum : ∑ j ∈ s, xi j = 0)
    (hL : L ∈ lattice E M)
    (hA : ∀ j ∈ s, X * A j ∈ lattice E (R - t))
    (hAb : ∀ j ∈ s, X * (A j - b) ∈ lattice E R)
    (hU : ∀ j ∈ s, U j - 1 - (k : E) * xi j * L ∈ lattice E (M + t)) :
    X * (∑ j ∈ s, A j * U j) - X * (∑ j ∈ s, A j) ∈ lattice E (M + R) := by
  have hlinear : ∑ j ∈ s, X * b * (k : E) * L * xi j = 0 := by
    rw [← Finset.mul_sum, hsum, mul_zero]
  have hterm : ∀ j ∈ s,
      X * A j * (U j - 1 - (k : E) * xi j * L) +
      X * (A j - b) * ((k : E) * xi j * L) ∈ lattice E (M + R) := by
    intro j hj
    apply (lattice E _).add_mem
    · have h := mul_mem_lattice E (hA j hj) (hU j hj)
      convert h using 1; ring
    · have hxiK : (k : E) * xi j ∈ lattice E 0 := by
        simpa using mul_mem_lattice E (natCast_mem_int_lattice_zero E k) (hxi j hj)
      have hlin : (k : E) * xi j * L ∈ lattice E M := by
        simpa using mul_mem_lattice E hxiK hL
      have h := mul_mem_lattice E (hAb j hj) hlin
      convert h using 1; ring
  have heq : X * (∑ j ∈ s, A j * U j) - X * (∑ j ∈ s, A j) =
      (∑ j ∈ s, (X * A j * (U j - 1 - (k : E) * xi j * L) +
        X * (A j - b) * ((k : E) * xi j * L))) +
        ∑ j ∈ s, X * b * (k : E) * L * xi j := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq, hlinear, add_zero]
  exact sum_mem_lattice E hterm

/-- Integral lower symmetric coefficients control the difference between
an actual translated norm and the original norm. -/
theorem translatedNorm_shift_integral
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra E L] [Module.Free E L] [Module.Finite E L]
    {p : ℕ} (hdegree : Module.finrank E L = p)
    (Delta : L) (c : E) (hc : c ≠ 0) (hcint : c ∈ lattice E 0)
    (he : ∀ i : ℕ, 1 ≤ i → i < p →
      elementarySymmetric E L i (algebraMap E L c⁻¹ * Delta) ∈ lattice E 0) :
    norm E L (Delta + algebraMap E L c) - norm E L Delta ∈ lattice E 0 := by
  let u := algebraMap E L c⁻¹ * Delta
  have hfactor : Delta + algebraMap E L c = algebraMap E L c * (1 + u) := by
    dsimp only [u]
    rw [mul_add, mul_one, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
    ring
  have hnorm : c ^ p * norm E L u = norm E L Delta := by
    dsimp only [u]
    rw [map_mul, LanglandsFirstMainLemma.norm_algebraMap, hdegree, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hc, one_pow, one_mul]
  have heq : norm E L (Delta + algebraMap E L c) - norm E L Delta =
      c ^ p * ∑ i ∈ Finset.range p, elementarySymmetric E L i u := by
    rw [hfactor, map_mul, LanglandsFirstMainLemma.norm_algebraMap, hdegree,
      norm_one_add_eq_sum_elementarySymmetric, hdegree, Finset.sum_range_succ,
      ← hdegree, elementarySymmetric_finrank, hdegree, mul_add, hnorm, add_sub_cancel_right]
  rw [heq]
  have hsum : (∑ i ∈ Finset.range p, elementarySymmetric E L i u) ∈ lattice E 0 := by
    apply sum_mem_lattice E
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      simp
    · exact he i (by omega) (Finset.mem_range.mp hi)
  simpa using mul_mem_lattice E (pow_mem_int_lattice E hcint p) hsum

/-- The power difference gains one factor of the integral norm difference;
negative orders of the two norms are retained. -/
theorem translatedNorm_power_difference
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (a b : E) (t : ℤ) (ht : 0 ≤ t)
    (ha : a ∈ lattice E (-t)) (hb : b ∈ lattice E (-t))
    (hab : a - b ∈ lattice E 0) (k : ℕ) :
    a ^ k - b ^ k ∈ lattice E (-((k : ℤ) - 1) * t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have heq : a ^ (k + 1) - b ^ (k + 1) = (a ^ k - b ^ k) * a + b ^ k * (a - b) := by
      simp only [pow_succ]; ring
    rw [heq]
    have h₁ := mul_mem_lattice E ih ha
    have h₂ := mul_mem_lattice E (pow_mem_int_lattice E hb k) hab
    apply (lattice E _).add_mem
    · convert h₁ using 1
      push_cast
      ring
    · convert h₂ using 1
      push_cast
      ring

/-- These representatives enumerate exactly `0 ∪ μ_(p-1)` in the base
field, so summing over `ZMod p` retains the complete translated-root sum. -/
theorem translatedNorm_representatives
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] (hchar : residueCharacteristic F = p) (c : F) :
    (∃ j : ZMod p, (primeTeichmuller F p hchar j : F) = c) ↔
      c = 0 ∨ c ^ (p - 1) = 1 := by
  have hp : p.Prime := Fact.out
  have hpoly := congrArg (Polynomial.eval₂RingHom ((ValuativeRel.valuation F).integer.subtype) c)
    (primeTeichmullerPolynomial_sub F p hchar)
  simp only [map_prod, coe_eval₂RingHom, eval₂_sub, eval₂_X, eval₂_C, eval₂_pow] at hpoly
  have heq : (∃ j : ZMod p, (primeTeichmuller F p hchar j : F) = c) ↔ c ^ p - c = 0 := by
    rw [← hpoly, Finset.prod_eq_zero_iff]
    simp only [Finset.mem_univ, true_and, sub_eq_zero]
    exact exists_congr (fun _ => eq_comm)
  rw [heq, show c ^ p - c = c * (c ^ (p - 1) - 1) by
    rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hp.one_le], mul_eq_zero, sub_eq_zero]

private theorem translatedNorm_representatives_separated
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (p : ℕ) [Fact p.Prime] (hchar : residueCharacteristic F = p)
    (i j : ZMod p)
    (h : algebraMap F K ((primeTeichmuller F p hchar i : F) -
      (primeTeichmuller F p hchar j : F)) ∈ lattice K 1) : i = j := by
  have hposK : ord K (algebraMap F K 1) < ord K (algebraMap F K
      ((primeTeichmuller F p hchar i : F) - (primeTeichmuller F p hchar j : F))) := by
    simpa only [map_one, ord_one] using
      lt_of_lt_of_le (by norm_num : (0 : WithTop ℤ) < (1 : ℤ)) ((mem_lattice K).1 h)
  have hposF := (ord_algebraMap_lt_iff F K 1 _).1 hposK
  have hm := (ord_pos_iff_mem_maximalIdeal F
    (primeTeichmuller F p hchar i - primeTeichmuller F p hchar j)).1
      (by simpa using hposF)
  have hr := (IsLocalRing.residue_eq_zero_iff _).2 hm
  change residueMap F (primeTeichmuller F p hchar i - primeTeichmuller F p hchar j) = 0 at hr
  rw [map_sub, sub_eq_zero, residueMap_primeTeichmuller, residueMap_primeTeichmuller] at hr
  exact (ZMod.castHom _ (ResidueField F)).injective hr

/-- Restriction identifies the actual upper conjugate norm sum with the
lower trace. Normality of the first lower field is supplied by the
abelian diamond; the norm compatibility is proved for the genuine maps. -/
theorem translatedNorm_actualTrace
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Module.Finite F K]
    (B₁ B₂ : IntermediateField F K) [IsGalois F B₁] [IsGalois B₂ K]
    {p : ℕ} [Fact p.Prime] (hp : p.Prime)
    (h₁ : Module.finrank F B₁ = p) (h₂ : Module.finrank F B₂ = p)
    (hupper : Module.finrank B₂ K = p) (hne : B₁ ≠ B₂)
    (e : ZMod p ≃ Gal(K/B₂)) (Delta : K) (k : ℕ) :
    (∑ j : ZMod p, norm B₁ K (e j Delta) ^ k) =
      algebraMap F B₁ (trace F B₁ (norm B₁ K Delta ^ k)) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hinf : B₁ ⊓ B₂ = ⊥ := by
    have hdvd := IntermediateField.finrank_dvd_of_le_right
      (show B₁ ⊓ B₂ ≤ B₁ from inf_le_left)
    rw [h₁] at hdvd
    rcases (Nat.dvd_prime hp).1 hdvd with hone | heq
    · exact IntermediateField.finrank_eq_one_iff.mp hone
    · exact (hne ((IntermediateField.eq_of_le_of_finrank_eq inf_le_left
        (heq.trans h₁.symm)).symm.trans
          (IntermediateField.eq_of_le_of_finrank_eq inf_le_right (heq.trans h₂.symm)))).elim
  let r := IntermediateField.restrictRestrictAlgEquivMapHom F B₁ B₂ K
  have hr : Function.Bijective r := (Fintype.bijective_iff_surjective_and_card r).2
    ⟨IntermediateField.restrictRestrictAlgEquivMapHom_surjective B₁ B₂ hinf, by
      simp only [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hupper, h₁]⟩
  let er := Equiv.ofBijective r hr
  have hn (sigma : Gal(K/B₂)) : norm B₁ K (sigma Delta) = r sigma (norm B₁ K Delta) := by
    have h := Algebra.norm_eq_of_equiv_equiv (r sigma).toRingEquiv sigma.toRingEquiv
      (by ext c; exact IntermediateField.restrictRestrictAlgEquivMapHom_apply B₁ B₂ sigma c) Delta
    change norm B₁ K Delta = (r sigma).symm (norm B₁ K (sigma Delta)) at h
    simpa only [AlgEquiv.apply_symm_apply] using (congrArg (r sigma) h).symm
  rw [trace_eq_sum_automorphisms, ← er.sum_comp, ← e.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  exact (congrArg (fun z : B₁ => z ^ k) (hn (e j))).trans (map_pow (r (e j)) _ k).symm

private theorem translatedNorm_residueDegree_tower
    (F E K : Type*) [Field F] [Field E] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    [ValuativeExtension F E] [ValuativeExtension E K] [ValuativeExtension F K]
    [Module.Finite F E] [Module.Finite E K] [Module.Finite F K] :
    residueDegree F E * residueDegree E K = residueDegree F K := by
  letI : IsScalarTower (ringOfIntegers F) (ringOfIntegers E) (ringOfIntegers K) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap F K (x : F) = algebraMap E K (algebraMap F E (x : F))
      rw [← IsScalarTower.algebraMap_apply F E K])
  letI : IsLocalHom (algebraMap (ringOfIntegers F) (ringOfIntegers E)) := inferInstance
  letI : IsLocalHom (algebraMap (ringOfIntegers E) (ringOfIntegers K)) := inferInstance
  rw [residueDegree_eq_finrank_residueField, residueDegree_eq_finrank_residueField,
    residueDegree_eq_finrank_residueField]
  exact Module.finrank_mul_finrank (ResidueField F) (ResidueField E) (ResidueField K)

section TranslatedNormAssembly

-- Use the canonical intermediate-field structures throughout the private helpers.
attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

namespace TranslatedNormProof

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K]
variable [Module.Finite F K] [IsGalois F K]
variable {p : ℕ} (hp : p.Prime)
variable (hG : Nonempty
  (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
variable (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
variable (D : OddTotalBreakData (F := F) (K := K) hp hG)

local notation "B₁" => D.B₁
local notation "B₂" => D.B₂
local notation "M" => (p : ℤ) * D.t₂

include hp hG hres in
/-- Total ramification and the degree of each edge of the actual diamond. -/
private theorem tower_data (B : IntermediateField F K) (hdegree : Module.finrank F B = p) :
    residueDegree F B = 1 ∧ residueDegree B K = 1 ∧
      ramificationIndex F B = p ∧ ramificationIndex B K = p ∧
      Module.finrank B K = p ∧ CyclicPrimeExtension F B ∧ CyclicPrimeExtension B K := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hupper, hlowerCyclic, hupperCyclic⟩ :=
    Basic.intermediateField_tower_compatible hp hG B hdegree
  obtain ⟨hlower, hupperRes⟩ := mul_eq_one.mp
    ((translatedNorm_residueDegree_tower F B K).trans hres)
  refine ⟨hlower, hupperRes, ?_, ?_, hupper, hlowerCyclic, hupperCyclic⟩
  · simpa only [hlower, mul_one, hdegree] using
      (finrank_eq_ramificationIndex_mul_residueDegree F B).symm
  · simpa only [hupperRes, mul_one, hupper] using
      (finrank_eq_ramificationIndex_mul_residueDegree B K).symm

omit [IsGalois F K] in
private theorem break_le_norm_depth : (D.t : ℤ) ≤ M := by
  exact_mod_cast D.t_le_t₂.trans (Nat.le_mul_of_pos_left D.t₂ hp.pos)

include hres in
private theorem prime_mem (hram : ramificationIndex B₁ K = p) :
    (p : B₁) ∈ lattice B₁ (((p : ℤ) - 1) * D.t₂) := by
  by_cases hz : (p : B₁) = 0
  · simp [hz]
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff B₁).2 hz)
  have h := oddTotal_primeValuationBound hp hG hres D
  rw [show (p : K) = algebraMap B₁ K (p : B₁) by simp,
    ord_algebraMap, hram, ← hv, ← WithTop.coe_nsmul, WithTop.coe_le_coe] at h
  push_cast [Nat.cast_sub hp.one_le] at h
  rw [mem_lattice, ← hv, WithTop.coe_le_coe]
  exact le_of_mul_le_mul_left (by simpa only [nsmul_eq_mul, mul_assoc] using h)
    (by exact_mod_cast hp.pos)

private theorem upper_trace_bound [PrimeCyclicExtension B₁ K]
    (hresUpper : residueDegree B₁ K = 1) (hdegree : Module.finrank B₁ K = p) :
    TraceIdealLowerBound B₁ K p
      (((p : ℤ) - 1) * ((D.t : ℤ) + (p : ℤ) * D.delta + 1)) := by
  have hbreak : PrimeCyclicExtension.IsLowerBreak B₁ K D.tPrime := by
    simpa only [OddTotalBreakData.B₁, Ramification.IntermediateBreakPair] using D.B₁_breaks.2
  obtain ⟨pi, hpi, hpiGen⟩ := monogenicUniformizer B₁ K hresUpper
  have h := traceIdealLowerBound_of_integralGenerator B₁ K hbreak hresUpper pi hpi hpiGen
  simpa only [hdegree, D.tPrime_eq, Nat.cast_mul, Nat.cast_add,
    Nat.cast_sub hp.one_le, Nat.cast_one] using h

omit [IsGalois F K] in
/-- The two specializations of the twisted trace estimate used in the unit correction. -/
private theorem coordinate_trace_bounds (Delta : K) (a : B₂)
    (hroot : Delta ^ p - Delta = algebraMap B₂ K a)
    (ha : ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (htw : ∀ (Y : B₂) (i : ℕ), i < p →
      ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) + ord B₂ Y ≤
        ord B₁ (trace B₁ K (algebraMap B₂ K Y * Delta ^ i))) :
    (∀ i : ℕ, i < p → trace B₁ K (Delta ^ i) ∈
      lattice B₁ (((p : ℤ) - 1) * ((D.t : ℤ) + D.delta) - (i : ℤ) * D.t)) ∧
    (p = 3 → trace B₁ K (Delta ^ 3 - Delta) ∈ lattice B₁ ((D.t : ℤ) + 2 * D.delta)) := by
  have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
  constructor
  · intro i hi
    simpa only [map_one, one_mul, ord_one, add_zero, mem_lattice, ht₂] using htw 1 i hi
  · intro hp3
    have hr : Delta ^ 3 - Delta = algebraMap B₂ K a := by simpa only [hp3] using hroot
    have h := htw a 0 hp.pos
    rw [ha, pow_zero, mul_one, ← WithTop.coe_add] at h
    rw [hr, mem_lattice]
    convert h using 1
    congr 1
    simp only [hp3, ht₂, Nat.cast_zero, Nat.cast_ofNat]
    ring

omit [IsGalois F K] in
private theorem linear_term_mem (Delta : K)
    (hpval : (p : B₁) ∈ lattice B₁ (((p : ℤ) - 1) * D.t₂))
    (htr : ∀ i : ℕ, i < p → trace B₁ K (Delta ^ i) ∈
      lattice B₁ (((p : ℤ) - 1) * ((D.t : ℤ) + D.delta) - (i : ℤ) * D.t)) :
    (p : B₁) * trace B₁ K (Delta ^ (p - 2)) ∈ lattice B₁ M := by
  have hpZ : (3 : ℤ) ≤ p := by exact_mod_cast D.odd_prime
  have h := mul_mem_lattice B₁ hpval (htr (p - 2) (by omega))
  apply lattice_antitone B₁ _ h
  push_cast [Nat.cast_sub (show 2 ≤ p by omega)]
  rw [D.t₂_eq, Nat.cast_add]
  have := mul_nonneg (show (0 : ℤ) ≤ (p : ℤ) - 2 by omega) (Int.natCast_nonneg D.delta)
  nlinarith

variable [Fact p.Prime]

/-- The same base-field representative, mapped into any edge of the tower. -/
private def representative (E : Type*) [Field E] [Algebra F E] (j : ZMod p) : E :=
  algebraMap F E (primeTeichmuller F p hchar j : F)

local notation "c₁" => representative hchar B₁
local notation "c₂" => representative hchar B₂
local notation "cK" => representative hchar K

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K] in
private theorem representative_map (E : IntermediateField F K) (j : ZMod p) :
    algebraMap E K (representative hchar E j) = cK j := by
  simp only [representative, ← IsScalarTower.algebraMap_apply F E K]

private theorem representative_pow (E : Type*) [Field E] [Algebra F E]
    (j : ZMod p) (hj : j ≠ 0) : representative hchar E j ^ (p - 1) = 1 := by
  have h := congrArg (primeTeichmuller F p hchar) (ZMod.pow_card_sub_one_eq_one hj)
  have hF : (primeTeichmuller F p hchar j : F) ^ (p - 1) = 1 := by
    exact_mod_cast (by simpa only [map_pow, map_one] using h :
      (primeTeichmuller F p hchar j) ^ (p - 1) = 1)
  simp only [representative, ← map_pow, hF, map_one]

omit [IsGalois F K] in
private theorem representative_mem (E : IntermediateField F K) (j : ZMod p) :
    representative hchar E j ∈ lattice E 0 := by
  rw [representative, mem_lattice, ord_algebraMap]
  exact nsmul_nonneg
    ((ord_nonneg_iff_mem_integer F _).2 (primeTeichmuller F p hchar j).property) _

omit [IsGalois F K] in
private theorem representative_sum : ∑ j : ZMod p, c₁ j = 0 := by
  have h := congrArg ((ValuativeRel.valuation F).integer.subtype)
    (sum_primeTeichmuller F p hchar)
  have hF : ∑ j : ZMod p, (primeTeichmuller F p hchar j : F) = 0 := by
    simpa [show p ≠ 2 by have := D.odd_prime; omega] using h
  simp only [representative, ← map_sum, hF, map_zero]

omit [IsGalois F K] in
private theorem center_ord (Delta : K)
    (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ)) (j : ZMod p) :
    ord K (Delta + cK j) = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) := by
  by_cases hj : j = 0
  · simpa [hj, representative] using hDelta
  · exact translated_root_center_ord K (by have := hp.one_lt; omega)
      (by exact_mod_cast D.t_pos) Delta _ hDelta (representative_pow hchar K j hj)

include hres in
/-- A representative determines a genuine conjugate with a small displacement and
its linear norm correction, in either characteristic. -/
private theorem corrected_conjugate (Delta : K) (a : B₂)
    (hroot : Delta ^ p - Delta = algebraMap B₂ K a)
    (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hgen : Algebra.adjoin B₂ ({Delta} : Set K) = ⊤)
    (hram : ramificationIndex B₁ K = p) (hdegree : Module.finrank B₁ K = p)
    (htrace : TraceIdealLowerBound B₁ K p
      (((p : ℤ) - 1) * ((D.t : ℤ) + (p : ℤ) * D.delta + 1)))
    (hpval : (p : B₁) ∈ lattice B₁ (((p : ℤ) - 1) * D.t₂))
    (htr : ∀ i : ℕ, i < p → trace B₁ K (Delta ^ i) ∈
      lattice B₁ (((p : ℤ) - 1) * ((D.t : ℤ) + D.delta) - (i : ℤ) * D.t))
    (hA3 : p = 3 → trace B₁ K (Delta ^ 3 - Delta) ∈ lattice B₁ ((D.t : ℤ) + 2 * D.delta))
    (j : ZMod p) :
    ∃ (sigma : Gal(K/B₂)) (eta : K), sigma Delta = Delta + cK j + eta ∧
      eta ∈ lattice K 1 ∧
      norm B₁ K (1 + translatedRootUnit Delta (cK j) eta) - 1 -
        c₁ j * ((p : B₁) * trace B₁ K (Delta ^ (p - 2))) ∈ lattice B₁ (M + D.t) := by
  by_cases hj : j = 0
  · subst j
    refine ⟨1, 0, ?_, by simp, ?_⟩ <;> simp [representative, translatedRootUnit]
  have hcenter := center_ord hp hG hchar D Delta hDelta j
  have hcenterNe : Delta + cK j ≠ 0 := (ord_ne_top_iff K).1 (by
    rw [hcenter]; exact WithTop.coe_ne_top)
  obtain ⟨sigma, eta, hsigma, hetaRoot, _, _, hcases⟩ :=
    translatedRoot_actualUnitCorrections_of_coordinate hp hG hres hchar D
      Delta a hroot hDelta hgen (c₂ j) (representative_pow hchar B₂ j hj)
  rw [representative_map] at hsigma hetaRoot hcases
  have hetamul : eta = (Delta + cK j) * translatedRootUnit Delta (cK j) eta := by
    simp only [translatedRootUnit, mul_div_cancel₀ _ hcenterNe]
  refine ⟨sigma, eta, hsigma, ?_⟩
  rcases hcases with ⟨hpzero, hu⟩ | ⟨_, V, hV, hu, _, _⟩
  · have heta : eta = 0 := by rw [hetamul, hu, mul_zero]
    have hpzero₁ : (p : B₁) = 0 := (algebraMap B₁ K).injective (by simpa using hpzero)
    simp [heta, translatedRootUnit, hpzero₁]
  · have ht : (0 : ℤ) < D.t := by exact_mod_cast D.t_pos
    have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
    have hpZ : (3 : ℤ) ≤ p := by exact_mod_cast D.odd_prime
    have hVbound := oddTotal_primeValuationBound hp hG hres D
    rw [hV, WithTop.coe_le_coe] at hVbound
    push_cast [Nat.cast_sub hp.one_le] at hVbound
    rw [ht₂] at hVbound
    have hetaMem : eta ∈ lattice K (V - ((p : ℤ) - 1) * D.t) := by
      rw [hetamul]
      convert mul_mem_lattice K ((mem_lattice K).2 hcenter.ge) hu using 1
      ring
    have hdepth := (translatedNorm_higher_depth p 2 (by omega) (by omega)
      D.t D.delta V ht.le (by positivity) hVbound).1
    have hM := break_le_norm_depth hp hG D
    rw [ht₂] at hM
    refine ⟨lattice_antitone K (by linarith) hetaMem, ?_⟩
    let xi : ringOfIntegers B₁ := ⟨c₁ j, (mem_lattice_zero_iff B₁).1
      (representative_mem hchar B₁ j)⟩
    have hxi : xi ^ (p - 1) = 1 := by
      apply Subtype.ext
      exact representative_pow hchar B₁ j hj
    have hcor := translatedRoot_norm_unit_correction B₁ K hp D.odd_prime D.t D.delta D.t_pos V
      hVbound ((residueCharacteristic_extension_eq F B₁).trans hchar) hdegree hram htrace
      Delta eta xi hxi (by simpa only [xi, representative_map] using hcenter) hV
      (by simpa only [xi, representative_map] using hetaMem)
      (by simpa only [xi, representative_map] using hetaRoot.trans hroot.symm)
      (by simpa only [ht₂] using hpval) htr hA3
    simpa only [xi, representative_map, ht₂] using hcor

/-- Small displacements make the selected conjugates distinct, hence exhaustive. -/
private theorem conjugate_equiv (Delta : K) (L : B₁)
    (hdegree : Module.finrank B₂ K = p)
    (hpacket : ∀ j : ZMod p, ∃ (sigma : Gal(K/B₂)) (eta : K),
      sigma Delta = Delta + cK j + eta ∧ eta ∈ lattice K 1 ∧
      norm B₁ K (1 + translatedRootUnit Delta (cK j) eta) - 1 - c₁ j * L ∈
        lattice B₁ (M + D.t)) :
    ∃ (e : ZMod p ≃ Gal(K/B₂)) (eta : ZMod p → K),
      (∀ j, e j Delta = Delta + cK j + eta j) ∧
      (∀ j, norm B₁ K (1 + translatedRootUnit Delta (cK j) (eta j)) - 1 - c₁ j * L ∈
        lattice B₁ (M + D.t)) := by
  classical
  choose sigma eta hsigma heta hunit using hpacket
  have hinj : Function.Injective sigma := by
    intro i j hij
    apply translatedNorm_representatives_separated F K p hchar i j
    have heq : cK i - cK j = eta j - eta i := by
      have hi := hsigma i
      rw [hij] at hi
      linear_combination -hi + hsigma j
    rw [map_sub]
    change cK i - cK j ∈ _
    rw [heq]
    exact (lattice K 1).sub_mem (heta j) (heta i)
  have hbij : Function.Bijective sigma := (Fintype.bijective_iff_injective_and_card sigma).2
    ⟨hinj, by rw [ZMod.card, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hdegree]⟩
  exact ⟨Equiv.ofBijective sigma hbij, eta, hsigma, hunit⟩

/-- Twisted symmetric estimates give the integral difference of the two norms. -/
private theorem norm_difference_mem (Delta : K) (hdegree : Module.finrank B₁ K = p)
    (hsym : ∀ (Y : B₂) (i : ℕ), 1 ≤ i → i < p →
      ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) + i • ord B₂ Y ≤
        ord B₁ (elementarySymmetric B₁ K i (algebraMap B₂ K Y * Delta))) (j : ZMod p) :
    norm B₁ K (Delta + cK j) - norm B₁ K Delta ∈ lattice B₁ 0 := by
  by_cases hj : j = 0
  · simp [hj, representative]
  have hpZ : (3 : ℤ) ≤ p := by exact_mod_cast D.odd_prime
  have hcroot := representative_pow hchar B₁ j hj
  rw [← representative_map hchar B₁]
  apply translatedNorm_shift_integral B₁ K hdegree Delta (c₁ j)
    (by intro hz; rw [hz, zero_pow (by omega)] at hcroot; exact zero_ne_one hcroot)
    (representative_mem hchar B₁ j)
  intro i hi hip
  have hY : ord B₂ (c₂ j)⁻¹ = 0 := by
    rw [ord_inv, translated_root_torsion_ord B₂ (by omega : 0 < p - 1) _
      (representative_pow hchar B₂ j hj), neg_zero]
  have h := hsym (c₂ j)⁻¹ i hi hip
  rw [hY, nsmul_zero, add_zero] at h
  have hnonneg : 0 ≤ ((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t := by
    have hiZ : (i : ℤ) ≤ (p : ℤ) - 1 := by omega
    have := mul_nonneg (sub_nonneg.mpr hiZ) (Int.natCast_nonneg D.t)
    have := mul_nonneg (show (0 : ℤ) ≤ (p : ℤ) - 1 by omega) (Int.natCast_nonneg D.delta)
    rw [D.t₂_eq, Nat.cast_add]
    nlinarith
  rw [mem_lattice]
  have hbound := (WithTop.coe_le_coe.mpr hnonneg).trans h
  simpa only [map_inv₀, representative_map] using hbound

/-- Raise the norm corrections to the requested power, cancel their linear terms,
and identify the sum over conjugates with the actual lower trace. -/
private theorem weighted_congruence [IsGalois F B₁]
    (Delta : K) (L : B₁) (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hL : L ∈ lattice B₁ M)
    (hres₁K : residueDegree B₁ K = 1) (hresF₂ : residueDegree F B₂ = 1)
    (hramF₁ : ramificationIndex F B₁ = p) (hdegreeUpper₂ : Module.finrank B₂ K = p)
    (e : ZMod p ≃ Gal(K/B₂)) (eta : ZMod p → K)
    (hsigma : ∀ j, e j Delta = Delta + cK j + eta j)
    (hunit : ∀ j, norm B₁ K (1 + translatedRootUnit Delta (cK j) (eta j)) - 1 - c₁ j * L ∈
      lattice B₁ (M + D.t))
    (hdiff : ∀ j, norm B₁ K (Delta + cK j) - norm B₁ K Delta ∈ lattice B₁ 0)
    (x : B₂) (v : ℤ) (k : ℕ) (hx : x ∈ lattice B₂ v) :
    let R := (p : ℤ) * v - ((k : ℤ) - 1) * D.t
    let X := algebraMap F B₁ (norm F B₂ x)
    X * algebraMap F B₁ (trace F B₁ (norm B₁ K Delta ^ k)) -
      X * (∑ j : ZMod p, norm B₁ K (Delta + cK j) ^ k) ∈ lattice B₁ (M + R) := by
  classical
  let R : ℤ := (p : ℤ) * v - ((k : ℤ) - 1) * D.t
  let X : B₁ := algebraMap F B₁ (norm F B₂ x)
  have ht : (0 : ℤ) ≤ D.t := by positivity
  have hM := break_le_norm_depth hp hG D
  have hcenter := center_ord hp hG hchar D Delta hDelta
  have hnormOrd (j) : ord B₁ (norm B₁ K (Delta + cK j)) = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_norm, hres₁K, one_nsmul, hcenter]
  have hbOrd : ord B₁ (norm B₁ K Delta) = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_norm, hres₁K, one_nsmul, hDelta]
  have hX : X ∈ lattice B₁ ((p : ℤ) * v) := by
    rw [mem_lattice, ord_algebraMap, hramF₁, ord_norm, hresF₂, one_nsmul]
    simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using
      nsmul_le_nsmul_right ((mem_lattice B₂).1 hx) p
  let A (j : ZMod p) : B₁ := norm B₁ K (Delta + cK j) ^ k
  let U (j : ZMod p) : B₁ := norm B₁ K (1 + translatedRootUnit Delta (cK j) (eta j)) ^ k
  have hA (j) : X * A j ∈ lattice B₁ (R - D.t) := by
    have h := mul_mem_lattice B₁ hX (pow_mem_int_lattice B₁ ((mem_lattice B₁).2 (hnormOrd j).ge) k)
    convert h using 1
    dsimp only [R]
    ring
  have hAb (j) : X * (A j - norm B₁ K Delta ^ k) ∈ lattice B₁ R := by
    have h := translatedNorm_power_difference B₁ _ _ D.t ht
      ((mem_lattice B₁).2 (hnormOrd j).ge) ((mem_lattice B₁).2 hbOrd.ge) (hdiff j) k
    convert mul_mem_lattice B₁ hX h using 1
    dsimp only [R]
    ring
  have hU (j) : U j - 1 - (k : B₁) * c₁ j * L ∈ lattice B₁ (M + D.t) := by
    have hz : c₁ j * L ∈ lattice B₁ M := by
      simpa using mul_mem_lattice B₁ (representative_mem hchar B₁ j) hL
    simpa only [mul_assoc] using translatedUnit_power_linear B₁ _ (c₁ j * L) M (M + D.t)
      (by omega) (by omega) (by omega) hz (hunit j) k
  have hcancel := translatedNorm_weighted_cancellation B₁ Finset.univ c₁ A U X
    (norm B₁ K Delta ^ k) L k D.t M R (by intro j _; exact representative_mem hchar B₁ j)
    (representative_sum hp hG hchar D) hL (by intro j _; exact hA j)
    (by intro j _; exact hAb j) (by intro j _; exact hU j)
  have hactual : (∑ j : ZMod p, A j * U j) =
      algebraMap F B₁ (trace F B₁ (norm B₁ K Delta ^ k)) := by
    rw [← translatedNorm_actualTrace B₁ B₂ hp D.degree_B₁ D.degree_B₂
      hdegreeUpper₂ D.B₁_ne_B₂ e Delta k]
    apply Finset.sum_congr rfl
    intro j _
    have hcenterNe : Delta + cK j ≠ 0 := (ord_ne_top_iff K).1 (by
      rw [hcenter]; exact WithTop.coe_ne_top)
    rw [hsigma, translatedRoot_norm_factor B₁ K Delta (cK j) (eta j) hcenterNe, mul_pow]
  rw [hactual] at hcancel
  exact hcancel

include hres in
/-- Assemble the translated-norm estimate for a fixed coordinate carrying the
original twisted estimates. All auxiliary bounds come from the genuine diamond. -/
private theorem coordinate_congruence (Delta : K) (a : B₂)
    (hroot : Delta ^ p - Delta = algebraMap B₂ K a)
    (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (ha : ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hgen : Algebra.adjoin B₂ ({Delta} : Set K) = ⊤)
    (htw : ∀ (Y : B₂) (i : ℕ), i < p →
      ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) + ord B₂ Y ≤
        ord B₁ (trace B₁ K (algebraMap B₂ K Y * Delta ^ i)))
    (hsym : ∀ (Y : B₂) (i : ℕ), 1 ≤ i → i < p →
      ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) + i • ord B₂ Y ≤
        ord B₁ (elementarySymmetric B₁ K i (algebraMap B₂ K Y * Delta)))
    (x : B₂) (v : ℤ) (k : ℕ) (hx : x ∈ lattice B₂ v) :
    let R := (p : ℤ) * v - ((k : ℤ) - 1) * D.t
    let X := algebraMap F B₁ (norm F B₂ x)
    X * algebraMap F B₁ (trace F B₁ (norm B₁ K Delta ^ k)) -
      X * (∑ j : ZMod p, norm B₁ K (Delta + cK j) ^ k) ∈ lattice B₁ (M + R) := by
  obtain ⟨_, hres₁K, hramF₁, hram₁K, hdegree₁K, hcycF₁, hcyc₁K⟩ :=
    tower_data hp hG hres B₁ D.degree_B₁
  obtain ⟨hresF₂, _, _, _, hdegree₂K, _, _⟩ := tower_data hp hG hres B₂ D.degree_B₂
  letI : IsGalois F B₁ := hcycF₁.1
  letI : PrimeCyclicExtension B₁ K := PrimeCyclicExtension.ofCyclicPrimeExtension B₁ K hcyc₁K
  have hpval := prime_mem hp hG hres D hram₁K
  obtain ⟨htr, hA3⟩ := coordinate_trace_bounds hp hG D Delta a hroot ha htw
  let L : B₁ := (p : B₁) * trace B₁ K (Delta ^ (p - 2))
  obtain ⟨e, eta, hsigma, hunit⟩ := conjugate_equiv hp hG hchar D Delta L hdegree₂K
    (corrected_conjugate hp hG hres hchar D Delta a hroot hDelta hgen hram₁K hdegree₁K
      (upper_trace_bound hp hG D hres₁K hdegree₁K) hpval htr hA3)
  exact weighted_congruence hp hG hchar D Delta L hDelta (linear_term_mem hp hG D Delta hpval htr)
    hres₁K hresF₂ hramF₁ hdegree₂K e eta hsigma hunit
    (norm_difference_mem hp hG hchar D Delta hdegree₁K hsym) x v k hx

end TranslatedNormProof

/-- Paper `O:A:lem:translate` (2046–2114), from the genuine totally ramified
odd Galois diamond. The same coordinate carries the twisted estimates and
the actual conjugate corrections. For a nonzero `x`, take `v=v₂(x)`;
using arbitrary integer lattice bounds also includes `x=0` at every depth.
The outer weight is exactly the lower norm `X=n₂(x)`, and the precision
is exactly `p*t₂+R`, with `R=p*v-(k-1)*t`. The representatives are the
complete set `0 ∪ μ_(p-1)`, by `translatedNorm_representatives`. -/
theorem translatedNorm
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (D : OddTotalBreakData (F := F) (K := K) hp hG) :
    letI : Fact p.Prime := ⟨hp⟩
    let B₁ := D.B₁
    let B₂ := D.B₂
    letI := Basic.intermediateFieldValuativeRel B₁
    letI := Basic.intermediateFieldTopology B₁
    letI := Basic.intermediateField_localField B₁
    letI := Basic.intermediateFieldValuativeRel B₂
    letI := Basic.intermediateFieldTopology B₂
    letI := Basic.intermediateField_localField B₂
    ∃ (Delta : K) (a : B₂),
      Delta ^ p - Delta = algebraMap B₂ K a ∧
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ¬ p ∣ D.t ∧ Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ ∧
      (∀ (theta : B₁) (Z : Fin p → B₂),
        algebraMap B₁ K theta = ∑ r : Fin p, algebraMap B₂ K (Z r) * Delta ^ (r : ℕ) →
        ∀ r : Fin p, ord B₁ theta + ((((r : ℕ) * D.t : ℕ) : ℤ) : WithTop ℤ) ≤
          ord B₂ (Z r)) ∧
      (∀ (Y : B₂) (i : ℕ), i < p →
        ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) + ord B₂ Y ≤
          ord B₁ (trace B₁ K (algebraMap B₂ K Y * Delta ^ i))) ∧
      (∀ (Y : B₂) (i : ℕ), 1 ≤ i → i < p →
        ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) + i • ord B₂ Y ≤
          ord B₁ (elementarySymmetric B₁ K i (algebraMap B₂ K Y * Delta))) ∧
      (∀ i : ℕ, 1 ≤ i → i < p →
        ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) ≤
          ord B₁ (elementarySymmetric B₁ K i Delta)) ∧
      ((((p : ℤ) - 1) * D.delta : ℤ) : WithTop ℤ) ≤
        ord B₁ (-elementarySymmetric B₁ K (p - 1) Delta) ∧
      ∀ (x : B₂) (v : ℤ) (k : ℕ), x ∈ lattice B₂ v → 1 ≤ k → k ≤ p →
        let R := (p : ℤ) * v - ((k : ℤ) - 1) * D.t
        let X := algebraMap F B₁ (norm F B₂ x)
        1 ≤ R →
        X * algebraMap F B₁ (trace F B₁ (norm B₁ K Delta ^ k)) -
          X * (∑ j : ZMod p,
            norm B₁ K (Delta + algebraMap F K (primeTeichmuller F p hchar j : F)) ^ k) ∈
              lattice B₁ ((p : ℤ) * D.t₂ + R) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Delta, a, hroot, hDelta, ha, hprime, hgen, hcoeff, htw, hsym, hei, hs⟩ :=
    twistedEstimates hp hG hres hchar D
  refine ⟨Delta, a, hroot, hDelta, ha, hprime, hgen, hcoeff, htw, hsym, hei, hs, ?_⟩
  dsimp only
  intro x v k hx _hk _hkp _hR
  exact TranslatedNormProof.coordinate_congruence hp hG hres hchar D
    Delta a hroot hDelta ha hgen htw hsym x v k hx

end TranslatedNormAssembly

end

end LanglandsSecondMainLemma.Odd.Total
