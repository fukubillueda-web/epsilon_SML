import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Total.CoefficientExtraction
import LanglandsSecondMainLemma.Local.TraceIdeals

/-!
# Odd / Total / Twisted Estimates

Paper `O:A:lem:twisted`, including `O:A:eq:twtrace`, `O:A:eq:twsym`,
and `O:A:eq:ei`. Exact Artin--Schreier power traces and coefficient
extraction give the crossed bound by whole-lattice trace duality. Newton's
identity then gives the symmetric bounds with the same common gain.
The final constructor uses the actual odd totally ramified diamond and
retains its coordinate and coefficient data. All depths are integers;
valuations may be infinite, and the mixed-characteristic `p*a` moment is
retained.
-/

namespace LanglandsSecondMainLemma.Odd.Total

open LanglandsFirstMainLemma
open scoped BigOperators

noncomputable section

/-- The Newton step of `O:A:lem:twisted`. A common nonnegative gain in all
positive power traces persists in the elementary symmetric coefficients
below the residue characteristic. The slope is an integer, so this also
applies when `v₂(Y) - t` is negative.

This supporting implication does not assert the crossed trace estimate:
that estimate must be proved separately for the actual diamond. -/
theorem twistedSymmetric_of_powerTrace
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra E L] [Module.Free E L] [Module.Finite E L] [IsGalois E L]
    (x : L) (C q : ℤ) (hC : 0 ≤ C)
    (htrace : ∀ j : ℕ, 1 ≤ j → j < residueCharacteristic E →
      ((C + (j : ℤ) * q : ℤ) : WithTop ℤ) ≤ ord E (trace E L (x ^ j)))
    (i : ℕ) (hi : 1 ≤ i) (hip : i < residueCharacteristic E) :
    ((C + (i : ℤ) * q : ℤ) : WithTop ℤ) ≤
      ord E (elementarySymmetric E L i x) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    have hiord : ord E (i : E) = 0 :=
      ord_natCast_eq_zero_of_lt_residueCharacteristic E hi hip
    have hsum : ((C + (i : ℤ) * q : ℤ) : WithTop ℤ) ≤
        ord E (∑ b ∈ Finset.HasAntidiagonal.antidiagonal i with b.1 < i,
          (-1 : E) ^ b.1 * elementarySymmetric E L b.1 x *
            galoisPowerSum E L b.2 x) := by
      apply ord_sum E
      intro b hb
      simp only [Finset.mem_filter] at hb
      have hbadd : b.1 + b.2 = i := by simpa using hb.1
      have hb2pos : 1 ≤ b.2 := by omega
      have hb2p : b.2 < residueCharacteristic E := by omega
      have hpower := htrace b.2 hb2pos hb2p
      by_cases hbzero : b.1 = 0
      · have hb2 : b.2 = i := by omega
        simpa [hbzero, hb2, elementarySymmetric_zero, galoisPowerSum] using hpower
      · have hcoeff := ih b.1 hb.2 (by omega) (by omega)
        have hbcast : (b.1 : ℤ) + (b.2 : ℤ) = (i : ℤ) := by
          exact_mod_cast hbadd
        have harith : C + (i : ℤ) * q ≤
            (C + (b.1 : ℤ) * q) + (C + (b.2 : ℤ) * q) := by
          rw [← hbcast]
          nlinarith
        have hprod := add_le_add hcoeff hpower
        rw [← WithTop.coe_add] at hprod
        exact (WithTop.coe_le_coe.mpr harith).trans (by
          simpa [galoisPowerSum] using hprod)
    have hnewton := elementarySymmetric_newton_identity E L x i
    calc
      ((C + (i : ℤ) * q : ℤ) : WithTop ℤ) ≤
          ord E ((-1 : E) ^ (i + 1) *
            ∑ b ∈ Finset.HasAntidiagonal.antidiagonal i with b.1 < i,
              (-1 : E) ^ b.1 * elementarySymmetric E L b.1 x *
                galoisPowerSum E L b.2 x) := by simpa using hsum
      _ = ord E ((i : E) * elementarySymmetric E L i x) :=
        congrArg (ord E) hnewton.symm
      _ = ord E (elementarySymmetric E L i x) := by simp [hiord]

/-- Coordinates of a power strictly below the dimension in a power basis. -/
private theorem powerBasis_repr_pow
    {E L : Type*} [Field E] [Field L] [Algebra E L]
    (pb : PowerBasis E L) (n : ℕ) (hn : n < pb.dim) (r : Fin pb.dim) :
    pb.basis.repr (pb.gen ^ n) r = if (r : ℕ) = n then 1 else 0 := by
  rw [← pb.basis_eq_pow ⟨n, hn⟩, Module.Basis.repr_self]
  simp [Finsupp.single_apply, Fin.ext_iff, eq_comm]

/-- Exact positive power traces below the Artin--Schreier degree, computed
from the multiplication matrix in the actual power basis. This computation
is valid in mixed characteristic as well as in equal characteristic. -/
theorem artinSchreier_powerTrace_below
    {E L : Type*} [Field E] [Field L] [Algebra E L]
    (pb : PowerBasis E L) {p : ℕ} (hp : 2 < p) (hdim : pb.dim = p)
    (a : E) (hroot : pb.gen ^ p - pb.gen = algebraMap E L a)
    (j : ℕ) (hj : 1 ≤ j) (hjp : j < p) :
    Algebra.trace E L (pb.gen ^ j) =
      if j = p - 1 then ((p - 1 : ℕ) : E) else 0 := by
  have hroot' : pb.gen ^ p = pb.gen + algebraMap E L a :=
    sub_eq_iff_eq_add.mp hroot |>.trans (add_comm _ _)
  have hdiag (r : Fin pb.dim) :
      pb.basis.repr (pb.gen ^ j * pb.basis r) r =
        if j = p - 1 ∧ (r : ℕ) ≠ 0 then (1 : E) else 0 := by
    rw [pb.basis_eq_pow, ← pow_add]
    have hr : (r : ℕ) < p := by simpa [hdim] using r.isLt
    by_cases hsmall : j + (r : ℕ) < p
    · rw [powerBasis_repr_pow pb _ (by omega)]
      have hne : (r : ℕ) ≠ j + (r : ℕ) := by omega
      have hnot : ¬ (j = p - 1 ∧ (r : ℕ) ≠ 0) := by omega
      simp [hnot, show j ≠ 0 by omega]
    · have hexp : j + (r : ℕ) = p + (j + (r : ℕ) - p) := by omega
      have hreduce : pb.gen ^ (j + (r : ℕ)) =
          pb.gen ^ (j + (r : ℕ) - p + 1) +
            algebraMap E L a * pb.gen ^ (j + (r : ℕ) - p) := by
        conv_lhs => rw [hexp, pow_add, hroot', add_mul]
        rw [pow_succ]
        ring
      rw [hreduce, map_add, ← Algebra.smul_def, map_smul]
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
      rw [powerBasis_repr_pow pb _ (by omega),
        powerBasis_repr_pow pb _ (by omega)]
      have hne : (r : ℕ) ≠ j + (r : ℕ) - p := by omega
      have heq : (r : ℕ) = j + (r : ℕ) - p + 1 ↔
          j = p - 1 ∧ (r : ℕ) ≠ 0 := by omega
      simp [hne, heq]
  rw [Algebra.trace_eq_matrix_trace pb.basis, Matrix.trace]
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, hdiag]
  by_cases hjlast : j = p - 1
  · simp only [hjlast, true_and, if_true]
    have hzero : (⟨0, by omega⟩ : Fin pb.dim) ∈ Finset.univ := Finset.mem_univ _
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hzero]
    simp only [ne_eq, not_true_eq_false, if_false, zero_add]
    have hsum : (∑ r ∈ Finset.univ \ {(⟨0, by omega⟩ : Fin pb.dim)},
        if (r : ℕ) ≠ 0 then (1 : E) else 0) =
        ∑ _r ∈ Finset.univ \ {(⟨0, by omega⟩ : Fin pb.dim)}, (1 : E) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrne : r ≠ ⟨0, by omega⟩ := by simpa using hr
      have hrval : (r : ℕ) ≠ 0 := by simpa [Fin.ext_iff] using hrne
      simp [hrval]
    rw [hsum]
    simp [Finset.card_sdiff, hdim]
  · simp [hjlast]

/-- The complete moment range used in the crossed trace pairing in
`O:A:lem:twisted`. In particular, the degree-`p` moment is `p*a`, without
assuming that the field has characteristic `p`. -/
theorem artinSchreier_powerTraces
    {E L : Type*} [Field E] [Field L] [Algebra E L]
    (pb : PowerBasis E L) {p : ℕ} (hp : 2 < p) (hdim : pb.dim = p)
    (a : E) (hroot : pb.gen ^ p - pb.gen = algebraMap E L a)
    (k : ℕ) (hk : 1 ≤ k) (hkp : k ≤ 2 * p - 2) :
    Algebra.trace E L (pb.gen ^ k) =
      (if k = p - 1 then ((p - 1 : ℕ) : E) else 0) +
      (if k = p then (p : E) * a else 0) +
      (if k = 2 * p - 2 then ((p - 1 : ℕ) : E) else 0) := by
  by_cases hsmall : k < p
  · rw [artinSchreier_powerTrace_below pb hp hdim a hroot k hk hsmall]
    simp [show k ≠ p by omega, show k ≠ 2 * p - 2 by omega]
  · have hreduce : pb.gen ^ k = pb.gen ^ (k - p + 1) +
        algebraMap E L a * pb.gen ^ (k - p) := by
      have heq : k = p + (k - p) := by omega
      have hroot' : pb.gen ^ p = pb.gen + algebraMap E L a := by
        linear_combination hroot
      conv_lhs => rw [heq, pow_add, hroot', add_mul]
      rw [pow_succ]
      ring
    rw [hreduce, map_add, ← Algebra.smul_def, map_smul]
    change Algebra.trace E L (pb.gen ^ (k - p + 1)) +
      a * Algebra.trace E L (pb.gen ^ (k - p)) = _
    rw [artinSchreier_powerTrace_below pb hp hdim a hroot _ (by omega) (by omega)]
    by_cases heq : k = p
    · subst k
      simp only [Nat.sub_self, zero_add, pow_zero]
      have htr1 : Algebra.trace E L (1 : L) = (p : E) := by
        rw [show (1 : L) = algebraMap E L 1 by simp,
          Algebra.trace_algebraMap_of_basis pb.basis]
        simp [hdim]
      rw [htr1]
      simp [show 1 ≠ p - 1 by omega, show p ≠ p - 1 by omega,
        show p ≠ 2 * p - 2 by omega]
      ring
    · rw [artinSchreier_powerTrace_below pb hp hdim a hroot _ (by omega) (by omega)]
      have hlast : k - p + 1 = p - 1 ↔ k = 2 * p - 2 := by omega
      simp [show k ≠ p - 1 by omega, heq, hlast,
        show k - p ≠ p - 1 by omega]

/-- Whole-lattice trace duality, recovered from the exact trace-image
formula. Testing every element of the complementary fractional lattice is
essential; a single vanishing trace does not imply this conclusion. -/
theorem mem_lattice_iff_integral_tracePairing
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    [Module.Free E L] [Module.Finite E L] [Algebra.IsSeparable E L]
    (x : L) (c : ℤ) :
    x ∈ lattice L c ↔ ∀ theta : L,
      theta ∈ lattice L (-Local.differentIdealExponent E L - c) →
      trace E L (theta * x) ∈ lattice E 0 := by
  let D := Local.differentIdealExponent E L
  constructor
  · intro hx theta htheta
    have hprod : theta * x ∈ lattice L (-D) := by
      simpa [D] using mul_mem_lattice L htheta hx
    have himage : trace E L (theta * x) ∈
        Submodule.map ((trace E L).restrictScalars (ringOfIntegers E))
          ((lattice L (-D)).restrictScalars (ringOfIntegers E)) :=
      Submodule.mem_map.mpr ⟨theta * x, hprod, rfl⟩
    rw [Local.traceIdeal_eq E L (-D)] at himage
    simpa [D] using himage
  · intro h
    by_cases hx : x = 0
    · simp [hx]
    obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff L).2 hx)
    have htr : ∀ z : L, z ∈ lattice L (v - D - c) →
        trace E L z ∈ lattice E 0 := by
      intro z hz
      have hxinv : x⁻¹ ∈ lattice L (-v) := by
        rw [mem_lattice, ord_inv, ← hv]
        simp
      have htheta : x⁻¹ * z ∈ lattice L (-D - c) := by
        convert mul_mem_lattice L hxinv hz using 1
        congr 1
        ring
      have ht := h (x⁻¹ * z) htheta
      simpa [mul_assoc, mul_comm, mul_left_comm, hx] using ht
    have hle : lattice E ((v - c) / (ramificationIndex E L : ℤ)) ≤
        lattice E 0 := by
      intro y hy
      have hyimage : y ∈
          Submodule.map ((trace E L).restrictScalars (ringOfIntegers E))
            ((lattice L (v - D - c)).restrictScalars (ringOfIntegers E)) := by
        rw [Local.traceIdeal_eq E L]
        convert hy using 1
        congr 2
        dsimp only [D]
        ring
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hyimage
      exact htr z hz
    have hfloor := (lattice_le_lattice_iff E).mp hle
    have he : (0 : ℤ) < (ramificationIndex E L : ℤ) := by
      exact_mod_cast ramificationIndex_pos E L
    have hvge : c ≤ v := by
      have := (Int.le_ediv_iff_mul_le he).mp hfloor
      omega
    rw [mem_lattice, ← hv]
    exact WithTop.coe_le_coe.mpr hvge

private theorem natCast_mem_lattice_zero
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (n : ℕ) : (n : E) ∈ lattice E 0 := by
  rw [mem_lattice]
  exact (ord_nonneg_iff_mem_integer E _).2 (n : ringOfIntegers E).property

/-- A weighted version of the exact moments. The weight retains the
exceptional degree-`p` term and allows negative lattice depths. -/
theorem artinSchreier_moment_mem
    {E L : Type*} [Field E] [Field L] [Algebra E L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    (pb : PowerBasis E L) {p : ℕ} (hp : 2 < p) (hdim : pb.dim = p)
    (a : E) (hroot : pb.gen ^ p - pb.gen = algebraMap E L a)
    (t : ℤ) (ht : 0 ≤ t) (ha : a ∈ lattice E (-t))
    (k : ℕ) (hk : 1 ≤ k) (hkp : k ≤ 2 * p - 2) :
    Algebra.trace E L (pb.gen ^ k) ∈ lattice E (((p : ℤ) - 1 - k) * t) := by
  rw [artinSchreier_powerTraces pb hp hdim a hroot k hk hkp]
  apply (lattice E _).add_mem
  · apply (lattice E _).add_mem
    · split_ifs with h
      · have hc : ((p : ℤ) - 1 - k) * t = 0 := by
          have : (k : ℤ) = (p : ℤ) - 1 := by omega
          rw [this]; ring
        rw [hc]
        exact natCast_mem_lattice_zero E (p - 1)
      · exact (lattice E _).zero_mem
    · split_ifs with h
      · subst k
        convert mul_mem_lattice E (natCast_mem_lattice_zero E p) ha using 1
        congr 1
        ring
      · exact (lattice E _).zero_mem
  · split_ifs with h
    · apply lattice_antitone E _ (natCast_mem_lattice_zero E (p - 1))
      have hkpZ : (p : ℤ) - 1 ≤ (k : ℤ) := by omega
      exact mul_nonpos_of_nonpos_of_nonneg (by omega) ht
    · exact (lattice E _).zero_mem

/-- The inner trace in the crossed trace-duality argument. The hypotheses
are coefficient lower bounds, not crossed trace or symmetric conclusions. -/
theorem artinSchreier_weightedTrace_mem
    {E L : Type*} [Field E] [Field L] [Algebra E L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    (pb : PowerBasis E L) {p : ℕ} (hp : 2 < p) (hdim : pb.dim = p)
    (a : E) (hroot : pb.gen ^ p - pb.gen = algebraMap E L a)
    (t m q : ℤ) (ht : 0 ≤ t) (ha : a ∈ lattice E (-t))
    (Y : E) (hY : Y ∈ lattice E q)
    (Z : Fin p → E) (hZ : ∀ r : Fin p, Z r ∈ lattice E (m + (r : ℕ) * t))
    (hpval : (p : E) ∈ lattice E (((p : ℤ) - 1) * t))
    (i : ℕ) (hip : i < p) :
    Algebra.trace E L
      ((∑ r : Fin p, algebraMap E L (Z r) * pb.gen ^ (r : ℕ)) *
        (algebraMap E L Y * pb.gen ^ i)) ∈
      lattice E (m + q + ((p : ℤ) - 1 - i) * t) := by
  have heq :
      (∑ r : Fin p, algebraMap E L (Z r) * pb.gen ^ (r : ℕ)) *
        (algebraMap E L Y * pb.gen ^ i) =
      ∑ r : Fin p, (Z r * Y) • pb.gen ^ ((r : ℕ) + i) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Algebra.smul_def, map_mul, pow_add]
    ring
  rw [heq, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply sum_mem_lattice E
  intro r hr
  have hmom : Algebra.trace E L (pb.gen ^ ((r : ℕ) + i)) ∈
      lattice E (((p : ℤ) - 1 - ((r : ℕ) + i)) * t) := by
    by_cases hk : (r : ℕ) + i = 0
    · rw [hk, pow_zero, show (1 : L) = algebraMap E L 1 by simp,
        Algebra.trace_algebraMap_of_basis pb.basis]
      have hkZ : ((r : ℕ) : ℤ) + (i : ℤ) = 0 := by exact_mod_cast hk
      simpa [hdim, hkZ] using hpval
    · exact artinSchreier_moment_mem pb hp hdim a hroot t ht ha
        ((r : ℕ) + i) (by omega) (by omega)
  have hprod := mul_mem_lattice E (mul_mem_lattice E (hZ r) hY) hmom
  convert hprod using 1
  congr 1
  ring

/-- Crossed trace duality for two actual finite field towers. Coefficient
extraction supplies the only nonstandard input; the trace-dual lattice is
constructed from the genuine different ideal. -/
theorem crossedTrace_of_coefficientExtraction
    (A E₁ E₂ L : Type*) [Field A] [Field E₁] [Field E₂] [Field L]
    [ValuativeRel A] [TopologicalSpace A] [IsNonarchimedeanLocalField A]
    [ValuativeRel E₁] [TopologicalSpace E₁] [IsNonarchimedeanLocalField E₁]
    [ValuativeRel E₂] [TopologicalSpace E₂] [IsNonarchimedeanLocalField E₂]
    [Algebra A E₁] [Algebra A E₂] [Algebra A L]
    [Algebra E₁ L] [Algebra E₂ L]
    [IsScalarTower A E₁ L] [IsScalarTower A E₂ L]
    [ValuativeExtension A E₁] [ValuativeExtension A E₂]
    [Module.Free A E₁] [Module.Finite A E₁] [Algebra.IsSeparable A E₁]
    [Module.Free A E₂] [Module.Finite A E₂] [Algebra.IsSeparable A E₂]
    [Module.Free E₁ L] [Module.Finite E₁ L]
    [Module.Free E₂ L] [Module.Finite E₂ L]
    (pb : PowerBasis E₂ L) {p : ℕ} (hp : 2 < p) (hdim : pb.dim = p)
    (a : E₂) (hroot : pb.gen ^ p - pb.gen = algebraMap E₂ L a)
    (t t₂ : ℤ) (ht : 0 ≤ t) (ha : a ∈ lattice E₂ (-t))
    (hdiff₁ : Local.differentIdealExponent A E₁ = ((p : ℤ) - 1) * (t + 1))
    (hdiff₂ : Local.differentIdealExponent A E₂ = ((p : ℤ) - 1) * (t₂ + 1))
    (hpval : (p : E₂) ∈ lattice E₂ (((p : ℤ) - 1) * t))
    (hcoeff : ∀ theta : E₁, ∃ Z : Fin p → E₂,
      algebraMap E₁ L theta = ∑ r : Fin p, algebraMap E₂ L (Z r) * pb.gen ^ (r : ℕ) ∧
      ∀ r : Fin p, ord E₁ theta + (((r : ℕ) * t : ℤ) : WithTop ℤ) ≤ ord E₂ (Z r))
    (Y : E₂) (q : ℤ) (hY : Y ∈ lattice E₂ q)
    (i : ℕ) (hip : i < p) :
    trace E₁ L (algebraMap E₂ L Y * pb.gen ^ i) ∈
      lattice E₁ (((p : ℤ) - 1) * t₂ - (i : ℤ) * t + q) := by
  let c : ℤ := ((p : ℤ) - 1) * t₂ - (i : ℤ) * t + q
  apply (mem_lattice_iff_integral_tracePairing A E₁ _ c).2
  intro theta htheta
  obtain ⟨Z, hexp, hZ⟩ := hcoeff theta
  let m : ℤ := -Local.differentIdealExponent A E₁ - c
  have hZm : ∀ r : Fin p, Z r ∈ lattice E₂ (m + (r : ℕ) * t) := by
    intro r
    rw [mem_lattice, WithTop.coe_add]
    have hsum := add_le_add ((mem_lattice E₁).mp htheta)
      (le_refl ((((r : ℕ) * t : ℤ) : WithTop ℤ)))
    exact hsum.trans (hZ r)
  have hinner := artinSchreier_weightedTrace_mem pb hp hdim a hroot t m q ht ha
    Y hY Z hZm hpval i hip
  have hdepth : m + q + ((p : ℤ) - 1 - i) * t =
      -Local.differentIdealExponent A E₂ := by
    dsimp only [m, c]
    rw [hdiff₁, hdiff₂]
    ring
  rw [hdepth, ← hexp] at hinner
  have houter : trace A E₂
      (trace E₂ L (algebraMap E₁ L theta *
        (algebraMap E₂ L Y * pb.gen ^ i))) ∈ lattice A 0 := by
    have himage : trace A E₂
        (trace E₂ L (algebraMap E₁ L theta *
          (algebraMap E₂ L Y * pb.gen ^ i))) ∈
        Submodule.map ((trace A E₂).restrictScalars (ringOfIntegers A))
          ((lattice E₂ (-Local.differentIdealExponent A E₂)).restrictScalars
            (ringOfIntegers A)) :=
      Submodule.mem_map.mpr ⟨_, hinner, rfl⟩
    rw [Local.traceIdeal_eq A E₂] at himage
    simpa using himage
  have heq : trace A E₁ (theta * trace E₁ L (algebraMap E₂ L Y * pb.gen ^ i)) =
      trace A E₂ (trace E₂ L (algebraMap E₁ L theta *
        (algebraMap E₂ L Y * pb.gen ^ i))) := by
    have hlin : trace E₁ L (algebraMap E₁ L theta *
        (algebraMap E₂ L Y * pb.gen ^ i)) =
        theta * trace E₁ L (algebraMap E₂ L Y * pb.gen ^ i) := by
      simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self_apply] using
        (map_smul (trace E₁ L) theta (algebraMap E₂ L Y * pb.gen ^ i))
    rw [← hlin, Algebra.trace_trace, Algebra.trace_trace]
  rw [heq]
  exact houter

private theorem residueDegree_tower
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (L : IntermediateField F K) :
    letI := Basic.intermediateFieldValuativeRel L
    letI := Basic.intermediateFieldTopology L
    letI := Basic.intermediateField_localField L
    letI := Basic.intermediateField_lowerValuativeExtension L
    letI := Basic.intermediateField_upperValuativeExtension L
    residueDegree F L * residueDegree L K = residueDegree F K := by
  letI := Basic.intermediateFieldValuativeRel L
  letI := Basic.intermediateFieldTopology L
  letI := Basic.intermediateField_localField L
  letI := Basic.intermediateField_lowerValuativeExtension L
  letI := Basic.intermediateField_upperValuativeExtension L
  letI : IsScalarTower (ringOfIntegers F) (ringOfIntegers L) (ringOfIntegers K) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap F K (x : F) = algebraMap L K (algebraMap F L (x : F))
      rw [← IsScalarTower.algebraMap_apply F L K])
  letI : IsLocalHom (algebraMap (ringOfIntegers F) (ringOfIntegers L)) := inferInstance
  letI : IsLocalHom (algebraMap (ringOfIntegers L) (ringOfIntegers K)) := inferInstance
  rw [residueDegree_eq_finrank_residueField, residueDegree_eq_finrank_residueField,
    residueDegree_eq_finrank_residueField]
  exact Module.finrank_mul_finrank (ResidueField F) (ResidueField L) (ResidueField K)

/-- Passing from all integer lower bounds to an extended-valued bound also
covers zero inputs, whose valuation is infinity. -/
private theorem affine_bound_withTop
    (a b : WithTop ℤ) (C : ℤ) (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ q : ℤ, (q : WithTop ℤ) ≤ a →
      ((C + (n : ℤ) * q : ℤ) : WithTop ℤ) ≤ b) :
    (C : WithTop ℤ) + n • a ≤ b := by
  by_cases ha : a = ⊤
  · by_cases hb : b = ⊤
    · simp [hb]
    obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hb
    let q : ℤ := max 0 (v - C + 1)
    have hq0 : 0 ≤ q := le_max_left _ _
    have hqv : v - C + 1 ≤ q := le_max_right _ _
    have hbound := h q (by simp [ha])
    rw [← hv, WithTop.coe_le_coe] at hbound
    have hnZ : (1 : ℤ) ≤ n := by exact_mod_cast hn
    have := mul_le_mul_of_nonneg_right hnZ hq0
    omega
  · obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp ha
    have hb := h q (by rw [hq])
    rw [← hq, ← WithTop.coe_nsmul, ← WithTop.coe_add]
    simpa only [nsmul_eq_mul] using hb

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K]
variable [Module.Free F K] [Module.Finite F K] [IsGalois F K]

/-- Paper `O:A:lem:twisted`, for the actual coordinate constructed by
coefficient extraction. The trace assertion includes `i = 0`. Both bounds
use extended valuations and hence include `Y = 0`; all finite depths are
integers. The final two assertions are the paper's `eᵢ` and `s` bounds. -/
theorem twistedEstimates {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (D : OddTotalBreakData (F := F) (K := K) hp hG) :
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
        ord B₁ (-elementarySymmetric B₁ K (p - 1) Delta) := by
  dsimp only [OddTotalBreakData.B₁, OddTotalBreakData.B₂]
  let B₁ := IntermediateField.fixedField D.H₁
  let B₂ := IntermediateField.fixedField D.H₂
  letI := Basic.intermediateFieldValuativeRel B₁
  letI := Basic.intermediateFieldTopology B₁
  letI := Basic.intermediateFieldValuativeRel B₂
  letI := Basic.intermediateFieldTopology B₂
  obtain ⟨hLocal₁, hFreeF₁, hFiniteF₁, hFree₁K, hFinite₁K, hScalar₁,
      hValF₁, hVal₁K, _htotal₁, hdegreeLower₁, hdegreeUpper₁,
      hcycF₁, hcyc₁K⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁
  letI := hLocal₁
  letI := hFreeF₁
  letI := hFiniteF₁
  letI := hFree₁K
  letI := hFinite₁K
  letI := hScalar₁
  letI := hValF₁
  letI := hVal₁K
  letI : IsGalois F B₁ := hcycF₁.1
  letI : IsGalois B₁ K := hcyc₁K.1
  letI : PrimeCyclicExtension F B₁ :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F B₁ hcycF₁
  obtain ⟨hLocal₂, hFreeF₂, hFiniteF₂, hFree₂K, hFinite₂K, hScalar₂,
      hValF₂, hVal₂K, _htotal₂, hdegreeLower₂, hdegreeUpper₂,
      hcycF₂, hcyc₂K⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
  letI := hLocal₂
  letI := hFreeF₂
  letI := hFiniteF₂
  letI := hFree₂K
  letI := hFinite₂K
  letI := hScalar₂
  letI := hValF₂
  letI := hVal₂K
  letI : IsGalois F B₂ := hcycF₂.1
  letI : IsGalois B₂ K := hcyc₂K.1
  letI : PrimeCyclicExtension F B₂ :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F B₂ hcycF₂
  have hresmul₁ := residueDegree_tower B₁
  have hresmul₂ := residueDegree_tower B₂
  rw [hres] at hresmul₁ hresmul₂
  have hresF₁ : residueDegree F B₁ = 1 := (mul_eq_one.mp hresmul₁).1
  have hresF₂ : residueDegree F B₂ = 1 := (mul_eq_one.mp hresmul₂).1
  have hres₂K : residueDegree B₂ K = 1 := (mul_eq_one.mp hresmul₂).2
  have hram₂K : ramificationIndex B₂ K = p := by
    have hfund := finrank_eq_ramificationIndex_mul_residueDegree B₂ K
    rw [hres₂K, mul_one, hdegreeUpper₂] at hfund
    exact hfund.symm
  have hbreak₁ : PrimeCyclicExtension.IsLowerBreak F B₁ D.t := by
    simpa only [B₁, Ramification.IntermediateBreakPair] using D.B₁_breaks.1
  have hbreak₂ : PrimeCyclicExtension.IsLowerBreak F B₂ D.t₂ := by
    simpa only [B₂, Ramification.IntermediateBreakPair] using D.B₂_breaks.1
  have hdiff₁ : Local.differentIdealExponent F B₁ =
      ((p : ℤ) - 1) * ((D.t : ℤ) + 1) := by
    rw [Local.differentIdealExponent_eq_fml F B₁ hresF₁]
    obtain ⟨pi, hpi, hgen⟩ :=
      exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one F B₁ hresF₁
    rw [differentExponent_eq F B₁ hbreak₁ pi hpi hgen, hdegreeLower₁]
    push_cast [Nat.cast_sub hp.one_le]
    rfl
  have hdiff₂ : Local.differentIdealExponent F B₂ =
      ((p : ℤ) - 1) * ((D.t₂ : ℤ) + 1) := by
    rw [Local.differentIdealExponent_eq_fml F B₂ hresF₂]
    obtain ⟨pi, hpi, hgen⟩ :=
      exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one F B₂ hresF₂
    rw [differentExponent_eq F B₂ hbreak₂ pi hpi hgen, hdegreeLower₂]
    push_cast [Nat.cast_sub hp.one_le]
    rfl
  have hpval : (p : B₂) ∈ lattice B₂ (((p : ℤ) - 1) * D.t) := by
    by_cases hpzero : (p : B₂) = 0
    · simp [hpzero]
    obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff B₂).2 hpzero)
    have hbound := oddTotal_primeValuationBound hp hG hres D
    rw [show (p : K) = algebraMap B₂ K (p : B₂) by simp,
      ord_algebraMap, hram₂K, ← hv, ← WithTop.coe_nsmul, WithTop.coe_le_coe] at hbound
    simp only [nsmul_eq_mul] at hbound
    have htle : (D.t : ℤ) ≤ D.t₂ := by exact_mod_cast D.t_le_t₂
    have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
    push_cast [Nat.cast_sub hp.one_le] at hbound
    rw [mem_lattice, ← hv, WithTop.coe_le_coe]
    have ht₂bound : ((p : ℤ) - 1) * D.t₂ ≤ v :=
      le_of_mul_le_mul_left (by simpa only [mul_assoc] using hbound) hpZ
    exact (mul_le_mul_of_nonneg_left htle (by omega)).trans ht₂bound
  have hdata := coefficientExtraction hp hG hres hchar D
  dsimp only [OddTotalBreakData.B₁, OddTotalBreakData.B₂] at hdata
  obtain ⟨Delta, a, hroot, hDelta, ha, hprime, hgen, hcoeff⟩ := hdata
  let pb : PowerBasis B₂ K :=
    PowerBasis.ofAdjoinEqTop (IsAlgebraic.of_finite B₂ Delta).isIntegral hgen
  have hpbgen : pb.gen = Delta := PowerBasis.ofAdjoinEqTop_gen _ _
  have hpbdim : pb.dim = p := by rw [← pb.finrank]; exact hdegreeUpper₂
  have hexp : ∀ theta : B₁, ∃ Z : Fin p → B₂,
      algebraMap B₁ K theta = ∑ r : Fin p, algebraMap B₂ K (Z r) * pb.gen ^ (r : ℕ) ∧
      ∀ r : Fin p, ord B₁ theta + (((r : ℕ) * (D.t : ℤ) : ℤ) : WithTop ℤ) ≤ ord B₂ (Z r) := by
    intro theta
    let Z : Fin p → B₂ := fun r => pb.basis.repr (algebraMap B₁ K theta) (Fin.cast hpbdim.symm r)
    have hzexp : algebraMap B₁ K theta =
        ∑ r : Fin p, algebraMap B₂ K (Z r) * pb.gen ^ (r : ℕ) := by
      let e : Fin p ≃ Fin pb.dim := (Fin.castOrderIso hpbdim.symm).toEquiv
      have hs := pb.basis.sum_repr (algebraMap B₁ K theta)
      rw [← e.sum_comp] at hs
      refine hs.symm.trans ?_
      apply Finset.sum_congr rfl
      intro r hr
      rw [pb.basis_eq_pow, Algebra.smul_def]
      rfl
    refine ⟨Z, hzexp, ?_⟩
    intro r
    have hz := hcoeff theta Z (by simpa [hpbgen] using hzexp) r
    simpa only [Nat.cast_mul] using hz
  have htr : ∀ (Y : B₂) (q : ℤ), Y ∈ lattice B₂ q → ∀ i : ℕ, i < p →
      trace B₁ K (algebraMap B₂ K Y * Delta ^ i) ∈
        lattice B₁ (((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t + q) := by
    intro Y q hY i hi
    have h := crossedTrace_of_coefficientExtraction F B₁ B₂ K pb D.odd_prime hpbdim
      a (by simpa [hpbgen] using hroot) D.t D.t₂ (by positivity)
      (by rw [mem_lattice, ha]) hdiff₁ hdiff₂ hpval hexp Y q hY i hi
    simpa only [hpbgen] using h
  have hC : 0 ≤ ((p : ℤ) - 1) * D.t₂ := by
    exact mul_nonneg (by have := hp.one_lt; omega) (Int.natCast_nonneg _)
  have hchar₁ : residueCharacteristic B₁ = p :=
    (residueCharacteristic_extension_eq F B₁).trans hchar
  have hsym : ∀ (Y : B₂) (q : ℤ), Y ∈ lattice B₂ q → ∀ i : ℕ, 1 ≤ i → i < p →
      ((((p : ℤ) - 1) * D.t₂ + (i : ℤ) * (q - D.t) : ℤ) : WithTop ℤ) ≤
        ord B₁ (elementarySymmetric B₁ K i (algebraMap B₂ K Y * Delta)) := by
    intro Y q hY i hi hip
    apply twistedSymmetric_of_powerTrace B₁ K _ _ _ hC _ i hi (by simpa [hchar₁] using hip)
    intro j hj hjp
    have hpow : Y ^ j ∈ lattice B₂ ((j : ℤ) * q) := by
      rw [mem_lattice, ord_pow]
      rw [mem_lattice] at hY
      simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using nsmul_le_nsmul_right hY j
    have h := htr (Y ^ j) ((j : ℤ) * q) hpow j (by simpa [hchar₁] using hjp)
    rw [mem_lattice] at h
    convert h using 1
    · congr 1; ring
    · rw [mul_pow, ← map_pow]
  have hsymOrd : ∀ (Y : B₂) (i : ℕ), 1 ≤ i → i < p →
      ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) + i • ord B₂ Y ≤
        ord B₁ (elementarySymmetric B₁ K i (algebraMap B₂ K Y * Delta)) := by
    intro Y i hi hip
    apply affine_bound_withTop _ _ _ i hi
    intro q hq
    convert hsym Y q hq i hi hip using 1
    congr 1
    ring
  have hei : ∀ i : ℕ, 1 ≤ i → i < p →
      ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) ≤
        ord B₁ (elementarySymmetric B₁ K i Delta) := by
    intro i hi hip
    simpa using hsymOrd 1 i hi hip
  refine ⟨Delta, a, hroot, hDelta, ha, hprime, hgen, hcoeff, ?_, hsymOrd, hei, ?_⟩
  · intro Y i hip
    simpa only [one_nsmul] using affine_bound_withTop (ord B₂ Y)
      (ord B₁ (trace B₁ K (algebraMap B₂ K Y * Delta ^ i)))
      (((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t) 1 (by omega)
      (by intro q hq; simpa using htr Y q hq i hip)
  · have h := hei (p - 1) (by have := hp.one_lt; omega) (by have := hp.pos; omega)
    rw [ord_neg]
    convert h using 1
    congr 1
    rw [D.t₂_eq, Nat.cast_add, Nat.cast_sub hp.one_le]
    ring

end

end LanglandsSecondMainLemma.Odd.Total
