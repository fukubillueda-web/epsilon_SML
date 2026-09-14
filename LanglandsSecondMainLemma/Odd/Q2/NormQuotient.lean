import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Odd.Parameters.FourFactors
import LanglandsSecondMainLemma.Odd.NormLog

/-!
# Odd / Q2 / Norm Quotient

Blueprint: blueprint/tasks/Odd/Q2/NormQuotient.md
Paper: Lemma 9.14 (`O:N:normquot`), corrected source lines 4044--4097.

The intermediate symmetric coefficients and positive power traces have the
common depth `b = (a + D) / p`. Newton's identity identifies their signed
sum modulo depth `2b`. Only the quotient is evaluated by the character's
full truncated-logarithm formula. Its denominator is retained throughout.
-/

namespace LanglandsSecondMainLemma.Odd.Q2

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

section Units

variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E]
  [Module.Finite F E]

private theorem ord_one_sub_of_pos {z : F} (hz : 0 < ord F z) :
    ord F (1 - z) = 0 := by
  simpa using (ord F).map_sub_eq_of_lt_left (x := 1) (y := z) (by simpa using hz)

private def oneSubUnit (z : F) (hz : 0 < ord F z) : Fˣ :=
  Units.mk0 (1 - z) (by
    intro h
    have ho := ord_one_sub_of_pos F hz
    simp [h] at ho)

/-- The actual norm quotient, as a unit of the base field. Positivity of
`a` proves that both `1-k` and `1-N(k)` are nonzero; no norm representative
or character value is part of this construction. -/
def normQuotientUnit (hres : residueDegree F E = 1)
    {a : ℤ} (ha : 1 ≤ a) (k : E) (hk : k ∈ lattice E a) : Fˣ :=
  normUnits F E (oneSubUnit E k (by
    have hpos : (0 : WithTop ℤ) < (a : WithTop ℤ) :=
      WithTop.coe_lt_coe.mpr (by omega)
    exact hpos.trans_le ((mem_lattice E).1 hk))) /
  oneSubUnit F (norm F E k) (by
    rw [ord_norm, hres, one_nsmul]
    exact (WithTop.coe_lt_coe.mpr (by omega : (0 : ℤ) < a)).trans_le
      ((mem_lattice E).1 hk))

@[simp] theorem coe_normQuotientUnit (hres : residueDegree F E = 1)
    {a : ℤ} (ha : 1 ≤ a) (k : E) (hk : k ∈ lattice E a) :
    (normQuotientUnit F E hres ha k hk : F) =
      norm F E (1 - k) / (1 - norm F E k) := by
  simp [normQuotientUnit, oneSubUnit, normUnits, LanglandsFirstMainLemma.norm]

end Units

section Newton

variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra F E] [Module.Free F E] [Module.Finite F E] [IsGalois F E]

/-- Newton's identity modulo the product of the two common-depth ideals.
Only the integers strictly below the residue characteristic are divided by. -/
private theorem signed_symmetric_add_powerTrace_mem
    {p j : ℕ} (hchar : residueCharacteristic F = p)
    (hj : 1 ≤ j) (hjp : j < p) (k : E) (b : ℤ)
    (hs : ∀ i, 1 ≤ i → i < p → elementarySymmetric F E i k ∈ lattice F b)
    (hq : ∀ i, 1 ≤ i → i < p → galoisPowerSum F E i k ∈ lattice F b) :
    (-1 : F) ^ j * elementarySymmetric F E j k +
      galoisPowerSum F E j k / (j : F) ∈ lattice F (2 * b) := by
  classical
  let S := (Finset.HasAntidiagonal.antidiagonal j).filter (fun ij : ℕ × ℕ ↦ ij.1 < j)
  let f : ℕ × ℕ → F := fun ij ↦
    (-1 : F) ^ ij.1 * elementarySymmetric F E ij.1 k * galoisPowerSum F E ij.2 k
  have hzero : (0, j) ∈ S := by simp [S]; omega
  have hfzero : f (0, j) = galoisPowerSum F E j k := by
    simp [f, elementarySymmetric_zero]
  let R : F := ∑ ij ∈ S.erase (0, j), f ij
  have hR : R ∈ lattice F (2 * b) := by
    apply sum_mem_lattice F
    intro ij hij
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hij
    obtain ⟨hadd, hlt⟩ := Finset.mem_filter.mp hmem
    have hadd' : ij.1 + ij.2 = j := by simpa using hadd
    have hi : 1 ≤ ij.1 := by
      by_contra hi
      have h0 : ij.1 = 0 := by omega
      apply hne
      exact Prod.ext h0 (by omega)
    have hterm := mul_mem_lattice F (hs ij.1 hi (by omega))
      (hq ij.2 (by omega) (by omega))
    rw [mem_lattice] at hterm ⊢
    simpa [f, mul_assoc, two_mul] using hterm
  have hsum : (∑ ij ∈ S, f ij) = galoisPowerSum F E j k + R := by
    rw [← Finset.sum_erase_add S f hzero, hfzero]
    exact add_comm _ _
  have hnewton := elementarySymmetric_newton_identity F E k j
  change (j : F) * elementarySymmetric F E j k =
    (-1 : F) ^ (j + 1) * (∑ ij ∈ S, f ij) at hnewton
  rw [hsum] at hnewton
  have hjord : ord F (j : F) = 0 :=
    ord_natCast_eq_zero_of_lt_residueCharacteristic F hj (by simpa [hchar] using hjp)
  have hjzero : (j : F) ≠ 0 := by intro hz; simp [hz] at hjord
  have hsign : (-1 : F) ^ j * (-1 : F) ^ (j + 1) = -1 := by
    rw [pow_succ]
    calc
      (-1 : F) ^ j * ((-1 : F) ^ j * -1) = ((-1 : F) * -1) ^ j * -1 := by
        rw [mul_pow]; ring
      _ = -1 := by simp
  have heq : (-1 : F) ^ j * elementarySymmetric F E j k +
      galoisPowerSum F E j k / (j : F) = -R / (j : F) := by
    apply (eq_div_iff hjzero).2
    calc
      ((-1 : F) ^ j * elementarySymmetric F E j k +
          galoisPowerSum F E j k / (j : F)) * (j : F) =
          (-1 : F) ^ j * ((j : F) * elementarySymmetric F E j k) +
            galoisPowerSum F E j k := by field_simp
      _ = -R := by rw [hnewton, ← mul_assoc, hsign]; ring
  rw [heq, div_mem_lattice_iff F _ _ 0 _ hjord, zero_add]
  exact neg_mem_lattice F hR

private theorem norm_one_sub_expansion {p : ℕ}
    (hdegree : Module.finrank F E = p) (hp : Odd p) (k : E) :
    norm F E (1 - k) = 1 - norm F E k +
      ∑ j ∈ Finset.Ico 1 p, (-1 : F) ^ j * elementarySymmetric F E j k := by
  have hp0 : 1 ≤ p := hp.pos
  have hneg (j : ℕ) : elementarySymmetric F E j (-k) =
      (-1 : F) ^ j * elementarySymmetric F E j k := by
    simpa using elementarySymmetric_algebraMap_mul F E (-1) k j
  have hn := norm_one_add_eq_sum_elementarySymmetric F E (-k)
  simp only [← sub_eq_add_neg, hdegree, hneg] at hn
  rw [Finset.sum_range_succ, hp.neg_one_pow,
    show elementarySymmetric F E p k = norm F E k by
      rw [← hdegree, elementarySymmetric_finrank]] at hn
  rw [Finset.sum_Ico_eq_sub _ hp0]
  simp only [Finset.sum_range_one, pow_zero, elementarySymmetric_zero, mul_one]
  rw [hn]
  ring

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsGalois F E] in
private theorem trace_truncatedLog {p : ℕ} (hp : 1 < p) (k : E) :
    trace F E (truncatedLog p k) =
      ∑ j ∈ Finset.Ico 1 p, galoisPowerSum F E j k / (j : F) := by
  rw [Finset.sum_eq_sum_Ico_succ_bot hp, truncatedLog_apply, map_add, map_sum]
  simp only [galoisPowerSum, pow_one, Nat.cast_one, div_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  calc
    trace F E (k ^ j / (j : E)) =
        trace F E (((j : F)⁻¹) • k ^ j) := by
      congr 1
      simp [Algebra.smul_def, div_eq_mul_inv, mul_comm]
    _ = trace F E (k ^ j) / (j : F) := by
      rw [map_smul]
      simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

end Newton

open private truncatedLog_sub_linear_mem from
  LanglandsSecondMainLemma.Odd.EnhancedStationary
open private lamprechtAddChar_eq_of_sub_mem from
  LanglandsFirstMainLemma.Lamprecht.Formula

section Character

variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E]
  [Module.Free F E] [Module.Finite F E] [PrimeCyclicExtension F E]

/-- **Paper Lemma 9.14 (`O:N:normquot`).**

For an actual totally ramified cyclic extension of odd prime degree, the
full coefficient of a continuous quasi-character evaluates the actual
norm quotient whenever `2 * floor ((a + D) / p)` reaches its conductor.
The integer `D = (p-1)(t+1)` comes from the positive lower break. Neither
of the two shallow factors is evaluated separately. Both equal and mixed
characteristic, including degree three, are covered.
-/
theorem normQuotient
    {p t : ℕ} (hdegree : Module.finrank F E = p) (hodd : 2 < p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
    (hres : residueDegree F E = 1)
    (lambda : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (hn : 2 ≤ lambda.conductor) (gamma : Fˣ)
    (hgamma : ord F (gamma : F) =
      ((-psi.conductor - (lambda.conductor : ℤ) : ℤ) : WithTop ℤ))
    (hformula : ∀ u : unitFiltration F (lambda.conductor ⌈/⌉ p),
      lambda.character u = psi.character
        ((gamma : F) * truncatedLog p (1 - ((u : Fˣ) : F))))
    {a : ℤ} (ha : 1 ≤ a) (k : E) (hk : k ∈ lattice E a)
    (hdepth : (lambda.conductor : ℤ) ≤
      2 * ((a + ((p : ℤ) - 1) * ((t : ℤ) + 1)) / (p : ℤ))) :
    lambda.character (normQuotientUnit F E hres ha k hk) =
      tracePullbackAddChar F E psi.character
        (algebraMap F E ((gamma : F) / (1 - norm F E k)) * truncatedLog p k) := by
  classical
  let D : ℤ := ((p : ℤ) - 1) * ((t : ℤ) + 1)
  let b : ℤ := (a + D) / (p : ℤ)
  let s : F := ∑ j ∈ Finset.Ico 1 p, (-1 : F) ^ j * elementarySymmetric F E j k
  let den : F := 1 - norm F E k
  let Q : F := s / den
  let u := normQuotientUnit F E hres ha k hk
  have hp : p.Prime := hdegree ▸ PrimeCyclicExtension.degree_prime F E
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have hchar : residueCharacteristic F = p :=
    (residueCharacteristic_eq_degree_of_positive_isLowerBreak F E ht htpos
      pi hpi hgen).trans hdegree
  have htrace : TraceIdealLowerBound F E p D := by
    have h := traceIdealLowerBound_of_integralGenerator F E ht hres pi hpi hgen
    simpa only [hdegree, Nat.cast_mul, Nat.cast_sub hp.one_le,
      Nat.cast_add, Nat.cast_one, D] using h
  have hbound (j : ℕ) (hj : 1 ≤ j) :
      b ≤ ((j : ℤ) * a + D) / (p : ℤ) := by
    apply Int.ediv_le_ediv (by exact_mod_cast hp.pos)
    have hjZ : (1 : ℤ) ≤ j := by exact_mod_cast hj
    nlinarith
  have hs (j : ℕ) (hj : 1 ≤ j) (hjp : j < p) :
      elementarySymmetric F E j k ∈ lattice F b := by
    have h := wild_elementarySymmetric_bound F E p (t + 1) a hp (by omega)
      hchar hdegree (by
        simpa only [Nat.cast_mul, Nat.cast_sub hp.one_le,
          Nat.cast_add, Nat.cast_one, D] using htrace)
      ((mem_lattice E).1 hk) hj hjp
    apply (mem_lattice F).2
    exact (WithTop.coe_le_coe.mpr (hbound j hj)).trans (by
      simpa only [Nat.cast_mul, Nat.cast_sub hp.one_le,
        Nat.cast_add, Nat.cast_one, D] using h)
  have hq (j : ℕ) (hj : 1 ≤ j) (_hjp : j < p) :
      galoisPowerSum F E j k ∈ lattice F b := by
    exact (mem_lattice F).2 ((WithTop.coe_le_coe.mpr (hbound j hj)).trans
      (powerSum_bound F E p D a hp.pos hdegree htrace ((mem_lattice E).1 hk) j hj))
  have hsMem : s ∈ lattice F b := by
    apply sum_mem_lattice F
    intro j hj
    rw [mem_lattice]
    simpa using (mem_lattice F).1 (hs j (Finset.mem_Ico.mp hj).1
      (Finset.mem_Ico.mp hj).2)
  have hkpos : 0 < ord E k :=
    (WithTop.coe_lt_coe.mpr (by omega : (0 : ℤ) < a)).trans_le ((mem_lattice E).1 hk)
  have hden : ord F den = 0 := by
    apply ord_one_sub_of_pos F
    simpa only [ord_norm, hres, one_nsmul] using hkpos
  have hden0 : den ≠ 0 := by intro hz; simp [hz] at hden
  have hQ : Q ∈ lattice F b := by
    exact (div_mem_lattice_iff F den s 0 b hden).2 (by simpa using hsMem)
  have hu : (u : F) = 1 + Q := by
    rw [coe_normQuotientUnit,
      norm_one_sub_expansion F E hdegree (hp.odd_of_ne_two (by omega))]
    change (den + s) / den = 1 + s / den
    rw [add_div, div_self hden0]
  have hnewton : s + trace F E (truncatedLog p k) ∈ lattice F (2 * b) := by
    rw [trace_truncatedLog F E (by omega : 1 < p) k]
    change (∑ j ∈ Finset.Ico 1 p, (-1 : F) ^ j * elementarySymmetric F E j k) +
      (∑ j ∈ Finset.Ico 1 p, galoisPowerSum F E j k / (j : F)) ∈ _
    rw [← Finset.sum_add_distrib]
    exact sum_mem_lattice F (fun j hj ↦ signed_symmetric_add_powerTrace_mem F E
      hchar (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2 k b hs hq)
  have hquotient : -Q - trace F E (truncatedLog p k) / den ∈ lattice F (2 * b) := by
    have heq : -Q - trace F E (truncatedLog p k) / den =
        -(s + trace F E (truncatedLog p k)) / den := by dsimp only [Q]; ring
    rw [heq, div_mem_lattice_iff F den _ 0 _ hden, zero_add]
    exact neg_mem_lattice F hnewton
  change (lambda.conductor : ℤ) ≤ 2 * b at hdepth
  have hbpos : 0 < b := by omega
  let r : ℕ := b.toNat
  have hr : (r : ℤ) = b := Int.toNat_of_nonneg hbpos.le
  have hrpos : 0 < r := by exact_mod_cast (hr.symm ▸ hbpos)
  have hnr : lambda.conductor ≤ 2 * r := by
    exact_mod_cast (show (lambda.conductor : ℤ) ≤ 2 * (r : ℤ) by simpa [hr] using hdepth)
  have hceil : lambda.conductor ⌈/⌉ p ≤ r := by
    apply (ceilDiv_le_iff_le_mul hp.pos).2
    exact hnr.trans (Nat.mul_le_mul_right r (by omega))
  have hur : u ∈ unitFiltration F r := by
    have hsucc : r = (r - 1) + 1 := by omega
    rw [hsucc, mem_unitFiltration_succ_iff_sub_mem_lattice, ← hsucc]
    simpa only [hu, add_sub_cancel_left, hr] using hQ
  let uc : unitFiltration F (lambda.conductor ⌈/⌉ p) :=
    ⟨u, unitFiltration_antitone F hceil hur⟩
  have hlinear : truncatedLog p (-Q) - -Q ∈ lattice F (2 * b) := by
    have h := truncatedLog_sub_linear_mem F p r hchar
      (show -Q ∈ lattice F (r : ℤ) by rw [hr]; exact neg_mem_lattice F hQ)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, hr] using h
  have herr : truncatedLog p (-Q) - trace F E (truncatedLog p k) / den ∈
      lattice F (lambda.conductor : ℤ) := by
    apply lattice_antitone F hdepth
    convert add_mem_lattice F hlinear hquotient using 1
    ring
  have hphase : psi.character ((gamma : F) * truncatedLog p (-Q)) =
      psi.character ((gamma : F) * (trace F E (truncatedLog p k) / den)) := by
    apply lamprechtAddChar_eq_of_sub_mem F psi
    have h := mul_mem_lattice F ((mem_lattice F).2 hgamma.ge) herr
    simpa only [sub_add_cancel, mul_sub] using h
  calc
    lambda.character u = psi.character ((gamma : F) * truncatedLog p (-Q)) := by
      have h := hformula uc
      simpa only [uc, hu, show (1 : F) - (1 + Q) = -Q by ring] using h
    _ = psi.character ((gamma : F) * (trace F E (truncatedLog p k) / den)) := hphase
    _ = tracePullbackAddChar F E psi.character
        (algebraMap F E ((gamma : F) / den) * truncatedLog p k) := by
      rw [tracePullbackAddChar_apply, ← Algebra.smul_def, map_smul]
      congr 1
      change (gamma : F) * (trace F E (truncatedLog p k) / den) =
        ((gamma : F) / den) * trace F E (truncatedLog p k)
      ring

end Character

end

end LanglandsSecondMainLemma.Odd.Q2
