import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Parameters.FourFactors
import LanglandsSecondMainLemma.Odd.Total.TraceNorm
import LanglandsSecondMainLemma.Odd.Total.PowerNorm

/-!
# Odd / R1 / Semilinear Trace

Blueprint: blueprint/tasks/Odd/R1/SemilinearTrace.md
Paper: Lemma 9.18 (`O:E:trace`), including `O:E:edifference`.

The characteristic-polynomial comparison keeps the actual factor `Y` in
the upper field. Newton's identity supplies the signed trace, with the
prime multiple controlled by the proved prime valuation bound. All ideal
depths are integers and all orders take values in `WithTop ℤ`.
-/

namespace LanglandsSecondMainLemma.Odd.R1

open LanglandsFirstMainLemma
open LanglandsSecondMainLemma.Odd.Total
open scoped BigOperators

noncomputable section

/-- The nonlinear part of Newton's identity at an even positive degree.
Each remaining term is a product of one positive symmetric coefficient
and one positive power trace, so it receives the common gain twice. -/
theorem newton_trace_remainder_mem
    (E K : Type*) [Field E] [Field K]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra E K] [Module.Free E K] [Module.Finite E K] [IsGalois E K]
    (x : K) (C q : ℤ) {n : ℕ} (hn : 0 < n) (heven : Even n)
    (hsym : ∀ i : ℕ, 1 ≤ i → i < n →
      elementarySymmetric E K i x ∈ lattice E (C + (i : ℤ) * q))
    (htrace : ∀ i : ℕ, 1 ≤ i → i < n →
      trace E K (x ^ i) ∈ lattice E (C + (i : ℤ) * q)) :
    trace E K (x ^ n) + (n : E) * elementarySymmetric E K n x ∈
      lattice E (2 * C + (n : ℤ) * q) := by
  classical
  let S := (Finset.HasAntidiagonal.antidiagonal n).filter (fun b => b.1 < n)
  let f (b : ℕ × ℕ) : E := (-1 : E) ^ b.1 *
    elementarySymmetric E K b.1 x * galoisPowerSum E K b.2 x
  have hzero : (0, n) ∈ S := by simp [S, hn]
  have hrem : (∑ b ∈ S.erase (0, n), f b) ∈
      lattice E (2 * C + (n : ℤ) * q) := by
    apply sum_mem_lattice E
    intro b hb
    have hbne := (Finset.mem_erase.mp hb).1
    have hbS := (Finset.mem_erase.mp hb).2
    have hbadd : b.1 + b.2 = n := by
      simpa using (Finset.mem_filter.mp hbS).1
    have hblt : b.1 < n := (Finset.mem_filter.mp hbS).2
    have hbpos : 1 ≤ b.1 := by
      by_contra h
      have hb0 : b.1 = 0 := by omega
      apply hbne
      exact Prod.ext hb0 (by omega)
    have hb2pos : 1 ≤ b.2 := by omega
    have hb2lt : b.2 < n := by omega
    have hprod := mul_mem_lattice E (hsym b.1 hbpos hblt)
      (htrace b.2 hb2pos hb2lt)
    have hbcast : (b.1 : ℤ) + (b.2 : ℤ) = (n : ℤ) := by exact_mod_cast hbadd
    have hdepth : (C + (b.1 : ℤ) * q) + (C + (b.2 : ℤ) * q) =
        2 * C + (n : ℤ) * q := by rw [← hbcast]; ring
    rw [hdepth] at hprod
    simpa only [f, mem_lattice, ord_mul, ord_pow, ord_neg, ord_one,
      nsmul_zero, zero_add, galoisPowerSum] using hprod
  have hnewton := elementarySymmetric_newton_identity E K x n
  have hsign : (-1 : E) ^ (n + 1) = -1 := by
    rw [pow_succ, heven.neg_one_pow, one_mul]
  change (n : E) * elementarySymmetric E K n x =
    (-1 : E) ^ (n + 1) * ∑ b ∈ S, f b at hnewton
  rw [hsign, ← Finset.sum_erase_add S f hzero] at hnewton
  have hfzero : f (0, n) = trace E K (x ^ n) := by
    simp [f, galoisPowerSum]
  rw [hfzero] at hnewton
  have heq : trace E K (x ^ n) + (n : E) * elementarySymmetric E K n x =
      -(∑ b ∈ S.erase (0, n), f b) := by linear_combination hnewton
  rw [heq]
  exact (lattice E _).neg_mem hrem

/-- Subtract the two actual characteristic polynomials. The norm of `Y`
is retained, so this identity does not assert multiplicative homogeneity
for the symmetric coefficients over the wrong lower field. -/
theorem semilinear_characteristic_identity
    (E K : Type*) [Field E] [Field K] [Algebra E K]
    [Module.Free E K] [Module.Finite E K]
    {p : ℕ} (hp : Odd p) (hdegree : Module.finrank E K = p) (Y Delta : K) :
    (∑ i ∈ Finset.Icc 1 (p - 1), (-1 : K) ^ i *
      (algebraMap E K (elementarySymmetric E K i (Y * Delta)) -
        Y ^ i * algebraMap E K (elementarySymmetric E K i Delta)) *
      (Y * Delta) ^ (p - i)) =
      algebraMap E K (norm E K Delta) *
        (algebraMap E K (norm E K Y) - Y ^ p) := by
  have hz := odd_norm_expansion E K hp hdegree (Y * Delta)
  have hd := odd_norm_expansion E K hp hdegree Delta
  have hterm (i : ℕ) (hi : i ∈ Finset.Icc 1 (p - 1)) :
      (-1 : K) ^ i *
        (algebraMap E K (elementarySymmetric E K i (Y * Delta)) -
          Y ^ i * algebraMap E K (elementarySymmetric E K i Delta)) *
        (Y * Delta) ^ (p - i) =
      (-1 : K) ^ i * algebraMap E K (elementarySymmetric E K i (Y * Delta)) *
        (Y * Delta) ^ (p - i) - Y ^ p *
      ((-1 : K) ^ i * algebraMap E K (elementarySymmetric E K i Delta) *
        Delta ^ (p - i)) := by
    have hip : i ≤ p := (Finset.mem_Icc.mp hi).2.trans (Nat.sub_le _ _)
    have hpow : Y ^ i * Y ^ (p - i) = Y ^ p := by
      rw [← pow_add, Nat.add_sub_of_le hip]
    rw [mul_pow]
    linear_combination -(-1 : K) ^ i *
      algebraMap E K (elementarySymmetric E K i Delta) * Delta ^ (p - i) * hpow
  simp_rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [map_mul, map_mul, mul_pow] at hz
  linear_combination -hz + Y ^ p * hd

/-- The coefficient comparison `O:E:edifference`, before substituting the
diamond's proved twisted bounds and its lower norm--power estimate.
The displayed norm hypotheses are estimates for actual field norms. -/
theorem semilinear_symmetric_mem
    (E K : Type*) [Field E] [Field K] [Algebra E K]
    [Module.Free E K] [Module.Finite E K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {p : ℕ} (hp : Odd p) (hp2 : 2 < p) (hdegree : Module.finrank E K = p)
    (Y Delta : K) (C M t : ℤ) (ht : 0 ≤ t)
    (hY : ord K Y = (M : WithTop ℤ))
    (hDelta : ord K Delta = ((-t : ℤ) : WithTop ℤ))
    (hcoeff : ∀ i : ℕ, 1 ≤ i → i < p →
      algebraMap E K (elementarySymmetric E K i Delta) ∈
        lattice K (C - (p : ℤ) * i * t))
    (htwisted : ∀ i : ℕ, 1 ≤ i → i < p →
      algebraMap E K (elementarySymmetric E K i (Y * Delta)) ∈
        lattice K (C + (i : ℤ) * (M - p * t)))
    (hNormDelta : algebraMap E K (norm E K Delta) ∈ lattice K (-(p : ℤ) * t))
    (hNormY : algebraMap E K (norm E K Y) - Y ^ p ∈
      lattice K ((p : ℤ) * M + C)) :
    algebraMap E K (elementarySymmetric E K (p - 1) (Y * Delta)) -
      Y ^ (p - 1) * algebraMap E K (elementarySymmetric E K (p - 1) Delta) ∈
      lattice K (((p : ℤ) - 1) * M + C - ((p : ℤ) - 1) ^ 2 * t) := by
  classical
  let z := Y * Delta
  let B₀ := ((p : ℤ) - 1) * M + C - ((p : ℤ) - 1) ^ 2 * t
  let d (i : ℕ) := algebraMap E K (elementarySymmetric E K i z) -
    Y ^ i * algebraMap E K (elementarySymmetric E K i Delta)
  let f (i : ℕ) := (-1 : K) ^ i * d i * z ^ (p - i)
  let S := Finset.Icc 1 (p - 1)
  have hz : ord K z = ((M - t : ℤ) : WithTop ℤ) := by
    rw [ord_mul, hY, hDelta, ← WithTop.coe_add]
    rfl
  have hdpow (i : ℕ) : Y ^ i ∈ lattice K ((i : ℤ) * M) := by
    rw [mem_lattice, ord_pow, hY, ← WithTop.coe_nsmul]
    rfl
  have hd (i : ℕ) (hi : 1 ≤ i) (hip : i < p) :
      d i ∈ lattice K (C + (i : ℤ) * (M - p * t)) := by
    apply (lattice K _).sub_mem (htwisted i hi hip)
    have h := mul_mem_lattice K (hdpow i) (hcoeff i hi hip)
    convert h using 1
    congr 1
    ring
  have hsmall : (∑ i ∈ S.erase (p - 1), f i) ∈ lattice K (M - t + B₀) := by
    apply sum_mem_lattice K
    intro i hi
    have hiS : i ∈ S := (Finset.mem_erase.mp hi).2
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hiS).1
    have hilast : i ≠ p - 1 := (Finset.mem_erase.mp hi).1
    have hip : i ≤ p - 2 := by
      have := (Finset.mem_Icc.mp hiS).2
      omega
    have hzpow : z ^ (p - i) ∈ lattice K (((p - i : ℕ) : ℤ) * (M - t)) := by
      rw [mem_lattice, ord_pow, hz, ← WithTop.coe_nsmul]
      rfl
    have hprod := mul_mem_lattice K (hd i hi1 (by omega)) hzpow
    have hdepth : M - t + B₀ ≤
        (C + (i : ℤ) * (M - p * t)) + (((p - i : ℕ) : ℤ) * (M - t)) := by
      have hcast : ((p - i : ℕ) : ℤ) = (p : ℤ) - i := by omega
      have hnonneg : 0 ≤ ((p : ℤ) - 1) * ((p : ℤ) - 2 - i) * t :=
        mul_nonneg (mul_nonneg (by omega) (by omega)) ht
      rw [hcast]
      dsimp only [B₀]
      nlinarith
    have hprod' := lattice_antitone K hdepth hprod
    simpa only [f, mem_lattice, ord_mul, ord_pow, ord_neg, ord_one,
      nsmul_zero, zero_add] using hprod'
  have hnorm : algebraMap E K (norm E K Delta) *
      (algebraMap E K (norm E K Y) - Y ^ p) ∈ lattice K (M - t + B₀) := by
    apply lattice_antitone K _ (mul_mem_lattice K hNormDelta hNormY)
    have hnonneg : 0 ≤ ((p : ℤ) - 1) * ((p : ℤ) - 2) * t :=
      mul_nonneg (mul_nonneg (by omega) (by omega)) ht
    dsimp only [B₀]
    nlinarith
  have hlast : p - 1 ∈ S := by simp [S]; omega
  have hpoly := semilinear_characteristic_identity E K hp hdegree Y Delta
  change (∑ i ∈ S, f i) = _ at hpoly
  rw [← Finset.sum_erase_add S f hlast] at hpoly
  have hlastMem : f (p - 1) ∈ lattice K (M - t + B₀) := by
    have h := (lattice K _).sub_mem hnorm hsmall
    rwa [← hpoly, add_sub_cancel_left] at h
  have heven : Even (p - 1) := Nat.Odd.sub_odd hp odd_one
  have hlastEq : f (p - 1) = d (p - 1) * z := by
    dsimp only [f]
    rw [heven.neg_one_pow, one_mul, show p - (p - 1) = 1 by omega, pow_one]
  rw [hlastEq] at hlastMem
  have hz0 : z ≠ 0 := (ord_ne_top_iff K).1 (by rw [hz]; exact WithTop.coe_ne_top)
  have hdiv := (div_mem_lattice_iff K z (d (p - 1) * z) (M - t) B₀ hz).2 hlastMem
  simpa only [mul_div_cancel_right₀ _ hz0, d, z, B₀] using hdiv

private theorem map_mem_scaled_lattice
    (E K : Type*) [Field E] [Field K]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra E K] [ValuativeExtension E K] [Module.Finite E K]
    {p : ℕ} (hram : ramificationIndex E K = p) {x : E} {q : ℤ}
    (hx : x ∈ lattice E q) :
    algebraMap E K x ∈ lattice K ((p : ℤ) * q) := by
  rw [mem_lattice, ord_algebraMap, hram]
  rw [mem_lattice] at hx
  simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using nsmul_le_nsmul_right hx p

private theorem residue_degree_mul
    (F E K : Type*) [Field F] [Field E] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F E] [Algebra F K] [Algebra E K] [IsScalarTower F E K]
    [ValuativeExtension F E] [ValuativeExtension F K] [ValuativeExtension E K]
    [Module.Finite F E] [Module.Finite F K] [Module.Finite E K] :
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

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K]
variable [Module.Free F K] [Module.Finite F K] [IsGalois F K]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Paper Lemma 9.18 (`O:E:trace`).** The signed trace of the actual
coordinate satisfies `v_K(T + Y^(p-1)s) ≥ B₀`; both summands have depth
at least `R`. Here `s = -E_(p-1)(Delta)` and `T = Tr((Y*Delta)^(p-1))`.

The coordinate is universally quantified and is never changed. Its order
and the two twisted bounds are the outputs of the accepted
`twistedEstimates` constructor. The theorem below also constructs such a
coordinate from the genuine diamond. No semilinear congruence, norm
representative or phase cancellation is an input. -/
theorem semilinearTrace {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1)
    (D : OddTotalBreakData (F := F) (K := K) hp hG) :
    let B₁ := D.B₁
    let B₂ := D.B₂
    letI := Basic.intermediateFieldValuativeRel B₁
    letI := Basic.intermediateFieldTopology B₁
    letI := Basic.intermediateField_localField B₁
    letI := Basic.intermediateFieldValuativeRel B₂
    letI := Basic.intermediateFieldTopology B₂
    letI := Basic.intermediateField_localField B₂
    ∀ Delta : K,
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) →
      (∀ (Y : B₂) (i : ℕ), i < p →
        ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) + ord B₂ Y ≤
          ord B₁ (trace B₁ K (algebraMap B₂ K Y * Delta ^ i))) →
      (∀ (Y : B₂) (i : ℕ), 1 ≤ i → i < p →
        ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) + i • ord B₂ Y ≤
          ord B₁ (elementarySymmetric B₁ K i (algebraMap B₂ K Y * Delta))) →
      ∀ (Y : B₂) (m : ℤ), ord B₂ Y = (m : WithTop ℤ) → (D.t : ℤ) < p * m →
      let M : ℤ := p * m
      let R : ℤ := ((p : ℤ) - 1) * M + p * ((p : ℤ) - 1) * D.delta
      let B₀ : ℤ := R + ((p : ℤ) - 1) * D.t
      let s : B₁ := -elementarySymmetric B₁ K (p - 1) Delta
      let T : B₁ := trace B₁ K ((algebraMap B₂ K Y * Delta) ^ (p - 1))
      let Z : K := (algebraMap B₂ K Y) ^ (p - 1) * algebraMap B₁ K s
      algebraMap B₁ K T + Z ∈ lattice K B₀ ∧
        algebraMap B₁ K T ∈ lattice K R ∧ Z ∈ lattice K R := by
  dsimp only [OddTotalBreakData.B₁, OddTotalBreakData.B₂]
  let B₁ := IntermediateField.fixedField D.H₁
  let B₂ := IntermediateField.fixedField D.H₂
  letI := Basic.intermediateFieldValuativeRel B₁
  letI := Basic.intermediateFieldTopology B₁
  letI := Basic.intermediateFieldValuativeRel B₂
  letI := Basic.intermediateFieldTopology B₂
  obtain ⟨hLocal₁, hFreeF₁, hFiniteF₁, hFree₁K, hFinite₁K, hScalar₁,
      hValF₁, hVal₁K, htotal, hdegreeLower₁, hdegreeUpper₁, hcycF₁, hcyc₁K⟩ :=
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
  obtain ⟨hLocal₂, hFreeF₂, hFiniteF₂, hFree₂K, hFinite₂K, hScalar₂,
      hValF₂, hVal₂K, _htotal₂, hdegreeLower₂, hdegreeUpper₂, hcycF₂, _hcyc₂K⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
  letI := hLocal₂
  letI := hFreeF₂
  letI := hFiniteF₂
  letI := hFree₂K
  letI := hFinite₂K
  letI := hScalar₂
  letI := hValF₂
  letI := hVal₂K
  letI : PrimeCyclicExtension F B₂ :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F B₂ hcycF₂
  have hresmul₁ := residue_degree_mul F B₁ K
  have hresmul₂ := residue_degree_mul F B₂ K
  rw [hres] at hresmul₁ hresmul₂
  have hres₁K : residueDegree B₁ K = 1 := (mul_eq_one.mp hresmul₁).2
  have hresF₂ : residueDegree F B₂ = 1 := (mul_eq_one.mp hresmul₂).1
  have hres₂K : residueDegree B₂ K = 1 := (mul_eq_one.mp hresmul₂).2
  have hram₁K : ramificationIndex B₁ K = p := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree B₁ K
    rw [hdegreeUpper₁, hres₁K, mul_one] at h
    exact h.symm
  have hram₂K : ramificationIndex B₂ K = p := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree B₂ K
    rw [hdegreeUpper₂, hres₂K, mul_one] at h
    exact h.symm
  have hp2 : 2 < p := D.odd_prime
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hpeven : Even (p - 1) := Nat.Odd.sub_odd hpodd odd_one
  have hpcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
  intro Delta hDelta htr hsym Y m hY _hM
  let y : K := algebraMap B₂ K Y
  let z : K := y * Delta
  let C : ℤ := ((p : ℤ) - 1) * D.t₂
  let M : ℤ := p * m
  let R : ℤ := ((p : ℤ) - 1) * M + p * ((p : ℤ) - 1) * D.delta
  let B₀ : ℤ := R + ((p : ℤ) - 1) * D.t
  have hy : ord K y = (M : WithTop ℤ) := by
    rw [ord_algebraMap, hram₂K, hY, ← WithTop.coe_nsmul]
    rfl
  have htrz (j : ℕ) (hj : j < p) :
      trace B₁ K (z ^ j) ∈ lattice B₁ (C + (j : ℤ) * (m - D.t)) := by
    have h := htr (Y ^ j) j hj
    rw [ord_pow, hY, ← WithTop.coe_nsmul, ← WithTop.coe_add] at h
    rw [mem_lattice]
    convert h using 1
    · congr 1
      dsimp only [C]
      simp only [nsmul_eq_mul]
      ring
    · simp only [z, y, mul_pow, map_pow]
      rfl
  have hsymz (i : ℕ) (hi : 1 ≤ i) (hip : i < p) :
      elementarySymmetric B₁ K i z ∈ lattice B₁ (C + (i : ℤ) * (m - D.t)) := by
    have h := hsym Y i hi hip
    rw [hY, ← WithTop.coe_nsmul, ← WithTop.coe_add] at h
    rw [mem_lattice]
    convert h using 1
    congr 1
    dsimp only [C]
    simp only [nsmul_eq_mul]
    ring
  have hcoeff (i : ℕ) (hi : 1 ≤ i) (hip : i < p) :
      elementarySymmetric B₁ K i Delta ∈ lattice B₁ (C - (i : ℤ) * D.t) := by
    simpa only [mem_lattice, map_one, one_mul, ord_one, nsmul_zero, add_zero, C]
      using hsym 1 i hi hip
  have hcoeffK (i : ℕ) (hi : 1 ≤ i) (hip : i < p) :
      algebraMap B₁ K (elementarySymmetric B₁ K i Delta) ∈
        lattice K ((p : ℤ) * C - (p : ℤ) * i * D.t) := by
    convert map_mem_scaled_lattice B₁ K hram₁K (hcoeff i hi hip) using 1
    congr 1
    ring
  have hsymK (i : ℕ) (hi : 1 ≤ i) (hip : i < p) :
      algebraMap B₁ K (elementarySymmetric B₁ K i z) ∈
        lattice K ((p : ℤ) * C + (i : ℤ) * (M - p * D.t)) := by
    convert map_mem_scaled_lattice B₁ K hram₁K (hsymz i hi hip) using 1
    congr 1
    dsimp only [M]
    ring
  have hNormDelta : algebraMap B₁ K (norm B₁ K Delta) ∈
      lattice K (-(p : ℤ) * D.t) := by
    rw [mem_lattice, ord_algebraMap, hram₁K, ord_norm, hres₁K, one_nsmul,
      hDelta, ← WithTop.coe_nsmul]
    simp only [nsmul_eq_mul, mul_neg, neg_mul]
    exact le_rfl
  have hNormY : algebraMap B₁ K (norm B₁ K y) - y ^ p ∈
      lattice K ((p : ℤ) * M + p * C) := by
    have hbreak₂ : PrimeCyclicExtension.IsLowerBreak F B₂ D.t₂ := by
      simpa only [B₂, Ramification.IntermediateBreakPair] using D.B₂_breaks.1
    have hpower := powerNorm F B₂ p D.t₂ hdegreeLower₂ D.odd_prime hbreak₂
      (lt_of_lt_of_le D.t_pos D.t_le_t₂) hresF₂ Y
    rw [hY, ← WithTop.coe_nsmul, ← WithTop.coe_add] at hpower
    have hpowerLat : Y ^ p - algebraMap F B₂ (norm F B₂ Y) ∈
        lattice B₂ ((p : ℤ) * m + C) := by
      rw [mem_lattice]
      simpa only [nsmul_eq_mul, Nat.cast_mul, hpcast, C] using hpower
    have hscaled := map_mem_scaled_lattice B₂ K hram₂K
      ((lattice B₂ _).neg_mem hpowerLat)
    have hrestrict := primeDiamond_norm_restrict B₁ B₂ hp htotal
      hdegreeLower₁ hdegreeLower₂ D.B₁_ne_B₂ Y
    change norm B₁ K y = algebraMap F B₁ (norm F B₂ Y) at hrestrict
    rw [hrestrict]
    have hdepth : (p : ℤ) * M + p * C = (p : ℤ) * ((p : ℤ) * m + C) := by
      dsimp only [M]
      ring
    rw [hdepth]
    simpa only [map_neg, map_sub, map_pow, ← IsScalarTower.algebraMap_apply, neg_sub, y]
      using hscaled
  have heDiff : algebraMap B₁ K (elementarySymmetric B₁ K (p - 1) z) -
      y ^ (p - 1) * algebraMap B₁ K (elementarySymmetric B₁ K (p - 1) Delta) ∈
      lattice K B₀ := by
    have h := semilinear_symmetric_mem B₁ K hpodd D.odd_prime hdegreeUpper₁
      y Delta (p * C) M D.t (Int.natCast_nonneg _) hy hDelta hcoeffK hsymK
      hNormDelta hNormY
    convert h using 1
    congr 1
    dsimp only [B₀, R, C]
    rw [ht₂]
    ring
  have hnonlinear :
      algebraMap B₁ K (trace B₁ K (z ^ (p - 1)) +
        ((p - 1 : ℕ) : B₁) * elementarySymmetric B₁ K (p - 1) z) ∈
      lattice K B₀ := by
    have h := newton_trace_remainder_mem B₁ K z C (m - D.t) (by omega) hpeven
      (fun i hi hip => hsymz i hi (by omega)) (fun i _hi hip => htrz i (by omega))
    apply lattice_antitone K _ (map_mem_scaled_lattice B₁ K hram₁K h)
    rw [hpcast]
    dsimp only [B₀, R, M, C]
    rw [ht₂]
    have hnonneg : 0 ≤ ((p : ℤ) - 1) ^ 2 * (D.t : ℤ) +
        (p : ℤ) * ((p : ℤ) - 1) * D.delta :=
      add_nonneg (mul_nonneg (sq_nonneg _) (Int.natCast_nonneg _))
        (mul_nonneg (mul_nonneg (Int.natCast_nonneg _) (by omega)) (Int.natCast_nonneg _))
    nlinarith
  have hTraceR : algebraMap B₁ K (trace B₁ K (z ^ (p - 1))) ∈ lattice K R := by
    convert map_mem_scaled_lattice B₁ K hram₁K (htrz (p - 1) (by omega)) using 1
    congr 1
    rw [hpcast]
    dsimp only [R, M, C]
    rw [ht₂]
    ring
  have hZR : y ^ (p - 1) *
      algebraMap B₁ K (-elementarySymmetric B₁ K (p - 1) Delta) ∈ lattice K R := by
    have hpow : y ^ (p - 1) ∈ lattice K (((p : ℤ) - 1) * M) := by
      rw [mem_lattice, ord_pow, hy, ← WithTop.coe_nsmul, nsmul_eq_mul, hpcast]
    have hs := map_mem_scaled_lattice B₁ K hram₁K
      ((lattice B₁ _).neg_mem (hcoeff (p - 1) (by have := D.odd_prime; omega) (by omega)))
    convert mul_mem_lattice K hpow hs using 1
    congr 1
    rw [hpcast]
    dsimp only [R, C]
    rw [ht₂]
    ring
  have hpZ : (p : K) * (y ^ (p - 1) *
      algebraMap B₁ K (-elementarySymmetric B₁ K (p - 1) Delta)) ∈ lattice K B₀ := by
    have hprime : (p : K) ∈ lattice K ((p : ℤ) * C) := by
      simpa only [mem_lattice, Nat.cast_mul, hpcast, C, mul_assoc]
        using oddTotal_primeValuationBound hp hG hres D
    apply lattice_antitone K _ (mul_mem_lattice K hprime hZR)
    dsimp only [B₀, C]
    have htle : (D.t : ℤ) ≤ D.t₂ := by exact_mod_cast D.t_le_t₂
    have hnonneg : 0 ≤ ((p : ℤ) - 1) * ((p : ℤ) * D.t₂ - D.t) := by
      apply mul_nonneg (by omega)
      nlinarith [Int.natCast_nonneg D.t₂]
    nlinarith
  have hmultiple : ((p - 1 : ℕ) : K) *
      (algebraMap B₁ K (elementarySymmetric B₁ K (p - 1) z) -
        y ^ (p - 1) * algebraMap B₁ K (elementarySymmetric B₁ K (p - 1) Delta)) ∈
      lattice K B₀ := by
    rw [← nsmul_eq_mul]
    exact (lattice K B₀).nsmul_mem heDiff (p - 1)
  refine ⟨?_, hTraceR, hZR⟩
  have hsum := (lattice K B₀).add_mem ((lattice K B₀).sub_mem hnonlinear hmultiple) hpZ
  convert hsum using 1
  simp only [map_add, map_mul, map_natCast, map_neg]
  have hpK : ((p - 1 : ℕ) : K) = (p : K) - 1 := by
    simpa only [Nat.cast_one] using (Nat.cast_sub (R := K) hp.one_le)
  rw [hpK]
  ring

/-- Construct an actual Artin--Schreier coordinate with the semilinear
estimate from the genuine totally ramified prime-square diamond. The same
coordinate retains its exact equation, both orders, generation property
and the accepted trace--norm comparison. The estimate is uniform in `Y`.

This constructor discharges the coordinate hypotheses of `semilinearTrace`
in both field characteristics; no auxiliary stationary model is assumed. -/
theorem exists_semilinearTrace_coordinate {p : ℕ} (hp : p.Prime)
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
      trace F B₁ (norm B₁ K Delta) - trace F B₂ a ∈ lattice F (1 + (D.t₂ : ℤ)) ∧
      ∀ (Y : B₂) (m : ℤ), ord B₂ Y = (m : WithTop ℤ) → (D.t : ℤ) < p * m →
      let M : ℤ := p * m
      let R : ℤ := ((p : ℤ) - 1) * M + p * ((p : ℤ) - 1) * D.delta
      let B₀ : ℤ := R + ((p : ℤ) - 1) * D.t
      let s : B₁ := -elementarySymmetric B₁ K (p - 1) Delta
      let T : B₁ := trace B₁ K ((algebraMap B₂ K Y * Delta) ^ (p - 1))
      let Z : K := (algebraMap B₂ K Y) ^ (p - 1) * algebraMap B₁ K s
      algebraMap B₁ K T + Z ∈ lattice K B₀ ∧
        algebraMap B₁ K T ∈ lattice K R ∧ Z ∈ lattice K R := by
  letI := Basic.intermediateFieldValuativeRel D.B₁
  letI := Basic.intermediateFieldTopology D.B₁
  letI := Basic.intermediateField_localField D.B₁
  letI := Basic.intermediateFieldValuativeRel D.B₂
  letI := Basic.intermediateFieldTopology D.B₂
  letI := Basic.intermediateField_localField D.B₂
  obtain ⟨Delta, a, hroot, hDelta, ha, hprime, hgen, _hcoeff, htr, hsym, hei, _hs⟩ :=
    twistedEstimates hp hG hres hchar D
  exact ⟨Delta, a, hroot, hDelta, ha, hprime, hgen,
    traceNorm hp hG hres hchar D Delta a hroot hgen hei,
    semilinearTrace hp hG hres D Delta hDelta htr hsym⟩

end

end LanglandsSecondMainLemma.Odd.R1
