import LanglandsSecondMainLemma.Odd.R1.SemilinearTrace

/-!
# Odd / R1 / Power

Paper Lemma 9.19 (`O:E:power`, `O:E:L1bound`), with setup at
`O:sec:weighted`. The weight is inserted before taking powers. The actual
norm `u = N_{B₂/F}(Y)` is retained, and all depths are integers.

The estimate for a fixed coordinate uses the accepted twisted bounds.
`exists_power_coordinate` constructs such a coordinate from the genuine
prime-square diamond, in either field characteristic.
-/

namespace LanglandsSecondMainLemma.Odd.R1
open LanglandsFirstMainLemma
open LanglandsSecondMainLemma.Odd.Total
open scoped BigOperators
noncomputable section

private theorem power_mem
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {x : E} {q : ℤ}
    (hx : x ∈ lattice E q) (n : ℕ) : x ^ n ∈ lattice E ((n : ℤ) * q) := by
  rw [mem_lattice, ord_pow]
  simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using
    nsmul_le_nsmul_right ((mem_lattice E).1 hx) n

/-- Every interior binomial coefficient is divisible by the prime, also
when that prime is zero in the field. -/
private theorem prime_binomial_mem
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {p : ℕ} (hp : p.Prime)
    {x y : E} {q C : ℤ} (hx : x ∈ lattice E q) (hy : y ∈ lattice E q)
    (hprime : (p : E) ∈ lattice E C) :
    (x + y) ^ p - (x ^ p + y ^ p) ∈ lattice E (C + (p : ℤ) * q) := by
  classical
  let f (i : ℕ) : E := x ^ i * y ^ (p - i) * (p.choose i : E)
  let S := (Finset.range (p + 1)).erase p
  have hpS : p ∈ Finset.range (p + 1) := by simp
  have hzero : 0 ∈ S := by simp [S, Ne.symm hp.ne_zero]
  have hsum : (∑ i ∈ S.erase 0, f i) ∈ lattice E (C + (p : ℤ) * q) := by
    apply sum_mem_lattice E
    intro i hi
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
    have hiS := (Finset.mem_erase.mp hi).2
    have hip : i < p := by
      have := Finset.mem_erase.mp hiS
      have := Finset.mem_range.mp this.2
      omega
    obtain ⟨k, hk⟩ := hp.dvd_choose_self hi0 hip
    have hc : (p.choose i : E) ∈ lattice E C := by
      rw [hk, Nat.cast_mul, mul_comm, ← nsmul_eq_mul]
      exact (lattice E C).nsmul_mem hprime k
    have h := mul_mem_lattice E
      (mul_mem_lattice E (power_mem E hx i) (power_mem E hy (p - i))) hc
    convert h using 1
    congr 1
    have hcast : ((p - i : ℕ) : ℤ) = (p : ℤ) - i := by omega
    rw [hcast]
    ring
  have hid := add_pow x y p
  change (x + y) ^ p = ∑ i ∈ Finset.range (p + 1), f i at hid
  rw [← Finset.sum_erase_add _ f hpS] at hid
  change (x + y) ^ p = (∑ i ∈ S, f i) + f p at hid
  rw [← Finset.sum_erase_add S f hzero] at hid
  have hf0 : f 0 = y ^ p := by simp [f]
  have hfp : f p = x ^ p := by simp [f]
  rw [hf0, hfp] at hid
  have heq : (x + y) ^ p - (x ^ p + y ^ p) = ∑ i ∈ S.erase 0, f i := by
    linear_combination hid
  rwa [heq]

/-- Taking a power of an integral element preserves its congruence to one. -/
private theorem integral_power_sub_one_mem
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {x : E} {C : ℤ}
    (hx : x ∈ lattice E 0) (herr : x - 1 ∈ lattice E C) (n : ℕ) :
    x ^ n - 1 ∈ lattice E C := by
  have hsum : (∑ i ∈ Finset.range n, x ^ i) ∈ lattice E 0 := by
    apply sum_mem_lattice E
    intro i _
    simpa only [mul_zero] using power_mem E hx i
  have h := mul_mem_lattice E hsum herr
  simpa only [geom_sum_mul, zero_add] using h

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K]
variable [Module.Free F K] [Module.Finite F K] [IsGalois F K]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Paper Lemma 9.19 (`O:E:power`).** The full weighted expression
`L₁ = u^(p-1) A₀ (T^p + u^(p-1) s^p)` has the explicit upstairs depth
`2p(p-1)M - pt + p²(p-1)δ`.

The coordinate, its actual trace and symmetric coefficient, and the actual
lower norms are fixed throughout. The coordinate order and twisted bounds
are supplied by the accepted `twistedEstimates` constructor; no power
congruence or exact norm representative is assumed. -/
theorem power {p : ℕ} (hp : p.Prime)
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
    ∀ (Delta : K) (a : B₂),
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) →
      ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) →
      (∀ (Y : B₂) (i : ℕ), i < p →
        ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) + ord B₂ Y ≤
          ord B₁ (trace B₁ K (algebraMap B₂ K Y * Delta ^ i))) →
      (∀ (Y : B₂) (i : ℕ), 1 ≤ i → i < p →
        ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) + i • ord B₂ Y ≤
          ord B₁ (elementarySymmetric B₁ K i (algebraMap B₂ K Y * Delta))) →
      ∀ (Y : B₂) (m : ℤ), ord B₂ Y = (m : WithTop ℤ) → (D.t : ℤ) < p * m →
      let M : ℤ := p * m
      let u : F := norm F B₂ Y
      let A₀ : F := norm F B₂ a
      let s : B₁ := -elementarySymmetric B₁ K (p - 1) Delta
      let T : B₁ := trace B₁ K ((algebraMap B₂ K Y * Delta) ^ (p - 1))
      let L₁ : B₁ := algebraMap F B₁ (u ^ (p - 1) * A₀) *
        (T ^ p + algebraMap F B₁ (u ^ (p - 1)) * s ^ p)
      algebraMap B₁ K L₁ ∈
        lattice K (2 * p * ((p : ℤ) - 1) * M - p * D.t +
          (p : ℤ) ^ 2 * ((p : ℤ) - 1) * D.delta) := by
  dsimp only [OddTotalBreakData.B₁, OddTotalBreakData.B₂]
  let B₁ := IntermediateField.fixedField D.H₁
  let B₂ := IntermediateField.fixedField D.H₂
  letI := Basic.intermediateFieldValuativeRel B₁
  letI := Basic.intermediateFieldTopology B₁
  letI := Basic.intermediateField_localField B₁
  letI := Basic.intermediateFieldValuativeRel B₂
  letI := Basic.intermediateFieldTopology B₂
  obtain ⟨hLocal₂, hFreeF₂, hFiniteF₂, hFree₂K, hFinite₂K, hScalar₂,
      hValF₂, hVal₂K, htotal, hdegreeLower₂, hdegreeUpper₂, hcycF₂, _hcyc₂K⟩ :=
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
  have hresmul : residueDegree F B₂ * residueDegree B₂ K = 1 := by
    letI : IsScalarTower (ringOfIntegers F) (ringOfIntegers B₂) (ringOfIntegers K) :=
      IsScalarTower.of_algebraMap_eq' (by
        ext x
        change algebraMap F K (x : F) = algebraMap B₂ K (algebraMap F B₂ (x : F))
        rw [← IsScalarTower.algebraMap_apply F B₂ K])
    letI : IsLocalHom (algebraMap (ringOfIntegers F) (ringOfIntegers B₂)) := inferInstance
    letI : IsLocalHom (algebraMap (ringOfIntegers B₂) (ringOfIntegers K)) := inferInstance
    rw [← hres, residueDegree_eq_finrank_residueField,
      residueDegree_eq_finrank_residueField, residueDegree_eq_finrank_residueField]
    exact Module.finrank_mul_finrank (ResidueField F) (ResidueField B₂) (ResidueField K)
  have hresF₂ : residueDegree F B₂ = 1 := (mul_eq_one.mp hresmul).1
  have hres₂K : residueDegree B₂ K = 1 := (mul_eq_one.mp hresmul).2
  have hram₂K : ramificationIndex B₂ K = p := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree B₂ K
    rw [hdegreeUpper₂, hres₂K, mul_one] at h
    exact h.symm
  have hramFK : ramificationIndex F K = p ^ 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [htotal, hres, mul_one] at h
    simpa only [pow_two] using h.symm
  have hp2 : 2 < p := D.odd_prime
  have hpcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
  intro Delta a hDelta ha htr hsym Y m hY hM
  let M : ℤ := p * m
  let R : ℤ := ((p : ℤ) - 1) * M + p * ((p : ℤ) - 1) * D.delta
  let B₀ : ℤ := R + ((p : ℤ) - 1) * D.t
  let C : ℤ := p * ((p : ℤ) - 1) * D.t₂
  let W : ℤ := p * ((p : ℤ) - 1) * M - (p : ℤ) ^ 2 * D.t
  let V : ℤ := 2 * p * ((p : ℤ) - 1) * M - p * D.t +
    (p : ℤ) ^ 2 * ((p : ℤ) - 1) * D.delta
  let y : K := algebraMap B₂ K Y
  let u : F := norm F B₂ Y
  let U : K := algebraMap F K u
  let A₀ : F := norm F B₂ a
  let w : K := algebraMap F K (u ^ (p - 1) * A₀)
  let s : B₁ := -elementarySymmetric B₁ K (p - 1) Delta
  let T : K := algebraMap B₁ K (trace B₁ K ((y * Delta) ^ (p - 1)))
  let Z : K := y ^ (p - 1) * algebraMap B₁ K s
  have hsemi := semilinearTrace hp hG hres D Delta hDelta htr hsym Y m hY hM
  obtain ⟨hE, hT, hZ⟩ := hsemi
  change T + Z ∈ lattice K B₀ at hE
  change T ∈ lattice K R at hT
  change Z ∈ lattice K R at hZ
  have hu : ord F u = (m : WithTop ℤ) := by
    rw [ord_norm, hresF₂, one_nsmul, hY]
  have hA₀ : ord F A₀ = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_norm, hresF₂, one_nsmul, ha]
  have hw : w ∈ lattice K W := by
    rw [mem_lattice, ord_algebraMap, hramFK, ord_mul, ord_pow, hu, hA₀,
      ← WithTop.coe_nsmul, ← WithTop.coe_add, ← WithTop.coe_nsmul]
    apply le_of_eq
    congr 1
    simp only [nsmul_eq_mul, Nat.cast_pow, hpcast, W, M]
    ring
  have hprime : (p : K) ∈ lattice K C := by
    simpa only [mem_lattice, Nat.cast_mul, hpcast, C, mul_assoc]
      using oddTotal_primeValuationBound hp hG hres D
  have hdepth : V ≤ W + (C + (p : ℤ) * R) := by
    have hnonneg : 0 ≤ (p : ℤ) * ((p : ℤ) - 1) * D.delta :=
      mul_nonneg (mul_nonneg (Int.natCast_nonneg _) (by omega)) (Int.natCast_nonneg _)
    dsimp only [V, W, C, R]
    rw [ht₂]
    nlinarith
  have hEp : w * (T + Z) ^ p ∈ lattice K V := by
    convert mul_mem_lattice K hw (power_mem K hE p) using 1
    congr 1
    dsimp only [V, W, B₀, R]
    ring
  have hmixed : w * ((T + Z) ^ p - (T ^ p + Z ^ p)) ∈ lattice K V :=
    lattice_antitone K hdepth
      (mul_mem_lattice K hw (prime_binomial_mem K hp hT hZ hprime))
  have hTpZp : w * (T ^ p + Z ^ p) ∈ lattice K V := by
    convert (lattice K V).sub_mem hEp hmixed using 1
    ring
  have hy : ord K y = (M : WithTop ℤ) := by
    rw [ord_algebraMap, hram₂K, hY, ← WithTop.coe_nsmul]
    rfl
  have hy0 : y ≠ 0 := (ord_ne_top_iff K).1 (by rw [hy]; exact WithTop.coe_ne_top)
  have hnorm : U - y ^ p ∈ lattice K ((p : ℤ) * M + C) := by
    have hbreak₂ : PrimeCyclicExtension.IsLowerBreak F B₂ D.t₂ := by
      simpa only [B₂, Ramification.IntermediateBreakPair] using D.B₂_breaks.1
    have h := powerNorm F B₂ p D.t₂ hdegreeLower₂ D.odd_prime hbreak₂
      (lt_of_lt_of_le D.t_pos D.t_le_t₂) hresF₂ Y
    rw [hY, ← WithTop.coe_nsmul, ← WithTop.coe_add] at h
    have hlat : Y ^ p - algebraMap F B₂ u ∈
        lattice B₂ ((p : ℤ) * m + ((p : ℤ) - 1) * D.t₂) := by
      rw [mem_lattice]
      simpa only [nsmul_eq_mul, Nat.cast_mul, hpcast, u] using h
    have hscaled : algebraMap B₂ K (Y ^ p - algebraMap F B₂ u) ∈
        lattice K ((p : ℤ) * M + C) := by
      rw [mem_lattice, ord_algebraMap, hram₂K]
      have h := nsmul_le_nsmul_right ((mem_lattice B₂).1 hlat) p
      rw [← WithTop.coe_nsmul] at h
      convert h using 1
      congr 1
      simp only [nsmul_eq_mul, M, C]
      ring
    have hneg := (lattice K ((p : ℤ) * M + C)).neg_mem hscaled
    simpa only [map_sub, map_pow, ← IsScalarTower.algebraMap_apply, neg_sub, U, y] using hneg
  let q : K := U / y ^ p
  have hqerr : q - 1 ∈ lattice K C := by
    have hyp : ord K (y ^ p) = (((p : ℤ) * M : ℤ) : WithTop ℤ) := by
      rw [ord_pow, hy, ← WithTop.coe_nsmul]
      rfl
    have hdiv := (div_mem_lattice_iff K (y ^ p) (U - y ^ p)
      ((p : ℤ) * M) C hyp).2 hnorm
    simpa only [q, sub_div, div_self (pow_ne_zero _ hy0)] using hdiv
  have hC : 0 ≤ C := by
    exact mul_nonneg (mul_nonneg (Int.natCast_nonneg _) (by omega)) (Int.natCast_nonneg _)
  have hq : q ∈ lattice K 0 := by
    have h := (lattice K 0).add_mem (lattice_antitone K hC hqerr)
      (show (1 : K) ∈ lattice K 0 by simp)
    simpa only [sub_add_cancel] using h
  have hreplace : w * ((q ^ (p - 1) - 1) * Z ^ p) ∈ lattice K V :=
    lattice_antitone K hdepth (mul_mem_lattice K hw
      (mul_mem_lattice K (integral_power_sub_one_mem K hq hqerr (p - 1))
        (power_mem K hZ p)))
  have hqmul : q * y ^ p = U := div_mul_cancel₀ U (pow_ne_zero _ hy0)
  have hqZ : q ^ (p - 1) * Z ^ p = U ^ (p - 1) * (algebraMap B₁ K s) ^ p := by
    dsimp only [Z]
    rw [mul_pow, ← pow_mul, Nat.mul_comm (p - 1) p, pow_mul, ← mul_assoc,
      ← mul_pow, hqmul]
  have hfinal := (lattice K V).add_mem hTpZp hreplace
  have heq : w * (T ^ p + Z ^ p) + w * ((q ^ (p - 1) - 1) * Z ^ p) =
      w * (T ^ p + U ^ (p - 1) * (algebraMap B₁ K s) ^ p) := by
    linear_combination w * hqZ
  rw [heq] at hfinal
  simpa only [map_mul, map_add, map_pow, ← IsScalarTower.algebraMap_apply,
    w, T, U, u, A₀, s, y, V, M] using hfinal

/-- Construct an actual Artin--Schreier coordinate satisfying the weighted
power estimate, uniformly in `Y`. Its exact equation, both orders,
generation property, and trace--norm comparison are retained. This uses
the accepted `twistedEstimates` constructor in both field characteristics. -/
theorem exists_power_coordinate {p : ℕ} (hp : p.Prime)
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
      let u : F := norm F B₂ Y
      let A₀ : F := norm F B₂ a
      let s : B₁ := -elementarySymmetric B₁ K (p - 1) Delta
      let T : B₁ := trace B₁ K ((algebraMap B₂ K Y * Delta) ^ (p - 1))
      let L₁ : B₁ := algebraMap F B₁ (u ^ (p - 1) * A₀) *
        (T ^ p + algebraMap F B₁ (u ^ (p - 1)) * s ^ p)
      algebraMap B₁ K L₁ ∈
        lattice K (2 * p * ((p : ℤ) - 1) * M - p * D.t +
          (p : ℤ) ^ 2 * ((p : ℤ) - 1) * D.delta) := by
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
    power hp hG hres D Delta a hDelta ha htr hsym⟩

end
end LanglandsSecondMainLemma.Odd.R1
