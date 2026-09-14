import LanglandsSecondMainLemma.Odd.R1.Power

/-!
# Odd / R1 / Weighted

Paper Theorem 9.20 (`O:E:main`, `O:E:Abound`), with the setup of
`O:sec:weighted`. The actual lower norms replace the powers in the accepted
weighted estimate. Descent to the base field retains the exact floor term.
All depths are integers, and zero expressions retain their infinite order.
-/

namespace LanglandsSecondMainLemma.Odd.R1
open LanglandsFirstMainLemma
open LanglandsSecondMainLemma.Odd.Total
noncomputable section

/-- Descent through a totally ramified extension at a divisible depth. -/
private theorem descend_lattice
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L] [Module.Finite E L]
    {p : ℕ} (hp : 0 < p) (hram : ramificationIndex E L = p)
    {x : E} {q : ℤ} (hx : algebraMap E L x ∈ lattice L ((p : ℤ) * q)) :
    x ∈ lattice E q := by
  rw [mem_lattice, ord_algebraMap, hram] at hx
  rw [mem_lattice]
  by_cases htop : ord E x = ⊤
  · simp [htop]
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp htop
  rw [← hr, ← WithTop.coe_nsmul, WithTop.coe_le_coe] at hx
  rw [← hr, WithTop.coe_le_coe]
  simp only [nsmul_eq_mul] at hx
  exact (mul_le_mul_iff_right₀ (show (0 : ℤ) < p by omega)).mp hx

/-- Integral descent of `p X - t` gives precisely `X - floor(t/p)`. -/
private theorem descend_lattice_floor
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L] [Module.Finite E L]
    {p : ℕ} (hp : 0 < p) (hram : ramificationIndex E L = p)
    {x : E} {X t : ℤ} (hx : algebraMap E L x ∈ lattice L ((p : ℤ) * X - t)) :
    x ∈ lattice E (X - t / p) := by
  rw [mem_lattice, ord_algebraMap, hram] at hx
  rw [mem_lattice]
  by_cases htop : ord E x = ⊤
  · simp [htop]
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp htop
  rw [← hr, ← WithTop.coe_nsmul, WithTop.coe_le_coe] at hx
  rw [← hr, WithTop.coe_le_coe]
  simp only [nsmul_eq_mul] at hx
  have hdiv : X - r ≤ t / (p : ℤ) :=
    (Int.le_ediv_iff_mul_le (show (0 : ℤ) < p by omega)).2 (by nlinarith)
  omega

/-- The final integer inequality in `O:E:Abound`. It is valid even when
`t` is divisible by `p`; the paper's coordinates additionally give `p ∤ t`. -/
private theorem conductor_le_weighted_depth
    {p t delta : ℕ} {m : ℤ} (hp : 2 < p) (hm : (t : ℤ) < p * m) :
    1 + ((t : ℤ) + delta) ≤
      2 * ((p : ℤ) - 1) * m + ((p : ℤ) - 1) * delta - (t : ℤ) / p := by
  have hpZ : (0 : ℤ) < p := by omega
  have ha : 0 ≤ (t : ℤ) / p := Int.ediv_nonneg (Int.natCast_nonneg _) hpZ.le
  have ham : (t : ℤ) / p < m := (Int.ediv_lt_iff_lt_mul hpZ).2 (by nlinarith)
  have hb : (t : ℤ) % p < p := Int.emod_lt_of_pos _ hpZ
  have hdecomp := Int.mul_ediv_add_emod (t : ℤ) (p : ℤ)
  have hpa : 0 ≤ ((p : ℤ) - 3) * ((t : ℤ) / p) := mul_nonneg (by omega) ha
  have hpd : 0 ≤ ((p : ℤ) - 2) * delta := mul_nonneg (by omega) (Int.natCast_nonneg _)
  have hpm : 0 ≤ ((p : ℤ) - 1) * (m - ((t : ℤ) / p + 1)) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

/-- The accepted cyclic norm--power bound, expressed at an integer lattice
lower bound, including when the input is zero. -/
private theorem power_norm_mem
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    [Module.Free E L] [Module.Finite E L] [PrimeCyclicExtension E L]
    {p t : ℕ} (hdegree : Module.finrank E L = p) (hp : 2 < p)
    (hbreak : PrimeCyclicExtension.IsLowerBreak E L t) (ht : 0 < t)
    (hres : residueDegree E L = 1) {x : L} {q : ℤ} (hx : x ∈ lattice L q) :
    x ^ p - algebraMap E L (norm E L x) ∈
      lattice L ((p : ℤ) * q + ((p : ℤ) - 1) * t) := by
  have h := powerNorm E L p t hdegree hp hbreak ht hres x
  have hq : p • (q : WithTop ℤ) + (((((p - 1) * t : ℕ) : ℤ) : WithTop ℤ)) ≤
      p • ord L x + (((((p - 1) * t : ℕ) : ℤ) : WithTop ℤ)) :=
    add_le_add (nsmul_le_nsmul_right ((mem_lattice L).1 hx) p) le_rfl
  have hpcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  simpa only [mem_lattice, ← WithTop.coe_nsmul, ← WithTop.coe_add,
    nsmul_eq_mul, Nat.cast_mul, hpcast] using hq.trans h

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
/-- **Paper Theorem 9.20 (`O:E:main`).** The actual expression
`L_A = u^(p-1) A₀ (N(T) + u^(p-1) N(s))` has depth at least
`2(p-1)m + (p-1)δ - floor(t/p)`, which reaches the ideal conductor `1+t₂`.

The fixed coordinate is unchanged. Its order and twisted bounds are the
outputs of the accepted `twistedEstimates` constructor. The constructor
`exists_weighted_coordinate` below supplies these inputs from the genuine
local-field diamond, in both field characteristics. -/
theorem weighted {p : ℕ} (hp : p.Prime)
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
      let u : F := norm F B₂ Y
      let A₀ : F := norm F B₂ a
      let s : B₁ := -elementarySymmetric B₁ K (p - 1) Delta
      let T : B₁ := trace B₁ K ((algebraMap B₂ K Y * Delta) ^ (p - 1))
      let L_A : F := u ^ (p - 1) * A₀ *
        (norm F B₁ T + u ^ (p - 1) * norm F B₁ s)
      let d : ℤ := 2 * ((p : ℤ) - 1) * m + ((p : ℤ) - 1) * D.delta - (D.t : ℤ) / p
      L_A ∈ lattice F d ∧ 1 + (D.t₂ : ℤ) ≤ d := by
  dsimp only [OddTotalBreakData.B₁, OddTotalBreakData.B₂]
  let B₁ := IntermediateField.fixedField D.H₁
  let B₂ := IntermediateField.fixedField D.H₂
  letI := Basic.intermediateFieldValuativeRel B₁
  letI := Basic.intermediateFieldTopology B₁
  letI := Basic.intermediateFieldValuativeRel B₂
  letI := Basic.intermediateFieldTopology B₂
  obtain ⟨hLocal₁, hFreeF₁, hFiniteF₁, hFree₁K, hFinite₁K, hScalar₁,
      hValF₁, hVal₁K, _htotal, hdegreeLower₁, hdegreeUpper₁, hcycF₁, _hcyc₁K⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁
  letI := hLocal₁
  letI := hFreeF₁
  letI := hFiniteF₁
  letI := hFree₁K
  letI := hFinite₁K
  letI := hScalar₁
  letI := hValF₁
  letI := hVal₁K
  letI : PrimeCyclicExtension F B₁ :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F B₁ hcycF₁
  obtain ⟨hLocal₂, hFreeF₂, hFiniteF₂, hFree₂K, hFinite₂K, hScalar₂,
      hValF₂, hVal₂K, _htotal₂, _hdegreeLower₂, _hdegreeUpper₂, _hcycF₂, _hcyc₂K⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
  letI := hLocal₂
  letI := hFreeF₂
  letI := hFiniteF₂
  letI := hFree₂K
  letI := hFinite₂K
  letI := hScalar₂
  letI := hValF₂
  letI := hVal₂K
  have hresmul₁ := residue_degree_mul F B₁ K
  have hresmul₂ := residue_degree_mul F B₂ K
  rw [hres] at hresmul₁ hresmul₂
  have hresF₁ : residueDegree F B₁ = 1 := (mul_eq_one.mp hresmul₁).1
  have hres₁K : residueDegree B₁ K = 1 := (mul_eq_one.mp hresmul₁).2
  have hresF₂ : residueDegree F B₂ = 1 := (mul_eq_one.mp hresmul₂).1
  have hramF₁ : ramificationIndex F B₁ = p := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F B₁
    rw [hdegreeLower₁, hresF₁, mul_one] at h
    exact h.symm
  have hram₁K : ramificationIndex B₁ K = p := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree B₁ K
    rw [hdegreeUpper₁, hres₁K, mul_one] at h
    exact h.symm
  have hpcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by have := D.odd_prime; omega
  have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
  have hbreak₁ : PrimeCyclicExtension.IsLowerBreak F B₁ D.t := D.B₁_breaks.1
  intro Delta a hDelta ha htr hsym Y m hY hM
  let u : F := norm F B₂ Y
  let A₀ : F := norm F B₂ a
  let s : B₁ := -elementarySymmetric B₁ K (p - 1) Delta
  let T : B₁ := trace B₁ K ((algebraMap B₂ K Y * Delta) ^ (p - 1))
  let w : B₁ := algebraMap F B₁ (u ^ (p - 1) * A₀)
  let U : B₁ := algebraMap F B₁ (u ^ (p - 1))
  let L₁ : B₁ := w * (T ^ p + U * s ^ p)
  let L_A : F := u ^ (p - 1) * A₀ * (norm F B₁ T + u ^ (p - 1) * norm F B₁ s)
  let X : ℤ := 2 * ((p : ℤ) - 1) * m + ((p : ℤ) - 1) * D.delta
  let Q : ℤ := (p : ℤ) * X - D.t
  have hu : ord F u = (m : WithTop ℤ) := by rw [ord_norm, hresF₂, one_nsmul, hY]
  have hA₀ : ord F A₀ = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_norm, hresF₂, one_nsmul, ha]
  have hT : T ∈ lattice B₁ (((p : ℤ) - 1) * (m + D.delta)) := by
    have h := htr (Y ^ (p - 1)) (p - 1) (by omega)
    rw [ord_pow, hY, ← WithTop.coe_nsmul, ← WithTop.coe_add] at h
    rw [mem_lattice]
    convert h using 1
    · congr 1
      simp only [nsmul_eq_mul, hpcast, ht₂]
      ring
    · simp only [T, mul_pow, map_pow]
      rfl
  have hs : s ∈ lattice B₁ (((p : ℤ) - 1) * D.delta) := by
    have h := hsym 1 (p - 1) (by have := D.odd_prime; omega) (by omega)
    simp only [ord_one, nsmul_zero, add_zero, map_one, one_mul] at h
    rw [mem_lattice, ord_neg]
    convert h using 1
    congr 1
    rw [hpcast, ht₂]
    ring
  have hL₁ : L₁ ∈ lattice B₁ Q := by
    apply descend_lattice B₁ K hp.pos hram₁K
    have h := power hp hG hres D Delta a hDelta ha htr hsym Y m hY hM
    convert h using 1
    · congr 1
      dsimp only [Q, X]
      ring
    · rfl
  have hw : w ∈ lattice B₁ ((p : ℤ) * (((p : ℤ) - 1) * m - D.t)) := by
    rw [mem_lattice, ord_algebraMap, hramF₁, ord_mul, ord_pow, hu, hA₀,
      ← WithTop.coe_nsmul, ← WithTop.coe_add, ← WithTop.coe_nsmul]
    apply le_of_eq
    congr 1
    simp only [nsmul_eq_mul, hpcast]
    ring
  have hwU : w * U ∈ lattice B₁ ((p : ℤ) * (2 * ((p : ℤ) - 1) * m - D.t)) := by
    have hU : U ∈ lattice B₁ ((p : ℤ) * ((p : ℤ) - 1) * m) := by
      rw [mem_lattice, ord_algebraMap, hramF₁, ord_pow, hu,
        ← WithTop.coe_nsmul, ← WithTop.coe_nsmul]
      apply le_of_eq
      congr 1
      simp only [nsmul_eq_mul, hpcast]
      ring
    convert mul_mem_lattice B₁ hw hU using 1
    congr 1
    ring
  have herrorT : w * (T ^ p - algebraMap F B₁ (norm F B₁ T)) ∈ lattice B₁ Q := by
    convert mul_mem_lattice B₁ hw
      (power_norm_mem F B₁ hdegreeLower₁ D.odd_prime hbreak₁ D.t_pos hresF₁ hT) using 1
    congr 1
    dsimp only [Q, X]
    ring
  have herrorS : w * U * (s ^ p - algebraMap F B₁ (norm F B₁ s)) ∈ lattice B₁ Q := by
    convert mul_mem_lattice B₁ hwU
      (power_norm_mem F B₁ hdegreeLower₁ D.odd_prime hbreak₁ D.t_pos hresF₁ hs) using 1
    congr 1
    dsimp only [Q, X]
    ring
  have hLA : algebraMap F B₁ L_A ∈ lattice B₁ Q := by
    have h := (lattice B₁ Q).sub_mem ((lattice B₁ Q).sub_mem hL₁ herrorT) herrorS
    convert h using 1
    dsimp only [L₁, L_A, w, U]
    simp only [map_mul, map_add, map_pow]
    ring
  refine ⟨descend_lattice_floor F B₁ hp.pos hramF₁ hLA, ?_⟩
  rw [ht₂]
  exact conductor_le_weighted_depth D.odd_prime hM

/-- The fully weighted first terminal phase is trivial, retaining the
unit denominator and the rational factor `1/2`. Here `Psi` is the paper's
actual scaled additive character `x ↦ e_F(α x)`, with ideal conductor
`1+t₂`; FML records its conductor with the opposite sign. -/
theorem weighted_phase {p : ℕ} (hp : p.Prime)
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
      let u : F := norm F B₂ Y
      let A₀ : F := norm F B₂ a
      let s : B₁ := -elementarySymmetric B₁ K (p - 1) Delta
      let T : B₁ := trace B₁ K ((algebraMap B₂ K Y * Delta) ^ (p - 1))
      let L_A : F := u ^ (p - 1) * A₀ *
        (norm F B₁ T + u ^ (p - 1) * norm F B₁ s)
      ∀ (Psi : ContinuousAddChar F) (den : F),
        IsAdditiveConductor F Psi (-(1 + (D.t₂ : ℤ))) → ord F den = 0 →
        Psi (L_A / (2 * den ^ 2)) = 1 := by
  letI := Basic.intermediateFieldValuativeRel D.B₁
  letI := Basic.intermediateFieldTopology D.B₁
  letI := Basic.intermediateField_localField D.B₁
  letI := Basic.intermediateFieldValuativeRel D.B₂
  letI := Basic.intermediateFieldTopology D.B₂
  letI := Basic.intermediateField_localField D.B₂
  dsimp only
  intro Delta a hDelta ha htr hsym Y m hY hM Psi den hPsi hden
  obtain ⟨hweighted, hdepth⟩ := weighted hp hG hres D Delta a hDelta ha htr hsym Y m hY hM
  have hmem := lattice_antitone F hdepth hweighted
  have htwo : ord F (2 : F) = 0 :=
    ord_natCast_eq_zero_of_lt_residueCharacteristic F (j := 2) (by omega) (by
      rw [hchar]
      exact D.odd_prime)
  apply hPsi.trivial
  simpa only [mem_lattice, neg_neg, ord_div, ord_mul, ord_pow,
    htwo, hden, nsmul_zero, add_zero, sub_zero] using hmem

/-- Construct an actual Artin--Schreier coordinate satisfying the strong
weighted bound, uniformly in `Y`. The exact root, both orders, generation,
nondivisibility of the break, and trace--norm comparison are retained. -/
theorem exists_weighted_coordinate {p : ℕ} (hp : p.Prime)
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
      let u : F := norm F B₂ Y
      let A₀ : F := norm F B₂ a
      let s : B₁ := -elementarySymmetric B₁ K (p - 1) Delta
      let T : B₁ := trace B₁ K ((algebraMap B₂ K Y * Delta) ^ (p - 1))
      let L_A : F := u ^ (p - 1) * A₀ *
        (norm F B₁ T + u ^ (p - 1) * norm F B₁ s)
      let d : ℤ := 2 * ((p : ℤ) - 1) * m + ((p : ℤ) - 1) * D.delta - (D.t : ℤ) / p
      L_A ∈ lattice F d ∧ 1 + (D.t₂ : ℤ) ≤ d := by
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
    weighted hp hG hres D Delta a hDelta ha htr hsym⟩

end
end LanglandsSecondMainLemma.Odd.R1
