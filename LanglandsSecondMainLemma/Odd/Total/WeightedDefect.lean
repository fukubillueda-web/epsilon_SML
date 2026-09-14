import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Total.FilteredCoefficients
import LanglandsSecondMainLemma.Odd.Total.PowerNorm
import Mathlib.FieldTheory.LinearDisjoint

/-!
# Odd / Total / Weighted Defect

Paper `O:A:thm:h` (7.8). The defect uses the actual upper norms and lower
traces. Its outer weight is the actual lower norm, and the congruence is
in the integer lattice of `B₁` at depth `p*t₂+R`.
-/

namespace LanglandsSecondMainLemma.Odd.Total

open LanglandsFirstMainLemma Polynomial
open scoped BigOperators

noncomputable section

/-- The weighted norm--trace defect of Paper `O:A:thm:h`, valued in the
base field. The coordinate multiplies the argument before either norm. -/
def weightedNormTraceDefect
    (F E₁ E₂ K : Type*) [Field F] [Field E₁] [Field E₂] [Field K]
    [Algebra F E₁] [Algebra F E₂] [Algebra E₁ K] [Algebra E₂ K]
    (Delta z : K) : F :=
  trace F E₁ (norm E₁ K (Delta * z)) - trace F E₂ (norm E₂ K (Delta * z))

private theorem weighted_power_mem
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {x : E} {q : ℤ}
    (hx : x ∈ lattice E q) (k : ℕ) : x ^ k ∈ lattice E ((k : ℤ) * q) := by
  rw [mem_lattice, ord_pow]
  simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using
    nsmul_le_nsmul_right ((mem_lattice E).1 hx) k

/-- Reindex a complete root sum using its monic root polynomial. This
avoids choosing an identification between residue fields. -/
private theorem weighted_sum_roots
    {I J E M : Type*} [Fintype I] [Fintype J] [Field E] [AddCommMonoid M]
    (c : I → E) (d : J → E)
    (h : (∏ i, (X - C (c i))) = ∏ j, (X - C (d j))) (f : E → M) :
    ∑ i, f (c i) = ∑ j, f (d j) := by
  have hs : Finset.univ.val.map c = Finset.univ.val.map d := by
    calc
      _ = ((Finset.univ.val.map c).map fun a => X - C a).prod.roots :=
        (roots_multiset_prod_X_sub_C _).symm
      _ = ((Finset.univ.val.map d).map fun a => X - C a).prod.roots := by
        simpa only [Multiset.map_map, Function.comp_def, Finset.prod] using
          congrArg Polynomial.roots h
      _ = _ := roots_multiset_prod_X_sub_C _
  have ht := congrArg (fun s : Multiset E => (s.map f).sum) hs
  simpa only [Multiset.map_map, Function.comp_def, Finset.sum] using ht

private theorem weighted_sum_zero_units
    {E M : Type*} [Field E] [Fintype E] [Fintype Eˣ] [AddCommMonoid M] (f : E → M) :
    ∑ x : E, f x = f 0 + ∑ u : Eˣ, f u := by
  classical
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ (0 : E))]
  congr 1
  apply Finset.sum_bij (fun x hx => Units.mk0 x (by simpa using hx))
  · intro x hx; exact Finset.mem_univ _
  · intro x hx y hy hxy; exact congrArg Units.val hxy
  · intro u hu
    exact ⟨u, by simp, by ext; rfl⟩
  · intro x hx; rfl

private theorem weighted_artinSchreier_norm
    {E K : Type*} [Field E] [Field K] [Algebra E K] [Module.Finite E K]
    {p : ℕ} (hp : 2 < p) (hodd : Odd p) (hdegree : Module.finrank E K = p)
    (Delta : K) (a : E) (hroot : Delta ^ p - Delta = algebraMap E K a)
    (hgen : Algebra.adjoin E ({Delta} : Set K) = ⊤) : norm E K Delta = a := by
  let P : E[X] := X ^ p - X - C a
  have hlow : (X + C a : E[X]).degree < (X ^ p : E[X]).degree := by
    rw [degree_X_pow]
    apply (degree_add_le _ _).trans_lt
    rw [max_lt_iff]
    constructor
    · simpa using (show (1 : WithBot ℕ) < (p : ℕ) by exact_mod_cast (by omega : 1 < p))
    · exact degree_C_le.trans_lt (by exact_mod_cast (by omega : 0 < p))
  have hPform : P = X ^ p - (X + C a) := by dsimp [P]; ring
  have hmonic : P.Monic := by rw [hPform]; exact (monic_X_pow p).sub_of_left hlow
  have hdegreeP : P.natDegree = p := by
    apply natDegree_eq_of_degree_eq_some
    rw [hPform, degree_sub_eq_left_of_degree_lt hlow, degree_X_pow]
  let pb := PowerBasis.ofAdjoinEqTop (IsAlgebraic.of_finite E Delta).isIntegral hgen
  have hpb : pb.gen = Delta := PowerBasis.ofAdjoinEqTop_gen _ _
  have hdim : pb.dim = p := by rw [← pb.finrank]; exact hdegree
  have hmin : P = minpoly E Delta := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic (IsAlgebraic.of_finite E Delta).isIntegral) hmonic
    · apply minpoly.dvd E Delta
      simp only [P, map_sub, map_pow, aeval_X, aeval_C, hroot, sub_self]
    · rw [hdegreeP, ← hpb, pb.natDegree_minpoly, hdim]
  rw [← hpb, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hdim, hpb, ← hmin]
  simp [P, hodd.neg_one_pow, show 0 ≠ p by omega]

/-- The power--norm error retains the factor `a^k`. After the lower trace
and the embedding in the other lower field its depth is `p*t₂+R`. -/
private theorem weighted_powerNorm_error
    (F E₁ E₂ : Type*) [Field F] [Field E₁] [Field E₂]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E₁] [TopologicalSpace E₁] [IsNonarchimedeanLocalField E₁]
    [ValuativeRel E₂] [TopologicalSpace E₂] [IsNonarchimedeanLocalField E₂]
    [Algebra F E₁] [ValuativeExtension F E₁] [Module.Finite F E₁]
    [Algebra F E₂] [ValuativeExtension F E₂] [Module.Finite F E₂]
    [PrimeCyclicExtension F E₂]
    {p t t₂ : ℕ} (hp : 2 < p) (ht : t ≤ t₂) (ht₂ : 0 < t₂)
    (hdegree : Module.finrank F E₂ = p) (hram : ramificationIndex F E₁ = p)
    (hres : residueDegree F E₂ = 1)
    (hbreak : PrimeCyclicExtension.IsLowerBreak F E₂ t₂)
    (x a : E₂) (v : ℤ) (hx : x ∈ lattice E₂ v)
    (ha : a ∈ lattice E₂ (-(t : ℤ))) (k : ℕ) :
    algebraMap F E₁ (trace F E₂ ((algebraMap F E₂ (norm F E₂ x) - x ^ p) * a ^ k)) ∈
      lattice E₁ ((p : ℤ) * t₂ + ((p : ℤ) * v - ((k : ℤ) - 1) * t)) := by
  have herr : algebraMap F E₂ (norm F E₂ x) - x ^ p ∈
      lattice E₂ ((p : ℤ) * v + ((p : ℤ) - 1) * t₂) := by
    have h := (add_le_add (nsmul_le_nsmul_right ((mem_lattice E₂).1 hx) p)
      (le_refl ((((p - 1) * t₂ : ℕ) : ℤ) : WithTop ℤ))).trans
        (powerNorm F E₂ p t₂ hdegree hp hbreak ht₂ hres x)
    rw [← WithTop.coe_nsmul, ← WithTop.coe_add] at h
    have hn := (lattice E₂ _).neg_mem ((mem_lattice E₂).2 h)
    simpa only [neg_sub, nsmul_eq_mul, Nat.cast_mul,
      Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] using hn
  have hy := mul_mem_lattice E₂ herr (weighted_power_mem E₂ ha k)
  let q : ℤ := (p : ℤ) * v + ((p : ℤ) - 1) * t₂ + (k : ℤ) * (-(t : ℤ))
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E₂ hres
  have htrace := traceIdealLowerBound_of_integralGenerator F E₂ hbreak hres pi hpi hgen
  have h := htrace q _ ((mem_lattice E₂).1 hy)
  rw [hdegree] at h
  have hs := nsmul_le_nsmul_right h p
  rw [← WithTop.coe_nsmul] at hs
  rw [mem_lattice, ord_algebraMap, hram]
  apply (WithTop.coe_le_coe.mpr ?_).trans hs
  simp only [nsmul_eq_mul]
  have hpZ : (0 : ℤ) < p := by omega
  let A : ℤ := q + (((p - 1) * (t₂ + 1) : ℕ) : ℤ)
  have hm := Int.emod_lt_of_pos A hpZ
  have he := Int.mul_ediv_add_emod A (p : ℤ)
  have hdeep : (p : ℤ) * t₂ + ((p : ℤ) * v - ((k : ℤ) - 1) * t) ≤
      q + ((p : ℤ) - 1) * t₂ := by
    have h₁ : (t : ℤ) ≤ t₂ := by exact_mod_cast ht
    have h₂ := mul_nonneg (show (0 : ℤ) ≤ (p : ℤ) - 3 by omega)
      (show (0 : ℤ) ≤ t₂ by positivity)
    dsimp only [q]
    nlinarith
  dsimp only [A] at hm he
  push_cast [Nat.cast_sub (by omega : 1 ≤ p)] at hm he ⊢
  nlinarith

private theorem weighted_teichmuller_sum
    (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] {p : ℕ} [Fact p.Prime]
    (hF : residueCharacteristic F = p) (hE : residueCharacteristic E = p)
    (f : E → E) :
    (∑ j : ZMod p, f (algebraMap F E (primeTeichmuller F p hF j))) =
      ∑ j : ZMod p, f (primeTeichmuller E p hE j) := by
  apply weighted_sum_roots
  have h₁ := congrArg
    (Polynomial.map ((algebraMap F E).comp ((ValuativeRel.valuation F).integer.subtype)))
    (primeTeichmullerPolynomial_sub F p hF)
  have h₂ := congrArg (Polynomial.map ((ValuativeRel.valuation E).integer.subtype))
    (primeTeichmullerPolynomial_sub E p hE)
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_pow, RingHom.comp_apply] at h₁ h₂
  exact h₁.trans h₂.symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- **Paper 7.8 (`O:A:thm:h`)**. A genuine totally ramified odd Galois
diamond supplies an exact Artin--Schreier coordinate and its weighted
norm--trace defect. For every `x : B₂` and `0 ≤ j ≤ p-1`, the error is in
`𝔭_{B₁}^{p*t₂+R}` for every integer `1 ≤ R ≤ v_K(x*Delta^j)`. Taking
`R=v_K(x*Delta^j)` gives exactly the paper's modulus; the lower-bound form
also covers zero inputs, whose valuation is infinity. The exceptional factor
is the complete lower norm times `1-s^p`, with `s=-E_{p-1}(Delta)`.
Both field characteristics are included. -/
theorem weightedDefect
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
      norm B₂ K Delta = a ∧
      ∀ (x : B₂) (j : ℕ) (R : ℤ), j ≤ p - 1 →
        (R : WithTop ℤ) ≤ ord K (algebraMap B₂ K x * Delta ^ j) → 1 ≤ R →
        algebraMap F B₁
          (weightedNormTraceDefect F B₁ B₂ K Delta (algebraMap B₂ K x * Delta ^ j)) -
          (if j = p - 2 then ((p : B₁) - 1) * algebraMap F B₁ (norm F B₂ x) *
            (1 - (-elementarySymmetric B₁ K (p - 1) Delta) ^ p) else 0) ∈
          lattice B₁ ((p : ℤ) * D.t₂ + R) := by
  classical
  dsimp only [OddTotalBreakData.B₁, OddTotalBreakData.B₂]
  letI : Fact p.Prime := ⟨hp⟩
  let B₁ := IntermediateField.fixedField D.H₁
  let B₂ := IntermediateField.fixedField D.H₂
  letI := Basic.intermediateFieldValuativeRel B₁
  letI := Basic.intermediateFieldTopology B₁
  letI := Basic.intermediateFieldValuativeRel B₂
  letI := Basic.intermediateFieldTopology B₂
  obtain ⟨hLocal₁, hFreeF₁, hFiniteF₁, hFree₁K, hFinite₁K, hScalar₁,
      hValF₁, hVal₁K, htotal₁, hdegreeLower₁, hdegreeUpper₁, hcycF₁, hcyc₁K⟩ :=
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
  letI : PrimeCyclicExtension B₁ K := PrimeCyclicExtension.ofCyclicPrimeExtension B₁ K hcyc₁K
  obtain ⟨hLocal₂, hFreeF₂, hFiniteF₂, hFree₂K, hFinite₂K, hScalar₂,
      hValF₂, hVal₂K, _htotal₂, hdegreeLower₂, hdegreeUpper₂, hcycF₂, hcyc₂K⟩ :=
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
  letI : PrimeCyclicExtension F B₂ := PrimeCyclicExtension.ofCyclicPrimeExtension F B₂ hcycF₂
  have hresmul (E : IntermediateField F K) :
      letI := Basic.intermediateFieldValuativeRel E
      letI := Basic.intermediateFieldTopology E
      letI := Basic.intermediateField_localField E
      letI := Basic.intermediateField_lowerValuativeExtension E
      letI := Basic.intermediateField_upperValuativeExtension E
      residueDegree F E * residueDegree E K = 1 := by
    letI := Basic.intermediateFieldValuativeRel E
    letI := Basic.intermediateFieldTopology E
    letI := Basic.intermediateField_localField E
    letI := Basic.intermediateField_lowerValuativeExtension E
    letI := Basic.intermediateField_upperValuativeExtension E
    letI : IsScalarTower (ringOfIntegers F) (ringOfIntegers E) (ringOfIntegers K) :=
      IsScalarTower.of_algebraMap_eq' (by
        ext x
        change algebraMap F K (x : F) = algebraMap E K (algebraMap F E (x : F))
        rw [← IsScalarTower.algebraMap_apply F E K])
    letI : IsLocalHom (algebraMap (ringOfIntegers F) (ringOfIntegers E)) := inferInstance
    letI : IsLocalHom (algebraMap (ringOfIntegers E) (ringOfIntegers K)) := inferInstance
    rw [← hres, residueDegree_eq_finrank_residueField, residueDegree_eq_finrank_residueField,
      residueDegree_eq_finrank_residueField]
    exact Module.finrank_mul_finrank (ResidueField F) (ResidueField E) (ResidueField K)
  have hresF₁ := (mul_eq_one.mp (hresmul B₁)).1
  have hresF₂ := (mul_eq_one.mp (hresmul B₂)).1
  have hres₁K := (mul_eq_one.mp (hresmul B₁)).2
  have hres₂K := (mul_eq_one.mp (hresmul B₂)).2
  have hramF₁ : ramificationIndex F B₁ = p := by
    simpa only [hresF₁, mul_one, hdegreeLower₁] using
      (finrank_eq_ramificationIndex_mul_residueDegree F B₁).symm
  have hram₁K : ramificationIndex B₁ K = p := by
    simpa only [hres₁K, mul_one, hdegreeUpper₁] using
      (finrank_eq_ramificationIndex_mul_residueDegree B₁ K).symm
  have hram₂K : ramificationIndex B₂ K = p := by
    simpa only [hres₂K, mul_one, hdegreeUpper₂] using
      (finrank_eq_ramificationIndex_mul_residueDegree B₂ K).symm
  have hchar₁ : residueCharacteristic B₁ = p :=
    (residueCharacteristic_extension_eq F B₁).trans hchar
  have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
  have hp3 := D.odd_prime
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hpval : (p : B₁) ∈ lattice B₁ (((p : ℤ) - 1) * D.t₂) := by
    by_cases hz : (p : B₁) = 0
    · simp [hz]
    obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff B₁).2 hz)
    have h := oddTotal_primeValuationBound hp hG hres D
    rw [show (p : K) = algebraMap B₁ K (p : B₁) by simp,
      ord_algebraMap, hram₁K, ← hv, ← WithTop.coe_nsmul, WithTop.coe_le_coe] at h
    push_cast [Nat.cast_sub hp.one_le] at h
    rw [mem_lattice, ← hv, WithTop.coe_le_coe]
    exact le_of_mul_le_mul_left (by simpa only [nsmul_eq_mul, mul_assoc] using h)
      (by omega : (0 : ℤ) < p)
  have hinf : B₁ ⊓ B₂ = ⊥ := by
    have hdvd := IntermediateField.finrank_dvd_of_le_right
      (show B₁ ⊓ B₂ ≤ B₁ from inf_le_left)
    rw [hdegreeLower₁] at hdvd
    rcases (Nat.dvd_prime hp).1 hdvd with hone | heq
    · exact IntermediateField.finrank_eq_one_iff.mp hone
    · exact (D.B₁_ne_B₂ ((IntermediateField.eq_of_le_of_finrank_eq inf_le_left
        (heq.trans hdegreeLower₁.symm)).symm.trans
          (IntermediateField.eq_of_le_of_finrank_eq inf_le_right
            (heq.trans hdegreeLower₂.symm)))).elim
  have hdis := IntermediateField.LinearDisjoint.of_inf_eq_bot hinf
  have hsup : B₁ ⊔ B₂ = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [hdis.finrank_sup, hdegreeLower₁, hdegreeLower₂]
    simpa using htotal₁.symm
  have hbreak₂ : PrimeCyclicExtension.IsLowerBreak F B₂ D.t₂ := by
    simpa only [B₂, Ramification.IntermediateBreakPair] using D.B₂_breaks.1
  have hdata := translatedNorm hp hG hres hchar D
  dsimp only [OddTotalBreakData.B₁, OddTotalBreakData.B₂] at hdata
  obtain ⟨Delta, a, hroot, hDelta, ha, hprime, hgen, _hcoeff, _htw, _hsym, hei, _hs,
    htranslate⟩ := hdata
  have hnorm := weighted_artinSchreier_norm hp3 hodd hdegreeUpper₂ Delta a hroot hgen
  refine ⟨Delta, a, hroot, hDelta, ha, hprime, hgen, hnorm, ?_⟩
  intro x j R hj hR hRpos
  by_cases hxne : x = 0
  · subst x
    simp [weightedNormTraceDefect]
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff B₂).2 hxne)
  have hx : x ∈ lattice B₂ v := (mem_lattice B₂).2 (le_of_eq hv)
  have hReq : R ≤ (p : ℤ) * v - (j : ℤ) * D.t := by
    rw [ord_mul, ord_algebraMap, hram₂K, ord_pow, hDelta, ← hv,
      ← WithTop.coe_nsmul, ← WithTop.coe_nsmul, ← WithTop.coe_add] at hR
    have h := WithTop.coe_le_coe.mp hR
    simp only [nsmul_eq_mul] at h
    linarith
  let r : ℤ := (p : ℤ) * v - (j : ℤ) * D.t
  apply lattice_antitone B₁ (show (p : ℤ) * D.t₂ + R ≤ (p : ℤ) * D.t₂ + r by
    dsimp only [r]; omega)
  have hrpos : 1 ≤ r := hRpos.trans hReq
  let k := j + 1
  have hk1 : 1 ≤ k := by dsimp [k]; omega
  have hk : k ≤ p := by dsimp [k]; omega
  have hdepth : (p : ℤ) * v - ((k : ℤ) - 1) * D.t = r := by
    dsimp only [k, r]; push_cast; ring
  let weight : B₁ := algebraMap F B₁ (norm F B₂ x)
  have hX : weight ∈ lattice B₁ (r + ((k : ℤ) - 1) * D.t) := by
    have hXd : r + ((k : ℤ) - 1) * D.t = (p : ℤ) * v := by linarith
    rw [hXd, mem_lattice, ord_algebraMap, hramF₁, ord_norm, hresF₂, one_nsmul]
    simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using
      nsmul_le_nsmul_right ((mem_lattice B₂).1 hx) p
  have hfiltered := filteredCoefficients B₁ K (by omega) hchar₁ hdegreeUpper₁ hram₁K
    Delta D.t D.delta r (by positivity) (by positivity) hDelta
    (by intro i hi hip; simpa only [mem_lattice, ← ht₂] using hei i hi hip)
    (by simpa only [← ht₂] using hpval) hk1 hk weight hX
  have hsum :
      (∑ z : ZMod p, norm B₁ K (Delta + algebraMap F K
        (primeTeichmuller F p hchar z : F)) ^ k) =
      norm B₁ K Delta ^ k + ∑ z : (ZMod p)ˣ, norm B₁ K
        (Delta + algebraMap B₁ K (primeTeichmuller B₁ p hchar₁ z)) ^ k := by
    have h := weighted_teichmuller_sum F B₁ hchar hchar₁
      (fun c => norm B₁ K (Delta + algebraMap B₁ K c) ^ k)
    simp only [← IsScalarTower.algebraMap_apply F B₁ K] at h
    rw [h, weighted_sum_zero_units]
    simp only [map_zero, Subring.coe_zero, add_zero]
  have htrace : trace B₁ K ((Delta ^ p - Delta) ^ k) =
      algebraMap F B₁ (trace F B₂ (a ^ k)) := by
    rw [hroot, ← map_pow]
    exact hdis.trace_algebraMap hsup _
  have htrans := htranslate x v k hx hk1 hk (by simpa only [hdepth] using hrpos)
  rw [hdepth, hsum] at htrans
  rw [← ht₂, htrace] at hfiltered
  have hmain : weight * (algebraMap F B₁ (trace F B₁ (norm B₁ K Delta ^ k)) -
      algebraMap F B₁ (trace F B₂ (a ^ k))) -
      (if k = p - 1 then ((p : B₁) - 1) * weight *
        (1 + elementarySymmetric B₁ K (p - 1) Delta ^ p) else 0) ∈
        lattice B₁ ((p : ℤ) * D.t₂ + r) := by
    convert (lattice B₁ _).add_mem htrans hfiltered using 1
    dsimp only [weight]
    ring
  have herr := weighted_powerNorm_error F B₁ B₂ hp3 D.t_le_t₂
    (lt_of_lt_of_le D.t_pos D.t_le_t₂) hdegreeLower₂ hramF₁ hresF₂ hbreak₂
    x a v hx ((mem_lattice B₂).2 ha.ge) k
  rw [hdepth] at herr
  have hnormcross : norm B₁ K (algebraMap B₂ K x) = weight := hdis.norm_algebraMap hsup x
  have hlin₁ : trace F B₁ (weight * norm B₁ K Delta ^ k) =
      norm F B₂ x * trace F B₁ (norm B₁ K Delta ^ k) := by
    simpa only [weight, Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self_apply] using
      (trace F B₁).map_smul (norm F B₂ x) (norm B₁ K Delta ^ k)
  have hlin₂ : trace F B₂ (algebraMap F B₂ (norm F B₂ x) * a ^ k) =
      norm F B₂ x * trace F B₂ (a ^ k) := by
    simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self_apply] using
      (trace F B₂).map_smul (norm F B₂ x) (a ^ k)
  have hdef : algebraMap F B₁
      (weightedNormTraceDefect F B₁ B₂ K Delta (algebraMap B₂ K x * Delta ^ j)) =
      weight * (algebraMap F B₁ (trace F B₁ (norm B₁ K Delta ^ k)) -
        algebraMap F B₁ (trace F B₂ (a ^ k))) +
      algebraMap F B₁ (trace F B₂ ((algebraMap F B₂ (norm F B₂ x) - x ^ p) * a ^ k)) := by
    have hz : Delta * (algebraMap B₂ K x * Delta ^ j) = algebraMap B₂ K x * Delta ^ k := by
      dsimp only [k]; rw [pow_succ]; ring
    dsimp only [weightedNormTraceDefect]
    simp only [hz, map_mul, map_pow, hnormcross,
      LanglandsFirstMainLemma.norm_algebraMap, hdegreeUpper₂, hnorm, hlin₁]
    simp only [sub_mul, map_sub, hlin₂, map_mul]
    dsimp only [weight]
    ring
  have hex : (k = p - 1) ↔ (j = p - 2) := by dsimp only [k]; omega
  have hsign : 1 + elementarySymmetric B₁ K (p - 1) Delta ^ p =
      1 - (-elementarySymmetric B₁ K (p - 1) Delta) ^ p := by
    rw [hodd.neg_pow]; ring
  rw [hdef]
  simp only [hex, hsign] at hmain
  convert (lattice B₁ _).add_mem hmain herr using 1
  dsimp only [weight]
  ring

end

end LanglandsSecondMainLemma.Odd.Total
