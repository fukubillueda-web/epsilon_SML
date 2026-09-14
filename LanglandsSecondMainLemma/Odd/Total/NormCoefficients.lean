import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Total.TwistedEstimates

/-!
# Odd / Total / Norm Coefficients

Paper Lemma `O:A:lem:bcoeff` (7.9). Expand the actual norm by its
characteristic polynomial, expand each symmetric coefficient in the exact
Artin--Schreier power basis, and reduce each monomial at most once using
`Delta ^ p = Delta + a`. The only low linear contribution is exactly
`-s₀`. Integer lattice depths retain negative bounds and infinite orders.
The constructor preserves all coordinate data and twisted estimates.
-/

namespace LanglandsSecondMainLemma.Odd.Total

open LanglandsFirstMainLemma
open scoped BigOperators

noncomputable section

private theorem coeff_pow
    {E L : Type*} [Field E] [Field L] [Algebra E L]
    (pb : PowerBasis E L) (n : ℕ) (hn : n < pb.dim) (l : Fin pb.dim) :
    pb.basis.repr (pb.gen ^ n) l = if (l : ℕ) = n then 1 else 0 := by
  rw [← pb.basis_eq_pow ⟨n, hn⟩, Module.Basis.repr_self]
  simp [Finsupp.single_apply, Fin.ext_iff, eq_comm]

private def coefficientDepth (p : ℕ) (t C : ℤ) (l : ℕ) : ℤ :=
  if l = 0 then C - t else if l = 1 then C else C - ((p : ℤ) - l) * t

private theorem coefficientDepth_le (p : ℕ) (hp : 1 ≤ p)
    (t C : ℤ) (ht : 0 ≤ t) (l : ℕ) :
    coefficientDepth p t C l ≤ C + ((l : ℤ) - 1) * t := by
  unfold coefficientDepth
  split_ifs with h0 h1
  · subst l; simp
  · subst l; simp
  · have hpZ : (1 : ℤ) ≤ p := by exact_mod_cast hp
    nlinarith

/-- Reduction of one monomial. The only contribution below the stated
linear precision is the constant coefficient of the last symmetric term. -/
private theorem reduced_monomial_mem
    {E L : Type*} [Field E] [Field L] [Algebra E L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    (pb : PowerBasis E L) {p : ℕ} (hp : 2 < p) (hdim : pb.dim = p)
    (a : E) (hroot : pb.gen ^ p - pb.gen = algebraMap E L a)
    (t C : ℤ) (ht : 0 ≤ t) (ha : a ∈ lattice E (-t))
    (i : ℕ) (hi : 1 ≤ i) (hip : i < p)
    (k l : Fin pb.dim) (z : E)
    (hz : z ∈ lattice E (C + ((k : ℕ) - (i : ℤ)) * t)) :
    z * (pb.basis.repr (pb.gen ^ ((k : ℕ) + p - i)) l -
      if i = p - 1 ∧ (k : ℕ) = 0 ∧ (l : ℕ) = 1 then 1 else 0) ∈
        lattice E (coefficientDepth p t C l) := by
  have hk : (k : ℕ) < p := by simpa [hdim] using k.isLt
  have hl : (l : ℕ) < p := by simpa [hdim] using l.isLt
  by_cases hn : (k : ℕ) + p - i < p
  · rw [coeff_pow pb _ (by omega)]
    by_cases heq : (l : ℕ) = (k : ℕ) + p - i
    · rw [if_pos heq]
      by_cases hlow : (l : ℕ) = 1
      · have hex : i = p - 1 ∧ (k : ℕ) = 0 ∧ (l : ℕ) = 1 := by omega
        simp [hex]
      · have hne : ¬ (i = p - 1 ∧ (k : ℕ) = 0 ∧ (l : ℕ) = 1) := by omega
        simp only [if_neg hne, sub_zero, mul_one]
        convert hz using 1
        unfold coefficientDepth
        rw [if_neg (by omega), if_neg hlow]
        have hrel : (k : ℤ) - i = (l : ℤ) - p := by omega
        rw [hrel]
        congr 1
        ring
    · have hne : ¬ (i = p - 1 ∧ (k : ℕ) = 0 ∧ (l : ℕ) = 1) := by omega
      simp [heq, hne]
  · have hki : i ≤ (k : ℕ) := by omega
    have hne : ¬ (i = p - 1 ∧ (k : ℕ) = 0 ∧ (l : ℕ) = 1) := by omega
    have hreduce : pb.gen ^ ((k : ℕ) + p - i) =
        pb.gen ^ ((k : ℕ) - i + 1) +
          algebraMap E L a * pb.gen ^ ((k : ℕ) - i) := by
      rw [show (k : ℕ) + p - i = p + ((k : ℕ) - i) by omega, pow_add,
        show pb.gen ^ p = pb.gen + algebraMap E L a by linear_combination hroot,
        add_mul, pow_succ]
      ring
    rw [hreduce, map_add, ← Algebra.smul_def, map_smul]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, if_neg hne, sub_zero]
    rw [coeff_pow pb _ (by omega), coeff_pow pb _ (by omega), mul_add]
    apply (lattice E _).add_mem
    · split_ifs with heq
      · simp only [mul_one]
        apply lattice_antitone E _ hz
        have hrel : (k : ℤ) - i = (l : ℤ) - 1 := by omega
        rw [hrel]
        exact coefficientDepth_le p (by omega) t C ht l
      · simp
    · split_ifs with heq
      · simp only [mul_one]
        apply lattice_antitone E _ (mul_mem_lattice E hz ha)
        have hrel : (k : ℤ) - i = (l : ℤ) := by omega
        rw [hrel]
        have hbound := coefficientDepth_le p (by omega) t C ht l
        nlinarith
      · simp

/-- The characteristic polynomial expresses the actual norm in odd degree. -/
theorem odd_norm_expansion
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    [Module.Free E L] [Module.Finite E L]
    {p : ℕ} (hp : Odd p) (hdegree : Module.finrank E L = p) (x : L) :
    algebraMap E L (norm E L x) = x ^ p +
      ∑ i ∈ Finset.Icc 1 (p - 1),
        (-1 : L) ^ i * algebraMap E L (elementarySymmetric E L i x) * x ^ (p - i) := by
  have hp0 : 0 < p := hp.pos
  let f := (Algebra.lmul E L x).charpoly
  have heval : Polynomial.eval₂ (algebraMap E L) x f = 0 :=
    Algebra.aeval_self_charpoly_lmul x
  have hcoeff (i : ℕ) (hi : i ≤ p) :
      algebraMap E L (f.coeff (p - i)) =
        (-1 : L) ^ i * algebraMap E L (elementarySymmetric E L i x) := by
    simp only [elementarySymmetric, hdegree, if_pos hi, map_mul, map_pow, map_neg, map_one]
    rw [← mul_assoc, ← pow_add, (Even.add_self i).neg_one_pow, one_mul]
  rw [Polynomial.eval₂_eq_sum_range' (algebraMap E L) (show f.natDegree < p + 1 by
    dsimp [f]; rw [LinearMap.charpoly_natDegree, hdegree]; omega)] at heval
  rw [← Finset.sum_range_reflect] at heval
  simp only [Nat.add_sub_cancel] at heval
  have heval' :
      (∑ i ∈ Finset.range (p + 1),
        (-1 : L) ^ i * algebraMap E L (elementarySymmetric E L i x) * x ^ (p - i)) = 0 := by
    convert heval using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcoeff i (by simpa using Finset.mem_range.mp hi)]
  rw [Finset.sum_range_succ, ← hdegree, elementarySymmetric_finrank, hdegree,
    hp.neg_one_pow, Nat.sub_self, pow_zero, mul_one, neg_one_mul] at heval'
  have hsplit :
      (∑ i ∈ Finset.range p,
        (-1 : L) ^ i * algebraMap E L (elementarySymmetric E L i x) * x ^ (p - i)) =
      x ^ p + ∑ i ∈ Finset.Icc 1 (p - 1),
        (-1 : L) ^ i * algebraMap E L (elementarySymmetric E L i x) * x ^ (p - i) := by
    have hs := Finset.sum_range_add_sum_Ico
      (fun i => (-1 : L) ^ i * algebraMap E L (elementarySymmetric E L i x) * x ^ (p - i))
      (m := 1) (n := p) hp0
    have hset : Finset.Ico 1 p = Finset.Icc 1 (p - 1) := by
      ext i
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    simpa [hset] using hs.symm
  rw [hsplit] at heval'
  linear_combination -heval'
/-- Coefficients of the norm remainder, with the low linear term removed
exactly. The two analytic inputs are the already proved extraction and
symmetric-coefficient bounds. -/
private theorem norm_remainder_mem
    (E₁ E₂ L : Type*) [Field E₁] [Field E₂] [Field L]
    [Algebra E₁ L] [Algebra E₂ L]
    [Module.Free E₁ L] [Module.Finite E₁ L]
    [ValuativeRel E₁] [TopologicalSpace E₁] [IsNonarchimedeanLocalField E₁]
    [ValuativeRel E₂] [TopologicalSpace E₂] [IsNonarchimedeanLocalField E₂]
    (pb : PowerBasis E₂ L) {p : ℕ} (hp : Odd p) (hp2 : 2 < p)
    (hdim : pb.dim = p) (hdegree : Module.finrank E₁ L = p)
    (a : E₂) (hroot : pb.gen ^ p - pb.gen = algebraMap E₂ L a)
    (t C : ℤ) (ht : 0 ≤ t) (ha : a ∈ lattice E₂ (-t))
    (hcoeff : ∀ (theta : E₁) (k : Fin pb.dim),
      ord E₁ theta + (((k : ℕ) * t : ℤ) : WithTop ℤ) ≤
        ord E₂ (pb.basis.repr (algebraMap E₁ L theta) k))
    (hei : ∀ i : ℕ, 1 ≤ i → i < p →
      ((C - (i : ℤ) * t : ℤ) : WithTop ℤ) ≤
        ord E₁ (elementarySymmetric E₁ L i pb.gen))
    (l : Fin pb.dim) :
    pb.basis.repr (algebraMap E₁ L (norm E₁ L pb.gen)) l -
      (if (l : ℕ) = 0 then a else 0) -
      (if (l : ℕ) = 1 then 1 +
        pb.basis.repr (algebraMap E₁ L (elementarySymmetric E₁ L (p - 1) pb.gen))
          ⟨0, by omega⟩ else 0) ∈
      lattice E₂ (coefficientDepth p t C l) := by
  let Z (i : ℕ) (k : Fin pb.dim) : E₂ :=
    (-1 : E₂) ^ i * pb.basis.repr
      (algebraMap E₁ L (elementarySymmetric E₁ L i pb.gen)) k
  have hZ (i : ℕ) (hi : i ∈ Finset.Icc 1 (p - 1)) (k : Fin pb.dim) :
      Z i k ∈ lattice E₂ (C + ((k : ℕ) - (i : ℤ)) * t) := by
    obtain ⟨hi, hip⟩ := Finset.mem_Icc.mp hi
    have h := (add_le_add_right (hei i hi (by omega))
      (((k : ℕ) * t : ℤ) : WithTop ℤ)).trans (by simpa only [add_comm] using hcoeff (elementarySymmetric E₁ L i pb.gen) k)
    rw [← WithTop.coe_add] at h
    rw [mem_lattice]
    simpa [add_comm, Z, show C + ((k : ℕ) - (i : ℤ)) * t = C - i * t + (k : ℕ) * t by ring] using h
  have hbound : (∑ i ∈ Finset.Icc 1 (p - 1), ∑ k : Fin pb.dim,
      Z i k * (pb.basis.repr (pb.gen ^ ((k : ℕ) + p - i)) l -
        if i = p - 1 ∧ (k : ℕ) = 0 ∧ (l : ℕ) = 1 then 1 else 0)) ∈
      lattice E₂ (coefficientDepth p t C l) := by
    apply sum_mem_lattice E₂
    intro i hi
    apply sum_mem_lattice E₂
    intro k hk
    have hi' := Finset.mem_Icc.mp hi
    exact reduced_monomial_mem pb hp2 hdim a hroot t C ht ha i hi'.1
      (by omega) k l (Z i k) (hZ i hi k)
  have hexp (i : ℕ) (hi : i ∈ Finset.Icc 1 (p - 1)) :
      (-1 : L) ^ i * algebraMap E₁ L (elementarySymmetric E₁ L i pb.gen) *
          pb.gen ^ (p - i) =
        ∑ k : Fin pb.dim, algebraMap E₂ L (Z i k) * pb.gen ^ ((k : ℕ) + p - i) := by
    have hs := pb.basis.sum_repr
      (algebraMap E₁ L (elementarySymmetric E₁ L i pb.gen))
    conv_lhs => rw [← hs]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hi' := Finset.mem_Icc.mp hi
    simp only [pb.basis_eq_pow, Algebra.smul_def, Z, map_mul, map_pow, map_neg, map_one]
    rw [show (k : ℕ) + p - i = (k : ℕ) + (p - i) by omega, pow_add]
    ring
  have hb := congrArg (fun x : L => pb.basis.repr x l)
    (odd_norm_expansion E₁ L hp hdegree pb.gen)
  rw [show pb.gen ^ p = pb.gen + algebraMap E₂ L a by linear_combination hroot,
    map_add, map_add, map_sum] at hb
  simp only [Finsupp.add_apply, Finsupp.finsetSum_apply] at hb
  have hconst : pb.basis.repr (algebraMap E₂ L a) l =
      if (l : ℕ) = 0 then a else 0 := by
    have h := coeff_pow pb 0 (by omega) l
    rw [pow_zero] at h
    rw [show algebraMap E₂ L a = a • (1 : L) by simp [Algebra.smul_def], map_smul]
    simp [h]
  rw [hconst, show pb.basis.repr pb.gen l = (if (l : ℕ) = 1 then 1 else 0) by
    simpa using coeff_pow pb 1 (by omega) l] at hb
  have hterms : (∑ i ∈ Finset.Icc 1 (p - 1),
      pb.basis.repr ((-1 : L) ^ i * algebraMap E₁ L (elementarySymmetric E₁ L i pb.gen) *
        pb.gen ^ (p - i)) l) =
      ∑ i ∈ Finset.Icc 1 (p - 1), ∑ k : Fin pb.dim,
        Z i k * pb.basis.repr (pb.gen ^ ((k : ℕ) + p - i)) l := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hexp i hi, map_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Algebra.smul_def, map_smul]
    rfl
  rw [hterms] at hb
  have hsign : (-1 : E₂) ^ (p - 1) = 1 := by
    apply Even.neg_one_pow
    obtain ⟨m, hm⟩ := hp
    exact ⟨m, by omega⟩
  have hlow : (∑ i ∈ Finset.Icc 1 (p - 1), ∑ k : Fin pb.dim,
      Z i k * (if i = p - 1 ∧ (k : ℕ) = 0 ∧ (l : ℕ) = 1 then 1 else 0)) =
      if (l : ℕ) = 1 then
        pb.basis.repr (algebraMap E₁ L (elementarySymmetric E₁ L (p - 1) pb.gen))
          ⟨0, by omega⟩ else 0 := by
    by_cases hl : (l : ℕ) = 1
    · simp only [hl, and_true, ite_true]
      rw [Finset.sum_eq_single (p - 1)]
      · simp only [true_and]
        rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin pb.dim)]
        · simp [Z, hsign]
        · intro k hk hne
          have hk0 : (k : ℕ) ≠ 0 := by simpa [Fin.ext_iff] using hne
          simp [hk0]
        · simp
      · intro i hi hne
        simp [hne]
      · simp [Finset.mem_Icc, show 1 ≤ p - 1 by omega]
    · simp [hl]
  simp_rw [mul_sub] at hbound
  simp_rw [Finset.sum_sub_distrib] at hbound
  rw [hlow] at hbound
  rw [hb]
  convert hbound using 1; split_ifs <;> ring

/-- Reindex the genuine basis expansion by the degree of the diamond. -/
private theorem norm_basis_expansion
    {E L : Type*} [Field E] [Field L] [Algebra E L]
    (pb : PowerBasis E L) {p : ℕ} (hdim : pb.dim = p) (x : L) :
    x = ∑ k : Fin p,
      algebraMap E L (pb.basis.repr x (Fin.cast hdim.symm k)) * pb.gen ^ (k : ℕ) := by
  let e : Fin p ≃ Fin pb.dim := (Fin.castOrderIso hdim.symm).toEquiv
  have h := pb.basis.sum_repr x
  rw [← e.sum_comp] at h
  refine h.symm.trans ?_
  apply Finset.sum_congr rfl
  intro k hk
  rw [pb.basis_eq_pow, Algebra.smul_def]
  rfl

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K]
variable [Module.Free F K] [Module.Finite F K] [IsGalois F K]

set_option maxHeartbeats 1600000 in
/-- Paper Lemma `O:A:lem:bcoeff` (7.9). The coefficients are constructed
from the actual norm `N₁ Delta` and `s = -e_{p-1}` in the same exact
Artin--Schreier coordinate supplied by `twistedEstimates`. Its entire
coordinate and estimate packet is retained for subsequent consumers.
In particular, the linear coefficient uses the actual constant coefficient
of `s`, and all three error depths are integers. -/
theorem normCoefficients {p : ℕ} (hp : p.Prime)
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
    ∃ (Delta : K) (a : B₂) (Y s : Fin p → B₂),
      Delta ^ p - Delta = algebraMap B₂ K a ∧
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ¬ p ∣ D.t ∧ Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ ∧
      (∀ (theta : B₁) (Z : Fin p → B₂),
        algebraMap B₁ K theta = ∑ r : Fin p, algebraMap B₂ K (Z r) * Delta ^ (r : ℕ) →
        ∀ r : Fin p, ord B₁ theta + ((((r : ℕ) * D.t : ℕ) : ℤ) : WithTop ℤ) ≤
          ord B₂ (Z r)) ∧
      (∀ (z : B₂) (i : ℕ), i < p →
        ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) + ord B₂ z ≤
          ord B₁ (trace B₁ K (algebraMap B₂ K z * Delta ^ i))) ∧
      (∀ (z : B₂) (i : ℕ), 1 ≤ i → i < p →
        ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) + i • ord B₂ z ≤
          ord B₁ (elementarySymmetric B₁ K i (algebraMap B₂ K z * Delta))) ∧
      (∀ i : ℕ, 1 ≤ i → i < p →
        ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) ≤
          ord B₁ (elementarySymmetric B₁ K i Delta)) ∧
      ((((p : ℤ) - 1) * D.delta : ℤ) : WithTop ℤ) ≤
        ord B₁ (-elementarySymmetric B₁ K (p - 1) Delta) ∧
      algebraMap B₁ K (norm B₁ K Delta) =
        ∑ l : Fin p, algebraMap B₂ K (Y l) * Delta ^ (l : ℕ) ∧
      algebraMap B₁ K (-elementarySymmetric B₁ K (p - 1) Delta) =
        ∑ l : Fin p, algebraMap B₂ K (s l) * Delta ^ (l : ℕ) ∧
      (∀ l : Fin p, 2 ≤ (l : ℕ) →
        ((((p : ℤ) - 1) * D.t₂ - ((p : ℤ) - (l : ℕ)) * D.t : ℤ) : WithTop ℤ) ≤
          ord B₂ (Y l)) ∧
      ((((p : ℤ) - 1) * D.t₂ - D.t : ℤ) : WithTop ℤ) ≤
        ord B₂ (Y ⟨0, hp.pos⟩ - a) ∧
      ∃ E : B₂, Y ⟨1, hp.one_lt⟩ = 1 - s ⟨0, hp.pos⟩ + E ∧
        ((((p : ℤ) - 1) * D.t₂ : ℤ) : WithTop ℤ) ≤ ord B₂ E := by
  dsimp only [OddTotalBreakData.B₁, OddTotalBreakData.B₂]
  let B₁ := IntermediateField.fixedField D.H₁
  let B₂ := IntermediateField.fixedField D.H₂
  letI := Basic.intermediateFieldValuativeRel B₁
  letI := Basic.intermediateFieldTopology B₁
  letI := Basic.intermediateFieldValuativeRel B₂
  letI := Basic.intermediateFieldTopology B₂
  obtain ⟨hLocal₁, hFreeF₁, hFiniteF₁, hFree₁K, hFinite₁K, hScalar₁,
      hValF₁, hVal₁K, _htotal₁, _hdegreeLower₁, hdegreeUpper₁,
      _hcycF₁, _hcyc₁K⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁
  letI := hLocal₁
  letI := hFree₁K
  letI := hFinite₁K
  obtain ⟨hLocal₂, hFreeF₂, hFiniteF₂, hFree₂K, hFinite₂K, hScalar₂,
      hValF₂, hVal₂K, _htotal₂, _hdegreeLower₂, hdegreeUpper₂,
      _hcycF₂, _hcyc₂K⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
  letI := hLocal₂
  letI := hFree₂K
  letI := hFinite₂K
  have hdata := twistedEstimates hp hG hres hchar D
  dsimp only [OddTotalBreakData.B₁, OddTotalBreakData.B₂] at hdata
  obtain ⟨Delta, a, hroot, hDelta, ha, hprime, hgen, hcoeff, htr, hsym, hei, hs⟩ := hdata
  let pb : PowerBasis B₂ K :=
    PowerBasis.ofAdjoinEqTop (IsAlgebraic.of_finite B₂ Delta).isIntegral hgen
  have hpbgen : pb.gen = Delta := PowerBasis.ofAdjoinEqTop_gen _ _
  have hpbdim : pb.dim = p := by rw [← pb.finrank]; exact hdegreeUpper₂
  let Z (theta : B₁) (k : Fin p) : B₂ :=
    pb.basis.repr (algebraMap B₁ K theta) (Fin.cast hpbdim.symm k)
  have hZexp (theta : B₁) : algebraMap B₁ K theta =
      ∑ k : Fin p, algebraMap B₂ K (Z theta k) * Delta ^ (k : ℕ) := by
    simpa only [Z, hpbgen] using norm_basis_expansion pb hpbdim (algebraMap B₁ K theta)
  have hZbound (theta : B₁) (k : Fin pb.dim) :
      ord B₁ theta + (((k : ℕ) * (D.t : ℤ) : ℤ) : WithTop ℤ) ≤
        ord B₂ (pb.basis.repr (algebraMap B₁ K theta) k) := by
    have h := hcoeff theta (Z theta) (hZexp theta) (Fin.cast hpbdim k)
    simpa only [Z, Fin.val_cast, Fin.cast_cast, Fin.cast_eq_self, Nat.cast_mul] using h
  let Y := Z (norm B₁ K Delta)
  let s := Z (-elementarySymmetric B₁ K (p - 1) Delta)
  have hrem (l : Fin p) :
      Y l - (if (l : ℕ) = 0 then a else 0) -
        (if (l : ℕ) = 1 then 1 - s ⟨0, hp.pos⟩ else 0) ∈
      lattice B₂ (coefficientDepth p D.t (((p : ℤ) - 1) * D.t₂) l) := by
    have h := norm_remainder_mem B₁ B₂ K pb (hp.odd_of_ne_two (by have := D.odd_prime; omega))
      D.odd_prime hpbdim hdegreeUpper₁ a (by simpa [hpbgen] using hroot)
      D.t (((p : ℤ) - 1) * D.t₂) (by positivity) (by rw [mem_lattice, ha])
      hZbound (by simpa only [hpbgen] using hei) (Fin.cast hpbdim.symm l)
    simp only [hpbgen, Fin.val_cast] at h
    convert h using 1
    simp only [Y, s, Z, Fin.cast_mk, map_neg, Finsupp.neg_apply, sub_neg_eq_add]
    congr 2
  refine ⟨Delta, a, Y, s, hroot, hDelta, ha, hprime, hgen, hcoeff,
    htr, hsym, hei, hs, hZexp _, hZexp _, ?_, ?_, ?_⟩
  · intro l hl
    have h := hrem l
    simpa [coefficientDepth, show (l : ℕ) ≠ 0 by omega,
      show (l : ℕ) ≠ 1 by omega, mem_lattice] using h
  · simpa [coefficientDepth, mem_lattice] using hrem ⟨0, hp.pos⟩
  · refine ⟨Y ⟨1, hp.one_lt⟩ - (1 - s ⟨0, hp.pos⟩), by ring, ?_⟩
    simpa [coefficientDepth, mem_lattice] using hrem ⟨1, hp.one_lt⟩

end
end LanglandsSecondMainLemma.Odd.Total
