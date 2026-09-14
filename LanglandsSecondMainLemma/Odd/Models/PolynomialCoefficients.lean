import LanglandsFirstMainLemma.Cases.WildOdd.HigherSymmetricVanishing
import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Models.Domains
import LanglandsSecondMainLemma.Odd.NormLog
import LanglandsSecondMainLemma.Odd.Total.TwistedEstimates

/-!
# Coefficients of the stationary discrepancy polynomial

Paper `O:M:poly` and `O:M:polycoeff`. The coefficient estimates below distinguish
annihilation by the residue characteristic from membership in the trivial ideal.
Only the degree-`p` nonlinear correction is asserted to lie in that ideal.
-/

namespace LanglandsSecondMainLemma.Odd.Models

noncomputable section
open LanglandsFirstMainLemma Polynomial

section PolynomialLattices
variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

private theorem coeff_mul_mem (f g : E[X]) (a b : ℤ)
    (hf : ∀ n, f.coeff n ∈ lattice E a)
    (hg : ∀ n, g.coeff n ∈ lattice E b) (n : ℕ) :
    (f * g).coeff n ∈ lattice E (a + b) := by
  rw [coeff_mul]
  exact sum_mem_lattice E fun ij _ => mul_mem_lattice E (hf ij.1) (hg ij.2)

private theorem coeff_pow_mem (f : E[X]) (a : ℤ)
    (hf : ∀ n, f.coeff n ∈ lattice E a) (k n : ℕ) :
    (f ^ k).coeff n ∈ lattice E ((k : ℤ) * a) := by
  induction k generalizing n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul, coeff_one]
    split_ifs
    · rw [mem_lattice]; simp
    · exact (lattice E 0).zero_mem
  | succ k ih =>
    rw [pow_succ]
    have heq : ((k + 1 : ℕ) : ℤ) * a = (k : ℤ) * a + a := by push_cast; ring
    rw [heq]
    exact coeff_mul_mem E (f ^ k) f ((k : ℤ) * a) a ih hf n

/-- The vanishing constant coefficient excludes zero-weight factors. This
estimate only uses coefficients strictly below `p`, even at weight `p` once
there are at least two factors. -/
private theorem coeff_pow_weighted (f : E[X]) (q C : ℤ) (p : ℕ)
    (hzero : f.coeff 0 = 0)
    (hf : ∀ n, 0 < n → n < p → f.coeff n ∈ lattice E ((n : ℤ) * q + C))
    (k : ℕ) (hk : 0 < k) (n : ℕ) (hn : n < p ∨ (n ≤ p ∧ 2 ≤ k)) :
    (f ^ k).coeff n ∈ lattice E ((n : ℤ) * q + (k : ℤ) * C) := by
  induction k, hk using Nat.le_induction generalizing n with
  | base =>
    simp only [pow_one, Nat.cast_one, one_mul]
    by_cases hn0 : n = 0
    · simp [hn0, hzero]
    · exact hf n (by omega) (by omega)
  | succ k hk ih =>
    rw [pow_succ, coeff_mul]
    apply sum_mem_lattice E
    intro ij hij
    have hijsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    by_cases hi0 : ij.1 = 0
    · have hc0 : (f ^ k).coeff 0 = 0 := by
        rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, hzero,
          zero_pow (by omega)]
      simp [hi0, hc0]
    by_cases hj0 : ij.2 = 0
    · simp [hj0, hzero]
    have hi : ij.1 < p := by omega
    have hj : ij.2 < p := by omega
    have hh := mul_mem_lattice E (ih ij.1 (Or.inl hi)) (hf ij.2 (by omega) hj)
    have heq : (n : ℤ) * q + ((k + 1 : ℕ) : ℤ) * C =
        (ij.1 : ℤ) * q + (k : ℤ) * C + ((ij.2 : ℤ) * q + C) := by
      rw [← hijsum]
      push_cast
      ring
    rw [heq]
    exact hh

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem coeff_pow_one_eq_zero (f : E[X]) (hzero : f.coeff 0 = 0)
    (k : ℕ) (hk : 2 ≤ k) : (f ^ k).coeff 1 = 0 := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, pow_two, mul_assoc, coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have hijsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  by_cases hi : ij.1 = 0
  · simp [hi, hzero]
  · have hj : ij.2 = 0 := by omega
    simp [hj, hzero]

end PolynomialLattices

/-- The exact polynomial `1 - N(1-Zz)` on a finite extension. -/
def normArgumentPolynomial (E L : Type*) [Field E] [Field L] [Algebra E L]
    [Module.Free E L] [Module.Finite E L] (z : L) : E[X] :=
  ∑ n ∈ Finset.Icc 1 (Module.finrank E L),
    monomial n (-((-1 : E) ^ n * elementarySymmetric E L n z))

@[simp] theorem normArgumentPolynomial_coeff
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    [Module.Free E L] [Module.Finite E L] (z : L) (n : ℕ) :
    (normArgumentPolynomial E L z).coeff n =
      if 1 ≤ n ∧ n ≤ Module.finrank E L then
        -((-1 : E) ^ n * elementarySymmetric E L n z) else 0 := by
  classical
  simp only [normArgumentPolynomial, finsetSum_coeff, coeff_monomial]
  by_cases hn : 1 ≤ n ∧ n ≤ Module.finrank E L <;>
    simp [Finset.mem_Icc, hn]

@[simp] theorem normArgumentPolynomial_coeff_zero
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    [Module.Free E L] [Module.Finite E L] (z : L) :
    (normArgumentPolynomial E L z).coeff 0 = 0 := by simp

@[simp] theorem normArgumentPolynomial_coeff_one
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    [Module.Free E L] [Module.Finite E L] (z : L) :
    (normArgumentPolynomial E L z).coeff 1 = trace E L z := by
  simp [show 1 ≤ Module.finrank E L from Module.finrank_pos]

/-- Composition with the actual truncated logarithm from `Odd/TruncatedLog`. -/
def normLogPolynomial (E L : Type*) [Field E] [Field L] [Algebra E L]
    [Module.Free E L] [Module.Finite E L] (p : ℕ) (z : L) : E[X] :=
  (truncatedLogPolynomial E p).comp (normArgumentPolynomial E L z)

private theorem normLogPolynomial_expansion
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    [Module.Free E L] [Module.Finite E L] (p : ℕ) (z : L) :
    normLogPolynomial E L p z = normArgumentPolynomial E L z +
      ∑ j ∈ Finset.Ico 2 p, C (j : E)⁻¹ * normArgumentPolynomial E L z ^ j := by
  simp [normLogPolynomial, truncatedLogPolynomial, sum_comp, mul_comp]

@[simp] theorem normLogPolynomial_coeff_one
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Module.Free E L] [Module.Finite E L] (p : ℕ) (z : L) :
    (normLogPolynomial E L p z).coeff 1 = trace E L z := by
  rw [normLogPolynomial_expansion, coeff_add, normArgumentPolynomial_coeff_one]
  suffices (∑ j ∈ Finset.Ico 2 p,
      C (j : E)⁻¹ * normArgumentPolynomial E L z ^ j).coeff 1 = 0 by rw [this, add_zero]
  rw [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  rw [coeff_C_mul, coeff_pow_one_eq_zero E _ (by simp) j (Finset.mem_Ico.mp hj).1,
    mul_zero]

/-- Evaluation uses the field norm, with the scalar embedded into its actual
source field. -/
theorem normArgumentPolynomial_eval
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Module.Free E L] [Module.Finite E L] [IsGalois E L] (z : L) (s : E) :
    (normArgumentPolynomial E L z).eval s =
      1 - norm E L (1 - algebraMap E L s * z) := by
  classical
  have hsum (f : ℕ → E) :
      ∑ n ∈ Finset.Icc 1 (Module.finrank E L), f n =
        ∑ n ∈ Finset.range (Module.finrank E L), f (n + 1) := by
    simpa [Finset.Ico_add_one_right_eq_Icc, Nat.add_comm] using
      (Finset.sum_Ico_add f 0 (Module.finrank E L) 1).symm
  rw [normArgumentPolynomial, eval_finsetSum]
  simp only [eval_monomial]
  rw [hsum]
  have heq : 1 - algebraMap E L s * z = 1 + algebraMap E L (-s) * z := by simp [sub_eq_add_neg]
  rw [heq, norm_one_add_eq_one_add_sum_elementarySymmetric]
  simp only [elementarySymmetric_algebraMap_mul, sub_add_eq_sub_sub,
    sub_self, zero_sub, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [neg_pow s (n + 1)]
  ring

@[simp] theorem normLogPolynomial_eval
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Module.Free E L] [Module.Finite E L] [IsGalois E L] (p : ℕ) (z : L) (s : E) :
    (normLogPolynomial E L p z).eval s =
      truncatedLog p (1 - norm E L (1 - algebraMap E L s * z)) := by
  rw [normLogPolynomial, eval_comp, normArgumentPolynomial_eval, truncatedLog]

/-- Apply the actual weighted field trace to every coefficient. -/
def weightedTracePolynomial (F E : Type*) [Field F] [Field E] [Algebra F E]
    (c : E) (f : E[X]) : F[X] :=
  ∑ n ∈ f.support, monomial n (trace F E (c * f.coeff n))

@[simp] theorem weightedTracePolynomial_coeff
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    (c : E) (f : E[X]) (n : ℕ) :
    (weightedTracePolynomial F E c f).coeff n = trace F E (c * f.coeff n) := by
  classical
  simp only [weightedTracePolynomial, finsetSum_coeff, coeff_monomial]
  by_cases hn : n ∈ f.support
  · simp [hn]
  · simp [hn, notMem_support_iff.mp hn]

/-- Coefficientwise trace commutes with evaluation at an embedded base scalar. -/
theorem weightedTracePolynomial_eval
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    (c : E) (f : E[X]) (s : F) :
    (weightedTracePolynomial F E c f).eval s =
      trace F E (c * f.eval (algebraMap F E s)) := by
  classical
  rw [weightedTracePolynomial, eval_finsetSum, eval_eq_sum, Polynomial.sum,
    Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [eval_monomial]
  have hlin := (trace F E).map_smul (s ^ n) (c * f.coeff n)
  simp only [Algebra.smul_def, Algebra.algebraMap_self_apply, map_pow] at hlin
  calc
    trace F E (c * f.coeff n) * s ^ n = s ^ n * trace F E (c * f.coeff n) := mul_comm _ _
    _ = trace F E ((algebraMap F E s) ^ n * (c * f.coeff n)) := hlin.symm
    _ = trace F E (c * (f.coeff n * (algebraMap F E s) ^ n)) := by congr 1; ring

/-- Paper's exact discrepancy polynomial `F_z`, with both norms and traces
retaining their source and target fields. -/
def discrepancyPolynomial (F E₁ E₂ L : Type*)
    [Field F] [Field E₁] [Field E₂] [Field L]
    [Algebra F E₁] [Algebra F E₂] [Algebra E₁ L] [Algebra E₂ L]
    [Module.Free E₁ L] [Module.Finite E₁ L]
    [Module.Free E₂ L] [Module.Finite E₂ L]
    (p : ℕ) (b : E₁) (a : E₂) (z : L) : F[X] :=
  weightedTracePolynomial F E₁ b (normLogPolynomial E₁ L p z) -
    weightedTracePolynomial F E₂ a (normLogPolynomial E₂ L p z)

@[simp] theorem discrepancyPolynomial_coeff
    (F E₁ E₂ L : Type*)
    [Field F] [Field E₁] [Field E₂] [Field L]
    [Algebra F E₁] [Algebra F E₂] [Algebra E₁ L] [Algebra E₂ L]
    [Module.Free E₁ L] [Module.Finite E₁ L]
    [Module.Free E₂ L] [Module.Finite E₂ L]
    (p : ℕ) (b : E₁) (a : E₂) (z : L) (n : ℕ) :
    (discrepancyPolynomial F E₁ E₂ L p b a z).coeff n =
      trace F E₁ (b * (normLogPolynomial E₁ L p z).coeff n) -
        trace F E₂ (a * (normLogPolynomial E₂ L p z).coeff n) := by
  simp [discrepancyPolynomial]

@[simp] theorem normLogPolynomial_coeff_zero
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    [Module.Free E L] [Module.Finite E L] (p : ℕ) (z : L) :
    (normLogPolynomial E L p z).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, normLogPolynomial, eval_comp,
    ← coeff_zero_eq_eval_zero, normArgumentPolynomial_coeff_zero]
  simp only [truncatedLogPolynomial, eval_add, eval_X, eval_finsetSum, eval_mul,
    eval_C, eval_pow, zero_add]
  apply Finset.sum_eq_zero
  intro k hk
  rw [zero_pow (by have := (Finset.mem_Ico.mp hk).1; omega), mul_zero]

private theorem normLogPolynomial_natDegree_le
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    [Module.Free E L] [Module.Finite E L] {p : ℕ} (hp : 2 ≤ p)
    (hdegree : Module.finrank E L = p) (z : L) :
    (normLogPolynomial E L p z).natDegree ≤ p * (p - 1) := by
  have hnorm : (normArgumentPolynomial E L z).natDegree ≤ p := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro n hn
    simp [normArgumentPolynomial_coeff, hdegree, Nat.not_le.mpr hn]
  have hlog : (truncatedLogPolynomial E p).natDegree ≤ p - 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [truncatedLogPolynomial, coeff_add, finsetSum_coeff]
    have hn1 : n ≠ 1 := by omega
    rw [coeff_X, if_neg (Ne.symm hn1), zero_add]
    apply Finset.sum_eq_zero
    intro k hk
    rw [coeff_C_mul, coeff_X_pow, if_neg (by have := (Finset.mem_Ico.mp hk).2; omega), mul_zero]
  exact natDegree_comp_le.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul hlog hnorm)

section Discrepancy
variable (F E₁ E₂ L : Type*) [Field F] [Field E₁] [Field E₂] [Field L]
  [Algebra F E₁] [Algebra F E₂] [Algebra E₁ L] [Algebra E₂ L]
  [Module.Free E₁ L] [Module.Finite E₁ L]
  [Module.Free E₂ L] [Module.Finite E₂ L]

@[simp] theorem discrepancyPolynomial_coeff_zero (p : ℕ) (b : E₁) (a : E₂) (z : L) :
    (discrepancyPolynomial F E₁ E₂ L p b a z).coeff 0 = 0 := by simp

/-- The exact degree range used by the subsequent finite-field rigidity lemma. -/
theorem discrepancyPolynomial_degree {p : ℕ} (hp : 2 ≤ p)
    (hdegree₁ : Module.finrank E₁ L = p) (hdegree₂ : Module.finrank E₂ L = p)
    (b : E₁) (a : E₂) (z : L) :
    (discrepancyPolynomial F E₁ E₂ L p b a z).natDegree ≤ p * (p - 1) ∧
      p * (p - 1) < p ^ 2 := by
  constructor
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro n hn
    have h₁ := coeff_eq_zero_of_natDegree_lt
      ((normLogPolynomial_natDegree_le E₁ L hp hdegree₁ z).trans_lt hn)
    have h₂ := coeff_eq_zero_of_natDegree_lt
      ((normLogPolynomial_natDegree_le E₂ L hp hdegree₂ z).trans_lt hn)
    simp only [discrepancyPolynomial_coeff, h₁, h₂, mul_zero, map_zero, sub_zero]
  · have he : p - 1 + 1 = p := by omega
    nlinarith

variable [ValuativeRel E₁] [TopologicalSpace E₁] [IsNonarchimedeanLocalField E₁]
  [ValuativeRel E₂] [TopologicalSpace E₂] [IsNonarchimedeanLocalField E₂]
  [IsGalois E₁ L] [IsGalois E₂ L]
  [Algebra F L] [IsScalarTower F E₁ L] [IsScalarTower F E₂ L]

/-- Paper formula `O:M:poly`, before applying the continuous additive character. -/
theorem discrepancyPolynomial_eval (p : ℕ) (b : E₁) (a : E₂) (z : L) (s : F) :
    (discrepancyPolynomial F E₁ E₂ L p b a z).eval s =
      trace F E₁ (b * truncatedLog p (1 - norm E₁ L (1 - algebraMap F L s * z))) -
      trace F E₂ (a * truncatedLog p (1 - norm E₂ L (1 - algebraMap F L s * z))) := by
  simp only [discrepancyPolynomial, eval_sub, weightedTracePolynomial_eval,
    normLogPolynomial_eval, ← IsScalarTower.algebraMap_apply]

variable [TopologicalSpace F] [IsTopologicalRing F]
  [Module.Free F E₁] [Module.Finite F E₁] [IsModuleTopology F E₁]
  [Module.Free F E₂] [Module.Finite F E₂] [IsModuleTopology F E₂]

omit [Module.Free F E₁] [Module.Finite F E₁] [Module.Free F E₂] [Module.Finite F E₂] in
/-- On their norm domains, the constructed group characters evaluate to
exactly the phase of `F_z`. The norm-domain membership proofs are supplied
by `domains_original` (or `domains` after unramified base change). -/
theorem discrepancyPolynomial_character (p q₁ m₁ q₂ m₂ : ℕ)
    (Psi : ContinuousAddChar F) (b : E₁) (a : E₂)
    (M : OddMinimalCharacterModels E₁ E₂ p q₁ m₁ q₂ m₂
      (tracePullbackAddChar F E₁ Psi) (tracePullbackAddChar F E₂ Psi) b a)
    (u : Lˣ) (h₁ : normUnits E₁ L u ∈ unitFiltration E₁ q₁)
    (h₂ : normUnits E₂ L u ∈ unitFiltration E₂ q₂) :
    Psi ((discrepancyPolynomial F E₁ E₂ L p b a (1 - (u : L))).eval 1) =
      M.R₁ ⟨normUnits E₁ L u, h₁⟩ / M.R₂ ⟨normUnits E₂ L u, h₂⟩ := by
  rw [discrepancyPolynomial_eval, M.R₁_apply, M.R₂_apply]
  simp only [tracePullbackAddChar_apply, map_one, one_mul, sub_sub_cancel, coe_normUnits]
  exact AddChar.map_sub_eq_div Psi.toAddChar _ _

end Discrepancy

section CyclicEstimates
variable (E L : Type*) [Field E] [Field L]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra E L] [ValuativeExtension E L]
  [Module.Free E L] [Module.Finite E L] [PrimeCyclicExtension E L]

omit [Module.Free E L] [Module.Finite E L] [PrimeCyclicExtension E L] in
private theorem mapped_mem_of_floor {p : ℕ} (hp : 0 < p)
    (hram : ramificationIndex E L = p) (N : ℤ) (x : E)
    (hx : x ∈ lattice E ((N + (p - 1 : ℕ)) / p)) :
    algebraMap E L x ∈ lattice L N := by
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff E).2 hx0)
  rw [mem_lattice, ← hv, WithTop.coe_le_coe] at hx
  rw [mem_lattice, ord_algebraMap, hram, ← hv, ← WithTop.coe_nsmul,
    WithTop.coe_le_coe]
  simp only [nsmul_eq_mul]
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  have hr := Int.emod_lt_of_pos (N + (p - 1 : ℕ)) hpZ
  have hd := Int.ediv_mul_add_emod (N + (p - 1 : ℕ)) (p : ℤ)
  push_cast [Nat.cast_sub hp] at hx hr hd
  nlinarith

omit [Module.Free E L] [Module.Finite E L] [PrimeCyclicExtension E L] in
private theorem mem_of_mapped_mem {p : ℕ} (hp : 0 < p)
    (hram : ramificationIndex E L = p) (T : ℤ) (x : E)
    (hx : algebraMap E L x ∈ lattice L ((p : ℤ) * (T - 1) + 1)) :
    x ∈ lattice E T := by
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff E).2 hx0)
  rw [mem_lattice, ord_algebraMap, hram, ← hv, ← WithTop.coe_nsmul,
    WithTop.coe_le_coe] at hx
  simp only [nsmul_eq_mul] at hx
  rw [mem_lattice, ← hv, WithTop.coe_le_coe]
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  nlinarith

/-- Coefficientwise version of the norm-domain estimate, together with the
strong weighted bound needed for degree `p`. -/
theorem normArgumentPolynomial_bounds {p u q r : ℕ}
    (hdegree : Module.finrank E L = p)
    (hchar : residueCharacteristic E = p)
    (hres : residueDegree E L = 1)
    (hu : PrimeCyclicExtension.IsLowerBreak E L u) (hupos : 0 < u)
    (hrq : r ≤ q)
    (hfloor : r ≤ (q + (p - 1) * (u + 1)) / p)
    (z : L) (hz : z ∈ lattice L (q : ℤ)) :
    (∀ n, (normArgumentPolynomial E L z).coeff n ∈ lattice E (r : ℤ)) ∧
    (∀ n, 0 < n → n < p →
      algebraMap E L ((normArgumentPolynomial E L z).coeff n) ∈
        lattice L ((n : ℤ) * q + ((p : ℤ) - 1) * u)) := by
  have hp : 0 < p := hdegree ▸ Module.finrank_pos
  have hram : ramificationIndex E L = p := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree E L
    simpa [hdegree, hres] using h.symm
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer E L hres
  have htrace := traceIdealLowerBound_of_integralGenerator E L hu hres pi hpi hgen
  have hsym := wild_symmetric_bound E L u hu hupos
    (hchar.trans hdegree.symm) (hram.trans hdegree.symm) htrace (q : ℤ) hz
  have hbound (n : ℕ) (hn : 0 < n) (hnp : n < p) :
      (normArgumentPolynomial E L z).coeff n ∈
        lattice E (((n : ℤ) * q + ((p : ℤ) - 1) * (u + 1)) / p) := by
    have hh := hsym.1 hn (hdegree ▸ hnp)
    simp only [wildDifferentContribution, hdegree] at hh
    rw [normArgumentPolynomial_coeff, if_pos ⟨hn, hdegree ▸ hnp.le⟩,
      mem_lattice, ord_neg, ord_mul, ord_pow]
    simpa [ord_neg, Nat.cast_sub hp] using hh
  constructor
  · intro n
    by_cases hn : 1 ≤ n ∧ n ≤ p
    · by_cases hnp : n = p
      · subst n
        rw [normArgumentPolynomial_coeff, if_pos ⟨hp, hdegree ▸ le_rfl⟩]
        have hend := hsym.2.2
        rw [hdegree] at hend
        apply lattice_antitone E (Int.ofNat_le.mpr hrq)
        rw [mem_lattice, ord_neg, ord_mul, ord_pow]
        simpa [ord_neg] using hend
      · apply lattice_antitone E (n :=
          ((n : ℤ) * q + ((p : ℤ) - 1) * (u + 1)) / p) _ (hbound n hn.1 (by omega))
        have hfZ : (r : ℤ) ≤ ((q : ℤ) + ((p : ℤ) - 1) * (u + 1)) / p := by
          have hh : (r : ℤ) ≤ (((q + (p - 1) * (u + 1)) / p : ℕ) : ℤ) := by
            exact_mod_cast hfloor
          simpa [Nat.cast_sub hp, Int.natCast_div] using hh
        refine hfZ.trans (Int.ediv_le_ediv (by positivity) ?_)
        have hnZ : (1 : ℤ) ≤ n := by exact_mod_cast hn.1
        nlinarith [Int.natCast_nonneg q]
    · simp [normArgumentPolynomial_coeff, hdegree, hn]
  · intro n hn hnp
    apply mapped_mem_of_floor E L hp hram _ _
    have heq : ((n : ℤ) * q + ((p : ℤ) - 1) * u + (p - 1 : ℕ)) / p =
        ((n : ℤ) * q + ((p : ℤ) - 1) * (u + 1)) / p := by
      congr 1
      push_cast [Nat.cast_sub hp]
      ring
    rw [heq]
    exact hbound n hn hnp

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension E L] [PrimeCyclicExtension E L] in
private theorem normLogPolynomial_coeff_mem {p : ℕ}
    (hchar : residueCharacteristic E = p) (r : ℤ) (hr : 0 ≤ r)
    (z : L) (hf : ∀ n, (normArgumentPolynomial E L z).coeff n ∈ lattice E r)
    (n : ℕ) : (normLogPolynomial E L p z).coeff n ∈ lattice E r := by
  rw [normLogPolynomial_expansion, coeff_add, finsetSum_coeff]
  apply (lattice E r).add_mem (hf n)
  apply sum_mem_lattice E
  intro k hk
  have hk' := Finset.mem_Ico.mp hk
  have hinv : (k : E)⁻¹ ∈ lattice E 0 := by
    rw [mem_lattice, ord_inv,
      ord_natCast_eq_zero_of_lt_residueCharacteristic E (by omega) (hchar ▸ hk'.2)]
    simp
  rw [coeff_C_mul]
  apply lattice_antitone E (n := (k : ℤ) * r) (by
    have hkZ : (1 : ℤ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    nlinarith)
  simpa only [zero_add] using mul_mem_lattice E hinv (coeff_pow_mem E _ r hf k n)

omit [PrimeCyclicExtension E L] in
/-- The nonlinear correction at degree `p` is deep. The hypothesis `hdepth`
is an integer inequality, specialized to the paper's two breaks below. -/
private theorem normLogPolynomial_coeff_prime_sub_mem {p u q t T : ℕ}
    (hp : p.Prime) (hdegree : Module.finrank E L = p)
    (hchar : residueCharacteristic E = p) (hres : residueDegree E L = 1)
    (c : E) (hc : c ∈ lattice E (-(t : ℤ)))
    (z : L)
    (hf : ∀ n, 0 < n → n < p →
      algebraMap E L ((normArgumentPolynomial E L z).coeff n) ∈
        lattice L ((n : ℤ) * q + ((p : ℤ) - 1) * u))
    (hdepth : (p : ℤ) * ((T : ℤ) - 1) + 1 ≤
      (p : ℤ) * q + 2 * ((p : ℤ) - 1) * u - (p : ℤ) * t) :
    c * ((normLogPolynomial E L p z).coeff p -
      (normArgumentPolynomial E L z).coeff p) ∈ lattice E (T : ℤ) := by
  have hram : ramificationIndex E L = p := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree E L
    simpa [hdegree, hres] using h.symm
  rw [normLogPolynomial_expansion, coeff_add, add_sub_cancel_left,
    finsetSum_coeff, Finset.mul_sum]
  apply sum_mem_lattice E
  intro k hk
  have hk' := Finset.mem_Ico.mp hk
  apply mem_of_mapped_mem E L hp.pos hram
  rw [coeff_C_mul, map_mul, map_mul]
  have hcL : algebraMap E L c ∈ lattice L (-(p : ℤ) * t) := by
    rw [mem_lattice, ord_algebraMap, hram]
    have h := nsmul_le_nsmul_right ((mem_lattice E).mp hc) p
    convert h using 1
    rw [← WithTop.coe_nsmul]
    congr 1
    simp [mul_neg, neg_mul]
  have hinv : algebraMap E L (k : E)⁻¹ ∈ lattice L 0 := by
    rw [mem_lattice, ord_algebraMap, ord_inv,
      ord_natCast_eq_zero_of_lt_residueCharacteristic E (by omega) (hchar ▸ hk'.2)]
    simp
  have hpow := coeff_pow_weighted L ((normArgumentPolynomial E L z).map (algebraMap E L))
    (q : ℤ) (((p : ℤ) - 1) * u) p (by simp)
    (by simpa only [coeff_map] using hf) k (by omega) p (Or.inr ⟨le_rfl, hk'.1⟩)
  rw [← Polynomial.map_pow, coeff_map] at hpow
  have hh := mul_mem_lattice L hcL (mul_mem_lattice L hinv hpow)
  apply lattice_antitone L _ hh
  have hkZ : (2 : ℤ) ≤ k := by exact_mod_cast hk'.1
  have hC : 0 ≤ ((p : ℤ) - 1) * (u : ℤ) := mul_nonneg (by have := hp.one_le; omega) (by positivity)
  nlinarith

/-- One genuine cyclic edge: all coefficients are killed by `p` at the
specified additive depth, while only the degree-`p` remainder is deep itself. -/
private theorem cyclic_coefficients {p u q r t T : ℕ}
    (hp : p.Prime) (hodd : 2 < p) (hdegree : Module.finrank E L = p)
    (hchar : residueCharacteristic E = p) (hres : residueDegree E L = 1)
    (hu : PrimeCyclicExtension.IsLowerBreak E L u) (hupos : 0 < u)
    (hrq : r ≤ q) (hfloor : r ≤ (q + (p - 1) * (u + 1)) / p)
    (c : E) (hc : c ∈ lattice E (-(t : ℤ))) (v : ℤ)
    (hpval : (p : E) ∈ lattice E v) (hkill : (T : ℤ) ≤ v - t + r)
    (hdepth : (p : ℤ) * ((T : ℤ) - 1) + 1 ≤
      (p : ℤ) * q + 2 * ((p : ℤ) - 1) * u - (p : ℤ) * t)
    (z : L) (hz : z ∈ lattice L (q : ℤ)) :
    (∀ n, (p : E) * (c * (normLogPolynomial E L p z).coeff n) ∈ lattice E (T : ℤ)) ∧
    c * ((normLogPolynomial E L p z).coeff p - norm E L z) ∈ lattice E (T : ℤ) := by
  obtain ⟨hcoeff, hweighted⟩ := normArgumentPolynomial_bounds E L hdegree hchar hres
    hu hupos hrq hfloor z hz
  constructor
  · intro n
    have hh := mul_mem_lattice E hpval (mul_mem_lattice E hc
      (normLogPolynomial_coeff_mem E L hchar (r : ℤ) (by positivity) z hcoeff n))
    exact lattice_antitone E (by linarith) hh
  · have hendpoint : (normArgumentPolynomial E L z).coeff p = norm E L z := by
      rw [normArgumentPolynomial_coeff, if_pos ⟨hp.one_le, hdegree ▸ le_rfl⟩,
        (hp.odd_of_ne_two (by omega)).neg_one_pow]
      simp only [neg_one_mul, neg_neg]
      rw [← hdegree, elementarySymmetric_finrank]
    simpa only [hendpoint] using normLogPolynomial_coeff_prime_sub_mem E L hp
      hdegree hchar hres c hc z hweighted hdepth

end CyclicEstimates

private theorem trace_mem_from_break
    (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Free F E] [Module.Finite F E] [PrimeCyclicExtension F E]
    {p t : ℕ} (hdegree : Module.finrank F E = p)
    (hres : residueDegree F E = 1) (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (T κ : ℤ) (hT : T + ((p - 1 : ℕ) : ℤ) * (t + 1) = (p : ℤ) * κ)
    (x : E) (hx : x ∈ lattice E T) : trace F E x ∈ lattice F κ := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have hh := traceIdealLowerBound_of_integralGenerator F E ht hres pi hpi hgen T x hx
  have hp : (p : ℤ) ≠ 0 := by
    have hp0 : 0 < p := hdegree ▸ Module.finrank_pos
    exact_mod_cast hp0.ne'
  rw [mem_lattice]
  simpa only [hdegree, Nat.cast_mul, Nat.cast_add, Nat.cast_one, hT,
    Int.mul_ediv_cancel_left _ hp] using hh

/-- Integer arithmetic for the two native character depths. No negative
quantity is represented by natural-number subtraction. -/
private theorem coefficient_depths {p t δ q r : ℕ}
    (hp : 2 < p) (hq : 1 + t + (t + p * δ) ≤ p * q)
    (hr : 0 < r) :
    (t + p * δ + 1 : ℤ) ≤ ((p : ℤ) - 1) * (t + δ) - t + q ∧
    (t + δ + 1 : ℤ) ≤ ((p : ℤ) - 1) * (t + δ) - t + r ∧
    (p : ℤ) * ((t + p * δ + 1 : ℤ) - 1) + 1 ≤
      (p : ℤ) * q + 2 * ((p : ℤ) - 1) * (t + p * δ) - (p : ℤ) * t ∧
    (p : ℤ) * ((t + δ + 1 : ℤ) - 1) + 1 ≤
      (p : ℤ) * q + 2 * ((p : ℤ) - 1) * t - (p : ℤ) * t := by
  have hpZ : (3 : ℤ) ≤ p := by omega
  have hqZ : 1 + (t : ℤ) + (t + p * δ) ≤ (p : ℤ) * q := by exact_mod_cast hq
  have hqδ : (δ : ℤ) + 1 ≤ q := by nlinarith [Int.natCast_nonneg t]
  have hpt : 0 ≤ ((p : ℤ) - 3) * t := mul_nonneg (by omega) (by positivity)
  have hpδ : 0 ≤ ((p : ℤ) - 2) * δ := mul_nonneg (by omega) (by positivity)
  have hppδ : 0 ≤ (p : ℤ) * (((p : ℤ) - 1) * δ) :=
    mul_nonneg (by positivity) (mul_nonneg (by omega) (by positivity))
  constructor
  · nlinarith
  constructor
  · have hrZ : (1 : ℤ) ≤ r := by omega
    nlinarith
  constructor <;> nlinarith

section Diamond
variable {F K : Type*} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]

omit [Module.Free F K] in
private theorem norm_tower_residueDegrees (E : IntermediateField F K)
    (hres : residueDegree F K = 1) :
    letI := Basic.intermediateFieldValuativeRel E
    letI := Basic.intermediateFieldTopology E
    letI := Basic.intermediateField_localField E
    letI := Basic.intermediateField_lowerValuativeExtension E
    letI := Basic.intermediateField_upperValuativeExtension E
    residueDegree F E = 1 ∧ residueDegree E K = 1 := by
  letI := Basic.intermediateFieldValuativeRel E
  letI := Basic.intermediateFieldTopology E
  letI := Basic.intermediateField_localField E
  letI := Basic.intermediateField_lowerValuativeExtension E
  letI := Basic.intermediateField_upperValuativeExtension E
  obtain ⟨x, hx⟩ := exists_ord_eq K 1
  have h := congrArg (ord F) (norm_trans F E K x)
  rw [ord_norm, ord_norm, ord_norm, hx, hres] at h
  norm_cast at h
  simp only [nsmul_eq_mul, mul_one, Nat.cast_one] at h
  have hn : residueDegree F E * residueDegree E K = 1 := by exact_mod_cast h
  exact mul_eq_one.mp hn

set_option maxHeartbeats 1200000 in
/-- Paper Lemma `O:M:polycoeff` for the actual totally ramified diamond.

The coordinate can be the one constructed in `oddMinimalCharacters_onUnits`:
only its proved order is needed here. The additive character is arbitrary
with the paper's exact conductor, so it includes the chart of every actual
nontrivial norm character. All integral base scalars occur in the order bound.
The final assertion concerns degree `p` alone.
-/
theorem polynomialCoefficients {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (D : Total.OddTotalBreakData (F := F) (K := K) hp hG)
    (Delta : K) (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((D.t₂ + 1 : ℕ) : ℤ)))
    (z : K) (hz : z ∈ lattice K ((firstModelDepth D : ℕ) : ℤ)) :
    let B₁ := D.B₁
    let B₂ := D.B₂
    letI := Basic.intermediateFieldValuativeRel B₁
    letI := Basic.intermediateFieldTopology B₁
    letI := Basic.intermediateField_localField B₁
    letI := Basic.intermediateFieldValuativeRel B₂
    letI := Basic.intermediateFieldTopology B₂
    letI := Basic.intermediateField_localField B₂
    let f := discrepancyPolynomial F B₁ B₂ K p (norm B₁ K Delta) (norm B₂ K Delta) z
    (∀ (n : ℕ) (x : ringOfIntegers F), Psi (f.coeff n * (x : F)) ^ p = 1) ∧
    f.coeff 1 =
      trace F B₁ (norm B₁ K Delta * trace B₁ K z) -
        trace F B₂ (norm B₂ K Delta * trace B₂ K z) ∧
    f.coeff p - (trace F B₁ (norm B₁ K (Delta * z)) -
      trace F B₂ (norm B₂ K (Delta * z))) ∈ lattice F ((D.t₂ + 1 : ℕ) : ℤ) := by
  let B₁ := D.B₁
  let B₂ := D.B₂
  letI := Basic.intermediateFieldValuativeRel B₁
  letI := Basic.intermediateFieldTopology B₁
  letI := Basic.intermediateField_localField B₁
  letI := Basic.intermediateField_lowerValuativeExtension B₁
  letI := Basic.intermediateField_upperValuativeExtension B₁
  letI := Basic.intermediateFieldValuativeRel B₂
  letI := Basic.intermediateFieldTopology B₂
  letI := Basic.intermediateField_localField B₂
  letI := Basic.intermediateField_lowerValuativeExtension B₂
  letI := Basic.intermediateField_upperValuativeExtension B₂
  let E₁ := Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁
  let E₂ := Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
  letI : PrimeCyclicExtension F B₁ := PrimeCyclicExtension.ofCyclicPrimeExtension F B₁
    E₁.2.2.2.2.2.2.2.2.2.2.2.1
  letI : PrimeCyclicExtension B₁ K := PrimeCyclicExtension.ofCyclicPrimeExtension B₁ K
    E₁.2.2.2.2.2.2.2.2.2.2.2.2
  letI : PrimeCyclicExtension F B₂ := PrimeCyclicExtension.ofCyclicPrimeExtension F B₂
    E₂.2.2.2.2.2.2.2.2.2.2.2.1
  letI : PrimeCyclicExtension B₂ K := PrimeCyclicExtension.ofCyclicPrimeExtension B₂ K
    E₂.2.2.2.2.2.2.2.2.2.2.2.2
  have hd₁ : Module.finrank B₁ K = p := E₁.2.2.2.2.2.2.2.2.2.2.1
  have hd₂ : Module.finrank B₂ K = p := E₂.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hrF₁, hr₁⟩ := norm_tower_residueDegrees B₁ hres
  obtain ⟨hrF₂, hr₂⟩ := norm_tower_residueDegrees B₂ hres
  have hram₁ : ramificationIndex B₁ K = p := by
    simpa [hd₁, hr₁] using (finrank_eq_ramificationIndex_mul_residueDegree B₁ K).symm
  have hram₂ : ramificationIndex B₂ K = p := by
    simpa [hd₂, hr₂] using (finrank_eq_ramificationIndex_mul_residueDegree B₂ K).symm
  have hchar₁ : residueCharacteristic B₁ = p :=
    (residueCharacteristic_extension_eq F B₁).trans hchar
  have hchar₂ : residueCharacteristic B₂ = p :=
    (residueCharacteristic_extension_eq F B₂).trans hchar
  obtain ⟨hqpos, hrpos, hqu, _, hrq, hfloor₂, _, _⟩ := domains_original D hres
  have hfloor₁ : firstModelDepth D ≤
      (firstModelDepth D + (p - 1) * (D.tPrime + 1)) / p := by
    rw [Nat.le_div_iff_mul_le hp.pos]
    have he : p - 1 + 1 = p := by have := hp.pos; omega
    nlinarith
  have hq : 1 + D.t + (D.t + p * D.delta) ≤ p * firstModelDepth D := by
    simpa [firstModelDepth, firstModelConductor, D.tPrime_eq, smul_eq_mul] using
      (le_smul_ceilDiv (b := firstModelConductor D) hp.pos)
  obtain ⟨hkill₁, hkill₂, hdepth₁, hdepth₂⟩ :=
    coefficient_depths D.odd_prime hq hrpos
  have hb : norm B₁ K Delta ∈ lattice B₁ (-(D.t : ℤ)) := by
    rw [mem_lattice, ord_norm, hr₁, one_nsmul, hDelta]
  have ha : norm B₂ K Delta ∈ lattice B₂ (-(D.t : ℤ)) := by
    rw [mem_lattice, ord_norm, hr₂, one_nsmul, hDelta]
  have hpvalK : (p : K) ∈ lattice K ((p : ℤ) * (((p : ℤ) - 1) * D.t₂)) := by
    have h := Total.oddTotal_primeValuationBound hp hG hres D
    simpa only [mem_lattice, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one,
      mul_assoc] using h
  have hpval₁ : (p : B₁) ∈ lattice B₁ (((p : ℤ) - 1) * D.t₂) := by
    apply mem_of_mapped_mem B₁ K hp.pos hram₁
    simpa only [map_natCast] using lattice_antitone K (by have := hp.pos; nlinarith) hpvalK
  have hpval₂ : (p : B₂) ∈ lattice B₂ (((p : ℤ) - 1) * D.t₂) := by
    apply mem_of_mapped_mem B₂ K hp.pos hram₂
    simpa only [map_natCast] using lattice_antitone K (by have := hp.pos; nlinarith) hpvalK
  have hkill₁' : ((D.tPrime + 1 : ℕ) : ℤ) ≤
      ((p : ℤ) - 1) * D.t₂ - D.t + firstModelDepth D := by
    simpa only [D.tPrime_eq, D.t₂_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hkill₁
  have hkill₂' : ((D.t₂ + 1 : ℕ) : ℤ) ≤
      ((p : ℤ) - 1) * D.t₂ - D.t + secondModelDepth D := by
    simpa only [D.t₂_eq, Nat.cast_add, Nat.cast_one] using hkill₂
  have hdepth₁' : (p : ℤ) * (((D.tPrime + 1 : ℕ) : ℤ) - 1) + 1 ≤
      (p : ℤ) * firstModelDepth D + 2 * ((p : ℤ) - 1) * D.tPrime - (p : ℤ) * D.t := by
    simpa only [D.tPrime_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hdepth₁
  have hdepth₂' : (p : ℤ) * (((D.t₂ + 1 : ℕ) : ℤ) - 1) + 1 ≤
      (p : ℤ) * firstModelDepth D + 2 * ((p : ℤ) - 1) * D.t - (p : ℤ) * D.t := by
    simpa only [D.t₂_eq, Nat.cast_add, Nat.cast_one] using hdepth₂
  obtain ⟨hcoeff₁, hprime₁⟩ := cyclic_coefficients B₁ K hp D.odd_prime hd₁ hchar₁ hr₁
    D.B₁_breaks.2 (by rw [D.tPrime_eq]; exact Nat.add_pos_left D.t_pos _) le_rfl hfloor₁
    _ hb _ hpval₁ hkill₁' hdepth₁' z hz
  obtain ⟨hcoeff₂, hprime₂⟩ := cyclic_coefficients B₂ K hp D.odd_prime hd₂ hchar₂ hr₂
    D.B₂_breaks.2 D.t_pos hrq hfloor₂ _ ha _ hpval₂ hkill₂' hdepth₂' z hz
  have ht₁ : ∀ x : B₁, x ∈ lattice B₁ ((D.tPrime + 1 : ℕ) : ℤ) →
      trace F B₁ x ∈ lattice F ((D.t₂ + 1 : ℕ) : ℤ) :=
    trace_mem_from_break F B₁ D.degree_B₁ hrF₁ D.B₁_breaks.1 _ _ (by
      simp only [D.tPrime_eq, D.t₂_eq, Nat.cast_add, Nat.cast_mul,
        Nat.cast_sub hp.one_le, Nat.cast_one]
      ring)
  have ht₂ : ∀ x : B₂, x ∈ lattice B₂ ((D.t₂ + 1 : ℕ) : ℤ) →
      trace F B₂ x ∈ lattice F ((D.t₂ + 1 : ℕ) : ℤ) :=
    trace_mem_from_break F B₂ D.degree_B₂ hrF₂ D.B₂_breaks.1 _ _ (by
      simp only [Nat.cast_add, Nat.cast_sub hp.one_le, Nat.cast_one]
      ring)
  dsimp only
  constructor
  · intro n x
    have h₁ := ht₁ _ (hcoeff₁ n)
    have h₂ := ht₂ _ (hcoeff₂ n)
    simp only [← nsmul_eq_mul, map_nsmul] at h₁ h₂
    have hh := (lattice F ((D.t₂ + 1 : ℕ) : ℤ)).sub_mem h₁ h₂
    have hx : (x : F) ∈ lattice F 0 := (mem_lattice_zero_iff F).2 x.property
    have hmul := mul_mem_lattice F hh hx
    have htriv := hPsi.trivial
    rw [neg_neg] at htriv
    have hv := htriv _ (by
      simpa only [nsmul_eq_mul, ← mul_sub, mul_assoc, add_zero] using hmul)
    simpa only [discrepancyPolynomial_coeff, ← nsmul_eq_mul,
      ← ContinuousAddChar.toAddChar_apply, AddChar.map_nsmul_eq_pow] using hv
  constructor
  · simp only [discrepancyPolynomial_coeff, normLogPolynomial_coeff_one]
  · have hh := (lattice F ((D.t₂ + 1 : ℕ) : ℤ)).sub_mem (ht₁ _ hprime₁) (ht₂ _ hprime₂)
    simp only [mul_sub, map_sub] at hh
    convert hh using 1
    simp only [discrepancyPolynomial_coeff, map_mul]
    ring

end Diamond

end
end LanglandsSecondMainLemma.Odd.Models
