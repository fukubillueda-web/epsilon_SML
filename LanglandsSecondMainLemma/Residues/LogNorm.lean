import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.LocalField.Lattices
import LanglandsFirstMainLemma.LocalField.MonogenicUniformizer
import LanglandsFirstMainLemma.LocalField.Valuation
import LanglandsSecondMainLemma.Residues.FreeBasis
import LanglandsSecondMainLemma.Residues.TraceCompatibility

/-!
# Logarithmic differentiation of the field norm

Appendix B, Lemma B.5 (`B:dlog-norm`) of the corrected manuscript.
The algebraic calculation differentiates the multiplication determinant.
The derivative of the basis contributes a commutator, whose trace is zero.
The formal product and substitution rules identify the resulting derivations
with termwise Laurent differentiation. The accepted extension presentation and
differential trace then give the statement on the actual local fields.
-/

open scoped BigOperators
open Matrix
namespace LanglandsSecondMainLemma.Residues
noncomputable section

private theorem derivation_prod {R : Type*} [CommRing R]
    (D : Derivation ℤ R R) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → R) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, D (f i) * ∏ j ∈ s.erase i, f j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, D.leibniz, ih, Finset.sum_insert ha]
    simp only [smul_eq_mul, Finset.mul_sum, Finset.erase_insert ha]
    apply Eq.trans (by ring : _ = D (f a) * ∏ i ∈ s, f i +
      ∑ i ∈ s, f a * (D (f i) * ∏ j ∈ s.erase i, f j))
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.erase_insert_of_ne (ne_of_mem_of_not_mem hi ha).symm,
      Finset.prod_insert (by simp [ha])]
    ring

private theorem derivation_det {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (D : Derivation ℤ R R) (M : Matrix ι ι R) :
    D M.det = ∑ j, (M.updateCol j (fun i ↦ D (M i j))).det := by
  rw [Matrix.det_apply']
  simp only [map_sum, D.leibniz, D.map_intCast, smul_eq_mul, mul_zero, add_zero,
    derivation_prod, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ hσ
  congr 1
  have hup : (fun i ↦ M.updateCol j (fun i ↦ D (M i j)) (σ i) i) =
      Function.update (fun i ↦ M (σ i) i) j (D (M (σ j) j)) := by
    funext i
    by_cases h : i = j <;> simp [h]
  rw [hup, Finset.prod_update_of_mem (Finset.mem_univ j), Finset.sdiff_singleton_eq_erase]

private theorem sum_det_updateCol_mul {R ι : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] (M A : Matrix ι ι R) :
    (∑ j, (M.updateCol j (fun i ↦ (M * A) i j)).det) = M.det * A.trace := by
  have h j : (M.updateCol j (fun i ↦ (M * A) i j)).det = A j j * M.det := by
    convert Matrix.det_updateCol_sum M j (fun i ↦ A i j) using 1
      <;> simp only [smul_eq_mul]
    congr 1
    ext i k
    simp only [Matrix.updateCol_apply, Matrix.mul_apply]
    split_ifs <;> simp [mul_comm]
  simp_rw [h]
  rw [← Finset.sum_mul, Matrix.trace, mul_comm]
  rfl

/-- Differentiating the coordinate expansion also differentiates the basis.
`B` records that contribution; it must be retained before taking the trace. -/
private theorem derivation_leftMulMatrix {F E ι : Type*}
    [Field F] [Field E] [Algebra F E] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι F E) (d : Derivation ℤ F F) (D : Derivation ℤ E E)
    (hD : ∀ a, D (algebraMap F E a) = algebraMap F E (d a)) (v : E) :
    let B : Matrix ι ι F := fun i j ↦ b.repr (D (b j)) i
    let M := Algebra.leftMulMatrix b v
    M.map d + B * M = Algebra.leftMulMatrix b (D v) + M * B := by
  dsimp only
  ext i j
  have h := congrArg (fun x ↦ b.repr x i)
    (congrArg D (b.sum_repr (v * b j)))
  have hsmul (a : F) (x : E) : D (a • x) = a • D x + d a • x := by
    simp only [Algebra.smul_def, D.leibniz, hD, Algebra.algebraMap_self, RingHom.id_apply]
    ring
  simp only [map_sum, hsmul, D.leibniz, smul_eq_mul, map_add,
    map_smul, Finsupp.finsetSum_apply, Finsupp.add_apply, Finsupp.smul_apply,
    smul_eq_mul] at h
  have hs : (∑ x, ((b.repr (v * b j)) x * b.repr (D (b x)) i +
        d ((b.repr (v * b j)) x) * b.repr (b x) i)) =
      (∑ x, b.repr (D (b x)) i * b.repr (v * b j) x) +
        d (b.repr (v * b j) i) := by
    rw [Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro x hx
      ring
    · simp [Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
  rw [hs] at h
  change d (Algebra.leftMulMatrix b v i j) +
      (∑ x, b.repr (D (b x)) i * Algebra.leftMulMatrix b v x j) =
    Algebra.leftMulMatrix b (D v) i j +
      ∑ x, Algebra.leftMulMatrix b v i x * b.repr (D (b j)) x
  simp only [Algebra.leftMulMatrix_eq_repr_mul]
  have hm := congrFun (Algebra.leftMulMatrix_mulVec_repr b v (D (b j))) i
  simp only [Matrix.mulVec, dotProduct, Algebra.leftMulMatrix_eq_repr_mul] at hm
  rw [hm]
  simpa only [mul_comm (b j) (D v), add_comm] using h

/-- The logarithmic derivative of the determinant norm for compatible
field derivations. Compatibility will be constructed from Laurent coordinates. -/
private theorem logNorm_of_derivations {F E : Type*} [Field F] [Field E]
    [Algebra F E] [Module.Finite F E]
    (d : Derivation ℤ F F) (D : Derivation ℤ E E)
    (hD : ∀ a, D (algebraMap F E a) = algebraMap F E (d a))
    (v : E) (hv : v ≠ 0) :
    d (Algebra.norm F v) / Algebra.norm F v = Algebra.trace F E (D v / v) := by
  classical
  let b := Module.finBasis F E
  let M := Algebra.leftMulMatrix b v
  let N := Algebra.leftMulMatrix b v⁻¹
  let B : Matrix (Fin (Module.finrank F E))
      (Fin (Module.finrank F E)) F := fun i j ↦ b.repr (D (b j)) i
  have hMN : M * N = 1 := by
    dsimp only [N, M]
    rw [← map_mul, mul_inv_cancel₀ hv, map_one]
  have hdM : M.map d = M * (Algebra.leftMulMatrix b (D v / v) + B - N * B * M) := by
    have h := derivation_leftMulMatrix b d D hD v
    change M.map d + B * M = Algebra.leftMulMatrix b (D v) + M * B at h
    rw [Matrix.mul_sub, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hMN,
      Matrix.one_mul]
    have hmul : M * Algebra.leftMulMatrix b (D v / v) = Algebra.leftMulMatrix b (D v) := by
      rw [← map_mul]
      congr 1
      field_simp
    rw [hmul]
    exact eq_sub_of_add_eq h
  rw [Algebra.norm_eq_matrix_det b, derivation_det]
  change (∑ j, (M.updateCol j (fun i ↦ M.map d i j)).det) / M.det = _
  rw [hdM, sum_det_updateCol_mul]
  rw [Matrix.trace_sub, Matrix.trace_add]
  have htrace : (N * B * M).trace = B.trace := by
    rw [Matrix.trace_mul_cycle, hMN, Matrix.one_mul]
  rw [htrace, add_sub_cancel_right]
  rw [mul_div_cancel_left₀]
  · exact (Algebra.trace_eq_matrix_trace b _).symm
  · change (Algebra.leftMulMatrix b v).det ≠ 0
    rw [← Algebra.norm_eq_matrix_det b]
    exact (Algebra.norm_ne_zero_iff).mpr hv

open scoped PowerSeries LaurentSeries
open HahnSeries
set_option maxHeartbeats 500000

-- Use the canonical integer algebra for transport across ring equivalences.
-- The coefficientwise integer algebra on Laurent series is propositionally equal.
local instance (k : Type*) [Field k] : Algebra ℤ (LaurentSeries k) := Ring.toIntAlgebra _

private theorem laurentDerivative_coeff {k : Type*} [Field k]
    (f : LaurentSeries k) (n : ℤ) :
    (LaurentSeries.derivative k f).coeff n = (n + 1 : k) * f.coeff (n + 1) := by
  simp [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, zsmul_eq_mul]

private theorem laurentDerivative_coe {k : Type*} [Field k] (p : PowerSeries k) :
    LaurentSeries.derivative k (p : LaurentSeries k) =
      (PowerSeries.derivative k p : LaurentSeries k) := by
  ext i
  cases i with
  | ofNat n =>
      simp only [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
        Ring.choose_one_right]
      norm_num
      rw [PowerSeries.coeff_coe, if_neg (by omega)]
      have habs : (n + 1 : ℤ).natAbs = n + 1 := by omega
      rw [habs]
      simp [PowerSeries.coeff_derivative, mul_comm]
  | negSucc n =>
      cases n with
      | zero => simp [PowerSeries.coeff_coe]
      | succ n =>
          rw [laurentDerivative_coeff]
          rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe,
            if_pos (by omega), if_pos (by omega)]
          simp

private theorem laurentDerivative_single_mul {k : Type*} [Field k]
    (n : ℤ) (f : LaurentSeries k) :
    LaurentSeries.derivative k (single n 1 * f) =
      single n 1 * LaurentSeries.derivative k f + single (n - 1) (n : k) * f := by
  ext j
  simp only [laurentDerivative_coeff, coeff_single_mul, coeff_add, one_mul]
  rw [show j + 1 - n = j - n + 1 by omega,
    show j - (n - 1) = j - n + 1 by omega]
  push_cast
  ring

private theorem laurentDerivative_mul {k : Type*} [Field k]
    (f g : LaurentSeries k) :
    LaurentSeries.derivative k (f * g) =
      f * LaurentSeries.derivative k g + g * LaurentSeries.derivative k f := by
  let p := f.powerSeriesPart
  let q := g.powerSeriesPart
  have hf : single f.order 1 * (p : LaurentSeries k) = f := f.single_order_mul_powerSeriesPart
  have hg : single g.order 1 * (q : LaurentSeries k) = g := g.single_order_mul_powerSeriesPart
  have hfg : f * g = single (f.order + g.order) 1 * ((p * q : PowerSeries k) :
      LaurentSeries k) := by
    conv_lhs => rw [← hf, ← hg]
    rw [map_mul]
    have hm : (single (f.order + g.order) (1 : k) : LaurentSeries k) =
        single f.order 1 * single g.order 1 := by simp
    rw [hm]
    ring
  rw [hfg, laurentDerivative_single_mul, laurentDerivative_coe,
    Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
  conv_rhs => rw [← hf, ← hg]
  rw [laurentDerivative_single_mul, laurentDerivative_single_mul,
    laurentDerivative_coe, laurentDerivative_coe]
  have h1 : single (f.order + g.order) (1 : k) = single f.order 1 * single g.order 1 := by
    simp
  have h2 : single (f.order + g.order - 1) (f.order + g.order : k) =
      single f.order 1 * single (g.order - 1) (g.order : k) +
        single g.order 1 * single (f.order - 1) (f.order : k) := by
    simp only [single_mul_single, one_mul]
    rw [show f.order + (g.order - 1) = f.order + g.order - 1 by omega,
      show g.order + (f.order - 1) = f.order + g.order - 1 by omega, ← HahnSeries.single_add]
    congr 1
    ring
  rw [Int.cast_add, h1, h2, map_mul]
  ring

private theorem laurentDerivative_div {k : Type*} [Field k]
    (f g : LaurentSeries k) (hg : g ≠ 0) :
    LaurentSeries.derivative k (f / g) =
      (LaurentSeries.derivative k f - (f / g) * LaurentSeries.derivative k g) / g := by
  apply (eq_div_iff hg).2
  have h := laurentDerivative_mul (f / g) g
  rw [div_mul_cancel₀ _ hg] at h
  linear_combination -h

/-- Termwise Laurent differentiation, bundled with its product rule. -/
private def laurentDerivation (k : Type*) [Field k] :
    Derivation ℤ (LaurentSeries k) (LaurentSeries k) where
  toFun := LaurentSeries.derivative k (V := k)
  map_add' := map_add (LaurentSeries.derivative k)
  map_smul' n x := by
    have hn : algebraMap ℤ (LaurentSeries k) n = (n : LaurentSeries k) :=
      map_intCast (algebraMap ℤ (LaurentSeries k)) n
    rw [Algebra.smul_def, hn]
    simpa only [RingHom.id_apply, zsmul_eq_mul] using
      map_zsmul (LaurentSeries.derivative k (V := k)) n x
  map_one_eq_zero' := by
    change LaurentSeries.derivative k (1 : LaurentSeries k) = 0
    rw [← map_one (HahnSeries.ofPowerSeries ℤ k), laurentDerivative_coe]
    simp
  leibniz' f g := by
    change LaurentSeries.derivative k (f * g) =
      f * LaurentSeries.derivative k g + g * LaurentSeries.derivative k f
    exact laurentDerivative_mul f g

private theorem coe_powerSeries_orderTop_nonneg {k : Type*} [Field k]
    (f : PowerSeries k) : (0 : WithTop ℤ) ≤ (f : LaurentSeries k).orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro j hj
  rw [PowerSeries.coeff_coe, if_pos (WithTop.coe_lt_coe.mp hj)]

/-- Truncation determines maps into Laurent series when the variable has
positive order and every power-series image has nonnegative order. -/
private theorem powerSeries_hom_ext {k l : Type*} [Field k] [Field l]
    (f g : PowerSeries k →+* LaurentSeries l)
    (hC : ∀ a, f (PowerSeries.C a) = g (PowerSeries.C a))
    (hX : f PowerSeries.X = g PowerSeries.X)
    (hpos : (1 : WithTop ℤ) ≤ (f PowerSeries.X).orderTop)
    (hf : ∀ a, 0 ≤ (f a).orderTop) (hg : ∀ a, 0 ≤ (g a).orderTop) : f = g := by
  have hpoly : f.comp (algebraMap (Polynomial k) (PowerSeries k)) =
      g.comp (algebraMap (Polynomial k) (PowerSeries k)) := by
    apply Polynomial.ringHom_ext
    · intro a
      change f (Polynomial.C a : PowerSeries k) = g (Polynomial.C a : PowerSeries k)
      simpa only [Polynomial.coe_C] using hC a
    · change f ((Polynomial.X : Polynomial k) : PowerSeries k) = g ((Polynomial.X : Polynomial k) : PowerSeries k)
      simpa only [Polynomial.coe_X] using hX
  ext p j
  let n := j.natAbs + 1
  let q : PowerSeries k := PowerSeries.mk fun i ↦ PowerSeries.coeff (i + n) p
  have hp := PowerSeries.eq_X_pow_mul_shift_add_trunc n p
  change p = PowerSeries.X ^ n * q + (PowerSeries.trunc n p : PowerSeries k) at hp
  have horder (a : PowerSeries k →+* LaurentSeries l) (hax : a PowerSeries.X = f PowerSeries.X)
      (ha : ∀ b, 0 ≤ (a b).orderTop) :
      (j : WithTop ℤ) < (a (PowerSeries.X ^ n * q)).orderTop := by
    rw [map_mul, map_pow, hax, HahnSeries.orderTop_mul]
    have hpow : (n : WithTop ℤ) ≤ ((f PowerSeries.X) ^ n).orderTop := by
      calc
        (n : WithTop ℤ) = n • (1 : WithTop ℤ) := by simp
        _ ≤ n • (f PowerSeries.X).orderTop := nsmul_le_nsmul_right hpos n
        _ ≤ _ := HahnSeries.orderTop_nsmul_le_orderTop_pow
    have hn : (j : WithTop ℤ) < (n : WithTop ℤ) := by
      exact WithTop.coe_lt_coe.mpr (by dsimp [n]; have := Int.le_natAbs (a := j); omega)
    exact hn.trans_le (by simpa using add_le_add hpow (ha q))
  have hfc := HahnSeries.coeff_eq_zero_of_lt_orderTop (horder f rfl hf)
  have hgc := HahnSeries.coeff_eq_zero_of_lt_orderTop (horder g hX.symm hg)
  have hpc := DFunLike.congr_fun hpoly (PowerSeries.trunc n p)
  change f (PowerSeries.trunc n p : PowerSeries k) =
    g (PowerSeries.trunc n p : PowerSeries k) at hpc
  conv_lhs => rw [hp, map_add, HahnSeries.coeff_add, hfc, zero_add]
  conv_rhs => rw [hp, map_add, HahnSeries.coeff_add, hgc, zero_add]
  rw [hpc]

private theorem substitution_powerSeries {k l : Type*} [Field k] [Field l]
    (e : ℕ) (he : 0 < e) (i : k →+* l) (u : PowerSeries l)
    (hu : PowerSeries.HasSubst u) (φ : LaurentSeries k →+* LaurentSeries l)
    (hφ : IsLaurentSubstitution e i (u : LaurentSeries l) φ) (p : PowerSeries k) :
    φ (p : LaurentSeries k) =
      (PowerSeries.subst u (PowerSeries.map i p) : LaurentSeries l) := by
  let f := φ.comp (HahnSeries.ofPowerSeries ℤ k)
  let g := (HahnSeries.ofPowerSeries ℤ l).comp
    ((PowerSeries.substAlgHom hu).toRingHom.comp (PowerSeries.map i))
  have hfg : f = g := by
    apply powerSeries_hom_ext
    · intro a
      simp only [f, g, RingHom.comp_apply, PowerSeries.map_C]
      change φ (PowerSeries.C a : LaurentSeries k) =
        (HahnSeries.ofPowerSeries ℤ l) ((PowerSeries.substAlgHom hu) (PowerSeries.C (i a)))
      rw [PowerSeries.coe_substAlgHom, PowerSeries.subst_C]
      change φ (PowerSeries.C a : LaurentSeries k) =
        (PowerSeries.C (i a) : LaurentSeries l)
      simpa only [PowerSeries.coe_C] using hφ.1 a
    · simpa [f, g, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hu] using hφ.2.1
    · change (1 : WithTop ℤ) ≤ (φ ((PowerSeries.X : PowerSeries k) : LaurentSeries k)).orderTop
      rw [PowerSeries.coe_X, hφ.2.2, HahnSeries.orderTop_single one_ne_zero]
      simpa using (show (1 : WithTop ℤ) ≤ e from by exact_mod_cast he)
    · intro p
      change 0 ≤ (φ (p : LaurentSeries k)).orderTop
      rw [hφ.2.2]
      exact nsmul_nonneg (coe_powerSeries_orderTop_nonneg p) e
    · intro p
      exact coe_powerSeries_orderTop_nonneg _
  have h := DFunLike.congr_fun hfg p
  dsimp only [f, g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe] at h
  change φ (p : LaurentSeries k) =
    (HahnSeries.ofPowerSeries ℤ l) ((PowerSeries.substAlgHom hu) (PowerSeries.map i p)) at h
  rw [PowerSeries.coe_substAlgHom] at h
  exact h

private theorem powerSeries_derivative_map {k l : Type*} [Field k] [Field l]
    (i : k →+* l) (p : PowerSeries k) :
    PowerSeries.derivative l (PowerSeries.map i p) =
      PowerSeries.map i (PowerSeries.derivative k p) := by
  ext n
  simp [PowerSeries.coeff_derivative]

/-- The formal chain rule for the actual, order-continuous Laurent substitution. -/
private theorem laurentDerivative_substitution {k l : Type*} [Field k] [Field l]
    (e : ℕ) (he : 0 < e) (i : k →+* l) (u : PowerSeries l)
    (hu : PowerSeries.HasSubst u) (φ : LaurentSeries k →+* LaurentSeries l)
    (hφ : IsLaurentSubstitution e i (u : LaurentSeries l) φ) (x : LaurentSeries k) :
    LaurentSeries.derivative l (φ x) =
      φ (LaurentSeries.derivative k x) *
        (PowerSeries.derivative l u : LaurentSeries l) := by
  have hpower (p : PowerSeries k) :
      LaurentSeries.derivative l (φ (p : LaurentSeries k)) =
        φ (LaurentSeries.derivative k (p : LaurentSeries k)) *
          (PowerSeries.derivative l u : LaurentSeries l) := by
    rw [substitution_powerSeries e he i u hu φ hφ, laurentDerivative_coe,
      PowerSeries.derivative_subst l hu, powerSeries_derivative_map,
      laurentDerivative_coe, substitution_powerSeries e he i u hu φ hφ, map_mul]
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (PowerSeries k) x
  simp only [LaurentSeries.coe_algebraMap]
  rw [map_div₀]
  have hq' : (q : LaurentSeries k) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
  have hφq : φ (q : LaurentSeries k) ≠ 0 := (map_ne_zero φ).mpr hq'
  rw [laurentDerivative_div _ _ hφq, laurentDerivative_div _ _ hq', hpower p, hpower q,
    map_div₀, map_sub, map_mul, map_div₀]
  ring

private def transportDerivation {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (D : Derivation ℤ A A) : Derivation ℤ B B :=
  Derivation.liftOfRightInverse (f := e.toRingHom.toIntAlgHom)
    (f_inv := e.symm) e.apply_symm_apply (d := D)
    (by intro x hx; have : x = 0 := e.injective (by simpa using hx); simp [this])

open LanglandsFirstMainLemma

/-- Appendix B, Lemma B.5: the logarithmic derivative of the actual field norm
is the actual differential trace of `dv/v`. The Laurent presentations and the
nonzero `ds` needed to define the differential trace are constructed from the
finite separable extension. There is no tameness or restriction on its degree. -/
theorem logNorm
    (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Finite F E] [Algebra.IsSeparable F E]
    (hchar : ringChar F = ringChar (ResidueField F)) (v : Eˣ) :
    let P := Classical.choice (exists_equalCharacteristicExtensionPresentation F E hchar)
    LaurentSeries.derivative (ResidueField F)
        (P.base.laurentEquiv.symm (Algebra.norm F (v : E))) /
        P.base.laurentEquiv.symm (Algebra.norm F (v : E)) =
      differentialTrace F E hchar
        (LaurentSeries.derivative (ResidueField E)
            (P.extension.laurentEquiv.symm (v : E)) /
          P.extension.laurentEquiv.symm (v : E)) := by
  let P := Classical.choice (exists_equalCharacteristicExtensionPresentation F E hchar)
  let u := FreeBasis.parameter (ramificationIndex F E)
    P.uniformizerExpansion.powerSeriesPart
  let du : LaurentSeries (ResidueField E) :=
    (PowerSeries.derivative (ResidueField E) u : LaurentSeries (ResidueField E))
  letI : NeZero (ramificationIndex F E) := ⟨(ramificationIndex_pos F E).ne'⟩
  have hu : (u : LaurentSeries (ResidueField E)) = P.uniformizerExpansion := by
    have hne : P.uniformizerExpansion ≠ 0 := by
      rw [← HahnSeries.orderTop_ne_top, P.uniformizerExpansion_order]
      exact WithTop.coe_ne_top
    have hord : P.uniformizerExpansion.order = (ramificationIndex F E : ℤ) := by
      apply WithTop.coe_injective
      rw [HahnSeries.order_eq_orderTop_of_ne_zero hne, P.uniformizerExpansion_order]
      rfl
    dsimp only [u, FreeBasis.parameter]
    rw [map_mul, map_pow, PowerSeries.coe_X, ← RatFunc.single_one_eq_pow]
    simpa only [hord] using P.uniformizerExpansion.single_order_mul_powerSeriesPart
  have hdu : du ≠ 0 := by
    obtain ⟨x, hx⟩ := Algebra.trace_surjective F E (1 : F)
    have h := differentialTrace_onDs F E hchar x
    change differentialTrace F E hchar (P.extension.laurentEquiv.symm x * du) =
      P.base.laurentEquiv.symm (Algebra.trace F E x) at h
    intro hz
    rw [hz, mul_zero, hx, map_one] at h
    simp [differentialTrace] at h
  have hchain (x : LaurentSeries (ResidueField F)) :
      LaurentSeries.derivative (ResidueField E) (P.substitution x) =
        P.substitution (LaurentSeries.derivative (ResidueField F) x) * du := by
    apply laurentDerivative_substitution (ramificationIndex F E)
      (ramificationIndex_pos F E) (extensionResidueMap F E) u
      (FreeBasis.parameter_hasSubst _ _) P.substitution
    rw [hu]
    exact P.substitution_spec
  let d := transportDerivation P.base.laurentEquiv (laurentDerivation (ResidueField F))
  let D := transportDerivation P.extension.laurentEquiv
    (du⁻¹ • laurentDerivation (ResidueField E))
  have hd (x : F) : d x = P.base.laurentEquiv
      (LaurentSeries.derivative (ResidueField F) (P.base.laurentEquiv.symm x)) := rfl
  have hD (x : E) : D x = P.extension.laurentEquiv
      (du⁻¹ * LaurentSeries.derivative (ResidueField E) (P.extension.laurentEquiv.symm x)) := rfl
  have hcoords (a : F) : P.extension.laurentEquiv.symm (algebraMap F E a) =
      P.substitution (P.base.laurentEquiv.symm a) := by
    apply P.extension.laurentEquiv.injective
    simp only [RingEquiv.apply_symm_apply, P.algebraMap_coordinates_apply]
  have hcompat (a : F) : D (algebraMap F E a) = algebraMap F E (d a) := by
    rw [hD, hcoords, hchain, hd]
    rw [← P.algebraMap_coordinates_apply]
    congr 1
    rw [mul_left_comm, inv_mul_cancel₀ hdu, mul_one]
  have h := logNorm_of_derivations d D hcompat (v : E) v.ne_zero
  have h' := congrArg P.base.laurentEquiv.symm h
  rw [map_div₀, hd, RingEquiv.symm_apply_apply] at h'
  change LaurentSeries.derivative (ResidueField F)
      (P.base.laurentEquiv.symm (Algebra.norm F (v : E))) /
      P.base.laurentEquiv.symm (Algebra.norm F (v : E)) = _
  rw [h']
  dsimp only [differentialTrace]
  change P.base.laurentEquiv.symm (Algebra.trace F E (D (v : E) / (v : E))) =
    P.base.laurentEquiv.symm (Algebra.trace F E
      (P.extension.laurentEquiv
        ((LaurentSeries.derivative (ResidueField E) (P.extension.laurentEquiv.symm (v : E)) /
          P.extension.laurentEquiv.symm (v : E)) / du)))
  congr 2
  rw [hD]
  apply P.extension.laurentEquiv.symm.injective
  simp only [map_div₀, RingEquiv.symm_apply_apply]
  ring

end
end LanglandsSecondMainLemma.Residues
