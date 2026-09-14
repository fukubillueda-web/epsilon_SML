import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.LocalField.Lattices
import LanglandsFirstMainLemma.LocalField.MonogenicUniformizer
import LanglandsFirstMainLemma.LocalField.Valuation
import LanglandsSecondMainLemma.Residues.EqualCharacteristicPresentation
import LanglandsSecondMainLemma.Residues.TraceSubstitution
import LanglandsSecondMainLemma.Basic.NormTrace
import LanglandsSecondMainLemma.Local.Newton

/-!
# Residues / Trace Compatibility

This file proves Appendix B, Theorem B.4 of the corrected SML manuscript.
Compatible Laurent-series coordinates split an actual finite separable local
extension into its coefficient-field part and its ramified substitution part.
The first trace is computed coefficientwise and the second is handled by
`traceSubstitution`; transitivity then transports the identity back to the
actual local fields.
-/

namespace LanglandsSecondMainLemma.Residues

noncomputable section

open scoped PowerSeries LaurentSeries
open HahnSeries
open LanglandsFirstMainLemma

private noncomputable def coefficientwiseMap {k l : Type*} [Field k] [Field l]
    [Algebra k l] : LaurentSeries k →+* LaurentSeries l :=
  FreeBasis.mapLaurentSeries (algebraMap k l)

@[simp] private theorem mapLaurentSeries_coeff {k l : Type*} [Field k]
    [Field l] (f : k →+* l) (a : LaurentSeries k) (n : ℤ) :
    (FreeBasis.mapLaurentSeries f a).coeff n = f (a.coeff n) := rfl

private theorem coeff_sum {R : Type*} [AddCommMonoid R] [Fintype ι]
    (f : ι → HahnSeries ℤ R) (n : ℤ) :
    (∑ i, f i).coeff n = ∑ i, (f i).coeff n := by
  simpa only [HahnSeries.coeff.addMonoidHom_apply] using
    map_sum (HahnSeries.coeff.addMonoidHom n) f Finset.univ

private noncomputable def coefficientSeries {k l : Type*} [Field k]
    [Field l] [Algebra k l] (b : Module.Basis ι k l)
    (x : LaurentSeries l) (i : ι) : LaurentSeries k where
  coeff n := b.repr (x.coeff n) i
  isPWO_support' := x.isPWO_support.mono (by
    intro n hn
    change b.repr (x.coeff n) i ≠ 0 at hn
    rw [HahnSeries.mem_support]
    intro hzero
    apply hn
    rw [hzero, map_zero]
    rfl)

@[simp] private theorem coefficientSeries_coeff {k l : Type*} [Field k]
    [Field l] [Algebra k l] (b : Module.Basis ι k l)
    (x : LaurentSeries l) (i : ι) (n : ℤ) :
    (coefficientSeries b x i).coeff n = b.repr (x.coeff n) i := rfl

section Coefficientwise

variable {k l : Type*} [Field k] [Field l] [Algebra k l]

@[reducible] private noncomputable def coefficientwiseAlgebra :
    Algebra (LaurentSeries k) (LaurentSeries l) :=
  (coefficientwiseMap (k := k) (l := l)).toAlgebra

local instance : Algebra (LaurentSeries k) (LaurentSeries l) :=
  coefficientwiseAlgebra

@[simp] private theorem coefficientwise_algebraMap_apply (a : LaurentSeries k) :
    algebraMap (LaurentSeries k) (LaurentSeries l) a =
      FreeBasis.mapLaurentSeries (algebraMap k l) a := rfl

private theorem coefficient_basis_linearIndependent [Fintype ι]
    (b : Module.Basis ι k l) :
    LinearIndependent (LaurentSeries k)
      (fun i ↦ HahnSeries.C (b i) : ι → LaurentSeries l) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  apply HahnSeries.ext
  funext n
  have hn := congrArg (fun z : LaurentSeries l ↦ z.coeff n) hg
  simp only [Algebra.smul_def, HahnSeries.coeff_zero] at hn
  exact (Fintype.linearIndependent_iff.mp b.linearIndependent
    (fun j ↦ (g j).coeff n) (by simpa [Algebra.smul_def] using hn) i)

private theorem coefficient_basis_spans [Fintype ι]
    (b : Module.Basis ι k l) :
    ⊤ ≤ Submodule.span (LaurentSeries k)
      (Set.range (fun i ↦ HahnSeries.C (b i) : ι → LaurentSeries l)) := by
  intro x hx
  have hdecomp : x = ∑ i, coefficientSeries b x i •
      (HahnSeries.C (b i) : LaurentSeries l) := by
    apply HahnSeries.ext
    funext n
    rw [coeff_sum]
    simp only [Algebra.smul_def, coefficientwise_algebraMap_apply,
      mapLaurentSeries_coeff, HahnSeries.C_apply,
      HahnSeries.coeff_mul_single_zero, coefficientSeries_coeff]
    simpa only [Algebra.smul_def] using (b.sum_repr (x.coeff n)).symm
  rw [hdecomp]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact Submodule.subset_span (Set.mem_range_self i)

private noncomputable def coefficientBasis [Fintype ι]
    (b : Module.Basis ι k l) :
    Module.Basis ι (LaurentSeries k) (LaurentSeries l) :=
  Module.Basis.mk (coefficient_basis_linearIndependent b)
    (coefficient_basis_spans b)

@[simp] private theorem coefficientBasis_apply [Fintype ι]
    (b : Module.Basis ι k l) (i : ι) :
    coefficientBasis b i = (HahnSeries.C (b i) : LaurentSeries l) :=
  Module.Basis.mk_apply _ _ i

private theorem coefficientBasis_repr_coeff [Fintype ι]
    (b : Module.Basis ι k l) (x : LaurentSeries l) (i : ι) (n : ℤ) :
    ((coefficientBasis b).repr x i).coeff n =
      b.repr (x.coeff n) i := by
  have hn := congrArg (fun z : LaurentSeries l ↦ z.coeff n)
    ((coefficientBasis b).sum_repr x)
  rw [coeff_sum] at hn
  simp only [Algebra.smul_def, coefficientwise_algebraMap_apply,
    mapLaurentSeries_coeff, coefficientBasis_apply, HahnSeries.C_apply,
    HahnSeries.coeff_mul_single_zero] at hn
  have hn' : ∑ c, (((coefficientBasis b).repr x) c).coeff n • b c =
      x.coeff n := by
    simpa only [Algebra.smul_def] using hn
  have hsynth : b.equivFun.symm
      (fun c ↦ (((coefficientBasis b).repr x) c).coeff n) = x.coeff n := by
    rw [Module.Basis.equivFun_symm_apply]
    exact hn'
  have hfun := congrArg b.equivFun hsynth
  exact congrFun
    (by simpa only [LinearEquiv.apply_symm_apply,
      Module.Basis.equivFun_apply] using hfun) i

private theorem trace_coefficientwise [Fintype ι]
    (b : Module.Basis ι k l) (x : LaurentSeries l) (n : ℤ) :
    (Algebra.trace (LaurentSeries k) (LaurentSeries l) x).coeff n =
      Algebra.trace k l (x.coeff n) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (coefficientBasis b),
    Algebra.trace_eq_matrix_trace b]
  simp only [Matrix.trace]
  rw [coeff_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    coefficientBasis_repr_coeff, coefficientBasis_apply, Matrix.diag_apply,
    Algebra.leftMulMatrix_eq_repr_mul]
  simp only [HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero]

end Coefficientwise

private theorem laurent_order_zpow {K : Type*} [Field K]
    (x : LaurentSeries K) (hx : x ≠ 0) (n : ℤ) :
    (x ^ n).orderTop = n • x.orderTop := by
  have order_inv (y : LaurentSeries K) (hy : y ≠ 0) :
      y⁻¹.order = -y.order := by
    have hmul := HahnSeries.order_mul hy (inv_ne_zero hy)
    rw [mul_inv_cancel₀ hy, HahnSeries.order_one] at hmul
    omega
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero (zpow_ne_zero n hx),
    ← HahnSeries.order_eq_orderTop_of_ne_zero hx]
  cases n with
  | ofNat n =>
      change (↑(order (x ^ n)) : WithTop ℤ) =
        (n : ℤ) • (↑(order x) : WithTop ℤ)
      rw [HahnSeries.order_pow, natCast_zsmul, ← WithTop.coe_nsmul]
  | negSucc n =>
      rw [zpow_negSucc, order_inv _ (pow_ne_zero _ hx), HahnSeries.order_pow,
        negSucc_zsmul, ← WithTop.coe_nsmul,
        ← WithTop.LinearOrderedAddCommGroup.coe_neg]

private theorem coe_powerSeries_orderTop_eq_zero_of_isUnit
    {K : Type*} [Field K] (p : PowerSeries K) (hp : IsUnit p) :
    ((p : LaurentSeries K)).orderTop = 0 := by
  apply le_antisymm
  · apply HahnSeries.orderTop_le_of_coeff_ne_zero
    simpa [PowerSeries.coeff_coe] using
      (PowerSeries.isUnit_iff_constantCoeff.mp hp).ne_zero
  · rw [HahnSeries.le_orderTop_iff_forall]
    intro j hj
    rw [PowerSeries.coeff_coe, if_pos]
    exact WithTop.coe_lt_coe.mp hj

private theorem parameter_order {K : Type*} [Field K]
    (e : ℕ) [NeZero e] (v : PowerSeries K)
    (hv : IsUnit (PowerSeries.constantCoeff v)) :
    (FreeBasis.parameter e v).order = e := by
  rw [FreeBasis.parameter, PowerSeries.order_mul, PowerSeries.order_X_pow]
  rw [PowerSeries.order_zero_of_unit
    (PowerSeries.isUnit_iff_constantCoeff.mpr hv)]
  simp

private theorem formalSubstitution_orderTop {K : Type*} [Field K]
    (e : ℕ) [NeZero e] (v : PowerSeries K)
    (hv : IsUnit (PowerSeries.constantCoeff v)) (H : LaurentSeries K) :
    (formalSubstitution (FreeBasis.parameter e v) e (NeZero.pos e)
      (parameter_order e v hv) H).orderTop = e • H.orderTop := by
  let u := FreeBasis.parameter e v
  let φ := formalSubstitution u e (NeZero.pos e) (parameter_order e v hv)
  by_cases hH : H = 0
  · rw [hH, map_zero, HahnSeries.orderTop_zero]
    have he : 0 < e := NeZero.pos e
    rw [show e = (e - 1) + 1 by omega, add_nsmul, one_nsmul, add_top]
  have hpart : IsUnit H.powerSeriesPart := by
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero,
      ← PowerSeries.coeff_zero_eq_constantCoeff,
      LaurentSeries.powerSeriesPart_coeff]
    simpa only [Int.ofNat_eq_natCast, Nat.cast_zero, add_zero,
      HahnSeries.leadingCoeff_eq] using
        HahnSeries.leadingCoeff_ne_zero.mpr hH
  have hu_ne : u ≠ 0 := by
    apply PowerSeries.order_eq_top.not.mp
    rw [show u = FreeBasis.parameter e v from rfl, parameter_order e v hv]
    exact ENat.coe_ne_top e
  have huOrderTop : ((u : PowerSeries K) : LaurentSeries K).orderTop =
      ((e : ℤ) : WithTop ℤ) := by
    rw [show u = PowerSeries.X ^ e * v by rfl, map_mul,
      HahnSeries.orderTop_mul,
      coe_powerSeries_orderTop_eq_zero_of_isUnit v
        (PowerSeries.isUnit_iff_constantCoeff.mpr hv), add_zero,
      map_pow, PowerSeries.coe_X, ← RatFunc.single_one_eq_pow,
      HahnSeries.orderTop_single one_ne_zero]
  have hsubstPart : IsUnit (PowerSeries.subst u H.powerSeriesPart) := by
    dsimp only [u]
    rw [← PowerSeries.coe_substAlgHom]
    exact hpart.map (PowerSeries.substAlgHom
      (FreeBasis.parameter_hasSubst e v)).toRingHom
  have hφX : φ (HahnSeries.single 1 1) = (u : LaurentSeries K) := by
    rw [← PowerSeries.coe_X]
    dsimp only [φ]
    rw [formalSubstitution_coe,
      PowerSeries.subst_X (FreeBasis.parameter_hasSubst e v)]
  have hdecomp : φ H = ((u : PowerSeries K) : LaurentSeries K) ^ H.order *
      ((PowerSeries.subst u H.powerSeriesPart : PowerSeries K) :
        LaurentSeries K) := by
    calc
      φ H = φ ((HahnSeries.single H.order 1 : LaurentSeries K) *
          (H.powerSeriesPart : LaurentSeries K)) := by
        rw [LaurentSeries.single_order_mul_powerSeriesPart]
      _ = φ (HahnSeries.single H.order 1 : LaurentSeries K) *
          φ (H.powerSeriesPart : LaurentSeries K) := map_mul φ _ _
      _ = _ := by
        rw [show (HahnSeries.single H.order 1 : LaurentSeries K) =
          (HahnSeries.single 1 1 : LaurentSeries K) ^ H.order from
            RatFunc.single_zpow H.order,
          map_zpow₀, hφX]
        dsimp only [φ]
        rw [formalSubstitution_coe]
  rw [hdecomp, HahnSeries.orderTop_mul,
    laurent_order_zpow _ ((map_ne_zero_iff
      (HahnSeries.ofPowerSeries ℤ K)
        HahnSeries.ofPowerSeries_injective).2 hu_ne),
    huOrderTop, coe_powerSeries_orderTop_eq_zero_of_isUnit _ hsubstPart,
    add_zero, ← HahnSeries.order_eq_orderTop_of_ne_zero hH]
  cases H.order with
  | ofNat n =>
      change (n : ℤ) • (((e : ℤ) : WithTop ℤ)) =
        e • (((n : ℤ) : WithTop ℤ))
      rw [natCast_zsmul, ← WithTop.coe_nsmul ((e : ℤ)) n,
        ← WithTop.coe_nsmul ((n : ℤ)) e]
      congr 1
      simp only [nsmul_eq_mul]
      ring
  | negSucc n =>
      rw [negSucc_zsmul, ← WithTop.coe_nsmul ((e : ℤ)) (n + 1),
        ← WithTop.LinearOrderedAddCommGroup.coe_neg,
        ← WithTop.coe_nsmul (Int.negSucc n) e]
      congr 1
      simp only [nsmul_eq_mul, Int.negSucc_eq]
      push_cast
      ring

section CoefficientScalars

variable {k l : Type*} [Field k] [Field l] [Algebra k l]

private noncomputable def coefficientScalarMap (e : ℕ)
    (v : PowerSeries l) (hv : IsUnit (PowerSeries.constantCoeff v)) :
    LaurentSeries k →+* FreeBasis.LaurentScalars l e v hv :=
  (FreeBasis.laurentScalarsEquiv e v hv).symm.toRingHom.comp
    (FreeBasis.mapLaurentSeries (algebraMap k l))

@[reducible] private noncomputable def coefficientScalarAlgebra
    (e : ℕ) (v : PowerSeries l)
    (hv : IsUnit (PowerSeries.constantCoeff v)) :
    Algebra (LaurentSeries k) (FreeBasis.LaurentScalars l e v hv) :=
  (coefficientScalarMap e v hv).toAlgebra

private noncomputable def coefficientScalarEquiv
    (e : ℕ) (v : PowerSeries l)
    (hv : IsUnit (PowerSeries.constantCoeff v)) :
    letI : Algebra (LaurentSeries k) (LaurentSeries l) :=
      coefficientwiseAlgebra
    letI : Algebra (LaurentSeries k)
        (FreeBasis.LaurentScalars l e v hv) :=
      coefficientScalarAlgebra e v hv
    FreeBasis.LaurentScalars l e v hv ≃ₐ[LaurentSeries k]
      LaurentSeries l := by
  letI : Algebra (LaurentSeries k) (LaurentSeries l) :=
    coefficientwiseAlgebra
  letI : Algebra (LaurentSeries k)
      (FreeBasis.LaurentScalars l e v hv) :=
    coefficientScalarAlgebra e v hv
  exact
    { toRingEquiv := FreeBasis.laurentScalarsEquiv e v hv
      commutes' := fun _ ↦ rfl }

private noncomputable def coefficientScalarBasis [Fintype ι]
    (b : Module.Basis ι k l) (e : ℕ) (v : PowerSeries l)
    (hv : IsUnit (PowerSeries.constantCoeff v)) :
    letI : Algebra (LaurentSeries k)
        (FreeBasis.LaurentScalars l e v hv) :=
      coefficientScalarAlgebra e v hv
    Module.Basis ι (LaurentSeries k)
      (FreeBasis.LaurentScalars l e v hv) := by
  letI : Algebra (LaurentSeries k) (LaurentSeries l) :=
    coefficientwiseAlgebra
  letI : Algebra (LaurentSeries k)
      (FreeBasis.LaurentScalars l e v hv) :=
    coefficientScalarAlgebra e v hv
  exact (coefficientBasis b).map
    (coefficientScalarEquiv e v hv).symm.toLinearEquiv

private theorem trace_coefficientScalar [Fintype ι]
    (b : Module.Basis ι k l) (e : ℕ) (v : PowerSeries l)
    (hv : IsUnit (PowerSeries.constantCoeff v))
    (z : FreeBasis.LaurentScalars l e v hv) (n : ℤ) :
    letI : Algebra (LaurentSeries k)
        (FreeBasis.LaurentScalars l e v hv) :=
      coefficientScalarAlgebra e v hv
    (Algebra.trace (LaurentSeries k)
      (FreeBasis.LaurentScalars l e v hv) z).coeff n =
        Algebra.trace k l
          ((FreeBasis.laurentScalarsEquiv e v hv z).coeff n) := by
  letI : Algebra (LaurentSeries k) (LaurentSeries l) :=
    coefficientwiseAlgebra
  letI : Algebra (LaurentSeries k)
      (FreeBasis.LaurentScalars l e v hv) :=
    coefficientScalarAlgebra e v hv
  rw [← Algebra.trace_eq_of_algEquiv (coefficientScalarEquiv e v hv) z]
  exact trace_coefficientwise b _ n

end CoefficientScalars

private theorem mapLaurentSeries_orderTop {k l : Type*} [Field k] [Field l]
    (f : k →+* l) (hf : Function.Injective f) (H : LaurentSeries k) :
    (FreeBasis.mapLaurentSeries f H).orderTop = H.orderTop := by
  by_cases hH : H = 0
  · simp [hH]
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero hH]
  apply HahnSeries.orderTop_eq_of_le
  · rw [HahnSeries.mem_support]
    exact (map_ne_zero_iff f hf).2
      (by simpa only [HahnSeries.leadingCoeff_eq] using
        HahnSeries.leadingCoeff_ne_zero.mpr hH)
  · intro n hn
    apply HahnSeries.order_le_of_coeff_ne_zero
    rw [HahnSeries.mem_support] at hn
    exact (map_ne_zero_iff f hf).mp hn

@[simp] private theorem mapLaurentSeries_C {k l : Type*} [Field k]
    [Field l] (f : k →+* l) (a : k) :
    FreeBasis.mapLaurentSeries f (HahnSeries.C a) =
      HahnSeries.C (f a) := by
  apply HahnSeries.ext
  funext n
  simp only [FreeBasis.mapLaurentSeries, HahnSeries.C_apply,
    HahnSeries.coeff_single]
  split_ifs <;> simp_all

@[simp] private theorem mapLaurentSeries_X {k l : Type*} [Field k]
    [Field l] (f : k →+* l) :
    FreeBasis.mapLaurentSeries f
        (HahnSeries.single 1 1 : LaurentSeries k) =
      (HahnSeries.single 1 1 : LaurentSeries l) := by
  apply HahnSeries.ext
  funext n
  simp [FreeBasis.mapLaurentSeries, HahnSeries.coeff_single]

private theorem laurentScalarsEquiv_symm_toRingHom_apply
    {K : Type*} [Field K] (e : ℕ) (v : PowerSeries K)
    (hv : IsUnit (PowerSeries.constantCoeff v)) (H : LaurentSeries K) :
    FreeBasis.laurentScalarsEquiv e v hv
        ((FreeBasis.laurentScalarsEquiv e v hv).symm.toRingHom H) = H :=
  (FreeBasis.laurentScalarsEquiv e v hv).apply_symm_apply H

private theorem algebraMap_eq_formalSubstitution {K : Type*} [Field K]
    (e : ℕ) [NeZero e] (v : PowerSeries K)
    (hv : IsUnit (PowerSeries.constantCoeff v))
    (a : FreeBasis.LaurentScalars K e v hv) :
    algebraMap (FreeBasis.LaurentScalars K e v hv) (LaurentSeries K) a =
      formalSubstitution (FreeBasis.parameter e v) e (NeZero.pos e)
        (parameter_order e v hv)
        (FreeBasis.laurentScalarsEquiv e v hv a) := by
  let left : FreeBasis.LaurentScalars K e v hv →+* LaurentSeries K :=
    algebraMap _ _
  let right : FreeBasis.LaurentScalars K e v hv →+* LaurentSeries K :=
    (formalSubstitution (FreeBasis.parameter e v) e (NeZero.pos e)
      (parameter_order e v hv)).comp
        (FreeBasis.laurentScalarsEquiv e v hv).toRingHom
  have hlr : left = right := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers (FreeBasis.scalarX e v))
    apply RingHom.ext
    intro p
    simp only [left, right, RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply
      (FreeBasis.PowerScalars K e v)
      (FreeBasis.LaurentScalars K e v hv) (LaurentSeries K)]
    change algebraMap (FreeBasis.PowerScalars K e v)
      (LaurentSeries K) p = _
    change algebraMap (PowerSeries K) (LaurentSeries K)
        (algebraMap (FreeBasis.PowerScalars K e v) (PowerSeries K) p) = _
    rw [FreeBasis.algebraMap_powerScalars_apply]
    change (PowerSeries.subst (FreeBasis.parameter e v)
        ((FreeBasis.powerScalarsEquiv e v) p) : LaurentSeries K) =
      formalSubstitution (FreeBasis.parameter e v) e (NeZero.pos e)
        (parameter_order e v hv)
        (((FreeBasis.powerScalarsEquiv e v) p : PowerSeries K) :
          LaurentSeries K)
    rw [formalSubstitution_coe]
  exact DFunLike.congr_fun hlr a

private theorem towerMap_isLaurentSubstitution
    {k l : Type*} [Field k] [Field l] [Algebra k l]
    (e : ℕ) [NeZero e] (v : PowerSeries l)
    (hv : IsUnit (PowerSeries.constantCoeff v)) :
    letI : Algebra (LaurentSeries k)
      (FreeBasis.LaurentScalars l e v hv) :=
        coefficientScalarAlgebra e v hv
    IsLaurentSubstitution e (algebraMap k l)
      (FreeBasis.parameter e v : LaurentSeries l)
      ((algebraMap (FreeBasis.LaurentScalars l e v hv)
        (LaurentSeries l)).comp (coefficientScalarMap e v hv)) := by
  letI : Algebra (LaurentSeries k)
      (FreeBasis.LaurentScalars l e v hv) :=
    coefficientScalarAlgebra e v hv
  constructor
  · intro a
    rw [RingHom.comp_apply, algebraMap_eq_formalSubstitution]
    simp only [coefficientScalarMap, RingHom.comp_apply,
      mapLaurentSeries_C]
    rw [laurentScalarsEquiv_symm_toRingHom_apply]
    rw [← PowerSeries.coe_C, formalSubstitution_coe,
      PowerSeries.subst_C]
    rw [← PowerSeries.C_apply]
  constructor
  · rw [RingHom.comp_apply, algebraMap_eq_formalSubstitution]
    simp only [coefficientScalarMap, RingHom.comp_apply,
      mapLaurentSeries_X (k := k) (l := l) (algebraMap k l)]
    rw [laurentScalarsEquiv_symm_toRingHom_apply]
    rw [← PowerSeries.coe_X]
    rw [formalSubstitution_coe,
      PowerSeries.subst_X (FreeBasis.parameter_hasSubst e v)]
  · intro H
    rw [RingHom.comp_apply, algebraMap_eq_formalSubstitution]
    simp only [coefficientScalarMap, RingHom.comp_apply]
    rw [laurentScalarsEquiv_symm_toRingHom_apply]
    rw [formalSubstitution_orderTop e v hv,
      mapLaurentSeries_orderTop (algebraMap k l)
        (algebraMap k l).injective H]

private theorem eq_parameter_powerSeriesPart {K : Type*} [Field K]
    (u : LaurentSeries K) (e : ℕ) (hu : u.order = (e : ℤ)) :
    (FreeBasis.parameter e u.powerSeriesPart : LaurentSeries K) = u := by
  change ((PowerSeries.X ^ e * u.powerSeriesPart : PowerSeries K) :
    LaurentSeries K) = u
  rw [map_mul, map_pow, PowerSeries.coe_X,
    ← RatFunc.single_one_eq_pow]
  simpa only [hu] using LaurentSeries.single_order_mul_powerSeriesPart u

set_option maxHeartbeats 800000

/-- The trace--residue identity for differentials `x · ds` in an actual finite
separable extension of equal-characteristic local fields. The presentation is
constructed by `exists_equalCharacteristicExtensionPresentation`; in these
coordinates `x · ds` is represented by `x · u'(t) dt`. -/
theorem traceCompatibility_onDs
    (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Finite F E] [Algebra.IsSeparable F E]
    (hchar : ringChar F = ringChar (ResidueField F)) (x : E) :
    let P := Classical.choice
      (exists_equalCharacteristicExtensionPresentation F E hchar)
    Algebra.trace (ResidueField F) (ResidueField E)
        (residue
          (P.extension.laurentEquiv.symm x *
            (PowerSeries.derivative (ResidueField E)
              (FreeBasis.parameter (ramificationIndex F E)
                P.uniformizerExpansion.powerSeriesPart) :
              LaurentSeries (ResidueField E)))) =
      residue (P.base.laurentEquiv.symm (Algebra.trace F E x)) := by
  let P := Classical.choice
    (exists_equalCharacteristicExtensionPresentation F E hchar)
  change Algebra.trace (ResidueField F) (ResidueField E)
      (residue
        (P.extension.laurentEquiv.symm x *
          (PowerSeries.derivative (ResidueField E)
            (FreeBasis.parameter (ramificationIndex F E)
              P.uniformizerExpansion.powerSeriesPart) :
            LaurentSeries (ResidueField E)))) =
    residue (P.base.laurentEquiv.symm (Algebra.trace F E x))
  let e := ramificationIndex F E
  let u := P.uniformizerExpansion
  let v := u.powerSeriesPart
  letI : NeZero e := ⟨Nat.ne_of_gt (ramificationIndex_pos F E)⟩
  have hu_ne : u ≠ 0 := by
    rw [← HahnSeries.orderTop_ne_top]
    rw [show u = P.uniformizerExpansion from rfl,
      P.uniformizerExpansion_order]
    exact WithTop.coe_ne_top
  have hu_order : u.order = (e : ℤ) := by
    apply WithTop.coe_injective
    rw [HahnSeries.order_eq_orderTop_of_ne_zero hu_ne]
    exact P.uniformizerExpansion_order
  have hv : IsUnit (PowerSeries.constantCoeff v) := by
    rw [isUnit_iff_ne_zero, ← PowerSeries.coeff_zero_eq_constantCoeff]
    change PowerSeries.coeff 0 u.powerSeriesPart ≠ 0
    rw [LaurentSeries.powerSeriesPart_coeff]
    simpa only [Int.ofNat_eq_natCast, Nat.cast_zero, add_zero,
      HahnSeries.leadingCoeff_eq] using
        HahnSeries.leadingCoeff_ne_zero.mpr hu_ne
  have hparameter :
      (FreeBasis.parameter e v : LaurentSeries (ResidueField E)) = u := by
    exact eq_parameter_powerSeriesPart u e hu_order
  letI : Algebra (LaurentSeries (ResidueField F))
      (FreeBasis.LaurentScalars (ResidueField E) e v hv) :=
    coefficientScalarAlgebra e v hv
  let residueBasis := Module.finBasis (ResidueField F) (ResidueField E)
  let coefficientBasis' := coefficientScalarBasis residueBasis e v hv
  letI : Module.Free (LaurentSeries (ResidueField F))
      (FreeBasis.LaurentScalars (ResidueField E) e v hv) :=
    Module.Free.of_basis coefficientBasis'
  letI : Module.Finite (LaurentSeries (ResidueField F))
      (FreeBasis.LaurentScalars (ResidueField E) e v hv) :=
    Module.Finite.of_basis coefficientBasis'
  let ramifiedBasis := FreeBasis.laurentSeriesBasis e v hv
  letI : Module.Free
      (FreeBasis.LaurentScalars (ResidueField E) e v hv)
      (LaurentSeries (ResidueField E)) :=
    Module.Free.of_basis ramifiedBasis
  letI : Module.Finite
      (FreeBasis.LaurentScalars (ResidueField E) e v hv)
      (LaurentSeries (ResidueField E)) :=
    Module.Finite.of_basis ramifiedBasis
  letI : Algebra (LaurentSeries (ResidueField F))
      (LaurentSeries (ResidueField E)) := P.substitution.toAlgebra
  have hstandard :
      (algebraMap (FreeBasis.LaurentScalars (ResidueField E) e v hv)
        (LaurentSeries (ResidueField E))).comp
          (coefficientScalarMap e v hv) = P.substitution := by
    apply P.substitution_unique
    simpa only [hparameter] using
      (towerMap_isLaurentSubstitution e v hv)
  letI : IsScalarTower (LaurentSeries (ResidueField F))
      (FreeBasis.LaurentScalars (ResidueField E) e v hv)
      (LaurentSeries (ResidueField E)) := by
    apply IsScalarTower.of_algebraMap_eq'
    change P.substitution =
      (algebraMap (FreeBasis.LaurentScalars (ResidueField E) e v hv)
        (LaurentSeries (ResidueField E))).comp
          (coefficientScalarMap e v hv)
    exact hstandard.symm
  let h := P.extension.laurentEquiv.symm x
  have hcoordinates :
      Algebra.trace (LaurentSeries (ResidueField F))
          (LaurentSeries (ResidueField E)) h =
        P.base.laurentEquiv.symm
          (Algebra.trace F E (P.extension.laurentEquiv h)) := by
    apply Algebra.trace_eq_of_equiv_equiv
      P.base.laurentEquiv P.extension.laurentEquiv
    exact P.algebraMap_coordinates.symm
  have hramified := traceSubstitution e v hv h
  change Algebra.trace (ResidueField F) (ResidueField E)
      (residue
        (h * (PowerSeries.derivative (ResidueField E)
          (FreeBasis.parameter e v) : LaurentSeries (ResidueField E)))) = _
  calc
    Algebra.trace (ResidueField F) (ResidueField E)
        (residue
          (h * (PowerSeries.derivative (ResidueField E)
            (FreeBasis.parameter e v) : LaurentSeries (ResidueField E)))) =
      Algebra.trace (ResidueField F) (ResidueField E)
        (residue
          (FreeBasis.laurentScalarsEquiv e v hv
            (Algebra.trace
              (FreeBasis.LaurentScalars (ResidueField E) e v hv)
              (LaurentSeries (ResidueField E)) h))) := by
        rw [hramified]
    _ = residue
        (Algebra.trace (LaurentSeries (ResidueField F))
          (FreeBasis.LaurentScalars (ResidueField E) e v hv)
          (Algebra.trace
            (FreeBasis.LaurentScalars (ResidueField E) e v hv)
            (LaurentSeries (ResidueField E)) h)) := by
      symm
      exact trace_coefficientScalar residueBasis e v hv _ (-1)
    _ = residue
        (Algebra.trace (LaurentSeries (ResidueField F))
          (LaurentSeries (ResidueField E)) h) := by
      have htower :
          Algebra.trace (LaurentSeries (ResidueField F))
              (FreeBasis.LaurentScalars (ResidueField E) e v hv)
              (Algebra.trace
                (FreeBasis.LaurentScalars (ResidueField E) e v hv)
                (LaurentSeries (ResidueField E)) h) =
            Algebra.trace (LaurentSeries (ResidueField F))
              (LaurentSeries (ResidueField E)) h :=
        Algebra.trace_trace
          (R := LaurentSeries (ResidueField F))
          (S := FreeBasis.LaurentScalars (ResidueField E) e v hv)
          (T := LaurentSeries (ResidueField E)) h
      exact congrArg
        (fun z : LaurentSeries (ResidueField F) ↦ residue z) htower
    _ = residue
        (P.base.laurentEquiv.symm (Algebra.trace F E x)) := by
      rw [hcoordinates]
      simp only [h, RingEquiv.apply_symm_apply]

section Differentials

variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E]
  [Module.Finite F E] [Algebra.IsSeparable F E]
  (hchar : ringChar F = ringChar (ResidueField F))

/-- Surjectivity of the actual field trace forces `ds` to be nonzero: a trace
with Laurent expansion `s⁻¹` has residue one, contradicting the `onDs`
identity if the derivative vanishes. -/
private theorem traceCompatibility_derivative_ne_zero :
    let P := Classical.choice
      (exists_equalCharacteristicExtensionPresentation F E hchar)
    (PowerSeries.derivative (ResidueField E)
      (FreeBasis.parameter (ramificationIndex F E)
        P.uniformizerExpansion.powerSeriesPart) :
      LaurentSeries (ResidueField E)) ≠ 0 := by
  let P := Classical.choice
    (exists_equalCharacteristicExtensionPresentation F E hchar)
  let u := FreeBasis.parameter (ramificationIndex F E)
    P.uniformizerExpansion.powerSeriesPart
  change (PowerSeries.derivative (ResidueField E) u :
    LaurentSeries (ResidueField E)) ≠ 0
  intro hzero
  obtain ⟨x, hx⟩ := Algebra.trace_surjective F E
    (P.base.laurentEquiv (HahnSeries.single (-1) 1))
  have h := traceCompatibility_onDs F E hchar x
  change Algebra.trace (ResidueField F) (ResidueField E)
      (residue (P.extension.laurentEquiv.symm x *
        (PowerSeries.derivative (ResidueField E) u :
          LaurentSeries (ResidueField E)))) =
    residue (P.base.laurentEquiv.symm (Algebra.trace F E x)) at h
  rw [hzero, mul_zero, hx, RingEquiv.symm_apply_apply] at h
  simp [residue] at h

/-- The actual differential trace in the internally constructed Laurent
coordinates. Write `eta = x · ds` by dividing its coefficient by `u'(t)`,
transport `x` to `E`, apply `Algebra.trace F E`, and expand the result in `F`.
The preceding lemma proves that this division is by a nonzero series. -/
noncomputable def differentialTrace
    (eta : FormalDifferential (ResidueField E)) :
    FormalDifferential (ResidueField F) :=
  let P := Classical.choice
    (exists_equalCharacteristicExtensionPresentation F E hchar)
  let u := FreeBasis.parameter (ramificationIndex F E)
    P.uniformizerExpansion.powerSeriesPart
  P.base.laurentEquiv.symm (Algebra.trace F E
    (P.extension.laurentEquiv
      (eta / (PowerSeries.derivative (ResidueField E) u :
        LaurentSeries (ResidueField E)))))

/-- On `x · ds`, the differential trace is precisely `Tr_{E/F}(x) · ds`,
as stipulated in Appendix B, Theorem B.4. -/
theorem differentialTrace_onDs (x : E) :
    let P := Classical.choice
      (exists_equalCharacteristicExtensionPresentation F E hchar)
    let u := FreeBasis.parameter (ramificationIndex F E)
      P.uniformizerExpansion.powerSeriesPart
    differentialTrace F E hchar
        (P.extension.laurentEquiv.symm x *
          (PowerSeries.derivative (ResidueField E) u :
            LaurentSeries (ResidueField E))) =
      P.base.laurentEquiv.symm (Algebra.trace F E x) := by
  dsimp only [differentialTrace]
  rw [mul_div_cancel_right₀ _
    (traceCompatibility_derivative_ne_zero F E hchar),
    RingEquiv.apply_symm_apply]

/-- Appendix B, Theorem B.4: trace commutes with residue for every formal
differential on an actual finite separable extension of equal-characteristic
local fields. All presentations are constructed from the field data, and
`differentialTrace` uses the actual field trace. -/
theorem traceCompatibility (eta : FormalDifferential (ResidueField E)) :
    Algebra.trace (ResidueField F) (ResidueField E) (residue eta) =
      residue (differentialTrace F E hchar eta) := by
  let P := Classical.choice
    (exists_equalCharacteristicExtensionPresentation F E hchar)
  let u := FreeBasis.parameter (ramificationIndex F E)
    P.uniformizerExpansion.powerSeriesPart
  have hderiv : (PowerSeries.derivative (ResidueField E) u :
      LaurentSeries (ResidueField E)) ≠ 0 :=
    traceCompatibility_derivative_ne_zero F E hchar
  have h := traceCompatibility_onDs F E hchar
    (P.extension.laurentEquiv
      (eta / (PowerSeries.derivative (ResidueField E) u :
        LaurentSeries (ResidueField E))))
  dsimp only [P, u] at hderiv h
  simpa only [RingEquiv.symm_apply_apply, div_mul_cancel₀ _ hderiv,
    differentialTrace] using h

end Differentials

end

end LanglandsSecondMainLemma.Residues
