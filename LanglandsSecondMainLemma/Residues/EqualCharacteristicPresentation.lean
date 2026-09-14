import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.LocalField.Lattices
import LanglandsFirstMainLemma.LocalField.ResidueField
import LanglandsFirstMainLemma.LocalField.Valuation
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.HahnSeries.HEval
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Evaluation

/-!
# Equal-characteristic local-field presentations

This file constructs coefficient fields and Laurent-series coordinates for actual
nonarchimedean local fields in equal characteristic, and proves that the coordinates are
compatible with a finite separable valuative extension. The coefficient fields are the
canonical Teichmuller representatives; their additivity and extension compatibility are
proved from uniqueness of roots of X ^ q - X. Power-series evaluation is constructed
from adic completeness, and the passage from polynomial identities to all Laurent series
is controlled by exact order scaling.
-/

namespace LanglandsSecondMainLemma.Residues

open LanglandsFirstMainLemma
open scoped PowerSeries

noncomputable section

private theorem residueCard_eq_char_pow
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ d : ℕ, residueCard K = ringChar (ResidueField K) ^ d := by
  letI := residueFieldFintype K
  let p := ringChar (ResidueField K)
  letI : Fact p.Prime := ⟨CharP.char_is_prime (ResidueField K) p⟩
  letI : Algebra (ZMod p) (ResidueField K) := ZMod.algebra _ _
  refine ⟨Module.finrank (ZMod p) (ResidueField K), ?_⟩
  simpa only [residueCard, ZMod.card] using
    (Module.card_eq_pow_finrank (K := ZMod p) (V := ResidueField K))

private theorem teichmuller_unique_of_pow_residueCard
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K))
    {x y : ringOfIntegers K}
    (hx : x ^ residueCard K = x) (hy : y ^ residueCard K = y)
    (hres : residueMap K x = residueMap K y) : x = y := by
  let p := ringChar (ResidueField K)
  obtain ⟨d, hq⟩ := residueCard_eq_char_pow K
  letI : Fact p.Prime := ⟨CharP.char_is_prime (ResidueField K) p⟩
  letI : CharP K p := ringChar.of_eq hchar
  let z : ringOfIntegers K := x - y
  have hzpow : z ^ residueCard K = z := by
    rw [hq]
    exact (sub_pow_char_pow x y d).trans (by rw [hq] at hx hy; rw [hx, hy])
  have hzmem : z ∈ IsLocalRing.maximalIdeal (ringOfIntegers K) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hres, sub_self]
  by_contra hz
  have hq0 : residueCard K ≠ 0 :=
    Nat.ne_of_gt (Nat.zero_lt_of_lt (one_lt_residueCard K))
  have hz0 : z ≠ 0 := sub_ne_zero.mpr hz
  have hunit : IsUnit z := by
    apply IsUnit.of_pow_eq_one (n := residueCard K - 1)
    · apply mul_right_cancel₀ hz0
      rw [pow_sub_one_mul hq0, hzpow, one_mul]
    · have hqgt := one_lt_residueCard K
      omega
  exact (IsLocalRing.mem_maximalIdeal z).mp hzmem hunit

private noncomputable def coefficientRingHom
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K)) :
    ResidueField K →+* ringOfIntegers K where
  toFun := teichmuller K
  map_one' := map_one (teichmuller K)
  map_mul' := map_mul (teichmuller K)
  map_zero' := map_zero (teichmuller K)
  map_add' a b := by
    apply teichmuller_unique_of_pow_residueCard K hchar
    · exact teichmuller_pow_residueCard K (a + b)
    · obtain ⟨d, hq⟩ := residueCard_eq_char_pow K
      let p := ringChar (ResidueField K)
      letI : Fact p.Prime := ⟨CharP.char_is_prime (ResidueField K) p⟩
      letI : CharP K p := ringChar.of_eq hchar
      rw [hq]
      exact (add_pow_char_pow (teichmuller K a) (teichmuller K b) p d).trans
        (by rw [← hq, teichmuller_pow_residueCard, teichmuller_pow_residueCard])
    · simp

private noncomputable def truncatedEval
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal S) (c : R →+* S) (s : S) (hs : s ∈ I) (n : ℕ) :
    PowerSeries R →+* S ⧸ I ^ n := by
  letI : UniformSpace R := ⊥
  letI : UniformSpace (S ⧸ I ^ n) := ⊥
  let phi : R →+* S ⧸ I ^ n := (Ideal.Quotient.mk (I ^ n)).comp c
  let a : S ⧸ I ^ n := Ideal.Quotient.mk (I ^ n) s
  apply PowerSeries.eval₂Hom (φ := phi) (a := a)
  · fun_prop
  · apply IsNilpotent.isTopologicallyNilpotent
    refine ⟨n, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hs n

private theorem truncatedEval_C
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal S) (c : R →+* S) (s : S) (hs : s ∈ I) (n : ℕ) (r : R) :
    truncatedEval I c s hs n (PowerSeries.C r) =
      Ideal.Quotient.mk (I ^ n) (c r) := by
  letI : UniformSpace R := ⊥
  letI : UniformSpace (S ⧸ I ^ n) := ⊥
  simp [truncatedEval, PowerSeries.coe_eval₂Hom]

private theorem truncatedEval_X
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal S) (c : R →+* S) (s : S) (hs : s ∈ I) (n : ℕ) :
    truncatedEval I c s hs n PowerSeries.X = Ideal.Quotient.mk (I ^ n) s := by
  letI : UniformSpace R := ⊥
  letI : UniformSpace (S ⧸ I ^ n) := ⊥
  simp [truncatedEval, PowerSeries.coe_eval₂Hom]

private theorem truncatedEval_eq_sum
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal S) (c : R →+* S) (s : S) (hs : s ∈ I) (n : ℕ)
    (f : PowerSeries R) :
    truncatedEval I c s hs n f =
      Ideal.Quotient.mk (I ^ n)
        (∑ i ∈ Finset.range n, c (PowerSeries.coeff i f) * s ^ i) := by
  conv_lhs => rw [PowerSeries.eq_X_pow_mul_shift_add_trunc n f]
  simp only [map_add, map_mul, map_pow, truncatedEval_X]
  have hs0 : (Ideal.Quotient.mk (I ^ n)) (s ^ n) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hs n
  rw [← map_pow, hs0, zero_mul, zero_add]
  letI : UniformSpace R := ⊥
  letI : UniformSpace (S ⧸ I ^ n) := ⊥
  simp only [truncatedEval, PowerSeries.coe_eval₂Hom]
  rw [PowerSeries.eval₂_coe]
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  simp only [RingHom.coe_comp, Function.comp_apply, map_pow, map_mul, map_sum]

private theorem truncatedEval_compatible
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal S) (c : R →+* S) (s : S) (hs : s ∈ I)
    {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow I hmn).comp (truncatedEval I c s hs n) =
      truncatedEval I c s hs m := by
  ext f
  change (Ideal.Quotient.factorPow I hmn) (truncatedEval I c s hs n f) =
    truncatedEval I c s hs m f
  rw [truncatedEval_eq_sum, truncatedEval_eq_sum]
  rw [Ideal.Quotient.factor_mk]
  simp only [map_sum, map_mul, map_pow]
  symm
  apply Finset.sum_subset (Finset.range_mono hmn)
  intro i hin him
  rw [← map_pow]
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  apply Ideal.mul_mem_left
  apply Ideal.pow_le_pow_right (Nat.le_of_not_gt (by simpa using him))
  exact Ideal.pow_mem_pow hs i

private noncomputable def powerSeriesEval
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K))
    (s : ringOfIntegers K)
    (hs : s ∈ IsLocalRing.maximalIdeal (ringOfIntegers K)) :
    PowerSeries (ResidueField K) →+* ringOfIntegers K := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  exact IsAdicComplete.liftRingHom (IsLocalRing.maximalIdeal (ringOfIntegers K))
    (truncatedEval (IsLocalRing.maximalIdeal (ringOfIntegers K))
      (coefficientRingHom K hchar) s hs)
    (fun hmn ↦ truncatedEval_compatible
      (IsLocalRing.maximalIdeal (ringOfIntegers K)) (coefficientRingHom K hchar) s hs hmn)

private theorem powerSeriesEval_mod
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K))
    (s : ringOfIntegers K)
    (hs : s ∈ IsLocalRing.maximalIdeal (ringOfIntegers K))
    (n : ℕ) (f : PowerSeries (ResidueField K)) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (ringOfIntegers K) ^ n)
        (powerSeriesEval K hchar s hs f) =
      truncatedEval (IsLocalRing.maximalIdeal (ringOfIntegers K))
        (coefficientRingHom K hchar) s hs n f := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  exact IsAdicComplete.mk_liftRingHom
    (IsLocalRing.maximalIdeal (ringOfIntegers K))
    (truncatedEval (IsLocalRing.maximalIdeal (ringOfIntegers K))
      (coefficientRingHom K hchar) s hs)
    (fun hmn ↦ truncatedEval_compatible
      (IsLocalRing.maximalIdeal (ringOfIntegers K)) (coefficientRingHom K hchar) s hs hmn)
    n f

private theorem powerSeriesEval_C
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K))
    (s : ringOfIntegers K)
    (hs : s ∈ IsLocalRing.maximalIdeal (ringOfIntegers K))
    (a : ResidueField K) :
    powerSeriesEval K hchar s hs (PowerSeries.C a) = coefficientRingHom K hchar a := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  rw [IsHausdorff.eq_iff_smodEq
    (I := IsLocalRing.maximalIdeal (ringOfIntegers K))]
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, powerSeriesEval_mod,
    truncatedEval_C, sub_self]

private theorem powerSeriesEval_X
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K))
    (s : ringOfIntegers K)
    (hs : s ∈ IsLocalRing.maximalIdeal (ringOfIntegers K)) :
    powerSeriesEval K hchar s hs PowerSeries.X = s := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  rw [IsHausdorff.eq_iff_smodEq
    (I := IsLocalRing.maximalIdeal (ringOfIntegers K))]
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, powerSeriesEval_mod,
    truncatedEval_X, sub_self]

private theorem coefficientRingHom_residue
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K)) (a : ResidueField K) :
    residueMap K (coefficientRingHom K hchar a) = a := by
  exact residueMap_teichmuller K a

private theorem exists_tail
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K))
    (s : ringOfIntegers K)
    (hspan : IsLocalRing.maximalIdeal (ringOfIntegers K) = Ideal.span {s})
    (x : ringOfIntegers K) :
    ∃ y : ringOfIntegers K,
      x = coefficientRingHom K hchar (residueMap K x) + s * y := by
  have hmem : x - coefficientRingHom K hchar (residueMap K x) ∈
      IsLocalRing.maximalIdeal (ringOfIntegers K) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, coefficientRingHom_residue, sub_self]
  rw [hspan, Ideal.mem_span_singleton'] at hmem
  obtain ⟨y, hy⟩ := hmem
  refine ⟨y, ?_⟩
  calc
    x = coefficientRingHom K hchar (residueMap K x) +
        (x - coefficientRingHom K hchar (residueMap K x)) := by ring
    _ = coefficientRingHom K hchar (residueMap K x) + y * s := by rw [hy]
    _ = coefficientRingHom K hchar (residueMap K x) + s * y := by rw [mul_comm]

private noncomputable def tail
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K))
    (s : ringOfIntegers K)
    (hspan : IsLocalRing.maximalIdeal (ringOfIntegers K) = Ideal.span {s})
    (x : ringOfIntegers K) : ringOfIntegers K :=
  (exists_tail K hchar s hspan x).choose

private theorem head_tail
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K))
    (s : ringOfIntegers K)
    (hspan : IsLocalRing.maximalIdeal (ringOfIntegers K) = Ideal.span {s})
    (x : ringOfIntegers K) :
    x = coefficientRingHom K hchar (residueMap K x) + s * tail K hchar s hspan x :=
  (exists_tail K hchar s hspan x).choose_spec

private noncomputable def expansion
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K))
    (s : ringOfIntegers K)
    (hspan : IsLocalRing.maximalIdeal (ringOfIntegers K) = Ideal.span {s})
    (x : ringOfIntegers K) : PowerSeries (ResidueField K) :=
  PowerSeries.mk fun n ↦ residueMap K ((tail K hchar s hspan)^[n] x)

private theorem expansion_approximation
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K))
    (s : ringOfIntegers K)
    (hspan : IsLocalRing.maximalIdeal (ringOfIntegers K) = Ideal.span {s})
    (x : ringOfIntegers K) (n : ℕ) :
    x = (∑ i ∈ Finset.range n,
        coefficientRingHom K hchar
          (residueMap K ((tail K hchar s hspan)^[i] x)) * s ^ i) +
      s ^ n * ((tail K hchar s hspan)^[n] x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        x = (∑ i ∈ Finset.range n,
              coefficientRingHom K hchar
                (residueMap K ((tail K hchar s hspan)^[i] x)) * s ^ i) +
            s ^ n * ((tail K hchar s hspan)^[n] x) := ih
        _ = (∑ i ∈ Finset.range n,
              coefficientRingHom K hchar
                (residueMap K ((tail K hchar s hspan)^[i] x)) * s ^ i) +
            s ^ n * (coefficientRingHom K hchar
                (residueMap K ((tail K hchar s hspan)^[n] x)) +
              s * tail K hchar s hspan ((tail K hchar s hspan)^[n] x)) := by
              nth_rewrite 1 [head_tail K hchar s hspan
                ((tail K hchar s hspan)^[n] x)]
              rfl
        _ = (∑ i ∈ Finset.range (n + 1),
              coefficientRingHom K hchar
                (residueMap K ((tail K hchar s hspan)^[i] x)) * s ^ i) +
            s ^ (n + 1) * ((tail K hchar s hspan)^[n + 1] x) := by
              rw [Finset.sum_range_succ, Function.iterate_succ_apply']
              ring

private theorem powerSeriesEval_expansion
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K))
    (s : ringOfIntegers K)
    (hs : s ∈ IsLocalRing.maximalIdeal (ringOfIntegers K))
    (hspan : IsLocalRing.maximalIdeal (ringOfIntegers K) = Ideal.span {s})
    (x : ringOfIntegers K) :
    powerSeriesEval K hchar s hs (expansion K hchar s hspan x) = x := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  rw [IsHausdorff.eq_iff_smodEq
    (I := IsLocalRing.maximalIdeal (ringOfIntegers K))]
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  rw [powerSeriesEval_mod, truncatedEval_eq_sum]
  simp only [expansion, PowerSeries.coeff_mk]
  conv_rhs => rw [expansion_approximation K hchar s hspan x n]
  symm
  apply Ideal.Quotient.eq.mpr
  simp only [add_sub_cancel_left]
  apply Ideal.mul_mem_right
  exact Ideal.pow_mem_pow hs n

private theorem powerSeriesEval_injective
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K))
    (s : ringOfIntegers K)
    (hs : s ∈ IsLocalRing.maximalIdeal (ringOfIntegers K))
    (hs0 : s ≠ 0) : Function.Injective (powerSeriesEval K hchar s hs) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  ext f
  simp only [RingHom.mem_ker, Ideal.mem_bot]
  constructor
  · intro hf
    by_contra hf0
    have hfactor := PowerSeries.X_pow_order_mul_divXPowOrder (f := f)
    have hunit : IsUnit (powerSeriesEval K hchar s hs (PowerSeries.divXPowOrder f)) :=
      (PowerSeries.isUnit_divided_by_X_pow_order hf0).map
        (powerSeriesEval K hchar s hs)
    have hne : powerSeriesEval K hchar s hs f ≠ 0 := by
      rw [← hfactor, map_mul, map_pow, powerSeriesEval_X]
      exact mul_ne_zero (pow_ne_zero _ hs0) hunit.ne_zero
    exact hne hf
  · rintro rfl
    exact map_zero _

private theorem powerSeriesEval_surjective
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K))
    (s : ringOfIntegers K)
    (hs : s ∈ IsLocalRing.maximalIdeal (ringOfIntegers K))
    (hspan : IsLocalRing.maximalIdeal (ringOfIntegers K) = Ideal.span {s}) :
    Function.Surjective (powerSeriesEval K hchar s hs) := by
  intro x
  exact ⟨expansion K hchar s hspan x,
    powerSeriesEval_expansion K hchar s hs hspan x⟩

private noncomputable def powerSeriesEquiv
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K))
    (s : ringOfIntegers K)
    (hs : s ∈ IsLocalRing.maximalIdeal (ringOfIntegers K))
    (hs0 : s ≠ 0)
    (hspan : IsLocalRing.maximalIdeal (ringOfIntegers K) = Ideal.span {s}) :
    PowerSeries (ResidueField K) ≃+* ringOfIntegers K :=
  RingEquiv.ofBijective (powerSeriesEval K hchar s hs)
    ⟨powerSeriesEval_injective K hchar s hs hs0,
     powerSeriesEval_surjective K hchar s hs hspan⟩

private noncomputable def laurentSeriesEquiv
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K))
    (s : ringOfIntegers K)
    (hs : s ∈ IsLocalRing.maximalIdeal (ringOfIntegers K))
    (hs0 : s ≠ 0)
    (hspan : IsLocalRing.maximalIdeal (ringOfIntegers K) = Ideal.span {s}) :
    LaurentSeries (ResidueField K) ≃+* K :=
  IsFractionRing.ringEquivOfRingEquiv
    (powerSeriesEquiv K hchar s hs hs0 hspan)

private theorem laurentSeriesEquiv_coe
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K))
    (s : ringOfIntegers K)
    (hs : s ∈ IsLocalRing.maximalIdeal (ringOfIntegers K))
    (hs0 : s ≠ 0)
    (hspan : IsLocalRing.maximalIdeal (ringOfIntegers K) = Ideal.span {s})
    (f : PowerSeries (ResidueField K)) :
    laurentSeriesEquiv K hchar s hs hs0 hspan f =
      ((powerSeriesEquiv K hchar s hs hs0 hspan f : ringOfIntegers K) : K) := by
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (powerSeriesEquiv K hchar s hs hs0 hspan) f

private theorem laurentSeriesEquiv_C
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K))
    (s : ringOfIntegers K)
    (hs : s ∈ IsLocalRing.maximalIdeal (ringOfIntegers K))
    (hs0 : s ≠ 0)
    (hspan : IsLocalRing.maximalIdeal (ringOfIntegers K) = Ideal.span {s})
    (a : ResidueField K) :
    laurentSeriesEquiv K hchar s hs hs0 hspan (HahnSeries.C a) =
      ((coefficientRingHom K hchar a : ringOfIntegers K) : K) := by
  rw [← PowerSeries.coe_C]
  rw [laurentSeriesEquiv_coe]
  change ((powerSeriesEval K hchar s hs (PowerSeries.C a) : ringOfIntegers K) : K) = _
  rw [powerSeriesEval_C]

private theorem laurentSeriesEquiv_X
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K))
    (s : ringOfIntegers K)
    (hs : s ∈ IsLocalRing.maximalIdeal (ringOfIntegers K))
    (hs0 : s ≠ 0)
    (hspan : IsLocalRing.maximalIdeal (ringOfIntegers K) = Ideal.span {s}) :
    laurentSeriesEquiv K hchar s hs hs0 hspan (HahnSeries.single 1 1) = (s : K) := by
  rw [← PowerSeries.coe_X]
  rw [laurentSeriesEquiv_coe]
  change ((powerSeriesEval K hchar s hs PowerSeries.X : ringOfIntegers K) : K) = _
  rw [powerSeriesEval_X]

private theorem ord_coe_unit_eq_zero'
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (u : (ringOfIntegers K)ˣ) :
    ord K (((u : ringOfIntegers K) : K)) = 0 := by
  have huval : (ValuativeRel.valuation K)
      (algebraMap (ringOfIntegers K) K (u : ringOfIntegers K)) = 1 :=
    Valuation.Integers.one_of_isUnit
      (Valuation.integer.integers (ValuativeRel.valuation K)) u.isUnit
  have huval' : (ValuativeRel.valuation K)
      (((u : ringOfIntegers K) : K)) = 1 := by
    simpa only [Algebra.coe_algebraMap_ofSubsemiring] using huval
  apply le_antisymm
  · rw [← ord_one K, ord_le_ord_iff]
    rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K)]
    rw [map_one, huval']
  · rw [← ord_one K, ord_le_ord_iff]
    rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K)]
    rw [map_one, huval']

private theorem zsmul_one_withTop_int (n : ℤ) :
    n • (1 : WithTop ℤ) = (n : WithTop ℤ) := by
  have hnat : ∀ m : ℕ, m • (1 : WithTop ℤ) = ((m : ℤ) : WithTop ℤ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [succ_nsmul, ih]
        change ((m : ℤ) : WithTop ℤ) + ((1 : ℤ) : WithTop ℤ) =
          (((m + 1 : ℕ) : ℤ) : WithTop ℤ)
        rw [← WithTop.coe_add, WithTop.coe_eq_coe]
        omega
  cases n with
  | ofNat m =>
      rw [Int.ofNat_eq_natCast, natCast_zsmul]
      exact hnat m
  | negSucc m =>
      rw [negSucc_zsmul, hnat]
      rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.coe_eq_coe]
      omega

private theorem laurentSeriesEquiv_order
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K))
    (s : ringOfIntegers K)
    (hs : s ∈ IsLocalRing.maximalIdeal (ringOfIntegers K))
    (hs0 : s ≠ 0)
    (hspan : IsLocalRing.maximalIdeal (ringOfIntegers K) = Ideal.span {s})
    (hirr : Irreducible s)
    (f : LaurentSeries (ResidueField K)) :
    ord K (laurentSeriesEquiv K hchar s hs hs0 hspan f) = f.orderTop := by
  by_cases hf : f = 0
  · simp [hf]
  have hpart : f.powerSeriesPart ≠ 0 :=
    (LaurentSeries.powerSeriesPart_eq_zero f).not.mpr hf
  have hpartUnit : IsUnit f.powerSeriesPart := by
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [LaurentSeries.powerSeriesPart_coeff]
    simpa using (HahnSeries.coeff_order_eq_zero (x := f)).not.mpr hf
  have himageUnit : IsUnit
      (powerSeriesEquiv K hchar s hs hs0 hspan f.powerSeriesPart) :=
    hpartUnit.map (powerSeriesEquiv K hchar s hs hs0 hspan).toRingHom
  obtain ⟨u, hu⟩ := himageUnit
  have hpartOrd : ord K
      (((powerSeriesEquiv K hchar s hs hs0 hspan f.powerSeriesPart) :
        ringOfIntegers K) : K) = 0 := by
    rw [← hu]
    exact ord_coe_unit_eq_zero' K u
  have hsUniformizer : (ValuativeRel.valuation K).IsUniformizer (s : K) := by
    apply Valuation.isUniformizer_of_maximalIdeal_eq_span
    exact (IsDiscreteValuationRing.irreducible_iff_uniformizer s).mp hirr
  calc
    ord K (laurentSeriesEquiv K hchar s hs hs0 hspan f) =
        ord K (laurentSeriesEquiv K hchar s hs hs0 hspan
          ((HahnSeries.single f.order 1) *
            (f.powerSeriesPart : LaurentSeries (ResidueField K)))) := by
            rw [LaurentSeries.single_order_mul_powerSeriesPart]
    _ = ord K ((s : K) ^ f.order *
          ((powerSeriesEquiv K hchar s hs hs0 hspan f.powerSeriesPart :
            ringOfIntegers K) : K)) := by
          rw [map_mul, RatFunc.single_zpow]
          have hpow :
              laurentSeriesEquiv K hchar s hs hs0 hspan
                  ((HahnSeries.single 1 1) ^ f.order) = (s : K) ^ f.order := by
            exact (map_zpow₀ (laurentSeriesEquiv K hchar s hs hs0 hspan)
              (HahnSeries.single 1 1) f.order).trans
                (congrArg (fun x : K ↦ x ^ f.order)
                  (laurentSeriesEquiv_X K hchar s hs hs0 hspan))
          rw [hpow, laurentSeriesEquiv_coe]
    _ = f.orderTop := by
      rw [LanglandsFirstMainLemma.ord_mul, ord_zpow,
        ord_uniformizer K hsUniformizer, hpartOrd, add_zero]
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero hf]
      exact zsmul_one_withTop_int f.order

/-- A coefficient field and uniformizer identify an equal-characteristic local field with
its Laurent-series field.  Every field and equivalence in this package is constructed from
the actual local field. -/
structure EqualCharacteristicPresentation
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] where
  equalCharacteristic : ringChar K = ringChar (ResidueField K)
  coefficient : ResidueField K →+* ringOfIntegers K
  coefficient_eq_teichmuller : ∀ a, coefficient a = teichmuller K a
  coefficient_residue : ∀ a, residueMap K (coefficient a) = a
  uniformizer : ringOfIntegers K
  uniformizer_irreducible : Irreducible uniformizer
  uniformizer_isUniformizer :
    (ValuativeRel.valuation K).IsUniformizer (uniformizer : K)
  powerSeriesEquiv : PowerSeries (ResidueField K) ≃+* ringOfIntegers K
  powerSeriesEquiv_C : ∀ a, powerSeriesEquiv (PowerSeries.C a) = coefficient a
  powerSeriesEquiv_X : powerSeriesEquiv PowerSeries.X = uniformizer
  laurentEquiv : LaurentSeries (ResidueField K) ≃+* K
  laurentEquiv_C : ∀ a,
    laurentEquiv (HahnSeries.C a) = ((coefficient a : ringOfIntegers K) : K)
  laurentEquiv_X :
    laurentEquiv (HahnSeries.single 1 1) = (uniformizer : K)
  laurentEquiv_order : ∀ f, ord K (laurentEquiv f) = f.orderTop

private noncomputable def existsEqualCharacteristicPresentation
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hchar : ringChar K = ringChar (ResidueField K)) :
    EqualCharacteristicPresentation K := by
  let s : ringOfIntegers K :=
    (IsDiscreteValuationRing.exists_irreducible (ringOfIntegers K)).choose
  have hirr : Irreducible s :=
    (IsDiscreteValuationRing.exists_irreducible (ringOfIntegers K)).choose_spec
  have hspan : IsLocalRing.maximalIdeal (ringOfIntegers K) = Ideal.span {s} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer s).mp hirr
  have hs : s ∈ IsLocalRing.maximalIdeal (ringOfIntegers K) := by
    rw [hspan, Ideal.mem_span_singleton]
  have hs0 : s ≠ 0 := hirr.ne_zero
  have hsunif : (ValuativeRel.valuation K).IsUniformizer (s : K) := by
    apply Valuation.isUniformizer_of_maximalIdeal_eq_span
    exact (IsDiscreteValuationRing.irreducible_iff_uniformizer s).mp hirr
  exact
    { equalCharacteristic := hchar
      coefficient := coefficientRingHom K hchar
      coefficient_eq_teichmuller := fun _ ↦ rfl
      coefficient_residue := coefficientRingHom_residue K hchar
      uniformizer := s
      uniformizer_irreducible := hirr
      uniformizer_isUniformizer := hsunif
      powerSeriesEquiv := powerSeriesEquiv K hchar s hs hs0 hspan
      powerSeriesEquiv_C := fun a ↦ powerSeriesEval_C K hchar s hs a
      powerSeriesEquiv_X := powerSeriesEval_X K hchar s hs
      laurentEquiv := laurentSeriesEquiv K hchar s hs hs0 hspan
      laurentEquiv_C := laurentSeriesEquiv_C K hchar s hs hs0 hspan
      laurentEquiv_X := laurentSeriesEquiv_X K hchar s hs hs0 hspan
      laurentEquiv_order :=
        laurentSeriesEquiv_order K hchar s hs hs0 hspan hirr }

private theorem residueMap_algebraMap_integer
    (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] (x : ringOfIntegers F) :
    residueMap E (algebraMap (ringOfIntegers F) (ringOfIntegers E) x) =
      extensionResidueMap F E (residueMap F x) := by
  rfl

private theorem equalCharacteristic_of_valuativeExtension
    (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    (hchar : ringChar F = ringChar (ResidueField F)) :
    ringChar E = ringChar (ResidueField E) := by
  calc
    ringChar E = ringChar F := (Algebra.ringChar_eq F E).symm
    _ = ringChar (ResidueField F) := hchar
    _ = ringChar (ResidueField E) :=
      Algebra.ringChar_eq (ResidueField F) (ResidueField E)

private theorem residueCard_extension
    (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] :
    residueCard E = residueCard F ^
      Module.finrank (ResidueField F) (ResidueField E) := by
  letI : Fintype (ResidueField F) := residueFieldFintype F
  letI : Fintype (ResidueField E) := residueFieldFintype E
  exact Module.card_eq_pow_finrank

private theorem pow_pow_fixed {R : Type*} [Monoid R] (x : R) (q d : ℕ)
    (hx : x ^ q = x) : x ^ (q ^ d) = x := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [pow_succ, pow_mul, ih, hx]

private theorem powerSeries_coe_orderTop_nonneg {k : Type*} [Field k]
    (f : PowerSeries k) :
    (0 : WithTop ℤ) ≤ (f : LaurentSeries k).orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro j hj
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_image_support
  rintro ⟨n, -, hn⟩
  have : (0 : ℤ) ≤ j := hn ▸ Int.natCast_nonneg n
  exact (not_lt_of_ge this) (WithTop.coe_lt_coe.mp hj)

private theorem truncation_sub_orderTop {k : Type*} [Field k]
    (f : PowerSeries k) (n : ℕ) :
    (((n : ℤ) : WithTop ℤ)) ≤
      ((f : LaurentSeries k) -
        ((PowerSeries.trunc n f).toPowerSeries : LaurentSeries k)).orderTop := by
  let g : PowerSeries k := PowerSeries.mk fun i ↦ PowerSeries.coeff (i + n) f
  have hdecomp := congrArg (HahnSeries.ofPowerSeries ℤ k)
    (PowerSeries.eq_X_pow_mul_shift_add_trunc n f)
  have hsub :
      (f : LaurentSeries k) -
          ((PowerSeries.trunc n f).toPowerSeries : LaurentSeries k) =
        ((PowerSeries.X ^ n : PowerSeries k) : LaurentSeries k) * (g : LaurentSeries k) := by
    dsimp only [g]
    simpa only [map_add, map_mul, map_pow, sub_eq_iff_eq_add] using hdecomp
  rw [hsub, HahnSeries.orderTop_mul]
  have hX :
      (((PowerSeries.X ^ n : PowerSeries k) : LaurentSeries k)).orderTop =
        ((n : ℤ) : WithTop ℤ) := by
    rw [PowerSeries.coe_pow, PowerSeries.coe_X,
      ← RatFunc.single_one_eq_pow, HahnSeries.orderTop_single one_ne_zero]
  rw [hX]
  simpa only [zero_add, add_comm] using
    add_le_add_left (powerSeries_coe_orderTop_nonneg g) ((n : ℤ) : WithTop ℤ)

private theorem int_lt_positive_multiple (j : ℤ) (e : ℕ) (he : 0 < e) :
    (j : WithTop ℤ) <
      e • (((j.natAbs + 1 : ℕ) : ℤ) : WithTop ℤ) := by
  rw [← WithTop.coe_nsmul, WithTop.coe_lt_coe]
  simp only [nsmul_eq_mul]
  have hj : j ≤ (j.natAbs : ℤ) := Int.le_natAbs
  have he' : 1 ≤ e := he
  push_cast
  have hprod : 0 ≤ ((e : ℤ) - 1) * ((j.natAbs : ℤ) + 1) :=
    mul_nonneg (by omega) (by omega)
  rw [Int.natCast_natAbs] at hj hprod
  nlinarith

/-- Laurent series maps which agree on coefficients and the variable, and which scale
order by the same positive integer, agree on every Laurent series.  This is the
continuity/density step needed to pass from polynomials to complete Laurent series. -/
private theorem laurentRingHom_ext_of_order
    {k K : Type*} [Field k] [Field K]
    (e : ℕ) (he : 0 < e) (f g : LaurentSeries k →+* LaurentSeries K)
    (hC : ∀ a, f (HahnSeries.C a) = g (HahnSeries.C a))
    (hX : f (HahnSeries.single 1 1) = g (HahnSeries.single 1 1))
    (hf : ∀ x, (f x).orderTop = e • x.orderTop)
    (hg : ∀ x, (g x).orderTop = e • x.orderTop) : f = g := by
  have hpolyHom :
      f.comp (algebraMap (Polynomial k) (LaurentSeries k)) =
        g.comp (algebraMap (Polynomial k) (LaurentSeries k)) := by
    apply Polynomial.ringHom_ext
    · intro a
      simpa using hC a
    · simpa using hX
  apply IsFractionRing.ringHom_ext (A := PowerSeries k)
  intro x
  apply HahnSeries.ext
  funext j
  let n : ℕ := j.natAbs + 1
  let p : PowerSeries k := (PowerSeries.trunc n x).toPowerSeries
  have hp : f (p : LaurentSeries k) = g (p : LaurentSeries k) := by
    exact DFunLike.congr_fun hpolyHom (PowerSeries.trunc n x)
  have htail : (((n : ℤ) : WithTop ℤ)) ≤
      ((x : LaurentSeries k) - (p : LaurentSeries k)).orderTop := by
    exact truncation_sub_orderTop x n
  have hftail : e • (((n : ℤ) : WithTop ℤ)) ≤
      (f ((x : LaurentSeries k) - (p : LaurentSeries k))).orderTop := by
    calc
      e • (((n : ℤ) : WithTop ℤ)) ≤
          e • ((x : LaurentSeries k) - (p : LaurentSeries k)).orderTop :=
        nsmul_le_nsmul_right htail e
      _ = _ := (hf _).symm
  have hgtail : e • (((n : ℤ) : WithTop ℤ)) ≤
      (g ((x : LaurentSeries k) - (p : LaurentSeries k))).orderTop := by
    calc
      e • (((n : ℤ) : WithTop ℤ)) ≤
          e • ((x : LaurentSeries k) - (p : LaurentSeries k)).orderTop :=
        nsmul_le_nsmul_right htail e
      _ = _ := (hg _).symm
  have hdiff : e • (((n : ℤ) : WithTop ℤ)) ≤
      (f (x : LaurentSeries k) - g (x : LaurentSeries k)).orderTop := by
    have htri := HahnSeries.min_orderTop_le_orderTop_sub
      (x := f ((x : LaurentSeries k) - (p : LaurentSeries k)))
      (y := g ((x : LaurentSeries k) - (p : LaurentSeries k)))
    have hrewrite :
        f ((x : LaurentSeries k) - (p : LaurentSeries k)) -
            g ((x : LaurentSeries k) - (p : LaurentSeries k)) =
          f (x : LaurentSeries k) - g (x : LaurentSeries k) := by
      rw [map_sub, map_sub, hp]
      ring
    rw [hrewrite] at htri
    exact (le_min hftail hgtail).trans htri
  have hj : (j : WithTop ℤ) <
      e • (((n : ℤ) : WithTop ℤ)) :=
    int_lt_positive_multiple j e he
  have hz := HahnSeries.coeff_eq_zero_of_lt_orderTop (hj.trans_le hdiff)
  simpa only [LaurentSeries.coe_algebraMap, HahnSeries.coeff_sub, sub_eq_zero] using hz

private theorem coefficientRingHom_algebraMap
    (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    (hcharF : ringChar F = ringChar (ResidueField F))
    (a : ResidueField F) :
    algebraMap (ringOfIntegers F) (ringOfIntegers E)
        (coefficientRingHom F hcharF a) =
      coefficientRingHom E
        (equalCharacteristic_of_valuativeExtension F E hcharF)
        (extensionResidueMap F E a) := by
  apply teichmuller_unique_of_pow_residueCard E
    (equalCharacteristic_of_valuativeExtension F E hcharF)
  · rw [residueCard_extension F E]
    apply pow_pow_fixed
    rw [← map_pow]
    exact congrArg (algebraMap (ringOfIntegers F) (ringOfIntegers E))
      (teichmuller_pow_residueCard F a)
  · exact teichmuller_pow_residueCard E (extensionResidueMap F E a)
  · rw [residueMap_algebraMap_integer F E]
    simp [coefficientRingHom]

/-- The coefficient-field embedding into the actual local field, obtained by composing the
constructed integral coefficient section with the valuation-ring inclusion. -/
def EqualCharacteristicPresentation.coefficientField
    {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (P : EqualCharacteristicPresentation K) :
    ResidueField K →+* K :=
  (algebraMap (ringOfIntegers K) K).comp P.coefficient

@[simp] theorem EqualCharacteristicPresentation.coefficientField_apply
    {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (P : EqualCharacteristicPresentation K)
    (a : ResidueField K) :
    P.coefficientField a = ((P.coefficient a : ringOfIntegers K) : K) := rfl

/-- A Laurent-series map is substitution by `u`, with coefficient map `i`, when it maps
constants by `i`, maps the variable to `u`, and scales Laurent order by the positive order
`e` of `u`. The order law supplies continuity at the Laurent topology. -/
def IsLaurentSubstitution {k K : Type*} [Field k] [Field K]
    (e : ℕ) (i : k →+* K) (u : LaurentSeries K)
    (f : LaurentSeries k →+* LaurentSeries K) : Prop :=
  (∀ a, f (HahnSeries.C a) = HahnSeries.C (i a)) ∧
    f (HahnSeries.single 1 1) = u ∧
    ∀ x, (f x).orderTop = e • x.orderTop

/-- Compatible equal-characteristic Laurent presentations of an actual finite separable
valuative extension. The final square is an equality of maps on the entire Laurent-series
field, not only on the chosen uniformizer. -/
structure EqualCharacteristicExtensionPresentation
    (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Finite F E] [Algebra.IsSeparable F E] where
  base : EqualCharacteristicPresentation F
  extension : EqualCharacteristicPresentation E
  coefficient_compatible : ∀ a,
    algebraMap (ringOfIntegers F) (ringOfIntegers E) (base.coefficient a) =
      extension.coefficient (extensionResidueMap F E a)
  uniformizerExpansion : LaurentSeries (ResidueField E)
  uniformizerExpansion_eq :
    extension.laurentEquiv uniformizerExpansion =
      algebraMap F E (base.uniformizer : F)
  uniformizerExpansion_order :
    uniformizerExpansion.orderTop =
      ((ramificationIndex F E : ℕ) : WithTop ℤ)
  substitution :
    LaurentSeries (ResidueField F) →+* LaurentSeries (ResidueField E)
  substitution_spec : IsLaurentSubstitution (ramificationIndex F E)
    (extensionResidueMap F E) uniformizerExpansion substitution
  algebraMap_coordinates :
    extension.laurentEquiv.toRingHom.comp substitution =
      (algebraMap F E).comp base.laurentEquiv.toRingHom

/-- The compatibility square evaluated on an arbitrary Laurent series. -/
theorem EqualCharacteristicExtensionPresentation.algebraMap_coordinates_apply
    {F E : Type*} [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Finite F E] [Algebra.IsSeparable F E]
    (P : EqualCharacteristicExtensionPresentation F E)
    (x : LaurentSeries (ResidueField F)) :
    P.extension.laurentEquiv (P.substitution x) =
      algebraMap F E (P.base.laurentEquiv x) := by
  exact DFunLike.congr_fun P.algebraMap_coordinates x

/-- The order-continuous substitution with prescribed coefficient map and image of the
variable is unique on all Laurent series. The proof uses polynomial truncations whose
orders tend to infinity. -/
theorem EqualCharacteristicExtensionPresentation.substitution_unique
    {F E : Type*} [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Finite F E] [Algebra.IsSeparable F E]
    (P : EqualCharacteristicExtensionPresentation F E)
    (f : LaurentSeries (ResidueField F) →+* LaurentSeries (ResidueField E))
    (hf : IsLaurentSubstitution (ramificationIndex F E)
      (extensionResidueMap F E) P.uniformizerExpansion f) :
    f = P.substitution := by
  apply laurentRingHom_ext_of_order (ramificationIndex F E)
    (ramificationIndex_pos F E)
  · intro a
    rw [hf.1 a, P.substitution_spec.1 a]
  · rw [hf.2.1, P.substitution_spec.2.1]
  · exact hf.2.2
  · exact P.substitution_spec.2.2

private noncomputable def coordinateAlgebraMap
    {F E : Type*} [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    (PF : EqualCharacteristicPresentation F)
    (PE : EqualCharacteristicPresentation E) :
    LaurentSeries (ResidueField F) →+* LaurentSeries (ResidueField E) :=
  PE.laurentEquiv.symm.toRingHom.comp
    ((algebraMap F E).comp PF.laurentEquiv.toRingHom)

private theorem presentationCoefficient_algebraMap
    {F E : Type*} [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    (PF : EqualCharacteristicPresentation F)
    (PE : EqualCharacteristicPresentation E) (a : ResidueField F) :
    algebraMap (ringOfIntegers F) (ringOfIntegers E) (PF.coefficient a) =
      PE.coefficient (extensionResidueMap F E a) := by
  rw [PF.coefficient_eq_teichmuller, PE.coefficient_eq_teichmuller]
  exact coefficientRingHom_algebraMap F E PF.equalCharacteristic a

private theorem presentationCoefficient_algebraMap_field
    {F E : Type*} [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    (PF : EqualCharacteristicPresentation F)
    (PE : EqualCharacteristicPresentation E) (a : ResidueField F) :
    algebraMap F E (PF.coefficientField a) =
      PE.coefficientField (extensionResidueMap F E a) := by
  have h := congrArg (fun x : ringOfIntegers E ↦ (x : E))
    (presentationCoefficient_algebraMap PF PE a)
  rw [show ((algebraMap (ringOfIntegers F) (ringOfIntegers E)
      (PF.coefficient a) : ringOfIntegers E) : E) =
      algebraMap F E ((PF.coefficient a : ringOfIntegers F) : F) by
        exact Valuation.HasExtension.val_algebraMap (PF.coefficient a)] at h
  exact h

private theorem coordinateAlgebraMap_C
    {F E : Type*} [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    (PF : EqualCharacteristicPresentation F)
    (PE : EqualCharacteristicPresentation E) (a : ResidueField F) :
    coordinateAlgebraMap PF PE (HahnSeries.C a) =
      HahnSeries.C (extensionResidueMap F E a) := by
  apply PE.laurentEquiv.injective
  change PE.laurentEquiv
      (PE.laurentEquiv.symm (algebraMap F E (PF.laurentEquiv (HahnSeries.C a)))) =
    PE.laurentEquiv (HahnSeries.C (extensionResidueMap F E a))
  rw [PE.laurentEquiv.apply_symm_apply]
  rw [PF.laurentEquiv_C, PE.laurentEquiv_C]
  exact presentationCoefficient_algebraMap_field PF PE a

private theorem coordinateAlgebraMap_order
    {F E : Type*} [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    (PF : EqualCharacteristicPresentation F)
    (PE : EqualCharacteristicPresentation E)
    (x : LaurentSeries (ResidueField F)) :
    (coordinateAlgebraMap PF PE x).orderTop =
      ramificationIndex F E • x.orderTop := by
  calc
    (coordinateAlgebraMap PF PE x).orderTop =
        ord E (PE.laurentEquiv (coordinateAlgebraMap PF PE x)) :=
      (PE.laurentEquiv_order _).symm
    _ = ord E (algebraMap F E (PF.laurentEquiv x)) := by
      simp [coordinateAlgebraMap]
    _ = ramificationIndex F E • ord F (PF.laurentEquiv x) :=
      ord_algebraMap F E _
    _ = ramificationIndex F E • x.orderTop := by
      rw [PF.laurentEquiv_order]

/-- Every actual finite separable valuative extension of equal-characteristic local fields
admits compatible coefficient fields and Laurent coordinates. Equal characteristic of the
top field and every compatibility law are derived from the base hypothesis. -/
private noncomputable def equalCharacteristicExtensionPresentation
    (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Finite F E] [Algebra.IsSeparable F E]
    (hchar : ringChar F = ringChar (ResidueField F)) :
    EqualCharacteristicExtensionPresentation F E := by
  let hcharE := equalCharacteristic_of_valuativeExtension F E hchar
  let PF := existsEqualCharacteristicPresentation F hchar
  let PE := existsEqualCharacteristicPresentation E hcharE
  let u : LaurentSeries (ResidueField E) :=
    PE.laurentEquiv.symm (algebraMap F E (PF.uniformizer : F))
  let subst := coordinateAlgebraMap PF PE
  have huEq : PE.laurentEquiv u = algebraMap F E (PF.uniformizer : F) := by
    exact PE.laurentEquiv.apply_symm_apply _
  have huOrder : u.orderTop =
      ((ramificationIndex F E : ℕ) : WithTop ℤ) := by
    calc
      u.orderTop = ord E (PE.laurentEquiv u) := (PE.laurentEquiv_order _).symm
      _ = ord E (algebraMap F E (PF.uniformizer : F)) := by rw [huEq]
      _ = ramificationIndex F E • ord F (PF.uniformizer : F) :=
        ord_algebraMap F E _
      _ = ramificationIndex F E • (1 : WithTop ℤ) := by
        rw [ord_uniformizer F PF.uniformizer_isUniformizer]
      _ = ((ramificationIndex F E : ℕ) : WithTop ℤ) := by
        simp
  have hsubstX : subst (HahnSeries.single 1 1) = u := by
    apply PE.laurentEquiv.injective
    change PE.laurentEquiv
        (PE.laurentEquiv.symm
          (algebraMap F E (PF.laurentEquiv (HahnSeries.single 1 1)))) =
      PE.laurentEquiv u
    rw [PE.laurentEquiv.apply_symm_apply, PF.laurentEquiv_X, huEq]
  have hsubstSquare : PE.laurentEquiv.toRingHom.comp subst =
      (algebraMap F E).comp PF.laurentEquiv.toRingHom := by
    ext x
    change PE.laurentEquiv
        (PE.laurentEquiv.symm (algebraMap F E (PF.laurentEquiv x))) =
      algebraMap F E (PF.laurentEquiv x)
    rw [PE.laurentEquiv.apply_symm_apply]
  exact
    { base := PF
      extension := PE
      coefficient_compatible := presentationCoefficient_algebraMap PF PE
      uniformizerExpansion := u
      uniformizerExpansion_eq := huEq
      uniformizerExpansion_order := huOrder
      substitution := subst
      substitution_spec :=
        ⟨coordinateAlgebraMap_C PF PE, hsubstX,
          coordinateAlgebraMap_order PF PE⟩
      algebraMap_coordinates := hsubstSquare }

/-- Existence of compatible equal-characteristic Laurent coordinates for an actual finite
separable valuative extension. No equal-characteristic or coordinate hypothesis is assumed
for the top field. -/
theorem exists_equalCharacteristicExtensionPresentation
    (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Finite F E] [Algebra.IsSeparable F E]
    (hchar : ringChar F = ringChar (ResidueField F)) :
    Nonempty (EqualCharacteristicExtensionPresentation F E) :=
  ⟨equalCharacteristicExtensionPresentation F E hchar⟩

end
end LanglandsSecondMainLemma.Residues
