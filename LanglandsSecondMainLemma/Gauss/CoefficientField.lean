import LanglandsSecondMainLemma.Gauss.MultiplicativeLifts
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# The cyclotomic coefficient field for the Gauss-sum argument

Following §7 of `epsilon_SML.tex`, this file adjoins a root of
`Φ_p(X + 1)` to the unramified coefficient ring. Eisenstein's criterion gives
the ramified extension, whose root is a uniformizer and whose fraction field
contains the required primitive `p`-th root of unity. The construction retains
the residue field and the multiplicative Teichmüller representatives. For
`p = 2`, the extension is identified explicitly with the unramified ring and
the uniformizer maps to `-2`.
-/

open Polynomial

namespace LanglandsSecondMainLemma.Gauss

noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]

def cyclotomicUniformizerPolynomial (U : UnramifiedCoefficientLift p k) :
    (AdjoinRoot U.polynomial)[X] :=
  ((cyclotomic p ℤ).comp (X + 1)).map (Int.castRingHom _)

omit [Finite k] in
private theorem unramifiedMaximalIdeal_eq_span_p (U : UnramifiedCoefficientLift p k) :
    letI : IsDomain (AdjoinRoot U.polynomial) :=
      AdjoinRoot.isDomain_of_prime U.polynomial_prime
    letI : IsLocalRing (AdjoinRoot U.polynomial) := U.localRing
    IsLocalRing.maximalIdeal (AdjoinRoot U.polynomial) =
      Ideal.span {(p : AdjoinRoot U.polynomial)} := by
  letI : IsDomain (AdjoinRoot U.polynomial) :=
    AdjoinRoot.isDomain_of_prime U.polynomial_prime
  letI : IsLocalRing (AdjoinRoot U.polynomial) := U.localRing
  rw [U.maximalIdeal_eq, PadicInt.maximalIdeal_eq_span_p, Ideal.map_span]
  simp

theorem cyclotomicUniformizerPolynomial_monic (U : UnramifiedCoefficientLift p k) :
    (cyclotomicUniformizerPolynomial p k U).Monic := by
  apply Polynomial.Monic.map
  rw [show (X + 1 : ℤ[X]) = X + C 1 by simp]
  exact (cyclotomic.monic p ℤ).comp (monic_X_add_C 1) (by
    rw [natDegree_X_add_C]
    exact one_ne_zero)

theorem cyclotomicUniformizerPolynomial_isEisenstein (U : UnramifiedCoefficientLift p k) :
    letI : IsDomain (AdjoinRoot U.polynomial) :=
      AdjoinRoot.isDomain_of_prime U.polynomial_prime
    letI : IsLocalRing (AdjoinRoot U.polynomial) := U.localRing
    (cyclotomicUniformizerPolynomial p k U).IsEisensteinAt
      (IsLocalRing.maximalIdeal (AdjoinRoot U.polynomial)) := by
  let R := AdjoinRoot U.polynomial
  letI : IsDomain R := AdjoinRoot.isDomain_of_prime U.polynomial_prime
  letI : IsLocalRing R := U.localRing
  letI : IsDiscreteValuationRing R := U.discreteValuationRing
  letI : Module.Free ℤ_[p] R := U.coefficientFree
  letI : CharZero R := Algebra.charZero_of_charZero ℤ_[p] R
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)} :=
    unramifiedMaximalIdeal_eq_span_p p k U
  have hmap : Ideal.map (Int.castRingHom R) (Ideal.span {(p : ℤ)}) =
      IsLocalRing.maximalIdeal R := by
    rw [hmax, Ideal.map_span]
    simp
  have hz := cyclotomic_comp_X_add_one_isEisensteinAt p
  refine (cyclotomicUniformizerPolynomial_monic p k U).isEisensteinAt_of_mem_of_notMem
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top ?_ ?_
  · intro n hn
    rw [cyclotomicUniformizerPolynomial, coeff_map, ← hmap]
    have hn' : n <
        (((cyclotomic p ℤ).comp (X + 1)).map (Int.castRingHom R)).natDegree := by
      simpa [cyclotomicUniformizerPolynomial] using hn
    rw [natDegree_map_eq_of_injective Int.cast_injective _] at hn'
    simpa only using Ideal.mem_map_of_mem (Int.castRingHom R) (hz.mem hn')
  · rw [cyclotomicUniformizerPolynomial, coeff_map]
    change (Int.castRingHom R) (((cyclotomic p ℤ).comp (X + 1)).coeff 0) ∉
      IsLocalRing.maximalIdeal R ^ 2
    rw [hmax, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    intro h
    have hp0 : (p : R) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    have hpirr : Irreducible (p : R) :=
      IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
        (p : R) hp0 hmax
    have hcoeff :
        (Int.castRingHom R) (((cyclotomic p ℤ).comp (X + 1)).coeff 0) = (p : R) := by
      rw [coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_one,
        zero_add, eval_one_cyclotomic_prime]
      rfl
    rw [hcoeff] at h
    obtain ⟨a, ha⟩ := h
    have hone : (1 : R) = (p : R) * a := by
      apply mul_left_cancel₀ hp0
      simpa [pow_two, mul_assoc] using ha
    exact hpirr.not_isUnit (isUnit_iff_dvd_one.mpr ⟨a, hone⟩)

private theorem adjoinRoot_coeff_zero_mem_span_root
    {R : Type*} [CommRing R] (Q : R[X]) :
    AdjoinRoot.of Q (Q.coeff 0) ∈
      Ideal.span {AdjoinRoot.root Q} := by
  rw [Ideal.mem_span_singleton]
  obtain ⟨g, hg⟩ := @Polynomial.X_dvd_sub_C R _ Q
  refine ⟨-AdjoinRoot.mk Q g, ?_⟩
  have h := congrArg (AdjoinRoot.mk Q) hg
  simp only [map_sub, AdjoinRoot.mk_self, AdjoinRoot.mk_C,
    AdjoinRoot.mk_X, map_mul, zero_sub] at h
  simpa [mul_comm] using congrArg Neg.neg h

theorem cyclotomicUniformizerPolynomial_prime (U : UnramifiedCoefficientLift p k) :
    letI : IsDomain (AdjoinRoot U.polynomial) :=
      AdjoinRoot.isDomain_of_prime U.polynomial_prime
    Prime (cyclotomicUniformizerPolynomial p k U) := by
  let R := AdjoinRoot U.polynomial
  letI : IsDomain R := AdjoinRoot.isDomain_of_prime U.polynomial_prime
  letI : IsLocalRing R := U.localRing
  letI : IsDiscreteValuationRing R := U.discreteValuationRing
  letI : Module.Free ℤ_[p] R := U.coefficientFree
  letI : CharZero R := Algebra.charZero_of_charZero ℤ_[p] R
  have he := cyclotomicUniformizerPolynomial_isEisenstein p k U
  have hm := cyclotomicUniformizerPolynomial_monic p k U
  apply UniqueFactorizationMonoid.irreducible_iff_prime.mp
  apply he.irreducible (IsLocalRing.maximalIdeal.isMaximal R).isPrime hm.isPrimitive
  rw [cyclotomicUniformizerPolynomial, natDegree_map_eq_of_injective Int.cast_injective,
    natDegree_comp, natDegree_cyclotomic, show (X + 1 : ℤ[X]) = X + C 1 by simp,
    natDegree_X_add_C, Nat.totient_prime (Fact.out : p.Prime), mul_one]
  exact Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt

private theorem cyclotomicBaseMap_injective (U : UnramifiedCoefficientLift p k) :
    letI : IsDomain (AdjoinRoot U.polynomial) :=
      AdjoinRoot.isDomain_of_prime U.polynomial_prime
    Function.Injective (AdjoinRoot.of (cyclotomicUniformizerPolynomial p k U)) := by
  letI : IsDomain (AdjoinRoot U.polynomial) :=
    AdjoinRoot.isDomain_of_prime U.polynomial_prime
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  intro hdegree
  have hone : cyclotomicUniformizerPolynomial p k U = 1 :=
    (cyclotomicUniformizerPolynomial_monic p k U).degree_le_zero_iff_eq_one.mp hdegree.le
  have hp := cyclotomicUniformizerPolynomial_prime p k U
  rw [hone] at hp
  exact hp.not_unit isUnit_one

omit [Finite k] in
private theorem baseMaximal_map_le_rootSpan
    (U : UnramifiedCoefficientLift p k) :
    letI : IsDomain (AdjoinRoot U.polynomial) :=
      AdjoinRoot.isDomain_of_prime U.polynomial_prime
    letI : IsLocalRing (AdjoinRoot U.polynomial) := U.localRing
    let Q := cyclotomicUniformizerPolynomial p k U
    Ideal.map (AdjoinRoot.of Q)
      (IsLocalRing.maximalIdeal (AdjoinRoot U.polynomial)) ≤
      Ideal.span {AdjoinRoot.root Q} := by
  dsimp only
  let R := AdjoinRoot U.polynomial
  letI : IsDomain R := AdjoinRoot.isDomain_of_prime U.polynomial_prime
  letI : IsLocalRing R := U.localRing
  let Q := cyclotomicUniformizerPolynomial p k U
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)} :=
    unramifiedMaximalIdeal_eq_span_p p k U
  have hcoeff : Q.coeff 0 = (p : R) := by
    dsimp only [Q]
    rw [cyclotomicUniformizerPolynomial, coeff_map, coeff_zero_eq_eval_zero, eval_comp,
      eval_add, eval_X, eval_one, zero_add, eval_one_cyclotomic_prime]
    rfl
  rw [hmax, Ideal.map_span, Set.image_singleton]
  rw [Ideal.span_le, Set.singleton_subset_iff, ← hcoeff]
  exact adjoinRoot_coeff_zero_mem_span_root Q

noncomputable def cyclotomicResidueMap
    (U : UnramifiedCoefficientLift p k) :
    letI : IsDomain (AdjoinRoot U.polynomial) :=
      AdjoinRoot.isDomain_of_prime U.polynomial_prime
    AdjoinRoot (cyclotomicUniformizerPolynomial p k U) →+* k := by
  let R := AdjoinRoot U.polynomial
  letI : IsDomain R := AdjoinRoot.isDomain_of_prime U.polynomial_prime
  letI : IsLocalRing R := U.localRing
  letI : CharP k p := charP_of_injective_algebraMap
    (RingHom.injective (algebraMap (ZMod p) k)) p
  let Q := cyclotomicUniformizerPolynomial p k U
  let φ : R →+* k := coefficientResidueMap p k U
  apply AdjoinRoot.lift φ 0
  rw [Polynomial.eval₂_at_zero]
  rw [cyclotomicUniformizerPolynomial, coeff_map,
    coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_one,
    zero_add, eval_one_cyclotomic_prime]
  change φ (p : R) = 0
  rw [map_natCast]
  exact CharP.cast_eq_zero k p

omit [Finite k] in
private theorem cyclotomicResidueMap_surjective
    (U : UnramifiedCoefficientLift p k) :
    letI : IsDomain (AdjoinRoot U.polynomial) :=
      AdjoinRoot.isDomain_of_prime U.polynomial_prime
    Function.Surjective (cyclotomicResidueMap p k U) := by
  letI : IsDomain (AdjoinRoot U.polynomial) :=
    AdjoinRoot.isDomain_of_prime U.polynomial_prime
  intro x
  obtain ⟨a, rfl⟩ := coefficientResidueMap_surjective p k U x
  refine ⟨AdjoinRoot.of (cyclotomicUniformizerPolynomial p k U) a, ?_⟩
  simp only [cyclotomicResidueMap, AdjoinRoot.lift_of]

private theorem adjoinRoot_mk_sub_coeff_zero_mem_span_root
    {R : Type*} [CommRing R] (Q g : R[X]) :
    AdjoinRoot.mk Q g - AdjoinRoot.of Q (g.coeff 0) ∈
      Ideal.span {AdjoinRoot.root Q} := by
  rw [Ideal.mem_span_singleton]
  obtain ⟨h, hh⟩ := @Polynomial.X_dvd_sub_C R _ g
  refine ⟨AdjoinRoot.mk Q h, ?_⟩
  have hm := congrArg (AdjoinRoot.mk Q) hh
  simpa only [map_sub, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_mul,
    mul_comm] using hm

omit [Finite k] in
private theorem cyclotomicResidueMap_ker
    (U : UnramifiedCoefficientLift p k) :
    letI : IsDomain (AdjoinRoot U.polynomial) :=
      AdjoinRoot.isDomain_of_prime U.polynomial_prime
    letI : IsDomain (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) :=
      AdjoinRoot.isDomain_of_prime (cyclotomicUniformizerPolynomial_prime p k U)
    RingHom.ker (cyclotomicResidueMap p k U) =
      Ideal.span {AdjoinRoot.root (cyclotomicUniformizerPolynomial p k U)} := by
  let R := AdjoinRoot U.polynomial
  letI : IsDomain R := AdjoinRoot.isDomain_of_prime U.polynomial_prime
  letI : IsLocalRing R := U.localRing
  let Q := cyclotomicUniformizerPolynomial p k U
  let φ : R →+* k := coefficientResidueMap p k U
  have hφ : Function.Surjective φ := coefficientResidueMap_surjective p k U
  have hbase : Ideal.map (AdjoinRoot.of Q) (IsLocalRing.maximalIdeal R) ≤
      Ideal.span {AdjoinRoot.root Q} :=
    baseMaximal_map_le_rootSpan p k U
  apply le_antisymm
  · intro y hy
    induction y using AdjoinRoot.induction_on with
    | ih g =>
      have hc : φ (g.coeff 0) = 0 := by
        rw [RingHom.mem_ker] at hy
        simpa only [cyclotomicResidueMap, AdjoinRoot.lift_mk,
          Polynomial.eval₂_at_zero] using hy
      have hcm : g.coeff 0 ∈ IsLocalRing.maximalIdeal R := by
        rw [← IsLocalRing.ker_eq_maximalIdeal φ hφ, RingHom.mem_ker]
        exact hc
      have hconst : AdjoinRoot.of Q (g.coeff 0) ∈
          Ideal.span {AdjoinRoot.root Q} :=
        hbase (Ideal.mem_map_of_mem (AdjoinRoot.of Q) hcm)
      have hsub := adjoinRoot_mk_sub_coeff_zero_mem_span_root Q g
      simpa only [sub_add_cancel] using
        (Ideal.add_mem (Ideal.span {AdjoinRoot.root Q}) hsub hconst)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change (cyclotomicResidueMap p k U) (AdjoinRoot.root Q) = 0
    unfold cyclotomicResidueMap
    apply AdjoinRoot.lift_root

omit [Finite k] in
private theorem rootSpan_isMaximal
    (U : UnramifiedCoefficientLift p k) :
    letI : IsDomain (AdjoinRoot U.polynomial) :=
      AdjoinRoot.isDomain_of_prime U.polynomial_prime
    letI : IsDomain (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) :=
      AdjoinRoot.isDomain_of_prime (cyclotomicUniformizerPolynomial_prime p k U)
    (Ideal.span {AdjoinRoot.root (cyclotomicUniformizerPolynomial p k U)}).IsMaximal := by
  letI : IsDomain (AdjoinRoot U.polynomial) :=
    AdjoinRoot.isDomain_of_prime U.polynomial_prime
  let Q := cyclotomicUniformizerPolynomial p k U
  let I : Ideal (AdjoinRoot Q) := Ideal.span {AdjoinRoot.root Q}
  have hker : RingHom.ker (cyclotomicResidueMap p k U) = I :=
    cyclotomicResidueMap_ker p k U
  have hsurj : Function.Surjective (cyclotomicResidueMap p k U) :=
    cyclotomicResidueMap_surjective p k U
  let e : (AdjoinRoot Q ⧸ I) ≃+* k :=
    (Ideal.quotEquivOfEq hker.symm).trans
      (RingHom.quotientKerEquivOfSurjective hsurj)
  apply (Ideal.Quotient.maximal_ideal_iff_isField_quotient I).mpr
  exact e.toMulEquiv.isField (Field.toIsField k)

private theorem root_pow_mem_baseMaximal
    (U : UnramifiedCoefficientLift p k) :
    letI : IsDomain (AdjoinRoot U.polynomial) :=
      AdjoinRoot.isDomain_of_prime U.polynomial_prime
    letI : IsLocalRing (AdjoinRoot U.polynomial) := U.localRing
    let Q := cyclotomicUniformizerPolynomial p k U
    AdjoinRoot.root Q ^ Q.natDegree ∈
      Ideal.map (algebraMap (AdjoinRoot U.polynomial) (AdjoinRoot Q))
        (IsLocalRing.maximalIdeal (AdjoinRoot U.polynomial)) := by
  letI : IsDomain (AdjoinRoot U.polynomial) :=
    AdjoinRoot.isDomain_of_prime U.polynomial_prime
  letI : IsLocalRing (AdjoinRoot U.polynomial) := U.localRing
  have hinj : Function.Injective
      (algebraMap (AdjoinRoot U.polynomial)
        (AdjoinRoot (cyclotomicUniformizerPolynomial p k U))) := by
    simpa only [AdjoinRoot.algebraMap_eq] using cyclotomicBaseMap_injective p k U
  exact (cyclotomicUniformizerPolynomial_isEisenstein p k U).isWeaklyEisensteinAt
    |>.pow_natDegree_le_of_aeval_zero_of_monic_mem_map
      (x := AdjoinRoot.root (cyclotomicUniformizerPolynomial p k U)) (by simp)
        (cyclotomicUniformizerPolynomial_monic p k U) (cyclotomicUniformizerPolynomial p k U).natDegree (by
          rw [natDegree_map_eq_of_injective hinj])

private theorem cyclotomicCoefficientLocalRing
    (U : UnramifiedCoefficientLift p k) :
    letI : IsDomain (AdjoinRoot U.polynomial) :=
      AdjoinRoot.isDomain_of_prime U.polynomial_prime
    letI : IsDomain (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) :=
      AdjoinRoot.isDomain_of_prime (cyclotomicUniformizerPolynomial_prime p k U)
    IsLocalRing (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) := by
  let R := AdjoinRoot U.polynomial
  letI : IsDomain R := AdjoinRoot.isDomain_of_prime U.polynomial_prime
  letI : IsLocalRing R := U.localRing
  let Q := cyclotomicUniformizerPolynomial p k U
  letI : IsDomain (AdjoinRoot Q) :=
    AdjoinRoot.isDomain_of_prime (cyclotomicUniformizerPolynomial_prime p k U)
  letI : Module.Finite R (AdjoinRoot Q) := (cyclotomicUniformizerPolynomial_monic p k U).finite_adjoinRoot
  let I : Ideal (AdjoinRoot Q) := Ideal.span {AdjoinRoot.root Q}
  have hImax : I.IsMaximal := rootSpan_isMaximal p k U
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨I, hImax, ?_⟩
  intro J hJ
  letI : J.IsMaximal := hJ
  have hcomap : J.comap (algebraMap R (AdjoinRoot Q)) =
      IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal J)
  have hmaple : Ideal.map (algebraMap R (AdjoinRoot Q))
      (IsLocalRing.maximalIdeal R) ≤ J := by
    rw [Ideal.map_le_iff_le_comap, hcomap]
  have hrootpow : AdjoinRoot.root Q ^ Q.natDegree ∈
      Ideal.map (algebraMap R (AdjoinRoot Q))
        (IsLocalRing.maximalIdeal R) :=
    root_pow_mem_baseMaximal p k U
  have hroot : AdjoinRoot.root Q ∈ J :=
    hJ.isPrime.mem_of_pow_mem Q.natDegree (hmaple hrootpow)
  have hIJ : I ≤ J := by
    change Ideal.span {AdjoinRoot.root Q} ≤ J
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hroot
  exact (hImax.eq_of_le hJ.ne_top hIJ).symm

private theorem cyclotomicCoefficientMaximalIdeal
    (U : UnramifiedCoefficientLift p k) :
    letI : IsDomain (AdjoinRoot U.polynomial) :=
      AdjoinRoot.isDomain_of_prime U.polynomial_prime
    letI : IsDomain (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) :=
      AdjoinRoot.isDomain_of_prime (cyclotomicUniformizerPolynomial_prime p k U)
    letI : IsLocalRing (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) := cyclotomicCoefficientLocalRing p k U
    IsLocalRing.maximalIdeal (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) =
      Ideal.span {AdjoinRoot.root (cyclotomicUniformizerPolynomial p k U)} := by
  letI : IsDomain (AdjoinRoot U.polynomial) :=
    AdjoinRoot.isDomain_of_prime U.polynomial_prime
  letI : IsDomain (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) :=
    AdjoinRoot.isDomain_of_prime (cyclotomicUniformizerPolynomial_prime p k U)
  letI : IsLocalRing (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) := cyclotomicCoefficientLocalRing p k U
  exact (IsLocalRing.eq_maximalIdeal (rootSpan_isMaximal p k U)).symm

private theorem cyclotomicUniformizer_ne_zero
    (U : UnramifiedCoefficientLift p k) :
    letI : IsDomain (AdjoinRoot U.polynomial) :=
      AdjoinRoot.isDomain_of_prime U.polynomial_prime
    AdjoinRoot.root (cyclotomicUniformizerPolynomial p k U) ≠ 0 := by
  let R := AdjoinRoot U.polynomial
  letI : IsDomain R := AdjoinRoot.isDomain_of_prime U.polynomial_prime
  letI : IsLocalRing R := U.localRing
  let Q := cyclotomicUniformizerPolynomial p k U
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)} :=
    unramifiedMaximalIdeal_eq_span_p p k U
  have hpbase : (p : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [hmax]
    exact Submodule.mem_span_singleton_self (p : R)
  have hpimage : AdjoinRoot.of Q (p : R) ∈
      Ideal.span {AdjoinRoot.root Q} :=
    baseMaximal_map_le_rootSpan p k U
      (Ideal.mem_map_of_mem (AdjoinRoot.of Q) hpbase)
  intro hroot
  rw [hroot, Set.singleton_zero, Ideal.span_zero] at hpimage
  have hpimage0 : AdjoinRoot.of Q (p : R) = 0 := by
    simpa only [Ideal.mem_bot] using hpimage
  have hpzero : (p : R) = 0 := by
    apply cyclotomicBaseMap_injective p k U
    simpa only [map_zero] using hpimage0
  letI : Module.Free ℤ_[p] R := U.coefficientFree
  letI : CharZero R := Algebra.charZero_of_charZero ℤ_[p] R
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hpzero

private theorem cyclotomicCoefficientDVR
    (U : UnramifiedCoefficientLift p k) :
    letI : IsDomain (AdjoinRoot U.polynomial) :=
      AdjoinRoot.isDomain_of_prime U.polynomial_prime
    letI : IsDomain (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) :=
      AdjoinRoot.isDomain_of_prime (cyclotomicUniformizerPolynomial_prime p k U)
    letI : IsLocalRing (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) := cyclotomicCoefficientLocalRing p k U
    IsDiscreteValuationRing (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) := by
  let R := AdjoinRoot U.polynomial
  letI : IsDomain R := AdjoinRoot.isDomain_of_prime U.polynomial_prime
  letI : IsLocalRing R := U.localRing
  letI : IsDiscreteValuationRing R := U.discreteValuationRing
  let Q := cyclotomicUniformizerPolynomial p k U
  letI : IsDomain (AdjoinRoot Q) :=
    AdjoinRoot.isDomain_of_prime (cyclotomicUniformizerPolynomial_prime p k U)
  letI : IsLocalRing (AdjoinRoot Q) := cyclotomicCoefficientLocalRing p k U
  letI : Module.Finite R (AdjoinRoot Q) := (cyclotomicUniformizerPolynomial_monic p k U).finite_adjoinRoot
  letI : IsNoetherianRing (AdjoinRoot Q) :=
    IsNoetherianRing.of_finite R (AdjoinRoot Q)
  have hmax := cyclotomicCoefficientMaximalIdeal p k U
  have hmaxne : IsLocalRing.maximalIdeal (AdjoinRoot Q) ≠ ⊥ := by
    rw [hmax]
    exact mt Ideal.span_singleton_eq_bot.mp (cyclotomicUniformizer_ne_zero p k U)
  have hnotfield : ¬ IsField (AdjoinRoot Q) :=
    IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr hmaxne
  have hprincipal :
      (IsLocalRing.maximalIdeal (AdjoinRoot Q)).IsPrincipal := by
    rw [hmax]
    infer_instance
  exact ((IsDiscreteValuationRing.TFAE (AdjoinRoot Q) hnotfield).out 4 0).mp
    hprincipal

private noncomputable def cyclotomicCoefficientResidueEquiv
    (U : UnramifiedCoefficientLift p k) :
    letI : IsDomain (AdjoinRoot U.polynomial) :=
      AdjoinRoot.isDomain_of_prime U.polynomial_prime
    letI : IsDomain (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) :=
      AdjoinRoot.isDomain_of_prime (cyclotomicUniformizerPolynomial_prime p k U)
    letI : IsLocalRing (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) := cyclotomicCoefficientLocalRing p k U
    IsLocalRing.ResidueField (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) ≃+* k := by
  letI : IsDomain (AdjoinRoot U.polynomial) :=
    AdjoinRoot.isDomain_of_prime U.polynomial_prime
  let Q := cyclotomicUniformizerPolynomial p k U
  letI : IsDomain (AdjoinRoot Q) :=
    AdjoinRoot.isDomain_of_prime (cyclotomicUniformizerPolynomial_prime p k U)
  letI : IsLocalRing (AdjoinRoot Q) := cyclotomicCoefficientLocalRing p k U
  let hker := cyclotomicResidueMap_ker p k U
  exact (Ideal.quotEquivOfEq (by rw [cyclotomicCoefficientMaximalIdeal p k U, ← hker])).trans
    (RingHom.quotientKerEquivOfSurjective (cyclotomicResidueMap_surjective p k U))

noncomputable def cyclotomicZeta (U : UnramifiedCoefficientLift p k) :
    AdjoinRoot (cyclotomicUniformizerPolynomial p k U) :=
  AdjoinRoot.root (cyclotomicUniformizerPolynomial p k U) + 1

private theorem cyclotomicZeta_primitive
    (U : UnramifiedCoefficientLift p k) :
    letI : IsDomain (AdjoinRoot U.polynomial) :=
      AdjoinRoot.isDomain_of_prime U.polynomial_prime
    letI : IsDomain (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) :=
      AdjoinRoot.isDomain_of_prime (cyclotomicUniformizerPolynomial_prime p k U)
    IsPrimitiveRoot (cyclotomicZeta p k U) p := by
  let R := AdjoinRoot U.polynomial
  letI : IsDomain R := AdjoinRoot.isDomain_of_prime U.polynomial_prime
  letI : Module.Free ℤ_[p] R := U.coefficientFree
  letI : CharZero R := Algebra.charZero_of_charZero ℤ_[p] R
  letI : IsDomain (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) :=
    AdjoinRoot.isDomain_of_prime (cyclotomicUniformizerPolynomial_prime p k U)
  letI : Module.Free R (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) :=
    (cyclotomicUniformizerPolynomial_monic p k U).free_adjoinRoot
  letI : CharZero (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) :=
    Algebra.charZero_of_charZero R (AdjoinRoot (cyclotomicUniformizerPolynomial p k U))
  apply (isRoot_cyclotomic_iff_charZero (Fact.out : p.Prime).pos).mp
  rw [Polynomial.IsRoot.def, ← map_cyclotomic_int, eval_map]
  have hroot := AdjoinRoot.eval₂_root (cyclotomicUniformizerPolynomial p k U)
  change (((cyclotomic p ℤ).comp (X + 1)).map (Int.castRingHom R)).eval₂
    (AdjoinRoot.of (cyclotomicUniformizerPolynomial p k U))
      (AdjoinRoot.root (cyclotomicUniformizerPolynomial p k U)) = 0 at hroot
  rw [eval₂_map, eval₂_comp] at hroot
  have hcast : (AdjoinRoot.of (cyclotomicUniformizerPolynomial p k U)).comp (Int.castRingHom R) =
      Int.castRingHom (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) := by
    ext z
    simp
  rw [hcast] at hroot
  simpa only [cyclotomicZeta, eval₂_add, eval₂_X, eval₂_one,
    RingHom.comp_apply, map_intCast, add_comm] using hroot

private theorem mem_smul_top_iff_basis_repr
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι A M)
    (I : Ideal A) (x : M) :
    x ∈ I • (⊤ : Submodule A M) ↔ ∀ i, b.repr x i ∈ I := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y hy
      simpa using I.mul_mem_right (b.repr y i) hr
    · intro x y hx hy
      simpa using I.add_mem hx hy
  · intro hx
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem_smul (hx i) (Submodule.mem_top)

private theorem isAdicComplete_of_finite_basis'
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι A M)
    (I : Ideal A) [IsAdicComplete I A] : IsAdicComplete I M where
  haus' x hx := by
    apply b.repr.injective
    ext i
    have : b.repr x i = 0 := by
      apply IsHausdorff.haus (I := I) (IsAdicComplete.toIsHausdorff)
      intro n
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      have hxn := hx n
      rw [SModEq.zero] at hxn
      exact (mem_smul_top_iff_basis_repr b (I ^ n) x).mp hxn i
    simpa using this
  prec' f hf := by
    have hcoord (i : ι) :
        ∃ L : A, ∀ n, b.repr (f n) i ≡ L
          [SMOD (I ^ n • ⊤ : Submodule A A)] := by
      apply IsPrecomplete.prec (I := I) (M := A)
        (IsAdicComplete.toIsPrecomplete)
      intro m n hmn
      rw [SModEq.sub_mem]
      have hmn' := hf hmn
      rw [SModEq.sub_mem] at hmn'
      have hmem :=
        (mem_smul_top_iff_basis_repr b (I ^ m) (f m - f n)).mp hmn' i
      simpa [smul_eq_mul, Ideal.mul_top] using hmem
    choose L hL using hcoord
    refine ⟨b.equivFun.symm L, fun n ↦ ?_⟩
    rw [SModEq.sub_mem]
    apply (mem_smul_top_iff_basis_repr b (I ^ n) _).mpr
    intro i
    have hi := hL i n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hi
    simpa [Module.Basis.equivFun] using hi

private theorem isAdicComplete_of_cofinal_ideals
    {A : Type*} [CommRing A] (I J : Ideal A) (e : ℕ) (he : 0 < e)
    (hIJ : I ^ e ≤ J) (hJI : J ≤ I) [IsAdicComplete J A] :
    IsAdicComplete I A where
  haus' x hx := by
    apply IsHausdorff.haus (I := J) (IsAdicComplete.toIsHausdorff)
    intro n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    have hxn := hx (e * n)
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top] at hxn
    have hpow := pow_le_pow_left' hIJ n
    rw [pow_mul] at hxn
    exact hpow hxn
  prec' f hf := by
    let g : ℕ → A := fun n ↦ f (e * n)
    have hg : ∀ {m n}, m ≤ n →
        g m ≡ g n [SMOD (J ^ m • ⊤ : Submodule A A)] := by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have hmn' := hf (Nat.mul_le_mul_left e hmn)
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hmn'
      have hpow := pow_le_pow_left' hIJ m
      rw [pow_mul] at hmn'
      exact hpow hmn'
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := J)
      (IsAdicComplete.toIsPrecomplete) hg
    refine ⟨L, fun n ↦ ?_⟩
    have hnle : n ≤ e * n := by
      calc
        n = 1 * n := by simp
        _ ≤ e * n := Nat.mul_le_mul_right n he
    have hfirst := hf hnle
    have hsecond := hL n
    apply hfirst.trans
    apply SModEq.of_toAddSubgroup_le
      (U := J ^ n • (⊤ : Submodule A A))
      (V := I ^ n • (⊤ : Submodule A A))
    · rw [smul_eq_mul, smul_eq_mul, Ideal.mul_top, Ideal.mul_top]
      exact pow_le_pow_left' hJI n
    · exact hsecond

private theorem cyclotomicCoefficientComplete
    (U : UnramifiedCoefficientLift p k) :
    letI : IsDomain (AdjoinRoot U.polynomial) :=
      AdjoinRoot.isDomain_of_prime U.polynomial_prime
    letI : IsDomain (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) :=
      AdjoinRoot.isDomain_of_prime (cyclotomicUniformizerPolynomial_prime p k U)
    letI : IsLocalRing (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) := cyclotomicCoefficientLocalRing p k U
    IsAdicComplete
      (IsLocalRing.maximalIdeal (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)))
      (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) := by
  let R := AdjoinRoot U.polynomial
  letI : IsDomain R := AdjoinRoot.isDomain_of_prime U.polynomial_prime
  letI : IsLocalRing R := U.localRing
  letI : Module.Free ℤ_[p] R := U.coefficientFree
  letI : CharZero R := Algebra.charZero_of_charZero ℤ_[p] R
  letI : IsAdicComplete (IsLocalRing.maximalIdeal R) R := U.complete
  let Q := cyclotomicUniformizerPolynomial p k U
  letI : IsDomain (AdjoinRoot Q) :=
    AdjoinRoot.isDomain_of_prime (cyclotomicUniformizerPolynomial_prime p k U)
  letI : IsLocalRing (AdjoinRoot Q) := cyclotomicCoefficientLocalRing p k U
  letI : Module.Free R (AdjoinRoot Q) := (cyclotomicUniformizerPolynomial_monic p k U).free_adjoinRoot
  letI : Module.Finite R (AdjoinRoot Q) := (cyclotomicUniformizerPolynomial_monic p k U).finite_adjoinRoot
  let I := IsLocalRing.maximalIdeal (AdjoinRoot Q)
  let J := Ideal.map (algebraMap R (AdjoinRoot Q))
    (IsLocalRing.maximalIdeal R)
  have hbase : IsAdicComplete (IsLocalRing.maximalIdeal R) (AdjoinRoot Q) :=
    isAdicComplete_of_finite_basis'
      (AdjoinRoot.powerBasis' (cyclotomicUniformizerPolynomial_monic p k U)).basis
        (IsLocalRing.maximalIdeal R)
  letI : IsAdicComplete J (AdjoinRoot Q) :=
    (IsAdicComplete.map_algebraMap_iff
      (IsLocalRing.maximalIdeal R) (AdjoinRoot Q)).mpr hbase
  have he : 0 < Q.natDegree := by
    dsimp only [Q]
    unfold cyclotomicUniformizerPolynomial
    rw [natDegree_map_eq_of_injective Int.cast_injective,
      natDegree_comp, natDegree_cyclotomic,
      show (X + 1 : ℤ[X]) = X + C 1 by simp, natDegree_X_add_C,
      Nat.totient_prime (Fact.out : p.Prime), mul_one]
    exact Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  have hIJ : I ^ Q.natDegree ≤ J := by
    dsimp only [I, J]
    rw [cyclotomicCoefficientMaximalIdeal p k U,
      Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
    exact root_pow_mem_baseMaximal p k U
  have hJI : J ≤ I := by
    dsimp only [I, J]
    change Ideal.map (AdjoinRoot.of Q) (IsLocalRing.maximalIdeal R) ≤
      IsLocalRing.maximalIdeal (AdjoinRoot Q)
    rw [cyclotomicCoefficientMaximalIdeal p k U]
    exact baseMaximal_map_le_rootSpan p k U
  exact isAdicComplete_of_cofinal_ideals I J Q.natDegree he hIJ hJI

theorem cyclotomicUniformizerPolynomial_two
    (U : UnramifiedCoefficientLift p k) (hp : p = 2) :
    cyclotomicUniformizerPolynomial p k U = X + C (2 : AdjoinRoot U.polynomial) := by
  subst p
  simp only [cyclotomicUniformizerPolynomial, cyclotomic_two,
    add_comp, X_comp, one_comp, map_ofNat]
  rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_X,
    Polynomial.map_one]
  ring

private noncomputable def cyclotomicTwoEquiv
    (U : UnramifiedCoefficientLift p k) (hp : p = 2) :
    AdjoinRoot (cyclotomicUniformizerPolynomial p k U) ≃+* AdjoinRoot U.polynomial := by
  let R := AdjoinRoot U.polynomial
  let Q := cyclotomicUniformizerPolynomial p k U
  have hroot : Q.eval₂ (RingHom.id R) (-2) = 0 := by
    change (cyclotomicUniformizerPolynomial p k U).eval₂ (RingHom.id R) (-2) = 0
    rw [cyclotomicUniformizerPolynomial_two p k U hp]
    simp
  let f : AdjoinRoot Q →+* R := AdjoinRoot.lift (RingHom.id R) (-2) hroot
  let g : R →+* AdjoinRoot Q := AdjoinRoot.of Q
  apply RingEquiv.ofRingHom f g
  · apply DFunLike.ext _ _
    intro r
    simp [f, g]
  · apply AdjoinRoot.ringHom_ext
    · apply DFunLike.ext _ _
      intro r
      simp [f, g]
    · simp only [RingHom.comp_apply, f, g, AdjoinRoot.lift_root,
        RingHom.id_apply]
      have hQroot := AdjoinRoot.eval₂_root Q
      change (cyclotomicUniformizerPolynomial p k U).eval₂ (AdjoinRoot.of Q)
        (AdjoinRoot.root Q) = 0 at hQroot
      rw [cyclotomicUniformizerPolynomial_two p k U hp] at hQroot
      simp only [eval₂_add, eval₂_X, eval₂_C] at hQroot
      rw [map_neg]
      exact (eq_neg_of_add_eq_zero_left hQroot).symm

private theorem cyclotomicTwoEquiv_root
    (U : UnramifiedCoefficientLift p k) (hp : p = 2) :
    cyclotomicTwoEquiv p k U hp (AdjoinRoot.root (cyclotomicUniformizerPolynomial p k U)) =
      (-2 : AdjoinRoot U.polynomial) := by
  let hroot : (cyclotomicUniformizerPolynomial p k U).eval₂
      (RingHom.id (AdjoinRoot U.polynomial)) (-2) = 0 := by
    rw [cyclotomicUniformizerPolynomial_two p k U hp]
    simp
  change (AdjoinRoot.lift (RingHom.id (AdjoinRoot U.polynomial))
    (-2) hroot) (AdjoinRoot.root (cyclotomicUniformizerPolynomial p k U)) = -2
  apply AdjoinRoot.lift_root

/-- The complete coefficient-ring data used for the appendix Gauss sums. -/
structure GaussCoefficientField where
  unramified : UnramifiedCoefficientLift p k
  multiplicativeLift : MultiplicativeResidueLift p k unramified
  cyclotomicPrime : Prime (cyclotomicUniformizerPolynomial p k unramified)
  coefficientDomain : IsDomain (AdjoinRoot (cyclotomicUniformizerPolynomial p k unramified))
  coefficientLocalRing :
    letI : IsDomain (AdjoinRoot (cyclotomicUniformizerPolynomial p k unramified)) := coefficientDomain
    IsLocalRing (AdjoinRoot (cyclotomicUniformizerPolynomial p k unramified))
  coefficientDVR :
    letI : IsDomain (AdjoinRoot (cyclotomicUniformizerPolynomial p k unramified)) := coefficientDomain
    letI : IsLocalRing (AdjoinRoot (cyclotomicUniformizerPolynomial p k unramified)) := coefficientLocalRing
    IsDiscreteValuationRing (AdjoinRoot (cyclotomicUniformizerPolynomial p k unramified))
  coefficientComplete :
    letI : IsDomain (AdjoinRoot (cyclotomicUniformizerPolynomial p k unramified)) := coefficientDomain
    letI : IsLocalRing (AdjoinRoot (cyclotomicUniformizerPolynomial p k unramified)) := coefficientLocalRing
    IsAdicComplete
      (IsLocalRing.maximalIdeal (AdjoinRoot (cyclotomicUniformizerPolynomial p k unramified)))
      (AdjoinRoot (cyclotomicUniformizerPolynomial p k unramified))
  residueEquiv :
    letI : IsDomain (AdjoinRoot (cyclotomicUniformizerPolynomial p k unramified)) := coefficientDomain
    letI : IsLocalRing (AdjoinRoot (cyclotomicUniformizerPolynomial p k unramified)) := coefficientLocalRing
    IsLocalRing.ResidueField (AdjoinRoot (cyclotomicUniformizerPolynomial p k unramified)) ≃+* k
  zetaPrimitive :
    letI : IsDomain (AdjoinRoot (cyclotomicUniformizerPolynomial p k unramified)) := coefficientDomain
    IsPrimitiveRoot (cyclotomicZeta p k unramified) p

namespace GaussCoefficientField

abbrev UnramifiedRing (C : GaussCoefficientField p k) :=
  AdjoinRoot C.unramified.polynomial

abbrev IntegerRing (C : GaussCoefficientField p k) :=
  AdjoinRoot (cyclotomicUniformizerPolynomial p k C.unramified)

abbrev CoefficientField (C : GaussCoefficientField p k) :=
  FractionRing C.IntegerRing

noncomputable def zeta (C : GaussCoefficientField p k) : C.IntegerRing :=
  cyclotomicZeta p k C.unramified

noncomputable def uniformizer (C : GaussCoefficientField p k) : C.IntegerRing :=
  AdjoinRoot.root (cyclotomicUniformizerPolynomial p k C.unramified)

end GaussCoefficientField

/-- The unramified lift and its Teichmüller section extend to a complete DVR
containing a primitive `p`-th root of unity and having residue field `k`. -/
theorem gaussCoefficientField_exists : Nonempty (GaussCoefficientField p k) := by
  obtain ⟨U⟩ := unramifiedCoefficientLift_exists p k
  obtain ⟨D⟩ := multiplicativeResidueLift_exists p k U
  let hprime := cyclotomicUniformizerPolynomial_prime p k U
  let hdomain : IsDomain (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) :=
    AdjoinRoot.isDomain_of_prime hprime
  let hlocal :
      letI : IsDomain (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) := hdomain
      IsLocalRing (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) := cyclotomicCoefficientLocalRing p k U
  let hdvr :
      letI : IsDomain (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) := hdomain
      letI : IsLocalRing (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) := hlocal
      IsDiscreteValuationRing (AdjoinRoot (cyclotomicUniformizerPolynomial p k U)) := cyclotomicCoefficientDVR p k U
  refine ⟨{
    unramified := U
    multiplicativeLift := D
    cyclotomicPrime := hprime
    coefficientDomain := hdomain
    coefficientLocalRing := hlocal
    coefficientDVR := hdvr
    coefficientComplete := cyclotomicCoefficientComplete p k U
    residueEquiv := cyclotomicCoefficientResidueEquiv p k U
    zetaPrimitive := cyclotomicZeta_primitive p k U
  }⟩

/-- The Teichmüller section, now viewed in the ramified coefficient ring. -/
noncomputable def teichmuller_lift (C : GaussCoefficientField p k) :
    k →*₀ C.IntegerRing :=
  (AdjoinRoot.of (cyclotomicUniformizerPolynomial p k C.unramified)).toMonoidWithZeroHom.comp
    C.multiplicativeLift.lift

theorem teichmuller_lift_reduction (C : GaussCoefficientField p k) (x : k) :
    cyclotomicResidueMap p k C.unramified (teichmuller_lift p k C x) = x := by
  calc
    cyclotomicResidueMap p k C.unramified (teichmuller_lift p k C x) =
        coefficientResidueMap p k C.unramified
          (C.multiplicativeLift.lift x) := by
      simp only [teichmuller_lift, MonoidWithZeroHom.coe_comp,
        Function.comp_apply]
      unfold cyclotomicResidueMap
      apply AdjoinRoot.lift_of
    _ = x := C.multiplicativeLift.reduction x

/-- The adjoined root generates the maximal ideal, i.e. it is the
cyclotomic uniformizer `ζ - 1`. -/
theorem cyclotomicUniformizer (C : GaussCoefficientField p k) :
    letI : IsDomain C.IntegerRing := C.coefficientDomain
    letI : IsLocalRing C.IntegerRing := C.coefficientLocalRing
    IsLocalRing.maximalIdeal C.IntegerRing = Ideal.span {C.uniformizer} := by
  exact cyclotomicCoefficientMaximalIdeal p k C.unramified

theorem cyclotomicUniformizer_irreducible (C : GaussCoefficientField p k) :
    letI : IsDomain C.IntegerRing := C.coefficientDomain
    letI : IsLocalRing C.IntegerRing := C.coefficientLocalRing
    letI : IsDiscreteValuationRing C.IntegerRing := C.coefficientDVR
    Irreducible C.uniformizer := by
  letI : IsDomain C.IntegerRing := C.coefficientDomain
  letI : IsLocalRing C.IntegerRing := C.coefficientLocalRing
  letI : IsDiscreteValuationRing C.IntegerRing := C.coefficientDVR
  apply IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
  · exact cyclotomicUniformizer_ne_zero p k C.unramified
  · exact cyclotomicUniformizer p k C

/-- In residue characteristic two the cyclotomic extension is the original
unramified ring, and the chosen root corresponds to `-2`. -/
noncomputable def GaussCoefficientField.equivUnramifiedOfTwo
    (C : GaussCoefficientField p k) (hp : p = 2) :
    C.IntegerRing ≃+* C.UnramifiedRing :=
  cyclotomicTwoEquiv p k C.unramified hp

theorem GaussCoefficientField.equivUnramifiedOfTwo_uniformizer
    (C : GaussCoefficientField p k) (hp : p = 2) :
    C.equivUnramifiedOfTwo p k hp C.uniformizer =
      (-2 : C.UnramifiedRing) :=
  cyclotomicTwoEquiv_root p k C.unramified hp

end
end LanglandsSecondMainLemma.Gauss
