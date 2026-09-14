import LanglandsSecondMainLemma.Residues.Substitution
import LanglandsSecondMainLemma.Residues.FreeBasis

/-!
# Trace and residue under a ramified substitution

This file proves Appendix B, Lemma B.3 of the corrected SML manuscript.  If
`u = X ^ e * v`, where `e > 0` and `v` has unit constant coefficient, the
algebraic trace on the finite free extension `k((t)) / k((u))` satisfies

`Res_s (Tr(h) ds) = Res_t (h * u' dt)`.

The characteristic-zero proof adjoins a formal `e`-th root of `v`, changes to
the order-one parameter `X * root(v)`, and reduces the trace to the pure-power
basis.  For arbitrary characteristic, the two residue coefficients are
specialized from a Laurent-localized integral polynomial coefficient ring.
Thus the proof never divides by `e` in the target field and includes the case
where the derivative of `u` vanishes.
-/

open scoped PowerSeries LaurentSeries
open HahnSeries

namespace Test

private def stretchHom (e : ℕ) : ℤ →+ ℤ where
  toFun n := (e : ℤ) * n
  map_zero' := by simp
  map_add' _ _ := by ring

private lemma stretchHom_injective (e : ℕ) [NeZero e] : Function.Injective (stretchHom e) := by
  intro a b h
  change (e : ℤ) * a = (e : ℤ) * b at h
  exact mul_left_cancel₀ (by exact_mod_cast NeZero.ne e) h

private lemma stretchHom_le_iff (e : ℕ) [NeZero e] (a b : ℤ) :
    stretchHom e a ≤ stretchHom e b ↔ a ≤ b := by
  change (e : ℤ) * a ≤ (e : ℤ) * b ↔ a ≤ b
  apply Int.mul_le_mul_left
  exact_mod_cast NeZero.pos e

private noncomputable def stretch {R : Type*} [CommRing R] (e : ℕ) [NeZero e] :
    LaurentSeries R →+* LaurentSeries R :=
  HahnSeries.embDomainRingHom (stretchHom e) (stretchHom_injective e)
    (stretchHom_le_iff e)

@[simp] private lemma stretch_coeff (e : ℕ) [NeZero e] {R : Type*} [CommRing R]
    (H : LaurentSeries R) (n : ℤ) :
    (stretch e H).coeff ((e : ℤ) * n) = H.coeff n := by
  exact HahnSeries.embDomain_coeff

private lemma stretch_notin_range (e : ℕ) [NeZero e] {R : Type*} [CommRing R]
    (H : LaurentSeries R) (n : ℤ) (hn : ∀ m : ℤ, (e : ℤ) * m ≠ n) :
    (stretch e H).coeff n = 0 := by
  apply HahnSeries.embDomain_notin_range
  rintro ⟨m, hm⟩
  exact hn m hm

private lemma stretch_powerSeries (e : ℕ) [NeZero e] {R : Type*} [CommRing R]
    (p : PowerSeries R) :
    stretch e (p : LaurentSeries R) =
      ((PowerSeries.subst (PowerSeries.X ^ e) p : PowerSeries R) : LaurentSeries R) := by
  ext n
  by_cases hn : ∃ m : ℤ, (e : ℤ) * m = n
  · obtain ⟨m, rfl⟩ := hn
    by_cases hm : 0 ≤ m
    · obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hm
      rw [stretch_coeff]
      have hcast : (e : ℤ) * (d : ℤ) = ((e * d : ℕ) : ℤ) := by push_cast; ring
      rw [hcast]
      simp only [HahnSeries.ofPowerSeries_apply_coeff]
      rw [PowerSeries.coeff_subst_X_pow (NeZero.ne e), if_pos]
      · rw [Nat.mul_div_cancel_left d (NeZero.pos e), Algebra.algebraMap_self_apply]
      · exact dvd_mul_right e d
    · have hem : (e : ℤ) * m < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast NeZero.pos e)
          (lt_of_not_ge hm)
      rw [stretch_coeff]
      have hzero :
          ((PowerSeries.subst (PowerSeries.X ^ e) p : PowerSeries R) :
            LaurentSeries R).coeff ((e : ℤ) * m) = 0 := by
        rw [HahnSeries.ofPowerSeries_apply]
        apply HahnSeries.embDomain_notin_range
        rintro ⟨d, hd⟩
        change (d : ℤ) = (e : ℤ) * m at hd
        omega
      have hleft : ((p : PowerSeries R) : LaurentSeries R).coeff m = 0 := by
        rw [HahnSeries.ofPowerSeries_apply]
        apply HahnSeries.embDomain_notin_range
        rintro ⟨d, hd⟩
        change (d : ℤ) = m at hd
        omega
      rw [hleft, hzero]
  · rw [stretch_notin_range e _ n (fun m hm ↦ hn ⟨m, hm⟩)]
    by_cases hnneg : n < 0
    · rw [HahnSeries.ofPowerSeries_apply]
      rw [HahnSeries.embDomain_notin_range]
      rintro ⟨d, hd⟩
      change (d : ℤ) = n at hd
      omega
    · obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hnneg)
      simp only [HahnSeries.ofPowerSeries_apply_coeff]
      rw [PowerSeries.coeff_subst_X_pow (NeZero.ne e), if_neg]
      intro hed
      obtain ⟨q, hq⟩ := hed
      apply hn ⟨q, by exact_mod_cast hq.symm⟩

end Test

namespace LanglandsSecondMainLemma.Residues

open FreeBasis

private theorem one_constantCoeff_isUnit {R : Type*} [CommRing R] :
    IsUnit (PowerSeries.constantCoeff (1 : PowerSeries R)) := by simp

private lemma pure_algebraMap_eq_stretch {R : Type*} [CommRing R]
    (e : ℕ) [NeZero e]
    (H : LaurentScalars R e (1 : PowerSeries R) one_constantCoeff_isUnit) :
    algebraMap (LaurentScalars R e (1 : PowerSeries R) one_constantCoeff_isUnit)
        (LaurentSeries R) H =
      Test.stretch e
        (laurentScalarsEquiv e (1 : PowerSeries R) one_constantCoeff_isUnit H) := by
  let j : LaurentScalars R e (1 : PowerSeries R) one_constantCoeff_isUnit →+*
      LaurentSeries R :=
    algebraMap _ _
  let k : LaurentScalars R e (1 : PowerSeries R) one_constantCoeff_isUnit →+*
      LaurentSeries R :=
    (Test.stretch e).comp
      (laurentScalarsEquiv e (1 : PowerSeries R) one_constantCoeff_isUnit).toRingHom
  have hjk : j = k := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers (scalarX e (1 : PowerSeries R)))
    apply RingHom.ext
    intro p
    simp only [j, k, RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply
      (PowerScalars R e (1 : PowerSeries R))
      (LaurentScalars R e (1 : PowerSeries R) one_constantCoeff_isUnit)
      (LaurentSeries R)]
    change powerToTargetLaurent e (1 : PowerSeries R) p =
      Test.stretch e
        (algebraMap (PowerSeries R) (LaurentSeries R)
          ((powerScalarsEquiv e (1 : PowerSeries R)) p))
    rw [powerToTargetLaurent, RingHom.comp_apply]
    rw [powerSubstitution, RingHom.comp_apply]
    change algebraMap (PowerSeries R) (LaurentSeries R)
        ((PowerSeries.substAlgHom (parameter_hasSubst e (1 : PowerSeries R)))
          ((powerScalarsEquiv e (1 : PowerSeries R)) p)) = _
    rw [PowerSeries.coe_substAlgHom]
    rw [parameter, mul_one]
    change ((PowerSeries.subst (PowerSeries.X ^ e)
        ((powerScalarsEquiv e (1 : PowerSeries R)) p) : PowerSeries R) :
          LaurentSeries R) =
      Test.stretch e
        (((powerScalarsEquiv e (1 : PowerSeries R)) p : PowerSeries R) :
          LaurentSeries R)
    exact (Test.stretch_powerSeries e _).symm
  exact DFunLike.congr_fun hjk H

private lemma pure_basis_term_coeff {R : Type*} [CommRing R]
    (e : ℕ) [NeZero e]
    (a : LaurentScalars R e (1 : PowerSeries R) one_constantCoeff_isUnit)
    (i j : Fin e) :
    (algebraMap (LaurentScalars R e (1 : PowerSeries R) one_constantCoeff_isUnit)
        (LaurentSeries R) a *
      laurentSeriesBasis e (1 : PowerSeries R) one_constantCoeff_isUnit j).coeff
        ((i : ℤ) - (e : ℤ)) =
      if j = i then
        (laurentScalarsEquiv e (1 : PowerSeries R) one_constantCoeff_isUnit a).coeff (-1)
      else 0 := by
  rw [laurentSeriesBasis_apply, pure_algebraMap_eq_stretch,
    HahnSeries.algebraMap_apply', Algebra.algebraMap_self_apply,
    HahnSeries.ofPowerSeries_X_pow, HahnSeries.coeff_mul_single]
  simp only [mul_one]
  split_ifs with hji
  · subst j
    convert Test.stretch_coeff e
        (laurentScalarsEquiv e (1 : PowerSeries R) one_constantCoeff_isUnit a) (-1) using 2
    all_goals simp
  · apply Test.stretch_notin_range
    intro m hm
    have hi : (i : ℕ) < e := i.isLt
    have hj : (j : ℕ) < e := j.isLt
    have hcasti : ((i : ℕ) : ℤ) = (i : ℤ) := rfl
    have hcastj : ((j : ℕ) : ℤ) = (j : ℤ) := rfl
    apply hji
    apply Fin.ext
    have hepos : (0 : ℤ) < (e : ℤ) := by exact_mod_cast NeZero.pos e
    have hmul : (e : ℤ) * (m + 1) = (i : ℤ) - (j : ℤ) := by
      calc
        (e : ℤ) * (m + 1) = (e : ℤ) * m + (e : ℤ) := by ring
        _ = (i : ℤ) - (j : ℤ) := by omega
    have hiZ : (i : ℤ) < (e : ℤ) := by exact_mod_cast hi
    have hjZ : (j : ℤ) < (e : ℤ) := by exact_mod_cast hj
    have hlower : -(e : ℤ) < (i : ℤ) - (j : ℤ) := by
      omega
    have hupper : (i : ℤ) - (j : ℤ) < (e : ℤ) := by
      omega
    have hmzero : m + 1 = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · have hle : (e : ℤ) * (m + 1) ≤ (e : ℤ) * (-1) :=
          (Int.mul_le_mul_left hepos).2 (by omega)
        omega
      · have hle : (e : ℤ) * 1 ≤ (e : ℤ) * (m + 1) :=
          (Int.mul_le_mul_left hepos).2 (by omega)
        omega
    have hijZ : (i : ℤ) = (j : ℤ) := by
      rw [hmzero, mul_zero] at hmul
      omega
    exact_mod_cast hijZ.symm

private lemma pure_diagonal_residue {R : Type*} [CommRing R]
    (e : ℕ) [NeZero e] (h : LaurentSeries R) (i : Fin e) :
    (laurentScalarsEquiv e (1 : PowerSeries R) one_constantCoeff_isUnit
      ((laurentSeriesBasis e (1 : PowerSeries R) one_constantCoeff_isUnit).repr
        (h * laurentSeriesBasis e (1 : PowerSeries R) one_constantCoeff_isUnit i) i)).coeff (-1) =
      h.coeff (-(e : ℤ)) := by
  let b := laurentSeriesBasis e (1 : PowerSeries R) one_constantCoeff_isUnit
  have hsum := b.sum_repr (h * b i)
  have hc := congrArg (fun x : LaurentSeries R ↦ x.coeff ((i : ℤ) - (e : ℤ))) hsum
  rw [HahnSeries.coeff_sum] at hc
  simp only [Algebra.smul_def] at hc
  dsimp only [b] at hc
  rw [Finset.sum_eq_single i] at hc
  · rw [pure_basis_term_coeff, if_pos rfl] at hc
    rw [laurentSeriesBasis_apply, HahnSeries.algebraMap_apply',
      Algebra.algebraMap_self_apply, HahnSeries.ofPowerSeries_X_pow,
      HahnSeries.coeff_mul_single] at hc
    simpa using hc
  · intro j _ hji
    rw [pure_basis_term_coeff, if_neg hji]
  · simp

private theorem pure_traceSubstitution {k : Type*} [Field k]
    (e : ℕ) [NeZero e] (h : LaurentSeries k) :
    residue
        (laurentScalarsEquiv e (1 : PowerSeries k) one_constantCoeff_isUnit
          (Algebra.trace
            (LaurentScalars k e (1 : PowerSeries k) one_constantCoeff_isUnit)
            (LaurentSeries k) h)) =
      residue
        (h * (PowerSeries.derivative k (parameter e (1 : PowerSeries k)) :
          LaurentSeries k)) := by
  classical
  rw [Algebra.trace_eq_matrix_trace
    (laurentSeriesBasis e (1 : PowerSeries k) one_constantCoeff_isUnit)]
  rw [Matrix.trace]
  change (
    laurentScalarsEquiv e (1 : PowerSeries k) one_constantCoeff_isUnit
      (∑ i, (laurentMultiplicationMatrix e (1 : PowerSeries k)
        one_constantCoeff_isUnit h) i i)).coeff
        (-1) = _
  rw [map_sum, HahnSeries.coeff_sum]
  simp only [laurentMultiplicationMatrix, Algebra.leftMulMatrix_eq_repr_mul,
    pure_diagonal_residue]
  rw [parameter, mul_one, PowerSeries.derivative_pow]
  simp only [PowerSeries.derivative_X, mul_one]
  unfold residue
  rw [map_mul, map_natCast, HahnSeries.ofPowerSeries_X_pow,
    show (e : LaurentSeries k) = HahnSeries.C (e : k) by rfl,
    HahnSeries.C_apply, HahnSeries.single_mul_single,
    HahnSeries.coeff_mul_single]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ, Fintype.card_fin]
  have hepos : 0 < e := NeZero.pos e
  have hecast : ((e - 1 : ℕ) : ℤ) = (e : ℤ) - 1 := by omega
  rw [hecast]
  ring_nf

private lemma binomialSeries_pow {K : Type*} [Field K] [CharZero K]
    (r : K) (n : ℕ) :
    (PowerSeries.binomialSeries K r) ^ n =
      PowerSeries.binomialSeries K ((n : K) * r) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, ← PowerSeries.binomialSeries_add]
      congr 2
      push_cast
      ring_nf

private lemma exists_powerSeries_root {K : Type*} [Field K] [CharZero K]
    [IsAlgClosed K] (e : ℕ) [NeZero e] (v : PowerSeries K)
    (hv : IsUnit (PowerSeries.constantCoeff v)) :
    ∃ w : PowerSeries K, IsUnit (PowerSeries.constantCoeff w) ∧ w ^ e = v := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (PowerSeries.constantCoeff v)
    (NeZero.pos e)
  have hv0 : PowerSeries.constantCoeff v ≠ 0 := by
    simpa only [isUnit_iff_ne_zero] using hv
  have ha0 : a ≠ 0 := by
    intro haz
    rw [haz, zero_pow (NeZero.ne e)] at ha
    exact hv0 ha.symm
  let normalized : PowerSeries K :=
    PowerSeries.C ((PowerSeries.constantCoeff v)⁻¹) * v
  have hnormalized : PowerSeries.constantCoeff normalized = 1 := by
    simp [normalized, hv0]
  let p : PowerSeries K := normalized - 1
  have hp0 : PowerSeries.constantCoeff p = 0 := by
    simp [p, hnormalized]
  let rootNormalized : PowerSeries K :=
    PowerSeries.subst p
      (PowerSeries.binomialSeries K ((e : K)⁻¹))
  have heroot : (e : K) ≠ 0 := by exact_mod_cast NeZero.ne e
  have hrootNormalized : rootNormalized ^ e = normalized := by
    dsimp only [rootNormalized]
    rw [← PowerSeries.subst_pow (PowerSeries.HasSubst.of_constantCoeff_zero' hp0)]
    rw [binomialSeries_pow]
    rw [mul_inv_cancel₀ heroot]
    rw [show (1 : K) = (1 : ℕ) by norm_num, PowerSeries.binomialSeries_nat]
    simp only [pow_one]
    rw [PowerSeries.subst_add (PowerSeries.HasSubst.of_constantCoeff_zero' hp0),
      PowerSeries.subst_X]
    · rw [← PowerSeries.coe_substAlgHom
        (PowerSeries.HasSubst.of_constantCoeff_zero' hp0)]
      simp [p]
    · exact PowerSeries.HasSubst.of_constantCoeff_zero' hp0
  let w := PowerSeries.C a * rootNormalized
  refine ⟨w, ?_, ?_⟩
  · dsimp only [w]
    have hconstRoot : PowerSeries.constantCoeff rootNormalized = 1 := by
      dsimp only [rootNormalized]
      rw [show PowerSeries.binomialSeries K ((e : K) ⁻¹) =
          1 + (PowerSeries.binomialSeries K ((e : K) ⁻¹) - 1) by ring]
      rw [PowerSeries.subst_add (PowerSeries.HasSubst.of_constantCoeff_zero' hp0)]
      have hz := PowerSeries.constantCoeff_subst_eq_zero hp0
        (PowerSeries.binomialSeries K ((e : K) ⁻¹) - 1) (by simp)
      rw [map_add]
      change PowerSeries.constantCoeff (PowerSeries.subst p 1) +
        MvPowerSeries.constantCoeff
          (PowerSeries.subst p (PowerSeries.binomialSeries K ((e : K) ⁻¹) - 1)) = 1
      rw [hz]
      rw [← PowerSeries.coe_substAlgHom
        (PowerSeries.HasSubst.of_constantCoeff_zero' hp0)]
      simp
    simp [hconstRoot, ha0]
  · dsimp only [w]
    rw [mul_pow, hrootNormalized, ← map_pow (PowerSeries.C : K →+* PowerSeries K), ha]
    dsimp only [normalized]
    rw [← mul_assoc, ← map_mul]
    simp [hv0]

private structure PureLaurent (K : Type*) [Zero K] (e : ℕ) where
  down : LaurentSeries K

private def pureLaurentEquiv {K : Type*} [Zero K] (e : ℕ) :
    PureLaurent K e ≃ LaurentSeries K where
  toFun := PureLaurent.down
  invFun := PureLaurent.mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl

noncomputable instance {K : Type*} [CommRing K] (e : ℕ) :
    CommRing (PureLaurent K e) := (pureLaurentEquiv e).commRing

private noncomputable def pureLaurentRingEquiv {K : Type*} [CommRing K] (e : ℕ) :
    PureLaurent K e ≃+* LaurentSeries K := (pureLaurentEquiv e).ringEquiv

private noncomputable def pureReparamMap {K : Type*} [CommRing K] (e : ℕ) [NeZero e]
    (v : PowerSeries K) (hv : IsUnit (PowerSeries.constantCoeff v)) :
    LaurentScalars K e v hv →+* PureLaurent K e :=
  (pureLaurentRingEquiv e).symm.toRingHom.comp
    ((Test.stretch e).comp
      (laurentScalarsEquiv e v hv).toRingHom)

noncomputable instance {K : Type*} [CommRing K] (e : ℕ) [NeZero e]
    (v : PowerSeries K) (hv : IsUnit (PowerSeries.constantCoeff v)) :
    Algebra (LaurentScalars K e v hv) (PureLaurent K e) :=
  (pureReparamMap e v hv).toAlgebra

private noncomputable def pureLaurentAlgEquiv {K : Type*} [CommRing K] (e : ℕ) [NeZero e] :
    PureLaurent K e ≃ₐ[
      LaurentScalars K e (1 : PowerSeries K) one_constantCoeff_isUnit]
      LaurentSeries K :=
  { toRingEquiv := pureLaurentRingEquiv e
    commutes' := fun a ↦ by
      rw [show algebraMap
        (LaurentScalars K e (1 : PowerSeries K) one_constantCoeff_isUnit)
          (PureLaurent K e) =
        pureReparamMap e (1 : PowerSeries K) one_constantCoeff_isUnit from rfl]
      change Test.stretch e
          (laurentScalarsEquiv e (1 : PowerSeries K)
            one_constantCoeff_isUnit a) = _
      exact (pure_algebraMap_eq_stretch e a).symm }

private lemma orderOne_algebraMap_bijective {K : Type*} [Field K]
    (w : PowerSeries K) (hw : IsUnit (PowerSeries.constantCoeff w)) :
    Function.Bijective
      (algebraMap (LaurentScalars K 1 w hw) (LaurentSeries K)) := by
  let b := laurentSeriesBasis 1 w hw
  letI : Nontrivial (LaurentScalars K 1 w hw) :=
    (laurentScalarsEquiv 1 w hw).toEquiv.nontrivial
  letI : Module.Free (LaurentScalars K 1 w hw) (LaurentSeries K) :=
    Module.Free.of_basis b
  apply Module.Free.bijective_algebraMap_of_finrank_eq_one
  rw [Module.finrank_eq_card_basis b]
  simp

private noncomputable def orderOneRingHom {K : Type*} [Field K] (e : ℕ)
    (w : PowerSeries K) (hw : IsUnit (PowerSeries.constantCoeff w)) :
    PureLaurent K e →+* LaurentSeries K :=
  (algebraMap (LaurentScalars K 1 w hw) (LaurentSeries K)).comp
    ((laurentScalarsEquiv 1 w hw).symm.toRingHom.comp
      (pureLaurentRingEquiv e).toRingHom)

private noncomputable def orderOneRingEquiv {K : Type*} [Field K] (e : ℕ)
    (w : PowerSeries K) (hw : IsUnit (PowerSeries.constantCoeff w)) :
    PureLaurent K e ≃+* LaurentSeries K :=
  RingEquiv.ofBijective (orderOneRingHom e w hw) <| by
    exact (orderOne_algebraMap_bijective w hw).comp
      ((laurentScalarsEquiv 1 w hw).symm.toEquiv.bijective.comp
        (pureLaurentRingEquiv e).toEquiv.bijective)

private lemma parameter_order {K : Type*} [Field K] (e : ℕ) [NeZero e]
    (v : PowerSeries K) (hv : IsUnit (PowerSeries.constantCoeff v)) :
    (parameter e v).order = e := by
  rw [parameter, PowerSeries.order_mul, PowerSeries.order_X_pow]
  rw [PowerSeries.order_zero_of_unit
    (PowerSeries.isUnit_iff_constantCoeff.mpr hv)]
  simp

private lemma orderOneRingHom_apply {K : Type*} [Field K] (e : ℕ)
    (w : PowerSeries K) (hw : IsUnit (PowerSeries.constantCoeff w))
    (g : LaurentSeries K) :
    orderOneRingHom e w hw ((pureLaurentRingEquiv e).symm g) =
      formalSubstitution (parameter 1 w) 1 (by omega)
        (parameter_order 1 w hw) g := by
  let left : LaurentSeries K →+* LaurentSeries K :=
    (orderOneRingHom e w hw).comp
      (pureLaurentRingEquiv e).symm.toRingHom
  let right : LaurentSeries K →+* LaurentSeries K :=
    formalSubstitution (parameter 1 w) 1 (by omega)
      (parameter_order 1 w hw)
  have hlr : left = right := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers (PowerSeries.X : PowerSeries K))
    apply RingHom.ext
    intro p
    simp only [left, right, RingHom.comp_apply]
    change algebraMap (LaurentScalars K 1 w hw) (LaurentSeries K)
        ((laurentScalarsEquiv 1 w hw).symm
          (algebraMap (PowerSeries K) (LaurentSeries K) p)) = _
    have hp : (laurentScalarsEquiv 1 w hw).symm
          (algebraMap (PowerSeries K) (LaurentSeries K) p) =
        algebraMap (PowerScalars K 1 w) (LaurentScalars K 1 w hw)
          ((powerScalarsEquiv 1 w).symm p) := by
      apply (laurentScalarsEquiv 1 w hw).injective
      rfl
    rw [hp]
    rw [← IsScalarTower.algebraMap_apply
      (PowerScalars K 1 w) (LaurentScalars K 1 w hw) (LaurentSeries K)]
    change algebraMap (PowerScalars K 1 w) (LaurentSeries K)
        ((powerScalarsEquiv 1 w).symm p) = _
    change algebraMap (PowerSeries K) (LaurentSeries K)
        (algebraMap (PowerScalars K 1 w) (PowerSeries K)
          ((powerScalarsEquiv 1 w).symm p)) = _
    rw [algebraMap_powerScalars_apply, RingEquiv.apply_symm_apply]
    change (PowerSeries.subst (parameter 1 w) p : LaurentSeries K) =
      formalSubstitution (parameter 1 w) 1 (by omega)
        (parameter_order 1 w hw) (p : LaurentSeries K)
    rw [formalSubstitution_coe]
  exact DFunLike.congr_fun hlr g

private lemma formalSubstitution_stretch {K : Type*} [Field K]
    (e : ℕ) [NeZero e] (w v : PowerSeries K)
    (hw : IsUnit (PowerSeries.constantCoeff w))
    (hv : IsUnit (PowerSeries.constantCoeff v)) (hpow : w ^ e = v)
    (g : LaurentSeries K) :
    formalSubstitution (parameter 1 w) 1 (by omega) (parameter_order 1 w hw)
        (Test.stretch e g) =
      formalSubstitution (parameter e v) e (NeZero.pos e)
        (parameter_order e v hv) g := by
  let left : LaurentSeries K →+* LaurentSeries K :=
    (formalSubstitution (parameter 1 w) 1 (by omega)
      (parameter_order 1 w hw)).comp (Test.stretch e)
  let right : LaurentSeries K →+* LaurentSeries K :=
    formalSubstitution (parameter e v) e (NeZero.pos e)
      (parameter_order e v hv)
  have hlr : left = right := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers (PowerSeries.X : PowerSeries K))
    apply RingHom.ext
    intro p
    simp only [left, right, RingHom.comp_apply]
    change formalSubstitution (parameter 1 w) 1 (by omega)
        (parameter_order 1 w hw) (Test.stretch e (p : LaurentSeries K)) =
      formalSubstitution (parameter e v) e (NeZero.pos e)
        (parameter_order e v hv) (p : LaurentSeries K)
    rw [Test.stretch_powerSeries, formalSubstitution_coe,
      formalSubstitution_coe]
    rw [PowerSeries.subst_comp_subst_apply
      (PowerSeries.HasSubst.X_pow (NeZero.ne e))
      (parameter_hasSubst 1 w)]
    congr 2
    rw [PowerSeries.subst_pow (parameter_hasSubst 1 w),
      PowerSeries.subst_X (parameter_hasSubst 1 w)]
    simp only [parameter, pow_one]
    rw [mul_pow, hpow]
  exact DFunLike.congr_fun hlr g

private lemma algebraMap_eq_formalSubstitution {K : Type*} [Field K]
    (e : ℕ) [NeZero e] (v : PowerSeries K)
    (hv : IsUnit (PowerSeries.constantCoeff v))
    (a : LaurentScalars K e v hv) :
    algebraMap (LaurentScalars K e v hv) (LaurentSeries K) a =
      formalSubstitution (parameter e v) e (NeZero.pos e)
        (parameter_order e v hv) (laurentScalarsEquiv e v hv a) := by
  let left : LaurentScalars K e v hv →+* LaurentSeries K := algebraMap _ _
  let right : LaurentScalars K e v hv →+* LaurentSeries K :=
    (formalSubstitution (parameter e v) e (NeZero.pos e)
      (parameter_order e v hv)).comp (laurentScalarsEquiv e v hv).toRingHom
  have hlr : left = right := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers (scalarX e v))
    apply RingHom.ext
    intro p
    simp only [left, right, RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply
      (PowerScalars K e v) (LaurentScalars K e v hv) (LaurentSeries K)]
    change algebraMap (PowerScalars K e v) (LaurentSeries K) p = _
    change algebraMap (PowerSeries K) (LaurentSeries K)
        (algebraMap (PowerScalars K e v) (PowerSeries K) p) = _
    rw [algebraMap_powerScalars_apply]
    change (PowerSeries.subst (parameter e v) ((powerScalarsEquiv e v) p) :
        LaurentSeries K) = formalSubstitution (parameter e v) e (NeZero.pos e)
          (parameter_order e v hv)
          (((powerScalarsEquiv e v) p : PowerSeries K) : LaurentSeries K)
    rw [formalSubstitution_coe]
  exact DFunLike.congr_fun hlr a

private noncomputable def reparamAlgEquiv {K : Type*} [Field K]
    (e : ℕ) [NeZero e] (v w : PowerSeries K)
    (hv : IsUnit (PowerSeries.constantCoeff v))
    (hw : IsUnit (PowerSeries.constantCoeff w)) (hpow : w ^ e = v) :
    PureLaurent K e ≃ₐ[LaurentScalars K e v hv] LaurentSeries K :=
  AlgEquiv.ofRingEquiv (f := orderOneRingEquiv e w hw) (fun a ↦ by
    rw [show algebraMap (LaurentScalars K e v hv) (PureLaurent K e) =
      pureReparamMap e v hv from rfl]
    change orderOneRingHom e w hw
        ((pureLaurentRingEquiv e).symm
          (Test.stretch e (laurentScalarsEquiv e v hv a))) = _
    rw [orderOneRingHom_apply, formalSubstitution_stretch e w v hw hv hpow]
    exact (algebraMap_eq_formalSubstitution e v hv a).symm)

private noncomputable def sourceToPureEquiv {K : Type*} [CommRing K] (e : ℕ)
    (v : PowerSeries K) (hv : IsUnit (PowerSeries.constantCoeff v)) :
    LaurentScalars K e v hv ≃+*
      LaurentScalars K e (1 : PowerSeries K) one_constantCoeff_isUnit :=
  (laurentScalarsEquiv e v hv).trans
    (laurentScalarsEquiv e (1 : PowerSeries K)
      one_constantCoeff_isUnit).symm

private theorem pureTraceOnReparam {K : Type*} [Field K]
    (e : ℕ) [NeZero e] (v : PowerSeries K)
    (hv : IsUnit (PowerSeries.constantCoeff v)) (x : PureLaurent K e) :
    residue (laurentScalarsEquiv e v hv
      (Algebra.trace (LaurentScalars K e v hv) (PureLaurent K e) x)) =
      residue (pureLaurentRingEquiv e x *
        (PowerSeries.derivative K (parameter e (1 : PowerSeries K)) :
          LaurentSeries K)) := by
  let e₁ := sourceToPureEquiv e v hv
  let e₂ : PureLaurent K e ≃+* LaurentSeries K := pureLaurentRingEquiv e
  have hsquare :
      (algebraMap
          (LaurentScalars K e (1 : PowerSeries K) one_constantCoeff_isUnit)
          (LaurentSeries K)).comp e₁.toRingHom =
        e₂.toRingHom.comp
          (algebraMap (LaurentScalars K e v hv) (PureLaurent K e)) := by
    apply RingHom.ext
    intro a
    change algebraMap
        (LaurentScalars K e (1 : PowerSeries K) one_constantCoeff_isUnit)
          (LaurentSeries K) (e₁ a) =
      Test.stretch e (laurentScalarsEquiv e v hv a)
    rw [pure_algebraMap_eq_stretch]
    rfl
  have htrace := Algebra.trace_eq_of_equiv_equiv e₁ e₂ hsquare x
  have hres : residue (laurentScalarsEquiv e v hv
        (Algebra.trace (LaurentScalars K e v hv) (PureLaurent K e) x)) =
      residue (laurentScalarsEquiv e (1 : PowerSeries K)
        one_constantCoeff_isUnit
          (Algebra.trace
            (LaurentScalars K e (1 : PowerSeries K) one_constantCoeff_isUnit)
            (LaurentSeries K) (pureLaurentRingEquiv e x))) := by
    rw [htrace]
    rfl
  rw [hres]
  exact pure_traceSubstitution e (pureLaurentRingEquiv e x)

private theorem traceSubstitution_algClosed_charZero {K : Type*} [Field K]
    [CharZero K] [IsAlgClosed K] (e : ℕ) [NeZero e]
    (v : PowerSeries K) (hv : IsUnit (PowerSeries.constantCoeff v))
    (h : LaurentSeries K) :
    residue (laurentScalarsEquiv e v hv
      (Algebra.trace (LaurentScalars K e v hv) (LaurentSeries K) h)) =
      residue (h *
        (PowerSeries.derivative K (parameter e v) : LaurentSeries K)) := by
  obtain ⟨w, hw, hpow⟩ := exists_powerSeries_root e v hv
  let E := reparamAlgEquiv e v w hv hw hpow
  let x : PureLaurent K e := E.symm h
  let g : LaurentSeries K := pureLaurentRingEquiv e x
  have hEx : E x = h := E.apply_symm_apply h
  have htrace :
      Algebra.trace (LaurentScalars K e v hv) (LaurentSeries K) h =
        Algebra.trace (LaurentScalars K e v hv) (PureLaurent K e) x := by
    rw [← hEx]
    exact Algebra.trace_eq_of_algEquiv E x
  rw [htrace]
  rw [pureTraceOnReparam e v hv x]
  have hzOrder := parameter_order 1 w hw
  have hchange := change_uniformizer (parameter 1 w) hzOrder
    (g * (PowerSeries.derivative K
      (parameter e (1 : PowerSeries K)) : LaurentSeries K))
  rw [← hchange]
  congr 1
  have hh : h = formalSubstitution (parameter 1 w) 1 (by omega) hzOrder g := by
    rw [← hEx]
    exact orderOneRingHom_apply e w hw g
  have hderiv :
      formalSubstitution (parameter 1 w) 1 (by omega) hzOrder
          ((PowerSeries.derivative K
            (parameter e (1 : PowerSeries K)) : PowerSeries K) : LaurentSeries K) *
        (PowerSeries.derivative K (parameter 1 w) : LaurentSeries K) =
      (PowerSeries.derivative K (parameter e v) : LaurentSeries K) := by
    rw [formalSubstitution_coe, ← PowerSeries.coe_mul]
    congr 1
    rw [← PowerSeries.derivative_subst]
    · congr 1
      rw [show parameter e (1 : PowerSeries K) =
        (PowerSeries.X : PowerSeries K) ^ e by simp [parameter]]
      rw [show parameter e v = (PowerSeries.X : PowerSeries K) ^ e * v by rfl]
      rw [PowerSeries.subst_pow (parameter_hasSubst 1 w),
        PowerSeries.subst_X (parameter_hasSubst 1 w)]
      simp only [parameter, pow_one]
      rw [mul_pow, hpow]
    · exact parameter_hasSubst 1 w
  rw [map_mul, hh, mul_assoc, hderiv]

private lemma map_derivative {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PowerSeries R) :
    PowerSeries.map f (PowerSeries.derivative R p) =
      PowerSeries.derivative S (PowerSeries.map f p) := by
  ext n
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_derivative, map_mul,
    map_add, map_natCast, map_one]

private lemma map_trace {R S : Type*} [CommRing R] [CommRing S]
    (e : ℕ) [NeZero e] (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) (f : R →+* S)
    (h : LaurentSeries R) :
    mapLaurentScalars e v hv f
        (Algebra.trace (LaurentScalars R e v hv) (LaurentSeries R) h) =
      Algebra.trace
        (LaurentScalars S e (PowerSeries.map f v) (hv.map f))
        (LaurentSeries S) (mapLaurentSeries f h) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (laurentSeriesBasis e v hv),
    Algebra.trace_eq_matrix_trace
      (laurentSeriesBasis e (PowerSeries.map f v) (hv.map f))]
  change mapLaurentScalars e v hv f
      (Matrix.trace (laurentMultiplicationMatrix e v hv h)) =
    Matrix.trace (laurentMultiplicationMatrix e (PowerSeries.map f v)
      (hv.map f) (mapLaurentSeries f h))
  rw [← map_laurentMultiplicationMatrix e v hv f h]
  simp [Matrix.trace]

private lemma map_traceCoefficient {R S : Type*} [CommRing R] [CommRing S]
    (e : ℕ) [NeZero e] (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) (f : R →+* S)
    (h : LaurentSeries R) :
    f ((laurentScalarsEquiv e v hv
      (Algebra.trace (LaurentScalars R e v hv) (LaurentSeries R) h)).coeff (-1)) =
      (laurentScalarsEquiv e (PowerSeries.map f v) (hv.map f)
        (Algebra.trace
          (LaurentScalars S e (PowerSeries.map f v) (hv.map f))
          (LaurentSeries S) (mapLaurentSeries f h))).coeff (-1) := by
  have ht := congrArg (fun q ↦
      (laurentScalarsEquiv e (PowerSeries.map f v) (hv.map f) q).coeff (-1))
    (map_trace e v hv f h)
  exact ht

private lemma map_differentialCoefficient {R S : Type*} [CommRing R] [CommRing S]
    (e : ℕ) (v : PowerSeries R) (f : R →+* S) (h : LaurentSeries R) :
    f ((h *
      (PowerSeries.derivative R (parameter e v) : LaurentSeries R)).coeff (-1)) =
      (mapLaurentSeries f h *
        (PowerSeries.derivative S (parameter e (PowerSeries.map f v)) :
          LaurentSeries S)).coeff (-1) := by
  change (mapLaurentSeries f (h *
      (PowerSeries.derivative R (parameter e v) : LaurentSeries R))).coeff (-1) = _
  rw [map_mul]
  rw [show mapLaurentSeries f
      ((PowerSeries.derivative R (parameter e v) : PowerSeries R) : LaurentSeries R) =
        ((PowerSeries.map f (PowerSeries.derivative R (parameter e v)) : PowerSeries S) :
          LaurentSeries S) by
    exact mapLaurentSeries_algebraMap f _]
  rw [map_derivative, map_parameter]

private lemma map_traceCoefficient_of_eq {R S : Type*}
    [CommRing R] [CommRing S] (e : ℕ) [NeZero e]
    (vR : PowerSeries R) (hvR : IsUnit (PowerSeries.constantCoeff vR))
    (f : R →+* S) (hR : LaurentSeries R) (vS : PowerSeries S)
    (hvS : IsUnit (PowerSeries.constantCoeff vS)) (hS : LaurentSeries S)
    (hvmap : PowerSeries.map f vR = vS)
    (hhmap : mapLaurentSeries f hR = hS) :
    f ((laurentScalarsEquiv e vR hvR
      (Algebra.trace (LaurentScalars R e vR hvR) (LaurentSeries R) hR)).coeff (-1)) =
      (laurentScalarsEquiv e vS hvS
        (Algebra.trace (LaurentScalars S e vS hvS) (LaurentSeries S) hS)).coeff
          (-1) := by
  subst vS
  subst hS
  exact map_traceCoefficient e vR hvR f hR

private lemma map_differentialCoefficient_of_eq {R S : Type*}
    [CommRing R] [CommRing S] (e : ℕ) (vR : PowerSeries R)
    (f : R →+* S) (hR : LaurentSeries R) (vS : PowerSeries S)
    (hS : LaurentSeries S) (hvmap : PowerSeries.map f vR = vS)
    (hhmap : mapLaurentSeries f hR = hS) :
    f ((hR * (PowerSeries.derivative R (parameter e vR) : LaurentSeries R)).coeff
          (-1)) =
      (hS * (PowerSeries.derivative S (parameter e vS) : LaurentSeries S)).coeff
        (-1) := by
  subst vS
  subst hS
  exact map_differentialCoefficient e vR f hR

private theorem traceSubstitution_charZero {K : Type*} [Field K] [CharZero K]
    (e : ℕ) [NeZero e] (v : PowerSeries K)
    (hv : IsUnit (PowerSeries.constantCoeff v)) (h : LaurentSeries K) :
    residue (laurentScalarsEquiv e v hv
      (Algebra.trace (LaurentScalars K e v hv) (LaurentSeries K) h)) =
      residue (h *
        (PowerSeries.derivative K (parameter e v) : LaurentSeries K)) := by
  let f : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  apply f.injective
  calc
    f (residue (laurentScalarsEquiv e v hv
        (Algebra.trace (LaurentScalars K e v hv) (LaurentSeries K) h))) =
        residue (laurentScalarsEquiv e (PowerSeries.map f v) (hv.map f)
          (Algebra.trace
            (LaurentScalars (AlgebraicClosure K) e (PowerSeries.map f v) (hv.map f))
            (LaurentSeries (AlgebraicClosure K)) (mapLaurentSeries f h))) :=
      map_traceCoefficient e v hv f h
    _ = residue (mapLaurentSeries f h *
          (PowerSeries.derivative (AlgebraicClosure K)
            (parameter e (PowerSeries.map f v)) : LaurentSeries (AlgebraicClosure K))) :=
      traceSubstitution_algClosed_charZero e (PowerSeries.map f v) (hv.map f)
        (mapLaurentSeries f h)
    _ = f (residue (h *
          (PowerSeries.derivative K (parameter e v) : LaurentSeries K))) :=
      (map_differentialCoefficient e v f h).symm

private abbrev UniversalCoefficients := MvPolynomial (Sum ℕ ℤ) ℤ

private noncomputable def universalEval {k : Type*} [Field k]
    (v : PowerSeries k) (h : LaurentSeries k) : UniversalCoefficients →+* k :=
  MvPolynomial.eval₂Hom (Int.castRingHom k) <| Sum.elim
    (fun n ↦ PowerSeries.coeff n v) (fun z ↦ h.coeff z)

private noncomputable def universalLead : UniversalCoefficients :=
  MvPolynomial.X (Sum.inl 0)

private abbrev LocalizedUniversal : Type :=
  Localization.Away universalLead

private lemma universalLead_ne_zero : universalLead ≠ 0 := by
  simp [universalLead]

noncomputable instance : IsDomain LocalizedUniversal :=
  Localization.Away.isDomain universalLead_ne_zero

noncomputable instance : CharZero LocalizedUniversal :=
  charZero_of_injective_algebraMap
    (IsLocalization.injective LocalizedUniversal
      (powers_le_nonZeroDivisors_of_noZeroDivisors universalLead_ne_zero))

private noncomputable def localizedUniversalUnitSeries :
    PowerSeries LocalizedUniversal :=
  PowerSeries.mk fun n ↦ algebraMap UniversalCoefficients LocalizedUniversal
    (MvPolynomial.X (Sum.inl n))

private lemma localizedUniversalUnitSeries_isUnit :
    IsUnit (PowerSeries.constantCoeff localizedUniversalUnitSeries) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp only [localizedUniversalUnitSeries, PowerSeries.coeff_mk]
  change IsUnit (algebraMap UniversalCoefficients LocalizedUniversal universalLead)
  exact IsLocalization.Away.algebraMap_isUnit universalLead

private noncomputable def localizedUniversalLaurent {k : Type*} [Field k]
    (h : LaurentSeries k) : LaurentSeries LocalizedUniversal := by
  classical
  exact
    { coeff := fun n ↦ if h.coeff n = 0 then 0 else
        algebraMap UniversalCoefficients LocalizedUniversal
          (MvPolynomial.X (Sum.inr n))
      isPWO_support' := h.isPWO_support.mono fun n hn ↦ by
        change h.coeff n ≠ 0
        intro hz
        simp [Function.mem_support, hz] at hn }

private lemma universalEval_lead_isUnit {k : Type*} [Field k]
    (v : PowerSeries k) (h : LaurentSeries k)
    (hv : IsUnit (PowerSeries.constantCoeff v)) :
    IsUnit (universalEval v h universalLead) := by
  simpa [universalEval, universalLead, PowerSeries.coeff_zero_eq_constantCoeff] using hv

private noncomputable def localizedUniversalEval {k : Type*} [Field k]
    (v : PowerSeries k) (h : LaurentSeries k)
    (hv : IsUnit (PowerSeries.constantCoeff v)) : LocalizedUniversal →+* k :=
  IsLocalization.Away.lift (S := LocalizedUniversal) (g := universalEval v h)
    universalLead (universalEval_lead_isUnit v h hv)

private lemma map_localizedUniversalUnitSeries {k : Type*} [Field k]
    (v : PowerSeries k) (h : LaurentSeries k)
    (hv : IsUnit (PowerSeries.constantCoeff v)) :
    PowerSeries.map (localizedUniversalEval v h hv)
      localizedUniversalUnitSeries = v := by
  ext n
  simp [localizedUniversalUnitSeries, localizedUniversalEval, universalEval]

private lemma map_localizedUniversalLaurent {k : Type*} [Field k]
    (v : PowerSeries k) (h : LaurentSeries k)
    (hv : IsUnit (PowerSeries.constantCoeff v)) :
    mapLaurentSeries (localizedUniversalEval v h hv)
      (localizedUniversalLaurent h) = h := by
  classical
  ext n
  change localizedUniversalEval v h hv
      (if h.coeff n = 0 then 0 else
        algebraMap UniversalCoefficients LocalizedUniversal
          (MvPolynomial.X (Sum.inr n))) = h.coeff n
  by_cases hn : h.coeff n = 0
  · simp [hn]
  · simp [hn, localizedUniversalEval, universalEval]

private lemma localized_universal_coefficient_identity (e : ℕ) [NeZero e]
    (h : LaurentSeries LocalizedUniversal) :
    (laurentScalarsEquiv e localizedUniversalUnitSeries
      localizedUniversalUnitSeries_isUnit
      (Algebra.trace
        (LaurentScalars LocalizedUniversal e localizedUniversalUnitSeries
          localizedUniversalUnitSeries_isUnit)
        (LaurentSeries LocalizedUniversal) h)).coeff (-1) =
      (h * (PowerSeries.derivative LocalizedUniversal
        (parameter e localizedUniversalUnitSeries) :
          LaurentSeries LocalizedUniversal)).coeff (-1) := by
  let F := FractionRing LocalizedUniversal
  let q : LocalizedUniversal →+* F := algebraMap _ _
  have hF := traceSubstitution_charZero e
    (PowerSeries.map q localizedUniversalUnitSeries)
    (localizedUniversalUnitSeries_isUnit.map q) (mapLaurentSeries q h)
  change
    (laurentScalarsEquiv e (PowerSeries.map q localizedUniversalUnitSeries)
      (localizedUniversalUnitSeries_isUnit.map q)
      (Algebra.trace
        (LaurentScalars F e (PowerSeries.map q localizedUniversalUnitSeries)
          (localizedUniversalUnitSeries_isUnit.map q))
        (LaurentSeries F) (mapLaurentSeries q h))).coeff (-1) =
      (mapLaurentSeries q h *
        (PowerSeries.derivative F
          (parameter e (PowerSeries.map q localizedUniversalUnitSeries)) :
            LaurentSeries F)).coeff (-1) at hF
  apply IsFractionRing.injective LocalizedUniversal F
  calc
    q ((laurentScalarsEquiv e localizedUniversalUnitSeries
        localizedUniversalUnitSeries_isUnit
        (Algebra.trace
          (LaurentScalars LocalizedUniversal e localizedUniversalUnitSeries
            localizedUniversalUnitSeries_isUnit)
          (LaurentSeries LocalizedUniversal) h)).coeff (-1)) =
        (laurentScalarsEquiv e (PowerSeries.map q localizedUniversalUnitSeries)
          (localizedUniversalUnitSeries_isUnit.map q)
          (Algebra.trace
            (LaurentScalars F e (PowerSeries.map q localizedUniversalUnitSeries)
              (localizedUniversalUnitSeries_isUnit.map q))
            (LaurentSeries F) (mapLaurentSeries q h))).coeff (-1) :=
      map_traceCoefficient e localizedUniversalUnitSeries
        localizedUniversalUnitSeries_isUnit q h
    _ = (mapLaurentSeries q h *
          (PowerSeries.derivative F
            (parameter e (PowerSeries.map q localizedUniversalUnitSeries)) :
              LaurentSeries F)).coeff (-1) := hF
    _ = q ((h * (PowerSeries.derivative LocalizedUniversal
          (parameter e localizedUniversalUnitSeries) :
            LaurentSeries LocalizedUniversal)).coeff (-1)) :=
      (map_differentialCoefficient e localizedUniversalUnitSeries q h).symm

/-- The algebraic trace for `k((t)) / k((X^e v))` is compatible with
formal Laurent residues.  This is Appendix B, Lemma B.3. -/
theorem traceSubstitution {k : Type*} [Field k]
    (e : ℕ) [NeZero e] (v : PowerSeries k)
    (hv : IsUnit (PowerSeries.constantCoeff v)) (h : LaurentSeries k) :
    residue (laurentScalarsEquiv e v hv
      (Algebra.trace (LaurentScalars k e v hv) (LaurentSeries k) h)) =
      residue (h *
        (PowerSeries.derivative k (parameter e v) : LaurentSeries k)) := by
  let f := localizedUniversalEval v h hv
  let H := localizedUniversalLaurent h
  have hvmap : PowerSeries.map f localizedUniversalUnitSeries = v :=
    map_localizedUniversalUnitSeries v h hv
  have hHmap : mapLaurentSeries f H = h :=
    map_localizedUniversalLaurent v h hv
  have htrace := map_traceCoefficient_of_eq e localizedUniversalUnitSeries
    localizedUniversalUnitSeries_isUnit f H v hv h hvmap hHmap
  have hdiff := map_differentialCoefficient_of_eq e localizedUniversalUnitSeries
    f H v h hvmap hHmap
  calc
    residue (laurentScalarsEquiv e v hv
        (Algebra.trace (LaurentScalars k e v hv) (LaurentSeries k) h)) =
        f ((laurentScalarsEquiv e localizedUniversalUnitSeries
          localizedUniversalUnitSeries_isUnit
          (Algebra.trace
            (LaurentScalars LocalizedUniversal e localizedUniversalUnitSeries
              localizedUniversalUnitSeries_isUnit)
            (LaurentSeries LocalizedUniversal) H)).coeff (-1)) := htrace.symm
    _ = f ((H * (PowerSeries.derivative LocalizedUniversal
          (parameter e localizedUniversalUnitSeries) :
            LaurentSeries LocalizedUniversal)).coeff (-1)) :=
      congrArg f (localized_universal_coefficient_identity e H)
    _ = residue (h *
          (PowerSeries.derivative k (parameter e v) : LaurentSeries k)) := hdiff

end LanglandsSecondMainLemma.Residues
