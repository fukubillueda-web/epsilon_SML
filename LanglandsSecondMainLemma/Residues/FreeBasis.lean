import Mathlib

/-!
# A finite free basis for a ramified power-series substitution

This file proves Appendix B, Lemma B.2 (`B:free-basis`) of the controlling
manuscript. If `u = X ^ e * v`, with `e > 0` and `v.constantCoeff` a unit,
then substitution `X ↦ u` makes `R⟦X⟧` finite free over a second copy of
`R⟦X⟧`, with basis `1, X, …, X ^ (e - 1)`. Localizing gives the same
basis for Laurent series. We use `ULift` only to distinguish the source
variable `s` from the target variable `t`; `ULift.ringEquiv` identifies these
scalar rings with the usual power- and Laurent-series rings.

The proof follows the paper's successive-cancellation argument. The quotient
operation removes the first `e` coefficients and divides by the unit `v`.
Iterating it supplies all coefficients of the unique expansion. In
particular, every output coefficient is obtained by a finite iteration of
ring operations and inversion of the leading unit. The final map theorem
records coefficient specialization explicitly.
-/

namespace LanglandsSecondMainLemma.Residues

noncomputable section

open scoped PowerSeries LaurentSeries

namespace FreeBasis

/-- The ramified parameter `u(t) = t^e v(t)`. -/
def parameter {R : Type*} [CommRing R] (e : ℕ) (v : PowerSeries R) : PowerSeries R :=
  PowerSeries.X ^ e * v

@[simp]
theorem parameter_coeff_zero {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) : PowerSeries.constantCoeff (parameter e v) = 0 := by
  simp [parameter, NeZero.ne e]

/-- Substitution of `parameter e v` is defined when `e` is positive. -/
theorem parameter_hasSubst {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) : PowerSeries.HasSubst (parameter e v) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (parameter_coeff_zero e v)

/-- A second copy of `R⟦X⟧`, used for the source variable `s`.

The parameters occur in the type so that its algebra structure on the target
power-series ring can remember the substitution `s ↦ X^e v`. -/
def PowerScalars (R : Type*) (_e : ℕ) (_v : PowerSeries R) := ULift.{0} (PowerSeries R)

instance {R : Type*} [CommRing R] (e : ℕ) (v : PowerSeries R) :
    CommRing (PowerScalars R e v) := by
  unfold PowerScalars
  infer_instance

/-- Identification of the source scalar ring with the usual power-series ring. -/
def powerScalarsEquiv {R : Type*} [CommRing R] (e : ℕ) (v : PowerSeries R) :
    PowerScalars R e v ≃+* PowerSeries R := by
  unfold PowerScalars
  exact ULift.ringEquiv

/-- The scalar map `R⟦s⟧ → R⟦t⟧`, `s ↦ t^e v(t)`. -/
def powerSubstitution {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) : PowerScalars R e v →+* PowerSeries R :=
  (PowerSeries.substAlgHom (parameter_hasSubst e v)).toRingHom.comp
    (powerScalarsEquiv e v).toRingHom

instance {R : Type*} [CommRing R] (e : ℕ) [NeZero e] (v : PowerSeries R) :
    Algebra (PowerScalars R e v) (PowerSeries R) :=
  (powerSubstitution e v).toAlgebra

@[simp]
theorem algebraMap_powerScalars_apply {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) (f : PowerScalars R e v) :
    algebraMap (PowerScalars R e v) (PowerSeries R) f =
      PowerSeries.subst (parameter e v) ((powerScalarsEquiv e v) f) := by
  change powerSubstitution e v f = _
  simp [powerSubstitution, powerScalarsEquiv, PowerSeries.coe_substAlgHom]

/-- The inverse of the unit power series `v`, constructed from its unit
constant coefficient. -/
def inverseUnit {R : Type*} [CommRing R] (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) : PowerSeries R :=
  PowerSeries.invOfUnit v hv.unit

@[simp]
theorem mul_inverseUnit {R : Type*} [CommRing R] (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) : v * inverseUnit v hv = 1 := by
  exact PowerSeries.mul_invOfUnit v hv.unit hv.unit_spec.symm

@[simp]
theorem inverseUnit_mul {R : Type*} [CommRing R] (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) : inverseUnit v hv * v = 1 := by
  exact PowerSeries.invOfUnit_mul v hv.unit hv.unit_spec.symm

/-- One step of successive coefficient cancellation: discard the first `e`
coefficients and divide the remaining series by `v`. -/
def quotient {R : Type*} [CommRing R] (e : ℕ) (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) (f : PowerSeries R) : PowerSeries R :=
  inverseUnit v hv * PowerSeries.mk (fun n ↦ PowerSeries.coeff (n + e) f)

/-- The elementary division identity underlying coefficient cancellation. -/
theorem eq_parameter_mul_quotient_add_trunc {R : Type*} [CommRing R] (e : ℕ)
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v)) (f : PowerSeries R) :
    f = parameter e v * quotient e v hv f + (PowerSeries.trunc e f : PowerSeries R) := by
  rw [parameter, quotient]
  calc
    f = PowerSeries.X ^ e * PowerSeries.mk (fun n ↦ PowerSeries.coeff (n + e) f) +
        (PowerSeries.trunc e f : PowerSeries R) := PowerSeries.eq_X_pow_mul_shift_add_trunc e f
    _ = (PowerSeries.X ^ e * v) *
          (inverseUnit v hv * PowerSeries.mk (fun n ↦ PowerSeries.coeff (n + e) f)) +
        (PowerSeries.trunc e f : PowerSeries R) := by
      rw [← mul_assoc (PowerSeries.X ^ e * v) (inverseUnit v hv)
        (PowerSeries.mk (fun n ↦ PowerSeries.coeff (n + e) f)),
        mul_assoc (PowerSeries.X ^ e) v (inverseUnit v hv), mul_inverseUnit, mul_one]

/-- The first `e` coefficients, written in the claimed basis. -/
theorem trunc_eq_sum_fin {R : Type*} [CommRing R] (e : ℕ) (f : PowerSeries R) :
    (PowerSeries.trunc e f : PowerSeries R) =
      ∑ i : Fin e, PowerSeries.C (PowerSeries.coeff i f) * PowerSeries.X ^ (i : ℕ) := by
  ext n
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  simp only [map_sum]
  by_cases hn : n < e
  · rw [if_pos hn, Finset.sum_eq_single ⟨n, hn⟩]
    · simp
    · intro j _ hj
      rw [PowerSeries.coeff_C_mul_X_pow, if_neg]
      exact fun h ↦ hj (Fin.ext h.symm)
    · simp
  · rw [if_neg hn]
    symm
    apply Finset.sum_eq_zero
    intro i _
    simp only [PowerSeries.coeff_C_mul_X_pow]
    rw [if_neg]
    exact fun h ↦ hn (h ▸ i.isLt)

/-- The finite approximation obtained after `N` cancellation steps. -/
def approximation {R : Type*} [CommRing R] (e : ℕ) (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) (N : ℕ) (f : PowerSeries R) : PowerSeries R :=
  ∑ j ∈ Finset.range N,
    parameter e v ^ j *
      (PowerSeries.trunc e ((quotient e v hv)^[j] f) : PowerSeries R)

/-- Iterating elementary division leaves a remainder divisible by `u^N`. -/
theorem eq_approximation_add_remainder {R : Type*} [CommRing R] (e : ℕ)
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v)) (N : ℕ)
    (f : PowerSeries R) :
    f = approximation e v hv N f +
      parameter e v ^ N * (quotient e v hv)^[N] f := by
  induction N with
  | zero => simp [approximation]
  | succ N ih =>
      calc
        f = approximation e v hv N f +
            parameter e v ^ N * (quotient e v hv)^[N] f := ih
        _ = approximation e v hv N f + parameter e v ^ N *
              (parameter e v * quotient e v hv ((quotient e v hv)^[N] f) +
                (PowerSeries.trunc e ((quotient e v hv)^[N] f) : PowerSeries R)) := by
              rw [← eq_parameter_mul_quotient_add_trunc e v hv
                ((quotient e v hv)^[N] f)]
        _ = approximation e v hv (N + 1) f +
              parameter e v ^ (N + 1) * (quotient e v hv)^[N + 1] f := by
              rw [approximation, approximation, Finset.sum_range_succ,
                Function.iterate_succ_apply', pow_succ]
              ring

/-- A sufficiently high remainder has zero prescribed coefficient. -/
theorem coeff_remainder_eq_zero {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v)) (n : ℕ)
    (f : PowerSeries R) :
    PowerSeries.coeff n
      (parameter e v ^ (n + 1) * (quotient e v hv)^[n + 1] f) = 0 := by
  rw [parameter, mul_pow, ← pow_mul, mul_assoc, PowerSeries.coeff_X_pow_mul']
  rw [if_neg]
  exact Nat.not_le_of_lt (lt_of_lt_of_le n.lt_succ_self <| Nat.le_mul_of_pos_left _ (NeZero.pos e))

/-- The coefficient series produced by successive cancellation. -/
def coordinates {R : Type*} [CommRing R] (e : ℕ) (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) (f : PowerSeries R) (i : Fin e) :
    PowerScalars R e v :=
  ⟨PowerSeries.mk (fun j ↦ PowerSeries.coeff i ((quotient e v hv)^[j] f))⟩

@[simp]
theorem coeff_coordinates {R : Type*} [CommRing R] (e : ℕ) (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) (f : PowerSeries R) (i : Fin e) (j : ℕ) :
    PowerSeries.coeff j ((powerScalarsEquiv e v) (coordinates e v hv f i)) =
      PowerSeries.coeff i ((quotient e v hv)^[j] f) := by
  change PowerSeries.coeff j
    (PowerSeries.mk (fun j ↦ PowerSeries.coeff i ((quotient e v hv)^[j] f))) = _
  simp

/-- Powers of the ramified parameter have the expected coefficient
vanishing below degree `e * d`. -/
theorem coeff_parameter_pow_eq_zero_of_lt {R : Type*} [CommRing R] (e : ℕ)
    (v : PowerSeries R) (d n : ℕ) (h : n < e * d) :
    PowerSeries.coeff n (parameter e v ^ d) = 0 := by
  rw [parameter, mul_pow, ← pow_mul, PowerSeries.coeff_X_pow_mul', if_neg h.not_ge]

/-- Substitution through a zero-constant parameter has finite coefficient
dependence: coefficient `n < N` sees only the first `N` input coefficients. -/
theorem coeff_subst_eq_coeff_subst_trunc_of_lt {R : Type*} [CommRing R]
    (e : ℕ) [NeZero e] (v f : PowerSeries R) {n N : ℕ} (hn : n < N) :
    PowerSeries.coeff n (PowerSeries.subst (parameter e v) f) =
      PowerSeries.coeff n
        (PowerSeries.subst (parameter e v) (PowerSeries.trunc N f : PowerSeries R)) := by
  rw [PowerSeries.coeff_subst' (parameter_hasSubst e v),
    PowerSeries.coeff_subst' (parameter_hasSubst e v)]
  apply finsum_congr
  intro d
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  by_cases hd : d < N
  · rw [if_pos hd]
  · rw [if_neg hd, zero_smul]
    have hnd : n < d := lt_of_lt_of_le hn (Nat.le_of_not_gt hd)
    have hde : d ≤ e * d := Nat.le_mul_of_pos_left d (NeZero.pos e)
    rw [coeff_parameter_pow_eq_zero_of_lt e v d n (hnd.trans_le hde), smul_zero]

/-- Substitution of a truncation is the corresponding finite polynomial in
the ramified parameter. -/
theorem subst_trunc_eq_sum_range {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v f : PowerSeries R) (N : ℕ) :
    PowerSeries.subst (parameter e v) (PowerSeries.trunc N f : PowerSeries R) =
      ∑ j ∈ Finset.range N,
        PowerSeries.C (PowerSeries.coeff j f) * parameter e v ^ j := by
  rw [PowerSeries.subst_coe (parameter_hasSubst e v)]
  simpa [Polynomial.aeval_def] using
    (PowerSeries.eval₂_trunc_eq_sum_range (parameter e v) PowerSeries.C N f)

/-- Synthesis of a family of coefficient series in the claimed basis. -/
def reconstruct {R : Type*} [CommRing R] (e : ℕ) [NeZero e] (v : PowerSeries R)
    (H : Fin e → PowerScalars R e v) : PowerSeries R :=
  ∑ i : Fin e,
    algebraMap (PowerScalars R e v) (PowerSeries R) (H i) * PowerSeries.X ^ (i : ℕ)

/-- Truncating all coefficient series turns reconstruction into the finite
cancellation approximation. -/
theorem reconstruct_truncated_coordinates {R : Type*} [CommRing R]
    (e : ℕ) [NeZero e] (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) (N : ℕ) (f : PowerSeries R) :
    ∑ i : Fin e,
        PowerSeries.subst (parameter e v)
            (PowerSeries.trunc N ((powerScalarsEquiv e v) (coordinates e v hv f i)) :
              PowerSeries R) *
          PowerSeries.X ^ (i : ℕ) =
      approximation e v hv N f := by
  rw [approximation]
  simp_rw [subst_trunc_eq_sum_range, trunc_eq_sum_fin]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  simp only [coeff_coordinates]
  ring

/-- Existence of the successive-cancellation expansion. -/
theorem reconstruct_coordinates {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v)) (f : PowerSeries R) :
    reconstruct e v (coordinates e v hv f) = f := by
  symm
  ext n
  have hfinite := reconstruct_truncated_coordinates e v hv (n + 1) f
  have happ := eq_approximation_add_remainder e v hv (n + 1) f
  calc
    PowerSeries.coeff n f = PowerSeries.coeff n (approximation e v hv (n + 1) f) := by
      have := congrArg (PowerSeries.coeff n) happ
      rw [map_add, coeff_remainder_eq_zero e v hv n f, add_zero] at this
      exact this
    _ = PowerSeries.coeff n
          (∑ i : Fin e,
            PowerSeries.subst (parameter e v)
                (PowerSeries.trunc (n + 1)
                    ((powerScalarsEquiv e v) (coordinates e v hv f i)) : PowerSeries R) *
              PowerSeries.X ^ (i : ℕ)) := congrArg (PowerSeries.coeff n) hfinite.symm
    _ = PowerSeries.coeff n (reconstruct e v (coordinates e v hv f)) := by
      rw [reconstruct]
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow']
      split_ifs with hin
      · rw [algebraMap_powerScalars_apply]
        exact (coeff_subst_eq_coeff_subst_trunc_of_lt e v _
          (Nat.sub_lt_succ n i)).symm
      · rfl

/-- Remove the constant coefficient from a scalar series. -/
def scalarShift {R : Type*} [CommRing R] (e : ℕ) (v : PowerSeries R)
    (H : PowerScalars R e v) : PowerScalars R e v :=
  ⟨PowerSeries.mk (fun n ↦ PowerSeries.coeff (n + 1) ((powerScalarsEquiv e v) H))⟩

@[simp]
theorem coeff_scalarShift {R : Type*} [CommRing R] (e : ℕ) (v : PowerSeries R)
    (H : PowerScalars R e v) (n : ℕ) :
    PowerSeries.coeff n ((powerScalarsEquiv e v) (scalarShift e v H)) =
      PowerSeries.coeff (n + 1) ((powerScalarsEquiv e v) H) := by
  change PowerSeries.coeff n
    (PowerSeries.mk (fun n ↦ PowerSeries.coeff (n + 1) ((powerScalarsEquiv e v) H))) = _
  simp

/-- The source-series head/tail identity after substitution. -/
theorem algebraMap_eq_parameter_mul_shift_add_const {R : Type*} [CommRing R]
    (e : ℕ) [NeZero e] (v : PowerSeries R) (H : PowerScalars R e v) :
    algebraMap (PowerScalars R e v) (PowerSeries R) H =
      parameter e v *
          algebraMap (PowerScalars R e v) (PowerSeries R) (scalarShift e v H) +
        PowerSeries.C (PowerSeries.constantCoeff ((powerScalarsEquiv e v) H)) := by
  rw [algebraMap_powerScalars_apply, algebraMap_powerScalars_apply]
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const ((powerScalarsEquiv e v) H)]
  rw [PowerSeries.subst_add (parameter_hasSubst e v),
    PowerSeries.subst_mul (parameter_hasSubst e v),
    PowerSeries.subst_X (parameter_hasSubst e v), PowerSeries.subst_C]
  change parameter e v *
      PowerSeries.subst (parameter e v)
        (PowerSeries.mk (fun p ↦
          PowerSeries.coeff (p + 1) ((powerScalarsEquiv e v) H))) +
      PowerSeries.C (PowerSeries.constantCoeff ((powerScalarsEquiv e v) H)) = _
  rfl

/-- Reconstruction obeys the same cancellation recurrence as an individual
power series. -/
theorem reconstruct_eq_parameter_mul_shift_add_head {R : Type*} [CommRing R]
    (e : ℕ) [NeZero e] (v : PowerSeries R) (H : Fin e → PowerScalars R e v) :
    reconstruct e v H = parameter e v * reconstruct e v (fun i ↦ scalarShift e v (H i)) +
      ∑ i : Fin e,
        PowerSeries.C (PowerSeries.constantCoeff ((powerScalarsEquiv e v) (H i))) *
          PowerSeries.X ^ (i : ℕ) := by
  calc
    reconstruct e v H =
        ∑ i : Fin e,
          (parameter e v *
              algebraMap (PowerScalars R e v) (PowerSeries R) (scalarShift e v (H i)) +
            PowerSeries.C (PowerSeries.constantCoeff ((powerScalarsEquiv e v) (H i)))) *
            PowerSeries.X ^ (i : ℕ) := by
      rw [reconstruct]
      apply Finset.sum_congr rfl
      intro i hi
      rw [algebraMap_eq_parameter_mul_shift_add_const]
    _ = parameter e v * reconstruct e v (fun i ↦ scalarShift e v (H i)) +
        ∑ i : Fin e,
          PowerSeries.C (PowerSeries.constantCoeff ((powerScalarsEquiv e v) (H i))) *
            PowerSeries.X ^ (i : ℕ) := by
      rw [reconstruct]
      simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      have hsum :
          (∑ i : Fin e,
              parameter e v *
                algebraMap (PowerScalars R e v) (PowerSeries R) (scalarShift e v (H i)) *
                PowerSeries.X ^ (i : ℕ)) =
            ∑ i : Fin e,
              parameter e v *
                (algebraMap (PowerScalars R e v) (PowerSeries R) (scalarShift e v (H i)) *
                  PowerSeries.X ^ (i : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hsum]

/-- Discard the first `e` coefficients of a power series. -/
def shiftAfter {R : Type*} [CommRing R] (e : ℕ) (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk (fun n ↦ PowerSeries.coeff (n + e) f)

@[simp]
theorem shiftAfter_add {R : Type*} [CommRing R] (e : ℕ) (f g : PowerSeries R) :
    shiftAfter e (f + g) = shiftAfter e f + shiftAfter e g := by
  ext n
  simp [shiftAfter]

@[simp]
theorem shiftAfter_X_pow_mul {R : Type*} [CommRing R] (e : ℕ) (f : PowerSeries R) :
    shiftAfter e (PowerSeries.X ^ e * f) = f := by
  ext n
  simp [shiftAfter, PowerSeries.coeff_X_pow_mul]

@[simp]
theorem shiftAfter_parameter_mul {R : Type*} [CommRing R] (e : ℕ)
    (v f : PowerSeries R) : shiftAfter e (parameter e v * f) = v * f := by
  rw [parameter, mul_assoc, shiftAfter_X_pow_mul]

/-- The polynomial head attached to a family of scalar series. -/
def head {R : Type*} [CommRing R] (e : ℕ) (v : PowerSeries R)
    (H : Fin e → PowerScalars R e v) : PowerSeries R :=
  ∑ i : Fin e,
    PowerSeries.C (PowerSeries.constantCoeff ((powerScalarsEquiv e v) (H i))) *
      PowerSeries.X ^ (i : ℕ)

@[simp]
theorem coeff_head {R : Type*} [CommRing R] (e : ℕ) (v : PowerSeries R)
    (H : Fin e → PowerScalars R e v) (i : Fin e) :
    PowerSeries.coeff i (head e v H) =
      PowerSeries.constantCoeff ((powerScalarsEquiv e v) (H i)) := by
  rw [head, map_sum, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [PowerSeries.coeff_C_mul_X_pow, if_neg]
    exact fun h ↦ hji (Fin.ext h.symm)
  · simp

@[simp]
theorem shiftAfter_head {R : Type*} [CommRing R] (e : ℕ) (v : PowerSeries R)
    (H : Fin e → PowerScalars R e v) : shiftAfter e (head e v H) = 0 := by
  ext n
  rw [shiftAfter, PowerSeries.coeff_mk, head, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [PowerSeries.coeff_C_mul_X_pow, if_neg]
  exact fun h ↦ (Nat.not_lt_of_ge (Nat.le_add_left e n)) (h ▸ i.isLt)

/-- The quotient operation is inverse to adjoining a polynomial head. -/
theorem quotient_parameter_mul_add_head {R : Type*} [CommRing R] (e : ℕ)
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v))
    (q : PowerSeries R) (H : Fin e → PowerScalars R e v) :
    quotient e v hv (parameter e v * q + head e v H) = q := by
  rw [quotient]
  change inverseUnit v hv * shiftAfter e (parameter e v * q + head e v H) = q
  rw [shiftAfter_add, shiftAfter_parameter_mul, shiftAfter_head, add_zero,
    ← mul_assoc, inverseUnit_mul, one_mul]

/-- One cancellation step on a reconstructed expansion removes the constant
coefficient of every scalar series. -/
theorem quotient_reconstruct {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v))
    (H : Fin e → PowerScalars R e v) :
    quotient e v hv (reconstruct e v H) =
      reconstruct e v (fun i ↦ scalarShift e v (H i)) := by
  rw [reconstruct_eq_parameter_mul_shift_add_head]
  exact quotient_parameter_mul_add_head e v hv _ H

/-- Below degree `e`, reconstruction reads the constant coefficient of the
corresponding scalar series. -/
theorem coeff_reconstruct {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) (H : Fin e → PowerScalars R e v) (i : Fin e) :
    PowerSeries.coeff i (reconstruct e v H) =
      PowerSeries.constantCoeff ((powerScalarsEquiv e v) (H i)) := by
  rw [reconstruct_eq_parameter_mul_shift_add_head, map_add]
  change PowerSeries.coeff i
      (parameter e v * reconstruct e v (fun i ↦ scalarShift e v (H i))) +
      PowerSeries.coeff i (head e v H) = _
  rw [coeff_head]
  rw [parameter, mul_assoc, PowerSeries.coeff_X_pow_mul', if_neg i.isLt.not_ge, zero_add]

/-- Iterated target quotients agree with iterated shifts of every source
coefficient series. -/
theorem iterate_quotient_reconstruct {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v))
    (H : Fin e → PowerScalars R e v) (j : ℕ) :
    (quotient e v hv)^[j] (reconstruct e v H) =
      reconstruct e v (fun i ↦ (scalarShift e v)^[j] (H i)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      calc
        (quotient e v hv)^[j + 1] (reconstruct e v H) =
            quotient e v hv ((quotient e v hv)^[j] (reconstruct e v H)) := by
              rw [Function.iterate_succ_apply']
        _ = quotient e v hv
              (reconstruct e v (fun i ↦ (scalarShift e v)^[j] (H i))) :=
            congrArg (quotient e v hv) ih
        _ = reconstruct e v
              (fun i ↦ scalarShift e v ((scalarShift e v)^[j] (H i))) :=
            quotient_reconstruct e v hv _
        _ = reconstruct e v (fun i ↦ (scalarShift e v)^[j + 1] (H i)) := by
            apply congrArg (reconstruct e v)
            funext i
            rw [Function.iterate_succ_apply']

/-- Iterating the scalar shift simply advances coefficient indices. -/
theorem coeff_iterate_scalarShift {R : Type*} [CommRing R] (e : ℕ)
    (v : PowerSeries R) (H : PowerScalars R e v) (j n : ℕ) :
    PowerSeries.coeff n ((powerScalarsEquiv e v) ((scalarShift e v)^[j] H)) =
      PowerSeries.coeff (n + j) ((powerScalarsEquiv e v) H) := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', coeff_scalarShift]
      simpa only [Nat.add_assoc, Nat.add_comm 1 j] using ih (n + 1)

/-- Successive cancellation is also a left inverse to reconstruction.  This
is the uniqueness assertion in Lemma B.2. -/
theorem coordinates_reconstruct {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v))
    (H : Fin e → PowerScalars R e v) : coordinates e v hv (reconstruct e v H) = H := by
  funext i
  apply (powerScalarsEquiv e v).injective
  ext j
  rw [coeff_coordinates, iterate_quotient_reconstruct, coeff_reconstruct]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [coeff_iterate_scalarShift]
  simp

/-- Reconstruction is injective; equivalently, the expansion is unique. -/
theorem reconstruct_injective {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v)) :
    Function.Injective (reconstruct e v) := by
  intro H K h
  rw [← coordinates_reconstruct e v hv H, ← coordinates_reconstruct e v hv K, h]

/-- The powers `1, X, …, X^(e-1)` are linearly independent over the
substitution scalars. -/
theorem powerBasis_linearIndependent {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v)) :
    LinearIndependent (PowerScalars R e v)
      (fun i : Fin e ↦ (PowerSeries.X ^ (i : ℕ) : PowerSeries R)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hg' : reconstruct e v g = 0 := by
    simpa only [reconstruct, Algebra.smul_def] using hg
  have hz : reconstruct e v (fun _ ↦ 0) = 0 := by
    rw [reconstruct]
    simp only [map_zero, zero_mul, Finset.sum_const_zero]
  have hzero : reconstruct e v g = reconstruct e v (fun _ ↦ 0) := by
    rw [hg', hz]
  exact congrFun (reconstruct_injective e v hv hzero) i

/-- The powers `1, X, …, X^(e-1)` span the target power-series ring over
the substitution scalars. -/
theorem powerBasis_span {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v)) :
    Submodule.span (PowerScalars R e v)
        (Set.range (fun i : Fin e ↦
          (PowerSeries.X ^ (i : ℕ) : PowerSeries R))) = ⊤ := by
  apply top_unique
  intro f hf
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨coordinates e v hv f, ?_⟩
  simpa [reconstruct, Algebra.smul_def] using reconstruct_coordinates e v hv f

/-- The power-series basis from Appendix B, Lemma B.2. -/
noncomputable def powerSeriesBasis {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v)) :
    Module.Basis (Fin e) (PowerScalars R e v) (PowerSeries R) :=
  Module.Basis.mk (powerBasis_linearIndependent e v hv) (powerBasis_span e v hv).ge

@[simp]
theorem powerSeriesBasis_apply {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v)) (i : Fin e) :
    powerSeriesBasis e v hv i = PowerSeries.X ^ (i : ℕ) :=
  Module.Basis.mk_apply _ _ i

/-- Map a source coefficient series along a coefficient-ring homomorphism. -/
def mapPowerScalar {R S : Type*} [CommRing R] [CommRing S] (e : ℕ)
    (v : PowerSeries R) (mapCoeffs : R →+* S) (H : PowerScalars R e v) :
    PowerScalars S e (PowerSeries.map mapCoeffs v) :=
  ⟨PowerSeries.map mapCoeffs ((powerScalarsEquiv e v) H)⟩

@[simp]
theorem powerScalarsEquiv_mapPowerScalar {R S : Type*} [CommRing R] [CommRing S]
    (e : ℕ) (v : PowerSeries R) (mapCoeffs : R →+* S) (H : PowerScalars R e v) :
    (powerScalarsEquiv e (PowerSeries.map mapCoeffs v)) (mapPowerScalar e v mapCoeffs H) =
      PowerSeries.map mapCoeffs ((powerScalarsEquiv e v) H) := by
  rfl

@[simp]
theorem map_parameter {R S : Type*} [CommRing R] [CommRing S] (e : ℕ)
    (v : PowerSeries R) (mapCoeffs : R →+* S) :
    PowerSeries.map mapCoeffs (parameter e v) = parameter e (PowerSeries.map mapCoeffs v) := by
  simp [parameter]

/-- Reconstruction commutes with every specialization of the coefficient
ring. -/
theorem map_reconstruct {R S : Type*} [CommRing R] [CommRing S] (e : ℕ) [NeZero e]
    (v : PowerSeries R) (mapCoeffs : R →+* S) (H : Fin e → PowerScalars R e v) :
    PowerSeries.map mapCoeffs (reconstruct e v H) =
      reconstruct e (PowerSeries.map mapCoeffs v) (fun i ↦ mapPowerScalar e v mapCoeffs (H i)) := by
  rw [reconstruct, reconstruct, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul, map_pow, PowerSeries.map_X, algebraMap_powerScalars_apply,
    algebraMap_powerScalars_apply]
  congr 1
  have hmap := PowerSeries.map_subst (h := mapCoeffs) (parameter_hasSubst e v)
    ((powerScalarsEquiv e v) (H i))
  change PowerSeries.map mapCoeffs
      (PowerSeries.subst (parameter e v) ((powerScalarsEquiv e v) (H i))) =
    PowerSeries.subst (PowerSeries.map mapCoeffs (parameter e v))
      (PowerSeries.map mapCoeffs ((powerScalarsEquiv e v) (H i))) at hmap
  simpa only [map_parameter, powerScalarsEquiv_mapPowerScalar] using hmap

/-- The coefficient expansions commute with arbitrary specialization.  This
is the formal finite-dependence assertion in the last sentence of Lemma B.2. -/
theorem map_coordinates {R S : Type*} [CommRing R] [CommRing S] (e : ℕ) [NeZero e]
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v))
    (mapCoeffs : R →+* S) (f : PowerSeries R) :
    coordinates e (PowerSeries.map mapCoeffs v)
        (hv.map mapCoeffs) (PowerSeries.map mapCoeffs f) =
      fun i ↦ mapPowerScalar e v mapCoeffs (coordinates e v hv f i) := by
  apply reconstruct_injective e (PowerSeries.map mapCoeffs v) (hv.map mapCoeffs)
  rw [reconstruct_coordinates, ← map_reconstruct, reconstruct_coordinates]

/-- Specialization as a ring homomorphism on the distinguished source
power-series scalar rings. -/
def mapPowerScalars {R S : Type*} [CommRing R] [CommRing S] (e : ℕ)
    (v : PowerSeries R) (mapCoeffs : R →+* S) :
    PowerScalars R e v →+* PowerScalars S e (PowerSeries.map mapCoeffs v) :=
  (powerScalarsEquiv e (PowerSeries.map mapCoeffs v)).symm.toRingHom.comp
    ((PowerSeries.map mapCoeffs).comp (powerScalarsEquiv e v).toRingHom)

@[simp]
theorem mapPowerScalars_apply {R S : Type*} [CommRing R] [CommRing S] (e : ℕ)
    (v : PowerSeries R) (mapCoeffs : R →+* S) (H : PowerScalars R e v) :
    mapPowerScalars e v mapCoeffs H = mapPowerScalar e v mapCoeffs H := by
  rfl

/-- The recursively constructed coordinates are the coordinates of the
power-series basis. -/
theorem powerSeriesBasis_repr_apply {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v))
    (f : PowerSeries R) (i : Fin e) :
    (powerSeriesBasis e v hv).repr f i = coordinates e v hv f i := by
  have hsum := (powerSeriesBasis e v hv).sum_repr f
  have hreconstruct :
      reconstruct e v (fun j ↦ (powerSeriesBasis e v hv).repr f j) = f := by
    simpa only [reconstruct, Algebra.smul_def, powerSeriesBasis_apply] using hsum
  have hcoordinates := congrFun
    (coordinates_reconstruct e v hv
      (fun j ↦ (powerSeriesBasis e v hv).repr f j)) i
  rw [hreconstruct] at hcoordinates
  exact hcoordinates.symm

/-- The matrix of multiplication by a power series in the basis
`1, X, …, X^(e-1)`. -/
noncomputable def powerMultiplicationMatrix {R : Type*} [CommRing R] (e : ℕ)
    [NeZero e] (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v))
    (f : PowerSeries R) : Matrix (Fin e) (Fin e) (PowerScalars R e v) :=
  Algebra.leftMulMatrix (powerSeriesBasis e v hv) f

/-- Multiplication matrices for the power-series basis commute entrywise
with arbitrary coefficient specialization. -/
theorem map_powerMultiplicationMatrix {R S : Type*} [CommRing R] [CommRing S]
    (e : ℕ) [NeZero e] (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) (mapCoeffs : R →+* S)
    (f : PowerSeries R) :
    (powerMultiplicationMatrix e v hv f).map (mapPowerScalars e v mapCoeffs) =
      powerMultiplicationMatrix e (PowerSeries.map mapCoeffs v) (hv.map mapCoeffs)
        (PowerSeries.map mapCoeffs f) := by
  ext i j
  simp only [Matrix.map_apply, powerMultiplicationMatrix,
    Algebra.leftMulMatrix_eq_repr_mul, powerSeriesBasis_repr_apply,
    powerSeriesBasis_apply, mapPowerScalars_apply]
  rw [← congrFun (map_coordinates e v hv mapCoeffs
    (f * PowerSeries.X ^ (j : ℕ))) i, map_mul, map_pow, PowerSeries.map_X]

/-- A second copy of the Laurent-series ring.  The proof parameter records
exactly the hypothesis needed to extend the ramified substitution across the
inverted source parameter. -/
def LaurentScalars (R : Type*) [CommRing R] (_e : ℕ) (v : PowerSeries R)
    (_hv : IsUnit (PowerSeries.constantCoeff v)) := ULift.{0} (LaurentSeries R)

instance {R : Type*} [CommRing R] (e : ℕ) (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) :
    CommRing (LaurentScalars R e v hv) := by
  unfold LaurentScalars
  infer_instance

/-- Identification of the source Laurent scalar ring with `R((s))`. -/
def laurentScalarsEquiv {R : Type*} [CommRing R] (e : ℕ) (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) :
    LaurentScalars R e v hv ≃+* LaurentSeries R := by
  unfold LaurentScalars
  exact ULift.ringEquiv

/-- The source parameter `s`, inside the distinguished copy of `R⟦s⟧`. -/
def scalarX {R : Type*} [CommRing R] (e : ℕ) (v : PowerSeries R) :
    PowerScalars R e v :=
  (powerScalarsEquiv e v).symm PowerSeries.X

@[simp]
theorem powerScalarsEquiv_scalarX {R : Type*} [CommRing R] (e : ℕ)
    (v : PowerSeries R) : (powerScalarsEquiv e v) (scalarX e v) = PowerSeries.X := by
  rfl

@[simp]
theorem algebraMap_scalarX {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) :
    algebraMap (PowerScalars R e v) (PowerSeries R) (scalarX e v) = parameter e v := by
  rw [algebraMap_powerScalars_apply, powerScalarsEquiv_scalarX,
    PowerSeries.subst_X (parameter_hasSubst e v)]

/-- The canonical inclusion `R⟦s⟧ → R((s))`. -/
def powerToLaurentScalars {R : Type*} [CommRing R] (e : ℕ) (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) :
    PowerScalars R e v →+* LaurentScalars R e v hv :=
  (laurentScalarsEquiv e v hv).symm.toRingHom.comp
    ((algebraMap (PowerSeries R) (LaurentSeries R)).comp
      (powerScalarsEquiv e v).toRingHom)

instance {R : Type*} [CommRing R] (e : ℕ) (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) :
    Algebra (PowerScalars R e v) (LaurentScalars R e v hv) :=
  (powerToLaurentScalars e v hv).toAlgebra

/-- `R((s))` is obtained from the distinguished copy of `R⟦s⟧` by
inverting `s`. -/
instance laurentScalars_isLocalization {R : Type*} [CommRing R] (e : ℕ)
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v)) :
    IsLocalization.Away (scalarX e v) (LaurentScalars R e v hv) := by
  letI : Algebra (PowerScalars R e v) (LaurentSeries R) :=
    (((algebraMap (PowerSeries R) (LaurentSeries R)).comp
      (powerScalarsEquiv e v).toRingHom)).toAlgebra
  have hsource : IsLocalization.Away (scalarX e v) (LaurentSeries R) := by
    apply IsLocalization.of_ringEquiv_left (M₁ := Submonoid.powers PowerSeries.X)
      (M₂ := Submonoid.powers (scalarX e v)) (powerScalarsEquiv e v)
    · rw [Submonoid.map_powers, powerScalarsEquiv_scalarX]
    · intro x
      rfl
  let sourceEquiv : LaurentSeries R ≃ₐ[PowerScalars R e v]
      LaurentScalars R e v hv :=
    { toRingEquiv := (laurentScalarsEquiv e v hv).symm
      commutes' := fun _ ↦ rfl }
  exact IsLocalization.isLocalization_of_algEquiv
    (Submonoid.powers (scalarX e v)) sourceEquiv

/-- The coefficient map from the source copy of `R⟦s⟧` to the target
Laurent-series ring, before extending across `s⁻¹`. -/
def powerToTargetLaurent {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) : PowerScalars R e v →+* LaurentSeries R :=
  (algebraMap (PowerSeries R) (LaurentSeries R)).comp (powerSubstitution e v)

instance {R : Type*} [CommRing R] (e : ℕ) [NeZero e] (v : PowerSeries R) :
    Algebra (PowerScalars R e v) (LaurentSeries R) :=
  (powerToTargetLaurent e v).toAlgebra

instance {R : Type*} [CommRing R] (e : ℕ) [NeZero e] (v : PowerSeries R) :
    IsScalarTower (PowerScalars R e v) (PowerSeries R) (LaurentSeries R) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Inverting `X` also inverts every positive power `X^e`. -/
theorem power_parameter_isLocalization {R : Type*} [CommRing R] (e : ℕ) [NeZero e] :
    IsLocalization.Away (PowerSeries.X ^ e : PowerSeries R) (LaurentSeries R) := by
  refine (IsLocalization.iff_of_le_of_exists_dvd
    (Submonoid.powers (PowerSeries.X ^ e : PowerSeries R))
    (Submonoid.powers (PowerSeries.X : PowerSeries R)) ?_ ?_).2 inferInstance
  · rw [Submonoid.powers_le]
    exact ⟨e, rfl⟩
  · intro x hx
    obtain ⟨n, rfl⟩ := hx
    refine ⟨(PowerSeries.X ^ e : PowerSeries R) ^ n, ⟨n, rfl⟩, ?_⟩
    rw [← pow_mul]
    exact pow_dvd_pow PowerSeries.X (Nat.le_mul_of_pos_left n (NeZero.pos e))

/-- Since `v` is a unit, localizing away from `X^e v` gives the usual
Laurent-series ring. -/
theorem parameter_isLocalization {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v)) :
    IsLocalization.Away (parameter e v) (LaurentSeries R) := by
  letI : IsLocalization.Away (PowerSeries.X ^ e : PowerSeries R)
      (LaurentSeries R) := power_parameter_isLocalization e
  have hassoc : Associated (PowerSeries.X ^ e : PowerSeries R) (parameter e v) := by
    rw [parameter]
    exact associated_mul_unit_right _ _ (PowerSeries.isUnit_iff_constantCoeff.mpr hv)
  exact IsLocalization.Away.of_associated (S := LaurentSeries R) hassoc

@[simp]
theorem powerToTargetLaurent_scalarX {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) :
    powerToTargetLaurent e v (scalarX e v) =
      algebraMap (PowerSeries R) (LaurentSeries R) (parameter e v) := by
  rw [powerToTargetLaurent, RingHom.comp_apply]
  change algebraMap (PowerSeries R) (LaurentSeries R)
    (algebraMap (PowerScalars R e v) (PowerSeries R) (scalarX e v)) = _
  rw [algebraMap_scalarX]

/-- Extension of `s ↦ X^e v` from `R⟦s⟧` to `R((s))`. -/
noncomputable def laurentSubstitution {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v)) :
    LaurentScalars R e v hv →+* LaurentSeries R := by
  letI : IsLocalization.Away (parameter e v) (LaurentSeries R) :=
    parameter_isLocalization e v hv
  apply IsLocalization.Away.lift (S := LaurentScalars R e v hv)
    (P := LaurentSeries R) (g := powerToTargetLaurent e v) (scalarX e v)
  rw [powerToTargetLaurent_scalarX]
  exact IsLocalization.Away.algebraMap_isUnit (parameter e v)

instance {R : Type*} [CommRing R] (e : ℕ) [NeZero e] (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) :
    Algebra (LaurentScalars R e v hv) (LaurentSeries R) :=
  (laurentSubstitution e v hv).toAlgebra

instance {R : Type*} [CommRing R] (e : ℕ) [NeZero e] (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) :
    IsScalarTower (PowerScalars R e v) (LaurentScalars R e v hv)
      (LaurentSeries R) := by
  apply IsScalarTower.of_algebraMap_eq'
  change powerToTargetLaurent e v =
    (laurentSubstitution e v hv).comp
      (algebraMap (PowerScalars R e v) (LaurentScalars R e v hv))
  letI : IsLocalization.Away (parameter e v) (LaurentSeries R) :=
    parameter_isLocalization e v hv
  have hu : IsUnit ((powerToTargetLaurent e v) (scalarX e v)) := by
    rw [powerToTargetLaurent_scalarX]
    exact IsLocalization.Away.algebraMap_isUnit (parameter e v)
  simpa only [laurentSubstitution] using
    (IsLocalization.Away.lift_comp (S := LaurentScalars R e v hv)
      (x := scalarX e v) hu).symm

/-- The Laurent-series basis obtained by localizing the power-series basis. -/
noncomputable def laurentSeriesBasis {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v)) :
    Module.Basis (Fin e) (LaurentScalars R e v hv) (LaurentSeries R) := by
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid (PowerSeries R)
        (Submonoid.powers (scalarX e v))) (LaurentSeries R) := by
    rw [Algebra.algebraMapSubmonoid_powers, algebraMap_scalarX]
    exact parameter_isLocalization e v hv
  exact (powerSeriesBasis e v hv).localizationLocalization
    (LaurentScalars R e v hv) (Submonoid.powers (scalarX e v)) (LaurentSeries R)

@[simp]
theorem laurentSeriesBasis_apply {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v)) (i : Fin e) :
    laurentSeriesBasis e v hv i =
      algebraMap (PowerSeries R) (LaurentSeries R) (PowerSeries.X ^ (i : ℕ)) := by
  simp [laurentSeriesBasis]

/-- Coefficientwise specialization of Laurent series. -/
def mapLaurentSeries {R S : Type*} [CommRing R] [CommRing S]
    (mapCoeffs : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun f := HahnSeries.map f mapCoeffs
  map_zero' := HahnSeries.map_zero mapCoeffs.toZeroHom
  map_one' := HahnSeries.map_one mapCoeffs.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add mapCoeffs.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul mapCoeffs.toNonUnitalRingHom

@[simp]
theorem mapLaurentSeries_algebraMap {R S : Type*} [CommRing R] [CommRing S]
    (mapCoeffs : R →+* S) (f : PowerSeries R) :
    mapLaurentSeries mapCoeffs (algebraMap (PowerSeries R) (LaurentSeries R) f) =
      algebraMap (PowerSeries S) (LaurentSeries S) (PowerSeries.map mapCoeffs f) := by
  ext n
  change mapCoeffs
      ((algebraMap (PowerSeries R) (LaurentSeries R) f).coeff n) =
    (algebraMap (PowerSeries S) (LaurentSeries S)
      (PowerSeries.map mapCoeffs f)).coeff n
  rw [HahnSeries.algebraMap_apply', HahnSeries.algebraMap_apply',
    Algebra.algebraMap_self_apply, Algebra.algebraMap_self_apply]
  by_cases hn : ∃ k : ℕ, (k : ℤ) = n
  · obtain ⟨k, rfl⟩ := hn
    simp only [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · have hzeroR : ((HahnSeries.ofPowerSeries ℤ R) f).coeff n = 0 := by
      rw [HahnSeries.ofPowerSeries_apply]
      apply HahnSeries.embDomain_notin_image_support
      rintro ⟨k, hk, rfl⟩
      exact hn ⟨k, rfl⟩
    have hzeroS :
        ((HahnSeries.ofPowerSeries ℤ S) (PowerSeries.map mapCoeffs f)).coeff n = 0 := by
      rw [HahnSeries.ofPowerSeries_apply]
      apply HahnSeries.embDomain_notin_image_support
      rintro ⟨k, hk, rfl⟩
      exact hn ⟨k, rfl⟩
    rw [hzeroR, hzeroS, map_zero]

/-- Coefficientwise specialization of the distinguished Laurent scalar
rings. -/
def mapLaurentScalars {R S : Type*} [CommRing R] [CommRing S] (e : ℕ)
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v))
    (mapCoeffs : R →+* S) :
    LaurentScalars R e v hv →+*
      LaurentScalars S e (PowerSeries.map mapCoeffs v) (hv.map mapCoeffs) :=
  (laurentScalarsEquiv e (PowerSeries.map mapCoeffs v) (hv.map mapCoeffs)).symm.toRingHom.comp
    ((mapLaurentSeries mapCoeffs).comp (laurentScalarsEquiv e v hv).toRingHom)

@[simp]
theorem laurentScalarsEquiv_mapLaurentScalars {R S : Type*} [CommRing R]
    [CommRing S] (e : ℕ) (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) (mapCoeffs : R →+* S)
    (H : LaurentScalars R e v hv) :
    laurentScalarsEquiv e (PowerSeries.map mapCoeffs v) (hv.map mapCoeffs)
        (mapLaurentScalars e v hv mapCoeffs H) =
      mapLaurentSeries mapCoeffs (laurentScalarsEquiv e v hv H) := by
  rfl

@[simp]
theorem mapLaurentScalars_algebraMap {R S : Type*} [CommRing R] [CommRing S]
    (e : ℕ) (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v))
    (mapCoeffs : R →+* S) (H : PowerScalars R e v) :
    mapLaurentScalars e v hv mapCoeffs
        (algebraMap (PowerScalars R e v) (LaurentScalars R e v hv) H) =
      algebraMap (PowerScalars S e (PowerSeries.map mapCoeffs v))
        (LaurentScalars S e (PowerSeries.map mapCoeffs v) (hv.map mapCoeffs))
        (mapPowerScalars e v mapCoeffs H) := by
  apply (laurentScalarsEquiv e (PowerSeries.map mapCoeffs v)
    (hv.map mapCoeffs)).injective
  change mapLaurentSeries mapCoeffs
      (algebraMap (PowerSeries R) (LaurentSeries R) ((powerScalarsEquiv e v) H)) =
    algebraMap (PowerSeries S) (LaurentSeries S)
      (PowerSeries.map mapCoeffs ((powerScalarsEquiv e v) H))
  rw [mapLaurentSeries_algebraMap]

/-- Specialization commutes with the coefficient map from source power
scalars to target Laurent series. -/
theorem map_powerToTargetLaurent {R S : Type*} [CommRing R] [CommRing S]
    (e : ℕ) [NeZero e] (v : PowerSeries R) (mapCoeffs : R →+* S)
    (H : PowerScalars R e v) :
    mapLaurentSeries mapCoeffs (powerToTargetLaurent e v H) =
      powerToTargetLaurent e (PowerSeries.map mapCoeffs v)
        (mapPowerScalars e v mapCoeffs H) := by
  rw [powerToTargetLaurent, powerToTargetLaurent, RingHom.comp_apply,
    RingHom.comp_apply]
  change mapLaurentSeries mapCoeffs
      (algebraMap (PowerSeries R) (LaurentSeries R)
        (algebraMap (PowerScalars R e v) (PowerSeries R) H)) =
    algebraMap (PowerSeries S) (LaurentSeries S)
      (algebraMap (PowerScalars S e (PowerSeries.map mapCoeffs v)) (PowerSeries S)
        (mapPowerScalars e v mapCoeffs H))
  rw [mapLaurentSeries_algebraMap, algebraMap_powerScalars_apply,
    algebraMap_powerScalars_apply]
  congr 1
  have hmap := PowerSeries.map_subst (h := mapCoeffs) (parameter_hasSubst e v)
    ((powerScalarsEquiv e v) H)
  change PowerSeries.map mapCoeffs
      (PowerSeries.subst (parameter e v) ((powerScalarsEquiv e v) H)) =
    PowerSeries.subst (PowerSeries.map mapCoeffs (parameter e v))
      (PowerSeries.map mapCoeffs ((powerScalarsEquiv e v) H)) at hmap
  simpa only [map_parameter, mapPowerScalars_apply,
    powerScalarsEquiv_mapPowerScalar] using hmap

/-- The square formed by specialization and the two ramified Laurent
substitutions commutes. -/
theorem mapLaurentSeries_comp_algebraMap {R S : Type*} [CommRing R] [CommRing S]
    (e : ℕ) [NeZero e] (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) (mapCoeffs : R →+* S) :
    (mapLaurentSeries mapCoeffs).comp
        (algebraMap (LaurentScalars R e v hv) (LaurentSeries R)) =
      (algebraMap
        (LaurentScalars S e (PowerSeries.map mapCoeffs v) (hv.map mapCoeffs))
      (LaurentSeries S)).comp (mapLaurentScalars e v hv mapCoeffs) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (scalarX e v))
  apply RingHom.ext
  intro H
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply (PowerScalars R e v)
      (LaurentScalars R e v hv) (LaurentSeries R),
    mapLaurentScalars_algebraMap,
    ← IsScalarTower.algebraMap_apply
      (PowerScalars S e (PowerSeries.map mapCoeffs v))
      (LaurentScalars S e (PowerSeries.map mapCoeffs v) (hv.map mapCoeffs))
      (LaurentSeries S)]
  exact map_powerToTargetLaurent e v mapCoeffs H

@[simp]
theorem mapLaurentSeries_laurentSeriesBasis_apply {R S : Type*} [CommRing R]
    [CommRing S] (e : ℕ) [NeZero e] (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) (mapCoeffs : R →+* S) (i : Fin e) :
    mapLaurentSeries mapCoeffs (laurentSeriesBasis e v hv i) =
      laurentSeriesBasis e (PowerSeries.map mapCoeffs v) (hv.map mapCoeffs) i := by
  rw [laurentSeriesBasis_apply, laurentSeriesBasis_apply,
    mapLaurentSeries_algebraMap]
  congr 1
  simp

/-- Laurent-series basis coordinates commute with coefficient
specialization. -/
theorem map_laurentSeriesBasis_repr {R S : Type*} [CommRing R] [CommRing S]
    (e : ℕ) [NeZero e] (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) (mapCoeffs : R →+* S)
    (f : LaurentSeries R) (i : Fin e) :
    (laurentSeriesBasis e (PowerSeries.map mapCoeffs v) (hv.map mapCoeffs)).repr
        (mapLaurentSeries mapCoeffs f) i =
      mapLaurentScalars e v hv mapCoeffs ((laurentSeriesBasis e v hv).repr f i) := by
  let bR := laurentSeriesBasis e v hv
  let bS := laurentSeriesBasis e (PowerSeries.map mapCoeffs v) (hv.map mapCoeffs)
  have hscalar (a : LaurentScalars R e v hv) :
      mapLaurentSeries mapCoeffs
          (algebraMap (LaurentScalars R e v hv) (LaurentSeries R) a) =
        algebraMap
          (LaurentScalars S e (PowerSeries.map mapCoeffs v) (hv.map mapCoeffs))
          (LaurentSeries S) (mapLaurentScalars e v hv mapCoeffs a) := by
    exact DFunLike.congr_fun (mapLaurentSeries_comp_algebraMap e v hv mapCoeffs) a
  have hbasis (j : Fin e) : mapLaurentSeries mapCoeffs (bR j) = bS j := by
    exact mapLaurentSeries_laurentSeriesBasis_apply e v hv mapCoeffs j
  have hsum := bR.sum_repr f
  have hmapped := congrArg (mapLaurentSeries mapCoeffs) hsum
  simp only [map_sum, Algebra.smul_def, map_mul, hscalar, hbasis] at hmapped
  change bS.repr (mapLaurentSeries mapCoeffs f) i =
    mapLaurentScalars e v hv mapCoeffs (bR.repr f i)
  rw [← hmapped]
  simp only [← Algebra.smul_def, map_sum, LinearEquiv.map_smul,
    Module.Basis.repr_self]
  let g : Fin e →₀
      LaurentScalars S e (PowerSeries.map mapCoeffs v) (hv.map mapCoeffs) :=
    Finsupp.mapRange (mapLaurentScalars e v hv mapCoeffs) (map_zero _)
      (bR.repr f)
  have hi := DFunLike.congr_fun (Finsupp.univ_sum_single g) i
  simpa only [g, Finsupp.mapRange_apply, Finsupp.smul_single, smul_eq_mul,
    mul_one] using hi

/-- The matrix of multiplication by a Laurent series in the localized
basis. -/
noncomputable def laurentMultiplicationMatrix {R : Type*} [CommRing R] (e : ℕ)
    [NeZero e] (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v))
    (f : LaurentSeries R) : Matrix (Fin e) (Fin e) (LaurentScalars R e v hv) :=
  Algebra.leftMulMatrix (laurentSeriesBasis e v hv) f

/-- Laurent multiplication matrices commute entrywise with arbitrary
coefficient specialization. -/
theorem map_laurentMultiplicationMatrix {R S : Type*} [CommRing R] [CommRing S]
    (e : ℕ) [NeZero e] (v : PowerSeries R)
    (hv : IsUnit (PowerSeries.constantCoeff v)) (mapCoeffs : R →+* S)
    (f : LaurentSeries R) :
    (laurentMultiplicationMatrix e v hv f).map
        (mapLaurentScalars e v hv mapCoeffs) =
      laurentMultiplicationMatrix e (PowerSeries.map mapCoeffs v) (hv.map mapCoeffs)
        (mapLaurentSeries mapCoeffs f) := by
  ext i j
  simp only [Matrix.map_apply, laurentMultiplicationMatrix,
    Algebra.leftMulMatrix_eq_repr_mul]
  symm
  calc
    _ = (laurentSeriesBasis e (PowerSeries.map mapCoeffs v) (hv.map mapCoeffs)).repr
        (mapLaurentSeries mapCoeffs
          (f * laurentSeriesBasis e v hv j)) i := by
      apply congrArg (fun x ↦
        (laurentSeriesBasis e (PowerSeries.map mapCoeffs v)
          (hv.map mapCoeffs)).repr x i)
      rw [map_mul, mapLaurentSeries_laurentSeriesBasis_apply]
    _ = _ := map_laurentSeriesBasis_repr e v hv mapCoeffs
      (f * laurentSeriesBasis e v hv j) i




end FreeBasis

/-- Appendix B, Lemma B.2: under `s ↦ X^e v`, power series and Laurent
series are free on `1, X, …, X^(e-1)` over their respective source
scalar rings.  The specialization assertions are the theorems
`FreeBasis.map_coordinates`, `FreeBasis.map_powerMultiplicationMatrix`,
`FreeBasis.map_laurentSeriesBasis_repr`, and
`FreeBasis.map_laurentMultiplicationMatrix` above. -/
theorem freeBasis {R : Type*} [CommRing R] (e : ℕ) [NeZero e]
    (v : PowerSeries R) (hv : IsUnit (PowerSeries.constantCoeff v)) :
    (∃ b : Module.Basis (Fin e) (FreeBasis.PowerScalars R e v) (PowerSeries R),
      ∀ i, b i = PowerSeries.X ^ (i : ℕ)) ∧
    (∃ b : Module.Basis (Fin e) (FreeBasis.LaurentScalars R e v hv)
        (LaurentSeries R),
      ∀ i, b i = algebraMap (PowerSeries R) (LaurentSeries R)
        (PowerSeries.X ^ (i : ℕ))) := by
  exact ⟨⟨FreeBasis.powerSeriesBasis e v hv,
      FreeBasis.powerSeriesBasis_apply e v hv⟩,
    ⟨FreeBasis.laurentSeriesBasis e v hv,
      FreeBasis.laurentSeriesBasis_apply e v hv⟩⟩

end

end LanglandsSecondMainLemma.Residues
