import Mathlib

/-!
# Formal Laurent residues and substitution

This file proves Lemma B.1 of the corrected SML manuscript. A positive-order
power series defines a substitution homomorphism on Laurent series. Pulling
back the differential H(s) ds along a series of exact order e multiplies its
residue by e. The proof of the negative monomial case is first carried out
over an integral universal coefficient ring, so it remains valid when the
characteristic divides an exponent.
-/

open scoped PowerSeries LaurentSeries
open HahnSeries

namespace LanglandsSecondMainLemma.Residues

noncomputable section

variable {R : Type*} [CommRing R]

private lemma derivative_units_zpow (v : R⟦X⟧ˣ) (n : ℤ) :
    PowerSeries.derivative R (↑(v ^ n) : R⟦X⟧) =
      PowerSeries.C (n : R) *
        ((↑(v ^ (n - 1)) : R⟦X⟧) * PowerSeries.derivative R (v : R⟦X⟧)) := by
  cases n with
  | ofNat n =>
      cases n with
      | zero => simp
      | succ n =>
          simp only [Int.ofNat_eq_natCast, zpow_natCast]
          have hexp : (↑(n + 1) : ℤ) - 1 = (n : ℤ) := by omega
          rw [hexp, zpow_natCast]
          simp only [Units.val_pow_eq_pow_val, PowerSeries.derivative_pow]
          simp only [Nat.add_sub_cancel, PowerSeries.C_eq_algebraMap, Int.cast_natCast]
          rw [map_natCast]
          ring
  | negSucc n =>
      change PowerSeries.derivative R (↑((v⁻¹) ^ (n + 1)) : R⟦X⟧) =
        PowerSeries.C (Int.negSucc n : R) *
          ((↑((v⁻¹) ^ (n + 2)) : R⟦X⟧) * PowerSeries.derivative R (v : R⟦X⟧))
      simp only [Units.val_pow_eq_pow_val, PowerSeries.derivative_pow,
        PowerSeries.derivative_inv]
      rw [Nat.add_sub_cancel]
      rw [pow_succ' (↑v⁻¹ : R⟦X⟧) (n + 1),
        pow_succ' (↑v⁻¹ : R⟦X⟧) n]
      simp only [Int.cast_negSucc, map_neg, map_add, map_one,
        Nat.cast_add, Nat.cast_one, map_natCast]
      ring

private lemma integral_negative_coefficient [IsDomain R] [CharZero R]
    (v : R⟦X⟧ˣ) (e q : ℕ) (he : 0 < e) (hq : 0 < q) :
    (e : R) * PowerSeries.coeff (e * q) (↑(v ^ (-(q : ℤ))) : R⟦X⟧) +
        PowerSeries.coeff (e * q - 1)
          ((↑(v ^ (-(q + 1 : ℕ) : ℤ)) : R⟦X⟧) *
            PowerSeries.derivative R (v : R⟦X⟧)) = 0 := by
  let B := PowerSeries.coeff (e * q) (↑(v ^ (-(q : ℤ))) : R⟦X⟧)
  let A := PowerSeries.coeff (e * q - 1)
    ((↑(v ^ (-(q + 1 : ℕ) : ℤ)) : R⟦X⟧) *
      PowerSeries.derivative R (v : R⟦X⟧))
  have hN : 0 < e * q := Nat.mul_pos he hq
  have hderiv := congrArg (PowerSeries.coeff (e * q - 1))
    (derivative_units_zpow v (-(q : ℤ)))
  have hindex : e * q - 1 + 1 = e * q := Nat.sub_add_cancel hN
  have hexponent : -(q : ℤ) - 1 = -(q + 1 : ℕ) := by omega
  have hcast : ((e * q - 1 : ℕ) : R) + 1 = (e * q : R) := by
    exact_mod_cast hindex
  have heq : (e * q : R) * B = -(q : R) * A := by
    simp only [PowerSeries.coeff_derivative, hindex, PowerSeries.coeff_C_mul,
      Int.cast_neg, Int.cast_natCast, hexponent] at hderiv
    rw [hcast] at hderiv
    simpa only [B, A, Nat.cast_mul, mul_comm] using hderiv
  have hqR : (q : R) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  apply (mul_eq_zero.mp ?_).resolve_left hqR
  calc
    (q : R) * ((e : R) * B + A) = (e * q : R) * B + (q : R) * A := by
      ring
    _ = 0 := by rw [heq]; ring

private lemma map_derivative {S : Type*} [CommRing S] (f : R →+* S) (p : R⟦X⟧) :
    PowerSeries.map f (PowerSeries.derivative R p) =
      PowerSeries.derivative S (PowerSeries.map f p) := by
  ext n
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_derivative, map_mul, map_add,
    map_natCast, map_one]

private abbrev UniversalCoefficients := MvPolynomial ℕ ℤ

private def universalUnitSeries : UniversalCoefficients⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 1 else MvPolynomial.X n

@[simp] private lemma coeff_universalUnitSeries (n : ℕ) :
    PowerSeries.coeff n universalUnitSeries =
      if n = 0 then 1 else MvPolynomial.X n := by
  simp [universalUnitSeries]

private lemma universalUnitSeries_isUnit : IsUnit universalUnitSeries := by
  rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff]
  simp

private noncomputable def universalUnit : UniversalCoefficients⟦X⟧ˣ :=
  universalUnitSeries_isUnit.unit

@[simp] private lemma coe_universalUnit : (universalUnit : UniversalCoefficients⟦X⟧) =
    universalUnitSeries := universalUnitSeries_isUnit.unit_spec

private def universalEval {k : Type*} [Field k] (v : k⟦X⟧) :
    UniversalCoefficients →+* k :=
  MvPolynomial.eval₂Hom (Int.castRingHom k) fun n => PowerSeries.coeff n v

private lemma map_universalUnitSeries {k : Type*} [Field k] (v : k⟦X⟧)
    (hv : PowerSeries.constantCoeff v = 1) :
    PowerSeries.map (universalEval v) universalUnitSeries = v := by
  ext n
  cases n with
  | zero => simpa [universalEval] using hv.symm
  | succ n => simp [universalEval]

private lemma negative_coefficient_of_constantCoeff_one {k : Type*} [Field k]
    (v : k⟦X⟧ˣ) (hv : PowerSeries.constantCoeff (v : k⟦X⟧) = 1)
    (e q : ℕ) (he : 0 < e) (hq : 0 < q) :
    (e : k) * PowerSeries.coeff (e * q) (↑(v ^ (-(q : ℤ))) : k⟦X⟧) +
        PowerSeries.coeff (e * q - 1)
          ((↑(v ^ (-(q + 1 : ℕ) : ℤ)) : k⟦X⟧) *
            PowerSeries.derivative k (v : k⟦X⟧)) = 0 := by
  let f := universalEval (v : k⟦X⟧)
  let V := universalUnit
  have hVval : PowerSeries.map f (V : UniversalCoefficients⟦X⟧) = (v : k⟦X⟧) := by
    simpa [f, V] using map_universalUnitSeries (v : k⟦X⟧) hv
  have hV : Units.map (PowerSeries.map f).toMonoidHom V = v := by
    apply Units.ext
    exact hVval
  have hpow (n : ℤ) :
      PowerSeries.map f (↑(V ^ n) : UniversalCoefficients⟦X⟧) =
        (↑(v ^ n) : k⟦X⟧) := by
    calc
      _ = (↑(Units.map (PowerSeries.map f).toMonoidHom (V ^ n)) : k⟦X⟧) :=
        (Units.coe_map _ _).symm
      _ = (↑((Units.map (PowerSeries.map f).toMonoidHom V) ^ n) : k⟦X⟧) := by
        rw [map_zpow]
      _ = _ := by rw [hV]
  have h := integral_negative_coefficient V e q he hq
  have hmapped := congrArg f h
  simp only [map_add, map_mul, map_natCast, map_zero] at hmapped
  rw [← PowerSeries.coeff_map, hpow, ← PowerSeries.coeff_map, map_mul,
    hpow, map_derivative, hVval] at hmapped
  exact hmapped

private lemma negative_coefficient_of_unit {k : Type*} [Field k]
    (v : k⟦X⟧ˣ) (e q : ℕ) (he : 0 < e) (hq : 0 < q) :
    (e : k) * PowerSeries.coeff (e * q) (↑(v ^ (-(q : ℤ))) : k⟦X⟧) +
        PowerSeries.coeff (e * q - 1)
          ((↑(v ^ (-(q + 1 : ℕ) : ℤ)) : k⟦X⟧) *
            PowerSeries.derivative k (v : k⟦X⟧)) = 0 := by
  let a : k := PowerSeries.constantCoeff (v : k⟦X⟧)
  have ha : a ≠ 0 := by
    have hv : IsUnit (PowerSeries.constantCoeff (v : k⟦X⟧)) :=
      PowerSeries.isUnit_iff_constantCoeff.mp v.isUnit
    simpa [a, isUnit_iff_ne_zero] using hv
  let ca : k⟦X⟧ˣ := Units.map PowerSeries.C.toMonoidHom (Units.mk0 a ha)
  let w : k⟦X⟧ˣ := ca⁻¹ * v
  have hw : PowerSeries.constantCoeff (w : k⟦X⟧) = 1 := by
    simp [w, ca, a, ha]
  have hvw : v = ca * w := by
    simp [w]
  have hca (n : ℤ) : (↑(ca ^ n) : k⟦X⟧) = PowerSeries.C (a ^ n) := by
    change (↑((Units.map PowerSeries.C.toMonoidHom (Units.mk0 a ha)) ^ n) : k⟦X⟧) = _
    rw [← map_zpow, Units.coe_map]
    simp
  have hpow (n : ℤ) :
      (↑(v ^ n) : k⟦X⟧) = PowerSeries.C (a ^ n) * (↑(w ^ n) : k⟦X⟧) := by
    rw [hvw, mul_zpow]
    simp only [Units.val_mul, hca]
  have hderiv : PowerSeries.derivative k (v : k⟦X⟧) =
      PowerSeries.C a * PowerSeries.derivative k (w : k⟦X⟧) := by
    rw [hvw]
    simp only [Units.val_mul]
    have hcaval : (ca : k⟦X⟧) = PowerSeries.C a := by
      simpa using hca 1
    rw [hcaval]
    simp
  have h := negative_coefficient_of_constantCoeff_one w hw e q he hq
  rw [hpow, hpow, hderiv] at ⊢
  simp only [PowerSeries.coeff_C_mul, mul_assoc]
  have hprod :
      (↑(w ^ (-(q + 1 : ℕ) : ℤ)) : k⟦X⟧) *
          (PowerSeries.C a * PowerSeries.derivative k (w : k⟦X⟧)) =
        PowerSeries.C a *
          ((↑(w ^ (-(q + 1 : ℕ) : ℤ)) : k⟦X⟧) *
            PowerSeries.derivative k (w : k⟦X⟧)) := by ring
  rw [hprod, PowerSeries.coeff_C_mul]
  have haexp : a ^ (-(q + 1 : ℕ) : ℤ) * a = a ^ (-(q : ℤ)) := by
    calc
      a ^ (-(q + 1 : ℕ) : ℤ) * a =
          a ^ (-(q + 1 : ℕ) : ℤ) * a ^ (1 : ℤ) := by rw [zpow_one]
      _ = a ^ ((-(q + 1 : ℕ) : ℤ) + 1) :=
        (zpow_add₀ ha (-(q + 1 : ℕ) : ℤ) 1).symm
      _ = a ^ (-(q : ℤ)) := by congr 1; omega
  rw [← mul_assoc (a ^ (-(q + 1 : ℕ) : ℤ)) a, haexp]
  calc
    (e : k) * (a ^ (-(q : ℤ)) *
        PowerSeries.coeff (e * q) (↑(w ^ (-(q : ℤ))) : k⟦X⟧)) +
        a ^ (-(q : ℤ)) * PowerSeries.coeff (e * q - 1)
          ((↑(w ^ (-(q + 1 : ℕ) : ℤ)) : k⟦X⟧) *
            PowerSeries.derivative k (w : k⟦X⟧)) =
      a ^ (-(q : ℤ)) *
        ((e : k) * PowerSeries.coeff (e * q) (↑(w ^ (-(q : ℤ))) : k⟦X⟧) +
          PowerSeries.coeff (e * q - 1)
            ((↑(w ^ (-(q + 1 : ℕ) : ℤ)) : k⟦X⟧) *
              PowerSeries.derivative k (w : k⟦X⟧))) := by ring
    _ = 0 := by rw [h, mul_zero]

private lemma coe_units_zpow {k : Type*} [Field k] (v : k⟦X⟧ˣ) (n : ℤ) :
    (((v : k⟦X⟧) : k⸨X⸩) ^ n) =
      ((↑(v ^ n) : k⟦X⟧) : k⸨X⸩) := by
  cases n with
  | ofNat n => simp [zpow_natCast, Units.val_pow_eq_pow_val]
  | negSucc n =>
      simp only [zpow_negSucc]
      have hinv (w : k⟦X⟧ˣ) :
          (HahnSeries.ofPowerSeries ℤ k) (↑w⁻¹ : k⟦X⟧) =
            ((HahnSeries.ofPowerSeries ℤ k) (w : k⟦X⟧))⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← map_mul]
        simp
      rw [hinv]
      have hvpow : (↑(v ^ (n + 1)) : k⟦X⟧) = (v : k⟦X⟧) ^ (n + 1) :=
        Units.val_pow_eq_pow_val v (n + 1)
      rw [hvpow, map_pow]

abbrev FormalDifferential (k : Type*) [Field k] := k⸨X⸩

def residue {k : Type*} [Field k] (ω : FormalDifferential k) : k :=
  ω.coeff (-1)

@[simp] private lemma residue_add {k : Type*} [Field k]
    (ω η : FormalDifferential k) : residue (ω + η) = residue ω + residue η := by
  simp [residue]

private lemma residue_single_neg_mul_coe {k : Type*} [Field k] (p : k⟦X⟧)
    (m : ℕ) (hm : 0 < m) :
    residue (HahnSeries.single (-(m : ℤ)) 1 * (p : k⸨X⸩)) =
      PowerSeries.coeff (m - 1) p := by
  unfold residue
  rw [show (-1 : ℤ) = ((m - 1 : ℕ) : ℤ) + -(m : ℤ) by omega]
  rw [HahnSeries.coeff_single_mul_add]
  simp

private lemma residue_single_neg_mul_coe' {k : Type*} [Field k] (p : k⟦X⟧)
    (r : k) (m : ℕ) (hm : 0 < m) :
    residue (HahnSeries.single (-(m : ℤ)) r * (p : k⸨X⸩)) =
      r * PowerSeries.coeff (m - 1) p := by
  unfold residue
  rw [show (-1 : ℤ) = ((m - 1 : ℕ) : ℤ) + -(m : ℤ) by omega]
  rw [HahnSeries.coeff_single_mul_add]
  simp

private lemma single_one_zpow {k : Type*} [Field k] (e n : ℤ) :
    (HahnSeries.single e (1 : k) : k⸨X⸩) ^ n =
      HahnSeries.single (e * n) 1 := by
  calc
    (HahnSeries.single e (1 : k) : k⸨X⸩) ^ n =
        ((HahnSeries.single 1 1 : k⸨X⸩) ^ e) ^ n := by
          rw [RatFunc.single_zpow]
    _ = (HahnSeries.single 1 1 : k⸨X⸩) ^ (e * n) :=
      (zpow_mul _ e n).symm
    _ = HahnSeries.single (e * n) 1 := (RatFunc.single_zpow _).symm

private lemma residue_factored_negative_pos {k : Type*} [Field k]
    (v : k⟦X⟧ˣ) (e q : ℕ) (he : 0 < e) (hq : 0 < q) :
    residue
        (((HahnSeries.single (e : ℤ) 1 * ((v : k⟦X⟧) : k⸨X⸩)) ^
            (-(q + 1 : ℕ) : ℤ)) *
          ((PowerSeries.C (e : k) * PowerSeries.X ^ (e - 1) * (v : k⟦X⟧) +
              PowerSeries.X ^ e * PowerSeries.derivative k (v : k⟦X⟧) :
            k⟦X⟧) : k⸨X⸩)) = 0 := by
  have hvmul :
      (↑(v ^ (-(q + 1 : ℕ) : ℤ)) : k⟦X⟧) * (v : k⟦X⟧) =
        (↑(v ^ (-(q : ℤ))) : k⟦X⟧) := by
    have hvunits : v ^ (-(q + 1 : ℕ) : ℤ) * v = v ^ (-(q : ℤ)) := by
      calc
        v ^ (-(q + 1 : ℕ) : ℤ) * v =
            v ^ (-(q + 1 : ℕ) : ℤ) * v ^ (1 : ℤ) := by rw [zpow_one]
        _ = v ^ ((-(q + 1 : ℕ) : ℤ) + 1) := by rw [zpow_add]
        _ = v ^ (-(q : ℤ)) := by congr 1; omega
    exact congrArg Units.val hvunits
  have hecast : ((e - 1 : ℕ) : ℤ) = (e : ℤ) - 1 := by omega
  have hexp1 :
      (e : ℤ) * (-(q + 1 : ℕ) : ℤ) + 0 + (e - 1 : ℕ) =
        -((e * q + 1 : ℕ) : ℤ) := by
    push_cast
    rw [hecast]
    ring
  have hexp2 :
      (e : ℤ) * (-(q + 1 : ℕ) : ℤ) + (e : ℤ) =
        -((e * q : ℕ) : ℤ) := by
    push_cast
    ring
  rw [mul_zpow, single_one_zpow, coe_units_zpow]
  simp only [PowerSeries.coe_add, PowerSeries.coe_mul, PowerSeries.coe_C,
    PowerSeries.coe_pow, PowerSeries.coe_X]
  rw [mul_add]
  have hfirst :
      HahnSeries.single ((e : ℤ) * (-(q + 1 : ℕ) : ℤ)) (1 : k) *
          ((↑(v ^ (-(q + 1 : ℕ) : ℤ)) : k⟦X⟧) : k⸨X⸩) *
          (HahnSeries.C (e : k) * (HahnSeries.single 1 1 : k⸨X⸩) ^ (e - 1) *
            (((v : k⟦X⟧) : k⸨X⸩))) =
        HahnSeries.single (-((e * q + 1 : ℕ) : ℤ)) (e : k) *
          ((↑(v ^ (-(q : ℤ))) : k⟦X⟧) : k⸨X⸩) := by
    calc
      _ = (HahnSeries.single ((e : ℤ) * (-(q + 1 : ℕ) : ℤ)) (1 : k) *
            HahnSeries.C (e : k) * (HahnSeries.single 1 1 : k⸨X⸩) ^ (e - 1)) *
          ((((↑(v ^ (-(q + 1 : ℕ) : ℤ)) : k⟦X⟧) : k⸨X⸩)) *
            (((v : k⟦X⟧) : k⸨X⸩))) := by ring
      _ = HahnSeries.single
            ((e : ℤ) * (-(q + 1 : ℕ) : ℤ) + 0 + (e - 1 : ℕ)) (e : k) *
          ((((↑(v ^ (-(q + 1 : ℕ) : ℤ)) : k⟦X⟧) : k⸨X⸩)) *
            (((v : k⟦X⟧) : k⸨X⸩))) := by
              rw [HahnSeries.C_apply, HahnSeries.single_pow]
              simp only [nsmul_eq_mul, mul_one, one_pow,
                HahnSeries.single_mul_single]
              ring_nf
      _ = _ := by
        rw [hexp1, ← PowerSeries.coe_mul, hvmul]
  have hsecond :
      HahnSeries.single ((e : ℤ) * (-(q + 1 : ℕ) : ℤ)) (1 : k) *
          ((↑(v ^ (-(q + 1 : ℕ) : ℤ)) : k⟦X⟧) : k⸨X⸩) *
          ((HahnSeries.single 1 1 : k⸨X⸩) ^ e *
            ((PowerSeries.derivative k (v : k⟦X⟧) : k⟦X⟧) : k⸨X⸩)) =
        HahnSeries.single (-((e * q : ℕ) : ℤ)) 1 *
          (((↑(v ^ (-(q + 1 : ℕ) : ℤ)) : k⟦X⟧) *
            PowerSeries.derivative k (v : k⟦X⟧) : k⟦X⟧) : k⸨X⸩) := by
    calc
      _ = (HahnSeries.single ((e : ℤ) * (-(q + 1 : ℕ) : ℤ)) (1 : k) *
            (HahnSeries.single 1 1 : k⸨X⸩) ^ e) *
          ((((↑(v ^ (-(q + 1 : ℕ) : ℤ)) : k⟦X⟧) : k⸨X⸩)) *
            ((PowerSeries.derivative k (v : k⟦X⟧) : k⟦X⟧) : k⸨X⸩)) := by ring
      _ = HahnSeries.single
            ((e : ℤ) * (-(q + 1 : ℕ) : ℤ) + (e : ℤ)) 1 *
          ((((↑(v ^ (-(q + 1 : ℕ) : ℤ)) : k⟦X⟧) : k⸨X⸩)) *
            ((PowerSeries.derivative k (v : k⟦X⟧) : k⟦X⟧) : k⸨X⸩)) := by
              rw [HahnSeries.single_pow]
              simp only [nsmul_eq_mul, mul_one, one_pow,
                HahnSeries.single_mul_single]
      _ = _ := by
        rw [hexp2, ← PowerSeries.coe_mul]
  rw [hfirst, hsecond, residue_add, residue_single_neg_mul_coe',
    residue_single_neg_mul_coe]
  · exact negative_coefficient_of_unit v e q he hq
  · exact Nat.mul_pos he hq
  · omega

private lemma residue_factored_minus_one {k : Type*} [Field k]
    (v : k⟦X⟧ˣ) (e : ℕ) (he : 0 < e) :
    residue
        (((HahnSeries.single (e : ℤ) 1 * ((v : k⟦X⟧) : k⸨X⸩)) ^ (-1 : ℤ)) *
          ((PowerSeries.C (e : k) * PowerSeries.X ^ (e - 1) * (v : k⟦X⟧) +
              PowerSeries.X ^ e * PowerSeries.derivative k (v : k⟦X⟧) :
            k⟦X⟧) : k⸨X⸩)) = (e : k) := by
  have hvmul :
      (↑(v ^ (-1 : ℤ)) : k⟦X⟧) * (v : k⟦X⟧) = 1 := by
    have hvunits : v ^ (-1 : ℤ) * v = 1 := by simp
    exact congrArg Units.val hvunits
  have hecast : ((e - 1 : ℕ) : ℤ) = (e : ℤ) - 1 := by omega
  have hexp1 : (e : ℤ) * (-1) + 0 + (e - 1 : ℕ) = -1 := by
    rw [hecast]
    ring
  have hexp2 : (e : ℤ) * (-1) + (e : ℤ) = 0 := by ring
  rw [mul_zpow, single_one_zpow, coe_units_zpow]
  simp only [PowerSeries.coe_add, PowerSeries.coe_mul, PowerSeries.coe_C,
    PowerSeries.coe_pow, PowerSeries.coe_X]
  rw [mul_add]
  have hfirst :
      HahnSeries.single ((e : ℤ) * (-1)) (1 : k) *
          ((↑(v ^ (-1 : ℤ)) : k⟦X⟧) : k⸨X⸩) *
          (HahnSeries.C (e : k) * (HahnSeries.single 1 1 : k⸨X⸩) ^ (e - 1) *
            (((v : k⟦X⟧) : k⸨X⸩))) =
        HahnSeries.single (-1 : ℤ) (e : k) := by
    calc
      _ = (HahnSeries.single ((e : ℤ) * (-1)) (1 : k) *
            HahnSeries.C (e : k) * (HahnSeries.single 1 1 : k⸨X⸩) ^ (e - 1)) *
          ((((↑(v ^ (-1 : ℤ)) : k⟦X⟧) : k⸨X⸩)) *
            (((v : k⟦X⟧) : k⸨X⸩))) := by ring
      _ = HahnSeries.single ((e : ℤ) * (-1) + 0 + (e - 1 : ℕ)) (e : k) *
          ((((↑(v ^ (-1 : ℤ)) : k⟦X⟧) : k⸨X⸩)) *
            (((v : k⟦X⟧) : k⸨X⸩))) := by
              rw [HahnSeries.C_apply, HahnSeries.single_pow]
              simp only [nsmul_eq_mul, mul_one, one_pow,
                HahnSeries.single_mul_single]
              ring_nf
      _ = _ := by
        rw [hexp1, ← PowerSeries.coe_mul, hvmul, map_one, mul_one]
  have hsecond :
      HahnSeries.single ((e : ℤ) * (-1)) (1 : k) *
          ((↑(v ^ (-1 : ℤ)) : k⟦X⟧) : k⸨X⸩) *
          ((HahnSeries.single 1 1 : k⸨X⸩) ^ e *
            ((PowerSeries.derivative k (v : k⟦X⟧) : k⟦X⟧) : k⸨X⸩)) =
        (((↑(v ^ (-1 : ℤ)) : k⟦X⟧) *
          PowerSeries.derivative k (v : k⟦X⟧) : k⟦X⟧) : k⸨X⸩) := by
    calc
      _ = (HahnSeries.single ((e : ℤ) * (-1)) (1 : k) *
            (HahnSeries.single 1 1 : k⸨X⸩) ^ e) *
          ((((↑(v ^ (-1 : ℤ)) : k⟦X⟧) : k⸨X⸩)) *
            ((PowerSeries.derivative k (v : k⟦X⟧) : k⟦X⟧) : k⸨X⸩)) := by ring
      _ = HahnSeries.single ((e : ℤ) * (-1) + (e : ℤ)) 1 *
          ((((↑(v ^ (-1 : ℤ)) : k⟦X⟧) : k⸨X⸩)) *
            ((PowerSeries.derivative k (v : k⟦X⟧) : k⟦X⟧) : k⸨X⸩)) := by
              rw [HahnSeries.single_pow]
              simp only [nsmul_eq_mul, mul_one, one_pow,
                HahnSeries.single_mul_single]
      _ = _ := by
        rw [hexp2, ← PowerSeries.coe_mul]
        simp
  rw [hfirst, hsecond, residue_add]
  simp only [residue, HahnSeries.coeff_single, PowerSeries.coeff_coe]
  norm_num

private lemma monomial_residue {k : Type*} [Field k] (u : k⟦X⟧) (e : ℕ)
    (he : 0 < e) (hu : u.order = e) (n : ℤ) :
    residue (((u : k⸨X⸩) ^ n) *
        (PowerSeries.derivative k u : k⸨X⸩)) =
      (e : k) * residue (HahnSeries.single n 1) := by
  have hune : u ≠ 0 := by
    intro hzero
    have htop : u.order = ⊤ := PowerSeries.order_eq_top.mpr hzero
    rw [hu] at htop
    exact ENat.coe_ne_top e htop
  have horderNat : u.order.toNat = e := by rw [hu]; simp
  have hvIsUnit : IsUnit u.divXPowOrder := by
    rw [PowerSeries.isUnit_iff_constantCoeff,
      PowerSeries.constantCoeff_divXPowOrder, isUnit_iff_ne_zero]
    exact PowerSeries.coeff_order hune
  let v : k⟦X⟧ˣ := hvIsUnit.unit
  have hv : (v : k⟦X⟧) = u.divXPowOrder := hvIsUnit.unit_spec
  have hfactor : PowerSeries.X ^ e * (v : k⟦X⟧) = u := by
    rw [hv, ← horderNat]
    exact PowerSeries.X_pow_order_mul_divXPowOrder
  have hfactorLaurent : (u : k⸨X⸩) =
      HahnSeries.single (e : ℤ) 1 * ((v : k⟦X⟧) : k⸨X⸩) := by
    rw [← hfactor, PowerSeries.coe_mul, PowerSeries.coe_pow, PowerSeries.coe_X,
      HahnSeries.single_pow]
    simp
  have hderiv : PowerSeries.derivative k u =
      PowerSeries.C (e : k) * PowerSeries.X ^ (e - 1) * (v : k⟦X⟧) +
        PowerSeries.X ^ e * PowerSeries.derivative k (v : k⟦X⟧) := by
    rw [← hfactor]
    rw [Derivation.leibniz, PowerSeries.derivative_pow, PowerSeries.derivative_X]
    simp
    ring
  cases n with
  | ofNat n =>
      change residue (((u : k⸨X⸩) ^ n) *
          (PowerSeries.derivative k u : k⸨X⸩)) =
        (e : k) * residue (HahnSeries.single (n : ℤ) 1)
      rw [← PowerSeries.coe_pow, ← PowerSeries.coe_mul]
      unfold residue
      rw [PowerSeries.coeff_coe, if_pos (by omega),
        HahnSeries.coeff_single, if_neg (by omega)]
      simp
  | negSucc q =>
      cases q with
      | zero =>
          rw [hfactorLaurent, hderiv]
          simpa [residue] using residue_factored_minus_one v e he
      | succ q =>
          rw [hfactorLaurent, hderiv]
          have hn : Int.negSucc (q + 1) = (-(q + 1 + 1 : ℕ) : ℤ) := by omega
          rw [hn, residue_factored_negative_pos v e (q + 1) he (Nat.succ_pos q)]
          symm
          apply mul_eq_zero_of_right
          unfold residue
          rw [HahnSeries.coeff_single, if_neg]
          omega

private def substitutionBaseHom {k : Type*} [Field k] (u : k⟦X⟧)
    (hu : PowerSeries.HasSubst u) : k⟦X⟧ →+* k⸨X⸩ :=
  (HahnSeries.ofPowerSeries ℤ k).comp (PowerSeries.substAlgHom hu).toRingHom

private lemma substitutionBaseHom_isUnit {k : Type*} [Field k] (u : k⟦X⟧)
    (hu : PowerSeries.HasSubst u) (hune : u ≠ 0) :
    ∀ y : Submonoid.powers (PowerSeries.X : k⟦X⟧),
      IsUnit (substitutionBaseHom u hu y) := by
    rintro ⟨_, n, rfl⟩
    change IsUnit ((HahnSeries.ofPowerSeries ℤ k)
      (PowerSeries.substAlgHom hu (PowerSeries.X ^ n)))
    rw [map_pow, PowerSeries.substAlgHom_X]
    rw [map_pow]
    apply IsUnit.pow
    rw [isUnit_iff_ne_zero]
    intro hzero
    apply hune
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa using hzero

private def substitutionHom {k : Type*} [Field k] (u : k⟦X⟧)
    (hu : PowerSeries.HasSubst u) (hune : u ≠ 0) : k⸨X⸩ →+* k⸨X⸩ :=
  IsLocalization.lift (M := Submonoid.powers (PowerSeries.X : k⟦X⟧))
    (substitutionBaseHom_isUnit u hu hune)

private lemma substitutionHom_coe {k : Type*} [Field k] (u : k⟦X⟧)
    (hu : PowerSeries.HasSubst u) (hune : u ≠ 0) (p : k⟦X⟧) :
    substitutionHom u hu hune (p : k⸨X⸩) =
      (PowerSeries.subst u p : k⸨X⸩) := by
  change substitutionHom u hu hune
    ((algebraMap k⟦X⟧ k⸨X⸩) p) = (PowerSeries.subst u p : k⸨X⸩)
  rw [substitutionHom, IsLocalization.lift_eq]
  simp [substitutionBaseHom, PowerSeries.coe_substAlgHom]

private lemma substitutionHom_C {k : Type*} [Field k] (u : k⟦X⟧)
    (hu : PowerSeries.HasSubst u) (hune : u ≠ 0) (a : k) :
    substitutionHom u hu hune (HahnSeries.C a) = HahnSeries.C a := by
  rw [← PowerSeries.coe_C, substitutionHom_coe]
  rw [PowerSeries.subst_C]
  rw [← PowerSeries.C_apply]

private lemma substitutionHom_X {k : Type*} [Field k] (u : k⟦X⟧)
    (hu : PowerSeries.HasSubst u) (hune : u ≠ 0) :
    substitutionHom u hu hune (HahnSeries.single 1 1) = (u : k⸨X⸩) := by
  rw [← PowerSeries.coe_X, substitutionHom_coe]
  exact congrArg (HahnSeries.ofPowerSeries ℤ k) (PowerSeries.subst_X hu)

private lemma substitutionHom_single_one {k : Type*} [Field k] (u : k⟦X⟧)
    (hu : PowerSeries.HasSubst u) (hune : u ≠ 0) (n : ℤ) :
    substitutionHom u hu hune (HahnSeries.single n 1) = (u : k⸨X⸩) ^ n := by
  rw [RatFunc.single_zpow, map_zpow₀, substitutionHom_X]

private lemma substitutionHom_single {k : Type*} [Field k] (u : k⟦X⟧)
    (hu : PowerSeries.HasSubst u) (hune : u ≠ 0) (n : ℤ) (a : k) :
    substitutionHom u hu hune (HahnSeries.single n a) =
      HahnSeries.C a * (u : k⸨X⸩) ^ n := by
  rw [show HahnSeries.single n a = HahnSeries.C a * HahnSeries.single n 1 by
    rw [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]]
  rw [map_mul, substitutionHom_C, substitutionHom_single_one]

private lemma residue_C_mul {k : Type*} [Field k] (a : k) (ω : FormalDifferential k) :
    residue (HahnSeries.C a * ω) = a * residue ω := by
  unfold residue
  rw [HahnSeries.C_apply]
  rw [show (-1 : ℤ) = (-1 : ℤ) + 0 by omega,
    HahnSeries.coeff_single_mul_add]
  simp

private lemma substitution_single_residue {k : Type*} [Field k]
    (u : k⟦X⟧) (e : ℕ) (he : 0 < e) (hu : u.order = e)
    (hs : PowerSeries.HasSubst u) (hune : u ≠ 0) (n : ℤ) (a : k) :
    residue (substitutionHom u hs hune (HahnSeries.single n a) *
        (PowerSeries.derivative k u : k⸨X⸩)) =
      (e : k) * residue (HahnSeries.single n a) := by
  rw [substitutionHom_single, mul_assoc, residue_C_mul,
    monomial_residue u e he hu n]
  unfold residue
  simp only [HahnSeries.coeff_single]
  by_cases hn : (-1 : ℤ) = n
  · subst n
    simp
    ring
  · simp [hn]

private def negativePartFinsupp {k : Type*} [Field k] (H : k⸨X⸩) : ℤ →₀ k :=
  Finsupp.ofSupportFinite ((HahnSeries.truncLT 0 H).coeff) <| by
    refine (Set.finite_Icc H.order (-1)).subset ?_
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn ⊢
    rw [HahnSeries.coeff_truncLT] at hn
    split at hn
    next hneg =>
      refine ⟨HahnSeries.order_le_of_coeff_ne_zero ?_, by omega⟩
      exact fun hzero ↦ hn (by simp [hzero])
    next hnonneg => exact (hn rfl).elim

private lemma ofFinsupp_negativePartFinsupp {k : Type*} [Field k] (H : k⸨X⸩) :
    HahnSeries.ofFinsupp (negativePartFinsupp H) = HahnSeries.truncLT 0 H := by
  ext n
  rw [HahnSeries.coeff_ofFinsupp]
  rfl

private lemma ofFinsupp_eq_sum_single {k : Type*} [Field k] (f : ℤ →₀ k) :
    HahnSeries.ofFinsupp f = f.sum fun n a ↦ HahnSeries.single n a := by
  classical
  ext i
  rw [HahnSeries.coeff_ofFinsupp]
  simp only [Finsupp.sum, HahnSeries.coeff_sum, HahnSeries.coeff_single]
  by_cases hi : i ∈ f.support
  · rw [Finset.sum_eq_single i]
    · simp
    · intro b hb hbi
      split
      next hib => exact (hbi hib.symm).elim
      next => rfl
    · exact fun h ↦ (h hi).elim
  · have hfi : f i = 0 := by
      simpa only [Finsupp.mem_support_iff, not_not] using hi
    rw [hfi]
    symm
    apply Finset.sum_eq_zero
    intro b hb
    split
    next h => exact (hi (h ▸ hb)).elim
    next => rfl

private def nonnegativePart {k : Type*} [Field k] (H : k⸨X⸩) : k⟦X⟧ :=
  PowerSeries.mk fun n ↦ H.coeff n

@[simp] private lemma coeff_nonnegativePart {k : Type*} [Field k] (H : k⸨X⸩) (n : ℕ) :
    PowerSeries.coeff n (nonnegativePart H) = H.coeff n := by
  simp [nonnegativePart]

private lemma negative_add_nonnegativePart {k : Type*} [Field k] (H : k⸨X⸩) :
    HahnSeries.ofFinsupp (negativePartFinsupp H) +
        (nonnegativePart H : k⸨X⸩) = H := by
  rw [ofFinsupp_negativePartFinsupp]
  ext n
  rw [HahnSeries.coeff_add, HahnSeries.coeff_truncLT]
  cases n with
  | ofNat n => simp
  | negSucc n => simp [PowerSeries.coeff_coe]

private lemma substitution_finsupp_residue {k : Type*} [Field k]
    (u : k⟦X⟧) (e : ℕ) (he : 0 < e) (hu : u.order = e)
    (hs : PowerSeries.HasSubst u) (hune : u ≠ 0) (f : ℤ →₀ k) :
    residue (substitutionHom u hs hune (HahnSeries.ofFinsupp f) *
        (PowerSeries.derivative k u : k⸨X⸩)) =
      (e : k) * residue (HahnSeries.ofFinsupp f) := by
  classical
  rw [ofFinsupp_eq_sum_single]
  induction f using Finsupp.induction with
  | zero => simp [residue]
  | single_add n a f hn ha ih =>
      rw [Finsupp.sum_add_index]
      · rw [Finsupp.sum_single_index, map_add, add_mul, residue_add, residue_add,
          substitution_single_residue u e he hu hs hune, ih]
        ring
        simp
      · intro i hi
        simp
      · intro i hi b₁ b₂
        ext i
        simp [HahnSeries.coeff_single]

private lemma substitution_powerSeries_residue_zero {k : Type*} [Field k]
    (u : k⟦X⟧) (hs : PowerSeries.HasSubst u) (hune : u ≠ 0) (p : k⟦X⟧) :
    residue (substitutionHom u hs hune (p : k⸨X⸩) *
        (PowerSeries.derivative k u : k⸨X⸩)) = 0 := by
  rw [substitutionHom_coe, ← PowerSeries.coe_mul]
  unfold residue
  rw [PowerSeries.coeff_coe, if_pos (by omega)]

private lemma powerSeries_ne_zero_of_order_eq {k : Type*} [Field k]
    (u : k⟦X⟧) (e : ℕ) (hu : u.order = e) : u ≠ 0 := by
  intro hzero
  have htop : u.order = ⊤ := PowerSeries.order_eq_top.mpr hzero
  rw [hu] at htop
  exact ENat.coe_ne_top e htop

private lemma hasSubst_of_order_eq {k : Type*} [Field k]
    (u : k⟦X⟧) (e : ℕ) (he : 0 < e) (hu : u.order = e) :
    PowerSeries.HasSubst u := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero'
  apply PowerSeries.one_le_order_iff_constCoeff_eq_zero.mp
  rw [hu]
  exact_mod_cast he

/-- Substitution of a positive-order power series in a Laurent series. -/
def formalSubstitution {k : Type*} [Field k]
    (u : k⟦X⟧) (e : ℕ) (he : 0 < e) (hu : u.order = e) :
    k⸨X⸩ →+* k⸨X⸩ :=
  substitutionHom u (hasSubst_of_order_eq u e he hu)
    (powerSeries_ne_zero_of_order_eq u e hu)

@[simp] lemma formalSubstitution_coe {k : Type*} [Field k]
    (u : k⟦X⟧) (e : ℕ) (he : 0 < e) (hu : u.order = e) (p : k⟦X⟧) :
    formalSubstitution u e he hu (p : k⸨X⸩) =
      (PowerSeries.subst u p : k⸨X⸩) := by
  exact substitutionHom_coe u _ _ p

/-- Formal substitution multiplies Laurent residues by the exact order of the
substituted power series (paper Lemma B.1). -/
theorem substitution {k : Type*} [Field k]
    (u : k⟦X⟧) (e : ℕ) (he : 0 < e) (hu : u.order = e)
    (H : k⸨X⸩) :
    residue (formalSubstitution u e he hu H *
        (PowerSeries.derivative k u : k⸨X⸩)) =
      (e : k) * residue H := by
  let hs := hasSubst_of_order_eq u e he hu
  let hune := powerSeries_ne_zero_of_order_eq u e hu
  let N := HahnSeries.ofFinsupp (negativePartFinsupp H)
  let P := nonnegativePart H
  have hdecomp : N + (P : k⸨X⸩) = H := negative_add_nonnegativePart H
  change residue (substitutionHom u hs hune H *
      (PowerSeries.derivative k u : k⸨X⸩)) = (e : k) * residue H
  rw [← hdecomp, map_add, add_mul, residue_add, residue_add]
  rw [substitution_finsupp_residue u e he hu hs hune,
    substitution_powerSeries_residue_zero u hs hune]
  have hPresidue : residue (P : k⸨X⸩) = 0 := by
    unfold residue
    rw [PowerSeries.coeff_coe, if_pos (by omega)]
  rw [hPresidue]
  ring

/-- A change of uniformizer is the exact-order-one case of formal substitution,
so it preserves residue. -/
theorem change_uniformizer {k : Type*} [Field k]
    (u : k⟦X⟧) (hu : u.order = 1) (H : k⸨X⸩) :
    residue (formalSubstitution u 1 (by omega) hu H *
        (PowerSeries.derivative k u : k⸨X⸩)) = residue H := by
  simpa using substitution u 1 (by omega) hu H

end

end LanglandsSecondMainLemma.Residues
