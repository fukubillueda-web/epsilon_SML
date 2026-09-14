import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.LocalField.Lattices
import LanglandsFirstMainLemma.LocalField.MonogenicUniformizer
import LanglandsFirstMainLemma.LocalField.Valuation
import LanglandsSecondMainLemma.Dyadic.Mixed.UnitSymbol
import LanglandsSecondMainLemma.Local.Newton
import Mathlib.Algebra.CharP.Reduced

open LanglandsFirstMainLemma
open Polynomial

/-!
# Dyadic nonmaximal alignment

This file proves the simultaneous generator and scalar adjustment in
Paper 13.2, `D:NM:alignment`.  The coefficient corrections alternate in
the truncated residue-characteristic-two ring.  At the boundary `a = r`,
the nonunit possibility is excluded using the third quadratic field and
the discriminant bound for an integral generator.
-/

namespace LanglandsSecondMainLemma.Dyadic.Nonmaximal

noncomputable section

private theorem natCast_withTop_eq_intCast (n : ℕ) :
    (n : WithTop ℤ) = ((n : ℤ) : WithTop ℤ) := by
  norm_num

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private theorem exists_depth_correction
    (hchar : residueCharacteristic F = 2)
    (pi A R : F) (n : ℕ)
    (hpi : (ValuativeRel.valuation F).IsUniformizer pi)
    (hA : ord F A = (0 : WithTop ℤ))
    (hR : R ∈ lattice F (n : ℤ)) :
    ∃ c : ringOfIntegers F,
      (R + A * pi ^ n * (c : F) ^ 2 ∈ lattice F ((n + 1 : ℕ) : ℤ)) ∧
      (ord F R = ((n : ℕ) : WithTop ℤ) → ord F (c : F) = 0) := by
  letI : Fintype (ResidueField F) := residueFieldFintype F
  letI : CharP (ResidueField F) 2 := ringChar.of_eq hchar
  have hpin : ord F (pi ^ n) = ((n : ℕ) : WithTop ℤ) := by
    rw [ord_pow, ord_uniformizer F hpi]
    norm_num
  have hscaled : R / pi ^ n ∈ lattice F 0 := by
    rw [div_mem_lattice_iff F (pi ^ n) R (n : ℤ) 0]
    · simpa using hR
    · exact hpin
  have hAint : A ∈ lattice F 0 := by
    rw [mem_lattice, hA]
    norm_num
  let R0 : ringOfIntegers F :=
    ⟨R / pi ^ n, (mem_lattice_zero_iff F).1 hscaled⟩
  let A0 : ringOfIntegers F :=
    ⟨A, (mem_lattice_zero_iff F).1 hAint⟩
  have hAres : residueMap F A0 ≠ 0 := by
    rw [ne_eq, residueMap_eq_zero_iff]
    rw [mem_lattice, hA]
    norm_num
  obtain ⟨cbar, hcbar⟩ :=
    isSquare_of_charTwo' (-(residueMap F R0) / residueMap F A0)
  let c : ringOfIntegers F := teichmuller F cbar
  refine ⟨c, ?_, ?_⟩
  have hred : residueMap F (R0 + A0 * c ^ 2) = 0 := by
    simp only [map_add, map_mul, map_pow, c, residueMap_teichmuller]
    rw [show cbar ^ 2 = -(residueMap F R0) / residueMap F A0 by
      simpa [pow_two] using hcbar.symm]
    field_simp [hAres]
    ring
  have hsmall : (R / pi ^ n) + A * (c : F) ^ 2 ∈ lattice F 1 := by
    exact (residueMap_eq_zero_iff F (R0 + A0 * c ^ 2)).1 hred
  have hquot : (R + A * pi ^ n * (c : F) ^ 2) / pi ^ n ∈ lattice F 1 := by
    convert hsmall using 1
    have hpi0 : pi ≠ 0 := (ord_ne_top_iff F).mp (by rw [ord_uniformizer F hpi]; simp)
    have hp0 : pi ^ n ≠ 0 := pow_ne_zero _ hpi0
    field_simp
  have hdeep := (div_mem_lattice_iff F (pi ^ n)
    (R + A * pi ^ n * (c : F) ^ 2) (n : ℤ) 1 hpin).1 hquot
  simpa [Nat.cast_add] using hdeep
  intro hRexact
  have hR0res : residueMap F R0 ≠ 0 := by
    rw [ne_eq, residueMap_eq_zero_iff, mem_lattice]
    rw [ord_div, hRexact, hpin]
    have hncast : ((n : ℕ) : WithTop ℤ) = ((n : ℤ) : WithTop ℤ) := by norm_num
    rw [hncast]
    rw [← WithTop.LinearOrderedAddCommGroup.coe_sub]
    norm_num
  have hcbar0 : cbar ≠ 0 := by
    intro hc0
    subst cbar
    simp only [zero_mul] at hcbar
    have : residueMap F R0 = 0 := by
      apply neg_eq_zero.mp
      exact (div_eq_zero_iff.mp hcbar).resolve_right hAres
    exact hR0res this
  apply (mem_lattice_and_not_mem_succ_iff F).1
  constructor
  · exact (mem_lattice_zero_iff F).2 c.property
  · intro hcdeep
    have hcres := (residueMap_eq_zero_iff F c).2 hcdeep
    exact hcbar0 (by simpa [c] using hcres)

private theorem exists_alternating_solution
    (hchar : residueCharacteristic F = 2)
    (pi C A U : F) (e a : ℕ)
    (hpi : (ValuativeRel.valuation F).IsUniformizer pi)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (ha : 1 ≤ a) (hae : a ≤ e)
    (hC : ord F C = (0 : WithTop ℤ))
    (hA : ord F A = (0 : WithTop ℤ))
    (hU : ord F U = (0 : WithTop ℤ)) :
    ∃ v w : ringOfIntegers F,
      C + pi * U * (w : F) ^ 2 + A * (v : F) ^ 2 ∈ lattice F (a : ℤ) ∧
      ord F (v : F) = 0 := by
  have H : ∀ n : ℕ, n ≤ a →
      ∃ v w : ringOfIntegers F,
        C + pi * U * (w : F) ^ 2 + A * (v : F) ^ 2 ∈ lattice F (n : ℤ) ∧
        ((n = 0 ∧ v = 0 ∧ w = 0) ∨ (n ≠ 0 ∧ ord F (v : F) = 0)) := by
    intro n hn
    induction n with
    | zero =>
        refine ⟨0, 0, ?_, Or.inl ⟨rfl, rfl, rfl⟩⟩
        rw [mem_lattice]
        simp [hC]
    | succ n ih =>
        obtain ⟨v, w, hR, hv⟩ := ih (by omega)
        have hnlt : n < a := by omega
        by_cases hneven : Even n
        · obtain ⟨k, hk⟩ := hneven
          let R := C + pi * U * (w : F) ^ 2 + A * (v : F) ^ 2
          obtain ⟨c, hcdeep, hcunit⟩ :=
            exists_depth_correction F hchar pi A R n hpi hA hR
          let v' : ringOfIntegers F := v + ⟨pi ^ k * (c : F), by
            rw [← mem_lattice_zero_iff, mem_lattice, ord_mul, ord_pow,
              ord_uniformizer F hpi]
            have hcint : (0 : WithTop ℤ) ≤ ord F (c : F) :=
              (ord_nonneg_iff_mem_integer F _).2 c.property
            norm_num at hcint ⊢
            exact add_nonneg (by norm_num) hcint⟩
          refine ⟨v', w, ?_, Or.inr ⟨by omega, ?_⟩⟩
          · have hcross :
                2 * A * (v : F) * pi ^ k * (c : F) ∈
                  lattice F ((n + 1 : ℕ) : ℤ) := by
              rw [mem_lattice, ord_mul, ord_mul, ord_mul, ord_mul,
                htwo, hA, ord_pow, ord_uniformizer F hpi]
              have hvint : (0 : WithTop ℤ) ≤ ord F (v : F) :=
                (ord_nonneg_iff_mem_integer F _).2 v.property
              have hcint : (0 : WithTop ℤ) ≤ ord F (c : F) :=
                (ord_nonneg_iff_mem_integer F _).2 c.property
              norm_num at hvint hcint ⊢
              calc
                ((n + 1 : ℕ) : WithTop ℤ) ≤ (e : WithTop ℤ) := by
                  exact_mod_cast (show n + 1 ≤ e by omega)
                _ ≤ (e : WithTop ℤ) + ord F (v : F) :=
                  le_add_of_nonneg_right hvint
                _ ≤ (e : WithTop ℤ) + ord F (v : F) + (k : WithTop ℤ) :=
                  le_add_of_nonneg_right (by norm_num)
                _ ≤ (e : WithTop ℤ) + ord F (v : F) + (k : WithTop ℤ) +
                    ord F (c : F) := le_add_of_nonneg_right hcint
            rw [show C + pi * U * (w : F) ^ 2 + A * (v' : F) ^ 2 =
                (R + A * pi ^ n * (c : F) ^ 2) +
                  2 * A * (v : F) * pi ^ k * (c : F) by
              simp only [v', R, Subring.coe_add]
              rw [hk]
              ring]
            exact add_mem_lattice F hcdeep hcross
          · rcases hv with ⟨rfl, rfl, rfl⟩ | hv
            · simp only [v', zero_add]
              have hc0 : ord F (c : F) = 0 := hcunit (by simpa [R] using hC)
              have hk0 : k = 0 := by omega
              subst k
              simpa using hc0
            · have hpipos : (0 : WithTop ℤ) < ord F (pi ^ k * (c : F)) := by
                rw [ord_mul, ord_pow, ord_uniformizer F hpi]
                have hcint : (0 : WithTop ℤ) ≤ ord F (c : F) :=
                  (ord_nonneg_iff_mem_integer F _).2 c.property
                norm_num at hcint ⊢
                have hkpos : 0 < k := by rcases hv with ⟨hn0, -⟩; omega
                exact add_pos_of_pos_of_nonneg (by exact_mod_cast hkpos) hcint
              simp only [v', Subring.coe_add]
              have hordne : ord F (v : F) ≠ ord F (pi ^ k * (c : F)) := by
                rw [hv.2]
                exact ne_of_lt hpipos
              rw [ord_add_eq_min F hordne, hv.2, min_eq_left hpipos.le]
        · have hnodd : Odd n := Nat.not_even_iff_odd.mp hneven
          obtain ⟨k, hk⟩ := hnodd
          let R := C + pi * U * (w : F) ^ 2 + A * (v : F) ^ 2
          obtain ⟨c, hcdeep, _hcunit⟩ :=
            exists_depth_correction F hchar pi U R n hpi hU hR
          let w' : ringOfIntegers F := w + ⟨pi ^ k * (c : F), by
            rw [← mem_lattice_zero_iff, mem_lattice, ord_mul, ord_pow,
              ord_uniformizer F hpi]
            have hcint : (0 : WithTop ℤ) ≤ ord F (c : F) :=
              (ord_nonneg_iff_mem_integer F _).2 c.property
            norm_num at hcint ⊢
            exact add_nonneg (by norm_num) hcint⟩
          refine ⟨v, w', ?_, ?_⟩
          · have hcross :
                2 * pi * U * (w : F) * pi ^ k * (c : F) ∈
                  lattice F ((n + 1 : ℕ) : ℤ) := by
              rw [mem_lattice, ord_mul, ord_mul, ord_mul, ord_mul, ord_mul,
                htwo, ord_uniformizer F hpi, hU, ord_pow, ord_uniformizer F hpi]
              have hwint : (0 : WithTop ℤ) ≤ ord F (w : F) :=
                (ord_nonneg_iff_mem_integer F _).2 w.property
              have hcint : (0 : WithTop ℤ) ≤ ord F (c : F) :=
                (ord_nonneg_iff_mem_integer F _).2 c.property
              norm_num at hwint hcint ⊢
              calc
                ((n + 1 : ℕ) : WithTop ℤ) ≤ (e : WithTop ℤ) := by
                  exact_mod_cast (show n + 1 ≤ e by omega)
                _ ≤ (e : WithTop ℤ) + 1 := le_add_of_nonneg_right (by norm_num)
                _ ≤ (e : WithTop ℤ) + 1 + ord F (w : F) :=
                  le_add_of_nonneg_right hwint
                _ ≤ (e : WithTop ℤ) + 1 + ord F (w : F) + (k : WithTop ℤ) :=
                  le_add_of_nonneg_right (by norm_num)
                _ ≤ (e : WithTop ℤ) + 1 + ord F (w : F) + (k : WithTop ℤ) +
                    ord F (c : F) := le_add_of_nonneg_right hcint
            rw [show C + pi * U * (w' : F) ^ 2 + A * (v : F) ^ 2 =
                (R + U * pi ^ n * (c : F) ^ 2) +
                  2 * pi * U * (w : F) * pi ^ k * (c : F) by
              simp only [w', R, Subring.coe_add]
              rw [hk]
              ring]
            exact add_mem_lattice F hcdeep hcross
          · exact Or.inr ⟨by omega, hv.resolve_left (by rintro ⟨h, -, -⟩; omega) |>.2⟩
  obtain ⟨v, w, hdeep, hv⟩ := H a le_rfl
  exact ⟨v, w, hdeep, (hv.resolve_left (by rintro ⟨h, -, -⟩; omega)).2⟩

section Quadratic

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

variable {L : Type*} [Field L] [Algebra F L]

private theorem adjoin_affine_eq_top
    (x y : L) (c b : F) (hc : c ≠ 0)
    (hy : y = algebraMap F L c * x + algebraMap F L b)
    (hx : Algebra.adjoin F ({x} : Set L) = ⊤) :
    Algebra.adjoin F ({y} : Set L) = ⊤ := by
  rw [← top_le_iff, ← hx]
  apply Algebra.adjoin_le
  rw [Set.singleton_subset_iff]
  let S := Algebra.adjoin F ({y} : Set L)
  have hyS : y ∈ S := Algebra.subset_adjoin (Set.mem_singleton y)
  have hsub : y - algebraMap F L b ∈ S :=
    S.sub_mem hyS (S.algebraMap_mem b)
  have hsmul : c⁻¹ • (y - algebraMap F L b) ∈ S := S.smul_mem hsub c⁻¹
  have heq : c⁻¹ • (y - algebraMap F L b) = x := by
    rw [hy, Algebra.smul_def]
    simp only [add_sub_cancel_right]
    rw [map_inv₀ (algebraMap F L) c]
    field_simp [hc]
  rw [← heq]
  exact hsmul

private theorem quadratic_minpoly
    [Module.Finite F L] [Algebra.IsQuadraticExtension F L]
    (u : L) (A B : F)
    (hu : u ^ 2 + algebraMap F L A * u = algebraMap F L B)
    (hgen : Algebra.adjoin F ({u} : Set L) = ⊤) :
    minpoly F u = X ^ 2 + C A * X - C B := by
  let q : F[X] := X ^ 2 + C A * X - C B
  have hlow : (C B - C A * X : F[X]).degree < (X ^ 2 : F[X]).degree := by
    rw [degree_X_pow]
    exact (degree_sub_le _ _).trans_lt (max_lt
      (degree_C_le.trans_lt (by norm_num))
      ((degree_C_mul_X_le A).trans_lt (by norm_num)))
  have hqform : q = X ^ 2 - (C B - C A * X) := by
    simp only [q]
    ring
  have hqmonic : q.Monic := by
    rw [hqform]
    exact (monic_X_pow 2).sub_of_left hlow
  have hqnat : q.natDegree = 2 := by
    apply natDegree_eq_of_degree_eq_some
    rw [hqform, degree_sub_eq_left_of_degree_lt hlow, degree_X_pow]
  have hqroot : Polynomial.aeval u q = 0 := by
    simp only [q, map_sub, map_add, map_pow, aeval_X, aeval_C, map_mul]
    rw [hu]
    ring
  let pb : PowerBasis F L :=
    PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral u) hgen
  have hpbdim : pb.dim = 2 := by
    rw [← PowerBasis.finrank pb]
    exact Algebra.IsQuadraticExtension.finrank_eq_two F L
  symm
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (Algebra.IsIntegral.isIntegral u)) hqmonic
  · exact minpoly.dvd F u hqroot
  · rw [hqnat,
      show (minpoly F u).natDegree = pb.dim by
        simpa only [pb, PowerBasis.ofAdjoinEqTop_gen] using
          PowerBasis.natDegree_minpoly pb,
      hpbdim]

private theorem quadraticPolynomial_monic
    {R : Type*} [CommRing R] [Nontrivial R] (A B : R) :
    (X ^ 2 + C A * X - C B : R[X]).Monic := by
  have hlow : (C B - C A * X : R[X]).degree < (X ^ 2 : R[X]).degree := by
    rw [degree_X_pow]
    exact (degree_sub_le _ _).trans_lt (max_lt
      (degree_C_le.trans_lt (by norm_num))
      ((degree_C_mul_X_le A).trans_lt (by norm_num)))
  rw [show X ^ 2 + C A * X - C B = X ^ 2 - (C B - C A * X) by ring]
  exact (monic_X_pow 2).sub_of_left hlow

private theorem discr_quadratic_generator
    [Module.Finite F L] [Algebra.IsQuadraticExtension F L]
    [Algebra.IsSeparable F L]
    (u : L) (A B : F)
    (htwo0 : (2 : F) ≠ 0)
    (hu : u ^ 2 + algebraMap F L A * u = algebraMap F L B)
    (hgen : Algebra.adjoin F ({u} : Set L) = ⊤) :
    Algebra.discr F
      (LanglandsSecondMainLemma.Local.monogenicPowerBasis u
        (Algebra.IsIntegral.isIntegral u) hgen).basis = A ^ 2 + 4 * B := by
  let pb : PowerBasis F L :=
    LanglandsSecondMainLemma.Local.monogenicPowerBasis u
      (Algebra.IsIntegral.isIntegral u) hgen
  have hpbgen : pb.gen = u :=
    LanglandsSecondMainLemma.Local.monogenicPowerBasis_gen u
      (Algebra.IsIntegral.isIntegral u) hgen
  have hmin : minpoly F u = X ^ 2 + C A * X - C B :=
    quadratic_minpoly F u A B hu hgen
  let y : L := 2 * u + algebraMap F L A
  let D : F := A ^ 2 + 4 * B
  have hy_sq : y ^ 2 = algebraMap F L D := by
    have hu' : u ^ 2 = algebraMap F L B - algebraMap F L A * u := by
      linear_combination hu
    calc
      y ^ 2 = 4 * u ^ 2 + 4 * algebraMap F L A * u +
          (algebraMap F L A) ^ 2 := by simp only [y]; ring
      _ = algebraMap F L D := by
        rw [hu']
        simp only [D, map_add, map_pow, map_mul, map_ofNat]
        ring
  have hygen : Algebra.adjoin F ({y} : Set L) = ⊤ := by
    apply adjoin_affine_eq_top F u y 2 A htwo0 (by
      simp only [y, map_ofNat]) hgen
  have hyrel : y ^ 2 + algebraMap F L 0 * y = algebraMap F L D := by
    simpa using hy_sq
  have hymin : minpoly F y = X ^ 2 - C D := by
    simpa using quadratic_minpoly F y 0 D hyrel hygen
  let pby : PowerBasis F L :=
    PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral y) hygen
  have hpbygen : pby.gen = y := PowerBasis.ofAdjoinEqTop_gen _ _
  have hpbydim : pby.dim = 2 := by
    rw [← PowerBasis.finrank pby]
    exact Algebra.IsQuadraticExtension.finrank_eq_two F L
  have hynorm : Algebra.norm F y = -D := by
    have hnorm := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pby
    rw [hpbygen, hymin, hpbydim] at hnorm
    simpa using hnorm
  rw [Algebra.discr_powerBasis_eq_norm F pb]
  rw [Algebra.IsQuadraticExtension.finrank_eq_two F L, hpbgen, hmin]
  have hderiv : Polynomial.aeval u
      (Polynomial.derivative (X ^ 2 + C A * X - C B)) = y := by
    simp only [Polynomial.derivative_pow, Polynomial.derivative_X,
      Polynomial.derivative_C, Polynomial.derivative_mul, Nat.cast_ofNat,
      zero_mul, map_sub, map_add, map_mul, map_pow,
      aeval_X, aeval_C, map_one]
    simp only [y]
    rw [map_ofNat]
    ring
  rw [hderiv, hynorm]
  simp [D]

/-- Scaling `1 + 2x` by a nonzero base scalar preserves the quadratic generator. -/
private theorem exists_scaled_quadratic_generator
    (x₀ : L) (f₀ f c : F) (htwo0 : (2 : F) ≠ 0) (hc0 : c ≠ 0)
    (hx₀eq : x₀ ^ 2 + x₀ = algebraMap F L f₀)
    (hx₀gen : Algebra.adjoin F ({x₀} : Set L) = ⊤)
    (hfrel : (1 + 4 * f₀) * c ^ 2 = 1 + 4 * f) :
    ∃ x : L, x ^ 2 + x = algebraMap F L f ∧
      Algebra.adjoin F ({x} : Set L) = ⊤ := by
  let x : L := ((1 + 2 * x₀) * algebraMap F L c - 1) / 2
  have htwoL : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using ((map_ne_zero (algebraMap F L)).2 htwo0)
  refine ⟨x, ?_, ?_⟩
  · have hSsq : (1 + 2 * x₀) ^ 2 = algebraMap F L (1 + 4 * f₀) := by
      rw [map_add, map_one, map_mul, map_ofNat, ← hx₀eq]
      ring
    dsimp only [x]
    field_simp [htwoL]
    rw [show ((1 + 2 * x₀) * algebraMap F L c - 1) *
        ((1 + 2 * x₀) * algebraMap F L c - 1 + 2) =
        (1 + 2 * x₀) ^ 2 * (algebraMap F L c) ^ 2 - 1 by ring,
      hSsq, ← map_pow, ← map_mul, hfrel]
    simp only [map_add, map_mul, map_one, map_ofNat]
    ring
  · apply adjoin_affine_eq_top F x₀ x c ((c - 1) / 2) hc0 _ hx₀gen
    dsimp only [x]
    rw [map_div₀, map_sub, map_one, map_ofNat]
    field_simp [htwoL]
    ring

end Quadratic

/-- The order of four is twice the dyadic absolute ramification index. -/
private theorem ord_four (e : ℕ) (htwo : ord F (2 : F) = (e : WithTop ℤ)) :
    ord F (4 : F) = ((2 * e : ℕ) : WithTop ℤ) := by
  rw [show (4 : F) = 2 * 2 by norm_num, ord_mul, htwo]
  exact_mod_cast (by omega : e + e = 2 * e)

/-- The linear and square perturbations are strictly deeper than the original numerator. -/
private theorem ord_quadratic_perturbation
    (e a : ℕ) (ha : 1 ≤ a) (hae : a ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (p U : F) (w : ringOfIntegers F)
    (hp : ord F p = ((e - a + 1 : ℕ) : WithTop ℤ))
    (hU : ord F U = 0)
    (hbase : ord F (U - 1) = ((2 * (e - a) + 1 : ℕ) : WithTop ℤ)) :
    ord F (U * (1 + p * (w : F)) ^ 2 - 1) =
      ((2 * (e - a) + 1 : ℕ) : WithTop ℤ) := by
  let b : ℕ := 2 * (e - a) + 1
  let s : ℕ := e - a + 1
  let c : F := 1 + p * (w : F)
  change ord F p = (s : WithTop ℤ) at hp
  change ord F (U - 1) = (b : WithTop ℤ) at hbase
  change ord F (U * c ^ 2 - 1) = (b : WithTop ℤ)
  have hcorrection : U * c ^ 2 - 1 - (U - 1) ∈ lattice F ((b + 1 : ℕ) : ℤ) := by
    have hterm1 : 2 * p * U * (w : F) ∈ lattice F ((b + 1 : ℕ) : ℤ) := by
      rw [mem_lattice, ord_mul, ord_mul, ord_mul, htwo, hp, hU]
      have hwint : (0 : WithTop ℤ) ≤ ord F (w : F) :=
        (ord_nonneg_iff_mem_integer F _).2 w.property
      norm_num at hwint ⊢
      have hlevel : b + 1 ≤ e + s := by simp only [b, s]; omega
      have hbaseTop : (b : WithTop ℤ) + 1 ≤
          (e : WithTop ℤ) + (s : WithTop ℤ) := by exact_mod_cast hlevel
      change (b + 1 : WithTop ℤ) ≤
        (e : WithTop ℤ) + (s : WithTop ℤ) + ord F (w : F)
      exact hbaseTop.trans (le_add_of_nonneg_right hwint)
    have hterm2 : U * p ^ 2 * (w : F) ^ 2 ∈ lattice F ((b + 1 : ℕ) : ℤ) := by
      rw [mem_lattice, ord_mul, ord_mul, ord_pow, hU, hp, ord_pow]
      have hwint : (0 : WithTop ℤ) ≤ ord F (w : F) :=
        (ord_nonneg_iff_mem_integer F _).2 w.property
      norm_num at hwint ⊢
      have heq : (b : WithTop ℤ) + 1 = 2 • (s : WithTop ℤ) := by
        rw [two_nsmul]
        exact_mod_cast (show b + 1 = s + s by simp only [b, s]; omega)
      change (b + 1 : WithTop ℤ) ≤
        2 • (s : WithTop ℤ) + 2 • ord F (w : F)
      rw [heq]
      exact le_add_of_nonneg_right (nsmul_nonneg hwint 2)
    rw [show U * c ^ 2 - 1 - (U - 1) =
        2 * p * U * (w : F) + U * p ^ 2 * (w : F) ^ 2 by
      simp only [c]
      ring]
    exact add_mem_lattice F hterm1 hterm2
  have hcorrgt : (b : WithTop ℤ) < ord F (U * c ^ 2 - 1 - (U - 1)) := by
    rw [mem_lattice] at hcorrection
    have hlt : (b : WithTop ℤ) < ((b + 1 : ℕ) : WithTop ℤ) := by
      exact_mod_cast (show b < b + 1 by omega)
    exact hlt.trans_le hcorrection
  calc
    ord F (U * c ^ 2 - 1) =
        ord F ((U - 1) + (U * c ^ 2 - 1 - (U - 1))) := by congr 1; ring
    _ = min (ord F (U - 1)) (ord F (U * c ^ 2 - 1 - (U - 1))) :=
      ord_add_eq_min F (by rw [hbase]; exact ne_of_lt hcorrgt)
    _ = (b : WithTop ℤ) := by rw [hbase, min_eq_left hcorrgt.le]

/-- Construct the base scalars by alternating residue corrections, keeping the full depth. -/
private theorem exists_aligned_scalars
    (pi : ringOfIntegers F)
    (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F))
    (e a r : ℕ) (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (hreschar : residueCharacteristic F = 2)
    (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (f₀ g : F)
    (hf₀ : ord F f₀ = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ))
    (hg : ord F g = (((1 : ℤ) - 2 * r : ℤ) : WithTop ℤ)) :
    ∃ c f d : F,
      ord F c = 0 ∧
      (1 + 4 * f₀) * c ^ 2 = 1 + 4 * f ∧
      ord F f = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ) ∧
      ord F d = (((r : ℤ) - a : ℤ) : WithTop ℤ) ∧
      f + d ^ 2 * g ∈ lattice F (1 - (a : ℤ)) := by
  have hae : a ≤ e := har.trans hre
  have htwo0 : (2 : F) ≠ 0 := by
    apply (ord_ne_top_iff F).mp
    rw [htwo]
    simp
  have hfour0 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero htwo0 htwo0
  have hpi0 : (pi : F) ≠ 0 := by
    apply (ord_ne_top_iff F).mp
    rw [ord_uniformizer F hpi]
    simp
  let b : ℕ := 2 * (e - a) + 1
  let s : ℕ := e - a + 1
  let t : ℕ := r - a
  let q : F := (pi : F) ^ b
  let p : F := (pi : F) ^ s
  let U : F := 1 + 4 * f₀
  let C₀ : F := 4 * f₀ / q
  let A₀ : F := 4 * (pi : F) ^ (2 * t) * g / q
  have hfour := ord_four F e htwo
  have hq : ord F q = (b : WithTop ℤ) := by
    simp only [q]
    rw [ord_pow, ord_uniformizer F hpi]
    norm_num
  have hp : ord F p = (s : WithTop ℤ) := by
    simp only [p]
    rw [ord_pow, ord_uniformizer F hpi]
    norm_num
  have hfourf₀ : ord F (4 * f₀) = (b : WithTop ℤ) := by
    rw [ord_mul, hfour, hf₀]
    rw [natCast_withTop_eq_intCast (2 * e), natCast_withTop_eq_intCast b]
    rw [← WithTop.coe_add]
    congr 1
    push_cast [b, Nat.cast_sub hae]
    omega
  have hU : ord F U = 0 := by
    have hbpos : (0 : WithTop ℤ) < (b : WithTop ℤ) := by
      exact_mod_cast (show 0 < b by simp [b])
    simp only [U]
    rw [ord_add_eq_min F (by rw [ord_one, hfourf₀]; exact ne_of_lt hbpos),
      ord_one, hfourf₀, min_eq_left hbpos.le]
  have hC₀ : ord F C₀ = 0 := by
    simp only [C₀]
    rw [ord_div, hfourf₀, hq]
    have hbcast : (b : WithTop ℤ) = ((b : ℤ) : WithTop ℤ) := by norm_num
    rw [hbcast, ← WithTop.LinearOrderedAddCommGroup.coe_sub]
    simp
  have hA₀ : ord F A₀ = 0 := by
    simp only [A₀]
    rw [ord_div, ord_mul, ord_mul, hfour, ord_pow,
      ord_uniformizer F hpi, hg, hq]
    rw [nsmul_one, natCast_withTop_eq_intCast (2 * e),
      natCast_withTop_eq_intCast (2 * t),
      natCast_withTop_eq_intCast b]
    have hi : ((2 * e : ℕ) : ℤ) + ((2 * t : ℕ) : ℤ) +
        (1 - 2 * (r : ℤ)) - (b : ℤ) = 0 := by
      push_cast [b, t, Nat.cast_sub hae, Nat.cast_sub har]
      omega
    rw [← WithTop.coe_add, ← WithTop.coe_add,
      ← WithTop.LinearOrderedAddCommGroup.coe_sub]
    exact congrArg (fun z : ℤ => (z : WithTop ℤ)) hi
  obtain ⟨v, w, halign, hv⟩ :=
    exists_alternating_solution F hreschar (pi : F) C₀ A₀ U e a
      hpi htwo ha hae hC₀ hA₀ hU
  let c : F := 1 + p * (w : F)
  let d : F := (pi : F) ^ t * (v : F)
  let f : F := (U * c ^ 2 - 1) / 4
  have hspos : 0 < s := by simp [s]
  have hc : ord F c = 0 := by
    have hpw : (0 : WithTop ℤ) < ord F (p * (w : F)) := by
      rw [ord_mul, hp]
      have hwint : (0 : WithTop ℤ) ≤ ord F (w : F) :=
        (ord_nonneg_iff_mem_integer F _).2 w.property
      exact add_pos_of_pos_of_nonneg (by exact_mod_cast hspos) hwint
    simp only [c]
    rw [ord_add_eq_min F (by rw [ord_one]; exact ne_of_lt hpw), ord_one,
      min_eq_left hpw.le]
  have hq0 : q ≠ 0 := by simp [q, hpi0]
  have hpsq : p ^ 2 = q * (pi : F) := by
    have hexp : s + s = b + 1 := by simp only [s, b]; omega
    rw [show p ^ 2 = (pi : F) ^ (s + s) by simp only [p, pow_two, ← pow_add],
      hexp, pow_succ]
  have htpow : ((pi : F) ^ t) ^ 2 = (pi : F) ^ (2 * t) := by
    rw [pow_two, ← pow_add]
    congr 1
    omega
  have hqC : q * C₀ = 4 * f₀ := by
    simp only [C₀]
    field_simp
  have hqA : q * A₀ = 4 * (pi : F) ^ (2 * t) * g := by
    simp only [A₀]
    field_simp
  have hnumer :
      4 * (f + d ^ 2 * g) =
        q * (C₀ + (pi : F) * U * (w : F) ^ 2 + A₀ * (v : F) ^ 2) +
          2 * p * U * (w : F) := by
    simp only [f, d]
    rw [mul_pow, htpow]
    rw [show q * (C₀ + (pi : F) * U * (w : F) ^ 2 + A₀ * (v : F) ^ 2) =
        q * C₀ + q * (pi : F) * U * (w : F) ^ 2 +
          (q * A₀) * (v : F) ^ 2 by ring,
      hqC, hqA, ← hpsq]
    field_simp [hfour0]
    simp only [c]
    ring
  have hmain :
      q * (C₀ + (pi : F) * U * (w : F) ^ 2 + A₀ * (v : F) ^ 2) ∈
        lattice F ((b : ℤ) + a) := by
    have hqmem : q ∈ lattice F (b : ℤ) := by
      rw [mem_lattice, hq]
      norm_num
    exact mul_mem_lattice F hqmem halign
  have hlinear : 2 * p * U * (w : F) ∈ lattice F ((b : ℤ) + a) := by
    rw [mem_lattice, ord_mul, ord_mul, ord_mul, htwo, hp, hU]
    have hwint : (0 : WithTop ℤ) ≤ ord F (w : F) :=
      (ord_nonneg_iff_mem_integer F _).2 w.property
    norm_num at hwint ⊢
    have heq : (b : WithTop ℤ) + (a : WithTop ℤ) =
        (e : WithTop ℤ) + (s : WithTop ℤ) := by
      exact_mod_cast (show b + a = e + s by simp only [b, s]; omega)
    change ((b : WithTop ℤ) + (a : WithTop ℤ) ≤
      (e : WithTop ℤ) + (s : WithTop ℤ) + ord F (w : F))
    rw [heq]
    exact le_add_of_nonneg_right hwint
  have hnumdeep : 4 * (f + d ^ 2 * g) ∈ lattice F ((b : ℤ) + a) := by
    rw [hnumer]
    exact add_mem_lattice F hmain hlinear
  have hE : f + d ^ 2 * g ∈ lattice F (1 - (a : ℤ)) := by
    have hdiv := (div_mem_lattice_iff F (4 : F) (4 * (f + d ^ 2 * g))
      (2 * e : ℤ) (1 - (a : ℤ)) (by
        change ord F (4 : F) = (((2 * e : ℕ) : ℤ) : WithTop ℤ)
        exact hfour)).2 ?_
    · simpa [hfour0] using hdiv
    · have hlevel : (2 * (e : ℤ)) + (1 - (a : ℤ)) = (b : ℤ) + a := by
        norm_num [b, Nat.cast_sub hae]
        omega
      rw [hlevel]
      exact hnumdeep
  have hfnum : ord F (U * c ^ 2 - 1) = (b : WithTop ℤ) :=
    ord_quadratic_perturbation F e a ha hae htwo p U w hp hU
      (by simpa only [U, add_sub_cancel_left] using hfourf₀)
  have hf : ord F f = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ) := by
    simp only [f]
    rw [ord_div, hfnum, hfour]
    rw [natCast_withTop_eq_intCast b, natCast_withTop_eq_intCast (2 * e)]
    have hi : (b : ℤ) - (2 * e : ℕ) = 1 - 2 * (a : ℤ) := by
      push_cast [b, Nat.cast_sub hae]
      omega
    rw [← WithTop.LinearOrderedAddCommGroup.coe_sub]
    exact congrArg (fun z : ℤ => (z : WithTop ℤ)) hi
  have hd : ord F d = (((r : ℤ) - a : ℤ) : WithTop ℤ) := by
    simp only [d]
    rw [ord_mul, ord_pow, ord_uniformizer F hpi, hv]
    rw [nsmul_one, natCast_withTop_eq_intCast t]
    have hi : (t : ℤ) = (r : ℤ) - a := by
      push_cast [t, Nat.cast_sub har]
      omega
    norm_num
    exact congrArg (fun z : ℤ => (z : WithTop ℤ)) hi
  refine ⟨c, f, d, hc, ?_, hf, hd, hE⟩
  dsimp only [f, U]
  field_simp [hfour0]
  ring

/-- At equal breaks, a nonunit `1 + d` would deepen the third quadratic parameter. -/
private theorem third_parameter_mem_of_nonunit
    (e a : ℕ) (ha : 1 ≤ a) (hae : a ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (f g d : F)
    (hf : ord F f = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ))
    (hg : ord F g = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ))
    (hd0 : ord F d = 0)
    (hE : f + d ^ 2 * g ∈ lattice F (1 - (a : ℤ)))
    (hk : ord F (1 + d) ≠ 0) :
    f + g + 4 * f * g ∈ lattice F (2 - 2 * (a : ℤ)) := by
  have hfour := ord_four F e htwo
  have hdint : (0 : WithTop ℤ) ≤ ord F d := hd0.ge
  have hkint : (0 : WithTop ℤ) ≤ ord F (1 + d) := by
    exact (ord F).map_le_add (by simp) hdint
  have hkpos : (0 : WithTop ℤ) < ord F (1 + d) :=
    lt_of_le_of_ne hkint (Ne.symm hk)
  have hkdeep : 1 + d ∈ lattice F 1 := by
    let k : ringOfIntegers F :=
      ⟨1 + d, (ord_nonneg_iff_mem_integer F _).1 hkint⟩
    exact (mem_lattice_one_iff_mem_maximalIdeal F k).2
      ((ord_pos_iff_mem_maximalIdeal F k).1 hkpos)
  have htwodeep : (2 : F) ∈ lattice F 1 := by
    rw [mem_lattice, htwo]
    exact_mod_cast (ha.trans hae)
  have hminus : 1 - d ∈ lattice F 1 := by
    rw [show 1 - d = 2 - (1 + d) by ring]
    exact sub_mem_lattice F htwodeep hkdeep
  have honeSubSq : 1 - d ^ 2 ∈ lattice F 2 := by
    rw [show 1 - d ^ 2 = (1 - d) * (1 + d) by ring]
    exact mul_mem_lattice F hminus hkdeep
  have hgprod : g * (1 - d ^ 2) ∈ lattice F (3 - 2 * (a : ℤ)) := by
    have hgmem : g ∈ lattice F (1 - 2 * (a : ℤ)) := by
      rw [mem_lattice, hg]
    have hlevel : (1 - 2 * (a : ℤ)) + 2 = 3 - 2 * (a : ℤ) := by ring
    simpa only [hlevel] using mul_mem_lattice F hgmem honeSubSq
  have hE' : f + d ^ 2 * g ∈ lattice F (2 - 2 * (a : ℤ)) :=
    lattice_antitone F (by omega) hE
  have hfg : f + g ∈ lattice F (2 - 2 * (a : ℤ)) := by
    rw [show f + g = (f + d ^ 2 * g) + g * (1 - d ^ 2) by ring]
    exact add_mem_lattice F hE'
      (lattice_antitone F (by omega) hgprod)
  have hfourfg : 4 * f * g ∈ lattice F (2 - 2 * (a : ℤ)) := by
    have hfourmem : (4 : F) ∈ lattice F (2 * (e : ℤ)) := by
      rw [mem_lattice]
      rw [hfour, natCast_withTop_eq_intCast (2 * e)]
      exact WithTop.coe_le_coe.mpr (by push_cast; omega)
    have hfmem : f ∈ lattice F (1 - 2 * (a : ℤ)) := by
      rw [mem_lattice, hf]
    have hgmem : g ∈ lattice F (1 - 2 * (a : ℤ)) := by
      rw [mem_lattice, hg]
    apply lattice_antitone F (show 2 - 2 * (a : ℤ) ≤
        2 * (e : ℤ) + (1 - 2 * (a : ℤ)) + (1 - 2 * (a : ℤ)) by omega)
    exact mul_mem_lattice F (mul_mem_lattice F hfourmem hfmem) hgmem
  exact add_mem_lattice F hfg hfourfg

section ThirdField

variable {L₃ : Type*} [Field L₃] [ValuativeRel L₃] [TopologicalSpace L₃]
  [IsNonarchimedeanLocalField L₃]
  [Algebra F L₃] [ValuativeExtension F L₃]
  [Module.Finite F L₃] [Algebra.IsQuadraticExtension F L₃] [IsGalois F L₃]

/-- Scaling a deep quadratic parameter gives an integral generator and bounds the different. -/
private theorem different_le_of_deep_quadratic_parameter
    (pi : ringOfIntegers F)
    (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F))
    (e a : ℕ) (ha : 1 ≤ a) (hae : a ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (h : F) (z : L₃)
    (hh : h ∈ lattice F (2 - 2 * (a : ℤ)))
    (hzeq : z ^ 2 + z = algebraMap F L₃ h)
    (hzgen : Algebra.adjoin F ({z} : Set L₃) = ⊤)
    (hres₃ : residueDegree F L₃ = 1) :
    differentExponent F L₃ ≤ 2 * (a - 1) := by
  have htwo0 : (2 : F) ≠ 0 := (ord_ne_top_iff F).mp (by rw [htwo]; simp)
  have hpi0 : (pi : F) ≠ 0 :=
    (ord_ne_top_iff F).mp (by rw [ord_uniformizer F hpi]; simp)
  have hfour := ord_four F e htwo
  let P : F := (pi : F) ^ (a - 1)
  let B : F := P ^ 2 * h
  let u : L₃ := algebraMap F L₃ P * z
  have hPord : ord F P = ((a - 1 : ℕ) : WithTop ℤ) := by
    simp only [P]
    rw [ord_pow, ord_uniformizer F hpi]
    norm_num
  have hP0 : P ≠ 0 := by simp [P, hpi0]
  have hBint : B ∈ lattice F 0 := by
    simp only [B]
    have hPmem : P ^ 2 ∈ lattice F (2 * ((a - 1 : ℕ) : ℤ)) := by
      rw [mem_lattice, ord_pow, hPord]
      rw [two_nsmul, natCast_withTop_eq_intCast (a - 1)]
      change (((2 : ℤ) * (a - 1 : ℕ)) : WithTop ℤ) ≤
        (((a - 1 : ℕ) : ℤ) : WithTop ℤ) + (((a - 1 : ℕ) : ℤ) : WithTop ℤ)
      rw [← WithTop.coe_add]
      exact WithTop.coe_le_coe.mpr (by omega)
    have hlevel : 2 * ((a - 1 : ℕ) : ℤ) + (2 - 2 * (a : ℤ)) = 0 := by
      norm_num [Nat.cast_sub ha]
      ring
    have hprod := mul_mem_lattice F hPmem hh
    rw [hlevel] at hprod
    exact hprod
  have hueq : u ^ 2 + algebraMap F L₃ P * u = algebraMap F L₃ B := by
    simp only [u, B, map_mul, map_pow]
    rw [← hzeq]
    ring
  have hugen : Algebra.adjoin F ({u} : Set L₃) = ⊤ := by
    apply adjoin_affine_eq_top F z u P 0 hP0
    · simp [u]
    · exact hzgen
  have huintegral : IsIntegral (ringOfIntegers F) u := by
    let PO : ringOfIntegers F := ⟨P, (mem_lattice_zero_iff F).1
      (by rw [mem_lattice, hPord]; norm_num)⟩
    let BO : ringOfIntegers F := ⟨B, (mem_lattice_zero_iff F).1 hBint⟩
    refine ⟨X ^ 2 + C PO * X - C BO, quadraticPolynomial_monic PO BO, ?_⟩
    change Polynomial.aeval u (X ^ 2 + C PO * X - C BO) = 0
    simp only [map_sub, map_add, map_pow, aeval_X, aeval_C, map_mul]
    have hPO : algebraMap (ringOfIntegers F) L₃ PO = algebraMap F L₃ P := by
      rw [IsScalarTower.algebraMap_apply (ringOfIntegers F) F L₃]
      rfl
    have hBO : algebraMap (ringOfIntegers F) L₃ BO = algebraMap F L₃ B := by
      rw [IsScalarTower.algebraMap_apply (ringOfIntegers F) F L₃]
      rfl
    rw [hPO, hBO]
    exact sub_eq_zero.mpr hueq
  letI : IsIntegralClosure (ringOfIntegers L₃) (ringOfIntegers F) L₃ :=
    ringOfIntegers_isIntegralClosure F L₃
  obtain ⟨uO, huO⟩ := (IsIntegralClosure.isIntegral_iff
    (A := ringOfIntegers L₃)).1 huintegral
  change (uO : L₃) = u at huO
  have huOgen : Algebra.adjoin F ({(uO : L₃)} : Set L₃) = ⊤ := by
    rw [huO]
    exact hugen
  have hbound := LanglandsSecondMainLemma.Local.differentExponent_le_ord_discr_of_generator
    F L₃ hres₃ uO huOgen
  have hdisc : Algebra.discr F
      (LanglandsSecondMainLemma.Local.monogenicPowerBasis (uO : L₃)
        (Algebra.IsIntegral.isIntegral (uO : L₃)) huOgen).basis =
      P ^ 2 + 4 * B := by
    have hueqO : (uO : L₃) ^ 2 + algebraMap F L₃ P * (uO : L₃) =
        algebraMap F L₃ B := by rw [huO]; exact hueq
    exact discr_quadratic_generator F (uO : L₃) P B htwo0 hueqO huOgen
  rw [hdisc] at hbound
  have hfourhpos : (0 : WithTop ℤ) < ord F (4 * h) := by
    rw [ord_mul, hfour]
    rw [mem_lattice] at hh
    have hpos : (0 : WithTop ℤ) <
        (((2 * e : ℕ) : ℤ) : WithTop ℤ) +
          ((2 - 2 * (a : ℤ) : ℤ) : WithTop ℤ) := by
      exact_mod_cast (show 0 < ((2 * e : ℕ) : ℤ) +
        (2 - 2 * (a : ℤ)) by push_cast; omega)
    rw [natCast_withTop_eq_intCast (2 * e)]
    exact hpos.trans_le (add_le_add (le_refl _) hh)
  have honefourh : ord F (1 + 4 * h) = 0 := by
    rw [ord_add_eq_min F (by rw [ord_one]; exact ne_of_lt hfourhpos), ord_one,
      min_eq_left hfourhpos.le]
  have hdiscord : ord F (P ^ 2 + 4 * B) =
      ((2 * (a - 1 : ℕ) : ℕ) : WithTop ℤ) := by
    rw [show P ^ 2 + 4 * B = P ^ 2 * (1 + 4 * h) by dsimp only [B]; ring,
      ord_mul, ord_pow, hPord, honefourh]
    rw [two_nsmul]
    exact_mod_cast (by omega : (a - 1) + (a - 1) + 0 = 2 * (a - 1))
  rw [hdiscord] at hbound
  rw [natCast_withTop_eq_intCast (2 * (a - 1))] at hbound
  exact_mod_cast (WithTop.coe_le_coe.mp hbound)

/-- Assemble the two cases: positive depth, or the third-field discriminant obstruction. -/
private theorem aligned_one_add_ord
    (pi : ringOfIntegers F)
    (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F))
    (e a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (f₀ f g c d : F) (z₀ : L₃)
    (hc : ord F c = 0)
    (hfrel : (1 + 4 * f₀) * c ^ 2 = 1 + 4 * f)
    (hf : ord F f = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ))
    (hg : ord F g = (((1 : ℤ) - 2 * r : ℤ) : WithTop ℤ))
    (hd : ord F d = (((r : ℤ) - a : ℤ) : WithTop ℤ))
    (hE : f + d ^ 2 * g ∈ lattice F (1 - (a : ℤ)))
    (hz₀eq : z₀ ^ 2 + z₀ = algebraMap F L₃ (f₀ + g + 4 * f₀ * g))
    (hz₀gen : Algebra.adjoin F ({z₀} : Set L₃) = ⊤)
    (hres₃ : residueDegree F L₃ = 1)
    (hdiff₃ : differentExponent F L₃ = 2 * r) :
    ord F (1 + d) = 0 := by
  by_cases hra : r = a
  · subst r
    by_contra hk
    have hh := third_parameter_mem_of_nonunit F e a ha hre htwo f g d hf hg
      (by simpa using hd) hE hk
    have htwo0 : (2 : F) ≠ 0 := (ord_ne_top_iff F).mp (by rw [htwo]; simp)
    have hc0 : c ≠ 0 := (ord_ne_top_iff F).mp (by rw [hc]; simp)
    have hhrel : (1 + 4 * (f₀ + g + 4 * f₀ * g)) * c ^ 2 =
        1 + 4 * (f + g + 4 * f * g) := by
      calc
        _ = ((1 + 4 * f₀) * c ^ 2) * (1 + 4 * g) := by ring
        _ = _ := by rw [hfrel]; ring
    obtain ⟨z, hzeq, hzgen⟩ := exists_scaled_quadratic_generator F z₀
      (f₀ + g + 4 * f₀ * g) (f + g + 4 * f * g) c htwo0 hc0 hz₀eq hz₀gen hhrel
    have hbound := different_le_of_deep_quadratic_parameter F pi hpi e a ha hre
      htwo (f + g + 4 * f * g) z hh hzeq hzgen hres₃
    rw [hdiff₃] at hbound
    omega
  · have hdpos : (0 : WithTop ℤ) < ord F d := by
      rw [hd]
      exact_mod_cast (show 0 < (r : ℤ) - a by omega)
    rw [ord_add_eq_min F (by rw [ord_one]; exact ne_of_lt hdpos), ord_one,
      min_eq_left hdpos.le]

end ThirdField

section Alignment

variable {L₁ L₃ : Type*} [Field L₁] [Field L₃]
  [ValuativeRel L₃] [TopologicalSpace L₃]
  [IsNonarchimedeanLocalField L₃]
  [Algebra F L₁] [Algebra F L₃] [ValuativeExtension F L₃]
  [Module.Finite F L₁] [Module.Finite F L₃]
  [Algebra.IsQuadraticExtension F L₁] [Algebra.IsQuadraticExtension F L₃]
  [IsGalois F L₃]

set_option linter.unusedSectionVars false in
/-- Paper 13.2 (`D:NM:alignment`): adjust the generator and scalar simultaneously.
The original hypotheses on `L₁` are retained as part of the public interface. -/
theorem alignment
    (pi : ringOfIntegers F)
    (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F))
    (e a r : ℕ)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (hreschar : residueCharacteristic F = 2)
    (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (f₀ g : F) (x₀ : L₁) (z₀ : L₃)
    (hf₀ : ord F f₀ = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ))
    (hg : ord F g = (((1 : ℤ) - 2 * r : ℤ) : WithTop ℤ))
    (hx₀eq : x₀ ^ 2 + x₀ = algebraMap F L₁ f₀)
    (hx₀gen : Algebra.adjoin F ({x₀} : Set L₁) = ⊤)
    (hz₀eq : z₀ ^ 2 + z₀ =
      algebraMap F L₃ (f₀ + g + 4 * f₀ * g))
    (hz₀gen : Algebra.adjoin F ({z₀} : Set L₃) = ⊤)
    (hres₃ : residueDegree F L₃ = 1)
    (hdiff₃ : differentExponent F L₃ = 2 * r) :
    ∃ (x : L₁) (f d : F),
      x ^ 2 + x = algebraMap F L₁ f ∧
      Algebra.adjoin F ({x} : Set L₁) = ⊤ ∧
      ord F f = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ) ∧
      ord F d = (((r : ℤ) - a : ℤ) : WithTop ℤ) ∧
      f + d ^ 2 * g ∈ lattice F (1 - (a : ℤ)) ∧
      ord F (1 + d) = 0 := by
  obtain ⟨c, f, d, hc, hfrel, hf, hd, hE⟩ :=
    exists_aligned_scalars F pi hpi e a r htwo hreschar ha har hre f₀ g hf₀ hg
  have htwo0 : (2 : F) ≠ 0 := (ord_ne_top_iff F).mp (by rw [htwo]; simp)
  have hc0 : c ≠ 0 := (ord_ne_top_iff F).mp (by rw [hc]; simp)
  obtain ⟨x, hxeq, hxgen⟩ :=
    exists_scaled_quadratic_generator F x₀ f₀ f c htwo0 hc0 hx₀eq hx₀gen hfrel
  exact ⟨x, f, d, hxeq, hxgen, hf, hd, hE,
    aligned_one_add_ord F pi hpi e a r ha har hre htwo f₀ f g c d z₀
      hc hfrel hf hg hd hE hz₀eq hz₀gen hres₃ hdiff₃⟩

end Alignment

end

end LanglandsSecondMainLemma.Dyadic.Nonmaximal
