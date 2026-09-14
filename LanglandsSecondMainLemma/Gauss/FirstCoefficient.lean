import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsSecondMainLemma.Gauss.CoefficientField

/-!
# The first coefficient of the appendix Gauss sum

This file proves paper Lemma A.1.  The plus-sign Gauss sum is formed in
the cyclotomic integer ring supplied by `GaussCoefficientField`.  Its
additive factor is `zeta` raised to the standard representative of the
absolute trace in `ZMod p`.

The proof expands that factor modulo the square of `zeta - 1`, evaluates
the resulting finite-field power sums, and obtains Frobenius invariance by
reindexing the nonzero residue classes.
-/

open scoped BigOperators

namespace LanglandsSecondMainLemma.Gauss

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]

/-- The representative in `{0, ..., p - 1}` of the absolute trace. -/
noncomputable def absoluteTraceRepresentative (x : k) : ℕ :=
  (Algebra.trace (ZMod p) k x).val

/-- The additive root-of-unity factor in the appendix Gauss sum. -/
noncomputable def coefficientAdditiveFactor (C : GaussCoefficientField p k)
    (x : k) : C.IntegerRing :=
  C.zeta ^ absoluteTraceRepresentative p k x

/-- The plus-sign Gauss sum `G_a` of Appendix A. -/
noncomputable def coefficientGaussSum (C : GaussCoefficientField p k)
    (a : ℕ) : C.IntegerRing := by
  exact ∑ x ∈ multiplicativeResidueUnits k,
    teichmuller_lift p k C (((x⁻¹ : kˣ) : k)) ^ a *
      coefficientAdditiveFactor p k C (x : k)

private theorem one_add_pow_firstOrder
    {R : Type*} [CommRing R] (pi : R) (n : ℕ) :
    (1 + pi) ^ n ≡ 1 + (n : R) * pi [SMOD Ideal.span {pi ^ 2}] := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (1 + pi) ^ (n + 1) = (1 + pi) ^ n * (1 + pi) := pow_succ _ _
        _ ≡ (1 + (n : R) * pi) * (1 + pi) [SMOD Ideal.span {pi ^ 2}] :=
          ih.mul SModEq.rfl
        _ = (1 + ((n + 1 : ℕ) : R) * pi) + (n : R) * pi ^ 2 := by
          push_cast
          ring
        _ ≡ 1 + ((n + 1 : ℕ) : R) * pi [SMOD Ideal.span {pi ^ 2}] := by
          rw [SModEq.sub_mem]
          have hmem : (n : R) * pi ^ 2 ∈ Ideal.span {pi ^ 2} :=
            Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
          have heq :
              (1 + ((n + 1 : ℕ) : R) * pi + (n : R) * pi ^ 2) -
                (1 + ((n + 1 : ℕ) : R) * pi) = (n : R) * pi ^ 2 := by
            ring
          rw [heq]
          exact hmem

private theorem weightedTraceSum_eq_neg_one
    : letI : Fintype k := Fintype.ofFinite k
    (∑ x ∈ multiplicativeResidueUnits k, (x : k)⁻¹ *
      algebraMap (ZMod p) k (Algebra.trace (ZMod p) k (x : k))) = -1 := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  letI : CharP k p := charP_of_injective_algebraMap
    (RingHom.injective (algebraMap (ZMod p) k)) p
  have hunits : multiplicativeResidueUnits k = Finset.univ := by
    ext x
    simp [multiplicativeResidueUnits]
  rw [hunits]
  let f := Module.finrank (ZMod p) k
  have hcard : Fintype.card k = p ^ f := by
    dsimp only [f]
    simpa only [ZMod.card] using
      (Module.card_eq_pow_finrank (K := ZMod p) (V := k))
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hterm (i : ℕ) (hi : i < f) :
      (∑ x : kˣ, (x : k)⁻¹ * (x : k) ^ p ^ i) =
        if i = 0 then -1 else 0 := by
    have hpowpos : 0 < p ^ i := pow_pos (Fact.out : p.Prime).pos i
    have hrewrite (x : kˣ) :
        (x : k)⁻¹ * (x : k) ^ p ^ i = (x : k) ^ (p ^ i - 1) := by
      rw [show p ^ i = (p ^ i - 1) + 1 by omega, pow_add, pow_one]
      calc
        (x : k)⁻¹ * ((x : k) ^ (p ^ i - 1) * (x : k)) =
            (x : k) ^ (p ^ i - 1) * ((x : k)⁻¹ * (x : k)) := by ring
        _ = (x : k) ^ (p ^ i - 1) := by
          rw [inv_mul_cancel₀ (Units.ne_zero x), mul_one]
    simp_rw [hrewrite]
    rw [show (∑ x : kˣ, (x : k) ^ (p ^ i - 1)) =
        if Fintype.card k - 1 ∣ p ^ i - 1 then -1 else 0 by
      simpa only [Units.val_pow_eq_pow_val] using
        (FiniteField.sum_pow_units k (p ^ i - 1))]
    by_cases hi0 : i = 0
    · subst i
      simp
    · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
      have hp_le : p ≤ p ^ i := by
        calc
          p = p ^ 1 := by simp
          _ ≤ p ^ i := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hi_pos
      have hexp_pos : 0 < p ^ i - 1 := by omega
      have hpif : p ^ i < p ^ f :=
        Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt hi
      have hexp_lt : p ^ i - 1 < Fintype.card k - 1 := by
        rw [hcard]
        omega
      have hnotdvd : ¬ Fintype.card k - 1 ∣ p ^ i - 1 :=
        Nat.not_dvd_of_pos_of_lt hexp_pos hexp_lt
      simp [hi0, hnotdvd]
  calc
    (∑ x : kˣ, (x : k)⁻¹ *
        algebraMap (ZMod p) k (Algebra.trace (ZMod p) k (x : k))) =
        ∑ x : kˣ, (x : k)⁻¹ *
          ∑ i ∈ Finset.range f, (x : k) ^ p ^ i := by
      apply Finset.sum_congr rfl
      intro x _hx
      congr 1
      rw [FiniteField.algebraMap_trace_eq_sum_pow (ZMod p) k]
      simp only [Nat.card_zmod, f]
    _ = ∑ i ∈ Finset.range f,
        ∑ x : kˣ, (x : k)⁻¹ * (x : k) ^ p ^ i := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = -1 := by
      rw [Finset.sum_congr rfl fun i hi ↦ hterm i (Finset.mem_range.mp hi)]
      have hf_pos : 0 < f := Module.finrank_pos
      simp [hf_pos]

private theorem sum_teichmuller_inverse_eq_zero
    (C : GaussCoefficientField p k) (hq : 2 < Nat.card k) :
    (∑ x ∈ multiplicativeResidueUnits k,
      teichmuller_lift p k C (((x⁻¹ : kˣ) : k))) = 0 := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  letI : IsDomain C.IntegerRing := C.coefficientDomain
  have hunits : multiplicativeResidueUnits k = Finset.univ := by
    ext x
    simp [multiplicativeResidueUnits]
  rw [hunits]
  have hcardUnits : 1 < Fintype.card kˣ := by
    rw [Fintype.card_units]
    rw [Fintype.card_eq_nat_card]
    omega
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card hcardUnits (1 : kˣ)
  let chi : kˣ →* C.IntegerRing :=
    { toFun := fun x ↦ teichmuller_lift p k C (((x⁻¹ : kˣ) : k))
      map_one' := by simp
      map_mul' := by
        intro x y
        simp only [mul_inv_rev, Units.val_mul]
        rw [map_mul]
        exact mul_comm _ _ }
  have hchi : chi ≠ 1 := by
    intro h
    have hyvalue := DFunLike.congr_fun h y
    change teichmuller_lift p k C (((y⁻¹ : kˣ) : k)) = 1 at hyvalue
    have hyred := congrArg (cyclotomicResidueMap p k C.unramified) hyvalue
    rw [teichmuller_lift_reduction, map_one] at hyred
    have hyinv : y⁻¹ = 1 := Units.ext hyred
    exact hy (inv_eq_one.mp hyinv)
  change (∑ x : kˣ, chi x) = 0
  exact sum_hom_units_eq_zero chi hchi

private theorem firstCoefficient_congruence
    (C : GaussCoefficientField p k) (hq : 2 < Nat.card k) :
    coefficientGaussSum p k C 1 ≡ -C.uniformizer
      [SMOD Ideal.span {C.uniformizer ^ 2}] := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  letI : IsDomain C.IntegerRing := C.coefficientDomain
  letI : IsLocalRing C.IntegerRing := C.coefficientLocalRing
  let pi : C.IntegerRing := C.uniformizer
  let liftTerm : kˣ → C.IntegerRing := fun x ↦
    teichmuller_lift p k C (((x⁻¹ : kˣ) : k))
  let traceTerm : kˣ → C.IntegerRing := fun x ↦
    (absoluteTraceRepresentative p k (x : k) : C.IntegerRing)
  let traceSum : C.IntegerRing :=
    ∑ x ∈ multiplicativeResidueUnits k, liftTerm x * traceTerm x
  have hzeta : C.zeta = 1 + pi := by
    dsimp only [GaussCoefficientField.zeta, GaussCoefficientField.uniformizer,
      cyclotomicZeta, pi]
    ring
  have hadditive (x : k) :
      coefficientAdditiveFactor p k C x ≡
        1 + (absoluteTraceRepresentative p k x : C.IntegerRing) * pi
          [SMOD Ideal.span {pi ^ 2}] := by
    rw [coefficientAdditiveFactor, hzeta]
    exact one_add_pow_firstOrder pi _
  have hgauss :
      coefficientGaussSum p k C 1 ≡
        ∑ x ∈ multiplicativeResidueUnits k,
          liftTerm x * (1 + traceTerm x * pi)
            [SMOD Ideal.span {pi ^ 2}] := by
    unfold coefficientGaussSum
    apply SModEq.sum
    intro x hx
    simp only [pow_one]
    exact SModEq.mul SModEq.rfl (hadditive (x : k))
  have hliftSum :
      (∑ x ∈ multiplicativeResidueUnits k, liftTerm x) = 0 := by
    exact sum_teichmuller_inverse_eq_zero p k C hq
  have hexpand :
      (∑ x ∈ multiplicativeResidueUnits k,
          liftTerm x * (1 + traceTerm x * pi)) = pi * traceSum := by
    calc
      (∑ x ∈ multiplicativeResidueUnits k,
          liftTerm x * (1 + traceTerm x * pi)) =
          ∑ x ∈ multiplicativeResidueUnits k,
            (liftTerm x + pi * (liftTerm x * traceTerm x)) := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
      _ = (∑ x ∈ multiplicativeResidueUnits k, liftTerm x) +
          pi * (∑ x ∈ multiplicativeResidueUnits k,
            liftTerm x * traceTerm x) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = pi * traceSum := by rw [hliftSum, zero_add]
  have htraceReduction :
      cyclotomicResidueMap p k C.unramified traceSum = -1 := by
    calc
      cyclotomicResidueMap p k C.unramified traceSum =
          ∑ x ∈ multiplicativeResidueUnits k,
            (x : k)⁻¹ *
              algebraMap (ZMod p) k (Algebra.trace (ZMod p) k (x : k)) := by
        dsimp only [traceSum, liftTerm, traceTerm]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [map_mul, teichmuller_lift_reduction, map_natCast]
        change (((x⁻¹ : kˣ) : k)) *
            (absoluteTraceRepresentative p k (x : k) : k) = _
        rw [show (((x⁻¹ : kˣ) : k)) = (x : k)⁻¹ by simp]
        congr 1
        rw [absoluteTraceRepresentative,
          ← map_natCast (algebraMap (ZMod p) k), ZMod.natCast_zmod_val]
      _ = -1 := weightedTraceSum_eq_neg_one p k
  have hsurjective : Function.Surjective
      (cyclotomicResidueMap p k C.unramified) := by
    intro x
    exact ⟨teichmuller_lift p k C x, teichmuller_lift_reduction p k C x⟩
  have hkernel : RingHom.ker (cyclotomicResidueMap p k C.unramified) =
      Ideal.span {pi} := by
    rw [IsLocalRing.ker_eq_maximalIdeal _ hsurjective]
    exact cyclotomicUniformizer p k C
  have htraceDiff : traceSum - (-1) ∈ Ideal.span {pi} := by
    rw [← hkernel, RingHom.mem_ker, map_sub, htraceReduction, map_neg,
      map_one, sub_self]
  have hlinear : pi * traceSum ≡ -pi [SMOD Ideal.span {pi ^ 2}] := by
    rw [SModEq.sub_mem, Ideal.mem_span_singleton]
    rw [Ideal.mem_span_singleton] at htraceDiff
    obtain ⟨a, ha⟩ := htraceDiff
    refine ⟨a, ?_⟩
    calc
      pi * traceSum - -pi = pi * (traceSum - -1) := by ring
      _ = pi * (pi * a) := by rw [ha]
      _ = pi ^ 2 * a := by ring
  calc
    coefficientGaussSum p k C 1 ≡
        ∑ x ∈ multiplicativeResidueUnits k,
          liftTerm x * (1 + traceTerm x * pi)
          [SMOD Ideal.span {pi ^ 2}] := hgauss
    _ = pi * traceSum := hexpand
    _ ≡ -pi [SMOD Ideal.span {pi ^ 2}] := hlinear

private theorem coefficientGaussSum_frobenius
    (C : GaussCoefficientField p k) (j : ℕ) :
    coefficientGaussSum p k C (p ^ j) = coefficientGaussSum p k C 1 := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  letI : CharP k p := charP_of_injective_algebraMap
    (RingHom.injective (algebraMap (ZMod p) k)) p
  let sigma := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k
  let sigmaj : k ≃ₐ[ZMod p] k := sigma ^ j
  let e : kˣ ≃* kˣ := Units.mapEquiv sigmaj.toMulEquiv
  have hsigmaj (x : k) : sigmaj x = x ^ p ^ j := by
    dsimp only [sigmaj, sigma]
    rw [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]
  have heval (x : kˣ) : (e x : k) = (x : k) ^ p ^ j := by
    change sigmaj (x : k) = _
    exact hsigmaj (x : k)
  have hinv (x : kˣ) : (((e x)⁻¹ : kˣ) : k) =
      (((x⁻¹ : kˣ) : k)) ^ p ^ j := by
    calc
      (((e x)⁻¹ : kˣ) : k) = (e x : k)⁻¹ := by simp
      _ = ((x : k) ^ p ^ j)⁻¹ := by rw [heval]
      _ = ((x : k)⁻¹) ^ p ^ j := (inv_pow _ _).symm
      _ = (((x⁻¹ : kˣ) : k)) ^ p ^ j := by simp
  have hlift (x : kˣ) :
      teichmuller_lift p k C (((x⁻¹ : kˣ) : k)) ^ p ^ j =
        teichmuller_lift p k C ((((e x)⁻¹ : kˣ) : k)) := by
    rw [← map_pow, ← hinv]
  have htrace (x : kˣ) :
      Algebra.trace (ZMod p) k (e x : k) =
        Algebra.trace (ZMod p) k (x : k) := by
    change Algebra.trace (ZMod p) k (sigmaj (x : k)) = _
    exact Algebra.trace_eq_of_algEquiv sigmaj (x : k)
  have hadditive (x : kˣ) :
      coefficientAdditiveFactor p k C (x : k) =
        coefficientAdditiveFactor p k C (e x : k) := by
    unfold coefficientAdditiveFactor absoluteTraceRepresentative
    rw [htrace]
  have hunits : multiplicativeResidueUnits k = Finset.univ := by
    ext x
    simp [multiplicativeResidueUnits]
  unfold coefficientGaussSum
  rw [hunits]
  calc
    (∑ x : kˣ,
        teichmuller_lift p k C (((x⁻¹ : kˣ) : k)) ^ p ^ j *
          coefficientAdditiveFactor p k C (x : k)) =
        ∑ x : kˣ,
          teichmuller_lift p k C ((((e x)⁻¹ : kˣ) : k)) *
            coefficientAdditiveFactor p k C (e x : k) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hlift, hadditive]
    _ = ∑ x : kˣ,
          teichmuller_lift p k C (((x⁻¹ : kˣ) : k)) *
            coefficientAdditiveFactor p k C (x : k) :=
      e.toEquiv.sum_comp (fun x : kˣ ↦
        teichmuller_lift p k C (((x⁻¹ : kˣ) : k)) *
          coefficientAdditiveFactor p k C (x : k))
    _ = ∑ x : kˣ,
          teichmuller_lift p k C (((x⁻¹ : kˣ) : k)) ^ 1 *
            coefficientAdditiveFactor p k C (x : k) := by simp

/-- The first-coefficient calculation of paper Lemma A.1.  The first
assertion is made only when `q > 2`.  The second retains the manuscript's
index bounds; in particular, its quantified range is empty when `k = 𝔽₂`. -/
theorem firstCoefficient (C : GaussCoefficientField p k) :
    (2 < Nat.card k →
      coefficientGaussSum p k C 1 ≡ -C.uniformizer
        [SMOD Ideal.span {C.uniformizer ^ 2}]) ∧
    ∀ j : ℕ, j < Module.finrank (ZMod p) k →
      p ^ j < Nat.card k - 1 →
        coefficientGaussSum p k C (p ^ j) =
          coefficientGaussSum p k C 1 := by
  constructor
  · exact firstCoefficient_congruence p k C
  · intro j _hj _hjbound
    exact coefficientGaussSum_frobenius p k C j

end

end LanglandsSecondMainLemma.Gauss
