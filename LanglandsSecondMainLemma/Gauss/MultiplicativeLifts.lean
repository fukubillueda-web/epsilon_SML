import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsSecondMainLemma.Gauss.UnramifiedLift
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Henselian

/-!
# Multiplicative residue lifts

This file formalizes the Teichmüller-lift construction in
`epsilon_SML.tex`, lines 8252--8256.  For the complete DVR supplied by
`UnramifiedLift`, Hensel's lemma gives a unique root of `X ^ |k| - X`
above every residue class.  Its derivative reduces to `-1`, so the root
is simple.  Uniqueness makes the resulting section multiplicative.

For nonzero residues the fixed-root equation is exactly
`X ^ (|k| - 1) - 1 = 0`.  The final equivalence and finite-sum theorem
identify these roots with `kˣ`, as required for the Gauss sums in the
following appendix nodes.
-/

namespace LanglandsSecondMainLemma.Gauss

open Polynomial

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]

/-- Reduction from the coefficient ring to the prescribed finite field. -/
noncomputable def coefficientResidueMap
    (U : UnramifiedCoefficientLift p k) :
    AdjoinRoot U.polynomial →+* k := by
  let R := AdjoinRoot U.polynomial
  letI : IsDomain R := AdjoinRoot.isDomain_of_prime U.polynomial_prime
  letI : IsLocalRing R := U.localRing
  exact U.residueEquiv.toRingHom.comp (IsLocalRing.residue R)

omit [Finite k] in
theorem coefficientResidueMap_surjective
    (U : UnramifiedCoefficientLift p k) :
    Function.Surjective (coefficientResidueMap p k U) := by
  intro x
  let R := AdjoinRoot U.polynomial
  letI : IsDomain R := AdjoinRoot.isDomain_of_prime U.polynomial_prime
  letI : IsLocalRing R := U.localRing
  obtain ⟨x, rfl⟩ := U.residueEquiv.surjective x
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective x
  exact ⟨a, by simpa [coefficientResidueMap] using congrArg U.residueEquiv ha⟩

private theorem fixedRoot_existsUnique
    {R : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (k : Type*) [Field k] [Fintype k]
    (φ : R →+* k) (hφ : Function.Surjective φ) (x : k) :
    ∃! y : R, y ^ Fintype.card k = y ∧ φ y = x := by
  let q := Fintype.card k
  let f : R[X] := X ^ q - X
  have hq : 1 < q := Fintype.one_lt_card
  have hfmonic : f.Monic := by
    apply Polynomial.monic_X_pow_sub
    simpa [q] using hq
  obtain ⟨a₀, ha₀⟩ := hφ x
  letI : IsLocalHom φ := hφ.isLocalHom
  have hfa₀ : f.eval a₀ ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.maximalIdeal_comap φ]
    change φ (f.eval a₀) ∈ IsLocalRing.maximalIdeal k
    rw [(IsLocalRing.maximalIdeal k).eq_bot_of_prime]
    simp [f, q, ha₀, FiniteField.pow_card]
  have hderivMap (a : R) : φ (f.derivative.eval a) = -1 := by
    simp [f, q, Polynomial.derivative_X_pow, Nat.cast_card_eq_zero k]
  have hderivUnit (a : R) : IsUnit (f.derivative.eval a) := by
    apply IsUnit.of_map φ
    rw [hderivMap]
    exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero)
  obtain ⟨y, hyroot, hyclose⟩ := HenselianRing.is_henselian
    f hfmonic a₀ hfa₀
      ((hderivUnit a₀).map
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)))
  have hyφ : φ y = x := by
    have hker : y - a₀ ∈ RingHom.ker φ := by
      rw [IsLocalRing.ker_eq_maximalIdeal φ hφ]
      exact hyclose
    rw [RingHom.mem_ker, map_sub, sub_eq_zero, ha₀] at hker
    exact hker
  refine ⟨y, ⟨?_, hyφ⟩, ?_⟩
  · exact sub_eq_zero.mp (by simpa [f, q, Polynomial.IsRoot.def] using hyroot)
  · rintro z ⟨hzroot, hzφ⟩
    have hzroot' : f.eval z = 0 := by
      simpa [f, q, Polynomial.IsRoot.def] using sub_eq_zero.mpr hzroot
    apply IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hzroot' hyroot
    · intro hunit
      have := hunit.map φ
      rw [map_sub, hzφ, hyφ, sub_self] at this
      exact not_isUnit_zero this
    · exact hderivUnit z

/-- A Teichmüller section of the prescribed residue map.  The final field
records Hensel uniqueness, not merely a selected family of representatives. -/
structure MultiplicativeResidueLift
    (U : UnramifiedCoefficientLift p k) where
  lift : k →*₀ AdjoinRoot U.polynomial
  reduction (x : k) : coefficientResidueMap p k U (lift x) = x
  pow_card (x : k) : lift x ^ Nat.card k = lift x
  unique (x : k) (y : AdjoinRoot U.polynomial) :
    y ^ Nat.card k = y → coefficientResidueMap p k U y = x → y = lift x

/-- For a nonzero residue, the fixed-root equation is the manuscript's
`X ^ (|k| - 1) - 1` equation. -/
theorem MultiplicativeResidueLift.pow_card_sub_one
    (U : UnramifiedCoefficientLift p k)
    (D : MultiplicativeResidueLift p k U)
    {x : k} (hx : x ≠ 0) :
    D.lift x ^ (Nat.card k - 1) = 1 := by
  let R := AdjoinRoot U.polynomial
  letI : IsDomain R := AdjoinRoot.isDomain_of_prime U.polynomial_prime
  have hlift : D.lift x ≠ 0 := by
    intro hzero
    have := congrArg (coefficientResidueMap p k U) hzero
    rw [D.reduction, map_zero] at this
    exact hx this
  apply mul_right_cancel₀ hlift
  rw [one_mul, ← pow_succ]
  rw [Nat.sub_add_cancel Nat.card_pos]
  exact D.pow_card x

/-- The lift is the unique root of `X ^ (|k| - 1) - 1` with the prescribed
nonzero residue, which is the Hensel uniqueness used in the manuscript. -/
theorem MultiplicativeResidueLift.unique_pow_card_sub_one
    (U : UnramifiedCoefficientLift p k)
    (D : MultiplicativeResidueLift p k U)
    {x : k} (_ : x ≠ 0) (y : AdjoinRoot U.polynomial)
    (hy : y ^ (Nat.card k - 1) = 1)
    (hyred : coefficientResidueMap p k U y = x) :
    y = D.lift x := by
  apply D.unique x y
  · rw [← Nat.sub_add_cancel Nat.card_pos, pow_succ, hy, one_mul]
  · exact hyred

/-- The Hensel-unique roots of `X ^ |k| - X` form a multiplicative section
of reduction from the unramified coefficient ring to `k`. -/
theorem multiplicativeResidueLift_exists
    (U : UnramifiedCoefficientLift p k) :
    Nonempty (MultiplicativeResidueLift p k U) := by
  letI : Fintype k := Fintype.ofFinite k
  let R := AdjoinRoot U.polynomial
  letI : IsDomain R := AdjoinRoot.isDomain_of_prime U.polynomial_prime
  letI : IsLocalRing R := U.localRing
  letI : IsAdicComplete (IsLocalRing.maximalIdeal R) R := U.complete
  let φ : R →+* k := coefficientResidueMap p k U
  have hφ : Function.Surjective φ := coefficientResidueMap_surjective p k U
  have hex (x : k) : ∃! y : R, y ^ Fintype.card k = y ∧ φ y = x :=
    fixedRoot_existsUnique k φ hφ x
  let t : k → R := fun x ↦ (hex x).choose
  have htroot (x : k) : t x ^ Fintype.card k = t x := (hex x).choose_spec.1.1
  have htred (x : k) : φ (t x) = x := (hex x).choose_spec.1.2
  have htunique (x : k) (y : R)
      (hyroot : y ^ Fintype.card k = y) (hyred : φ y = x) : y = t x :=
    (hex x).choose_spec.2 y ⟨hyroot, hyred⟩
  have htzero : t 0 = 0 := by
    symm
    apply htunique 0 0
    · exact zero_pow Fintype.card_ne_zero
    · exact map_zero φ
  have htone : t 1 = 1 := by
    symm
    apply htunique 1 1
    · simp
    · exact map_one φ
  have htmul (x y : k) : t (x * y) = t x * t y := by
    symm
    apply htunique (x * y) (t x * t y)
    · rw [mul_pow, htroot, htroot]
    · rw [map_mul, htred, htred]
  let lift : k →*₀ R :=
    { toFun := t
      map_one' := htone
      map_mul' := htmul
      map_zero' := htzero }
  refine ⟨{
    lift := lift
    reduction := ?_
    pow_card := ?_
    unique := ?_
  }⟩
  · intro x
    change φ (t x) = x
    exact htred x
  · intro x
    change t x ^ Nat.card k = t x
    simpa [Nat.card_eq_fintype_card] using htroot x
  · intro x y hyroot hyred
    change y = t x
    apply htunique x y
    · simpa [Nat.card_eq_fintype_card] using hyroot
    · exact hyred

/-- The nonzero roots of `X ^ |k| - X` in the coefficient ring, expressed
as units so that they can index multiplicative character sums. -/
def MultiplicativeResidueRoots
    (U : UnramifiedCoefficientLift p k) :=
  {u : (AdjoinRoot U.polynomial)ˣ //
    (u : AdjoinRoot U.polynomial) ^ Nat.card k = u}

/-- Reduction identifies the nonzero Hensel roots with `kˣ`. -/
noncomputable def multiplicativeResidueRootEquiv
    (U : UnramifiedCoefficientLift p k)
    (D : MultiplicativeResidueLift p k U) :
    kˣ ≃ MultiplicativeResidueRoots p k U where
  toFun x := ⟨Units.map D.lift.toMonoidHom x, by
    change D.lift (x : k) ^ Nat.card k = D.lift (x : k)
    exact D.pow_card (x : k)⟩
  invFun u := Units.map (coefficientResidueMap p k U).toMonoidHom u.1
  left_inv x := by
    apply Units.ext
    change coefficientResidueMap p k U (D.lift (x : k)) = x
    exact D.reduction (x : k)
  right_inv u := by
    apply Subtype.ext
    apply Units.ext
    change D.lift (coefficientResidueMap p k U (u.1 : AdjoinRoot U.polynomial)) =
      (u.1 : AdjoinRoot U.polynomial)
    exact (D.unique _ (u.1 : AdjoinRoot U.polynomial) u.property rfl).symm

/-- The finite indexing set `kˣ`, with its `Fintype` chosen from finiteness. -/
noncomputable def multiplicativeResidueUnits : Finset kˣ := by
  letI : Fintype kˣ := Fintype.ofFinite kˣ
  exact Finset.univ

/-- The injective map sending a nonzero residue to its Teichmüller
representative. -/
noncomputable def multiplicativeResidueEmbedding
    (U : UnramifiedCoefficientLift p k)
    (D : MultiplicativeResidueLift p k U) :
    kˣ ↪ AdjoinRoot U.polynomial where
  toFun x := D.lift (x : k)
  inj' x y hxy := by
    apply Units.ext
    calc
      (x : k) = coefficientResidueMap p k U (D.lift (x : k)) :=
        (D.reduction (x : k)).symm
      _ = coefficientResidueMap p k U (D.lift (y : k)) := congrArg _ hxy
      _ = (y : k) := D.reduction (y : k)

/-- The finite set of nonzero Teichmüller representatives in the coefficient
ring. -/
noncomputable def multiplicativeResidueRootsFinset
    (U : UnramifiedCoefficientLift p k)
    (D : MultiplicativeResidueLift p k U) :
    Finset (AdjoinRoot U.polynomial) := by
  exact (multiplicativeResidueUnits k).map
    (multiplicativeResidueEmbedding p k U D)

/-- A sum over the nonzero Hensel roots is the corresponding finite-field
unit sum after the canonical multiplicative lift. -/
theorem sum_multiplicativeResidueRoots
    (U : UnramifiedCoefficientLift p k)
    (D : MultiplicativeResidueLift p k U)
    {A : Type*} [AddCommMonoid A]
    (F : AdjoinRoot U.polynomial → A) :
    (∑ y ∈ multiplicativeResidueRootsFinset p k U D, F y) =
      ∑ x ∈ multiplicativeResidueUnits k, F (D.lift (x : k)) := by
  exact Finset.sum_map (multiplicativeResidueUnits k)
    (multiplicativeResidueEmbedding p k U D) F

end

end LanglandsSecondMainLemma.Gauss
