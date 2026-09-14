import LanglandsFirstMainLemma.Delta.ResidueFormula
import LanglandsFirstMainLemma.Ramification.NormBelowBreak
import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace
import LanglandsFirstMainLemma.FiniteField.HasseFunction
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.MinimalFunctions
import LanglandsSecondMainLemma.Finite.MissingCoset

/-!
# Equal nonmaximal breaks: residue scalars and cancellation

Paper `D:NM:minimal-one` (Proposition 13.12), with arbitrary last-layer
additive coefficient `gamma`. The finite lemmas retain the complete
Hasse functions and prove the missing-coset cancellation.

The actual critical norm coefficients and full Lamprecht Hasse functions
are constructed over one common residue field, on the same source lift.
Their distinct kernels and common full function determine both the
translation value and its nontrivial polar character on the missing coset.
This supplies a direct cancellation proof without a second construction
of the critical polar-trace scalar. The residue lemmas also retain the
explicit, non-normalized scalar and lower norm-annihilation formulas.

`equalBreaks` assembles the complete canonical local constants from the
proved minimal-origin sides and restores the original additive character.
-/

namespace LanglandsSecondMainLemma.Dyadic.Nonmaximal
noncomputable section
open LanglandsFirstMainLemma
open scoped BigOperators

section ResidueFields
variable (k : Type*) [Field k] [Fintype k] [CharP k 2]
local instance : Algebra (ZMod 2) k := ZMod.algebra k 2

/-- The characteristic-two critical norm polynomial, with its linear term. -/
def equalBreakNormPolynomial (c u : k) : k →+ k where
  toFun v := v ^ 2 + (c / u) * v
  map_zero' := by simp
  map_add' x y := by simp only [CharTwo.add_sq, mul_add]; ring

omit [Fintype k] in
@[simp] theorem equalBreakNormPolynomial_apply (c u v : k) :
    equalBreakNormPolynomial k c u v = v ^ 2 + (c / u) * v := rfl

omit [Fintype k] in
/-- The two-element kernel is retained at the critical depth. -/
theorem equalBreakNormPolynomial_eq_zero (c u v : k) :
    equalBreakNormPolynomial k c u v = 0 ↔ v = 0 ∨ v = c / u := by
  rw [equalBreakNormPolynomial_apply,
    show v ^ 2 + c / u * v = v * (v + c / u) by ring, mul_eq_zero,
    CharTwo.add_eq_zero]

omit [Fintype k] in
/-- Counting the actual two roots of the residual norm polynomial. -/
theorem equalBreakNormPolynomial_card_ker {c u : k} (hc : c ≠ 0) (hu : u ≠ 0) :
    Nat.card (equalBreakNormPolynomial k c u).ker = 2 := by
  classical
  let z : (equalBreakNormPolynomial k c u).ker := ⟨0, by simp⟩
  let w : (equalBreakNormPolynomial k c u).ker := ⟨c / u, by
    change equalBreakNormPolynomial k c u (c / u) = 0
    exact (equalBreakNormPolynomial_eq_zero k c u _).mpr (Or.inr rfl)⟩
  apply Nat.card_eq_two_iff.mpr
  refine ⟨z, w, ?_, ?_⟩
  · intro h
    have h' := congrArg Subtype.val h
    exact (div_ne_zero hc hu) h'.symm
  · ext v
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    have hv := (equalBreakNormPolynomial_eq_zero k c u (v : k)).mp v.property
    exact hv.imp (fun h ↦ Subtype.ext h) (fun h ↦ Subtype.ext h)

/-- The image has index two, not full residue-field cardinality. -/
theorem equalBreakNormPolynomial_index {c u : k} (hc : c ≠ 0) (hu : u ≠ 0) :
    (equalBreakNormPolynomial k c u).range.index = 2 := by
  rw [AddSubgroup.index_range, equalBreakNormPolynomial_card_ker k hc hu]

/-- FML's scaled Artin--Schreier theorem gives the exact image hyperplane. -/
theorem equalBreakNormPolynomial_mem_range {c u : k} (hc : c ≠ 0) (hu : u ≠ 0)
    (x : k) :
    x ∈ (equalBreakNormPolynomial k c u).range ↔
      absoluteTraceTwo k (u ^ 2 * x / c ^ 2) = 0 := by
  let lam := c / u
  have hlam : lam ≠ 0 := div_ne_zero hc hu
  have hr := finiteField_scaledFrobeniusSub_range_eq_scaledTraceKer
    k 2 (ringChar.eq k 2) lam hlam
  have hr' : Set.range (equalBreakNormPolynomial k c u) =
      Set.range (fun y : (absoluteTraceTwo k).ker ↦ lam ^ 2 * (y : k)) := by
    simpa only [Nat.reduceSub, pow_one, CharTwo.sub_eq_add, equalBreakNormPolynomial,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk, lam] using hr
  change x ∈ Set.range (equalBreakNormPolynomial k c u) ↔ _
  rw [hr']
  constructor
  · rintro ⟨y, rfl⟩
    convert (show absoluteTraceTwo k (y : k) = 0 from y.property) using 1
    dsimp [lam]
    congr 1
    field_simp
  · intro hx
    refine ⟨⟨u ^ 2 * x / c ^ 2, hx⟩, ?_⟩
    dsimp [lam]
    field_simp

/-- Whole-field trace duality determines the linear coefficient of a
quadratic polynomial annihilated by the actual additive character. -/
theorem equalBreaks_lowerScalar {gamma s c eta : k}
    (hs : s ^ 2 = gamma) (hs0 : s ≠ 0) (hc : c ≠ 0)
    (hann : ∀ v : k, absoluteTraceTwo k (gamma * c ^ 2 * (v ^ 2 + eta * v)) = 0) :
    eta = (s * c)⁻¹ := by
  have htrace (v : k) : absoluteTraceTwo k
      ((s * c + gamma * c ^ 2 * eta) * v) = 0 := by
    calc
      _ = absoluteTraceTwo k (s * c * v) +
          absoluteTraceTwo k (gamma * c ^ 2 * eta * v) := by rw [add_mul, map_add]
      _ = absoluteTraceTwo k ((s * c * v) ^ 2) +
          absoluteTraceTwo k (gamma * c ^ 2 * eta * v) := by rw [absoluteTraceTwo_sq]
      _ = absoluteTraceTwo k (gamma * c ^ 2 * (v ^ 2 + eta * v)) := by
        rw [← map_add, mul_pow, mul_pow, hs]
        congr 1
        ring
      _ = 0 := hann v
  have hz : s * c + gamma * c ^ 2 * eta = 0 := by
    by_contra hne
    obtain ⟨v, hv⟩ := exists_absoluteTraceTwo_mul_eq_one k hne
    exact one_ne_zero (hv.symm.trans (htrace v))
  have hcoeff : gamma * c ^ 2 * eta = s * c :=
    (CharTwo.add_eq_zero.mp hz).symm
  rw [← hs] at hcoeff
  apply (mul_left_cancel₀ (mul_ne_zero hs0 hc))
  have heq : (s * c) * ((s * c) * eta) = (s * c) * 1 := by
    simpa only [mul_one] using (show (s * c) * ((s * c) * eta) = s * c by
      convert hcoeff using 1; ring)
  have hunit := mul_left_cancel₀ (mul_ne_zero hs0 hc) heq
  rw [hunit, mul_inv_cancel₀ (mul_ne_zero hs0 hc)]

/-- The non-normalized coefficient fixes `u² = √gamma c₁c₂c₃`. -/
theorem equalBreaks_scalarIdentity {gamma u c d e : k}
    (hgamma : gamma ≠ 0) (hu : u ≠ 0) (hc : c ≠ 0)
    (hann : ∀ v : k,
      absoluteTraceTwo k (gamma * c ^ 2 * (v ^ 2 + (d * e / u ^ 2) * v)) = 0) :
    ∃ s : k, s ^ 2 = gamma ∧ s ≠ 0 ∧
      d * e / u ^ 2 = (s * c)⁻¹ ∧ u ^ 2 = s * (c * d * e) := by
  obtain ⟨s, hs, _⟩ := existsUnique_squareRoot k gamma
  have hs0 : s ≠ 0 := fun h ↦ hgamma (by rw [← hs, h]; simp)
  have heta := equalBreaks_lowerScalar k hs hs0 hc hann
  refine ⟨s, hs, hs0, heta, ?_⟩
  have heq := congrArg (fun z : k ↦ s * c * z) heta
  rw [mul_inv_cancel₀ (mul_ne_zero hs0 hc)] at heq
  field_simp at heq
  linear_combination -heq

/-- The actual additive character is represented without normalizing its
nonzero scalar to one. -/
theorem equalBreaks_additiveCoefficient (psi : FiniteAddChar k) (hpsi : psi ≠ 1) :
    ∃! gamma : k, gamma ≠ 0 ∧ (absoluteTraceChar k).mulShift gamma = psi := by
  obtain ⟨gamma, hgamma, huniq⟩ := existsUnique_absoluteTraceChar_mulShift k psi
  refine ⟨gamma, ⟨?_, hgamma⟩, fun d hd ↦ huniq d hd.2⟩
  intro hz
  rw [hz, AddChar.mulShift_zero] at hgamma
  exact hpsi hgamma.symm

omit [Fintype k] in
private theorem traceChar_cases (x : k) :
    absoluteTraceChar k x = if absoluteTraceTwo k x = 0 then 1 else -1 := by
  rw [absoluteTraceChar_apply]
  have hz : absoluteTraceTwo k x ^ 2 = absoluteTraceTwo k x :=
    ZMod.pow_card (absoluteTraceTwo k x)
  rcases eq_zero_or_one_of_sq_eq_self hz with hz | hz
  · rw [hz, ZMod.val_zero, pow_zero, if_pos rfl]
  · rw [hz, ZMod.val_one, pow_one, if_neg one_ne_zero]

/-- The polar bicharacter, with values in units for `Finite.missingCoset`. -/
def equalBreakPolar (A : k) : AddChar k (AddChar k ℂˣ) where
  toFun x :=
    { toFun y := Units.mk0 (absoluteTraceChar k (A * x * y))
        ((absoluteTraceChar k).val_isUnit _).ne_zero
      map_zero_eq_one' := by apply Units.ext; simp
      map_add_eq_mul' y z := by
        apply Units.ext
        simp only [Units.val_mk0, Units.val_mul, mul_add, AddChar.map_add_eq_mul] }
  map_zero_eq_one' := by
    apply AddChar.ext
    intro y
    apply Units.ext
    change absoluteTraceChar k (A * 0 * y) = 1
    simp
  map_add_eq_mul' x y := by
    apply AddChar.ext
    intro z
    apply Units.ext
    change absoluteTraceChar k (A * (x + y) * z) =
      absoluteTraceChar k (A * x * z) * absoluteTraceChar k (A * y * z)
    rw [mul_add, add_mul, AddChar.map_add_eq_mul]

omit [Fintype k] in
@[simp] theorem equalBreakPolar_apply (A x y : k) :
    (equalBreakPolar k A x y : ℂ) = absoluteTraceChar k (A * x * y) := rfl

omit [Fintype k] in
/-- The other ramification kernel gives the required translation point. -/
theorem equalBreaks_translation (c d e u : k) (hcde : c + d = e) :
    equalBreakNormPolynomial k c u (d / u) = d * e / u ^ 2 := by
  rw [equalBreakNormPolynomial_apply, ← hcde]
  by_cases hu : u = 0
  · simp [hu]
  · field_simp
    ring

omit [Fintype k] [CharP k 2] in
/-- Every scalar in the polar character is fixed by the lower norm chart. -/
theorem equalBreaks_polarCoefficient {gamma s c d e u : k}
    (hs : s ^ 2 = gamma) (hscalar : u ^ 2 = s * (c * d * e))
    (hc : c ≠ 0) (hu : u ≠ 0) :
    gamma * (d * e) * (d * e / u ^ 2) = u ^ 2 / c ^ 2 := by
  have hfour : u ^ 4 = gamma * (c * d * e) ^ 2 := by
    calc
      u ^ 4 = (u ^ 2) ^ 2 := by ring
      _ = (s * (c * d * e)) ^ 2 := congrArg (fun z : k ↦ z ^ 2) hscalar
      _ = gamma * (c * d * e) ^ 2 := by rw [mul_pow, hs]
  field_simp
  linear_combination -hfour

/-- The polar character at the translation point is one precisely on
the norm image, and is minus one on the entire missing coset. -/
theorem equalBreaks_polarDetect {gamma s c d e u : k}
    (hs : s ^ 2 = gamma) (hscalar : u ^ 2 = s * (c * d * e))
    (hc : c ≠ 0) (hu : u ≠ 0) (x : k) :
    (x ∈ (equalBreakNormPolynomial k c u).range →
      equalBreakPolar k (gamma * (d * e)) (d * e / u ^ 2) x = 1) ∧
    (x ∉ (equalBreakNormPolynomial k c u).range →
      equalBreakPolar k (gamma * (d * e)) (d * e / u ^ 2) x = -1) := by
  have hcoef := equalBreaks_polarCoefficient k hs hscalar hc hu
  have hval : (equalBreakPolar k (gamma * (d * e)) (d * e / u ^ 2) x : ℂ) =
      if absoluteTraceTwo k (u ^ 2 * x / c ^ 2) = 0 then 1 else -1 := by
    rw [equalBreakPolar_apply, hcoef,
      show u ^ 2 / c ^ 2 * x = u ^ 2 * x / c ^ 2 by ring, traceChar_cases]
  constructor
  · intro hx
    apply Units.ext
    rw [hval, if_pos ((equalBreakNormPolynomial_mem_range k hc hu x).mp hx)]
    rfl
  · intro hx
    apply Units.ext
    rw [hval, if_neg (fun h ↦ hx ((equalBreakNormPolynomial_mem_range k hc hu x).mpr h))]
    rfl

omit [Fintype k] in
/-- The full common function fixes the translation's value, including
the affine part of the Hasse function. -/
theorem equalBreaks_translationValue {c d e u : k} (hcde : c + d = e)
    (H J : k → ℂ) (hJ : J 0 = 1)
    (hcommon : ∀ v : k,
      H (equalBreakNormPolynomial k c u v) = J (equalBreakNormPolynomial k d u v)) :
    H (d * e / u ^ 2) = 1 := by
  rw [← equalBreaks_translation k c d e u hcde, hcommon,
    (equalBreakNormPolynomial_eq_zero k d u _).mpr (Or.inr rfl), hJ]

/-- Finite end of `D:NM:minimal-one`: every missing-coset hypothesis is
proved from the displayed scalar, full common-function and polar formulas.
This lemma does not assert that arbitrary finite data come from local fields. -/
theorem equalBreaks_residualSum {gamma s c d e u : k}
    (hs : s ^ 2 = gamma) (hscalar : u ^ 2 = s * (c * d * e))
    (hc : c ≠ 0) (hu : u ≠ 0) (hcde : c + d = e)
    (H : HasseFunction k ((absoluteTraceChar k).mulShift (gamma * (d * e))))
    (J : k → ℂ) (hJ : J 0 = 1)
    (hcommon : ∀ v : k,
      H (equalBreakNormPolynomial k c u v) = J (equalBreakNormPolynomial k d u v)) :
    (∑ x : k, H x) = ((1 : ℂ) / 2) *
      ∑ v : k, H (equalBreakNormPolynomial k c u v) := by
  let p := equalBreakNormPolynomial k c u
  let Hu : k → ℂˣ := fun x ↦ Units.mk0 (H x) (H.ne_zero x)
  let Q : k → ℂˣ := fun v ↦ Hu (p v)
  let w := d * e / u ^ 2
  have hw : Hu w = 1 := by
    apply Units.ext
    exact equalBreaks_translationValue k hcde H J hJ hcommon
  have hw_mem : w ∈ p.range :=
    ⟨d / u, equalBreaks_translation k c d e u hcde⟩
  have hpolar (x y : k) :
      Hu (x + y) = equalBreakPolar k (gamma * (d * e)) x y * Hu x * Hu y := by
    apply Units.ext
    dsimp only [Hu]
    simp only [Units.val_mk0, Units.val_mul, equalBreakPolar_apply, H.map_add,
      AddChar.mulShift_apply]
    simp only [mul_comm, mul_left_comm]
  exact Finite.missingCoset Hu (equalBreakPolar k (gamma * (d * e))) Q p w
    (by apply Units.ext; exact H.map_zero) hpolar
    (equalBreakNormPolynomial_card_ker k hc hu)
    (equalBreakNormPolynomial_index k hc hu) (fun _ ↦ rfl) hw_mem hw
    (equalBreaks_polarDetect k hs hscalar hc hu)

/-- The three residue sums coincide for arbitrary non-normalized additive
coefficient `gamma`. Its scalar identity is deduced from whole-field lower
norm annihilation, rather than included as an additional assumption. -/
theorem equalBreaks_threeResidualSums {gamma c d e u : k}
    (hgamma : gamma ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hu : u ≠ 0)
    (hcde : c + d = e)
    (hann : ∀ v : k,
      absoluteTraceTwo k (gamma * c ^ 2 * (v ^ 2 + (d * e / u ^ 2) * v)) = 0)
    (H : HasseFunction k ((absoluteTraceChar k).mulShift (gamma * (d * e))))
    (J : HasseFunction k ((absoluteTraceChar k).mulShift (gamma * (c * e))))
    (M : HasseFunction k ((absoluteTraceChar k).mulShift (gamma * (c * d))))
    (hHJ : ∀ v : k,
      H (equalBreakNormPolynomial k c u v) = J (equalBreakNormPolynomial k d u v))
    (hHM : ∀ v : k,
      H (equalBreakNormPolynomial k c u v) = M (equalBreakNormPolynomial k e u v)) :
    (∑ x : k, H x) = ∑ x : k, J x ∧ (∑ x : k, H x) = ∑ x : k, M x := by
  obtain ⟨s, hs, _, _, hscalar⟩ := equalBreaks_scalarIdentity k hgamma hu hc hann
  have hH := equalBreaks_residualSum k hs hscalar hc hu hcde H J J.map_zero hHJ
  have hscalarJ : u ^ 2 = s * (d * c * e) := by rw [hscalar]; ring
  have hJ := equalBreaks_residualSum k hs hscalarJ hd hu
    (by rw [add_comm]; exact hcde) J H H.map_zero (fun v ↦ (hHJ v).symm)
  have hscalarM : u ^ 2 = s * (e * c * d) := by rw [hscalar]; ring
  have hecd : e + c = d := by
    rw [← hcde, add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  have hM := equalBreaks_residualSum k hs hscalarM he hu hecd M H H.map_zero
    (fun v ↦ (hHM v).symm)
  refine ⟨?_, ?_⟩
  · rw [hH, hJ]
    congr 1
    exact Fintype.sum_congr _ _ hHJ
  · rw [hH, hM]
    congr 1
    exact Fintype.sum_congr _ _ hHM

/-- The full common function determines the missing-coset character directly.
The second critical kernel supplies the translation, and nondegeneracy of
the actual polar character rules out the trivial character on the quotient. -/
theorem equalBreaks_hasseCancellation {a b : k} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (rho : FiniteAddChar k) (hrho : rho ≠ 1)
    (H : HasseFunction k rho) (J : k → ℂ) (hJ : J 0 = 1)
    (hcommon : ∀ v, H (equalBreakNormPolynomial k a 1 v) =
      J (equalBreakNormPolynomial k b 1 v)) :
    (∑ x : k, H x) = ((1 : ℂ) / 2) *
      ∑ v : k, H (equalBreakNormPolynomial k a 1 v) := by
  obtain ⟨A, ⟨hA, hArho⟩, _⟩ := equalBreaks_additiveCoefficient k rho hrho
  let p := equalBreakNormPolynomial k a 1
  let q := equalBreakNormPolynomial k b 1
  let w := p b
  have hqb : q b = 0 := by
    simp [q, equalBreakNormPolynomial, pow_two, CharTwo.add_self_eq_zero]
  have hw0 : w ≠ 0 := by
    intro hw
    rcases (equalBreakNormPolynomial_eq_zero k a 1 b).mp hw with hz | hz
    · exact hb hz
    · exact hab (by simpa using hz.symm)
  have hw : H w = 1 := by rw [show H w = J (q b) from hcommon b, hqb, hJ]
  have hpolar (x y : k) :
      (equalBreakPolar k A x y : ℂ) = rho (x * y) := by
    rw [equalBreakPolar_apply, ← hArho, AddChar.mulShift_apply, mul_assoc]
  have hann (x : k) (hx : x ∈ p.range) : rho (w * x) = 1 := by
    obtain ⟨v, rfl⟩ := hx
    have hshift : H (w + p v) = H (p v) := by
      rw [show w + p v = p (b + v) from (map_add p b v).symm,
        hcommon, map_add q, hqb, zero_add, ← hcommon]
    rw [H.map_add, hw, one_mul] at hshift
    exact (mul_left_cancel₀ (H.ne_zero (p v))) (hshift.trans (mul_one _).symm)
  have hindex : p.range.index = 2 := equalBreakNormPolynomial_index k ha one_ne_zero
  have hdetect (x : k) : (x ∈ p.range → equalBreakPolar k A w x = 1) ∧
      (x ∉ p.range → equalBreakPolar k A w x = -1) := by
    constructor
    · intro hx
      apply Units.ext
      exact (hpolar w x).trans (hann x hx)
    · intro hx
      have hne : rho (w * x) ≠ 1 := by
        intro heq
        obtain ⟨z, hz⟩ := exists_absoluteTraceChar_mul_ne_one k (mul_ne_zero hA hw0)
        have hz' : rho (w * z) ≠ 1 := by
          simpa only [← hArho, AddChar.mulShift_apply, mul_assoc] using hz
        have hzmem : z ∉ p.range := fun h ↦ hz' (hann z h)
        have hxz : x + z ∈ p.range :=
          (p.range.add_mem_iff_of_index_two hindex).mpr ⟨fun h ↦ (hx h).elim,
            fun h ↦ (hzmem h).elim⟩
        have h := hann (x + z) hxz
        rw [mul_add, AddChar.map_add_eq_mul, heq, one_mul] at h
        exact hz' h
      have hsq : rho (w * x) ^ 2 = 1 := by
        rw [pow_two, ← AddChar.map_add_eq_mul, CharTwo.add_self_eq_zero,
          AddChar.map_zero_eq_one]
      apply Units.ext
      exact (hpolar w x).trans ((sq_eq_one_iff.mp hsq).resolve_left hne)
  let Hu : k → ℂˣ := fun x ↦ Units.mk0 (H x) (H.ne_zero x)
  apply Finite.missingCoset Hu (equalBreakPolar k A) (fun v ↦ Hu (p v)) p w
    (by apply Units.ext; exact H.map_zero) _
    (equalBreakNormPolynomial_card_ker k ha one_ne_zero) hindex (fun _ ↦ rfl)
    ⟨b, rfl⟩ (by apply Units.ext; exact hw) hdetect
  intro x y
  apply Units.ext
  change H (x + y) = (equalBreakPolar k A x y : ℂ) * H x * H y
  rw [H.map_add, hpolar]
  ring

/-- Distinct critical kernels and the complete common function identify
the two actual Hasse sums, with no choice of polar normalization. -/
theorem equalBreaks_hasseComparison {a b : k} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (rho sigma : FiniteAddChar k) (hrho : rho ≠ 1) (hsigma : sigma ≠ 1)
    (H : HasseFunction k rho) (J : HasseFunction k sigma)
    (hcommon : ∀ v, H (equalBreakNormPolynomial k a 1 v) =
      J (equalBreakNormPolynomial k b 1 v)) :
    (∑ x : k, H x) = ∑ x : k, J x := by
  rw [equalBreaks_hasseCancellation k ha hb hab rho hrho H J J.map_zero hcommon,
    equalBreaks_hasseCancellation k hb ha hab.symm sigma hsigma J H H.map_zero
      (fun v ↦ (hcommon v).symm)]
  congr 1
  exact Fintype.sum_congr _ _ hcommon

end ResidueFields
section LastLayer
variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [CharP (ResidueField E) 2]

/-- Construct the manuscript's arbitrary nonzero additive coefficient from
FML's actual last-layer character, and evaluate it on every integral lift. -/
theorem equalBreaks_lastLayerCoefficient
    (Psi : LocalAddCharData E) (t : ℕ) (hPsi : Psi.conductor = -((t : ℤ) + 1))
    (pi : Eˣ) (hpi : ord E (pi : E) = 1) :
    ∃ gamma : ResidueField E, gamma ≠ 0 ∧
      ∀ v : ringOfIntegers E,
        (Psi.character ((pi : E) ^ t * (v : E)) : ℂ) =
          absoluteTraceChar (ResidueField E) (gamma * residueMap E v) := by
  letI := residueFieldFintype E
  let D : Eˣ := (pi ^ t)⁻¹
  have hpit : ord E ((pi : E) ^ t) = ((t : ℤ) : WithTop ℤ) := by
    rw [ord_pow, hpi]
    norm_cast
    simp
  have hD : ord E (D : E) = ((Psi.conductor + 1 : ℤ) : WithTop ℤ) := by
    simp only [D, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, ord_inv, hpit]
    rw [hPsi]
    change ((-(t : ℤ) : ℤ) : WithTop ℤ) = _
    congr 1
    omega
  obtain ⟨gamma, ⟨hgamma, hchar⟩, _⟩ := equalBreaks_additiveCoefficient
    (ResidueField E) (residualAddChar E Psi D hD) (residualAddChar_ne_one E Psi D hD)
  refine ⟨gamma, hgamma, ?_⟩
  intro v
  have hv := residualAddChar_integral_lift E Psi D hD (v : E)
    ((mem_lattice_zero_iff E).mpr v.property)
  rw [← hchar, AddChar.mulShift_apply] at hv
  rw [reduce_mk] at hv
  rw [hv]
  congr 2
  simp only [D, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    div_inv_eq_mul, mul_comm]

end LastLayer

section CriticalNorm
variable (E M : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra E M] [ValuativeExtension E M] [Module.Finite E M]
  [Algebra.IsQuadraticExtension E M] [PrimeCyclicExtension E M]

/-- FML fixes both coefficients of the actual quadratic critical norm;
the characteristic-two residue field follows from the positive break. -/
theorem equalBreaks_criticalNormPolynomial
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak E M t) (htpos : 0 < t)
    (hres : residueDegree E M = 1) (pi : ringOfIntegers M)
    (hpi : (ValuativeRel.valuation M).IsUniformizer (pi : M))
    (hgen : Algebra.adjoin (ringOfIntegers E) ({pi} : Set (ringOfIntegers M)) = ⊤)
    (x : ResidueField E) :
    criticalNormPolynomialValue E M ht htpos hres pi hpi hgen x =
      x ^ 2 + criticalNormRamificationLambda E M ht hres pi hpi * x := by
  have hchar : residueCharacteristic E = 2 := by
    rw [residueCharacteristic_eq_degree_of_positive_break E M ht htpos pi hpi hgen,
      Algebra.IsQuadraticExtension.finrank_eq_two E M]
  letI : CharP (ResidueField E) 2 := by rw [← hchar]; infer_instance
  simpa only [Algebra.IsQuadraticExtension.finrank_eq_two E M,
    Nat.reduceSub, pow_one, CharTwo.sub_eq_add] using
    criticalNormPolynomialValue_exact_of_positiveBreak E M ht htpos hres pi hpi hgen x

end CriticalNorm

section ActualCoordinate
variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  (L : IntermediateField F K)
attribute [local instance] Basic.intermediateFieldValuativeRel
  Basic.intermediateFieldTopology Basic.intermediateField_localField
  Basic.intermediateField_lowerValuativeExtension Basic.intermediateField_upperValuativeExtension
variable [Algebra.IsQuadraticExtension L K] [PrimeCyclicExtension L K]

/-- The coordinate exported by `MinimalFunctions` is FML's actual critical
norm polynomial on a canonical source lift. The trace term is retained. -/
theorem equalBreaks_criticalCoordinate
    {q r t : ℕ} {w : ℤ} {C : Kˣ} {hC : trace L K (C : K) ≠ 0}
    (ht : PrimeCyclicExtension.IsLowerBreak L K t) (htpos : 0 < t)
    (hres : residueDegree L K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers L) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (delta : Lˣ) (hdelta : ord L (delta : L) = ((t : ℤ) : WithTop ℤ))
    (hdelta_val : (delta : L) = criticalNormLowerUniformizer L K pi ^ t)
    (x : ResidueField L)
    (V : MinimalFunctionLift L q t r w C
      (minimalFunctionPoint C t htpos (criticalNormSourceDisplacement L K t pi hpi x)) hC) :
    minimalCriticalCoordinate L delta hdelta V.upper =
      x ^ 2 + criticalNormRamificationLambda L K ht hres pi hpi * x := by
  rw [← equalBreaks_criticalNormPolynomial L K ht htpos hres pi hpi hgen x,
    criticalNormPolynomialValue_raw, minimalCriticalCoordinate]
  congr 1
  rw [V.upper_value L htpos, hdelta_val]
  rfl

end ActualCoordinate

section Hasse
variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

open private normalizedStationaryNumerator normalizedStationaryNumerator_coe
  normalizedStationaryNumerator_represents normalizedResidualFunction_eq_lamprecht from
  LanglandsSecondMainLemma.Stationary.NormalizedFactor

/-- The full normalized residual function is a constructed Hasse function.
Its nontrivial polar character is evaluated on every integral lift using
the actual stationary numerator and admissible denominator. -/
theorem equalBreaks_residualHasse
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E) (alpha Z : Eˣ)
    (d : ℕ) (hm : theta.conductor = 2 * d + 1) (hlarge : 1 < theta.conductor)
    (hZ : ord E (Z : E) =
      ((-(scaleAddCharData E psi alpha).conductor - (theta.conductor : ℤ) : ℤ) : WithTop ℤ))
    (hstationary : Stationary.IsNormalizedStationaryCoefficientAtDepth E theta
      (scaleAddCharData E psi alpha) Z (d + 1)
      (lamprechtFormula_stationaryDepth E theta d 1 (by omega) hm hlarge).pos)
    (delta : Eˣ) (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ)) :
    ∃ (rho : FiniteAddChar (ResidueField E)) (H : HasseFunction (ResidueField E) rho),
      rho ≠ 1 ∧
      (∀ x, Stationary.normalizedResidualFunction E theta psi alpha Z d hm hlarge
        delta hdelta x = H x) ∧
      ∀ v : ringOfIntegers E, rho (residueMap E v) =
        ((scaleAddCharData E psi alpha).character
          (-(Z : E) * (delta : E) ^ 2 * (v : E)) : ℂ) := by
  let Gamma : AdmissibleGamma E theta psi :=
    Classical.choice (AdmissibleGamma.exists_admissible (F := E))
  let c := normalizedStationaryNumerator E theta psi alpha Z Gamma hZ
  have hc := normalizedStationaryNumerator_represents E theta psi alpha Z
    d 1 (by omega) hm hlarge Gamma hZ hstationary
  let rho := lamprechtResidualAddChar E theta psi d hm hlarge Gamma delta hdelta
  let H := lamprechtHasseFunction E theta psi d hm hlarge Gamma delta hdelta c hc
  refine ⟨rho, H,
    lamprechtResidualAddChar_ne_one E theta psi d hm hlarge Gamma delta hdelta c hc,
    normalizedResidualFunction_eq_lamprecht E theta psi alpha Z d hm hlarge Gamma
      hZ hstationary delta hdelta, ?_⟩
  intro v
  have hv := lamprechtResidualAddChar_integral_lift E theta psi d hm hlarge
    Gamma delta hdelta c hc (v : E) ((mem_lattice_zero_iff E).mpr v.property)
  rw [reduce_mk] at hv
  change lamprechtResidualAddChar E theta psi d hm hlarge Gamma delta hdelta
    (residueMap E v) = _
  rw [hv, scaleAddCharData_character_apply]
  congr 2
  dsimp only [c]
  rw [normalizedStationaryNumerator_coe]
  field_simp

end Hasse

section LowerAnnihilation
variable (E M : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra E M] [ValuativeExtension E M] [Module.Finite E M]
  [Algebra.IsQuadraticExtension E M] [PrimeCyclicExtension E M]
  [CharP (ResidueField E) 2]

/-- Triviality on actual critical norms gives the whole-residue-field
annihilation equation used to determine the scalar. No critical norm
surjectivity or exact preimage of a prescribed target is assumed. -/
theorem equalBreaks_lowerNormAnnihilation
    {q t : ℕ} (hqt : q ≤ t)
    (ht : PrimeCyclicExtension.IsLowerBreak E M t) (htpos : 0 < t)
    (hres : residueDegree E M = 1) (piM : ringOfIntegers M)
    (hpiM : (ValuativeRel.valuation M).IsUniformizer (piM : M))
    (hgen : Algebra.adjoin (ringOfIntegers E) ({piM} : Set (ringOfIntegers M)) = ⊤)
    (pi : Eˣ) (hpi : ord E (pi : E) = 1)
    (hpi_val : (pi : E) = criticalNormLowerUniformizer E M piM)
    (omega : NormCharacter E M) (Psi : LocalAddCharData E) (beta : ringOfIntegers E)
    (hlower : ∀ v ∈ lattice E (q : ℤ), ∀ B : Eˣ, (B : E) = 1 - v →
      omega.1 B = Psi.character ((beta : E) * v))
    (gamma : ResidueField E)
    (hgamma : ∀ v : ringOfIntegers E,
      (Psi.character ((pi : E) ^ t * (v : E)) : ℂ) =
        absoluteTraceChar (ResidueField E) (gamma * residueMap E v))
    (x : ResidueField E) :
    absoluteTraceTwo (ResidueField E)
      (gamma * residueMap E beta *
        (x ^ 2 + criticalNormRamificationLambda E M ht hres piM hpiM * x)) = 0 := by
  let U := criticalNormSourceUnit E M htpos piM hpiM x
  let B : Eˣ := normUnits E M (U : Mˣ)
  have hB : B ∈ unitFiltration E t :=
    normMapsUnitFiltration_atBreak E M ht hres piM hpiM hgen U U.property
  have hinc : (B : E) - 1 ∈ lattice E (t : ℤ) := by
    have hB' : B ∈ unitFiltration E (t - 1 + 1) := by
      simpa only [Nat.sub_add_cancel htpos] using hB
    simpa only [Nat.sub_add_cancel htpos] using
      (mem_unitFiltration_succ_iff_sub_mem_lattice E (t - 1) B).mp hB'
  have hnorm : omega.1 B = 1 :=
    omega.eq_one_on_normRange E M B ⟨(U : Mˣ), rfl⟩
  have hminus := hlower (-((B : E) - 1))
    (lattice_antitone E (by exact_mod_cast hqt) (neg_mem_lattice E hinc)) B (by ring)
  rw [hnorm] at hminus
  have hplus : Psi.character ((beta : E) * ((B : E) - 1)) = 1 := by
    have hsum := ContinuousAddChar.map_add_eq_mul Psi.character
      ((beta : E) * ((B : E) - 1)) ((beta : E) * -((B : E) - 1))
    rw [show (beta : E) * ((B : E) - 1) + (beta : E) * -((B : E) - 1) = 0 by ring,
      ← hminus] at hsum
    simpa using hsum.symm
  have hpit : ord E ((pi : E) ^ t) = ((t : ℤ) : WithTop ℤ) := by
    rw [ord_pow, hpi]
    norm_cast
    simp
  let z : lattice E 0 := ⟨((B : E) - 1) / (pi : E) ^ t,
    (div_mem_lattice_iff E _ _ (t : ℤ) 0 hpit).mpr (by simpa using hinc)⟩
  let zO : ringOfIntegers E := ⟨z, (mem_lattice_zero_iff E).mp z.property⟩
  have hBval : (B : E) = norm E M
      (1 + algebraMap E M ((teichmuller E x : ringOfIntegers E) : E) * (piM : M) ^ t) := by
    dsimp only [B]
    rw [coe_normUnits, coe_criticalNormSourceUnit]
  have hz : residueMap E zO =
      x ^ 2 + criticalNormRamificationLambda E M ht hres piM hpiM * x := by
    rw [← equalBreaks_criticalNormPolynomial E M ht htpos hres piM hpiM hgen x,
      criticalNormPolynomialValue_raw]
    change reduce E (((B : E) - 1) / (pi : E) ^ t) z.property = _
    congr 1
    rw [hBval, hpi_val]
  have hphase := hgamma (beta * zO)
  have harg : (pi : E) ^ t * ((beta * zO : ringOfIntegers E) : E) =
      (beta : E) * ((B : E) - 1) := by
    change (pi : E) ^ t * ((beta : E) * (((B : E) - 1) / (pi : E) ^ t)) = _
    field_simp
  rw [harg, hplus] at hphase
  simp only [Units.val_one, map_mul, hz, ← mul_assoc] at hphase
  rw [traceChar_cases] at hphase
  by_contra hne
  rw [if_neg hne] at hphase
  norm_num at hphase

end LowerAnnihilation

section Edge
variable (E M : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra E M] [ValuativeExtension E M] [Module.Finite E M]
  [Algebra.IsQuadraticExtension E M] [PrimeCyclicExtension E M]

open private norm_eq_self_mul_nontrivial trace_eq_self_add_nontrivial from
  LanglandsSecondMainLemma.Dyadic.Nonmaximal.Origin

/-- Reduction of an integral quadratic norm is the square of the upper
residue. The break hypothesis makes the Galois action on residues
trivial, and the residue-field embedding stays explicit. -/
theorem equalBreaks_normResidue
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak E M t)
    (a : ringOfIntegers M) :
    let hn : norm E M (a : M) ∈ lattice E 0 := by
      rw [mem_lattice, ord_norm]
      exact nsmul_nonneg ((mem_lattice_zero_iff M).mpr a.property) _
    extensionResidueMap E M (reduce E (norm E M (a : M)) hn) =
      residueMap M a ^ 2 := by
  dsimp only
  let sigma := PrimeCyclicExtension.generator E M
  let na : ringOfIntegers E := ⟨norm E M (a : M), by
    apply (mem_lattice_zero_iff E).mp
    rw [mem_lattice, ord_norm]
    exact nsmul_nonneg ((mem_lattice_zero_iff M).mpr a.property) _⟩
  have hsigma : sigma ∈ lowerRamificationGroup E M (t : ℤ) := by rw [ht.1]; trivial
  have hcong : residueMap M (galoisIntegerEquiv E M sigma a) = residueMap M a := by
    apply (residueMap_eq_residueMap_iff M _ _).mpr
    exact lattice_antitone M (by omega)
      ((mem_lowerRamificationGroup_iff_lattice E M sigma (t : ℤ)).mp hsigma a)
  have hnorm : algebraMap (ringOfIntegers E) (ringOfIntegers M) na =
      a * galoisIntegerEquiv E M sigma a := by
    apply Subtype.ext
    change algebraMap E M (norm E M (a : M)) = (a : M) * sigma (a : M)
    exact norm_eq_self_mul_nontrivial sigma (PrimeCyclicExtension.generator_ne_one E M)
      (by rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank,
        Algebra.IsQuadraticExtension.finrank_eq_two]) (a : M)
  change extensionResidueMap E M (residueMap E na) = _
  have hext : extensionResidueMap E M (residueMap E na) =
      residueMap M (algebraMap (ringOfIntegers E) (ringOfIntegers M) na) :=
    Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
      (ValuativeRel.valuation E) (ValuativeRel.valuation M) na
  rw [hext, hnorm, map_mul, hcong, pow_two]

/-- The upper conjugate difference is an integral unit and has the same
residue as the trace, since the exact error is `2C`. -/
theorem equalBreaks_conjugateDifference
    (C : M) {t : ℕ}
    (hC : ord M C = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (htwo : (((t : ℤ) + 1 : ℤ) : WithTop ℤ) ≤ ord M (2 : M))
    (htrace : ord E (trace E M C) = 0) :
    ord M (PrimeCyclicExtension.generator E M C - C) = 0 ∧
    ∃ (c h : ringOfIntegers M),
      (c : M) = PrimeCyclicExtension.generator E M C - C ∧
      (h : M) = algebraMap E M (trace E M C) ∧
      residueMap M c = residueMap M h ∧ residueMap M c ≠ 0 := by
  let sigma := PrimeCyclicExtension.generator E M
  have htr : algebraMap E M (trace E M C) = C + sigma C :=
    trace_eq_self_add_nontrivial sigma (PrimeCyclicExtension.generator_ne_one E M)
      (by rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank,
        Algebra.IsQuadraticExtension.finrank_eq_two]) C
  have htrOrd : ord M (algebraMap E M (trace E M C)) = 0 := by
    rw [ord_algebraMap, htrace, nsmul_zero]
  have h2C : 2 * C ∈ lattice M 1 := by
    have h := mul_mem_lattice M htwo (show C ∈ lattice M (-(t : ℤ)) by rw [mem_lattice, hC])
    simpa using h
  have heq : sigma C - C = algebraMap E M (trace E M C) - 2 * C := by
    rw [htr]
    ring
  have hdiffOrd : ord M (sigma C - C) = 0 := by
    rw [heq, sub_eq_add_neg, ord_add_eq_min M]
    · rw [htrOrd, ord_neg, min_eq_left]
      exact (show (0 : WithTop ℤ) ≤ 1 by norm_num).trans h2C
    · rw [htrOrd, ord_neg]
      exact ne_of_lt ((show (0 : WithTop ℤ) < 1 by norm_num).trans_le h2C)
  refine ⟨hdiffOrd, ⟨sigma C - C, (mem_lattice_zero_iff M).mp (by rw [mem_lattice, hdiffOrd]; exact le_rfl)⟩,
    ⟨algebraMap E M (trace E M C), (mem_lattice_zero_iff M).mp (by rw [mem_lattice, htrOrd]; exact le_rfl)⟩,
    rfl, rfl, ?_, ?_⟩
  · apply (residueMap_eq_residueMap_iff M _ _).mpr
    change sigma C - C - algebraMap E M (trace E M C) ∈ lattice M 1
    rw [heq, sub_sub_cancel_left]
    exact neg_mem_lattice M h2C
  · intro hz
    have h := (residueMap_eq_zero_iff M _).mp hz
    change sigma C - C ∈ lattice M 1 at h
    rw [mem_lattice, hdiffOrd] at h
    have bad : (1 : ℤ) ≤ 0 := by exact_mod_cast h
    omega

/-- A nonzero critical coordinate of an actual norm-one unit is exactly
FML's ramification coefficient. This fixes the scalar using the norm
kernel, independently of conventions for a uniformizer displacement. -/
theorem equalBreaks_normOneCoordinate
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak E M t) (htpos : 0 < t)
    (hres : residueDegree E M = 1) (pi : ringOfIntegers M)
    (hpi : (ValuativeRel.valuation M).IsUniformizer (pi : M))
    (hgen : Algebra.adjoin (ringOfIntegers E) ({pi} : Set (ringOfIntegers M)) = ⊤)
    (U : unitFiltration M t) (hnorm : normUnits E M (U : Mˣ) = 1)
    (hU : unitGradedMk M t U ≠ 1) :
    (criticalNormResidueEquiv E M hres).symm
      (criticalNormPositiveUnitGradedResidueAddEquiv M htpos (pi : M) hpi
        (Additive.ofMul (unitGradedMk M t U))) =
      criticalNormRamificationLambda E M ht hres pi hpi := by
  let e := criticalNormResidueEquiv E M hres
  let co := criticalNormPositiveUnitGradedResidueAddEquiv M htpos (pi : M) hpi
  let x := e.symm (co (Additive.ofMul (unitGradedMk M t U)))
  have hx0 : x ≠ 0 := by
    intro hx
    have hc : co (Additive.ofMul (unitGradedMk M t U)) = 0 := by
      have h := congrArg e hx
      simpa only [x, RingEquiv.apply_symm_apply, map_zero] using h
    apply hU
    have h : Additive.ofMul (unitGradedMk M t U) = (0 : Additive (UnitGradedPiece M t)) :=
      co.injective (hc.trans (map_zero co).symm)
    exact congrArg Additive.toMul h
  have hsource : unitGradedMk M t (criticalNormSourceUnit E M htpos pi hpi x) =
      unitGradedMk M t U := by
    have h : Additive.ofMul (unitGradedMk M t (criticalNormSourceUnit E M htpos pi hpi x)) =
        Additive.ofMul (unitGradedMk M t U) := by
      apply co.injective
      dsimp only [co]
      rw [criticalNormSourceCoordinate]
      exact e.apply_symm_apply _
    exact congrArg Additive.toMul h
  have hn : criticalGradedNorm E M ht hres pi hpi hgen (unitGradedMk M t U) = 1 := by
    rw [criticalGradedNorm_mk]
    have hn' : normBelowBreakUnitFiltrationHom E M t t
        (normMapsUnitFiltration_atBreak E M ht hres pi hpi hgen) U = 1 := by
      apply Subtype.ext
      exact hnorm
    rw [hn', map_one]
  have hp : criticalNormPolynomialValue E M ht htpos hres pi hpi hgen x = 0 := by
    rw [criticalNormPolynomialValue, hsource, hn]
    change criticalNormPositiveUnitGradedResidueAddEquiv E htpos
      (criticalNormLowerUniformizer E M pi)
      (criticalNormLowerUniformizer_isUniformizer E M hres pi hpi) 0 = 0
    exact map_zero _
  rw [equalBreaks_criticalNormPolynomial E M ht htpos hres pi hpi hgen x] at hp
  have hf : x * (x + criticalNormRamificationLambda E M ht hres pi hpi) = 0 := by
    convert hp using 1; ring
  have hchar : residueCharacteristic E = 2 := by
    rw [residueCharacteristic_eq_degree_of_positive_break E M ht htpos pi hpi hgen,
      Algebra.IsQuadraticExtension.finrank_eq_two E M]
  letI : CharP (ResidueField E) 2 := by rw [← hchar]; infer_instance
  exact CharTwo.add_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left hx0)

/-- At an equal-break origin the actual upper critical coefficient is
`c/u`, where `c` is the residue of the conjugate difference and `u` the
residue of `C*pi^t`. Both local units are constructed from `C`.
The exact norm-one unit `sigma(C)/C` fixes the nonzero critical root. -/
theorem equalBreaks_originRamificationCoefficient
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak E M t) (htpos : 0 < t)
    (hres : residueDegree E M = 1) (pi : ringOfIntegers M)
    (hpi : (ValuativeRel.valuation M).IsUniformizer (pi : M))
    (hgen : Algebra.adjoin (ringOfIntegers E) ({pi} : Set (ringOfIntegers M)) = ⊤)
    (C : Mˣ) (hC : ord M (C : M) = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hdiff : ord M (PrimeCyclicExtension.generator E M (C : M) - (C : M)) = 0) :
    ∃ c u : unitGroup M,
      ((c : Mˣ) : M) = PrimeCyclicExtension.generator E M (C : M) - (C : M) ∧
      ((u : Mˣ) : M) = (C : M) * (pi : M) ^ t ∧
      extensionResidueMap E M (criticalNormRamificationLambda E M ht hres pi hpi) =
        (residueUnits M c : ResidueField M) / (residueUnits M u : ResidueField M) := by
  let sigma := PrimeCyclicExtension.generator E M
  have hdiff0 : sigma (C : M) - (C : M) ≠ 0 :=
    (ord_ne_top_iff M).mp (by rw [hdiff]; exact WithTop.zero_ne_top)
  let c : unitGroup M := ⟨Units.mk0 (sigma (C : M) - (C : M)) hdiff0,
    (mem_unitGroup_iff_ord_eq_zero M _).mpr hdiff⟩
  let piU : Mˣ := Units.mk0 (pi : M) hpi.ne_zero
  have hpit : ord M ((pi : M) ^ t) = ((t : ℤ) : WithTop ℤ) := by
    rw [ord_pow, ord_uniformizer M hpi]
    norm_cast
    simp
  have huord : ord M ((C * piU ^ t : Mˣ) : M) = 0 := by
    change ord M ((C : M) * (pi : M) ^ t) = 0
    rw [ord_mul, hC, hpit]
    norm_cast
    omega
  let u : unitGroup M := ⟨C * piU ^ t, (mem_unitGroup_iff_ord_eq_zero M _).mpr huord⟩
  let A : Mˣ := Units.map sigma.toMonoidHom C / C
  have hAval : (A : M) - 1 = (sigma (C : M) - (C : M)) / (C : M) := by
    dsimp only [A]
    simp only [Units.val_div_eq_div_val, Units.coe_map]
    field_simp
    rfl
  have hAord : ord M ((A : M) - 1) = ((t : ℤ) : WithTop ℤ) := by
    rw [hAval, ord_div, hdiff, hC]
    norm_cast
    omega
  have hA : A ∈ unitFiltration M t := by
    rw [← Nat.sub_add_cancel htpos]
    apply (mem_unitFiltration_succ_iff_sub_mem_lattice M (t - 1) A).mpr
    rw [mem_lattice, hAord, Nat.sub_add_cancel htpos]
  let U : unitFiltration M t := ⟨A, hA⟩
  have hn : normUnits E M (U : Mˣ) = 1 := by
    have hconj : normUnits E M (Units.map sigma.toMonoidHom C) = normUnits E M C := by
      apply Units.ext
      simp only [Units.coe_map]
      change norm E M (sigma (C : M)) = norm E M (C : M)
      exact norm_galoisConjugate E M sigma (C : M)
    change normUnits E M (Units.map sigma.toMonoidHom C / C) = 1
    rw [map_div, hconj, div_self']
  have hU : unitGradedMk M t U ≠ 1 := by
    intro hzero
    have h := (unitGradedMk_eq_one_iff M t U).mp hzero
    have hd := (mem_unitFiltration_succ_iff_sub_mem_lattice M t A).mp h
    rw [mem_lattice, hAord, WithTop.coe_le_coe] at hd
    omega
  have hc := equalBreaks_normOneCoordinate E M ht htpos hres pi hpi hgen U hn hU
  have hcoord : criticalNormPositiveUnitGradedResidueAddEquiv M htpos (pi : M) hpi
      (Additive.ofMul (unitGradedMk M t U)) =
      (residueUnits M (c / u) : ResidueField M) := by
    rw [criticalNormPositiveUnitGradedResidueAddEquiv_mk, residueUnits_coe]
    change residueMap M ⟨((A : M) - 1) / (pi : M) ^ t, _⟩ = _
    congr 1
    apply Subtype.ext
    have hcu : (((unitGroupMulEquivRingOfIntegers M (c / u) :
        (ringOfIntegers M)ˣ) : ringOfIntegers M) : M) =
        (((c / u : unitGroup M) : Mˣ) : M) := rfl
    have hcuval : (((c / u : unitGroup M) : Mˣ) : M) =
        (sigma (C : M) - (C : M)) / ((C : M) * (pi : M) ^ t) := by
      simp [c, u, piU, Units.val_div_eq_div_val]
    rw [hcu, hcuval]
    change ((A : M) - 1) / (pi : M) ^ t = _
    rw [hAval, div_div]
  refine ⟨c, u, rfl, rfl, ?_⟩
  have h := congrArg (criticalNormResidueEquiv E M hres) hc
  rw [RingEquiv.apply_symm_apply, hcoord, map_div, Units.val_div_eq_div_val] at h
  exact h.symm

end Edge
section Biquadratic
variable (F K : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  [IsKleinFour Gal(K/F)]

omit [IsGalois F K] in
/-- The conjugate-difference calculation in `D:NM:critical-polynomials`.
All discarded terms are proved to lie in the next ideal: the trace term
has depth at least `t+1`, and the terms containing `2C²` have positive depth.
The lower conjugate difference therefore has residue `c_j*c_k`. -/
theorem equalBreaks_biquadraticResidues
    (sigma tau : Gal(K/F)) (C : K) (t : ℕ)
    (hC : ord K C = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (htwo : (2 : K) ∈ lattice K (2 * (t : ℤ) + 1))
    (hTotal : C + sigma C + tau C + (sigma * tau) C ∈ lattice K ((t : ℤ) + 1))
    (c₁ c₂ c₃ : ringOfIntegers K)
    (hc₁ : (c₁ : K) = sigma C - C) (hc₂ : (c₂ : K) = tau C - C)
    (hc₃ : (c₃ : K) = (sigma * tau) C - C)
    (hc₂ord : ord K (c₂ : K) = 0) (hc₃ord : ord K (c₃ : K) = 0) :
    residueMap K c₁ + residueMap K c₂ = residueMap K c₃ ∧
    ord K (tau (C * sigma C) - C * sigma C) = 0 ∧
    ∃ n : ringOfIntegers K,
      (n : K) = tau (C * sigma C) - C * sigma C ∧
      residueMap K n = residueMap K c₂ * residueMap K c₃ := by
  let T := C + sigma C + tau C + (sigma * tau) C
  have hCmem : C ∈ lattice K (-(t : ℤ)) := by rw [mem_lattice, hC]
  have hsigma : sigma C ∈ lattice K (-(t : ℤ)) := by
    rw [mem_lattice, ord_galoisConjugate, hC]
  have hst : (sigma * tau) C ∈ lattice K (-(t : ℤ)) := by
    rw [mem_lattice, ord_galoisConjugate, hC]
  have htwoSum : 2 * (C + (sigma * tau) C) ∈ lattice K 1 := by
    have h := mul_mem_lattice K htwo (add_mem_lattice K hCmem hst)
    exact lattice_antitone K (by omega : (1 : ℤ) ≤ 2 * t + 1 + -(t : ℤ)) h
  have hsumDiff : (c₁ : K) + (c₂ : K) - (c₃ : K) ∈ lattice K 1 := by
    have h := sub_mem_lattice K (lattice_antitone K (by omega : (1 : ℤ) ≤ t + 1) hTotal) htwoSum
    convert h using 1
    rw [hc₁, hc₂, hc₃]
    ring
  have hsum : residueMap K c₁ + residueMap K c₂ = residueMap K c₃ := by
    rw [← map_add]
    exact (residueMap_eq_residueMap_iff K (c₁ + c₂) c₃).mpr hsumDiff
  have hCT : C * T ∈ lattice K 1 := by
    simpa only [neg_add_cancel_left] using mul_mem_lattice K hCmem hTotal
  have h2CC : 2 * C * C ∈ lattice K 1 := by
    have h := mul_mem_lattice K (mul_mem_lattice K htwo hCmem) hCmem
    simpa only [show 2 * (t : ℤ) + 1 + -(t : ℤ) + -(t : ℤ) = 1 by omega] using h
  have h2CS : 2 * C * sigma C ∈ lattice K 1 := by
    have h := mul_mem_lattice K (mul_mem_lattice K htwo hCmem) hsigma
    simpa only [show 2 * (t : ℤ) + 1 + -(t : ℤ) + -(t : ℤ) = 1 by omega] using h
  let err := C * T - 2 * C * C - 2 * C * sigma C
  have herr : err ∈ lattice K 1 := sub_mem_lattice K (sub_mem_lattice K hCT h2CC) h2CS
  have hnorm : tau (C * sigma C) - C * sigma C = (c₂ : K) * (c₃ : K) + err := by
    have hcomm : tau (sigma C) = (sigma * tau) C := by
      rw [← AlgEquiv.mul_apply,
        mul_comm_of_exponent_two IsKleinFour.exponent_two tau sigma]
    rw [map_mul, hcomm, hc₂, hc₃]
    dsimp only [err, T]
    ring
  have hprod : ord K ((c₂ : K) * (c₃ : K)) = 0 := by
    rw [ord_mul, hc₂ord, hc₃ord, zero_add]
  have hlt : ord K ((c₂ : K) * (c₃ : K)) < ord K err := by
    rw [hprod]
    exact (show (0 : WithTop ℤ) < 1 by norm_num).trans_le herr
  have hnord : ord K (tau (C * sigma C) - C * sigma C) = 0 := by
    rw [hnorm, ord_add_eq_min K (ne_of_lt hlt), min_eq_left hlt.le, hprod]
  let n : ringOfIntegers K := ⟨tau (C * sigma C) - C * sigma C,
    (mem_lattice_zero_iff K).mp (by rw [mem_lattice, hnord]; exact le_rfl)⟩
  refine ⟨hsum, hnord, n, rfl, ?_⟩
  rw [← map_mul]
  apply (residueMap_eq_residueMap_iff K n (c₂ * c₃)).mpr
  change tau (C * sigma C) - C * sigma C - (c₂ : K) * (c₃ : K) ∈ lattice K 1
  rw [hnorm, add_sub_cancel_left]
  exact herr

end Biquadratic


section CommonCoordinates
variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  (L : IntermediateField F K)
attribute [local instance] Basic.intermediateFieldValuativeRel
  Basic.intermediateFieldTopology Basic.intermediateField_localField
  Basic.intermediateField_lowerValuativeExtension Basic.intermediateField_upperValuativeExtension
variable [Algebra.IsQuadraticExtension L K] [PrimeCyclicExtension L K]

open private norm_increment_congruent from
  LanglandsSecondMainLemma.Dyadic.Nonmaximal.MinimalFunctions

/-- Transport the actual norm coordinate to the common top residue field,
using the very same top Teichmüller lift on every quadratic flag. -/
theorem equalBreaks_commonCoordinate
    {r q s : ℕ} {w : ℤ} {C : Kˣ} {hC : trace L K (C : K) ≠ 0}
    (hr : 1 ≤ r) (ht : PrimeCyclicExtension.IsLowerBreak L K (2 * r - 1))
    (hres : residueDegree L K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (delta : Lˣ) (hdelta : ord L (delta : L) = (((2 * r - 1 : ℕ) : ℤ) : WithTop ℤ))
    (hdelta_val : (delta : L) = criticalNormLowerUniformizer L K pi ^ (2 * r - 1))
    (x : ResidueField K)
    (V : MinimalFunctionLift L q (2 * r - 1) s w C
      (minimalFunctionPoint C (2 * r - 1) (by omega)
        (minimalSourceLift K (Units.mk0 (pi : K) hpi.ne_zero)
          (ord_uniformizer K hpi) (2 * r - 1) (teichmuller K x))) hC) :
    criticalNormResidueEquiv L K hres (minimalCriticalCoordinate L delta hdelta V.upper) =
      x ^ 2 + criticalNormUpperRamificationLambda L K ht pi hpi * x := by
  let e := criticalNormResidueEquiv L K hres
  let y := e.symm x
  let z : ringOfIntegers K :=
    algebraMap (ringOfIntegers L) (ringOfIntegers K) (teichmuller L y)
  have hz : residueMap K z = x := by
    rw [show residueMap K z = extensionResidueMap L K
        (residueMap L (teichmuller L y)) from
      (Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
        (ValuativeRel.valuation L) (ValuativeRel.valuation K) _).symm,
      residueMap_teichmuller]
    exact e.apply_symm_apply x
  let v := minimalSourceLift K (Units.mk0 (pi : K) hpi.ne_zero)
    (ord_uniformizer K hpi) (2 * r - 1) (teichmuller K x)
  let v' := criticalNormSourceDisplacement L K (2 * r - 1) pi hpi y
  have hvv' : (v : K) - (v' : K) ∈ lattice K (((2 * r - 1 : ℕ) : ℤ) + 1) := by
    have h := minimalSourceLift_sub_mem K (Units.mk0 (pi : K) hpi.ne_zero)
      (ord_uniformizer K hpi) (2 * r - 1) (teichmuller K x) z
      ((residueMap_teichmuller K x).trans hz.symm)
    convert h using 1
    dsimp only [v, v', minimalSourceLift, criticalNormSourceDisplacement]
    simp only [Units.val_mk0]
    congr 1
    exact mul_comm _ _
  have hn := norm_increment_congruent L K hr (by omega : 0 < 2 * r - 1)
    ht hres (by omega : (((2 * r - 1 : ℕ) : ℤ) + 1) ≤
      (((2 * r - 1 : ℕ) : ℤ) + 1 + 2 * r) / 2) le_rfl v v' hvv'
  have hgen := algebra_adjoin_uniformizer_eq_top_of_residueDegree_eq_one L K hres pi hpi
  have hcoord : minimalCriticalCoordinate L delta hdelta V.upper =
      criticalNormPolynomialValue L K ht (by omega) hres pi hpi hgen y := by
    rw [minimalCriticalCoordinate, criticalNormPolynomialValue_raw]
    apply (reduce_eq_reduce_iff L _ _).mpr
    apply (congruentAtDepth_iff_sub_mem_lattice L _ _ _).mpr
    rw [V.upper_value L (by omega) v, ← hdelta_val, ← sub_div,
      sub_sub_sub_cancel_right]
    exact (div_mem_lattice_iff L _ _ (((2 * r - 1 : ℕ) : ℤ)) 1 hdelta).mpr hn
  rw [hcoord, equalBreaks_criticalNormPolynomial L K ht (by omega) hres pi hpi hgen,
    map_add, map_pow, map_mul, criticalNormResidueEquiv_ramificationLambda]
  simp only [y, e, RingEquiv.apply_symm_apply]

/-- A residue equivalence transports the full actual Hasse function and
preserves the nontriviality of its polar character. -/
theorem equalBreaks_transportHasse
    (hres : residueDegree L K = 1) (rho : FiniteAddChar (ResidueField L)) (hrho : rho ≠ 1)
    (H : HasseFunction (ResidueField L) rho) :
    ∃ (sigma : FiniteAddChar (ResidueField K)) (J : HasseFunction (ResidueField K) sigma),
      sigma ≠ 1 ∧ ∀ x, J x = H ((criticalNormResidueEquiv L K hres).symm x) := by
  let e := criticalNormResidueEquiv L K hres
  let sigma : FiniteAddChar (ResidueField K) := rho.compAddMonoidHom e.symm.toAddMonoidHom
  have hsigma : sigma ≠ 1 := by
    intro h
    apply hrho
    ext x
    have hx := DFunLike.congr_fun h (e x)
    change rho (e.symm (e x)) = 1 at hx
    simpa only [RingEquiv.symm_apply_apply, AddChar.one_apply] using hx
  let J : HasseFunction (ResidueField K) sigma := {
    toFun := fun x ↦ H (e.symm x)
    ne_zero' := fun x ↦ H.ne_zero _
    map_add' := by
      intro x y
      change H (e.symm (x + y)) = H (e.symm x) * H (e.symm y) * rho (e.symm (x * y))
      rw [map_add, map_mul, H.map_add] }
  exact ⟨sigma, J, hsigma, fun _ ↦ rfl⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] in
private theorem equalBreaks_generatorFixed (x : K) :
    (PrimeCyclicExtension.generator L K).restrictScalars F x = x ↔ x ∈ L := by
  change PrimeCyclicExtension.generator L K x = x ↔ _
  constructor
  · intro hx
    have hfix (s : Gal(K/L)) : s x = x := by
      have hle : Subgroup.zpowers (PrimeCyclicExtension.generator L K) ≤
          MulAction.stabilizer Gal(K/L) x := Subgroup.zpowers_le.mpr hx
      exact hle (PrimeCyclicExtension.generator_mem_zpowers L K s)
    obtain ⟨y, hy⟩ := (IsGalois.mem_range_algebraMap_iff_fixed x).mpr hfix
    exact hy ▸ y.property
  · intro hx
    exact (PrimeCyclicExtension.generator L K).commutes (⟨x, hx⟩ : L)

variable [Algebra.IsQuadraticExtension F L] [PrimeCyclicExtension F L]

open private minimal_stationary criticalValue_eq_residual from
  LanglandsSecondMainLemma.Dyadic.Nonmaximal.MinimalFunctions

private theorem equalBreaks_topHasse [IsKleinFour Gal(K/F)]
    {r : ℕ} (hr : 1 ≤ r) (htF : PrimeCyclicExtension.IsLowerBreak F L (2 * r - 1))
    (htK : PrimeCyclicExtension.IsLowerBreak L K (2 * r - 1))
    (hresF : residueDegree F L = 1) (hresK : residueDegree L K = 1)
    (theta : LocalQuasiCharData L) (hm : theta.conductor = 4 * r - 1)
    (omega : NormCharacter F L) (Psi : LocalAddCharData F) (hPsi : Psi.conductor = -2 * (r : ℤ))
    (PsiL : LocalAddCharData L) (hPsiL : PsiL.character = Psi.character.compTrace)
    (Theta : ContinuousQuasiChar K) (hcompatible : normQuasiChar L K theta.character = Theta)
    (C : Kˣ) (hC : ord K (C : K) = ((1 - 2 * (r : ℤ) : ℤ) : WithTop ℤ))
    (S : MinimalOriginSide L r (2 * r) 0 omega Psi.character theta.character (C : K))
    (pi : ringOfIntegers K) (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (delta : Lˣ) (hdelta : ord L (delta : L) = (((2 * r - 1 : ℕ) : ℤ) : WithTop ℤ))
    (hdelta_val : (delta : L) = criticalNormLowerUniformizer L K pi ^ (2 * r - 1)) :
    ∃ (rho : FiniteAddChar (ResidueField K)) (H : HasseFunction (ResidueField K) rho),
      rho ≠ 1 ∧ (∀ x, Stationary.normalizedResidualFunction L theta PsiL 1 (normUnits L K C)
        (2 * r - 1) (by omega) (by omega) delta hdelta
        ((criticalNormResidueEquiv L K hresK).symm x) = H x) ∧
      ∀ x,
        let v := minimalSourceLift K (Units.mk0 (pi : K) hpi.ne_zero)
          (ord_uniformizer K hpi) (2 * r - 1) (teichmuller K x)
        let C' := minimalFunctionPoint C (2 * r - 1) (by omega) v
        H (x ^ 2 + criticalNormUpperRamificationLambda L K htK pi hpi * x) =
          (Theta (C' / C) : ℂ)⁻¹ *
            (Psi.character (-elementarySymmetric F K 2 (C' : K) +
              elementarySymmetric F K 2 (C : K)) : ℂ) := by
  have hs := minimal_stationary L hr (by omega : 0 < 2 * r - 1) htF hresF hresK
    theta Psi PsiL hPsiL C
    (by convert hC using 1; rw [hPsi, hm]; congr 1; omega)
    (by simpa only [show 2 * r - 1 + 1 = 2 * r by omega] using S.upper_formula)
  have h1 : unitOrder L (1 : Lˣ) = 0 := by simp [unitOrder]
  obtain ⟨rho, H, hrho, hH, _⟩ := equalBreaks_residualHasse L theta PsiL 1
    (normUnits L K C) (2 * r - 1) (by omega) (by omega)
    (by simpa only [scaleAddCharData_conductor, h1, add_zero] using hs.1)
    (by intro v; simpa only [scaleAddCharData_character_apply, Units.val_one, one_mul]
      using hs.2 v) delta hdelta
  obtain ⟨sigma, J, hsigma, hJ⟩ := equalBreaks_transportHasse L hresK rho hrho H
  have hresidual (x) := (hH ((criticalNormResidueEquiv L K hresK).symm x)).trans (hJ x).symm
  refine ⟨sigma, J, hsigma, hresidual, ?_⟩
  intro x
  let v := minimalSourceLift K (Units.mk0 (pi : K) hpi.ne_zero)
    (ord_uniformizer K hpi) (2 * r - 1) (teichmuller K x)
  let V := minimalFunctionLift L r (2 * r - 1) r r (2 * r - 1) (1 - 2 * (r : ℤ)) 0
    hr (by omega) (by omega) hr le_rfl htF htK hresF hresK
    (by omega) le_rfl (by omega) C hC S.trace_order S.trace_ne_zero v
  have hcoord := equalBreaks_commonCoordinate L hr htK hresK pi hpi delta hdelta hdelta_val x V
  have heq := congrArg (criticalNormResidueEquiv L K hresK).symm hcoord
  rw [RingEquiv.symm_apply_apply] at heq
  rw [← hresidual, ← heq]
  exact (criticalValue_eq_residual L theta PsiL (normUnits L K C) (by omega)
    (by omega) hs.1 hs.2 delta hdelta V.upper).symm.trans
      (V.critical_value L (by omega) (by omega) theta omega Psi PsiL hPsiL
        S.lower_formula Theta hcompatible)

open private commonOrigin_edge from LanglandsSecondMainLemma.Stationary.CommonOrigin

omit [PrimeCyclicExtension L K] in
/-- The complete factor at the constructed minimal origin, including the
actual lower quadratic character and its even-conductor Lamprecht factor. -/
private theorem equalBreaks_fullFactor [IsKleinFour Gal(K/F)]
    {r : ℕ} (hr : 1 ≤ r) (htF : PrimeCyclicExtension.IsLowerBreak F L (2 * r - 1))
    (hresF : residueDegree F L = 1) (hresK : residueDegree L K = 1)
    (theta : LocalQuasiCharData L) (hm : theta.conductor = 4 * r - 1)
    (omega : NormCharacter F L) (homega : omega ≠ 1)
    (Psi : LocalAddCharData F) (hPsi : Psi.conductor = -2 * (r : ℤ))
    (PsiL : LocalAddCharData L) (hPsiL : PsiL.character = Psi.character.compTrace)
    (Theta : ContinuousQuasiChar K) (hc : normQuasiChar L K theta.character = Theta)
    (C : Kˣ) (hC : ord K (C : K) = ((1 - 2 * (r : ℤ) : ℤ) : WithTop ℤ))
    (S : MinimalOriginSide L r (2 * r) 0 omega Psi.character theta.character (C : K))
    (delta : Lˣ) (hd : ord L (delta : L) = (((2 * r - 1 : ℕ) : ℤ) : WithTop ℤ)) :
    LanglandsFirstMainLemma.localConstant L theta.character PsiL.character *
        LanglandsFirstMainLemma.localConstant F omega.1 Psi.character =
      ((Characters.restrictQuasiChar F L theta.character * omega.1) (-1) : ℂ) *
        (Theta C : ℂ)⁻¹ * (Psi.character (-elementarySymmetric F K 2 (C : K)) : ℂ) *
        Stationary.normalizedResidualFactor L theta PsiL 1 (normUnits L K C)
          (2 * r - 1) (by omega) (by omega) delta hd := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F L hresF
  let omegaD : LocalQuasiCharData F := ⟨omega.1, 2 * r, by
    simpa only [Nat.sub_add_cancel (show 1 ≤ 2 * r by omega)] using
      ramifiedNormCharacter_conductor F L htF hresF pi hpi hgen omega homega⟩
  have hs := minimal_stationary L hr (by omega : 0 < 2 * r - 1) htF hresF hresK
    theta Psi PsiL hPsiL C
    (by convert hC using 1; rw [hPsi, hm]; congr 1; omega)
    (by simpa only [show 2 * r - 1 + 1 = 2 * r by omega] using S.upper_formula)
  have h1L : unitOrder L (1 : Lˣ) = 0 := by simp [unitOrder]
  have h1F : unitOrder F (1 : Fˣ) = 0 := by simp [unitOrder]
  have hz : Stationary.IsOrdinaryStationaryCoefficient L theta (scaleAddCharData L PsiL 1)
      (normUnits L K C) (by omega) := by
    refine ⟨by simpa only [scaleAddCharData_conductor, h1L, add_zero] using hs.1, ?_⟩
    have hs' : Stationary.IsNormalizedStationaryCoefficientAtDepth L theta
        (scaleAddCharData L PsiL 1) (normUnits L K C) (2 * r - 1 + 1) (by omega) := by
      simpa only [Stationary.IsNormalizedStationaryCoefficientAtDepth,
        scaleAddCharData_character_apply, Units.val_one, one_mul] using hs.2
    convert hs' using 1
    omega
  have hw : Stationary.IsOrdinaryStationaryCoefficient F omegaD (scaleAddCharData F Psi 1)
      (Stationary.commonOriginLowerCoefficient L C S.trace_ne_zero) (by dsimp [omegaD]; omega) := by
    constructor
    · change ord F (norm F L (trace L K (C : K))) = _
      rw [ord_norm, S.trace_order, WithTop.coe_zero, nsmul_zero,
        scaleAddCharData_conductor, h1F, add_zero, hPsi]
      change (0 : WithTop ℤ) = ((-(-2 * (r : ℤ)) - (2 * r : ℕ) : ℤ) : WithTop ℤ)
      norm_cast
      omega
    · have hdF : omegaD.conductor / 2 + omegaD.conductor % 2 = r := by dsimp [omegaD]; omega
      intro v
      simpa only [scaleAddCharData_character_apply, Units.val_one, one_mul, omegaD,
        Stationary.commonOriginLowerCoefficient, coe_normUnits, Units.val_mk0] using
        S.lower_formula v (by simpa only [hdF] using v.property)
          (positiveUnitOfLattice F (by omega) (-v))
          (by simp only [coe_positiveUnitOfLattice, Submodule.coe_neg, sub_eq_add_neg])
  have hres : Stationary.completeNormalizedResidualFactor L theta PsiL 1 (normUnits L K C)
      (by omega) = Stationary.normalizedResidualFactor L theta PsiL 1 (normUnits L K C)
        (2 * r - 1) (by omega) (by omega) delta hd := by
    have ho := (Stationary.normalizedFactor L theta PsiL 1 (normUnits L K C)
      (2 * r - 1) 1 (by omega) (by omega) (by omega) hz.1
      (by convert hz.2 using 1; omega)).2 rfl delta hd
    have ha := Stationary.completeNormalizedFactor L theta PsiL 1 (normUnits L K C) (by omega) hz
    exact mul_left_cancel₀ (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (ha.symm.trans ho)
  have hedge := commonOrigin_edge L theta omegaD omega rfl Theta hc Psi PsiL hPsiL
    1 C S.trace_ne_zero (by omega) (by dsimp [omegaD]; omega)
    (by simpa only [map_one] using hz) hw
  have hlower := Stationary.completeNormalizedResidualFactor_even F omegaD Psi 1
    (Stationary.commonOriginLowerCoefficient L C S.trace_ne_zero) (by dsimp [omegaD]; omega)
    (by dsimp [omegaD]; omega)
  simpa only [Stationary.commonOriginResidualProduct, map_one, hlower, hres, mul_one,
    inv_one, scaleAddCharData_character_apply, Units.val_one, one_mul] using hedge

end CommonCoordinates

section DistinctRoots
variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  [IsKleinFour Gal(K/F)] [CharP (ResidueField K) 2]
  (L₁ L₂ L₃ : IntermediateField F K)
attribute [local instance] Basic.intermediateFieldValuativeRel
  Basic.intermediateFieldTopology Basic.intermediateField_localField
  Basic.intermediateField_lowerValuativeExtension Basic.intermediateField_upperValuativeExtension
variable [Algebra.IsQuadraticExtension L₁ K] [PrimeCyclicExtension L₁ K]
  [Algebra.IsQuadraticExtension L₂ K] [PrimeCyclicExtension L₂ K]
  [Algebra.IsQuadraticExtension L₃ K] [PrimeCyclicExtension L₃ K]

/-- The three actual upper kernels are distinct. The conjugate-difference
residues add because the first automorphism acts trivially on the residue
field; the third trace is a unit, so their sum cannot vanish. -/
theorem equalBreaks_distinctRoots
    (h₁₂ : L₁ ≠ L₂) (h₁₃ : L₁ ≠ L₃) (h₂₃ : L₂ ≠ L₃)
    {t : ℕ} (htpos : 0 < t)
    (ht₁ : PrimeCyclicExtension.IsLowerBreak L₁ K t)
    (ht₂ : PrimeCyclicExtension.IsLowerBreak L₂ K t)
    (hres₁ : residueDegree L₁ K = 1) (hres₂ : residueDegree L₂ K = 1)
    (pi : ringOfIntegers K) (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (C : Kˣ) (hC : ord K (C : K) = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (htwo : (((t : ℤ) + 1 : ℤ) : WithTop ℤ) ≤ ord K (2 : K))
    (htrace₁ : ord L₁ (trace L₁ K (C : K)) = 0)
    (htrace₂ : ord L₂ (trace L₂ K (C : K)) = 0)
    (htrace₃ : ord L₃ (trace L₃ K (C : K)) = 0) :
    criticalNormUpperRamificationLambda L₁ K ht₁ pi hpi ≠
      criticalNormUpperRamificationLambda L₂ K ht₂ pi hpi := by
  classical
  let s := (PrimeCyclicExtension.generator L₁ K).restrictScalars F
  let v := (PrimeCyclicExtension.generator L₂ K).restrictScalars F
  let z := (PrimeCyclicExtension.generator L₃ K).restrictScalars F
  have hs : s ≠ 1 := fun h ↦ PrimeCyclicExtension.generator_ne_one L₁ K
    (AlgEquiv.ext fun x ↦ AlgEquiv.congr_fun h x)
  have hv : v ≠ 1 := fun h ↦ PrimeCyclicExtension.generator_ne_one L₂ K
    (AlgEquiv.ext fun x ↦ AlgEquiv.congr_fun h x)
  have hz : z ≠ 1 := fun h ↦ PrimeCyclicExtension.generator_ne_one L₃ K
    (AlgEquiv.ext fun x ↦ AlgEquiv.congr_fun h x)
  have hsv : s ≠ v := by
    intro h
    apply h₁₂
    ext x
    rw [← equalBreaks_generatorFixed L₁ x, ← equalBreaks_generatorFixed L₂ x]
    exact Iff.of_eq (congrArg (fun g : Gal(K/F) ↦ g x = x) h)
  have hsz : s ≠ z := by
    intro h
    apply h₁₃
    ext x
    rw [← equalBreaks_generatorFixed L₁ x, ← equalBreaks_generatorFixed L₃ x]
    exact Iff.of_eq (congrArg (fun g : Gal(K/F) ↦ g x = x) h)
  have hvz : v ≠ z := by
    intro h
    apply h₂₃
    ext x
    rw [← equalBreaks_generatorFixed L₂ x, ← equalBreaks_generatorFixed L₃ x]
    exact Iff.of_eq (congrArg (fun g : Gal(K/F) ↦ g x = x) h)
  have hprod : s * v = z := by
    have hmem := Finset.mem_univ z
    rw [← IsKleinFour.eq_finset_univ hs hv hsv] at hmem
    have hzprod : z = s * v := by simpa [hz, hsz.symm, hvz.symm] using hmem
    exact hzprod.symm
  obtain ⟨hc₁, c₁, _, hc₁val, _, _, _⟩ :=
    equalBreaks_conjugateDifference L₁ K (C : K) hC htwo htrace₁
  obtain ⟨hc₂, c₂, _, hc₂val, _, _, _⟩ :=
    equalBreaks_conjugateDifference L₂ K (C : K) hC htwo htrace₂
  obtain ⟨_, c₃, _, hc₃val, _, _, hc₃ne⟩ :=
    equalBreaks_conjugateDifference L₃ K (C : K) hC htwo htrace₃
  have hsum : residueMap K c₁ + residueMap K c₂ = residueMap K c₃ := by
    rw [← map_add]
    apply (residueMap_eq_residueMap_iff K (c₁ + c₂) c₃).mpr
    have hact := (mem_lowerRamificationGroup_iff_lattice L₁ K
      (PrimeCyclicExtension.generator L₁ K) (t : ℤ)).mp
      (by rw [ht₁.1]; trivial) c₂
    apply lattice_antitone K (by omega : (1 : ℤ) ≤ (t : ℤ) + 1)
    convert neg_mem_lattice K hact using 1
    change (c₁ : K) + (c₂ : K) - (c₃ : K) = -(s (c₂ : K) - (c₂ : K))
    rw [hc₁val, hc₂val, hc₃val, map_sub]
    change s (C : K) - (C : K) + (v (C : K) - (C : K)) -
      (z (C : K) - (C : K)) = -(s (v (C : K)) - s (C : K) - (v (C : K) - (C : K)))
    rw [← AlgEquiv.mul_apply, hprod]
    ring
  obtain ⟨a, u, ha, hu, hlam₁⟩ := equalBreaks_originRamificationCoefficient L₁ K
    ht₁ htpos hres₁ pi hpi
    (algebra_adjoin_uniformizer_eq_top_of_residueDegree_eq_one L₁ K hres₁ pi hpi) C hC hc₁
  obtain ⟨b, u', hb, hu', hlam₂⟩ := equalBreaks_originRamificationCoefficient L₂ K
    ht₂ htpos hres₂ pi hpi
    (algebra_adjoin_uniformizer_eq_top_of_residueDegree_eq_one L₂ K hres₂ pi hpi) C hC hc₂
  have huu : u = u' := Subtype.ext (Units.ext (hu.trans hu'.symm))
  have hares : (residueUnits K a : ResidueField K) = residueMap K c₁ := by
    rw [residueUnits_coe]
    congr 1
    exact Subtype.ext (ha.trans hc₁val.symm)
  have hbres : (residueUnits K b : ResidueField K) = residueMap K c₂ := by
    rw [residueUnits_coe]
    congr 1
    exact Subtype.ext (hb.trans hc₂val.symm)
  intro h
  change criticalNormResidueEquiv L₁ K hres₁ _ = _ at hlam₁
  change criticalNormResidueEquiv L₂ K hres₂ _ = _ at hlam₂
  rw [criticalNormResidueEquiv_ramificationLambda] at hlam₁ hlam₂
  have h' := hlam₁.symm.trans (h.trans hlam₂)
  rw [hares, hbres, huu, div_left_inj' (residueUnits K u').ne_zero] at h'
  apply hc₃ne
  rw [← hsum, h', CharTwo.add_self_eq_zero]

variable [Algebra.IsQuadraticExtension F L₁] [PrimeCyclicExtension F L₁]
  [Algebra.IsQuadraticExtension F L₂] [PrimeCyclicExtension F L₂]

private theorem equalBreaks_residualFactors
    {r : ℕ} (hr : 1 ≤ r)
    (htF₁ : PrimeCyclicExtension.IsLowerBreak F L₁ (2 * r - 1))
    (htF₂ : PrimeCyclicExtension.IsLowerBreak F L₂ (2 * r - 1))
    (htK₁ : PrimeCyclicExtension.IsLowerBreak L₁ K (2 * r - 1))
    (htK₂ : PrimeCyclicExtension.IsLowerBreak L₂ K (2 * r - 1))
    (hresF₁ : residueDegree F L₁ = 1) (hresF₂ : residueDegree F L₂ = 1)
    (hresK₁ : residueDegree L₁ K = 1) (hresK₂ : residueDegree L₂ K = 1)
    (theta₁ : LocalQuasiCharData L₁) (theta₂ : LocalQuasiCharData L₂)
    (hm₁ : theta₁.conductor = 4 * r - 1) (hm₂ : theta₂.conductor = 4 * r - 1)
    (omega₁ : NormCharacter F L₁) (omega₂ : NormCharacter F L₂)
    (Psi : LocalAddCharData F) (hPsi : Psi.conductor = -2 * (r : ℤ))
    (Psi₁ : LocalAddCharData L₁) (Psi₂ : LocalAddCharData L₂)
    (hPsi₁ : Psi₁.character = Psi.character.compTrace)
    (hPsi₂ : Psi₂.character = Psi.character.compTrace)
    (Theta : ContinuousQuasiChar K)
    (hc₁ : normQuasiChar L₁ K theta₁.character = Theta)
    (hc₂ : normQuasiChar L₂ K theta₂.character = Theta)
    (C : Kˣ) (hC : ord K (C : K) = ((1 - 2 * (r : ℤ) : ℤ) : WithTop ℤ))
    (S₁ : MinimalOriginSide L₁ r (2 * r) 0 omega₁ Psi.character theta₁.character (C : K))
    (S₂ : MinimalOriginSide L₂ r (2 * r) 0 omega₂ Psi.character theta₂.character (C : K))
    (pi : ringOfIntegers K) (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hroots : criticalNormUpperRamificationLambda L₁ K htK₁ pi hpi ≠
      criticalNormUpperRamificationLambda L₂ K htK₂ pi hpi)
    (delta₁ : L₁ˣ) (delta₂ : L₂ˣ)
    (hd₁ : ord L₁ (delta₁ : L₁) = (((2 * r - 1 : ℕ) : ℤ) : WithTop ℤ))
    (hd₂ : ord L₂ (delta₂ : L₂) = (((2 * r - 1 : ℕ) : ℤ) : WithTop ℤ))
    (hdv₁ : (delta₁ : L₁) = criticalNormLowerUniformizer L₁ K pi ^ (2 * r - 1))
    (hdv₂ : (delta₂ : L₂) = criticalNormLowerUniformizer L₂ K pi ^ (2 * r - 1)) :
    Stationary.normalizedResidualFactor L₁ theta₁ Psi₁ 1 (normUnits L₁ K C)
        (2 * r - 1) (by omega) (by omega) delta₁ hd₁ =
      Stationary.normalizedResidualFactor L₂ theta₂ Psi₂ 1 (normUnits L₂ K C)
        (2 * r - 1) (by omega) (by omega) delta₂ hd₂ := by
  letI := residueFieldFintype K
  letI := residueFieldFintype L₁
  letI := residueFieldFintype L₂
  let e₁ := criticalNormResidueEquiv L₁ K hresK₁
  let e₂ := criticalNormResidueEquiv L₂ K hresK₂
  obtain ⟨rho, H, hrho, hH, hQH⟩ := equalBreaks_topHasse L₁ hr htF₁ htK₁ hresF₁ hresK₁
    theta₁ hm₁ omega₁ Psi hPsi Psi₁ hPsi₁ Theta hc₁ C hC S₁ pi hpi delta₁ hd₁ hdv₁
  obtain ⟨sigma, J, hsigma, hJ, hQJ⟩ := equalBreaks_topHasse L₂ hr htF₂ htK₂ hresF₂ hresK₂
    theta₂ hm₂ omega₂ Psi hPsi Psi₂ hPsi₂ Theta hc₂ C hC S₂ pi hpi delta₂ hd₂ hdv₂
  have ha : criticalNormUpperRamificationLambda L₁ K htK₁ pi hpi ≠ 0 := by
    rw [← criticalNormResidueEquiv_ramificationLambda L₁ K htK₁ hresK₁ pi hpi,
      map_ne_zero]
    exact criticalNormRamificationLambda_ne_zero L₁ K htK₁ hresK₁ pi hpi
      (algebra_adjoin_uniformizer_eq_top_of_residueDegree_eq_one L₁ K hresK₁ pi hpi)
  have hb : criticalNormUpperRamificationLambda L₂ K htK₂ pi hpi ≠ 0 := by
    rw [← criticalNormResidueEquiv_ramificationLambda L₂ K htK₂ hresK₂ pi hpi,
      map_ne_zero]
    exact criticalNormRamificationLambda_ne_zero L₂ K htK₂ hresK₂ pi hpi
      (algebra_adjoin_uniformizer_eq_top_of_residueDegree_eq_one L₂ K hresK₂ pi hpi)
  have hsum := equalBreaks_hasseComparison (ResidueField K) ha hb hroots rho sigma hrho hsigma H J
    (fun x ↦ by simpa only [equalBreakNormPolynomial_apply, div_one] using
      (hQH x).trans (hQJ x).symm)
  have hs₁ := (e₁.symm.toEquiv.sum_comp (Stationary.normalizedResidualFunction L₁ theta₁
    Psi₁ 1 (normUnits L₁ K C) (2 * r - 1) (by omega) (by omega) delta₁ hd₁)).symm.trans
      (Fintype.sum_congr _ _ hH)
  have hs₂ := (e₂.symm.toEquiv.sum_comp (Stationary.normalizedResidualFunction L₂ theta₂
    Psi₂ 1 (normUnits L₂ K C) (2 * r - 1) (by omega) (by omega) delta₂ hd₂)).symm.trans
      (Fintype.sum_congr _ _ hJ)
  have hcard : residueCard L₁ = residueCard L₂ :=
    (Fintype.card_congr e₁.toEquiv).trans (Fintype.card_congr e₂.toEquiv).symm
  unfold Stationary.normalizedResidualFactor
  rw [hs₁, hs₂, hcard, hsum]

end DistinctRoots

private theorem equalBreaks_localConstant_scale
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E) (alpha : Eˣ) :
    LanglandsFirstMainLemma.localConstant E theta.character (scaleAddCharData E psi alpha).character =
      (theta.character alpha : ℂ) * LanglandsFirstMainLemma.localConstant E theta.character psi.character := by
  let Gamma : AdmissibleGamma E theta psi :=
    Classical.choice (AdmissibleGamma.exists_admissible (F := E))
  let Gamma' : AdmissibleGamma E theta (scaleAddCharData E psi alpha) :=
    Classical.choice (AdmissibleGamma.exists_admissible (F := E))
  rw [localConstant_isDeltaFinite E theta psi Gamma,
    localConstant_isDeltaFinite E theta (scaleAddCharData E psi alpha) Gamma']
  exact delta_additive_scale E theta psi alpha Gamma Gamma'

section Comparison
variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  [CharP (ResidueField K) 2]
  (L : Fin 3 → IntermediateField F K)
attribute [local instance] Basic.intermediateFieldValuativeRel
  Basic.intermediateFieldTopology Basic.intermediateField_localField
  Basic.intermediateField_lowerValuativeExtension Basic.intermediateField_upperValuativeExtension
variable [∀ i, Algebra.IsQuadraticExtension F (L i)] [∀ i, PrimeCyclicExtension F (L i)]
  [∀ i, Algebra.IsQuadraticExtension (L i) K] [∀ i, PrimeCyclicExtension (L i) K]

open private commonOrigin_kleinFour from LanglandsSecondMainLemma.Stationary.CommonOrigin
open private primeNormCharacter_card normCharacterProduct_two from
  LanglandsSecondMainLemma.Characters.Conjugacy
open private ramification_two from LanglandsSecondMainLemma.Dyadic.Nonmaximal.MinimalOrigin

/-- **Paper Proposition 13.12 (`D:NM:minimal-one`).** The three complete
canonical local constants agree at the same minimal origin when the breaks
are equal. The sides `S` are the outputs of the proved `minimalOrigin`
constructor; they retain their full upper and lower stationary ideals.

The lower factors are the complete norm-character products. The proof
constructs the actual common residue functions, proves their distinct
critical kernels and missing-coset cancellation, and restores the original
arbitrary additive character. No residue model, polar identity, exact norm
representative, or cancellation hypothesis is supplied by the caller. -/
theorem equalBreaks
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (hsep : Function.Injective (fun i ↦ Ramification.intermediateNormRange (L i)))
    {r : ℕ} (hr : 1 ≤ r) (htwo : (2 : F) ∈ lattice F (r : ℤ))
    (htF : ∀ i, PrimeCyclicExtension.IsLowerBreak F (L i) (2 * r - 1))
    (htK : ∀ i, PrimeCyclicExtension.IsLowerBreak (L i) K (2 * r - 1))
    (hresF : ∀ i, residueDegree F (L i) = 1) (hresK : ∀ i, residueDegree (L i) K = 1)
    (theta : (i : Fin 3) → LocalQuasiCharData (L i))
    (hm : ∀ i, (theta i).conductor = 4 * r - 1)
    (omega : (i : Fin 3) → NormCharacter F (L i)) (homega : ∀ i, omega i ≠ 1)
    (psi : LocalAddCharData F) (psiL : (i : Fin 3) → LocalAddCharData (L i))
    (hpsiL : ∀ i, (psiL i).character = psi.character.compTrace)
    (alpha : Fˣ) (hPsi : (scaleAddCharData F psi alpha).conductor = -2 * (r : ℤ))
    (Theta : ContinuousQuasiChar K)
    (hc : ∀ i, normQuasiChar (L i) K (theta i).character = Theta)
    (hprimitive : ¬ ∃ chi : ContinuousQuasiChar F, normQuasiChar F K chi = Theta)
    (C : Kˣ) (hC : ord K (C : K) = ((1 - 2 * (r : ℤ) : ℤ) : WithTop ℤ))
    (S : ∀ i, MinimalOriginSide (L i) r (2 * r) 0 (omega i)
      (scaleAddCharData F psi alpha).character (theta i).character (C : K)) :
    ∀ i j : Fin 3,
      LanglandsFirstMainLemma.localConstant (L i) (theta i).character (psiL i).character *
          LanglandsFirstMainLemma.localConstant F
            (Characters.intermediateNormCharacterProduct Nat.prime_two hG (L i)
              (Algebra.IsQuadraticExtension.finrank_eq_two F (L i))) psi.character =
        LanglandsFirstMainLemma.localConstant (L j) (theta j).character (psiL j).character *
          LanglandsFirstMainLemma.localConstant F
            (Characters.intermediateNormCharacterProduct Nat.prime_two hG (L j)
              (Algebra.IsQuadraticExtension.finrank_eq_two F (L j))) psi.character := by
  letI := commonOrigin_kleinFour hG
  let Psi := scaleAddCharData F psi alpha
  let alphaL (i : Fin 3) := Units.map (algebraMap F (L i)).toMonoidHom alpha
  let PsiL (i : Fin 3) := scaleAddCharData (L i) (psiL i) (alphaL i)
  have hPsiL (i) : (PsiL i).character = Psi.character.compTrace := by
    apply ContinuousAddChar.ext
    intro x
    rw [ContinuousAddChar.compTrace_apply]
    change (scaleAddCharData (L i) (psiL i) (alphaL i)).character x =
      (scaleAddCharData F psi alpha).character (trace F (L i) x)
    rw [scaleAddCharData_character_apply, scaleAddCharData_character_apply,
      hpsiL i, ContinuousAddChar.compTrace_apply]
    congr 1
    change trace F (L i) (algebraMap F (L i) (alpha : F) * x) = _
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hprod (i) : Characters.intermediateNormCharacterProduct Nat.prime_two hG (L i)
      (Algebra.IsQuadraticExtension.finrank_eq_two F (L i)) = (omega i).1 := by
    letI := primeCyclicNormCharacter_finite F (L i)
    exact normCharacterProduct_two F (L i)
      ((primeNormCharacter_card F (L i)).trans (Algebra.IsQuadraticExtension.finrank_eq_two F (L i)))
      (omega i) (homega i)
  let D (i : Fin 3) := Characters.restrictQuasiChar F (L i) (theta i).character * (omega i).1
  have hD (i j : Fin 3) (hij : i ≠ j) : D i = D j := by
    have h := (Characters.conjugacy Nat.prime_two hG (L i) (L j)
      (Algebra.IsQuadraticExtension.finrank_eq_two F (L i))
      (Algebra.IsQuadraticExtension.finrank_eq_two F (L j)) (hsep.ne hij)
      (theta i).character (theta j).character Theta (hc i) (hc j) hprimitive).2.2.1
    simpa only [hprod] using h
  have hL : Function.Injective L := fun i j h ↦ hsep (congrArg Ramification.intermediateNormRange h)
  obtain ⟨pi, hpi, _⟩ := monogenicUniformizer (L 0) K (hresK 0)
  let delta (i : Fin 3) := normUnits (L i) K (Units.mk0 (pi : K) hpi.ne_zero) ^ (2 * r - 1)
  have hdv (i) : (delta i : L i) = criticalNormLowerUniformizer (L i) K pi ^ (2 * r - 1) := rfl
  have hd (i) : ord (L i) (delta i : L i) = (((2 * r - 1 : ℕ) : ℤ) : WithTop ℤ) := by
    rw [hdv, ord_pow, criticalNormLowerUniformizer, ord_norm, hresK i, one_nsmul,
      ord_uniformizer K hpi]
    norm_cast
    simp
  have hC' : ord K (C : K) = ((-((2 * r - 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
    rw [hC]
    congr 1
    omega
  have htwoK : ((((2 * r - 1 : ℕ) : ℤ) + 1 : ℤ) : WithTop ℤ) ≤ ord K (2 : K) := by
    rw [show (2 : K) = algebraMap F K (2 : F) from (map_ofNat (algebraMap F K) 2).symm,
      IsScalarTower.algebraMap_apply F (L 0) K, ord_algebraMap, ord_algebraMap,
      ramification_two F (L 0) (hresF 0), ramification_two (L 0) K (hresK 0)]
    calc
      _ ≤ 2 • (2 • (((r : ℤ) : WithTop ℤ))) := by
        norm_cast
        simp only [nsmul_eq_mul]
        omega
      _ ≤ 2 • (2 • ord F (2 : F)) := by gcongr; exact htwo
  have hfactor (i) := equalBreaks_fullFactor (L i) hr (htF i) (hresF i) (hresK i)
    (theta i) (hm i) (omega i) (homega i) Psi hPsi (PsiL i) (hPsiL i)
    Theta (hc i) C hC (S i) (delta i) (hd i)
  have hscale (i) :
      LanglandsFirstMainLemma.localConstant (L i) (theta i).character (PsiL i).character *
          LanglandsFirstMainLemma.localConstant F (omega i).1 Psi.character =
        (D i alpha : ℂ) *
          (LanglandsFirstMainLemma.localConstant (L i) (theta i).character (psiL i).character *
            LanglandsFirstMainLemma.localConstant F (omega i).1 psi.character) := by
    have hw := equalBreaks_localConstant_scale F
      (canonicalLocalQuasiCharData F (omega i).1) psi alpha
    rw [canonicalLocalQuasiCharData_character] at hw
    rw [equalBreaks_localConstant_scale (L i) (theta i) (psiL i) (alphaL i), hw]
    change (_ * _) * (_ * _) = (((theta i).character (alphaL i) * (omega i).1 alpha : ℂˣ) : ℂ) * _
    rw [Units.val_mul]
    ring
  intro i j
  by_cases hij : i = j
  · subst j
    rfl
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
    fin_cases i <;> fin_cases j <;> decide
  have hroots := equalBreaks_distinctRoots (L i) (L j) (L k)
    (hL.ne hij) (hL.ne hki.symm) (hL.ne hkj.symm) (by omega : 0 < 2 * r - 1)
    (htK i) (htK j) (hresK i) (hresK j) pi hpi C hC' htwoK
    (S i).trace_order (S j).trace_order (S k).trace_order
  have hres := equalBreaks_residualFactors (L i) (L j) hr (htF i) (htF j) (htK i) (htK j)
    (hresF i) (hresF j) (hresK i) (hresK j) (theta i) (theta j) (hm i) (hm j)
    (omega i) (omega j) Psi hPsi (PsiL i) (PsiL j) (hPsiL i) (hPsiL j)
    Theta (hc i) (hc j) C hC (S i) (S j) pi hpi hroots (delta i) (delta j)
    (hd i) (hd j) (hdv i) (hdv j)
  have heq :
      LanglandsFirstMainLemma.localConstant (L i) (theta i).character (PsiL i).character *
          LanglandsFirstMainLemma.localConstant F (omega i).1 Psi.character =
        LanglandsFirstMainLemma.localConstant (L j) (theta j).character (PsiL j).character *
          LanglandsFirstMainLemma.localConstant F (omega j).1 Psi.character := by
    rw [hfactor i, hfactor j]
    change (D i (-1) : ℂ) * _ * _ * _ = (D j (-1) : ℂ) * _ * _ * _
    rw [hD i j hij, hres]
  rw [hscale i, hscale j, hD i j hij] at heq
  simpa only [hprod] using mul_left_cancel₀ (Units.ne_zero (D j alpha)) heq

end Comparison

end
end LanglandsSecondMainLemma.Dyadic.Nonmaximal
