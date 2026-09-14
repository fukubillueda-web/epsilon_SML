import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Dyadic.Equal.Origin
import LanglandsSecondMainLemma.Basic.NormTrace

/-!
# Moving the simultaneous origin by an element of the third field

The exact identities (D:EQ:adjust), (D:EQ:commonC), (D:EQ:commonE) and
bounds (D:EQ:a-bound), (D:EQ:Q-bound), (D:EQ:E-bound) of the corrected paper.
All fields, norms and traces below are the actual ones retained by the
proved `SimultaneousASGenerators` constructor in `Origin`.

Indices `0, 1, 2` are the paper's `1, 2, 3`. The correction `thirdQ` is
constructed as an upper trace; its equality with `aY + dᵢX` is proved.
The common error is an element of the base field, with its complete affine
factor retained. No character or stationary-phase hypothesis is used here.
-/

open LanglandsFirstMainLemma
namespace LanglandsSecondMainLemma.Dyadic.Equal
noncomputable section

open private originLine_degrees originLine_norm_trace origin_residueDegrees from
  LanglandsSecondMainLemma.Dyadic.Equal.Origin

section Diamond
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  [CharP F 2] [CharP K 2] [IsKleinFour Gal(K/F)]
local instance thirdNormValuativeRel (L : IntermediateField F K) : ValuativeRel L := Basic.intermediateFieldValuativeRel L
local instance thirdNormTopology (L : IntermediateField F K) : TopologicalSpace L := Basic.intermediateFieldTopology L
local instance thirdNormLocalField (L : IntermediateField F K) : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
local instance thirdNormLowerExtension (L : IntermediateField F K) : ValuativeExtension F L := Basic.intermediateField_lowerValuativeExtension L
local instance thirdNormUpperExtension (L : IntermediateField F K) : ValuativeExtension L K := Basic.intermediateField_upperValuativeExtension L
local instance thirdNormGalois (L : IntermediateField F K) : IsGalois F L := by
  letI : IsMulCommutative Gal(K/F) := IsKleinFour.isMulCommutative
  letI : L.fixingSubgroup.Normal := inferInstance
  have h := IsGalois.of_fixedField_normal_subgroup L.fixingSubgroup
  rwa [IsGalois.fixedField_fixingSubgroup L] at h

namespace SimultaneousASGenerators
variable {P : Residues.EqualCharacteristicPresentation F} (A : SimultaneousASGenerators F K P)

omit [IsGalois F K] [CharP F 2] [CharP K 2] in
private theorem fixes_generator (i : Fin 3) : A.g i (A.z i : K) = A.z i :=
  (IntermediateField.mem_fixedField_iff _ _).mp (A.z i).property _ (Or.inr rfl)

omit [IsGalois F K] [CharP F 2] [CharP K 2] in
private theorem lower_action (i : Fin 3) :
    (if i = 0 then A.g 1 else A.g 0) (A.z i : K) = (A.z i : K) + 1 := by
  fin_cases i
  · exact A.second_action
  · exact A.first_action
  · change A.g 0 (A.z 2 : K) = (A.z 2 : K) + 1
    rw [A.third_generator, map_add, A.fixes_generator 0, A.first_action]
    ring

omit [CharP F 2] [CharP K 2] in
/-- The lower quadratic norm and trace, embedded in the common top field. -/
private theorem lower_norm_trace (i : Fin 3)
    (x : IntermediateField.fixedField (originLine (A.g i))) :
    algebraMap F K (Algebra.norm F x) =
        (x : K) * (if i = 0 then A.g 1 else A.g 0) (x : K) ∧
      algebraMap F K (Algebra.trace F _ x) =
        (x : K) + (if i = 0 then A.g 1 else A.g 0) (x : K) := by
  classical
  let L := IntermediateField.fixedField (originLine (A.g i))
  let g := if i = 0 then A.g 1 else A.g 0
  let sigma : Gal(L/F) := AlgEquiv.restrictNormalHom L g
  have hsigma : sigma ≠ 1 := by
    intro h
    have hz := congrArg (fun s : Gal(L/F) ↦ (s (A.z i) : K)) h
    rw [AlgEquiv.restrictNormalHom_apply] at hz
    have hact := A.lower_action i
    change g (A.z i : K) = (A.z i : K) at hz
    rw [hz] at hact
    have hzero := add_left_cancel (show (A.z i : K) + 0 = (A.z i : K) + 1 by
      rw [add_zero]
      exact hact)
    exact zero_ne_one hzero
  have hcard : Fintype.card Gal(L/F) = 2 := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank,
      (originLine_degrees F K (A.g i) (A.nontrivial i)).1]
  have huniv : ({1, sigma} : Finset Gal(L/F)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simp [hsigma.symm, hcard]
  have hn := Algebra.norm_eq_prod_automorphisms F x
  have ht := trace_eq_sum_automorphisms (K := F) x
  rw [← huniv, Finset.prod_pair hsigma.symm] at hn
  rw [← huniv, Finset.sum_pair hsigma.symm] at ht
  constructor
  · have h := congrArg (algebraMap L K) hn
    simp only [map_mul, AlgEquiv.one_apply] at h
    change algebraMap L K (algebraMap F L (Algebra.norm F x)) =
      (x : K) * (sigma x : K) at h
    rw [← IsScalarTower.algebraMap_apply,
      show (sigma x : K) = g (x : K) from AlgEquiv.restrictNormalHom_apply L g x] at h
    exact h
  · have h := congrArg (algebraMap L K) ht
    simp only [map_add, AlgEquiv.one_apply] at h
    change algebraMap L K (algebraMap F L (Algebra.trace F L x)) =
      (x : K) + (sigma x : K) at h
    rw [← IsScalarTower.algebraMap_apply,
      show (sigma x : K) = g (x : K) from AlgEquiv.restrictNormalHom_apply L g x] at h
    exact h

/-- The actual lower trace `a = Tr_{L₃/F} X`. -/
def thirdTrace (X : IntermediateField.fixedField (originLine (A.g 2))) : F :=
  Algebra.trace F _ X

/-- The rational coordinate `p` in `X = p + a z₃`, constructed by trace. -/
def thirdConstant (X : IntermediateField.fixedField (originLine (A.g 2))) : F :=
  Algebra.trace F _ ((1 + A.z 2) * X)

/-- The actual moved numerator `C = Y + X` in `K`. -/
def thirdC (X : IntermediateField.fixedField (originLine (A.g 2))) : K := A.Y + X

/-- The correction belongs to `Lᵢ` because it is an actual upper trace.
For `i = 0, 1`, it equals the paper's `aY + dᵢX`. -/
def thirdQ (X : IntermediateField.fixedField (originLine (A.g 2))) (i : Fin 3) :
    IntermediateField.fixedField (originLine (A.g i)) :=
  Algebra.trace _ K (A.Y * A.g i (X : K))

/-- The rational factor `a a₃ + κ₃ X`, expressed in its exact coordinates. -/
def thirdErrorFactor (X : IntermediateField.fixedField (originLine (A.g 2))) : F :=
  A.thirdTrace X * A.B + A.kappa 2 * A.thirdConstant X

/-- The common lower-norm error, including the full constant contribution. -/
def thirdError (X : IntermediateField.fixedField (originLine (A.g 2))) : F :=
  A.thirdTrace X * A.thirdErrorFactor X

/-- Trace constructs the two exact rational coordinates of every third-field
point, without a norm-surjectivity or representative assumption. -/
theorem third_coordinates (X : IntermediateField.fixedField (originLine (A.g 2))) :
    (X : K) = algebraMap F K (A.thirdConstant X) +
      algebraMap F K (A.thirdTrace X) * (A.z 2 : K) := by
  have ha := (A.lower_norm_trace 2 X).2
  have hp := (A.lower_norm_trace 2 ((1 + A.z 2) * X)).2
  have hz := A.lower_action 2
  simp only [show (2 : Fin 3) ≠ 0 by decide, if_false] at ha hp hz
  change algebraMap F K (A.thirdTrace X) = _ at ha
  change algebraMap F K (A.thirdConstant X) =
    (1 + (A.z 2 : K)) * (X : K) + A.g 0 ((1 + (A.z 2 : K)) * (X : K)) at hp
  rw [map_mul, map_add, map_one, hz] at hp
  rw [ha, hp]
  ring_nf
  simp [CharTwo.two_eq_zero]

omit [IsGalois F K] [CharP F 2] [CharP K 2] in
private theorem third_generator_action (i : Fin 3) (hi : i ≠ 2) :
    A.g i (A.z 2 : K) = (A.z 2 : K) + 1 := by
  fin_cases i
  · exact A.lower_action 2
  · change A.g 1 (A.z 2 : K) = (A.z 2 : K) + 1
    rw [A.third_generator, map_add, A.second_action, A.fixes_generator 1]
    ring
  · exact (hi rfl).elim

/-- Both comparison involutions act on `X` by its actual lower trace. -/
theorem third_conjugate (X : IntermediateField.fixedField (originLine (A.g 2)))
    (i : Fin 3) (hi : i ≠ 2) :
    A.g i (X : K) = (X : K) + algebraMap F K (A.thirdTrace X) := by
  rw [A.third_coordinates X]
  simp only [map_add, map_mul, AlgEquiv.commutes, A.third_generator_action i hi]
  ring

/-- The trace definition constructs the exact correction in (D:EQ:adjust). -/
theorem thirdQ_coe (X : IntermediateField.fixedField (originLine (A.g 2)))
    (i : Fin 3) (hi : i ≠ 2) :
    (A.thirdQ X i : K) = algebraMap F K (A.thirdTrace X) * A.Y +
      algebraMap F K (A.root i) * (X : K) := by
  have h := (originLine_norm_trace F K (A.g i) (A.nontrivial i)
    (A.Y * A.g i (X : K))).2
  change (A.thirdQ X i : K) = _ at h
  have hY : A.g i A.Y = A.Y + algebraMap F K (A.root i) := by
    linear_combination (A.exact_origin i).1
  have hX : A.g i (A.g i (X : K)) = (X : K) := by
    rw [← AlgEquiv.mul_apply, IsKleinFour.mul_self, AlgEquiv.one_apply]
  rw [h, map_mul, hY, hX, A.third_conjugate X i hi]
  ring_nf
  simp [CharTwo.two_eq_zero]

/-- The explicit `p + qz₃` calculation keeps the same rational coordinates
in the two different lower fields. -/
theorem thirdQ_coordinates (X : IntermediateField.fixedField (originLine (A.g 2)))
    (i : Fin 3) (hi : i ≠ 2) :
    let L := IntermediateField.fixedField (originLine (A.g i))
    A.thirdQ X i = algebraMap F L (A.root i * A.thirdConstant X) +
      algebraMap F L (A.thirdTrace X * A.root 2) * A.z i := by
  apply (algebraMap (IntermediateField.fixedField (originLine (A.g i))) K).injective
  change (A.thirdQ X i : K) = _
  rw [A.thirdQ_coe X i hi, A.third_coordinates X, A.third_generator, Y,
    simultaneousOrigin]
  simp only [map_add, map_mul, ← IsScalarTower.algebraMap_apply, A.root_third,
    IntermediateField.algebraMap_apply]
  fin_cases i <;> dsimp
  · ring_nf
    simp [CharTwo.two_eq_zero]
  · ring_nf
    simp [CharTwo.two_eq_zero]
  · exact (hi rfl).elim

/-- The factor of the common error is rational, with its actual third-field
expression, not merely its leading term. -/
theorem thirdErrorFactor_spec (X : IntermediateField.fixedField (originLine (A.g 2))) :
    let L := IntermediateField.fixedField (originLine (A.g 2))
    algebraMap F L (A.thirdErrorFactor X) =
      algebraMap F L (A.thirdTrace X) * Algebra.norm L A.Y +
        algebraMap F L (A.kappa 2) * X := by
  let L := IntermediateField.fixedField (originLine (A.g 2))
  have hX : X = algebraMap F L (A.thirdConstant X) +
      algebraMap F L (A.thirdTrace X) * A.z 2 := by
    apply (algebraMap L K).injective
    exact A.third_coordinates X
  change algebraMap F L (A.thirdErrorFactor X) =
    algebraMap F L (A.thirdTrace X) * Algebra.norm L A.Y +
      algebraMap F L (A.kappa 2) * X
  rw [(A.exact_origin 2).2.2]
  calc
    _ = algebraMap F L (A.thirdTrace X) *
          (algebraMap F L (A.kappa 2) * A.z 2 + algebraMap F L A.B) +
        algebraMap F L (A.kappa 2) *
          (algebraMap F L (A.thirdConstant X) +
            algebraMap F L (A.thirdTrace X) * A.z 2) := by
      simp only [thirdErrorFactor, map_add, map_mul]
      ring_nf
      simp [CharTwo.two_eq_zero]
    _ = _ := by rw [← hX]

omit [CharP F 2] in
private theorem lower_norm_linear (i : Fin 3) (p q : F) :
    let L := IntermediateField.fixedField (originLine (A.g i))
    Algebra.norm F (algebraMap F L p + algebraMap F L q * A.z i) =
      p ^ 2 + p * q + q ^ 2 * A.f i := by
  let L := IntermediateField.fixedField (originLine (A.g i))
  apply (algebraMap F K).injective
  rw [(A.lower_norm_trace i _).1]
  change (algebraMap F K p + algebraMap F K q * (A.z i : K)) *
    (if i = 0 then A.g 1 else A.g 0)
      (algebraMap F K p + algebraMap F K q * (A.z i : K)) = _
  simp only [map_add, map_mul, AlgEquiv.commutes, A.lower_action i, map_pow]
  have hz : (A.z i : K) ^ 2 + (A.z i : K) = algebraMap F K (A.f i) :=
    congrArg (fun x : L ↦ (x : K)) (A.edge i).1
  calc
    _ = algebraMap F K p ^ 2 + algebraMap F K p * algebraMap F K q +
        algebraMap F K q ^ 2 * ((A.z i : K) ^ 2 + (A.z i : K)) := by
      ring_nf
      simp [CharTwo.two_eq_zero]
    _ = _ := by rw [hz]

/-- The actual third norm, in the exact trace-constructed coordinates. -/
theorem third_norm_coordinates (X : IntermediateField.fixedField (originLine (A.g 2))) :
    Algebra.norm F X = A.thirdConstant X ^ 2 + A.thirdConstant X * A.thirdTrace X +
      A.thirdTrace X ^ 2 * A.f 2 := by
  have hX : X = algebraMap F _ (A.thirdConstant X) +
      algebraMap F _ (A.thirdTrace X) * A.z 2 := by
    apply (algebraMap (IntermediateField.fixedField (originLine (A.g 2))) K).injective
    exact A.third_coordinates X
  calc
    _ = Algebra.norm F (algebraMap F _ (A.thirdConstant X) +
        algebraMap F _ (A.thirdTrace X) * A.z 2) := congrArg (Algebra.norm F) hX
    _ = _ := A.lower_norm_linear 2 _ _

/-- The complete common error in the two actual lower norms (D:EQ:commonE). -/
theorem thirdQ_norm (X : IntermediateField.fixedField (originLine (A.g 2)))
    (i : Fin 3) (hi : i ≠ 2) :
    Algebra.norm F (A.thirdQ X i) = A.beta i * Algebra.norm F X + A.thirdError X := by
  rw [A.thirdQ_coordinates X i hi, A.lower_norm_linear, A.third_norm_coordinates X]
  simp only [thirdError, thirdErrorFactor, B, A.third_parameter, kappa,
    ← (A.scalar_data 0).1, ← (A.scalar_data 1).1, A.root_third]
  fin_cases i <;> dsimp
  · rw [← (A.scalar_data 0).1]
    ring_nf
    simp [CharTwo.two_eq_zero]
  · rw [← (A.scalar_data 1).1]
    ring_nf
    simp [CharTwo.two_eq_zero]
  · exact (hi rfl).elim

/-- The two moved upper norms and traces are exact field identities
(D:EQ:commonC). -/
theorem thirdC_norm_trace (X : IntermediateField.fixedField (originLine (A.g 2)))
    (i : Fin 3) (hi : i ≠ 2) :
    let L := IntermediateField.fixedField (originLine (A.g i))
    Algebra.norm L (A.thirdC X) = Algebra.norm L A.Y +
        algebraMap F L (Algebra.norm F X) + A.thirdQ X i ∧
      Algebra.trace L K (A.thirdC X) = algebraMap F L (A.root i + A.thirdTrace X) := by
  let L := IntermediateField.fixedField (originLine (A.g i))
  have hY : A.g i A.Y = A.Y + algebraMap F K (A.root i) := by
    linear_combination (A.exact_origin i).1
  have hnX : algebraMap F K (Algebra.norm F X) =
      (X : K) * ((X : K) + algebraMap F K (A.thirdTrace X)) := by
    rw [(A.lower_norm_trace 2 X).1]
    exact congrArg ((X : K) * ·) (A.third_conjugate X 0 (by decide))
  constructor
  · apply (algebraMap L K).injective
    rw [(originLine_norm_trace F K (A.g i) (A.nontrivial i) (A.thirdC X)).1,
      map_add, map_add, (originLine_norm_trace F K (A.g i) (A.nontrivial i) A.Y).1,
      ← IsScalarTower.algebraMap_apply, hnX]
    change A.thirdC X * A.g i (A.thirdC X) = _ + (A.thirdQ X i : K)
    rw [thirdC, map_add, hY, A.third_conjugate X i hi, A.thirdQ_coe X i hi]
    ring_nf
    simp [CharTwo.two_eq_zero]
  · apply (algebraMap L K).injective
    rw [(originLine_norm_trace F K (A.g i) (A.nontrivial i) (A.thirdC X)).2,
      ← IsScalarTower.algebraMap_apply, map_add, thirdC, map_add, hY,
      A.third_conjugate X i hi]
    ring_nf
    simp [CharTwo.two_eq_zero]

omit [CharP F 2] [CharP K 2] in
private theorem ramification_indices (hres : residueDegree F K = 1) (i : Fin 3) :
    let L := IntermediateField.fixedField (originLine (A.g i))
    ramificationIndex F L = 2 ∧ ramificationIndex L K = 2 := by
  let L := IntermediateField.fixedField (originLine (A.g i))
  have hl := finrank_eq_ramificationIndex_mul_residueDegree F L
  have hu := finrank_eq_ramificationIndex_mul_residueDegree L K
  rw [(originLine_degrees F K (A.g i) (A.nontrivial i)).1,
    (origin_residueDegrees F K hres L).1, mul_one] at hl
  rw [(originLine_degrees F K (A.g i) (A.nontrivial i)).2,
    (origin_residueDegrees F K hres L).2, mul_one] at hu
  exact ⟨hl.symm, hu.symm⟩

/-- The lower trace bound (D:EQ:a-bound), with integer ceiling `(h+1)/2`.
The hypothesis is whole-ideal membership, so it also permits `X = 0`. -/
theorem thirdTrace_bound (hres : residueDegree F K = 1)
    (X : IntermediateField.fixedField (originLine (A.g 2))) (h : ℤ)
    (hX : X ∈ lattice _ (-h)) :
    ((((A.t 1 : ℤ) + 1) / 2 - (h + 1) / 2 : ℤ) : WithTop ℤ) ≤
      ord F (A.thirdTrace X) := by
  let L := IntermediateField.fixedField (originLine (A.g 2))
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F L
    (origin_residueDegrees F K hres L).1
  have ht := trace_mem_lattice_floor F L pi hpi hgen (-h) hX
  change (((-h + (differentExponent F L : ℤ)) / (ramificationIndex F L : ℤ) : ℤ) :
    WithTop ℤ) ≤ ord F (A.thirdTrace X) at ht
  rw [(A.edge 2).2.2.2.2.2.2.2.2, A.third_break, (A.ramification_indices hres 2).1] at ht
  convert ht using 1
  congr 1
  have hodd : Odd (A.t 1 : ℤ) := by exact_mod_cast (A.edge 1).2.2.2.2.1
  obtain ⟨r, hr⟩ := hodd
  norm_num
  omega

/-- The upper trace proves both (D:EQ:Q-bound) inequalities directly,
without making separate assumptions on the two summands of `aY + dᵢX`. -/
theorem thirdQ_bound (hres : residueDegree F K = 1)
    (X : IntermediateField.fixedField (originLine (A.g 2))) (h : ℤ)
    (hX : X ∈ lattice _ (-h)) (i : Fin 3) :
    ((((if i = 0 then (A.t 1 : ℤ) - A.t 0 else 0) - h : ℤ)) : WithTop ℤ) ≤
      ord (IntermediateField.fixedField (originLine (A.g i))) (A.thirdQ X i) := by
  let L := IntermediateField.fixedField (originLine (A.g i))
  let L₃ := IntermediateField.fixedField (originLine (A.g 2))
  change ((-h : ℤ) : WithTop ℤ) ≤ ord L₃ X at hX
  have htop : ((-2 * h : ℤ) : WithTop ℤ) ≤ ord K (X : K) := by
    change _ ≤ ord K (algebraMap L₃ K X)
    rw [ord_algebraMap, (A.ramification_indices hres 2).2, two_nsmul]
    have hsum := add_le_add hX hX
    simpa only [← WithTop.coe_add, show -h + -h = -2 * h by omega] using hsum
  have hprod : A.Y * A.g i (X : K) ∈ lattice K (-(A.t 0 : ℤ) - 2 * h) := by
    change _ ≤ ord K (A.Y * A.g i (X : K))
    rw [ord_mul, ord_galoisConjugate F K, (A.origin_orders hres).1]
    have hsum := add_le_add (le_refl ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ)) htop
    simpa only [← WithTop.coe_add, sub_eq_add_neg, neg_mul] using hsum
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer L K
    (origin_residueDegrees F K hres L).2
  have ht := trace_mem_lattice_floor L K pi hpi hgen (-(A.t 0 : ℤ) - 2 * h) hprod
  change (((-(A.t 0 : ℤ) - 2 * h + (differentExponent L K : ℤ)) /
    (ramificationIndex L K : ℤ) : ℤ) : WithTop ℤ) ≤ ord L (A.thirdQ X i) at ht
  rw [A.upper_different hres i, (A.ramification_indices hres i).2] at ht
  convert ht using 1
  congr 1
  split_ifs <;> norm_num <;> omega

omit [IsGalois F K] [CharP F 2] [CharP K 2] in
private theorem twice_delta :
    2 * (((A.t 1 : ℤ) - A.t 0) / 2) = (A.t 1 : ℤ) - A.t 0 := by
  have ho₁ : Odd (A.t 1 : ℤ) := by exact_mod_cast (A.edge 1).2.2.2.2.1
  have ho₀ : Odd (A.t 0 : ℤ) := by exact_mod_cast (A.edge 0).2.2.2.2.1
  obtain ⟨r₁, hr₁⟩ := ho₁
  obtain ⟨r₀, hr₀⟩ := ho₀
  omega

/-- The invariant factor has downstairs depth `δ - floor(h/2)`, as in
the proof of (D:EQ:E-bound). Infinity is allowed throughout. -/
theorem thirdErrorFactor_bound (hres : residueDegree F K = 1)
    (X : IntermediateField.fixedField (originLine (A.g 2))) (h : ℤ)
    (hX : X ∈ lattice _ (-h)) :
    (((((A.t 1 : ℤ) - A.t 0) / 2 - h / 2 : ℤ)) : WithTop ℤ) ≤
      ord F (A.thirdErrorFactor X) := by
  let L := IntermediateField.fixedField (originLine (A.g 2))
  have ha := A.thirdTrace_bound hres X h hX
  have hκ : ord L (algebraMap F L (A.kappa 2)) =
      (((A.t 1 : ℤ) - A.t 0 : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, (A.ramification_indices hres 2).1,
      A.kappa_order, A.third_break, ← WithTop.coe_nsmul]
    congr 1
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using A.twice_delta
  have hleft : (((A.t 1 : ℤ) - A.t 0 - h : ℤ) : WithTop ℤ) ≤
      ord L (algebraMap F L (A.thirdTrace X) * Algebra.norm L A.Y) := by
    rw [ord_mul, ord_algebraMap, (A.ramification_indices hres 2).1, two_nsmul,
      ((A.origin_orders hres).2.1 2).1]
    have hsum := add_le_add (add_le_add ha ha)
      (le_refl ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ))
    simp only [← WithTop.coe_add] at hsum
    apply le_trans (WithTop.coe_le_coe.mpr ?_) hsum
    have hodd : Odd (A.t 1 : ℤ) := by exact_mod_cast (A.edge 1).2.2.2.2.1
    obtain ⟨r, hr⟩ := hodd
    omega
  have hright : (((A.t 1 : ℤ) - A.t 0 - h : ℤ) : WithTop ℤ) ≤
      ord L (algebraMap F L (A.kappa 2) * X) := by
    rw [ord_mul, hκ]
    change ((-h : ℤ) : WithTop ℤ) ≤ ord L X at hX
    simpa only [← WithTop.coe_add, sub_eq_add_neg] using
      add_le_add (le_refl (((A.t 1 : ℤ) - A.t 0 : ℤ) : WithTop ℤ)) hX
  have hfactor : (((A.t 1 : ℤ) - A.t 0 - h : ℤ) : WithTop ℤ) ≤
      ord L (algebraMap F L (A.thirdErrorFactor X)) := by
    rw [A.thirdErrorFactor_spec X]
    exact (le_min hleft hright).trans (ord_add L _ _)
  rw [ord_algebraMap, (A.ramification_indices hres 2).1] at hfactor
  by_cases hz : ord F (A.thirdErrorFactor X) = ⊤
  · rw [hz]
    exact le_top
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hz
  rw [← hv, ← WithTop.coe_nsmul] at hfactor
  rw [← hv]
  apply WithTop.coe_le_coe.mpr
  have hbound := WithTop.coe_le_coe.mp hfactor
  have hdelta := A.twice_delta
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at hbound
  omega

/-- The common error bound (D:EQ:E-bound). The two integer roundings add
to `h`, including negative `h`; a vanishing trace gives infinite order. -/
theorem thirdError_bound (hres : residueDegree F K = 1)
    (X : IntermediateField.fixedField (originLine (A.g 2))) (h : ℤ)
    (hX : X ∈ lattice _ (-h)) :
    (((((A.t 1 : ℤ) + 1) / 2 + ((A.t 1 : ℤ) - A.t 0) / 2 - h : ℤ)) : WithTop ℤ) ≤
      ord F (A.thirdError X) := by
  rw [thirdError, ord_mul]
  have hb := add_le_add (A.thirdTrace_bound hres X h hX)
    (A.thirdErrorFactor_bound hres X h hX)
  simp only [← WithTop.coe_add] at hb
  convert hb using 1
  congr 1
  omega

end SimultaneousASGenerators

/-- The exact third-field adjustment (D:EQ:adjust), (D:EQ:commonC) and
(D:EQ:commonE), for the simultaneous origin constructed in `Origin`.
The common error lies in `F`; the displayed third-field equality retains
its complete factor `a a₃ + κ₃ X`. Only indices `0, 1` are comparison fields. -/
theorem dyadicEqual_thirdNorm_identities
    {P : Residues.EqualCharacteristicPresentation F} (A : SimultaneousASGenerators F K P)
    (X : IntermediateField.fixedField (originLine (A.g 2))) :
    let L₃ := IntermediateField.fixedField (originLine (A.g 2))
    algebraMap F L₃ (A.thirdError X) = algebraMap F L₃ (A.thirdTrace X) *
        (algebraMap F L₃ (A.thirdTrace X) * Algebra.norm L₃ A.Y +
          algebraMap F L₃ (A.kappa 2) * X) ∧
      ∀ i : Fin 3, i ≠ 2 →
        let L := IntermediateField.fixedField (originLine (A.g i))
        (A.thirdQ X i : K) = algebraMap F K (A.thirdTrace X) * A.Y +
            algebraMap F K (A.root i) * (X : K) ∧
          Algebra.norm L (A.thirdC X) = Algebra.norm L A.Y +
            algebraMap F L (Algebra.norm F X) + A.thirdQ X i ∧
          Algebra.trace L K (A.thirdC X) = algebraMap F L (A.root i + A.thirdTrace X) ∧
          Algebra.norm F (A.thirdQ X i) = A.beta i * Algebra.norm F X + A.thirdError X := by
  refine ⟨?_, fun i hi ↦ ⟨A.thirdQ_coe X i hi, (A.thirdC_norm_trace X i hi).1,
    (A.thirdC_norm_trace X i hi).2, A.thirdQ_norm X i hi⟩⟩
  rw [SimultaneousASGenerators.thirdError, map_mul, A.thirdErrorFactor_spec X]

/-- The bounds (D:EQ:a-bound), (D:EQ:Q-bound), (D:EQ:E-bound), together
with the rational-factor estimate used in their proof. Here `(h+1)/2` is
the integer ceiling of `h/2`, while `h/2` is its integer floor. There is no
sign restriction on `h` and orders take values in `WithTop ℤ`. The stronger
whole-ideal formulation includes the paper's shell `v_{L₃} X = -h`. -/
theorem dyadicEqual_thirdNorm_bounds
    {P : Residues.EqualCharacteristicPresentation F} (A : SimultaneousASGenerators F K P)
    (hres : residueDegree F K = 1)
    (X : IntermediateField.fixedField (originLine (A.g 2))) (h : ℤ)
    (hX : X ∈ lattice (IntermediateField.fixedField (originLine (A.g 2))) (-h)) :
    let r₂ : ℤ := ((A.t 1 : ℤ) + 1) / 2
    let δ : ℤ := ((A.t 1 : ℤ) - A.t 0) / 2
    ((r₂ - (h + 1) / 2 : ℤ) : WithTop ℤ) ≤ ord F (A.thirdTrace X) ∧
      ((2 * δ - h : ℤ) : WithTop ℤ) ≤
        ord (IntermediateField.fixedField (originLine (A.g 0))) (A.thirdQ X 0) ∧
      ((-h : ℤ) : WithTop ℤ) ≤
        ord (IntermediateField.fixedField (originLine (A.g 1))) (A.thirdQ X 1) ∧
      ((δ - h / 2 : ℤ) : WithTop ℤ) ≤ ord F (A.thirdErrorFactor X) ∧
      ((r₂ + δ - h : ℤ) : WithTop ℤ) ≤ ord F (A.thirdError X) := by
  refine ⟨A.thirdTrace_bound hres X h hX, ?_, ?_,
    A.thirdErrorFactor_bound hres X h hX, A.thirdError_bound hres X h hX⟩
  · simpa only [ite_true, A.twice_delta] using A.thirdQ_bound hres X h hX 0
  · simpa using A.thirdQ_bound hres X h hX 1

end Diamond
end
end LanglandsSecondMainLemma.Dyadic.Equal
