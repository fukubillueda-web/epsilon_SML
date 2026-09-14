import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Dyadic.Maximal.Origin

/-!
# Dyadic / Maximal / Common Error

This file formalizes the exact adjustment identities preceding
`D:MX:errors` and the four bounds in that lemma.  All norms and traces
are the genuine maps on the three intermediate fields.  In particular,
the common error is first defined intrinsically from the first lower
norm, and the proof identifies it with the paper's conjugate product
and with the corresponding second lower norm.

Blueprint: `blueprint/tasks/Dyadic/Maximal/CommonError.md`.
Paper: `D:MX:adjust-identities`, `D:MX:Delta`, and `D:MX:errors`.
-/

namespace LanglandsSecondMainLemma.Dyadic.Maximal

open LanglandsFirstMainLemma

noncomputable section

private theorem quadratic_trace_eq
    {E M : Type*} [Field E] [Field M] [Algebra E M]
    [FiniteDimensional E M] [IsGalois E M]
    (sigma : Gal(M/E)) (hsigma : sigma ≠ 1)
    (hdegree : Module.finrank E M = 2) (x : M) :
    algebraMap E M (trace E M x) = x + sigma x := by
  classical
  rw [trace_eq_sum_automorphisms]
  have hcard : Fintype.card Gal(M/E) = 2 := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, hdegree]
  have huniv : ({sigma, (1 : Gal(M/E))} : Finset Gal(M/E)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simpa using hsigma),
      Finset.card_singleton, hcard]
  rw [← huniv]
  simp [hsigma, add_comm]

private theorem quadratic_norm_eq
    {E M : Type*} [Field E] [Field M] [Algebra E M]
    [FiniteDimensional E M] [IsGalois E M]
    (sigma : Gal(M/E)) (hsigma : sigma ≠ 1)
    (hdegree : Module.finrank E M = 2) (x : M) :
    algebraMap E M (norm E M x) = x * sigma x := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms]
  have hcard : Fintype.card Gal(M/E) = 2 := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, hdegree]
  have huniv : ({sigma, (1 : Gal(M/E))} : Finset Gal(M/E)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simpa using hsigma),
      Finset.card_singleton, hcard]
  rw [← huniv]
  simp [hsigma, mul_comm]

/-- The quadratic norm of a translation by a base scalar. -/
private theorem quadratic_norm_sub_base
    {E M : Type*} [Field E] [Field M] [Algebra E M]
    [FiniteDimensional E M] [IsGalois E M]
    (sigma : Gal(M/E)) (hsigma : sigma ≠ 1)
    (hdegree : Module.finrank E M = 2) (x : M) (c : E) :
    norm E M (x - algebraMap E M c) =
      norm E M x + c ^ 2 - c * trace E M x := by
  apply (algebraMap E M).injective
  simp only [map_sub, map_add, map_mul, map_pow]
  rw [quadratic_norm_eq sigma hsigma hdegree,
    quadratic_norm_eq sigma hsigma hdegree,
    quadratic_trace_eq sigma hsigma hdegree]
  simp only [map_sub, sigma.commutes]
  ring

/-- Residue degrees multiply through the canonical valuation-compatible
structure on an actual intermediate field. -/
private theorem intermediate_residueDegree_mul
    {F K : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]
    (L : IntermediateField F K) :
    letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
    letI : TopologicalSpace L := Basic.intermediateFieldTopology L
    letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
    letI : ValuativeExtension F L :=
      Basic.intermediateField_lowerValuativeExtension L
    letI : ValuativeExtension L K :=
      Basic.intermediateField_upperValuativeExtension L
    residueDegree F L * residueDegree L K = residueDegree F K := by
  letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
  letI : TopologicalSpace L := Basic.intermediateFieldTopology L
  letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
  letI : ValuativeExtension F L :=
    Basic.intermediateField_lowerValuativeExtension L
  letI : ValuativeExtension L K :=
    Basic.intermediateField_upperValuativeExtension L
  letI : IsScalarTower
      (ringOfIntegers F) (ringOfIntegers L) (ringOfIntegers K) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap F K (x : F) = algebraMap L K (algebraMap F L (x : F))
      rw [← IsScalarTower.algebraMap_apply F L K])
  letI : IsLocalHom
      (algebraMap (ringOfIntegers F) (ringOfIntegers L)) := inferInstance
  letI : IsLocalHom
      (algebraMap (ringOfIntegers L) (ringOfIntegers K)) := inferInstance
  rw [residueDegree_eq_finrank_residueField,
    residueDegree_eq_finrank_residueField,
    residueDegree_eq_finrank_residueField]
  exact Module.finrank_mul_finrank
    (ResidueField F) (ResidueField L) (ResidueField K)

section QuadraticAlgebra

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
  [Module.Finite F K] [IsGalois F K]

/-- The two terms in the crossed trace, evaluated in the top field. -/
private theorem quadratic_crossed_trace
    (L M : IntermediateField F K) (g : Gal(K/L)) (hg : g ≠ 1)
    (hdegree : Module.finrank L K = 2) (q : Gal(M/F)) (X : M) (Y : K)
    (hX : g (algebraMap M K X) = algebraMap M K (q X))
    (hX' : g (algebraMap M K (q X)) = algebraMap M K X) :
    algebraMap L K (trace L K (Y * g (algebraMap M K X))) =
      Y * algebraMap M K (q X) + g Y * algebraMap M K X := by
  rw [quadratic_trace_eq g hg hdegree, map_mul, hX, hX']

/-- Norm and trace of `Y - X` along either upper quadratic edge. -/
private theorem quadratic_adjustment_identities
    (L M : IntermediateField F K) [IsGalois F M]
    (g : Gal(K/L)) (hg : g ≠ 1) (hdegree : Module.finrank L K = 2)
    (q : Gal(M/F)) (hq : q ≠ 1) (hdegreeM : Module.finrank F M = 2)
    (X : M) (Y : K)
    (hX : g (algebraMap M K X) = algebraMap M K (q X))
    (hX' : g (algebraMap M K (q X)) = algebraMap M K X) :
    norm L K (Y - algebraMap M K X) =
        norm L K Y + algebraMap F L (norm F M X) -
          trace L K (Y * g (algebraMap M K X)) ∧
      trace L K (Y - algebraMap M K X) =
        trace L K Y - algebraMap F L (trace F M X) := by
  have hnorm : algebraMap F K (norm F M X) =
      algebraMap M K X * algebraMap M K (q X) := by
    rw [IsScalarTower.algebraMap_apply F M K, quadratic_norm_eq q hq hdegreeM,
      map_mul]
  have htrace : algebraMap F K (trace F M X) =
      algebraMap M K X + algebraMap M K (q X) := by
    rw [IsScalarTower.algebraMap_apply F M K, quadratic_trace_eq q hq hdegreeM,
      map_add]
  constructor
  · apply (algebraMap L K).injective
    rw [quadratic_norm_eq g hg hdegree, map_sub]
    simp only [map_sub, map_add]
    rw [quadratic_crossed_trace L M g hg hdegree q X Y hX hX',
      quadratic_norm_eq g hg hdegree, hX,
      ← IsScalarTower.algebraMap_apply F L K, hnorm]
    ring
  · apply (algebraMap L K).injective
    rw [quadratic_trace_eq g hg hdegree, map_sub, hX, map_sub,
      quadratic_trace_eq g hg hdegree,
      ← IsScalarTower.algebraMap_apply F L K, htrace]
    ring

/-- Translating an upper trace whose total trace is `-2` gives the common increment. -/
private theorem quadratic_trace_norm_increment
    (L : IntermediateField F K) [IsGalois F L]
    (q : Gal(L/F)) (hq : q ≠ 1) (hdegree : Module.finrank F L = 2)
    (Y : K) (p : F) (htrace : trace F K Y = -2) :
    norm F L (trace L K Y - algebraMap F L p) =
      norm F L (trace L K Y) + (p ^ 2 + 2 * p) := by
  rw [quadratic_norm_sub_base q hq hdegree, Algebra.trace_trace, htrace]
  ring

end QuadraticAlgebra

namespace AlignmentData

variable {F K : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]
variable {pi : ringOfIntegers F} {e a b : Nat}
  {u0 w0 : (ringOfIntegers F)ˣ} {s R0 : K}

/-- The paper's translated top-field origin `C = Y - X`. -/
def adjustedOrigin (D : AlignmentData pi e a b u0 w0 s R0)
    (X : D.thirdField) : K :=
  D.origin - algebraMap D.thirdField K X

/-- The common base norm `A = n_3(X)`. -/
def adjustmentNorm (D : AlignmentData pi e a b u0 w0 s R0)
    (X : D.thirdField) : F :=
  norm F D.thirdField X

/-- The lower trace coordinate `p_X = tr_3(X)`. -/
def adjustmentTrace (D : AlignmentData pi e a b u0 w0 s R0)
    (X : D.thirdField) : F :=
  trace F D.thirdField X

/-- The first crossed trace `Q_1 = S_1(Y g_1 X)`. -/
def firstCrossedTrace (D : AlignmentData pi e a b u0 w0 s R0)
    (g1 : Gal(K/D.firstField)) (X : D.thirdField) : D.firstField :=
  trace D.firstField K
    (D.origin * g1 (algebraMap D.thirdField K X))

/-- The second crossed trace `Q_2 = S_2(Y g_2 X)`. -/
def secondCrossedTrace (D : AlignmentData pi e a b u0 w0 s R0)
    (g2 : Gal(K/D.secondField)) (X : D.thirdField) : D.secondField :=
  trace D.secondField K
    (D.origin * g2 (algebraMap D.thirdField K X))

/-- The common trace-norm increment `Delta = p_X^2 + 2 p_X`. -/
def traceNormIncrement (D : AlignmentData pi e a b u0 w0 s R0)
    (X : D.thirdField) : F :=
  D.adjustmentTrace X ^ 2 + 2 * D.adjustmentTrace X

/-- The intrinsic common error.  The theorem below proves that this is
also the second weighted lower-norm error and the conjugate product in
the paper. -/
def commonErrorTerm (D : AlignmentData pi e a b u0 w0 s R0)
    (g1 : Gal(K/D.firstField)) (X : D.thirdField) : F :=
  norm F D.firstField (D.firstCrossedTrace g1 X) -
    D.beta1 * D.adjustmentNorm X

end AlignmentData

private theorem actualGaloisGroup_isMulCommutative
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (hG : Gal(K/F) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    IsMulCommutative Gal(K/F) := by
  apply IsMulCommutative.of_comm
  intro sigma tau
  apply hG.injective
  simpa only [map_mul] using mul_comm (hG sigma) (hG tau)

private theorem actualIntermediateField_isGalois
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    [Module.Finite F K] [IsGalois F K]
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (L : IntermediateField F K) : IsGalois F L := by
  letI : IsMulCommutative Gal(K/F) :=
    actualGaloisGroup_isMulCommutative (Classical.choice hG)
  letI : L.fixingSubgroup.Normal := inferInstance
  have hfixed : IsGalois F (IntermediateField.fixedField L.fixingSubgroup) :=
    IsGalois.of_fixedField_normal_subgroup L.fixingSubgroup
  rw [IsGalois.fixedField_fixingSubgroup L] at hfixed
  exact hfixed

/-- The actual lower break on the lower edge `F -> L`, installed using
the accepted intermediate-field valuation and the genuine Klein-four
tower constructor. -/
def actualLowerBreak
    {F K : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (_hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (L : IntermediateField F K) (_hdegree : Module.finrank F L = 2)
    (t : Nat) : Prop := by
  letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
  letI : TopologicalSpace L := Basic.intermediateFieldTopology L
  letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
  letI : ValuativeExtension F L :=
    Basic.intermediateField_lowerValuativeExtension L
  letI : IsGalois F L := actualIntermediateField_isGalois _hG L
  exact PrimeCyclicExtension.IsLowerBreak F L t

/-- The actual lower break on the upper edge `L -> K`, with the same
canonical tower installation as `actualLowerBreak`. -/
def actualUpperBreak
    {F K : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (_hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (L : IntermediateField F K) (_hdegree : Module.finrank F L = 2)
    (t : Nat) : Prop := by
  letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
  letI : TopologicalSpace L := Basic.intermediateFieldTopology L
  letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
  letI : ValuativeExtension L K :=
    Basic.intermediateField_upperValuativeExtension L
  exact PrimeCyclicExtension.IsLowerBreak L K t

variable {F K : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]
variable {pi : ringOfIntegers F} {e a b : Nat}
  {u0 w0 : (ringOfIntegers F)ˣ} {s R0 : K}

/-- The exact identities and weighted bounds attached to one genuine
third-field element `X`. -/
structure CommonErrorData
    (D : AlignmentData pi e a b u0 w0 s R0)
    (g1 : Gal(K/D.firstField)) (g2 : Gal(K/D.secondField))
    (q3 : Gal(D.thirdField/F)) (X : D.thirdField) (h : Int) : Prop where
  first_norm :
    norm D.firstField K (D.adjustedOrigin X) =
      D.a1 + algebraMap F D.firstField (D.adjustmentNorm X) -
        D.firstCrossedTrace g1 X
  second_norm :
    norm D.secondField K (D.adjustedOrigin X) =
      D.a2 + algebraMap F D.secondField (D.adjustmentNorm X) -
        D.secondCrossedTrace g2 X
  first_trace :
    trace D.firstField K (D.adjustedOrigin X) =
      D.h1 - algebraMap F D.firstField (D.adjustmentTrace X)
  second_trace :
    trace D.secondField K (D.adjustedOrigin X) =
      D.h2 - algebraMap F D.secondField (D.adjustmentTrace X)
  first_weighted_norm :
    norm F D.firstField (D.firstCrossedTrace g1 X) =
      D.beta1 * D.adjustmentNorm X + D.commonErrorTerm g1 X
  second_weighted_norm :
    norm F D.secondField (D.secondCrossedTrace g2 X) =
      D.beta2 * D.adjustmentNorm X + D.commonErrorTerm g1 X
  error_product :
    algebraMap F D.thirdField (D.commonErrorTerm g1 X) =
      (q3 X - X) * (D.a3 * q3 X - q3 D.a3 * X)
  first_trace_norm :
    norm F D.firstField (trace D.firstField K (D.adjustedOrigin X)) =
      D.beta1 + D.traceNormIncrement X
  second_trace_norm :
    norm F D.secondField (trace D.secondField K (D.adjustedOrigin X)) =
      D.beta2 + D.traceNormIncrement X
  trace_bound :
    ((((e : Int) - h / 2 : Int)) : WithTop Int) <=
      ord F (D.adjustmentTrace X)
  error_bound :
    (((((2 * e + 1 : Nat) : Int) - (a : Int) - h : Int)) : WithTop Int) <=
      ord F (D.commonErrorTerm g1 X)
  first_crossed_bound :
    ((((b : Int) - h : Int)) : WithTop Int) <=
      intermediateOrder D.firstField (D.firstCrossedTrace g1 X)
  second_crossed_bound :
    (((-h : Int)) : WithTop Int) <=
      intermediateOrder D.secondField (D.secondCrossedTrace g2 X)

section CommonErrorProof

-- Keep all intermediate-field instances canonical and local to this proof development.
attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

private theorem quadratic_ramificationIndex
    {E M : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M] [Algebra E M] [ValuativeExtension E M]
    [Module.Finite E M] (hdegree : Module.finrank E M = 2)
    (hres : residueDegree E M = 1) : ramificationIndex E M = 2 := by
  have hd := finrank_eq_ramificationIndex_mul_residueDegree E M
  rw [hdegree, hres, mul_one] at hd
  exact hd.symm

/-- The two ramified quadratic edges through one actual intermediate field. -/
private structure QuadraticTower (L : IntermediateField F K) : Prop where
  lower_cyclic : PrimeCyclicExtension F L
  upper_cyclic : PrimeCyclicExtension L K
  upper_degree : Module.finrank L K = 2
  lower_residue : residueDegree F L = 1
  upper_residue : residueDegree L K = 1
  lower_ramification : ramificationIndex F L = 2
  upper_ramification : ramificationIndex L K = 2

omit [Module.Free F K] in
private theorem quadraticTower
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (hres : residueDegree F K = 1) (L : IntermediateField F K)
    (hdegree : Module.finrank F L = 2) : QuadraticTower L := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hupper, hlowerCyclic, hupperCyclic⟩ :=
    Basic.intermediateField_tower_compatible Nat.prime_two hG L hdegree
  have hresMul := intermediate_residueDegree_mul L
  rw [hres] at hresMul
  obtain ⟨hlowerRes, hupperRes⟩ := mul_eq_one.mp hresMul
  exact ⟨PrimeCyclicExtension.ofCyclicPrimeExtension F L hlowerCyclic,
    PrimeCyclicExtension.ofCyclicPrimeExtension L K hupperCyclic,
    hupper, hlowerRes, hupperRes,
    quadratic_ramificationIndex hdegree hlowerRes,
    quadratic_ramificationIndex hupper hupperRes⟩

/-- Coordinates in the basis `1, SR` of the third quadratic field. -/
private theorem thirdField_coordinates
    (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)
    (X : D.thirdField) :
    ∃ P Q : F, X = algebraMap F D.thirdField P +
      algebraMap F D.thirdField Q * D.thirdGenerator := by
  let pb : PowerBasis F D.thirdField := by
    set_option backward.isDefEq.respectTransparency false in
      exact IntermediateField.adjoin.powerBasis
        (Algebra.IsIntegral.isIntegral (D.S * D.R))
  have hpbgen : pb.gen = D.thirdGenerator := by
    apply Subtype.ext
    simp [pb, AlignmentData.thirdGenerator]
  have hpbdim : pb.dim = 2 := by
    rw [← PowerBasis.finrank pb, O.third_degree]
  let B : Module.Basis (Fin 2) F D.thirdField :=
    pb.basis.reindex (finCongr hpbdim)
  have hB0 : B 0 = 1 := by
    simp [B]
  have hB1 : B 1 = D.thirdGenerator := by
    simp [B, hpbgen]
  let P : F := B.repr X 0
  let Q : F := B.repr X 1
  refine ⟨P, Q, ?_⟩
  have hs := B.sum_repr X
  rw [Fin.sum_univ_two, hB0, hB1] at hs
  simpa only [Algebra.smul_def, mul_one] using hs.symm

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K] [IsGalois F K] in
/-- The square of the third generator, expressed in the base field. -/
private theorem thirdGenerator_sq (D : AlignmentData pi e a b u0 w0 s R0) :
    D.thirdGenerator ^ 2 =
      algebraMap F D.thirdField ((1 + D.epsilon) * D.rSquare) := by
  apply (algebraMap D.thirdField K).injective
  change (D.S * D.R) ^ 2 = algebraMap D.thirdField K
    (algebraMap F D.thirdField ((1 + D.epsilon) * D.rSquare))
  rw [← IsScalarTower.algebraMap_apply F D.thirdField K, mul_pow,
    D.S_sq, D.R_sq, map_mul]

omit [IsGalois F K] in
/-- Conjugation, norm, and trace in the coordinates `X = P + Q SR`. -/
private theorem thirdField_coordinate_formulas
    (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)
    [IsGalois F D.thirdField]
    (q3 : Gal(D.thirdField/F)) (hq3 : q3 ≠ 1)
    (hq3SR : q3 D.thirdGenerator = -D.thirdGenerator)
    (X : D.thirdField) (P Q : F)
    (hcoord : X = algebraMap F D.thirdField P +
      algebraMap F D.thirdField Q * D.thirdGenerator) :
    q3 X = algebraMap F D.thirdField P -
        algebraMap F D.thirdField Q * D.thirdGenerator ∧
      D.adjustmentNorm X = P ^ 2 - Q ^ 2 * ((1 + D.epsilon) * D.rSquare) ∧
      D.adjustmentTrace X = 2 * P := by
  have hthirdSquare := thirdGenerator_sq D
  have hq3X : q3 X = algebraMap F D.thirdField P -
      algebraMap F D.thirdField Q * D.thirdGenerator := by
    rw [hcoord]
    simp only [map_add, map_mul, q3.commutes, hq3SR]
    ring
  have hAcoord : D.adjustmentNorm X =
      P ^ 2 - Q ^ 2 * ((1 + D.epsilon) * D.rSquare) := by
    apply (algebraMap F D.thirdField).injective
    rw [AlignmentData.adjustmentNorm,
      quadratic_norm_eq q3 hq3 O.third_degree, hq3X, hcoord]
    simp only [map_sub, map_mul, map_pow]
    rw [← map_mul, ← hthirdSquare]
    ring
  have hpcoord : D.adjustmentTrace X = 2 * P := by
    apply (algebraMap F D.thirdField).injective
    rw [AlignmentData.adjustmentTrace,
      quadratic_trace_eq q3 hq3 O.third_degree, hq3X, hcoord]
    simp only [map_mul, map_ofNat]
    ring

  exact ⟨hq3X, hAcoord, hpcoord⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K] [IsGalois F K] in
/-- An upper involution negating `SR` exchanges the two third-field conjugates. -/
private theorem upper_conjugate_coordinates
    (D : AlignmentData pi e a b u0 w0 s R0) (L : IntermediateField F K)
    (g : Gal(K/L)) (hg : g (D.S * D.R) = -(D.S * D.R))
    (q3 : Gal(D.thirdField/F)) (X : D.thirdField) (P Q : F)
    (hcoord : X = algebraMap F D.thirdField P +
      algebraMap F D.thirdField Q * D.thirdGenerator)
    (hq3X : q3 X = algebraMap F D.thirdField P -
      algebraMap F D.thirdField Q * D.thirdGenerator) :
    g (algebraMap D.thirdField K X) = algebraMap D.thirdField K (q3 X) ∧
      g (algebraMap D.thirdField K (q3 X)) = algebraMap D.thirdField K X := by
  have hgF (x : F) :
      g (algebraMap D.thirdField K (algebraMap F D.thirdField x)) =
        algebraMap D.thirdField K (algebraMap F D.thirdField x) := by
    rw [← IsScalarTower.algebraMap_apply F D.thirdField K]
    exact (g.restrictScalars F).commutes x
  change g (algebraMap D.thirdField K D.thirdGenerator) =
    -(algebraMap D.thirdField K D.thirdGenerator) at hg
  constructor <;> rw [hq3X, hcoord] <;>
    simp only [map_add, map_sub, map_mul] <;> rw [hgF, hgF, hg] <;> ring

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeExtension F K] [Module.Free F K] in
/-- Coordinates of the two crossed traces. -/
private theorem crossedTrace_coordinates
    (D : AlignmentData pi e a b u0 w0 s R0)
    (htwoK : (2 : K) ≠ 0)
    (g1 : Gal(K/D.firstField)) (hg1 : g1 ≠ 1) (hg1R : g1 D.R = -D.R)
    (g2 : Gal(K/D.secondField)) (hg2 : g2 ≠ 1) (hg2S : g2 D.S = -D.S)
    (hdegree1K : Module.finrank D.firstField K = 2)
    (hdegree2K : Module.finrank D.secondField K = 2)
    (q3 : Gal(D.thirdField/F)) (X : D.thirdField) (P Q : F)
    (hcoord : X = algebraMap F D.thirdField P +
      algebraMap F D.thirdField Q * D.thirdGenerator)
    (hq3X : q3 X = algebraMap F D.thirdField P -
      algebraMap F D.thirdField Q * D.thirdGenerator)
    (hg1X : g1 (algebraMap D.thirdField K X) = algebraMap D.thirdField K (q3 X))
    (hg1X' : g1 (algebraMap D.thirdField K (q3 X)) = algebraMap D.thirdField K X)
    (hg2X : g2 (algebraMap D.thirdField K X) = algebraMap D.thirdField K (q3 X))
    (hg2X' : g2 (algebraMap D.thirdField K (q3 X)) = algebraMap D.thirdField K X) :
    D.firstCrossedTrace g1 X = -algebraMap F D.firstField P +
        algebraMap F D.firstField (P - Q * D.rSquare) * D.firstGenerator ∧
      D.secondCrossedTrace g2 X = -algebraMap F D.secondField P +
        algebraMap F D.secondField (P - Q * (1 + D.epsilon)) * D.secondGenerator := by
  have hg1S : g1 D.S = D.S := by
    change g1 (algebraMap D.firstField K D.firstGenerator) =
      algebraMap D.firstField K D.firstGenerator
    exact g1.commutes D.firstGenerator
  have hg2R : g2 D.R = D.R := by
    change g2 (algebraMap D.secondField K D.secondGenerator) =
      algebraMap D.secondField K D.secondGenerator
    exact g2.commutes D.secondGenerator
  have hg1Y : g1 D.origin = (D.S - D.R - 1) / 2 := by
    simp only [AlignmentData.origin, map_div₀, map_sub, map_add, map_one,
      map_ofNat, hg1S, hg1R]
    ring
  have hg2Y : g2 D.origin = (-D.S + D.R - 1) / 2 := by
    simp only [AlignmentData.origin, map_div₀, map_sub, map_add, map_one,
      map_ofNat, hg2S, hg2R]
  have hQ1mapK := quadratic_crossed_trace D.firstField D.thirdField
    g1 hg1 hdegree1K q3 X D.origin hg1X hg1X'
  have hQ2mapK := quadratic_crossed_trace D.secondField D.thirdField
    g2 hg2 hdegree2K q3 X D.origin hg2X hg2X'
  have hQ1coord : D.firstCrossedTrace g1 X =
      -algebraMap F D.firstField P +
        algebraMap F D.firstField (P - Q * D.rSquare) * D.firstGenerator := by
    apply (algebraMap D.firstField K).injective
    rw [AlignmentData.firstCrossedTrace, hQ1mapK, hq3X, hcoord]
    simp only [map_add, map_sub, map_mul,
      ← IsScalarTower.algebraMap_apply F D.thirdField K,
      ← IsScalarTower.algebraMap_apply F D.firstField K,
      map_neg]
    rw [show algebraMap D.thirdField K D.thirdGenerator = D.S * D.R by rfl,
      show algebraMap D.firstField K D.firstGenerator = D.S by rfl, hg1Y]
    change D.origin * (algebraMap F K P - algebraMap F K Q * (D.S * D.R)) +
      (D.S - D.R - 1) / 2 *
        (algebraMap F K P + algebraMap F K Q * (D.S * D.R)) =
      -algebraMap F K P +
        (algebraMap F K P - algebraMap F K Q * algebraMap F K D.rSquare) * D.S
    rw [AlignmentData.origin]
    field_simp [htwoK]
    ring_nf
    rw [D.R_sq]
    ring
  have hQ2coord : D.secondCrossedTrace g2 X =
      -algebraMap F D.secondField P +
        algebraMap F D.secondField (P - Q * (1 + D.epsilon)) *
          D.secondGenerator := by
    apply (algebraMap D.secondField K).injective
    rw [AlignmentData.secondCrossedTrace, hQ2mapK, hq3X, hcoord]
    simp only [map_add, map_sub, map_mul,
      ← IsScalarTower.algebraMap_apply F D.thirdField K,
      ← IsScalarTower.algebraMap_apply F D.secondField K,
      map_neg]
    rw [show algebraMap D.thirdField K D.thirdGenerator = D.S * D.R by rfl,
      show algebraMap D.secondField K D.secondGenerator = D.R by rfl, hg2Y]
    rw [← map_add]
    change D.origin * (algebraMap F K P - algebraMap F K Q * (D.S * D.R)) +
      (-D.S + D.R - 1) / 2 *
        (algebraMap F K P + algebraMap F K Q * (D.S * D.R)) =
      -algebraMap F K P +
        (algebraMap F K P - algebraMap F K Q *
          algebraMap F K (1 + D.epsilon)) * D.R
    rw [AlignmentData.origin]
    field_simp [htwoK]
    ring_nf
    rw [D.S_sq]
    ring

  exact ⟨hQ1coord, hQ2coord⟩

/-- The coordinate polynomial for the intrinsic common error. -/
private def commonErrorPolynomial (D : AlignmentData pi e a b u0 w0 s R0)
    (P Q : F) : F :=
  2 * P * Q * ((1 + D.epsilon) * D.rSquare) -
    Q ^ 2 * (D.epsilon + D.rSquare) * ((1 + D.epsilon) * D.rSquare)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K] [IsGalois F K] in
private theorem epsilon_add_rSquare (D : AlignmentData pi e a b u0 w0 s R0)
    (htwo0 : (2 : F) ≠ 0) : D.epsilon + D.rSquare = 4 * D.C0 := by
  have hfour0 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero htwo0 htwo0
  exact (mul_div_cancel₀ _ hfour0).symm

omit [IsGalois F K] in
/-- The first weighted lower norm determines the common error polynomial. -/
private theorem commonError_coordinates
    (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)
    [IsGalois F D.firstField]
    (q1 : Gal(D.firstField/F)) (hq1 : q1 ≠ 1)
    (hq1S : q1 D.firstGenerator = -D.firstGenerator)
    (g1 : Gal(K/D.firstField)) (X : D.thirdField) (P Q : F)
    (hAcoord : D.adjustmentNorm X =
      P ^ 2 - Q ^ 2 * ((1 + D.epsilon) * D.rSquare))
    (hQ1coord : D.firstCrossedTrace g1 X = -algebraMap F D.firstField P +
      algebraMap F D.firstField (P - Q * D.rSquare) * D.firstGenerator) :
    D.commonErrorTerm g1 X = commonErrorPolynomial D P Q := by
  apply (algebraMap F D.firstField).injective
  rw [AlignmentData.commonErrorTerm, map_sub, map_mul,
    quadratic_norm_eq q1 hq1 O.first_degree, hQ1coord,
    O.beta1_table, hAcoord]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
    q1.commutes, hq1S, commonErrorPolynomial]
  have hSsq : D.firstGenerator ^ 2 =
      algebraMap F D.firstField (1 + D.epsilon) := by
    apply (algebraMap D.firstField K).injective
    change D.S ^ 2 = algebraMap D.firstField K
      (algebraMap F D.firstField (1 + D.epsilon))
    rw [D.S_sq, ← IsScalarTower.algebraMap_apply F D.firstField K]
  ring_nf
  rw [hSsq]
  simp only [map_one, map_add]
  ring

omit [IsGalois F K] in
/-- The second weighted lower norm has the same coordinate error. -/
private theorem second_weighted_norm
    (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)
    [IsGalois F D.secondField]
    (q2 : Gal(D.secondField/F)) (hq2 : q2 ≠ 1)
    (hq2R : q2 D.secondGenerator = -D.secondGenerator)
    (g1 : Gal(K/D.firstField)) (g2 : Gal(K/D.secondField))
    (X : D.thirdField) (P Q : F)
    (hAcoord : D.adjustmentNorm X =
      P ^ 2 - Q ^ 2 * ((1 + D.epsilon) * D.rSquare))
    (hQ2coord : D.secondCrossedTrace g2 X = -algebraMap F D.secondField P +
      algebraMap F D.secondField (P - Q * (1 + D.epsilon)) * D.secondGenerator)
    (herrorCoord : D.commonErrorTerm g1 X = commonErrorPolynomial D P Q) :
    norm F D.secondField (D.secondCrossedTrace g2 X) =
      D.beta2 * D.adjustmentNorm X + D.commonErrorTerm g1 X := by
  apply (algebraMap F D.secondField).injective
  rw [quadratic_norm_eq q2 hq2 O.second_degree, hQ2coord,
    O.beta2_table, hAcoord, herrorCoord]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_one,
    map_ofNat, q2.commutes, hq2R, commonErrorPolynomial]
  have hRsq : D.secondGenerator ^ 2 =
      algebraMap F D.secondField D.rSquare := by
    apply (algebraMap D.secondField K).injective
    change D.R ^ 2 = algebraMap D.secondField K
      (algebraMap F D.secondField D.rSquare)
    rw [D.R_sq, ← IsScalarTower.algebraMap_apply F D.secondField K]
  ring_nf
  rw [hRsq]

omit [IsGalois F K] in
/-- Identification of the intrinsic error with the paper's conjugate product. -/
private theorem commonError_product
    (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)
    (htwo0 : (2 : F) ≠ 0)
    (g1 : Gal(K/D.firstField)) (q3 : Gal(D.thirdField/F))
    (hq3SR : q3 D.thirdGenerator = -D.thirdGenerator)
    (X : D.thirdField) (P Q : F)
    (hcoord : X = algebraMap F D.thirdField P +
      algebraMap F D.thirdField Q * D.thirdGenerator)
    (hq3X : q3 X = algebraMap F D.thirdField P -
      algebraMap F D.thirdField Q * D.thirdGenerator)
    (herrorCoord : D.commonErrorTerm g1 X = commonErrorPolynomial D P Q) :
    algebraMap F D.thirdField (D.commonErrorTerm g1 X) =
      (q3 X - X) * (D.a3 * q3 X - q3 D.a3 * X) := by
  have htwo3 : (2 : D.thirdField) ≠ 0 := by
    simpa only [map_ofNat, map_zero] using
      (algebraMap F D.thirdField).injective.ne htwo0
  have hthirdSquare := thirdGenerator_sq D
  have hfourC := epsilon_add_rSquare D htwo0
  have ha3coord : D.a3 = -D.thirdGenerator / 2 -
      algebraMap F D.thirdField D.C0 := by
    apply (algebraMap D.thirdField K).injective
    simp only [map_sub, map_div₀, map_neg, map_ofNat]
    rw [← IsScalarTower.algebraMap_apply F D.thirdField K]
    exact O.a3_table
  rw [herrorCoord, commonErrorPolynomial, hfourC, hq3X, hcoord, ha3coord]
  simp only [map_sub, map_mul, map_pow, map_add, map_ofNat, q3.commutes,
    hq3SR, map_neg, map_div₀]
  rw [← map_add, ← map_mul, ← hthirdSquare]
  field_simp [htwo3]
  ring

/-- Trace-ideal containment for a totally ramified quadratic edge of lower break `t`. -/
private theorem quadratic_trace_mem_lattice
    {E M : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M] [Algebra E M] [ValuativeExtension E M]
    [Module.Free E M] [Module.Finite E M] [PrimeCyclicExtension E M]
    (hdegree : Module.finrank E M = 2) (hres : residueDegree E M = 1)
    {t : Nat} (hbreak : PrimeCyclicExtension.IsLowerBreak E M t)
    {n : Int} {x : M} (hx : x ∈ lattice M n) :
    trace E M x ∈ lattice E ((n + ((t + 1 : Nat) : Int)) / 2) := by
  obtain ⟨piM, hpiM, hgenM⟩ := monogenicUniformizer E M hres
  have htrace := trace_mem_lattice_floor E M piM hpiM hgenM n hx
  simpa only [differentExponent_eq E M hbreak piM hpiM hgenM, hdegree,
    quadratic_ramificationIndex hdegree hres, Nat.reduceSub, one_mul,
    Nat.cast_ofNat] using htrace

private theorem adjustmentTrace_mem_lattice
    (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)
    [PrimeCyclicExtension F D.thirdField]
    (hres : residueDegree F D.thirdField = 1)
    (hbreak : PrimeCyclicExtension.IsLowerBreak F D.thirdField (2 * e))
    (X : D.thirdField) (h : Int)
    (hX : intermediateOrder D.thirdField X = ((-h : Int) : WithTop Int)) :
    D.adjustmentTrace X ∈ lattice F ((e : Int) - h / 2) := by
  have hx : X ∈ lattice D.thirdField (-h) := (mem_lattice D.thirdField).2 hX.ge
  have htrace := quadratic_trace_mem_lattice O.third_degree hres hbreak hx
  have hexponent : (-h + ((2 * e + 1 : Nat) : Int)) / 2 = (e : Int) - h / 2 := by
    omega
  simpa only [AlignmentData.adjustmentTrace, hexponent] using htrace

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K] [IsGalois F K] in
/-- The square of `SR` has base-field order `b`. -/
private theorem thirdBase_order
    (D : AlignmentData pi e a b u0 w0 s R0)
    (hb : b = 2 * e - 2 * a + 1) :
    ord F ((1 + D.epsilon) * D.rSquare) = (b : WithTop Int) := by
  have honeEpsOrder : ord F (1 + D.epsilon) = 0 := by
    have hbpos : 0 < b := by omega
    rw [ord_add_eq_min F (by
      rw [ord_one, D.epsilon_order]
      exact ne_of_lt (WithTop.coe_pos.mpr (by exact_mod_cast hbpos))),
      ord_one, D.epsilon_order, min_eq_left]
    exact WithTop.coe_nonneg.mpr (by exact_mod_cast Nat.zero_le b)
  rw [ord_mul, honeEpsOrder, D.rSquare_order, zero_add]

omit [Module.Free F K] [IsGalois F K] in
private theorem thirdGenerator_order
    (D : AlignmentData pi e a b u0 w0 s R0)
    (hramF3 : ramificationIndex F D.thirdField = 2)
    (hthirdBaseOrder : ord F ((1 + D.epsilon) * D.rSquare) = (b : WithTop Int)) :
    ord D.thirdField D.thirdGenerator = (b : WithTop Int) := by
  let thirdBase : F := (1 + D.epsilon) * D.rSquare
  have hthirdSquare := thirdGenerator_sq D
  have hs := congrArg (ord D.thirdField) hthirdSquare
  rw [ord_pow, ord_algebraMap, hramF3, hthirdBaseOrder] at hs
  have hthirdBase0 : thirdBase ≠ 0 :=
    (ord_ne_top_iff F).1 (by
      rw [hthirdBaseOrder]
      exact WithTop.coe_ne_top)
  have hthirdBaseMap0 : algebraMap F D.thirdField thirdBase ≠ 0 :=
    by simpa only [map_zero] using
      (algebraMap F D.thirdField).injective.ne hthirdBase0
  have hthirdGenerator0 : D.thirdGenerator ≠ 0 := by
    intro hz0
    apply hthirdBaseMap0
    rw [← hthirdSquare, hz0]
    norm_num
  obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp
    ((ord_ne_top_iff D.thirdField).2 hthirdGenerator0)
  rw [← hz] at hs
  change ((2 • z : Int) : WithTop Int) =
    2 • (((b : Int) : WithTop Int)) at hs
  rw [← WithTop.coe_nsmul] at hs
  have hsInt := WithTop.coe_eq_coe.mp hs
  norm_num [nsmul_eq_mul] at hsInt
  have hzb : z = (b : Int) := by omega
  rw [← hz]
  exact congrArg ((↑) : Int → WithTop Int) hzb

omit [Module.Free F K] [IsGalois F K] in
/-- Bounds on both coefficients in `X = P + Q SR`, for every integer depth. -/
private theorem thirdField_coefficient_bounds
    (D : AlignmentData pi e a b u0 w0 s R0)
    (htwo : ord F (2 : F) = (e : WithTop Int))
    (hae : a <= e) (hb : b = 2 * e - 2 * a + 1)
    (hramF3 : ramificationIndex F D.thirdField = 2)
    (X : D.thirdField) (h : Int)
    (hX : intermediateOrder D.thirdField X = ((-h : Int) : WithTop Int))
    (P Q : F)
    (hcoord : X = algebraMap F D.thirdField P +
      algebraMap F D.thirdField Q * D.thirdGenerator)
    (hpcoord : D.adjustmentTrace X = 2 * P)
    (hpLat : D.adjustmentTrace X ∈ lattice F ((e : Int) - h / 2)) :
    P ∈ lattice F (-(h / 2)) ∧
      Q ∈ lattice F ((a : Int) - (e : Int) + (-h) / 2) := by
  have htwo0 : (2 : F) ≠ 0 :=
    (ord_ne_top_iff F).1 (by rw [htwo]; exact WithTop.coe_ne_top)
  have hxLat : X ∈ lattice D.thirdField (-h) := (mem_lattice D.thirdField).2 hX.ge
  have hthirdGeneratorOrder := thirdGenerator_order D hramF3 (thirdBase_order D hb)
  have hPLat : P ∈ lattice F (- (h / 2)) := by
    have hpDiv : D.adjustmentTrace X / 2 ∈ lattice F (- (h / 2)) := by
      apply (div_mem_lattice_iff F (2 : F) (D.adjustmentTrace X)
        (e : Int) (- (h / 2)) htwo).2
      simpa only [sub_eq_add_neg] using hpLat
    rw [hpcoord] at hpDiv
    simpa [htwo0] using hpDiv
  have hPmapLat : algebraMap F D.thirdField P ∈ lattice D.thirdField (-h) := by
    rw [mem_lattice, ord_algebraMap, hramF3]
    have hPord := (mem_lattice F).1 hPLat
    calc
      ((-h : Int) : WithTop Int) <=
          2 • ((-(h / 2) : Int) : WithTop Int) := by
            rw [← WithTop.coe_nsmul]
            simp only [nsmul_eq_mul]
            exact WithTop.coe_le_coe.mpr (by omega)
      _ <= 2 • ord F P := nsmul_le_nsmul_right hPord 2
  have hQtLat : algebraMap F D.thirdField Q * D.thirdGenerator ∈
      lattice D.thirdField (-h) := by
    have hs := sub_mem_lattice D.thirdField hxLat hPmapLat
    convert hs using 1
    rw [hcoord]
    ring

  let qExp : Int := (a : Int) - (e : Int) + (-h) / 2
  have hQLat : Q ∈ lattice F qExp := by
    by_cases hQ0 : Q = 0
    · rw [hQ0]
      exact zero_mem _
    have hQordFinite := (ord_ne_top_iff F).2 hQ0
    obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp hQordFinite
    have hQtOrd := (mem_lattice D.thirdField).1 hQtLat
    rw [ord_mul, ord_algebraMap, hramF3, hthirdGeneratorOrder, ← hz] at hQtOrd
    have hQtInt : -h ≤ 2 * z + (b : Int) := by
      exact_mod_cast hQtOrd
    rw [mem_lattice, ← hz]
    apply WithTop.coe_le_coe.mpr
    simp only [qExp]
    push_cast [hb, Nat.cast_sub hae] at hQtInt
    omega

  exact ⟨hPLat, hQLat⟩

omit [IsGalois F K] in
/-- The aligned sum error supplies the extra depth in the quadratic term. -/
private theorem epsilon_add_rSquare_bound
    (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)
    (htwo : ord F (2 : F) = (e : WithTop Int))
    (hae : a <= e) (hb : b = 2 * e - 2 * a + 1) :
    (((b + a : Nat) : Int) : WithTop Int) <= ord F (D.epsilon + D.rSquare) := by
  have htwo0 : (2 : F) ≠ 0 :=
    (ord_ne_top_iff F).1 (by rw [htwo]; exact WithTop.coe_ne_top)
  have hfourC := epsilon_add_rSquare D htwo0
  have hfourOrder : ord F (4 : F) = ((2 * (e : Int) : Int) : WithTop Int) := by
    rw [show (4 : F) = 2 * 2 by norm_num, ord_mul, htwo]
    rw [show (2 * (e : Int) : Int) = e + e by omega, WithTop.coe_add]
    norm_cast

  rw [hfourC, ord_mul, hfourOrder]
  have hC := O.C0_order
  calc
    (((b + a : Nat) : Int) : WithTop Int) =
        ((2 * (e : Int) : Int) : WithTop Int) +
          (((1 : Int) - a : Int) : WithTop Int) := by
            rw [← WithTop.coe_add]
            congr 1
            push_cast [hb, Nat.cast_sub hae]
            omega
    _ <= ((2 * (e : Int) : Int) : WithTop Int) + ord F D.C0 :=
      add_le_add_right hC _

omit [IsGalois F K] in
/-- The two monomials in the common error meet the required weighted depth. -/
private theorem commonErrorPolynomial_mem_lattice
    (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)
    (htwo : ord F (2 : F) = (e : WithTop Int))
    (_ha : 1 <= a) (hae : a <= e) (hb : b = 2 * e - 2 * a + 1)
    (h : Int) (P Q : F)
    (hPLat : P ∈ lattice F (-(h / 2)))
    (hQLat : Q ∈ lattice F ((a : Int) - (e : Int) + (-h) / 2)) :
    commonErrorPolynomial D P Q ∈ lattice F
      (((2 * e + 1 : Nat) : Int) - (a : Int) - h) := by
  let thirdBase : F := (1 + D.epsilon) * D.rSquare
  let qExp : Int := (a : Int) - (e : Int) + (-h) / 2
  have hthirdBaseOrder := thirdBase_order D hb
  have hepsPlusOrder := epsilon_add_rSquare_bound D O htwo hae hb
  let target : Int := ((2 * e + 1 : Nat) : Int) - (a : Int) - h
  have hterm1 : 2 * P * Q * thirdBase ∈ lattice F target := by
    have h2 : (2 : F) ∈ lattice F (e : Int) := by
      rw [mem_lattice, htwo]
      norm_num
    have hm := mul_mem_lattice F (mul_mem_lattice F
      (mul_mem_lattice F h2 hPLat) hQLat)
      (by
        rw [mem_lattice, hthirdBaseOrder]
        norm_num : thirdBase ∈ lattice F (b : Int))
    have hdepth1 : target =
        (e : Int) + -(h / 2) + qExp + (b : Int) := by
      simp only [target, qExp]
      push_cast [hb, Nat.cast_sub hae]
      omega
    rw [hdepth1]
    exact hm
  have hterm2 : Q ^ 2 * (D.epsilon + D.rSquare) * thirdBase ∈
      lattice F target := by
    have hQ2 : Q ^ 2 ∈ lattice F (2 * qExp) := by
      rw [show (2 * qExp : Int) = qExp + qExp by ring]
      simpa only [pow_two] using mul_mem_lattice F hQLat hQLat
    have hepsPlus : D.epsilon + D.rSquare ∈ lattice F ((b + a : Nat) : Int) :=
      (mem_lattice F).2 hepsPlusOrder
    have hm := mul_mem_lattice F (mul_mem_lattice F hQ2 hepsPlus)
      (by
        rw [mem_lattice, hthirdBaseOrder]
        norm_num : thirdBase ∈ lattice F (b : Int))
    apply (mem_lattice F).2
    have hmord := (mem_lattice F).1 hm
    calc
      ((target : Int) : WithTop Int) <=
          (((2 * qExp + (b + a : Nat) + b : Int)) : WithTop Int) := by
            apply WithTop.coe_le_coe.mpr
            simp only [target, qExp]
            push_cast [hb, Nat.cast_sub hae]
            omega
      _ <= ord F (Q ^ 2 * (D.epsilon + D.rSquare) * thirdBase) := hmord
  exact sub_mem_lattice F hterm1 hterm2

/-- The shared upper-trace estimate for either crossed trace. -/
private theorem crossedTrace_bound
    (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)
    (L : IntermediateField F K) [PrimeCyclicExtension L K]
    (hdegree : Module.finrank L K = 2) (hres : residueDegree L K = 1)
    (hram3K : ramificationIndex D.thirdField K = 2)
    {t : Nat} (hbreak : PrimeCyclicExtension.IsLowerBreak L K t)
    (g : Gal(K/L)) (X : D.thirdField) (h j : Int)
    (hX : intermediateOrder D.thirdField X = ((-h : Int) : WithTop Int))
    (hj : (-(2 * (a : Int) - 1) - 2 * h + ((t + 1 : Nat) : Int)) / 2 = j) :
    (j : WithTop Int) <=
      intermediateOrder L (trace L K (D.origin * g (algebraMap D.thirdField K X))) := by
  change ord D.thirdField X = ((-h : Int) : WithTop Int) at hX
  have hxKOrder : ord K (algebraMap D.thirdField K X) =
      ((-2 * h : Int) : WithTop Int) := by
    rw [ord_algebraMap, hram3K, hX, ← WithTop.coe_nsmul]
    congr 1
    simp
  let depth : Int := -(2 * (a : Int) - 1) - 2 * h
  have hprod : D.origin * g (algebraMap D.thirdField K X) ∈
      lattice K depth := by
    rw [mem_lattice, ord_mul, ord_galoisConjugate, hxKOrder, O.origin_order]
    apply le_of_eq
    rw [← WithTop.coe_add]
    congr 1
    simp only [depth]
    omega
  have htrace := quadratic_trace_mem_lattice hdegree hres hbreak hprod
  rw [show (depth + ((t + 1 : Nat) : Int)) / 2 = j from hj] at htrace
  exact (mem_lattice L).1 htrace

/-- **Weighted common error (`D:MX:adjust-identities`--`D:MX:errors`).**

The three break hypotheses refer to the genuine lower filtrations on
`L_3/F`, `K/L_1`, and `K/L_2`.  The theorem constructs the coordinate
calculation from the actual aligned generator and proves both the exact
identities and all four estimates for every integer `h`. -/
theorem commonError
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (hres : residueDegree F K = 1)
    (htwo : ord F (2 : F) = (e : WithTop Int))
    (ha : 1 <= a) (hae : a <= e) (hb : b = 2 * e - 2 * a + 1)
    (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)
    (g1 : Gal(K/D.firstField)) (hg1 : g1 ≠ 1)
    (hg1R : g1 D.R = -D.R)
    (g2 : Gal(K/D.secondField)) (hg2 : g2 ≠ 1)
    (hg2S : g2 D.S = -D.S)
    (q1 : Gal(D.firstField/F)) (hq1 : q1 ≠ 1)
    (hq1S : q1 D.firstGenerator = -D.firstGenerator)
    (q2 : Gal(D.secondField/F)) (hq2 : q2 ≠ 1)
    (hq2R : q2 D.secondGenerator = -D.secondGenerator)
    (q3 : Gal(D.thirdField/F)) (hq3 : q3 ≠ 1)
    (hq3SR : q3 D.thirdGenerator = -D.thirdGenerator)
    (hbreak3 : actualLowerBreak hG D.thirdField O.third_degree (2 * e))
    (hbreak1 : actualUpperBreak hG D.firstField O.first_degree
      (4 * e - 2 * a + 1))
    (hbreak2 : actualUpperBreak hG D.secondField O.second_degree
      (2 * a - 1))
    (X : D.thirdField) (h : Int)
    (hX : intermediateOrder D.thirdField X = ((-h : Int) : WithTop Int)) :
    CommonErrorData D g1 g2 q3 X h := by
  have T1 := quadraticTower hG hres D.firstField O.first_degree
  have T2 := quadraticTower hG hres D.secondField O.second_degree
  have T3 := quadraticTower hG hres D.thirdField O.third_degree
  letI := T1.lower_cyclic
  letI := T1.upper_cyclic
  letI := T2.lower_cyclic
  letI := T2.upper_cyclic
  letI := T3.lower_cyclic
  letI := T3.upper_cyclic
  have hbreak3' : PrimeCyclicExtension.IsLowerBreak F D.thirdField (2 * e) := by
    simpa [actualLowerBreak] using hbreak3
  have hbreak1' : PrimeCyclicExtension.IsLowerBreak D.firstField K
      (4 * e - 2 * a + 1) := by
    simpa [actualUpperBreak] using hbreak1
  have hbreak2' : PrimeCyclicExtension.IsLowerBreak D.secondField K (2 * a - 1) := by
    simpa [actualUpperBreak] using hbreak2
  have htwo0 : (2 : F) ≠ 0 :=
    (ord_ne_top_iff F).1 (by rw [htwo]; exact WithTop.coe_ne_top)
  have htwoK : (2 : K) ≠ 0 := by
    simpa only [map_ofNat, map_zero] using (algebraMap F K).injective.ne htwo0

  obtain ⟨P, Q, hcoord⟩ := thirdField_coordinates D O X
  obtain ⟨hq3X, hAcoord, hpcoord⟩ :=
    thirdField_coordinate_formulas D O q3 hq3 hq3SR X P Q hcoord
  have hg1third : g1 (D.S * D.R) = -(D.S * D.R) := by
    have hg1S : g1 D.S = D.S := g1.commutes D.firstGenerator
    rw [map_mul, hg1S, hg1R]
    ring
  have hg2third : g2 (D.S * D.R) = -(D.S * D.R) := by
    have hg2R : g2 D.R = D.R := g2.commutes D.secondGenerator
    rw [map_mul, hg2S, hg2R]
    ring
  obtain ⟨hg1X, hg1X'⟩ :=
    upper_conjugate_coordinates D D.firstField g1 hg1third q3 X P Q hcoord hq3X
  obtain ⟨hg2X, hg2X'⟩ :=
    upper_conjugate_coordinates D D.secondField g2 hg2third q3 X P Q hcoord hq3X
  obtain ⟨hfirstNorm, hfirstTrace⟩ := quadratic_adjustment_identities
    D.firstField D.thirdField g1 hg1 T1.upper_degree q3 hq3 O.third_degree
    X D.origin hg1X hg1X'
  obtain ⟨hsecondNorm, hsecondTrace⟩ := quadratic_adjustment_identities
    D.secondField D.thirdField g2 hg2 T2.upper_degree q3 hq3 O.third_degree
    X D.origin hg2X hg2X'
  obtain ⟨hQ1coord, hQ2coord⟩ := crossedTrace_coordinates D htwoK
    g1 hg1 hg1R g2 hg2 hg2S T1.upper_degree T2.upper_degree q3 X P Q hcoord hq3X
    hg1X hg1X' hg2X hg2X'

  have herrorCoord := commonError_coordinates D O q1 hq1 hq1S g1 X P Q hAcoord hQ1coord
  have hsecondWeighted :=
    second_weighted_norm D O q2 hq2 hq2R g1 g2 X P Q hAcoord hQ2coord herrorCoord
  have herrorProduct := commonError_product D O htwo0 g1 q3 hq3SR X P Q
    hcoord hq3X herrorCoord
  have hfirstTraceNorm :
      norm F D.firstField (trace D.firstField K (D.adjustedOrigin X)) =
        D.beta1 + D.traceNormIncrement X := by
    rw [AlignmentData.adjustedOrigin, hfirstTrace]
    exact quadratic_trace_norm_increment D.firstField q1 hq1 O.first_degree
      D.origin (D.adjustmentTrace X) O.total_trace
  have hsecondTraceNorm :
      norm F D.secondField (trace D.secondField K (D.adjustedOrigin X)) =
        D.beta2 + D.traceNormIncrement X := by
    rw [AlignmentData.adjustedOrigin, hsecondTrace]
    exact quadratic_trace_norm_increment D.secondField q2 hq2 O.second_degree
      D.origin (D.adjustmentTrace X) O.total_trace

  have hpLat := adjustmentTrace_mem_lattice D O T3.lower_residue hbreak3' X h hX
  obtain ⟨hPLat, hQLat⟩ :=
    thirdField_coefficient_bounds D htwo hae hb T3.lower_ramification X h hX
      P Q hcoord hpcoord hpLat
  have herrorLat := commonErrorPolynomial_mem_lattice D O htwo ha hae hb h P Q hPLat hQLat
  rw [← herrorCoord] at herrorLat
  have hQ1Bound := crossedTrace_bound D O D.firstField T1.upper_degree T1.upper_residue
    T3.upper_ramification hbreak1' g1 X h ((b : Int) - h) hX (by
      push_cast [hb, Nat.cast_sub hae]
      omega)
  have hQ2Bound := crossedTrace_bound D O D.secondField T2.upper_degree T2.upper_residue
    T3.upper_ramification hbreak2' g2 X h (-h) hX (by
      push_cast
      omega)

  exact {
    first_norm := hfirstNorm
    second_norm := hsecondNorm
    first_trace := hfirstTrace
    second_trace := hsecondTrace
    first_weighted_norm := by simp [AlignmentData.commonErrorTerm]
    second_weighted_norm := hsecondWeighted
    error_product := herrorProduct
    first_trace_norm := hfirstTraceNorm
    second_trace_norm := hsecondTraceNorm
    trace_bound := (mem_lattice F).1 hpLat
    error_bound := (mem_lattice F).1 herrorLat
    first_crossed_bound := hQ1Bound
    second_crossed_bound := hQ2Bound }

end CommonErrorProof

end

end LanglandsSecondMainLemma.Dyadic.Maximal
