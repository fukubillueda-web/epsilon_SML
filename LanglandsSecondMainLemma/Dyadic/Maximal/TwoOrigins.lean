import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Dyadic.Maximal.HigherCoefficients
import LanglandsSecondMainLemma.Stationary.CommonFunction

/-!
# Two stationary origins in the maximal dyadic case

The exact calculation at `D:MX:two-origins` (paper lines 7348–7358).
The upper functions use `C + V`, where `C = Y - X`, while the lower
functions use `Y + V`. The common correction `p_X * Tr_{K/F}(V)` is
retained as an equality in the base field, without a depth restriction.

The trace shifts are supplied by the constructed `CommonErrorData` for
an actual third-field element. In particular, no lower stationarity at
`C` is asserted. The pointwise functions below retain both affine terms
and the actual multiplicative character values.
-/

namespace LanglandsSecondMainLemma.Dyadic.Maximal

open LanglandsFirstMainLemma

noncomputable section

/-- Extend FML's exact quadratic norm expansion to an arbitrary base scalar,
including zero, and put it in the manuscript's `x - p` order. -/
private theorem twoOrigin_norm_sub_base
    (F E : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
    (hdeg : Module.finrank F E = 2) (x : E) (p : F) :
    norm F E (x - algebraMap F E p) =
      norm F E x + p ^ 2 - p * trace F E x := by
  by_cases hp : p = 0
  · simp [hp]
  have hneg (w : E) : norm F E (-w) = norm F E w := by
    rw [show -w = algebraMap F E (-1 : F) * w by simp, map_mul,
      LanglandsFirstMainLemma.norm_algebraMap, hdeg]
    norm_num
  have hn := wildQuadratic_norm_sub F E hdeg (Units.mk0 p hp) x
  simp only [Units.val_mk0] at hn
  rw [show x - algebraMap F E p = -(algebraMap F E p - x) by ring, hneg, hn]
  ring

section Edge

variable {F K : Type*} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [Module.Finite F K] [IsGalois F K]
  (L : IntermediateField F K)
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension F L]
  [Algebra.IsQuadraticExtension F L]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The difference of the lower trace-norm increments, before applying an
additive character. Its sign is the one immediately preceding
`D:MX:two-origins`. The trace-shift hypothesis is proved for both actual
flags by `commonError`. -/
theorem twoOrigin_traceNorm_increment
    (C Y V : K) (p : F)
    (hshift : trace L K C = trace L K Y - algebraMap F L p) :
    (norm F L (trace L K (C + V)) - norm F L (trace L K C)) -
      (norm F L (trace L K (Y + V)) - norm F L (trace L K Y)) =
        -p * trace F K V := by
  have hshift' : trace L K (C + V) =
      trace L K (Y + V) - algebraMap F L p := by
    rw [map_add, map_add, hshift]
    ring
  rw [hshift', hshift, twoOrigin_norm_sub_base F L
    (Algebra.IsQuadraticExtension.finrank_eq_two F L),
    twoOrigin_norm_sub_base F L (Algebra.IsQuadraticExtension.finrank_eq_two F L)]
  simp only [map_add, Basic.trace_tower (F := F) (L := L)]
  ring

variable [IsKleinFour Gal(K/F)] [Algebra.IsQuadraticExtension L K]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The exact two-origin elementary phase on one genuine quadratic flag.
This is stronger than a congruence at the additive conductor: the common
correction is retained in `F`, even when it is shallow. -/
theorem twoOrigin_phase_increment
    (C Y V : K) (p : F)
    (hshift : trace L K C = trace L K Y - algebraMap F L p) :
    trace F L (norm L K (C + V) - norm L K C) +
      (norm F L (trace L K (Y + V)) - norm F L (trace L K Y)) =
        elementarySymmetric F K 2 (C + V) - elementarySymmetric F K 2 C +
          p * trace F K V := by
  have hinc := twoOrigin_traceNorm_increment L C Y V p hshift
  rw [Algebra.biquadraticE2 F K L, Algebra.biquadraticE2 F K L, map_sub]
  linear_combination -hinc

end Edge

section Functions

variable {F K : Type*} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [Module.Finite F K] [IsGalois F K]
  (L : IntermediateField F K)
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension F L] [ValuativeExtension L K]

/-- The complete pointwise product with separate upper and lower origins.
The lower coefficient is the norm of `Tr(Y)`, while the upper coefficient
is the norm of `C`. All four character arguments and both affine terms
are literal. In particular, `Tr(C)` need not be nonzero. -/
def twoOriginFunctionProduct
    (theta : ContinuousQuasiChar L) (omega : ContinuousQuasiChar F)
    (Psi : ContinuousAddChar F) (C C' : Kˣ) (Y Y' : K)
    (hy : trace L K Y ≠ 0) (hy' : trace L K Y' ≠ 0) : ℂˣ :=
  let Z := normUnits L K C
  let W := normUnits F L (Units.mk0 (trace L K Y) hy)
  let r := normUnits L K C' / Z
  let s := normUnits F L (Units.mk0 (trace L K Y') hy') / W
  tracePullbackAddChar F L Psi (-(Z : L) * ((r : L) - 1)) * (theta r)⁻¹ *
    Psi (-(W : F) * ((s : F) - 1)) * (omega s)⁻¹

private theorem twoOrigin_neg_unit_increment {E : Type*} [Field E] (Z Z' : Eˣ) :
    -(Z : E) * (((Z' / Z : Eˣ) : E) - 1) = -(Z' : E) + (Z : E) := by
  rw [Units.val_div_eq_div_val]
  field_simp
  ring

variable [IsKleinFour Gal(K/F)]
  [Algebra.IsQuadraticExtension F L] [Algebra.IsQuadraticExtension L K]

/-- The full two-origin pointwise identity, before taking residual sums.
Compatibility evaluates the upper quotient by the actual common pullback.
The lower quotient is an exhibited norm, so its actual norm-character
value is one. The common correction remains inside the additive phase. -/
theorem twoOriginFunctionProduct_eq
    (theta : ContinuousQuasiChar L) (omega : NormCharacter F L)
    (Theta : ContinuousQuasiChar K) (hc : normQuasiChar L K theta = Theta)
    (Psi : ContinuousAddChar F) (C C' : Kˣ) (Y Y' V : K)
    (hy : trace L K Y ≠ 0) (hy' : trace L K Y' ≠ 0)
    (hC' : (C' : K) = (C : K) + V) (hY' : Y' = Y + V)
    (p : F) (hshift : trace L K (C : K) = trace L K Y - algebraMap F L p) :
    twoOriginFunctionProduct L theta omega.1 Psi C C' Y Y' hy hy' =
      (Theta (C' / C))⁻¹ * Psi
        (-elementarySymmetric F K 2 (C' : K) + elementarySymmetric F K 2 (C : K) -
          p * trace F K V) := by
  let Z := normUnits L K C
  let Z' := normUnits L K C'
  let W := normUnits F L (Units.mk0 (trace L K Y) hy)
  let W' := normUnits F L (Units.mk0 (trace L K Y') hy')
  have htheta : theta (Z' / Z) = Theta (C' / C) := by
    have hh := DFunLike.congr_fun hc (C' / C)
    change theta (normUnits L K (C' / C)) = _ at hh
    simpa only [map_div] using hh
  have homega : omega.1 (W' / W) = 1 := by
    apply omega.eq_one_on_normRange F L
    exact ⟨Units.mk0 (trace L K Y') hy' / Units.mk0 (trace L K Y) hy,
      map_div _ _ _⟩
  have hphase := twoOrigin_phase_increment L (C : K) Y V p hshift
  rw [← hC', ← hY', map_sub] at hphase
  have hadd : tracePullbackAddChar F L Psi (-(Z' : L) + (Z : L)) *
      Psi (-(W' : F) + (W : F)) =
      Psi (-elementarySymmetric F K 2 (C' : K) + elementarySymmetric F K 2 (C : K) -
        p * trace F K V) := by
    rw [tracePullbackAddChar_apply, ← ContinuousAddChar.map_add_eq_mul]
    congr 1
    change trace F L (-norm L K (C' : K) + norm L K (C : K)) +
      (-norm F L (trace L K Y') + norm F L (trace L K Y)) = _
    rw [map_add, map_neg]
    linear_combination -hphase
  change _ * (theta (Z' / Z))⁻¹ * _ * (omega.1 (W' / W))⁻¹ = _
  rw [htheta, homega, inv_one, mul_one,
    twoOrigin_neg_unit_increment, twoOrigin_neg_unit_increment]
  calc
    _ = (Theta (C' / C))⁻¹ *
        (tracePullbackAddChar F L Psi (-(Z' : L) + (Z : L)) *
          Psi (-(W' : F) + (W : F))) := by ac_rfl
    _ = _ := by rw [hadd]

/-- The modulus of the complete product for arbitrary continuous
quasi-characters. Only the common multiplicative value contributes:
the retained additive phase has modulus one by FML. -/
theorem twoOriginFunctionProduct_norm
    (theta : ContinuousQuasiChar L) (omega : NormCharacter F L)
    (Theta : ContinuousQuasiChar K) (hc : normQuasiChar L K theta = Theta)
    (Psi : LocalAddCharData F) (C C' : Kˣ) (Y Y' V : K)
    (hy : trace L K Y ≠ 0) (hy' : trace L K Y' ≠ 0)
    (hC' : (C' : K) = (C : K) + V) (hY' : Y' = Y + V)
    (p : F) (hshift : trace L K (C : K) = trace L K Y - algebraMap F L p) :
    ‖(twoOriginFunctionProduct L theta omega.1 Psi.character C C' Y Y' hy hy' : ℂ)‖ =
      ‖(Theta (C' / C) : ℂ)‖⁻¹ := by
  rw [twoOriginFunctionProduct_eq L theta omega Theta hc Psi.character C C' Y Y' V
    hy hy' hC' hY' p hshift, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv,
    localAddChar_norm_eq_one, mul_one]

/-- In particular, the product has modulus one on a top-field unit
quotient. The quasi-characters themselves need not be unitary. -/
theorem twoOriginFunctionProduct_norm_eq_one
    (theta : ContinuousQuasiChar L) (omega : NormCharacter F L)
    (Theta : ContinuousQuasiChar K) (hc : normQuasiChar L K theta = Theta)
    (Psi : LocalAddCharData F) (C C' : Kˣ) (Y Y' V : K)
    (hy : trace L K Y ≠ 0) (hy' : trace L K Y' ≠ 0)
    (hC' : (C' : K) = (C : K) + V) (hY' : Y' = Y + V)
    (p : F) (hshift : trace L K (C : K) = trace L K Y - algebraMap F L p)
    (hu : C' / C ∈ unitGroup K) :
    ‖(twoOriginFunctionProduct L theta omega.1 Psi.character C C' Y Y' hy hy' : ℂ)‖ = 1 := by
  rw [twoOriginFunctionProduct_norm L theta omega Theta hc Psi C C' Y Y' V
    hy hy' hC' hY' p hshift,
    continuousQuasiChar_norm_eq_one_of_mem_unitGroup K Theta _ hu, inv_one]

omit [IsGalois F K] [IsKleinFour Gal(K/F)]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension L K]
  [Algebra.IsQuadraticExtension F L] [Algebra.IsQuadraticExtension L K] in
/-- On the stated positive-depth lattices the two-origin product is the
product of the complete normalized critical functions. The equations
identify actual norm quotients, without assuming a norm map is onto. -/
theorem twoOriginFunctionProduct_eq_criticalValues
    (theta : LocalQuasiCharData L) (omega : LocalQuasiCharData F)
    (PsiF : LocalAddCharData F) (PsiL : LocalAddCharData L)
    (hPsi : PsiL.character = tracePullbackAddChar F L PsiF.character)
    (C C' : Kˣ) (Y Y' : K) (hy : trace L K Y ≠ 0) (hy' : trace L K Y' ≠ 0)
    (dL dF : ℕ) (hdL : 0 < dL) (hdF : 0 < dF)
    (z : lattice L (dL : ℤ)) (w : lattice F (dF : ℤ))
    (hz : 1 + (z : L) = ((normUnits L K C' / normUnits L K C : Lˣ) : L))
    (hw : 1 + (w : F) = ((normUnits F L (Units.mk0 (trace L K Y') hy') /
      normUnits F L (Units.mk0 (trace L K Y) hy) : Fˣ) : F)) :
    (twoOriginFunctionProduct L theta.character omega.character PsiF.character
      C C' Y Y' hy hy' : ℂ) =
      Stationary.normalizedCriticalValue L theta PsiL (normUnits L K C) dL hdL z *
      Stationary.normalizedCriticalValue F omega PsiF
        (normUnits F L (Units.mk0 (trace L K Y) hy)) dF hdF w := by
  have hunitL : positiveUnitOfLattice L hdL z = normUnits L K C' / normUnits L K C := by
    apply Units.ext
    exact hz
  have hunitF : positiveUnitOfLattice F hdF w =
      normUnits F L (Units.mk0 (trace L K Y') hy') /
        normUnits F L (Units.mk0 (trace L K Y) hy) := by
    apply Units.ext
    exact hw
  dsimp only [twoOriginFunctionProduct, Stationary.normalizedCriticalValue]
  rw [← hz, ← hw, ← hunitL, ← hunitF, hPsi]
  simp only [add_sub_cancel_left, Units.val_mul, Units.val_inv_eq_inv_val]
  ring

end Functions

/-- The trace estimate used for the lower perturbations, with integer
source and target depths and the actual upper break. -/
private theorem twoOrigin_trace_mem
    (E M : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    [Algebra E M] [ValuativeExtension E M] [Module.Finite E M]
    [PrimeCyclicExtension E M] {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak E M t)
    (hres : residueDegree E M = 1) (hdeg : Module.finrank E M = 2)
    {j r : ℤ} (hdepth : r ≤ (j + (t + 1 : ℕ)) / 2)
    {x : M} (hx : x ∈ lattice M j) : trace E M x ∈ lattice E r := by
  obtain ⟨piM, hpiM, hgen⟩ := monogenicUniformizer E M hres
  have hmap : trace E M x ∈
      Submodule.map ((trace E M).restrictScalars (ringOfIntegers E))
        ((lattice M j).restrictScalars (ringOfIntegers E)) :=
    Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  rw [cyclicPrime_trace_lattice_image_eq E M ht hres piM hpiM hgen, hdeg] at hmap
  apply lattice_antitone E hdepth
  simpa only [Nat.reduceSub, one_mul, Nat.cast_ofNat] using hmap

/-- Construct the perturbed top-field unit from its positive relative
depth. This also proves that the quotient lies in the full stated unit
filtration, so compact-unit unitarity applies to any quasi-character. -/
theorem twoOrigin_perturbedUnit
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (C : Eˣ) (V : E) {d : ℕ} (hd : 0 < d)
    (hV : V / (C : E) ∈ lattice E (d : ℤ)) :
    ∃ C' : Eˣ, (C' : E) = (C : E) + V ∧ C' / C ∈ unitFiltration E d := by
  let u := positiveUnitOfLattice E hd ⟨V / (C : E), hV⟩
  refine ⟨C * (u : Eˣ), ?_, ?_⟩
  · simp only [Units.val_mul, u, coe_positiveUnitOfLattice]
    field_simp
  · simp

section ActualOrigins

variable {F K : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]
  {pi : ringOfIntegers F} {e a b : ℕ}
  {u0 w0 : (ringOfIntegers F)ˣ} {s R0 : K}

local instance (L : IntermediateField F K) : ValuativeRel L :=
  Basic.intermediateFieldValuativeRel L
local instance (L : IntermediateField F K) : TopologicalSpace L :=
  Basic.intermediateFieldTopology L
local instance (L : IntermediateField F K) : IsNonarchimedeanLocalField L :=
  Basic.intermediateField_localField L
local instance (L : IntermediateField F K) : ValuativeExtension F L :=
  Basic.intermediateField_lowerValuativeExtension L

local instance (L : IntermediateField F K) : ValuativeExtension L K :=
  Basic.intermediateField_upperValuativeExtension L

/-- **The exact two-origin identity (`D:MX:two-origins`).**

For the actual aligned origin `Y` and the actual third-field element `X`,
the lower trace-norm increments differ by `-p_X * Tr(V)` on both flags.
Consequently the upper increments at `C + V` plus the lower increments
at `Y + V` have the displayed common value, with its full correction.

`O` and `CE` are the data proved by `dyadicMaximal_origin_data` and
`commonError`; they are also the data used in `higherCoefficients`.
The algebra holds for every integer `h` and every `V : K`, hence in
particular for every higher conductor and `V = Y * π^(2e) * z` in the
paper. No valuation bound or stationarity hypothesis is needed for this
exact identity, and none of the lower coefficients is replaced by a
trace norm at `C`.
-/
theorem dyadicMaximal_twoOrigin_identity
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)
    (g1 : Gal(K/D.firstField)) (g2 : Gal(K/D.secondField))
    (q3 : Gal(D.thirdField/F)) (X : D.thirdField) (h : ℤ)
    (CE : CommonErrorData D g1 g2 q3 X h) (V : K) :
    let C := D.adjustedOrigin X
    let Y := D.origin
    let p := D.adjustmentTrace X
    let E := elementarySymmetric F K 2 (C + V) - elementarySymmetric F K 2 C +
      p * trace F K V
    ((norm F D.firstField (trace D.firstField K (C + V)) -
        norm F D.firstField (trace D.firstField K C)) -
      (norm F D.firstField (trace D.firstField K (Y + V)) - D.beta1) =
        -p * trace F K V) ∧
    ((norm F D.secondField (trace D.secondField K (C + V)) -
        norm F D.secondField (trace D.secondField K C)) -
      (norm F D.secondField (trace D.secondField K (Y + V)) - D.beta2) =
        -p * trace F K V) ∧
    (trace F D.firstField (norm D.firstField K (C + V) - norm D.firstField K C) +
      (norm F D.firstField (trace D.firstField K (Y + V)) - D.beta1) = E) ∧
    (trace F D.secondField (norm D.secondField K (C + V) - norm D.secondField K C) +
      (norm F D.secondField (trace D.secondField K (Y + V)) - D.beta2) = E) := by
  letI : IsKleinFour Gal(K/F) := by
    let phi := Classical.choice hG
    constructor
    · rw [Nat.card_congr phi.toEquiv]
      simp
    · rw [Monoid.exponent_eq_of_mulEquiv phi]
      simp [Monoid.exponent_prod]
  letI : Algebra.IsQuadraticExtension F D.firstField :=
    { finrank_eq_two' := O.first_degree }
  letI : Algebra.IsQuadraticExtension F D.secondField :=
    { finrank_eq_two' := O.second_degree }
  have hdata1 := Basic.intermediateField_tower_compatible Nat.prime_two hG
    D.firstField O.first_degree
  have hdata2 := Basic.intermediateField_tower_compatible Nat.prime_two hG
    D.secondField O.second_degree
  letI : Algebra.IsQuadraticExtension D.firstField K :=
    { finrank_eq_two' := hdata1.2.2.2.2.2.2.2.2.2.2.1 }
  letI : Algebra.IsQuadraticExtension D.secondField K :=
    { finrank_eq_two' := hdata2.2.2.2.2.2.2.2.2.2.2.1 }
  exact ⟨twoOrigin_traceNorm_increment D.firstField _ _ V _ CE.first_trace,
    twoOrigin_traceNorm_increment D.secondField _ _ V _ CE.second_trace,
    twoOrigin_phase_increment D.firstField _ _ V _ CE.first_trace,
    twoOrigin_phase_increment D.secondField _ _ V _ CE.second_trace⟩

/-- The full pointwise products on the two actual maximal-case flags.
The lower coefficients are precisely `beta₁` and `beta₂`, expressed as
norms of the nonzero original traces. The upper and lower perturbations
are made at `C` and `Y` respectively, and the common character value and
the complete additive correction are retained in `ℂˣ`.

The nonzero perturbed traces are exactly what is needed to form the lower
norm quotients. There is no assumption about the traces at `C` or `C'`.
`twoOriginFunctionProduct_eq_criticalValues` identifies these products
with the actual critical functions at their terminal coordinates. -/
theorem dyadicMaximal_twoOrigin_function
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)
    (g1 : Gal(K/D.firstField)) (g2 : Gal(K/D.secondField))
    (q3 : Gal(D.thirdField/F)) (X : D.thirdField) (h : ℤ)
    (CE : CommonErrorData D g1 g2 q3 X h)
    (theta₁ : ContinuousQuasiChar D.firstField)
    (theta₂ : ContinuousQuasiChar D.secondField)
    (omega₁ : NormCharacter F D.firstField) (omega₂ : NormCharacter F D.secondField)
    (Theta : ContinuousQuasiChar K)
    (hc₁ : normQuasiChar D.firstField K theta₁ = Theta)
    (hc₂ : normQuasiChar D.secondField K theta₂ = Theta)
    (Psi : ContinuousAddChar F) (C C' : Kˣ) (V : K)
    (hC : (C : K) = D.adjustedOrigin X) (hC' : (C' : K) = (C : K) + V)
    (hy₁ : trace D.firstField K (D.origin + V) ≠ 0)
    (hy₂ : trace D.secondField K (D.origin + V) ≠ 0) :
    let P₁ := twoOriginFunctionProduct D.firstField theta₁ omega₁.1 Psi C C'
      D.origin (D.origin + V) O.h1_ne_zero hy₁
    let P₂ := twoOriginFunctionProduct D.secondField theta₂ omega₂.1 Psi C C'
      D.origin (D.origin + V) O.h2_ne_zero hy₂
    let Q := (Theta (C' / C))⁻¹ * Psi
      (-elementarySymmetric F K 2 (C' : K) + elementarySymmetric F K 2 (C : K) -
        D.adjustmentTrace X * trace F K V)
    P₁ = Q ∧ P₂ = Q ∧ P₁ = P₂ := by
  letI : IsKleinFour Gal(K/F) := by
    let phi := Classical.choice hG
    constructor
    · rw [Nat.card_congr phi.toEquiv]
      simp
    · rw [Monoid.exponent_eq_of_mulEquiv phi]
      simp [Monoid.exponent_prod]
  letI : Algebra.IsQuadraticExtension F D.firstField :=
    { finrank_eq_two' := O.first_degree }
  letI : Algebra.IsQuadraticExtension F D.secondField :=
    { finrank_eq_two' := O.second_degree }
  have hdata1 := Basic.intermediateField_tower_compatible Nat.prime_two hG
    D.firstField O.first_degree
  have hdata2 := Basic.intermediateField_tower_compatible Nat.prime_two hG
    D.secondField O.second_degree
  letI : Algebra.IsQuadraticExtension D.firstField K :=
    { finrank_eq_two' := hdata1.2.2.2.2.2.2.2.2.2.2.1 }
  letI : Algebra.IsQuadraticExtension D.secondField K :=
    { finrank_eq_two' := hdata2.2.2.2.2.2.2.2.2.2.2.1 }
  have hp₁ := twoOriginFunctionProduct_eq D.firstField theta₁ omega₁ Theta hc₁ Psi
    C C' D.origin (D.origin + V) V O.h1_ne_zero hy₁ hC' rfl (D.adjustmentTrace X)
    (by rw [hC]; exact CE.first_trace)
  have hp₂ := twoOriginFunctionProduct_eq D.secondField theta₂ omega₂ Theta hc₂ Psi
    C C' D.origin (D.origin + V) V O.h2_ne_zero hy₂ hC' rfl (D.adjustmentTrace X)
    (by rw [hC]; exact CE.second_trace)
  exact ⟨hp₁, hp₂, hp₁.trans hp₂.symm⟩

omit [IsGalois F K] in
/-- The actual perturbation `V = Y * π^(2e) * z` belongs to the complete
source lattice of depth `b`, including `z = 0`. -/
theorem twoOrigin_perturbation_mem
    (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)
    (hae : a ≤ e) (hb : b = 2 * e - 2 * a + 1)
    (piK : K) (hpiK : ord K piK = 1) (z : ringOfIntegers K) :
    D.origin * piK ^ (2 * e) * (z : K) ∈ lattice K (b : ℤ) := by
  have hY : D.origin ∈ lattice K (1 - 2 * (a : ℤ)) :=
    (mem_lattice K).2 (le_of_eq O.origin_order.symm)
  have hpi : piK ^ (2 * e) ∈ lattice K (2 * (e : ℤ)) := by
    rw [mem_lattice, ord_pow, hpiK,
      show (1 : WithTop ℤ) = ((1 : ℤ) : WithTop ℤ) from rfl, ← WithTop.coe_nsmul]
    apply WithTop.coe_le_coe.mpr
    simp
  have hz : (z : K) ∈ lattice K 0 :=
    (mem_lattice K).2 ((ord_nonneg_iff_mem_integer K (z : K)).2 z.property)
  have hm := mul_mem_lattice K (mul_mem_lattice K hY hpi) hz
  convert hm using 1
  congr 1
  omega

/-- The higher coefficient order and the perturbation bound construct
`C + V` as a genuine nonzero unit, with relative depth `b + 2h`.
The coefficient order is the one proved by `higherCoefficients`. -/
theorem twoOrigin_upper_perturbation
    (C : Kˣ) (V : K) (h : ℕ) (hb : 0 < b)
    (hC : ord K (C : K) = ((-2 * (h : ℤ) : ℤ) : WithTop ℤ))
    (hV : V ∈ lattice K (b : ℤ)) :
    ∃ C' : Kˣ, (C' : K) = (C : K) + V ∧ C' / C ∈ unitFiltration K (b + 2 * h) := by
  apply twoOrigin_perturbedUnit K C V (by omega)
  apply (div_mem_lattice_iff K _ _ (-2 * (h : ℤ)) ((b + 2 * h : ℕ) : ℤ) hC).2
  convert hV using 1
  congr 1
  push_cast
  ring

/-- On the actual two totally ramified upper edges, every perturbation
of depth `b` preserves the original lower trace orders. Thus all lower
character arguments used in `dyadicMaximal_twoOrigin_function` are
nonzero. The trace bounds are on whole ideals, not just residue values. -/
theorem twoOrigin_lower_perturbation
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)
    (ha : 1 ≤ a) (hae : a ≤ e) (hb : b = 2 * e - 2 * a + 1)
    (hres₁ : residueDegree D.firstField K = 1)
    (hres₂ : residueDegree D.secondField K = 1)
    (ht₁ : actualUpperBreak hG D.firstField O.first_degree (4 * e - 2 * a + 1))
    (ht₂ : actualUpperBreak hG D.secondField O.second_degree (2 * a - 1))
    (V : K) (hV : V ∈ lattice K (b : ℤ)) :
    trace D.firstField K V ∈ lattice D.firstField (3 * (e : ℤ) - 2 * (a : ℤ) + 1) ∧
    trace D.secondField K V ∈ lattice D.secondField (e : ℤ) ∧
    intermediateOrder D.firstField (trace D.firstField K (D.origin + V)) = (b : WithTop ℤ) ∧
    intermediateOrder D.secondField (trace D.secondField K (D.origin + V)) = 0 ∧
    trace D.firstField K (D.origin + V) ≠ 0 ∧
    trace D.secondField K (D.origin + V) ≠ 0 := by
  have E₁ := Basic.intermediateField_tower_compatible Nat.prime_two hG
    D.firstField O.first_degree
  have E₂ := Basic.intermediateField_tower_compatible Nat.prime_two hG
    D.secondField O.second_degree
  letI : PrimeCyclicExtension D.firstField K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension D.firstField K E₁.2.2.2.2.2.2.2.2.2.2.2.2
  letI : PrimeCyclicExtension D.secondField K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension D.secondField K E₂.2.2.2.2.2.2.2.2.2.2.2.2
  have ht₁' : PrimeCyclicExtension.IsLowerBreak D.firstField K (4 * e - 2 * a + 1) := by
    simpa [actualUpperBreak] using ht₁
  have ht₂' : PrimeCyclicExtension.IsLowerBreak D.secondField K (2 * a - 1) := by
    simpa [actualUpperBreak] using ht₂
  have hV₁ := twoOrigin_trace_mem D.firstField K ht₁' hres₁
    E₁.2.2.2.2.2.2.2.2.2.2.1
    (show 3 * (e : ℤ) - 2 * (a : ℤ) + 1 ≤
      ((b : ℤ) + (4 * e - 2 * a + 1 + 1 : ℕ)) / 2 by omega) hV
  have hV₂ := twoOrigin_trace_mem D.secondField K ht₂' hres₂
    E₂.2.2.2.2.2.2.2.2.2.2.1
    (show (e : ℤ) ≤ ((b : ℤ) + (2 * a - 1 + 1 : ℕ)) / 2 by omega) hV
  have hy₁ : ord D.firstField (trace D.firstField K D.origin) = (b : WithTop ℤ) :=
    O.h1_order
  have hy₂ : ord D.secondField (trace D.secondField K D.origin) = 0 := O.h2_order
  have hlt₁ : ord D.firstField (trace D.firstField K D.origin) <
      ord D.firstField (trace D.firstField K V) := by
    rw [hy₁]
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega))
      ((mem_lattice D.firstField).1 hV₁)
  have hlt₂ : ord D.secondField (trace D.secondField K D.origin) <
      ord D.secondField (trace D.secondField K V) := by
    rw [hy₂]
    exact lt_of_lt_of_le (show (0 : WithTop ℤ) < ((e : ℤ) : WithTop ℤ) by
      exact WithTop.coe_lt_coe.mpr (by omega)) ((mem_lattice D.secondField).1 hV₂)
  have hnew₁ : ord D.firstField (trace D.firstField K (D.origin + V)) =
      (b : WithTop ℤ) := by
    rw [map_add, ord_add_eq_min D.firstField hlt₁.ne, min_eq_left hlt₁.le, hy₁]
  have hnew₂ : ord D.secondField (trace D.secondField K (D.origin + V)) = 0 := by
    rw [map_add, ord_add_eq_min D.secondField hlt₂.ne, min_eq_left hlt₂.le, hy₂]
  exact ⟨hV₁, hV₂, hnew₁, hnew₂,
    (ord_ne_top_iff D.firstField).1 (by rw [hnew₁]; exact WithTop.coe_ne_top),
    (ord_ne_top_iff D.secondField).1 (by rw [hnew₂]; exact WithTop.zero_ne_top)⟩

end ActualOrigins

end

end LanglandsSecondMainLemma.Dyadic.Maximal
