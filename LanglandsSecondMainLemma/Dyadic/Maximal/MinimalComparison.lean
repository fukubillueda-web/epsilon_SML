import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Dyadic.Maximal.MinimalOrigin
import LanglandsSecondMainLemma.Stationary.CommonFunction

/-!
# Maximal dyadic minimal comparison

Paper Theorem 12.11 (`D:MX:minimal`), with the ambient maximal-break
setup in Section 12 and the common-twist realization `D:MX:twisted`.

The two graded bijections below come from FML's actual norm and trace
maps. The comparison keeps the full affine critical functions, constructs
the common origin with `minimalOrigin`, and includes both lower factors
in the canonical local-constant products. No sign is inferred from a
squared-sum identity.
-/

namespace LanglandsSecondMainLemma.Dyadic.Maximal
open LanglandsFirstMainLemma
open scoped BigOperators
noncomputable section

section Graded
variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

private theorem comparison_mul_mem {r s : ℤ} (c : E)
    (hc : ord E c = ((s - r : ℤ) : WithTop ℤ))
    {x : E} (hx : x ∈ lattice E r) : c * x ∈ lattice E s := by
  have h := mul_mem_lattice E ((mem_lattice E).2 hc.ge) hx
  simpa using h

/-- Multiplication by an actual element on successive fractional lattices. -/
def comparisonScaleGraded {r s : ℤ} (c : E)
    (hc : ord E c = ((s - r : ℤ) : WithTop ℤ)) :
    LatticeGradedPiece E r → LatticeGradedPiece E s :=
  Quotient.lift (fun x : lattice E r =>
    latticeQuotientMk E (show s ≤ s + 1 by omega)
      ⟨c * (x : E), comparison_mul_mem E c hc x.property⟩) (by
        intro x y hxy
        apply (latticeQuotientMk_eq_mk_iff E (show s ≤ s + 1 by omega)).2
        have h : (x : E) - (y : E) ∈ lattice E (r + 1) :=
          (latticeQuotientMk_eq_mk_iff E (show r ≤ r + 1 by omega)).1
            (Quotient.sound hxy)
        have hc' : ord E c = (((s + 1) - (r + 1) : ℤ) : WithTop ℤ) := by
          simpa using hc
        simpa only [← mul_sub] using comparison_mul_mem E c hc' h)

@[simp]
theorem comparisonScaleGraded_mk {r s : ℤ} (c : E)
    (hc : ord E c = ((s - r : ℤ) : WithTop ℤ)) (x : lattice E r) :
    comparisonScaleGraded E c hc (latticeQuotientMk E (by omega) x) =
      latticeQuotientMk E (show s ≤ s + 1 by omega)
        ⟨c * (x : E), comparison_mul_mem E c hc x.property⟩ := rfl

theorem comparisonScaleGraded_bijective {r s : ℤ} (c : E)
    (hc : ord E c = ((s - r : ℤ) : WithTop ℤ)) :
    Function.Bijective (comparisonScaleGraded E c hc) := by
  have hc0 : c ≠ 0 := (ord_ne_top_iff E).1 (by rw [hc]; exact WithTop.coe_ne_top)
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective E (show r ≤ r + 1 by omega) x
    obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective E (show r ≤ r + 1 by omega) y
    have h := (latticeQuotientMk_eq_mk_iff E (show s ≤ s + 1 by omega)).1 hxy
    apply (latticeQuotientMk_eq_mk_iff E (show r ≤ r + 1 by omega)).2
    have hdiv := (div_mem_lattice_iff E c (c * (x : E) - c * (y : E))
      (s - r) (r + 1) hc).2 (by
        rw [show s - r + (r + 1) = s + 1 by omega]
        exact h)
    simpa only [← mul_sub, mul_div_cancel_left₀ _ hc0] using hdiv
  · intro y
    obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective E (show s ≤ s + 1 by omega) y
    have hx : (y : E) / c ∈ lattice E r :=
      (div_mem_lattice_iff E c (y : E) (s - r) r hc).2 (by simpa only [sub_add_cancel] using y.property)
    refine ⟨latticeQuotientMk E (show r ≤ r + 1 by omega) ⟨(y : E) / c, hx⟩, ?_⟩
    rw [comparisonScaleGraded_mk]
    congr 1
    apply Subtype.ext
    exact mul_div_cancel₀ _ hc0

def comparisonScaleGradedEquiv {r s : ℤ} (c : E)
    (hc : ord E c = ((s - r : ℤ) : WithTop ℤ)) :
    LatticeGradedPiece E r ≃ LatticeGradedPiece E s :=
  Equiv.ofBijective (comparisonScaleGraded E c hc)
    (comparisonScaleGraded_bijective E c hc)

/-- The canonical displacement coordinate, at any positive depth. -/
def comparisonUnitLatticeEquiv {d : ℕ} (hd : 0 < d) :
    UnitGradedPiece E d ≃ LatticeGradedPiece E (d : ℤ) := by
  cases d with
  | zero => omega
  | succ d => exact (positiveUnitGradedEquivLattice E d).toEquiv.trans Multiplicative.toAdd

@[simp]
theorem comparisonUnitLatticeEquiv_mk {d : ℕ} (hd : 0 < d)
    (u : unitFiltration E d) :
    comparisonUnitLatticeEquiv E hd (unitGradedMk E d u) =
      latticeQuotientMk E (show (d : ℤ) ≤ (d : ℤ) + 1 by omega)
        (positiveUnitDisplacement E hd u) := by
  cases d with
  | zero => omega
  | succ d => rfl

@[simp]
theorem comparisonUnitLatticeEquiv_symm_mk {d : ℕ} (hd : 0 < d)
    (x : lattice E (d : ℤ)) :
    (comparisonUnitLatticeEquiv E hd).symm (latticeQuotientMk E (by omega) x) =
      unitGradedMk E d (positiveUnitOfLattice E hd x) := by
  apply (comparisonUnitLatticeEquiv E hd).injective
  rw [Equiv.apply_symm_apply, comparisonUnitLatticeEquiv_mk]
  congr 1
  apply Subtype.ext
  simp

private def comparisonResidueLift (d : ℕ) (pi : E)
    (hp : (ValuativeRel.valuation E).IsUniformizer pi) (x : ResidueField E) :
    lattice E (d : ℤ) :=
  ⟨pi ^ d * (teichmuller E x : E), by
    have hp' : pi ^ d ∈ lattice E (d : ℤ) := by
      rw [mem_lattice, ord_pow, ord_uniformizer E hp]
      norm_num
    simpa using mul_mem_lattice E hp'
      ((mem_lattice_zero_iff E).2 (teichmuller E x).property)⟩

private theorem comparisonResidueLift_coord (d : ℕ) (pi : E)
    (hp : (ValuativeRel.valuation E).IsUniformizer pi) (x : ResidueField E) :
    criticalNormLatticeGradedResidueAddEquiv E pi hp d
        (latticeQuotientMk E (by omega) (comparisonResidueLift E d pi hp x)) = x := by
  rw [criticalNormLatticeGradedResidueAddEquiv_mk]
  have heq : (comparisonResidueLift E d pi hp x : E) / pi ^ d =
      (teichmuller E x : E) := mul_div_cancel_left₀ _ (pow_ne_zero _ hp.ne_zero)
  simp only [heq, reduce]
  exact residueMap_teichmuller E x

end Graded

section Norm
variable (F E : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

/-- The actual norm on a positive lattice row strictly below its break. -/
def comparisonNormGradedEquiv {d t : ℕ} (hd : 0 < d)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hdt : d < t)
    (hres : residueDegree F E = 1) :
    LatticeGradedPiece E (d : ℤ) ≃ LatticeGradedPiece F (d : ℤ) := by
  let pi := Classical.choose (monogenicUniformizer F E hres)
  have hp := Classical.choose_spec (monogenicUniformizer F E hres)
  exact (comparisonUnitLatticeEquiv E hd).symm.trans
    ((gradedNormEquiv_belowBreak F E ht hdt hres pi hp.1 hp.2).toEquiv.trans
      (comparisonUnitLatticeEquiv F hd))

/-- FML containment, with the generating uniformizer constructed internally. -/
theorem comparisonNorm_mem {d t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hdt : d ≤ t)
    (hres : residueDegree F E = 1) (u : unitFiltration E d) :
    normUnits F E (u : Eˣ) ∈ unitFiltration F d := by
  obtain ⟨pi, hp, hg⟩ := monogenicUniformizer F E hres
  exact normMapsUnitFiltration_belowBreak F E ht hdt hres pi hp hg _ u.property

@[simp]
theorem comparisonNormGradedEquiv_mk {d t : ℕ} (hd : 0 < d)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hdt : d < t)
    (hres : residueDegree F E = 1) (x : lattice E (d : ℤ)) :
    comparisonNormGradedEquiv F E hd ht hdt hres
        (latticeQuotientMk E (by omega) x) =
      latticeQuotientMk F (show (d : ℤ) ≤ (d : ℤ) + 1 by omega)
        (positiveUnitDisplacement F hd ⟨normUnits F E (positiveUnitOfLattice E hd x),
          comparisonNorm_mem F E ht hdt.le hres _⟩) := by
  unfold comparisonNormGradedEquiv
  simp only [Equiv.trans_apply, comparisonUnitLatticeEquiv_symm_mk]
  exact comparisonUnitLatticeEquiv_mk F hd _

private theorem comparison_trace_mem {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hdeg : Module.finrank F E = 2) (hres : residueDegree F E = 1)
    {j q : ℤ} (hdepth : q ≤ (j + ((t + 1 : ℕ) : ℤ)) / 2)
    {x : E} (hx : x ∈ lattice E j) : trace F E x ∈ lattice F q := by
  obtain ⟨pi, hp, hg⟩ := monogenicUniformizer F E hres
  have hmap : trace F E x ∈
      Submodule.map ((trace F E).restrictScalars (ringOfIntegers F))
        ((lattice E j).restrictScalars (ringOfIntegers F)) :=
    Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  rw [cyclicPrime_trace_lattice_image_eq F E ht hres pi hp hg, hdeg] at hmap
  apply lattice_antitone F hdepth
  simpa only [Nat.reduceSub, one_mul, Nat.cast_ofNat] using hmap

/-- The normalized upper-trace change on its precise odd shifted row.
Its coefficient is the supplied element `C`, and the divisor is its actual trace. -/
def comparisonTraceGradedEquiv {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
    (hdeg : Module.finrank F E = 2) (hres : residueDegree F E = 1)
    (hram : ramificationIndex F E = 2) {d r q : ℤ} (hr : 0 ≤ r)
    (hodd : r + ((t + 1 : ℕ) : ℤ) = 2 * q + 1)
    (C : E) (hC : ord E C = ((r - d : ℤ) : WithTop ℤ))
    (hS : ord F (trace F E C) = 0) :
    LatticeGradedPiece E d ≃ LatticeGradedPiece F q := by
  let pi := Classical.choose (monogenicUniformizer F E hres)
  have hp := Classical.choose_spec (monogenicUniformizer F E hres)
  exact (comparisonScaleGradedEquiv E C hC).trans
    ((wildQuadraticGradedTraceEquiv F E pi hp.1 hp.2 ht htpos hram hdeg hr hodd).toEquiv.trans
      (comparisonScaleGradedEquiv F (trace F E C)⁻¹ (by simp [hS])))

private theorem comparisonTrace_mem {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hdeg : Module.finrank F E = 2) (hres : residueDegree F E = 1)
    {d r q : ℤ} (hodd : r + ((t + 1 : ℕ) : ℤ) = 2 * q + 1)
    (C : E) (hC : ord E C = ((r - d : ℤ) : WithTop ℤ))
    (hS : ord F (trace F E C) = 0) (x : lattice E d) :
    trace F E (C * (x : E)) / trace F E C ∈ lattice F q := by
  apply (div_mem_lattice_iff F (trace F E C) _ 0 q (by simpa using hS)).2
  simpa only [zero_add] using comparison_trace_mem F E ht hdeg hres
    (show q ≤ (r + ((t + 1 : ℕ) : ℤ)) / 2 by omega)
    (comparison_mul_mem E C hC x.property)

@[simp]
theorem comparisonTraceGradedEquiv_mk {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
    (hdeg : Module.finrank F E = 2) (hres : residueDegree F E = 1)
    (hram : ramificationIndex F E = 2) {d r q : ℤ} (hr : 0 ≤ r)
    (hodd : r + ((t + 1 : ℕ) : ℤ) = 2 * q + 1)
    (C : E) (hC : ord E C = ((r - d : ℤ) : WithTop ℤ))
    (hS : ord F (trace F E C) = 0) (x : lattice E d) :
    comparisonTraceGradedEquiv F E ht htpos hdeg hres hram hr hodd C hC hS
        (latticeQuotientMk E (by omega) x) =
      latticeQuotientMk F (show q ≤ q + 1 by omega)
        ⟨trace F E (C * (x : E)) / trace F E C,
          comparisonTrace_mem F E ht hdeg hres hodd C hC hS x⟩ := by
  unfold comparisonTraceGradedEquiv
  simp only [Equiv.trans_apply]
  let pi := Classical.choose (monogenicUniformizer F E hres)
  have hp := Classical.choose_spec (monogenicUniformizer F E hres)
  change comparisonScaleGraded F (trace F E C)⁻¹ (by simp [hS])
    (wildQuadraticGradedTraceEquiv F E pi hp.1 hp.2 ht htpos hram hdeg hr hodd
      (comparisonScaleGraded E C hC (latticeQuotientMk E _ x))) = _
  rw [comparisonScaleGraded_mk]
  unfold wildQuadraticGradedTraceEquiv quadraticGradedTraceEquiv
  simp only [LinearEquiv.ofBijective_apply]
  rw [quadraticGradedTrace_mk, comparisonScaleGraded_mk]
  congr 1
  apply Subtype.ext
  exact (div_eq_inv_mul _ _).symm

end Norm

section Perturbation
variable (F E : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeExtension F E] [PrimeCyclicExtension F E] in
private theorem comparison_norm_one_add (hdeg : Module.finrank F E = 2) (x : E) :
    norm F E (1 + x) = 1 + trace F E x + norm F E x := by
  have h := norm_one_add_eq_one_add_sum_elementarySymmetric F E x
  rw [hdeg] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd] at h
  rw [elementarySymmetric_one] at h
  have hn : elementarySymmetric F E 2 x = norm F E x := by
    rw [← hdeg]
    exact elementarySymmetric_finrank F E x
  simpa only [hn, add_assoc] using h

/-- The exact quadratic norm expansion at any certified trace and norm depths. -/
theorem comparisonNormAtDepth_mem {d q t : ℕ} (hd : 0 < d) (hq : 0 < q)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hdeg : Module.finrank F E = 2) (hres : residueDegree F E = 1)
    (htrace : (q : ℤ) ≤ ((d : ℤ) + ((t + 1 : ℕ) : ℤ)) / 2) (hnorm : q ≤ d)
    (x : lattice E (d : ℤ)) :
    normUnits F E (positiveUnitOfLattice E hd x) ∈ unitFiltration F q := by
  have htr := comparison_trace_mem F E ht hdeg hres htrace x.property
  have hnm : norm F E (x : E) ∈ lattice F (q : ℤ) := by
    apply lattice_antitone F (show (q : ℤ) ≤ (d : ℤ) by omega)
    simpa only [mem_lattice, ord_norm, hres, one_nsmul] using x.property
  cases q with
  | zero => omega
  | succ q =>
    apply (mem_unitFiltration_succ_iff_sub_mem_lattice F q _).2
    rw [coe_normUnits, coe_positiveUnitOfLattice, comparison_norm_one_add F E hdeg]
    simpa only [add_assoc, add_sub_cancel_left] using add_mem_lattice F htr hnm

omit [ValuativeExtension F E] [Module.Finite F E] [PrimeCyclicExtension F E] in
/-- The upper trace remains nonzero under a positive normalized trace change. -/
theorem comparisonTracePerturbation {d q : ℕ} (hd : 0 < d) (hq : 0 < q)
    (C : Eˣ) (hS : trace F E (C : E) ≠ 0) (x : lattice E (d : ℤ))
    (hv : trace F E ((C : E) * (x : E)) / trace F E (C : E) ∈ lattice F (q : ℤ)) :
    ∃ hS' : trace F E ((C * positiveUnitOfLattice E hd x : Eˣ) : E) ≠ 0,
      Units.mk0 (trace F E ((C * positiveUnitOfLattice E hd x : Eˣ) : E)) hS' /
          Units.mk0 (trace F E (C : E)) hS =
        (positiveUnitOfLattice F hq ⟨_, hv⟩ : Fˣ) := by
  let v : lattice F (q : ℤ) := ⟨_, hv⟩
  have heq : trace F E ((C * positiveUnitOfLattice E hd x : Eˣ) : E) =
      trace F E (C : E) * ((positiveUnitOfLattice F hq v : Fˣ) : F) := by
    rw [Units.val_mul, coe_positiveUnitOfLattice, coe_positiveUnitOfLattice,
      mul_add, mul_one, map_add]
    dsimp [v]
    field_simp
  have hn : trace F E ((C * positiveUnitOfLattice E hd x : Eˣ) : E) ≠ 0 := by
    rw [heq]
    exact mul_ne_zero hS (Units.ne_zero _)
  refine ⟨hn, ?_⟩
  apply Units.ext
  rw [Units.val_div_eq_div_val, Units.val_mk0, Units.val_mk0, heq]
  exact mul_div_cancel_left₀ _ hS

end Perturbation

section Flag
open Stationary
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [Module.Finite F K]
  (L : IntermediateField F K)
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

omit [Module.Finite F K] in
/-- Interpret both factors at the literal perturbed origin. All memberships
in this lemma are proved from the break bounds in the comparison below. -/
theorem comparisonProductPerturbation
    (theta : LocalQuasiCharData L) (omega : LocalQuasiCharData F)
    (psiF : LocalAddCharData F) (psiL : LocalAddCharData L) (alpha : Fˣ)
    (C : Kˣ) (hS : trace L K (C : K) ≠ 0)
    {d dL q dF : ℕ} (hd : 0 < d) (hdL : 0 < dL) (hq : 0 < q) (hdF : 0 < dF)
    (x : lattice K (d : ℤ))
    (hN : normUnits L K (positiveUnitOfLattice K hd x) ∈ unitFiltration L dL)
    (v : lattice L (q : ℤ))
    (hS' : trace L K ((C * positiveUnitOfLattice K hd x : Kˣ) : K) ≠ 0)
    (hv : Units.mk0 (trace L K ((C * positiveUnitOfLattice K hd x : Kˣ) : K)) hS' /
        Units.mk0 (trace L K (C : K)) hS = (positiveUnitOfLattice L hq v : Lˣ))
    (hW : normUnits F L (positiveUnitOfLattice L hq v) ∈ unitFiltration F dF) :
    commonFunctionProduct L theta omega psiF psiL alpha C
        (C * positiveUnitOfLattice K hd x) hS hS' =
      normalizedCriticalValue L theta
        (scaleAddCharData L psiL (Units.map (algebraMap F L).toMonoidHom alpha))
        (normUnits L K C) dL hdL (positiveUnitDisplacement L hdL ⟨_, hN⟩) *
      normalizedCriticalValue F omega (scaleAddCharData F psiF alpha)
        (commonOriginLowerCoefficient L C hS) dF hdF
        (positiveUnitDisplacement F hdF ⟨_, hW⟩) := by
  apply commonFunctionProduct_eq_criticalValues L theta omega psiF psiL alpha C
    (C * positiveUnitOfLattice K hd x) hS hS' dL dF hdL hdF
  · simp only [coe_positiveUnitDisplacement, add_sub_cancel,
      map_mul, mul_div_cancel_left]
  · have hw : commonOriginLowerCoefficient L
          (C * positiveUnitOfLattice K hd x) hS' / commonOriginLowerCoefficient L C hS =
        normUnits F L (positiveUnitOfLattice L hq v) := by
      unfold commonOriginLowerCoefficient
      rw [← map_div, hv]
    rw [hw]
    simp only [coe_positiveUnitDisplacement, add_sub_cancel]

end Flag

section Residual
open Stationary
variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  (theta : LocalQuasiCharData E) (psi : LocalAddCharData E) (alpha Z : Eˣ)
  (d : ℕ) (hm : theta.conductor = 2 * d + 1) (hlarge : 1 < theta.conductor)
  (hZ : ord E (Z : E) =
    ((-(scaleAddCharData E psi alpha).conductor - (theta.conductor : ℤ) : ℤ) : WithTop ℤ))
  (hs : IsNormalizedStationaryCoefficientAtDepth E theta
    (scaleAddCharData E psi alpha) Z (d + 1) (by omega))

/-- The full affine critical function on its actual lattice quotient. -/
def comparisonCriticalFunction : LatticeGradedPiece E (d : ℤ) → ℂ :=
  Quotient.lift (normalizedCriticalValue E theta (scaleAddCharData E psi alpha) Z d
    (by omega)) (by
      intro x y hxy
      apply normalizedCriticalValue_odd_eq_of_congruent E theta psi alpha Z d hm hlarge hZ hs
      have h := (latticeQuotientMk_eq_mk_iff_congruentAtDepth E
        (show (d : ℤ) ≤ (d : ℤ) + 1 by omega)).1 (Quotient.sound hxy)
      simpa only [Nat.cast_add, Nat.cast_one] using h)

@[simp]
theorem comparisonCriticalFunction_mk (x : lattice E (d : ℤ)) :
    comparisonCriticalFunction E theta psi alpha Z d hm hlarge hZ hs
        (latticeQuotientMk E (by omega) x) =
      normalizedCriticalValue E theta (scaleAddCharData E psi alpha) Z d (by omega) x := rfl

/-- Sum over the actual terminal row, without a choice of residue coordinates. -/
def comparisonCriticalSum : ℂ := by
  letI := Fintype.ofFinite (LatticeGradedPiece E (d : ℤ))
  exact (Real.sqrt (residueCard E : ℝ) : ℂ)⁻¹ *
    ∑ x : LatticeGradedPiece E (d : ℤ),
      comparisonCriticalFunction E theta psi alpha Z d hm hlarge hZ hs x

private theorem comparisonResidualFunction_eq (pi : E)
    (hp : (ValuativeRel.valuation E).IsUniformizer pi) (x : ResidueField E) :
    normalizedResidualFunction E theta psi alpha Z d hm hlarge
        (Units.mk0 (pi ^ d) (pow_ne_zero _ hp.ne_zero))
        (by simp [ord_uniformizer E hp]) x =
      comparisonCriticalFunction E theta psi alpha Z d hm hlarge hZ hs
        (latticeQuotientMk E (by omega) (comparisonResidueLift E d pi hp x)) := by
  rw [comparisonCriticalFunction_mk]
  unfold normalizedResidualFunction normalizedCriticalValue
  congr 1
  · congr 2
    dsimp [comparisonResidueLift]
    ring

/-- The quotient sum is precisely the paper's complete normalized odd sum. -/
theorem comparisonCriticalSum_eq_normalized (pi : E)
    (hp : (ValuativeRel.valuation E).IsUniformizer pi) :
    comparisonCriticalSum E theta psi alpha Z d hm hlarge hZ hs =
      normalizedResidualFactor E theta psi alpha Z d hm hlarge
        (Units.mk0 (pi ^ d) (pow_ne_zero _ hp.ne_zero))
        (by simp [ord_uniformizer E hp]) := by
  letI := residueFieldFintype E
  letI := Fintype.ofFinite (LatticeGradedPiece E (d : ℤ))
  unfold comparisonCriticalSum normalizedResidualFactor
  congr 1
  apply Fintype.sum_equiv (criticalNormLatticeGradedResidueAddEquiv E pi hp d).toEquiv
  intro x
  rw [comparisonResidualFunction_eq E theta psi alpha Z d hm hlarge hZ hs pi hp]
  congr 1
  apply (criticalNormLatticeGradedResidueAddEquiv E pi hp d).injective
  exact (comparisonResidueLift_coord E d pi hp _).symm

/-- No residue-coordinate choice changes the complete odd factor. -/
theorem comparisonCriticalSum_eq_complete :
    comparisonCriticalSum E theta psi alpha Z d hm hlarge hZ hs =
      completeNormalizedResidualFactor E theta psi alpha Z hlarge := by
  obtain ⟨pi, hpi⟩ := exists_ord_eq E 1
  have hp := (ord_eq_one_iff_isUniformizer E pi).1 (by simpa using hpi)
  have ho : IsOrdinaryStationaryCoefficient E theta (scaleAddCharData E psi alpha)
      Z hlarge := by
    refine ⟨hZ, ?_⟩
    have hd : theta.conductor / 2 + theta.conductor % 2 = d + 1 := by omega
    simpa only [hd] using hs
  have hf := (normalizedFactor E theta psi alpha Z d 1 (by omega) hm hlarge hZ hs).2
    rfl (Units.mk0 (pi ^ d) (pow_ne_zero _ hp.ne_zero))
      (by simp [ord_uniformizer E hp])
  rw [← comparisonCriticalSum_eq_normalized E theta psi alpha Z d hm hlarge hZ hs pi hp] at hf
  have hg := completeNormalizedFactor E theta psi alpha Z hlarge ho
  have hn : (theta.character ((-alpha * Z)⁻¹) : ℂ) *
      ((scaleAddCharData E psi alpha).character (-(Z : E)) : ℂ) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
  exact (mul_left_cancel₀ hn) (hf.symm.trans hg)

end Residual

section Pair
open Stationary
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [Module.Finite F K] [IsGalois F K] [IsKleinFour Gal(K/F)]
  (I J : IntermediateField F K)
  [ValuativeRel I] [TopologicalSpace I] [IsNonarchimedeanLocalField I]
  [ValuativeRel J] [TopologicalSpace J] [IsNonarchimedeanLocalField J]
  [ValuativeExtension F I] [ValuativeExtension I K]
  [ValuativeExtension F J] [ValuativeExtension J K]
  [PrimeCyclicExtension F I] [PrimeCyclicExtension I K]
  [PrimeCyclicExtension F J] [PrimeCyclicExtension J K]
  [Algebra.IsQuadraticExtension F I] [Algebra.IsQuadraticExtension I K]
  [Algebra.IsQuadraticExtension F J] [Algebra.IsQuadraticExtension J K]

set_option maxHeartbeats 1200000 in
/-- The two complete residual products at the constructed minimal origin agree.
The two bijections are the actual upper norm and the normalized upper trace
followed by the lower norm. Even factors are retained until proved equal to one. -/
theorem comparisonResidualProducts
    {e a : ℕ} (ha : 1 ≤ a) (hae : a ≤ e)
    (hIK : Module.finrank I K = 2) (hJK : Module.finrank J K = 2)
    (hresIK : residueDegree I K = 1) (hresJK : residueDegree J K = 1)
    (hresFI : residueDegree F I = 1) (hresFJ : residueDegree F J = 1)
    (hramJK : ramificationIndex J K = 2)
    (htI : PrimeCyclicExtension.IsLowerBreak F I (2 * a - 1))
    (htJ : PrimeCyclicExtension.IsLowerBreak F J (2 * e))
    (htIK : PrimeCyclicExtension.IsLowerBreak I K (4 * e - 2 * a + 1))
    (htJK : PrimeCyclicExtension.IsLowerBreak J K (2 * a - 1))
    (thetaI : LocalQuasiCharData I) (thetaJ : LocalQuasiCharData J)
    (omegaI omegaJ : LocalQuasiCharData F)
    (nuI : NormCharacter F I) (nuJ : NormCharacter F J)
    (hnuI : omegaI.character = nuI.1) (hnuJ : omegaJ.character = nuJ.1)
    (Theta : ContinuousQuasiChar K)
    (hcI : normQuasiChar I K thetaI.character = Theta)
    (hcJ : normQuasiChar J K thetaJ.character = Theta)
    (psiF : LocalAddCharData F) (psiI : LocalAddCharData I) (psiJ : LocalAddCharData J)
    (hpsiI : psiI.character = psiF.character.compTrace)
    (hpsiJ : psiJ.character = psiF.character.compTrace)
    (alpha : Fˣ) (C : Kˣ)
    (hC : ord K (C : K) = ((1 - 2 * (a : ℤ) : ℤ) : WithTop ℤ))
    (hSI : ord I (trace I K (C : K)) =
      ((2 * (e : ℤ) - 2 * (a : ℤ) + 1 : ℤ) : WithTop ℤ))
    (hSJ : ord J (trace J K (C : K)) = 0)
    (hSI0 : trace I K (C : K) ≠ 0) (hSJ0 : trace J K (C : K) ≠ 0)
    (hmI : thetaI.conductor = 4 * e + 1) (hmJ : thetaJ.conductor = 2 * e + 2 * a)
    (hwI : omegaI.conductor = 2 * a) (hwJ : omegaJ.conductor = 2 * e + 1)
    (hsI : IsOrdinaryStationaryCoefficient I thetaI
      (scaleAddCharData I psiI (Units.map (algebraMap F I).toMonoidHom alpha))
      (normUnits I K C) (by omega))
    (hsJ : IsOrdinaryStationaryCoefficient J thetaJ
      (scaleAddCharData J psiJ (Units.map (algebraMap F J).toMonoidHom alpha))
      (normUnits J K C) (by omega))
    (hsWI : IsOrdinaryStationaryCoefficient F omegaI (scaleAddCharData F psiF alpha)
      (commonOriginLowerCoefficient I C hSI0) (by omega))
    (hsWJ : IsOrdinaryStationaryCoefficient F omegaJ (scaleAddCharData F psiF alpha)
      (commonOriginLowerCoefficient J C hSJ0) (by omega)) :
    commonOriginResidualProduct I thetaI omegaI psiF psiI alpha C hSI0 (by omega) (by omega) =
      commonOriginResidualProduct J thetaJ omegaJ psiF psiJ alpha C hSJ0 (by omega) (by omega) := by
  have he : 0 < e := by omega
  have ha0 : 0 < a := by omega
  have h2e : 0 < 2 * e := by omega
  have hma : 0 < e + a := by omega
  have hmI' : thetaI.conductor = 2 * (2 * e) + 1 := by omega
  have hmJ' : thetaJ.conductor = 2 * (e + a) := by omega
  have hlargeI : 1 < thetaI.conductor := by omega
  have hlargeJ : 1 < thetaJ.conductor := by omega
  have hlargeWI : 1 < omegaI.conductor := by omega
  have hlargeWJ : 1 < omegaJ.conductor := by omega
  have hsI' : IsNormalizedStationaryCoefficientAtDepth I thetaI
      (scaleAddCharData I psiI (Units.map (algebraMap F I).toMonoidHom alpha))
      (normUnits I K C) (2 * e + 1) (by omega) := by
    convert hsI.2 using 1; omega
  have hsJ' : IsNormalizedStationaryCoefficientAtDepth J thetaJ
      (scaleAddCharData J psiJ (Units.map (algebraMap F J).toMonoidHom alpha))
      (normUnits J K C) (e + a) hma := by
    convert hsJ.2 using 1; omega
  have hsWI' : IsNormalizedStationaryCoefficientAtDepth F omegaI
      (scaleAddCharData F psiF alpha) (commonOriginLowerCoefficient I C hSI0) a ha0 := by
    convert hsWI.2 using 1; omega
  have hsWJ' : IsNormalizedStationaryCoefficientAtDepth F omegaJ
      (scaleAddCharData F psiF alpha) (commonOriginLowerCoefficient J C hSJ0) (e + 1)
      (by omega) := by
    convert hsWJ.2 using 1; omega
  let HI := comparisonCriticalFunction I thetaI psiI
    (Units.map (algebraMap F I).toMonoidHom alpha) (normUnits I K C)
    (2 * e) hmI' hlargeI hsI.1 hsI'
  let HJ := comparisonCriticalFunction F omegaJ psiF alpha
    (commonOriginLowerCoefficient J C hSJ0) e hwJ hlargeWJ hsWJ.1 hsWJ'
  let P := comparisonNormGradedEquiv I K h2e htIK (by omega) hresIK
  let r : ℤ := 2 * (e : ℤ) - 2 * (a : ℤ) + 1
  have hr : 0 ≤ r := by dsimp [r]; omega
  have hodd : r + ((2 * a - 1 + 1 : ℕ) : ℤ) = 2 * (e : ℤ) + 1 := by
    dsimp [r]; omega
  have hCr : ord K (C : K) = ((r - (2 * e : ℕ) : ℤ) : WithTop ℤ) := by
    rw [hC]
    congr 1
    dsimp [r]
    omega
  let T := comparisonTraceGradedEquiv J K htJK (by omega) hJK hresJK hramJK hr hodd
    (C : K) hCr hSJ
  let Q := T.trans (comparisonNormGradedEquiv F J he htJ (by omega) hresFJ)
  have hpoint : ∀ z : LatticeGradedPiece K ((2 * e : ℕ) : ℤ), HI (P z) = HJ (Q z) := by
    intro z
    obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective K (by omega) z
    let u : Kˣ := positiveUnitOfLattice K h2e x
    let C' : Kˣ := C * u
    have hNI := comparisonNorm_mem I K htIK (show 2 * e ≤ 4 * e - 2 * a + 1 by omega)
      hresIK (positiveUnitOfLattice K h2e x)
    have hNJ := comparisonNormAtDepth_mem J K h2e hma htJK hJK hresJK (by omega) (by omega) x
    have hvI : trace I K ((C : K) * (x : K)) / trace I K (C : K) ∈ lattice I (a : ℤ) := by
      apply (div_mem_lattice_iff I _ _ r (a : ℤ) hSI).2
      apply comparison_trace_mem I K htIK hIK hresIK
        (show r + (a : ℤ) ≤ (r + ((4 * e - 2 * a + 1 + 1 : ℕ) : ℤ)) / 2 by
          dsimp [r]; omega)
      exact comparison_mul_mem K (C : K) hCr x.property
    let vI : lattice I (a : ℤ) := ⟨_, hvI⟩
    have hvJ := comparisonTrace_mem J K htJK hJK hresJK hodd (C : K) hCr hSJ x
    let vJ : lattice J (e : ℤ) := ⟨_, hvJ⟩
    obtain ⟨hSI', hratioI⟩ := comparisonTracePerturbation I K h2e ha0 C hSI0 x hvI
    obtain ⟨hSJ', hratioJ⟩ := comparisonTracePerturbation J K h2e he C hSJ0 x hvJ
    have hWI := comparisonNorm_mem F I htI (show a ≤ 2 * a - 1 by omega) hresFI
      (positiveUnitOfLattice I ha0 vI)
    have hWJ := comparisonNorm_mem F J htJ (show e ≤ 2 * e by omega) hresFJ
      (positiveUnitOfLattice J he vJ)
    have hPI := comparisonProductPerturbation I thetaI omegaI psiF psiI alpha C hSI0
      h2e h2e ha0 ha0 x hNI vI hSI' hratioI hWI
    have hPJ := comparisonProductPerturbation J thetaJ omegaJ psiF psiJ alpha C hSJ0
      h2e hma he he x hNJ vJ hSJ' hratioJ hWJ
    rw [normalizedCriticalValue_even F omegaI _ _ a hwI hlargeWI hsWI', mul_one] at hPI
    rw [normalizedCriticalValue_even J thetaJ _ _ (e + a) hmJ' hlargeJ hsJ', one_mul] at hPJ
    have heq := (commonFunctionProduct_eq I thetaI omegaI nuI hnuI Theta hcI
      psiF psiI hpsiI alpha C C' hSI0 hSI').trans
      (commonFunctionProduct_eq J thetaJ omegaJ nuJ hnuJ Theta hcJ
        psiF psiJ hpsiJ alpha C C' hSJ0 hSJ').symm
    rw [hPI, hPJ] at heq
    dsimp only [HI, HJ, P, Q, T, Equiv.trans_apply]
    rw [comparisonNormGradedEquiv_mk, comparisonTraceGradedEquiv_mk,
      comparisonNormGradedEquiv_mk, comparisonCriticalFunction_mk, comparisonCriticalFunction_mk]
    exact heq
  letI := Fintype.ofFinite (LatticeGradedPiece K ((2 * e : ℕ) : ℤ))
  letI := Fintype.ofFinite (LatticeGradedPiece I ((2 * e : ℕ) : ℤ))
  letI := Fintype.ofFinite (LatticeGradedPiece F (e : ℤ))
  have hsum : ∑ z, HI z = ∑ z, HJ z := by
    calc
      ∑ z, HI z = ∑ z, HI (P z) := (Fintype.sum_equiv P _ _ (fun _ => rfl)).symm
      _ = ∑ z, HJ (Q z) := Finset.sum_congr rfl (fun z _ => hpoint z)
      _ = ∑ z, HJ z := Fintype.sum_equiv Q _ _ (fun _ => rfl)
  have hcard : residueCard I = residueCard F := by
    have h := Nat.card_congr (P.symm.trans Q)
    simpa only [LatticeGradedPiece, latticeQuotient_card, add_sub_cancel_left,
      Int.toNat_one, pow_one] using h
  unfold commonOriginResidualProduct
  rw [completeNormalizedResidualFactor_even F omegaI _ _ _ hlargeWI (by omega), mul_one,
    completeNormalizedResidualFactor_even J thetaJ _ _ _ hlargeJ (by omega), one_mul,
    ← comparisonCriticalSum_eq_complete I thetaI psiI _ _ (2 * e) hmI' hlargeI hsI.1 hsI',
    ← comparisonCriticalSum_eq_complete F omegaJ psiF alpha _ e hwJ hlargeWJ hsWJ.1 hsWJ']
  change (Real.sqrt (residueCard I : ℝ) : ℂ)⁻¹ * (∑ z, HI z) =
    (Real.sqrt (residueCard F : ℝ) : ℂ)⁻¹ * (∑ z, HJ z)
  rw [hcard, hsum]

end Pair

section ChartAdapters
open Stationary
variable (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

private theorem comparisonStationary_of_coreChart
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E) (Z : Eˣ)
    (hlarge : 1 < theta.conductor) {r : ℕ} (hr : 0 < r)
    (hdepth : theta.conductor / 2 + theta.conductor % 2 = r)
    (hZ : ord E (Z : E) = ((-Psi.conductor - (theta.conductor : ℤ) : ℤ) : WithTop ℤ))
    (hchart : ∀ u : unitFiltration E r,
      theta.character (u : Eˣ) = corePhaseValue E Psi.character (Z : E) (u : Eˣ)) :
    IsOrdinaryStationaryCoefficient E theta Psi Z hlarge := by
  refine ⟨hZ, ?_⟩
  have h : IsNormalizedStationaryCoefficientAtDepth E theta Psi Z r hr := by
    intro z
    have h := hchart (positiveUnitOfLattice E hr (-z))
    simpa [corePhaseValue] using h
  simpa only [hdepth] using h

private theorem comparisonStationary_of_lowerChart
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E) (Z : Eˣ)
    (hlarge : 1 < theta.conductor) {r : ℕ} (hr : 0 < r)
    (hdepth : theta.conductor / 2 + theta.conductor % 2 = r)
    (hZ : ord E (Z : E) = ((-Psi.conductor - (theta.conductor : ℤ) : ℤ) : WithTop ℤ))
    (hchart : ∀ (z : E) (hz : z ∈ lattice E (r : ℤ)),
      theta.character (lowerOneSubUnit E r hr z hz) = Psi.character ((Z : E) * z)) :
    IsOrdinaryStationaryCoefficient E theta Psi Z hlarge := by
  refine ⟨hZ, ?_⟩
  have h : IsNormalizedStationaryCoefficientAtDepth E theta Psi Z r hr := by
    intro z
    have hu : (positiveUnitOfLattice E hr (-z) : Eˣ) =
        lowerOneSubUnit E r hr (z : E) z.property := by
      apply Units.ext
      simp [coe_lowerOneSubUnit, sub_eq_add_neg]
    rw [hu]
    exact hchart (z : E) z.property
  simpa only [hdepth] using h

end ChartAdapters

section EdgeAdapters
variable (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

private theorem comparison_normCharacter_unique {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hdeg : Module.finrank F E = 2) (hres : residueDegree F E = 1)
    (mu nu : NormCharacter F E) (hmu : mu ≠ 1) (hnu : nu ≠ 1) : mu = nu := by
  obtain ⟨pi, hp, hg⟩ := monogenicUniformizer F E hres
  have hc : Nat.card (NormCharacter F E) = 2 :=
    (ramifiedNormCharacter_card F E ht hres pi hp hg).trans hdeg
  exact ((Nat.card_eq_two_iff' (1 : NormCharacter F E)).mp hc).unique hmu hnu

private theorem comparison_normCharacter_conductor {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hres : residueDegree F E = 1)
    (mu : NormCharacter F E) (hmu : mu ≠ 1)
    (omega : LocalQuasiCharData F) (homega : omega.character = mu.1) :
    omega.conductor = t + 1 := by
  obtain ⟨pi, hp, hg⟩ := monogenicUniformizer F E hres
  apply omega.isConductor.unique
  rw [homega]
  exact ramifiedNormCharacter_conductor F E ht hres pi hp hg mu hmu

private theorem comparison_scaled_trace_character
    (psiF : LocalAddCharData F) (psiE : LocalAddCharData E)
    (hpsi : psiE.character = psiF.character.compTrace) (alpha : Fˣ) :
    (scaleAddCharData E psiE (Units.map (algebraMap F E).toMonoidHom alpha)).character =
      (scaleAddCharData F psiF alpha).character.compTrace := by
  ext x
  simp only [scaleAddCharData_character_apply, hpsi, ContinuousAddChar.compTrace_apply]
  congr 2
  change trace F E (algebraMap F E (alpha : F) * x) = (alpha : F) * trace F E x
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

private theorem comparison_trace_conductor {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hdeg : Module.finrank F E = 2) (hres : residueDegree F E = 1)
    (PsiF : LocalAddCharData F) (PsiE : LocalAddCharData E)
    (hpsi : PsiE.character = PsiF.character.compTrace) :
    PsiE.conductor = 2 * PsiF.conductor + ((t + 1 : ℕ) : ℤ) := by
  obtain ⟨pi, hp, hg⟩ := monogenicUniformizer F E hres
  simpa only [hdeg, Nat.reduceSub, one_mul, Nat.cast_ofNat] using
    PsiF.conductor_compTrace_eq_cyclicPrime F E ht hres pi hp hg PsiE hpsi

end EdgeAdapters

section Diagram
open Stationary
variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]

local instance comparison_valuation (L : IntermediateField F K) : ValuativeRel L :=
  Basic.intermediateFieldValuativeRel L
local instance comparison_topology (L : IntermediateField F K) : TopologicalSpace L :=
  Basic.intermediateFieldTopology L
local instance comparison_localField (L : IntermediateField F K) : IsNonarchimedeanLocalField L :=
  Basic.intermediateField_localField L
local instance comparison_lowerValuation (L : IntermediateField F K) : ValuativeExtension F L :=
  Basic.intermediateField_lowerValuativeExtension L
local instance comparison_upperValuation (L : IntermediateField F K) : ValuativeExtension L K :=
  Basic.intermediateField_upperValuativeExtension L

omit [Module.Free F K] in
private theorem comparison_residueDegrees (L : IntermediateField F K)
    (hres : residueDegree F K = 1) :
    residueDegree F L = 1 ∧ residueDegree L K = 1 := by
  obtain ⟨x, hx⟩ := exists_ord_eq K 1
  have h := congrArg (ord F) (Basic.norm_tower (F := F) (L := L) x)
  rw [ord_norm, ord_norm, ord_norm, hres, hx] at h
  have hz : residueDegree F L • residueDegree L K • (1 : ℤ) = 1 • (1 : ℤ) := by
    exact_mod_cast h
  have hz' : (residueDegree F L : ℤ) * (residueDegree L K : ℤ) = 1 := by
    simpa [nsmul_eq_mul] using hz
  have hm : residueDegree F L * residueDegree L K = 1 := by exact_mod_cast hz'
  exact mul_eq_one.mp hm

variable {pi : ringOfIntegers F} {e a b : ℕ}
  {u0 w0 : (ringOfIntegers F)ˣ} {s R0 : K}

set_option maxHeartbeats 1600000 in
/-- **Exact minimal comparison** (`D:MX:minimal`, Theorem 12.11).

The common-twist presentation, full core charts, and core conductors are the
outputs of `models`, `twist`, and `normalization`. For every twist with
`n ≤ 2e+a`, `minimalOrigin` constructs the permitted normalization and the
actual common origin. This theorem then proves both graded bijections, retains
all four parity factors, and compares the canonical FML local constants with
the complete lower norm-character products. No residual identity or exact
norm representative is an input to the comparison. -/
theorem minimalComparison
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)
    (hres : residueDegree F K = 1)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (ha : 1 ≤ a) (hae : a ≤ e) (hb : b = 2 * e - 2 * a + 1)
    (ht₁ : actualLowerBreak hG D.firstField O.first_degree (2 * a - 1))
    (ht₂ : actualLowerBreak hG D.secondField O.second_degree (2 * e))
    (ht₃ : actualLowerBreak hG D.thirdField O.third_degree (2 * e))
    (hU₁ : actualUpperBreak hG D.firstField O.first_degree (4 * e - 2 * a + 1))
    (hU₂ : actualUpperBreak hG D.secondField O.second_degree (2 * a - 1))
    (g1 : Gal(K/D.firstField)) (hg1 : g1 ≠ 1) (hg1R : g1 D.R = -D.R)
    (g2 : Gal(K/D.secondField)) (hg2 : g2 ≠ 1) (hg2S : g2 D.S = -D.S)
    (q1 : Gal(D.firstField/F)) (hq1 : q1 ≠ 1)
    (hq1S : q1 D.firstGenerator = -D.firstGenerator)
    (q2 : Gal(D.secondField/F)) (hq2 : q2 ≠ 1)
    (hq2R : q2 D.secondGenerator = -D.secondGenerator)
    (q3 : Gal(D.thirdField/F)) (hq3 : q3 ≠ 1)
    (hq3SR : q3 D.thirdGenerator = -D.thirdGenerator)
    (tau₁ : NormCharacter F D.firstField) (htau₁ : tau₁ ≠ 1)
    (tau₂ : NormCharacter F D.secondField) (htau₂ : tau₂ ≠ 1)
    (tau₃ : NormCharacter F D.thirdField) (htau₃ : tau₃ ≠ 1)
    (psi : LocalAddCharData F) (alpha : Fˣ)
    (halpha : ord F (alpha : F) =
      ((-psi.conductor - (2 * (e : ℤ) + 1) : ℤ) : WithTop ℤ))
    (chi₁ : ContinuousQuasiChar D.firstField) (chi₂ : ContinuousQuasiChar D.secondField)
    (chi₃ : ContinuousQuasiChar D.thirdField)
    (hchi₁ : IsMultiplicativeConductor D.firstField chi₁ (4 * e + 1))
    (hchi₂ : IsMultiplicativeConductor D.secondField chi₂ (2 * e + 2 * a))
    (H : NormalizationFormulas F D.firstField D.secondField D.thirdField
      a e ha tau₁ tau₂ tau₃ psi D.beta1 D.beta2 D.beta3 D.h1 D.h2 D.h3
      D.a1 D.a2 D.a3 chi₁ chi₂ chi₃ alpha)
    (lambda : LocalQuasiCharData F) (hn : lambda.conductor ≤ 2 * e + a)
    (theta₁ : LocalQuasiCharData D.firstField) (theta₂ : LocalQuasiCharData D.secondField)
    (htheta₁ : theta₁.character = chi₁ * normQuasiChar F D.firstField lambda.character)
    (htheta₂ : theta₂.character = chi₂ * normQuasiChar F D.secondField lambda.character)
    (Theta : ContinuousQuasiChar K)
    (hc₁ : normQuasiChar D.firstField K theta₁.character = Theta)
    (hc₂ : normQuasiChar D.secondField K theta₂.character = Theta)
    (hprimitive : ¬ ∃ chi : ContinuousQuasiChar F, normQuasiChar F K chi = Theta)
    (hne : Ramification.intermediateNormRange D.firstField ≠
      Ramification.intermediateNormRange D.secondField)
    (psi₁ : LocalAddCharData D.firstField) (psi₂ : LocalAddCharData D.secondField)
    (hpsi₁ : psi₁.character = psi.character.compTrace)
    (hpsi₂ : psi₂.character = psi.character.compTrace) :
    LanglandsFirstMainLemma.localConstant D.firstField theta₁.character psi₁.character *
        LanglandsFirstMainLemma.localConstant F
          (Characters.intermediateNormCharacterProduct Nat.prime_two hG D.firstField O.first_degree)
          psi.character =
      LanglandsFirstMainLemma.localConstant D.secondField theta₂.character psi₂.character *
        LanglandsFirstMainLemma.localConstant F
          (Characters.intermediateNormCharacterProduct Nat.prime_two hG D.secondField O.second_degree)
          psi.character := by
  let I := D.firstField
  let J := D.secondField
  have hdataI := Basic.intermediateField_tower_compatible Nat.prime_two hG I O.first_degree
  have hdataJ := Basic.intermediateField_tower_compatible Nat.prime_two hG J O.second_degree
  have hIK := hdataI.2.2.2.2.2.2.2.2.2.2.1
  have hJK := hdataJ.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F I hdataI.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension I K hdataI.2.2.2.2.2.2.2.2.2.2.2.2
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F J hdataJ.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension J K hdataJ.2.2.2.2.2.2.2.2.2.2.2.2
  letI : Algebra.IsQuadraticExtension F I := ⟨O.first_degree⟩
  letI : Algebra.IsQuadraticExtension I K := ⟨hIK⟩
  letI : Algebra.IsQuadraticExtension F J := ⟨O.second_degree⟩
  letI : Algebra.IsQuadraticExtension J K := ⟨hJK⟩
  letI : IsKleinFour Gal(K/F) := by
    let eg := Classical.choice hG
    constructor
    · rw [Nat.card_congr eg.toEquiv]; simp
    · rw [Monoid.exponent_eq_of_mulEquiv eg]; simp [Monoid.exponent_prod]
  have htI : PrimeCyclicExtension.IsLowerBreak F I (2 * a - 1) := by
    simpa [actualLowerBreak, I] using ht₁
  have htJ : PrimeCyclicExtension.IsLowerBreak F J (2 * e) := by
    simpa [actualLowerBreak, J] using ht₂
  have htIK : PrimeCyclicExtension.IsLowerBreak I K (4 * e - 2 * a + 1) := by
    simpa [actualUpperBreak, I] using hU₁
  have htJK : PrimeCyclicExtension.IsLowerBreak J K (2 * a - 1) := by
    simpa [actualUpperBreak, J] using hU₂
  have hrI := comparison_residueDegrees I hres
  have hrJ := comparison_residueDegrees J hres
  have hramJK : ramificationIndex J K = 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree J K
    rw [hJK, hrJ.2, mul_one] at h
    exact h.symm
  have hn' : multiplicativeConductorExponent F lambda.character ≤ 2 * e + a := by
    rwa [multiplicativeConductorExponent_eq_of_isConductor F _ lambda.isConductor]
  have hm := (twist_conductors F I J ha hae htI htJ hrI.1 hrJ.1 O.first_degree
    O.second_degree chi₁ chi₂ hchi₁ hchi₂ lambda.character).1 hn'
  have hmI : theta₁.conductor = 4 * e + 1 := by
    rw [← multiplicativeConductorExponent_eq_of_isConductor I _ theta₁.isConductor, htheta₁]
    exact hm.1
  have hmJ : theta₂.conductor = 2 * e + 2 * a := by
    rw [← multiplicativeConductorExponent_eq_of_isConductor J _ theta₂.isConductor, htheta₂]
    exact hm.2.1
  obtain ⟨u, X, huorder, _Hu, _hX, HC⟩ := minimalOrigin hG D O hres htwo ha hae hb
    ht₁ ht₂ ht₃ hU₁ hU₂ g1 hg1 hg1R g2 hg2 hg2S q1 hq1 hq1S q2 hq2 hq2R q3 hq3 hq3SR
    tau₁ htau₁ tau₂ htau₂ tau₃ htau₃ psi alpha halpha chi₁ chi₂ chi₃ H lambda hn
    theta₁.character theta₂.character htheta₁ htheta₂
  let alpha' : Fˣ := alpha * (u : Fˣ)
  let Psi := scaleAddCharData F psi alpha'
  let PsiI := scaleAddCharData I psi₁ (Units.map (algebraMap F I).toMonoidHom alpha')
  let PsiJ := scaleAddCharData J psi₂ (Units.map (algebraMap F J).toMonoidHom alpha')
  let C : Kˣ := Units.mk0 (D.adjustedOrigin X) HC.origin_ne_zero
  have hPsi : Psi.conductor = -(2 * (e : ℤ) + 1) := by
    have hu : unitOrder F alpha' = -psi.conductor - (2 * (e : ℤ) + 1) :=
      WithTop.coe_injective ((ord_coe_eq_unitOrder F alpha').symm.trans (huorder.trans halpha))
    dsimp [Psi]
    rw [scaleAddCharData_conductor, hu]
    ring
  have hPsiI := comparison_scaled_trace_character F I psi psi₁ hpsi₁ alpha'
  have hPsiJ := comparison_scaled_trace_character F J psi psi₂ hpsi₂ alpha'
  have hJI : PsiI.conductor = -(4 * (e : ℤ) + 2 - 2 * (a : ℤ)) := by
    have h := comparison_trace_conductor F I htI O.first_degree hrI.1 Psi PsiI hPsiI
    rw [hPsi] at h
    omega
  have hJJ : PsiJ.conductor = -(2 * (e : ℤ) + 1) := by
    have h := comparison_trace_conductor F J htJ O.second_degree hrJ.1 Psi PsiJ hPsiJ
    rw [hPsi] at h
    omega
  have hconj := Characters.conjugacy Nat.prime_two hG I J O.first_degree O.second_degree hne
    theta₁.character theta₂.character Theta hc₁ hc₂ hprimitive
  obtain ⟨nuI, nuJ, hnuI0, hnuJ0, hnuI, hnuJ⟩ := hconj.2.2.2.2 rfl
  have hnI := comparison_normCharacter_unique F I htI O.first_degree hrI.1 nuI tau₁ hnuI0 htau₁
  have hnJ := comparison_normCharacter_unique F J htJ O.second_degree hrJ.1 nuJ tau₂ hnuJ0 htau₂
  subst nuI nuJ
  let omegaI := canonicalLocalQuasiCharData F
    (Characters.intermediateNormCharacterProduct Nat.prime_two hG I O.first_degree)
  let omegaJ := canonicalLocalQuasiCharData F
    (Characters.intermediateNormCharacterProduct Nat.prime_two hG J O.second_degree)
  have hwI : omegaI.conductor = 2 * a := by
    have h := comparison_normCharacter_conductor F I htI hrI.1 tau₁ htau₁ omegaI hnuI
    omega
  have hwJ : omegaJ.conductor = 2 * e + 1 :=
    comparison_normCharacter_conductor F J htJ hrJ.1 tau₂ htau₂ omegaJ hnuJ
  have hlargeI : 1 < theta₁.conductor := by omega
  have hlargeJ : 1 < theta₂.conductor := by omega
  have hlargeWI : 1 < omegaI.conductor := by omega
  have hlargeWJ : 1 < omegaJ.conductor := by omega
  have hC : ord K (C : K) = ((1 - 2 * (a : ℤ) : ℤ) : WithTop ℤ) := HC.origin_order
  have hSI : ord I (trace I K (C : K)) =
      ((2 * (e : ℤ) - 2 * (a : ℤ) + 1 : ℤ) : WithTop ℤ) := by
    have h : ord I (trace I K (C : K)) = (b : WithTop ℤ) := HC.first_trace_order
    rw [h]
    exact_mod_cast (show (b : ℤ) = 2 * (e : ℤ) - 2 * (a : ℤ) + 1 by omega)
  have hSJ : ord J (trace J K (C : K)) = 0 := HC.second_trace_order
  have hSI0 : trace I K (C : K) ≠ 0 := HC.first_trace_ne_zero
  have hSJ0 : trace J K (C : K) ≠ 0 := HC.second_trace_ne_zero
  have hsI : IsOrdinaryStationaryCoefficient I theta₁ PsiI (normUnits I K C) hlargeI := by
    apply comparisonStationary_of_coreChart I theta₁ PsiI _ hlargeI
      (show 0 < 2 * e + 1 by omega) (by omega)
    · rw [coe_normUnits, ord_norm, hrI.2, one_nsmul, hC, hJI, hmI]
      congr 1
      push_cast
      ring
    · intro v
      rw [hPsiI]
      exact HC.first_formula v
  have hsJ : IsOrdinaryStationaryCoefficient J theta₂ PsiJ (normUnits J K C) hlargeJ := by
    apply comparisonStationary_of_coreChart J theta₂ PsiJ _ hlargeJ
      (show 0 < e + a by omega) (by omega)
    · rw [coe_normUnits, ord_norm, hrJ.2, one_nsmul, hC, hJJ, hmJ]
      congr 1
      push_cast
      ring
    · intro v
      rw [hPsiJ]
      exact HC.second_formula v
  have hsWI : IsOrdinaryStationaryCoefficient F omegaI Psi
      (commonOriginLowerCoefficient I C hSI0) hlargeWI := by
    apply comparisonStationary_of_lowerChart F omegaI Psi _ hlargeWI
      (show 0 < a by omega) (by omega)
    · change ord F (norm F I (trace I K (C : K))) = _
      rw [ord_norm, hrI.1, one_nsmul, hSI, hPsi, hwI]
      congr 1
      push_cast
      ring
    · intro z hz
      rw [show omegaI.character = tau₁.1 from hnuI]
      exact HC.first_lower (by omega) z hz
  have hsWJ : IsOrdinaryStationaryCoefficient F omegaJ Psi
      (commonOriginLowerCoefficient J C hSJ0) hlargeWJ := by
    apply comparisonStationary_of_lowerChart F omegaJ Psi _ hlargeWJ
      (show 0 < e + 1 by omega) (by omega)
    · change ord F (norm F J (trace J K (C : K))) = _
      rw [ord_norm, hrJ.1, one_nsmul, hSJ, hPsi, hwJ]
      simp
    · intro z hz
      rw [show omegaJ.character = tau₂.1 from hnuJ]
      exact HC.second_lower z hz
  have hresidual := comparisonResidualProducts I J ha hae hIK hJK hrI.2 hrJ.2 hrI.1 hrJ.1
    hramJK htI htJ htIK htJK theta₁ theta₂ omegaI omegaJ tau₁ tau₂ hnuI hnuJ Theta hc₁ hc₂
    psi psi₁ psi₂ hpsi₁ hpsi₂ alpha' C hC hSI hSJ hSI0 hSJ0 hmI hmJ hwI hwJ hsI hsJ hsWI hsWJ
  exact (commonOrigin hG I J O.first_degree O.second_degree hne theta₁ theta₂ Theta
    hc₁ hc₂ hprimitive psi psi₁ psi₂ hpsi₁ hpsi₂ alpha' C hSI0 hSJ0
    hlargeI hlargeJ hlargeWI hlargeWJ hsI hsJ hsWI hsWJ).2.2.2 hresidual

end Diagram

end
end LanglandsSecondMainLemma.Dyadic.Maximal
