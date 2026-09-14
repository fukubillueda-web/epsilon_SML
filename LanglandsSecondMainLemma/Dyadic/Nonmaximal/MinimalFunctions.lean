import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.MinimalOrigin
import LanglandsSecondMainLemma.Stationary.CommonFunction

/-!
# Full critical functions at a nonmaximal minimal origin

Paper `D:NM:actual-functions`, with the full stationary formulas of
`D:NM:minimal-origin`. All increments below are literal norm quotients.
The lower trace quotients stay nonzero and their complete stationary
factors cancel before any residual sum is taken.
-/

namespace LanglandsSecondMainLemma.Dyadic.Nonmaximal

noncomputable section

open LanglandsFirstMainLemma
open private trace_mem_of_depth from
  LanglandsSecondMainLemma.Dyadic.Nonmaximal.MinimalOrigin

set_option maxHeartbeats 1000000

section Quadratic

variable (E M : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra E M] [ValuativeExtension E M] [Module.Finite E M]
  [Algebra.IsQuadraticExtension E M] [PrimeCyclicExtension E M]

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [ValuativeExtension E M] [PrimeCyclicExtension E M] in
private theorem norm_one_add (v : M) :
    norm E M (1 + v) = 1 + trace E M v + norm E M v := by
  rw [norm_one_add_eq_sum_elementarySymmetric,
    Algebra.IsQuadraticExtension.finrank_eq_two E M]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    elementarySymmetric_zero, elementarySymmetric_one]
  rw [← Algebra.IsQuadraticExtension.finrank_eq_two E M, elementarySymmetric_finrank]

/-- The quadratic norm increment retains its trace term at the boundary. -/
private theorem norm_increment_mem {t : ℕ} (htpos : 1 ≤ t)
    (ht : PrimeCyclicExtension.IsLowerBreak E M (2 * t - 1))
    (hres : residueDegree E M = 1) {j b : ℤ}
    (htrace : b ≤ (j + 2 * t) / 2) (hnorm : b ≤ j)
    {v : M} (hv : v ∈ lattice M j) :
    norm E M (1 + v) - 1 ∈ lattice E b := by
  have hn : norm E M v ∈ lattice E j := by
    simpa only [mem_lattice, ord_norm, hres, one_nsmul] using hv
  rw [norm_one_add]
  convert add_mem_lattice E (trace_mem_of_depth E M htpos ht hres htrace hv)
    (lattice_antitone E hnorm hn) using 1; ring

/-- A source change in the next ideal changes the actual norm increment
in the next target ideal. This proves that the graded norm coordinate is
independent of a chosen lift, including at the critical norm boundary. -/
private theorem norm_increment_congruent {t n b : ℕ}
    (htpos : 1 ≤ t) (hn : 0 < n)
    (ht : PrimeCyclicExtension.IsLowerBreak E M (2 * t - 1))
    (hres : residueDegree E M = 1)
    (htrace : (b : ℤ) + 1 ≤ ((n : ℤ) + 1 + 2 * t) / 2) (hnorm : b ≤ n)
    (v v' : lattice M (n : ℤ))
    (hvv' : (v : M) - (v' : M) ∈ lattice M ((n : ℤ) + 1)) :
    norm E M (1 + (v : M)) - norm E M (1 + (v' : M)) ∈ lattice E ((b : ℤ) + 1) := by
  have hv' : ord M (1 + (v' : M)) = 0 := by
    have h := (mem_unitFiltration_zero M (positiveUnitOfLattice M hn v')).mp
      (unitFiltration_antitone M (Nat.zero_le n) (positiveUnitOfLattice M hn v').property)
    simpa only [coe_positiveUnitOfLattice] using h
  have hv'0 : 1 + (v' : M) ≠ 0 :=
    (ord_ne_top_iff M).mp (by rw [hv']; exact WithTop.zero_ne_top)
  have hD : ((v : M) - (v' : M)) / (1 + (v' : M)) ∈ lattice M ((n : ℤ) + 1) :=
    (div_mem_lattice_iff M _ _ 0 ((n : ℤ) + 1) (by simpa using hv')).mpr
      (by simpa using hvv')
  have hN := norm_increment_mem E M htpos ht hres htrace
    (show (b : ℤ) + 1 ≤ (n : ℤ) + 1 by omega) hD
  have hnormUnit : norm E M (1 + (v' : M)) ∈ lattice E 0 := by
    rw [mem_lattice, ord_norm, hv', nsmul_zero]
    rfl
  have heq : 1 + (v : M) =
      (1 + (v' : M)) * (1 + ((v : M) - (v' : M)) / (1 + (v' : M))) := by
    field_simp; ring
  have hfactor : norm E M (1 + (v : M)) - norm E M (1 + (v' : M)) =
      norm E M (1 + (v' : M)) *
        (norm E M (1 + ((v : M) - (v' : M)) / (1 + (v' : M))) - 1) := by
    rw [heq, map_mul]
    ring
  rw [hfactor]
  simpa only [zero_add] using mul_mem_lattice E hnormUnit hN

end Quadratic

section Residues

variable (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- The manuscript's source `π^n v`, for any integral representative `v`.
In particular `v = teichmuller E x` constructs the source for every residue
class without any norm-surjectivity hypothesis. -/
def minimalSourceLift (π : Eˣ) (hπ : ord E (π : E) = 1) (n : ℕ)
    (v : ringOfIntegers E) : lattice E (n : ℤ) :=
  ⟨(π : E) ^ n * (v : E), by
    have hpow : (π : E) ^ n ∈ lattice E (n : ℤ) := by
      rw [mem_lattice, ord_pow, hπ]
      norm_cast
      simp
    simpa only [add_zero] using mul_mem_lattice E hpow
      ((mem_lattice_zero_iff E).mpr v.property)⟩

/-- Two representatives of the same source residue differ in the next
source ideal, the exact input of `minimalGradedNorm_lift_independent`. -/
theorem minimalSourceLift_sub_mem (π : Eˣ) (hπ : ord E (π : E) = 1) (n : ℕ)
    (v v' : ringOfIntegers E) (hvv' : residueMap E v = residueMap E v') :
    (minimalSourceLift E π hπ n v : E) - (minimalSourceLift E π hπ n v' : E) ∈
      lattice E ((n : ℤ) + 1) := by
  change (π : E) ^ n * (v : E) - (π : E) ^ n * (v' : E) ∈ _
  rw [← mul_sub]
  apply mul_mem_lattice E _ ((residueMap_eq_residueMap_iff E v v').mp hvv')
  rw [mem_lattice, ord_pow, hπ]
  norm_cast
  simp

/-- The actual coordinate of an increment in its one-dimensional graded
ideal. This definition takes no square root or preimage under a norm map. -/
def minimalCriticalCoordinate {b : ℕ} (δ : Eˣ)
    (hδ : ord E (δ : E) = ((b : ℤ) : WithTop ℤ))
    (v : lattice E (b : ℤ)) : ResidueField E :=
  reduce E ((v : E) / (δ : E))
    ((div_mem_lattice_iff E _ _ (b : ℤ) 0 hδ).mpr (by simp))

/-- The target graded coordinate is unchanged on a complete next-ideal
coset, independently of the integrality proofs in its definition. -/
theorem minimalCriticalCoordinate_eq_of_congruent {b : ℕ} (δ : Eˣ)
    (hδ : ord E (δ : E) = ((b : ℤ) : WithTop ℤ))
    (v v' : lattice E (b : ℤ))
    (hvv' : (v : E) - (v' : E) ∈ lattice E ((b : ℤ) + 1)) :
    minimalCriticalCoordinate E δ hδ v = minimalCriticalCoordinate E δ hδ v' := by
  apply (reduce_eq_reduce_iff E _ _).mpr
  apply (congruentAtDepth_iff_sub_mem_lattice E _ _ _).mpr
  rw [← sub_div]
  exact (div_mem_lattice_iff E _ _ (b : ℤ) 1 hδ).mpr (by simpa [add_comm] using hvv')

/-- Transport to the actual residual function, including its affine
part, using FML's proved terminal-coset invariance. -/
private theorem criticalValue_eq_residual
    (θ : LocalQuasiCharData E) (Ψ : LocalAddCharData E) (Z : Eˣ)
    {b : ℕ} (hb : 0 < b) (hm : θ.conductor = 2 * b + 1)
    (hZ : ord E (Z : E) = ((-Ψ.conductor - (θ.conductor : ℤ) : ℤ) : WithTop ℤ))
    (hs : Stationary.IsNormalizedStationaryCoefficientAtDepth E θ Ψ Z (b + 1) (by omega))
    (δ : Eˣ) (hδ : ord E (δ : E) = ((b : ℤ) : WithTop ℤ))
    (v : lattice E (b : ℤ)) :
    Stationary.normalizedCriticalValue E θ Ψ Z b hb v =
      Stationary.normalizedResidualFunction E θ Ψ 1 Z b hm (by omega) δ hδ
        (minimalCriticalCoordinate E δ hδ v) := by
  have hvδ : (v : E) / (δ : E) ∈ lattice E 0 :=
    (div_mem_lattice_iff E _ _ (b : ℤ) 0 hδ).mpr (by simp)
  let z : ringOfIntegers E := ⟨(v : E) / (δ : E), (mem_lattice_zero_iff E).mp hvδ⟩
  let w := teichmuller E (residueMap E z)
  let v' : lattice E (b : ℤ) := ⟨(δ : E) * (w : E), by
    simpa only [add_zero] using mul_mem_lattice E
      (show (δ : E) ∈ lattice E (b : ℤ) by rw [mem_lattice, hδ])
      ((mem_lattice_zero_iff E).mpr w.property)⟩
  have hzw : (z : E) - (w : E) ∈ lattice E 1 :=
    (residueMap_eq_residueMap_iff E z w).mp (by simp [w])
  have hvv' : CongruentAtDepth ((b + 1 : ℕ) : ℤ) (v : E) (v' : E) := by
    apply (congruentAtDepth_iff_sub_mem_lattice E _ _ _).mpr
    have heq : (v : E) - (v' : E) = (δ : E) * ((z : E) - (w : E)) := by
      dsimp [v', z]
      field_simp
    rw [heq]
    exact mul_mem_lattice E (by rw [mem_lattice, hδ]) hzw
  have hstat : Stationary.IsNormalizedStationaryCoefficientAtDepth E θ
      (scaleAddCharData E Ψ 1) Z (b + 1) (by omega) := by
    simpa only [Stationary.IsNormalizedStationaryCoefficientAtDepth,
      scaleAddCharData_character_apply, Units.val_one, one_mul] using hs
  have horder : ord E (Z : E) =
      ((-(scaleAddCharData E Ψ 1).conductor - (θ.conductor : ℤ) : ℤ) : WithTop ℤ) := by
    have h1 : unitOrder E 1 = 0 := by
      unfold unitOrder
      rw [Units.val_one, ord_one]
      rfl
    simpa only [scaleAddCharData_conductor, h1, add_zero] using hZ
  have hval := Stationary.normalizedCriticalValue_odd_eq_of_congruent E θ Ψ 1 Z b hm
    (by omega) horder hstat v v' hvv'
  have hval' : Stationary.normalizedCriticalValue E θ Ψ Z b hb v =
      Stationary.normalizedCriticalValue E θ Ψ Z b hb v' := by
    simpa only [Stationary.normalizedCriticalValue, scaleAddCharData_character_apply,
      Units.val_one, one_mul] using hval
  rw [hval']
  have hunit : (lamprechtHasseUnit E θ b hm (by omega) δ hδ (w : E)
      ((mem_lattice_zero_iff E).mpr w.property) : Eˣ) =
        positiveUnitOfLattice E hb v' := by
    apply Units.ext
    rw [lamprechtHasseUnit_coe, coe_positiveUnitOfLattice]
  change Stationary.normalizedCriticalValue E θ Ψ Z b hb v' =
    Stationary.normalizedResidualFunction E θ Ψ 1 Z b hm (by omega) δ hδ (residueMap E z)
  dsimp only [Stationary.normalizedCriticalValue, Stationary.normalizedResidualFunction]
  rw [hunit]
  simp only [scaleAddCharData_character_apply, Units.val_one, one_mul, v', w, mul_assoc]

end Residues

section ActualFields

variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

attribute [local instance] Basic.intermediateFieldValuativeRel
  Basic.intermediateFieldTopology Basic.intermediateField_localField
  Basic.intermediateField_lowerValuativeExtension Basic.intermediateField_upperValuativeExtension

/-- The same perturbed top element is used on every side. The full source
ideal includes `π^(2r-1) v` for every integral `v`, including zero. -/
def minimalFunctionPoint (C : Kˣ) (n : ℕ) (hn : 0 < n)
    (v : lattice K (n : ℤ)) : Kˣ := C * positiveUnitOfLattice K hn v

@[simp] theorem minimalFunctionPoint_coe (C : Kˣ) (n : ℕ) (hn : 0 < n)
    (v : lattice K (n : ℤ)) :
    (minimalFunctionPoint C n hn v : K) = (C : K) * (1 + (v : K)) := rfl

variable (L : IntermediateField F K)

/-- All actual arguments of the full upper and lower critical functions.
`minimalFunctionLift` constructs these data from the origin and the trace
ledger; the record is never an additional existence assumption. -/
structure MinimalFunctionLift (q b r : ℕ) (w : ℤ) (C C' : Kˣ)
    (hC : trace L K (C : K) ≠ 0) where
  trace_change : trace L K ((C : K) * (((C' / C : Kˣ) : K) - 1)) ∈
    lattice L (w + r)
  trace_order : ord L (trace L K (C' : K)) = (w : WithTop ℤ)
  trace_ne_zero : trace L K (C' : K) ≠ 0
  relative_trace : lattice L (r : ℤ)
  relative_trace_eq : 1 + (relative_trace : L) =
    trace L K (C' : K) / trace L K (C : K)
  upper : lattice L (b : ℤ)
  upper_eq : 1 + (upper : L) = ((normUnits L K C' / normUnits L K C : Lˣ) : L)
  lower : lattice F (q : ℤ)
  lower_eq : 1 + (lower : F) =
    ((Stationary.commonOriginLowerCoefficient L C' trace_ne_zero /
      Stationary.commonOriginLowerCoefficient L C hC : Fˣ) : F)

omit [IsGalois F K] in
/-- The upper coordinate is the literal norm increment of the source
unit; it is independent of the common origin and of the trace witnesses. -/
theorem MinimalFunctionLift.upper_value
    {q b r n : ℕ} {w : ℤ} {C : Kˣ} {hC : trace L K (C : K) ≠ 0}
    (hn : 0 < n) (v : lattice K (n : ℤ))
    (V : MinimalFunctionLift L q b r w C (minimalFunctionPoint C n hn v) hC) :
    (V.upper : L) = norm L K (1 + (v : K)) - 1 := by
  have h := V.upper_eq
  rw [← map_div, coe_normUnits] at h
  simp only [minimalFunctionPoint, mul_div_cancel_left, coe_positiveUnitOfLattice] at h
  exact eq_sub_of_add_eq' h

variable [Algebra.IsQuadraticExtension F L] [Algebra.IsQuadraticExtension L K]
  [PrimeCyclicExtension F L] [PrimeCyclicExtension L K]

omit [Algebra.IsQuadraticExtension F L] [PrimeCyclicExtension F L] in
/-- Descent of the actual upper norm coordinate through the full source
residue quotient. The numerical successor bound holds on both sides of
`D:NM:actual-functions`, also when their breaks are equal. -/
theorem minimalGradedNorm_lift_independent
    {q b r t n : ℕ} {w : ℤ} {C : Kˣ} {hC : trace L K (C : K) ≠ 0}
    (htpos : 1 ≤ t) (hn : 0 < n)
    (ht : PrimeCyclicExtension.IsLowerBreak L K (2 * t - 1))
    (hres : residueDegree L K = 1)
    (htrace : (b : ℤ) + 1 ≤ ((n : ℤ) + 1 + 2 * t) / 2) (hnorm : b ≤ n)
    (δ : Lˣ) (hδ : ord L (δ : L) = ((b : ℤ) : WithTop ℤ))
    (v v' : lattice K (n : ℤ))
    (hvv' : (v : K) - (v' : K) ∈ lattice K ((n : ℤ) + 1))
    (V : MinimalFunctionLift L q b r w C (minimalFunctionPoint C n hn v) hC)
    (V' : MinimalFunctionLift L q b r w C (minimalFunctionPoint C n hn v') hC) :
    minimalCriticalCoordinate L δ hδ V.upper = minimalCriticalCoordinate L δ hδ V'.upper := by
  apply minimalCriticalCoordinate_eq_of_congruent
  rw [V.upper_value L hn v, V'.upper_value L hn v', sub_sub_sub_cancel_right]
  exact norm_increment_congruent L K htpos hn ht hres htrace hnorm v v' hvv'

/-- Integer inequalities are kept separate from the exact trace and norm
calculation so the two unequal sides and the equal-break third side use
one proof. In the application the relative trace depth is `r`. -/
def minimalFunctionLift
    (q b r t n : ℕ) (c w : ℤ) (hq : 1 ≤ q) (hr : 0 < r) (hn : 0 < n)
    (htpos : 1 ≤ t) (hqr : q ≤ r)
    (htF : PrimeCyclicExtension.IsLowerBreak F L (2 * q - 1))
    (htK : PrimeCyclicExtension.IsLowerBreak L K (2 * t - 1))
    (hresF : residueDegree F L = 1) (hresK : residueDegree L K = 1)
    (hupperTrace : (b : ℤ) ≤ ((n : ℤ) + 2 * t) / 2) (hupperNorm : b ≤ n)
    (hchange : w + r ≤ (c + n + 2 * t) / 2)
    (C : Kˣ) (hC : ord K (C : K) = (c : WithTop ℤ))
    (hS : ord L (trace L K (C : K)) = (w : WithTop ℤ))
    (hS0 : trace L K (C : K) ≠ 0) (v : lattice K (n : ℤ)) :
    MinimalFunctionLift L q b r w C (minimalFunctionPoint C n hn v) hS0 := by
  let C' := minimalFunctionPoint C n hn v
  have hC' : (C' : K) = (C : K) * (1 + (v : K)) := rfl
  have hratio : ((C' / C : Kˣ) : K) = 1 + (v : K) := by
    simp [C', minimalFunctionPoint, coe_positiveUnitOfLattice]
  have hCv : (C : K) * (v : K) ∈ lattice K (c + n) :=
    mul_mem_lattice K (by rw [mem_lattice, hC]) v.property
  have hD := trace_mem_of_depth L K htpos htK hresK hchange hCv
  have hSC' : trace L K (C' : K) =
      trace L K (C : K) + trace L K ((C : K) * (v : K)) := by
    rw [hC', mul_add, mul_one, map_add]
  have hlt : ord L (trace L K (C : K)) <
      ord L (trace L K ((C : K) * (v : K))) := by
    rw [hS]
    exact (WithTop.coe_lt_coe.mpr (by omega : w < w + r)).trans_le hD
  have hSCord : ord L (trace L K (C' : K)) = (w : WithTop ℤ) := by
    rw [hSC', ord_add_eq_min L (ne_of_lt hlt), min_eq_left hlt.le, hS]
  have hSC0 : trace L K (C' : K) ≠ 0 :=
    (ord_ne_top_iff L).mp (by rw [hSCord]; exact WithTop.coe_ne_top)
  let D : lattice L (r : ℤ) :=
    ⟨trace L K ((C : K) * (v : K)) / trace L K (C : K),
      (div_mem_lattice_iff L _ _ w (r : ℤ) hS).mpr (by simpa [add_comm] using hD)⟩
  have hDeq : 1 + (D : L) = trace L K (C' : K) / trace L K (C : K) := by
    rw [hSC', add_div, div_self hS0]
  let z : lattice L (b : ℤ) := ⟨norm L K (1 + (v : K)) - 1,
    norm_increment_mem L K htpos htK hresK hupperTrace (by exact_mod_cast hupperNorm)
      v.property⟩
  have hzeq : 1 + (z : L) = ((normUnits L K C' / normUnits L K C : Lˣ) : L) := by
    rw [← map_div, coe_normUnits, hratio]
    dsimp [z]
    ring
  let u : lattice F (q : ℤ) := ⟨norm F L (1 + (D : L)) - 1,
    norm_increment_mem F L hq htF hresF (by omega) (by exact_mod_cast hqr) D.property⟩
  have hueq : 1 + (u : F) =
      ((Stationary.commonOriginLowerCoefficient L C' hSC0 /
        Stationary.commonOriginLowerCoefficient L C hS0 : Fˣ) : F) := by
    change 1 + (norm F L (1 + (D : L)) - 1) =
      ((normUnits F L (Units.mk0 _ hSC0) / normUnits F L (Units.mk0 _ hS0) : Fˣ) : F)
    rw [← map_div, coe_normUnits, Units.val_div_eq_div_val, Units.val_mk0,
      Units.val_mk0, ← hDeq]
    ring
  refine ⟨?_, hSCord, hSC0, D, hDeq, z, hzeq, u, hueq⟩
  change trace L K ((C : K) * (((C' / C : Kˣ) : K) - 1)) ∈ _
  rw [hratio, add_sub_cancel_left]
  exact hD

omit [Algebra.IsQuadraticExtension L K]
  [PrimeCyclicExtension F L] [PrimeCyclicExtension L K] in
/-- The lower argument is still a literal norm of a nonzero trace
quotient. Its stationary additive phase is also one, on the whole lower
ideal. Thus no lower factor is silently discarded. -/
theorem MinimalFunctionLift.lower_values
    {q b r : ℕ} {w : ℤ} {C C' : Kˣ} {hC : trace L K (C : K) ≠ 0}
    (V : MinimalFunctionLift L q b r w C C' hC)
    (ω : NormCharacter F L) (Ψ : ContinuousAddChar F)
    (hlower : ∀ v ∈ lattice F (q : ℤ), ∀ B : Fˣ, (B : F) = 1 - v →
      ω.1 B = Ψ (norm F L (trace L K (C : K)) * v)) :
    let W := Stationary.commonOriginLowerCoefficient L C hC
    let W' := Stationary.commonOriginLowerCoefficient L C' V.trace_ne_zero
    ω.1 (W' / W) = 1 ∧ Ψ (-(W : F) * (V.lower : F)) = 1 := by
  dsimp only
  have hn : ω.1 (Stationary.commonOriginLowerCoefficient L C' V.trace_ne_zero /
      Stationary.commonOriginLowerCoefficient L C hC) = 1 := by
    apply ω.eq_one_on_normRange F L
    exact ⟨Units.mk0 (trace L K (C' : K)) V.trace_ne_zero /
      Units.mk0 (trace L K (C : K)) hC, map_div _ _ _⟩
  refine ⟨hn, ?_⟩
  have h := hlower (-(V.lower : F)) (neg_mem_lattice F V.lower.property)
    (Stationary.commonOriginLowerCoefficient L C' V.trace_ne_zero /
      Stationary.commonOriginLowerCoefficient L C hC)
    (by simpa only [sub_neg_eq_add] using V.lower_eq.symm)
  rw [hn] at h
  change Ψ (-norm F L (trace L K (C : K)) * (V.lower : F)) = 1
  simpa only [mul_neg, neg_mul] using h.symm

omit [PrimeCyclicExtension F L] [PrimeCyclicExtension L K] in
/-- The complete critical value on one side, after proving both lower
values equal one. Compatibility supplies the common multiplicative value,
and the biquadratic identity supplies its full additive exponent. -/
theorem MinimalFunctionLift.critical_value [IsKleinFour Gal(K/F)]
    {q b r : ℕ} {w : ℤ} {C C' : Kˣ} {hC : trace L K (C : K) ≠ 0}
    (hq : 0 < q) (hb : 0 < b) (V : MinimalFunctionLift L q b r w C C' hC)
    (θ : LocalQuasiCharData L) (ω : NormCharacter F L)
    (Ψ : LocalAddCharData F) (ΨL : LocalAddCharData L)
    (hΨL : ΨL.character = Ψ.character.compTrace)
    (hlower : ∀ v ∈ lattice F (q : ℤ), ∀ B : Fˣ, (B : F) = 1 - v →
      ω.1 B = Ψ.character (norm F L (trace L K (C : K)) * v))
    (Θ : ContinuousQuasiChar K) (hc : normQuasiChar L K θ.character = Θ) :
    Stationary.normalizedCriticalValue L θ ΨL (normUnits L K C) b hb V.upper =
      (Θ (C' / C) : ℂ)⁻¹ *
        (Ψ.character (-elementarySymmetric F K 2 (C' : K) +
          elementarySymmetric F K 2 (C : K)) : ℂ) := by
  let ωD := canonicalLocalQuasiCharData F ω.1
  have hp := Stationary.commonFunctionProduct_eq L θ ωD ω rfl Θ hc Ψ ΨL hΨL
    1 C C' hC V.trace_ne_zero
  have hf := Stationary.commonFunctionProduct_eq_criticalValues L θ ωD Ψ ΨL
    1 C C' hC V.trace_ne_zero b q hb hq V.upper V.lower V.upper_eq V.lower_eq
  have hu : positiveUnitOfLattice F hq V.lower =
      Stationary.commonOriginLowerCoefficient L C' V.trace_ne_zero /
        Stationary.commonOriginLowerCoefficient L C hC := Units.ext V.lower_eq
  obtain ⟨hn, ha⟩ := V.lower_values L ω Ψ.character hlower
  have hl : Stationary.normalizedCriticalValue F ωD Ψ
      (Stationary.commonOriginLowerCoefficient L C hC) q hq V.lower = 1 := by
    dsimp only [Stationary.normalizedCriticalValue]
    rw [hu, ha]
    change (1 : ℂˣ).val * (ω.1 _ : ℂ)⁻¹ = 1
    rw [hn]
    simp
  have h := hf.symm.trans hp
  have h' : Stationary.normalizedCriticalValue L θ ΨL (normUnits L K C) b hb V.upper *
        Stationary.normalizedCriticalValue F ωD Ψ
          (Stationary.commonOriginLowerCoefficient L C hC) q hq V.lower =
      (Θ (C' / C) : ℂ)⁻¹ *
        (Ψ.character (-elementarySymmetric F K 2 (C' : K) +
          elementarySymmetric F K 2 (C : K)) : ℂ) := by
    simpa only [Stationary.normalizedCriticalValue, map_one,
      scaleAddCharData_character_apply, Units.val_one, one_mul] using h
  rwa [hl, mul_one] at h'

/-- The first side's precise trace-change depth is `3r-2a`, and its
relative trace change has depth `r`. Its upper critical depth is `2r-1`. -/
def minimalFirstLift
    {a r : ℕ} (ha : 1 ≤ a) (har : a ≤ r)
    (htF : PrimeCyclicExtension.IsLowerBreak F L (2 * a - 1))
    (htK : PrimeCyclicExtension.IsLowerBreak L K (4 * r - 2 * a - 1))
    (hresF : residueDegree F L = 1) (hresK : residueDegree L K = 1)
    (C : Kˣ) (hC : ord K (C : K) = ((1 - 2 * (a : ℤ) : ℤ) : WithTop ℤ))
    (hS : ord L (trace L K (C : K)) = ((2 * ((r : ℤ) - a) : ℤ) : WithTop ℤ))
    (hS0 : trace L K (C : K) ≠ 0) (v : lattice K ((2 * r - 1 : ℕ) : ℤ)) :
    MinimalFunctionLift L a (2 * r - 1) r (2 * ((r : ℤ) - a)) C
      (minimalFunctionPoint C (2 * r - 1) (by omega) v) hS0 := by
  apply minimalFunctionLift L a (2 * r - 1) r (2 * r - a) (2 * r - 1)
    (1 - 2 * (a : ℤ)) (2 * ((r : ℤ) - a)) ha (by omega) (by omega) (by omega)
    har htF _ hresF hresK (by omega) le_rfl (by omega) C hC hS hS0 v
  convert htK using 1; omega

/-- The second side's trace change and relative trace change have depth
`r`; its full upper critical depth is `a+r-1`. This also applies to the
third field when `a=r`, using its constructed third minimal-origin side. -/
def minimalOtherLift
    {a r : ℕ} (ha : 1 ≤ a) (har : a ≤ r)
    (htF : PrimeCyclicExtension.IsLowerBreak F L (2 * r - 1))
    (htK : PrimeCyclicExtension.IsLowerBreak L K (2 * a - 1))
    (hresF : residueDegree F L = 1) (hresK : residueDegree L K = 1)
    (C : Kˣ) (hC : ord K (C : K) = ((1 - 2 * (a : ℤ) : ℤ) : WithTop ℤ))
    (hS : ord L (trace L K (C : K)) = 0)
    (hS0 : trace L K (C : K) ≠ 0) (v : lattice K ((2 * r - 1 : ℕ) : ℤ)) :
    MinimalFunctionLift L r (a + r - 1) r 0 C
      (minimalFunctionPoint C (2 * r - 1) (by omega) v) hS0 :=
  minimalFunctionLift L r (a + r - 1) r a (2 * r - 1) (1 - 2 * (a : ℤ)) 0
    (by omega) (by omega) (by omega) ha le_rfl htF htK hresF hresK
    (by omega) (by omega) (by omega) C hC (by simpa using hS) hS0 v

omit [Algebra.IsQuadraticExtension L K] [PrimeCyclicExtension L K] in
/-- The full upper chart of `minimalOrigin` is precisely the stationary
chart needed for terminal invariance. Its coefficient order follows from
the actual norm and FML's trace conductor formula. -/
private theorem minimal_stationary
    {q b : ℕ} (hq : 1 ≤ q) (hb : 0 < b)
    (htF : PrimeCyclicExtension.IsLowerBreak F L (2 * q - 1))
    (hresF : residueDegree F L = 1) (hresK : residueDegree L K = 1)
    (θ : LocalQuasiCharData L)
    (Ψ : LocalAddCharData F) (ΨL : LocalAddCharData L)
    (hΨL : ΨL.character = Ψ.character.compTrace)
    (C : Kˣ) (hC : ord K (C : K) =
      ((-(2 * Ψ.conductor + 2 * q) - (θ.conductor : ℤ) : ℤ) : WithTop ℤ))
    (hu : ∀ v ∈ lattice L ((b + 1 : ℕ) : ℤ), ∀ B : Lˣ, (B : L) = 1 - v →
      θ.character B = tracePullbackAddChar F L Ψ.character (norm L K (C : K) * v)) :
    ord L ((normUnits L K C : Lˣ) : L) =
      ((-ΨL.conductor - (θ.conductor : ℤ) : ℤ) : WithTop ℤ) ∧
    Stationary.IsNormalizedStationaryCoefficientAtDepth L θ ΨL (normUnits L K C)
      (b + 1) (by omega) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F L hresF
  have hc := Ψ.conductor_compTrace_eq_cyclicPrime F L htF hresF pi hpi hgen ΨL hΨL
  rw [Algebra.IsQuadraticExtension.finrank_eq_two F L] at hc
  have hc' : ΨL.conductor = 2 * Ψ.conductor + 2 * q := by
    simp only [Nat.cast_ofNat, Nat.reduceSub, one_mul] at hc
    omega
  refine ⟨?_, ?_⟩
  · rw [coe_normUnits, ord_norm, hresK, one_nsmul, hC, hc']
  · intro v
    have h := hu v v.property (positiveUnitOfLattice L (by omega) (-v))
      (by simp only [coe_positiveUnitOfLattice, Submodule.coe_neg, sub_eq_add_neg])
    rw [hΨL]
    exact h

end ActualFields

section Comparison

variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  [IsKleinFour Gal(K/F)]
  (L₁ L₂ : IntermediateField F K)

attribute [local instance] Basic.intermediateFieldValuativeRel
  Basic.intermediateFieldTopology Basic.intermediateField_localField
  Basic.intermediateField_lowerValuativeExtension Basic.intermediateField_upperValuativeExtension

variable [Algebra.IsQuadraticExtension F L₁] [Algebra.IsQuadraticExtension L₁ K]
  [Algebra.IsQuadraticExtension F L₂] [Algebra.IsQuadraticExtension L₂ K]
  [PrimeCyclicExtension F L₁] [PrimeCyclicExtension L₁ K]
  [PrimeCyclicExtension F L₂] [PrimeCyclicExtension L₂ K]

/-- **Paper `D:NM:actual-functions`.** At every point of the full critical
source ideal, the two actual upper residual functions have the common value
`Θ(C'/C)⁻¹ Ψ(-E₂(C')+E₂(C))`. Their arguments are the actual graded norm
coordinates, with arbitrary scales of the specified exact orders.

The data `H₁,H₂` are the outputs of the proved `minimalOrigin` constructor;
the normalization and conductor equations are supplied by `lowerCharacters`
and `twist`. All lifts, trace depths, nonvanishing, lower norm arguments and
their stationary cancellation are constructed here. No common-function
identity, residual sign, or surjectivity of a critical norm is a hypothesis.

Taking `v = π^(2r-1) v₀` gives the paper's perturbation. Taking Teichmüller
lifts of `v₀` gives its equality on residue classes. When `a=r`, the second
slot can be the third field with the third side of the same `minimalOrigin`.
-/
theorem dyadicNonmaximal_commonFunctions
    {a r : ℕ} (ha : 1 ≤ a) (har : a ≤ r)
    (htF₁ : PrimeCyclicExtension.IsLowerBreak F L₁ (2 * a - 1))
    (htF₂ : PrimeCyclicExtension.IsLowerBreak F L₂ (2 * r - 1))
    (htK₁ : PrimeCyclicExtension.IsLowerBreak L₁ K (4 * r - 2 * a - 1))
    (htK₂ : PrimeCyclicExtension.IsLowerBreak L₂ K (2 * a - 1))
    (hresF₁ : residueDegree F L₁ = 1) (hresF₂ : residueDegree F L₂ = 1)
    (hresK₁ : residueDegree L₁ K = 1) (hresK₂ : residueDegree L₂ K = 1)
    (θ₁ : LocalQuasiCharData L₁) (θ₂ : LocalQuasiCharData L₂)
    (hm₁ : θ₁.conductor = 4 * r - 1) (hm₂ : θ₂.conductor = 2 * a + 2 * r - 1)
    (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂)
    (Ψ : LocalAddCharData F) (hΨ : Ψ.conductor = -2 * (r : ℤ))
    (Ψ₁ : LocalAddCharData L₁) (Ψ₂ : LocalAddCharData L₂)
    (hΨ₁ : Ψ₁.character = Ψ.character.compTrace)
    (hΨ₂ : Ψ₂.character = Ψ.character.compTrace)
    (Θ : ContinuousQuasiChar K)
    (hc₁ : normQuasiChar L₁ K θ₁.character = Θ)
    (hc₂ : normQuasiChar L₂ K θ₂.character = Θ)
    (C : Kˣ) (hC : ord K (C : K) = ((1 - 2 * (a : ℤ) : ℤ) : WithTop ℤ))
    (H₁ : MinimalOriginSide L₁ a (2 * r) (2 * ((r : ℤ) - a)) ω₁
      Ψ.character θ₁.character (C : K))
    (H₂ : MinimalOriginSide L₂ r (a + r) 0 ω₂ Ψ.character θ₂.character (C : K))
    (δ₁ : L₁ˣ) (hδ₁ : ord L₁ (δ₁ : L₁) = (((2 * r - 1 : ℕ) : ℤ) : WithTop ℤ))
    (δ₂ : L₂ˣ) (hδ₂ : ord L₂ (δ₂ : L₂) = (((a + r - 1 : ℕ) : ℤ) : WithTop ℤ))
    (v : lattice K ((2 * r - 1 : ℕ) : ℤ)) :
    let C' := minimalFunctionPoint C (2 * r - 1) (by omega) v
    let V₁ := minimalFirstLift L₁ ha har htF₁ htK₁ hresF₁ hresK₁ C hC
      H₁.trace_order H₁.trace_ne_zero v
    let V₂ := minimalOtherLift L₂ ha har htF₂ htK₂ hresF₂ hresK₂ C hC
      (by simpa using H₂.trace_order) H₂.trace_ne_zero v
    let Q := (Θ (C' / C) : ℂ)⁻¹ *
      (Ψ.character (-elementarySymmetric F K 2 (C' : K) +
        elementarySymmetric F K 2 (C : K)) : ℂ)
    Stationary.normalizedResidualFunction L₁ θ₁ Ψ₁ 1 (normUnits L₁ K C)
        (2 * r - 1) (by omega) (by omega) δ₁ hδ₁
        (minimalCriticalCoordinate L₁ δ₁ hδ₁ V₁.upper) = Q ∧
    Stationary.normalizedResidualFunction L₂ θ₂ Ψ₂ 1 (normUnits L₂ K C)
        (a + r - 1) (by omega) (by omega) δ₂ hδ₂
        (minimalCriticalCoordinate L₂ δ₂ hδ₂ V₂.upper) = Q := by
  dsimp only
  let V₁ := minimalFirstLift L₁ ha har htF₁ htK₁ hresF₁ hresK₁ C hC
    H₁.trace_order H₁.trace_ne_zero v
  let V₂ := minimalOtherLift L₂ ha har htF₂ htK₂ hresF₂ hresK₂ C hC
    (by simpa using H₂.trace_order) H₂.trace_ne_zero v
  have hs₁ := minimal_stationary L₁ ha (show 0 < 2 * r - 1 by omega)
    htF₁ hresF₁ hresK₁ θ₁ Ψ Ψ₁ hΨ₁ C
    (by convert hC using 1; rw [hΨ, hm₁]; congr 1; omega)
    (by simpa only [show 2 * r - 1 + 1 = 2 * r by omega] using H₁.upper_formula)
  have hs₂ := minimal_stationary L₂ (show 1 ≤ r by omega) (show 0 < a + r - 1 by omega)
    htF₂ hresF₂ hresK₂ θ₂ Ψ Ψ₂ hΨ₂ C
    (by convert hC using 1; rw [hΨ, hm₂]; congr 1; omega)
    (by simpa only [show a + r - 1 + 1 = a + r by omega] using H₂.upper_formula)
  have hp₁ := V₁.critical_value L₁ (by omega) (by omega) θ₁ ω₁ Ψ Ψ₁ hΨ₁
    H₁.lower_formula Θ hc₁
  have hp₂ := V₂.critical_value L₂ (by omega) (by omega) θ₂ ω₂ Ψ Ψ₂ hΨ₂
    H₂.lower_formula Θ hc₂
  exact ⟨(criticalValue_eq_residual L₁ θ₁ Ψ₁ (normUnits L₁ K C) (by omega)
      (by omega) hs₁.1 hs₁.2 δ₁ hδ₁ V₁.upper).symm.trans hp₁,
    (criticalValue_eq_residual L₂ θ₂ Ψ₂ (normUnits L₂ K C) (by omega)
      (by omega) hs₂.1 hs₂.2 δ₂ hδ₂ V₂.upper).symm.trans hp₂⟩

end Comparison

end

end LanglandsSecondMainLemma.Dyadic.Nonmaximal
