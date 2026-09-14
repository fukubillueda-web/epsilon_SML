import LanglandsFirstMainLemma.Ramification.NormBelowBreak
import LanglandsFirstMainLemma.Ramification.NormAboveBreak
import LanglandsSecondMainLemma.Dyadic.Equal.MinimalFunctions

/-!
# The unequal-break minimal row

Paper `D:EQ:min-two`, with the full functions of `D:EQ:commonH-general`.
Indices 0 and 1 denote the paper's first and second intermediate fields.
-/

namespace LanglandsSecondMainLemma.Dyadic.Equal
open LanglandsFirstMainLemma
noncomputable section
open scoped BigOperators

open private originLine_degrees origin_residueDegrees origin_group_equiv from
  LanglandsSecondMainLemma.Dyadic.Equal.Origin
open private edge_ramification from
  LanglandsSecondMainLemma.Dyadic.Equal.Compatibility
open private terminal_ledger from
  LanglandsSecondMainLemma.Dyadic.Equal.MinimalFunctions

open private model_ledger from LanglandsSecondMainLemma.Dyadic.Equal.Models
open private scale_one from LanglandsSecondMainLemma.Dyadic.Equal.MinimalFunctions
open private residualScale commonOrigin_edge from
  LanglandsSecondMainLemma.Stationary.CommonOrigin

open private field_injective from LanglandsSecondMainLemma.Dyadic.Equal.Models

section ResidueSum
variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

private def terminalResidueUnit {d : ℕ} (hd : 0 < d) (δ : Eˣ)
    (hδ : ord E (δ : E) = ((d : ℤ) : WithTop ℤ)) (x : ResidueField E) :
    unitFiltration E d :=
  positiveUnitOfLattice E hd ⟨(δ : E) * (teichmuller E x : E), by
    simpa only [add_zero] using mul_mem_lattice E hδ.ge
      ((mem_lattice_zero_iff E).2 (teichmuller E x).property)⟩

private theorem terminalResidueUnit_bijective {d : ℕ} (hd : 0 < d) (δ : Eˣ)
    (hδ : ord E (δ : E) = ((d : ℤ) : WithTop ℤ)) :
    Function.Bijective (fun x ↦ unitGradedMk E d (terminalResidueUnit E hd δ hδ x)) := by
  apply (Nat.bijective_iff_injective_and_card _).2
  constructor
  · intro x y hxy
    have h := (unitGradedMk_eq_mk_iff E d _ _).1 hxy
    change CongruentAtDepth ((d + 1 : ℕ) : ℤ)
      (1 + (δ : E) * (teichmuller E x : E))
      (1 + (δ : E) * (teichmuller E y : E)) at h
    have hm : (δ : E) * ((teichmuller E x : E) - (teichmuller E y : E)) ∈
        lattice E ((d : ℤ) + 1) := by
      rw [congruentAtDepth_iff_sub_mem_lattice] at h
      rw [Nat.cast_add, Nat.cast_one] at h
      convert h using 1
      ring
    have hh := (div_mem_lattice_iff E (δ : E)
      ((δ : E) * ((teichmuller E x : E) - (teichmuller E y : E)))
      (d : ℤ) 1 hδ).2 hm
    rw [mul_div_cancel_left₀ _ (Units.ne_zero δ)] at hh
    have he := (residueMap_eq_residueMap_iff E (teichmuller E x) (teichmuller E y)).2 hh
    simpa only [residueMap_teichmuller] using he
  · rw [positiveUnitFiltrationQuotient_card E hd (Nat.le_succ d)]
    letI := residueFieldFintype E
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel_left, pow_one, Nat.card_eq_fintype_card]
    rfl

private theorem normalizedResidualFactor_eq_sum {d : ℕ} (hd : 0 < d)
    (χ : LocalQuasiCharData E) (Ψ : LocalAddCharData E) (Z : Eˣ)
    (hm : χ.conductor = 2 * d + 1) (hlarge : 1 < χ.conductor)
    (δ : Eˣ) (hδ : ord E (δ : E) = ((d : ℤ) : WithTop ℤ))
    (f : UnitGradedPiece E d → ℂ)
    (hf : ∀ u : unitFiltration E d, f (unitGradedMk E d u) =
      Stationary.normalizedCriticalValue E χ Ψ Z d hd
        (positiveUnitDisplacement E hd u)) :
    Stationary.normalizedResidualFactor E χ Ψ 1 Z d hm hlarge δ hδ =
      (letI : Fintype (UnitGradedPiece E d) := Fintype.ofFinite _
       (Real.sqrt (residueCard E : ℝ) : ℂ)⁻¹ * ∑ x, f x) := by
  classical
  letI := residueFieldFintype E
  letI : Fintype (UnitGradedPiece E d) := Fintype.ofFinite _
  unfold Stationary.normalizedResidualFactor
  congr 1
  apply Fintype.sum_bijective _ (terminalResidueUnit_bijective E hd δ hδ)
  intro x
  rw [hf]
  dsimp only [Stationary.normalizedResidualFunction, Stationary.normalizedCriticalValue]
  rw [scaleAddCharData_character_apply, Units.val_one, one_mul]
  have hu : (positiveUnitOfLattice E hd (positiveUnitDisplacement E hd
      (terminalResidueUnit E hd δ hδ x)) : Eˣ) =
      lamprechtHasseUnit E χ d hm hlarge δ hδ (teichmuller E x : E)
        ((mem_lattice_zero_iff E).2 (teichmuller E x).property) := by
    apply Units.ext
    rw [coe_positiveUnitOfLattice, coe_positiveUnitDisplacement, lamprechtHasseUnit_coe]
    change 1 + ((1 + (δ : E) * (teichmuller E x : E)) - 1) = _
    ring
  rw [hu]
  congr 2
  congr 1
  change -(Z : E) * (δ : E) * (teichmuller E x : E) =
    -(Z : E) * ((1 + (δ : E) * (teichmuller E x : E)) - 1)
  ring

private theorem scale_cancel (Ψ : LocalAddCharData E) (α : Eˣ) :
    scaleAddCharData E (scaleAddCharData E Ψ α) α⁻¹ = Ψ := by
  apply LocalAddCharData.eq_of_character_eq
  ext x
  simp only [scaleAddCharData_character_apply, Units.val_inv_eq_inv_val]
  congr 1
  field_simp

private theorem residual_scale_cancel (χ : LocalQuasiCharData E)
    (Ψ : LocalAddCharData E) (α Z : Eˣ) (hχ : 1 < χ.conductor) :
    Stationary.completeNormalizedResidualFactor E χ (scaleAddCharData E Ψ α) α⁻¹ Z hχ =
      Stationary.completeNormalizedResidualFactor E χ Ψ 1 Z hχ := by
  unfold Stationary.completeNormalizedResidualFactor
  split_ifs
  · rfl
  · simp only [Stationary.normalizedResidualFactor, Stationary.normalizedResidualFunction,
      scale_cancel, scale_one]

end ResidueSum

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  [CharP F 2] [CharP K 2] [IsKleinFour Gal(K/F)]

local instance unequalBreaksValuativeRel (L : IntermediateField F K) : ValuativeRel L :=
  Basic.intermediateFieldValuativeRel L
local instance unequalBreaksTopology (L : IntermediateField F K) : TopologicalSpace L :=
  Basic.intermediateFieldTopology L
local instance unequalBreaksLocalField (L : IntermediateField F K) : IsNonarchimedeanLocalField L :=
  Basic.intermediateField_localField L
local instance unequalBreaksLowerExtension (L : IntermediateField F K) : ValuativeExtension F L :=
  Basic.intermediateField_lowerValuativeExtension L
local instance unequalBreaksUpperExtension (L : IntermediateField F K) : ValuativeExtension L K :=
  Basic.intermediateField_upperValuativeExtension L
local instance unequalBreaksIsGalois (L : IntermediateField F K) : IsGalois F L := by
  letI : IsMulCommutative Gal(K/F) := IsKleinFour.isMulCommutative
  letI : L.fixingSubgroup.Normal := inferInstance
  have h := IsGalois.of_fixedField_normal_subgroup L.fixingSubgroup
  rwa [IsGalois.fixedField_fixingSubgroup L] at h

namespace SimultaneousASGenerators
variable {P : Residues.EqualCharacteristicPresentation F}
  (A : SimultaneousASGenerators F K P)


omit [IsGalois F K] [CharP F 2] [CharP K 2] in
/-- The integer depth ledger for the two different breaks. -/
theorem unequalTerminalDepths (hlt : A.t 0 < A.t 1) :
    A.minimalTerminalDepth 0 = A.t 1 ∧
      2 * A.minimalTerminalDepth 1 = A.t 0 + A.t 1 ∧
      A.t 0 < A.minimalTerminalDepth 1 ∧
      A.minimalTerminalDepth 1 < A.t 1 := by
  obtain ⟨a, ha⟩ := (A.edge 0).2.2.2.2.1
  obtain ⟨b, hb⟩ := (A.edge 1).2.2.2.2.1
  simp only [minimalTerminalDepth, stationaryDepth]
  norm_num
  omega

/-- The actual upper norm sends the source terminal units to each target
terminal group. This uses the full norm increment, including its trace term. -/
def minimalNormUnit (hres : residueDegree F K = 1) (i : Fin 3)
    (u : unitFiltration K (A.t 1)) :
    unitFiltration (A.field i) (A.minimalTerminalDepth i) :=
  ⟨normUnits (A.field i) K u, by
    have hu := (positiveUnitDisplacement K (A.edge 1).2.2.2.1 u).property
    have hn := A.minimalNormIncrement_mem hres i hu
    have he : 1 + (((u : Kˣ) : K) - 1) = ((u : Kˣ) : K) := by ring
    change Algebra.norm (A.field i) (1 + (((u : Kˣ) : K) - 1)) - 1 ∈ _ at hn
    rw [he] at hn
    obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (terminal_ledger A i).1.ne'
    rw [hd, mem_unitFiltration_succ_iff_sub_mem_lattice]
    simpa only [coe_normUnits, hd] using hn⟩

/-- Below the first upper break the trace is strictly deeper than the
terminal norm endpoint, at the exact integer exponent `t₂+1`. -/
theorem unequalFirstTrace_deep (hres : residueDegree F K = 1)
    (hlt : A.t 0 < A.t 1) {u : K} (hu : u ∈ lattice K (A.t 1 : ℤ)) :
    Algebra.trace (A.field 0) K u ∈ lattice (A.field 0) ((A.t 1 : ℤ) + 1) := by
  apply lattice_antitone _ _ (A.upperTrace_mem hres 0 _ hu)
  norm_num
  omega

omit [CharP F 2] [CharP K 2] in
/-- Above the second upper break the norm endpoint is strictly deeper than
the terminal trace, at the exact integer exponent `ℓ₂+1`. -/
theorem unequalSecondNorm_deep (hres : residueDegree F K = 1)
    (hlt : A.t 0 < A.t 1) {u : K} (hu : u ∈ lattice K (A.t 1 : ℤ)) :
    Algebra.norm (A.field 1) u ∈
      lattice (A.field 1) ((A.minimalTerminalDepth 1 : ℤ) + 1) := by
  have hn : Algebra.norm (A.field 1) u ∈ lattice (A.field 1) (A.t 1 : ℤ) := by
    change _ ≤ ord (A.field 1) (norm (A.field 1) K u)
    rw [ord_norm, (origin_residueDegrees F K hres (A.field 1)).2, one_nsmul]
    exact hu
  apply lattice_antitone _ _ hn
  have := (A.unequalTerminalDepths hlt).2.2.2
  omega

/-- The two adjacent source ideals have precisely the two adjacent target
trace ideals. These equalities use the upper different `t₁+1`. -/
theorem unequalSecondTrace_depths (hres : residueDegree F K = 1)
    (hlt : A.t 0 < A.t 1) :
    ((A.t 1 : ℤ) + differentExponent (A.field 1) K) /
        ramificationIndex (A.field 1) K = A.minimalTerminalDepth 1 ∧
      ((A.t 1 : ℤ) + 1 + differentExponent (A.field 1) K) /
        ramificationIndex (A.field 1) K = (A.minimalTerminalDepth 1 : ℤ) + 1 := by
  rw [A.upper_different hres 1, (edge_ramification A hres 1).2]
  have := (A.unequalTerminalDepths hlt).2.1
  norm_num
  omega

/-- Denominator containment uses the next source level, not a truncated
or interpolated depth. -/
private theorem minimalNormUnit_deeper (hres : residueDegree F K = 1) (i : Fin 3) :
    AboveBreakNormMapsUnitFiltration (A.field i) K (A.t 1 + 1)
      (A.minimalTerminalDepth i + 1) := by
  intro u hu
  have hx := (mem_unitFiltration_succ_iff_sub_mem_lattice K (A.t 1) u).1 hu
  have hn := A.normIncrement_mem hres i ((lattice K _).neg_mem hx)
  have he : 1 - -((u : K) - 1) = (u : K) := by ring
  rw [he] at hn
  rw [mem_unitFiltration_succ_iff_sub_mem_lattice]
  have hdep := (terminal_ledger A i).2.1
  simpa only [hdep, Nat.cast_add, Nat.cast_one, neg_sub, coe_normUnits] using
    (lattice (A.field i) _).neg_mem hn

private theorem minimalNormUnit_mem (hres : residueDegree F K = 1) (i : Fin 3) :
    AboveBreakNormMapsUnitFiltration (A.field i) K (A.t 1) (A.minimalTerminalDepth i) := by
  intro u hu
  exact (A.minimalNormUnit hres i ⟨u, hu⟩).property

/-- The actual graded upper norm, with numerator and denominator
containment proved from the field data. -/
def minimalGradedNorm (hres : residueDegree F K = 1) (i : Fin 3) :
    UnitGradedPiece K (A.t 1) →*
      UnitGradedPiece (A.field i) (A.minimalTerminalDepth i) :=
  aboveBreakNormUnitFiltrationQuotient (A.field i) K (Nat.le_succ _) (Nat.le_succ _)
    (A.minimalNormUnit_mem hres i)
    (A.minimalNormUnit_deeper hres i)

@[simp]
theorem minimalGradedNorm_mk (hres : residueDegree F K = 1) (i : Fin 3)
    (u : unitFiltration K (A.t 1)) :
    A.minimalGradedNorm hres i (unitGradedMk K (A.t 1) u) =
      unitGradedMk (A.field i) (A.minimalTerminalDepth i) (A.minimalNormUnit hres i u) := rfl

/-- The two actual graded norms are bijections. The first is FML's
below-break norm (the Frobenius endpoint); the second is FML's above-break
norm, whose representative formula is trace. No norm choices are assumed. -/
theorem minimalGradedNorm_bijective (hres : residueDegree F K = 1)
    (hlt : A.t 0 < A.t 1) (i : Fin 3) (hi : i = 0 ∨ i = 1) :
    Function.Bijective (A.minimalGradedNorm hres i) := by
  let L := A.field i
  have hdegree := (originLine_degrees F K (A.g i) (A.nontrivial i)).2
  letI : IsCyclic Gal(K/L) := isCyclic_of_prime_card
    ((IsGalois.card_aut_eq_finrank L K).trans hdegree)
  letI : PrimeCyclicExtension L K :=
    ⟨inferInstance, inferInstance, by rw [hdegree]; exact Nat.prime_two⟩
  have hr := (origin_residueDegrees F K hres L).2
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer L K hr
  have hb := A.upper_break i
  rcases hi with rfl | rfl
  · have hit : A.t 1 < A.t 0 + 2 * (A.t 1 - A.t 0) := by omega
    simp only [ite_true] at hb
    have he := (A.unequalTerminalDepths hlt).1
    unfold minimalGradedNorm
    exact normUnitGraded_bijective_belowBreak L K hb (by omega) hit hr pi hpi hgen
  · have hit := (A.unequalTerminalDepths hlt).2.2.1
    norm_num at hb
    have hs : aboveBreakSourceDepth (A.t 0) (Module.finrank L K)
        (A.minimalTerminalDepth 1) = A.t 1 := by
      rw [aboveBreakSourceDepth_eq _ _ hit.le, hdegree]
      have := (A.unequalTerminalDepths hlt).2.1
      omega
    have h := norm_graded_bijective_above_break L K hb hit hr pi hpi hgen
    unfold normGradedAboveBreakCanonical normGradedAboveBreak at h
    have transport (a : ℕ)
        (hn : AboveBreakNormMapsUnitFiltration L K a (A.minimalTerminalDepth 1))
        (hd : AboveBreakNormMapsUnitFiltration L K (a + 1) (A.minimalTerminalDepth 1 + 1))
        (ha : a = A.t 1)
        (hb : Function.Bijective (aboveBreakNormUnitFiltrationQuotient L K
          (Nat.le_succ a) (Nat.le_succ _) hn hd)) :
        Function.Bijective (A.minimalGradedNorm hres 1) := by
      subst a
      exact hb
    exact transport _ _ _ hs h

/-- The full affine critical function on actual terminal unit classes. -/
def minimalGradedFunction (hres : residueDegree F K = 1)
    (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i)) (C : Kˣ)
    (hC : A.IsMinimalFunctionOrigin θ C) (i : Fin 3)
    (hi : i ≠ 2 ∨ A.t 0 = A.t 1) :
    UnitGradedPiece (A.field i) (A.minimalTerminalDepth i) → ℂ :=
  unitFiltrationQuotientLift (A.field i) (Nat.le_succ _)
    (fun u ↦ A.minimalFullFunction hres (θ i) C
      (positiveUnitDisplacement (A.field i) (terminal_ledger A i).1 u)) (by
        intro u v huv
        apply A.minimalFullFunction_eq_of_congruent hres θ C hC i hi
        have h := huv.add (CongruentAtDepth.refl (-1 : A.field i))
        simpa only [coe_positiveUnitDisplacement, sub_eq_add_neg, Nat.succ_eq_add_one,
          (terminal_ledger A i).2.1] using h)

/-- Pullback of each full quotient function along the actual graded norm
is the common value with the actual source unit. -/
theorem minimalGradedFunction_norm (hres : residueDegree F K = 1)
    (Θ : ContinuousQuasiChar K) (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hc : ∀ i, normQuasiChar (A.field i) K (θ i) = Θ)
    (C : Kˣ) (hC : A.IsMinimalFunctionOrigin θ C) (i : Fin 3)
    (hi : i ≠ 2 ∨ A.t 0 = A.t 1) (u : unitFiltration K (A.t 1)) :
    A.minimalGradedFunction hres θ C hC i hi
      (A.minimalGradedNorm hres i (unitGradedMk K (A.t 1) u)) =
        A.minimalCommonValue Θ C u := by
  rw [A.minimalGradedNorm_mk]
  exact A.minimalFullFunction_norm hres Θ θ hc C hC i hi u
    (positiveUnitDisplacement K (A.edge 1).2.2.2.1 u).property

/-- The complete finite critical sum over the actual terminal group. -/
def minimalGradedSum (hres : residueDegree F K = 1)
    (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i)) (C : Kˣ)
    (hC : A.IsMinimalFunctionOrigin θ C) (i : Fin 3)
    (hi : i ≠ 2 ∨ A.t 0 = A.t 1) : ℂ := by
  letI : Fintype (UnitGradedPiece (A.field i) (A.minimalTerminalDepth i)) :=
    Fintype.ofFinite _
  exact ∑ x, A.minimalGradedFunction hres θ C hC i hi x

/-- Summation of `D:EQ:commonH-general` using the two constructed graded
norm bijections. Affine terms and all complex character values are retained. -/
theorem minimalGradedSum_eq (hres : residueDegree F K = 1)
    (hlt : A.t 0 < A.t 1)
    (Θ : ContinuousQuasiChar K) (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hc : ∀ i, normQuasiChar (A.field i) K (θ i) = Θ)
    (C : Kˣ) (hC : A.IsMinimalFunctionOrigin θ C) :
    A.minimalGradedSum hres θ C hC 0 (Or.inl (by decide)) =
      A.minimalGradedSum hres θ C hC 1 (Or.inl (by decide)) := by
  classical
  letI : Fintype (UnitGradedPiece K (A.t 1)) := Fintype.ofFinite _
  letI : Fintype (UnitGradedPiece (A.field 0) (A.minimalTerminalDepth 0)) := Fintype.ofFinite _
  letI : Fintype (UnitGradedPiece (A.field 1) (A.minimalTerminalDepth 1)) := Fintype.ofFinite _
  have h (x : UnitGradedPiece K (A.t 1)) :
      A.minimalGradedFunction hres θ C hC 0 (Or.inl (by decide))
          (A.minimalGradedNorm hres 0 x) =
        A.minimalGradedFunction hres θ C hC 1 (Or.inl (by decide))
          (A.minimalGradedNorm hres 1 x) := by
    obtain ⟨u, rfl⟩ := unitGradedMk_surjective K (A.t 1) x
    rw [A.minimalGradedFunction_norm hres Θ θ hc,
      A.minimalGradedFunction_norm hres Θ θ hc]
  unfold minimalGradedSum
  rw [← (A.minimalGradedNorm_bijective hres hlt 0 (Or.inl rfl)).sum_comp,
    ← (A.minimalGradedNorm_bijective hres hlt 1 (Or.inr rfl)).sum_comp]
  exact Finset.sum_congr rfl (fun x _ ↦ h x)

private theorem minimalUpper_stationary (hres : residueDegree F K = 1)
    (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i)) (C : Kˣ)
    (hC : A.IsMinimalFunctionOrigin θ C) (i : Fin 3)
    (hi : i ≠ 2 ∨ A.t 0 = A.t 1)
    (hlarge : 1 < (canonicalLocalQuasiCharData (A.field i) (θ i)).conductor) :
    Stationary.IsOrdinaryStationaryCoefficient (A.field i)
      (canonicalLocalQuasiCharData (A.field i) (θ i))
      (A.minimalUpperPsi hres i) (normUnits (A.field i) K C) hlarge := by
  constructor
  · change ord (A.field i) (norm (A.field i) K (C : K)) =
      ((-(-A.additiveModulus i) -
        (multiplicativeConductorExponent (A.field i) (θ i) : ℤ) : ℤ) : WithTop ℤ)
    rw [ord_norm, (origin_residueDegrees F K hres (A.field i)).2, one_nsmul,
      hC.order, hC.conductor i, (model_ledger A i).2.2.2.1]
    congr 1
    ring
  · intro z
    have hm := (hC.conductor i).trans (terminal_ledger A i).2.2.1
    have hs : (canonicalLocalQuasiCharData (A.field i) (θ i)).conductor / 2 +
        (canonicalLocalQuasiCharData (A.field i) (θ i)).conductor % 2 = A.stationaryDepth i := by
      change multiplicativeConductorExponent (A.field i) (θ i) / 2 +
        multiplicativeConductorExponent (A.field i) (θ i) % 2 = _
      have := (terminal_ledger A i).2.1
      omega
    have hz : 1 - ((positiveUnitOfLattice (A.field i) (by omega) (-z) : (A.field i)ˣ) : A.field i) =
        (z : A.field i) := by simp only [coe_positiveUnitOfLattice, Submodule.coe_neg]; ring
    exact (hC.upper i hi _ (by rw [hz]; simpa only [hs] using z.property)).trans
      (by rw [hz]; rfl)

private theorem minimalUpper_residual (hres : residueDegree F K = 1)
    (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i)) (C : Kˣ)
    (hC : A.IsMinimalFunctionOrigin θ C) (i : Fin 3)
    (hi : i ≠ 2 ∨ A.t 0 = A.t 1)
    (hlarge : 1 < (canonicalLocalQuasiCharData (A.field i) (θ i)).conductor) :
    Stationary.completeNormalizedResidualFactor (A.field i)
      (canonicalLocalQuasiCharData (A.field i) (θ i)) (A.minimalUpperPsi hres i)
      1 (normUnits (A.field i) K C) hlarge =
        (Real.sqrt (residueCard (A.field i) : ℝ) : ℂ)⁻¹ *
          A.minimalGradedSum hres θ C hC i hi := by
  let χ := canonicalLocalQuasiCharData (A.field i) (θ i)
  have hm : χ.conductor = 2 * A.minimalTerminalDepth i + 1 :=
    (hC.conductor i).trans (terminal_ledger A i).2.2.1
  have hd : χ.conductor / 2 = A.minimalTerminalDepth i := by omega
  have heven : ¬ χ.conductor % 2 = 0 := by omega
  change Stationary.completeNormalizedResidualFactor (A.field i) χ _ _ _ _ = _
  rw [Stationary.completeNormalizedResidualFactor, dif_neg heven]
  have transport (d : ℕ) (hm' : χ.conductor = 2 * d + 1)
      (δ' : (A.field i)ˣ) (hord : ord (A.field i) (δ' : A.field i) = ((d : ℤ) : WithTop ℤ))
      (he : d = A.minimalTerminalDepth i) :
      Stationary.normalizedResidualFactor (A.field i) χ (A.minimalUpperPsi hres i)
        1 (normUnits (A.field i) K C) d hm' hlarge δ' hord =
          (Real.sqrt (residueCard (A.field i) : ℝ) : ℂ)⁻¹ *
            A.minimalGradedSum hres θ C hC i hi := by
    subst d
    exact normalizedResidualFactor_eq_sum (A.field i) (terminal_ledger A i).1 χ
      (A.minimalUpperPsi hres i) (normUnits (A.field i) K C) hm' hlarge δ' hord
      (A.minimalGradedFunction hres θ C hC i hi) (fun _ ↦ rfl)
  exact transport _ _ _ _ hd

omit [CharP F 2] [CharP K 2] in
private theorem minimalLower_conductor (hres : residueDegree F K = 1) (i : Fin 3)
    (ω : NormCharacter F (A.field i)) (hω : ω ≠ 1) :
    multiplicativeConductorExponent F ω.1 = A.t i + 1 := by
  let L := A.field i
  have hdegree := (originLine_degrees F K (A.g i) (A.nontrivial i)).1
  letI : IsCyclic Gal(L/F) := isCyclic_of_prime_card
    ((IsGalois.card_aut_eq_finrank F L).trans hdegree)
  letI : PrimeCyclicExtension F L :=
    ⟨inferInstance, inferInstance, by rw [hdegree]; exact Nat.prime_two⟩
  have hr := (origin_residueDegrees F K hres L).1
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F L hr
  exact multiplicativeConductorExponent_eq_of_isConductor F ω.1
    (ramifiedNormCharacter_conductor F L (A.edge i).2.2.2.2.2.2.2.1
      hr pi hpi hgen ω hω)

private theorem minimalLower_stationary (hres : residueDegree F K = 1)
    (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i)) (C : Kˣ)
    (hC : A.IsMinimalFunctionOrigin θ C) (i : Fin 3)
    (hi : i ≠ 2 ∨ A.t 0 = A.t 1)
    (ω : NormCharacter F (A.field i)) (hω : ω ≠ 1)
    (htrace : trace (A.field i) K (C : K) ≠ 0)
    (hlarge : 1 < (canonicalLocalQuasiCharData F ω.1).conductor) :
    Stationary.IsOrdinaryStationaryCoefficient F (canonicalLocalQuasiCharData F ω.1)
      A.minimalBasePsi (Stationary.commonOriginLowerCoefficient (A.field i) C htrace) hlarge := by
  have hm := A.minimalLower_conductor hres i ω hω
  constructor
  · change ord F (norm F (A.field i) (trace (A.field i) K (C : K))) =
      ((-(-((A.t 1 : ℤ) + 1)) - (multiplicativeConductorExponent F ω.1 : ℤ) : ℤ) : WithTop ℤ)
    rw [ord_norm, (origin_residueDegrees F K hres (A.field i)).1, one_nsmul,
      A.minimalOrigin_trace_order hres (C : K) hC.order i, hm]
    congr 1
    push_cast
    ring
  · intro z
    have hs : ((canonicalLocalQuasiCharData F ω.1).conductor / 2 +
        (canonicalLocalQuasiCharData F ω.1).conductor % 2 : ℤ) = A.lowerDepth i := by
      change ((multiplicativeConductorExponent F ω.1 / 2 +
        multiplicativeConductorExponent F ω.1 % 2 : ℕ) : ℤ) = _
      rw [hm]
      obtain ⟨a, ha⟩ := (A.edge i).2.2.2.2.1
      simp only [lowerDepth]
      omega
    have hz : 1 - ((positiveUnitOfLattice F (by omega) (-z) : Fˣ) : F) =
        (z : F) := by simp only [coe_positiveUnitOfLattice, Submodule.coe_neg]; ring
    exact (hC.lower i hi ω hω _ (by rw [hz, ← hs]; exact z.property)).trans
      (by rw [hz]; rfl)

/-- Additive scaling commutes with the actual lower trace pullback. -/
theorem minimalScaledUpperPsi_character (hres : residueDegree F K = 1)
    (i : Fin 3) (α : Fˣ) :
    (scaleAddCharData (A.field i) (A.minimalUpperPsi hres i)
      (Units.map (algebraMap F (A.field i)).toMonoidHom α)).character =
        (scaleAddCharData F A.minimalBasePsi α).character.compTrace := by
  apply DFunLike.ext
  intro x
  simp only [scaleAddCharData_character_apply, ContinuousAddChar.compTrace_apply]
  change A.minimalBasePsi.character
      (Algebra.trace F (A.field i) (algebraMap F (A.field i) (α : F) * x)) =
    A.minimalBasePsi.character ((α : F) * Algebra.trace F (A.field i) x)
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-- The actual upper/lower local-constant product has the common elementary
factor times its complete normalized terminal sum (`D:EQ:minfull`).
The scalar is arbitrary, and the corrected restriction is retained. -/
theorem minimalInductionFactor (hres : residueDegree F K = 1)
    (Θ : ContinuousQuasiChar K) (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hc : ∀ i, normQuasiChar (A.field i) K (θ i) = Θ)
    (C : Kˣ) (hC : A.IsMinimalFunctionOrigin θ C) (i : Fin 3)
    (hi : i ≠ 2 ∨ A.t 0 = A.t 1)
    (ω : NormCharacter F (A.field i)) (hω : ω ≠ 1) (α : Fˣ) :
    localConstant (A.field i) (θ i)
        (scaleAddCharData (A.field i) (A.minimalUpperPsi hres i)
          (Units.map (algebraMap F (A.field i)).toMonoidHom α)).character *
        localConstant F ω.1 (scaleAddCharData F A.minimalBasePsi α).character =
      ((Characters.restrictQuasiChar F (A.field i) (θ i) * ω.1) α : ℂ) * (Θ C : ℂ)⁻¹ *
        (A.minimalBasePsi.character (-elementarySymmetric F K 2 (C : K)) : ℂ) *
        ((Real.sqrt (residueCard (A.field i) : ℝ) : ℂ)⁻¹ *
          A.minimalGradedSum hres θ C hC i hi) := by
  let L := A.field i
  have hdegree := originLine_degrees F K (A.g i) (A.nontrivial i)
  letI : Algebra.IsQuadraticExtension F L := ⟨hdegree.1⟩
  letI : Algebra.IsQuadraticExtension L K := ⟨hdegree.2⟩
  have htrace : trace L K (C : K) ≠ 0 := (ord_ne_top_iff L).mp (by
    rw [A.minimalOrigin_trace_order hres (C : K) hC.order i]
    exact WithTop.coe_ne_top)
  let χ := canonicalLocalQuasiCharData L (θ i)
  let μ := canonicalLocalQuasiCharData F ω.1
  have hm : χ.conductor = 2 * A.minimalTerminalDepth i + 1 :=
    (hC.conductor i).trans (terminal_ledger A i).2.2.1
  have hχ : 1 < χ.conductor := by have := (terminal_ledger A i).1; omega
  have hμc : μ.conductor = A.t i + 1 := A.minimalLower_conductor hres i ω hω
  have hμ : 1 < μ.conductor := by have := (A.edge i).2.2.2.1; omega
  let αL := Units.map (algebraMap F L).toMonoidHom α
  have hψ := A.minimalScaledUpperPsi_character hres i α
  have he := commonOrigin_edge L χ μ ω rfl Θ (hc i)
    (scaleAddCharData F A.minimalBasePsi α)
    (scaleAddCharData L (A.minimalUpperPsi hres i) αL) hψ α⁻¹ C htrace hχ hμ
    (by simpa only [αL, map_inv, scale_cancel] using A.minimalUpper_stationary hres θ C hC i hi hχ)
    (by simpa only [scale_cancel] using A.minimalLower_stationary hres θ C hC i hi ω hω htrace hμ)
  have heven : μ.conductor % 2 = 0 := by
    obtain ⟨a, ha⟩ := (A.edge i).2.2.2.2.1
    omega
  have hneg : (-α : Fˣ) = α := by apply Units.ext; exact CharTwo.neg_eq _
  simp only [Stationary.commonOriginResidualProduct, map_inv, inv_inv, hneg,
    scale_cancel, Stationary.completeNormalizedResidualFactor_even F μ _ _ _ hμ heven,
    mul_one] at he
  rw [residual_scale_cancel L χ (A.minimalUpperPsi hres i) αL] at he
  have hR := A.minimalUpper_residual hres θ C hC i hi hχ
  change Stationary.completeNormalizedResidualFactor L χ _ _ _ hχ = _ at hR
  rw [hR] at he
  exact he

private theorem unequalResidueCards (hres : residueDegree F K = 1)
    (hlt : A.t 0 < A.t 1) : residueCard (A.field 0) = residueCard (A.field 1) := by
  let e₀ := Equiv.ofBijective _ (A.minimalGradedNorm_bijective hres hlt 0 (Or.inl rfl))
  let e₁ := Equiv.ofBijective _ (A.minimalGradedNorm_bijective hres hlt 1 (Or.inr rfl))
  have h := Nat.card_congr (e₀.symm.trans e₁)
  rw [positiveUnitFiltrationQuotient_card (A.field 0) (terminal_ledger A 0).1 (Nat.le_succ _),
    positiveUnitFiltrationQuotient_card (A.field 1) (terminal_ledger A 1).1 (Nat.le_succ _)] at h
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel_left, pow_one] using h

omit [IsGalois F K] [CharP K 2] in
/-- The unscaled canonical residue character in the manuscript is one of
the additive scalings in `unequalBreaks_scaled`. The scalar is constructed
in the actual base field from its Laurent presentation. -/
theorem minimalBasePsi_scale_canonical :
    ∃ α : Fˣ, (scaleAddCharData F A.minimalBasePsi α).character = originAddChar F P 0 := by
  let t : ℤ := (A.t 1 : ℤ) + 1
  let a : F := P.laurentEquiv (HahnSeries.single t 1)
  have ha : a ≠ 0 := by
    simpa only [map_zero] using P.laurentEquiv.injective.ne
      (HahnSeries.single_ne_zero (one_ne_zero : (1 : ResidueField F) ≠ 0) :
        HahnSeries.single t (1 : ResidueField F) ≠ 0)
  refine ⟨Units.mk0 a ha, ?_⟩
  apply DFunLike.ext
  intro x
  apply Units.ext
  simp only [scaleAddCharData_character_apply, minimalBasePsi, originAddChar_apply,
    Units.val_mk0, a, t, map_mul, RingEquiv.symm_apply_apply, scaledResiduePhase,
    ← mul_assoc, HahnSeries.single_mul_single, one_mul, neg_add_cancel, neg_zero,
    HahnSeries.single_zero_one]

end SimultaneousASGenerators

/-- **Paper Proposition 11.9 (`D:EQ:min-two`).** Every primitive compatible
minimal family with `t₁ < t₂` has equal induction expressions on the first
two fields. The origin and both graded bijections are constructed from the
actual field and character data. The complete lower norm-character products
are retained. The arbitrary additive scalar includes the manuscript's
canonical normalization as well as the scaled character Ψ. -/
theorem unequalBreaks_scaled (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (A : SimultaneousASGenerators F K P)
    (hlt : A.t 0 < A.t 1)
    (Θ : ContinuousQuasiChar K) (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hcompatible : ∀ i, normQuasiChar (A.field i) K (θ i) = Θ)
    (hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Θ)
    (hminimal : multiplicativeConductorExponent (A.field 0) (θ 0) = A.minimalConductor 0)
    (α : Fˣ) :
    let hG := origin_group_equiv F K
    let ψ := (scaleAddCharData F A.minimalBasePsi α).character
    localConstant (A.field 0) (θ 0) (tracePullbackAddChar F (A.field 0) ψ) *
        localConstant F (Characters.intermediateNormCharacterProduct Nat.prime_two hG
          (A.field 0) (originLine_degrees F K (A.g 0) (A.nontrivial 0)).1) ψ =
      localConstant (A.field 1) (θ 1) (tracePullbackAddChar F (A.field 1) ψ) *
        localConstant F (Characters.intermediateNormCharacterProduct Nat.prime_two hG
          (A.field 1) (originLine_degrees F K (A.g 1) (A.nontrivial 1)).1) ψ := by
  dsimp only
  obtain ⟨C, hC⟩ := A.minimalFunctionOrigin_exists hres Θ θ hcompatible hprimitive hminimal
  obtain ⟨_, _, _, _, hranges, _⟩ := Characters.quadraticProduct F
    (origin_group_equiv F K) A.field
    (fun i ↦ (originLine_degrees F K (A.g i) (A.nontrivial i)).1) (field_injective A)
  have hconj := Characters.conjugacy Nat.prime_two (origin_group_equiv F K)
    (A.field 0) (A.field 1)
    (originLine_degrees F K (A.g 0) (A.nontrivial 0)).1
    (originLine_degrees F K (A.g 1) (A.nontrivial 1)).1
    (fun he ↦ (by decide : (0 : Fin 3) ≠ 1) (hranges he))
    (θ 0) (θ 1) Θ (hcompatible 0) (hcompatible 1) hprimitive
  obtain ⟨ω₀, ω₁, hω₀, hω₁, he₀, he₁⟩ := hconj.2.2.2.2 rfl
  have hD := hconj.2.2.1
  rw [he₀, he₁] at hD ⊢
  have hψ (i : Fin 3) : tracePullbackAddChar F (A.field i)
      (scaleAddCharData F A.minimalBasePsi α).character =
        (scaleAddCharData (A.field i) (A.minimalUpperPsi hres i)
          (Units.map (algebraMap F (A.field i)).toMonoidHom α)).character :=
    (A.minimalScaledUpperPsi_character hres i α).symm
  rw [hψ 0, hψ 1,
    A.minimalInductionFactor hres Θ θ hcompatible C hC 0 (Or.inl (by decide)) ω₀ hω₀ α,
    A.minimalInductionFactor hres Θ θ hcompatible C hC 1 (Or.inl (by decide)) ω₁ hω₁ α,
    hD, A.unequalResidueCards hres hlt,
    A.minimalGradedSum_eq hres hlt Θ θ hcompatible C hC]

/-- **The two-break minimal row, `D:EQ:min-two`, with the manuscript's
canonical additive character.** The auxiliary stationary origin, the graded
maps, and the normalization scalar are all constructed in the proof. -/
theorem unequalBreaks (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (A : SimultaneousASGenerators F K P)
    (hlt : A.t 0 < A.t 1)
    (Θ : ContinuousQuasiChar K) (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hcompatible : ∀ i, normQuasiChar (A.field i) K (θ i) = Θ)
    (hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Θ)
    (hminimal : multiplicativeConductorExponent (A.field 0) (θ 0) = A.minimalConductor 0) :
    let hG := origin_group_equiv F K
    let ψ := originAddChar F P 0
    localConstant (A.field 0) (θ 0) (tracePullbackAddChar F (A.field 0) ψ) *
        localConstant F (Characters.intermediateNormCharacterProduct Nat.prime_two hG
          (A.field 0) (originLine_degrees F K (A.g 0) (A.nontrivial 0)).1) ψ =
      localConstant (A.field 1) (θ 1) (tracePullbackAddChar F (A.field 1) ψ) *
        localConstant F (Characters.intermediateNormCharacterProduct Nat.prime_two hG
          (A.field 1) (originLine_degrees F K (A.g 1) (A.nontrivial 1)).1) ψ := by
  obtain ⟨α, hα⟩ := A.minimalBasePsi_scale_canonical
  simpa only [hα] using
    unequalBreaks_scaled hres P A hlt Θ θ hcompatible hprimitive hminimal α

end
end LanglandsSecondMainLemma.Dyadic.Equal
