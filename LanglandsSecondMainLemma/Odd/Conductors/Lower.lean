import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Characters.Conjugacy
import LanglandsSecondMainLemma.Odd.Total.ASCoordinate
import LanglandsSecondMainLemma.Ramification.LeadingTerm

/-!
# Primitive conductor lower bounds

Paper Lemma 9.32 (`O:G:lower`), with the setup at lines 4962–4982.
The conjugate quotient has upper-break conductor. A nontrivial value on
that critical unit layer is an actual commutator value of the original
character. The lower ramification inclusion puts this commutator in the
sum of the two break depths. No exact leading coefficient is required.
-/

namespace LanglandsSecondMainLemma.Odd.Conductors

open LanglandsFirstMainLemma

noncomputable section

section Edge
variable {F E : Type} [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E] [IsGalois F E]

omit [IsGalois F E] in
/-- The weak ramification inclusion on nonnegative lattices. The induction
uses only integral displacement bounds and division by a uniformizer. -/
private theorem ramification_lattice_shift
    (σ : Gal(E/F)) {t : ℕ} (hσ : σ ∈ lowerRamificationGroup F E (t : ℤ))
    (π : E) (hπ : (ValuativeRel.valuation E).IsUniformizer π)
    (n : ℕ) {x : E} (hx : x ∈ lattice E (n : ℤ)) :
    σ x - x ∈ lattice E ((n : ℤ) + t) := by
  have hπord := ord_uniformizer E hπ
  have hπint : π ∈ ringOfIntegers E :=
    (ord_nonneg_iff_mem_integer E π).1 (by rw [hπord]; norm_num)
  have hπdiff : σ π - π ∈ lattice E ((t : ℤ) + 1) :=
    (mem_lowerRamificationGroup_iff_lattice F E σ (t : ℤ)).1 hσ ⟨π, hπint⟩
  have hσπ : σ π ∈ lattice E 1 := by
    rw [mem_lattice, ord_galoisConjugate, hπord]
    norm_num
  induction n generalizing x with
  | zero =>
      have h := (mem_lowerRamificationGroup_iff_lattice F E σ (t : ℤ)).1 hσ
        ⟨x, (mem_lattice_zero_iff E).1 hx⟩
      exact lattice_antitone E (by simp) h
  | succ n ih =>
      have ha : x / π ∈ lattice E (n : ℤ) := by
        apply (div_mem_lattice_iff E π x 1 (n : ℤ) hπord).2
        simpa [Nat.cast_add, add_comm] using hx
      have h₁ := mul_mem_lattice E (ih ha) hσπ
      have h₂ := mul_mem_lattice E ha hπdiff
      have heq : σ x - x = (σ (x / π) - x / π) * σ π +
          (x / π) * (σ π - π) := by
        rw [sub_mul, mul_sub, ← map_mul, div_mul_cancel₀ x hπ.ne_zero]
        ring
      rw [heq]
      exact (lattice E ((↑(n + 1) : ℤ) + t)).add_mem
        (by simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using h₁)
        (by simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using h₂)

omit [IsGalois F E] in
/-- A critical upper unit gives a commutator in the sum of the break depths. -/
private theorem commutator_mem
    (σ : Gal(E/F)) {t u : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hu : 0 < u) (π : E) (hπ : (ValuativeRel.valuation E).IsUniformizer π)
    (y : Eˣ) (hy : y ∈ unitFiltration E u) :
    Units.map σ.toMonoidHom y / y ∈ unitFiltration E (t + u) := by
  obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hu)
  have hyunit := unitFiltration_le_unitGroup E (v + 1) hy
  have hσyunit : Units.map σ.toMonoidHom y ∈ unitGroup E := by
    rw [mem_unitGroup_iff_ord_eq_zero]
    change ord E (σ (y : E)) = 0
    rw [ord_galoisConjugate]
    exact (mem_unitGroup_iff_ord_eq_zero E y).1 hyunit
  apply (div_mem_unitFiltration_iff_congruentAtDepth E _ _ _ hσyunit hyunit).2
  have h := ramification_lattice_shift σ (by rw [ht.1]; trivial) π hπ (v + 1)
    ((mem_unitFiltration_succ_iff_sub_mem_lattice E v y).1 hy)
  have heq : σ ((y : E) - 1) - ((y : E) - 1) = σ (y : E) - (y : E) := by
    rw [map_sub, map_one]
    ring
  change σ (y : E) - (y : E) ∈ lattice E ((t + (v + 1) : ℕ) : ℤ)
  simpa [heq, Nat.cast_add, add_comm, add_left_comm, add_assoc] using h

end Edge

section Tower
variable {F E K : Type} [Field F] [Field E] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F E] [Algebra E K]
  [ValuativeExtension F E] [ValuativeExtension E K]
  [Module.Finite F E] [Module.Finite E K]
  [PrimeCyclicExtension F E] [PrimeCyclicExtension E K]

private theorem lower_of_conjugateTwistData
    {θ : ContinuousQuasiChar E} (D : Characters.ConjugateTwistData F E K θ)
    {t u a : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hu : PrimeCyclicExtension.IsLowerBreak E K u) (hupos : 0 < u)
    (hresFE : residueDegree F E = 1) (hresEK : residueDegree E K = 1)
    (ha : IsMultiplicativeConductor E θ a) : 1 + t + u ≤ a := by
  let σ := PrimeCyclicExtension.generator F E
  let μ := D.quotientEquiv σ
  have hμ : μ ≠ 1 := by
    intro h
    exact PrimeCyclicExtension.generator_ne_one F E
      (D.quotientEquiv.injective (h.trans D.quotientEquiv.map_one.symm))
  obtain ⟨πK, hπK, hgenK⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one E K hresEK
  have hcond := ramifiedNormCharacter_conductor E K hu hresEK πK hπK hgenK μ hμ
  obtain ⟨y, hy, hval⟩ := hcond.exists_ne_one_of_lt (Nat.lt_succ_self u)
  obtain ⟨πE, hπE, _hgenE⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one F E hresFE
  have hcomm := commutator_mem σ.symm ht hupos πE hπE y hy
  have hvalue : θ (Units.map σ.symm.toMonoidHom y / y) = μ.1 y := by
    rw [map_div]
    exact (DFunLike.congr_fun (D.quotient_eq σ) y).symm
  have hnontriv : ¬ QuasiCharTrivialOnUnitFiltration E θ (t + u) := by
    intro htriv
    exact hval (hvalue.symm.trans (htriv _ hcomm))
  have := ha.not_trivialOnUnitFiltration_iff.mp hnontriv
  omega

end Tower

section Diamond
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

private theorem intermediate_residueDegrees_eq_one
    (I : IntermediateField F K) (hres : residueDegree F K = 1) :
    letI := Basic.intermediateFieldValuativeRel I
    letI := Basic.intermediateFieldTopology I
    letI := Basic.intermediateField_localField I
    letI := Basic.intermediateField_lowerValuativeExtension I
    letI := Basic.intermediateField_upperValuativeExtension I
    residueDegree F I = 1 ∧ residueDegree I K = 1 := by
  letI := Basic.intermediateFieldValuativeRel I
  letI := Basic.intermediateFieldTopology I
  letI := Basic.intermediateField_localField I
  letI := Basic.intermediateField_lowerValuativeExtension I
  letI := Basic.intermediateField_upperValuativeExtension I
  letI : IsScalarTower (ringOfIntegers F) (ringOfIntegers I) (ringOfIntegers K) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap F K (x : F) = algebraMap I K (algebraMap F I (x : F))
      rw [← IsScalarTower.algebraMap_apply F I K])
  letI : IsLocalHom (algebraMap (ringOfIntegers F) (ringOfIntegers I)) := inferInstance
  letI : IsLocalHom (algebraMap (ringOfIntegers I) (ringOfIntegers K)) := inferInstance
  have hmul : residueDegree F I * residueDegree I K = residueDegree F K := by
    rw [residueDegree_eq_finrank_residueField, residueDegree_eq_finrank_residueField,
      residueDegree_eq_finrank_residueField]
    exact Module.finrank_mul_finrank (ResidueField F) (ResidueField I) (ResidueField K)
  exact mul_eq_one.mp (hmul.trans hres)

/-- **Paper Lemma 9.32 (`O:G:lower`).** Both endpoints of the actual primitive
compatible pair have conductor at least one plus their lower and upper breaks.

The fields and breaks are the constructed `OddTotalBreakData`; `hne` is the
same distinguished lower norm-subgroup separation used by `Characters.conjugacy`.
The characters are arbitrary continuous group quasi-characters, with their exact
FML multiplicative conductors. In particular no unitarity, characteristic-zero,
Artin--Schreier coordinate, or exact commutator coefficient hypothesis is imposed.
The conjugate quotients and their nontrivial commutator values are constructed
inside the proof from the compatible pair and its failure to descend. -/
theorem lower {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1)
    (D : Total.OddTotalBreakData (F := F) (K := K) hp hG)
    (hne : Ramification.intermediateNormRange D.B₁ ≠
      Ramification.intermediateNormRange D.B₂) :
    letI := Basic.intermediateFieldValuativeRel D.B₁
    letI := Basic.intermediateFieldTopology D.B₁
    letI := Basic.intermediateField_localField D.B₁
    letI := Basic.intermediateField_lowerValuativeExtension D.B₁
    letI := Basic.intermediateField_upperValuativeExtension D.B₁
    letI := Basic.intermediateFieldValuativeRel D.B₂
    letI := Basic.intermediateFieldTopology D.B₂
    letI := Basic.intermediateField_localField D.B₂
    letI := Basic.intermediateField_lowerValuativeExtension D.B₂
    letI := Basic.intermediateField_upperValuativeExtension D.B₂
    ∀ (ψ₁ : ContinuousQuasiChar D.B₁) (ψ₂ : ContinuousQuasiChar D.B₂)
      (ψB : ContinuousQuasiChar K) (a₁ a₂ : ℕ),
      normQuasiChar D.B₁ K ψ₁ = ψB → normQuasiChar D.B₂ K ψ₂ = ψB →
      (¬ ∃ χ : ContinuousQuasiChar F, normQuasiChar F K χ = ψB) →
      IsMultiplicativeConductor D.B₁ ψ₁ a₁ →
      IsMultiplicativeConductor D.B₂ ψ₂ a₂ →
      1 + D.t + D.tPrime ≤ a₁ ∧ 1 + D.t₂ + D.t ≤ a₂ := by
  letI := Basic.intermediateFieldValuativeRel D.B₁
  letI := Basic.intermediateFieldTopology D.B₁
  letI := Basic.intermediateField_localField D.B₁
  letI := Basic.intermediateField_lowerValuativeExtension D.B₁
  letI := Basic.intermediateField_upperValuativeExtension D.B₁
  letI := Basic.intermediateFieldValuativeRel D.B₂
  letI := Basic.intermediateFieldTopology D.B₂
  letI := Basic.intermediateField_localField D.B₂
  letI := Basic.intermediateField_lowerValuativeExtension D.B₂
  letI := Basic.intermediateField_upperValuativeExtension D.B₂
  intro ψ₁ ψ₂ ψB a₁ a₂ hc₁ hc₂ hprimitive ha₁ ha₂
  have hdata₁ := Basic.intermediateField_tower_compatible hp hG D.B₁ D.degree_B₁
  have hdata₂ := Basic.intermediateField_tower_compatible hp hG D.B₂ D.degree_B₂
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F D.B₁
    hdata₁.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension D.B₁ K
    hdata₁.2.2.2.2.2.2.2.2.2.2.2.2
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F D.B₂
    hdata₂.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension D.B₂ K
    hdata₂.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨C₁⟩, ⟨C₂⟩, _⟩ := Characters.conjugacy hp hG D.B₁ D.B₂
    D.degree_B₁ D.degree_B₂ hne ψ₁ ψ₂ ψB hc₁ hc₂ hprimitive
  have hbreaks₁ : PrimeCyclicExtension.IsLowerBreak F D.B₁ D.t ∧
      PrimeCyclicExtension.IsLowerBreak D.B₁ K D.tPrime := D.B₁_breaks
  have hbreaks₂ : PrimeCyclicExtension.IsLowerBreak F D.B₂ D.t₂ ∧
      PrimeCyclicExtension.IsLowerBreak D.B₂ K D.t := D.B₂_breaks
  have hr₁ := intermediate_residueDegrees_eq_one D.B₁ hres
  have hr₂ := intermediate_residueDegrees_eq_one D.B₂ hres
  have htPrime : 0 < D.tPrime := by
    rw [D.tPrime_eq]
    exact Nat.add_pos_left D.t_pos _
  exact ⟨lower_of_conjugateTwistData C₁ hbreaks₁.1 hbreaks₁.2 htPrime hr₁.1 hr₁.2 ha₁,
    lower_of_conjugateTwistData C₂ hbreaks₂.1 hbreaks₂.2 D.t_pos hr₂.1 hr₂.2 ha₂⟩

end Diamond
end
end LanglandsSecondMainLemma.Odd.Conductors
