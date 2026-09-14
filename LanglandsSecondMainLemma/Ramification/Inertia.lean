import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Ramification.InertiaCoefficients

/-!
# Ramification / Inertia

This file completes Paper Lemma D.2.  The preceding two files construct the genuine residue
action and its quotient, the actual inertia fixed field, and the multiplicative and additive
ramification coefficients.  Here we assemble those results and prove the two compatibility
statements not contained in the coefficient construction:

* a lift of the `q_F`-power residue Frobenius acts on `I / G₁` by the `q_F`-power map;
* under the canonical equivalence `H ≃ Gal(K / Kᴴ)`, the lower group over `Kᴴ` is exactly
  `H ∩ G_j`.

The latter equality is proved directly from FML's defining integral congruences.  In particular,
both sides use the same normalized order on the top field `K`; no rescaled intermediate-field
valuation is introduced.
-/

namespace LanglandsSecondMainLemma.Ramification

open LanglandsFirstMainLemma

noncomputable section

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]
variable [IsGalois F K]

/-- Lower numbering is unchanged on passage from `K/F` to `K/Kᴴ`.

The right side is the group-theoretic intersection `H ∩ G_j`, expressed as a comap to `H`.
The left side transports the lower group for `K/Kᴴ` back along Mathlib's canonical equivalence
`H ≃ Gal(K/Kᴴ)`.  Unfolding membership on both sides leaves literally the same congruence in
the normalized order of `K`. -/
theorem lowerRamificationGroup_fixedField
    (H : Subgroup Gal(K/F)) (j : ℤ) :
    let E := IntermediateField.fixedField H
    letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E
    letI : TopologicalSpace E := Basic.intermediateFieldTopology E
    letI : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E
    letI : ValuativeExtension E K := Basic.intermediateField_upperValuativeExtension E
    (lowerRamificationGroup E K j).comap
        (IntermediateField.subgroupEquivAlgEquiv H).toMonoidHom =
      (lowerRamificationGroup F K j).comap H.subtype := by
  dsimp only
  let E := IntermediateField.fixedField H
  letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E
  letI : TopologicalSpace E := Basic.intermediateFieldTopology E
  letI : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E
  letI : ValuativeExtension E K := Basic.intermediateField_upperValuativeExtension E
  ext σ
  simp only [Subgroup.mem_comap]
  rw [mem_lowerRamificationGroup, mem_lowerRamificationGroup]
  rfl

/-- The tame coefficient does not depend on the uniformizer used to compute it.

Writing `ρ = uπ`, the quotient `u` has order zero.  Inertia fixes its residue, so
`σ(u) / u` is congruent to one at depth one.  Multiplying by `σ(π) / π` proves equality of the
two reduced tame ratios. -/
theorem tameResidue_uniformizer_independent
    (σ : lowerRamificationGroup F K 0) {π ρ : K}
    (hπ : (ValuativeRel.valuation K).IsUniformizer π)
    (hρ : (ValuativeRel.valuation K).IsUniformizer ρ) :
    lowerRamificationTameResidue F K σ π hπ =
      lowerRamificationTameResidue F K σ ρ hρ := by
  let u : K := ρ / π
  have huord : ord K u = 0 := by
    dsimp only [u]
    rw [ord_div, ord_uniformizer K hρ, ord_uniformizer K hπ]
    simp
  have hu0 : u ≠ 0 := by
    intro hu
    rw [hu] at huord
    simp at huord
  have huinvord : ord K u⁻¹ = 0 := by
    rw [ord_inv, huord]
    simp
  let uO : ringOfIntegers K :=
    ⟨u, (ord_nonneg_iff_mem_integer K u).1 (huord ▸ le_rfl)⟩
  have hσu : CongruentAtDepth 1 ((σ : Gal(K/F)) u) u := by
    simpa only [uO, zero_add] using
      (mem_lowerRamificationGroup F K (σ : Gal(K/F)) 0).1 σ.prop uO
  have hunit : CongruentAtDepth 1
      ((σ : Gal(K/F)) u * u⁻¹) 1 := by
    simpa [hu0] using hσu.mul_right
      (show 0 ≤ ord K u⁻¹ by rw [huinvord])
  let rπ : K := (σ : Gal(K/F)) π / π
  have hrπord : ord K rπ = 0 := by
    dsimp only [rπ]
    rw [ord_div, ord_galoisConjugate, ord_uniformizer K hπ]
    simp
  have hratio : CongruentAtDepth 1
      ((σ : Gal(K/F)) ρ / ρ) ((σ : Gal(K/F)) π / π) := by
    have h := hunit.mul_right (show 0 ≤ ord K rπ by rw [hrπord])
    rw [one_mul] at h
    convert h using 1
    dsimp only [u, rπ]
    rw [map_div₀]
    field_simp [hπ.ne_zero, hρ.ne_zero]
  unfold lowerRamificationTameResidue
  rw [reduce_eq_reduce_iff]
  exact hratio.symm

/-- The canonical arithmetic Frobenius of the actual residue extension, namely the
`|k_F|`-power automorphism. -/
noncomputable def residueFrobenius :
    Gal(ResidueField K / ResidueField F) := by
  letI : Fintype (ResidueField F) := residueFieldFintype F
  letI : Module.Finite (ResidueField F) (ResidueField K) :=
    Module.Finite.of_finite
  exact FiniteField.frobeniusAlgEquivOfAlgebraic
    (ResidueField F) (ResidueField K)

@[simp]
theorem residueFrobenius_apply (x : ResidueField K) :
    residueFrobenius (F := F) (K := K) x = x ^ residueCard F := by
  letI : Fintype (ResidueField F) := residueFieldFintype F
  simp [residueFrobenius, residueCard]

/-- Conjugation by an element of the full Galois group, restricted to inertia.  Normality is
proved by FML directly from the integral congruence definition of the lower groups. -/
noncomputable def conjugateInertia
    (φ : Gal(K/F)) (σ : lowerRamificationGroup F K 0) :
    lowerRamificationGroup F K 0 :=
  ⟨φ * (σ : Gal(K/F)) * φ⁻¹,
    (lowerRamificationGroup_normal F K 0).conj_mem
      (σ : Gal(K/F)) σ.prop φ⟩

@[simp]
theorem conjugateInertia_coe
    (φ : Gal(K/F)) (σ : lowerRamificationGroup F K 0) :
    (conjugateInertia φ σ : Gal(K/F)) =
      φ * (σ : Gal(K/F)) * φ⁻¹ :=
  rfl

/-- A lift of residue Frobenius acts on the multiplicative tame coefficient by the
`q_F`-power map. -/
theorem tameInertiaHom_conjugate
    (φ : Gal(K/F)) (σ : lowerRamificationGroup F K 0)
    (hφ : residueAction (F := F) (K := K) φ =
      residueFrobenius (F := F) (K := K)) :
    tameInertiaHom (F := F) (K := K) (conjugateInertia φ σ) =
      tameInertiaHom (F := F) (K := K) σ ^ residueCard F := by
  let π : K := inertiaUniformizer (F := F) (K := K)
  let hπ : (ValuativeRel.valuation K).IsUniformizer π :=
    inertiaUniformizer_isUniformizer (F := F) (K := K)
  let ρ : K := φ.symm π
  have hρ : (ValuativeRel.valuation K).IsUniformizer ρ := by
    rw [← ord_eq_one_iff_isUniformizer K, ord_galoisConjugate,
      ord_uniformizer K hπ]
  let rρ := lowerRamificationTameRatio F K σ ρ hρ
  let τ := conjugateInertia φ σ
  let rτ := lowerRamificationTameRatio F K τ π hπ
  have hratio : (rτ : K) = φ (rρ : K) := by
    dsimp only [rτ, rρ, τ, ρ]
    simp only [coe_lowerRamificationTameRatio, conjugateInertia_coe,
      AlgEquiv.mul_apply, map_div₀]
    simp
  have hreduce :
      lowerRamificationTameResidue F K τ π hπ =
        residueAction (F := F) (K := K) φ
          (lowerRamificationTameResidue F K σ ρ hρ) := by
    unfold lowerRamificationTameResidue
    change residueMap K
        ⟨(rτ : K), (mem_lattice_zero_iff K).1 rτ.prop⟩ =
      residueAction (F := F) (K := K) φ
        (residueMap K
          ⟨(rρ : K), (mem_lattice_zero_iff K).1 rρ.prop⟩)
    rw [residueAction_apply_residue]
    apply congrArg (residueMap K)
    apply Subtype.ext
    exact hratio
  have hindependent :
      lowerRamificationTameResidue F K σ ρ hρ =
        lowerRamificationTameResidue F K σ π hπ :=
    tameResidue_uniformizer_independent σ hρ hπ
  apply Units.ext
  change lowerRamificationTameResidue F K τ π hπ =
    lowerRamificationTameResidue F K σ π hπ ^ residueCard F
  rw [hreduce, hφ, hindependent, residueFrobenius_apply]

/-- A lift of residue Frobenius conjugates the actual tame inertia quotient `I/G₁` by the
`q_F`-power map. -/
theorem tameInertiaQuotient_conjugate
    (φ : Gal(K/F)) (σ : lowerRamificationGroup F K 0)
    (hφ : residueAction (F := F) (K := K) φ =
      residueFrobenius (F := F) (K := K)) :
    lowerRamificationGradedMk F K 0 (conjugateInertia φ σ) =
      (lowerRamificationGradedMk F K 0 σ) ^ residueCard F := by
  rw [← map_pow]
  apply (lowerRamificationQuotientMk_eq_iff F K
    (show (0 : ℤ) ≤ 1 by omega)
    (conjugateInertia φ σ) (σ ^ residueCard F)).2
  apply (tameInertiaHom_eq_one_iff (F := F) (K := K)
    (conjugateInertia φ σ / σ ^ residueCard F)).1
  rw [map_div, map_pow,
    tameInertiaHom_conjugate (F := F) (K := K) φ σ hφ]
  simp

/-- The residue-action quotient is cyclic.  The proof transports finite-field cyclicity across
the genuine quotient equivalence constructed in `UnramifiedPart`. -/
theorem residueActionQuotient_cyclic :
    IsCyclic (Gal(K/F) ⧸ inertiaSubgroup (F := F) (K := K)) := by
  letI : Module.Finite (ResidueField F) (ResidueField K) :=
    Module.Finite.of_finite
  letI : IsCyclic Gal(ResidueField K / ResidueField F) := inferInstance
  exact isCyclic_of_injective
    (residueActionQuotientEquiv (F := F) (K := K)).toMonoidHom
    (residueActionQuotientEquiv (F := F) (K := K)).injective

/-- The actual inertia fixed field is the maximal unramified subextension constructed in
`UnramifiedPart`: it is Galois over `F`, has ramification index one, and has the full residue
degree of `K/F`. -/
theorem inertiaFixedField_unramified :
    let E := IntermediateField.fixedField
      (inertiaSubgroup (F := F) (K := K))
    letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E
    letI : TopologicalSpace E := Basic.intermediateFieldTopology E
    letI : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E
    letI : ValuativeExtension F E := Basic.intermediateField_lowerValuativeExtension E
    IsGalois F E ∧ ramificationIndex F E = 1 ∧
      residueDegree F E = residueDegree F K := by
  obtain ⟨a, P, hPmonic, hPred, hprimitive, haRoot,
      hfixed, hGalois, hdegree, hramification, hresidue⟩ :=
    maximalUnramified_fixedField (F := F) (K := K)
  dsimp only
  rw [← hfixed]
  exact ⟨hGalois, hramification, hresidue⟩

/-- **Paper Lemma D.2 (inertia, tame action, and subgroup numbering).**

For a finite Galois extension of actual nonarchimedean local fields, this theorem packages:

* the quotient induced by the genuine residue action and its cyclicity;
* the equality `I = G₀` and the unramified inertia fixed field;
* cyclic prime-to-`p` tame inertia and `p`-primary wild inertia;
* an actual Frobenius lift whose conjugation action on `I/G₁` is `q_F`th power;
* the lower-numbering rule `H_j = H ∩ G_j` for every subgroup and every `j ≥ 0`.
-/
theorem inertia :
    (∃ e : Gal(K/F) ⧸ inertiaSubgroup (F := F) (K := K) ≃*
        Gal(ResidueField K / ResidueField F),
      ∀ σ : Gal(K/F),
        e (QuotientGroup.mk σ) = residueAction (F := F) (K := K) σ) ∧
    IsCyclic (Gal(K/F) ⧸ inertiaSubgroup (F := F) (K := K)) ∧
    inertiaSubgroup (F := F) (K := K) = lowerRamificationGroup F K 0 ∧
    (let E := IntermediateField.fixedField
        (inertiaSubgroup (F := F) (K := K));
      letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E;
      letI : TopologicalSpace E := Basic.intermediateFieldTopology E;
      letI : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E;
      letI : ValuativeExtension F E := Basic.intermediateField_lowerValuativeExtension E;
      IsGalois F E ∧ ramificationIndex F E = 1 ∧
        residueDegree F E = residueDegree F K) ∧
    (IsCyclic (LowerRamificationGraded F K 0) ∧
      Nat.Coprime (Nat.card (LowerRamificationGraded F K 0))
        (residueCharacteristic F)) ∧
    IsPGroup (residueCharacteristic F) (lowerRamificationGroup F K 1) ∧
    (∃ φ : Gal(K/F),
      residueAction (F := F) (K := K) φ =
          residueFrobenius (F := F) (K := K) ∧
        ∀ σ : lowerRamificationGroup F K 0,
          lowerRamificationGradedMk F K 0 (conjugateInertia φ σ) =
            (lowerRamificationGradedMk F K 0 σ) ^ residueCard F) ∧
    ∀ (H : Subgroup Gal(K/F)) (j : ℤ), 0 ≤ j →
      let E := IntermediateField.fixedField H;
      letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E;
      letI : TopologicalSpace E := Basic.intermediateFieldTopology E;
      letI : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E;
      letI : ValuativeExtension E K := Basic.intermediateField_upperValuativeExtension E;
      (lowerRamificationGroup E K j).comap
          (IntermediateField.subgroupEquivAlgEquiv H).toMonoidHom =
        (lowerRamificationGroup F K j).comap H.subtype := by
  refine ⟨?_, residueActionQuotient_cyclic (F := F) (K := K),
    inertiaSubgroup_eq_lowerRamificationGroup_zero (F := F) (K := K),
    inertiaFixedField_unramified (F := F) (K := K),
    tameInertia_cyclic (F := F) (K := K),
    wildInertia_isPGroup (F := F) (K := K), ?_, ?_⟩
  · refine ⟨residueActionQuotientEquiv (F := F) (K := K), ?_⟩
    exact residueActionQuotientEquiv_mk (F := F) (K := K)
  · obtain ⟨φ, hφ⟩ := residueAction_surjective
      (F := F) (K := K) (residueFrobenius (F := F) (K := K))
    refine ⟨φ, hφ, ?_⟩
    exact fun σ =>
      tameInertiaQuotient_conjugate (F := F) (K := K) φ σ hφ
  · intro H j _hj
    exact lowerRamificationGroup_fixedField (F := F) (K := K) H j

end

end LanglandsSecondMainLemma.Ramification
