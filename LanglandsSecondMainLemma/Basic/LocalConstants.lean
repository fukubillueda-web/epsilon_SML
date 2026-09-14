import LanglandsFirstMainLemma.Delta.Elementary
import LanglandsFirstMainLemma.Delta.FirstMainStatement
import LanglandsFirstMainLemma.Delta.LocalConstantRealization
import LanglandsFirstMainLemma.Main
import LanglandsSecondMainLemma.Basic.Characters

/-!
# Basic / Local Constants

Blueprint: `blueprint/tasks/Basic/LocalConstants.md`.
Paper: lines 277--337, especially `U:delta-definition` and `U:interface`.

This file exposes FML's canonical `localConstant` through its proved finite
realization.  The nontriviality of the additive character remains explicit,
and the supplied denominator belongs to the canonical exact-conductor
packages.  Since the theorem holds for every such denominator, it retains
FML's proved admissible-denominator independence.

It also proves the manuscript's change-of-variables identity for an actual
`F`-automorphism `σ` of a finite local-field extension `K/F`.  Conjugation has
the manuscript's orientation

`χ^σ(x) = χ(σ⁻¹ x)`.

FML proves that `σ` preserves normalized order but has no exported local-
constant automorphism theorem.  We first derive continuity from order
preservation, transport the unit filtration and its finite quotient, and then
reindex the representative-free finite Gauss sum.  No unitarity assumption is
made, and the depth-zero unit filtration is handled explicitly.
-/

namespace LanglandsSecondMainLemma.Basic

noncomputable section

open LanglandsFirstMainLemma

section FiniteRealization

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- The canonical FML local constant is its finite formula for a nontrivial
additive character and any genuinely admissible denominator for the canonical
exact-conductor packages.

The arbitrary `γ` is intentional: its subtype property is the exact order
condition from `U:delta-definition`, and FML's realization theorem has already
proved that changing this admissible denominator does not change the value. -/
theorem localConstant_eq_finite
    (χ : ContinuousQuasiChar E) (ψ : ContinuousAddChar E) (hψ : ψ ≠ 1)
    (γ : AdmissibleGamma E (canonicalLocalQuasiCharData E χ)
      (canonicalLocalAddCharData E ψ hψ)) :
    LanglandsFirstMainLemma.localConstant E χ ψ =
      deltaFinite (canonicalLocalQuasiCharData E χ)
        (canonicalLocalAddCharData E ψ hψ) γ :=
  LanglandsFirstMainLemma.localConstant_eq_deltaFinite E χ ψ hψ γ

end FiniteRealization

section Automorphism

variable (F K : Type*)
variable [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]

/-- An algebra automorphism of a finite local-field extension is continuous.

FML's `ord_galoisConjugate` says that it preserves normalized order.  The
integer valuation lattices form a neighborhood basis of zero, so continuity
follows at zero and hence everywhere from additivity. -/
private theorem continuous_galoisAutomorphism (σ : Gal(K/F)) : Continuous σ := by
  apply continuous_of_continuousAt_zero σ.toAlgHom.toAddMonoidHom
  change Filter.Tendsto (fun x : K => σ x) (nhds 0) (nhds (σ 0))
  rw [map_zero, (lattice_nhds_zero_hasBasis K).tendsto_right_iff]
  intro n _
  filter_upwards [(lattice_isOpen K n).mem_nhds (by simp)] with x hx
  change (n : WithTop ℤ) ≤ ord K (σ x)
  rw [ord_galoisConjugate]
  exact hx

/-- The continuous multiplicative equivalence underlying a local-field
automorphism. -/
private def galoisContinuousMulEquiv (σ : Gal(K/F)) : K ≃ₜ* K where
  __ := σ.toRingEquiv.toMulEquiv
  continuous_toFun := continuous_galoisAutomorphism F K σ
  continuous_invFun := continuous_galoisAutomorphism F K σ.symm

/-- The continuous action of a local-field automorphism on nonzero field
elements. -/
private def galoisUnitsContinuousMulEquiv (σ : Gal(K/F)) : Kˣ ≃ₜ* Kˣ :=
  Units.mapContinuousMulEquiv (galoisContinuousMulEquiv F K σ)

/-- Conjugation of a continuous quasi-character by an actual field
automorphism, with the orientation of manuscript line 311:
`χ^σ(x) = χ(σ⁻¹ x)`. -/
def conjugateQuasiChar (σ : Gal(K/F))
    (χ : ContinuousQuasiChar K) : ContinuousQuasiChar K :=
  χ.pullback (galoisUnitsContinuousMulEquiv F K σ).symm

/-- Pointwise form fixing the orientation of `conjugateQuasiChar`. -/
@[simp]
theorem conjugateQuasiChar_apply (σ : Gal(K/F))
    (χ : ContinuousQuasiChar K) (x : Kˣ) :
    conjugateQuasiChar F K σ χ x =
      χ (Units.map σ.symm.toRingEquiv.toMonoidHom x) := by
  rfl

/-- An automorphism preserves every unit-filtration layer.  The zero layer
uses preservation of order zero; positive layers use preservation of the
congruence with `1`. -/
@[simp]
private theorem galois_mem_unitFiltration_iff
    (σ : Gal(K/F)) (n : ℕ) (u : Kˣ) :
    Units.map σ.toRingEquiv.toMonoidHom u ∈ unitFiltration K n ↔
      u ∈ unitFiltration K n := by
  cases n with
  | zero =>
      simp only [mem_unitFiltration_zero, Units.coe_map]
      change ord K (σ (u : K)) = 0 ↔ ord K (u : K) = 0
      rw [ord_galoisConjugate]
  | succ n =>
      simp only [mem_unitFiltration_succ, Units.coe_map]
      change CongruentAtDepth ((n + 1 : ℕ) : ℤ) (σ (u : K)) 1 ↔ _
      simp only [CongruentAtDepth]
      have hmap : σ (u : K) - 1 = σ ((u : K) - 1) := by simp
      rw [hmap, ord_galoisConjugate]

/-- The action of an automorphism on a fixed unit-filtration layer. -/
private def galoisUnitFiltrationEquiv (σ : Gal(K/F)) (n : ℕ) :
    unitFiltration K n ≃* unitFiltration K n where
  toFun u := ⟨Units.map σ.toRingEquiv.toMonoidHom u,
    (galois_mem_unitFiltration_iff F K σ n u).2 u.property⟩
  invFun u := ⟨Units.map σ.symm.toRingEquiv.toMonoidHom u,
    (galois_mem_unitFiltration_iff F K σ.symm n u).2 u.property⟩
  left_inv u := by ext; simp
  right_inv u := by ext; simp
  map_mul' x y := by ext; simp

/-- Conjugating exact multiplicative-conductor data preserves the whole
exact conductor, including conductor zero. -/
private theorem conjugateQuasiChar_isConductor (σ : Gal(K/F))
    (χ : LocalQuasiCharData K) :
    IsMultiplicativeConductor K
      (conjugateQuasiChar F K σ χ.character) χ.conductor := by
  constructor
  · intro u hu
    rw [conjugateQuasiChar_apply]
    exact χ.isConductor.trivial _
      ((galois_mem_unitFiltration_iff F K σ.symm χ.conductor u).2 hu)
  · intro r hr
    apply χ.isConductor.minimal r
    intro u hu
    let uσ : Kˣ := Units.map σ.toRingEquiv.toMonoidHom u
    have huσ : uσ ∈ unitFiltration K r :=
      (galois_mem_unitFiltration_iff F K σ r u).2 hu
    have h := hr uσ huσ
    have huval : Units.map σ.symm.toRingEquiv.toMonoidHom uσ = u := by
      ext
      simp [uσ]
    rw [conjugateQuasiChar_apply, huval] at h
    exact h

/-- The exact-conductor package of a conjugated quasi-character. -/
private def conjugateLocalQuasiCharData (σ : Gal(K/F))
    (χ : LocalQuasiCharData K) : LocalQuasiCharData K where
  character := conjugateQuasiChar F K σ χ.character
  conductor := χ.conductor
  isConductor := conjugateQuasiChar_isConductor F K σ χ

@[simp]
private theorem conjugateLocalQuasiCharData_conductor (σ : Gal(K/F))
    (χ : LocalQuasiCharData K) :
    (conjugateLocalQuasiCharData F K σ χ).conductor = χ.conductor := rfl

/-- Transport an admissible denominator by the automorphism.  Its order is
unchanged, so it is admissible for the conjugated multiplicative data and the
unchanged additive data. -/
private def conjugateAdmissibleGamma (σ : Gal(K/F))
    (χ : LocalQuasiCharData K) (ψ : LocalAddCharData K)
    (γ : AdmissibleGamma K χ ψ) :
    AdmissibleGamma K (conjugateLocalQuasiCharData F K σ χ) ψ := by
  refine ⟨Units.map σ.toRingEquiv.toMonoidHom (γ : Kˣ), ?_⟩
  change ord K (σ (((γ : Kˣ) : K))) = _
  rw [ord_galoisConjugate, γ.property]
  rfl

/-- The automorphism of `U_K^0` maps its internal copy of `U_K^n` onto
itself. -/
private theorem galoisUnitFiltrationInside_map (σ : Gal(K/F)) (n : ℕ) :
    (unitFiltrationInside K (Nat.zero_le n)).map
        (galoisUnitFiltrationEquiv F K σ 0) =
      unitFiltrationInside K (Nat.zero_le n) := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    apply (mem_unitFiltrationInside K (Nat.zero_le n) _).2
    exact (galois_mem_unitFiltration_iff F K σ n (v : Kˣ)).2
      ((mem_unitFiltrationInside K (Nat.zero_le n) v).1 hv)
  · intro hu
    let v := (galoisUnitFiltrationEquiv F K σ 0).symm u
    refine ⟨v, ?_, ?_⟩
    · apply (mem_unitFiltrationInside K (Nat.zero_le n) v).2
      apply (galois_mem_unitFiltration_iff F K σ.symm n (u : Kˣ)).2
      exact (mem_unitFiltrationInside K (Nat.zero_le n) u).1 hu
    · exact (galoisUnitFiltrationEquiv F K σ 0).apply_symm_apply u

/-- Change of variables by `σ` on the actual finite quotient
`U_K^0 / U_K^n`. -/
private def galoisUnitFiltrationQuotientEquiv (σ : Gal(K/F)) (n : ℕ) :
    UnitFiltrationQuotient K 0 n (Nat.zero_le n) ≃*
      UnitFiltrationQuotient K 0 n (Nat.zero_le n) :=
  QuotientGroup.congr _ _ (galoisUnitFiltrationEquiv F K σ 0)
    (galoisUnitFiltrationInside_map F K σ n)

@[simp]
private theorem galoisUnitFiltrationQuotientEquiv_mk
    (σ : Gal(K/F)) (n : ℕ) (u : unitFiltration K 0) :
    galoisUnitFiltrationQuotientEquiv F K σ n
        (unitFiltrationQuotientMk K (Nat.zero_le n) u) =
      unitFiltrationQuotientMk K (Nat.zero_le n)
        (galoisUnitFiltrationEquiv F K σ 0 u) := by
  rfl

/-- Pointwise change of variables in the finite Gauss summand. -/
private theorem finiteGaussSummandRepresentative_conjugate
    (σ : Gal(K/F)) (χ : LocalQuasiCharData K) (ψ : LocalAddCharData K)
    (hψ : ∀ x : K, ψ.character (σ x) = ψ.character x)
    (γ : AdmissibleGamma K χ ψ) (u : unitFiltration K 0) :
    finiteGaussSummandRepresentative (conjugateLocalQuasiCharData F K σ χ) ψ
        (conjugateAdmissibleGamma F K σ χ ψ γ)
        (galoisUnitFiltrationEquiv F K σ 0 u) =
      finiteGaussSummandRepresentative χ ψ γ u := by
  rw [finiteGaussSummandRepresentative, finiteGaussSummandRepresentative]
  change (ψ.character
      (σ (((u : unitFiltration K 0) : Kˣ) : K) /
        σ (((γ : AdmissibleGamma K χ ψ) : Kˣ) : K)) : ℂ) *
      (χ.character (Units.map σ.symm.toRingEquiv.toMonoidHom
        (Units.map σ.toRingEquiv.toMonoidHom (u : Kˣ))) : ℂ)⁻¹ = _
  rw [← map_div₀, hψ]
  have hu : Units.map σ.symm.toRingEquiv.toMonoidHom
      (Units.map σ.toRingEquiv.toMonoidHom (u : Kˣ)) = (u : Kˣ) := by
    ext
    simp
  rw [hu]

/-- The representative-free summand commutes with the quotient change of
variables. -/
private theorem finiteGaussSummand_conjugate
    (σ : Gal(K/F)) (χ : LocalQuasiCharData K) (ψ : LocalAddCharData K)
    (hψ : ∀ x : K, ψ.character (σ x) = ψ.character x)
    (γ : AdmissibleGamma K χ ψ)
    (z : UnitFiltrationQuotient K 0 χ.conductor (Nat.zero_le _)) :
    finiteGaussSummand (conjugateLocalQuasiCharData F K σ χ) ψ
        (conjugateAdmissibleGamma F K σ χ ψ γ)
        (galoisUnitFiltrationQuotientEquiv F K σ χ.conductor z) =
      finiteGaussSummand χ ψ γ z := by
  obtain ⟨u, rfl⟩ :=
    unitFiltrationQuotientMk_surjective K (Nat.zero_le χ.conductor) z
  rw [galoisUnitFiltrationQuotientEquiv_mk]
  change finiteGaussSummandRepresentative
      (conjugateLocalQuasiCharData F K σ χ) ψ
        (conjugateAdmissibleGamma F K σ χ ψ γ)
        (galoisUnitFiltrationEquiv F K σ 0 u) =
    finiteGaussSummandRepresentative χ ψ γ u
  exact finiteGaussSummandRepresentative_conjugate F K σ χ ψ hψ γ u

/-- Reindexing the complete finite unit-quotient sum gives the same Gauss
sum. -/
private theorem finiteGaussSum_conjugate
    (σ : Gal(K/F)) (χ : LocalQuasiCharData K) (ψ : LocalAddCharData K)
    (hψ : ∀ x : K, ψ.character (σ x) = ψ.character x)
    (γ : AdmissibleGamma K χ ψ) :
    finiteGaussSum (conjugateLocalQuasiCharData F K σ χ) ψ
        (conjugateAdmissibleGamma F K σ χ ψ γ) =
      finiteGaussSum χ ψ γ := by
  letI := unitFiltrationQuotientFintype K (Nat.zero_le χ.conductor)
  unfold finiteGaussSum
  symm
  apply Fintype.sum_equiv
    (galoisUnitFiltrationQuotientEquiv F K σ χ.conductor).toEquiv
  intro z
  exact (finiteGaussSummand_conjugate F K σ χ ψ hψ γ z).symm

/-- Change of variables in the complete finite local constant, including its
nonunitary denominator factor. -/
private theorem deltaFinite_conjugate
    (σ : Gal(K/F)) (χ : LocalQuasiCharData K) (ψ : LocalAddCharData K)
    (hψ : ∀ x : K, ψ.character (σ x) = ψ.character x)
    (γ : AdmissibleGamma K χ ψ) :
    deltaFinite (conjugateLocalQuasiCharData F K σ χ) ψ
        (conjugateAdmissibleGamma F K σ χ ψ γ) =
      deltaFinite χ ψ γ := by
  rw [deltaFinite, deltaFinite, finiteGaussSum_conjugate F K σ χ ψ hψ γ]
  change (χ.character (Units.map σ.symm.toRingEquiv.toMonoidHom
      (Units.map σ.toRingEquiv.toMonoidHom (γ : Kˣ))) : ℂ) * _ = _
  have hγ : Units.map σ.symm.toRingEquiv.toMonoidHom
      (Units.map σ.toRingEquiv.toMonoidHom (γ : Kˣ)) = (γ : Kˣ) := by
    ext
    simp
  rw [hγ]

/-- The canonical FML local constant is invariant under an actual field
automorphism when the additive character is invariant.

The left character is the manuscript's `χ^σ = χ ∘ σ⁻¹`; `hψσ` is the exact
pointwise form of trace-invariance needed for the change of variables. -/
theorem localConstant_conjugate
    (σ : Gal(K/F)) (χ : ContinuousQuasiChar K) (ψ : ContinuousAddChar K)
    (hψ : ψ ≠ 1) (hψσ : ∀ x : K, ψ (σ x) = ψ x) :
    LanglandsFirstMainLemma.localConstant K
        (conjugateQuasiChar F K σ χ) ψ =
      LanglandsFirstMainLemma.localConstant K χ ψ := by
  let χData := canonicalLocalQuasiCharData K χ
  let ψData := canonicalLocalAddCharData K ψ hψ
  let γ : AdmissibleGamma K χData ψData :=
    Classical.choice (AdmissibleGamma.exists_admissible (F := K))
  let χσData := conjugateLocalQuasiCharData F K σ χData
  let γσ : AdmissibleGamma K χσData ψData :=
    conjugateAdmissibleGamma F K σ χData ψData γ
  calc
    LanglandsFirstMainLemma.localConstant K
        (conjugateQuasiChar F K σ χ) ψ =
        deltaFinite χσData ψData γσ := by
      exact localConstant_isDeltaFinite K χσData ψData γσ
    _ = deltaFinite χData ψData γ := by
      exact deltaFinite_conjugate F K σ χData ψData hψσ γ
    _ = LanglandsFirstMainLemma.localConstant K χ ψ := by
      exact (localConstant_isDeltaFinite K χData ψData γ).symm

end Automorphism

end

end LanglandsSecondMainLemma.Basic
