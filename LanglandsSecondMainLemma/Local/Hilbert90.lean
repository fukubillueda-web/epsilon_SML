import LanglandsSecondMainLemma.Basic.Fields
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-!
# Local / Hilbert90

Blueprint: `blueprint/tasks/Local/Hilbert90.md`.
Paper: Lemma C.1, `C:hilbert90` (lines 8583--8614).

For a finite Galois extension `E/F` and a specified generator `σ` of its Galois group, this
file identifies both classical kernels with the ranges of the correspondingly oriented
coboundary maps:

* the kernel of the actual norm on `Eˣ` is the range of `y ↦ y / σ(y)`;
* the kernel of the actual trace on `E` is the range of `y ↦ σ(y) - y`.

The multiplicative inclusion from the norm kernel uses Mathlib's Hilbert 90 theorem. The
additive equality is proved by the paper's dimension argument. In particular, the generator
hypothesis identifies the fixed space of `σ` with the base field even when the characteristic
divides the extension degree.
-/

namespace LanglandsSecondMainLemma.Local

open LanglandsFirstMainLemma

noncomputable section

section Coboundaries

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The multiplicative coboundary with the orientation used in Paper C.1:
`y ↦ y / σ(y)` on the unit group of `E`. -/
def multiplicativeCoboundary (σ : Gal(E/F)) : Eˣ →* Eˣ where
  toFun y := y / Units.map σ.toMonoidHom y
  map_one' := by simp
  map_mul' y z := by
    simp only [map_mul, div_eq_mul_inv, mul_inv_rev]
    ac_rfl

@[simp]
theorem multiplicativeCoboundary_apply (σ : Gal(E/F)) (y : Eˣ) :
    multiplicativeCoboundary σ y = y / Units.map σ.toMonoidHom y :=
  rfl

/-- The additive coboundary with the orientation used in Paper C.1:
`y ↦ σ(y) - y`. -/
def additiveCoboundary (σ : Gal(E/F)) : E →ₗ[F] E :=
  σ.toLinearMap - LinearMap.id

@[simp]
theorem additiveCoboundary_apply (σ : Gal(E/F)) (y : E) :
    additiveCoboundary σ y = σ y - y := by
  rfl

end Coboundaries

section CyclicExtension

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/-- **Cyclic Hilbert 90, in both forms** (Paper C.1, `C:hilbert90`).

Here `hσ` says that the specified automorphism `σ` generates the *actual* Galois group
`Gal(E/F)`. The first equality is on `Eˣ` and uses FML's actual unit norm
`normUnits F E`; its right-hand side is exactly the set of `y / σ(y)`. The second equality
uses FML's actual field trace `trace F E`; its right-hand side is exactly the set of
`σ(y) - y`.

The quotient and subtraction orientations are therefore the ones printed in the paper, not
the inverses or negatives sometimes used in equivalent formulations of Hilbert 90. -/
theorem hilbert90 [FiniteDimensional F E] [IsGalois F E]
    (σ : Gal(E/F)) (hσ : ∀ τ : Gal(E/F), τ ∈ Subgroup.zpowers σ) :
    (normUnits F E).ker = (multiplicativeCoboundary σ).range ∧
      (trace F E).ker = (additiveCoboundary σ).range := by
  letI : IsCyclic Gal(E/F) := ⟨σ, hσ⟩
  constructor
  · apply le_antisymm
    · intro x hx
      have hxField : Algebra.norm F (x : E) = 1 := by
        exact congrArg Units.val hx
      obtain ⟨y, hy⟩ := groupCohomology.exists_div_of_norm_eq_one
        (K := F) (L := E) (g := σ) hσ hxField
      refine ⟨y, ?_⟩
      apply Units.ext
      simpa using hy
    · rintro x ⟨y, rfl⟩
      change normUnits F E (y / Units.map σ.toMonoidHom y) = 1
      rw [map_div, div_eq_one]
      apply Units.ext
      change Algebra.norm F (y : E) = Algebra.norm F (σ (y : E))
      exact (Algebra.norm_eq_of_algEquiv σ (y : E)).symm
  · have hRange_le_ker :
        (additiveCoboundary σ).range ≤ (trace F E).ker := by
      rintro x ⟨y, rfl⟩
      change trace F E (σ y - y) = 0
      rw [map_sub, Algebra.trace_eq_of_algEquiv σ, sub_self]

    have hCoboundaryKer :
        (additiveCoboundary σ).ker = LinearMap.range (Algebra.linearMap F E) := by
      ext x
      constructor
      · intro hx
        have hxσ : σ x = x := by
          simpa only [LinearMap.mem_ker, additiveCoboundary_apply, sub_eq_zero] using hx
        have hxRange : x ∈ Set.range (algebraMap F E) := by
          rw [IsGalois.mem_range_algebraMap_iff_fixed]
          intro τ
          have hσStabilizes : σ ∈ MulAction.stabilizer Gal(E/F) x := by
            rw [MulAction.mem_stabilizer_iff]
            simpa [AlgEquiv.smul_def] using hxσ
          have hτStabilizes := (Subgroup.zpowers_le.mpr hσStabilizes) (hσ τ)
          rw [MulAction.mem_stabilizer_iff] at hτStabilizes
          simpa [AlgEquiv.smul_def] using hτStabilizes
        obtain ⟨a, ha⟩ := hxRange
        exact ⟨a, by simpa using ha⟩
      · intro hx
        rw [LinearMap.mem_range] at hx
        obtain ⟨a, rfl⟩ := hx
        rw [LinearMap.mem_ker, additiveCoboundary_apply, sub_eq_zero]
        exact σ.commutes a

    have hCoboundaryKerFinrank :
        Module.finrank F (additiveCoboundary σ).ker = 1 := by
      rw [hCoboundaryKer, LinearMap.finrank_range_of_inj]
      · simp
      · exact (algebraMap F E).injective

    have hTraceRange : LinearMap.range (trace F E) = ⊤ :=
      LinearMap.range_eq_top.mpr (Algebra.trace_surjective F E)

    have hCoboundaryRank :=
      LinearMap.finrank_range_add_finrank_ker (additiveCoboundary σ)
    have hTraceRank := LinearMap.finrank_range_add_finrank_ker (trace F E)
    rw [hCoboundaryKerFinrank] at hCoboundaryRank
    rw [hTraceRange] at hTraceRank
    simp only [finrank_top, Module.finrank_self] at hTraceRank

    apply (Submodule.eq_of_le_of_finrank_eq hRange_le_ker ?_).symm
    omega

end CyclicExtension

end

end LanglandsSecondMainLemma.Local
