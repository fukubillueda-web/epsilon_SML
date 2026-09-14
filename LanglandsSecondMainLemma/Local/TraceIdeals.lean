import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Basic.Fields
import LanglandsSecondMainLemma.Basic.NormTrace
import LanglandsSecondMainLemma.Local.Different

/-!
# Local / Trace Ideals

Blueprint: `blueprint/tasks/Local/TraceIdeals.md`.
Paper: (U:trace-ideal), lines 339--369, especially the inverse-different
argument at lines 345--352; see also lines 8668--8720.

For an arbitrary finite separable extension of nonarchimedean local fields,
this file defines the different exponent as the normalized upper-field depth
of Mathlib's genuine `differentIdeal`.  The inverse-different identity then
gives the trace dual at depth zero, scaling gives the dual of every
integer-indexed fractional lattice, and comparison of the two principal
annihilator lattices gives the exact trace image.

The source-facing theorems require separability, not Galoisness, and choose no
uniformizer or monogenic generator.  A separate theorem identifies the
ideal-theoretic exponent with FML's lower-ramification `differentExponent` in
the totally ramified Galois setting where the accepted bridge applies.  All
lattice and conductor exponents remain in `ℤ`, including negative depths.
-/

namespace LanglandsSecondMainLemma.Local

open LanglandsFirstMainLemma
open scoped Pointwise

noncomputable section

attribute [local instance] FractionRing.liftAlgebra

private theorem span_singleton_eq_smul_lattice_zero
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (a : E) :
    (ringOfIntegers E) ∙ a = a • lattice E 0 := by
  rw [lattice_zero, Submodule.one_eq_span]
  rw [← Submodule.span_singleton_mul]
  rw [← Submodule.one_eq_span, mul_one]

/-- The normalized upper-field valuation of the genuine different ideal.

This definition is available for every finite extension of local fields.  The
separability hypothesis enters the theorems identifying the different with
the inverse trace dual, not the definition of its ideal-theoretic depth. -/
noncomputable def differentIdealExponent
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] : ℤ :=
  (ord K (algebraMap (ringOfIntegers K) K
    (Submodule.IsPrincipal.generator
      (differentIdeal (ringOfIntegers F) (ringOfIntegers K))))).untop₀

theorem differentIdeal_eq_lattice
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [Algebra.IsSeparable F K] :
    IsLocalization.coeSubmodule K
        (differentIdeal (ringOfIntegers F) (ringOfIntegers K)) =
      lattice K (differentIdealExponent F K) := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  letI : IsIntegralClosure (ringOfIntegers K) (ringOfIntegers F) K :=
    ringOfIntegers_isIntegralClosure F K
  letI : Algebra.IsSeparable
      (FractionRing (ringOfIntegers F))
      (FractionRing (ringOfIntegers K)) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv (ringOfIntegers F) F).symm.toRingEquiv
      (FractionRing.algEquiv (ringOfIntegers K) K).symm.toRingEquiv ?_
    ext x
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv (ringOfIntegers F) F).symm
      (FractionRing.algEquiv (ringOfIntegers K) K).symm x
  let I : Ideal (ringOfIntegers K) :=
    differentIdeal (ringOfIntegers F) (ringOfIntegers K)
  let d : ringOfIntegers K := Submodule.IsPrincipal.generator I
  have hI : Ideal.span ({d} : Set (ringOfIntegers K)) = I :=
    Ideal.span_singleton_generator I
  have hIne : I ≠ ⊥ := by
    exact differentIdeal_ne_bot
  have hd : d ≠ 0 := by
    intro hd
    apply hIne
    rw [← hI, hd]
    simp
  have hdK : algebraMap (ringOfIntegers K) K d ≠ 0 := by
    rw [congrFun (Algebra.coe_algebraMap_ofSubsemiring
      (ringOfIntegers K)) d]
    exact Subtype.coe_ne_coe.mpr hd
  have hord : ord K (algebraMap (ringOfIntegers K) K d) =
      (differentIdealExponent F K : WithTop ℤ) := by
    change ord K (algebraMap (ringOfIntegers K) K d) =
      ((ord K (algebraMap (ringOfIntegers K) K d)).untop₀ : WithTop ℤ)
    exact (WithTop.coe_untop₀_of_ne_top
      ((ord_ne_top_iff K).2 hdK)).symm
  calc
    IsLocalization.coeSubmodule K
        (differentIdeal (ringOfIntegers F) (ringOfIntegers K)) =
        IsLocalization.coeSubmodule K I := rfl
    _ = IsLocalization.coeSubmodule K
        (Ideal.span ({d} : Set (ringOfIntegers K))) := congrArg _ hI.symm
    _ = (ringOfIntegers K) ∙ algebraMap (ringOfIntegers K) K d :=
      IsLocalization.coeSubmodule_span_singleton K d
    _ = algebraMap (ringOfIntegers K) K d • lattice K 0 :=
      span_singleton_eq_smul_lattice_zero K _
    _ = lattice K (differentIdealExponent F K) :=
      lattice_smul_zero_of_ord_eq K _ _ hord

/-- The ideal-theoretic exponent agrees with FML's numerical Hilbert-sum
exponent for a totally ramified Galois extension.  The generating uniformizer
needed by the accepted ideal/numerical bridge is constructed internally from
the genuine extension; it is not a hypothesis of this theorem. -/
theorem differentIdealExponent_eq_fml
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (hres : residueDegree F K = 1) :
    differentIdealExponent F K = (differentExponent F K : ℤ) := by
  obtain ⟨piK, hpiK, hgen⟩ := monogenicUniformizer F K hres
  have hideal : IsLocalization.coeSubmodule K
      (differentIdeal (ringOfIntegers F) (ringOfIntegers K)) =
      lattice K (differentIdealExponent F K) :=
    differentIdeal_eq_lattice F K
  have hfml : IsLocalization.coeSubmodule K
      (differentIdeal (ringOfIntegers F) (ringOfIntegers K)) =
      lattice K (differentExponent F K : ℤ) :=
    coeSubmodule_differentIdeal_eq_lattice F K piK hpiK hgen
  exact (lattice_eq_lattice_iff K).1 (hideal.symm.trans hfml)

/-- The inverse different is the integral trace dual, expressed at the
canonical ideal-theoretic different depth. -/
private theorem traceDual_lattice_zero_from_different
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [Algebra.IsSeparable F K] :
    Submodule.traceDual (ringOfIntegers F) F (lattice K 0) =
      lattice K (-differentIdealExponent F K) := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  letI : IsIntegralClosure (ringOfIntegers K) (ringOfIntegers F) K :=
    ringOfIntegers_isIntegralClosure F K
  let D : ℤ := differentIdealExponent F K
  obtain ⟨delta, hdelta⟩ := exists_ord_eq K D
  have hdiffSubmodule :
      IsLocalization.coeSubmodule K
          (differentIdeal (ringOfIntegers F) (ringOfIntegers K)) =
        lattice K D := by
    exact differentIdeal_eq_lattice F K
  have hdiffFractional :
      (differentIdeal (ringOfIntegers F) (ringOfIntegers K) :
          FractionalIdeal (nonZeroDivisors (ringOfIntegers K)) K) =
        FractionalIdeal.spanSingleton
          (nonZeroDivisors (ringOfIntegers K)) delta := by
    apply FractionalIdeal.coeToSubmodule_injective
    have hspanSubmodule : IsLocalization.coeSubmodule K
        (differentIdeal (ringOfIntegers F) (ringOfIntegers K)) =
        (ringOfIntegers K) ∙ delta := by
      rw [hdiffSubmodule, span_singleton_eq_smul_lattice_zero K,
        lattice_smul_zero_of_ord_eq K delta D hdelta]
    simpa only [FractionalIdeal.coe_coeIdeal,
      FractionalIdeal.coe_spanSingleton] using hspanSubmodule
  have hinvDual :
      (FractionalIdeal.dual (ringOfIntegers F) F
          (1 : FractionalIdeal
            (nonZeroDivisors (ringOfIntegers K)) K))⁻¹ =
        FractionalIdeal.spanSingleton
          (nonZeroDivisors (ringOfIntegers K)) delta := by
    rw [← hdiffFractional]
    exact (coeIdeal_differentIdeal
      (ringOfIntegers F) F K (ringOfIntegers K)).symm
  have hdualFractional :
      FractionalIdeal.dual (ringOfIntegers F) F
          (1 : FractionalIdeal
            (nonZeroDivisors (ringOfIntegers K)) K) =
        (FractionalIdeal.spanSingleton
          (nonZeroDivisors (ringOfIntegers K)) delta)⁻¹ := by
    apply inv_involutive.injective
    simpa only [inv_inv] using hinvDual
  have hdeltaInv : ord K delta⁻¹ = ((-D : ℤ) : WithTop ℤ) := by
    rw [ord_inv, hdelta]
    norm_num
  rw [lattice_zero]
  have hdualSubmodule := congrArg
    (fun I : FractionalIdeal (nonZeroDivisors (ringOfIntegers K)) K ↦
      (I : Submodule (ringOfIntegers K) K)) hdualFractional
  rw [FractionalIdeal.coe_dual_one,
    FractionalIdeal.spanSingleton_inv,
    FractionalIdeal.coe_spanSingleton] at hdualSubmodule
  rw [hdualSubmodule, span_singleton_eq_smul_lattice_zero K,
    lattice_smul_zero_of_ord_eq K delta⁻¹ (-D) hdeltaInv]

/-- Scaling the inverse different gives the trace dual of every fractional
lattice, at arbitrary integer depth. -/
private theorem traceDual_lattice_from_different
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [Algebra.IsSeparable F K]
    (a : ℤ) :
    Submodule.traceDual (ringOfIntegers F) F (lattice K a) =
      lattice K (-a - differentIdealExponent F K) := by
  let D : ℤ := differentIdealExponent F K
  have hbase (z : K) :
      (∀ x : K, x ∈ lattice K 0 → trace F K (z * x) ∈ lattice F 0) ↔
        z ∈ lattice K (-D) := by
    rw [← mem_traceDual_iff_trace_mul_mem_lattice_zero F K,
      traceDual_lattice_zero_from_different F K]
  ext z
  rw [mem_traceDual_iff_trace_mul_mem_lattice_zero F K]
  change (∀ x : K, x ∈ lattice K a → trace F K (z * x) ∈ lattice F 0) ↔
    z ∈ lattice K (-a - D)
  calc
    (∀ x : K, x ∈ lattice K a → trace F K (z * x) ∈ lattice F 0) ↔
        ∀ x : K, x ∈ lattice K a → z * x ∈ lattice K (-D) := by
      constructor
      · intro h x hx
        apply (hbase (z * x)).1
        intro y hy
        have hxy : x * y ∈ lattice K a := by
          simpa using mul_mem_lattice K hx hy
        simpa [mul_assoc] using h (x * y) hxy
      · intro h x hx
        have h' := (hbase (z * x)).2 (h x hx) 1 (by simp)
        simpa using h'
    _ ↔ z ∈ lattice K ((-D) - a) := mul_lattice_subset_iff K
    _ ↔ z ∈ lattice K (-a - D) := by ring_nf

private theorem ediv_lower_upper (n : ℤ) (e : ℕ) (he : 0 < e) :
    (n / (e : ℤ)) * (e : ℤ) ≤ n ∧
      n < (n / (e : ℤ) + 1) * (e : ℤ) := by
  have heZ : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  constructor
  · exact Int.ediv_mul_le n heZ.ne'
  · exact (Int.ediv_lt_iff_lt_mul heZ).mp (by omega)

/-- Inverse-different duality forces an exact trace image, not merely an
inclusion.  The contradiction in `hexact` is the paper's comparison of the
two principal annihilator ideals. -/
private theorem trace_lattice_image_of_traceDual
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (D a : ℤ)
    (hdual : Submodule.traceDual (ringOfIntegers F) F (lattice K a) =
      lattice K (-a - D)) :
    Submodule.map ((trace F K).restrictScalars (ringOfIntegers F))
        ((lattice K a).restrictScalars (ringOfIntegers F)) =
      lattice F ((a + D) / (ramificationIndex F K : ℤ)) := by
  let e : ℕ := ramificationIndex F K
  let c : ℤ := (a + D) / (e : ℤ)
  have he : 0 < e := ramificationIndex_pos F K
  have hbounds : c * (e : ℤ) ≤ a + D ∧
      a + D < (c + 1) * (e : ℤ) := by
    simpa only [c] using ediv_lower_upper (a + D) e he

  have htrace_mem : ∀ x : K, x ∈ lattice K a →
      trace F K x ∈ lattice F c := by
    intro x hx
    have hmul : ∀ y : F, y ∈ lattice F (-c) →
        trace F K x * y ∈ lattice F 0 := by
      intro y hy
      have hyK : algebraMap F K y ∈ lattice K (-a - D) := by
        rw [mem_lattice, ord_algebraMap]
        rw [mem_lattice] at hy
        have hsmul := nsmul_le_nsmul_right hy e
        have harith : -a - D ≤ (e : ℤ) * (-c) := by
          nlinarith [hbounds.1]
        apply (WithTop.coe_le_coe.mpr harith).trans
        have hcoe : (((e : ℤ) * (-c) : ℤ) : WithTop ℤ) =
            e • ((-c : ℤ) : WithTop ℤ) := by
          rw [← WithTop.coe_nsmul]
          congr 1
        rw [hcoe]
        exact hsmul
      have hyDual : algebraMap F K y ∈
          Submodule.traceDual (ringOfIntegers F) F (lattice K a) := by
        rw [hdual]
        exact hyK
      have htr :=
        (mem_traceDual_iff_trace_mul_mem_lattice_zero F K).1 hyDual x hx
      rw [← Algebra.smul_def, map_smul] at htr
      change y * trace F K x ∈ lattice F 0 at htr
      simpa only [mul_comm] using htr
    have hz := (mul_lattice_subset_iff F (c := trace F K x)
      (m := 0) (n := -c)).1 hmul
    simpa using hz

  have hexact : ∃ x : K, x ∈ lattice K a ∧
      ord F (trace F K x) = (c : WithTop ℤ) := by
    by_contra hnone
    have hnone' : ∀ x : K, x ∈ lattice K a →
        ord F (trace F K x) ≠ (c : WithTop ℤ) := by
      intro x hx heq
      exact hnone ⟨x, hx, heq⟩
    have htrace_deep : ∀ x : K, x ∈ lattice K a →
        trace F K x ∈ lattice F (c + 1) := by
      intro x hx
      rw [mem_lattice]
      have hc := htrace_mem x hx
      rw [mem_lattice] at hc
      have hne := hnone' x hx
      by_cases htop : ord F (trace F K x) = ⊤
      · simp [htop]
      have hlt : (c : WithTop ℤ) < ord F (trace F K x) :=
        lt_of_le_of_ne hc (Ne.symm hne)
      obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp htop
      rw [← hz] at hlt ⊢
      exact WithTop.coe_le_coe.mpr (by
        have hltZ : c < z := WithTop.coe_lt_coe.mp hlt
        omega)
    obtain ⟨y, hy⟩ := exists_ord_eq F (-(c + 1))
    have hyDual : algebraMap F K y ∈
        Submodule.traceDual (ringOfIntegers F) F (lattice K a) := by
      apply (mem_traceDual_iff_trace_mul_mem_lattice_zero F K).2
      intro x hx
      have hprod := mul_mem_lattice F
        (show y ∈ lattice F (-(c + 1)) by rw [mem_lattice, hy])
        (htrace_deep x hx)
      have htrace : trace F K (algebraMap F K y * x) =
          y * trace F K x := by
        rw [← Algebra.smul_def, map_smul]
        rfl
      rw [htrace]
      simpa using hprod
    have hyLat : algebraMap F K y ∈ lattice K (-a - D) := by
      rw [← hdual]
      exact hyDual
    have hordMap : ord K (algebraMap F K y) =
        (((e : ℤ) * (-(c + 1)) : ℤ) : WithTop ℤ) := by
      rw [ord_algebraMap, hy]
      simpa [e, mul_comm] using
        (WithTop.coe_nsmul (-(c + 1)) e).symm
    rw [mem_lattice, hordMap, WithTop.coe_le_coe] at hyLat
    have hstrict : (e : ℤ) * (-(c + 1)) < -a - D := by
      nlinarith [hbounds.2]
    exact (not_lt_of_ge hyLat) hstrict

  obtain ⟨x0, hx0, htrace0⟩ := hexact
  have htrace0ne : trace F K x0 ≠ 0 := by
    intro hz
    simp [hz] at htrace0
  change Submodule.map ((trace F K).restrictScalars (ringOfIntegers F))
      ((lattice K a).restrictScalars (ringOfIntegers F)) = lattice F c
  ext y
  constructor
  · intro hy
    rcases Submodule.mem_map.mp hy with ⟨x, hx, hxy⟩
    rw [← hxy]
    exact htrace_mem x hx
  · intro hy
    let z : F := (trace F K x0)⁻¹ * y
    have hz : z ∈ lattice F 0 := by
      rw [mem_lattice]
      dsimp only [z]
      rw [ord_mul, ord_inv, htrace0]
      rw [mem_lattice] at hy
      norm_num at hy ⊢
      have h := add_le_add_left hy (-(c : WithTop ℤ))
      simpa [add_assoc, add_comm, add_left_comm] using h
    let x : K := algebraMap F K z * x0
    have hx : x ∈ lattice K a := by
      have hzK : algebraMap F K z ∈ lattice K 0 := by
        rw [mem_lattice, ord_algebraMap]
        rw [mem_lattice] at hz
        have hsmul := nsmul_le_nsmul_right hz e
        simpa [e] using hsmul
      simpa [x] using mul_mem_lattice K hzK hx0
    apply Submodule.mem_map.mpr
    refine ⟨x, hx, ?_⟩
    change trace F K x = y
    rw [show x = z • x0 by simp [x, Algebra.smul_def], map_smul]
    change z * trace F K x0 = y
    dsimp only [z]
    field_simp

/-- **Trace-ideal floor formula** (Paper (U:trace-ideal)).

For every integer `j`, including negative values, the image of
`𝓅_K^j` under the actual field trace is
`𝓅_F^((j + D) / e)`, where `D` is the exponent of Mathlib's genuine
different ideal.  Division by the positive ramification index is Euclidean
integer division and hence the floor in the paper.  The submodule equality
states both containment and exact surjectivity. -/
theorem traceIdeal_eq
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [Algebra.IsSeparable F K]
    (j : ℤ) :
    Submodule.map ((trace F K).restrictScalars (ringOfIntegers F))
        ((lattice K j).restrictScalars (ringOfIntegers F)) =
      lattice F ((j + differentIdealExponent F K) /
        (ramificationIndex F K : ℤ)) := by
  exact trace_lattice_image_of_traceDual F K
    (differentIdealExponent F K) j
    (traceDual_lattice_from_different F K j)

/-- In the totally ramified Galois case, the general formula can be written
with FML's lower-ramification different exponent.  This corollary uses the
proved ideal/numerical bridge and introduces no chosen generator. -/
theorem traceIdeal_eq_fml
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (hres : residueDegree F K = 1) (j : ℤ) :
    Submodule.map ((trace F K).restrictScalars (ringOfIntegers F))
        ((lattice K j).restrictScalars (ringOfIntegers F)) =
      lattice F ((j + (differentExponent F K : ℤ)) /
        (ramificationIndex F K : ℤ)) := by
  rw [← differentIdealExponent_eq_fml F K hres]
  exact traceIdeal_eq F K j

/-- Exact trace images transport triviality on a whole upper lattice to
triviality on the corresponding lower lattice. -/
private theorem addCharTrivialOnLattice_trace_iff
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [Algebra.IsSeparable F K]
    (psi : ContinuousAddChar F) (a : ℤ) :
    AddCharTrivialOnLattice K psi.compTrace a ↔
      AddCharTrivialOnLattice F psi
        ((a + differentIdealExponent F K) /
          (ramificationIndex F K : ℤ)) := by
  constructor
  · intro h y hy
    have hyImage : y ∈ Submodule.map
        ((trace F K).restrictScalars (ringOfIntegers F))
        ((lattice K a).restrictScalars (ringOfIntegers F)) := by
      rw [traceIdeal_eq F K a]
      exact hy
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hyImage
    have hxone := h x hx
    change trace F K x = y at hxy
    rw [ContinuousAddChar.compTrace_apply, hxy] at hxone
    exact hxone
  · intro h x hx
    rw [ContinuousAddChar.compTrace_apply]
    apply h
    have hxImage : trace F K x ∈ Submodule.map
        ((trace F K).restrictScalars (ringOfIntegers F))
        ((lattice K a).restrictScalars (ringOfIntegers F)) :=
      Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    rw [traceIdeal_eq F K a] at hxImage
    exact hxImage

/-- **Additive conductor under trace** (Paper (U:trace-ideal)).

If `psi` has conductor `n` on `F`, its pullback by the actual field trace has
conductor `e * n + D` on `K`, where `D` is the ideal-theoretic different
exponent.  The proof uses triviality on the entire exact trace-image lattice,
not a single character value. -/
theorem additiveConductor_trace
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [Algebra.IsSeparable F K]
    {psi : ContinuousAddChar F} {n : ℤ}
    (hpsi : IsAdditiveConductor F psi n) :
    IsAdditiveConductor K psi.compTrace
      ((ramificationIndex F K : ℤ) * n +
        differentIdealExponent F K) := by
  let e : ℕ := ramificationIndex F K
  let D : ℤ := differentIdealExponent F K
  have he : 0 < e := ramificationIndex_pos F K
  have heZ : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  refine ⟨?_, ?_⟩
  · rw [addCharTrivialOnLattice_trace_iff F K]
    have hdepth : (-((e : ℤ) * n + D) + D) / (e : ℤ) = -n := by
      have he0 : (e : ℤ) ≠ 0 := ne_of_gt heZ
      rw [show -((e : ℤ) * n + D) + D = (e : ℤ) * (-n) by ring]
      exact Int.mul_ediv_cancel_left (-n) he0
    rw [hdepth]
    exact hpsi.trivial
  · intro a ha
    have hdown :=
      (addCharTrivialOnLattice_trace_iff F K psi a).1 ha
    have hmin : -n ≤ (a + D) / (e : ℤ) := hpsi.minimal _ hdown
    have hmul : (-n) * (e : ℤ) ≤ a + D :=
      (Int.le_ediv_iff_mul_le heZ).mp hmin
    change -((e : ℤ) * n + D) ≤ a
    nlinarith

/-- FML-numerical form of `additiveConductor_trace` for a totally ramified
Galois extension, obtained only after applying the ideal/numerical bridge. -/
theorem additiveConductor_trace_fml
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (hres : residueDegree F K = 1)
    {psi : ContinuousAddChar F} {n : ℤ}
    (hpsi : IsAdditiveConductor F psi n) :
    IsAdditiveConductor K psi.compTrace
      ((ramificationIndex F K : ℤ) * n +
        (differentExponent F K : ℤ)) := by
  rw [← differentIdealExponent_eq_fml F K hres]
  exact additiveConductor_trace F K hpsi

end

end LanglandsSecondMainLemma.Local
