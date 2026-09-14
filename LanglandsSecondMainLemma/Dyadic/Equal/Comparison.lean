import LanglandsFirstMainLemma.Delta.Elementary
import LanglandsFirstMainLemma.Delta.LocalConstantRealization
import LanglandsSecondMainLemma.Dyadic.Equal.UnequalBreaks
import LanglandsSecondMainLemma.Dyadic.Equal.EqualBreaks
import LanglandsSecondMainLemma.Dyadic.Equal.Intermediate
import LanglandsSecondMainLemma.Dyadic.Equal.HighComparison
import LanglandsSecondMainLemma.Characters.InducingChoice

/-!
# Dyadic / Equal / Comparison

Paper `D:EQ:main` and `D:EQ:total-complete`. Finite ideal duality and
compactness supply additive scaling without an extra character hypothesis.
The minimal, intermediate, and high conductor intervals cover all three
fields. The common-twist realization and stationary coefficients are
constructed from the actual family, and the third-field relabeling retains
the exact AS generators. Finally, constructed Laurent coordinates and
independence of inducing choices give `comparison` for arbitrary quadratic
intermediate fields of the genuine characteristic-two extension.
-/

namespace LanglandsSecondMainLemma.Dyadic.Equal

open LanglandsFirstMainLemma
open scoped BigOperators
noncomputable section

open private isCompact_lattice isOpen_lattice from
  LanglandsFirstMainLemma.LocalField.FiniteQuotients

section AdditiveScaling
variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Finite ideal duality realizes a character on any prescribed fractional
ideal, with all coefficients in one fixed compact lattice. -/
private theorem additiveScale_on_lattice (ψ₀ ψ : LocalAddCharData F)
    (r : ℤ) (hr : r ≤ -ψ.conductor) :
    ∃ c : F, c ∈ lattice F (-ψ₀.conductor + ψ.conductor) ∧
      ∀ x : F, x ∈ lattice F r → ψ₀.character (c * x) = ψ.character x := by
  let q := -ψ.conductor
  let M := -ψ₀.conductor
  have hΓ : ord F ((1 : Fˣ) : F) = ((M + ψ₀.conductor : ℤ) : WithTop ℤ) := by
    simp [M]
  have hΓ' : ord F ((1 : Fˣ) : F) = ((q + ψ.conductor : ℤ) : WithTop ℤ) := by
    simp [q]
  let χ : AddChar (LatticeQuotient F r q hr) ℂˣ :=
    lamprechtPairing F ψ hr 1 hΓ'
      (latticeQuotientMk F (sub_le_sub_left hr q) ⟨1, by simp [q]⟩)
  obtain ⟨c, hc⟩ := (lamprechtPairingLeft_bijective F ψ₀ hr 1 hΓ).surjective
    (unitAddCharToComplex _ χ)
  obtain ⟨c, rfl⟩ := latticeQuotientMk_surjective F (sub_le_sub_left hr M) c
  refine ⟨c, by simpa only [M, q, sub_neg_eq_add] using c.property, ?_⟩
  intro x hx
  have he := DFunLike.congr_fun hc (latticeQuotientMk F hr ⟨x, hx⟩)
  rw [lamprechtPairingLeft_apply, lamprechtPairing_mk_mk] at he
  apply Units.ext
  simpa only [χ, unitAddCharToComplex, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    MonoidHom.compAddChar_apply, Function.comp_apply, Units.coeHom_apply, lamprechtPairing_mk_mk,
    Units.val_one, div_one, one_mul] using he

/-- Every nontrivial continuous additive character is a nonzero scaling
of any fixed nontrivial character. Compactness makes the finite-duality
coefficients agree on the whole field, rather than on just one ideal. -/
theorem additiveScale_exists (ψ₀ ψ : LocalAddCharData F) :
    ∃ c : Fˣ, (scaleAddCharData F ψ₀ c).character = ψ.character := by
  let s : ℤ → Set F := fun r ↦ {c | c ∈ lattice F (-ψ₀.conductor + ψ.conductor) ∧
    ∀ x : F, x ∈ lattice F (min r (-ψ.conductor)) →
      ψ₀.character (c * x) = ψ.character x}
  have hclosed (r : ℤ) : IsClosed (s r) := by
    have hL : IsClosed (lattice F (-ψ₀.conductor + ψ.conductor) : Set F) := by
      exact AddSubgroup.isClosed_of_isOpen
        (lattice F (-ψ₀.conductor + ψ.conductor)).toAddSubgroup (isOpen_lattice F _)
    apply IsClosed.inter hL
    change IsClosed {c : F | ∀ x : F, x ∈ lattice F (min r (-ψ.conductor)) →
      ψ₀.character (c * x) = ψ.character x}
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun x ↦ isClosed_iInter fun _ ↦
      isClosed_eq (ψ₀.character.continuous.comp (continuous_id.mul continuous_const))
        continuous_const
  have hnonempty (r : ℤ) : (s r).Nonempty :=
    additiveScale_on_lattice F ψ₀ ψ _ (min_le_right _ _)
  have hdirected : Directed (· ⊇ ·) s := by
    intro r t
    refine ⟨min r t, ?_, ?_⟩
    · intro c hc
      exact ⟨hc.1, fun x hx ↦ hc.2 x
        (lattice_antitone F (min_le_min_right _ (min_le_left r t)) hx)⟩
    · intro c hc
      exact ⟨hc.1, fun x hx ↦ hc.2 x
        (lattice_antitone F (min_le_min_right _ (min_le_right r t)) hx)⟩
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    s hdirected hnonempty
    (fun r ↦ (isCompact_lattice F _).of_isClosed_subset (hclosed r) (fun _ h ↦ h.1))
    hclosed
  have he (x : F) : ψ₀.character (c * x) = ψ.character x := by
    by_cases hx : x = 0
    · simp [hx]
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).2 hx)
    exact (Set.mem_iInter.mp hc r).2 x (by
      change ((min r (-ψ.conductor) : ℤ) : WithTop ℤ) ≤ ord F x
      rw [← hr]
      exact_mod_cast min_le_left r (-ψ.conductor))
  have hc0 : c ≠ 0 := by
    intro h
    apply ψ.character_ne_one
    ext x
    have hh := he x
    simpa [h] using (congrArg Units.val hh).symm
  refine ⟨Units.mk0 c hc0, ?_⟩
  ext x
  exact congrArg Units.val (he x)

end AdditiveScaling

section CharacterTransport

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  [CharP F 2] [CharP K 2] [IsKleinFour Gal(K/F)]

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

local instance comparisonLowerGalois (L : IntermediateField F K) : IsGalois F L := by
  letI : IsMulCommutative Gal(K/F) := IsKleinFour.isMulCommutative
  letI : L.fixingSubgroup.Normal := inferInstance
  have h := IsGalois.of_fixedField_normal_subgroup L.fixingSubgroup
  rwa [IsGalois.fixedField_fixingSubgroup L] at h

open private originLine_degrees origin_group_equiv from
  LanglandsSecondMainLemma.Dyadic.Equal.Origin
open private field_injective from LanglandsSecondMainLemma.Dyadic.Equal.Models

namespace SimultaneousASGenerators

variable {P : Residues.EqualCharacteristicPresentation F}
  (A : SimultaneousASGenerators F K P)

/-- The last step of `D:EQ:main`: a comparison at the canonical residue
character transports to every nontrivial continuous additive character.
This is a conditional transport lemma; the conductor comparison at the
canonical character remains a separate input. Both expressions retain the
complete lower norm-character product, and conjugacy proves that their
scaling factors agree for the actual compatible primitive family. -/
theorem expressions_eq_of_canonical
    (Θ : ContinuousQuasiChar K) (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hcompatible : ∀ i, normQuasiChar (A.field i) K (θ i) = Θ)
    (hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Θ)
    (i j : Fin 3)
    (hcanonical : A.oneBreakExpression θ (originAddChar F P 0) i =
      A.oneBreakExpression θ (originAddChar F P 0) j)
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1) :
    A.oneBreakExpression θ ψ i = A.oneBreakExpression θ ψ j := by
  by_cases hij : i = j
  · subst j; rfl
  obtain ⟨_, _, _, _, hranges, _⟩ := Characters.quadraticProduct F
    (origin_group_equiv F K) A.field
    (fun k ↦ (originLine_degrees F K (A.g k) (A.nontrivial k)).1) (field_injective A)
  have hne : Ramification.intermediateNormRange (A.field i) ≠
      Ramification.intermediateNormRange (A.field j) := fun h ↦ hij (hranges h)
  obtain ⟨_, _, hD, _, hquadratic⟩ := Characters.conjugacy Nat.prime_two (origin_group_equiv F K)
    (A.field i) (A.field j)
    (originLine_degrees F K (A.g i) (A.nontrivial i)).1
    (originLine_degrees F K (A.g j) (A.nontrivial j)).1 hne
    (θ i) (θ j) Θ (hcompatible i) (hcompatible j) hprimitive
  obtain ⟨oi, oj, hoi, hoj, hprodI, hprodJ⟩ := hquadratic rfl
  rw [hprodI, hprodJ] at hD
  let ψ₀ := originCanonicalPsi F P
  let ψd := canonicalLocalAddCharData F ψ hψ
  obtain ⟨c, hc⟩ := additiveScale_exists F ψ₀ ψd
  change (scaleAddCharData F ψ₀ c).character = ψ at hc
  change A.oneBreakExpression θ ψ₀.character i =
    A.oneBreakExpression θ ψ₀.character j at hcanonical
  rw [A.oneBreakExpression_eq θ ψ₀ i oi hoi,
    A.oneBreakExpression_eq θ ψ₀ j oj hoj] at hcanonical
  rw [← hc, A.oneBreakExpression_eq θ (scaleAddCharData F ψ₀ c) i oi hoi,
    A.oneBreakExpression_eq θ (scaleAddCharData F ψ₀ c) j oj hoj,
    quadraticPair_scale F (A.field i) (θ i) oi.1 ψ₀ c,
    quadraticPair_scale F (A.field j) (θ j) oj.1 ψ₀ c, hD, hcanonical]

end SimultaneousASGenerators

/-- The minimal one-break conductor case, now for any nontrivial continuous
additive character on the actual field. The canonical comparison and all
its stationary data are supplied by `equalBreaks`. -/
theorem equalBreaks_arbitraryAddChar (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (A : SimultaneousASGenerators F K P)
    (heq : A.t 0 = A.t 1)
    (Θ : ContinuousQuasiChar K) (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hcompatible : ∀ i, normQuasiChar (A.field i) K (θ i) = Θ)
    (hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Θ)
    (hminimal : multiplicativeConductorExponent (A.field 0) (θ 0) = A.minimalConductor 0)
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1) (i j : Fin 3) :
    A.oneBreakExpression θ ψ i = A.oneBreakExpression θ ψ j :=
  A.expressions_eq_of_canonical Θ θ hcompatible hprimitive i j
    (equalBreaks hres P A heq Θ θ hcompatible hprimitive hminimal i j) ψ hψ

/-- The minimal two-break comparison for an arbitrary nontrivial additive
character, expressed with the complete lower norm-character product. -/
theorem unequalBreaks_arbitraryAddChar (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (A : SimultaneousASGenerators F K P)
    (hlt : A.t 0 < A.t 1)
    (Θ : ContinuousQuasiChar K) (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hcompatible : ∀ i, normQuasiChar (A.field i) K (θ i) = Θ)
    (hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Θ)
    (hminimal : multiplicativeConductorExponent (A.field 0) (θ 0) = A.minimalConductor 0)
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1) :
    A.oneBreakExpression θ ψ 0 = A.oneBreakExpression θ ψ 1 := by
  apply A.expressions_eq_of_canonical Θ θ hcompatible hprimitive 0 1 _ ψ hψ
  obtain ⟨_, _, _, _, hranges, _⟩ := Characters.quadraticProduct F
    (origin_group_equiv F K) A.field
    (fun i ↦ (originLine_degrees F K (A.g i) (A.nontrivial i)).1) (field_injective A)
  obtain ⟨_, _, _, _, hquadratic⟩ := Characters.conjugacy Nat.prime_two
    (origin_group_equiv F K) (A.field 0) (A.field 1)
    (originLine_degrees F K (A.g 0) (A.nontrivial 0)).1
    (originLine_degrees F K (A.g 1) (A.nontrivial 1)).1
    (fun he ↦ (by decide : (0 : Fin 3) ≠ 1) (hranges he))
    (θ 0) (θ 1) Θ (hcompatible 0) (hcompatible 1) hprimitive
  obtain ⟨ω₀, ω₁, hω₀, hω₁, hprod₀, hprod₁⟩ := hquadratic rfl
  have he := unequalBreaks hres P A hlt Θ θ hcompatible hprimitive hminimal
  dsimp only at he
  rw [hprod₀, hprod₁] at he
  change A.oneBreakExpression θ (originCanonicalPsi F P).character 0 =
    A.oneBreakExpression θ (originCanonicalPsi F P).character 1
  rw [A.oneBreakExpression_eq θ (originCanonicalPsi F P) 0 ω₀ hω₀,
    A.oneBreakExpression_eq θ (originCanonicalPsi F P) 1 ω₁ hω₁]
  exact he

/-- Assemble both minimal break patterns for the distinguished first pair.
The only conductor hypothesis is the actual first inducing conductor. -/
theorem minimalComparison_arbitraryAddChar (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (A : SimultaneousASGenerators F K P)
    (Θ : ContinuousQuasiChar K) (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hcompatible : ∀ i, normQuasiChar (A.field i) K (θ i) = Θ)
    (hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Θ)
    (hminimal : multiplicativeConductorExponent (A.field 0) (θ 0) = A.minimalConductor 0)
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1) :
    A.oneBreakExpression θ ψ 0 = A.oneBreakExpression θ ψ 1 := by
  rcases lt_or_eq_of_le A.smallest with hlt | heq
  · exact unequalBreaks_arbitraryAddChar hres P A hlt Θ θ hcompatible hprimitive
      hminimal ψ hψ
  · exact equalBreaks_arbitraryAddChar hres P A heq Θ θ hcompatible hprimitive
      hminimal ψ hψ 0 1

/-- The intermediate row with arbitrary nontrivial additive character.
All coefficient and norm data are constructed by `intermediate`; the core
chart is precisely the one supplied by the actual `twist` realization. -/
theorem intermediate_arbitraryAddChar (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (A : SimultaneousASGenerators F K P)
    (χ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hchart : ∀ i u, u ∈ unitFiltration (A.field i) (A.stationaryDepth i) →
      χ i u = A.modelValue i u)
    (lambda : ContinuousQuasiChar F) (h : ℤ)
    (hlo : A.lowerDepth 0 ≤ h) (hhi : h ≤ A.lowerDepth 0 + 2 * A.lowerDepth 1 - 2)
    (hn : (multiplicativeConductorExponent F lambda : ℤ) = (A.t 1 : ℤ) + 1 + h)
    (Θ : ContinuousQuasiChar K)
    (hcompatible : ∀ i, normQuasiChar (A.field i) K
      (χ i * normQuasiChar F (A.field i) lambda) = Θ)
    (hprimitive : ¬ ∃ eta : ContinuousQuasiChar F, normQuasiChar F K eta = Θ)
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1) :
    A.oneBreakExpression (fun i ↦ χ i * normQuasiChar F (A.field i) lambda) ψ 0 =
      A.oneBreakExpression (fun i ↦ χ i * normQuasiChar F (A.field i) lambda) ψ 1 := by
  obtain ⟨c, hc⟩ := additiveScale_exists F A.minimalBasePsi
    (canonicalLocalAddCharData F ψ hψ)
  have he := intermediate hres P A χ hchart lambda h hlo hhi hn Θ hcompatible hprimitive c⁻¹
  dsimp only at he
  simp only [inv_inv] at he
  change (scaleAddCharData F A.minimalBasePsi c).character = ψ at hc
  change A.intermediateInductionFactor 0 _ (scaleAddCharData F A.minimalBasePsi c).character =
    A.intermediateInductionFactor 1 _ (scaleAddCharData F A.minimalBasePsi c).character at he
  rw [hc] at he
  exact he

/-- The first pair agrees throughout the minimal and intermediate rows
of `D:EQ:total-complete`. The bound is on the actual first inducing
conductor; `twist` constructs the common core, its charts, and the base
twist. In the nonminimal row the bound is equivalent to
`h ≤ r₁ + 2r₂ - 2`, the last intermediate integer. -/
theorem comparison_belowHigh (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (A : SimultaneousASGenerators F K P)
    (Θ : ContinuousQuasiChar K) (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hcompatible : ∀ i, normQuasiChar (A.field i) K (θ i) = Θ)
    (hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Θ)
    (hbound : multiplicativeConductorExponent (A.field 0) (θ 0) ≤ 4 * A.t 1)
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1) :
    A.oneBreakExpression θ ψ 0 = A.oneBreakExpression θ ψ 1 := by
  obtain ⟨Θc, χ, lambda, _, _, _, _, _, hchart, hrealize, _, hranges⟩ :=
    twist hres P A Θ θ hcompatible hprimitive
  rcases lt_or_ge (multiplicativeConductorExponent F lambda) A.twistThreshold with hlo | hhi
  · exact minimalComparison_arbitraryAddChar hres P A Θ θ hcompatible hprimitive
      (hranges.1 hlo 0).1 ψ hψ
  · let h : ℤ := (multiplicativeConductorExponent F lambda : ℤ) - ((A.t 1 : ℤ) + 1)
    have hn : (multiplicativeConductorExponent F lambda : ℤ) = (A.t 1 : ℤ) + 1 + h := by
      dsimp only [h]
      omega
    have hlower : A.lowerDepth 0 ≤ h := by
      dsimp only [SimultaneousASGenerators.twistThreshold] at hhi
      dsimp only [SimultaneousASGenerators.lowerDepth]
      omega
    have hupper : h ≤ A.lowerDepth 0 + 2 * A.lowerDepth 1 - 2 := by
      have hconductor := (hranges.2 hhi 0).1
      change (multiplicativeConductorExponent (A.field 0) (θ 0) : ℤ) =
        2 * (multiplicativeConductorExponent F lambda : ℤ) - ((A.t 0 : ℤ) + 1)
        at hconductor
      obtain ⟨a, ha⟩ := (A.edge 0).2.2.2.2.1
      obtain ⟨b, hb⟩ := (A.edge 1).2.2.2.2.1
      dsimp only [SimultaneousASGenerators.lowerDepth]
      omega
    have hcompat : ∀ i, normQuasiChar (A.field i) K
        (χ i * normQuasiChar F (A.field i) lambda) = Θ := by
      intro i
      rw [← hrealize i]
      exact hcompatible i
    have he := intermediate_arbitraryAddChar hres P A χ hchart lambda h hlower hupper hn
      Θ hcompat hprimitive ψ hψ
    have hfamily : θ = fun i ↦ χ i * normQuasiChar F (A.field i) lambda := funext hrealize
    rwa [hfamily]

namespace SimultaneousASGenerators

private def comparisonSwap : Fin 3 → Fin 3 := ![0, 2, 1]

/-- Interchange the second and third fields while keeping the distinguished
smallest-break field. All generator identities and upper breaks are retained;
no new stationary-model or character assumptions are introduced. -/
private def swapLast {P : Residues.EqualCharacteristicPresentation F}
    (A : SimultaneousASGenerators F K P) : SimultaneousASGenerators F K P where
  g i := A.g (comparisonSwap i)
  nontrivial i := A.nontrivial (comparisonSwap i)
  distinct := by
    change A.g 0 ≠ A.g 2
    intro he
    have h := A.third_automorphism
    rw [← he] at h
    exact A.nontrivial 1 (mul_left_cancel (h.symm.trans (mul_one (A.g 0)).symm))
  third_automorphism := by
    change A.g 1 = A.g 0 * A.g 2
    rw [A.third_automorphism, ← mul_assoc, IsKleinFour.mul_self, one_mul]
  z i := A.z (comparisonSwap i)
  f i := A.f (comparisonSwap i)
  t i := A.t (comparisonSwap i)
  smallest := by
    change A.t 0 ≤ A.t 2
    rw [A.third_break]
    exact A.smallest
  third_break := A.third_break.symm
  third_parameter := by
    change A.f 1 = A.f 0 + A.f 2
    rw [A.third_parameter, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  third_generator := by
    change (A.z 1 : K) = (A.z 0 : K) + (A.z 2 : K)
    rw [A.third_generator, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  first_action := by
    change A.g 0 (A.z 2 : K) = (A.z 2 : K) + 1
    have hfix : A.g 0 (A.z 0 : K) = (A.z 0 : K) :=
      (IntermediateField.mem_fixedField_iff _ _).mp (A.z 0).property _ (Or.inr rfl)
    rw [A.third_generator, map_add, hfix, A.first_action, add_assoc]
  second_action := by
    change A.g 2 (A.z 0 : K) = (A.z 0 : K) + 1
    have hfix : A.g 0 (A.z 0 : K) = (A.z 0 : K) :=
      (IntermediateField.mem_fixedField_iff _ _).mp (A.z 0).property _ (Or.inr rfl)
    rw [A.third_automorphism, AlgEquiv.mul_apply, A.second_action, map_add, hfix, map_one]
  edge i := A.edge (comparisonSwap i)
  upper_break i := by
    have he := A.upper_break (comparisonSwap i)
    fin_cases i <;> simpa [comparisonSwap, A.third_break] using he

end SimultaneousASGenerators

/-- Independence of all three induction expressions throughout the minimal
and intermediate conductor intervals of `D:EQ:total-complete`. Relabeling the
last two exact AS generators proves the second distinguished comparison,
including the two-break case. -/
theorem comparison_belowHigh_all (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (A : SimultaneousASGenerators F K P)
    (Θ : ContinuousQuasiChar K) (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hcompatible : ∀ i, normQuasiChar (A.field i) K (θ i) = Θ)
    (hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Θ)
    (hbound : multiplicativeConductorExponent (A.field 0) (θ 0) ≤ 4 * A.t 1)
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1) (i j : Fin 3) :
    A.oneBreakExpression θ ψ i = A.oneBreakExpression θ ψ j := by
  have h01 := comparison_belowHigh hres P A Θ θ hcompatible hprimitive hbound ψ hψ
  have h02 := comparison_belowHigh hres P A.swapLast Θ
    (fun i ↦ θ (SimultaneousASGenerators.comparisonSwap i))
    (fun i ↦ hcompatible (SimultaneousASGenerators.comparisonSwap i))
    hprimitive (by
      change multiplicativeConductorExponent (A.field 0) (θ 0) ≤ 4 * A.t 2
      rwa [A.third_break]) ψ hψ
  change A.oneBreakExpression θ ψ 0 = A.oneBreakExpression θ ψ 2 at h02
  have hfirst (k : Fin 3) : A.oneBreakExpression θ ψ 0 = A.oneBreakExpression θ ψ k := by
    fin_cases k
    · rfl
    · exact h01
    · exact h02
  exact (hfirst i).symm.trans (hfirst j)

/-- The high row for an arbitrary nontrivial additive character. The actual
base stationary coefficient is constructed, and the common correction in
`highComparison` is used before comparing any two fields. -/
theorem highComparison_arbitraryAddChar (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (A : SimultaneousASGenerators F K P)
    (χ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (Θc : ContinuousQuasiChar K)
    (hc : ∀ i, normQuasiChar (A.field i) K (χ i) = Θc)
    (hp : ¬ ∃ eta : ContinuousQuasiChar F, normQuasiChar F K eta = Θc)
    (hchart : ∀ i u, u ∈ unitFiltration (A.field i) (A.stationaryDepth i) →
      χ i u = A.modelValue i u)
    (lambda : ContinuousQuasiChar F) {h : ℤ} (hh : A.highThreshold ≤ h)
    (hn : (multiplicativeConductorExponent F lambda : ℤ) = (A.t 1 : ℤ) + 1 + h)
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1) (i j : Fin 3) :
    A.oneBreakExpression (fun k ↦ χ k * normQuasiChar F (A.field k) lambda) ψ i =
      A.oneBreakExpression (fun k ↦ χ k * normQuasiChar F (A.field k) lambda) ψ j := by
  obtain ⟨a, ha, hbase⟩ := A.highBaseCoefficient_exists hh lambda hn
  obtain ⟨c, hcψ⟩ := additiveScale_exists F A.minimalBasePsi
    (canonicalLocalAddCharData F ψ hψ)
  have he := (highComparison hres P A χ Θc hc hp hchart lambda hh hn a ha hbase c⁻¹).1
  dsimp only at he
  simp only [inv_inv] at he
  have hij := (he i).trans (he j).symm
  change (scaleAddCharData F A.minimalBasePsi c).character = ψ at hcψ
  change A.oneBreakExpression (fun k ↦ χ k * normQuasiChar F (A.field k) lambda)
      (scaleAddCharData F A.minimalBasePsi c).character i =
    A.oneBreakExpression (fun k ↦ χ k * normQuasiChar F (A.field k) lambda)
      (scaleAddCharData F A.minimalBasePsi c).character j at hij
  rwa [hcψ] at hij

/-- The consecutive minimal, intermediate, and high intervals exhaust all
conductors of the actual inducing family (`D:EQ:total-complete`). -/
theorem comparison_of_generators (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (A : SimultaneousASGenerators F K P)
    (Θ : ContinuousQuasiChar K) (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hcompatible : ∀ i, normQuasiChar (A.field i) K (θ i) = Θ)
    (hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Θ)
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1) (i j : Fin 3) :
    A.oneBreakExpression θ ψ i = A.oneBreakExpression θ ψ j := by
  by_cases hbound : multiplicativeConductorExponent (A.field 0) (θ 0) ≤ 4 * A.t 1
  · exact comparison_belowHigh_all hres P A Θ θ hcompatible hprimitive hbound ψ hψ i j
  obtain ⟨Θc, χ, lambda, _, _, hc, _, hp, hchart, hrealize, _, hranges⟩ :=
    twist hres P A Θ θ hcompatible hprimitive
  have hhi : A.twistThreshold ≤ multiplicativeConductorExponent F lambda := by
    by_contra hlo
    have hm := (hranges.1 (lt_of_not_ge hlo) 0).1
    have ht := (A.edge 1).2.2.2.1
    simp only [SimultaneousASGenerators.minimalConductor] at hm
    norm_num at hm
    omega
  let h : ℤ := (multiplicativeConductorExponent F lambda : ℤ) - ((A.t 1 : ℤ) + 1)
  have hn : (multiplicativeConductorExponent F lambda : ℤ) = (A.t 1 : ℤ) + 1 + h := by
    dsimp only [h]
    omega
  have hh : A.highThreshold ≤ h := by
    have hm := (hranges.2 hhi 0).1
    change (multiplicativeConductorExponent (A.field 0) (θ 0) : ℤ) =
      2 * (multiplicativeConductorExponent F lambda : ℤ) - ((A.t 0 : ℤ) + 1) at hm
    dsimp only [SimultaneousASGenerators.highThreshold, SimultaneousASGenerators.lowerDepth]
    omega
  have he := highComparison_arbitraryAddChar hres P A χ Θc hc hp hchart lambda hh hn ψ hψ i j
  have hfamily : θ = fun k ↦ χ k * normQuasiChar F (A.field k) lambda := funext hrealize
  rwa [hfamily]

namespace SimultaneousASGenerators

omit [CharP F 2] [CharP K 2] in
/-- The constructed AS fields include every quadratic intermediate field. -/
private theorem comparison_field_surjective {P : Residues.EqualCharacteristicPresentation F}
    (A : SimultaneousASGenerators F K P) (L : IntermediateField F K)
    (hL : Module.finrank F L = 2) : ∃ i : Fin 3, A.field i = L := by
  have hdata := Basic.intermediateField_tower_compatible Nat.prime_two
    (origin_group_equiv F K) L hL
  have hcard : Nat.card L.fixingSubgroup = 2 := by
    rw [IsGalois.card_fixingSubgroup_eq_finrank]
    exact hdata.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨g, _, hg, _, _, hline⟩ := exists_origin_generators L.fixingSubgroup hcard
  have hfield : IntermediateField.fixedField (originLine g) = L := by
    rw [← hline, IsGalois.fixedField_fixingSubgroup]
  by_cases h0 : g = A.g 0
  · exact ⟨0, by simpa only [SimultaneousASGenerators.field, h0] using hfield⟩
  by_cases h1 : g = A.g 1
  · exact ⟨1, by simpa only [SimultaneousASGenerators.field, h1] using hfield⟩
  have h2 : g = A.g 2 := by
    rw [A.third_automorphism]
    exact IsKleinFour.eq_mul_of_ne_all (A.nontrivial 0) (A.nontrivial 1) A.distinct hg h0 h1
  exact ⟨2, by simpa only [SimultaneousASGenerators.field, h2] using hfield⟩

omit [CharP F 2] [CharP K 2] in
/-- The branch expression is the shared complete induction factor. -/
private theorem oneBreakExpression_eq_inducingFactor
    {P : Residues.EqualCharacteristicPresentation F} (A : SimultaneousASGenerators F K P)
    (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (ψ : ContinuousAddChar F) (i : Fin 3) :
    A.oneBreakExpression θ ψ i = Characters.inducingFactor Nat.prime_two
      (origin_group_equiv F K) ψ (A.field i)
      (originLine_degrees F K (A.g i) (A.nontrivial i)).1 (θ i) := by
  rfl

end SimultaneousASGenerators

omit [CharP K 2] in
/-- **Dyadic equal-characteristic comparison**, `D:EQ:main` and
`D:EQ:total-complete`. For an actual totally ramified Klein-four extension
in characteristic two, the complete induction factor is independent of
the quadratic intermediate field and of its inducing character.

Laurent coordinates, simultaneous AS generators, the primitive core,
and all stationary coefficients are constructed from the genuine inputs.
The additive character is arbitrary and nontrivial, and the continuous
quasi-characters need not be unitary. -/
theorem comparison (hres : residueDegree F K = 1)
    (Θ : ContinuousQuasiChar K)
    (hinv : ∀ σ : Gal(K/F), Basic.conjugateQuasiChar F K σ Θ = Θ)
    (hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Θ)
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1)
    (I J : IntermediateField F K) (hI : Module.finrank F I = 2) (hJ : Module.finrank F J = 2)
    (θI : ContinuousQuasiChar I) (θJ : ContinuousQuasiChar J)
    (hcI : normQuasiChar I K θI = Θ) (hcJ : normQuasiChar J K θJ = Θ) :
    Characters.inducingFactor Nat.prime_two (origin_group_equiv F K) ψ I hI θI =
      Characters.inducingFactor Nat.prime_two (origin_group_equiv F K) ψ J hJ θJ := by
  letI : CharP K 2 := charP_of_injective_algebraMap (algebraMap F K).injective 2
  obtain ⟨_, P, A, _⟩ := dyadicEqual_origin_exists F K hres
  choose θ hθ using fun i : Fin 3 ↦ Characters.invariantCharacter_inducing_exists
    Nat.prime_two (origin_group_equiv F K) Θ hinv (A.field i)
      (originLine_degrees F K (A.g i) (A.nontrivial i)).1
  obtain ⟨_, _, _, _, hranges, _⟩ := Characters.quadraticProduct F
    (origin_group_equiv F K) A.field
    (fun i ↦ (originLine_degrees F K (A.g i) (A.nontrivial i)).1) (field_injective A)
  have hto (L : IntermediateField F K) (hL : Module.finrank F L = 2)
      (χ : ContinuousQuasiChar L) (hc : normQuasiChar L K χ = Θ) :
      Characters.inducingFactor Nat.prime_two (origin_group_equiv F K) ψ L hL χ =
        A.oneBreakExpression θ ψ 0 := by
    obtain ⟨i, rfl⟩ := A.comparison_field_surjective L hL
    obtain ⟨j, hj⟩ := exists_ne i
    have he := Characters.inducingChoice_independent Nat.prime_two (origin_group_equiv F K)
      (A.field i) (A.field j) hL
      (originLine_degrees F K (A.g j) (A.nontrivial j)).1
      (fun h ↦ hj (hranges h).symm) (θ i) χ (θ j) Θ (hθ i) hc (hθ j) hprimitive ψ hψ
    rw [he, ← A.oneBreakExpression_eq_inducingFactor θ ψ i]
    exact comparison_of_generators hres P A Θ θ hθ hprimitive ψ hψ i 0
  exact (hto I hI θI hcI).trans (hto J hJ θJ hcJ).symm

end CharacterTransport

end

end LanglandsSecondMainLemma.Dyadic.Equal
