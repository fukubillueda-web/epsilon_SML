import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Dyadic.Equal.Models
import LanglandsSecondMainLemma.Characters.Conjugacy

/-!
# Dyadic / Equal / Twist

Paper Proposition 11.7, `D:EQ:realize`. Quadratic conjugacy makes the
quotient on the first field descend to the base. The remaining upper norm
characters are trivial on the whole stationary groups, so the adjusted
cores retain the actual origin charts. FML's conductor formulas give the
two exhaustive ranges, with strictly unequal conductors at their boundary.
-/

namespace LanglandsSecondMainLemma.Dyadic.Equal

open LanglandsFirstMainLemma
noncomputable section

open private originLine_degrees origin_residueDegrees origin_group_equiv from
  LanglandsSecondMainLemma.Dyadic.Equal.Origin
open private field_injective upperCyclic model_ledger from
  LanglandsSecondMainLemma.Dyadic.Equal.Models

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  [CharP F 2] [CharP K 2] [IsKleinFour Gal(K/F)]

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
local instance (L : IntermediateField F K) : IsGalois F L := by
  letI : IsMulCommutative Gal(K/F) := IsKleinFour.isMulCommutative
  letI : L.fixingSubgroup.Normal := inferInstance
  have h := IsGalois.of_fixedField_normal_subgroup L.fixingSubgroup
  rwa [IsGalois.fixedField_fixingSubgroup L] at h

namespace SimultaneousASGenerators
variable {P : Residues.EqualCharacteristicPresentation F}
  (A : SimultaneousASGenerators F K P)

/-- The common transition `T₂ + r₁` in the manuscript. -/
def twistThreshold : ℕ := A.t 1 + 1 + (A.t 0 + 1) / 2

omit [CharP F 2] [CharP K 2] in
private theorem lowerCyclic (i : Fin 3) : PrimeCyclicExtension F (A.field i) := by
  have hd := (originLine_degrees F K (A.g i) (A.nontrivial i)).1
  letI : IsCyclic Gal(A.field i/F) := isCyclic_of_prime_card
    ((IsGalois.card_aut_eq_finrank F (A.field i)).trans hd)
  exact ⟨inferInstance, inferInstance, by rw [hd]; exact Nat.prime_two⟩

omit [CharP F 2] [CharP K 2] in
/-- FML's critical bound and exact high formula on the actual lower edge. -/
private theorem pullback_conductors (hres : residueDegree F K = 1)
    (lambda : ContinuousQuasiChar F) (i : Fin 3) :
    let n := multiplicativeConductorExponent F lambda
    let q := multiplicativeConductorExponent (A.field i)
      (normQuasiChar F (A.field i) lambda)
    (n ≤ A.t i + 1 → q ≤ A.t i + 1) ∧
      (A.t i + 1 < n → (q : ℤ) = 2 * (n : ℤ) - ((A.t i : ℤ) + 1)) := by
  letI := A.lowerCyclic i
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F (A.field i)
    (origin_residueDegrees F K hres (A.field i)).1
  have ht := (A.edge i).2.2.2.2.2.2.2.1
  let c := canonicalLocalQuasiCharData F lambda
  let d := canonicalLocalQuasiCharData (A.field i) (normQuasiChar F (A.field i) lambda)
  change (c.conductor ≤ A.t i + 1 → d.conductor ≤ A.t i + 1) ∧
    (A.t i + 1 < c.conductor →
      (d.conductor : ℤ) = 2 * (c.conductor : ℤ) - ((A.t i : ℤ) + 1))
  constructor
  · intro hn
    by_cases hbelow : c.conductor ≤ A.t i
    · rw [c.conductor_compNorm_eq_belowBreak F (A.field i) ht
        (origin_residueDegrees F K hres (A.field i)).1 pi hpi hgen d rfl hbelow]
      exact hn
    · exact c.conductor_compNorm_le_critical F (A.field i) ht
        (origin_residueDegrees F K hres (A.field i)).1 pi hpi hgen d rfl (by omega)
  · intro hn
    simpa only [(originLine_degrees F K (A.g i) (A.nontrivial i)).1,
      Nat.cast_ofNat, Nat.reduceSub, one_mul, Nat.cast_add, Nat.cast_one] using
      c.conductor_compNorm_eq_high_explicit F (A.field i) ht
        (origin_residueDegrees F K hres (A.field i)).1 pi hpi hgen d rfl hn

omit [IsGalois F K] [CharP F 2] [CharP K 2] in
/-- The same integer boundary separates the odd core and even high
pullback conductors on all three fields. -/
private theorem twist_ledger (i : Fin 3) :
    A.t i + 1 < A.minimalConductor i ∧
    A.t i + 1 < A.twistThreshold ∧
    (A.minimalConductor i : ℤ) =
      2 * (A.twistThreshold : ℤ) - ((A.t i : ℤ) + 1) - 1 := by
  have hpos := (A.edge 0).2.2.2.1
  obtain ⟨a, ha⟩ := (A.edge 0).2.2.2.2.1
  obtain ⟨b, hb⟩ := (A.edge 1).2.2.2.2.1
  have hs := A.smallest
  have ht := A.third_break
  fin_cases i <;> simp only [minimalConductor, twistThreshold] <;> norm_num
  all_goals try rw [show A.t ⟨2, by decide⟩ = A.t 1 from ht]
  all_goals omega

/-- Conductor alternatives for every actual core and every continuous
base twist. In particular the high pullback is one larger than the odd
core at `n = T₂ + r₁`, so no equal-conductor cancellation is possible. -/
theorem twist_conductors (hres : residueDegree F K = 1)
    (χ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hχ : ∀ i, IsMultiplicativeConductor (A.field i) (χ i) (A.minimalConductor i))
    (lambda : ContinuousQuasiChar F) :
    let n := multiplicativeConductorExponent F lambda
    let M := fun i ↦ multiplicativeConductorExponent (A.field i)
      (χ i * normQuasiChar F (A.field i) lambda)
    (n < A.twistThreshold → ∀ i, M i = A.minimalConductor i ∧ Odd (M i)) ∧
    (A.twistThreshold ≤ n → ∀ i,
      (M i : ℤ) = 2 * (n : ℤ) - ((A.t i : ℤ) + 1) ∧
        Even (M i) ∧ A.minimalConductor i < M i) := by
  let n := multiplicativeConductorExponent F lambda
  dsimp only
  constructor
  · intro hn i
    let q := multiplicativeConductorExponent (A.field i)
      (normQuasiChar F (A.field i) lambda)
    have hq := multiplicativeConductorExponent_isConductor (A.field i)
      (normQuasiChar F (A.field i) lambda)
    have hp := A.pullback_conductors hres lambda i
    have hl := A.twist_ledger i
    have hsmall : q < A.minimalConductor i := by
      by_cases h : n ≤ A.t i + 1
      · have := hp.1 h
        omega
      · have := hp.2 (by omega)
        omega
    have he := multiplicativeConductorExponent_eq_of_isConductor (A.field i) _
      ((hχ i).mul_of_gt hq hsmall)
    exact ⟨he, he.symm ▸ (model_ledger A i).2.2.2.2⟩
  · intro hn i
    let q := multiplicativeConductorExponent (A.field i)
      (normQuasiChar F (A.field i) lambda)
    have hq := multiplicativeConductorExponent_isConductor (A.field i)
      (normQuasiChar F (A.field i) lambda)
    have hl := A.twist_ledger i
    have hp := (A.pullback_conductors hres lambda i).2 (by omega)
    have hlarge : A.minimalConductor i < q := by omega
    have he := multiplicativeConductorExponent_eq_of_isConductor (A.field i) _
      ((hχ i).mul_of_lt hq hlarge)
    rw [he]
    refine ⟨hp, ?_, hlarge⟩
    obtain ⟨a, ha⟩ := (A.edge i).2.2.2.2.1
    exact ⟨n - (a + 1), by omega⟩

omit [CharP F 2] [CharP K 2] in
private theorem normUnits_tower (i : Fin 3) (x : Kˣ) :
    normUnits F (A.field i) (normUnits (A.field i) K x) = normUnits F K x := by
  apply Units.ext
  exact Basic.norm_tower (F := F) (L := A.field i) (x : K)

omit [CharP F 2] [CharP K 2] in
/-- Every upper norm character on the second or third field is trivial
on the whole core chart domain, including the critical successor. -/
private theorem upperNormCharacter_chart (hres : residueDegree F K = 1)
    (i : Fin 3) (hi : i ≠ 0) (μ : NormCharacter (A.field i) K)
    (u : (A.field i)ˣ) (hu : u ∈ unitFiltration (A.field i) (A.stationaryDepth i)) :
    μ.1 u = 1 := by
  letI := upperCyclic A i
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer (A.field i) K
    (origin_residueDegrees F K hres (A.field i)).2
  have ht : PrimeCyclicExtension.IsLowerBreak (A.field i) K (A.t 0) := by
    simpa only [if_neg hi] using A.upper_break i
  have hs : A.t 0 + 1 ≤ A.stationaryDepth i := by
    have hsmall := A.smallest
    obtain ⟨a, ha⟩ := (A.edge 0).2.2.2.2.1
    obtain ⟨b, hb⟩ := (A.edge 1).2.2.2.2.1
    simp only [stationaryDepth, if_neg hi]
    omega
  exact ramifiedNormCharacter_trivialOn_break_succ (A.field i) K ht
    (origin_residueDegrees F K hres (A.field i)).2 pi hpi hgen μ u
    (unitFiltration_antitone (A.field i) hs hu)

omit [CharP K 2] in
/-- Realization relative to a constructed primitive core family. The
quotient on the first field descends by quadratic conjugacy; all remaining
quotients are actual upper norm characters with the proved chart bound. -/
private theorem realize_core (hres : residueDegree F K = 1)
    (Θ : ContinuousQuasiChar K)
    (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hθ : ∀ i, normQuasiChar (A.field i) K (θ i) = Θ)
    (hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Θ)
    (Θc : ContinuousQuasiChar K)
    (χ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hχ : ∀ i, normQuasiChar (A.field i) K (χ i) = Θc)
    (hcprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Θc)
    (hchart : ∀ i u, u ∈ unitFiltration (A.field i) (A.stationaryDepth i) →
      χ i u = A.modelValue i u) :
    ∃ (lambda : ContinuousQuasiChar F)
      (χ' : (i : Fin 3) → ContinuousQuasiChar (A.field i)),
      (∀ i, normQuasiChar (A.field i) K (χ' i) = Θc) ∧
      (∀ i u, u ∈ unitFiltration (A.field i) (A.stationaryDepth i) →
        χ' i u = A.modelValue i u) ∧
      ∀ i, θ i = χ' i * normQuasiChar F (A.field i) lambda := by
  obtain ⟨_, _, _, _, hranges, _⟩ := Characters.quadraticProduct F
    (origin_group_equiv F K) A.field
    (fun i ↦ (originLine_degrees F K (A.g i) (A.nontrivial i)).1) (field_injective A)
  have hne : Ramification.intermediateNormRange (A.field 0) ≠
      Ramification.intermediateNormRange (A.field 1) :=
    fun h ↦ (by decide : (0 : Fin 3) ≠ 1) (hranges h)
  obtain ⟨⟨Dt⟩, _⟩ := Characters.conjugacy Nat.prime_two (origin_group_equiv F K)
    (A.field 0) (A.field 1)
    (originLine_degrees F K (A.g 0) (A.nontrivial 0)).1
    (originLine_degrees F K (A.g 1) (A.nontrivial 1)).1 hne
    (θ 0) (θ 1) Θ (hθ 0) (hθ 1) hprimitive
  obtain ⟨⟨Dc⟩, _⟩ := Characters.conjugacy Nat.prime_two (origin_group_equiv F K)
    (A.field 0) (A.field 1)
    (originLine_degrees F K (A.g 0) (A.nontrivial 0)).1
    (originLine_degrees F K (A.g 1) (A.nontrivial 1)).1 hne
    (χ 0) (χ 1) Θc (hχ 0) (hχ 1) hcprimitive
  have hcard : Nat.card (NormCharacter (A.field 0) K) = 2 :=
    (Nat.card_congr Dt.quotientEquiv.toEquiv).symm.trans
      ((IsGalois.card_aut_eq_finrank F (A.field 0)).trans
        (originLine_degrees F K (A.g 0) (A.nontrivial 0)).1)
  have heq (σ : Gal(A.field 0/F)) : Dt.quotientEquiv σ = Dc.quotientEquiv σ := by
    by_cases hσ : σ = 1
    · simp [hσ]
    · exact ((Nat.card_eq_two_iff' (1 : NormCharacter (A.field 0) K)).mp hcard).unique
        ((map_ne_one_iff Dt.quotientEquiv Dt.quotientEquiv.injective).2 hσ)
        ((map_ne_one_iff Dc.quotientEquiv Dc.quotientEquiv.injective).2 hσ)
  have hinv (σ : Gal(A.field 0/F)) (x : (A.field 0)ˣ) :
      (θ 0 / χ 0) (Units.map σ.toMonoidHom x) = (θ 0 / χ 0) x := by
    have h := congrArg Subtype.val (heq σ.symm)
    rw [Dt.quotient_eq, Dc.quotient_eq] at h
    have hx := DFunLike.congr_fun h x
    change θ 0 (Units.map σ.toMonoidHom x) / θ 0 x =
      χ 0 (Units.map σ.toMonoidHom x) / χ 0 x at hx
    change θ 0 (Units.map σ.toMonoidHom x) / χ 0 (Units.map σ.toMonoidHom x) =
      θ 0 x / χ 0 x
    apply div_eq_div_iff_mul_eq_mul.mpr
    exact (div_eq_div_iff_mul_eq_mul.mp hx).trans (mul_comm _ _)
  letI := A.lowerCyclic 0
  obtain ⟨lambda, hlambda⟩ := Local.invariantCharacter_descends F (A.field 0)
    (θ 0 / χ 0) hinv
  let χ' := fun i ↦ θ i / normQuasiChar F (A.field i) lambda
  have hfirst : χ' 0 = χ 0 := by
    change θ 0 / normQuasiChar F (A.field 0) lambda = χ 0
    rw [hlambda, div_div_cancel]
  have hnorm (i : Fin 3) : normQuasiChar (A.field i) K (χ' i) = Θc := by
    apply ContinuousMonoidHom.ext
    intro x
    have ht : θ i (normUnits (A.field i) K x) = θ 0 (normUnits (A.field 0) K x) :=
      (DFunLike.congr_fun (hθ i) x).trans (DFunLike.congr_fun (hθ 0) x).symm
    have hl := DFunLike.congr_fun hlambda (normUnits (A.field 0) K x)
    change lambda (normUnits F (A.field 0) (normUnits (A.field 0) K x)) =
      θ 0 (normUnits (A.field 0) K x) / χ 0 (normUnits (A.field 0) K x) at hl
    change θ i (normUnits (A.field i) K x) /
      lambda (normUnits F (A.field i) (normUnits (A.field i) K x)) = Θc x
    rw [ht, A.normUnits_tower i, ← A.normUnits_tower 0, hl, div_div_cancel]
    exact DFunLike.congr_fun (hχ 0) x
  refine ⟨lambda, χ', hnorm, ?_, ?_⟩
  · intro i u hu
    by_cases hi : i = 0
    · subst i
      rw [hfirst]
      exact hchart 0 u hu
    · let μ : NormCharacter (A.field i) K := ⟨χ' i / χ i, by
        apply ContinuousMonoidHom.ext
        intro x
        change χ' i (normUnits (A.field i) K x) / χ i (normUnits (A.field i) K x) = 1
        exact div_eq_one.mpr
          ((DFunLike.congr_fun (hnorm i) x).trans (DFunLike.congr_fun (hχ i) x).symm)⟩
      have hμ := A.upperNormCharacter_chart hres i hi μ u hu
      change χ' i u / χ i u = 1 at hμ
      exact (div_eq_one.mp hμ).trans (hchart i u hu)
  · intro i
    exact (div_mul_cancel (θ i) (normQuasiChar F (A.field i) lambda)).symm

end SimultaneousASGenerators

/-- **Actual common-twist realization (Proposition 11.7, D:EQ:realize).**
Every primitive compatible family on the actual three quadratic fields is
a common base twist of a primitive core family with the exact original
stationary charts and odd minimal conductors. All characters are continuous
quasi-characters; their values on uniformizers are unrestricted.

The cutoff is `T₂ + r₁`. Below it all conductors are `mᵢ`; at and above it
they are the even integers `2n - Tᵢ`, strictly larger than `mᵢ`. These
ranges exhaust every natural conductor `n`. The high conductor formulas
use integer subtraction, without truncated depths.
The origin data are constructed by `simultaneousASGenerators_exists`.
No model, descent, or realization assumption is required. -/
theorem twist (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (A : SimultaneousASGenerators F K P)
    (Θ : ContinuousQuasiChar K)
    (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hcompatible : ∀ i, normQuasiChar (A.field i) K (θ i) = Θ)
    (hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Θ) :
    ∃ (Θc : ContinuousQuasiChar K)
      (χ : (i : Fin 3) → ContinuousQuasiChar (A.field i)) (lambda : ContinuousQuasiChar F),
      (∀ i, IsMultiplicativeConductor (A.field i) (χ i) (A.minimalConductor i) ∧
        Odd (A.minimalConductor i)) ∧
      IsMultiplicativeConductor K Θc (A.t 0 + 2 * A.t 1 + 1) ∧
      (∀ i, normQuasiChar (A.field i) K (χ i) = Θc) ∧
      (∀ (τ : Gal(K/F)) (x : Kˣ), Θc (Units.map τ.toMonoidHom x) = Θc x) ∧
      (¬ ∃ eta : ContinuousQuasiChar F, normQuasiChar F K eta = Θc) ∧
      (∀ (i : Fin 3) (u : (A.field i)ˣ),
        u ∈ unitFiltration (A.field i) (A.stationaryDepth i) →
          χ i u = tracePullbackAddChar F (A.field i)
            (originAddChar F P ((A.t 1 : ℤ) + 1))
            (Algebra.norm (A.field i) A.Y * (1 - (u : A.field i)))) ∧
      (∀ i, θ i = χ i * normQuasiChar F (A.field i) lambda) ∧
      (∀ i, A.minimalConductor i ≤ multiplicativeConductorExponent (A.field i) (θ i)) ∧
      (let n := multiplicativeConductorExponent F lambda
       let M := fun i ↦ multiplicativeConductorExponent (A.field i) (θ i)
       (n < A.twistThreshold → ∀ i, M i = A.minimalConductor i ∧ Odd (M i)) ∧
       (A.twistThreshold ≤ n → ∀ i,
         (M i : ℤ) = 2 * (n : ℤ) - ((A.t i : ℤ) + 1) ∧
           Even (M i) ∧ A.minimalConductor i < M i)) := by
  obtain ⟨Θc, χc, hcondc, hcommon, hnormc, hinv, hprimc, hchartc⟩ := models hres P A
  obtain ⟨lambda, χ, hnorm, hchart, hrealize⟩ :=
    A.realize_core hres Θ θ hcompatible hprimitive Θc χc hnormc hprimc hchartc
  have hcond (i : Fin 3) := A.conductor_of_modelChart hres i (χ i) (hchart i)
  have hranges := A.twist_conductors hres χ hcond lambda
  simp only [← hrealize] at hranges
  refine ⟨Θc, χ, lambda, fun i ↦ ⟨hcond i, (hcondc i).2⟩, hcommon,
    hnorm, hinv, hprimc, hchart, hrealize, ?_, hranges⟩
  intro i
  rcases lt_or_ge (multiplicativeConductorExponent F lambda) A.twistThreshold with h | h
  · exact ((hranges.1 h i).1).ge
  · exact (hranges.2 h i).2.2.le

end

end LanglandsSecondMainLemma.Dyadic.Equal
