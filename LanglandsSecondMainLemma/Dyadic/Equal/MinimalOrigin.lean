import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsFirstMainLemma.Ramification.NormRepresentatives
import LanglandsSecondMainLemma.Dyadic.Equal.Twist
import LanglandsSecondMainLemma.Dyadic.Equal.ThirdNorm

/-!
# Full stationary origins at minimal conductors

The norm choice preceding Lemma 11.8 (`D:EQ:min-approx`) and all the
stationary identities of `D:EQ:min-origin` in the corrected manuscript.
Indices `0, 1, 2` denote its fields `1, 2, 3`. Coefficient congruences are on
whole integer lattices and use only subcritical precision. The theorem
`SimultaneousASGenerators.minimalOrigin_zero` proves all three upper and
lower identities when the base conductor is at most `q₀`.
`SimultaneousASGenerators.minimalOrigin_third` constructs the actual moved
numerator and proves both third-side identities throughout the minimal
conductor range when the breaks agree. Its affine error is proved integral;
the actual third norm and the unchanged upper trace are retained.

The first two moved sides use the exact identities and whole-ideal bounds
from `ThirdNorm`, retaining the complete common affine error until its
phase is proved trivial on the required stationary ideal. The public
`minimalOrigin` theorem obtains the core charts from `twist` for an actual
primitive compatible family in the full minimal conductor row. Its one
numerator works on the first two fields, and on all three when the breaks
agree.
-/

namespace LanglandsSecondMainLemma.Dyadic.Equal
open LanglandsFirstMainLemma
noncomputable section

open private originLine_degrees originLine_norm_trace origin_residueDegrees from
  LanglandsSecondMainLemma.Dyadic.Equal.Origin
open private edge_ramification depth_ledger norm_one_sub_charTwo from
  LanglandsSecondMainLemma.Dyadic.Equal.Compatibility
open private lowerCyclic from LanglandsSecondMainLemma.Dyadic.Equal.Twist

private theorem phase_eq_of_sub_mem
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (ψ : ContinuousAddChar E) {J : ℤ}
    (hψ : IsAdditiveConductor E ψ (-J)) {x y : E}
    (h : x - y ∈ lattice E J) : ψ x = ψ y := by
  apply div_eq_one.mp
  change ψ.toAddChar x / ψ.toAddChar y = 1
  rw [← AddChar.map_sub_eq_div]
  exact hψ.trivial (x - y) (by simpa only [neg_neg] using h)

private theorem quasiChar_trivial_of_one_sub_mem
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (lambda : ContinuousQuasiChar E)
    {q : ℕ} (hq : 0 < q)
    (hn : multiplicativeConductorExponent E lambda ≤ q)
    (u : Eˣ) (hu : 1 - (u : E) ∈ lattice E (q : ℤ)) : lambda u = 1 := by
  have hu' : u ∈ unitFiltration E q := by
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
    rw [hr, mem_unitFiltration_succ_iff_sub_mem_lattice]
    simpa only [neg_sub, hr] using (lattice E (q : ℤ)).neg_mem hu
  exact (multiplicativeConductorExponent_isConductor E lambda).trivial u
    (unitFiltration_antitone E hn hu')

/-- FML's stationary class supplies an actual coefficient of the exact order,
on every element of the specified unit group. The denominator is `1`. -/
private theorem stationary_coefficient
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [CharP E 2] (lambda : ContinuousQuasiChar E)
    (ψ : ContinuousAddChar E) (J : ℤ) (hψ : IsAdditiveConductor E ψ (-J))
    (q : ℕ) (hq : IsLamprechtStationaryDepth (multiplicativeConductorExponent E lambda) q) :
    ∃ c : E, ord E c = ((J - (multiplicativeConductorExponent E lambda : ℤ) : ℤ) :
        WithTop ℤ) ∧
      ∀ u : Eˣ, 1 - (u : E) ∈ lattice E (q : ℤ) →
        lambda u = ψ (c * (1 - (u : E))) := by
  let χ := canonicalLocalQuasiCharData E lambda
  let Ψ : LocalAddCharData E := ⟨ψ, -J, hψ⟩
  have hΓ : ord E ((1 : Eˣ) : E) = ((J + Ψ.conductor : ℤ) : WithTop ℤ) := by
    simp [Ψ]
  obtain ⟨c, hc⟩ := latticeQuotientMk_surjective E
    (sub_le_sub_left hq.int_le_conductor J)
    (stationaryNumeratorClass E χ Ψ J hq 1 hΓ)
  refine ⟨c, stationaryNumeratorClass_representative_ord E χ Ψ J hq 1 hΓ c hc, ?_⟩
  intro u hu
  have hlin := stationaryNumeratorClass_linearization E χ Ψ J hq 1 hΓ c hc
    ⟨1 - (u : E), hu⟩
  have he : positiveUnitOfLattice E hq.pos ⟨1 - (u : E), hu⟩ = u := by
    apply Units.ext
    simp [positiveUnitOfLattice, CharTwo.sub_eq_add, ← add_assoc,
      CharTwo.add_self_eq_zero]
  simpa only [he, χ, canonicalLocalQuasiCharData, Ψ, Units.val_one, div_one] using hlin

private theorem quadratic_square_sub_norm
    (E M : Type) [Field E] [Field M] [Algebra E M]
    [Module.Finite E M] [IsGalois E M] [CharP M 2]
    (hdegree : Module.finrank E M = 2) (x : M) :
    x ^ 2 - algebraMap E M (Algebra.norm E x) =
      algebraMap E M (Algebra.trace E M x) * x := by
  classical
  have hcard : Nat.card Gal(M/E) = 2 :=
    (IsGalois.card_aut_eq_finrank E M).trans hdegree
  obtain ⟨σ, hσ, _⟩ := (Nat.card_eq_two_iff' (1 : Gal(M/E))).mp hcard
  have hcard' : Fintype.card Gal(M/E) = 2 := by
    rwa [Fintype.card_eq_nat_card]
  have huniv : ({1, σ} : Finset Gal(M/E)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simp [hσ.symm, hcard']
  rw [Algebra.norm_eq_prod_automorphisms, trace_eq_sum_automorphisms,
    ← huniv, Finset.prod_pair hσ.symm, Finset.sum_pair hσ.symm]
  simp only [AlgEquiv.one_apply, CharTwo.sub_eq_add]
  ring

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  [CharP F 2] [CharP K 2] [IsKleinFour Gal(K/F)]

local instance minimalOriginValuativeRel (L : IntermediateField F K) : ValuativeRel L :=
  Basic.intermediateFieldValuativeRel L
local instance minimalOriginTopology (L : IntermediateField F K) : TopologicalSpace L :=
  Basic.intermediateFieldTopology L
local instance minimalOriginLocalField (L : IntermediateField F K) : IsNonarchimedeanLocalField L :=
  Basic.intermediateField_localField L
local instance minimalOriginLowerExtension (L : IntermediateField F K) : ValuativeExtension F L :=
  Basic.intermediateField_lowerValuativeExtension L
local instance minimalOriginUpperExtension (L : IntermediateField F K) : ValuativeExtension L K :=
  Basic.intermediateField_upperValuativeExtension L
local instance minimalOriginGalois (L : IntermediateField F K) : IsGalois F L := by
  letI : IsMulCommutative Gal(K/F) := IsKleinFour.isMulCommutative
  letI : L.fixingSubgroup.Normal := inferInstance
  have h := IsGalois.of_fixedField_normal_subgroup L.fixingSubgroup
  rwa [IsGalois.fixedField_fixingSubgroup L] at h

namespace SimultaneousASGenerators
variable {P : Residues.EqualCharacteristicPresentation F}
  (A : SimultaneousASGenerators F K P)

/-- Both lower trace and lower norm of the entire upper stationary ideal
lie in the common base ideal of depth `q₀ = r₁ + r₂`. -/
theorem stationary_trace_norm_mem (hres : residueDegree F K = 1)
    (i : Fin 3) {z : A.field i}
    (hz : z ∈ lattice (A.field i) (A.stationaryDepth i : ℤ)) :
    Algebra.trace F (A.field i) z ∈ lattice F (A.stationaryDepth 1 : ℤ) ∧
      Algebra.norm F z ∈ lattice F (A.stationaryDepth 1 : ℤ) := by
  have hdepth : A.stationaryDepth 1 ≤ A.stationaryDepth i ∧
      2 * (A.stationaryDepth 1 : ℤ) ≤
        (A.stationaryDepth i : ℤ) + ((A.t i : ℤ) + 1) := by
    have hs := A.smallest
    have ht := A.third_break
    obtain ⟨a, ha⟩ := (A.edge 0).2.2.2.2.1
    obtain ⟨b, hb⟩ := (A.edge 1).2.2.2.2.1
    fin_cases i <;> simp only [stationaryDepth] <;> norm_num
    all_goals try rw [show A.t ⟨2, by decide⟩ = A.t 1 from ht]
    all_goals omega
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F (A.field i)
    (origin_residueDegrees F K hres (A.field i)).1
  constructor
  · have ht := trace_mem_lattice_floor F (A.field i) pi hpi hgen _ hz
    apply lattice_antitone F ?_ ht
    rw [(edge_ramification A hres i).1, (A.edge i).2.2.2.2.2.2.2.2]
    push_cast
    omega
  · change _ ≤ ord F (norm F (A.field i) z)
    rw [ord_norm, (origin_residueDegrees F K hres (A.field i)).1, one_nsmul]
    exact lattice_antitone _ (by exact_mod_cast hdepth.1) hz

omit [IsGalois F K] [CharP F 2] [CharP K 2] in
private theorem minimal_norm_ledger {n : ℕ} (hn : n < A.twistThreshold)
    (hqn : A.stationaryDepth 1 < n) :
    IsLamprechtStationaryDepth n (A.stationaryDepth 1) ∧
      n - A.stationaryDepth 1 ≤ A.t 2 ∧
      ((A.t 1 : ℤ) + 1 - (n : ℤ)) + ((n - A.stationaryDepth 1 : ℕ) : ℤ) =
        ((A.t 1 : ℤ) - A.t 0) / 2 ∧
      ((A.t 1 : ℤ) - A.t 0) / 2 + (A.stationaryDepth 1 : ℤ) =
        (A.t 1 : ℤ) + 1 := by
  have hpos := (A.edge 0).2.2.2.1
  have hs := A.smallest
  have ht := A.third_break
  obtain ⟨a, ha⟩ := (A.edge 0).2.2.2.2.1
  obtain ⟨b, hb⟩ := (A.edge 1).2.2.2.2.1
  simp only [twistThreshold, stationaryDepth] at hn hqn ⊢
  norm_num at hn hqn ⊢
  refine ⟨⟨by omega, by omega, by omega⟩, by omega, by omega, by omega⟩

/-- The actual subcritical norm choice in `D:EQ:min-approx`, including its
exact shell, full coefficient congruence, and preservation of the character
on the whole base ideal. The relative precision is `n - q₀ = δ + h > 0`;
this natural subtraction is only used under the explicit inequality `q₀ < n`.
Every fractional-ideal exponent remains an integer. -/
theorem minimalNormApproximation (hres : residueDegree F K = 1)
    (lambda : ContinuousQuasiChar F)
    (hn : multiplicativeConductorExponent F lambda < A.twistThreshold)
    (hqn : A.stationaryDepth 1 < multiplicativeConductorExponent F lambda) :
    let n := multiplicativeConductorExponent F lambda
    let h : ℤ := (n : ℤ) - ((A.t 1 : ℤ) + 1)
    let δ : ℤ := ((A.t 1 : ℤ) - A.t 0) / 2
    ∃ (c : Fˣ) (X : (A.field 2)ˣ),
      n - A.stationaryDepth 1 ≤ A.t 2 ∧
      IsSubcriticalNormRepresentative F (A.field 2) (-h)
        (n - A.stationaryDepth 1) c X ∧
      (c : F) - Algebra.norm F (X : A.field 2) ∈ lattice F δ ∧
      ∀ u : Fˣ, 1 - (u : F) ∈ lattice F (A.stationaryDepth 1 : ℤ) →
        lambda u = originAddChar F P ((A.t 1 : ℤ) + 1)
          (Algebra.norm F (X : A.field 2) * (1 - (u : F))) := by
  dsimp only
  have hl := A.minimal_norm_ledger hn hqn
  let Ψ := originAddChar F P ((A.t 1 : ℤ) + 1)
  have hΨ := originAddChar_conductor F P ((A.t 1 : ℤ) + 1)
  obtain ⟨c, hc, hchart⟩ := stationary_coefficient F lambda Ψ
    ((A.t 1 : ℤ) + 1) hΨ (A.stationaryDepth 1) hl.1
  have hc0 : c ≠ 0 := (ord_ne_top_iff F).1 (by rw [hc]; exact WithTop.coe_ne_top)
  let c₀ := Units.mk0 c hc0
  letI := lowerCyclic A 2
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F (A.field 2)
    (origin_residueDegrees F K hres (A.field 2)).1
  obtain ⟨X, hX⟩ := normRepresentative_subcritical F (A.field 2)
    (A.edge 2).2.2.2.2.2.2.2.1 (origin_residueDegrees F K hres (A.field 2)).1
    pi hpi hgen hl.2.1 c₀ hc
  have he : (c₀ : F) - Algebra.norm F (X : A.field 2) ∈
      lattice F (((A.t 1 : ℤ) - A.t 0) / 2) := by
    simpa only [hl.2.2.1] using hX.norm_congruent
  refine ⟨c₀, X, hl.2.1, ?_, he, ?_⟩
  · simpa only [neg_sub] using hX
  · intro u hu
    rw [hchart u hu]
    apply phase_eq_of_sub_mem Ψ hΨ
    rw [← sub_mul]
    have hp := mul_mem_lattice F he hu
    rwa [hl.2.2.2] at hp

/-- The valuation assertion of `D:EQ:min-origin`: every third-field choice
in the constructed lattice is strictly smaller in absolute value than `Y`.
The whole-lattice hypothesis includes the zero choice and infinite order. -/
theorem minimalMovedOrigin_order (hres : residueDegree F K = 1)
    {n : ℕ} (hn : n < A.twistThreshold) (X : A.field 2)
    (hX : X ∈ lattice (A.field 2) ((A.t 1 : ℤ) + 1 - (n : ℤ))) :
    ord K (A.Y + (X : K)) = ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ) := by
  have hbound : -(A.t 0 : ℤ) < 2 * ((A.t 1 : ℤ) + 1 - (n : ℤ)) := by
    simp only [twistThreshold] at hn
    omega
  have htop : ((2 * ((A.t 1 : ℤ) + 1 - (n : ℤ)) : ℤ) : WithTop ℤ) ≤
      ord K (X : K) := by
    change _ ≤ ord K (algebraMap (A.field 2) K X)
    rw [ord_algebraMap, (edge_ramification A hres 2).2, two_nsmul]
    have hx : (((A.t 1 : ℤ) + 1 - (n : ℤ) : ℤ) : WithTop ℤ) ≤
        ord (A.field 2) X := hX
    simpa only [← WithTop.coe_add, two_mul] using add_le_add hx hx
  have hlt : ord K A.Y < ord K (X : K) := by
    rw [(A.origin_orders hres).1]
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hbound) htop
  rw [ord_add_eq_min K hlt.ne, min_eq_left hlt.le, (A.origin_orders hres).1]

/-- The norm choice also covers the trivial base chart: take `X = 0` when
`n ≤ q₀`. Otherwise the preceding theorem supplies a nonzero exact-order
representative. This constructs the input to the full-origin proof. -/
theorem minimalNormChoice (hres : residueDegree F K = 1)
    (lambda : ContinuousQuasiChar F)
    (hn : multiplicativeConductorExponent F lambda < A.twistThreshold) :
    let n := multiplicativeConductorExponent F lambda
    ∃ X : A.field 2,
      X ∈ lattice (A.field 2) ((A.t 1 : ℤ) + 1 - (n : ℤ)) ∧
      (n ≤ A.stationaryDepth 1 → X = 0) ∧
      (A.stationaryDepth 1 < n →
        ord (A.field 2) X = (((A.t 1 : ℤ) + 1 - (n : ℤ) : ℤ) : WithTop ℤ)) ∧
      ∀ u : Fˣ, 1 - (u : F) ∈ lattice F (A.stationaryDepth 1 : ℤ) →
        lambda u = originAddChar F P ((A.t 1 : ℤ) + 1)
          (Algebra.norm F X * (1 - (u : F))) := by
  dsimp only
  by_cases hqn : multiplicativeConductorExponent F lambda ≤ A.stationaryDepth 1
  · refine ⟨0, (lattice _ _).zero_mem, fun _ ↦ rfl, fun h ↦ (not_lt_of_ge hqn h).elim, ?_⟩
    intro u hu
    simpa using quasiChar_trivial_of_one_sub_mem F lambda (depth_ledger A 1).1 hqn u hu
  · obtain ⟨c, X, _, hX, _, hchart⟩ := A.minimalNormApproximation hres lambda hn
      (lt_of_not_ge hqn)
    refine ⟨X, ?_, fun h ↦ (hqn h).elim, fun _ ↦ ?_, hchart⟩
    · simpa only [neg_sub] using hX.source_exactDepth.1
    · simpa only [neg_sub] using hX.source_order

/-- The actual lower norm carries every full upper stationary group into
the base group at depth `q₀`. Both terms of its quadratic increment are
retained, including the norm term. -/
theorem stationaryNorm_mem (hres : residueDegree F K = 1)
    (i : Fin 3) (u : (A.field i)ˣ)
    (hu : 1 - (u : A.field i) ∈ lattice (A.field i) (A.stationaryDepth i : ℤ)) :
    1 - (normUnits F (A.field i) u : F) ∈ lattice F (A.stationaryDepth 1 : ℤ) := by
  obtain ⟨ht, hn⟩ := A.stationary_trace_norm_mem hres i hu
  have he := norm_one_sub_charTwo F (A.field i)
    (originLine_degrees F K (A.g i) (A.nontrivial i)).1 (1 - (u : A.field i))
  simp only [sub_sub_cancel] at he
  change 1 - Algebra.norm F (u : A.field i) ∈ _
  rw [he, CharTwo.sub_eq_add]
  simp only [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  exact (lattice F _).add_mem ht hn

/-- In the `n ≤ q₀` branch of `D:EQ:min-origin`, the entire pulled-back
base character is trivial on each full upper stationary group. -/
theorem minimalNormPullback_trivial (hres : residueDegree F K = 1)
    (lambda : ContinuousQuasiChar F)
    (hn : multiplicativeConductorExponent F lambda ≤ A.stationaryDepth 1)
    (i : Fin 3) (u : (A.field i)ˣ)
    (hu : 1 - (u : A.field i) ∈ lattice (A.field i) (A.stationaryDepth i : ℤ)) :
    normQuasiChar F (A.field i) lambda u = 1 := by
  exact quasiChar_trivial_of_one_sub_mem F lambda (depth_ledger A 1).1 hn _
    (A.stationaryNorm_mem hres i u hu)

/-- The lower chart at the original numerator uses the actual norm of
its actual upper trace. This applies to every nontrivial lower norm
character, on the whole lower stationary ideal. -/
theorem origin_lowerChart (hres : residueDegree F K = 1)
    (i : Fin 3) (ω : NormCharacter F (A.field i)) (hω : ω ≠ 1)
    (u : Fˣ) (hu : 1 - (u : F) ∈ lattice F (A.lowerDepth i)) :
    ω.1 u = originAddChar F P ((A.t 1 : ℤ) + 1)
      (Algebra.norm F (Algebra.trace (A.field i) K A.Y) * (1 - (u : F))) := by
  have hf : ord F (A.f i) = ((-(A.t i : ℤ) : ℤ) : WithTop ℤ) := by
    rw [← P.laurentEquiv.apply_symm_apply (A.f i), P.laurentEquiv_order]
    exact (A.edge i).2.2.2.2.2.2.1
  have hcharts := dyadicEqual_lowerCharts F (A.field i)
    (originLine_degrees F K (A.g i) (A.nontrivial i)).1
    (origin_residueDegrees F K hres (A.field i)).1 P
    (A.f i) (A.z i) (A.edge i).1 (A.edge i).2.1
    (A.t i) (A.edge i).2.2.2.1 (A.edge i).2.2.2.2.1
    (A.edge i).2.2.1 hf (A.edge i).2.2.2.2.2.2.2.2 ω hω (A.t 1)
    (by exact_mod_cast (A.edge 1).2.2.2.2.1)
  rw [(A.exact_origin i).2.1, (A.scalar_data i).2.2.2.2]
  exact hcharts.2.2.2.2.2.1 u hu

/-- The complete zero-translation branch of `D:EQ:min-origin`.
The core chart is the one furnished by `twist`; no stationarity of the
twisted character is assumed. When `n ≤ q₀`, the single numerator `Y`
works on all three upper and lower sides, even with unequal breaks. -/
theorem minimalOrigin_zero (hres : residueDegree F K = 1)
    (χ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hchart : ∀ (i : Fin 3) (u : (A.field i)ˣ),
      u ∈ unitFiltration (A.field i) (A.stationaryDepth i) →
        χ i u = tracePullbackAddChar F (A.field i)
          (originAddChar F P ((A.t 1 : ℤ) + 1))
          (Algebra.norm (A.field i) A.Y * (1 - (u : A.field i))))
    (lambda : ContinuousQuasiChar F)
    (hn : multiplicativeConductorExponent F lambda ≤ A.stationaryDepth 1) :
    ord K A.Y = ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ) ∧
      ∀ i : Fin 3,
        (∀ (u : (A.field i)ˣ),
          1 - (u : A.field i) ∈ lattice (A.field i) (A.stationaryDepth i : ℤ) →
          (χ i * normQuasiChar F (A.field i) lambda) u =
            tracePullbackAddChar F (A.field i) (originAddChar F P ((A.t 1 : ℤ) + 1))
              (Algebra.norm (A.field i) A.Y * (1 - (u : A.field i)))) ∧
        (∀ (ω : NormCharacter F (A.field i)), ω ≠ 1 → ∀ (u : Fˣ),
          1 - (u : F) ∈ lattice F (A.lowerDepth i) →
          ω.1 u = originAddChar F P ((A.t 1 : ℤ) + 1)
            (Algebra.norm F (Algebra.trace (A.field i) K A.Y) * (1 - (u : F)))) := by
  refine ⟨(A.origin_orders hres).1, fun i ↦ ⟨?_, A.origin_lowerChart hres i⟩⟩
  intro u hu
  change χ i u * normQuasiChar F (A.field i) lambda u = _
  rw [A.minimalNormPullback_trivial hres lambda hn i u hu, mul_one]
  exact hchart i u ((A.modelDomain_iff i u).2 hu)

/-- The norm-phase conversion from `Origin`, on its whole lower stationary
ideal, with the simultaneous coefficients and fields made explicit. -/
theorem origin_normPhase (hres : residueDegree F K = 1) (i : Fin 3)
    (x : A.field i) (hx : x ∈ lattice (A.field i) (A.lowerDepth i)) :
    tracePullbackAddChar F (A.field i) (originAddChar F P ((A.t 1 : ℤ) + 1))
      (algebraMap F (A.field i) (A.beta i) * x) =
        originAddChar F P ((A.t 1 : ℤ) + 1) (A.beta i * Algebra.norm F x) := by
  have hf : ord F (A.f i) = ((-(A.t i : ℤ) : ℤ) : WithTop ℤ) := by
    rw [← P.laurentEquiv.apply_symm_apply (A.f i), P.laurentEquiv_order]
    exact (A.edge i).2.2.2.2.2.2.1
  exact originAddChar_normPhase F (A.field i)
    (originLine_degrees F K (A.g i) (A.nontrivial i)).1
    (origin_residueDegrees F K hres (A.field i)).1 P (A.f i) (A.z i) (A.edge i).1
    (A.t i) (A.lowerDepth i) (A.t 1) (depth_ledger A i).2.2.1 (by
      obtain ⟨a, ha⟩ := (A.edge i).2.2.2.2.1
      simp only [lowerDepth]
      omega) (by
      rw [(A.edge i).2.2.2.2.2.2.2.2]
      simp only [lowerDepth, Nat.cast_add, Nat.cast_one]
      omega) (A.edge i).2.2.1 hf.ge x hx

/-- A whole-ideal base chart and the norm-phase identity evaluate the
entire quadratic norm pullback, including both trace and norm terms. -/
private theorem normPullback_of_normPhase (hres : residueDegree F K = 1)
    (lambda : ContinuousQuasiChar F) (b : F)
    (hbase : ∀ u : Fˣ, 1 - (u : F) ∈ lattice F (A.stationaryDepth 1 : ℤ) →
      lambda u = originAddChar F P ((A.t 1 : ℤ) + 1) (b * (1 - (u : F))))
    (i : Fin 3) (q : A.field i) (u : (A.field i)ˣ)
    (hu : 1 - (u : A.field i) ∈ lattice (A.field i) (A.stationaryDepth i : ℤ))
    (hphase : tracePullbackAddChar F (A.field i)
      (originAddChar F P ((A.t 1 : ℤ) + 1)) (q * (1 - (u : A.field i))) =
        originAddChar F P ((A.t 1 : ℤ) + 1) (b * Algebra.norm F (1 - (u : A.field i)))) :
    normQuasiChar F (A.field i) lambda u =
      tracePullbackAddChar F (A.field i) (originAddChar F P ((A.t 1 : ℤ) + 1))
        ((algebraMap F (A.field i) b + q) * (1 - (u : A.field i))) := by
  let L := A.field i
  let z : L := 1 - (u : L)
  let Ψ := originAddChar F P ((A.t 1 : ℤ) + 1)
  let Φ := tracePullbackAddChar F L Ψ
  have htrace : Φ (algebraMap F L b * z) = Ψ (b * Algebra.trace F L z) := by
    change Ψ (Algebra.trace F L (algebraMap F L b * z)) = _
    rw [← Algebra.smul_def, map_smul, Algebra.smul_def, Algebra.algebraMap_self_apply]
  have hinc : 1 - (normUnits F L u : F) = Algebra.trace F L z + Algebra.norm F z := by
    have he := norm_one_sub_charTwo F L
      (originLine_degrees F K (A.g i) (A.nontrivial i)).1 z
    change Algebra.norm F (1 - (1 - (u : L))) = _ at he
    rw [sub_sub_cancel] at he
    change 1 - Algebra.norm F (u : L) = _
    rw [he, CharTwo.sub_eq_add]
    simp only [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hlambda := hbase (normUnits F L u) (A.stationaryNorm_mem hres i u hu)
  change lambda (normUnits F L u) = Ψ (b * (1 - (normUnits F L u : F))) at hlambda
  rw [hinc, mul_add, ContinuousAddChar.map_add_eq_mul] at hlambda
  change lambda (normUnits F L u) = Φ ((algebraMap F L b + q) * z)
  rw [add_mul, ContinuousAddChar.map_add_eq_mul, htrace, hphase]
  exact hlambda

/-- Translation by the third field leaves its upper trace unchanged.
Its upper norm retains the complete quadratic term `X²`. These are the
third-side identities used at the end of `D:EQ:min-origin`. -/
theorem thirdMoved_norm_trace (X : A.field 2) :
    Algebra.norm (A.field 2) (A.Y + (X : K)) =
        Algebra.norm (A.field 2) A.Y + X ^ 2 +
          algebraMap F (A.field 2) (A.root 2) * X ∧
      Algebra.trace (A.field 2) K (A.Y + (X : K)) =
        Algebra.trace (A.field 2) K A.Y := by
  have hfix : A.g 2 (X : K) = X :=
    (IntermediateField.mem_fixedField_iff _ _).mp X.property _ (Or.inr rfl)
  have hY : A.g 2 A.Y = A.Y + algebraMap F K (A.root 2) := by
    linear_combination (A.exact_origin 2).1
  constructor
  · apply (algebraMap (A.field 2) K).injective
    rw [(originLine_norm_trace F K (A.g 2) (A.nontrivial 2) _).1]
    simp only [map_add, map_pow, map_mul, ← IsScalarTower.algebraMap_apply]
    rw [(originLine_norm_trace F K (A.g 2) (A.nontrivial 2) A.Y).1, hfix, hY]
    ring_nf
    simp [CharTwo.two_eq_zero, mul_comm]
  · apply (algebraMap (A.field 2) K).injective
    rw [(originLine_norm_trace F K (A.g 2) (A.nontrivial 2) _).2,
      (originLine_norm_trace F K (A.g 2) (A.nontrivial 2) A.Y).2, map_add, hfix]
    rw [add_add_add_comm, CharTwo.add_self_eq_zero, add_zero]

/-- The third-side affine error is integral throughout the minimal range.
The actual norm is retained, and the whole-lattice hypothesis permits zero
and negative integer depths. -/
theorem minimalThird_error_mem (hres : residueDegree F K = 1)
    {n : ℕ} (hn : n < A.twistThreshold) (X : A.field 2)
    (hX : X ∈ lattice (A.field 2) ((A.t 1 : ℤ) + 1 - (n : ℤ))) :
    X ^ 2 - algebraMap F (A.field 2) (Algebra.norm F X) ∈ lattice (A.field 2) 0 := by
  rw [quadratic_square_sub_norm F (A.field 2)
    (originLine_degrees F K (A.g 2) (A.nontrivial 2)).1 X]
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F (A.field 2)
    (origin_residueDegrees F K hres (A.field 2)).1
  have ht := trace_mem_lattice_floor F (A.field 2) pi hpi hgen _ hX
  rw [(edge_ramification A hres 2).1, (A.edge 2).2.2.2.2.2.2.2.2,
    A.third_break] at ht
  change ((((A.t 1 : ℤ) + 1 - (n : ℤ) + ((A.t 1 + 1 : ℕ) : ℤ)) / 2 : ℤ) :
    WithTop ℤ) ≤ ord F (Algebra.trace F (A.field 2) X) at ht
  have ht' : algebraMap F (A.field 2) (Algebra.trace F (A.field 2) X) ∈
      lattice (A.field 2) (2 * (((A.t 1 : ℤ) + 1 - (n : ℤ) +
        ((A.t 1 + 1 : ℕ) : ℤ)) / 2)) := by
    change _ ≤ ord (A.field 2) (algebraMap F (A.field 2) _)
    rw [ord_algebraMap, (edge_ramification A hres 2).1, two_nsmul]
    simpa only [← WithTop.coe_add, two_mul] using add_le_add ht ht
  apply lattice_antitone (A.field 2) ?_ (mul_mem_lattice (A.field 2) ht' hX)
  have hs := A.smallest
  obtain ⟨a, ha⟩ := (A.edge 0).2.2.2.2.1
  obtain ⟨b, hb⟩ := (A.edge 1).2.2.2.2.1
  simp only [twistThreshold] at hn
  push_cast
  omega

/-- On the third field in the equal-break case, the entire norm pullback
has coefficient `n₃X + d₃X`. Its base chart is the one constructed by
`minimalNormChoice`, on the whole base ideal, and no critical norm
surjectivity or stationarity of the pulled-back character is assumed. -/
theorem minimalThirdPullback (hres : residueDegree F K = 1)
    (hequal : A.t 0 = A.t 1) (lambda : ContinuousQuasiChar F)
    (hn : multiplicativeConductorExponent F lambda < A.twistThreshold)
    (X : A.field 2)
    (hX : X ∈ lattice (A.field 2)
      ((A.t 1 : ℤ) + 1 - (multiplicativeConductorExponent F lambda : ℤ)))
    (hbase : ∀ u : Fˣ, 1 - (u : F) ∈ lattice F (A.stationaryDepth 1 : ℤ) →
      lambda u = originAddChar F P ((A.t 1 : ℤ) + 1)
        (Algebra.norm F X * (1 - (u : F))))
    (u : (A.field 2)ˣ)
    (hu : 1 - (u : A.field 2) ∈ lattice (A.field 2) (A.stationaryDepth 2 : ℤ)) :
    normQuasiChar F (A.field 2) lambda u =
      tracePullbackAddChar F (A.field 2) (originAddChar F P ((A.t 1 : ℤ) + 1))
        ((algebraMap F (A.field 2) (Algebra.norm F X) +
          algebraMap F (A.field 2) (A.root 2) * X) * (1 - (u : A.field 2))) := by
  let L := A.field 2
  let d : L := algebraMap F L (A.root 2)
  let z : L := 1 - (u : L)
  let Ψ := originAddChar F P ((A.t 1 : ℤ) + 1)
  let Φ := tracePullbackAddChar F L Ψ
  have hdord : ord L d = (0 : WithTop ℤ) := by
    dsimp only [d, L]
    rw [ord_algebraMap, (edge_ramification A hres 2).1,
      (A.scalar_data 2).2.1, A.third_break]
    norm_num
  have hd : d ≠ 0 := (ord_ne_top_iff L).mp (by rw [hdord]; exact WithTop.coe_ne_top)
  have hβ : A.beta 2 ≠ 0 := by
    intro h
    have hv := (A.scalar_data 2).2.2.1
    rw [h, ord_zero] at hv
    exact WithTop.top_ne_coe hv
  have hdepth : A.lowerDepth 2 ≤
      (A.t 1 : ℤ) + 1 - (multiplicativeConductorExponent F lambda : ℤ) +
        (A.stationaryDepth 2 : ℤ) := by
    have ht := A.third_break
    obtain ⟨b, hb⟩ := (A.edge 1).2.2.2.2.1
    simp only [twistThreshold, hequal] at hn
    simp only [lowerDepth, stationaryDepth, hequal]
    norm_num
    omega
  have hy : X / d * z ∈ lattice L (A.lowerDepth 2) := by
    rw [div_mul_eq_mul_div]
    apply (div_mem_lattice_iff L d (X * z) 0 (A.lowerDepth 2) hdord).mpr
    simpa only [zero_add] using
      lattice_antitone L hdepth (mul_mem_lattice L hX hu)
  have hphase := A.origin_normPhase hres 2 (X / d * z) hy
  have hleft : algebraMap F L (A.beta 2) * (X / d * z) = d * X * z := by
    rw [← (A.scalar_data 2).1, map_pow]
    change d ^ 2 * (X / d * z) = d * X * z
    field_simp
  have hright : A.beta 2 * Algebra.norm F (X / d * z) =
      Algebra.norm F X * Algebra.norm F z := by
    rw [map_mul, div_eq_mul_inv, map_mul, Algebra.norm_inv,
      show Algebra.norm F d = A.beta 2 from (A.scalar_data 2).2.2.2.2]
    field_simp
  change Φ (algebraMap F L (A.beta 2) * (X / d * z)) =
    Ψ (A.beta 2 * Algebra.norm F (X / d * z)) at hphase
  rw [hleft, hright] at hphase
  exact A.normPullback_of_normPhase hres lambda (Algebra.norm F X) hbase 2 (d * X) u hu
    hphase

/-- The preserved third-side construction works for the same `X` as the
first two sides: only its lattice membership and proved base chart enter. -/
theorem minimalThird_upperChart (hres : residueDegree F K = 1)
    (hequal : A.t 0 = A.t 1) (χ : ContinuousQuasiChar (A.field 2))
    (hchart : ∀ u : (A.field 2)ˣ,
      u ∈ unitFiltration (A.field 2) (A.stationaryDepth 2) →
        χ u = tracePullbackAddChar F (A.field 2)
          (originAddChar F P ((A.t 1 : ℤ) + 1))
          (Algebra.norm (A.field 2) A.Y * (1 - (u : A.field 2))))
    (lambda : ContinuousQuasiChar F)
    (hn : multiplicativeConductorExponent F lambda < A.twistThreshold)
    (X : A.field 2)
    (hX : X ∈ lattice (A.field 2)
      ((A.t 1 : ℤ) + 1 - (multiplicativeConductorExponent F lambda : ℤ)))
    (hbase : ∀ u : Fˣ, 1 - (u : F) ∈ lattice F (A.stationaryDepth 1 : ℤ) →
      lambda u = originAddChar F P ((A.t 1 : ℤ) + 1)
        (Algebra.norm F X * (1 - (u : F))))
    (u : (A.field 2)ˣ)
    (hu : 1 - (u : A.field 2) ∈ lattice (A.field 2) (A.stationaryDepth 2 : ℤ)) :
    (χ * normQuasiChar F (A.field 2) lambda) u =
      tracePullbackAddChar F (A.field 2) (originAddChar F P ((A.t 1 : ℤ) + 1))
        (Algebra.norm (A.field 2) (A.Y + (X : K)) * (1 - (u : A.field 2))) := by
  change χ u * normQuasiChar F (A.field 2) lambda u = _
  rw [hchart u ((A.modelDomain_iff 2 u).2 hu),
    A.minimalThirdPullback hres hequal lambda hn X hX hbase u hu,
    ← ContinuousAddChar.map_add_eq_mul, ← add_mul]
  apply phase_eq_of_sub_mem _ (A.modelAddChar_conductor hres 2)
  rw [(A.thirdMoved_norm_trace X).1]
  have hs : (A.stationaryDepth 2 : ℤ) = A.additiveModulus 2 := by
    have ht := A.third_break
    obtain ⟨b, hb⟩ := (A.edge 1).2.2.2.2.1
    simp only [stationaryDepth, additiveModulus, hequal]
    norm_num
    omega
  have he := (lattice (A.field 2) 0).neg_mem (A.minimalThird_error_mem hres hn X hX)
  have hp := mul_mem_lattice (A.field 2) he hu
  simp only [neg_sub, zero_add, hs] at hp
  convert hp using 1; ring

/-- The complete third-side branch of `D:EQ:min-origin` when the breaks
are equal. The same subcritical norm construction supplies `X`, including
the zero choice at small conductors. The numerator is the actual `Y + X`,
its valuation is exact, and both full stationary identities are proved.
The core chart is supplied by `twist`; uniformizer values of the continuous
quasi-characters remain unrestricted. -/
theorem minimalOrigin_third (hres : residueDegree F K = 1)
    (hequal : A.t 0 = A.t 1) (χ : ContinuousQuasiChar (A.field 2))
    (hchart : ∀ u : (A.field 2)ˣ,
      u ∈ unitFiltration (A.field 2) (A.stationaryDepth 2) →
        χ u = tracePullbackAddChar F (A.field 2)
          (originAddChar F P ((A.t 1 : ℤ) + 1))
          (Algebra.norm (A.field 2) A.Y * (1 - (u : A.field 2))))
    (lambda : ContinuousQuasiChar F)
    (hn : multiplicativeConductorExponent F lambda < A.twistThreshold) :
    let n := multiplicativeConductorExponent F lambda
    ∃ X : A.field 2,
      X ∈ lattice (A.field 2) ((A.t 1 : ℤ) + 1 - (n : ℤ)) ∧
      (n ≤ A.stationaryDepth 1 → X = 0) ∧
      (A.stationaryDepth 1 < n →
        ord (A.field 2) X = (((A.t 1 : ℤ) + 1 - (n : ℤ) : ℤ) : WithTop ℤ)) ∧
      ord K (A.Y + (X : K)) = ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ) ∧
      (∀ u : (A.field 2)ˣ,
        1 - (u : A.field 2) ∈ lattice (A.field 2) (A.stationaryDepth 2 : ℤ) →
        (χ * normQuasiChar F (A.field 2) lambda) u =
          tracePullbackAddChar F (A.field 2) (originAddChar F P ((A.t 1 : ℤ) + 1))
            (Algebra.norm (A.field 2) (A.Y + (X : K)) * (1 - (u : A.field 2)))) ∧
      (∀ (ω : NormCharacter F (A.field 2)), ω ≠ 1 → ∀ u : Fˣ,
        1 - (u : F) ∈ lattice F (A.lowerDepth 2) →
        ω.1 u = originAddChar F P ((A.t 1 : ℤ) + 1)
          (Algebra.norm F (Algebra.trace (A.field 2) K (A.Y + (X : K))) * (1 - (u : F)))) := by
  obtain ⟨X, hX, hzero, horder, hbase⟩ := A.minimalNormChoice hres lambda hn
  refine ⟨X, hX, hzero, horder, A.minimalMovedOrigin_order hres hn X hX, ?_, ?_⟩
  · exact A.minimalThird_upperChart hres hequal χ hchart lambda hn X hX hbase
  · intro ω hω u hu
    rw [(A.thirdMoved_norm_trace X).2]
    exact A.origin_lowerChart hres 2 ω hω u hu

omit [IsGalois F K] [CharP F 2] [CharP K 2] in
private theorem minimal_adjustment_ledger {n : ℕ} (hn : n < A.twistThreshold)
    (i : Fin 3) :
    let h : ℤ := (n : ℤ) - ((A.t 1 : ℤ) + 1)
    2 * ((A.t 1 : ℤ) - A.t i) + A.lowerDepth i ≤
        (if i = 0 then (A.t 1 : ℤ) - A.t 0 else 0) - h +
          (A.stationaryDepth i : ℤ) ∧
      ((A.t 1 : ℤ) - A.t i) + ((A.t 1 : ℤ) + 1) ≤
        ((A.t 1 : ℤ) + 1) / 2 + ((A.t 1 : ℤ) - A.t 0) / 2 - h +
          (A.stationaryDepth i : ℤ) ∧
      (A.t 1 : ℤ) + 1 ≤
        2 * (((A.t 1 : ℤ) + 1) / 2 - (h + 1) / 2) + A.lowerDepth i := by
  have hs := A.smallest
  have ht := A.third_break
  obtain ⟨a, ha⟩ := (A.edge 0).2.2.2.2.1
  obtain ⟨b, hb⟩ := (A.edge 1).2.2.2.2.1
  simp only [twistThreshold] at hn
  dsimp only
  fin_cases i <;> simp only [stationaryDepth, lowerDepth] <;> norm_num
  all_goals try rw [show A.t ⟨2, by decide⟩ = A.t 1 from ht]
  all_goals omega

/-- The actual adjustment argument lies in the whole norm-phase ideal,
and the complete common error vanishes at the base character modulus.
These are the two estimates used in `D:EQ:pullback-adjust` at minimal
conductors, including negative values of `h = n - T₂`. -/
theorem minimalAdjustment_mem (hres : residueDegree F K = 1)
    {n : ℕ} (hn : n < A.twistThreshold) (X : A.field 2)
    (hX : X ∈ lattice (A.field 2) ((A.t 1 : ℤ) + 1 - (n : ℤ)))
    (i : Fin 3) (z : A.field i)
    (hz : z ∈ lattice (A.field i) (A.stationaryDepth i : ℤ)) :
    A.thirdQ X i / algebraMap F (A.field i) (A.beta i) * z ∈
        lattice (A.field i) (A.lowerDepth i) ∧
      A.thirdError X / A.beta i * Algebra.norm F z ∈
        lattice F ((A.t 1 : ℤ) + 1) := by
  let h : ℤ := (n : ℤ) - ((A.t 1 : ℤ) + 1)
  have hX' : X ∈ lattice (A.field 2) (-h) := by
    simpa only [h, neg_sub] using hX
  have hl := A.minimal_adjustment_ledger hn i
  have hβ : ord (A.field i) (algebraMap F (A.field i) (A.beta i)) =
      ((2 * ((A.t 1 : ℤ) - A.t i) : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, (edge_ramification A hres i).1,
      (A.scalar_data i).2.2.1, ← WithTop.coe_nsmul]
    congr 1
  constructor
  · rw [div_mul_eq_mul_div]
    apply (div_mem_lattice_iff _ _ _ _ _ hβ).2
    exact lattice_antitone _ hl.1 (mul_mem_lattice _ (A.thirdQ_bound hres X h hX' i) hz)
  · have hnz : Algebra.norm F z ∈ lattice F (A.stationaryDepth i : ℤ) := by
      change _ ≤ ord F (norm F (A.field i) z)
      rw [ord_norm, (origin_residueDegrees F K hres (A.field i)).1, one_nsmul]
      exact hz
    rw [div_mul_eq_mul_div]
    apply (div_mem_lattice_iff _ _ _ _ _ (A.scalar_data i).2.2.1).2
    exact lattice_antitone _ hl.2.1
      (mul_mem_lattice _ (A.thirdError_bound hres X h hX') hnz)

/-- The first two full pulled-back characters have coefficient `n₃X + Qᵢ`.
The common affine error in the exact norm of `Qᵢ` is discarded only after
its product with the actual norm of the variable is proved trivial. -/
theorem minimalMovedPullback (hres : residueDegree F K = 1)
    (lambda : ContinuousQuasiChar F)
    (hn : multiplicativeConductorExponent F lambda < A.twistThreshold)
    (X : A.field 2)
    (hX : X ∈ lattice (A.field 2)
      ((A.t 1 : ℤ) + 1 - (multiplicativeConductorExponent F lambda : ℤ)))
    (hbase : ∀ u : Fˣ, 1 - (u : F) ∈ lattice F (A.stationaryDepth 1 : ℤ) →
      lambda u = originAddChar F P ((A.t 1 : ℤ) + 1)
        (Algebra.norm F X * (1 - (u : F))))
    (i : Fin 3) (hi : i ≠ 2) (u : (A.field i)ˣ)
    (hu : 1 - (u : A.field i) ∈ lattice (A.field i) (A.stationaryDepth i : ℤ)) :
    normQuasiChar F (A.field i) lambda u =
      tracePullbackAddChar F (A.field i) (originAddChar F P ((A.t 1 : ℤ) + 1))
        ((algebraMap F (A.field i) (Algebra.norm F X) + A.thirdQ X i) *
          (1 - (u : A.field i))) := by
  let L := A.field i
  let z : L := 1 - (u : L)
  let Ψ := originAddChar F P ((A.t 1 : ℤ) + 1)
  let Φ := tracePullbackAddChar F L Ψ
  have hβ : A.beta i ≠ 0 := by
    intro h
    have hv := (A.scalar_data i).2.2.1
    rw [h, ord_zero] at hv
    exact WithTop.top_ne_coe hv
  have hβ' : algebraMap F L (A.beta i) ≠ 0 := (map_ne_zero (algebraMap F L)).2 hβ
  obtain ⟨harg, herr⟩ := A.minimalAdjustment_mem hres hn X hX i z hu
  have hphase := A.origin_normPhase hres i
    (A.thirdQ X i / algebraMap F L (A.beta i) * z) harg
  have hleft : algebraMap F L (A.beta i) *
      (A.thirdQ X i / algebraMap F L (A.beta i) * z) = A.thirdQ X i * z := by
    field_simp
  have hright : A.beta i * Algebra.norm F
      (A.thirdQ X i / algebraMap F L (A.beta i) * z) =
        (Algebra.norm F X + A.thirdError X / A.beta i) * Algebra.norm F z := by
    rw [map_mul, div_eq_mul_inv, map_mul, Algebra.norm_inv, Algebra.norm_algebraMap,
      (originLine_degrees F K (A.g i) (A.nontrivial i)).1, A.thirdQ_norm X i hi]
    field_simp
  change Φ (algebraMap F L (A.beta i) *
    (A.thirdQ X i / algebraMap F L (A.beta i) * z)) =
      Ψ (A.beta i * Algebra.norm F
        (A.thirdQ X i / algebraMap F L (A.beta i) * z)) at hphase
  rw [hleft, hright] at hphase
  have hphase' : Φ (A.thirdQ X i * z) = Ψ (Algebra.norm F X * Algebra.norm F z) := by
    rw [hphase]
    apply phase_eq_of_sub_mem Ψ (originAddChar_conductor F P ((A.t 1 : ℤ) + 1))
    convert herr using 1; ring
  exact A.normPullback_of_normPhase hres lambda (Algebra.norm F X) hbase i (A.thirdQ X i)
    u hu hphase'

/-- The lower stationary coefficient is the norm of the actual moved
upper trace, `(dᵢ + a)² = βᵢ + a²`. Its full error is trivial throughout
the minimal range on each of the first two lower ideals. -/
theorem minimalMoved_lowerChart (hres : residueDegree F K = 1)
    {n : ℕ} (hn : n < A.twistThreshold) (X : A.field 2)
    (hX : X ∈ lattice (A.field 2) ((A.t 1 : ℤ) + 1 - (n : ℤ)))
    (i : Fin 3) (hi : i ≠ 2) (ω : NormCharacter F (A.field i)) (hω : ω ≠ 1)
    (u : Fˣ) (hu : 1 - (u : F) ∈ lattice F (A.lowerDepth i)) :
    ω.1 u = originAddChar F P ((A.t 1 : ℤ) + 1)
      (Algebra.norm F (Algebra.trace (A.field i) K (A.Y + (X : K))) *
        (1 - (u : F))) := by
  rw [A.origin_lowerChart hres i ω hω u hu, (A.exact_origin i).2.1,
    (A.scalar_data i).2.2.2.2]
  have he := (A.thirdC_norm_trace X i hi).2
  change Algebra.trace (A.field i) K (A.Y + (X : K)) = _ at he
  rw [he, Algebra.norm_algebraMap,
    (originLine_degrees F K (A.g i) (A.nontrivial i)).1]
  simp only [add_sq, CharTwo.two_eq_zero, zero_mul, add_zero, (A.scalar_data i).1]
  apply phase_eq_of_sub_mem _ (originAddChar_conductor F P ((A.t 1 : ℤ) + 1))
  let h : ℤ := (n : ℤ) - ((A.t 1 : ℤ) + 1)
  have ha := A.thirdTrace_bound hres X h (by simpa only [h, neg_sub] using hX)
  have haa := mul_mem_lattice F ha ha
  have hp := (lattice F ((A.t 1 : ℤ) + 1)).neg_mem
    (lattice_antitone F (by
      simpa only [two_mul] using (A.minimal_adjustment_ledger hn i).2.2)
      (mul_mem_lattice F haa hu))
  convert hp using 1; ring

/-- The full construction in `D:EQ:min-origin` for a realized core family.
A single subcritical norm choice supplies the first two upper and lower
charts for every `n < twistThreshold`, and all three when the breaks agree.
The zero branch and the exact nonzero shell are retained. -/
theorem minimalOrigin_of_core (hres : residueDegree F K = 1)
    (χ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hchart : ∀ (i : Fin 3) (u : (A.field i)ˣ),
      u ∈ unitFiltration (A.field i) (A.stationaryDepth i) →
        χ i u = tracePullbackAddChar F (A.field i)
          (originAddChar F P ((A.t 1 : ℤ) + 1))
          (Algebra.norm (A.field i) A.Y * (1 - (u : A.field i))))
    (lambda : ContinuousQuasiChar F)
    (hn : multiplicativeConductorExponent F lambda < A.twistThreshold) :
    let n := multiplicativeConductorExponent F lambda
    ∃ X : A.field 2,
      X ∈ lattice (A.field 2) ((A.t 1 : ℤ) + 1 - (n : ℤ)) ∧
      (n ≤ A.stationaryDepth 1 → X = 0) ∧
      (A.stationaryDepth 1 < n →
        ord (A.field 2) X = (((A.t 1 : ℤ) + 1 - (n : ℤ) : ℤ) : WithTop ℤ)) ∧
      ord K (A.Y + (X : K)) = ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ) ∧
      ∀ i : Fin 3, i ≠ 2 ∨ A.t 0 = A.t 1 →
        (∀ u : (A.field i)ˣ,
          1 - (u : A.field i) ∈ lattice (A.field i) (A.stationaryDepth i : ℤ) →
          (χ i * normQuasiChar F (A.field i) lambda) u =
            tracePullbackAddChar F (A.field i) (originAddChar F P ((A.t 1 : ℤ) + 1))
              (Algebra.norm (A.field i) (A.Y + (X : K)) * (1 - (u : A.field i)))) ∧
        (∀ (ω : NormCharacter F (A.field i)), ω ≠ 1 → ∀ u : Fˣ,
          1 - (u : F) ∈ lattice F (A.lowerDepth i) →
          ω.1 u = originAddChar F P ((A.t 1 : ℤ) + 1)
            (Algebra.norm F (Algebra.trace (A.field i) K (A.Y + (X : K))) *
              (1 - (u : F)))) := by
  obtain ⟨X, hX, hzero, horder, hbase⟩ := A.minimalNormChoice hres lambda hn
  refine ⟨X, hX, hzero, horder, A.minimalMovedOrigin_order hres hn X hX, ?_⟩
  intro i hside
  rcases eq_or_ne i 2 with rfl | hi
  · have hequal : A.t 0 = A.t 1 := hside.resolve_left (by simp)
    refine ⟨A.minimalThird_upperChart hres hequal (χ 2) (hchart 2) lambda hn X hX hbase, ?_⟩
    intro ω hω u hu
    rw [(A.thirdMoved_norm_trace X).2]
    exact A.origin_lowerChart hres 2 ω hω u hu
  · refine ⟨?_, A.minimalMoved_lowerChart hres hn X hX i hi⟩
    intro u hu
    change χ i u * normQuasiChar F (A.field i) lambda u = _
    rw [hchart i u ((A.modelDomain_iff i u).2 hu),
      A.minimalMovedPullback hres lambda hn X hX hbase i hi u hu,
      ← ContinuousAddChar.map_add_eq_mul, ← add_mul]
    rw [show A.Y + (X : K) = A.thirdC X from rfl,
      (A.thirdC_norm_trace X i hi).1, add_assoc]

end SimultaneousASGenerators

/-- **The full stationary properties (Lemma 11.8, `D:EQ:min-origin`).**
For an actual primitive compatible family in the minimal conductor row,
one third-field translation of the constructed origin has the exact
valuation and both full stationary identities on the first two fields.
When the breaks agree, the same element works on all three fields.

Minimality of the first conductor suffices: `twist` constructs a core
family and common base character and forces `n < twistThreshold`.
Thus no auxiliary stationary chart or norm representative is assumed.
The characters are continuous quasi-characters, with unrestricted
uniformizer values, and the lower coefficients are actual trace norms. -/
theorem minimalOrigin (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (A : SimultaneousASGenerators F K P)
    (Θ : ContinuousQuasiChar K)
    (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hcompatible : ∀ i, normQuasiChar (A.field i) K (θ i) = Θ)
    (hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Θ)
    (hminimal : multiplicativeConductorExponent (A.field 0) (θ 0) = A.minimalConductor 0) :
    ∃ X : A.field 2,
      ord K (A.Y + (X : K)) = ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ) ∧
      ∀ i : Fin 3, i ≠ 2 ∨ A.t 0 = A.t 1 →
        (∀ u : (A.field i)ˣ,
          1 - (u : A.field i) ∈ lattice (A.field i) (A.stationaryDepth i : ℤ) →
          θ i u = tracePullbackAddChar F (A.field i)
            (originAddChar F P ((A.t 1 : ℤ) + 1))
            (Algebra.norm (A.field i) (A.Y + (X : K)) * (1 - (u : A.field i)))) ∧
        (∀ (ω : NormCharacter F (A.field i)), ω ≠ 1 → ∀ u : Fˣ,
          1 - (u : F) ∈ lattice F (A.lowerDepth i) →
          ω.1 u = originAddChar F P ((A.t 1 : ℤ) + 1)
            (Algebra.norm F (Algebra.trace (A.field i) K (A.Y + (X : K))) *
              (1 - (u : F)))) := by
  obtain ⟨Θc, χ, lambda, _, _, _, _, _, hchart, hrealize, _, hranges⟩ :=
    twist hres P A Θ θ hcompatible hprimitive
  have hn : multiplicativeConductorExponent F lambda < A.twistThreshold := by
    by_contra h
    have hlt := (hranges.2 (Nat.le_of_not_gt h) 0).2.2
    change A.minimalConductor 0 < multiplicativeConductorExponent (A.field 0) (θ 0) at hlt
    rw [hminimal] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨X, _, _, _, horder, hstationary⟩ := A.minimalOrigin_of_core hres χ hchart lambda hn
  refine ⟨X, horder, fun i hi ↦ ?_⟩
  obtain ⟨hu, hl⟩ := hstationary i hi
  refine ⟨?_, hl⟩
  simpa only [hrealize i] using hu

end
end LanglandsSecondMainLemma.Dyadic.Equal
