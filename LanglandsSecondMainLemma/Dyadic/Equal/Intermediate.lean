import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsFirstMainLemma.Ramification.NormRepresentatives
import LanglandsSecondMainLemma.Dyadic.Equal.Twist
import LanglandsSecondMainLemma.Dyadic.Equal.ThirdNorm

/-!
# Dyadic / Equal / Intermediate

Paper Theorem 11.11 (`D:EQ:intermediate`). The third-field representative is
chosen only at the permitted subcritical precision. The original lower
coefficients are retained; the moved upper traces need not give lower
stationary coefficients. All depth arithmetic is in the integers.

The base coefficient, norm representative, common base ideal, even upper
conductors, and moved numerator's exact norm valuations are constructed
below. The full pullback chart retains the correction error until the
actual additive conductor kills it. Applying the exact `ThirdNorm`
identities then gives the common numerator `C = Y + X`, with the original
lower coefficients and identical `E₂(C) + a²` phase on both sides.
-/

namespace LanglandsSecondMainLemma.Dyadic.Equal

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

section Field
variable (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [CharP E 2]

/-- Extract a field coefficient from the actual FML stationary class on
the entire specified ideal. -/
private theorem coefficient_exists (χ : LocalQuasiCharData E) (ψ : LocalAddCharData E)
    {r : ℕ} (hr : IsLamprechtStationaryDepth χ.conductor r) :
    ∃ B : Eˣ,
      ord E (B : E) = ((-ψ.conductor - (χ.conductor : ℤ) : ℤ) : WithTop ℤ) ∧
      ∀ u : Eˣ, 1 - (u : E) ∈ lattice E (r : ℤ) →
        χ.character u = ψ.character ((B : E) * (1 - (u : E))) := by
  obtain ⟨Γ⟩ := AdmissibleGamma.exists_admissible (F := E) (χ := χ) (ψ := ψ)
  obtain ⟨c, hc⟩ := latticeQuotientMk_surjective E
    (sub_le_sub_left hr.int_le_conductor (χ.conductor : ℤ))
    (stationaryNumeratorClass E χ ψ (χ.conductor : ℤ) hr Γ Γ.property)
  let β := lamprechtStationaryRepresentativeUnit E χ ψ hr Γ c hc
  refine ⟨β / (Γ : Eˣ), ?_, ?_⟩
  · rw [Units.val_div_eq_div_val, ord_div,
      lamprechtStationaryRepresentativeUnit_ord, Γ.property]
    norm_cast
    ring
  · intro u hu
    let z : lattice E (r : ℤ) := ⟨1 - (u : E), hu⟩
    have hunit : positiveUnitOfLattice E hr.pos z = u := by
      apply Units.ext
      simp [z, coe_positiveUnitOfLattice, CharTwo.sub_eq_add, ← add_assoc,
        CharTwo.add_self_eq_zero]
    have hl := stationaryNumeratorClass_linearization E χ ψ (χ.conductor : ℤ)
      hr Γ Γ.property c hc z
    rw [hunit] at hl
    exact hl.trans (by congr 1; simp [β, z, Units.val_div_eq_div_val, div_mul_eq_mul_div])

/-- The even formula at the inverse of the actual coefficient. The
stationary numerator is one and its full-ideal property is proved. -/
private theorem even_coefficient (χ : LocalQuasiCharData E) (ψ : LocalAddCharData E)
    (b : ℕ) (hb : 0 < b) (hm : χ.conductor = 2 * b) (B : Eˣ)
    (hB : ord E (B : E) = ((-ψ.conductor - 2 * (b : ℤ) : ℤ) : WithTop ℤ))
    (hs : ∀ u : Eˣ, 1 - (u : E) ∈ lattice E (b : ℤ) →
      χ.character u = ψ.character ((B : E) * (1 - (u : E)))) :
    localConstant E χ.character ψ.character =
      (χ.character B : ℂ)⁻¹ * (ψ.character (B : E) : ℂ) := by
  let Γ : AdmissibleGamma E χ ψ := ⟨B⁻¹, by
    rw [Units.val_inv_eq_inv_val, ord_inv, hB, hm]
    norm_cast
    ring⟩
  let hr := lamprechtFormula_stationaryDepth E χ b 0 (by omega) (by omega) (by omega)
  let c : lattice E ((χ.conductor : ℤ) - χ.conductor) := ⟨1, by simp⟩
  have hc : latticeQuotientMk E (sub_le_sub_left hr.int_le_conductor (χ.conductor : ℤ)) c =
      stationaryNumeratorClass E χ ψ (χ.conductor : ℤ) hr Γ Γ.property := by
    apply (latticeQuotientMk_eq_stationaryNumeratorClass_iff E χ ψ
      (χ.conductor : ℤ) hr Γ Γ.property c).mpr
    intro z
    have hz : 1 - ((positiveUnitOfLattice E hr.pos z : Eˣ) : E) = (z : E) := by
      simp [coe_positiveUnitOfLattice, CharTwo.sub_eq_add, ← add_assoc,
        CharTwo.add_self_eq_zero]
    rw [hs _ (by rw [hz]; exact z.property), hz]
    congr 1
    simp [c, Γ, Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_comm]
  have hrep : lamprechtStationaryRepresentativeUnit E χ ψ hr Γ c hc = 1 := by
    apply Units.ext
    rfl
  rw [localConstant_isDeltaFinite E χ ψ Γ,
    lamprechtEven E χ ψ b hm (by omega) Γ c hc]
  change (χ.character B⁻¹ : ℂ) * lamprechtElementaryFactor E χ ψ Γ
    (lamprechtStationaryRepresentativeUnit E χ ψ hr Γ c hc) = _
  rw [hrep, lamprechtElementaryFactor]
  simp [Γ, Units.val_inv_eq_inv_val, mul_comm]

end Field

open private originLine_degrees origin_residueDegrees origin_group_equiv from
  LanglandsSecondMainLemma.Dyadic.Equal.Origin
open private norm_one_sub_charTwo depth_ledger edge_ramification from
  LanglandsSecondMainLemma.Dyadic.Equal.Compatibility
open private field_injective model_ledger from LanglandsSecondMainLemma.Dyadic.Equal.Models
open private lowerCyclic from LanglandsSecondMainLemma.Dyadic.Equal.Twist
open private primeNormCharacter_card from LanglandsSecondMainLemma.Characters.Conjugacy

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  [CharP F 2] [CharP K 2] [IsKleinFour Gal(K/F)]

local instance intermediateValuativeRel (L : IntermediateField F K) : ValuativeRel L :=
  Basic.intermediateFieldValuativeRel L
local instance intermediateTopology (L : IntermediateField F K) : TopologicalSpace L :=
  Basic.intermediateFieldTopology L
local instance intermediateLocalField (L : IntermediateField F K) : IsNonarchimedeanLocalField L :=
  Basic.intermediateField_localField L
local instance intermediateLowerValuativeExtension (L : IntermediateField F K) : ValuativeExtension F L :=
  Basic.intermediateField_lowerValuativeExtension L
local instance intermediateUpperValuativeExtension (L : IntermediateField F K) : ValuativeExtension L K :=
  Basic.intermediateField_upperValuativeExtension L
local instance intermediateGalois (L : IntermediateField F K) : IsGalois F L := by
  letI : IsMulCommutative Gal(K/F) := IsKleinFour.isMulCommutative
  letI : L.fixingSubgroup.Normal := inferInstance
  have h := IsGalois.of_fixedField_normal_subgroup L.fixingSubgroup
  rwa [IsGalois.fixedField_fixingSubgroup L] at h

namespace SimultaneousASGenerators
variable {P : Residues.EqualCharacteristicPresentation F} (A : SimultaneousASGenerators F K P)

/-- The base ideal containing both lower traces and lower norms. -/
def intermediateBaseDepth (h : ℤ) : ℤ := A.lowerDepth 1 + (h + A.lowerDepth 0) / 2

/-- The actual upper stationary depths `bᵢ = T₂ + h - rᵢ`. -/
def intermediateDepth (h : ℤ) (i : Fin 3) : ℤ := (A.t 1 : ℤ) + 1 + h - A.lowerDepth i

omit [IsGalois F K] [CharP F 2] [CharP K 2] in
private theorem lowerDepth_twice (i : Fin 3) :
    0 < A.lowerDepth i ∧ 2 * A.lowerDepth i = (A.t i : ℤ) + 1 := by
  have hp := (A.edge i).2.2.2.1
  obtain ⟨a, ha⟩ := (A.edge i).2.2.2.2.1
  simp only [lowerDepth]
  omega

omit [IsGalois F K] [CharP F 2] [CharP K 2] in
private theorem intermediate_ledger (h : ℤ)
    (hlo : A.lowerDepth 0 ≤ h) (hhi : h ≤ A.lowerDepth 0 + 2 * A.lowerDepth 1 - 2)
    (i : Fin 3) (hi : i ≠ 2) :
    let n := (A.t 1 : ℤ) + 1 + h
    let q := A.intermediateBaseDepth h
    let b := A.intermediateDepth h i
    0 < q ∧ n ≤ 2 * q ∧ q + 1 ≤ n ∧
      0 ≤ h + ((A.t 1 : ℤ) + 1) - q ∧
      h + ((A.t 1 : ℤ) + 1) - q ≤ A.t 1 ∧
      0 < b ∧ (A.stationaryDepth i : ℤ) ≤ b ∧ q ≤ b ∧
      q ≤ (b + ((A.t i : ℤ) + 1)) / 2 ∧
      (if i = 0 then (A.t 1 : ℤ) - A.t 0 else 0) - h -
          2 * ((A.t 1 : ℤ) - A.t i) + b ≥ A.lowerDepth i ∧
      A.lowerDepth 1 + ((A.t 1 : ℤ) - A.t 0) / 2 - h -
          ((A.t 1 : ℤ) - A.t i) + b ≥ (A.t 1 : ℤ) + 1 := by
  have h₀ := A.lowerDepth_twice 0
  have h₁ := A.lowerDepth_twice 1
  have hsmall := A.smallest
  fin_cases i
  · norm_num [intermediateBaseDepth, intermediateDepth, stationaryDepth, lowerDepth] at *
    omega
  · norm_num [intermediateBaseDepth, intermediateDepth, stationaryDepth, lowerDepth] at *
    omega
  · exact (hi rfl).elim

/-- Both actual lower images of every stationary variable belong to the
same base ideal; the different is that of the lower edge. -/
theorem intermediate_trace_norm_mem (hres : residueDegree F K = 1) (h : ℤ)
    (hlo : A.lowerDepth 0 ≤ h) (hhi : h ≤ A.lowerDepth 0 + 2 * A.lowerDepth 1 - 2)
    (i : Fin 3) (hi : i ≠ 2) (z : A.field i)
    (hz : z ∈ lattice (A.field i) (A.intermediateDepth h i)) :
    Algebra.trace F (A.field i) z ∈ lattice F (A.intermediateBaseDepth h) ∧
      Algebra.norm F z ∈ lattice F (A.intermediateBaseDepth h) := by
  obtain ⟨_, _, _, _, _, _, _, hqb, hqt, _, _⟩ := A.intermediate_ledger h hlo hhi i hi
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F (A.field i)
    (origin_residueDegrees F K hres (A.field i)).1
  have ht := trace_mem_lattice_floor F (A.field i) pi hpi hgen _ hz
  rw [(edge_ramification A hres i).1, (A.edge i).2.2.2.2.2.2.2.2] at ht
  constructor
  · exact lattice_antitone F (by simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      using hqt) ht
  · apply lattice_antitone F hqb
    change _ ≤ ord F (norm F (A.field i) z)
    rw [ord_norm, (origin_residueDegrees F K hres (A.field i)).1, one_nsmul]
    exact hz

/-- Choose a genuine third-field norm at exactly the allowed precision.
Its class preserves the base character on the *whole* common ideal. The
representative package retains both exact valuations and the congruence;
it makes no assertion at the critical successor. -/
theorem intermediate_norm_exists (hres : residueDegree F K = 1)
    (lambda : ContinuousQuasiChar F) (h : ℤ)
    (hlo : A.lowerDepth 0 ≤ h) (hhi : h ≤ A.lowerDepth 0 + 2 * A.lowerDepth 1 - 2)
    (hn : (multiplicativeConductorExponent F lambda : ℤ) = (A.t 1 : ℤ) + 1 + h) :
    ∃ (B : Fˣ) (X : (A.field 2)ˣ),
      ord F (B : F) = ((-h : ℤ) : WithTop ℤ) ∧
      IsSubcriticalNormRepresentative F (A.field 2) (-h)
        (h + ((A.t 1 : ℤ) + 1) - A.intermediateBaseDepth h).toNat B X ∧
      ∀ u : Fˣ, 1 - (u : F) ∈ lattice F (A.intermediateBaseDepth h) →
        lambda u = originAddChar F P ((A.t 1 : ℤ) + 1)
          (Algebra.norm F (X : A.field 2) * (1 - (u : F))) := by
  let χ := canonicalLocalQuasiCharData F lambda
  let ψ : LocalAddCharData F := ⟨originAddChar F P ((A.t 1 : ℤ) + 1),
    -((A.t 1 : ℤ) + 1), originAddChar_conductor F P ((A.t 1 : ℤ) + 1)⟩
  let q := A.intermediateBaseDepth h
  let s := h + ((A.t 1 : ℤ) + 1) - q
  obtain ⟨hqpos, hhalf, hqn, hspos, hsbound, _⟩ :=
    A.intermediate_ledger h hlo hhi 0 (by decide)
  have hq : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hqpos.le
  have hs : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hspos
  have hr : IsLamprechtStationaryDepth χ.conductor q.toNat := by
    have hc : (χ.conductor : ℤ) = (A.t 1 : ℤ) + 1 + h := hn
    refine ⟨?_, ?_, ?_⟩ <;> omega
  obtain ⟨B, hB, hchart⟩ := coefficient_exists F χ ψ hr
  have hB' : ord F (B : F) = ((-h : ℤ) : WithTop ℤ) := by
    rw [hB]
    congr 1
    change -(-((A.t 1 : ℤ) + 1)) - (multiplicativeConductorExponent F lambda : ℤ) = -h
    rw [hn]
    ring
  letI := lowerCyclic A 2
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F (A.field 2)
    (origin_residueDegrees F K hres (A.field 2)).1
  have hst : s.toNat ≤ A.t 2 := by rw [A.third_break]; omega
  obtain ⟨X, hX⟩ := normRepresentative_subcritical F (A.field 2)
    (A.edge 2).2.2.2.2.2.2.2.1 (origin_residueDegrees F K hres (A.field 2)).1
    pi hpi hgen hst B hB'
  refine ⟨B, X, hB', hX, ?_⟩
  intro u hu
  have hlin := hchart u (by simpa only [hq] using hu)
  change lambda u = ψ.character ((B : F) * (1 - (u : F))) at hlin
  rw [hlin]
  have hdiff : (B : F) - Algebra.norm F (X : A.field 2) ∈
      lattice F (((A.t 1 : ℤ) + 1) - q) := by
    have hd := hX.norm_congruent
    rw [hs] at hd
    convert hd using 1
    dsimp only [s]
    congr 1
    ring
  have hmul := mul_mem_lattice F hdiff hu
  have hmul' : ((B : F) - Algebra.norm F (X : A.field 2)) * (1 - (u : F)) ∈
      lattice F (-ψ.conductor) := by
    simpa only [ψ, q, neg_neg, sub_add_cancel] using hmul
  have hphase : ψ.character
      ((B : F) * (1 - (u : F)) - Algebra.norm F (X : A.field 2) * (1 - (u : F))) = 1 := by
    apply ψ.isConductor.trivial
    convert hmul' using 1
    ring
  have heq := (ψ.character.toAddChar.map_sub_eq_div _ _).symm.trans hphase
  exact div_eq_one.mp heq

/-- Every third-field representative with the required valuation gives a
nonzero moved numerator and the exact valuations of all its upper norms.
The strict inequality uses `2 r₁ = t₁ + 1`, including the endpoint `h = r₁`. -/
theorem intermediate_moved_norm_order (hres : residueDegree F K = 1)
    (h : ℤ) (hlo : A.lowerDepth 0 ≤ h) (X : A.field 2)
    (hX : ord (A.field 2) X = ((-h : ℤ) : WithTop ℤ)) :
    A.Y + (X : K) ≠ 0 ∧
      ord K (A.Y + (X : K)) = ((-2 * h : ℤ) : WithTop ℤ) ∧
      ∀ i : Fin 3, ord (A.field i) (Algebra.norm (A.field i) (A.Y + (X : K))) =
        ((-2 * h : ℤ) : WithTop ℤ) := by
  have hXtop : ord K (X : K) = ((-2 * h : ℤ) : WithTop ℤ) := by
    change ord K (algebraMap (A.field 2) K X) = _
    rw [ord_algebraMap, (edge_ramification A hres 2).2, hX,
      two_nsmul, ← WithTop.coe_add]
    congr 1
    ring
  have hlt : ord K (X : K) < ord K A.Y := by
    rw [hXtop, (A.origin_orders hres).1]
    have hr := A.lowerDepth_twice 0
    exact WithTop.coe_lt_coe.mpr (by omega)
  have hC : ord K (A.Y + (X : K)) = ((-2 * h : ℤ) : WithTop ℤ) := by
    rw [ord_add_eq_min K hlt.ne', min_eq_right hlt.le, hXtop]
  refine ⟨?_, hC, ?_⟩
  · intro hzero
    rw [hzero, ord_zero] at hC
    exact WithTop.top_ne_coe hC
  · intro i
    change ord (A.field i) (norm (A.field i) K (A.Y + (X : K))) = _
    rw [ord_norm, (origin_residueDegrees F K hres (A.field i)).2, one_nsmul, hC]

/-- The lower norm character converts trace to norm on the whole lower
stationary ideal, as in (D:EQ:normphase). -/
private theorem intermediate_norm_phase (hres : residueDegree F K = 1)
    (i : Fin 3) (x : A.field i) (hx : x ∈ lattice (A.field i) (A.lowerDepth i)) :
    originAddChar F P ((A.t 1 : ℤ) + 1)
        (Algebra.trace F (A.field i) (algebraMap F (A.field i) (A.beta i) * x)) =
      originAddChar F P ((A.t 1 : ℤ) + 1) (A.beta i * Algebra.norm F x) := by
  let ψ := originAddChar F P ((A.t 1 : ℤ) + 1)
  have htrace : Algebra.trace F (A.field i)
      (algebraMap F (A.field i) (A.beta i) * x) =
      A.beta i * Algebra.trace F (A.field i) x := by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have harg : Algebra.trace F (A.field i)
        (algebraMap F (A.field i) (A.beta i) * x) - A.beta i * Algebra.norm F x =
      A.beta i * (Algebra.norm F (1 - x) - 1) := by
    rw [htrace, norm_one_sub_charTwo F (A.field i)
      (originLine_degrees F K (A.g i) (A.nontrivial i)).1]
    simp only [CharTwo.sub_eq_add]
    ring_nf
    simp [CharTwo.two_eq_zero]
  have hphase : ψ (Algebra.trace F (A.field i)
      (algebraMap F (A.field i) (A.beta i) * x) - A.beta i * Algebra.norm F x) = 1 := by
    rw [harg]
    exact A.lowerNorm_phase hres i hx
  exact div_eq_one.mp ((ψ.toAddChar.map_sub_eq_div _ _).symm.trans hphase)

/-- The exact conversion (D:EQ:pullback-adjust). Its full error `e / βᵢ`
is retained; the norm identity and the domain are explicit inputs to this
supporting calculation, to be supplied by the actual third-field data. -/
theorem intermediate_pullback_adjust (hres : residueDegree F K = 1)
    (i : Fin 3) (R e : F) (Q z : A.field i)
    (hnorm : Algebra.norm F Q = A.beta i * R + e)
    (hz : Q / algebraMap F (A.field i) (A.beta i) * z ∈
      lattice (A.field i) (A.lowerDepth i)) :
    originAddChar F P ((A.t 1 : ℤ) + 1) (Algebra.trace F (A.field i) (Q * z)) =
      originAddChar F P ((A.t 1 : ℤ) + 1) ((R + e / A.beta i) * Algebra.norm F z) := by
  have hβ : A.beta i ≠ 0 := by
    intro hzero
    have hord := (A.scalar_data i).2.2.1
    rw [hzero, ord_zero] at hord
    exact WithTop.top_ne_coe hord
  have hβL : algebraMap F (A.field i) (A.beta i) ≠ 0 := by
    simpa only [map_zero] using (algebraMap F (A.field i)).injective.ne hβ
  have htrace : algebraMap F (A.field i) (A.beta i) *
      (Q / algebraMap F (A.field i) (A.beta i) * z) = Q * z := by
    field_simp
  have hn : A.beta i * Algebra.norm F
      (Q / algebraMap F (A.field i) (A.beta i) * z) =
      (R + e / A.beta i) * Algebra.norm F z := by
    rw [map_mul, div_eq_mul_inv, map_mul, Algebra.norm_inv, Algebra.norm_algebraMap,
      (originLine_degrees F K (A.g i) (A.nontrivial i)).1, hnorm]
    field_simp
  have hphase := A.intermediate_norm_phase hres i _ hz
  rwa [htrace, hn] at hphase

/-- The complete pullback chart on the upper stationary ideal. The
integer bounds make the retained error trivial at the base character's
actual conductor. `ThirdNorm` supplies the three hypotheses on `Q, e`
when this calculation is applied to a third-field representative. -/
theorem intermediate_pullback_chart (hres : residueDegree F K = 1)
    (lambda : ContinuousQuasiChar F) (h : ℤ)
    (hlo : A.lowerDepth 0 ≤ h) (hhi : h ≤ A.lowerDepth 0 + 2 * A.lowerDepth 1 - 2)
    (R : F)
    (hbase : ∀ u : Fˣ, 1 - (u : F) ∈ lattice F (A.intermediateBaseDepth h) →
      lambda u = originAddChar F P ((A.t 1 : ℤ) + 1) (R * (1 - (u : F))))
    (i : Fin 3) (hi : i ≠ 2) (Q : A.field i) (e : F)
    (hnorm : Algebra.norm F Q = A.beta i * R + e)
    (hQ : Q ∈ lattice (A.field i) ((if i = 0 then (A.t 1 : ℤ) - A.t 0 else 0) - h))
    (he : e ∈ lattice F (A.lowerDepth 1 + ((A.t 1 : ℤ) - A.t 0) / 2 - h))
    (u : (A.field i)ˣ)
    (hu : 1 - (u : A.field i) ∈ lattice (A.field i) (A.intermediateDepth h i)) :
    normQuasiChar F (A.field i) lambda u =
      originAddChar F P ((A.t 1 : ℤ) + 1)
        (Algebra.trace F (A.field i)
          ((algebraMap F (A.field i) R + Q) * (1 - (u : A.field i)))) := by
  let ψ := originAddChar F P ((A.t 1 : ℤ) + 1)
  let z : A.field i := 1 - (u : A.field i)
  obtain ⟨_, _, _, _, _, _, _, _, _, hQbound, hebound⟩ :=
    A.intermediate_ledger h hlo hhi i hi
  have hβ := (A.scalar_data i).2.2.1
  have hβL : ord (A.field i) (algebraMap F (A.field i) (A.beta i)) =
      ((2 * ((A.t 1 : ℤ) - A.t i) : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, (edge_ramification A hres i).1, hβ,
      two_nsmul, ← WithTop.coe_add]
    congr 1
    ring
  have hQz : Q / algebraMap F (A.field i) (A.beta i) * z ∈
      lattice (A.field i) (A.lowerDepth i) := by
    rw [div_mul_eq_mul_div]
    apply (div_mem_lattice_iff _ _ _ _ _ hβL).2
    exact lattice_antitone _ (by omega) (mul_mem_lattice (A.field i) hQ hu)
  have hnz : Algebra.norm F z ∈ lattice F (A.intermediateDepth h i) := by
    change (A.intermediateDepth h i : WithTop ℤ) ≤ ord F (norm F (A.field i) z)
    rw [ord_norm, (origin_residueDegrees F K hres (A.field i)).1, one_nsmul]
    exact hu
  have hez : (e / A.beta i) * Algebra.norm F z ∈ lattice F ((A.t 1 : ℤ) + 1) := by
    rw [div_mul_eq_mul_div]
    apply (div_mem_lattice_iff _ _ _ _ _ hβ).2
    exact lattice_antitone F (by omega) (mul_mem_lattice F he hnz)
  have herr : ψ ((e / A.beta i) * Algebra.norm F z) = 1 := by
    apply (originAddChar_conductor F P ((A.t 1 : ℤ) + 1)).trivial
    simpa only [neg_neg] using hez
  have hphase := A.intermediate_pullback_adjust hres i R e Q z hnorm hQz
  change ψ (Algebra.trace F (A.field i) (Q * z)) =
    ψ ((R + e / A.beta i) * Algebra.norm F z) at hphase
  rw [add_mul, ψ.map_add_eq_mul, herr, mul_one] at hphase
  let ν := normUnits F (A.field i) u
  have hν : 1 - (ν : F) = Algebra.trace F (A.field i) z + Algebra.norm F z := by
    have huz : (u : A.field i) = 1 - z := by dsimp only [z]; ring
    change 1 - Algebra.norm F (u : A.field i) = _
    rw [huz, norm_one_sub_charTwo F (A.field i)
      (originLine_degrees F K (A.g i) (A.nontrivial i)).1, CharTwo.sub_eq_add]
    simp only [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hνmem : 1 - (ν : F) ∈ lattice F (A.intermediateBaseDepth h) := by
    rw [hν]
    obtain ⟨htr, hnormz⟩ := A.intermediate_trace_norm_mem hres h hlo hhi i hi z hu
    exact (lattice F _).add_mem htr hnormz
  have htrace : Algebra.trace F (A.field i) ((algebraMap F (A.field i) R + Q) * z) =
      R * Algebra.trace F (A.field i) z + Algebra.trace F (A.field i) (Q * z) := by
    rw [add_mul, map_add, ← Algebra.smul_def, map_smul, smul_eq_mul]
  calc
    _ = ψ (R * (Algebra.trace F (A.field i) z + Algebra.norm F z)) := by
      change lambda ν = _
      rw [hbase ν hνmem, hν]
    _ = ψ (R * Algebra.trace F (A.field i) z) *
        ψ (Algebra.trace F (A.field i) (Q * z)) := by
      rw [mul_add, ψ.map_add_eq_mul, hphase]
    _ = _ := by rw [htrace, ψ.map_add_eq_mul]

/-- The core charts force their exact conductors, so FML's pullback
formula gives the even upper conductors without an extra model hypothesis. -/
theorem intermediate_conductors (hres : residueDegree F K = 1)
    (χ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hchart : ∀ i u, u ∈ unitFiltration (A.field i) (A.stationaryDepth i) →
      χ i u = A.modelValue i u)
    (lambda : ContinuousQuasiChar F) (h : ℤ) (hlo : A.lowerDepth 0 ≤ h)
    (hn : (multiplicativeConductorExponent F lambda : ℤ) = (A.t 1 : ℤ) + 1 + h)
    (i : Fin 3) :
    IsMultiplicativeConductor (A.field i) (χ i * normQuasiChar F (A.field i) lambda)
      (2 * (A.intermediateDepth h i).toNat) ∧ 0 < A.intermediateDepth h i := by
  have hcond := fun i ↦ A.conductor_of_modelChart hres i (χ i) (hchart i)
  have hthreshold : A.twistThreshold ≤ multiplicativeConductorExponent F lambda := by
    simp only [twistThreshold, lowerDepth] at *
    omega
  have hc := (A.twist_conductors hres χ hcond lambda).2 hthreshold i
  have hcZ : (multiplicativeConductorExponent (A.field i)
      (χ i * normQuasiChar F (A.field i) lambda) : ℤ) =
      2 * (multiplicativeConductorExponent F lambda : ℤ) - ((A.t i : ℤ) + 1) := hc.1
  have hl := A.lowerDepth_twice i
  have hm := (model_ledger A i).1
  have hpos : 0 < A.intermediateDepth h i := by
    dsimp only [intermediateDepth]
    have : (A.minimalConductor i : ℤ) <
        (multiplicativeConductorExponent (A.field i)
          (χ i * normQuasiChar F (A.field i) lambda) : ℤ) := by exact_mod_cast hc.2.2
    omega
  have he : multiplicativeConductorExponent (A.field i)
      (χ i * normQuasiChar F (A.field i) lambda) = 2 * (A.intermediateDepth h i).toNat := by
    apply Int.ofNat_inj.mp
    rw [Nat.cast_mul, Nat.cast_ofNat, Int.toNat_of_nonneg hpos.le]
    dsimp only [intermediateDepth]
    omega
  exact ⟨he ▸ multiplicativeConductorExponent_isConductor (A.field i)
    (χ i * normQuasiChar F (A.field i) lambda), hpos⟩

/-- The full lower factor uses the original actual coefficient `βᵢ`.
Its multiplicative value is one because `βᵢ` is an actual lower norm.
No stationary assertion about the moved trace is needed. -/
theorem intermediate_lower_factor (hres : residueDegree F K = 1)
    (i : Fin 3) (ω : NormCharacter F (A.field i)) (hω : ω ≠ 1) :
    localConstant F ω.1 (originAddChar F P ((A.t 1 : ℤ) + 1)) =
      (originAddChar F P ((A.t 1 : ℤ) + 1) (A.beta i) : ℂ) := by
  have hf : ord F (A.f i) = ((-(A.t i : ℤ) : ℤ) : WithTop ℤ) := by
    rw [← P.laurentEquiv.apply_symm_apply (A.f i), P.laurentEquiv_order]
    exact (A.edge i).2.2.2.2.2.2.1
  have hodd : Odd (A.t 1 : ℤ) := by exact_mod_cast (A.edge 1).2.2.2.2.1
  obtain ⟨hm, hψ, _, _, ⟨hβ, hωβ⟩, hchart, _⟩ :=
    dyadicEqual_lowerCharts F (A.field i)
      (originLine_degrees F K (A.g i) (A.nontrivial i)).1
      (origin_residueDegrees F K hres (A.field i)).1 P (A.f i) (A.z i)
      (A.edge i).1 (A.edge i).2.1 (A.t i) (A.edge i).2.2.2.1
      (A.edge i).2.2.2.2.1 (A.edge i).2.2.1 hf (A.edge i).2.2.2.2.2.2.2.2
      ω hω (A.t 1) hodd
  let χ : LocalQuasiCharData F := ⟨ω.1, A.t i + 1, hm⟩
  let ψ : LocalAddCharData F := ⟨originAddChar F P ((A.t 1 : ℤ) + 1),
    -((A.t 1 : ℤ) + 1), hψ⟩
  let β : Fˣ := Units.mk0 (A.beta i) hβ
  have hr := A.lowerDepth_twice i
  have hb : ((A.lowerDepth i).toNat : ℤ) = A.lowerDepth i := Int.toNat_of_nonneg hr.1.le
  have hβord : ord F (β : F) =
      ((-ψ.conductor - 2 * ((A.lowerDepth i).toNat : ℤ) : ℤ) : WithTop ℤ) := by
    rw [show (β : F) = A.beta i from rfl, (A.scalar_data i).2.2.1]
    congr 1
    dsimp only [ψ]
    omega
  have he := even_coefficient F χ ψ (A.lowerDepth i).toNat (by omega)
    (by dsimp only [χ]; omega) β hβord (by
      intro u hu
      apply hchart u
      change 1 - (u : F) ∈ lattice F (A.lowerDepth i)
      rwa [hb] at hu)
  change localConstant F ω.1 ψ.character = _
  rw [he]
  change (ω.1 β : ℂ)⁻¹ * (ψ.character (A.beta i) : ℂ) = _
  rw [show ω.1 β = 1 from hωβ]
  simp only [Units.val_one, inv_one, one_mul]
  rfl

/-- Combine the original core chart with the complete pullback chart on
the whole upper stationary ideal. The equation on `C` is exactly the
upper norm component of (D:EQ:commonC). -/
private theorem intermediate_upper_chart (hres : residueDegree F K = 1)
    (χ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hchart : ∀ i u, u ∈ unitFiltration (A.field i) (A.stationaryDepth i) →
      χ i u = A.modelValue i u)
    (lambda : ContinuousQuasiChar F) (h : ℤ)
    (hlo : A.lowerDepth 0 ≤ h) (hhi : h ≤ A.lowerDepth 0 + 2 * A.lowerDepth 1 - 2)
    (R : F)
    (hbase : ∀ u : Fˣ, 1 - (u : F) ∈ lattice F (A.intermediateBaseDepth h) →
      lambda u = originAddChar F P ((A.t 1 : ℤ) + 1) (R * (1 - (u : F))))
    (i : Fin 3) (hi : i ≠ 2) (Q : A.field i) (e : F)
    (hnorm : Algebra.norm F Q = A.beta i * R + e)
    (hQ : Q ∈ lattice (A.field i) ((if i = 0 then (A.t 1 : ℤ) - A.t 0 else 0) - h))
    (he : e ∈ lattice F (A.lowerDepth 1 + ((A.t 1 : ℤ) - A.t 0) / 2 - h))
    (C : K)
    (hC : Algebra.norm (A.field i) C = Algebra.norm (A.field i) A.Y +
      algebraMap F (A.field i) R + Q)
    (u : (A.field i)ˣ)
    (hu : 1 - (u : A.field i) ∈ lattice (A.field i) (A.intermediateDepth h i)) :
    (χ i * normQuasiChar F (A.field i) lambda) u =
      tracePullbackAddChar F (A.field i) (originAddChar F P ((A.t 1 : ℤ) + 1))
        (Algebra.norm (A.field i) C * (1 - (u : A.field i))) := by
  obtain ⟨_, _, _, _, _, _, hsb, _⟩ := A.intermediate_ledger h hlo hhi i hi
  have hcore := hchart i u ((A.modelDomain_iff i u).2
    (lattice_antitone (A.field i) hsb hu))
  have hpull := A.intermediate_pullback_chart hres lambda h hlo hhi R hbase i hi
    Q e hnorm hQ he u hu
  rw [ContinuousQuasiChar.mul_apply, hcore, hpull]
  simp only [modelValue, tracePullbackAddChar_apply]
  rw [← ContinuousAddChar.map_add_eq_mul, ← map_add, ← add_mul, hC, add_assoc]

/-- The lower coefficient remains `βᵢ`. Using the actual upper trace in
(D:EQ:E2) retains the identical `a²` increment, including its affine
contribution, without asserting lower stationarity of the moved trace. -/
private theorem intermediate_trace_square (C : K) (a : F) (i : Fin 3)
    (htrace : Algebra.trace (A.field i) K C =
      algebraMap F (A.field i) (A.root i + a)) :
    Algebra.trace F (A.field i) (Algebra.norm (A.field i) C) + A.beta i =
      elementarySymmetric F K 2 C + a ^ 2 := by
  letI : Algebra.IsQuadraticExtension F (A.field i) :=
    ⟨(originLine_degrees F K (A.g i) (A.nontrivial i)).1⟩
  letI : Algebra.IsQuadraticExtension (A.field i) K :=
    ⟨(originLine_degrees F K (A.g i) (A.nontrivial i)).2⟩
  have he₂ := Algebra.biquadraticE2 F K (A.field i) C
  change elementarySymmetric F K 2 C =
    Algebra.trace F (A.field i) (Algebra.norm (A.field i) C) +
      Algebra.norm F (Algebra.trace (A.field i) K C) at he₂
  rw [he₂, htrace, Algebra.norm_algebraMap,
    (originLine_degrees F K (A.g i) (A.nontrivial i)).1,
    CharTwo.add_sq, (A.scalar_data i).1]
  simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The full upper and lower Lamprecht factors at a common numerator.
The multiplicative factor is its actual common character value and the
phase retains `E₂(C) + a²`. The actual third-field construction below
supplies the upper chart and trace identity. -/
private theorem intermediate_complete_factor (hres : residueDegree F K = 1)
    (χ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hchart : ∀ i u, u ∈ unitFiltration (A.field i) (A.stationaryDepth i) →
      χ i u = A.modelValue i u)
    (lambda : ContinuousQuasiChar F) (h : ℤ) (hlo : A.lowerDepth 0 ≤ h)
    (hn : (multiplicativeConductorExponent F lambda : ℤ) = (A.t 1 : ℤ) + 1 + h)
    (Θ : ContinuousQuasiChar K) (i : Fin 3)
    (hcompatible : normQuasiChar (A.field i) K
      (χ i * normQuasiChar F (A.field i) lambda) = Θ)
    (ω : NormCharacter F (A.field i)) (hω : ω ≠ 1)
    (C : Kˣ) (a : F)
    (hord : ord (A.field i) (Algebra.norm (A.field i) (C : K)) =
      ((-2 * h : ℤ) : WithTop ℤ))
    (hstationary : ∀ u : (A.field i)ˣ,
      1 - (u : A.field i) ∈ lattice (A.field i) (A.intermediateDepth h i) →
        (χ i * normQuasiChar F (A.field i) lambda) u =
          tracePullbackAddChar F (A.field i) (originAddChar F P ((A.t 1 : ℤ) + 1))
            (Algebra.norm (A.field i) (C : K) * (1 - (u : A.field i))))
    (htrace : Algebra.trace (A.field i) K (C : K) =
      algebraMap F (A.field i) (A.root i + a)) :
    localConstant (A.field i) (χ i * normQuasiChar F (A.field i) lambda)
        (tracePullbackAddChar F (A.field i) (originAddChar F P ((A.t 1 : ℤ) + 1))) *
      localConstant F ω.1 (originAddChar F P ((A.t 1 : ℤ) + 1)) =
        (Θ C : ℂ)⁻¹ *
          (originAddChar F P ((A.t 1 : ℤ) + 1)
            (elementarySymmetric F K 2 (C : K) + a ^ 2) : ℂ) := by
  obtain ⟨hcond, hbpos⟩ := A.intermediate_conductors hres χ hchart lambda h hlo hn i
  let b := (A.intermediateDepth h i).toNat
  have hb : (b : ℤ) = A.intermediateDepth h i := Int.toNat_of_nonneg hbpos.le
  let θ : LocalQuasiCharData (A.field i) :=
    ⟨χ i * normQuasiChar F (A.field i) lambda, 2 * b, hcond⟩
  let ψ : LocalAddCharData (A.field i) :=
    ⟨tracePullbackAddChar F (A.field i) (originAddChar F P ((A.t 1 : ℤ) + 1)),
      -A.additiveModulus i, A.modelAddChar_conductor hres i⟩
  let B := normUnits (A.field i) K C
  have hB : ord (A.field i) (B : A.field i) =
      ((-ψ.conductor - 2 * (b : ℤ) : ℤ) : WithTop ℤ) := by
    change ord (A.field i) (Algebra.norm (A.field i) (C : K)) = _
    rw [hord, hb]
    congr 1
    have hr := (A.lowerDepth_twice i).2
    dsimp only [ψ, additiveModulus, intermediateDepth]
    omega
  have hupper := even_coefficient (A.field i) θ ψ b (by omega) rfl B hB (by
    intro u hu
    exact hstationary u (by rwa [hb] at hu))
  have hvalue : θ.character B = Θ C :=
    congrArg (fun η : ContinuousQuasiChar K ↦ η C) hcompatible
  rw [hupper, A.intermediate_lower_factor hres i ω hω, hvalue]
  change (Θ C : ℂ)⁻¹ *
    (originAddChar F P ((A.t 1 : ℤ) + 1)
      (Algebra.trace F (A.field i) (Algebra.norm (A.field i) (C : K))) : ℂ) * _ = _
  rw [mul_assoc, ← Units.val_mul, ← ContinuousAddChar.map_add_eq_mul,
    A.intermediate_trace_square (C : K) a i htrace]

/-- Construct the actual common numerator from the subcritical norm
representative, and apply the full upper and original lower formulas.
The common error, its bounds, and both moved traces come from `ThirdNorm`;
none is an additional hypothesis on the family. -/
theorem intermediate_common_factor (hres : residueDegree F K = 1)
    (χ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hchart : ∀ i u, u ∈ unitFiltration (A.field i) (A.stationaryDepth i) →
      χ i u = A.modelValue i u)
    (lambda : ContinuousQuasiChar F) (h : ℤ)
    (hlo : A.lowerDepth 0 ≤ h) (hhi : h ≤ A.lowerDepth 0 + 2 * A.lowerDepth 1 - 2)
    (hn : (multiplicativeConductorExponent F lambda : ℤ) = (A.t 1 : ℤ) + 1 + h)
    (Θ : ContinuousQuasiChar K)
    (hcompatible : ∀ i, normQuasiChar (A.field i) K
      (χ i * normQuasiChar F (A.field i) lambda) = Θ) :
    ∃ (C : Kˣ) (a : F), ∀ i : Fin 3, i ≠ 2 →
      ∀ (ω : NormCharacter F (A.field i)), ω ≠ 1 →
        localConstant (A.field i) (χ i * normQuasiChar F (A.field i) lambda)
            (tracePullbackAddChar F (A.field i) (originAddChar F P ((A.t 1 : ℤ) + 1))) *
          localConstant F ω.1 (originAddChar F P ((A.t 1 : ℤ) + 1)) =
            (Θ C : ℂ)⁻¹ * (originAddChar F P ((A.t 1 : ℤ) + 1)
              (elementarySymmetric F K 2 (C : K) + a ^ 2) : ℂ) := by
  obtain ⟨B, X, _, hX, hbase⟩ := A.intermediate_norm_exists hres lambda h hlo hhi hn
  obtain ⟨hC, _, horder⟩ := A.intermediate_moved_norm_order hres h hlo
    (X : A.field 2) hX.source_order
  let C : Kˣ := Units.mk0 (A.thirdC (X : A.field 2)) hC
  have hXmem : (X : A.field 2) ∈ lattice (A.field 2) (-h) := hX.source_exactDepth.1
  refine ⟨C, A.thirdTrace (X : A.field 2), ?_⟩
  intro i hi ω hω
  apply A.intermediate_complete_factor hres χ hchart lambda h hlo hn Θ i
    (hcompatible i) ω hω C (A.thirdTrace (X : A.field 2)) (horder i)
  · exact A.intermediate_upper_chart hres χ hchart lambda h hlo hhi
      (Algebra.norm F (X : A.field 2)) hbase i hi (A.thirdQ (X : A.field 2) i)
      (A.thirdError (X : A.field 2)) (A.thirdQ_norm (X : A.field 2) i hi)
      (A.thirdQ_bound hres (X : A.field 2) h hXmem i)
      (A.thirdError_bound hres (X : A.field 2) h hXmem) (C : K)
      (A.thirdC_norm_trace (X : A.field 2) i hi).1
  · exact (A.thirdC_norm_trace (X : A.field 2) i hi).2

/-- The complete induction expression, including the trivial lower
norm character. Its finiteness is proved on the actual quadratic edge. -/
def intermediateInductionFactor (i : Fin 3) (θ : ContinuousQuasiChar (A.field i))
    (ψ : ContinuousAddChar F) : ℂ := by
  letI := lowerCyclic A i
  letI := primeCyclicNormCharacter_finite F (A.field i)
  letI := normCharacterFintype F (A.field i)
  exact localConstant (A.field i) θ (tracePullbackAddChar F (A.field i) ψ) *
    ∏ ω : NormCharacter F (A.field i), localConstant F ω.1 ψ

omit [CharP F 2] [CharP K 2] in
/-- In degree two the complete lower product is the nontrivial factor:
FML proves that the remaining trivial-character local constant is one. -/
private theorem intermediate_factor_eq (i : Fin 3)
    (θ : ContinuousQuasiChar (A.field i)) (ψ : LocalAddCharData F)
    (ω : NormCharacter F (A.field i)) (hω : ω ≠ 1) :
    A.intermediateInductionFactor i θ ψ.character =
      localConstant (A.field i) θ (tracePullbackAddChar F (A.field i) ψ.character) *
        localConstant F ω.1 ψ.character := by
  classical
  letI := lowerCyclic A i
  letI := primeCyclicNormCharacter_finite F (A.field i)
  letI := normCharacterFintype F (A.field i)
  have hcard : Nat.card (NormCharacter F (A.field i)) = 2 :=
    (primeNormCharacter_card F (A.field i)).trans
      (originLine_degrees F K (A.g i) (A.nontrivial i)).1
  have huniv : ({1, ω} : Finset (NormCharacter F (A.field i))) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simp only [Finset.card_pair hω.symm, Fintype.card_eq_nat_card, hcard]
  obtain ⟨Γ⟩ := AdmissibleGamma.exists_admissible
    (F := F) (χ := trivialQuasiCharData F) (ψ := ψ)
  have htriv : localConstant F 1 ψ.character = 1 :=
    (localConstant_isDeltaFinite F (trivialQuasiCharData F) ψ Γ).trans
      (delta_trivial_character F ψ Γ)
  change _ * (∏ μ : NormCharacter F (A.field i), localConstant F μ.1 ψ.character) = _
  rw [← huniv, Finset.prod_pair hω.symm]
  change _ * (localConstant F 1 ψ.character * _) = _
  rw [htriv, one_mul]

omit [CharP F 2] [CharP K 2] in
/-- Scale both actual local constants. The multiplier is the restriction
of the upper character corrected by the original lower norm character. -/
private theorem intermediate_scale_factor (i : Fin 3)
    (θ : ContinuousQuasiChar (A.field i)) (ψ : LocalAddCharData F)
    (ω : NormCharacter F (A.field i)) (hω : ω ≠ 1) (u : Fˣ) :
    A.intermediateInductionFactor i θ (scaleAddCharData F ψ u).character =
      ((Characters.restrictQuasiChar F (A.field i) θ * ω.1) u : ℂ) *
        A.intermediateInductionFactor i θ ψ.character := by
  let L := A.field i
  let ψL := canonicalLocalAddCharData L (tracePullbackAddChar F L ψ.character)
    (Basic.tracePullbackAddChar_ne_one F L ψ.character ψ.isConductor.character_ne_one)
  let uL := Units.map (algebraMap F L).toMonoidHom u
  have hscale : tracePullbackAddChar F L (scaleAddCharData F ψ u).character =
      (scaleAddCharData L ψL uL).character := by
    apply ContinuousAddChar.ext
    intro x
    change ψ.character ((u : F) * Algebra.trace F L x) =
      ψ.character (Algebra.trace F L (algebraMap F L (u : F) * x))
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  let θL := canonicalLocalQuasiCharData L θ
  let ωF := canonicalLocalQuasiCharData F ω.1
  obtain ⟨ΓL⟩ := AdmissibleGamma.exists_admissible (F := L) (χ := θL) (ψ := ψL)
  obtain ⟨ΓF⟩ := AdmissibleGamma.exists_admissible (F := F) (χ := ωF) (ψ := ψ)
  have hupper := delta_additive_scale L θL ψL uL ΓL (scaleAdmissibleGamma L uL ΓL)
  have hlower := delta_additive_scale F ωF ψ u ΓF (scaleAdmissibleGamma F u ΓF)
  rw [← localConstant_isDeltaFinite L, ← localConstant_isDeltaFinite L] at hupper
  rw [← localConstant_isDeltaFinite F, ← localConstant_isDeltaFinite F] at hlower
  change localConstant L θ (scaleAddCharData L ψL uL).character =
    (θ uL : ℂ) * localConstant L θ ψL.character at hupper
  change localConstant F ω.1 (scaleAddCharData F ψ u).character =
    (ω.1 u : ℂ) * localConstant F ω.1 ψ.character at hlower
  rw [A.intermediate_factor_eq i θ (scaleAddCharData F ψ u) ω hω,
    A.intermediate_factor_eq i θ ψ ω hω, hscale, hupper, hlower]
  change ((θ uL : ℂ) * localConstant L θ ψL.character) *
    ((ω.1 u : ℂ) * localConstant F ω.1 ψ.character) =
      ((θ uL * ω.1 u : ℂˣ) : ℂ) *
        (localConstant L θ ψL.character * localConstant F ω.1 ψ.character)
  rw [Units.val_mul]
  ring

end SimultaneousASGenerators

/-- **Exact intermediate comparison**, Theorem 11.11 (`D:EQ:intermediate`).
The core charts and actual common-twist family are supplied by `twist`.
For every integer `r₁ ≤ h ≤ r₁ + 2r₂ - 2`, the complete induction
expressions on fields `0, 1` agree. The proof constructs the third-field
norm at its permitted precision and retains `E₂(C) + a²` and `Θ(C)`.

The arbitrary nonzero scale `α` writes the paper's additive character as
`ψ(x) = Ψ(α⁻¹ x)`; the corrected restrictions give the identical scaling
factor. All characters are continuous quasi-characters, with unrestricted
values on uniformizers. No stationary or norm-representative data are
assumed beyond the original core charts constructed by `twist`. -/
theorem intermediate (hres : residueDegree F K = 1)
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
    (α : Fˣ) :
    let Ψ : LocalAddCharData F := ⟨originAddChar F P ((A.t 1 : ℤ) + 1),
      -((A.t 1 : ℤ) + 1), originAddChar_conductor F P ((A.t 1 : ℤ) + 1)⟩
    let ψ := (scaleAddCharData F Ψ α⁻¹).character
    A.intermediateInductionFactor 0 (χ 0 * normQuasiChar F (A.field 0) lambda) ψ =
      A.intermediateInductionFactor 1 (χ 1 * normQuasiChar F (A.field 1) lambda) ψ := by
  dsimp only
  let Ψ : LocalAddCharData F := ⟨originAddChar F P ((A.t 1 : ℤ) + 1),
    -((A.t 1 : ℤ) + 1), originAddChar_conductor F P ((A.t 1 : ℤ) + 1)⟩
  let θ := fun i ↦ χ i * normQuasiChar F (A.field i) lambda
  obtain ⟨_, _, _, _, hranges, _⟩ := Characters.quadraticProduct F
    (origin_group_equiv F K) A.field
    (fun i ↦ (originLine_degrees F K (A.g i) (A.nontrivial i)).1) (field_injective A)
  obtain ⟨_, _, hdet, _, hquadratic⟩ := Characters.conjugacy Nat.prime_two
    (origin_group_equiv F K) (A.field 0) (A.field 1)
    (originLine_degrees F K (A.g 0) (A.nontrivial 0)).1
    (originLine_degrees F K (A.g 1) (A.nontrivial 1)).1
    (fun he ↦ (by decide : (0 : Fin 3) ≠ 1) (hranges he))
    (θ 0) (θ 1) Θ (hcompatible 0) (hcompatible 1) hprimitive
  obtain ⟨ω₀, ω₁, hω₀, hω₁, hprod₀, hprod₁⟩ := hquadratic rfl
  rw [hprod₀, hprod₁] at hdet
  obtain ⟨C, a, hfactor⟩ :=
    A.intermediate_common_factor hres χ hchart lambda h hlo hhi hn Θ hcompatible
  have heq : A.intermediateInductionFactor 0 (θ 0) Ψ.character =
      A.intermediateInductionFactor 1 (θ 1) Ψ.character := by
    rw [A.intermediate_factor_eq 0 (θ 0) Ψ ω₀ hω₀,
      A.intermediate_factor_eq 1 (θ 1) Ψ ω₁ hω₁]
    exact (hfactor 0 (by decide) ω₀ hω₀).trans (hfactor 1 (by decide) ω₁ hω₁).symm
  rw [A.intermediate_scale_factor 0 (θ 0) Ψ ω₀ hω₀ α⁻¹,
    A.intermediate_scale_factor 1 (θ 1) Ψ ω₁ hω₁ α⁻¹, hdet, heq]

end

end LanglandsSecondMainLemma.Dyadic.Equal
