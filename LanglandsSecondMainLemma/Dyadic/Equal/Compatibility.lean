import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Dyadic.Equal.Origin
import LanglandsSecondMainLemma.Algebra.BiquadraticE2

/-!
# Dyadic / Equal / Compatibility

Compatibility on the full common unit subgroup, `D:EQ:Rcompat`.
All fields and coefficients come from the constructed simultaneous AS origin.
The stationary domains are those of `D:EQ:coreledger` and `D:EQ:Rmodel`.
-/

namespace LanglandsSecondMainLemma.Dyadic.Equal

open LanglandsFirstMainLemma
noncomputable section
open private originLine_degrees origin_residueDegrees from
  LanglandsSecondMainLemma.Dyadic.Equal.Origin

private theorem norm_one_sub_charTwo
    (E M : Type) [Field E] [Field M] [Algebra E M]
    [Module.Finite E M] [CharP M 2]
    (hdegree : Module.finrank E M = 2) (x : M) :
    Algebra.norm E (1 - x) = 1 + Algebra.trace E M x + Algebra.norm E x := by
  rw [CharTwo.sub_eq_add]
  change norm E M (1 + x) = _
  rw [norm_one_add_eq_sum_elementarySymmetric, hdegree]
  have he₂ : elementarySymmetric E M 2 x = norm E M x := by
    rw [← hdegree, elementarySymmetric_finrank]
  simp [Finset.sum_range_succ, he₂]

private theorem one_sub_ne_zero_of_lattice
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {r : ℤ} (hr : 0 < r)
    {x : E} (hx : x ∈ lattice E r) : 1 - x ≠ 0 := by
  intro h
  have heq : x = 1 := (sub_eq_zero.mp h).symm
  have hbound : (r : WithTop ℤ) ≤ ord E x := hx
  rw [heq, ord_one] at hbound
  exact (not_le_of_gt hr) (WithTop.coe_le_coe.mp hbound)

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

/-- The actual fixed field indexed by the retained origin data. -/
abbrev field (i : Fin 3) : IntermediateField F K :=
  IntermediateField.fixedField (originLine (A.g i))

/-- The integer lower stationary depth `rᵢ`. -/
def lowerDepth (i : Fin 3) : ℤ := ((A.t i : ℤ) + 1) / 2

/-- The exact stationary domain depths of (D:EQ:coreledger). -/
def stationaryDepth (i : Fin 3) : ℕ :=
  if i = 0 then A.t 1 + 1 else (A.t 0 + 1) / 2 + (A.t 1 + 1) / 2

omit [IsGalois F K] [CharP F 2] [CharP K 2] in
private theorem depth_ledger (i : Fin 3) :
    0 < A.stationaryDepth i ∧ A.stationaryDepth i ≤ A.t 1 + 1 ∧
      0 < A.lowerDepth i ∧ A.lowerDepth i ≤ A.lowerDepth 1 ∧
      2 * (A.stationaryDepth i : ℤ) - A.t 0 =
        2 * ((A.t 1 : ℤ) + 1) - ((A.t i : ℤ) + 1) + 1 := by
  have ht₀ := (A.edge 0).2.2.2.1
  have ht₁ := (A.edge 1).2.2.2.1
  obtain ⟨a, ha⟩ := (A.edge 0).2.2.2.2.1
  obtain ⟨b, hb⟩ := (A.edge 1).2.2.2.2.1
  have hs := A.smallest
  have hthird := A.third_break
  fin_cases i <;> simp only [stationaryDepth, lowerDepth] <;> norm_num
  all_goals try rw [show A.t ⟨2, by decide⟩ = A.t 1 from hthird]
  all_goals omega

omit [CharP F 2] [CharP K 2] in
private theorem edge_ramification (hres : residueDegree F K = 1) (i : Fin 3) :
    ramificationIndex F (A.field i) = 2 ∧ ramificationIndex (A.field i) K = 2 := by
  have h := originLine_degrees F K (A.g i) (A.nontrivial i)
  have hr := origin_residueDegrees F K hres (A.field i)
  constructor
  · have he := finrank_eq_ramificationIndex_mul_residueDegree F (A.field i)
    simpa [hr.1, h.1] using he.symm
  · have he := finrank_eq_ramificationIndex_mul_residueDegree (A.field i) K
    simpa [hr.2, h.2] using he.symm

/-- The full upper trace bound, using the actual different exponent. -/
theorem upperTrace_mem (hres : residueDegree F K = 1) (i : Fin 3)
    (a : ℤ) {x : K} (hx : x ∈ lattice K a) :
    Algebra.trace (A.field i) K x ∈ lattice (A.field i)
      ((a + if i = 0 then 2 * ((A.t 1 : ℤ) + 1) - ((A.t 0 : ℤ) + 1)
        else (A.t 0 : ℤ) + 1) / 2) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer (A.field i) K
    (origin_residueDegrees F K hres (A.field i)).2
  have h := trace_mem_lattice_floor (A.field i) K pi hpi hgen a hx
  rw [(A.edge_ramification hres i).2, A.upper_different hres i] at h
  exact h

/-- Both terms of the quadratic norm increment lie in the full model domain. -/
theorem normIncrement_mem (hres : residueDegree F K = 1) (i : Fin 3)
    {z : K} (hz : z ∈ lattice K ((A.t 1 : ℤ) + 1)) :
    1 - Algebra.norm (A.field i) (1 - z) ∈
      lattice (A.field i) (A.stationaryDepth i : ℤ) := by
  have hn : Algebra.norm (A.field i) z ∈
      lattice (A.field i) ((A.t 1 : ℤ) + 1) := by
    change ((A.t 1 : ℤ) + 1 : WithTop ℤ) ≤ ord (A.field i) (norm (A.field i) K z)
    rw [ord_norm, (origin_residueDegrees F K hres (A.field i)).2, one_nsmul]
    exact hz
  have ht := A.upperTrace_mem hres i _ hz
  have hbound : (A.stationaryDepth i : ℤ) ≤
      (((A.t 1 : ℤ) + 1 + if i = 0 then
        2 * ((A.t 1 : ℤ) + 1) - ((A.t 0 : ℤ) + 1) else (A.t 0 : ℤ) + 1) / 2) := by
    have hs := A.smallest
    fin_cases i <;> simp only [stationaryDepth] <;> norm_num <;> omega
  rw [norm_one_sub_charTwo (A.field i) K
    (originLine_degrees F K (A.g i) (A.nontrivial i)).2,
    CharTwo.sub_eq_add]
  simp only [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  exact (lattice (A.field i) _).add_mem
    (lattice_antitone _ hbound ht)
    (lattice_antitone _ (by exact_mod_cast (A.depth_ledger i).2.1) hn)

/-- The normalized trace `hᵢ = Sᵢ(Yz)/dᵢ` has depth at least `r₂`,
including the loss of `2δ` on the first lower field. -/
theorem normalizedTrace_mem (hres : residueDegree F K = 1) (i : Fin 3)
    {z : K} (hz : z ∈ lattice K ((A.t 1 : ℤ) + 1)) :
    Algebra.trace (A.field i) K (A.Y * z) /
      algebraMap F (A.field i) (A.root i) ∈ lattice (A.field i) (A.lowerDepth 1) := by
  have hY : A.Y ∈ lattice K (-(A.t 0 : ℤ)) := (A.origin_orders hres).1.ge
  have ht := A.upperTrace_mem hres i _ (mul_mem_lattice K hY hz)
  have hd : ord (A.field i) (algebraMap F (A.field i) (A.root i)) =
      ((2 * (((A.t 1 : ℤ) - A.t i) / 2) : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, (A.edge_ramification hres i).1, (A.scalar_data i).2.1,
      ← WithTop.coe_nsmul]
    congr 1
  apply (div_mem_lattice_iff _ _ _ _ _ hd).2
  apply lattice_antitone _ _ ht
  obtain ⟨a, ha⟩ := (A.edge 0).2.2.2.2.1
  obtain ⟨b, hb⟩ := (A.edge 1).2.2.2.2.1
  have hs := A.smallest
  have hthird := A.third_break
  fin_cases i <;> simp only [lowerDepth] <;> norm_num
  all_goals try rw [show A.t ⟨2, by decide⟩ = A.t 1 from hthird]
  all_goals omega

/-- Applying the actual lower norm character to `nᵢ(1-h)` kills the
entire lower-norm increment, on the whole specified ideal. -/
theorem lowerNorm_phase (hres : residueDegree F K = 1) (i : Fin 3)
    {h : A.field i} (hh : h ∈ lattice (A.field i) (A.lowerDepth i)) :
    originAddChar F P ((A.t 1 : ℤ) + 1)
      (A.beta i * (Algebra.norm F (1 - h) - 1)) = 1 := by
  let L := A.field i
  have hdegree := (originLine_degrees F K (A.g i) (A.nontrivial i)).1
  have hr := (A.depth_ledger i).2.2.1
  have hn : Algebra.norm F h ∈ lattice F (A.lowerDepth i) := by
    change (A.lowerDepth i : WithTop ℤ) ≤ ord F (norm F L h)
    rw [ord_norm, (origin_residueDegrees F K hres L).1, one_nsmul]
    exact hh
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F L
    (origin_residueDegrees F K hres L).1
  have ht := trace_mem_lattice_floor F L pi hpi hgen _ hh
  have htr : Algebra.trace F L h ∈ lattice F (A.lowerDepth i) := by
    apply lattice_antitone _ _ ht
    rw [(A.edge_ramification hres i).1, (A.edge i).2.2.2.2.2.2.2.2]
    simp only [lowerDepth, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    omega
  have hh0 := one_sub_ne_zero_of_lattice L hr hh
  let u := normUnits F L (Units.mk0 (1 - h) hh0)
  have hu : 1 - (u : F) = Algebra.trace F L h + Algebra.norm F h := by
    change 1 - Algebra.norm F (1 - h) = _
    rw [norm_one_sub_charTwo F L hdegree, CharTwo.sub_eq_add]
    simp only [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hlat : 1 - (u : F) ∈ lattice F (A.lowerDepth i) := by
    rw [hu]
    exact (lattice F _).add_mem htr hn
  have hf : ord F (A.f i) = ((-(A.t i : ℤ) : ℤ) : WithTop ℤ) := by
    rw [← P.laurentEquiv.apply_symm_apply (A.f i), P.laurentEquiv_order]
    exact (A.edge i).2.2.2.2.2.2.1
  have hchart := constructedNormCharacter_lowerChart F L hdegree P
    (A.f i) (A.z i) (A.edge i).1 (A.t i) (A.lowerDepth i) (A.t 1)
    hr (by
      obtain ⟨a, ha⟩ := (A.edge i).2.2.2.2.1
      simp only [lowerDepth]
      omega) (A.edge i).2.2.1 hf.ge u hlat
  have hone := (EqualChar.constructedNormCharacter F L hdegree
    (A.f i) (A.z i) (A.edge i).1).eq_one_on_normRange F L u
      ⟨Units.mk0 (1 - h) hh0, rfl⟩
  rw [hone] at hchart
  change 1 = originAddChar F P ((A.t 1 : ℤ) + 1)
    (A.beta i * (1 - Algebra.norm F (1 - h))) at hchart
  simpa only [CharTwo.sub_eq_add, add_comm] using hchart.symm

/-- The lower norm of the actual upper trace has trivial additive increment.
This retains the exact quotient by `dᵢ` and its actual norm. -/
theorem upperTraceNorm_phase (hres : residueDegree F K = 1) (i : Fin 3)
    {z : K} (hz : z ∈ lattice K ((A.t 1 : ℤ) + 1)) :
    originAddChar F P ((A.t 1 : ℤ) + 1)
      (Algebra.norm F (Algebra.trace (A.field i) K (A.Y * (1 - z))) -
        Algebra.norm F (Algebra.trace (A.field i) K A.Y)) = 1 := by
  let L := A.field i
  let d := algebraMap F L (A.root i)
  let h := Algebra.trace L K (A.Y * z) / d
  have hroot : A.root i ≠ 0 := by
    intro hzero
    have hord := (A.scalar_data i).2.1
    rw [hzero, ord_zero] at hord
    exact WithTop.top_ne_coe hord
  have hd : d ≠ 0 := by simpa [d] using (algebraMap F L).injective.ne hroot
  have hh : h ∈ lattice L (A.lowerDepth i) :=
    lattice_antitone L (A.depth_ledger i).2.2.2.1 (A.normalizedTrace_mem hres i hz)
  have htrace : Algebra.trace L K (A.Y * (1 - z)) = d * (1 - h) := by
    rw [mul_sub, mul_one, map_sub, (A.exact_origin i).2.1]
    dsimp only [h]
    field_simp
    rfl
  have hn : Algebra.norm F d = A.beta i := (A.scalar_data i).2.2.2.2
  rw [htrace, map_mul, hn, (A.exact_origin i).2.1, hn]
  rw [show A.beta i * Algebra.norm F (1 - h) - A.beta i =
    A.beta i * (Algebra.norm F (1 - h) - 1) by ring]
  exact A.lowerNorm_phase hres i hh

/-- The model value before restricting its argument to the stationary unit group. -/
def modelValue (i : Fin 3) (u : (A.field i)ˣ) : ℂˣ :=
  originAddChar F P ((A.t 1 : ℤ) + 1)
    (Algebra.trace F (A.field i) (Algebra.norm (A.field i) A.Y * (1 - (u : A.field i))))

/-- Both applications of the biquadratic `E₂` identity give the same base-field
phase, with the lower norm increment killed by its actual norm character. -/
theorem modelValue_norm (hres : residueDegree F K = 1) (i : Fin 3)
    {z : K} (hz : z ∈ lattice K ((A.t 1 : ℤ) + 1))
    (hz0 : 1 - z ≠ 0) :
    A.modelValue i (normUnits (A.field i) K (Units.mk0 (1 - z) hz0)) =
      originAddChar F P ((A.t 1 : ℤ) + 1)
        (elementarySymmetric F K 2 (A.Y * (1 - z)) - elementarySymmetric F K 2 A.Y) := by
  let L := A.field i
  letI : Algebra.IsQuadraticExtension F L :=
    ⟨(originLine_degrees F K (A.g i) (A.nontrivial i)).1⟩
  letI : Algebra.IsQuadraticExtension L K :=
    ⟨(originLine_degrees F K (A.g i) (A.nontrivial i)).2⟩
  have heq : elementarySymmetric F K 2 (A.Y * (1 - z)) -
      elementarySymmetric F K 2 A.Y =
      Algebra.trace F L (Algebra.norm L A.Y * (1 - Algebra.norm L (1 - z))) +
        (Algebra.norm F (Algebra.trace L K (A.Y * (1 - z))) -
          Algebra.norm F (Algebra.trace L K A.Y)) := by
    have hlinear : Algebra.trace F L
        (Algebra.norm L A.Y * (1 - Algebra.norm L (1 - z))) =
        Algebra.trace F L (Algebra.norm L A.Y) -
          Algebra.trace F L (Algebra.norm L A.Y * Algebra.norm L (1 - z)) := by
      rw [mul_sub, mul_one, map_sub]
    rw [Algebra.biquadraticE2 F K L, Algebra.biquadraticE2 F K L, hlinear]
    simp only [norm_apply, trace_apply, map_mul, CharTwo.sub_eq_add]
    abel
  rw [heq, ContinuousAddChar.map_add_eq_mul, A.upperTraceNorm_phase hres i hz, mul_one]
  rfl

omit [IsGalois F K] [CharP F 2] in
/-- Membership in the stationary domain, with the paper's `1-u` sign. -/
theorem modelDomain_iff (i : Fin 3) (u : (A.field i)ˣ) :
    u ∈ unitFiltration (A.field i) (A.stationaryDepth i) ↔
      1 - (u : A.field i) ∈ lattice (A.field i) (A.stationaryDepth i : ℤ) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (A.depth_ledger i).1)
  rw [hn, mem_unitFiltration_succ_iff_sub_mem_lattice]
  simp only [CharTwo.sub_eq_add, add_comm]

/-- The quadratic multiplication error lies in the actual base-character
triviality ideal; its estimate retains the full lower trace bound. -/
theorem modelError_phase (hres : residueDegree F K = 1) (i : Fin 3)
    {x y : A.field i}
    (hx : x ∈ lattice (A.field i) (A.stationaryDepth i : ℤ))
    (hy : y ∈ lattice (A.field i) (A.stationaryDepth i : ℤ)) :
    originAddChar F P ((A.t 1 : ℤ) + 1)
      (Algebra.trace F (A.field i) (Algebra.norm (A.field i) A.Y * (x * y))) = 1 := by
  let L := A.field i
  have ha : Algebra.norm L A.Y ∈ lattice L (-(A.t 0 : ℤ)) :=
    ((A.origin_orders hres).2.1 i).1.ge
  have he := mul_mem_lattice L ha (mul_mem_lattice L hx hy)
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F L
    (origin_residueDegrees F K hres L).1
  have ht := trace_mem_lattice_floor F L pi hpi hgen _ he
  apply (originAddChar_conductor F P ((A.t 1 : ℤ) + 1)).trivial
  apply lattice_antitone F _ ht
  rw [(A.edge_ramification hres i).1, (A.edge i).2.2.2.2.2.2.2.2]
  have hnum := (A.depth_ledger i).2.2.2.2
  push_cast
  omega

/-- The genuine group homomorphism prescribed by (D:EQ:Rmodel), constructed
from the origin and total ramification alone. -/
def stationaryCharacter (hres : residueDegree F K = 1) (i : Fin 3) :
    unitFiltration (A.field i) (A.stationaryDepth i) →* ℂˣ where
  toFun u := A.modelValue i u
  map_one' := by simp [modelValue]
  map_mul' u v := by
    let L := A.field i
    let Ψ := tracePullbackAddChar F L (originAddChar F P ((A.t 1 : ℤ) + 1))
    let a := Algebra.norm L A.Y
    let x := 1 - ((u : Lˣ) : L)
    let y := 1 - ((v : Lˣ) : L)
    have hx := (A.modelDomain_iff i (u : Lˣ)).mp u.property
    have hy := (A.modelDomain_iff i (v : Lˣ)).mp v.property
    have herr : Ψ (a * (x * y)) = 1 := A.modelError_phase hres i hx hy
    change Ψ (a * (1 - ((u : Lˣ) : L) * ((v : Lˣ) : L))) =
      Ψ (a * x) * Ψ (a * y)
    have heq : a * (1 - ((u : Lˣ) : L) * ((v : Lˣ) : L)) =
        (a * x + a * y) - a * (x * y) := by dsimp [x, y]; ring
    rw [heq, CharTwo.sub_eq_add, ContinuousAddChar.map_add_eq_mul,
      herr, mul_one, ContinuousAddChar.map_add_eq_mul]

/-- The constructed character has exactly the full stationary chart. -/
@[simp] theorem stationaryCharacter_apply (hres : residueDegree F K = 1) (i : Fin 3)
    (u : unitFiltration (A.field i) (A.stationaryDepth i)) :
    A.stationaryCharacter hres i u =
      tracePullbackAddChar F (A.field i) (originAddChar F P ((A.t 1 : ℤ) + 1))
        (Algebra.norm (A.field i) A.Y * (1 - ((u : (A.field i)ˣ) : A.field i))) := rfl

/-- These are continuous characters of the complete stationary unit groups. -/
theorem stationaryCharacter_continuous (hres : residueDegree F K = 1) (i : Fin 3) :
    Continuous (A.stationaryCharacter hres i) := by
  change Continuous (fun u : unitFiltration (A.field i) (A.stationaryDepth i) ↦
    tracePullbackAddChar F (A.field i) (originAddChar F P ((A.t 1 : ℤ) + 1))
      (Algebra.norm (A.field i) A.Y * (1 - ((u : (A.field i)ˣ) : A.field i))))
  exact ContinuousAddChar.continuous _ |>.comp
    (continuous_const.mul (continuous_const.sub (Units.continuous_val.comp continuous_subtype_val)))

end SimultaneousASGenerators

/-- **Compatibility on the full common unit subgroup (D:EQ:Rcompat).**
For every `z ∈ 𝔭_K^{T₂}`, every actual norm `Nᵢ(1-z)` belongs to the full
stationary domain and its constructed character value is the common `E₂`
phase. The origin data have a proved constructor `dyadicEqual_origin_exists`;
no stationary compatibility or phase identity is an input. -/
theorem compatibility (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (A : SimultaneousASGenerators F K P)
    (z : K) (hz : z ∈ lattice K ((A.t 1 : ℤ) + 1)) :
    ∃ hz0 : 1 - z ≠ 0, ∀ i : Fin 3,
      ∃ hu : normUnits (A.field i) K (Units.mk0 (1 - z) hz0) ∈
          unitFiltration (A.field i) (A.stationaryDepth i),
        A.stationaryCharacter hres i ⟨normUnits (A.field i) K (Units.mk0 (1 - z) hz0), hu⟩ =
          originAddChar F P ((A.t 1 : ℤ) + 1)
            (elementarySymmetric F K 2 (A.Y * (1 - z)) - elementarySymmetric F K 2 A.Y) := by
  have hz0 := one_sub_ne_zero_of_lattice K (by omega : 0 < (A.t 1 : ℤ) + 1) hz
  refine ⟨hz0, fun i ↦ ?_⟩
  have hu := (A.modelDomain_iff i (normUnits (A.field i) K (Units.mk0 (1 - z) hz0))).mpr
    (A.normIncrement_mem hres i hz)
  exact ⟨hu, A.modelValue_norm hres i hz hz0⟩

end

end LanglandsSecondMainLemma.Dyadic.Equal
