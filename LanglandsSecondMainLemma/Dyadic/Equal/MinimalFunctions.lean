import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Dyadic.Equal.MinimalOrigin
import LanglandsSecondMainLemma.Stationary.CommonFunction

/-!
# Full common functions in the minimal equal-characteristic row

The construction at `D:EQ:commonH-general`, lines 6501–6542 of the
corrected manuscript. Indices `0, 1, 2` denote the paper's `1, 2, 3`.
The actual norm increment is retained, and equality is proved for every
representative of its terminal class. Thus the functions include their
affine terms. All trace estimates use the different of the relevant edge.
-/

namespace LanglandsSecondMainLemma.Dyadic.Equal
open LanglandsFirstMainLemma
noncomputable section

open private originLine_degrees origin_residueDegrees from
  LanglandsSecondMainLemma.Dyadic.Equal.Origin
open private edge_ramification depth_ledger norm_one_sub_charTwo
  one_sub_ne_zero_of_lattice from LanglandsSecondMainLemma.Dyadic.Equal.Compatibility
open private model_ledger from LanglandsSecondMainLemma.Dyadic.Equal.Models
open private constructedNormCharacter_nontrivial from
  LanglandsSecondMainLemma.EqualChar.NormCharacter

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

/-- The positive terminal depth: `t₂` on side 1 and `(t₁+t₂)/2`
on sides 2 and 3. Subtraction is natural only here, where the depth is
proved at least two. All lattice exponents below are integers. -/
def minimalTerminalDepth (i : Fin 3) : ℕ := A.stationaryDepth i - 1

omit [IsGalois F K] [CharP F 2] [CharP K 2] in
private theorem terminal_ledger (i : Fin 3) :
    0 < A.minimalTerminalDepth i ∧
      A.minimalTerminalDepth i + 1 = A.stationaryDepth i ∧
      A.minimalConductor i = 2 * A.minimalTerminalDepth i + 1 ∧
      A.minimalTerminalDepth i ≤ A.t 1 := by
  have hm := model_ledger A i
  have hd := depth_ledger A i
  simp only [minimalTerminalDepth]
  omega

/-- At the negative order of the actual common numerator, the upper trace
has exact order `t₂-tᵢ`. To apply FML's nonnegative trace-shell theorem,
first multiply by a lower-field element of order `t₁`, then divide back.
In particular no negative ideal depth is truncated. -/
theorem minimalOrigin_trace_order (hres : residueDegree F K = 1)
    (C : K) (hC : ord K C = ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ)) (i : Fin 3) :
    ord (A.field i) (Algebra.trace (A.field i) K C) =
      (((A.t 1 : ℤ) - A.t i : ℤ) : WithTop ℤ) := by
  let L := A.field i
  obtain ⟨c, hc⟩ := exists_ord_eq L (A.t 0 : ℤ)
  have hc0 : c ≠ 0 := (ord_ne_top_iff L).mp (by rw [hc]; exact WithTop.coe_ne_top)
  let x := algebraMap L K c * C
  have hx : ord K x = ((A.t 0 : ℤ) : WithTop ℤ) := by
    dsimp only [x]
    rw [ord_mul, ord_algebraMap, (edge_ramification A hres i).2, hc, hC,
      ← WithTop.coe_nsmul, ← WithTop.coe_add]
    congr 1
    simp only [nsmul_eq_mul]
    ring
  have hshift : (A.t 0 : ℤ) + (differentExponent L K : ℤ) =
      2 * ((A.t 1 : ℤ) - A.t i + A.t 0) + 1 := by
    rw [A.upper_different hres i]
    have ht := A.third_break
    fin_cases i <;> norm_num
    all_goals try rw [show A.t ⟨2, by decide⟩ = A.t 1 from ht]
    all_goals ring
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer L K
    (origin_residueDegrees F K hres L).2
  have ht := (quadratic_trace_shell_iff L K pi hpi hgen (by positivity)
    (edge_ramification A hres i).2
    (originLine_degrees F K (A.g i) (A.nontrivial i)).2 hshift x hx.ge).2 hx
  have he : Algebra.trace L K x = c * Algebra.trace L K C := by
    change Algebra.trace L K (algebraMap L K c * C) = _
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have he' : Algebra.trace L K C = Algebra.trace L K x / c := by
    rw [he, mul_div_cancel_left₀ _ hc0]
  rw [he', ord_div, ht, hc, ← WithTop.LinearOrderedAddCommGroup.coe_sub]
  congr 1
  ring

/-- The actual upper norm increment at source depth `t₂` belongs to the
terminal ideal. Both its trace and its norm term are estimated. -/
theorem minimalNormIncrement_mem (hres : residueDegree F K = 1) (i : Fin 3)
    {u : K} (hu : u ∈ lattice K (A.t 1 : ℤ)) :
    Algebra.norm (A.field i) (1 + u) - 1 ∈
      lattice (A.field i) (A.minimalTerminalDepth i : ℤ) := by
  have hn : Algebra.norm (A.field i) u ∈ lattice (A.field i) (A.t 1 : ℤ) := by
    change _ ≤ ord (A.field i) (norm (A.field i) K u)
    rw [ord_norm, (origin_residueDegrees F K hres (A.field i)).2, one_nsmul]
    exact hu
  have ht := A.upperTrace_mem hres i _ hu
  have hb : (A.minimalTerminalDepth i : ℤ) ≤
      ((A.t 1 : ℤ) + if i = 0 then
        2 * ((A.t 1 : ℤ) + 1) - ((A.t 0 : ℤ) + 1) else (A.t 0 : ℤ) + 1) / 2 := by
    have hs := A.smallest
    have hl := A.terminal_ledger i
    obtain ⟨a, ha⟩ := (A.edge 0).2.2.2.2.1
    obtain ⟨b, hb⟩ := (A.edge 1).2.2.2.2.1
    fin_cases i <;> simp only [stationaryDepth] at hl ⊢ <;> norm_num at hl ⊢ <;> omega
  have he := norm_one_sub_charTwo (A.field i) K
    (originLine_degrees F K (A.g i) (A.nontrivial i)).2 u
  simp only [CharTwo.sub_eq_add] at he ⊢
  rw [he]
  have he' : 1 + Algebra.trace (A.field i) K u + Algebra.norm (A.field i) u + 1 =
      Algebra.trace (A.field i) K u + Algebra.norm (A.field i) u := by
    linear_combination (norm := ring_nf) CharTwo.add_self_eq_zero (1 : A.field i)
  rw [he']
  exact (lattice _ _).add_mem (lattice_antitone _ hb ht)
    (lattice_antitone _ (by exact_mod_cast (A.terminal_ledger i).2.2.2) hn)

/-- At the actual different, the relative upper-trace change has depth at
least `r₂`, including the first side's loss of `2δ`. -/
theorem minimalRelativeTrace_mem (hres : residueDegree F K = 1)
    (C : K) (hC : ord K C = ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ))
    (i : Fin 3) {u : K} (hu : u ∈ lattice K (A.t 1 : ℤ)) :
    Algebra.trace (A.field i) K (C * u) / Algebra.trace (A.field i) K C ∈
      lattice (A.field i) (A.lowerDepth 1) := by
  have ht := A.upperTrace_mem hres i _ (mul_mem_lattice K hC.ge hu)
  apply (div_mem_lattice_iff _ _ _ _ _ (A.minimalOrigin_trace_order hres C hC i)).2
  apply lattice_antitone _ _ ht
  have hs := A.smallest
  have ht₃ := A.third_break
  obtain ⟨a, ha⟩ := (A.edge 0).2.2.2.2.1
  obtain ⟨b, hb⟩ := (A.edge 1).2.2.2.2.1
  fin_cases i <;> simp only [lowerDepth] <;> norm_num
  all_goals try rw [show A.t ⟨2, by decide⟩ = A.t 1 from ht₃]
  all_goals omega


/-- The canonical scaled residue character with its exact conductor. -/
def minimalBasePsi : LocalAddCharData F :=
  ⟨originAddChar F P ((A.t 1 : ℤ) + 1), -((A.t 1 : ℤ) + 1),
    originAddChar_conductor F P ((A.t 1 : ℤ) + 1)⟩

/-- The actual trace pullback, at the lower edge's actual different. -/
def minimalUpperPsi (hres : residueDegree F K = 1) (i : Fin 3) :
    LocalAddCharData (A.field i) :=
  ⟨tracePullbackAddChar F (A.field i) A.minimalBasePsi.character,
    -A.additiveModulus i, A.modelAddChar_conductor hres i⟩

/-- The full critical function on the terminal ideal, with the actual upper
norm as coefficient. It is subsequently proved constant on terminal cosets. -/
def minimalFullFunction (hres : residueDegree F K = 1)
    (θ : ContinuousQuasiChar (A.field i)) (C : Kˣ)
    (v : lattice (A.field i) (A.minimalTerminalDepth i : ℤ)) : ℂ :=
  Stationary.normalizedCriticalValue (A.field i) (canonicalLocalQuasiCharData _ θ)
    (A.minimalUpperPsi hres i) (normUnits (A.field i) K C)
    (A.minimalTerminalDepth i) (A.terminal_ledger i).1 v

/-- The common value of `U:common-function`, with the actual perturbed
numerator `C * U` and the actual character value `Θ U`. -/
def minimalCommonValue (Θ : ContinuousQuasiChar K) (C U : Kˣ) : ℂ :=
  (Θ U : ℂ)⁻¹ * (A.minimalBasePsi.character
    (-elementarySymmetric F K 2 ((C * U : Kˣ) : K) +
      elementarySymmetric F K 2 (C : K)) : ℂ)

/-- The precise stationary information furnished by `minimalOrigin`.
This proposition has a constructor from the genuine family below; none
of these charts is an extra hypothesis of the public theorem. -/
structure IsMinimalFunctionOrigin
    (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i)) (C : Kˣ) : Prop where
  order : ord K (C : K) = ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ)
  conductor : ∀ i, multiplicativeConductorExponent (A.field i) (θ i) = A.minimalConductor i
  upper : ∀ i : Fin 3, i ≠ 2 ∨ A.t 0 = A.t 1 → ∀ v : (A.field i)ˣ,
    1 - (v : A.field i) ∈ lattice (A.field i) (A.stationaryDepth i : ℤ) →
    θ i v = tracePullbackAddChar F (A.field i) A.minimalBasePsi.character
      (Algebra.norm (A.field i) (C : K) * (1 - (v : A.field i)))
  lower : ∀ i : Fin 3, i ≠ 2 ∨ A.t 0 = A.t 1 →
    ∀ ω : NormCharacter F (A.field i), ω ≠ 1 → ∀ v : Fˣ,
    1 - (v : F) ∈ lattice F (A.lowerDepth i) →
    ω.1 v = A.minimalBasePsi.character
      (Algebra.norm F (Algebra.trace (A.field i) K (C : K)) * (1 - (v : F)))

/-- Construct the origin and its charts from the primitive compatible family.
Minimality on side 1 forces the full minimal row by the proved twist theorem. -/
theorem minimalFunctionOrigin_exists (hres : residueDegree F K = 1)
    (Θ : ContinuousQuasiChar K) (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hcompatible : ∀ i, normQuasiChar (A.field i) K (θ i) = Θ)
    (hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Θ)
    (hminimal : multiplicativeConductorExponent (A.field 0) (θ 0) = A.minimalConductor 0) :
    ∃ C : Kˣ, A.IsMinimalFunctionOrigin θ C := by
  obtain ⟨X, hC, hcharts⟩ := minimalOrigin hres P A Θ θ hcompatible hprimitive hminimal
  have hC0 : A.Y + (X : K) ≠ 0 :=
    (ord_ne_top_iff K).mp (by rw [hC]; exact WithTop.coe_ne_top)
  obtain ⟨Θc, χ, lambda, _, _, _, _, _, _, _, _, hranges⟩ :=
    twist hres P A Θ θ hcompatible hprimitive
  have hn : multiplicativeConductorExponent F lambda < A.twistThreshold := by
    by_contra h
    have hlt := (hranges.2 (Nat.le_of_not_gt h) 0).2.2
    change A.minimalConductor 0 < multiplicativeConductorExponent (A.field 0) (θ 0) at hlt
    rw [hminimal] at hlt
    exact lt_irrefl _ hlt
  exact ⟨Units.mk0 _ hC0, hC, fun i ↦ (hranges.1 hn i).1,
    fun i hi ↦ (hcharts i hi).1, fun i hi ↦ (hcharts i hi).2⟩

private theorem scale_one (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (Ψ : LocalAddCharData E) : scaleAddCharData E Ψ 1 = Ψ := by
  apply LocalAddCharData.eq_of_character_eq
  ext x
  simp only [scaleAddCharData_character_apply, Units.val_one, one_mul]

/-- Independence of the full critical value from its terminal representative,
using the actual numerator's exact order and the whole upper stationary chart. -/
theorem minimalFullFunction_eq_of_congruent (hres : residueDegree F K = 1)
    (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i)) (C : Kˣ)
    (hC : A.IsMinimalFunctionOrigin θ C) (i : Fin 3) (hi : i ≠ 2 ∨ A.t 0 = A.t 1)
    (v w : lattice (A.field i) (A.minimalTerminalDepth i : ℤ))
    (hvw : CongruentAtDepth (A.stationaryDepth i : ℤ) (v : A.field i) (w : A.field i)) :
    A.minimalFullFunction hres (θ i) C v = A.minimalFullFunction hres (θ i) C w := by
  let L := A.field i
  let χ := canonicalLocalQuasiCharData L (θ i)
  have hm : χ.conductor = 2 * A.minimalTerminalDepth i + 1 :=
    (hC.conductor i).trans (A.terminal_ledger i).2.2.1
  have hlarge : 1 < χ.conductor := by have := (A.terminal_ledger i).1; omega
  have hZ : ord L (normUnits L K C : L) =
      ((-(scaleAddCharData L (A.minimalUpperPsi hres i) 1).conductor -
        (χ.conductor : ℤ) : ℤ) : WithTop ℤ) := by
    rw [scale_one]
    change ord L (norm L K (C : K)) =
      ((-(-A.additiveModulus i) - (multiplicativeConductorExponent L (θ i) : ℤ) : ℤ) : WithTop ℤ)
    rw [ord_norm, (origin_residueDegrees F K hres L).2, one_nsmul, hC.order,
      hC.conductor i, (model_ledger A i).2.2.2.1]
    congr 1
    ring
  have hs : Stationary.IsNormalizedStationaryCoefficientAtDepth L χ
      (scaleAddCharData L (A.minimalUpperPsi hres i) 1) (normUnits L K C)
      (A.minimalTerminalDepth i + 1) (by have := (A.terminal_ledger i).1; omega) := by
    rw [scale_one]
    intro z
    have hz : 1 - ((positiveUnitOfLattice L (by have := (A.terminal_ledger i).1; omega) (-z) : Lˣ) : L) =
        (z : L) := by simp only [coe_positiveUnitOfLattice, Submodule.coe_neg]; ring
    exact (hC.upper i hi _ (by rw [hz]; simpa only [(A.terminal_ledger i).2.1] using z.property)).trans
      (by rw [hz]; rfl)
  have he := Stationary.normalizedCriticalValue_odd_eq_of_congruent L χ
    (A.minimalUpperPsi hres i) 1 (normUnits L K C) (A.minimalTerminalDepth i)
    hm hlarge hZ hs v w (by simpa only [(A.terminal_ledger i).2.1] using hvw)
  simpa only [scale_one, minimalFullFunction, χ, L] using he


/-- The lower norm of every relative trace change on the required ideal
stays in the lower stationary group. The quadratic trace and norm terms
are both retained, with the lower edge's different `tᵢ+1`. -/
theorem minimalLowerNormIncrement_mem (hres : residueDegree F K = 1) (i : Fin 3)
    {h : A.field i} (hh : h ∈ lattice (A.field i) (A.lowerDepth 1)) :
    Algebra.norm F (1 + h) - 1 ∈ lattice F (A.lowerDepth i) := by
  let L := A.field i
  have hh' := lattice_antitone L (depth_ledger A i).2.2.2.1 hh
  have hn : Algebra.norm F h ∈ lattice F (A.lowerDepth i) := by
    change _ ≤ ord F (norm F L h)
    rw [ord_norm, (origin_residueDegrees F K hres L).1, one_nsmul]
    exact hh'
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F L
    (origin_residueDegrees F K hres L).1
  have ht := trace_mem_lattice_floor F L pi hpi hgen _ hh'
  have ht' : Algebra.trace F L h ∈ lattice F (A.lowerDepth i) := by
    apply lattice_antitone _ _ ht
    rw [(edge_ramification A hres i).1, (A.edge i).2.2.2.2.2.2.2.2]
    simp only [lowerDepth, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    omega
  have he := norm_one_sub_charTwo F L
    (originLine_degrees F K (A.g i) (A.nontrivial i)).1 h
  simp only [CharTwo.sub_eq_add] at he ⊢
  rw [he]
  have he' : 1 + Algebra.trace F L h + Algebra.norm F h + 1 =
      Algebra.trace F L h + Algebra.norm F h := by
    linear_combination (norm := ring_nf) CharTwo.add_self_eq_zero (1 : F)
  rw [he']
  exact (lattice _ _).add_mem ht' hn

/-- The perturbed trace is nonzero and its actual relative norm lies in the
full lower stationary group. These conclusions hold for every origin of
the prescribed order, not just a chosen exact norm representative. -/
theorem minimalTraceNorm_control (hres : residueDegree F K = 1)
    (C U : Kˣ) (hC : ord K (C : K) = ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ))
    (hU : (U : K) - 1 ∈ lattice K (A.t 1 : ℤ)) (i : Fin 3) :
    Algebra.trace (A.field i) K ((C * U : Kˣ) : K) ≠ 0 ∧
      Algebra.norm F (Algebra.trace (A.field i) K ((C * U : Kˣ) : K) /
        Algebra.trace (A.field i) K (C : K)) - 1 ∈ lattice F (A.lowerDepth i) := by
  let L := A.field i
  let d := Algebra.trace L K (C : K)
  let h := Algebra.trace L K ((C : K) * ((U : K) - 1)) / d
  have hd : d ≠ 0 := (ord_ne_top_iff L).mp (by
    rw [A.minimalOrigin_trace_order hres (C : K) hC i]
    exact WithTop.coe_ne_top)
  have hh : h ∈ lattice L (A.lowerDepth 1) := A.minimalRelativeTrace_mem hres _ hC i hU
  have hh0 : 1 + h ≠ 0 := by
    simpa only [CharTwo.sub_eq_add] using
      one_sub_ne_zero_of_lattice L (depth_ledger A 1).2.2.1 hh
  have ht : Algebra.trace L K ((C * U : Kˣ) : K) = d * (1 + h) := by
    dsimp only [h, d]
    rw [mul_sub, mul_one, map_sub]
    change Algebra.trace L K ((C : K) * (U : K)) = _
    field_simp [show Algebra.trace L K (C : K) ≠ 0 from hd]
    ring
  refine ⟨ht ▸ mul_ne_zero hd hh0, ?_⟩
  rw [ht, mul_div_cancel_left₀ _ hd]
  exact A.minimalLowerNormIncrement_mem hres i hh

/-- The entire lower additive phase is one, evaluated by the full lower
chart on the actual norm of the trace quotient. Norm surjectivity is never
used. The lemma applies to every nontrivial lower norm character. -/
theorem minimalLowerPhase (hres : residueDegree F K = 1)
    (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i)) (C U : Kˣ)
    (hC : A.IsMinimalFunctionOrigin θ C)
    (hU : (U : K) - 1 ∈ lattice K (A.t 1 : ℤ))
    (i : Fin 3) (hi : i ≠ 2 ∨ A.t 0 = A.t 1)
    (ω : NormCharacter F (A.field i)) (hω : ω ≠ 1)
    (hd : trace (A.field i) K (C : K) ≠ 0)
    (hd' : trace (A.field i) K ((C * U : Kˣ) : K) ≠ 0) :
    let W := Stationary.commonOriginLowerCoefficient (A.field i) C hd
    let W' := Stationary.commonOriginLowerCoefficient (A.field i) (C * U) hd'
    A.minimalBasePsi.character (-(W : F) * (((W' / W : Fˣ) : F) - 1)) = 1 ∧
      ω.1 (W' / W) = 1 := by
  dsimp only
  let L := A.field i
  let W := Stationary.commonOriginLowerCoefficient L C hd
  let W' := Stationary.commonOriginLowerCoefficient L (C * U) hd'
  let R := Units.mk0 (trace L K ((C * U : Kˣ) : K)) hd' /
    Units.mk0 (trace L K (C : K)) hd
  have hs : W' / W = normUnits F L R := (map_div _ _ _).symm
  have hsval : ((W' / W : Fˣ) : F) =
      Algebra.norm F (Algebra.trace L K ((C * U : Kˣ) : K) /
        Algebra.trace L K (C : K)) := by
    rw [hs]
    change Algebra.norm F (R : L) = _
    simp only [R, Units.val_div_eq_div_val, Units.val_mk0]
  have hmem : 1 - ((W' / W : Fˣ) : F) ∈ lattice F (A.lowerDepth i) := by
    rw [hsval]
    simpa only [neg_sub] using (lattice F _).neg_mem
      (A.minimalTraceNorm_control hres C U hC.order hU i).2
  have hone : ω.1 (W' / W) = 1 :=
    ω.eq_one_on_normRange F L _ ⟨R, hs.symm⟩
  refine ⟨?_, hone⟩
  change A.minimalBasePsi.character (-(W : F) * (((W' / W : Fˣ) : F) - 1)) = 1
  have he : -(W : F) * (((W' / W : Fˣ) : F) - 1) =
      (W : F) * (1 - ((W' / W : Fˣ) : F)) := by ring
  rw [he]
  change A.minimalBasePsi.character
    (Algebra.norm F (Algebra.trace L K (C : K)) * (1 - ((W' / W : Fˣ) : F))) = 1
  rw [← hC.lower i hi ω hω _ hmem]
  exact hone


/-- A representative of the actual graded upper norm map. The argument is
an actual unit in `1 + 𝓅_K^t₂`; no onto property is asserted. -/
def minimalNormCoordinate (hres : residueDegree F K = 1)
    (U : Kˣ) (hU : (U : K) - 1 ∈ lattice K (A.t 1 : ℤ)) (i : Fin 3) :
    lattice (A.field i) (A.minimalTerminalDepth i : ℤ) :=
  ⟨(normUnits (A.field i) K U : A.field i) - 1, by
    have he : 1 + ((U : K) - 1) = (U : K) := by ring
    simpa only [he, coe_normUnits] using A.minimalNormIncrement_mem hres i hU⟩

/-- `U:common-function` on the actual norm coordinate. The full lower factor
is evaluated on the actual trace quotient and proved one before removal. -/
theorem minimalFullFunction_norm (hres : residueDegree F K = 1)
    (Θ : ContinuousQuasiChar K) (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hcompatible : ∀ i, normQuasiChar (A.field i) K (θ i) = Θ)
    (C : Kˣ) (hC : A.IsMinimalFunctionOrigin θ C)
    (i : Fin 3) (hi : i ≠ 2 ∨ A.t 0 = A.t 1)
    (U : Kˣ) (hU : (U : K) - 1 ∈ lattice K (A.t 1 : ℤ)) :
    A.minimalFullFunction hres (θ i) C (A.minimalNormCoordinate hres U hU i) =
      A.minimalCommonValue Θ C U := by
  let L := A.field i
  have hdegree := originLine_degrees F K (A.g i) (A.nontrivial i)
  letI : Algebra.IsQuadraticExtension F L := ⟨hdegree.1⟩
  letI : Algebra.IsQuadraticExtension L K := ⟨hdegree.2⟩
  let ω := EqualChar.constructedNormCharacter F L hdegree.1 (A.f i) (A.z i) (A.edge i).1
  have hω : ω ≠ 1 := constructedNormCharacter_nontrivial F L hdegree.1
    (A.f i) (A.z i) (A.edge i).1 (A.edge i).2.1
  let χ := canonicalLocalQuasiCharData L (θ i)
  let ωd := canonicalLocalQuasiCharData F ω.1
  have hd : trace L K (C : K) ≠ 0 := (ord_ne_top_iff L).mp (by
    rw [A.minimalOrigin_trace_order hres (C : K) hC.order i]
    exact WithTop.coe_ne_top)
  have hd' : trace L K ((C * U : Kˣ) : K) ≠ 0 :=
    (A.minimalTraceNorm_control hres C U hC.order hU i).1
  have hpoint := Stationary.commonFunctionProduct_eq L χ ωd ω rfl Θ (hcompatible i)
    A.minimalBasePsi (A.minimalUpperPsi hres i) rfl 1 C (C * U) hd hd'
  have hlow := A.minimalLowerPhase hres θ C U hC hU i hi ω hω hd hd'
  have hr : normUnits L K (C * U) / normUnits L K C = normUnits L K U := by
    rw [map_mul, mul_div_cancel_left]
  have hv : (positiveUnitOfLattice L (A.terminal_ledger i).1
      (A.minimalNormCoordinate hres U hU i) : Lˣ) = normUnits L K U := by
    apply Units.ext
    change 1 + ((normUnits L K U : L) - 1) = _
    ring
  have hprod : Stationary.commonFunctionProduct L χ ωd A.minimalBasePsi
      (A.minimalUpperPsi hres i) 1 C (C * U) hd hd' =
        A.minimalFullFunction hres (θ i) C (A.minimalNormCoordinate hres U hU i) := by
    dsimp only [Stationary.commonFunctionProduct]
    rw [map_one, scale_one, scale_one, hr, hlow.1]
    change _ * (1 : ℂˣ).val * (ω.1 _ : ℂ)⁻¹ = _
    rw [hlow.2]
    simp only [Units.val_one, inv_one, mul_one]
    dsimp only [minimalFullFunction, Stationary.normalizedCriticalValue]
    rw [hv]
    rfl
  rw [hprod, mul_div_cancel_left, scale_one] at hpoint
  exact hpoint

end SimultaneousASGenerators

/-- **The full identity `D:EQ:commonH-general`.** From the actual primitive
compatible minimal family, construct one numerator `C`. For every compared
side and every `U ∈ 1 + 𝓅_K^t₂`, its full critical function at *any*
representative of the actual graded norm class equals the same value
`Θ(U)⁻¹ Ψ_F(-E₂(CU)+E₂(C))`.

The source parameter in the paper is `U = 1 + π^t₂ z`, `z ∈ 𝒪_K`.
The congruence formulation below is precisely `Hᵢ(pᵢ(z)) = Q(z)` and
also proves independence of the terminal lift. The norm coordinate is
constructed by `minimalNormCoordinate`. The conclusion retains both
nonzero traces and the lower relative norm's membership in its full
stationary ideal. Indices 0 and 1 always apply; index 2 also applies when
the breaks agree. Uniformizer values of quasi-characters are unrestricted. -/
theorem dyadicEqual_minimal_commonFunctions (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (A : SimultaneousASGenerators F K P)
    (Θ : ContinuousQuasiChar K) (θ : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hcompatible : ∀ i, normQuasiChar (A.field i) K (θ i) = Θ)
    (hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Θ)
    (hminimal : multiplicativeConductorExponent (A.field 0) (θ 0) = A.minimalConductor 0) :
    ∃ C : Kˣ, A.IsMinimalFunctionOrigin θ C ∧
      ∀ i : Fin 3, i ≠ 2 ∨ A.t 0 = A.t 1 →
        trace (A.field i) K (C : K) ≠ 0 ∧
        ∀ (U : Kˣ) (hU : (U : K) - 1 ∈ lattice K (A.t 1 : ℤ)),
          trace (A.field i) K ((C * U : Kˣ) : K) ≠ 0 ∧
          Algebra.norm F (trace (A.field i) K ((C * U : Kˣ) : K) /
            trace (A.field i) K (C : K)) - 1 ∈ lattice F (A.lowerDepth i) ∧
          ∀ v : lattice (A.field i) (A.minimalTerminalDepth i : ℤ),
            CongruentAtDepth (A.stationaryDepth i : ℤ) (v : A.field i)
              (A.minimalNormCoordinate hres U hU i : A.field i) →
            A.minimalFullFunction hres (θ i) C v = A.minimalCommonValue Θ C U := by
  obtain ⟨C, hC⟩ := A.minimalFunctionOrigin_exists hres Θ θ hcompatible hprimitive hminimal
  refine ⟨C, hC, fun i hi ↦ ⟨?_, fun U hU ↦ ?_⟩⟩
  · apply (ord_ne_top_iff (A.field i)).mp
    rw [A.minimalOrigin_trace_order hres (C : K) hC.order i]
    exact WithTop.coe_ne_top
  · obtain ⟨ht, hn⟩ := A.minimalTraceNorm_control hres C U hC.order hU i
    refine ⟨ht, hn, fun v hv ↦ ?_⟩
    exact (A.minimalFullFunction_eq_of_congruent hres θ C hC i hi v
      (A.minimalNormCoordinate hres U hU i) hv).trans
      (A.minimalFullFunction_norm hres Θ θ hcompatible C hC i hi U hU)

end
end LanglandsSecondMainLemma.Dyadic.Equal
