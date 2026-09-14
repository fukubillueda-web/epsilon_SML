import LanglandsFirstMainLemma.Delta.Elementary
import LanglandsFirstMainLemma.Delta.FirstMainStatement
import LanglandsFirstMainLemma.Delta.LocalConstantRealization
import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsFirstMainLemma.Main
import LanglandsSecondMainLemma.Tame.FiniteComparison
import LanglandsSecondMainLemma.Tame.Covector
import LanglandsSecondMainLemma.Tame.ConductorReduction
import LanglandsSecondMainLemma.Characters.InducingChoice

/-!
# Tame / Comparison

Blueprint: blueprint/tasks/Tame/Comparison.md
Paper: O:F:tame

The conductor-one branch derives the finite-field compatibility, primitivity,
additive transports, and complete lower correction products from the local
pair. The higher-conductor branch constructs the common covector and applies
exact stable twist and FML. Tame inertia supplies the distinguished unramified
field; inducing-choice independence assembles `comparison` for arbitrary pairs.
-/

namespace LanglandsSecondMainLemma.Tame

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

private theorem phase_product {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    phase (∏ i ∈ s, f i) = ∏ i ∈ s, phase (f i) := by
  rw [phase_of_ne_zero (Finset.prod_ne_zero_iff.mpr hf), norm_prod,
    Complex.ofReal_prod, ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl (fun i hi => (phase_of_ne_zero (hf i hi)).symm)

/-- The phase identity used in the final conductor-one calculation.
The degree-scaling character and every lower Gauss factor remain explicit,
including the single quadratic factor when `ell = 2`. -/
theorem finiteComparison_phase
    {k κ : Type*} [Field k] [Fintype k] [Field κ] [Fintype κ] [Algebra k κ]
    (ell : ℕ) (hell : ell.Prime) (hdegree : Module.finrank k κ = ell)
    (hdiv : ell ∣ Fintype.card k - 1)
    (χκ : FiniteMulChar κ) (χ₀ μ : FiniteMulChar k)
    (hμ : orderOf μ = ell) (hcompat : χκ ^ ell = normMulChar k κ χ₀)
    (hprim : ∃ u : kˣ, u ^ ell = 1 ∧ χ₀ (u : k) ≠ 1)
    (ψ : FiniteAddChar k) (hψ : ψ ≠ 1) :
    phase (langlandsGaussSum χκ (traceAddChar k κ ψ)) =
      χ₀ (ell : k) * phase (langlandsGaussSum χ₀ ψ) *
        ∏ j ∈ Finset.Icc 1 (ell - 1), phase (langlandsGaussSum (μ ^ j) ψ) := by
  classical
  have hden := finiteComparisonDenominator_ne_zero ell hdiv χ₀ μ ψ hψ
  have hχ : χ₀ (ell : k) ≠ 0 := by
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hden).1).1
  have hellk : (ell : k) ≠ 0 := by
    intro h
    exact hχ (by rw [h, MulChar.map_zero])
  have hnorm : ‖χ₀ (ell : k)‖ = 1 :=
    Complex.norm_eq_one_of_mem_rootsOfUnity
      (χ₀.apply_mem_rootsOfUnity (Units.mk0 (ell : k) hellk))
  rw [finiteComparison ell hell hdegree hdiv χκ χ₀ μ hμ hcompat hprim ψ hψ,
    phase_mul (mul_ne_zero hχ (langlandsGaussSum_ne_zero χ₀ hψ))
      (Finset.prod_ne_zero_iff.mpr (fun j _ => langlandsGaussSum_ne_zero (μ ^ j) hψ)),
    phase_mul_of_norm_eq_one hnorm (langlandsGaussSum_ne_zero χ₀ hψ),
    phase_product _ _ (fun j _ => langlandsGaussSum_ne_zero (μ ^ j) hψ)]

/-- A nontrivial residue Frobenius quotient produces the literal root of
unity required by the finite comparison. It is the indicated power of the
norm of the witnessing unit, so no choice of a cyclic generator is needed. -/
theorem finiteComparison_primitive_of_frobenius
    {k κ : Type*} [Field k] [Fintype k] [Field κ] [Fintype κ] [Algebra k κ]
    (ell : ℕ) (hdiv : ell ∣ Fintype.card k - 1)
    (χκ : FiniteMulChar κ) (χ₀ : FiniteMulChar k)
    (hcompat : χκ ^ ell = normMulChar k κ χ₀)
    (hFrob : ∃ x : κˣ, χκ (x : κ) ^ (Fintype.card k - 1) ≠ 1) :
    ∃ u : kˣ, u ^ ell = 1 ∧ χ₀ (u : k) ≠ 1 := by
  obtain ⟨x, hx⟩ := hFrob
  let d := (Fintype.card k - 1) / ell
  have hd : ell * d = Fintype.card k - 1 := Nat.mul_div_cancel' hdiv
  let u := normUnits k κ x ^ d
  have hnorm := DFunLike.congr_fun hcompat (x : κ)
  rw [MulChar.pow_apply_coe, normMulChar_apply] at hnorm
  refine ⟨u, ?_, ?_⟩
  · dsimp only [u]
    rw [← pow_mul, Nat.mul_comm d ell, hd]
    apply Units.ext
    exact FiniteField.pow_card_sub_one_eq_one _ (Units.ne_zero (normUnits k κ x))
  · have heval : χ₀ (u : k) = χκ (x : κ) ^ (Fintype.card k - 1) := by
      dsimp only [u]
      rw [Units.val_pow_eq_pow_val, map_pow, coe_normUnits]
      change χ₀ (residueNorm k κ (x : κ)) ^ d = _
      rw [← hnorm, ← pow_mul, hd]
    rwa [heval]

section LocalFormula

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance : Fintype (ResidueField F) := residueFieldFintype F

/-- The conductor-one formula for the canonical local constant, using an
arbitrary denominator of the exact integer order `n(ψ) + 1`. -/
theorem localConstant_conductorOne
    (χ : LocalQuasiCharData F) (hχ : χ.conductor = 1)
    (ψ : LocalAddCharData F) (γ : Fˣ)
    (hγ : ord F (γ : F) = ((ψ.conductor + 1 : ℤ) : WithTop ℤ)) :
    localConstant F χ.character ψ.character =
      -(χ.character γ : ℂ) * phase (langlandsGaussSum (residualMulChar F χ)
        (residualAddChar F ψ γ hγ)) := by
  let Γ : AdmissibleGamma F χ ψ := ⟨γ, by simpa [hχ, add_comm] using hγ⟩
  rw [localConstant_isDeltaFinite F χ ψ Γ]
  exact deltaFinite_conductor_one F χ hχ ψ Γ

end LocalFormula

section ResidualAdditive

variable (F E : Type) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]

local instance : Fintype (ResidueField F) := residueFieldFintype F
local instance : Fintype (ResidueField E) := residueFieldFintype E

/-- On the unramified edge, a denominator of order `n_F + 1` is
admissible upstairs and the actual residue additive character is the
finite-field trace pullback. -/
theorem unramified_residualAddChar
    (hunr : ramificationIndex F E = 1)
    (ψF : LocalAddCharData F) (ψE : LocalAddCharData E)
    (hψ : ψE.character = tracePullbackAddChar F E ψF.character)
    (γ : Fˣ) (hγ : ord F (γ : F) = ((ψF.conductor + 1 : ℤ) : WithTop ℤ)) :
    ∃ hγE : ord E (algebraMap F E (γ : F)) =
        ((ψE.conductor + 1 : ℤ) : WithTop ℤ),
      residualAddChar E ψE (Units.map (algebraMap F E).toMonoidHom γ) hγE =
        traceAddChar (ResidueField F) (ResidueField E)
          (residualAddChar F ψF γ hγ) := by
  have hn : ψE.conductor = ψF.conductor := by
    apply ψE.isConductor.unique
    rw [hψ]
    exact (unramified_additiveConductor_compTrace F E hunr
      ψF.character ψF.conductor).2 ψF.isConductor
  have hγE : ord E (algebraMap F E (γ : F)) =
      ((ψE.conductor + 1 : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hunr, one_nsmul, hγ, hn]
  refine ⟨hγE, ?_⟩
  ext x
  obtain ⟨z, rfl⟩ := residueMap_surjective E x
  have hzE : (z : E) ∈ lattice E 0 := (mem_lattice_zero_iff E).2 z.property
  have hzF : (integralTrace F E z : F) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (integralTrace F E z).property
  change residualAddChar E ψE (Units.map (algebraMap F E).toMonoidHom γ) hγE
      (residueMap E z) =
    residualAddChar F ψF γ hγ
      (residueTrace (ResidueField F) (ResidueField E) (residueMap E z))
  rw [residue_trace F E hunr, ← reduce_mk E z,
    ← reduce_mk F (integralTrace F E z),
    residualAddChar_integral_lift E ψE _ hγE (z : E) hzE,
    residualAddChar_integral_lift F ψF γ hγ (integralTrace F E z : F) hzF,
    hψ]
  apply congrArg Units.val
  apply congrArg ψF.character
  change trace F E ((z : E) / algebraMap F E (γ : F)) =
    (integralTrace F E z : F) / (γ : F)
  rw [coe_integralTrace, div_eq_mul_inv, ← map_inv₀, mul_comm,
    ← Algebra.smul_def, map_smul, Algebra.smul_def, div_eq_mul_inv]
  simp [mul_comm]

/-- On the ramified tame edge the common denominator is admissible with
the full different shift, and reduction of trace on base lifts multiplies
by the degree. This is the source of the factor `χ₀(ell)` in `O:F:tame`. -/
theorem tame_residualAddChar [PrimeCyclicExtension F E]
    (hram : ramificationIndex F E ≠ 1) (htame : IsTamelyRamified F E)
    (ψF : LocalAddCharData F) (ψE : LocalAddCharData E)
    (hψ : ψE.character = tracePullbackAddChar F E ψF.character)
    (γ : Fˣ) (hγ : ord F (γ : F) = ((ψF.conductor + 1 : ℤ) : WithTop ℤ)) :
    ∃ hγE : ord E (algebraMap F E (γ : F)) =
        ((ψE.conductor + 1 : ℤ) : WithTop ℤ),
      ∀ x : ResidueField F,
        residualAddChar E ψE (Units.map (algebraMap F E).toMonoidHom γ) hγE
            (extensionResidueMap F E x) =
          (residualAddChar F ψF γ hγ).mulShift
            (Module.finrank F E : ResidueField F) x := by
  let P := primeCyclicPreparation F E hram
  have ht := P.isLowerBreak_zero_of_isTamelyRamified F E htame
  have hn := ψF.conductor_compTrace_eq_cyclicPrime F E ht P.hres P.piK
    P.hpiK P.hgen ψE hψ
  have hγE : ord E (algebraMap F E (γ : F)) =
      ((ψE.conductor + 1 : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, P.ramificationIndex_eq_degree, hγ, ← WithTop.coe_nsmul]
    congr 1
    rw [hn]
    have hd := Module.finrank_pos (R := F) (M := E)
    simp only [zero_add, mul_one, Nat.cast_sub (by omega : 1 ≤ Module.finrank F E),
      Nat.cast_one, nsmul_eq_mul]
    ring
  refine ⟨hγE, ?_⟩
  intro x
  obtain ⟨a, rfl⟩ := residueMap_surjective F x
  let aE := algebraMap (ringOfIntegers F) (ringOfIntegers E) a
  let b : ringOfIntegers F := (Module.finrank F E : ringOfIntegers F) * a
  have ha : (aE : E) = algebraMap F E (a : F) := Valuation.HasExtension.val_algebraMap a
  have haE : (aE : E) ∈ lattice E 0 := (mem_lattice_zero_iff E).2 aE.property
  have hb : (b : F) ∈ lattice F 0 := (mem_lattice_zero_iff F).2 b.property
  have hredE : extensionResidueMap F E (residueMap F a) = residueMap E aE := rfl
  have hredF : (Module.finrank F E : ResidueField F) * residueMap F a =
      residueMap F b := by simp [b]
  change residualAddChar E ψE _ hγE _ =
    residualAddChar F ψF γ hγ ((Module.finrank F E : ResidueField F) * residueMap F a)
  rw [hredE, hredF, ← reduce_mk E aE, ← reduce_mk F b,
    residualAddChar_integral_lift E ψE _ hγE (aE : E) haE,
    residualAddChar_integral_lift F ψF γ hγ (b : F) hb, hψ]
  apply congrArg Units.val
  apply congrArg ψF.character
  change trace F E ((aE : E) / algebraMap F E (γ : F)) = (b : F) / (γ : F)
  rw [ha, ← map_div₀, trace_algebraMap]
  change Module.finrank F E • ((a : F) / (γ : F)) =
    ((Module.finrank F E : F) * (a : F)) / (γ : F)
  simp only [nsmul_eq_mul]
  ring

end ResidualAdditive

section ResidualFrobenius

variable (F U : Type) [Field F] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U]
  [PrimeCyclicExtension F U]

local instance : Fintype (ResidueField F) := residueFieldFintype F
local instance : Fintype (ResidueField U) := residueFieldFintype U

/-- Non-descent of an actual conductor-one character on the unramified
field forces a nontrivial residue Frobenius quotient. If that quotient
were trivial, every residue automorphism would fix the character; a base
uniformizer then gives invariance on all field units, contradicting cyclic
norm descent. -/
theorem unramified_residual_frobenius_nontrivial
    (hunr : ramificationIndex F U = 1)
    (χ : LocalQuasiCharData U) (hχ : χ.conductor = 1)
    (hprimitive : ¬ ∃ lam : ContinuousQuasiChar F,
      normQuasiChar F U lam = χ.character) :
    ∃ x : (ResidueField U)ˣ,
      residualMulChar U χ (x : ResidueField U) ^ (Fintype.card (ResidueField F) - 1) ≠ 1 := by
  classical
  by_contra! htriv
  let q := Fintype.card (ResidueField F)
  have hqpos : 0 < q := Fintype.card_pos
  have hpow (x : (ResidueField U)ˣ) (i : ℕ) :
      residualMulChar U χ (x : ResidueField U) ^ (q ^ i) =
        residualMulChar U χ (x : ResidueField U) := by
    have hq : residualMulChar U χ (x : ResidueField U) ^ q =
        residualMulChar U χ (x : ResidueField U) := by
      rw [show q = (q - 1) + 1 by omega, pow_succ, htriv x, one_mul]
    induction i with
    | zero => simp
    | succ i hi => rw [pow_succ, pow_mul, hi, hq]
  have hres (σ : Gal(ResidueField U / ResidueField F)) (x : (ResidueField U)ˣ) :
      residualMulChar U χ (σ (x : ResidueField U)) =
        residualMulChar U χ (x : ResidueField U) := by
    obtain ⟨i, rfl⟩ :=
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
        (ResidueField F) (ResidueField U)).2 σ
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
      map_pow]
    exact hpow x i.val
  have hunit (σ : Gal(U/F)) (u : unitGroup U) :
      χ.character (Units.map σ.toMonoidHom (u : Uˣ)) = χ.character (u : Uˣ) := by
    let v : unitGroup U := ⟨Units.map σ.toMonoidHom (u : Uˣ), by
      rw [mem_unitGroup_iff_ord_eq_zero]
      change ord U (σ ((u : Uˣ) : U)) = 0
      rw [ord_galoisConjugate]
      exact (mem_unitGroup_iff_ord_eq_zero U (u : Uˣ)).1 u.property⟩
    have hv : ((residueUnits U v : (ResidueField U)ˣ) : ResidueField U) =
        Ramification.residueAction (F := F) (K := U) σ
          ((residueUnits U u : (ResidueField U)ˣ) : ResidueField U) := by
      rw [residueUnits_coe, residueUnits_coe, Ramification.residueAction_apply_residue]
      rfl
    apply Units.ext
    change (χ.character (v : Uˣ) : ℂ) = (χ.character (u : Uˣ) : ℂ)
    rw [← residualMulChar_residueUnits U χ (by omega) v,
      ← residualMulChar_residueUnits U χ (by omega) u, hv]
    exact hres _ _
  apply hprimitive
  apply Local.invariantCharacter_descends F U χ.character
  intro σ x
  obtain ⟨p, hp⟩ := exists_ord_eq F 1
  let π : Fˣ := Units.mk0 p ((ord_ne_top_iff F).1 (hp.trans_ne WithTop.coe_ne_top))
  let πU : Uˣ := Units.map (algebraMap F U).toMonoidHom π
  have hπ : ord U (πU : U) = 1 := by
    change ord U (algebraMap F U p) = 1
    rw [ord_algebraMap, hunr, one_nsmul, hp]
    rfl
  have hπfix : Units.map σ.toMonoidHom πU = πU := by
    apply Units.ext
    change σ (algebraMap F U p) = algebraMap F U p
    exact σ.commutes p
  let n := localUnitOrder U x
  have horder : ord U ((x / πU ^ n : Uˣ) : U) = 0 := by
    rw [Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val,
      ord_div, ord_zpow, hπ, ← coe_localUnitOrder]
    change (n : WithTop ℤ) - n • (1 : WithTop ℤ) = 0
    have hn : n • (1 : WithTop ℤ) = (n : WithTop ℤ) := by
      cases n with
      | ofNat a => simp
      | negSucc a => rw [negSucc_zsmul]; norm_num [Int.negSucc_eq]
    rw [hn]
    simp
  let u : unitGroup U := ⟨x / πU ^ n, (mem_unitGroup_iff_ord_eq_zero U _).2 horder⟩
  have hx : x = (u : Uˣ) * πU ^ n := by simp [u]
  rw [hx, map_mul, map_zpow, hπfix, map_mul, map_mul, hunit σ u]

end ResidualFrobenius

section ResidualRestriction

variable (F E : Type) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]

private def lowerResidualMulChar (χ : LocalQuasiCharData E) :
    FiniteMulChar (ResidueField F) where
  toFun x := residualMulChar E χ (extensionResidueMap F E x)
  map_one' := by simp
  map_mul' x y := by simp
  map_nonunit' x hx := by
    have hx0 : x = 0 := by simpa [isUnit_iff_ne_zero] using hx
    rw [hx0, map_zero, MulChar.map_zero]

omit [Module.Finite F E] in
private theorem lowerResidualMulChar_unit
    (χ : LocalQuasiCharData E) (hχ : χ.conductor = 1) (u : unitGroup F) :
    lowerResidualMulChar F E χ
        ((residueUnits F u : (ResidueField F)ˣ) : ResidueField F) =
      (χ.character (Units.map (algebraMap F E).toMonoidHom (u : Fˣ)) : ℂ) := by
  let v : unitGroup E := ⟨Units.map (algebraMap F E).toMonoidHom (u : Fˣ), by
    rw [mem_unitGroup_iff_ord_eq_zero]
    change ord E (algebraMap F E ((u : Fˣ) : F)) = 0
    rw [ord_algebraMap, (mem_unitGroup_iff_ord_eq_zero F (u : Fˣ)).1 u.property]
    simp⟩
  have hv : ((residueUnits E v : (ResidueField E)ˣ) : ResidueField E) =
      extensionResidueMap F E ((residueUnits F u : (ResidueField F)ˣ) : ResidueField F) := by
    rw [residueUnits_coe, residueUnits_coe]
    rfl
  change residualMulChar E χ _ = _
  rw [← hv, residualMulChar_residueUnits E χ (by omega)]

end ResidualRestriction

section ResidualCompatibility

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

local instance : Fintype (ResidueField F) := residueFieldFintype F

/-- The local compatibility identity descends to the exact multiplicative
residue identity in `O:F:tame`. Norm base change is applied to the actual
linearly disjoint intermediate fields. -/
private theorem conductorOne_residual_compatibility
    {ell : ℕ} (hell : ell.Prime)
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod ell) × Multiplicative (ZMod ell))))
    (U E : IntermediateField F K)
    (hU : Module.finrank F U = ell) (hE : Module.finrank F E = ell)
    (hne : U ≠ E) (hunr : ramificationIndex F U = 1)
    (χU : LocalQuasiCharData U) (χE : LocalQuasiCharData E)
    (hχE : χE.conductor = 1)
    (hcomp : normQuasiChar U K χU.character = normQuasiChar E K χE.character) :
    residualMulChar U χU ^ ell =
      normMulChar (ResidueField F) (ResidueField U) (lowerResidualMulChar F E χE) := by
  have dataU := Basic.intermediateField_tower_compatible hell hG U hU
  have dataE := Basic.intermediateField_tower_compatible hell hG E hE
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F U
    dataU.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E
    dataE.2.2.2.2.2.2.2.2.2.2.2.1
  have hinf : U ⊓ E = ⊥ := by
    have hd : Module.finrank F ↥(U ⊓ E) ∣ ell :=
      hU ▸ IntermediateField.finrank_dvd_of_le_right (show U ⊓ E ≤ U from inf_le_left)
    rcases (Nat.dvd_prime hell).1 hd with h | h
    · exact IntermediateField.finrank_eq_one_iff.mp h
    · have heq : U ⊓ E = U :=
        IntermediateField.eq_of_le_of_finrank_eq inf_le_left (h.trans hU.symm)
      have hle : U ≤ E := by rw [← heq]; exact inf_le_right
      exact (hne (IntermediateField.eq_of_le_of_finrank_eq hle (hU.trans hE.symm))).elim
  have hd := IntermediateField.LinearDisjoint.of_inf_eq_bot hinf
  have hUK := dataU.2.2.2.2.2.2.2.2.2.2.1
  have hsup : U ⊔ E = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [hd.finrank_sup, IntermediateField.finrank_top', hU, hE]
    exact dataU.2.2.2.2.2.2.2.2.1.symm
  have hcross (x : Uˣ) : χU.character x ^ ell =
      χE.character (Units.map (algebraMap F E).toMonoidHom (normUnits F U x)) := by
    have hnormU : normUnits U K (Units.map (algebraMap U K).toMonoidHom x) = x ^ ell := by
      apply Units.ext
      change Algebra.norm U (algebraMap U K (x : U)) = (x : U) ^ ell
      rw [Algebra.norm_algebraMap, hUK]
    have hnormE : normUnits E K (Units.map (algebraMap U K).toMonoidHom x) =
        Units.map (algebraMap F E).toMonoidHom (normUnits F U x) := by
      apply Units.ext
      exact hd.symm.norm_algebraMap (by rwa [sup_comm]) (x : U)
    have hx := DFunLike.congr_fun hcomp (Units.map (algebraMap U K).toMonoidHom x)
    change χU.character (normUnits U K _) = χE.character (normUnits E K _) at hx
    rwa [hnormU, hnormE, map_pow] at hx
  apply MulChar.ext
  intro x
  let u : unitGroup U := teichmullerLocalUnits U x
  let v := unramifiedNormUnitGroup F U u
  have hv : residueUnits F v = Units.map (residueNorm (ResidueField F) (ResidueField U)) x := by
    rw [unramified_residue_norm_units F U hunr, residueUnits_teichmullerLocalUnits]
  rw [MulChar.pow_apply_coe, residualMulChar_apply_unit, normMulChar_apply]
  have hl := lowerResidualMulChar_unit F E χE hχE v
  rw [hv] at hl
  change lowerResidualMulChar F E χE (residueNorm (ResidueField F) (ResidueField U)
    (x : ResidueField U)) = _ at hl
  change (χU.character (u : Uˣ) : ℂ) ^ ell = _
  rw [hl, ← Units.val_pow_eq_pow_val, hcross]
  rfl

end ResidualCompatibility

section LowerProducts

variable (F E : Type) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

local instance : Finite (NormCharacter F E) := primeCyclicNormCharacter_finite F E
local instance : Fintype (ResidueField F) := residueFieldFintype F

private def normResidualCharacterHom :
    NormCharacter F E →* FiniteMulChar (ResidueField F) where
  toFun ν := residualMulChar F (canonicalLocalQuasiCharData F ν.1)
  map_one' := by
    apply MulChar.ext
    intro u
    rw [residualMulChar_apply_unit, MulChar.one_apply u.isUnit]
    rfl
  map_mul' ν η := by
    apply MulChar.ext
    intro u
    rw [MulChar.mul_apply, residualMulChar_apply_unit,
      residualMulChar_apply_unit, residualMulChar_apply_unit]
    rfl

private theorem normResidualCharacterHom_injective
    (hram : ramificationIndex F E ≠ 1) (htame : IsTamelyRamified F E) :
    Function.Injective (normResidualCharacterHom F E) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro ν hν
  by_contra hne
  let P := primeCyclicPreparation F E hram
  have hc := tameNormCharacter_conductor F E
    (P.isLowerBreak_zero_of_isTamelyRamified F E htame)
    P.hres P.piK P.hpiK P.hgen ν hne
  exact residualMulChar_ne_one F (canonicalLocalQuasiCharData F ν.1)
    ((canonicalLocalQuasiCharData F ν.1).isConductor.unique hc) hν

/-- The full unramified lower correction product evaluated at any element
of order `n(ψ)`. This includes the trivial norm character, and makes no
nonnegativity assumption on the additive conductor. -/
theorem unramified_lowerProduct
    (hunr : ramificationIndex F E = 1) (ψ : LocalAddCharData F)
    (γ : Fˣ) (hγ : ord F (γ : F) = (ψ.conductor : WithTop ℤ)) :
    (normCharacterFinset F E).prod (fun ν => localConstant F ν.1 ψ.character) =
      (Characters.normCharacterProduct F E γ : ℂ) := by
  rw [Characters.normCharacterProduct_apply, Units.coe_prod]
  apply Finset.prod_congr rfl
  intro ν _
  let χ := continuousQuasiChar_toData F ν.1 0
    (unramifiedNormCharacter_conductor F E hunr ν)
  let Γ : AdmissibleGamma F χ ψ := ⟨γ, by simpa [χ] using hγ⟩
  exact (localConstant_isDeltaFinite F χ ψ Γ).trans
    (deltaFinite_conductor_zero F χ rfl ψ Γ)

open Classical in
/-- The complete ramified tame correction product in the conductor-one
calculation (paper lines 1024–1031). The identity character is evaluated as
one before the remaining factors are expanded. In degree two this retains
the quadratic character value at `γ` and its full residual Gauss phase. -/
theorem tame_lowerProduct
    (hram : ramificationIndex F E ≠ 1) (htame : IsTamelyRamified F E)
    (ψ : LocalAddCharData F) (γ : Fˣ)
    (hγ : ord F (γ : F) = ((ψ.conductor + 1 : ℤ) : WithTop ℤ)) :
    (normCharacterFinset F E).prod (fun ν => localConstant F ν.1 ψ.character) =
      (-1 : ℂ) ^ (Module.finrank F E - 1) *
        (Characters.normCharacterProduct F E γ : ℂ) *
        ((normCharacterFinset F E).erase 1).prod (fun ν =>
          phase (langlandsGaussSum
            (residualMulChar F (canonicalLocalQuasiCharData F ν.1))
            (residualAddChar F ψ γ hγ))) := by
  classical
  letI := normCharacterFintype F E
  let S := normCharacterFinset F E
  have hone : (1 : NormCharacter F E) ∈ S := Finset.mem_univ _
  let P := primeCyclicPreparation F E hram
  have ht := P.isLowerBreak_zero_of_isTamelyRamified F E htame
  have hcard : (S.erase 1).card = Module.finrank F E - 1 := by
    rw [Finset.card_erase_of_mem hone]
    change Fintype.card (NormCharacter F E) - 1 = _
    rw [← Nat.card_eq_fintype_card,
      ramifiedNormCharacter_card F E P.ht P.hres P.piK P.hpiK P.hgen]
  have htriv : localConstant F (1 : ContinuousQuasiChar F) ψ.character = 1 := by
    let Γ := Classical.choice (AdmissibleGamma.exists_admissible
      (F := F) (χ := trivialQuasiCharData F) (ψ := ψ))
    exact (localConstant_isDeltaFinite F (trivialQuasiCharData F) ψ Γ).trans
      (delta_trivial_character F ψ Γ)
  have hterm (ν : NormCharacter F E) (hν : ν ∈ S.erase 1) :
      localConstant F ν.1 ψ.character = -(ν.1 γ : ℂ) *
        phase (langlandsGaussSum
          (residualMulChar F (canonicalLocalQuasiCharData F ν.1))
          (residualAddChar F ψ γ hγ)) := by
    have hc := tameNormCharacter_conductor F E ht P.hres P.piK P.hpiK P.hgen
      ν (Finset.mem_erase.mp hν).1
    exact localConstant_conductorOne F (canonicalLocalQuasiCharData F ν.1)
      ((canonicalLocalQuasiCharData F ν.1).isConductor.unique hc) ψ γ hγ
  have heval : (S.erase 1).prod (fun ν => (ν.1 γ : ℂ)) =
      (Characters.normCharacterProduct F E γ : ℂ) := by
    rw [Characters.normCharacterProduct_apply, Units.coe_prod]
    exact Finset.prod_erase (s := S) (f := fun ν => (ν.1 γ : ℂ)) (by simp)
  calc
    S.prod (fun ν => localConstant F ν.1 ψ.character) =
        (S.erase 1).prod (fun ν => localConstant F ν.1 ψ.character) := by
      rw [← Finset.mul_prod_erase S _ hone]
      change localConstant F 1 ψ.character * _ = _
      rw [htriv, one_mul]
    _ = (S.erase 1).prod (fun ν => -(ν.1 γ : ℂ) *
        phase (langlandsGaussSum
          (residualMulChar F (canonicalLocalQuasiCharData F ν.1))
          (residualAddChar F ψ γ hγ))) := Finset.prod_congr rfl hterm
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_neg, hcard, heval]

/-- Construct the order-`[E:F]` residue character used in the paper and
reindex all the nontrivial lower Gauss factors by its powers. The generator
comes from the actual lower norm-character group; it is not supplied as
auxiliary data. -/
theorem tame_lowerProduct_generator
    (hram : ramificationIndex F E ≠ 1) (htame : IsTamelyRamified F E)
    (ψ : LocalAddCharData F) (γ : Fˣ)
    (hγ : ord F (γ : F) = ((ψ.conductor + 1 : ℤ) : WithTop ℤ)) :
    ∃ μ : FiniteMulChar (ResidueField F),
      orderOf μ = Module.finrank F E ∧
      Module.finrank F E ∣ Fintype.card (ResidueField F) - 1 ∧
      (normCharacterFinset F E).prod (fun ν => localConstant F ν.1 ψ.character) =
        (-1 : ℂ) ^ (Module.finrank F E - 1) *
          (Characters.normCharacterProduct F E γ : ℂ) *
          ∏ j ∈ Finset.Icc 1 (Module.finrank F E - 1),
            phase (langlandsGaussSum (μ ^ j) (residualAddChar F ψ γ hγ)) := by
  classical
  letI := normCharacterFintype F E
  let P := primeCyclicPreparation F E hram
  letI := ramifiedNormCharacter_isCyclic F E P.ht P.hres P.piK P.hpiK P.hgen
  obtain ⟨ν, hνtop⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic (NormCharacter F E))
  have hνorder : orderOf ν = Module.finrank F E :=
    (orderOf_eq_card_of_zpowers_eq_top hνtop).trans
      (ramifiedNormCharacter_card F E P.ht P.hres P.piK P.hpiK P.hgen)
  let μ := normResidualCharacterHom F E ν
  have hμ : orderOf μ = Module.finrank F E :=
    (orderOf_injective (normResidualCharacterHom F E)
      (normResidualCharacterHom_injective F E hram htame) ν).trans hνorder
  refine ⟨μ, hμ, hμ ▸ μ.orderOf_dvd_card_sub_one, ?_⟩
  rw [tame_lowerProduct F E hram htame ψ γ hγ]
  congr 1
  symm
  apply Finset.prod_bij (fun j _ => ν ^ j)
  · intro j hj
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    have hjb := Finset.mem_Icc.mp hj
    exact pow_ne_one_of_lt_orderOf (by omega) (by omega)
  · intro i hi j hj hij
    apply pow_injOn_Iio_orderOf (x := ν) _ _ hij
    · have := Finset.mem_Icc.mp hi; change i < orderOf ν; omega
    · have := Finset.mem_Icc.mp hj; change j < orderOf ν; omega
  · intro η hη
    have hmem : η ∈ Subgroup.zpowers ν := hνtop ▸ Subgroup.mem_top η
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp
      (mem_zpowers_iff_mem_range_orderOf.mp hmem)
    have hjlt := Finset.mem_range.mp hj
    have hjpos : 0 < j := by
      by_contra h
      have hz : j = 0 := by omega
      exact (Finset.mem_erase.mp hη).1 (by simpa [hz] using heq.symm)
    exact ⟨j, Finset.mem_Icc.mpr ⟨hjpos, by omega⟩, heq⟩
  · intro j _
    change phase (langlandsGaussSum (μ ^ j) _) =
      phase (langlandsGaussSum (normResidualCharacterHom F E (ν ^ j)) _)
    rw [map_pow]

open Polynomial in
/-- Evaluation at a uniformizer gives the exact unramified correction
sign. The roots-of-unity equivalence includes the trivial norm character. -/
theorem unramified_normCharacterProduct_uniformizer
    (hunr : ramificationIndex F E = 1)
    (π : Fˣ) (hπ : (ValuativeRel.valuation F).IsUniformizer (π : F)) :
    (Characters.normCharacterProduct F E π : ℂ) =
      (-1 : ℂ) ^ (Module.finrank F E - 1) := by
  classical
  letI := normCharacterFintype F E
  let n := Nat.card (NormQuotient F E)
  have hn : n = Module.finrank F E := unramifiedNormQuotient_natCard F E hunr
  have hnpos : 0 < n := hn ▸ Module.finrank_pos
  letI : NeZero n := ⟨hnpos.ne'⟩
  letI : Fintype (rootsOfUnity n ℂ) := Fintype.ofFinite _
  letI : Fintype {x : ℂ // x ∈ nthRoots n (1 : ℂ)} := Fintype.ofFinite _
  have hroot : (nthRoots n (1 : ℂ)).prod = (-1 : ℂ) ^ (n - 1) := by
    have hc : (-1 : ℂ) = (-1 : ℂ) ^ n * (nthRoots n (1 : ℂ)).prod := by
      have hp := (IsAlgClosed.splits (X ^ n - C (1 : ℂ))).coeff_zero_eq_prod_roots_of_monic
        (monic_X_pow_sub_C (1 : ℂ) hnpos.ne')
      rw [natDegree_X_pow_sub_C] at hp
      rw [coeff_sub, coeff_X_pow, coeff_C, if_neg (Ne.symm hnpos.ne'),
        if_pos rfl, zero_sub] at hp
      exact hp
    have hs : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
      rw [← pow_add, show n + n = 2 * n by omega, pow_mul]
      simp
    calc
      _ = ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) * (nthRoots n (1 : ℂ)).prod := by rw [hs, one_mul]
      _ = (-1 : ℂ) ^ n * (-1 : ℂ) := by rw [mul_assoc, ← hc]
      _ = (-1 : ℂ) ^ (n - 1) := by
        rw [← pow_succ, show n + 1 = (n - 1) + 2 by omega, pow_add]
        simp
  rw [Characters.normCharacterProduct_apply, Units.coe_prod]
  change (∏ ν : NormCharacter F E, (ν.1 π : ℂ)) = _
  calc
    _ = ∏ z : rootsOfUnity n ℂ, ((z : ℂˣ) : ℂ) := by
      exact Fintype.prod_equiv
        (unramifiedNormCharacterEvaluationEquivCard F E hunr π hπ).toEquiv _ _
        (fun ν => (unramifiedNormCharacterEvaluationEquivCard_coe F E hunr π hπ ν).symm)
    _ = ∏ x : {x : ℂ // x ∈ nthRoots n (1 : ℂ)}, (x : ℂ) :=
      Fintype.prod_equiv (rootsOfUnityEquivNthRoots ℂ n) _ _ (fun _ => rfl)
    _ = ∏ x ∈ nthRootsFinset n (1 : ℂ), x :=
      (Finset.prod_subtype (nthRootsFinset n (1 : ℂ))
        (fun x => by simp [nthRootsFinset_def]) (fun x : ℂ => x)).symm
    _ = (nthRoots n (1 : ℂ)).prod := by
      rw [nthRootsFinset_def, Finset.prod_eq_multiset_prod]
      simp only [Multiset.map_id']
      rw [Multiset.toFinset_val,
        (Complex.isPrimitiveRoot_exp n hnpos.ne').nthRoots_one_nodup.dedup]
    _ = _ := by rw [hroot, hn]

/-- The sign cancellation needed at conductor one, expressed without
truncating the additive conductor or choosing a nonnegative exponent. -/
theorem unramified_lowerProduct_conductorOne
    (hunr : ramificationIndex F E = 1) (ψ : LocalAddCharData F)
    (γ : Fˣ) (hγ : ord F (γ : F) = ((ψ.conductor + 1 : ℤ) : WithTop ℤ)) :
    (Characters.normCharacterProduct F E γ : ℂ) =
      (-1 : ℂ) ^ (Module.finrank F E - 1) *
        (normCharacterFinset F E).prod (fun ν => localConstant F ν.1 ψ.character) := by
  obtain ⟨p, hp⟩ := exists_ord_eq F 1
  let π : Fˣ := Units.mk0 p ((ord_ne_top_iff F).1 (hp.trans_ne WithTop.coe_ne_top))
  have hπ : (ValuativeRel.valuation F).IsUniformizer (π : F) :=
    (ord_eq_one_iff_isUniformizer F (π : F)).1 hp
  have hquot : ord F ((γ / π : Fˣ) : F) = (ψ.conductor : WithTop ℤ) := by
    rw [Units.val_div_eq_div_val, ord_div, hγ, ord_uniformizer F hπ]
    norm_cast
    omega
  rw [unramified_lowerProduct F E hunr ψ (γ / π) hquot,
    map_div, Units.val_div_eq_div_val,
    ← unramified_normCharacterProduct_uniformizer F E hunr π hπ]
  exact (mul_div_cancel₀ _ (Units.ne_zero (Characters.normCharacterProduct F E π))).symm

end LowerProducts

section ConductorOneInputs

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

local instance : Fintype (ResidueField F) := residueFieldFintype F
local instance (L : IntermediateField F K) : Fintype (ResidueField L) := residueFieldFintype L

/-- The finite phase identity with all multiplicative inputs derived from
the actual conductor-one compatible pair. In particular the primitivity
condition of `finiteComparison` is a conclusion of local non-descent, and
the generator comes from the complete lower norm-character group. -/
theorem conductorOne_finite_phase
    {ell : ℕ} (hell : ell.Prime)
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod ell) × Multiplicative (ZMod ell))))
    (U E : IntermediateField F K)
    (hU : Module.finrank F U = ell) (hE : Module.finrank F E = ell)
    (hne : U ≠ E) (hunr : ramificationIndex F U = 1)
    (hram : ramificationIndex F E ≠ 1) (htame : IsTamelyRamified F E)
    (χU : LocalQuasiCharData U) (χE : LocalQuasiCharData E)
    (hχU : χU.conductor = 1) (hχE : χE.conductor = 1)
    (hcomp : normQuasiChar U K χU.character = normQuasiChar E K χE.character)
    (hprimitive : ¬ ∃ lam : ContinuousQuasiChar F,
      normQuasiChar F K lam = normQuasiChar U K χU.character)
    (ψ : LocalAddCharData F) (γ : Fˣ)
    (hγ : ord F (γ : F) = ((ψ.conductor + 1 : ℤ) : WithTop ℤ)) :
    letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E
      (Basic.intermediateField_tower_compatible hell hG E hE).2.2.2.2.2.2.2.2.2.2.2.1
    letI := primeCyclicNormCharacter_finite F E
    ∃ μ : FiniteMulChar (ResidueField F),
      orderOf μ = ell ∧
      phase (langlandsGaussSum (residualMulChar U χU)
        (traceAddChar (ResidueField F) (ResidueField U) (residualAddChar F ψ γ hγ))) =
        lowerResidualMulChar F E χE (ell : ResidueField F) *
          phase (langlandsGaussSum (lowerResidualMulChar F E χE) (residualAddChar F ψ γ hγ)) *
          ∏ j ∈ Finset.Icc 1 (ell - 1),
            phase (langlandsGaussSum (μ ^ j) (residualAddChar F ψ γ hγ)) ∧
      (normCharacterFinset F E).prod (fun ν => localConstant F ν.1 ψ.character) =
        (-1 : ℂ) ^ (ell - 1) * (Characters.normCharacterProduct F E γ : ℂ) *
          ∏ j ∈ Finset.Icc 1 (ell - 1),
            phase (langlandsGaussSum (μ ^ j) (residualAddChar F ψ γ hγ)) := by
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F U
    (Basic.intermediateField_tower_compatible hell hG U hU).2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E
    (Basic.intermediateField_tower_compatible hell hG E hE).2.2.2.2.2.2.2.2.2.2.2.1
  letI := primeCyclicNormCharacter_finite F E
  obtain ⟨μ, hμ, hdiv, hprod⟩ := tame_lowerProduct_generator F E hram htame ψ γ hγ
  rw [hE] at hμ hdiv hprod
  have hc := conductorOne_residual_compatibility hell hG U E hU hE hne hunr χU χE hχE hcomp
  have hprimU : ¬ ∃ lam : ContinuousQuasiChar F,
      normQuasiChar F U lam = χU.character := by
    rintro ⟨lam, hlam⟩
    apply hprimitive
    refine ⟨lam, ?_⟩
    rw [← hlam]
    apply ContinuousMonoidHom.ext
    intro x
    change lam (normUnits F K x) = lam (normUnits F U (normUnits U K x))
    congr 1
    apply Units.ext
    exact (Basic.norm_tower (F := F) (L := U) (x := (x : K))).symm
  have hFrob := unramified_residual_frobenius_nontrivial F U hunr χU hχU hprimU
  have hprim := finiteComparison_primitive_of_frobenius ell hdiv
    (residualMulChar U χU) (lowerResidualMulChar F E χE) hc hFrob
  refine ⟨μ, hμ, ?_, hprod⟩
  exact finiteComparison_phase ell hell ((unramified_residue_degree F U hunr).trans hU)
    hdiv (residualMulChar U χU) (lowerResidualMulChar F E χE) μ hμ hc hprim
    (residualAddChar F ψ γ hγ) (residualAddChar_ne_one F ψ γ hγ)

/-- The conductor-one local equality, including both complete lower
products and the degree-two sign. The residual characters and all finite
comparison hypotheses are derived from the local pair. -/
theorem comparison_of_conductor_one
    {ell : ℕ} (hell : ell.Prime)
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod ell) × Multiplicative (ZMod ell))))
    (U E : IntermediateField F K)
    (hU : Module.finrank F U = ell) (hE : Module.finrank F E = ell)
    (hne : Ramification.intermediateNormRange U ≠ Ramification.intermediateNormRange E)
    (hunr : ramificationIndex F U = 1)
    (hram : ramificationIndex F E ≠ 1) (htame : IsTamelyRamified F E)
    (χU : LocalQuasiCharData U) (χE : LocalQuasiCharData E)
    (hχU : χU.conductor = 1) (hχE : χE.conductor = 1)
    (hcomp : normQuasiChar U K χU.character = normQuasiChar E K χE.character)
    (hprimitive : ¬ ∃ lam : ContinuousQuasiChar F,
      normQuasiChar F K lam = normQuasiChar U K χU.character)
    (ψ : LocalAddCharData F) :
    Characters.inducingFactor hell hG ψ.character U hU χU.character =
      Characters.inducingFactor hell hG ψ.character E hE χE.character := by
  classical
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F U
    (Basic.intermediateField_tower_compatible hell hG U hU).2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E
    (Basic.intermediateField_tower_compatible hell hG E hE).2.2.2.2.2.2.2.2.2.2.2.1
  letI := primeCyclicNormCharacter_finite F U
  letI := primeCyclicNormCharacter_finite F E
  obtain ⟨c, hc⟩ := exists_ord_eq F (ψ.conductor + 1)
  let γ : Fˣ := Units.mk0 c ((ord_ne_top_iff F).1 (hc.trans_ne WithTop.coe_ne_top))
  have hγ : ord F (γ : F) = ((ψ.conductor + 1 : ℤ) : WithTop ℤ) := hc
  let ψU := canonicalLocalAddCharData U (tracePullbackAddChar F U ψ.character)
    (Basic.tracePullbackAddChar_ne_one F U ψ.character ψ.character_ne_one)
  let ψE := canonicalLocalAddCharData E (tracePullbackAddChar F E ψ.character)
    (Basic.tracePullbackAddChar_ne_one F E ψ.character ψ.character_ne_one)
  obtain ⟨hγU, hAU⟩ := unramified_residualAddChar F U hunr ψ ψU rfl γ hγ
  obtain ⟨hγE, hAE⟩ := tame_residualAddChar F E hram htame ψ ψE rfl γ hγ
  rw [hE] at hAE
  have hδU := localConstant_conductorOne U χU hχU ψU
    (Units.map (algebraMap F U).toMonoidHom γ) hγU
  have hδE := localConstant_conductorOne E χE hχE ψE
    (Units.map (algebraMap F E).toMonoidHom γ) hγE
  rw [hAU] at hδU
  obtain ⟨μ, hμ, hphase, hprod⟩ := conductorOne_finite_phase hell hG U E hU hE
    (fun h => hne (congrArg Ramification.intermediateNormRange h)) hunr hram htame
    χU χE hχU hχE hcomp hprimitive ψ γ hγ
  let χ₀ := lowerResidualMulChar F E χE
  let ψ₀ := residualAddChar F ψ γ hγ
  letI : Module.Free (ResidueField F) (ResidueField E) :=
    Module.Free.of_divisionRing (K := ResidueField F) (V := ResidueField E)
  let e : ResidueField F ≃+* ResidueField E := RingEquiv.ofBijective
    (extensionResidueMap F E) ((Algebra.finrank_eq_one_iff_bijective_algebraMap
      (F := ResidueField F) (E := ResidueField E)).mp (by
      rw [← residueDegree_eq_finrank_residueField F E]
      exact (primeCyclicPreparation F E hram).hres))
  have hGauss : langlandsGaussSum (residualMulChar E χE)
      (residualAddChar E ψE (Units.map (algebraMap F E).toMonoidHom γ) hγE) =
        langlandsGaussSum χ₀ (ψ₀.mulShift (ell : ResidueField F)) := by
    rw [langlandsGaussSum, langlandsGaussSum]
    congr 1
    rw [gaussSum, gaussSum]
    rw [← e.toEquiv.sum_comp]
    apply Finset.sum_congr rfl
    intro x _
    rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv']
    change (χ₀ x)⁻¹ * residualAddChar E ψE
      (Units.map (algebraMap F E).toMonoidHom γ) hγE (extensionResidueMap F E x) = _
    rw [hAE]
  have hdiv : ell ∣ Fintype.card (ResidueField F) - 1 := hμ ▸ μ.orderOf_dvd_card_sub_one
  have hψ₀ : ψ₀ ≠ 1 := residualAddChar_ne_one F ψ γ hγ
  have hden := finiteComparisonDenominator_ne_zero ell hdiv χ₀ μ ψ₀ hψ₀
  have hellval : χ₀ (ell : ResidueField F) ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hden).1).1
  have hellk : (ell : ResidueField F) ≠ 0 := by
    intro h
    exact hellval (by rw [h, MulChar.map_zero])
  let a : (ResidueField F)ˣ := Units.mk0 (ell : ResidueField F) hellk
  have ha : ‖χ₀ (ell : ResidueField F)‖ = 1 :=
    Complex.norm_eq_one_of_mem_rootsOfUnity (χ₀.apply_mem_rootsOfUnity a)
  have hphaseE : phase (langlandsGaussSum (residualMulChar E χE)
      (residualAddChar E ψE (Units.map (algebraMap F E).toMonoidHom γ) hγE)) =
        χ₀ (ell : ResidueField F) * phase (langlandsGaussSum χ₀ ψ₀) := by
    rw [hGauss]
    change phase (langlandsGaussSum χ₀ (ψ₀.mulShift (a : ResidueField F))) = _
    rw [langlandsGaussSum_mulShift_unit]
    exact phase_mul_of_norm_eq_one ha (langlandsGaussSum_ne_zero χ₀ hψ₀)
  rw [hphaseE] at hδE
  have hε := unramified_lowerProduct_conductorOne F U hunr ψ γ hγ
  rw [hU] at hε
  have hs : (-1 : ℂ) ^ (ell - 1) * (-1 : ℂ) ^ (ell - 1) = 1 := by
    rw [← pow_add, show (ell - 1) + (ell - 1) = 2 * (ell - 1) by omega, pow_mul]
    simp
  have hprodU : (normCharacterFinset F U).prod (fun ν => localConstant F ν.1 ψ.character) =
      (-1 : ℂ) ^ (ell - 1) * (Characters.normCharacterProduct F U γ : ℂ) := by
    rw [hε, ← mul_assoc, hs, one_mul]
  have hconj := Characters.conjugacy hell hG U E hU hE hne χU.character χE.character
    (normQuasiChar U K χU.character) rfl hcomp.symm hprimitive
  have hres := congrArg Units.val (DFunLike.congr_fun hconj.2.2.1 γ)
  change (χU.character (Units.map (algebraMap F U).toMonoidHom γ) : ℂ) *
      (Characters.normCharacterProduct F U γ : ℂ) =
    (χE.character (Units.map (algebraMap F E).toMonoidHom γ) : ℂ) *
      (Characters.normCharacterProduct F E γ : ℂ) at hres
  unfold Characters.inducingFactor
  change localConstant U χU.character ψU.character * _ = localConstant E χE.character ψE.character * _
  rw [hδU, hδE, hphase, hprod, hprodU]
  linear_combination -(χ₀ (ell : ResidueField F) * phase (langlandsGaussSum χ₀ ψ₀) *
    (∏ j ∈ Finset.Icc 1 (ell - 1), phase (langlandsGaussSum (μ ^ j) ψ₀)) *
    (-1 : ℂ) ^ (ell - 1)) * hres

end ConductorOneInputs

section StableFormula

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private theorem halfDepth {m : ℕ} (hm : 1 < m) :
    IsLamprechtStationaryDepth m (m ⌈/⌉ 2) := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  exact ⟨hm, by omega, by omega⟩

/-- Construct an ordinary covector from the stationary quotient, with its
exact integer order. The choice is made only after finite duality has
constructed the class. -/
private theorem ordinaryCovector_exists
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (hm : 1 < χ.conductor) :
    ∃ g : Fˣ,
      ord F (g : F) = ((-((χ.conductor : ℤ) + ψ.conductor) : ℤ) : WithTop ℤ) ∧
      ∀ x : lattice F ((χ.conductor ⌈/⌉ 2 : ℕ) : ℤ),
        χ.character (positiveUnitOfLattice F (halfDepth hm).pos x) =
          ψ.character ((g : F) * (x : F)) := by
  let hr := halfDepth hm
  let Γ : AdmissibleGamma F χ ψ := Classical.choice AdmissibleGamma.exists_admissible
  obtain ⟨c, hc⟩ := latticeQuotientMk_surjective F
    (sub_le_sub_left hr.int_le_conductor (χ.conductor : ℤ))
    (stationaryNumeratorClass F χ ψ (χ.conductor : ℤ) hr Γ Γ.property)
  let β := stableStationaryRepresentativeUnit F χ ψ hr Γ c hc
  have hβ : ord F (β : F) = 0 := by
    rw [stableStationaryRepresentativeUnit_coe,
      stationaryNumeratorClass_representative_ord F χ ψ (χ.conductor : ℤ)
        hr Γ Γ.property c hc]
    simp
  refine ⟨β / (Γ : Fˣ), ?_, ?_⟩
  · rw [Units.val_div_eq_div_val, ord_div, hβ, Γ.property]
    simp [add_comm]
  · intro x
    have h := stationaryNumeratorClass_linearization F χ ψ (χ.conductor : ℤ)
      hr Γ Γ.property c hc x
    convert h using 2
    simp only [Units.val_div_eq_div_val, β, stableStationaryRepresentativeUnit_coe]
    ring

/-- Apply exact stable twist at the literal inverse covector. The
representative is verified on the whole stationary lattice by finite
duality; a single character value would not suffice. -/
private theorem localConstant_twist_of_covector
    (ν χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (hm : 1 < χ.conductor) (hν : ν.conductor ≤ χ.conductor / 2)
    (g : Fˣ)
    (hg : ord F (g : F) =
      ((-((χ.conductor : ℤ) + ψ.conductor) : ℤ) : WithTop ℤ))
    (hlinear : ∀ x : lattice F ((χ.conductor ⌈/⌉ 2 : ℕ) : ℤ),
      χ.character (positiveUnitOfLattice F (halfDepth hm).pos x) =
        ψ.character ((g : F) * (x : F))) :
    localConstant F (ν.character * χ.character) ψ.character =
      (ν.character g⁻¹ : ℂ) * localConstant F χ.character ψ.character := by
  let d := χ.conductor / 2
  let e := χ.conductor % 2
  have he : e ≤ 1 := by dsimp [e]; omega
  have hde : χ.conductor = 2 * d + e := by dsimp [d, e]; omega
  let hr := stableTwist_stationaryDepth F χ d e he hde hm
  have hdepth : d + e = χ.conductor ⌈/⌉ 2 := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    dsimp [d, e]
    omega
  let Γ : AdmissibleGamma F χ ψ := Classical.choice AdmissibleGamma.exists_admissible
  have horder : ord F ((g * (Γ : Fˣ) : Fˣ) : F) = 0 := by
    rw [Units.val_mul, ord_mul, hg, Γ.property]
    rw [← WithTop.coe_add]
    norm_cast
    omega
  let c : lattice F ((χ.conductor : ℤ) - (χ.conductor : ℤ)) :=
    ⟨((g * (Γ : Fˣ) : Fˣ) : F), by rw [mem_lattice, horder]; simp⟩
  have hc : latticeQuotientMk F
      (sub_le_sub_left hr.int_le_conductor (χ.conductor : ℤ)) c =
        stationaryNumeratorClass F χ ψ (χ.conductor : ℤ) hr Γ Γ.property := by
    apply (latticeQuotientMk_eq_stationaryNumeratorClass_iff
      F χ ψ (χ.conductor : ℤ) hr Γ Γ.property c).2
    intro x
    let x' : lattice F ((χ.conductor ⌈/⌉ 2 : ℕ) : ℤ) :=
      ⟨x, by simpa only [← hdepth] using x.property⟩
    have hx : (positiveUnitOfLattice F hr.pos x : Fˣ) =
        positiveUnitOfLattice F (halfDepth hm).pos x' := by
      apply Units.ext
      rfl
    rw [hx, hlinear]
    congr 1
    dsimp only [c, x']
    simp only [Units.val_mul]
    field_simp
  have hs := stableTwist F ν χ ψ d e he hde hm hν Γ c hc
  dsimp only at hs
  have hu : (Γ : Fˣ) / stableStationaryRepresentativeUnit F χ ψ hr Γ c hc =
      g⁻¹ := by
    have hb : stableStationaryRepresentativeUnit F χ ψ hr Γ c hc =
        g * (Γ : Fˣ) := by apply Units.ext; rfl
    rw [hb]
    simp [div_eq_mul_inv]
  rw [hu, ← localConstant_isDeltaFinite F, ← localConstant_isDeltaFinite F] at hs
  exact hs

end StableFormula

section StableLowerProduct

variable (F E : Type) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

local instance : Finite (NormCharacter F E) := primeCyclicNormCharacter_finite F E

/-- The full identity `O:F:stableFML`, including the quadratic evaluation
factor. Every lower twist is evaluated before the products are combined. -/
private theorem stable_pullback_lowerProduct
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (hm : 1 < χ.conductor)
    (hbound : ∀ ν : NormCharacter F E,
      multiplicativeConductorExponent F ν.1 ≤ χ.conductor / 2)
    (g : Fˣ)
    (hg : ord F (g : F) =
      ((-((χ.conductor : ℤ) + ψ.conductor) : ℤ) : WithTop ℤ))
    (hlinear : ∀ x : lattice F ((χ.conductor ⌈/⌉ 2 : ℕ) : ℤ),
      χ.character (positiveUnitOfLattice F (halfDepth hm).pos x) =
        ψ.character ((g : F) * (x : F))) :
    localConstant E (normQuasiChar F E χ.character)
        (tracePullbackAddChar F E ψ.character) *
      (normCharacterFinset F E).prod (fun ν => localConstant F ν.1 ψ.character) =
      (Characters.normCharacterProduct F E g⁻¹ : ℂ) *
        localConstant F χ.character ψ.character ^ Module.finrank F E := by
  classical
  letI := normCharacterFintype F E
  have hf := firstMainLemma F E
    (PrimeCyclicExtension.toCyclicPrimeExtension (F := F) (K := E))
    χ.character ψ.character ψ.character_ne_one
  change localConstant E (normQuasiChar F E χ.character)
      (tracePullbackAddChar F E ψ.character) *
    (normCharacterFinset F E).prod (fun ν => localConstant F ν.1 ψ.character) =
    (normCharacterFinset F E).prod
      (fun ν => localConstant F (ν.1 * χ.character) ψ.character) at hf
  rw [hf]
  have hcard : (normCharacterFinset F E).card = Module.finrank F E := by
    change @Fintype.card (NormCharacter F E) _ = _
    rw [← Nat.card_eq_fintype_card]
    by_cases hunr : ramificationIndex F E = 1
    · exact unramifiedNormCharacter_card F E hunr
    · let P := primeCyclicPreparation F E hunr
      exact ramifiedNormCharacter_card F E P.ht P.hres P.piK P.hpiK P.hgen
  calc
    _ = (normCharacterFinset F E).prod (fun ν =>
        (ν.1 g⁻¹ : ℂ) * localConstant F χ.character ψ.character) := by
      apply Finset.prod_congr rfl
      intro ν _
      exact localConstant_twist_of_covector F (canonicalLocalQuasiCharData F ν.1)
        χ ψ hm (hbound ν) g hg hlinear
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, hcard,
        Characters.normCharacterProduct_apply, Units.coe_prod]

end StableLowerProduct

section StableSides

variable (F U E : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field U] [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U]
  [PrimeCyclicExtension F U]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

local instance : Finite (NormCharacter F U) := primeCyclicNormCharacter_finite F U
local instance : Finite (NormCharacter F E) := primeCyclicNormCharacter_finite F E

/-- The two stable sides with their complete correction products. The
common covector is constructed from the base character and transported by
`covector`; no stationary data are assumed. -/
private theorem tame_stable_sides
    {ell : ℕ} (hell : ell.Prime) (hchar : residueCharacteristic F ≠ ell)
    (hU : Module.finrank F U = ell) (hE : Module.finrank F E = ell)
    (hunr : ramificationIndex F U = 1)
    (hram : ramificationIndex F E ≠ 1) (htame : IsTamelyRamified F E)
    (χ : LocalQuasiCharData F) (hm : 1 < χ.conductor)
    (νU : LocalQuasiCharData U) (νE : LocalQuasiCharData E)
    (hνU : νU.conductor = 1) (hνE : νE.conductor = 1)
    (ψ : LocalAddCharData F) :
    ∃ a : Fˣ,
      localConstant U (νU.character * normQuasiChar F U χ.character)
          (tracePullbackAddChar F U ψ.character) *
        (normCharacterFinset F U).prod (fun ν => localConstant F ν.1 ψ.character) =
        (νU.character (Units.map (algebraMap F U) a) *
          Characters.normCharacterProduct F U a : ℂˣ) *
          localConstant F χ.character ψ.character ^ ell ∧
      localConstant E (νE.character * normQuasiChar F E χ.character)
          (tracePullbackAddChar F E ψ.character) *
        (normCharacterFinset F E).prod (fun ν => localConstant F ν.1 ψ.character) =
        (νE.character (Units.map (algebraMap F E) a) *
          Characters.normCharacterProduct F E a : ℂˣ) *
          localConstant F χ.character ψ.character ^ ell := by
  let P := primeCyclicPreparation F E hram
  have ht := P.isLowerBreak_zero_of_isTamelyRamified F E htame
  let χU : LocalQuasiCharData U := ⟨normQuasiChar F U χ.character, χ.conductor,
    (unramified_multiplicativeConductor_compNorm F U hunr
      χ.character χ.conductor).2 χ.isConductor⟩
  let χE := canonicalLocalQuasiCharData E (normQuasiChar F E χ.character)
  have hχE : χE.conductor = 1 + ell * (χ.conductor - 1) := by
    have hc := χ.conductor_compNorm_eq_high F E ht P.hres P.piK P.hpiK P.hgen
      χE rfl (by simpa using hm)
    rw [hc, herbrandPsiNat, hE]
    simp
    omega
  have hmE : 1 < χE.conductor := by
    rw [hχE]
    have := hell.two_le
    have : 1 ≤ χ.conductor - 1 := by omega
    nlinarith
  let ψU : LocalAddCharData U := ⟨tracePullbackAddChar F U ψ.character, ψ.conductor,
    (unramified_additiveConductor_compTrace F U hunr
      ψ.character ψ.conductor).2 ψ.isConductor⟩
  let ψE := canonicalLocalAddCharData E (tracePullbackAddChar F E ψ.character)
    (Basic.tracePullbackAddChar_ne_one F E ψ.character ψ.character_ne_one)
  have hsum := high_compNorm_add_compTrace_conductor_eq F E ht P.hres
    P.piK P.hpiK P.hgen χ χE ψ ψE rfl rfl (by simpa using hm)
  obtain ⟨g, hg, hlinear⟩ := ordinaryCovector_exists F χ ψ hm
  obtain ⟨hlinU, hlinE⟩ := covector F U E ell χ.conductor hell hm hchar
    hU hunr hE P.hres χ.character χ.isConductor ψ.character ψ.character_ne_one
    g hlinear
  let gU : Uˣ := Units.map (algebraMap F U) g
  let gE : Eˣ := Units.map (algebraMap F E) g
  have hgU : ord U (gU : U) =
      ((-((χU.conductor : ℤ) + ψU.conductor) : ℤ) : WithTop ℤ) := by
    change ord U (algebraMap F U (g : F)) = _
    rw [ord_algebraMap, hunr, one_nsmul, hg]
  have hgE : ord E (gE : E) =
      ((-((χE.conductor : ℤ) + ψE.conductor) : ℤ) : WithTop ℤ) := by
    change ord E (algebraMap F E (g : F)) = _
    rw [ord_algebraMap, P.ramificationIndex_eq_degree, hg, hsum,
      ← WithTop.coe_nsmul]
    congr 1
    simp only [nsmul_eq_mul]
    ring
  have hlinE' : ∀ x : lattice E ((χE.conductor ⌈/⌉ 2 : ℕ) : ℤ),
      χE.character (positiveUnitOfLattice E (halfDepth hmE).pos x) =
        ψE.character ((gE : E) * (x : E)) := by
    intro x
    let x' : lattice E (((1 + ell * (χ.conductor - 1)) ⌈/⌉ 2 : ℕ) : ℤ) :=
      ⟨x, by simpa only [hχE] using x.property⟩
    convert hlinE x' using 1
    · apply congrArg (normQuasiChar F E χ.character)
      apply Units.ext
      rfl
    · rfl
  have hsU := localConstant_twist_of_covector U νU χU ψU hm
    (by rw [hνU]; change 1 ≤ χ.conductor / 2; omega) gU hgU hlinU
  have hsE := localConstant_twist_of_covector E νE χE ψE hmE
    (by rw [hνE]; omega) gE hgE hlinE'
  have hpU := stable_pullback_lowerProduct F U χ ψ hm (by
    intro ν
    rw [(multiplicativeConductorExponent_isConductor F ν.1).unique
      (unramifiedNormCharacter_conductor F U hunr ν)]
    exact Nat.zero_le _) g hg hlinear
  have hpE := stable_pullback_lowerProduct F E χ ψ hm (by
    intro ν
    by_cases hn : ν = 1
    · subst ν
      have hc : IsMultiplicativeConductor F (1 : ContinuousQuasiChar F) 0 :=
        IsMultiplicativeConductor.of_zero (fun _ _ => rfl)
      change multiplicativeConductorExponent F (1 : ContinuousQuasiChar F) ≤ _
      rw [(multiplicativeConductorExponent_isConductor F
        (1 : ContinuousQuasiChar F)).unique hc]
      exact Nat.zero_le _
    · rw [(multiplicativeConductorExponent_isConductor F ν.1).unique
        (tameNormCharacter_conductor F E ht P.hres P.piK P.hpiK P.hgen ν hn)]
      omega) g hg hlinear
  rw [hU] at hpU
  rw [hE] at hpE
  change localConstant E χE.character ψE.character * _ = _ at hpE
  refine ⟨g⁻¹, ?_, ?_⟩
  · change localConstant U (νU.character * χU.character) ψU.character * _ = _
    rw [hsU, mul_assoc, hpU]
    simp only [gU, ← map_inv, Units.val_mul]
    ring
  · change localConstant E (νE.character * χE.character) ψE.character * _ = _
    rw [hsE, mul_assoc, hpE]
    simp only [gE, ← map_inv, Units.val_mul]
    ring

end StableSides

section StableDiamond

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

/-- The higher-conductor part of `O:F:tame`, lines 980–1000, for the
genuine primitive compatible pair. The common base twist, conductor-one
pair, covector, and corrected restriction are all constructed. This includes
`ell = 2`, `m = 2`, arbitrary additive conductor, and nonunitary characters. -/
theorem comparison_of_conductor_gt_one
    {ell : ℕ} (hell : ell.Prime) (hchar : ell ≠ residueCharacteristic F)
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod ell) × Multiplicative (ZMod ell))))
    (U E : IntermediateField F K)
    (hU : Module.finrank F U = ell) (hE : Module.finrank F E = ell)
    (hne : Ramification.intermediateNormRange U ≠ Ramification.intermediateNormRange E)
    (hunr : ramificationIndex F U = 1)
    (θU : ContinuousQuasiChar U) (θE : ContinuousQuasiChar E)
    (Θ : ContinuousQuasiChar K) (m : ℕ)
    (hθU : IsMultiplicativeConductor U θU m) (hm : 1 < m)
    (hcU : normQuasiChar U K θU = Θ) (hcE : normQuasiChar E K θE = Θ)
    (hprimitive : ¬ ∃ ρ : ContinuousQuasiChar F, normQuasiChar F K ρ = Θ)
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1) :
    Characters.inducingFactor hell hG ψ U hU θU =
      Characters.inducingFactor hell hG ψ E hE θE := by
  have dataU := Basic.intermediateField_tower_compatible hell hG U hU
  have dataE := Basic.intermediateField_tower_compatible hell hG E hE
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F U
    dataU.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E
    dataE.2.2.2.2.2.2.2.2.2.2.2.1
  letI := primeCyclicNormCharacter_finite F U
  letI := primeCyclicNormCharacter_finite F E
  obtain ⟨lam, χU, χE, Ξ, htwU, htwE, hcompU, hcompE, hprim,
    hcondU, hcondE, _, hlam, _, hpullE, _, _⟩ :=
    tame_commonTwist hell hchar hG U E hU hE hne hunr θU θE Θ m hθU hm
      hcU hcE hprimitive
  have hram : ramificationIndex F E ≠ 1 := by
    intro he
    have hc := (unramified_multiplicativeConductor_compNorm F E he lam m).2 hlam
    have hd := hc.unique hpullE
    have := hell.two_le
    have : m - 1 + 1 = m := by omega
    nlinarith
  have htame : IsTamelyRamified F E := by
    change ¬ residueCharacteristic F ∣ ramificationIndex F E
    rw [(primeCyclicPreparation F E hram).ramificationIndex_eq_degree, hE]
    intro hd
    rcases (Nat.dvd_prime hell).1 hd with h | h
    · exact (residueCharacteristic_prime F).ne_one h
    · exact hchar h.symm
  let χ : LocalQuasiCharData F := ⟨lam, m, hlam⟩
  let νU : LocalQuasiCharData U := ⟨χU, 1, hcondU⟩
  let νE : LocalQuasiCharData E := ⟨χE, 1, hcondE⟩
  let ψF := canonicalLocalAddCharData F ψ hψ
  obtain ⟨a, haU, haE⟩ := tame_stable_sides F U E hell (Ne.symm hchar) hU hE
    hunr hram htame χ hm νU νE rfl rfl ψF
  have hconj := Characters.conjugacy hell hG U E hU hE hne
    χU χE Ξ hcompU hcompE hprim
  have ha := DFunLike.congr_fun hconj.2.2.1 a
  change χU (Units.map (algebraMap F U) a) * Characters.normCharacterProduct F U a =
    χE (Units.map (algebraMap F E) a) * Characters.normCharacterProduct F E a at ha
  unfold Characters.inducingFactor
  rw [htwU, htwE]
  exact haU.trans ((congrArg (fun z : ℂˣ =>
    (z : ℂ) * localConstant F lam ψ ^ ell) ha).trans haE.symm)

private theorem conductorOne_partner
    {ell : ℕ} (hell : ell.Prime) (hchar : ell ≠ residueCharacteristic F)
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod ell) × Multiplicative (ZMod ell))))
    (U E : IntermediateField F K)
    (hU : Module.finrank F U = ell) (hE : Module.finrank F E = ell)
    (hne : Ramification.intermediateNormRange U ≠ Ramification.intermediateNormRange E)
    (hunr : ramificationIndex F U = 1) (hram : ramificationIndex F E ≠ 1)
    (χU : LocalQuasiCharData U) (χE : LocalQuasiCharData E) (hχU : χU.conductor = 1)
    (hcomp : normQuasiChar U K χU.character = normQuasiChar E K χE.character)
    (hprimitive : ¬ ∃ lam : ContinuousQuasiChar F,
      normQuasiChar F K lam = normQuasiChar U K χU.character) : χE.conductor = 1 := by
  have dataU := Basic.intermediateField_tower_compatible hell hG U hU
  have dataE := Basic.intermediateField_tower_compatible hell hG E hE
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F U dataU.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension U K dataU.2.2.2.2.2.2.2.2.2.2.2.2
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E dataE.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension E K dataE.2.2.2.2.2.2.2.2.2.2.2.2
  let PE := primeCyclicPreparation F E hram
  have heE : ramificationIndex F E = ell := PE.ramificationIndex_eq_degree.trans hE
  have heTower (L : IntermediateField F K) :
      ramificationIndex F K = ramificationIndex F L * ramificationIndex L K := by
    obtain ⟨x, hx⟩ := exists_ord_eq F 1
    have h := congrArg (ord K) (IsScalarTower.algebraMap_apply F L K x)
    rw [ord_algebraMap, ord_algebraMap, ord_algebraMap, hx] at h
    simp only [← WithTop.coe_nsmul, nsmul_eq_mul] at h
    have hi : (ramificationIndex F K : ℤ) =
        (ramificationIndex F L : ℤ) * ramificationIndex L K := by
      simpa only [mul_one] using (WithTop.coe_injective h).trans (mul_comm _ _)
    exact_mod_cast hi
  have heU := heTower U
  have heE' := heTower E
  have hramUK : ramificationIndex U K ≠ 1 := by
    intro h
    rw [hunr, h, one_mul] at heU
    rw [heU, heE] at heE'
    have := ramificationIndex_pos E K
    have := hell.two_le
    nlinarith
  let PU := primeCyclicPreparation U K hramUK
  have heUK : ramificationIndex U K = ell :=
    PU.ramificationIndex_eq_degree.trans dataU.2.2.2.2.2.2.2.2.2.2.1
  have hunrEK : ramificationIndex E K = 1 := by
    rw [hunr, heUK, one_mul] at heU
    rw [heU, heE] at heE'
    exact Nat.mul_left_cancel hell.pos (by simpa using heE'.symm)
  have htameUK : IsTamelyRamified U K := by
    change ¬ residueCharacteristic U ∣ ramificationIndex U K
    rw [heUK, residueCharacteristic_extension_eq F U]
    intro h
    rcases (Nat.dvd_prime hell).1 h with h | h
    · exact (residueCharacteristic_prime F).ne_one h
    · exact hchar h.symm
  have ht := PU.isLowerBreak_zero_of_isTamelyRamified U K htameUK
  obtain ⟨D⟩ := (Characters.conjugacy hell hG U E hU hE hne χU.character χE.character
    (normQuasiChar U K χU.character) rfl hcomp.symm hprimitive).1
  let χK := canonicalLocalQuasiCharData K (normQuasiChar U K χU.character)
  have hχK : χK.conductor = χU.conductor :=
    χU.conductor_compNorm_eq_of_minimalOrbit U K ht PU.hres PU.piK PU.hpiK PU.hgen
      χK rfl (by omega) (by
        intro μ q hq
        by_contra hlt
        have hq0 : q = 0 := by omega
        obtain ⟨σ, hσ⟩ := D.quotientEquiv.surjective μ
        have hconj : IsMultiplicativeConductor U
            (Basic.conjugateQuasiChar F U σ χU.character) q := by
          rw [D.conjugate_eq_twist, hσ]
          have hcomm : χU.character * μ.1 = μ.1 * χU.character := by
            apply ContinuousMonoidHom.ext
            intro x
            exact mul_comm _ _
          rw [hcomm]
          exact hq
        have hz : χU.conductor ≤ 0 := χU.isConductor.minimal 0 (by
          intro x hx
          have hy : Units.map σ.toMonoidHom x ∈ unitFiltration U q := by
            rw [hq0, mem_unitFiltration_zero]
            change ord U (σ (x : U)) = 0
            rw [ord_galoisConjugate]
            exact (mem_unitFiltration_zero U x).1 hx
          have hh := hconj.trivial _ hy
          rw [Basic.conjugateQuasiChar_apply] at hh
          have heq : Units.map σ.symm.toRingEquiv.toMonoidHom (Units.map σ.toMonoidHom x) = x := by
            apply Units.ext
            simp
          rwa [heq] at hh)
        omega)
  have hcK := χK.isConductor
  rw [hχK, hχU] at hcK
  have hcE : IsMultiplicativeConductor E χE.character 1 := by
    apply (unramified_multiplicativeConductor_compNorm E K hunrEK χE.character 1).1
    change IsMultiplicativeConductor K (normQuasiChar E K χE.character) 1
    rw [← hcomp]
    exact hcK
  exact χE.isConductor.unique hcE

/-- Both conductor branches for a distinguished unramified lower field.
The ramified partner's conductor-one condition is derived, rather than
assumed, in the endpoint branch. -/
theorem unramified_comparison
    {ell : ℕ} (hell : ell.Prime) (hchar : ell ≠ residueCharacteristic F)
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod ell) × Multiplicative (ZMod ell))))
    (U E : IntermediateField F K)
    (hU : Module.finrank F U = ell) (hE : Module.finrank F E = ell)
    (hne : Ramification.intermediateNormRange U ≠ Ramification.intermediateNormRange E)
    (hunr : ramificationIndex F U = 1) (hram : ramificationIndex F E ≠ 1)
    (θU : ContinuousQuasiChar U) (θE : ContinuousQuasiChar E)
    (Θ : ContinuousQuasiChar K)
    (hcU : normQuasiChar U K θU = Θ) (hcE : normQuasiChar E K θE = Θ)
    (hprimitive : ¬ ∃ ρ : ContinuousQuasiChar F, normQuasiChar F K ρ = Θ)
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1) :
    Characters.inducingFactor hell hG ψ U hU θU =
      Characters.inducingFactor hell hG ψ E hE θE := by
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F U
    (Basic.intermediateField_tower_compatible hell hG U hU).2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E
    (Basic.intermediateField_tower_compatible hell hG E hE).2.2.2.2.2.2.2.2.2.2.2.1
  let χU := canonicalLocalQuasiCharData U θU
  let χE := canonicalLocalQuasiCharData E θE
  by_cases hm : 1 < χU.conductor
  · exact comparison_of_conductor_gt_one hell hchar hG U E hU hE hne hunr θU θE Θ
      χU.conductor χU.isConductor hm hcU hcE hprimitive ψ hψ
  have hprimU : ¬ ∃ lam : ContinuousQuasiChar F, normQuasiChar F U lam = θU := by
    rintro ⟨lam, hlam⟩
    apply hprimitive
    refine ⟨lam, ?_⟩
    rw [← hcU, ← hlam]
    apply ContinuousMonoidHom.ext
    intro x
    change lam (normUnits F K x) = lam (normUnits F U (normUnits U K x))
    congr 1
    apply Units.ext
    exact (Basic.norm_tower (F := F) (L := U) (x := (x : K))).symm
  have hpos := tame_primitive_conductor_positive F U θU χU.isConductor hprimU
  have hχU : χU.conductor = 1 := by omega
  have hprim : ¬ ∃ lam : ContinuousQuasiChar F,
      normQuasiChar F K lam = normQuasiChar U K χU.character := by
    simpa only [χU, canonicalLocalQuasiCharData_character, hcU] using hprimitive
  have hcomp : normQuasiChar U K χU.character = normQuasiChar E K χE.character :=
    hcU.trans hcE.symm
  have hχE := conductorOne_partner hell hchar hG U E hU hE hne hunr hram χU χE hχU hcomp hprim
  have htame : IsTamelyRamified F E := by
    change ¬ residueCharacteristic F ∣ ramificationIndex F E
    rw [(primeCyclicPreparation F E hram).ramificationIndex_eq_degree, hE]
    intro h
    rcases (Nat.dvd_prime hell).1 h with h | h
    · exact (residueCharacteristic_prime F).ne_one h
    · exact hchar h.symm
  exact comparison_of_conductor_one hell hG U E hU hE hne hunr hram htame χU χE hχU hχE
    hcomp hprim (canonicalLocalAddCharData F ψ hψ)

private theorem tame_inertia_lines
    {ell : ℕ} (hell : ell.Prime) (hchar : ell ≠ residueCharacteristic F)
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod ell) × Multiplicative (ZMod ell)))) :
    Nat.card (Ramification.inertiaSubgroup (F := F) (K := K)) = ell ∧
      ∃ H : Subgroup Gal(K/F), Nat.card H = ell ∧
        H ≠ Ramification.inertiaSubgroup (F := F) (K := K) := by
  classical
  obtain ⟨e⟩ := hG
  have hpow (σ : Gal(K/F)) : σ ^ ell = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    ext <;> apply Multiplicative.toAdd.injective <;> simp [nsmul_eq_mul]
  have hcardG : Nat.card Gal(K/F) = ell * ell := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    have hc : Nat.card (Multiplicative (ZMod ell)) = ell :=
      (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod ell)
    rw [hc]
  have hcop : Nat.Coprime (residueCharacteristic F) ell :=
    (Nat.coprime_primes (residueCharacteristic_prime F) hell).2 (Ne.symm hchar)
  have hwild (σ : lowerRamificationGroup F K 1) : σ = 1 := by
    have hp : σ ^ ell = 1 := Subtype.ext (hpow σ.1)
    apply orderOf_eq_one_iff.mp
    have hc := (Ramification.wildInertia_isPGroup (F := F) (K := K)).orderOf_coprime hcop σ
    exact hc.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hp)
  have hinj : Function.Injective (Ramification.tameInertiaHom (F := F) (K := K)) := by
    apply (MonoidHom.ker_eq_bot_iff _).1
    apply (Subgroup.eq_bot_iff_forall _).2
    intro σ hσ
    have hs := (Ramification.tameInertiaHom_eq_one_iff (F := F) (K := K) σ).1 hσ
    exact Subtype.ext (congrArg (fun y : lowerRamificationGroup F K 1 => (y : Gal(K/F)))
      (hwild ⟨σ.1, hs⟩))
  let I := Ramification.inertiaSubgroup (F := F) (K := K)
  letI : IsCyclic I := by
    letI : IsCyclic (lowerRamificationGroup F K 0) := isCyclic_of_injective _ hinj
    let eI : I ≃* lowerRamificationGroup F K 0 := MulEquiv.subgroupCongr
      (Ramification.inertiaSubgroup_eq_lowerRamificationGroup_zero (F := F) (K := K))
    exact isCyclic_of_injective eI.toMonoidHom eI.injective
  letI : IsCyclic (Gal(K/F) ⧸ I) := Ramification.residueActionQuotient_cyclic (F := F) (K := K)
  have cyclicCardDiv {G : Type} [Group G] [IsCyclic G]
      (hp : ∀ x : G, x ^ ell = 1) : Nat.card G ∣ ell := by
    obtain ⟨x, hx⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
    rw [← orderOf_eq_card_of_zpowers_eq_top hx]
    exact orderOf_dvd_of_pow_eq_one (hp x)
  have hIdvd : Nat.card I ∣ ell := cyclicCardDiv (fun x : I => Subtype.ext (hpow x.1))
  have hQdvd : Nat.card (Gal(K/F) ⧸ I) ∣ ell := cyclicCardDiv (by
    intro x
    induction x using QuotientGroup.induction_on with
    | H x => rw [← QuotientGroup.mk_pow, hpow x]; rfl)
  have hI : Nat.card I = ell := by
    rcases (Nat.dvd_prime hell).1 hIdvd with h | h
    · have hc := I.card_mul_index
      rw [h, one_mul, I.index_eq_card, hcardG] at hc
      have hle := Nat.le_of_dvd hell.pos hQdvd
      rw [hc] at hle
      have := hell.two_le
      nlinarith
    · exact h
  refine ⟨hI, ?_⟩
  have hItop : I ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top, hcardG] at hI
    have := hell.two_le
    nlinarith
  obtain ⟨x, hx⟩ : ∃ x : Gal(K/F), x ∉ I := by
    by_contra! h
    exact hItop ((Subgroup.eq_top_iff' I).2 h)
  have hx1 : x ≠ 1 := fun h => hx (h ▸ I.one_mem)
  have ho : orderOf x = ell :=
    (Nat.dvd_prime hell).1 (orderOf_dvd_of_pow_eq_one (hpow x)) |>.resolve_left
      (fun h => hx1 (orderOf_eq_one_iff.mp h))
  refine ⟨Subgroup.zpowers x, (Nat.card_zpowers x).trans ho, ?_⟩
  intro h
  apply hx
  change x ∈ Ramification.inertiaSubgroup (F := F) (K := K)
  rw [← h]
  exact Subgroup.mem_zpowers x

set_option maxHeartbeats 800000 in
/-- **The complete tame comparison**, `O:F:tame` (Theorem 5.3).

For actual local fields in either characteristic and every prime different
from the residue characteristic, arbitrary compatible inducing characters
of an invariant, non-descending character have equal normalized induction
expressions. The expressions use FML's canonical local constant and the
complete lower norm-character products, including in degree two. -/
theorem comparison
    {ell : ℕ} (hell : ell.Prime) (hchar : ell ≠ residueCharacteristic F)
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod ell) × Multiplicative (ZMod ell))))
    (Θ : ContinuousQuasiChar K)
    (hinv : ∀ σ : Gal(K/F), Basic.conjugateQuasiChar F K σ Θ = Θ)
    (hprimitive : ¬ ∃ lam : ContinuousQuasiChar F, normQuasiChar F K lam = Θ)
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1)
    (I J : IntermediateField F K)
    (hI : Module.finrank F I = ell) (hJ : Module.finrank F J = ell)
    (θI : ContinuousQuasiChar I) (θJ : ContinuousQuasiChar J)
    (hcI : normQuasiChar I K θI = Θ) (hcJ : normQuasiChar J K θJ = Θ) :
    Characters.inducingFactor hell hG ψ I hI θI =
      Characters.inducingFactor hell hG ψ J hJ θJ := by
  classical
  obtain ⟨hInertia, H, hH, hHne⟩ := tame_inertia_lines hell hchar hG
  let T := Ramification.inertiaSubgroup (F := F) (K := K)
  let U := IntermediateField.fixedField T
  let E₀ := IntermediateField.fixedField H
  have htotal : Module.finrank F K = ell * ell := by
    rw [← IsGalois.card_aut_eq_finrank F K, Nat.card_congr hG.some.toEquiv, Nat.card_prod]
    have hc : Nat.card (Multiplicative (ZMod ell)) = ell :=
      (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod ell)
    rw [hc]
  have hdegree (A : Subgroup Gal(K/F)) (hA : Nat.card A = ell) :
      Module.finrank F (IntermediateField.fixedField A) = ell := by
    have h := Module.finrank_mul_finrank F (IntermediateField.fixedField A) K
    rw [IntermediateField.finrank_fixedField_eq_card, hA, htotal] at h
    exact Nat.mul_right_cancel hell.pos h
  have hU : Module.finrank F U = ell := hdegree T hInertia
  have hE₀ : Module.finrank F E₀ = ell := hdegree H hH
  have hUdata := Ramification.inertiaFixedField_unramified (F := F) (K := K)
  change IsGalois F U ∧ ramificationIndex F U = 1 ∧ residueDegree F U = residueDegree F K at hUdata
  have hunr : ramificationIndex F U = 1 := hUdata.2.1
  have hsep₀ : Ramification.intermediateNormRange U ≠ Ramification.intermediateNormRange E₀ :=
    (Ramification.normSeparation hell hG).unramified_lower hInertia H hH hHne
  obtain ⟨_, _, hall⟩ := Characters.distinguishedComparisons_imply_family hell hG U E₀
    hU hE₀ hsep₀ Θ hinv hprimitive ψ hψ (by
      intro E hE hEU θU θE hcU hcE
      have dataE := Basic.intermediateField_tower_compatible hell hG E hE
      letI := PrimeCyclicExtension.ofCyclicPrimeExtension F U
        (Basic.intermediateField_tower_compatible hell hG U hU).2.2.2.2.2.2.2.2.2.2.2.1
      letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E dataE.2.2.2.2.2.2.2.2.2.2.2.1
      have hfix : Nat.card E.fixingSubgroup = Module.finrank E K := by
        rw [← IntermediateField.finrank_fixedField_eq_card, IsGalois.fixedField_fixingSubgroup]
      have hfixcard : Nat.card E.fixingSubgroup = ell :=
        hfix.trans dataE.2.2.2.2.2.2.2.2.2.2.1
      have hfixne : E.fixingSubgroup ≠ T := by
        intro h
        apply hEU
        rw [← IsGalois.fixedField_fixingSubgroup E, h]
      have hsep := (Ramification.normSeparation hell hG).unramified_lower
        hInertia E.fixingSubgroup hfixcard hfixne
      rw [IsGalois.fixedField_fixingSubgroup E] at hsep
      have hram : ramificationIndex F E ≠ 1 := by
        intro he
        have hresU : residueDegree F U = ell := by
          have h := finrank_eq_ramificationIndex_mul_residueDegree F U
          rw [hU, hunr, one_mul] at h
          exact h.symm
        have hresE : residueDegree F E = ell := by
          have h := finrank_eq_ramificationIndex_mul_residueDegree F E
          rw [hE, he, one_mul] at h
          exact h.symm
        apply hsep
        change (normUnits F U).range = (normUnits F E).range
        ext x
        rw [mem_unramified_norm_range_iff_order_dvd F U hunr,
          mem_unramified_norm_range_iff_order_dvd F E he, hresU, hresE]
      exact unramified_comparison hell hchar hG U E hU hE hsep hunr hram θU θE Θ
        hcU hcE hprimitive ψ hψ)
  exact hall I J hI hJ θI θJ hcI hcJ

end StableDiamond



end

end LanglandsSecondMainLemma.Tame
