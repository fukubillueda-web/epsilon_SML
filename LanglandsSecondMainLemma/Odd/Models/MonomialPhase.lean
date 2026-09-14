import Batteries.Tactic.OpenPrivate
import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Odd.Models.Setup
import LanglandsSecondMainLemma.Odd.Total.WeightedDefect
import LanglandsSecondMainLemma.Odd.Total.SecondDefect
import LanglandsSecondMainLemma.Odd.NormPhase
import LanglandsSecondMainLemma.Odd.Total.ProjectionTransfer

/-!
# Odd / Models / Monomial Phase

Paper Lemma 8.2 (`O:M:monophase`), retaining one exact coordinate for
both defects. The common coordinate is constructed by `Total.translatedNorm`;
the coefficient and weighted calculations reuse the compiled helper proofs
of the declared dependencies. Norm-character conversion is on its whole
domain, with integer lattice exponents and the actual lower norm.
-/

namespace LanglandsSecondMainLemma.Odd.Models

noncomputable section

open LanglandsFirstMainLemma

/-- The numerical inequalities needed specifically by the exceptional
monomial in Paper 8.2. -/
theorem monomialPhase_depth_bounds {p t δ : ℕ} (hp : 2 < p) (ht : 0 < t) :
    let q := (1 + t + (t + p * δ)) ⌈/⌉ p
    1 + δ ≤ q ∧
      (t + δ : ℤ) + 1 ≤ q + ((p : ℤ) - 2) * t ∧
      1 + (t + δ : ℤ) + ((p : ℤ) - 3) * t ≤
        q + ((p : ℤ) - 2) * t + (p : ℤ) * ((p : ℤ) - 1) * δ := by
  dsimp only
  let q := (1 + t + (t + p * δ)) ⌈/⌉ p
  have hround := le_smul_ceilDiv (b := 1 + t + (t + p * δ))
    (show 0 < p by omega)
  simp only [smul_eq_mul] at hround
  have hq : 1 + δ ≤ q := by
    by_contra h
    have hle : q ≤ δ := by omega
    have hmul := Nat.mul_le_mul_left p hle
    dsimp only [q] at hmul
    omega
  have hqZ : 1 + (δ : ℤ) ≤ q := by exact_mod_cast hq
  have hpZ : (3 : ℤ) ≤ p := by omega
  have htZ : (1 : ℤ) ≤ t := by omega
  have hδZ : (0 : ℤ) ≤ δ := by positivity
  have hprod : 0 ≤ (p : ℤ) * ((p : ℤ) - 1) * δ :=
    mul_nonneg (mul_nonneg (by omega) (by omega)) hδZ
  dsimp only [q] at hqZ
  refine ⟨hq, ?_, ?_⟩
  · nlinarith
  · nlinarith

section Lattices

variable (E L : Type*) [Field E] [Field L]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra E L] [ValuativeExtension E L]

/-- The strict upper depth `1+p*t` of a ground-field element descends to
`t+1`, using the integral normalized valuation, including its infinite value. -/
theorem monomialPhase_descend_lattice {p : ℕ} (hp : 0 < p)
    (hram : ramificationIndex E L = p) {t : ℤ} {z : E}
    (hz : algebraMap E L z ∈ lattice L (1 + (p : ℤ) * t)) :
    z ∈ lattice E (t + 1) := by
  by_cases hz0 : z = 0
  · simp [hz0]
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff E).2 hz0)
  rw [mem_lattice, ord_algebraMap, hram, ← hv, ← WithTop.coe_nsmul,
    WithTop.coe_le_coe] at hz
  simp only [nsmul_eq_mul] at hz
  rw [mem_lattice, ← hv, WithTop.coe_le_coe]
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  have : t < v := by nlinarith
  omega

/-- Descent to the complete norm-conversion domain, with the exact ceiling. -/
theorem monomialPhase_ceil_depth {p T : ℕ} (hp : 0 < p)
    (hram : ramificationIndex E L = p) {x : E}
    (hx : algebraMap E L x ∈ lattice L (T : ℤ)) :
    x ∈ lattice E ((T ⌈/⌉ p : ℕ) : ℤ) := by
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff E).2 hx0)
  rw [mem_lattice, ord_algebraMap, hram, ← hv, ← WithTop.coe_nsmul,
    WithTop.coe_le_coe] at hx
  simp only [nsmul_eq_mul] at hx
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  have hv0 : 0 ≤ v := by nlinarith [Int.natCast_nonneg T]
  have hnat : T ≤ v.toNat * p := by
    exact_mod_cast (show (T : ℤ) ≤ (v.toNat : ℤ) * p by
      rw [Int.toNat_of_nonneg hv0]; nlinarith)
  have hc := (ceilDiv_le_iff_le_mul hp).2 (by simpa only [mul_comm] using hnat)
  rw [mem_lattice, ← hv, WithTop.coe_le_coe]
  simpa only [Int.toNat_of_nonneg hv0] using
    (show ((T ⌈/⌉ p : ℕ) : ℤ) ≤ (v.toNat : ℤ) by exact_mod_cast hc)

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeExtension E L] in
/-- Removing the negative coordinate power raises the coefficient depth.
There is no subtraction in natural-number ideal exponents. -/
theorem monomialPhase_coefficient_mem {t j : ℕ} {q : ℤ} {Delta : L} {x : E}
    (hDelta : ord L Delta = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hx : algebraMap E L x * Delta ^ j ∈ lattice L q) :
    algebraMap E L x ∈ lattice L (q + (j : ℤ) * t) := by
  have hDelta0 : Delta ≠ 0 := by
    intro hz
    rw [hz, ord_zero] at hDelta
    exact WithTop.coe_ne_top hDelta.symm
  have hi : (Delta ^ j)⁻¹ ∈ lattice L ((j : ℤ) * t) := by
    simp only [mem_lattice, ord_inv, ord_pow, hDelta, ← WithTop.coe_nsmul,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg, nsmul_eq_mul, mul_neg,
      neg_neg, le_refl]
  simpa only [mul_inv_cancel_right₀ (pow_ne_zero j hDelta0)] using
    mul_mem_lattice L hx hi

end Lattices

section Phase

variable (F E₁ E₂ K : Type*) [Field F] [Field E₁] [Field E₂] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E₁] [TopologicalSpace E₁] [IsNonarchimedeanLocalField E₁]
  [ValuativeRel E₂] [TopologicalSpace E₂] [IsNonarchimedeanLocalField E₂]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F E₁] [ValuativeExtension F E₁]
  [Algebra F E₂] [ValuativeExtension F E₂]
  [Algebra E₁ K] [ValuativeExtension E₁ K]
  [Algebra E₂ K] [ValuativeExtension E₂ K]

/-- The exceptional coefficient and the scalar product have precisely the
depths needed for whole-domain conversion and Paper H17, respectively. -/
theorem monomialPhase_exceptional_depths {p t δ : ℕ}
    (hp : 2 < p) (ht : 0 < t)
    (hram₁ : ramificationIndex E₁ K = p)
    (hram₂ : ramificationIndex E₂ K = p)
    {Delta : K} {x : E₂} {s : E₁}
    (hDelta : ord K Delta = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hs : s ∈ lattice E₁ (((p : ℤ) - 1) * δ))
    (hx : algebraMap E₂ K x * Delta ^ (p - 2) ∈
      lattice K (((1 + t + (t + p * δ)) ⌈/⌉ p : ℕ) : ℤ)) :
    algebraMap E₂ K x ∈ lattice K ((t + δ : ℤ) + 1) ∧
      x ∈ lattice E₂ ((((t + δ + 1) ⌈/⌉ p : ℕ) : ℤ)) ∧
      algebraMap E₂ K x * algebraMap E₁ K s ∈
        lattice K (1 + (t + δ : ℤ) + ((p : ℤ) - 3) * t) := by
  obtain ⟨_hq, hcoeffDepth, htransferDepth⟩ := monomialPhase_depth_bounds hp ht
  have hcoeff := monomialPhase_coefficient_mem E₂ K hDelta hx
  rw [Nat.cast_sub (by omega : 2 ≤ p), Nat.cast_ofNat] at hcoeff
  have hxK : algebraMap E₂ K x ∈ lattice K ((t + δ : ℤ) + 1) :=
    lattice_antitone K hcoeffDepth hcoeff
  refine ⟨hxK, ?_, ?_⟩
  · apply monomialPhase_ceil_depth E₂ K (by omega) hram₂
    simpa only [Nat.cast_add, Nat.cast_one] using hxK
  · have hsK : algebraMap E₁ K s ∈
        lattice K ((p : ℤ) * (((p : ℤ) - 1) * δ)) := by
      rw [mem_lattice, ord_algebraMap, hram₁]
      simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using
        nsmul_le_nsmul_right ((mem_lattice E₁).1 hs) p
    apply lattice_antitone K _ (mul_mem_lattice K hcoeff hsK)
    simpa only [mul_assoc] using htransferDepth

/-- Outside the exceptional exponent, both defects are killed by the
whole base-field conductor ideal. -/
theorem monomialPhase_nonexceptional {p : ℕ} (hp : 0 < p)
    (hram : ramificationIndex F E₁ = p) {t : ℕ}
    (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    {g h : F} (hg : g ∈ lattice F ((t + 1 : ℕ) : ℤ))
    (hh : algebraMap F E₁ h ∈ lattice E₁ (1 + (p : ℤ) * t)) :
    Psi (g + h) = 1 := by
  have hhF := monomialPhase_descend_lattice F E₁ hp hram hh
  apply hPsi.trivial
  simpa only [neg_neg, Nat.cast_add, Nat.cast_one] using
    (lattice F ((t : ℤ) + 1)).add_mem hg hhF

variable [Module.Free F E₂] [Module.Finite F E₂] [PrimeCyclicExtension F E₂]

/-- The exceptional trace--norm calculation of Paper 8.2 from simultaneous
defect and projection estimates. `monomialPhase` constructs these estimates
for one coordinate. Conversion uses the actual norm character on its entire
truncated-log chart. -/
theorem monomialPhase_exceptional_of_estimates {p t c : ℕ}
    (hp : 2 < p) (htpos : 0 < t)
    (hdegree : Module.finrank F E₂ = p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E₂ t)
    (hres : residueDegree F E₂ = 1)
    (hchar : residueCharacteristic F = p)
    (hramF₁ : ramificationIndex F E₁ = p)
    (hram₁K : ramificationIndex E₁ K = p)
    (hram₂K : ramificationIndex E₂ K = p)
    (hc : c = (t + 1) ⌈/⌉ p) (hcpos : 0 < c)
    (tau : NormCharacter F E₂) (htau : tau ≠ 1)
    (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (hchart : ∀ z : lattice F (c : ℤ),
      tau.1 (positiveUnitOfLattice F hcpos (-z)) =
        Psi (Odd.truncatedLog p (z : F)))
    (x y : E₂) (s : E₁) (g h : F)
    (hx : algebraMap E₂ K x ∈ lattice K ((t + 1 : ℕ) : ℤ))
    (hs : s ∈ lattice E₁ 0)
    (hprime : (p : E₁) ∈ lattice E₁ (((p : ℤ) - 1) * t))
    (hclose : algebraMap E₂ K y - algebraMap E₂ K x * algebraMap E₁ K s ∈
      lattice K (1 + (p : ℤ) * t))
    (hg : g = trace F E₂ (y - x))
    (hh : algebraMap F E₁ h -
      ((p : E₁) - 1) * algebraMap F E₁ (norm F E₂ x) * (1 - s ^ p) ∈
        lattice E₁ (1 + (p : ℤ) * t))
    (htransfer : algebraMap F E₁ (norm F E₂ x) * s ^ p -
      algebraMap F E₁ (norm F E₂ y) ∈ lattice E₁ (1 + (p : ℤ) * t)) :
    Psi (g + h) = 1 := by
  have hp0 : 0 < p := by omega
  have hxC : x ∈ lattice E₂ (c : ℤ) := by
    rw [hc]
    exact monomialPhase_ceil_depth E₂ K hp0 hram₂K hx
  have hsK : algebraMap E₁ K s ∈ lattice K 0 := by
    rw [mem_lattice, ord_algebraMap, hram₁K]
    simpa only [← WithTop.coe_nsmul, nsmul_zero] using
      nsmul_le_nsmul_right ((mem_lattice E₁).1 hs) p
  have hxs : algebraMap E₂ K x * algebraMap E₁ K s ∈
      lattice K ((t + 1 : ℕ) : ℤ) := by
    simpa only [add_zero] using mul_mem_lattice K hx hsK
  have hcloseT : algebraMap E₂ K y - algebraMap E₂ K x * algebraMap E₁ K s ∈
      lattice K ((t + 1 : ℕ) : ℤ) := by
    apply lattice_antitone K _ hclose
    push_cast
    have hpZ : (1 : ℤ) ≤ p := by omega
    nlinarith [Int.natCast_nonneg t]
  have hyK : algebraMap E₂ K y ∈ lattice K ((t + 1 : ℕ) : ℤ) := by
    simpa only [sub_add_cancel] using
      (lattice K ((t + 1 : ℕ) : ℤ)).add_mem hcloseT hxs
  have hyC : y ∈ lattice E₂ (c : ℤ) := by
    rw [hc]
    exact monomialPhase_ceil_depth E₂ K hp0 hram₂K hyK
  have hnormX : algebraMap F E₁ (norm F E₂ x) ∈
      lattice E₁ ((t + 1 : ℕ) : ℤ) := by
    rw [mem_lattice, ord_algebraMap, hramF₁, ord_norm, hres, one_nsmul]
    simpa only [mem_lattice, ord_algebraMap, hram₂K] using hx
  have hsp : s ^ p ∈ lattice E₁ 0 := by
    rw [mem_lattice, ord_pow]
    simpa only [← WithTop.coe_nsmul, nsmul_zero] using
      nsmul_le_nsmul_right ((mem_lattice E₁).1 hs) p
  have hfactor : 1 - s ^ p ∈ lattice E₁ 0 :=
    (lattice E₁ 0).sub_mem (by simp) hsp
  have hcorrection : (p : E₁) * algebraMap F E₁ (norm F E₂ x) *
      (1 - s ^ p) ∈ lattice E₁ (1 + (p : ℤ) * t) := by
    have hc := mul_mem_lattice E₁ (mul_mem_lattice E₁ hprime hnormX) hfactor
    convert hc using 1
    congr 1
    push_cast
    ring
  have hnormError : algebraMap F E₁ (h + norm F E₂ x - norm F E₂ y) ∈
      lattice E₁ (1 + (p : ℤ) * t) := by
    have herr := (lattice E₁ (1 + (p : ℤ) * t)).add_mem
      ((lattice E₁ _).add_mem hh hcorrection) htransfer
    convert herr using 1
    simp only [map_add, map_sub]
    ring
  have hnormErrorF := monomialPhase_descend_lattice F E₁ hp0 hramF₁ hnormError
  have herrorPhase : Psi (h + norm F E₂ x - norm F E₂ y) = 1 := by
    apply hPsi.trivial
    simpa only [neg_neg, Nat.cast_add, Nat.cast_one] using hnormErrorF
  have hconversion (z : E₂) (hz : z ∈ lattice E₂ (c : ℤ)) :
      Psi (trace F E₂ z + norm F E₂ z) = 1 := by
    apply (Odd.normPhase F E₂ ht htpos hres (hchar.trans hdegree.symm)
      (by omega) c (by simpa only [hdegree] using hc) hcpos tau htau Psi hPsi
      (by simpa only [hdegree] using hchart) z hz).1
  have hphaseDifference :
      Psi ((trace F E₂ y + norm F E₂ y) -
        (trace F E₂ x + norm F E₂ x)) = 1 := by
    calc
      _ = Psi (trace F E₂ y + norm F E₂ y) /
          Psi (trace F E₂ x + norm F E₂ x) := Psi.toAddChar.map_sub_eq_div _ _
      _ = 1 := by rw [hconversion y hyC, hconversion x hxC, div_one]
  calc
    Psi (g + h) = Psi (((trace F E₂ y + norm F E₂ y) -
        (trace F E₂ x + norm F E₂ x)) +
          (h + norm F E₂ x - norm F E₂ y)) := by
      congr 1
      rw [hg, map_sub]
      ring
    _ = Psi ((trace F E₂ y + norm F E₂ y) -
        (trace F E₂ x + norm F E₂ x)) *
          Psi (h + norm F E₂ x - norm F E₂ y) := Psi.toAddChar.map_add_eq_mul _ _
    _ = 1 := by rw [hphaseDifference, herrorPhase, one_mul]

end Phase

/-- Paper H17 in the scalar form used in Lemma 8.2. The crossed norm
restriction is proved from the genuine prime-square diamond; the factor
on the left is the complete lower norm. -/
theorem monomialPhase_projectionTransfer
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (D : Total.OddTotalBreakData (F := F) (K := K) hp hG) :
    let B₁ := D.B₁
    let B₂ := D.B₂
    letI := Basic.intermediateFieldValuativeRel B₁
    letI := Basic.intermediateFieldTopology B₁
    letI := Basic.intermediateField_localField B₁
    letI := Basic.intermediateFieldValuativeRel B₂
    letI := Basic.intermediateFieldTopology B₂
    letI := Basic.intermediateField_localField B₂
    ∀ (x : B₂) (s : B₁) (y : B₂),
      algebraMap B₂ K x * algebraMap B₁ K s - algebraMap B₂ K y ∈
        lattice K (1 + (p : ℤ) * D.t₂) →
      algebraMap B₂ K x * algebraMap B₁ K s ∈
        lattice K (1 + D.t₂ + ((p : ℤ) - 3) * D.t) →
      algebraMap F B₁ (norm F B₂ x) * s ^ p - algebraMap F B₁ (norm F B₂ y) ∈
        lattice B₁ (1 + (p : ℤ) * D.t₂) := by
  dsimp only [Total.OddTotalBreakData.B₁, Total.OddTotalBreakData.B₂]
  let B₁ := IntermediateField.fixedField D.H₁
  let B₂ := IntermediateField.fixedField D.H₂
  letI := Basic.intermediateFieldValuativeRel B₁
  letI := Basic.intermediateFieldTopology B₁
  letI := Basic.intermediateField_localField B₁
  letI := Basic.intermediateFieldValuativeRel B₂
  letI := Basic.intermediateFieldTopology B₂
  letI := Basic.intermediateField_localField B₂
  obtain ⟨_hLocal₁, hFreeF₁, hFiniteF₁, hFree₁K, hFinite₁K, _hScalar₁,
      _hValF₁, _hVal₁K, htotal, hdegree₁, hdegree₁K, hcyc₁, _hcyc₁K⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁
  letI := hFreeF₁
  letI := hFiniteF₁
  letI := hFree₁K
  letI := hFinite₁K
  letI : IsGalois F B₁ := hcyc₁.1
  intro x s y hclose hdepth
  have htransfer := Total.projectionTransfer hp hG hres hchar D x s y hclose
    ((mem_lattice K).1 hdepth)
  have hcross : norm B₁ K (algebraMap B₂ K x) =
      algebraMap F B₁ (norm F B₂ x) :=
    Total.primeDiamond_norm_restrict B₁ B₂ hp htotal hdegree₁ D.degree_B₂ D.B₁_ne_B₂ x
  change norm B₁ K (algebraMap B₂ K x * algebraMap B₁ K s) -
    algebraMap F B₁ (norm F B₂ y) ∈ lattice B₁ (1 + (p : ℤ) * D.t₂) at htransfer
  rw [map_mul, LanglandsFirstMainLemma.norm_algebraMap, hdegree₁K, hcross] at htransfer
  exact htransfer

section CommonCoordinate

open Total
open scoped BigOperators

-- Reuse the existing kernel-checked calculations without changing their modules.
open private weighted_artinSchreier_norm weighted_teichmuller_sum
  weighted_sum_zero_units weighted_powerNorm_error from
  LanglandsSecondMainLemma.Odd.Total.WeightedDefect
open private norm_remainder_mem norm_basis_expansion coefficientDepth from
  LanglandsSecondMainLemma.Odd.Total.NormCoefficients
open private additiveConductor_of_normCharacterChart from
  LanglandsSecondMainLemma.Odd.Models.Setup

-- These are the canonical structures already used in the public statement.
attribute [local instance] Basic.intermediateFieldValuativeRel
  Basic.intermediateFieldTopology Basic.intermediateField_localField
  Basic.intermediateField_lowerValuativeExtension Basic.intermediateField_upperValuativeExtension

open private translatedNorm_residueDegree_tower from
  LanglandsSecondMainLemma.Odd.Total.TranslatedNorm

section CoordinateEstimates

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]
  {p : ℕ} {hp : p.Prime}
  {hG : Nonempty
    (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))}

omit [Module.Free F K] in
include hp hG in
/-- Degree, ramification, and cyclicity on both edges of an intermediate tower. -/
private theorem monomialPhase_tower (hres : residueDegree F K = 1)
    (E : IntermediateField F K) (hdegree : Module.finrank F E = p) :
    Module.finrank E K = p ∧ residueDegree F E = 1 ∧
      ramificationIndex F E = p ∧ ramificationIndex E K = p ∧
      CyclicPrimeExtension F E ∧ CyclicPrimeExtension E K := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hupper, hlowerCyclic, hupperCyclic⟩ :=
    Basic.intermediateField_tower_compatible hp hG E hdegree
  obtain ⟨hlowerRes, hupperRes⟩ := mul_eq_one.mp
    ((translatedNorm_residueDegree_tower F E K).trans hres)
  refine ⟨hupper, hlowerRes, ?_, ?_, hlowerCyclic, hupperCyclic⟩
  · simpa only [hlowerRes, mul_one, hdegree] using
      (finrank_eq_ramificationIndex_mul_residueDegree F E).symm
  · simpa only [hupperRes, mul_one, hupper] using
      (finrank_eq_ramificationIndex_mul_residueDegree E K).symm

variable (D : OddTotalBreakData (F := F) (K := K) hp hG)

/-- The prime has the required depth in either intermediate field. -/
private theorem monomialPhase_prime_mem (hres : residueDegree F K = 1)
    (E : IntermediateField F K) (hram : ramificationIndex E K = p) :
    (p : E) ∈ lattice E (((p : ℤ) - 1) * D.t₂) := by
  have hbound : algebraMap E K (p : E) ∈
      lattice K ((p * ((p - 1) * D.t₂) : ℕ) : ℤ) := by
    simpa only [map_natCast, mem_lattice, mul_assoc] using
      oddTotal_primeValuationBound hp hG hres D
  have h := monomialPhase_ceil_depth E K hp.pos hram hbound
  have hceil : (p * ((p - 1) * D.t₂)) ⌈/⌉ p = (p - 1) * D.t₂ :=
    smul_ceilDiv hp.pos _
  simpa only [hceil, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one] using h

local notation "B₁" => IntermediateField.fixedField D.H₁
local notation "B₂" => IntermediateField.fixedField D.H₂

/-- The two distinct prime-degree fields are disjoint and generate the top field. -/
private theorem monomialPhase_diamond [IsGalois F B₁] :
    IntermediateField.LinearDisjoint B₁ B₂ ∧ B₁ ⊔ B₂ = ⊤ := by
  have hinf : B₁ ⊓ B₂ = ⊥ := by
    have hdvd := IntermediateField.finrank_dvd_of_le_right
      (show B₁ ⊓ B₂ ≤ B₁ from inf_le_left)
    rw [D.degree_B₁] at hdvd
    rcases (Nat.dvd_prime hp).1 hdvd with hone | heq
    · exact IntermediateField.finrank_eq_one_iff.mp hone
    · exact (D.B₁_ne_B₂ ((IntermediateField.eq_of_le_of_finrank_eq inf_le_left
        (heq.trans D.degree_B₁.symm)).symm.trans
          (IntermediateField.eq_of_le_of_finrank_eq inf_le_right
            (heq.trans D.degree_B₂.symm)))).elim
  have hdis := IntermediateField.LinearDisjoint.of_inf_eq_bot hinf
  refine ⟨hdis, ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, htotal, _⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁
  apply IntermediateField.eq_of_le_of_finrank_eq le_top
  rw [hdis.finrank_sup, D.degree_B₁, D.degree_B₂]
  simpa using htotal.symm

variable [Fact p.Prime]

/-- The estimates supplied by `translatedNorm`, all for one coordinate. -/
private structure MonomialCoordinate (hchar : residueCharacteristic F = p) where
  Delta : K
  a : B₂
  root : Delta ^ p - Delta = algebraMap B₂ K a
  ord_Delta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ)
  ord_a : ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ)
  prime_not_dvd : ¬ p ∣ D.t
  adjoin_eq_top : Algebra.adjoin B₂ ({Delta} : Set K) = ⊤
  coefficient_bound : ∀ (theta : B₁) (Z : Fin p → B₂),
    algebraMap B₁ K theta = ∑ r : Fin p, algebraMap B₂ K (Z r) * Delta ^ (r : ℕ) →
    ∀ r : Fin p, ord B₁ theta + ((((r : ℕ) * D.t : ℕ) : ℤ) : WithTop ℤ) ≤
      ord B₂ (Z r)
  symmetric_bound : ∀ i : ℕ, 1 ≤ i → i < p →
    ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) ≤
      ord B₁ (elementarySymmetric B₁ K i Delta)
  scalar_bound : ((((p : ℤ) - 1) * D.delta : ℤ) : WithTop ℤ) ≤
    ord B₁ (-elementarySymmetric B₁ K (p - 1) Delta)
  translated_norm : ∀ (x : B₂) (v : ℤ) (k : ℕ),
    x ∈ lattice B₂ v → 1 ≤ k → k ≤ p →
    let R := (p : ℤ) * v - ((k : ℤ) - 1) * D.t
    let X := algebraMap F B₁ (norm F B₂ x)
    1 ≤ R →
    X * algebraMap F B₁ (trace F B₁ (norm B₁ K Delta ^ k)) -
      X * (∑ j : ZMod p,
        norm B₁ K (Delta + algebraMap F K (primeTeichmuller F p hchar j : F)) ^ k) ∈
          lattice B₁ ((p : ℤ) * D.t₂ + R)

/-- Construct the common coordinate from the genuine diamond. -/
private theorem monomialCoordinate_exists (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = p) : Nonempty (MonomialCoordinate D hchar) := by
  obtain ⟨Delta, a, hroot, hDelta, ha, hprime, hgen, hcoeff, _, _, hei, hsord,
    htranslate⟩ := translatedNorm hp hG hres hchar D
  exact ⟨⟨Delta, a, hroot, hDelta, ha, hprime, hgen, hcoeff, hei, hsord, htranslate⟩⟩

variable [IsGalois F (IntermediateField.fixedField D.H₁)]
  [PrimeCyclicExtension F (IntermediateField.fixedField D.H₂)]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- The weighted defect, with its full lower-norm weight and exceptional sign. -/
private theorem monomialPhase_weighted_estimate (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = p) (C : MonomialCoordinate D hchar) :
    ∀ (x : B₂) (j : ℕ) (R : ℤ), j ≤ p - 1 →
      (R : WithTop ℤ) ≤ ord K (algebraMap B₂ K x * C.Delta ^ j) → 1 ≤ R →
      algebraMap F B₁
        (weightedNormTraceDefect F B₁ B₂ K C.Delta (algebraMap B₂ K x * C.Delta ^ j)) -
        (if j = p - 2 then ((p : B₁) - 1) * algebraMap F B₁ (norm F B₂ x) *
          (1 - (-elementarySymmetric B₁ K (p - 1) C.Delta) ^ p) else 0) ∈
        lattice B₁ ((p : ℤ) * D.t₂ + R) := by
  classical
  obtain ⟨Delta, a, hroot, hDelta, ha, _, hgen, _, hei, _, htranslate⟩ := C
  obtain ⟨hdegreeUpper₁, _, hramF₁, hram₁K, _, hcyc₁K⟩ :=
    monomialPhase_tower (hp := hp) (hG := hG) hres B₁ D.degree_B₁
  obtain ⟨hdegreeUpper₂, hresF₂, _, hram₂K, _, _⟩ :=
    monomialPhase_tower (hp := hp) (hG := hG) hres B₂ D.degree_B₂
  letI : PrimeCyclicExtension B₁ K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension B₁ K hcyc₁K
  have hdegreeLower₂ := D.degree_B₂
  have hbreak₂ : PrimeCyclicExtension.IsLowerBreak F B₂ D.t₂ := D.B₂_breaks.1
  have hchar₁ : residueCharacteristic B₁ = p :=
    (residueCharacteristic_extension_eq F B₁).trans hchar
  have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
  have hp3 := D.odd_prime
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hpval := monomialPhase_prime_mem D hres B₁ hram₁K
  obtain ⟨hdis, hsup⟩ := monomialPhase_diamond D
  have hnorm := weighted_artinSchreier_norm hp3 hodd hdegreeUpper₂ Delta a hroot hgen
  intro x j R hj hR hRpos
  by_cases hxne : x = 0
  · subst x
    simp [weightedNormTraceDefect]
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff B₂).2 hxne)
  have hx : x ∈ lattice B₂ v := (mem_lattice B₂).2 (le_of_eq hv)
  have hReq : R ≤ (p : ℤ) * v - (j : ℤ) * D.t := by
    rw [ord_mul, ord_algebraMap, hram₂K, ord_pow, hDelta, ← hv,
      ← WithTop.coe_nsmul, ← WithTop.coe_nsmul, ← WithTop.coe_add] at hR
    have h := WithTop.coe_le_coe.mp hR
    simp only [nsmul_eq_mul] at h
    linarith
  let r : ℤ := (p : ℤ) * v - (j : ℤ) * D.t
  apply lattice_antitone B₁ (show (p : ℤ) * D.t₂ + R ≤ (p : ℤ) * D.t₂ + r by
    dsimp only [r]; omega)
  have hrpos : 1 ≤ r := hRpos.trans hReq
  let k := j + 1
  have hk1 : 1 ≤ k := by dsimp [k]; omega
  have hk : k ≤ p := by dsimp [k]; omega
  have hdepth : (p : ℤ) * v - ((k : ℤ) - 1) * D.t = r := by
    dsimp only [k, r]; push_cast; ring
  let weight : B₁ := algebraMap F B₁ (norm F B₂ x)
  have hX : weight ∈ lattice B₁ (r + ((k : ℤ) - 1) * D.t) := by
    have hXd : r + ((k : ℤ) - 1) * D.t = (p : ℤ) * v := by linarith
    rw [hXd, mem_lattice, ord_algebraMap, hramF₁, ord_norm, hresF₂, one_nsmul]
    simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using
      nsmul_le_nsmul_right ((mem_lattice B₂).1 hx) p
  have hfiltered := filteredCoefficients B₁ K (by omega) hchar₁ hdegreeUpper₁ hram₁K
    Delta D.t D.delta r (by positivity) (by positivity) hDelta
    (by intro i hi hip; simpa only [mem_lattice, ← ht₂] using hei i hi hip)
    (by simpa only [← ht₂] using hpval) hk1 hk weight hX
  have hsum :
      (∑ z : ZMod p, norm B₁ K (Delta + algebraMap F K
        (primeTeichmuller F p hchar z : F)) ^ k) =
      norm B₁ K Delta ^ k + ∑ z : (ZMod p)ˣ, norm B₁ K
        (Delta + algebraMap B₁ K (primeTeichmuller B₁ p hchar₁ z)) ^ k := by
    have h := weighted_teichmuller_sum F B₁ hchar hchar₁
      (fun c => norm B₁ K (Delta + algebraMap B₁ K c) ^ k)
    simp only [← IsScalarTower.algebraMap_apply F B₁ K] at h
    rw [h, weighted_sum_zero_units]
    simp only [map_zero, Subring.coe_zero, add_zero]
  have htrace : trace B₁ K ((Delta ^ p - Delta) ^ k) =
      algebraMap F B₁ (trace F B₂ (a ^ k)) := by
    rw [hroot, ← map_pow]
    exact hdis.trace_algebraMap hsup _
  have htrans := htranslate x v k hx hk1 hk (by simpa only [hdepth] using hrpos)
  rw [hdepth, hsum] at htrans
  rw [← ht₂, htrace] at hfiltered
  have hmain : weight * (algebraMap F B₁ (trace F B₁ (norm B₁ K Delta ^ k)) -
      algebraMap F B₁ (trace F B₂ (a ^ k))) -
      (if k = p - 1 then ((p : B₁) - 1) * weight *
        (1 + elementarySymmetric B₁ K (p - 1) Delta ^ p) else 0) ∈
        lattice B₁ ((p : ℤ) * D.t₂ + r) := by
    convert (lattice B₁ _).add_mem htrans hfiltered using 1
    dsimp only [weight]
    ring
  have herr := weighted_powerNorm_error F B₁ B₂ hp3 D.t_le_t₂
    (lt_of_lt_of_le D.t_pos D.t_le_t₂) hdegreeLower₂ hramF₁ hresF₂ hbreak₂
    x a v hx ((mem_lattice B₂).2 ha.ge) k
  rw [hdepth] at herr
  have hnormcross : norm B₁ K (algebraMap B₂ K x) = weight := hdis.norm_algebraMap hsup x
  have hlin₁ : trace F B₁ (weight * norm B₁ K Delta ^ k) =
      norm F B₂ x * trace F B₁ (norm B₁ K Delta ^ k) := by
    simpa only [weight, Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self_apply] using
      (trace F B₁).map_smul (norm F B₂ x) (norm B₁ K Delta ^ k)
  have hlin₂ : trace F B₂ (algebraMap F B₂ (norm F B₂ x) * a ^ k) =
      norm F B₂ x * trace F B₂ (a ^ k) := by
    simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self_apply] using
      (trace F B₂).map_smul (norm F B₂ x) (a ^ k)
  have hdef : algebraMap F B₁
      (weightedNormTraceDefect F B₁ B₂ K Delta (algebraMap B₂ K x * Delta ^ j)) =
      weight * (algebraMap F B₁ (trace F B₁ (norm B₁ K Delta ^ k)) -
        algebraMap F B₁ (trace F B₂ (a ^ k))) +
      algebraMap F B₁ (trace F B₂ ((algebraMap F B₂ (norm F B₂ x) - x ^ p) * a ^ k)) := by
    have hz : Delta * (algebraMap B₂ K x * Delta ^ j) = algebraMap B₂ K x * Delta ^ k := by
      dsimp only [k]; rw [pow_succ]; ring
    dsimp only [weightedNormTraceDefect]
    simp only [hz, map_mul, map_pow, hnormcross,
      LanglandsFirstMainLemma.norm_algebraMap, hdegreeUpper₂, hnorm, hlin₁]
    simp only [sub_mul, map_sub, hlin₂, map_mul]
    dsimp only [weight]
    ring
  have hex : (k = p - 1) ↔ (j = p - 2) := by dsimp only [k]; omega
  have hsign : 1 + elementarySymmetric B₁ K (p - 1) Delta ^ p =
      1 - (-elementarySymmetric B₁ K (p - 1) Delta) ^ p := by
    rw [hodd.neg_pow]; ring
  rw [hdef]
  simp only [hex, hsign] at hmain
  convert (lattice B₁ _).add_mem hmain herr using 1
  dsimp only [weight]
  ring

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
omit [IsGalois F (IntermediateField.fixedField D.H₁)]
  [PrimeCyclicExtension F (IntermediateField.fixedField D.H₂)] in
/-- Extract the second defect and its exceptional projection in the same power basis. -/
private theorem monomialPhase_second_estimates (hres : residueDegree F K = 1)
    {hchar : residueCharacteristic F = p} (C : MonomialCoordinate D hchar) :
    ∃ omega : B₂,
      (∀ (x : B₂) (j : ℕ), j < p → j ≠ p - 2 →
        algebraMap B₂ K x * C.Delta ^ j ∈ lattice K (1 + (D.delta : ℤ)) →
        trace B₂ K ((algebraMap B₁ K (norm B₁ K C.Delta) - algebraMap B₂ K C.a) *
          (algebraMap B₂ K x * C.Delta ^ j)) ∈ lattice B₂ (1 + (D.t₂ : ℤ))) ∧
      (∀ x : B₂,
        algebraMap B₂ K x * C.Delta ^ (p - 2) ∈ lattice K (1 + (D.delta : ℤ)) →
        trace B₂ K ((algebraMap B₁ K (norm B₁ K C.Delta) - algebraMap B₂ K C.a) *
          (algebraMap B₂ K x * C.Delta ^ (p - 2))) = x * (omega - 1) ∧
        algebraMap B₂ K (x * omega) - algebraMap B₂ K x *
          algebraMap B₁ K (-elementarySymmetric B₁ K (p - 1) C.Delta) ∈
            lattice K (1 + (p : ℤ) * D.t₂)) := by
  classical
  obtain ⟨Delta, a, hroot, hDelta, ha, _, hgen, hcoeff, hei, hsord, _⟩ := C
  obtain ⟨hdegreeUpper₁, _, _, _, _, _⟩ :=
    monomialPhase_tower (hp := hp) (hG := hG) hres B₁ D.degree_B₁
  obtain ⟨hdegreeUpper₂, _, _, hram₂K, _, _⟩ :=
    monomialPhase_tower (hp := hp) (hG := hG) hres B₂ D.degree_B₂
  have hodd : Odd p := hp.odd_of_ne_two (by have := D.odd_prime; omega)
  let pb : PowerBasis B₂ K :=
    PowerBasis.ofAdjoinEqTop (IsAlgebraic.of_finite B₂ Delta).isIntegral hgen
  have hpbgen : pb.gen = Delta := PowerBasis.ofAdjoinEqTop_gen _ _
  have hpbdim : pb.dim = p := by rw [← pb.finrank]; exact hdegreeUpper₂
  let Z (theta : B₁) (k : Fin p) : B₂ :=
    pb.basis.repr (algebraMap B₁ K theta) (Fin.cast hpbdim.symm k)
  have hZexp (theta : B₁) : algebraMap B₁ K theta =
      ∑ k : Fin p, algebraMap B₂ K (Z theta k) * Delta ^ (k : ℕ) := by
    simpa only [Z, hpbgen] using norm_basis_expansion pb hpbdim (algebraMap B₁ K theta)
  have hZbound (theta : B₁) (k : Fin pb.dim) :
      ord B₁ theta + (((k : ℕ) * (D.t : ℤ) : ℤ) : WithTop ℤ) ≤
        ord B₂ (pb.basis.repr (algebraMap B₁ K theta) k) := by
    have h := hcoeff theta (Z theta) (hZexp theta) (Fin.cast hpbdim k)
    simpa only [Z, Fin.val_cast, Fin.cast_cast, Fin.cast_eq_self, Nat.cast_mul] using h
  let Y := Z (norm B₁ K Delta)
  let s := Z (-elementarySymmetric B₁ K (p - 1) Delta)
  have hrem (l : Fin p) :
      Y l - (if (l : ℕ) = 0 then a else 0) -
        (if (l : ℕ) = 1 then 1 - s ⟨0, hp.pos⟩ else 0) ∈
      lattice B₂ (coefficientDepth p D.t (((p : ℤ) - 1) * D.t₂) l) := by
    have h := norm_remainder_mem B₁ B₂ K pb hodd
      D.odd_prime hpbdim hdegreeUpper₁ a (by simpa [hpbgen] using hroot)
      D.t (((p : ℤ) - 1) * D.t₂) (by positivity) (by rw [mem_lattice, ha])
      hZbound (by simpa only [hpbgen] using hei) (Fin.cast hpbdim.symm l)
    simp only [hpbgen, Fin.val_cast] at h
    convert h using 1
    simp only [Y, s, Z, Fin.cast_mk, map_neg, Finsupp.neg_apply, sub_neg_eq_add]
  have hYhigh (l : Fin p) (hl : 2 ≤ (l : ℕ)) :
      Y l ∈ lattice B₂ (((p : ℤ) - 1) * D.t₂ - ((p : ℤ) - l) * D.t) := by
    simpa [coefficientDepth, show (l : ℕ) ≠ 0 by omega,
      show (l : ℕ) ≠ 1 by omega] using hrem l
  have hYzero : Y ⟨0, hp.pos⟩ - a ∈
      lattice B₂ (((p : ℤ) - 1) * D.t₂ - D.t) := by
    simpa [coefficientDepth] using hrem ⟨0, hp.pos⟩
  let error := Y ⟨1, hp.one_lt⟩ - (1 - s ⟨0, hp.pos⟩)
  have hYone : Y ⟨1, hp.one_lt⟩ = 1 - s ⟨0, hp.pos⟩ + error := by
    dsimp only [error]; ring
  have herror : error ∈ lattice B₂ (((p : ℤ) - 1) * D.t₂) := by
    simpa [coefficientDepth, error] using hrem ⟨1, hp.one_lt⟩
  have hpval₂ := monomialPhase_prime_mem D hres B₂ hram₂K
  have hscoeff (l : Fin p) :
      s l ∈ lattice B₂ (((p : ℤ) - 1) * D.delta + (l : ℤ) * D.t) := by
    rw [mem_lattice, WithTop.coe_add]
    have h := add_le_add_right hsord ((((l : ℕ) * D.t : ℕ) : ℤ) : WithTop ℤ)
    have h' := h.trans (by simpa only [add_comm] using hcoeff _ s (hZexp _) l)
    simpa only [Nat.cast_mul, add_comm] using h'
  have hcalc := secondDefect_of_coefficients pb D.odd_prime hpbdim hram₂K
    a (by simpa only [hpbgen] using hroot) D.t D.t₂ D.delta
    (by positivity) (by positivity) (by exact_mod_cast D.t₂_eq)
    (by simpa only [hpbgen] using hDelta) (by rw [mem_lattice, ha]) hpval₂
    (algebraMap B₁ K (norm B₁ K Delta))
    (algebraMap B₁ K (-elementarySymmetric B₁ K (p - 1) Delta)) Y s
    (by simpa only [hpbgen] using hZexp (norm B₁ K Delta))
    (by simpa only [hpbgen] using hZexp (-elementarySymmetric B₁ K (p - 1) Delta))
    hscoeff hYhigh hYzero error hYone herror
  dsimp only at hcalc
  simp only [hpbgen] at hcalc
  let omega : B₂ := 1 + ((p - 1 : ℕ) : B₂) * Y ⟨1, hp.one_lt⟩ +
    (p : B₂) * a * Y ⟨2, D.odd_prime⟩
  refine ⟨omega, hcalc.1, ?_⟩
  intro x hx
  simpa only [map_mul] using hcalc.2 x hx

omit [Module.Free F K] [Fact p.Prime]
  [IsGalois F (IntermediateField.fixedField D.H₁)] in
/-- Trace preserves the conductor lattice at the lower break. -/
private theorem monomialPhase_trace_mem (hres : residueDegree F K = 1)
    (z : B₂) (hz : z ∈ lattice B₂ (1 + (D.t₂ : ℤ))) :
    trace F B₂ z ∈ lattice F (1 + (D.t₂ : ℤ)) := by
  obtain ⟨_, hresF₂, hramF₂, _, _, _⟩ :=
    monomialPhase_tower (hp := hp) (hG := hG) hres B₂ D.degree_B₂
  have hdegreeLower₂ := D.degree_B₂
  have hbreak₂ : PrimeCyclicExtension.IsLowerBreak F B₂ D.t₂ := D.B₂_breaks.1
  have hdiff₂ : (differentExponent F B₂ : ℤ) =
      ((p : ℤ) - 1) * ((D.t₂ : ℤ) + 1) := by
    obtain ⟨pi, hpi, hgen⟩ :=
      exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one F B₂ hresF₂
    rw [differentExponent_eq F B₂ hbreak₂ pi hpi hgen, hdegreeLower₂]
    push_cast [Nat.cast_sub hp.one_le]
    rfl
  have hmem : trace F B₂ z ∈ Submodule.map
      ((trace F B₂).restrictScalars (ringOfIntegers F))
      ((lattice B₂ (1 + (D.t₂ : ℤ))).restrictScalars (ringOfIntegers F)) :=
    Submodule.mem_map.mpr ⟨z, hz, rfl⟩
  rw [Local.traceIdeal_eq_fml F B₂ hresF₂, hdiff₂, hramF₂,
    show 1 + (D.t₂ : ℤ) + ((p : ℤ) - 1) * (D.t₂ + 1) =
      (1 + (D.t₂ : ℤ)) * p by ring,
    Int.mul_ediv_cancel _ (by exact_mod_cast hp.ne_zero)] at hmem
  exact hmem

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- Cancel the phase using the conductor ideal and, at the exceptional exponent,
whole-domain norm conversion and projection transfer. -/
private theorem monomialPhase_coordinate_phase (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = p) (C : MonomialCoordinate D hchar) :
    ∀ (c : ℕ) (_hc : c = (D.t₂ + 1) ⌈/⌉ p) (hcpos : 0 < c)
      (tau : NormCharacter F B₂) (_htau : tau ≠ 1) (Psi : ContinuousAddChar F),
      (∀ z : lattice F (c : ℤ),
        tau.1 (positiveUnitOfLattice F hcpos (-z)) =
          Psi (Odd.truncatedLog p (z : F))) →
      ∀ (x : B₂) (j : ℕ), j < p →
        algebraMap B₂ K x * C.Delta ^ j ∈ lattice K (firstModelDepth D : ℤ) →
        let z := algebraMap B₂ K x * C.Delta ^ j
        Psi ((trace F B₁ (norm B₁ K C.Delta * trace B₁ K z) -
          trace F B₂ (C.a * trace B₂ K z)) +
          weightedNormTraceDefect F B₁ B₂ K C.Delta z) = 1 := by
  classical
  obtain ⟨_, _, hramF₁, hram₁K, _, _⟩ :=
    monomialPhase_tower (hp := hp) (hG := hG) hres B₁ D.degree_B₁
  obtain ⟨_, hresF₂, _, hram₂K, _, _⟩ :=
    monomialPhase_tower (hp := hp) (hG := hG) hres B₂ D.degree_B₂
  have hdegreeLower₂ := D.degree_B₂
  have hbreak₂ : PrimeCyclicExtension.IsLowerBreak F B₂ D.t₂ := D.B₂_breaks.1
  have hp3 := D.odd_prime
  have hpval := monomialPhase_prime_mem D hres B₁ hram₁K
  have hweighted := monomialPhase_weighted_estimate D hres hchar C
  obtain ⟨omega, hcalc⟩ := monomialPhase_second_estimates D hres C
  obtain ⟨Delta, a, _, hDelta, _, _, _, _, _, hsord, _⟩ := C
  dsimp only at hweighted hcalc ⊢
  intro c hc hcpos tau htau Psi hchart x j hj hx
  have ht₂pos : 0 < D.t₂ := D.t_pos.trans_le D.t_le_t₂
  have hPsi := additiveConductor_of_normCharacterChart F B₂ hp hp3 hchar
    hdegreeLower₂ hbreak₂ ht₂pos hresF₂ hc hcpos tau htau Psi hchart
  have hq : (1 + (D.delta : ℤ)) ≤ (firstModelDepth D : ℤ) := by
    have h := (monomialPhase_depth_bounds (δ := D.delta) hp3 D.t_pos).1
    exact_mod_cast (show 1 + D.delta ≤ firstModelDepth D by
      simpa only [firstModelDepth, firstModelConductor, D.tPrime_eq] using h)
  have hxSmall : algebraMap B₂ K x * Delta ^ j ∈ lattice K (1 + (D.delta : ℤ)) :=
    lattice_antitone K hq hx
  have hw := hweighted x j 1 (by omega)
    ((WithTop.coe_le_coe.mpr (show (1 : ℤ) ≤ firstModelDepth D by omega)).trans
      ((mem_lattice K).1 hx)) le_rfl
  by_cases hjex : j = p - 2
  · subst j
    obtain ⟨hg, hclose⟩ := hcalc.2 x hxSmall
    have hdepth := monomialPhase_exceptional_depths B₁ B₂ K hp3 D.t_pos
      hram₁K hram₂K hDelta ((mem_lattice B₁).2 hsord)
      (by simpa only [firstModelDepth, firstModelConductor, D.tPrime_eq] using hx)
    have hxK : algebraMap B₂ K x ∈ lattice K ((D.t₂ + 1 : ℕ) : ℤ) := by
      simpa only [D.t₂_eq, Nat.cast_add, Nat.cast_one] using hdepth.1
    have hsint : -elementarySymmetric B₁ K (p - 1) Delta ∈ lattice B₁ 0 :=
      lattice_antitone B₁
        (mul_nonneg (by omega) (Int.natCast_nonneg _)) ((mem_lattice B₁).2 hsord)
    have htransferFn := monomialPhase_projectionTransfer hp hG hres hchar D
    dsimp only [OddTotalBreakData.B₁, OddTotalBreakData.B₂] at htransferFn
    have htransfer := htransferFn x
      (-elementarySymmetric B₁ K (p - 1) Delta) (x * omega)
      (by simpa only [neg_sub] using neg_mem_lattice K hclose)
      (by simpa only [D.t₂_eq, Nat.cast_add] using hdepth.2.2)
    apply monomialPhase_exceptional_of_estimates F B₁ B₂ K hp3 ht₂pos
      hdegreeLower₂ hbreak₂ hresF₂ hchar hramF₁ hram₁K hram₂K hc hcpos
      tau htau Psi hPsi hchart x (x * omega)
      (-elementarySymmetric B₁ K (p - 1) Delta) _ _ hxK hsint hpval hclose
    · rw [secondDefect_trace_pairing F B₁ B₂ K, hg]
      congr 1
      ring
    · simpa only [if_pos rfl, ite_true, add_comm] using hw
    · exact htransfer
  · have hg := monomialPhase_trace_mem D hres _ (hcalc.1 x j hj hjex hxSmall)
    apply monomialPhase_nonexceptional F B₁ hp.pos hramF₁ Psi hPsi
    · rw [secondDefect_trace_pairing F B₁ B₂ K]
      simpa only [Nat.cast_add, Nat.cast_one, add_comm] using hg
    · simpa only [if_neg hjex, sub_zero, add_comm] using hw

end CoordinateEstimates

/-- **Paper 8.2 (`O:M:monophase`).** The genuine odd totally ramified diamond
constructs one exact Artin--Schreier coordinate for which every monomial in
the full model lattice has trivial trace--norm defect phase. The assertion
holds for every nontrivial actual norm character and its whole-domain
truncated-log chart. The additive conductor is derived from that chart.
No defect estimate, coordinate compatibility, or phase cancellation is
assumed. The same coordinate works for all such characters. -/
theorem monomialPhase
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (D : OddTotalBreakData (F := F) (K := K) hp hG) :
    let B₁ := D.B₁
    let B₂ := D.B₂
    letI := Basic.intermediateFieldValuativeRel B₁
    letI := Basic.intermediateFieldTopology B₁
    letI := Basic.intermediateField_localField B₁
    letI := Basic.intermediateFieldValuativeRel B₂
    letI := Basic.intermediateFieldTopology B₂
    letI := Basic.intermediateField_localField B₂
    letI := Basic.intermediateField_lowerValuativeExtension B₂
    ∃ (Delta : K) (a : B₂),
      Delta ^ p - Delta = algebraMap B₂ K a ∧
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ¬ p ∣ D.t ∧ Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ ∧
      norm B₂ K Delta = a ∧
      ∀ (c : ℕ) (_hc : c = (D.t₂ + 1) ⌈/⌉ p) (hcpos : 0 < c)
        (tau : NormCharacter F B₂) (_htau : tau ≠ 1)
        (Psi : ContinuousAddChar F),
        (∀ z : lattice F (c : ℤ),
          tau.1 (positiveUnitOfLattice F hcpos (-z)) =
            Psi (Odd.truncatedLog p (z : F))) →
        ∀ (x : B₂) (j : ℕ), j < p →
          algebraMap B₂ K x * Delta ^ j ∈ lattice K (firstModelDepth D : ℤ) →
          let z := algebraMap B₂ K x * Delta ^ j
          Psi ((trace F B₁ (norm B₁ K Delta * trace B₁ K z) -
            trace F B₂ (a * trace B₂ K z)) +
            weightedNormTraceDefect F B₁ B₂ K Delta z) = 1 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨_, _, _, _, hcycF₁, _⟩ :=
    monomialPhase_tower (hp := hp) (hG := hG) hres D.B₁ D.degree_B₁
  obtain ⟨hdegreeUpper₂, _, _, _, hcycF₂, _⟩ :=
    monomialPhase_tower (hp := hp) (hG := hG) hres D.B₂ D.degree_B₂
  letI : IsGalois F (IntermediateField.fixedField D.H₁) := hcycF₁.1
  letI : PrimeCyclicExtension F (IntermediateField.fixedField D.H₂) :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F D.B₂ hcycF₂
  obtain ⟨C⟩ := monomialCoordinate_exists D hres hchar
  have hodd : Odd p := hp.odd_of_ne_two (by have := D.odd_prime; omega)
  refine ⟨C.Delta, C.a, C.root, C.ord_Delta, C.ord_a, C.prime_not_dvd,
    C.adjoin_eq_top, ?_, monomialPhase_coordinate_phase D hres hchar C⟩
  exact weighted_artinSchreier_norm D.odd_prime hodd hdegreeUpper₂
    C.Delta C.a C.root C.adjoin_eq_top

end CommonCoordinate

end

end LanglandsSecondMainLemma.Odd.Models
