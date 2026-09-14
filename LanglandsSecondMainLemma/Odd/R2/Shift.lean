import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Odd.R2.Commutator

/-!
# Odd / R2 / Shift

Paper: Lemma 8.10, `O:R:shift`, with the normalization at lines 2782--2810.

The norm polynomial and the actual translated root are estimated separately.
Both errors have the stronger depth `t + (p-1)*delta`. The final modulus is
exactly the integer `R = T' - q`, including the ceiling in `q`.

The translating upper automorphism is constructed for the supplied exact
coordinate, so the norm, signed symmetric coefficient, and commutator all use
that same coordinate. The mixed-characteristic correction is bounded using
FML's trace ideal and strong symmetric estimates; it is zero in equal
characteristic. No character unitarity or extra norm equation is used.
-/

namespace LanglandsSecondMainLemma.Odd.R2

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The trace coefficient of the actual unit correction has sufficient depth.
This integer calculation includes the smallest odd prime. -/
private theorem shift_trace_depth (p : ℕ) (hp : 3 ≤ p)
    (t d V : ℤ) (ht : 0 ≤ t) (hd : 0 ≤ d)
    (hV : (p : ℤ) * ((p : ℤ) - 1) * (t + d) ≤ V) :
    2 * t + ((p : ℤ) - 1) * d ≤
      (V - ((p : ℤ) - 2) * t +
        ((p : ℤ) - 1) * (t + (p : ℤ) * d + 1)) / (p : ℤ) := by
  have hpZ : (3 : ℤ) ≤ p := by exact_mod_cast hp
  rw [Int.le_ediv_iff_mul_le (by omega : (0 : ℤ) < p)]
  have hpt := mul_nonneg (mul_nonneg (show (0 : ℤ) ≤ (p : ℤ) - 3 by omega)
    (show (0 : ℤ) ≤ p by omega)) ht
  have hpd := mul_nonneg (mul_nonneg (show (0 : ℤ) ≤ p by omega)
    (show (0 : ℤ) ≤ (p : ℤ) - 1 by omega)) hd
  nlinarith only [hV, hpt, hpd, ht, hpZ]

/-- The complete norm of a unit with the divided Hensel depth. The trace
is estimated explicitly, and the higher coefficients include the endpoint. -/
private theorem shift_unit_norm_mem
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    [Module.Free E L] [Module.Finite E L] [IsGalois E L]
    {p : ℕ} (hp : p.Prime) (hpodd : 2 < p)
    (t d : ℕ) (ht : 0 < t) (V : ℤ)
    (hV : (p : ℤ) * ((p : ℤ) - 1) * ((t : ℤ) + d) ≤ V)
    (hchar : residueCharacteristic E = p)
    (hdegree : Module.finrank E L = p) (hram : ramificationIndex E L = p)
    (htrace : TraceIdealLowerBound E L p
      (((p : ℤ) - 1) * ((t : ℤ) + (p : ℤ) * d + 1)))
    (u : L) (hu : u ∈ lattice L (V - ((p : ℤ) - 2) * t)) :
    norm E L (1 + u) - 1 ∈ lattice E (2 * (t : ℤ) + ((p : ℤ) - 1) * d) := by
  have htr : trace E L u ∈ lattice E (2 * (t : ℤ) + ((p : ℤ) - 1) * d) := by
    rw [mem_lattice]
    exact (WithTop.coe_le_coe.mpr
      (shift_trace_depth p (by omega) t d V (by positivity) (by positivity) hV)).trans
        (htrace _ u ((mem_lattice L).1 hu))
  have hhigh := Total.translatedUnit_norm_linear E L hp hpodd t d ht V hV
    hchar hdegree hram htrace u hu
  have hbound : 2 * (t : ℤ) + ((p : ℤ) - 1) * d ≤
      (p : ℤ) * ((t : ℤ) + d) + t := by
    have hpZ : (3 : ℤ) ≤ p := by exact_mod_cast hpodd
    have := mul_nonneg (show (0 : ℤ) ≤ (p : ℤ) - 1 by omega)
      (show (0 : ℤ) ≤ t by positivity)
    nlinarith [show (0 : ℤ) ≤ d by positivity]
  have h := (lattice E _).add_mem (lattice_antitone E hbound hhigh) htr
  simpa only [sub_add_cancel] using h

/-- Split the exact norm polynomial at its last two coefficients. -/
private theorem shift_norm_polynomial
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    [Module.Free E L] [Module.Finite E L]
    {p : ℕ} (hp : 2 ≤ p) (hdegree : Module.finrank E L = p) (Delta : L) :
    norm E L (Delta + 1) - norm E L Delta -
        (1 - (-elementarySymmetric E L (p - 1) Delta)) =
      ∑ j ∈ Finset.range (p - 2), elementarySymmetric E L (j + 1) Delta := by
  have hsplit : p = (p - 2) + 1 + 1 := by omega
  have hend : elementarySymmetric E L p Delta = norm E L Delta := by
    rw [← hdegree, elementarySymmetric_finrank]
  rw [add_comm Delta 1, norm_one_add_eq_one_add_sum_elementarySymmetric, hdegree]
  conv_lhs => arg 1; arg 1; arg 2; rw [hsplit, Finset.sum_range_succ, Finset.sum_range_succ]
  rw [show p - 2 + 1 = p - 1 by omega, show p - 1 + 1 = p by omega, hend]
  ring

section Diamond

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]
  {p : ℕ} (hp : p.Prime)
  (hG : Nonempty
    (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
  (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
  (D : Total.OddTotalBreakData (F := F) (K := K) hp hG)

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

local notation "B₁" => D.B₁
local notation "B₂" => D.B₂

local instance : PrimeCyclicExtension F B₁ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₁
    (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.2.2.2.1
local instance : PrimeCyclicExtension B₁ K :=
  PrimeCyclicExtension.ofCyclicPrimeExtension B₁ K
    (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.2.2.2.2

open private realization_tower_data from LanglandsSecondMainLemma.Odd.Models.Realization
open private translated_root_center_ord from LanglandsSecondMainLemma.Odd.Total.TranslatedNorm

include hp hG D

omit [Module.Free F K] [IsGalois F K] in
/-- The paper's exponent is computed in the integers, with no truncated
subtraction. The last bound is the precision supplied by the norm expansion. -/
theorem shift_depth :
    ((D.tPrime + 1 : ℕ) : ℤ) - ((D.delta + (D.t + 1) ⌈/⌉ p : ℕ) : ℤ) =
      (D.t : ℤ) + 1 - ((D.t + 1) ⌈/⌉ p : ℕ) + ((p : ℤ) - 1) * D.delta ∧
    ((D.tPrime + 1 : ℕ) : ℤ) - ((D.delta + (D.t + 1) ⌈/⌉ p : ℕ) : ℤ) ≤
      (D.t : ℤ) + ((p : ℤ) - 1) * D.delta := by
  have hc : 0 < (D.t + 1) ⌈/⌉ p := by
    have h : D.t + 1 ≤ p * ((D.t + 1) ⌈/⌉ p) := le_smul_ceilDiv hp.pos
    by_contra hn
    have hz : (D.t + 1) ⌈/⌉ p = 0 := by omega
    rw [hz, mul_zero] at h
    omega
  have heq : ((D.tPrime + 1 : ℕ) : ℤ) - ((D.delta + (D.t + 1) ⌈/⌉ p : ℕ) : ℤ) =
      (D.t : ℤ) + 1 - ((D.t + 1) ⌈/⌉ p : ℕ) + ((p : ℤ) - 1) * D.delta := by
    rw [D.tPrime_eq]
    push_cast
    ring
  refine ⟨heq, ?_⟩
  rw [heq]
  have hcZ : (1 : ℤ) ≤ ((D.t + 1) ⌈/⌉ p : ℕ) := by exact_mod_cast hc
  linarith

include hres hchar

/-- The formal translation of the same coordinate has the signed shift
`1-s`; the intermediate coefficients have at least depth `t+(p-1)*delta`. -/
theorem shift_formal_translation
    (Delta : K) (a : B₂)
    (hroot : Delta ^ p - Delta = algebraMap B₂ K a)
    (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ D.t) (hgen : Algebra.adjoin B₂ ({Delta} : Set K) = ⊤) :
    norm B₁ K (Delta + 1) - norm B₁ K Delta -
        (1 - (-elementarySymmetric B₁ K (p - 1) Delta)) ∈
      lattice B₁ ((D.t : ℤ) + ((p : ℤ) - 1) * D.delta) := by
  obtain ⟨hdegree, _, _, _, _⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  obtain ⟨_, _, hsym, _⟩ := Models.realization_twistedEstimates_of_coordinate
    hp hG hres hchar D Delta a hroot hDelta hprime hgen
  rw [shift_norm_polynomial B₁ K hp.two_le hdegree Delta]
  apply sum_mem_lattice B₁
  intro j hj
  have hjlt := Finset.mem_range.mp hj
  have h := hsym (j + 1) (by omega) (by omega)
  rw [mem_lattice]
  apply (WithTop.coe_le_coe.mpr ?_).trans h
  have hjZ : (j : ℤ) + 1 ≤ (p : ℤ) - 2 := by omega
  have hmul := mul_nonneg (sub_nonneg.mpr hjZ) (show (0 : ℤ) ≤ D.t by positivity)
  rw [D.t₂_eq]
  push_cast
  nlinarith only [hmul]

/-- Lemma 8.10 (`O:R:shift`) for the genuine normalized coordinate.
The upper automorphism near `Delta+1` is constructed, and `sigma` in the
congruence is its actual restriction to `B₁`. This constructor works for
any supplied coordinate, in particular the one returned by
`commutator_realization`. The affine term is `1-s`, with
`s = -elementarySymmetric B₁ K (p-1) Delta`. -/
theorem shift
    (Delta : K) (a : B₂)
    (hroot : Delta ^ p - Delta = algebraMap B₂ K a)
    (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ D.t) (hgen : Algebra.adjoin B₂ ({Delta} : Set K) = ⊤) :
    ∃ sigma : Gal(K/B₂),
      sigma Delta - (Delta + 1) ∈ lattice K 1 ∧
      let sigma₁ := IntermediateField.restrictRestrictAlgEquivMapHom F B₁ B₂ K sigma
      sigma₁ (norm B₁ K Delta) - norm B₁ K Delta -
          (1 - (-elementarySymmetric B₁ K (p - 1) Delta)) ∈
        lattice B₁ (((D.tPrime + 1 : ℕ) : ℤ) -
          ((D.delta + (D.t + 1) ⌈/⌉ p : ℕ) : ℤ)) := by
  obtain ⟨hdegree, _, hres₁K, _, hram₁K⟩ :=
    realization_tower_data hp hG hres B₁ D.degree_B₁
  have ht : (0 : ℤ) < D.t := by exact_mod_cast D.t_pos
  have hcenter : ord K (Delta + 1) = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) :=
    translated_root_center_ord K (by have := hp.one_lt; omega : 0 < p - 1) ht Delta 1 hDelta (by simp)
  have hcenterNe : Delta + 1 ≠ 0 := (ord_ne_top_iff K).1 (by
    rw [hcenter]; exact WithTop.coe_ne_top)
  obtain ⟨sigma, eta, hsigma, _, _, hnorm, hcases⟩ :=
    Total.translatedRoot_actualUnitCorrections_of_coordinate hp hG hres hchar D
      Delta a hroot hDelta hgen 1 (by simp)
  simp only [map_one] at hsigma hnorm hcases
  let u := Total.translatedRootUnit Delta 1 eta
  have heta : eta = (Delta + 1) * u := by
    dsimp only [u, Total.translatedRootUnit]
    rw [mul_div_cancel₀ _ hcenterNe]
  have hunit : eta ∈ lattice K 1 ∧
      norm B₁ K (1 + u) - 1 ∈
        lattice B₁ (2 * (D.t : ℤ) + ((p : ℤ) - 1) * D.delta) := by
    rcases hcases with ⟨_, hu⟩ | ⟨_, V, hV, hu, _, _⟩
    · change u = 0 at hu
      rw [heta, hu]
      simp
    · have hVbound := Total.oddTotal_primeValuationBound hp hG hres D
      rw [hV, WithTop.coe_le_coe] at hVbound
      push_cast [Nat.cast_sub hp.one_le] at hVbound
      rw [D.t₂_eq, Nat.cast_add] at hVbound
      have hhigh := (Total.translatedNorm_higher_depth p 2 (by have := D.odd_prime; omega)
        (by omega) D.t D.delta V (by positivity) (by positivity) hVbound).1
      have hetaMem : eta ∈ lattice K
          (-(D.t : ℤ) + (V - ((p : ℤ) - 2) * D.t)) := by
        rw [heta]
        exact mul_mem_lattice K ((mem_lattice K).2 hcenter.ge) hu
      refine ⟨lattice_antitone K ?_ hetaMem, ?_⟩
      · have hpos : 1 ≤ (p : ℤ) * ((D.t : ℤ) + D.delta) := by
          have hpZ : (1 : ℤ) ≤ p := by exact_mod_cast hp.one_le
          nlinarith [show (0 : ℤ) ≤ D.delta by positivity]
        linarith
      · obtain ⟨pi, hpi, hpiGen⟩ := monogenicUniformizer B₁ K hres₁K
        have htrace : TraceIdealLowerBound B₁ K p
            (((p : ℤ) - 1) * ((D.t : ℤ) + (p : ℤ) * D.delta + 1)) := by
          have h := traceIdealLowerBound_of_integralGenerator B₁ K D.B₁_breaks.2
            hres₁K pi hpi hpiGen
          simpa only [hdegree, D.tPrime_eq, Nat.cast_mul, Nat.cast_add,
            Nat.cast_sub hp.one_le, Nat.cast_one] using h
        exact shift_unit_norm_mem B₁ K hp D.odd_prime D.t D.delta D.t_pos V hVbound
          ((residueCharacteristic_extension_eq F B₁).trans hchar) hdegree hram₁K htrace u hu
  let sigma₁ := IntermediateField.restrictRestrictAlgEquivMapHom F B₁ B₂ K sigma
  have hnormSigma : sigma₁ (norm B₁ K Delta) = norm B₁ K (sigma Delta) := by
    have h := Algebra.norm_eq_of_equiv_equiv sigma₁.toRingEquiv sigma.toRingEquiv
      (by ext c; exact IntermediateField.restrictRestrictAlgEquivMapHom_apply B₁ B₂ sigma c) Delta
    change norm B₁ K Delta = sigma₁.symm (norm B₁ K (sigma Delta)) at h
    simpa only [AlgEquiv.apply_symm_apply] using congrArg sigma₁ h
  have hnormMem : norm B₁ K (Delta + 1) ∈ lattice B₁ (-(D.t : ℤ)) := by
    rw [mem_lattice, ord_norm, hres₁K, one_nsmul, hcenter]
  have herror : sigma₁ (norm B₁ K Delta) - norm B₁ K (Delta + 1) ∈
      lattice B₁ ((D.t : ℤ) + ((p : ℤ) - 1) * D.delta) := by
    rw [hnormSigma, hnorm]
    have h := mul_mem_lattice B₁ hnormMem hunit.2
    convert h using 1
    · congr 1
      ring
    · dsimp only [u]
      ring
  refine ⟨sigma, ?_, ?_⟩
  · rw [hsigma, add_sub_cancel_left]
    exact hunit.1
  · have h := (lattice B₁ _).add_mem herror
        (shift_formal_translation hp hG hres hchar D Delta a hroot hDelta hprime hgen)
    apply lattice_antitone B₁ (shift_depth hp hG D).2
    convert h using 1
    dsimp only [sigma₁]
    ring

open private commutator_additiveConductor from LanglandsSecondMainLemma.Odd.R2.Commutator
open private additivePhase_sub from LanglandsSecondMainLemma.Odd.Models.TwistFormula

/-- Equation `O:R:S` on the whole shallow ideal. The actual translating
root is constructed by `shift`, and the coefficient error is killed at
exactly `R+q=T'`. The full model and chart are the ones supplied by
`Models.realization`; no shallow model formula is assumed. -/
theorem shift_commutator
    (c : ℕ) (hc : c = (D.t₂ + 1) ⌈/⌉ p) (hcpos : 0 < c)
    (tau : NormCharacter F B₂) (htau : tau ≠ 1) (Psi : ContinuousAddChar F)
    (hchart : ∀ z : lattice F (c : ℤ),
      tau.1 (positiveUnitOfLattice F hcpos (-z)) = Psi (truncatedLog p (z : F)))
    (Delta : K) (a : B₂)
    (hroot : Delta ^ p - Delta = algebraMap B₂ K a)
    (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ D.t) (hgen : Algebra.adjoin B₂ ({Delta} : Set K) = ⊤)
    (chi : ContinuousQuasiChar B₁)
    (hmodel : ∀ u : unitFiltration B₁ (Models.firstModelDepth D),
      chi u = tracePullbackAddChar F B₁ Psi
        (norm B₁ K Delta * truncatedLog p (1 - ((u : B₁ˣ) : B₁)))) :
    ∃ sigma : Gal(K/B₂),
      sigma Delta - (Delta + 1) ∈ lattice K 1 ∧
      let sigma₁ := IntermediateField.restrictRestrictAlgEquivMapHom F B₁ B₂ K sigma
      ∀ x : lattice B₁ ((D.delta + (D.t + 1) ⌈/⌉ p : ℕ) : ℤ),
        (Basic.conjugateQuasiChar F B₁ sigma₁ chi / chi)
            (positiveUnitOfLattice B₁ (commutator_depths hp hG D).1 (-x)) =
          tracePullbackAddChar F B₁ Psi
            ((1 - (-elementarySymmetric B₁ K (p - 1) Delta)) * truncatedLog p (x : B₁)) := by
  obtain ⟨sigma, hnear, hshift⟩ := shift hp hG hres hchar D Delta a hroot hDelta hprime hgen
  refine ⟨sigma, hnear, ?_⟩
  dsimp only
  intro x
  rw [commutator hp hG hres hchar D c hc hcpos tau htau Psi hchart Delta hDelta chi hmodel]
  have hPsi := commutator_additiveConductor hp hG hres hchar D c hc hcpos tau htau Psi hchart
  have hlog : truncatedLog p (x : B₁) ∈
      lattice B₁ ((D.delta + (D.t + 1) ⌈/⌉ p : ℕ) : ℤ) := by
    rw [mem_lattice, ord_truncatedLog B₁ p
      ((residueCharacteristic_extension_eq F B₁).trans hchar)
      (lattice_antitone B₁ (by exact_mod_cast (commutator_depths hp hG D).1) x.property)]
    exact x.property
  apply div_eq_one.mp
  rw [← additivePhase_sub]
  apply hPsi.trivial
  have h := mul_mem_lattice B₁ hshift hlog
  simpa only [sub_add_cancel, neg_neg, sub_mul] using h

end Diamond

end

end LanglandsSecondMainLemma.Odd.R2
