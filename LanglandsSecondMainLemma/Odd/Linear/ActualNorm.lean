import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Linear.Setup
import LanglandsSecondMainLemma.Odd.Total.TranslatedNorm

/-!
# The actual upper norms of translated conjugates

Paper: `O:W:actualnorm`, with the setup of `O:sec:linear`.

The strong symmetric estimate bounds the norm of the multiplicative
Hensel correction. The different and its trace bound come from FML's
integral-generator constructor. All depths are integers, including the
division by the extension degree, and corrections may have infinite order.
-/

namespace LanglandsSecondMainLemma.Odd.Linear

noncomputable section
open LanglandsFirstMainLemma
open scoped BigOperators

/-- The strong norm estimate obtained by summing the nonterminal symmetric
coefficients and retaining the terminal norm coefficient separately. -/
private theorem norm_one_add_strong_bound
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    [Module.Free E L] [Module.Finite E L] [PrimeCyclicExtension E L]
    {b : ℕ} (hbreak : PrimeCyclicExtension.IsLowerBreak E L b) (hb : 0 < b)
    (hchar : residueCharacteristic E = Module.finrank E L)
    (hram : ramificationIndex E L = Module.finrank E L)
    (htrace : TraceIdealLowerBound E L (Module.finrank E L)
      (wildDifferentContribution (Module.finrank E L) b))
    (q : ℤ) (hq : 0 ≤ q) (z : L) (hz : (q : WithTop ℤ) ≤ ord L z) :
    ((min q ((q + wildDifferentContribution (Module.finrank E L) b) /
      (Module.finrank E L : ℤ)) : ℤ) : WithTop ℤ) ≤
        ord E (norm E L (1 + z) - 1) := by
  have hs := wild_symmetric_bound E L b hbreak hb hchar hram htrace q hz
  rw [norm_one_add_eq_one_add_sum_elementarySymmetric, add_sub_cancel_left]
  apply ord_sum E
  intro j hj
  have hjlt := Finset.mem_range.mp hj
  by_cases hjtop : j + 1 = Module.finrank E L
  · rw [hjtop, hs.2.1]
    exact (WithTop.coe_le_coe.mpr (min_le_left _ _)).trans hz
  · have hdegree : (0 : ℤ) < Module.finrank E L := by
      exact_mod_cast (PrimeCyclicExtension.degree_prime E L).pos
    have hqj : q ≤ ((j + 1 : ℕ) : ℤ) * q := by
      have hjnonneg : (0 : ℤ) ≤ j := by positivity
      push_cast
      nlinarith
    apply (WithTop.coe_le_coe.mpr (min_le_right _ _)).trans
    apply (WithTop.coe_le_coe.mpr ?_).trans (hs.1 (by omega) (by omega))
    exact Int.ediv_le_ediv hdegree (by omega)

/-- The two entries of the strong norm estimate both reach `t+t₂+1`.
The floor is kept as integer division; no rounding or divisibility of
`V` is discarded. This includes `p=3` and `delta=0`. -/
private theorem actualNorm_depth
    (p t delta V : ℤ) (hp : 3 ≤ p) (ht : 1 ≤ t) (hd : 0 ≤ delta)
    (hV : p * (p - 1) * (t + delta) ≤ V) :
    0 ≤ V - (p - 2) * t ∧
      t + (t + delta) + 1 ≤ min (V - (p - 2) * t)
        ((V - (p - 2) * t + (p - 1) * (t + p * delta + 1)) / p) := by
  have hpt : 0 ≤ p * (p - 3) * t :=
    mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
  have hdt : 0 ≤ (p * (p - 1) - 1) * delta :=
    mul_nonneg (by nlinarith) hd
  have hdd : 0 ≤ p * (2 * p - 3) * delta :=
    mul_nonneg (mul_nonneg (by omega) (by omega)) hd
  have hfirst : t + (t + delta) + 1 ≤ V - (p - 2) * t := by
    nlinarith [mul_nonneg (by omega : 0 ≤ p - 1) (by omega : 0 ≤ t)]
  refine ⟨by linarith, le_min hfirst ?_⟩
  rw [Int.le_ediv_iff_mul_le (by omega : 0 < p)]
  nlinarith

open private realization_tower_data from
  LanglandsSecondMainLemma.Odd.Models.Realization
open private translated_root_center_ord from
  LanglandsSecondMainLemma.Odd.Total.TranslatedNorm

section Diamond

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]
  {p : ℕ} {hp : p.Prime}
  {hG : Nonempty
    (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))}
  (D : Total.OddTotalBreakData (F := F) (K := K) hp hG)

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

local notation "B₁" => D.B₁
local notation "B₂" => D.B₂

local instance : PrimeCyclicExtension B₁ K :=
  PrimeCyclicExtension.ofCyclicPrimeExtension B₁ K
    (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.2.2.2.2

/-- The norm error for any additive correction with the constructed
Hensel bound. This does not replace either the coordinate or its shift;
`actualNorm` below supplies an actual conjugate and this bound. -/
theorem actualNorm_of_correction
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (Delta : K) (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (xi : F) (hxi : xi = 0 ∨ xi ^ (p - 1) = 1)
    (eta : K)
    (heta : ord K (p : K) - ((((p - 1) * D.t : ℕ) : ℤ) : WithTop ℤ) ≤ ord K eta) :
    (((D.t₂ : ℤ) + 1 : ℤ) : WithTop ℤ) ≤
      ord B₁ (norm B₁ K (Delta + algebraMap F K xi + eta) -
        norm B₁ K (Delta + algebraMap F K xi)) := by
  by_cases hpzero : (p : K) = 0
  · have hetaZero : eta = 0 := by
      apply (ord_eq_top_iff K).mp
      simpa only [hpzero, ord_zero, WithTop.LinearOrderedAddCommGroup.top_sub,
        top_le_iff] using heta
    simp [hetaZero]
  obtain ⟨V, hV⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff K).mpr hpzero)
  have hVord : ord K (p : K) = (V : WithTop ℤ) := hV.symm
  have hVbound := Total.oddTotal_primeValuationBound hp hG hres D
  rw [hVord, WithTop.coe_le_coe] at hVbound
  push_cast [Nat.cast_sub hp.one_le] at hVbound
  have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
  rw [ht₂] at hVbound
  have hdepth := actualNorm_depth p D.t D.delta V
    (by exact_mod_cast D.odd_prime) (by exact_mod_cast D.t_pos)
    (by positivity) hVbound
  have hcenter : ord K (Delta + algebraMap F K xi) =
      ((-(D.t : ℤ) : ℤ) : WithTop ℤ) := by
    rcases hxi with rfl | hxi
    · simpa only [map_zero, add_zero] using hDelta
    · exact translated_root_center_ord K (n := p - 1) (by have := hp.one_lt; omega)
        (by exact_mod_cast D.t_pos) Delta (algebraMap F K xi) hDelta
          (by rw [← map_pow, hxi, map_one])
  have hcenterNe : Delta + algebraMap F K xi ≠ 0 :=
    (ord_ne_top_iff K).mp (hcenter ▸ WithTop.coe_ne_top)
  have hetaMem : eta ∈ lattice K (V - ((p : ℤ) - 1) * D.t) := by
    rw [hVord, ← WithTop.LinearOrderedAddCommGroup.coe_sub] at heta
    simpa only [mem_lattice, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one] using heta
  have hz := Total.translatedRootUnit_mem K p D.t V Delta (algebraMap F K xi) eta
    hcenter hetaMem
  obtain ⟨hdegree, _, hres₁, _, hram⟩ :=
    realization_tower_data hp hG hres B₁ D.degree_B₁
  have hbreak : PrimeCyclicExtension.IsLowerBreak B₁ K D.tPrime := by
    simpa only [Total.OddTotalBreakData.B₁, Ramification.IntermediateBreakPair]
      using D.B₁_breaks.2
  have htPrime : 0 < D.tPrime := by have := D.tPrime_eq; have := D.t_pos; omega
  obtain ⟨pi, hpi, hpiGen⟩ := monogenicUniformizer B₁ K hres₁
  have htrace := traceIdealLowerBound_of_integralGenerator B₁ K hbreak hres₁ pi hpi hpiGen
  have hnorm := norm_one_add_strong_bound B₁ K hbreak htPrime
    (by rw [hdegree]; exact (residueCharacteristic_extension_eq F B₁).trans hchar)
    (hram.trans hdegree.symm) htrace
    (V - ((p : ℤ) - 2) * D.t) hdepth.1
    (Total.translatedRootUnit Delta (algebraMap F K xi) eta) ((mem_lattice K).mp hz)
  have hunit : norm B₁ K (1 + Total.translatedRootUnit Delta (algebraMap F K xi) eta) - 1 ∈
      lattice B₁ ((D.t : ℤ) + D.t₂ + 1) := by
    rw [mem_lattice]
    apply (WithTop.coe_le_coe.mpr ?_).trans hnorm
    simpa only [hdegree, wildDifferentContribution, D.tPrime_eq,
      Nat.cast_mul, Nat.cast_add, Nat.cast_sub hp.one_le, Nat.cast_one, ht₂] using hdepth.2
  have hbase : norm B₁ K (Delta + algebraMap F K xi) ∈ lattice B₁ (-(D.t : ℤ)) := by
    rw [mem_lattice, ord_norm, hres₁, one_nsmul, hcenter]
  have hfactor : norm B₁ K (Delta + algebraMap F K xi + eta) -
      norm B₁ K (Delta + algebraMap F K xi) =
        norm B₁ K (Delta + algebraMap F K xi) *
          (norm B₁ K (1 + Total.translatedRootUnit Delta (algebraMap F K xi) eta) - 1) := by
    rw [Total.translatedRoot_norm_factor B₁ K Delta (algebraMap F K xi) eta hcenterNe]
    ring
  rw [hfactor]
  have hproduct := mul_mem_lattice B₁ hbase hunit
  convert (mem_lattice B₁).mp hproduct using 1
  congr 1
  ring

/-- Paper `O:W:actualnorm`, for the prescribed genuine coordinate.
For each member of `{0} ∪ μ_{p-1} ⊂ F`, construct the actual `B/B₂`
conjugate, retain its Hensel displacement, and prove the crossed upper
norm error at depth `t₂+1` in `B₁`. In equal characteristic the translation
and hence its norm comparison are exact. The displacement is constructed
by `OddLinearData.actual_conjugate`, not imposed as a new input. -/
theorem actualNorm
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    {Delta : K} {a : B₂} {w : B₂ˣ} {m : ℤ}
    (L : OddLinearData D Delta a w m)
    (xi : F) (hxi : xi = 0 ∨ xi ^ (p - 1) = 1) :
    ∃ (sigma : Gal(K/B₂)) (eta : K),
      sigma Delta = Delta + algebraMap F K xi + eta ∧
      ord K (p : K) - ((((p - 1) * D.t : ℕ) : ℤ) : WithTop ℤ) ≤ ord K eta ∧
      (((D.t₂ : ℤ) + 1 : ℤ) : WithTop ℤ) ≤
        ord B₁ (norm B₁ K (sigma Delta) - norm B₁ K (Delta + algebraMap F K xi)) ∧
      ((p : K) = 0 → eta = 0 ∧ sigma Delta = Delta + algebraMap F K xi ∧
        norm B₁ K (sigma Delta) = norm B₁ K (Delta + algebraMap F K xi)) := by
  obtain ⟨sigma, eta, hsigma, heta⟩ := L.actual_conjugate hres hchar xi hxi
  refine ⟨sigma, eta, hsigma, heta, ?_, ?_⟩
  · rw [hsigma]
    exact actualNorm_of_correction D hres hchar Delta L.Delta_order xi hxi eta heta
  · intro hpzero
    have hetaZero : eta = 0 := by
      apply (ord_eq_top_iff K).mp
      simpa only [hpzero, ord_zero, WithTop.LinearOrderedAddCommGroup.top_sub,
        top_le_iff] using heta
    have heq : sigma Delta = Delta + algebraMap F K xi := by
      simpa only [hetaZero, add_zero] using hsigma
    exact ⟨hetaZero, heq, congrArg (norm B₁ K) heq⟩

end Diamond

end

end LanglandsSecondMainLemma.Odd.Linear
