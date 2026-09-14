import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Q2.Moments

/-!
# The full Z congruence

Paper Proposition 9.16 (`O:N:Z`). The actual lower characteristic polynomials
supply the numerator, and the strong symmetric bound controls the weighted
replacement of its denominator. All depths are integer lattice exponents.
-/
namespace LanglandsSecondMainLemma.Odd.Q2

open LanglandsFirstMainLemma
open scoped BigOperators
noncomputable section

/-- The exact floor bound suffices without a residue-class split for the break. -/
private theorem denominator_depths (p t d m : ℤ)
    (hp : 3 ≤ p) (ht : 1 ≤ t) (hd : 0 ≤ d) (hm : t < p * m) :
    let L := (p * m - t + (p - 1) * (t + d + 1)) / p
    1 ≤ m ∧ 1 ≤ L ∧
    t + d + m + 1 ≤ (p - 1) * (m + d) + L ∧
    t + d + m + 1 ≤ 2 * (p - 1) * m + (p - 1) * d ∧
    1 + p * (t + d + m) ≤
      p * (p - 1) * m + p * (p - 1) * d + (p - 1) * t := by
  have hmpos : 1 ≤ m := by nlinarith
  have hp0 : 0 < p := by omega
  have hpm : t + 1 ≤ p * m := by omega
  have hpd : 0 ≤ (p - 1) * d := by nlinarith
  have hpm₂ : 2 * (p * m) ≤ p * ((p - 1) * m) := by nlinarith
  have hpd₂ : d ≤ (p - 1) * d := by nlinarith
  dsimp only
  refine ⟨hmpos, ?_, ?_, ?_, ?_⟩
  · apply (Int.le_ediv_iff_mul_le hp0).2
    nlinarith
  · have hfloor : t + d + m + 1 - (p - 1) * (m + d) ≤
        (p * m - t + (p - 1) * (t + d + 1)) / p := by
      apply (Int.le_ediv_iff_mul_le hp0).2
      have : 0 ≤ p * ((p - 1) * d) - d := by nlinarith
      nlinarith
    linarith
  · have : 0 ≤ (p - 3) * m := by nlinarith
    nlinarith
  · have hgain : p * m ≤ p * ((p - 2) * m) := by nlinarith
    have hdgain : 0 ≤ p * ((p - 2) * d) := by nlinarith
    nlinarith

private theorem norm_expansion (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F E] [Module.Free F E] [Module.Finite F E] [IsGalois F E]
    {p : ℕ} (hp : 1 ≤ p) (hdegree : Module.finrank F E = p) (u : F) (x : E) :
    norm F E (1 + algebraMap F E u * x) =
      1 + (∑ i ∈ Finset.range (p - 1), u ^ (i + 1) * elementarySymmetric F E (i + 1) x) +
        u ^ p * norm F E x := by
  rw [norm_one_add_eq_one_add_sum_elementarySymmetric, hdegree]
  have hsplit : p = p - 1 + 1 := by omega
  conv_lhs => arg 2; rw [hsplit, Finset.sum_range_succ]
  simp only [Nat.sub_add_cancel hp, elementarySymmetric_algebraMap_mul]
  rw [← hdegree, elementarySymmetric_finrank]
  ring

private theorem contract_lattice (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
    {p : ℕ} (hp : 0 < p) (hram : ramificationIndex F E = p)
    (r : ℤ) (x : F) (hx : algebraMap F E x ∈ lattice E (1 + (p : ℤ) * r)) :
    x ∈ lattice F (r + 1) := by
  rw [mem_lattice, ord_algebraMap, hram] at hx
  rw [mem_lattice]
  by_cases hzero : x = 0
  · simp [hzero]
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).2 hzero)
  rw [← hv, ← WithTop.coe_nsmul, WithTop.coe_le_coe] at hx
  rw [← hv, WithTop.coe_le_coe]
  simp only [nsmul_eq_mul] at hx
  have hpZ : 0 < (p : ℤ) := by exact_mod_cast hp
  by_contra h
  have : (p : ℤ) * v ≤ (p : ℤ) * r := mul_le_mul_of_nonneg_left (by omega) hpZ.le
  omega

private theorem ord_eq_zero_of_sub_one (F : Type*) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {x : F} (hx : x - 1 ∈ lattice F 1) : ord F x = 0 := by
  have hpos : (0 : WithTop ℤ) < ord F (x - 1) :=
    lt_of_lt_of_le (by norm_cast) ((mem_lattice F).1 hx)
  have h := ord_add_eq_min F (x := x - 1) (y := 1) (by simpa using hpos.ne')
  simpa only [sub_add_cancel, ord_one, min_eq_right hpos.le] using h

set_option backward.isDefEq.respectTransparency false

open private realization_tower_data from LanglandsSecondMainLemma.Odd.Models.Realization
open private exact_coordinate_orders_and_generation from
  LanglandsSecondMainLemma.Odd.Total.ASCoordinate

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
local instance : PrimeCyclicExtension F B₂ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₂
    (Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.1
local instance : PrimeCyclicExtension B₁ K :=
  PrimeCyclicExtension.ofCyclicPrimeExtension B₁ K
    (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.2.2.2.2
local instance : PrimeCyclicExtension B₂ K :=
  PrimeCyclicExtension.ofCyclicPrimeExtension B₂ K
    (Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.2

include hres hchar

set_option maxHeartbeats 1000000 in
/-- **Paper Proposition 9.16 (`O:N:Z`).** The complete congruence for the
literal ratio of lower norms, with the actual exceptional coefficient and
common norm denominator. The exact coordinate and norm witness are those
used in `moments`; no comparison or denominator congruence is assumed.

The character data enter through `u = alpha/gamma`, its order `m`, and the
exact witness `n₂(w) = u⁻¹`. This algebraic conclusion holds for every such
ratio and witness, in both field characteristics. -/
theorem zCongruence
    (Delta : K)
    (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ D.t)
    (hroot : Delta ^ p - Delta = algebraMap B₂ K (norm B₂ K Delta))
    (u : Fˣ) (w : B₂ˣ) (hw : normUnits F B₂ w = u⁻¹)
    (m : ℤ) (hu : ord F (u : F) = (m : WithTop ℤ))
    (hm : (D.t : ℤ) < (p : ℤ) * m) :
    let a := norm B₂ K Delta
    let b₀ := norm B₁ K Delta
    let s := -elementarySymmetric B₁ K (p - 1) Delta
    let H := norm F B₁ s
    let Y := norm F B₂ (1 + algebraMap F B₂ (u : F) * a) - (u : F) ^ (p - 1)
    let D₀ := 1 + (u : F) ^ p * norm F B₂ a
    let Z := norm F B₁ (1 + algebraMap F B₁ (u : F) * b₀) / Y
    Z - (1 + (u : F) ^ (p - 1) * H / D₀) ∈ lattice F ((D.t₂ : ℤ) + m + 1) := by
  classical
  dsimp only
  let a := norm B₂ K Delta
  let b := norm B₁ K Delta
  let s := -elementarySymmetric B₁ K (p - 1) Delta
  let H := norm F B₁ s
  let q := (u : F) ^ (p - 1)
  let N := norm F B₁ (1 + algebraMap F B₁ (u : F) * b)
  let P := norm F B₂ (1 + algebraMap F B₂ (u : F) * a)
  let Y := P - q
  let D₀ := 1 + (u : F) ^ p * norm F B₂ a
  let r : ℤ := (D.t₂ : ℤ) + m
  let L : ℤ := ((p : ℤ) * m - D.t + ((p : ℤ) - 1) * ((D.t₂ : ℤ) + 1)) / p
  change N / Y - (1 + q * H / D₀) ∈ lattice F (r + 1)
  have hp3 := D.odd_prime
  have hpZ : (3 : ℤ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
  have htZ : (1 : ℤ) ≤ D.t := by exact_mod_cast (show 1 ≤ D.t from D.t_pos)
  have hdZ : (0 : ℤ) ≤ D.delta := by positivity
  have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
  obtain ⟨hmpos, hLpos, hLweight, hqweight, hpowerDepth⟩ :=
    denominator_depths p D.t D.delta m hpZ htZ hdZ hm
  rw [← ht₂] at hLpos hLweight
  change 1 ≤ L at hLpos
  change r + 1 ≤ ((p : ℤ) - 1) * (m + D.delta) + L at hLweight
  have hdegreeF₁ : Module.finrank F B₁ = p := D.degree_B₁
  have hdegreeF₂ : Module.finrank F B₂ = p := D.degree_B₂
  obtain ⟨_, hresF₁, hres₁K, hramF₁, _⟩ :=
    realization_tower_data hp hG hres B₁ D.degree_B₁
  obtain ⟨hdegree₂, hresF₂, hres₂K, hramF₂, hram₂K⟩ :=
    realization_tower_data hp hG hres B₂ D.degree_B₂
  have hbreak₁ : PrimeCyclicExtension.IsLowerBreak F B₁ D.t := D.B₁_breaks.1
  have hbreak₂ : PrimeCyclicExtension.IsLowerBreak F B₂ D.t₂ := D.B₂_breaks.1
  obtain ⟨_, hgen⟩ := exact_coordinate_orders_and_generation B₂ K hp D.t_pos
    hdegree₂ hram₂K Delta a hDelta hprime hroot
  obtain ⟨_, _, _, hs⟩ := Models.realization_twistedEstimates_of_coordinate
    hp hG hres hchar D Delta a hroot hDelta hprime hgen
  change ((((p : ℤ) - 1) * D.delta : ℤ) : WithTop ℤ) ≤ ord B₁ s at hs
  have hH : H ∈ lattice F (((p : ℤ) - 1) * D.delta) := by
    simpa only [H, mem_lattice, ord_norm, hresF₁, one_nsmul] using hs
  have hq : ord F q = ((((p : ℤ) - 1) * m : ℤ) : WithTop ℤ) := by
    simp only [q, ord_pow, hu, ← WithTop.coe_nsmul, nsmul_eq_mul,
      Nat.cast_sub hp.one_le, Nat.cast_one]
  have hqH := mul_mem_lattice F ((mem_lattice F).2 hq.ge) hH
  have hqH' : q * H ∈ lattice F (((p : ℤ) - 1) * (m + D.delta)) := by
    simpa only [mul_add] using hqH
  have hnorm : norm F B₁ b = norm F B₂ a := by
    dsimp only [a, b]
    rw [norm_trans, norm_trans]
  have hN := norm_expansion F B₁ hp.one_le hdegreeF₁ (u : F) b
  have hP := norm_expansion F B₂ hp.one_le hdegreeF₂ (u : F) a
  change N = _ at hN
  change P = _ at hP
  rw [hnorm] at hN
  -- Sum the actual nonterminal characteristic-polynomial coefficients.
  have hmom := (moments hp hG hres hchar D Delta hDelta hprime hroot u w hw m hu hm).2
  have hsum := sum_mem_lattice B₁ (s := Finset.range (p - 1))
    (fun i hi => hmom (i + 1) (by omega) (by have := Finset.mem_range.mp hi; omega))
  have hlast : ∀ i : ℕ, i + 1 = p - 1 ↔ i = p - 2 := by omega
  simp only [hlast, Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (show p - 2 ∈ Finset.range (p - 1) by simp; omega)] at hsum
  have hnum : algebraMap F B₁ (N - Y) - algebraMap F B₁ q * s ^ p ∈
      lattice B₁ (1 + (p : ℤ) * r) := by
    convert hsum using 1
    dsimp only [Y, q, s]
    rw [hN, hP]
    simp only [map_sub, map_add, map_one, map_mul, map_pow, map_sum,
      mul_sub, Finset.sum_sub_distrib]
    ring
  -- Replace s^p by its actual lower norm, at the full upstairs modulus.
  have hpn := Total.powerNorm F B₁ p D.t hdegreeF₁ hp3 hbreak₁ D.t_pos hresF₁ s
  have hpn' : s ^ p - algebraMap F B₁ H ∈
      lattice B₁ ((p : ℤ) * (((p : ℤ) - 1) * D.delta) + ((p : ℤ) - 1) * D.t) := by
    apply (mem_lattice B₁).2
    have h := (add_le_add (nsmul_le_nsmul_right hs p)
      (le_refl (((((p - 1) * D.t : ℕ) : ℤ) : WithTop ℤ)))).trans hpn
    simpa only [← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul,
      Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one, H] using h
  have hq₁ : algebraMap F B₁ q ∈ lattice B₁ ((p : ℤ) * (((p : ℤ) - 1) * m)) := by
    simp only [mem_lattice, ord_algebraMap, hramF₁, hq, ← WithTop.coe_nsmul,
      nsmul_eq_mul, le_refl]
  have hcorr := mul_mem_lattice B₁ hq₁ hpn'
  have hcorr' : algebraMap F B₁ q * (s ^ p - algebraMap F B₁ H) ∈
      lattice B₁ (1 + (p : ℤ) * r) := by
    apply lattice_antitone B₁ (show 1 + (p : ℤ) * r ≤ _ from ?_) hcorr
    dsimp only [r]
    rw [ht₂]
    nlinarith [hpowerDepth]
  have hbase : N - Y - q * H ∈ lattice F (r + 1) := by
    apply contract_lattice F B₁ hp.pos hramF₁ r
    convert (lattice B₁ (1 + (p : ℤ) * r)).add_mem hnum hcorr' using 1
    simp only [map_sub, map_mul]
    ring
  -- The same strong symmetric bound controls the literal denominator.
  let x := algebraMap F B₂ (u : F) * a
  have hx : x ∈ lattice B₂ ((p : ℤ) * m - D.t) := by
    simp only [x, a, mem_lattice, ord_mul, ord_algebraMap, hramF₂, hu, ord_norm,
      hres₂K, one_nsmul, hDelta, ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul]
    norm_cast
  obtain ⟨pi, hpi, hpiGen⟩ := monogenicUniformizer F B₂ hresF₂
  have htrace := traceIdealLowerBound_of_integralGenerator F B₂ hbreak₂ hresF₂ pi hpi hpiGen
  have he := wild_symmetric_bound F B₂ D.t₂ hbreak₂ (by omega)
    (hchar.trans hdegreeF₂.symm) (hramF₂.trans hdegreeF₂.symm)
    (by simpa only [wildDifferentContribution] using htrace)
    ((p : ℤ) * m - D.t) ((mem_lattice B₂).1 hx)
  have heL (i : ℕ) (hi : 1 ≤ i) (hip : i < p) :
      elementarySymmetric F B₂ i x ∈ lattice F L := by
    apply (mem_lattice F).2
    apply (WithTop.coe_le_coe.mpr ?_).trans (he.1 hi (by simpa [hdegreeF₂] using hip))
    dsimp only [L]
    simp only [hdegreeF₂, wildDifferentContribution, Nat.cast_mul,
      Nat.cast_sub hp.one_le, Nat.cast_one, Nat.cast_add]
    apply Int.ediv_le_ediv (by positivity)
    have hiZ : (1 : ℤ) ≤ i := by exact_mod_cast hi
    nlinarith
  let E := ∑ i ∈ Finset.range (p - 1), elementarySymmetric F B₂ (i + 1) x
  have hE : E ∈ lattice F L := by
    apply sum_mem_lattice F
    intro i hi
    exact heL (i + 1) (by omega) (by have := Finset.mem_range.mp hi; omega)
  have hYD : Y - D₀ = E - q := by
    dsimp only [Y, D₀, E, x]
    rw [hP]
    simp only [elementarySymmetric_algebraMap_mul]
    ring
  have hDsmall : D₀ - 1 ∈ lattice F 1 := by
    dsimp only [D₀]
    rw [add_sub_cancel_left, mem_lattice, ord_mul, ord_pow, hu, ord_norm,
      hresF₂, one_nsmul]
    dsimp only [a]
    rw [ord_norm, hres₂K, one_nsmul, hDelta, ← WithTop.coe_nsmul,
      ← WithTop.coe_add, WithTop.coe_le_coe]
    simp only [nsmul_eq_mul]
    omega
  have hqsmall : q ∈ lattice F 1 := by
    rw [mem_lattice, hq, WithTop.coe_le_coe]
    nlinarith
  have hYsmall : Y - 1 ∈ lattice F 1 := by
    have h := (lattice F 1).add_mem hDsmall
      ((lattice F 1).sub_mem (lattice_antitone F hLpos hE) hqsmall)
    convert h using 1
    rw [← hYD]
    ring
  have hYord := ord_eq_zero_of_sub_one F hYsmall
  have hDord := ord_eq_zero_of_sub_one F hDsmall
  have hYne : Y ≠ 0 := (ord_ne_top_iff F).1 (by rw [hYord]; exact WithTop.coe_ne_top)
  have hDne : D₀ ≠ 0 := (ord_ne_top_iff F).1 (by rw [hDord]; exact WithTop.coe_ne_top)
  have hweighted : q * H * (Y - D₀) ∈ lattice F (r + 1) := by
    rw [hYD, mul_sub]
    apply (lattice F (r + 1)).sub_mem
    · exact lattice_antitone F hLweight (mul_mem_lattice F hqH' hE)
    · apply lattice_antitone F (show r + 1 ≤ _ from ?_) (mul_mem_lattice F hqH' ((mem_lattice F).2 hq.ge))
      dsimp only [r]
      rw [ht₂]
      nlinarith [hqweight]
  have hquot : (N - Y - q * H) / Y ∈ lattice F (r + 1) := by
    simpa only [mem_lattice, ord_div, hYord, sub_zero] using hbase
  have hreplace : q * H * (Y - D₀) / (Y * D₀) ∈ lattice F (r + 1) := by
    simpa only [mem_lattice, ord_div, ord_mul, hYord, hDord, add_zero, sub_zero] using hweighted
  convert (lattice F (r + 1)).sub_mem hquot hreplace using 1
  field_simp [hYne, hDne]
  ring

end Diamond
end
end LanglandsSecondMainLemma.Odd.Q2
