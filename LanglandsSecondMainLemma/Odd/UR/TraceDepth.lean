import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.UR.ScalarPhase

/-!
# Odd / UR / Trace Depth

Paper Lemma 6.12 (`O:I:Sdepth`), in the setup of 1060--1128 and
1408--1430 of `references/epsilon_SML.tex`.

We use Newton's identities twice. Pairing the quadratic terms by
`i ↦ p-i` supplies their factor of `p`; the terms with at least three
factors already have sufficient depth. This proves the needed consequence
of the paper's integral universal identity without introducing its
auxiliary polynomial. All depth calculations use integer exponents.
-/

namespace LanglandsSecondMainLemma.Odd.UR

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

section Newton
variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra F E] [Module.Finite F E] [IsGalois F E]

/-- FML's Newton identity with the constant elementary coefficient
separated and the remaining terms indexed by `1 ≤ i < j`. -/
private theorem traceDepth_newton (x : E) {j : ℕ} (hj : 0 < j) :
    trace F E (x ^ j) =
      (-1 : F) ^ (j + 1) * j * elementarySymmetric F E j x -
        ∑ i ∈ Finset.Ico 1 j,
          (-1 : F) ^ i * elementarySymmetric F E i x * trace F E (x ^ (j - i)) := by
  classical
  have hn := elementarySymmetric_newton_identity F E x j
  have hsum : (∑ a ∈ Finset.HasAntidiagonal.antidiagonal j with a.1 < j,
      (-1 : F) ^ a.1 * elementarySymmetric F E a.1 x * galoisPowerSum F E a.2 x) =
      trace F E (x ^ j) + ∑ i ∈ Finset.Ico 1 j,
        (-1 : F) ^ i * elementarySymmetric F E i x * trace F E (x ^ (j - i)) := by
    simp only [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, lt_self_iff_false, if_false, add_zero]
    have hfilter : (∑ i ∈ Finset.range j, if i < j then
        (-1 : F) ^ i * elementarySymmetric F E i x * galoisPowerSum F E (j - i) x
        else 0) = ∑ i ∈ Finset.range j,
        (-1 : F) ^ i * elementarySymmetric F E i x * trace F E (x ^ (j - i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [if_pos (Finset.mem_range.mp hi)]
      rfl
    rw [hfilter, ← Finset.sum_range_add_sum_Ico _ hj]
    simp [elementarySymmetric_zero]
  rw [hsum] at hn
  have hsign : (-1 : F) ^ (j + 1) * (-1 : F) ^ (j + 1) = 1 := by
    rw [← mul_pow]
    simp
  have hn' := congrArg (fun z : F => (-1 : F) ^ (j + 1) * z) hn
  simp only [← mul_assoc, hsign, one_mul] at hn'
  linear_combination -hn'

/-- The paired quadratic Newton contribution. Multiplication by two
keeps the identity integral, in both field characteristics. -/
private theorem traceDepth_secondOrder {p : ℕ} (hp : Odd p)
    (hdegree : Module.finrank F E = p) (x : E) :
    2 * ((p : F) * norm F E x - trace F E (x ^ p) + (p : F) * trace F E x) =
      (p : F) * (∑ i ∈ Finset.Ico 1 p,
        elementarySymmetric F E i x * elementarySymmetric F E (p - i) x) +
      2 * (∑ i ∈ Finset.Ico 1 p,
        (-1 : F) ^ i * elementarySymmetric F E i x *
          (trace F E (x ^ (p - i)) - (-1 : F) ^ (p - i + 1) *
            (p - i : ℕ) * elementarySymmetric F E (p - i) x)) +
      2 * (p : F) * trace F E x := by
  classical
  let a : ℕ → F := fun i => elementarySymmetric F E i x
  let s : ℕ → F := fun i => trace F E (x ^ i)
  have hn := traceDepth_newton F E x hp.pos
  have hsign : (-1 : F) ^ (p + 1) = 1 := by rw [pow_succ, hp.neg_one_pow]; ring
  rw [hsign, one_mul, ← hdegree, elementarySymmetric_finrank, hdegree] at hn
  have hpair : (∑ i ∈ Finset.Ico 1 p, ((p - i : ℕ) : F) * a i * a (p - i)) =
      ∑ i ∈ Finset.Ico 1 p, (i : F) * a i * a (p - i) := by
    have hr := Finset.sum_Ico_reflect (fun i => (i : F) * a i * a (p - i))
      1 (show p ≤ p + 1 by omega)
    simp only [Nat.add_sub_cancel_left, Nat.add_sub_cancel] at hr
    rw [← hr]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_Ico.mp hi
    rw [Nat.sub_sub_self (by omega : i ≤ p)]
    ring
  have hdouble : 2 * (∑ i ∈ Finset.Ico 1 p, ((p - i : ℕ) : F) * a i * a (p - i)) =
      (p : F) * ∑ i ∈ Finset.Ico 1 p, a i * a (p - i) := by
    calc
      _ = (∑ i ∈ Finset.Ico 1 p, ((p - i : ℕ) : F) * a i * a (p - i)) +
          ∑ i ∈ Finset.Ico 1 p, (i : F) * a i * a (p - i) := by rw [← hpair]; ring
      _ = _ := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Nat.cast_sub (by have := Finset.mem_Ico.mp hi; omega : i ≤ p)]
        ring
  have hexpand : (∑ i ∈ Finset.Ico 1 p, (-1 : F) ^ i * a i * s (p - i)) =
      (∑ i ∈ Finset.Ico 1 p, ((p - i : ℕ) : F) * a i * a (p - i)) +
      ∑ i ∈ Finset.Ico 1 p, (-1 : F) ^ i * a i *
        (s (p - i) - (-1 : F) ^ (p - i + 1) * (p - i : ℕ) * a (p - i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_Ico.mp hi
    have hsign' : (-1 : F) ^ i * (-1 : F) ^ (p - i + 1) = 1 := by
      rw [← pow_add, show i + (p - i + 1) = p + 1 by omega, hsign]
    linear_combination ((p - i : ℕ) : F) * a i * a (p - i) * hsign'
  change _ = (p : F) * (∑ i ∈ Finset.Ico 1 p, a i * a (p - i)) +
    2 * (∑ i ∈ Finset.Ico 1 p, (-1 : F) ^ i * a i *
      (s (p - i) - (-1 : F) ^ (p - i + 1) * (p - i : ℕ) * a (p - i))) + _
  change s p = (p : F) * norm F E x -
    ∑ i ∈ Finset.Ico 1 p, (-1 : F) ^ i * a i * s (p - i) at hn
  rw [hexpand] at hn
  linear_combination -2 * hn + hdouble

end Newton

section Depths
variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

omit [Module.Finite F E] [PrimeCyclicExtension F E] in
/-- Move a ceiling bound to the ramified field, without truncating
negative depths or excluding elements of infinite valuation. -/
private theorem traceDepth_map_bound {p : ℕ} (hp : 0 < p)
    (hram : ramificationIndex F E = p) {a : ℤ} {z : F}
    (hz : z ∈ lattice F ((a + p - 1) / p)) :
    algebraMap F E z ∈ lattice E a := by
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  have hfloor : a ≤ (p : ℤ) * ((a + p - 1) / p) := by
    have he := Int.emod_add_mul_ediv (a + p - 1) p
    have hr := Int.emod_lt_of_pos (a + p - 1) hpZ
    omega
  rw [mem_lattice, ord_algebraMap, hram]
  calc
    (a : WithTop ℤ) ≤ p • (((a + p - 1) / p : ℤ) : WithTop ℤ) := by
      simpa only [← WithTop.coe_nsmul, nsmul_eq_mul, WithTop.coe_le_coe] using hfloor
    _ ≤ p • ord F z := nsmul_le_nsmul_right hz p

/-- All three input bounds are constructed from the genuine different
and FML's symmetric and trace estimates. Upstairs their common numerator
is `(p-1)t`, so subsequent products have integer depths. -/
private theorem traceDepth_inputBounds {p t h : ℕ}
    (hdegree : Module.finrank F E = p) (htpos : 0 < t)
    (hchar : residueCharacteristic F = p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hres : residueDegree F E = 1)
    {x : E} (hx : x ∈ lattice E (-(h : ℤ))) :
    (p : E) ∈ lattice E (((p : ℤ) - 1) * t) ∧
    (∀ i : ℕ, 1 ≤ i → i < p →
      algebraMap F E (elementarySymmetric F E i x) ∈
        lattice E (((p : ℤ) - 1) * t - i * h)) ∧
    (∀ j : ℕ, 1 ≤ j →
      algebraMap F E (trace F E (x ^ j)) ∈
        lattice E (((p : ℤ) - 1) * t - j * h)) := by
  have hp : p.Prime := hdegree ▸ PrimeCyclicExtension.degree_prime F E
  have hram : ramificationIndex F E = p := by
    have he := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa only [hdegree, hres, mul_one] using he.symm
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have htrace := traceIdealLowerBound_of_integralGenerator F E ht hres pi hpi hgen
  rw [hdegree] at htrace
  have hconvert (j : ℕ) :
      (j : ℤ) * -(h : ℤ) + (((p - 1) * (t + 1) : ℕ) : ℤ) =
        (((p : ℤ) - 1) * t - j * h) + p - 1 := by
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hp.one_le]
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  · have hb := degree_natCast_ord_bound F E p _ hp.pos hdegree htrace
    have hD : (((p - 1) * (t + 1) : ℕ) : ℤ) =
        (((p : ℤ) - 1) * t) + p - 1 := by simpa using hconvert 0
    rw [hD] at hb
    simpa only [map_natCast] using traceDepth_map_bound F E hp.pos hram hb
  · intro i hi hip
    have hb := wild_elementarySymmetric_bound F E p (t + 1) (-(h : ℤ))
      hp (by omega) hchar hdegree htrace hx hi hip
    rw [hconvert] at hb
    exact traceDepth_map_bound F E hp.pos hram hb
  · intro j hj
    have hb := powerSum_bound F E p _ (-(h : ℤ)) hp.pos hdegree htrace hx j hj
    rw [hconvert] at hb
    exact traceDepth_map_bound F E hp.pos hram hb

/-- The two strict inequalities that distinguish the vanishing rows
from the terminal cubic row. -/
private theorem traceDepth_depths {p t h : ℕ} (hodd : 2 < p)
    (ht : 0 < t) (hh : h ≤ t) (hrow : h < t ∨ 3 < p) :
    (p : ℤ) * t < 2 * ((p : ℤ) - 1) * t - h ∧
    (p : ℤ) * t < 3 * ((p : ℤ) - 1) * t - p * h := by
  have hpZ : (3 : ℤ) ≤ p := by omega
  have htZ : (0 : ℤ) < t := by omega
  have hhZ : (h : ℤ) ≤ t := by omega
  rcases hrow with hlt | hlarge
  · have hltZ : (h : ℤ) < t := by omega
    have hb := mul_nonneg (show (0 : ℤ) ≤ p - 3 by omega) (le_of_lt htZ)
    have hc := mul_pos (show (0 : ℤ) < p by omega) (show (0 : ℤ) < t - h by omega)
    constructor <;> nlinarith
  · have hpZ' : (3 : ℤ) < p := by omega
    have hb := mul_pos (show (0 : ℤ) < p - 3 by omega) htZ
    have hc := mul_nonneg (show (0 : ℤ) ≤ p by omega) (show (0 : ℤ) ≤ t - h by omega)
    constructor <;> nlinarith

/-- The depth estimate for the scalar in `O:I:Sexact`. The only
hypothesis on the input is its lattice depth; in particular the result
includes integral inputs and `x = 0`. -/
theorem traceDepth_scalar {p t h : ℕ} (hodd : 2 < p)
    (hdegree : Module.finrank F E = p) (htpos : 0 < t)
    (hchar : residueCharacteristic F = p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hres : residueDegree F E = 1)
    {x : E} (hx : x ∈ lattice E (-(h : ℤ))) (hh : h ≤ t)
    (hrow : h < t ∨ 3 < p) :
    (p : F) * norm F E x - trace F E (x ^ p) + (p : F) * trace F E x ∈
      lattice F ((t : ℤ) + 1) := by
  classical
  have hp : p.Prime := hdegree ▸ PrimeCyclicExtension.degree_prime F E
  have hram : ramificationIndex F E = p := by
    have he := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa only [hdegree, hres, mul_one] using he.symm
  let B : ℤ := ((p : ℤ) - 1) * t
  let a : ℕ → E := fun i => algebraMap F E (elementarySymmetric F E i x)
  let s : ℕ → E := fun i => algebraMap F E (trace F E (x ^ i))
  let r : ℕ → E := fun j => s j - (-1 : E) ^ (j + 1) * j * a j
  let S : F := (p : F) * norm F E x - trace F E (x ^ p) + (p : F) * trace F E x
  obtain ⟨hpval, ha, hs⟩ := traceDepth_inputBounds F E hdegree htpos hchar ht hres hx
  change (p : E) ∈ lattice E B at hpval
  change ∀ i : ℕ, 1 ≤ i → i < p → a i ∈ lattice E (B - i * h) at ha
  change ∀ j : ℕ, 1 ≤ j → s j ∈ lattice E (B - j * h) at hs
  have hsign {z : E} {n : ℤ} (hz : z ∈ lattice E n) (i : ℕ) :
      (-1 : E) ^ i * z ∈ lattice E n := by
    rw [mem_lattice, ord_mul, ord_pow, ord_neg, ord_one, nsmul_zero, zero_add]
    exact hz
  have hr (j : ℕ) (hj : 1 ≤ j) (hjp : j < p) :
      r j ∈ lattice E (2 * B - j * h) := by
    have hn := congrArg (algebraMap F E) (traceDepth_newton F E x hj)
    simp only [map_sub, map_mul, map_pow, map_neg, map_one, map_natCast, map_sum] at hn
    change s j = (-1 : E) ^ (j + 1) * j * a j -
      ∑ i ∈ Finset.Ico 1 j, (-1 : E) ^ i * a i * s (j - i) at hn
    have heq : r j = -(∑ i ∈ Finset.Ico 1 j, (-1 : E) ^ i * a i * s (j - i)) := by
      dsimp only [r]
      rw [hn]
      ring
    rw [heq]
    apply neg_mem_lattice E
    apply sum_mem_lattice E
    intro i hi
    obtain ⟨hi, hij⟩ := Finset.mem_Ico.mp hi
    have hm := hsign (mul_mem_lattice E (ha i hi (by omega))
      (hs (j - i) (by omega))) i
    have hdepth : (B - (i : ℤ) * h) + (B - (j - i : ℕ) * h) =
        2 * B - j * h := by
      rw [Nat.cast_sub (by omega : i ≤ j)]
      ring
    simpa only [hdepth, mul_assoc] using hm
  have hquad : (p : E) * (∑ i ∈ Finset.Ico 1 p, a i * a (p - i)) ∈
      lattice E (3 * B - p * h) := by
    rw [Finset.mul_sum]
    apply sum_mem_lattice E
    intro i hi
    obtain ⟨hi, hip⟩ := Finset.mem_Ico.mp hi
    have hm := mul_mem_lattice E hpval
      (mul_mem_lattice E (ha i hi hip) (ha (p - i) (by omega) (by omega)))
    have hdepth : B + ((B - (i : ℤ) * h) + (B - (p - i : ℕ) * h)) =
        3 * B - p * h := by
      rw [Nat.cast_sub (by omega : i ≤ p)]
      ring
    simpa only [hdepth] using hm
  have hrem : (∑ i ∈ Finset.Ico 1 p, (-1 : E) ^ i * a i * r (p - i)) ∈
      lattice E (3 * B - p * h) := by
    apply sum_mem_lattice E
    intro i hi
    obtain ⟨hi, hip⟩ := Finset.mem_Ico.mp hi
    have hm := hsign (mul_mem_lattice E (ha i hi hip) (hr (p - i) (by omega) (by omega))) i
    have hdepth : (B - (i : ℤ) * h) + (2 * B - (p - i : ℕ) * h) =
        3 * B - p * h := by
      rw [Nat.cast_sub (by omega : i ≤ p)]
      ring
    simpa only [hdepth, mul_assoc] using hm
  have hlin : (p : E) * s 1 ∈ lattice E (2 * B - h) := by
    have hdepth : B + (B - (1 : ℕ) * (h : ℤ)) = 2 * B - h := by push_cast; ring
    simpa only [hdepth] using mul_mem_lattice E hpval (hs 1 (by omega))
  have hid : 2 * algebraMap F E S =
      (p : E) * (∑ i ∈ Finset.Ico 1 p, a i * a (p - i)) +
      2 * (∑ i ∈ Finset.Ico 1 p, (-1 : E) ^ i * a i * r (p - i)) + 2 * ((p : E) * s 1) := by
    simpa only [S, a, s, r, map_add, map_sub, map_mul, map_pow, map_neg, map_one,
      map_ofNat, map_natCast, map_sum, pow_one, mul_assoc] using
      congrArg (algebraMap F E)
        (traceDepth_secondOrder F E (hp.odd_of_ne_two (by omega)) hdegree x)
  obtain ⟨hdepth1, hdepth3⟩ := traceDepth_depths hodd htpos hh hrow
  have hS2 : 2 * algebraMap F E S ∈ lattice E ((p : ℤ) * t + 1) := by
    rw [hid]
    apply add_mem_lattice E
    · apply lattice_antitone E
        (show (p : ℤ) * t + 1 ≤ 3 * B - p * h by dsimp [B]; nlinarith only [hdepth3])
      apply add_mem_lattice E hquad
      simpa only [two_mul] using add_mem_lattice E hrem hrem
    · apply lattice_antitone E
        (show (p : ℤ) * t + 1 ≤ 2 * B - h by dsimp [B]; nlinarith only [hdepth1])
      simpa only [two_mul] using add_mem_lattice E hlin hlin
  have htwo : ord E (2 : E) = 0 :=
    ord_natCast_eq_zero_of_lt_residueCharacteristic E (by omega : 0 < 2)
      (by rw [residueCharacteristic_extension_eq F E, hchar]; exact hodd)
  rw [mem_lattice, ord_mul, htwo, zero_add, ord_algebraMap, hram] at hS2
  change S ∈ lattice F ((t : ℤ) + 1)
  by_cases htop : ord F S = ⊤
  · simp [mem_lattice, htop]
  · obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hv, ← WithTop.coe_nsmul, WithTop.coe_le_coe, nsmul_eq_mul] at hS2
    rw [mem_lattice, ← hv, WithTop.coe_le_coe]
    have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
    have : (t : ℤ) < v := by nlinarith
    omega

end Depths

section Assembly
variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  (E U : IntermediateField F K)

local instance traceDepthValuativeRelE : ValuativeRel E := Basic.intermediateFieldValuativeRel E
local instance traceDepthTopologyE : TopologicalSpace E := Basic.intermediateFieldTopology E
local instance traceDepthLocalFieldE : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E
local instance traceDepthLowerExtensionE : ValuativeExtension F E := Basic.intermediateField_lowerValuativeExtension E
local instance traceDepthUpperExtensionE : ValuativeExtension E K := Basic.intermediateField_upperValuativeExtension E
local instance traceDepthValuativeRelU : ValuativeRel U := Basic.intermediateFieldValuativeRel U
local instance traceDepthTopologyU : TopologicalSpace U := Basic.intermediateFieldTopology U
local instance traceDepthLocalFieldU : IsNonarchimedeanLocalField U := Basic.intermediateField_localField U
local instance traceDepthLowerExtensionU : ValuativeExtension F U := Basic.intermediateField_lowerValuativeExtension U
local instance traceDepthUpperExtensionU : ValuativeExtension U K := Basic.intermediateField_upperValuativeExtension U

variable {p : ℕ} (hp : p.Prime)
  (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
  (hFE : Module.finrank F E = p) (hFU : Module.finrank F U = p)

include hp hG hFE hFU

/-- **Paper Lemma 6.12 (`O:I:Sdepth`).**

For the actual primitive compatible pair, retain the norm witness and
all the data constructed by `scalarPhase`, and prove the depth of the
literal trace difference `S`. The additional row condition includes
`h = 0`, every `h < t`, and `h = t` for `p > 3`.

The ideal-membership proof is separate from the exact Artin--Schreier
trace cancellations already contained in `ScalarPhaseAt`. No trace
identity or exact norm choice is added as an unproved input.
-/
theorem traceDepth
    {t q : ℕ} (hodd : 2 < p) (htpos : 0 < t)
    (hchar : residueCharacteristic F = p) :
  letI : IsGalois F E :=
    (Basic.intermediateField_tower_compatible hp hG E hFE).2.2.2.2.2.2.2.2.2.2.2.1.1
  letI : IsGalois F U :=
    (Basic.intermediateField_tower_compatible hp hG U hFU).2.2.2.2.2.2.2.2.2.2.2.1.1
  ∀ (_ht : PrimeCyclicExtension.IsLowerBreak F E t) (_hres : residueDegree F E = 1)
    (_hunr : ramificationIndex F U = 1) (_hsup : E ⊔ U = ⊤)
    (_hne : Ramification.intermediateNormRange U ≠ Ramification.intermediateNormRange E)
    (_hq : q = (t + 1) ⌈/⌉ p) {hqpos : 0 < q}
    (tau : NormCharacter F E) (_htaune : tau ≠ 1)
    (psiF : LocalAddCharData F) (alpha : Fˣ)
    (_hPsi : (scaleAddCharData F psiF alpha).conductor = -((t + 1 : ℕ) : ℤ))
    (_htau : ∀ z : lattice F (q : ℤ),
      tau.1 (positiveUnitOfLattice F hqpos (-z)) =
        (scaleAddCharData F psiF alpha).character (truncatedLog p (z : F)))
    (c : ringOfIntegers F) (d : ringOfIntegers U)
    (_hd : (d : U) ^ p - (d : U) = algebraMap F U (c : F))
    (_hgen : IntermediateField.adjoin F {(d : U)} = ⊤)
    {M : CompatibleModels F E U K p (t + 1) q hqpos tau.1
      (scaleAddCharData F psiF alpha).character (c : F) (d : U)}
    {thetaU : ContinuousQuasiChar U} {thetaE : ContinuousQuasiChar E}
    (_hcomp : normQuasiChar U K thetaU = normQuasiChar E K thetaE)
    (_hprimitive : ¬ ∃ chi : ContinuousQuasiChar F, normQuasiChar F K chi = normQuasiChar U K thetaU)
    (D : ActualTwist F E U K M thetaU thetaE) (_hh : D.h ≤ t) (_hrow : D.h < t ∨ 3 < p),
    ∃ (x : E) (epsilon : F),
      epsilon ∈ lattice F 0 ∧
      (D.h < t → epsilon = 0) ∧
      (∀ z : lattice F (((t + 1 + D.h) / 2 : ℕ) : ℤ),
        D.lambda (positiveUnitOfLattice F (normChoice_depths hodd htpos).1 (-z)) =
          (scaleAddCharData F psiF alpha).character
            ((norm F E x + epsilon) * truncatedLog p (z : F))) ∧
      (0 < D.h → ord E x = ((-(D.h : ℤ) : ℤ) : WithTop ℤ) ∧
        ord F (norm F E x) = ((-(D.h : ℤ) : ℤ) : WithTop ℤ)) ∧
      (D.h = 0 → x ∈ lattice E 0) ∧
      (QuasiCharTrivialOnUnitFiltration F D.lambda ((t + 1 + D.h) / 2) →
        x = 0 ∧ norm F E x = 0 ∧ epsilon = 0) ∧
      NormDepthsAt F E U K thetaU thetaE (scaleAddCharData F psiF alpha).character
        p t D.h (c : F) (d : U) x epsilon ∧
      ScalarPhaseAt F E U K thetaU thetaE psiF.character (scaleAddCharData F psiF alpha).character
        p (c : F) (d : U) x epsilon ∧
      (trace F U (norm U K (algebraMap E K x + algebraMap U K (d : U))) -
        trace F E (norm E K (algebraMap E K x + algebraMap U K (d : U)))) ∈
          lattice F ((t : ℤ) + 1) := by
  letI : PrimeCyclicExtension F E :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F E
      (Basic.intermediateField_tower_compatible hp hG E hFE).2.2.2.2.2.2.2.2.2.2.2.1
  letI : PrimeCyclicExtension F U :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F U
      (Basic.intermediateField_tower_compatible hp hG U hFU).2.2.2.2.2.2.2.2.2.2.2.1
  letI : PrimeCyclicExtension E K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension E K
      (Basic.intermediateField_tower_compatible hp hG E hFE).2.2.2.2.2.2.2.2.2.2.2.2
  letI : PrimeCyclicExtension U K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension U K
      (Basic.intermediateField_tower_compatible hp hG U hFU).2.2.2.2.2.2.2.2.2.2.2.2
  letI : IsGalois F E := PrimeCyclicExtension.instIsGalois F E
  letI : IsGalois F U := PrimeCyclicExtension.instIsGalois F U
  intro ht hres hunr hsup hne hq hqpos tau htaune psiF alpha hPsi htau c d hd hgen
    M thetaU thetaE hcomp hprimitive D hh hrow
  obtain ⟨x, epsilon, hepsilon, hepsilon_zero, hchart, horder, hintegral, hzero, R, P⟩ :=
    scalarPhase F K E U hp hG hFE hFU hodd htpos hchar ht hres hunr hsup hne hq
      tau htaune psiF alpha hPsi htau c d hd hgen hcomp hprimitive D hh
  refine ⟨x, epsilon, hepsilon, hepsilon_zero, hchart, horder, hintegral, hzero, R, P, ?_⟩
  have hx : x ∈ lattice E (-(D.h : ℤ)) := by
    by_cases hhzero : D.h = 0
    · simpa only [hhzero, Nat.cast_zero, neg_zero] using hintegral hhzero
    · rw [mem_lattice, (horder (by omega)).1]
  rw [P.2]
  exact traceDepth_scalar F E hodd hFE htpos hchar ht hres hx hh hrow

end Assembly

end

end LanglandsSecondMainLemma.Odd.UR
