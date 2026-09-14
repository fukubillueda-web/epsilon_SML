import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Linear.ActualNorm

/-!
# Odd / Linear / Split

Paper: `O:W:normquotient`, `O:W:p3root`, and `O:W:split`.

The rational summands and the signed exceptional summands retain their
actual coefficients. In particular, the exceptional sum has no rational
interpolation denominator. All congruences use integer fractional lattices.
-/

namespace LanglandsSecondMainLemma.Odd.Linear

noncomputable section
open LanglandsFirstMainLemma
open scoped BigOperators

open private pow_mem_int_lattice natCast_mem_int_lattice_zero
  translated_root_torsion_ord translated_root_center_ord
  translatedNorm_representatives_separated from
  LanglandsSecondMainLemma.Odd.Total.TranslatedNorm
open private one_add_div_order ne_zero_of_order from
  LanglandsSecondMainLemma.Odd.Linear.Setup
open private realization_tower_data from
  LanglandsSecondMainLemma.Odd.Models.Realization
open private correctionFormula_norm_add_algebraMap from
  LanglandsFirstMainLemma.Cases.WildOdd.CorrectionFormula

section Estimates

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

private theorem split_div_mem {x y : E} {q r : ℤ}
    (hx : x ∈ lattice E q) (hy : ord E y = (r : WithTop ℤ)) :
    x / y ∈ lattice E (q - r) := by
  apply (div_mem_lattice_iff E y x r (q - r) hy).2
  simpa only [add_sub_cancel] using hx

private theorem split_pow_sub_mem {x y : E} {d q : ℤ}
    (hx : x ∈ lattice E d) (hy : y ∈ lattice E d)
    (hxy : x - y ∈ lattice E q) (i : ℕ) :
    x ^ i - y ^ i ∈ lattice E (q + ((i : ℤ) - 1) * d) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have heq : x ^ (i + 1) - y ^ (i + 1) =
        (x ^ i - y ^ i) * x + y ^ i * (x - y) := by
      simp only [pow_succ]; ring
    rw [heq]
    apply (lattice E _).add_mem
    · convert mul_mem_lattice E ih hx using 1; push_cast; ring
    · convert mul_mem_lattice E (pow_mem_int_lattice E hy i) hxy using 1
      push_cast
      ring

private theorem split_weighted_power_mem {x y w g : E} {d q r s : ℤ}
    (hx : x ∈ lattice E d) (hy : y ∈ lattice E d)
    (hxy : x - y ∈ lattice E q) (hw : ord E w = (r : WithTop ℤ))
    (hg : g ∈ lattice E s) (i : ℕ) :
    (x / w) ^ i * g - (y / w) ^ i * g ∈
      lattice E (q + ((i : ℤ) - 1) * d - (i : ℤ) * r + s) := by
  have hwi : ord E (w ^ i) = (((i : ℤ) * r : ℤ) : WithTop ℤ) := by
    simp only [ord_pow, hw, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have h := mul_mem_lattice E
    (split_div_mem E (split_pow_sub_mem E hx hy hxy i) hwi) hg
  convert h using 1
  rw [div_pow, div_pow, sub_div]
  ring

/-- Integer arithmetic for the pointwise replacement when `p≥5`.
The full pole `-p*t` of the quotient is included. -/
private theorem split_large_depth (p t delta M V i : ℤ)
    (hp : 5 ≤ p) (ht : 1 ≤ t) (hd : 0 ≤ delta) (hM : t + 1 ≤ M)
    (hV : p * (p - 1) * (t + delta) ≤ V) (hi : 1 ≤ i) :
    1 + p * (t + delta) ≤ V + i * M - (2 * p + i - 2) * t := by
  have hM' := mul_nonneg (sub_nonneg.mpr hM) (by omega : 0 ≤ i)
  have hpoly : 0 ≤ p ^ 2 - 4 * p + 2 := by nlinarith
  have hpt := mul_nonneg hpoly (by omega : 0 ≤ t)
  have hdelta := mul_nonneg (mul_nonneg (by omega : 0 ≤ p)
    (by omega : 0 ≤ p - 2)) hd
  nlinarith

private theorem split_correction_depth (p t u V : ℤ)
    (hp : 3 ≤ p) (ht : 1 ≤ t) (htu : t ≤ u)
    (hV : p * (p - 1) * u ≤ V) : 1 ≤ V - (p - 1) * t := by
  have hbase : 1 ≤ (p - 1) * t := by nlinarith
  have hgap := mul_nonneg (mul_nonneg (by omega : 0 ≤ p - 1)
    (by omega : 0 ≤ p - 1)) (by omega : 0 ≤ t)
  have htu' := mul_nonneg (mul_nonneg (by omega : 0 ≤ p)
    (by omega : 0 ≤ p - 1)) (sub_nonneg.mpr htu)
  nlinarith

/-- The first cubic Newton iterate gives precisely the refinement used
in `O:W:p3root`. The correction is for the actual root supplied as input. -/
private theorem split_cubic_root
    (Delta xi eta : E) (t V : ℤ) (ht : 0 ≤ t) (hVt : 3 * t ≤ V)
    (hxi : xi ^ 2 = 1)
    (hDelta : ord E Delta = ((-t : ℤ) : WithTop ℤ))
    (hcenter : ord E (Delta + xi) = ((-t : ℤ) : WithTop ℤ))
    (hV : ord E (3 : E) = (V : WithTop ℤ))
    (heta : eta ∈ lattice E (V - 2 * t))
    (hroot : (Delta + xi + eta) ^ 3 - (Delta + xi + eta) = Delta ^ 3 - Delta) :
    eta - 3 * xi * Delta ^ 2 ∈ lattice E (V - t) := by
  have hfirst := (Total.translatedRootUnit_cubic_iterates E t V ht (by omega)
    Delta xi eta hxi hcenter hV heta hroot).1
  have hne : Delta + xi ≠ 0 := ne_zero_of_order E hcenter
  have hcenterMem : Delta + xi ∈ lattice E (-t) := (mem_lattice E).2 hcenter.ge
  have hthree : (3 : E) ∈ lattice E V := (mem_lattice E).2 hV.ge
  have hDeltaMem : Delta ∈ lattice E (-t) := (mem_lattice E).2 hDelta.ge
  have herror : eta - 3 * xi * Delta ^ 2 =
      (Delta + xi) * (Total.translatedRootUnit Delta xi eta - 3 * xi * Delta) +
        3 * Delta := by
    dsimp only [Total.translatedRootUnit]
    field_simp
    linear_combination 3 * Delta * hxi
  rw [herror]
  apply (lattice E _).add_mem
  · have h := mul_mem_lattice E hcenterMem hfirst
    exact lattice_antitone E (by omega) h
  · simpa only [sub_eq_add_neg] using mul_mem_lattice E hthree hDeltaMem

/-- The exact divided difference, with a fixed derivative denominator.
Its error only uses integral displacements from `b` and the actual unit
denominators. No surjectivity of a norm map is involved. -/
private theorem split_quotient_linearization
    (x y b W k : E) (N H S : ℤ)
    (hW : ord E W = ((-N : ℤ) : WithTop ℤ))
    (hx : ord E (1 + x / W) = 0) (hy : ord E (1 + y / W) = 0)
    (hb : ord E (1 + b / W) = 0)
    (hxb : x - b ∈ lattice E 0) (hyb : y - b ∈ lattice E 0)
    (hk : k ∈ lattice E S) (herror : x - y + k ∈ lattice E H)
    (hdepth : H ≤ N + S) :
    x / (1 + x / W) - (y / (1 + y / W) - k / (1 + b / W) ^ 2) ∈
      lattice E H := by
  let A := 1 + x / W
  let B := 1 + y / W
  let C := 1 + b / W
  have hA : A ≠ 0 := ne_zero_of_order E (n := 0) hx
  have hB : B ≠ 0 := ne_zero_of_order E (n := 0) hy
  have hC : C ≠ 0 := ne_zero_of_order E (n := 0) hb
  have hWne := ne_zero_of_order E hW
  have hAB : ord E (A * B) = 0 := by rw [ord_mul, hx, hy, add_zero]
  have hABC : ord E (A * B * C ^ 2) = 0 := by
    rw [ord_mul, hAB, ord_pow, hb, nsmul_zero, add_zero]
  have hdiff : A * B - C ^ 2 ∈ lattice E N := by
    have heq : A * B - C ^ 2 = (x - b) / W * B + C * ((y - b) / W) := by
      dsimp only [A, B, C]; field_simp; ring
    rw [heq]
    apply (lattice E N).add_mem
    · convert mul_mem_lattice E (split_div_mem E hxb hW)
        ((mem_lattice E).2 hy.ge) using 1; ring
    · convert mul_mem_lattice E ((mem_lattice E).2 hb.ge)
        (split_div_mem E hyb hW) using 1; ring
  have heq : x / A - (y / B - k / C ^ 2) =
      (x - y + k) / (A * B) + k * (A * B - C ^ 2) / (A * B * C ^ 2) := by
    field_simp
    dsimp only [A, B, C]
    ring
  change x / A - (y / B - k / C ^ 2) ∈ _
  rw [heq]
  apply (lattice E H).add_mem
  · simpa only [sub_zero] using split_div_mem E herror hAB
  · apply lattice_antitone E (by omega)
    simpa only [sub_zero, add_comm] using split_div_mem E (mul_mem_lattice E hk hdiff) hABC

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem split_sum_three (c : ZMod 3 → E)
    (hc0 : c 0 = 0) (hc1 : c 1 = 1) (hcsum : ∑ j, c j = 0) (f : E → E) :
    (∑ j, f (c j)) = f 0 + f 1 + f (-1) := by
  have hc2 : c 2 = -1 := by
    change (∑ j : Fin 3, c j) = 0 at hcsum
    rw [Fin.sum_univ_three] at hcsum
    change c (0 : ZMod 3) + c (1 : ZMod 3) + c (2 : ZMod 3) = 0 at hcsum
    rw [hc0, hc1] at hcsum
    linear_combination hcsum
  change (∑ j : Fin 3, f (c j)) = _
  rw [Fin.sum_univ_three]
  change f (c (0 : ZMod 3)) + f (c (1 : ZMod 3)) + f (c (2 : ZMod 3)) = _
  rw [hc0, hc1, hc2]

/-- The cubic rational identities and the signed power sums are used
together. The latter contribute `2*(lambda-1)` and
`4*(lambda-1)*Delta`, with no factor `Y+xi` in their denominators. -/
private theorem split_cubic_sum_error
    (Delta w b W s lam : E) (c : ZMod 3 → E)
    (t delta M V : ℤ) (ht : 1 ≤ t) (hd : 0 ≤ delta)
    (hM : t + 1 ≤ M) (hV : 6 * (t + delta) ≤ V)
    (hDelta : ord E Delta = ((-t : ℤ) : WithTop ℤ))
    (hw : ord E w = ((-M : ℤ) : WithTop ℤ))
    (hb : ord E b = ((-3 * t : ℤ) : WithTop ℤ))
    (hW : ord E W = ((-3 * M : ℤ) : WithTop ℤ))
    (hY : ord E (W + b) = ((-3 * M : ℤ) : WithTop ℤ))
    (hC : ord E (1 + b / W) = 0)
    (hs : s ∈ lattice E (6 * delta)) (hlam : lam ∈ lattice E 0)
    (hlam1 : lam - 1 ∈ lattice E (V - 2 * t))
    (hc0 : c 0 = 0) (hc1 : c 1 = 1) (hcsum : ∑ j, c j = 0)
    (i : ℕ) (hi : 1 ≤ i) (hi3 : i < 3) :
    (∑ j, ((Delta + lam * c j) / w) ^ i *
      (W * (b + c j) / (W + b + c j) - c j * s / (1 + b / W) ^ 2)) -
    (∑ j, ((Delta + c j) / w) ^ i *
      (W * (b + c j) / (W + b + c j) - c j * s / (1 + b / W) ^ 2)) ∈
      lattice E (1 + 3 * (t + delta)) := by
  let Y := W + b
  let C := 1 + b / W
  have hYsq : ord E (Y ^ 2 - 1) = ((-6 * M : ℤ) : WithTop ℤ) := by
    have hpow : ord E (Y ^ 2) = ((-6 * M : ℤ) : WithTop ℤ) := by
      rw [ord_pow, show ord E Y = _ from hY, ← WithTop.coe_nsmul]
      simp only [nsmul_eq_mul]
      congr 1; ring
    rw [sub_eq_add_neg, (ord E).map_add_eq_of_lt_left (by
      rw [hpow, ord_neg, ord_one]
      exact WithTop.coe_lt_coe.mpr (by omega)), hpow]
  have hWne := ne_zero_of_order E hW
  have hwne := ne_zero_of_order E hw
  have hYne := ne_zero_of_order E hY
  have hCne : C ≠ 0 := ne_zero_of_order E (n := 0) hC
  have hYsqne := ne_zero_of_order E hYsq
  have hYminus : W + b - 1 ≠ 0 := by
    intro h; apply hYsqne
    change (W + b) ^ 2 - 1 = 0
    rw [sub_eq_zero.mp h]; ring
  have hYp : W + b + 1 ≠ 0 := by
    intro h; apply hYsqne
    have heq : W + b = -1 := by linear_combination h
    change (W + b) ^ 2 - 1 = 0
    rw [heq]; ring
  have hw2 : ord E (w ^ 2) = ((-2 * M : ℤ) : WithTop ℤ) := by
    simp only [ord_pow, hw, ← WithTop.coe_nsmul, nsmul_eq_mul]; congr 1; ring
  have hCC : ord E (C ^ 2) = 0 := by rw [ord_pow, hC, nsmul_zero]
  have hone : (1 : E) ∈ lattice E 0 := by simp only [mem_lattice, ord_one]; rfl
  have htwo : (2 : E) ∈ lattice E 0 := by simpa using natCast_mem_int_lattice_zero E 2
  have hfour : (4 : E) ∈ lattice E 0 := by simpa using natCast_mem_int_lattice_zero E 4
  have hDm : Delta ∈ lattice E (-t) := (mem_lattice E).2 hDelta.ge
  have hWm : W ∈ lattice E (-3 * M) := (mem_lattice E).2 hW.ge
  have hbm : b ∈ lattice E (-3 * t) := (mem_lattice E).2 hb.ge
  have hYm : Y ∈ lattice E (-3 * M) := (mem_lattice E).2 hY.ge
  rw [split_sum_three E c hc0 hc1 hcsum (fun z => ((Delta + lam * z) / w) ^ i *
      (W * (b + z) / (W + b + z) - z * s / (1 + b / W) ^ 2)),
    split_sum_three E c hc0 hc1 hcsum (fun z => ((Delta + z) / w) ^ i *
      (W * (b + z) / (W + b + z) - z * s / (1 + b / W) ^ 2))]
  rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
  · have heq :
        ((Delta + lam * 0) / w) ^ 1 * (W * (b + 0) / (W + b + 0) - 0 * s / C ^ 2) +
        ((Delta + lam * 1) / w) ^ 1 * (W * (b + 1) / (W + b + 1) - 1 * s / C ^ 2) +
        ((Delta + lam * -1) / w) ^ 1 * (W * (b + -1) / (W + b + -1) - -1 * s / C ^ 2) -
        (((Delta + 0) / w) ^ 1 * (W * (b + 0) / (W + b + 0) - 0 * s / C ^ 2) +
        ((Delta + 1) / w) ^ 1 * (W * (b + 1) / (W + b + 1) - 1 * s / C ^ 2) +
        ((Delta + -1) / w) ^ 1 * (W * (b + -1) / (W + b + -1) - -1 * s / C ^ 2)) =
        2 * (lam - 1) * W ^ 2 / (w * (Y ^ 2 - 1)) -
          2 * (lam - 1) * s / (w * C ^ 2) := by
      rw [show Y ^ 2 - 1 = (W + b - 1) * (W + b + 1) by dsimp only [Y]; ring]
      simp only [pow_one, mul_zero, add_zero, zero_mul, zero_div, sub_zero,
        mul_one, one_mul, mul_neg, ← sub_eq_add_neg]
      field_simp [hwne, hYminus, hYp, hCne]
      ring
    rw [heq]
    apply (lattice E _).sub_mem
    · have hden : ord E (w * (Y ^ 2 - 1)) = ((-7 * M : ℤ) : WithTop ℤ) := by
        rw [ord_mul, hw, hYsq, ← WithTop.coe_add]; congr 1; ring
      have h := split_div_mem E (mul_mem_lattice E (mul_mem_lattice E htwo hlam1)
        (pow_mem_int_lattice E hWm 2)) hden
      apply lattice_antitone E _ h
      norm_num; omega
    · have hden : ord E (w * C ^ 2) = ((-M : ℤ) : WithTop ℤ) := by
        rw [ord_mul, hw, hCC, add_zero]
      have h := split_div_mem E (mul_mem_lattice E (mul_mem_lattice E htwo hlam1) hs) hden
      exact lattice_antitone E (by omega) h
  · have heq :
        ((Delta + lam * 0) / w) ^ 2 * (W * (b + 0) / (W + b + 0) - 0 * s / C ^ 2) +
        ((Delta + lam * 1) / w) ^ 2 * (W * (b + 1) / (W + b + 1) - 1 * s / C ^ 2) +
        ((Delta + lam * -1) / w) ^ 2 * (W * (b + -1) / (W + b + -1) - -1 * s / C ^ 2) -
        (((Delta + 0) / w) ^ 2 * (W * (b + 0) / (W + b + 0) - 0 * s / C ^ 2) +
        ((Delta + 1) / w) ^ 2 * (W * (b + 1) / (W + b + 1) - 1 * s / C ^ 2) +
        ((Delta + -1) / w) ^ 2 * (W * (b + -1) / (W + b + -1) - -1 * s / C ^ 2)) =
        2 * W * (lam - 1) * ((lam + 1) * (b * Y - 1) + 2 * W * Delta) /
          (w ^ 2 * (Y ^ 2 - 1)) - 4 * (lam - 1) * Delta * s / (w ^ 2 * C ^ 2) := by
      rw [show Y ^ 2 - 1 = (W + b - 1) * (W + b + 1) by dsimp only [Y]; ring]
      dsimp only [Y]
      simp only [mul_zero, add_zero, zero_mul, zero_div, sub_zero,
        mul_one, one_mul, mul_neg, ← sub_eq_add_neg]
      field_simp [hwne, hYminus, hYp, hCne]
      ring
    rw [heq]
    have hbracket : (lam + 1) * (b * Y - 1) + 2 * W * Delta ∈
        lattice E (-3 * t - 3 * M) := by
      apply (lattice E _).add_mem
      · have hunit : lam + 1 ∈ lattice E 0 :=
          (lattice E 0).add_mem hlam hone
        have hby : b * Y - 1 ∈ lattice E (-3 * t - 3 * M) := by
          apply (lattice E _).sub_mem
          · convert mul_mem_lattice E hbm hYm using 1; ring
          · exact lattice_antitone E (by omega) hone
        simpa using mul_mem_lattice E hunit hby
      · have h := mul_mem_lattice E (mul_mem_lattice E htwo hWm) hDm
        exact lattice_antitone E (by omega) h
    apply (lattice E _).sub_mem
    · have hden : ord E (w ^ 2 * (Y ^ 2 - 1)) = ((-8 * M : ℤ) : WithTop ℤ) := by
        rw [ord_mul, hw2, hYsq, ← WithTop.coe_add]; congr 1; ring
      have h := split_div_mem E (mul_mem_lattice E
        (mul_mem_lattice E (mul_mem_lattice E htwo hWm) hlam1) hbracket) hden
      exact lattice_antitone E (by omega) h
    · have hden : ord E (w ^ 2 * C ^ 2) = ((-2 * M : ℤ) : WithTop ℤ) := by
        rw [ord_mul, hw2, hCC, add_zero]
      have h := split_div_mem E (mul_mem_lattice E
        (mul_mem_lattice E (mul_mem_lattice E hfour hlam1) hDm) hs) hden
      exact lattice_antitone E (by omega) h

end Estimates

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

variable {Delta : K} {a : D.B₂} {w : D.B₂ˣ} {m : ℤ}
  (L : OddLinearData D Delta a w m)

include L

omit [Module.Free F K] in
/-- The exact affine norm polynomial leaves the signed coefficient
`-xi*s`; the remaining coefficients have depth at least `p*t₂`. -/
theorem split_norm_polynomial
    (xi : F) (hxi : xi = 0 ∨ xi ^ (p - 1) = 1) :
    algebraMap B₁ K (norm B₁ K (Delta + algebraMap F K xi)) -
      (algebraMap B₁ K (norm B₁ K Delta) + algebraMap F K xi) +
        algebraMap F K xi * algebraMap B₁ K (linearS D Delta) ∈
      lattice K ((p : ℤ) * D.t₂) := by
  rcases hxi with rfl | hxi
  · simp
  have hp3 := D.odd_prime
  have ht : (0 : ℤ) ≤ D.t := by positivity
  have hd : (0 : ℤ) ≤ D.delta := by positivity
  have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
  let c : B₁ := algebraMap F B₁ xi
  have hc : c ^ (p - 1) = 1 := by simp only [c, ← map_pow, hxi, map_one]
  have hcne : c ≠ 0 := by
    intro hz; rw [hz, zero_pow (by omega)] at hc; exact zero_ne_one hc
  have hcp : c ^ p = c := by
    calc
      c ^ p = c ^ (p - 1 + 1) := congrArg (c ^ ·) (by omega)
      _ = c := by rw [pow_succ, hc, one_mul]
  have hdegree : Module.finrank B₁ K = p :=
    (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.2.2.1
  have hn := correctionFormula_norm_add_algebraMap B₁ K p hdegree Delta c hcne
  let f (r : ℕ) := c ^ (p - r) * elementarySymmetric B₁ K r Delta
  have hn' : norm B₁ K (Delta + algebraMap B₁ K c) =
      (∑ r ∈ Finset.range (p - 2), f (r + 1)) +
        c * elementarySymmetric B₁ K (p - 1) Delta + c + norm B₁ K Delta := by
    have hs := Finset.sum_range_succ' f (p - 1)
    rw [Nat.sub_add_cancel hp.one_le] at hs
    have hs' := Finset.sum_range_succ (fun r => f (r + 1)) (p - 2)
    rw [show p - 2 + 1 = p - 1 by omega] at hs'
    rw [hn]
    change (∑ r ∈ Finset.range (p + 1), f r) = _
    rw [Finset.sum_range_succ, hs, hs']
    have hf0 : f 0 = c := by simp only [f, Nat.sub_zero, elementarySymmetric_zero,
      mul_one, hcp]
    have hfp : f p = norm B₁ K Delta := by
      simp only [f, Nat.sub_self, pow_zero, one_mul]
      simpa only [hdegree] using elementarySymmetric_finrank B₁ K Delta
    have hfpen : f (p - 1) = c * elementarySymmetric B₁ K (p - 1) Delta := by
      simp only [f, show p - (p - 1) = 1 by omega, pow_one]
    rw [hf0, hfp, hfpen]
  have heq : algebraMap B₁ K (norm B₁ K (Delta + algebraMap F K xi)) -
      (algebraMap B₁ K (norm B₁ K Delta) + algebraMap F K xi) +
        algebraMap F K xi * algebraMap B₁ K (linearS D Delta) =
      ∑ r ∈ Finset.range (p - 2), algebraMap B₁ K (f (r + 1)) := by
    have hcmap : algebraMap B₁ K c = algebraMap F K xi :=
      (IsScalarTower.algebraMap_apply F B₁ K xi).symm
    rw [← hcmap, hn', map_add, map_add, map_add, map_mul,
      linearS, map_neg, map_sum]
    ring
  rw [heq]
  apply sum_mem_lattice K
  intro r hr
  have hrlt := Finset.mem_range.mp hr
  have hcK : ord K (algebraMap B₁ K c) = 0 :=
    translated_root_torsion_ord K (by omega : 0 < p - 1) _
      (by rw [← map_pow, hc, map_one])
  have hcPow : algebraMap B₁ K c ^ (p - (r + 1)) ∈ lattice K 0 := by
    simp only [mem_lattice, ord_pow, hcK, nsmul_zero, WithTop.coe_zero, le_refl]
  have he := mul_mem_lattice K hcPow ((mem_lattice K).2
    (L.symmetric_order (r + 1) (by omega) (by omega)))
  simp only [f, map_mul, map_pow]
  apply lattice_antitone K _ he
  simp only [zero_add]
  have hgap : 0 ≤ ((p : ℤ) - 2 - (r + 1 : ℕ)) * D.t :=
    mul_nonneg (by omega) ht
  have hdel : 0 ≤ ((p : ℤ) - 2) * D.delta := mul_nonneg (by omega) hd
  have hpz : (0 : ℤ) ≤ p := by positivity
  apply mul_le_mul_of_nonneg_left _ hpz
  rw [ht₂]
  nlinarith

omit [Module.Free F K] [IsGalois F K] L [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [ValuativeExtension F K] [Module.Finite F K] in
private theorem split_shift_integral (hp : p.Prime)
    (xi : F) (hxi : xi = 0 ∨ xi ^ (p - 1) = 1) :
    algebraMap F K xi ∈ lattice K 0 := by
  rcases hxi with rfl | hxi
  · simp
  rw [mem_lattice, translated_root_torsion_ord K (n := p - 1) (by have := hp.one_lt; omega)
    _ (by rw [← map_pow, hxi, map_one])]
  rfl

/-- Paper `O:W:normquotient`, for any actual conjugate with its Hensel
displacement. The norm error is obtained from `actualNorm_of_correction`.
The correction has the fixed denominator `(1+b/W)^2`. -/
theorem split_normQuotient
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (xi : F) (hxi : xi = 0 ∨ xi ^ (p - 1) = 1)
    (sigma : Gal(K/B₂)) (eta : K)
    (hsigma : sigma Delta = Delta + algebraMap F K xi + eta)
    (heta : ord K (p : K) - ((((p - 1) * D.t : ℕ) : ℤ) : WithTop ℤ) ≤ ord K eta) :
    let x := algebraMap B₁ K (norm B₁ K (sigma Delta))
    let b := algebraMap B₁ K (norm B₁ K Delta)
    let W := algebraMap F K (transitionNorm D w)
    let c := algebraMap F K xi
    let s := algebraMap B₁ K (linearS D Delta)
    x / (1 + x / W) - (W * (b + c) / (W + b + c) - c * s / (1 + b / W) ^ 2) ∈
      lattice K ((p : ℤ) * D.t₂) := by
  dsimp only
  let x := algebraMap B₁ K (norm B₁ K (sigma Delta))
  let b := algebraMap B₁ K (norm B₁ K Delta)
  let W := algebraMap F K (transitionNorm D w)
  let c := algebraMap F K xi
  let s := algebraMap B₁ K (linearS D Delta)
  let H : ℤ := (p : ℤ) * D.t₂
  let S : ℤ := (p : ℤ) * (p - 1) * D.delta
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact mul_nonneg (mul_nonneg (by positivity) (by have := hp.one_lt; omega)) (by positivity)
  have hc : c ∈ lattice K 0 := split_shift_integral (hp := hp) xi hxi
  have hs : s ∈ lattice K S := (mem_lattice K).2 L.s_order
  have hk : c * s ∈ lattice K S := by simpa using mul_mem_lattice K hc hs
  have hr := actualNorm_of_correction D hres hchar Delta L.Delta_order xi hxi eta heta
  rw [← hsigma] at hr
  obtain ⟨_, _, _, _, hram⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  have hn : x - algebraMap B₁ K (norm B₁ K (Delta + c)) ∈ lattice K H := by
    rw [mem_lattice]
    change (H : WithTop ℤ) ≤ ord K
      (algebraMap B₁ K (norm B₁ K (sigma Delta)) -
        algebraMap B₁ K (norm B₁ K (Delta + algebraMap F K xi)))
    rw [← map_sub, ord_algebraMap, hram]
    apply (WithTop.coe_le_coe.mpr ?_).trans (nsmul_le_nsmul_right hr p)
    simp only [nsmul_eq_mul]
    dsimp only [H]
    nlinarith [Int.natCast_nonneg p]
  have herror : x - (b + c) + c * s ∈ lattice K H := by
    have he := (lattice K H).add_mem hn (split_norm_polynomial D L xi hxi)
    convert he using 1; dsimp only [x, b, c, s]; ring
  have hxb : x - b ∈ lattice K 0 := by
    have h := (lattice K 0).add_mem
      ((lattice K 0).sub_mem (lattice_antitone K hH herror)
        (lattice_antitone K hS hk)) hc
    convert h using 1; ring
  have hyb : b + c - b ∈ lattice K 0 := by simpa using hc
  have hyord : ord K (b + c) = ((-((p : ℤ) * D.t) : ℤ) : WithTop ℤ) := by
    rw [(ord K).map_add_eq_of_lt_left (by
      change ord K b < ord K c
      rw [show ord K b = _ from L.b_order_K]
      apply lt_of_lt_of_le _ ((mem_lattice K).1 hc)
      apply WithTop.coe_lt_coe.mpr
      have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
      have htz : (0 : ℤ) < D.t := by exact_mod_cast D.t_pos
      exact neg_neg_of_pos (mul_pos hpz htz)), L.b_order_K]
  have hxu := L.denominator_order x (L.conjugate_norm_order sigma)
  have hyu := L.denominator_order (b + c) hyord
  have hbu := L.denominator_order b L.b_order_K
  have hdepth : H ≤ (p : ℤ) ^ 2 * m + S := by
    have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
    have hpz : (3 : ℤ) ≤ p := by exact_mod_cast D.odd_prime
    have hgap := mul_nonneg (by omega : (0 : ℤ) ≤ p) (sub_nonneg.mpr L.transition)
    have hd := mul_nonneg (mul_nonneg (by omega : (0 : ℤ) ≤ p)
      (by omega : (0 : ℤ) ≤ (p : ℤ) - 2)) (Int.natCast_nonneg D.delta)
    dsimp only [H, S]
    rw [ht₂]
    nlinarith
  have h := split_quotient_linearization K x (b + c) b W (c * s)
    ((p : ℤ) ^ 2 * m) H S L.W_order_K hxu hyu hbu hxb hyb hk herror hdepth
  have hWne : W ≠ 0 := ne_zero_of_order K L.W_order_K
  have hrat : (b + c) / (1 + (b + c) / W) = W * (b + c) / (W + b + c) := by
    field_simp
    ring
  rw [hrat] at h
  exact h

/-- The chosen Hensel roots enumerate all actual upper automorphisms.
The zero representative has the identity automorphism and zero error;
separation is proved using the residue classes, not assumed. -/
private theorem split_conjugates
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p) :
    letI : Fact p.Prime := ⟨hp⟩
    ∃ (e : ZMod p ≃ Gal(K/B₂)) (eta : ZMod p → K), eta 0 = 0 ∧
      ∀ j : ZMod p,
        e j Delta = Delta + algebraMap F K (primeTeichmuller F p hchar j : F) + eta j ∧
        ord K (p : K) - ((((p - 1) * D.t : ℕ) : ℤ) : WithTop ℤ) ≤ ord K (eta j) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let c (j : ZMod p) : F := primeTeichmuller F p hchar j
  have hc (j : ZMod p) : c j = 0 ∨ c j ^ (p - 1) = 1 :=
    (Total.translatedNorm_representatives F p hchar (c j)).1 ⟨j, rfl⟩
  have hpacket (j : ZMod p) : ∃ (sigma : Gal(K/B₂)) (eta : K),
      sigma Delta = Delta + algebraMap F K (c j) + eta ∧
      ord K (p : K) - ((((p - 1) * D.t : ℕ) : ℤ) : WithTop ℤ) ≤ ord K eta ∧
      (j = 0 → eta = 0) := by
    by_cases hj : j = 0
    · subst j
      exact ⟨1, 0, by simp [c], by simp, by simp⟩
    obtain ⟨sigma, eta, hsigma, heta⟩ := L.actual_conjugate hres hchar (c j) (hc j)
    exact ⟨sigma, eta, hsigma, heta, fun h => (hj h).elim⟩
  choose sigma eta hsigma heta hzero using hpacket
  have heta1 (j) : eta j ∈ lattice K 1 := by
    by_cases hpzero : (p : K) = 0
    · have hz : eta j = 0 := by
        apply (ord_eq_top_iff K).mp
        simpa only [hpzero, ord_zero, WithTop.LinearOrderedAddCommGroup.top_sub,
          top_le_iff] using heta j
      simp [hz]
    obtain ⟨V, hV⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff K).mpr hpzero)
    have hVbound := L.prime_order
    rw [← hV, WithTop.coe_le_coe] at hVbound
    have hpos := split_correction_depth p D.t D.t₂ V
      (by exact_mod_cast D.odd_prime) (by exact_mod_cast D.t_pos)
      (by exact_mod_cast D.t_le_t₂) hVbound
    have h := heta j
    rw [← hV, ← WithTop.LinearOrderedAddCommGroup.coe_sub] at h
    push_cast [Nat.cast_sub hp.one_le] at h
    exact (mem_lattice K).2 ((WithTop.coe_le_coe.mpr hpos).trans h)
  have hinj : Function.Injective sigma := by
    intro i j hij
    apply translatedNorm_representatives_separated F K p hchar i j
    change algebraMap F K (c i - c j) ∈ lattice K 1
    have heq : algebraMap F K (c i - c j) = eta j - eta i := by
      have hi := hsigma i
      rw [hij] at hi
      rw [map_sub]
      linear_combination -hi + hsigma j
    rw [heq]
    exact (lattice K 1).sub_mem (heta1 j) (heta1 i)
  have hdegree : Module.finrank B₂ K = p :=
    (Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂).2.2.2.2.2.2.2.2.2.2.1
  have hbij : Function.Bijective sigma := (Fintype.bijective_iff_injective_and_card sigma).2
    ⟨hinj, by rw [ZMod.card, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hdegree]⟩
  exact ⟨Equiv.ofBijective sigma hbij, eta, hzero 0 rfl, fun j => ⟨hsigma j, heta j⟩⟩

/-- Paper `O:W:split` (`O:W:Wsplit`), for the prescribed coordinate and
actual lower norm witness. The representatives indexed by `ZMod p` are
exactly `{0} ∪ μ_{p-1}`; erasing zero gives the complete exceptional sum.
Both field characteristics and every odd prime, including three, occur
in this one statement. The setup has the proved constructor
`oddLinearData_construct`; no power replacement is an input. -/
theorem split
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (i : ℕ) (hi : 1 ≤ i) (hip : i ≤ p - 1) :
    letI : Fact p.Prime := ⟨hp⟩
    let c (j : ZMod p) := algebraMap F K (primeTeichmuller F p hchar j : F)
    let wK := algebraMap B₂ K (w : B₂)
    let W := algebraMap F K (transitionNorm D w)
    let b := algebraMap B₁ K (norm B₁ K Delta)
    let s := algebraMap B₁ K (linearS D Delta)
    algebraMap B₂ K (linearTrace D Delta w i) -
      ((wK ^ i)⁻¹ * (∑ j : ZMod p, (Delta + c j) ^ i * (W * (b + c j) / (W + b + c j))) -
        s / (wK ^ i * (1 + b / W) ^ 2) *
          (∑ j ∈ (Finset.univ : Finset (ZMod p)).erase 0, c j * (Delta + c j) ^ i)) ∈
      lattice K (1 + (p : ℤ) * D.t₂) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let cF (j : ZMod p) : F := primeTeichmuller F p hchar j
  let c (j : ZMod p) : K := algebraMap F K (cF j)
  let wK := algebraMap B₂ K (w : B₂)
  let W := algebraMap F K (transitionNorm D w)
  let b := algebraMap B₁ K (norm B₁ K Delta)
  let s := algebraMap B₁ K (linearS D Delta)
  let g (j : ZMod p) := W * (b + c j) / (W + b + c j) - c j * s / (1 + b / W) ^ 2
  let H : ℤ := (p : ℤ) * D.t₂
  have ht : (1 : ℤ) ≤ D.t := by exact_mod_cast D.t_pos
  have hpz : (3 : ℤ) ≤ p := by exact_mod_cast D.odd_prime
  have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
  have hi' : (1 : ℤ) ≤ i := by exact_mod_cast hi
  have hc0 : c 0 = 0 := by simp [c, cF]
  have hc1 : c 1 = 1 := by simp [c, cF]
  have hcsum : ∑ j, c j = 0 := by
    have h := congrArg ((ValuativeRel.valuation F).integer.subtype)
      (sum_primeTeichmuller F p hchar)
    have hF : ∑ j, cF j = 0 := by
      simpa [cF, show p ≠ 2 by omega] using h
    simp only [c, ← map_sum, hF, map_zero]
  have hcF (j) : cF j = 0 ∨ cF j ^ (p - 1) = 1 :=
    (Total.translatedNorm_representatives F p hchar (cF j)).1 ⟨j, rfl⟩
  have hcint (j) : c j ∈ lattice K 0 := split_shift_integral (hp := hp) (cF j) (hcF j)
  have hcroot (j : ZMod p) (hj : j ≠ 0) : c j ^ (p - 1) = 1 := by
    have h := congrArg (primeTeichmuller F p hchar) (ZMod.pow_card_sub_one_eq_one hj)
    have hF : cF j ^ (p - 1) = 1 := by
      dsimp only [cF]
      exact_mod_cast (by simpa only [map_pow, map_one] using h :
        primeTeichmuller F p hchar j ^ (p - 1) = 1)
    simp only [c, ← map_pow, hF, map_one]
  have hcenter (j) : ord K (Delta + c j) = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) := by
    by_cases hj : j = 0
    · simpa only [hj, hc0, add_zero] using L.Delta_order
    · exact translated_root_center_ord K (by omega : 0 < p - 1) (by omega)
        Delta (c j) L.Delta_order (hcroot j hj)
  obtain ⟨e, eta, heta0, hconj⟩ := split_conjugates D L hres hchar
  have hnorm (j) := split_normQuotient D L hres hchar (cF j) (hcF j)
    (e j) (eta j) (hconj j).1 (hconj j).2
  have hg (j) : g j ∈ lattice K (-((p : ℤ) * D.t)) := by
    have hx := L.conjugate_norm_order (e j)
    have hu := L.denominator_order _ hx
    have hfrac := split_div_mem K ((mem_lattice K).2 hx.ge) hu
    simp only [sub_zero] at hfrac
    have herror := lattice_antitone K (show -((p : ℤ) * D.t) ≤ H by
      dsimp only [H]
      exact le_trans (neg_nonpos.mpr (by positivity)) (by positivity))
      (hnorm j)
    have h := (lattice K (-((p : ℤ) * D.t))).sub_mem hfrac herror
    convert h using 1; dsimp only [g, c, cF, b, W, s]; ring
  have htrace : algebraMap B₂ K (linearTrace D Delta w i) =
      ∑ j : ZMod p, (e j Delta / wK) ^ i *
        (algebraMap B₁ K (norm B₁ K (e j Delta)) /
          (1 + algebraMap B₁ K (norm B₁ K (e j Delta)) / W)) := by
    rw [linearTrace_eq_sum D, ← e.sum_comp]
  have hnormSum : algebraMap B₂ K (linearTrace D Delta w i) -
      (∑ j : ZMod p, (e j Delta / wK) ^ i * g j) ∈ lattice K (1 + H) := by
    rw [htrace, ← Finset.sum_sub_distrib]
    apply sum_mem_lattice K
    intro j _
    have h := mul_mem_lattice K ((mem_lattice K).2 (L.power_order_pos (e j) hi)) (hnorm j)
    convert h using 1; dsimp only [g, c, cF, b, W, s, wK]; ring
  have hpowerSum : (∑ j : ZMod p, (e j Delta / wK) ^ i * g j) -
      (∑ j : ZMod p, ((Delta + c j) / wK) ^ i * g j) ∈ lattice K (1 + H) := by
    by_cases hpzero : (p : K) = 0
    · have heq (j) : e j Delta = Delta + c j := by
        have heta : eta j = 0 := by
          apply (ord_eq_top_iff K).mp
          simpa only [hpzero, ord_zero, WithTop.LinearOrderedAddCommGroup.top_sub,
            top_le_iff] using (hconj j).2
        simpa only [heta, add_zero] using (hconj j).1
      simp only [heq, sub_self, Submodule.zero_mem]
    obtain ⟨V, hV⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff K).mpr hpzero)
    have hVbound := L.prime_order
    rw [← hV, WithTop.coe_le_coe, ht₂] at hVbound
    have heta (j) : eta j ∈ lattice K (V - ((p : ℤ) - 1) * D.t) := by
      have h := (hconj j).2
      rw [← hV, ← WithTop.LinearOrderedAddCommGroup.coe_sub] at h
      simpa only [mem_lattice, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one] using h
    have hactual (j) : e j Delta ∈ lattice K (-(D.t : ℤ)) := by
      rw [mem_lattice, ord_galoisConjugate, L.Delta_order]
    by_cases hp3 : p = 3
    · subst hp3
      let lam : K := 1 + 3 * Delta ^ 2
      have hthree : (3 : K) ∈ lattice K V := (mem_lattice K).2 hV.symm.ge
      have hDm : Delta ∈ lattice K (-(D.t : ℤ)) := (mem_lattice K).2 L.Delta_order.ge
      have hlam1 : lam - 1 ∈ lattice K (V - 2 * D.t) := by
        have h := mul_mem_lattice K hthree (pow_mem_int_lattice K hDm 2)
        simp only [lam, add_sub_cancel_left]
        convert h using 1
        congr 1
        norm_num
        ring
      have hlam : lam ∈ lattice K 0 := by
        have hone : (1 : K) ∈ lattice K 0 := by simp
        have h := (lattice K 0).add_mem hone (lattice_antitone K (by norm_num at hVbound; omega) hlam1)
        convert h using 1; ring
      have hscaled (j) : Delta + lam * c j ∈ lattice K (-(D.t : ℤ)) := by
        have h : lam * c j ∈ lattice K 0 := by simpa using mul_mem_lattice K hlam (hcint j)
        exact (lattice K _).add_mem hDm (lattice_antitone K (by omega) h)
      have hrefined (j) : e j Delta - (Delta + lam * c j) ∈ lattice K (V - D.t) := by
        by_cases hj : j = 0
        · subst j
          have heq := (hconj 0).1
          change e 0 Delta = Delta + c 0 + eta 0 at heq
          simp only [hc0, heta0, add_zero] at heq
          simp [heq, hc0]
        have hroot : (Delta + c j + eta j) ^ 3 - (Delta + c j + eta j) = Delta ^ 3 - Delta := by
          rw [← (hconj j).1]
          calc
            (e j Delta) ^ 3 - e j Delta = e j (Delta ^ 3 - Delta) := by simp
            _ = Delta ^ 3 - Delta := by rw [L.root, AlgEquiv.commutes]
        have h := split_cubic_root K Delta (c j) (eta j) D.t V (by omega)
          (by norm_num at hVbound; omega) (by simpa only using hcroot j hj)
          L.Delta_order (hcenter j) (by simpa using hV.symm)
          (by simpa using heta j) hroot
        have heq : e j Delta - (Delta + lam * c j) = eta j - 3 * c j * Delta ^ 2 := by
          rw [(hconj j).1]
          dsimp only [lam, c, cF]
          ring
        rw [heq]
        exact h
      have hfirst : (∑ j, (e j Delta / wK) ^ i * g j) -
          (∑ j, ((Delta + lam * c j) / wK) ^ i * g j) ∈ lattice K (1 + H) := by
        rw [← Finset.sum_sub_distrib]
        apply sum_mem_lattice K
        intro j _
        have h := split_weighted_power_mem K (hactual j) (hscaled j) (hrefined j)
          L.w_order_K (hg j) i
        apply lattice_antitone K _ h
        dsimp only [H]
        norm_num at hVbound ⊢
        rw [ht₂]
        have hMi := mul_nonneg (by omega : (0 : ℤ) ≤ i) (sub_nonneg.mpr L.transition)
        norm_num at hMi
        nlinarith
      have hY3 : ord K (W + b) = ((-3 * (3 * m) : ℤ) : WithTop ℤ) := by
        have h := L.Y_order
        simp only [transitionY, map_add, ← IsScalarTower.algebraMap_apply F D.B₁ K] at h
        dsimp only [W, b]
        convert h using 1
        congr 1
        norm_num
        ring
      have hsecond := split_cubic_sum_error K Delta wK b W s lam c D.t D.delta
        (3 * m) V ht (by positivity) (by simpa using L.transition)
        (by simpa using hVbound) L.Delta_order (by simpa only [wK, Nat.cast_ofNat] using L.w_order_K)
        (by simpa only [b, Nat.cast_ofNat, neg_mul] using L.b_order_K)
        (by dsimp only [W]; convert L.W_order_K using 1; congr 1; norm_num; ring)
        hY3
        (L.denominator_order b L.b_order_K) (by simpa [s, mem_lattice] using L.s_order)
        hlam hlam1 hc0 hc1 hcsum i hi (by omega)
      have hsecond' : (∑ j, ((Delta + lam * c j) / wK) ^ i * g j) -
          (∑ j, ((Delta + c j) / wK) ^ i * g j) ∈ lattice K (1 + H) := by
        simpa only [g, H, Nat.cast_ofNat, ht₂] using hsecond
      simpa only [sub_add_sub_cancel] using (lattice K (1 + H)).add_mem hfirst hsecond'
    · have hp5 : 5 ≤ p := by
        have hp4 : p ≠ 4 := by intro h; norm_num [h] at hp
        omega
      rw [← Finset.sum_sub_distrib]
      apply sum_mem_lattice K
      intro j _
      have hdiff : e j Delta - (Delta + c j) ∈ lattice K (V - ((p : ℤ) - 1) * D.t) := by
        change e j Delta - (Delta + algebraMap F K (primeTeichmuller F p hchar j : F)) ∈ _
        simpa only [(hconj j).1, add_sub_cancel_left] using heta j
      have h := split_weighted_power_mem K (hactual j) ((mem_lattice K).2 (hcenter j).ge)
        hdiff L.w_order_K (hg j) i
      apply lattice_antitone K _ h
      have hd := split_large_depth p D.t D.delta ((p : ℤ) * m) V i
        (by exact_mod_cast hp5) ht (by positivity) L.transition hVbound hi'
      dsimp only [H]
      rw [ht₂]
      nlinarith only [hd]
  have hsum : (∑ j : ZMod p, ((Delta + c j) / wK) ^ i * g j) =
      (wK ^ i)⁻¹ * (∑ j : ZMod p, (Delta + c j) ^ i * (W * (b + c j) / (W + b + c j))) -
        s / (wK ^ i * (1 + b / W) ^ 2) *
          (∑ j ∈ (Finset.univ : Finset (ZMod p)).erase 0, c j * (Delta + c j) ^ i) := by
    have herase : (∑ j ∈ (Finset.univ : Finset (ZMod p)).erase 0, c j * (Delta + c j) ^ i) =
        ∑ j : ZMod p, c j * (Delta + c j) ^ i := by
      simpa only [hc0, zero_mul, add_zero] using
        (Finset.sum_erase_add (Finset.univ : Finset (ZMod p))
          (fun j => c j * (Delta + c j) ^ i) (a := 0) (by simp))
    rw [herase, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [g]
    simp only [div_eq_mul_inv, mul_inv_rev, mul_pow]
    ring
  have h := (lattice K (1 + H)).add_mem hnormSum hpowerSum
  rw [sub_add_sub_cancel, hsum] at h
  exact h

end Diamond

end

end LanglandsSecondMainLemma.Odd.Linear
