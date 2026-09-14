import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Linear.Split
import LanglandsSecondMainLemma.Finite.Interpolation

/-!
# Odd / Linear / Denominator

Paper Lemma 9.4 (`O:W:den`), with the notation of `O:W:ledger`.
The characteristic polynomial bounds the actual remainder `b-a-Delta`.
The prime-binomial identity then bounds `D-D₀` without dividing by `p`,
so the same proof includes mixed and equal characteristic. All depths
are integers and every field embedding in the final comparison is explicit.
-/

namespace LanglandsSecondMainLemma.Odd.Linear

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

open private pow_mem_int_lattice natCast_mem_int_lattice_zero
  translated_root_torsion_ord from LanglandsSecondMainLemma.Odd.Total.TranslatedNorm
open private ne_zero_of_order from LanglandsSecondMainLemma.Odd.Linear.Setup
open private split_div_mem from LanglandsSecondMainLemma.Odd.Linear.Split

section Estimates

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- Each mixed binomial term contains the residue prime and at least
one copy of the deeper argument. This allows negative input depths. -/
private theorem denominator_binomial
    {p : ℕ} (hp : p.Prime) {x y : E} {r s V : ℤ} (hrs : r ≤ s)
    (hx : x ∈ lattice E r) (hy : y ∈ lattice E s)
    (hpV : (p : E) ∈ lattice E V) :
    (x + y) ^ p - x ^ p - y ^ p ∈ lattice E (V + ((p : ℤ) - 1) * r + s) := by
  have hyr : y ∈ lattice E r := lattice_antitone E hrs hy
  have hsum :
      (∑ k ∈ Finset.Ioo 0 p,
        x ^ (k - 1) * y ^ (p - k - 1) * ((p.choose k / p : ℕ) : E)) ∈
          lattice E (((p : ℤ) - 2) * r) := by
    apply sum_mem_lattice E
    intro k hk
    obtain ⟨hk0, hkp⟩ := Finset.mem_Ioo.mp hk
    have h := mul_mem_lattice E
      (mul_mem_lattice E (pow_mem_int_lattice E hx (k - 1))
        (pow_mem_int_lattice E hyr (p - k - 1)))
      (natCast_mem_int_lattice_zero E (p.choose k / p))
    convert h using 1
    have h₁ : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
    have h₂ : ((p - k - 1 : ℕ) : ℤ) = (p : ℤ) - k - 1 := by omega
    rw [h₁, h₂]
    congr 1
    ring
  rw [add_pow_prime_eq hp x y]
  have h := mul_mem_lattice E (mul_mem_lattice E (mul_mem_lattice E hpV hx) hy) hsum
  convert h using 1
  · congr 1
    ring
  · ring

/-- The three lower bounds in the proof of `O:W:den`, after multiplying
the normalized error by `W^p`. -/
private theorem denominator_depths (p t u M : ℤ)
    (hp : 3 ≤ p) (ht : 1 ≤ t) (hu : t ≤ u) (hM : t + 1 ≤ M) :
    let T := 1 + p * u + M - p ^ 2 * M
    T ≤ p * (p - 1) * u - p * (p - 1) * M - p * t ∧
      T ≤ p * (p * u - (p + 1) * t) ∧ T ≤ p * u - (p + 1) * t := by
  dsimp only
  have hpoly : 1 ≤ p ^ 2 - 2 * p - 1 := by nlinarith
  have hpt := mul_le_mul_of_nonneg_right hpoly (by omega : 0 ≤ t)
  have hgap := mul_nonneg (by nlinarith : 0 ≤ p ^ 2 - 1)
    (by omega : 0 ≤ M - t - 1)
  have hgap' := mul_nonneg (by omega : 0 ≤ p - 1)
    (by omega : 0 ≤ M - t - 1)
  have hu₁ := mul_nonneg (mul_nonneg (by omega : 0 ≤ p) (by omega : 0 ≤ p - 2))
    (sub_nonneg.mpr hu)
  have hu₂ := mul_nonneg (mul_nonneg (by omega : 0 ≤ p) (by omega : 0 ≤ p - 1))
    (sub_nonneg.mpr hu)
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- An unnormalized form of the paper's `W^p E` estimate. The
remainder is the actual `b-a-Delta`, not an independently chosen norm. -/
private theorem denominator_difference
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (Delta a b W : E) (t u M : ℤ)
    (ht : 1 ≤ t) (hu : t ≤ u) (hM : t + 1 ≤ M)
    (hroot : Delta ^ p - Delta = a)
    (hDelta : Delta ∈ lattice E (-t))
    (ha : a ∈ lattice E (-(p : ℤ) * t))
    (hb : b ∈ lattice E (-(p : ℤ) * t))
    (hW : W ∈ lattice E (-(p : ℤ) * M))
    (hprime : (p : E) ∈ lattice E ((p : ℤ) * (p - 1) * u))
    (hrem : b - a - Delta ∈ lattice E ((p : ℤ) * u - (p + 1) * t)) :
    ((W + b) ^ p - (W + b)) - (W ^ p - W + a ^ p) ∈
      lattice E (1 + (p : ℤ) * u + M - (p : ℤ) ^ 2 * M) := by
  let h := b - a - Delta
  have hpz : (3 : ℤ) ≤ p := by exact_mod_cast hp3
  have hrt : -(p : ℤ) * M ≤ -(p : ℤ) * t := by nlinarith
  have hD : Delta ∈ lattice E (-(p : ℤ) * t) :=
    lattice_antitone E (by nlinarith) hDelta
  have hh : h ∈ lattice E (-(p : ℤ) * t) :=
    lattice_antitone E (by nlinarith) hrem
  have had : a + Delta ∈ lattice E (-(p : ℤ) * t) := (lattice E _).add_mem ha hD
  obtain ⟨h₁, h₂, h₃⟩ := denominator_depths (p : ℤ) t u M hpz ht hu hM
  have hmix (x y : E) (hx : x ∈ lattice E (-(p : ℤ) * M))
      (hy : y ∈ lattice E (-(p : ℤ) * t)) :
      (x + y) ^ p - x ^ p - y ^ p ∈
        lattice E (1 + (p : ℤ) * u + M - (p : ℤ) ^ 2 * M) := by
    apply lattice_antitone E _ (denominator_binomial E hp hrt hx hy hprime)
    nlinarith only [h₁]
  have hfirst := hmix W b hW hb
  have hsecond := hmix (a + Delta) h (lattice_antitone E hrt had) hh
  have hthird := hmix a Delta (lattice_antitone E hrt ha) hD
  have hpower := lattice_antitone E h₂ (pow_mem_int_lattice E hrem p)
  have hlinear := lattice_antitone E h₃ hrem
  have heq : ((W + b) ^ p - (W + b)) - (W ^ p - W + a ^ p) =
      ((W + b) ^ p - W ^ p - b ^ p) +
      ((a + Delta + h) ^ p - (a + Delta) ^ p - h ^ p) +
      ((a + Delta) ^ p - a ^ p - Delta ^ p) + h ^ p - h := by
    rw [show a + Delta + h = b by dsimp only [h]; ring]
    dsimp only [h]
    linear_combination hroot
  rw [heq]
  exact (lattice E _).sub_mem
    ((lattice E _).add_mem ((lattice E _).add_mem
      ((lattice E _).add_mem hfirst hsecond) hthird) hpower) hlinear

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
/-- The first form of `O:W:bforms`, expressed without choosing `omega`:
the actual difference `b-a-Delta` has depth `pt₂-(p+1)t`. -/
private theorem denominator_norm_remainder :
    algebraMap B₁ K (norm B₁ K Delta) - algebraMap B₂ K a - Delta ∈
      lattice K ((p : ℤ) * D.t₂ - (p + 1) * D.t) := by
  have hp3 := D.odd_prime
  have hpz : (3 : ℤ) ≤ p := by exact_mod_cast hp3
  have ht : (0 : ℤ) ≤ D.t := Int.natCast_nonneg _
  have htu : (D.t : ℤ) ≤ D.t₂ := by exact_mod_cast D.t_le_t₂
  have hdegree : Module.finrank B₁ K = p :=
    (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.2.2.1
  have hnorm := Total.odd_norm_expansion B₁ K (hp.odd_of_ne_two (by omega)) hdegree Delta
  have heq : algebraMap B₁ K (norm B₁ K Delta) - algebraMap B₂ K a - Delta =
      ∑ j ∈ Finset.Icc 1 (p - 1),
        (-1 : K) ^ j * algebraMap B₁ K (elementarySymmetric B₁ K j Delta) *
          Delta ^ (p - j) := by linear_combination hnorm + L.root
  rw [heq]
  apply sum_mem_lattice K
  intro j hj
  obtain ⟨hj1, hjp⟩ := Finset.mem_Icc.mp hj
  have hjlt : j < p := by omega
  have hsign : (-1 : K) ^ j ∈ lattice K 0 := by
    simp only [mem_lattice, ord_pow, ord_neg, ord_one, nsmul_zero,
      WithTop.coe_zero, le_refl]
  have h := mul_mem_lattice K
    (mul_mem_lattice K hsign ((mem_lattice K).2 (L.symmetric_order j hj1 hjlt)))
    (pow_mem_int_lattice K ((mem_lattice K).2 L.Delta_order.ge) (p - j))
  apply lattice_antitone K _ h
  have hjcast : ((p - j : ℕ) : ℤ) = (p : ℤ) - j := by omega
  rw [hjcast]
  have h₁ := mul_nonneg
    (mul_nonneg (by omega : 0 ≤ (p : ℤ)) (by omega : 0 ≤ (p : ℤ) - 2))
    (sub_nonneg.mpr htu)
  have h₂ := mul_nonneg
    (mul_nonneg (by omega : 0 ≤ (p : ℤ) - 1)
      (by omega : 0 ≤ (p : ℤ) - 1 - j)) ht
  nlinarith

omit [Module.Free F K] in
/-- The selected argument avoids every interpolation pole. This follows
from its negative valuation, including for roots of unity in the total field. -/
theorem denominator_nonpole :
    -(algebraMap B₁ K (transitionY D Delta w)) ∉ Finite.teichmullerSet K p := by
  classical
  intro h
  have hint : 0 ≤ ord K (-(algebraMap B₁ K (transitionY D Delta w))) := by
    rcases Finset.mem_insert.mp h with hz | hz
    · rw [hz, ord_zero]
      exact le_top
    · have hroot := (Polynomial.mem_nthRootsFinset
        (by have := D.odd_prime; omega : 0 < p - 1) (1 : K)).mp hz
      rw [translated_root_torsion_ord K (by have := D.odd_prime; omega) _ hroot]
  exact ne_zero_of_order K (L.Y_add_order _ hint) (add_neg_cancel _)

omit [Module.Free F K] in
/-- Paper `O:W:den`: replace the actual denominator at the full depth
`1+pt₂`, retaining the complete numerator and the actual norm witness.
The estimate also holds for `i=0`; the linear calculation uses `1≤i<p`. -/
theorem denominator (i : ℕ) (hi : i < p) :
    let W := algebraMap F K (transitionNorm D w)
    let Y := algebraMap B₁ K (transitionY D Delta w)
    W ^ 2 * (Delta - Y) ^ i /
        (algebraMap B₂ K (w : B₂) ^ i * algebraMap B₁ K (transitionD D Delta w)) -
      W ^ 2 * (Delta - Y) ^ i /
        (algebraMap B₂ K (w : B₂) ^ i * algebraMap B₂ K (transitionD₀ D a w)) ∈
      lattice K (1 + (p : ℤ) * D.t₂) := by
  let M : ℤ := (p : ℤ) * m
  let W := algebraMap F K (transitionNorm D w)
  let Y := algebraMap B₁ K (transitionY D Delta w)
  let b := algebraMap B₁ K (norm B₁ K Delta)
  let A := algebraMap B₂ K a
  let wK := algebraMap B₂ K (w : B₂)
  let d := algebraMap B₁ K (transitionD D Delta w)
  let d₀ := algebraMap B₂ K (transitionD₀ D a w)
  have hp3 := D.odd_prime
  have hpz : (3 : ℤ) ≤ p := by exact_mod_cast hp3
  have ht : (1 : ℤ) ≤ D.t := by exact_mod_cast D.t_pos
  have hu : (D.t : ℤ) ≤ D.t₂ := by exact_mod_cast D.t_le_t₂
  have hM : (D.t : ℤ) + 1 ≤ M := L.transition
  have hW : ord K W = ((-(p : ℤ) * M : ℤ) : WithTop ℤ) := by
    convert L.W_order_K using 1
    dsimp only [M]
    congr 1
    ring
  have hw : ord K wK = ((-M : ℤ) : WithTop ℤ) := L.w_order_K
  have hY : ord K Y = ((-(p : ℤ) * M : ℤ) : WithTop ℤ) := by
    convert L.Y_order using 1
    dsimp only [M]
    congr 1
    ring
  have hd : ord K d = ((-(p : ℤ) ^ 2 * M : ℤ) : WithTop ℤ) := by
    convert L.D_order using 1
    dsimp only [M]
    congr 1
    ring
  have hd₀ : ord K d₀ = ((-(p : ℤ) ^ 2 * M : ℤ) : WithTop ℤ) := by
    convert L.D₀_order using 1
    dsimp only [M]
    congr 1
    ring
  have hdiff : d - d₀ ∈ lattice K (1 + (p : ℤ) * D.t₂ + M - (p : ℤ) ^ 2 * M) := by
    have h := denominator_difference K hp hp3 Delta A b W D.t D.t₂ M ht hu hM
      L.root ((mem_lattice K).2 L.Delta_order.ge)
      (by simpa only [neg_mul] using (mem_lattice K).2 L.a_order_K.ge)
      (by simpa only [neg_mul] using (mem_lattice K).2 L.b_order_K.ge)
      ((mem_lattice K).2 hW.ge) ((mem_lattice K).2 L.prime_order)
      (denominator_norm_remainder D L)
    simpa only [d, d₀, transitionD, transitionD₀, transitionY,
      map_add, map_sub, map_pow, ← IsScalarTower.algebraMap_apply F B₁ K,
      ← IsScalarTower.algebraMap_apply F B₂ K, W, b, A] using h
  have hDY : Delta - Y ∈ lattice K (-(p : ℤ) * M) := by
    apply (lattice K _).sub_mem _ ((mem_lattice K).2 hY.ge)
    exact lattice_antitone K (by nlinarith) ((mem_lattice K).2 L.Delta_order.ge)
  have hden : ord K (wK ^ i * d * d₀) =
      ((-(i : ℤ) * M - 2 * (p : ℤ) ^ 2 * M : ℤ) : WithTop ℤ) := by
    simp only [ord_mul, ord_pow, hw, hd, hd₀, ← WithTop.coe_nsmul, ← WithTop.coe_add,
      nsmul_eq_mul]
    congr 1
    ring
  have hnum := mul_mem_lattice K
    (mul_mem_lattice K (pow_mem_int_lattice K ((mem_lattice K).2 hW.ge) 2)
      (pow_mem_int_lattice K hDY i)) hdiff
  have hquot := split_div_mem K hnum hden
  have hfull : W ^ 2 * (Delta - Y) ^ i * (d - d₀) / (wK ^ i * d * d₀) ∈
      lattice K (1 + (p : ℤ) * D.t₂) := by
    apply lattice_antitone K _ hquot
    have hpos := mul_nonneg
      (mul_nonneg (by omega : 0 ≤ (p : ℤ) - 1)
        (by omega : 0 ≤ (p : ℤ) - 1 - i)) (by omega : 0 ≤ M)
    norm_num
    nlinarith only [hpos]
  have hwne := ne_zero_of_order K hw
  have hdne := ne_zero_of_order K hd
  have hd₀ne := ne_zero_of_order K hd₀
  change W ^ 2 * (Delta - Y) ^ i / (wK ^ i * d) -
    W ^ 2 * (Delta - Y) ^ i / (wK ^ i * d₀) ∈ _
  have heq : W ^ 2 * (Delta - Y) ^ i / (wK ^ i * d) -
      W ^ 2 * (Delta - Y) ^ i / (wK ^ i * d₀) =
        -(W ^ 2 * (Delta - Y) ^ i * (d - d₀) / (wK ^ i * d * d₀)) := by
    field_simp
    ring
  rw [heq]
  exact (lattice K _).neg_mem hfull

end Diamond

end

end LanglandsSecondMainLemma.Odd.Linear
