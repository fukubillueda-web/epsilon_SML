import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Linear.Setup
import LanglandsSecondMainLemma.Odd.Total.TwistedEstimates

/-!
# Uniform conjugate replacement in the quadratic packet

Paper `O:D:WPdef`, `O:D:Tbound`, and `O:D:conjugates` (3560–3706).
The coordinate and norm witness are the prescribed ones in `OddLinearData`.
All three factors in a summand retain their actual norms and traces.
The cyclic trace estimate keeps its integer floor. For the norm difference,
the elementary product bound already suffices after the two outer weights;
it gives the same final depth as `O:D:Henselprod`.
-/

namespace LanglandsSecondMainLemma.Odd.Quadratic

noncomputable section
open LanglandsFirstMainLemma
open scoped BigOperators

open private pow_mem_int_lattice translatedNorm_representatives_separated from
  LanglandsSecondMainLemma.Odd.Total.TranslatedNorm
open private pow_sub_pow_mem_lattice from
  LanglandsSecondMainLemma.Odd.Total.CoefficientExtraction
open private realization_tower_data from
  LanglandsSecondMainLemma.Odd.Models.Realization

section Estimates

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

private theorem prod_mem (s : Finset ι) (x : ι → E) (d : ℤ)
    (hx : ∀ i ∈ s, x i ∈ lattice E d) :
    (∏ i ∈ s, x i) ∈ lattice E ((s.card : ℤ) * d) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have h := mul_mem_lattice E (hx i (by simp))
      (ih (fun j hj => hx j (by simp [hj])))
    convert h using 1
    congr 1
    push_cast
    ring

private theorem prod_sub_mem (s : Finset ι) (x y : ι → E) (d r : ℤ)
    (hx : ∀ i ∈ s, x i ∈ lattice E d)
    (hy : ∀ i ∈ s, y i ∈ lattice E d)
    (hxy : ∀ i ∈ s, x i - y i ∈ lattice E r) :
    (∏ i ∈ s, x i) - (∏ i ∈ s, y i) ∈
      lattice E (r + ((s.card : ℤ) - 1) * d) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have heq : x i * ∏ j ∈ s, x j - y i * ∏ j ∈ s, y j =
        x i * ((∏ j ∈ s, x j) - ∏ j ∈ s, y j) +
          (x i - y i) * ∏ j ∈ s, y j := by ring
    rw [heq]
    have h₁ := mul_mem_lattice E (hx i (by simp))
      (ih (fun j hj => hx j (by simp [hj])) (fun j hj => hy j (by simp [hj]))
        (fun j hj => hxy j (by simp [hj])))
    have h₂ := mul_mem_lattice E (hxy i (by simp))
      (prod_mem E s y d (fun j hj => hy j (by simp [hj])))
    apply (lattice E _).add_mem
    · convert h₁ using 1
      congr 1
      push_cast
      ring
    · convert h₂ using 1
      congr 1
      push_cast
      ring

/-- The exact rational function from the quadratic packet. -/
def quadraticFunction (W X : E) : E := X / (1 + X / W) ^ 2

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem quadraticFunction_sub (W X Y : E)
    (hx : 1 + X / W ≠ 0) (hy : 1 + Y / W ≠ 0) :
    quadraticFunction E W X - quadraticFunction E W Y =
      (X - Y) * (1 - X * Y / W ^ 2) /
        ((1 + X / W) ^ 2 * (1 + Y / W) ^ 2) := by
  dsimp only [quadraticFunction]
  rw [div_sub_div _ _ (pow_ne_zero 2 hx) (pow_ne_zero 2 hy)]
  congr 1
  simp only [div_eq_mul_inv]
  ring

private theorem quadraticFunction_sub_mem (W X Y : E) (d r : ℤ)
    (hX : ord E X = (d : WithTop ℤ)) (hY : ord E Y = (d : WithTop ℤ))
    (hWlt : ord E W < (d : WithTop ℤ))
    (hx : ord E (1 + X / W) = 0) (hy : ord E (1 + Y / W) = 0)
    (hXY : X - Y ∈ lattice E r) :
    quadraticFunction E W X - quadraticFunction E W Y ∈ lattice E r := by
  have hxne : 1 + X / W ≠ 0 := (ord_ne_top_iff E).1 (by rw [hx]; simp)
  have hyne : 1 + Y / W ≠ 0 := (ord_ne_top_iff E).1 (by rw [hy]; simp)
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hWlt)
  have hvd : v < d := by simpa only [← hv, WithTop.coe_lt_coe] using hWlt
  have hratio : X * Y / W ^ 2 ∈ lattice E 0 := by
    rw [mem_lattice, ord_div, ord_mul, hX, hY, ord_pow, ← hv,
      ← WithTop.coe_add, ← WithTop.coe_nsmul,
      ← WithTop.LinearOrderedAddCommGroup.coe_sub, WithTop.coe_le_coe]
    simp only [nsmul_eq_mul]
    omega
  have hnum := mul_mem_lattice E hXY ((lattice E 0).sub_mem
    (show (1 : E) ∈ lattice E 0 from by simp only [mem_lattice, ord_one, WithTop.coe_zero, le_refl]) hratio)
  rw [quadraticFunction_sub E W X Y hxne hyne]
  apply (div_mem_lattice_iff E _ _ 0 r (by simp [hx, hy])).2
  simpa using hnum

end Estimates

private theorem error_depth (p t delta M : ℤ)
    (hp : 3 ≤ p) (ht : 0 ≤ t) (hd : 0 ≤ delta) (hM : t + 1 ≤ M) :
    1 + p * (t + delta) ≤
      p * (p - 1) * (t + delta) + p * (p - 1) * delta +
        2 * (p - 1) * M - 3 * (p - 1) * t := by
  have hc : 0 ≤ p ^ 2 - 3 * p + 1 := by nlinarith [mul_nonneg (by omega : 0 ≤ p) (by omega : 0 ≤ p - 3)]
  have h₁ := mul_nonneg hc ht
  have h₂ := mul_nonneg (mul_nonneg (by omega : 0 ≤ p) (by omega : 0 ≤ 2 * p - 3)) hd
  have h₃ := mul_nonneg (by omega : 0 ≤ 2 * (p - 1)) (by omega : 0 ≤ M - t - 1)
  nlinarith

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

local instance : PrimeCyclicExtension F B₁ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₁
    (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.2.2.2.1
local instance : PrimeCyclicExtension B₁ K :=
  PrimeCyclicExtension.ofCyclicPrimeExtension B₁ K
    (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.2.2.2.2
local instance : PrimeCyclicExtension B₂ K :=
  PrimeCyclicExtension.ofCyclicPrimeExtension B₂ K
    (Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.2

/-- The inner trace `T`, with the specified denominator and variable coordinate. -/
def quadraticInner (w : B₂ˣ) (x : K) : B₁ :=
  trace B₁ K ((x / algebraMap B₂ K (w : B₂)) ^ (p - 1))

/-- One full summand, before taking the second upper trace. -/
def quadraticSummand (w : B₂ˣ) (x : K) : K :=
  quadraticFunction K (algebraMap F K (Linear.transitionNorm D w))
      (algebraMap B₁ K (norm B₁ K x)) *
    (x / algebraMap B₂ K (w : B₂)) ^ (p - 1) *
      algebraMap B₁ K (quadraticInner D w x)

/-- The actual packet `Q` in its own field `B₂`, as in `O:D:WPdef`. -/
def quadraticTrace (Delta : K) (w : B₂ˣ) : B₂ :=
  trace B₂ K (quadraticSummand D w Delta)

omit [Module.Free F K] in
theorem conjugate_crossedTrace (x : K) (sigma : Gal(K/B₂)) :
    sigma (algebraMap B₁ K (trace B₁ K x)) =
      algebraMap B₁ K (trace B₁ K (sigma x)) := by
  let r := IntermediateField.restrictRestrictAlgEquivMapHom F B₁ B₂ K
  have h := Algebra.trace_eq_of_equiv_equiv (r sigma).toRingEquiv sigma.toRingEquiv
    (by ext c; exact IntermediateField.restrictRestrictAlgEquivMapHom_apply B₁ B₂ sigma c) x
  change trace B₁ K x = (r sigma).symm (trace B₁ K (sigma x)) at h
  have ht : r sigma (trace B₁ K x) = trace B₁ K (sigma x) := by
    simpa only [AlgEquiv.apply_symm_apply] using congrArg (r sigma) h
  rw [← ht]
  exact (IntermediateField.restrictRestrictAlgEquivMapHom_apply B₁ B₂ sigma _).symm

omit [Module.Free F K] in
theorem quadraticInner_conjugate (w : B₂ˣ) (x : K) (sigma : Gal(K/B₂)) :
    algebraMap B₁ K (quadraticInner D w (sigma x)) =
      sigma (algebraMap B₁ K (quadraticInner D w x)) := by
  simp only [quadraticInner, conjugate_crossedTrace D, map_pow, map_div₀, AlgEquiv.commutes]

omit [Module.Free F K] in
theorem quadraticTrace_eq_sum (Delta : K) (w : B₂ˣ) :
    algebraMap B₂ K (quadraticTrace D Delta w) =
      ∑ sigma : Gal(K/B₂), quadraticSummand D w (sigma Delta) := by
  classical
  rw [quadraticTrace, trace, trace_eq_sum_automorphisms]
  apply Finset.sum_congr rfl
  intro sigma _
  have hW : sigma (algebraMap F K (Linear.transitionNorm D w)) =
      algebraMap F K (Linear.transitionNorm D w) := (sigma.restrictScalars F).commutes _
  simp only [quadraticSummand, quadraticFunction, map_mul, map_pow, map_div₀, map_add,
    map_one, AlgEquiv.commutes, Linear.conjugate_crossedNorm D, hW,
    quadraticInner_conjugate D]

omit [Module.Free F K] in
private theorem crossedNorm_sub_mem (hres : residueDegree F K = 1)
    (x y : K) (d r : ℤ) (hx : x ∈ lattice K d) (hy : y ∈ lattice K d)
    (hxy : x - y ∈ lattice K r) :
    algebraMap B₁ K (norm B₁ K x) - algebraMap B₁ K (norm B₁ K y) ∈
      lattice K (r + ((p : ℤ) - 1) * d) := by
  classical
  obtain ⟨hdegree, _, _, _, _⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  rw [Algebra.norm_eq_prod_automorphisms, Algebra.norm_eq_prod_automorphisms]
  have h := prod_sub_mem K (Finset.univ : Finset (Gal(K/B₁)))
    (fun sigma => sigma x) (fun sigma => sigma y) d r
    (by intro sigma _; simpa only [mem_lattice, ord_galoisConjugate] using hx)
    (by intro sigma _; simpa only [mem_lattice, ord_galoisConjugate] using hy)
    (by intro sigma _; simpa only [← map_sub, mem_lattice, ord_galoisConjugate] using hxy)
  simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card,
    IsGalois.card_aut_eq_finrank, hdegree] using h

omit [Module.Free F K] in
/-- The floor in the cyclic trace ideal loses at most `p-1` on lifting
back to `K`; this leaves the full gain `(p-1)t'`. -/
private theorem crossedTrace_mem (hres : residueDegree F K = 1)
    (x : K) (n : ℤ) (hx : x ∈ lattice K n) :
    algebraMap B₁ K (trace B₁ K x) ∈
      lattice K (n + ((p : ℤ) - 1) * D.tPrime) := by
  obtain ⟨hdegree, _, hr, _, he⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  have hbreak : PrimeCyclicExtension.IsLowerBreak B₁ K D.tPrime := D.B₁_breaks.2
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer B₁ K hr
  have h := traceIdealLowerBound_of_integralGenerator B₁ K hbreak hr pi hpi hgen n x hx
  rw [hdegree] at h
  have hupper := nsmul_le_nsmul_right h p
  rw [mem_lattice, ord_algebraMap, he]
  apply le_trans _ hupper
  rw [← WithTop.coe_nsmul, WithTop.coe_le_coe]
  simp only [nsmul_eq_mul]
  push_cast [Nat.cast_sub hp.one_le]
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hr := Int.emod_lt_of_pos (n + ((p : ℤ) - 1) * (D.tPrime + 1)) hpZ
  have heq := Int.emod_add_mul_ediv (n + ((p : ℤ) - 1) * (D.tPrime + 1)) (p : ℤ)
  nlinarith

section Replacement

variable {D} {Delta : K} {a : D.B₂} {w : D.B₂ˣ} {m : ℤ}
  (L : Odd.Linear.OddLinearData D Delta a w m)

include L

omit [Module.Free F K] in
private theorem inner_mem :
    algebraMap B₁ K (quadraticInner D w Delta) ∈
      lattice K ((p : ℤ) * (p - 1) * D.delta + (p - 1) * ((p : ℤ) * m)) := by
  have h := L.crossed_trace_order ((w : B₂)⁻¹ ^ (p - 1)) (p - 1)
    (by have := hp.pos; omega)
  have hw : ord K (algebraMap B₂ K ((w : B₂)⁻¹ ^ (p - 1))) =
      (((p : ℤ) - 1) * ((p : ℤ) * m) : ℤ) := by
    rw [map_pow, map_inv₀, ord_pow, ord_inv, L.w_order_K,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_nsmul]
    simp only [nsmul_eq_mul, neg_neg, Nat.cast_sub hp.one_le, Nat.cast_one]
  rw [hw, ← WithTop.coe_add] at h
  rw [mem_lattice]
  convert h using 1
  · congr 1
    rw [D.t₂_eq]
    push_cast [Nat.cast_sub hp.one_le]
    ring
  · simp only [quadraticInner, div_eq_mul_inv, mul_pow, map_pow, map_inv₀, mul_comm]

omit [Module.Free F K] in
private theorem summand_replacement (hres : residueDegree F K = 1)
    (sigma : Gal(K/B₂)) (xi : K) (hxi : 0 ≤ ord K xi)
    (herr : sigma Delta - (Delta + xi) ∈
      lattice K ((p : ℤ) * (p - 1) * D.t₂ - (p - 1) * D.t)) :
    quadraticSummand D w (sigma Delta) - quadraticSummand D w (Delta + xi) ∈
      lattice K (1 + (p : ℤ) * D.t₂) := by
  let P : ℤ := p
  let q : ℤ := P - 1
  let t : ℤ := D.t
  let M : ℤ := P * m
  let S : ℤ := P * q * D.delta
  -- This finite lower bound for `v_K(p)` works in both characteristics.
  let V : ℤ := P * q * D.t₂
  let A : ℤ := q * (M - t)
  let B : ℤ := S + q * M
  let R : ℤ := V - (2 * P - 3) * t + q * M
  let H : ℤ := V + S + 2 * q * M - 3 * q * t
  let x : K := sigma Delta
  let y : K := Delta + xi
  let W : K := algebraMap F K (Odd.Linear.transitionNorm D w)
  let v : K := algebraMap B₂ K (w : B₂)
  let X : K := algebraMap B₁ K (norm B₁ K x)
  let Y : K := algebraMap B₁ K (norm B₁ K y)
  let U : K := (x / v) ^ (p - 1)
  let U' : K := (y / v) ^ (p - 1)
  let T : K := algebraMap B₁ K (quadraticInner D w x)
  let T' : K := algebraMap B₁ K (quadraticInner D w y)
  have hpZ : 3 ≤ P := by
    dsimp only [P]
    exact_mod_cast (show 3 ≤ p by have := D.odd_prime; omega)
  have hq : 0 ≤ q := by dsimp only [q]; omega
  have ht : 0 < t := by dsimp only [t]; exact_mod_cast D.t_pos
  have hd : (0 : ℤ) ≤ D.delta := by positivity
  have ht₂ : (D.t₂ : ℤ) = t + D.delta := by dsimp only [t]; exact_mod_cast D.t₂_eq
  have htp : q * (D.tPrime : ℤ) = q * t + S := by
    dsimp only [S, q, P, t]
    rw [D.tPrime_eq]
    push_cast
    ring
  have hM : t + 1 ≤ M := L.transition
  have hV : q * t ≤ V := by
    dsimp only [V]
    rw [ht₂]
    nlinarith [mul_nonneg hq ht.le, mul_nonneg (mul_nonneg (by omega : 0 ≤ P) hq) hd]
  have hRB : B ≤ R + q * D.tPrime := by
    rw [htp]
    dsimp only [B, R, q] at *
    nlinarith
  have hH : 1 + (p : ℤ) * D.t₂ ≤ H := by
    simpa only [H, V, S, q, ← ht₂, P] using error_depth P t D.delta M hpZ ht.le hd hM
  have hxord : ord K x = ((-t : ℤ) : WithTop ℤ) := by
    simpa only [x, t, ord_galoisConjugate] using L.Delta_order
  have hyord : ord K y = ((-t : ℤ) : WithTop ℤ) := by
    have hlt : ord K Delta < ord K xi := by
      rw [L.Delta_order]
      exact (show ((-(D.t : ℤ) : ℤ) : WithTop ℤ) < 0 by
        exact WithTop.coe_lt_coe.mpr (neg_neg_of_pos ht)).trans_le hxi
    dsimp only [y]
    rw [(ord K).map_add_eq_of_lt_left hlt, L.Delta_order]
  have hxmem : x ∈ lattice K (-t) := hxord.ge
  have hymem : y ∈ lattice K (-t) := hyord.ge
  have hvmem : v⁻¹ ^ (p - 1) ∈ lattice K (q * M) := by
    rw [mem_lattice, ord_pow, ord_inv, L.w_order_K,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_nsmul]
    simp only [nsmul_eq_mul, neg_neg, Nat.cast_sub hp.one_le, Nat.cast_one, q, M, P, le_refl]
  have hU' : U' ∈ lattice K A := by
    have h := mul_mem_lattice K (pow_mem_int_lattice K hymem (p - 1)) hvmem
    simpa only [U', div_eq_mul_inv, mul_pow, A, q, P, Nat.cast_sub hp.one_le,
      Nat.cast_one, mul_sub, mul_neg, sub_eq_add_neg, add_comm] using h
  have hUU' : U - U' ∈ lattice K R := by
    have h := mul_mem_lattice K
      (pow_sub_pow_mem_lattice K hxmem hymem herr (p - 1)) hvmem
    have heq : U - U' = (x ^ (p - 1) - y ^ (p - 1)) * v⁻¹ ^ (p - 1) := by
      simp only [U, U', div_eq_mul_inv, mul_pow]; ring
    rw [heq]
    convert h using 1
    congr 1
    dsimp only [R, V, q, P, t]
    push_cast [Nat.cast_sub (show 1 ≤ p - 1 by omega), Nat.cast_sub hp.one_le]
    ring
  have hT : T ∈ lattice K B := by
    dsimp only [T, x]
    rw [quadraticInner_conjugate D, mem_lattice, ord_galoisConjugate]
    exact inner_mem L
  have hTT' : T - T' ∈ lattice K (R + q * D.tPrime) := by
    have h := crossedTrace_mem D hres (U - U') R hUU'
    simpa only [T, T', quadraticInner, U, U', v, map_sub, q, P] using h
  have hT' : T' ∈ lattice K B := by
    have h := (lattice K B).sub_mem hT (lattice_antitone K hRB hTT')
    simpa only [sub_sub_cancel] using h
  obtain ⟨_, _, hr₁, _, he₁⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  have hX : ord K X = ((-P * t : ℤ) : WithTop ℤ) := by
    simpa only [X, x, P, t, neg_mul] using L.conjugate_norm_order sigma
  have hY : ord K Y = ((-P * t : ℤ) : WithTop ℤ) := by
    dsimp only [Y]
    rw [ord_algebraMap, ord_norm, hr₁, one_nsmul, hyord, he₁,
      ← WithTop.coe_nsmul]
    simp only [nsmul_eq_mul, P, mul_neg, neg_mul]
  have hdenX : ord K (1 + X / W) = 0 := L.denominator_order X (by simpa only [P, t, neg_mul] using hX)
  have hdenY : ord K (1 + Y / W) = 0 := L.denominator_order Y (by simpa only [P, t, neg_mul] using hY)
  have hfX : quadraticFunction K W X ∈ lattice K (-P * t) := by
    rw [mem_lattice, quadraticFunction, ord_div, ord_pow, hdenX, hX]
    simp
  have hXY : X - Y ∈ lattice K (V - 2 * q * t) := by
    have h := crossedNorm_sub_mem D hres x y (-t) _ hxmem hymem herr
    convert h using 1
    congr 1
    dsimp only [V, q, P, t]
    ring
  have hfXY : quadraticFunction K W X - quadraticFunction K W Y ∈
      lattice K (V - 2 * q * t) := by
    apply quadraticFunction_sub_mem K W X Y (-P * t) _ hX hY _ hdenX hdenY hXY
    rw [L.W_order_K]
    apply WithTop.coe_lt_coe.mpr
    dsimp only [P, t, M] at *
    nlinarith [mul_pos (by omega : (0 : ℤ) < p) (by omega : 0 < (p : ℤ) * m - D.t)]
  have heq : quadraticSummand D w x - quadraticSummand D w y =
      quadraticFunction K W X * (U - U') * T +
        quadraticFunction K W X * U' * (T - T') +
          (quadraticFunction K W X - quadraticFunction K W Y) * U' * T' := by
    dsimp only [quadraticSummand, W, X, Y, U, U', T, T', v]
    ring
  rw [heq]
  apply lattice_antitone K hH
  apply (lattice K H).add_mem
  · apply (lattice K H).add_mem
    · convert mul_mem_lattice K (mul_mem_lattice K hfX hUU') hT using 1
      congr 1
      dsimp only [H, R, B, q]; ring
    · have h := mul_mem_lattice K (mul_mem_lattice K hfX hU') hTT'
      rw [htp] at h
      convert h using 1
      congr 1
      dsimp only [H, A, R, q]; ring
  · convert mul_mem_lattice K (mul_mem_lattice K hfXY hU') hT' using 1
    congr 1
    dsimp only [H, A, B]; ring

end Replacement

/-- Paper `O:D:conjugates`. The complete Teichmuller set indexes all actual
`K/B₂` conjugates of the prescribed coordinate. Each full quadratic
summand, and consequently their sum, is unchanged modulo `P_K^(1+p*t₂)`.
The correspondence retains the extended Hensel bound; when `(p : K)=0`
it forces the root correction to be exactly zero. The setup has the proved
constructor `Odd.Linear.oddLinearData_construct`, so no replacement or
trace estimate is an additional hypothesis. -/
theorem conjugates (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = p)
    (Delta : K) (a : B₂) (w : B₂ˣ) (m : ℤ)
    (L : Odd.Linear.OddLinearData D Delta a w m) :
    letI : Fact p.Prime := ⟨hp⟩
    ∃ e : ZMod p ≃ Gal(K/B₂),
      (∀ j : ZMod p,
        ord K (p : K) - ((((p : ℤ) - 1) * D.t : ℤ) : WithTop ℤ) ≤
          ord K (e j Delta -
            (Delta + algebraMap F K (primeTeichmuller F p hchar j : F)))) ∧
      (∀ j : ZMod p,
        quadraticSummand D w (e j Delta) -
          quadraticSummand D w
            (Delta + algebraMap F K (primeTeichmuller F p hchar j : F)) ∈
              lattice K (1 + (p : ℤ) * D.t₂)) ∧
      algebraMap B₂ K (quadraticTrace D Delta w) -
        (∑ j : ZMod p, quadraticSummand D w
          (Delta + algebraMap F K (primeTeichmuller F p hchar j : F))) ∈
            lattice K (1 + (p : ℤ) * D.t₂) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let c (j : ZMod p) : K := algebraMap F K (primeTeichmuller F p hchar j : F)
  let E : ℤ := (p : ℤ) * (p - 1) * D.t₂ - (p - 1) * D.t
  have hE : 1 ≤ E := by
    have hpZ : (3 : ℤ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := D.odd_prime; omega)
    have ht : (1 : ℤ) ≤ D.t := by exact_mod_cast D.t_pos
    have ht₂ : (D.t : ℤ) ≤ D.t₂ := by exact_mod_cast D.t_le_t₂
    have hpt : 2 * (D.t : ℤ) ≤ (p : ℤ) * D.t₂ := by nlinarith
    have hmul := mul_nonneg (by omega : (0 : ℤ) ≤ (p : ℤ) - 1)
      (by omega : (0 : ℤ) ≤ (p : ℤ) * D.t₂ - 2 * D.t)
    dsimp only [E]
    nlinarith
  have hfinite {z : K}
      (hz : ord K (p : K) - ((((p : ℤ) - 1) * D.t : ℤ) : WithTop ℤ) ≤ ord K z) :
      z ∈ lattice K E := by
    apply le_trans _ hz
    dsimp only [E]
    rw [WithTop.LinearOrderedAddCommGroup.coe_sub]
    simpa only [sub_eq_add_neg, add_comm] using
      add_le_add_right L.prime_order (-((((p : ℤ) - 1) * D.t : ℤ) : WithTop ℤ))
  have hpacket (j : ZMod p) : ∃ sigma : Gal(K/B₂),
      ord K (p : K) - ((((p : ℤ) - 1) * D.t : ℤ) : WithTop ℤ) ≤
        ord K (sigma Delta - (Delta + c j)) := by
    have hc : (primeTeichmuller F p hchar j : F) = 0 ∨
        (primeTeichmuller F p hchar j : F) ^ (p - 1) = 1 :=
      (Total.translatedNorm_representatives F p hchar _).1 ⟨j, rfl⟩
    obtain ⟨sigma, eta, heq, heta⟩ := L.actual_conjugate hres hchar _ hc
    refine ⟨sigma, ?_⟩
    dsimp only [c]
    rw [heq, add_sub_cancel_left]
    simpa only [Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one] using heta
  choose sigma hsigma using hpacket
  have hinj : Function.Injective sigma := by
    intro i j hij
    apply translatedNorm_representatives_separated F K p hchar i j
    have hi := lattice_antitone K hE (hfinite (hsigma i))
    have hj := lattice_antitone K hE (hfinite (hsigma j))
    have h := (lattice K 1).sub_mem hj hi
    rw [hij] at h
    have heq : sigma j Delta - (Delta + c j) - (sigma j Delta - (Delta + c i)) =
        c i - c j := by ring
    rw [heq] at h
    simpa only [c, map_sub] using h
  obtain ⟨hdegree, _, _, _, _⟩ := realization_tower_data hp hG hres B₂ D.degree_B₂
  have hbij : Function.Bijective sigma := (Fintype.bijective_iff_injective_and_card sigma).2
    ⟨hinj, by rw [ZMod.card, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hdegree]⟩
  let e : ZMod p ≃ Gal(K/B₂) := Equiv.ofBijective sigma hbij
  have hterm (j : ZMod p) :
      quadraticSummand D w (e j Delta) - quadraticSummand D w (Delta + c j) ∈
        lattice K (1 + (p : ℤ) * D.t₂) := by
    apply summand_replacement L hres (e j) (c j) _ (hfinite (hsigma j))
    dsimp only [c]
    rw [ord_algebraMap]
    exact nsmul_nonneg ((ord_nonneg_iff_mem_integer F _).2
      (primeTeichmuller F p hchar j).property) _
  refine ⟨e, hsigma, hterm, ?_⟩
  rw [quadraticTrace_eq_sum D, ← e.sum_comp, ← Finset.sum_sub_distrib]
  exact sum_mem_lattice K (fun j _ => hterm j)

end Diamond


end

end LanglandsSecondMainLemma.Odd.Quadratic
