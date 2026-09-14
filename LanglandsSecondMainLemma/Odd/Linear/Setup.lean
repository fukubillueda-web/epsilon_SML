import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Parameters.FourFactors
import LanglandsSecondMainLemma.Odd.Total.ASCoordinate

/-!
# The common data for the odd linear calculation

Paper: the notation and local estimates preceding `O:W:actualnorm`, and
`W_i` in the power-factor paragraph of `O:sec:linear`.

All scalars use the actual norm witness and prescribed Artin--Schreier
coordinate. The constructor reuses the estimates for that very coordinate
from `Models.Realization`, available through `Parameters.FourFactors`.
`linearTrace` is the actual upper field trace; its summands use genuine
Galois conjugates and their actual crossed norms. The depth `m` and every
valuation exponent are integers. No character evaluation occurs here.
-/

namespace LanglandsSecondMainLemma.Odd.Linear

noncomputable section
open LanglandsFirstMainLemma
open scoped BigOperators

private theorem ne_zero_of_order
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {x : E} {n : ℤ}
    (h : ord E x = (n : WithTop ℤ)) : x ≠ 0 :=
  (ord_ne_top_iff E).mp (h ▸ WithTop.coe_ne_top)

private theorem one_add_div_order
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {x W : E} {n N : ℤ}
    (hx : ord E x = (n : WithTop ℤ)) (hW : ord E W = (N : WithTop ℤ))
    (h : N < n) : ord E (1 + x / W) = 0 := by
  have hpos : 0 < ord E (x / W) := by
    rw [ord_div, hx, hW, ← WithTop.LinearOrderedAddCommGroup.coe_sub]
    exact WithTop.coe_lt_coe.mpr (sub_pos.mpr h)
  exact ((ord E).map_add_eq_of_lt_left (by simpa using hpos)).trans (ord_one E)

private theorem negative_power_sub_order
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {x : E} {n : ℤ} {p : ℕ}
    (hx : ord E x = (n : WithTop ℤ)) (hn : n < 0) (hp : 1 < p) :
    ord E (x ^ p - x) = (((p : ℤ) * n : ℤ) : WithTop ℤ) := by
  have hpow : ord E (x ^ p) = (((p : ℤ) * n : ℤ) : WithTop ℤ) := by
    simp only [ord_pow, hx, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have hlt : ord E (x ^ p) < ord E (-x) := by
    rw [hpow, ord_neg, hx]
    apply WithTop.coe_lt_coe.mpr
    have hp' : (1 : ℤ) < p := by exact_mod_cast hp
    nlinarith
  rw [sub_eq_add_neg, (ord E).map_add_eq_of_lt_left hlt, hpow]

open private realization_tower_data from
  LanglandsSecondMainLemma.Odd.Models.Realization

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
local instance : PrimeCyclicExtension B₂ K :=
  PrimeCyclicExtension.ofCyclicPrimeExtension B₂ K
    (Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.2

/-- The actual lower norm `W = n₂ w`, in the base field. -/
def transitionNorm (w : B₂ˣ) : F := norm F B₂ (w : B₂)

/-- The paper's `Y = W + b`, in the first lower field. -/
def transitionY (Delta : K) (w : B₂ˣ) : B₁ :=
  algebraMap F B₁ (transitionNorm D w) + norm B₁ K Delta

/-- The actual denominator `D = Y^p - Y`, in the first lower field. -/
def transitionD (Delta : K) (w : B₂ˣ) : B₁ :=
  transitionY D Delta w ^ p - transitionY D Delta w

/-- The comparison denominator `D₀ = W^p - W + a^p`, in the second lower field. -/
def transitionD₀ (a : B₂) (w : B₂ˣ) : B₂ :=
  algebraMap F B₂ (transitionNorm D w) ^ p -
    algebraMap F B₂ (transitionNorm D w) + a ^ p

/-- The unit `C = 1 + a/W`, in the second lower field. -/
def transitionC (a : B₂) (w : B₂ˣ) : B₂ :=
  1 + a / algebraMap F B₂ (transitionNorm D w)

/-- The actual signed coefficient `s = -e_{p-1}`, in the first lower field. -/
def linearS (Delta : K) : B₁ := -elementarySymmetric B₁ K (p - 1) Delta

/-- The actual trace `W_i`, with its power of the actual witness `w`. -/
def linearTrace (Delta : K) (w : B₂ˣ) (i : ℕ) : B₂ :=
  trace B₂ K ((Delta / algebraMap B₂ K (w : B₂)) ^ i *
    (algebraMap B₁ K (norm B₁ K Delta) /
      (1 + algebraMap B₁ K (norm B₁ K Delta) /
        algebraMap F K (transitionNorm D w))))

/-- All valuation and denominator data required by the linear calculation.
The coordinate, its coefficient, and the lower norm witness are parameters,
so constructing this record cannot silently replace any of them. -/
structure OddLinearData (Delta : K) (a : B₂) (w : B₂ˣ) (m : ℤ) : Prop where
  root : Delta ^ p - Delta = algebraMap B₂ K a
  Delta_order : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ)
  prime_to_break : ¬ p ∣ D.t
  generates : Algebra.adjoin B₂ ({Delta} : Set K) = ⊤
  norm_eq_a : norm B₂ K Delta = a
  transition : (D.t : ℤ) + 1 ≤ (p : ℤ) * m
  u_order : ord F (transitionNorm D w)⁻¹ = (m : WithTop ℤ)
  W_order : ord F (transitionNorm D w) = ((-m : ℤ) : WithTop ℤ)
  w_order : ord B₂ (w : B₂) = ((-m : ℤ) : WithTop ℤ)
  w_order_K : ord K (algebraMap B₂ K (w : B₂)) =
    ((-((p : ℤ) * m) : ℤ) : WithTop ℤ)
  W_order_K : ord K (algebraMap F K (transitionNorm D w)) =
    ((-((p : ℤ) ^ 2 * m) : ℤ) : WithTop ℤ)
  a_order : ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ)
  b_order : ord B₁ (norm B₁ K Delta) = ((-(D.t : ℤ) : ℤ) : WithTop ℤ)
  a_order_K : ord K (algebraMap B₂ K a) =
    ((-((p : ℤ) * D.t) : ℤ) : WithTop ℤ)
  b_order_K : ord K (algebraMap B₁ K (norm B₁ K Delta)) =
    ((-((p : ℤ) * D.t) : ℤ) : WithTop ℤ)
  prime_order : (((p : ℤ) * (p - 1) * D.t₂ : ℤ) : WithTop ℤ) ≤ ord K (p : K)
  symmetric_order : ∀ i : ℕ, 1 ≤ i → i < p →
    (((p : ℤ) * ((p - 1) * D.t₂ - (i : ℤ) * D.t) : ℤ) : WithTop ℤ) ≤
      ord K (algebraMap B₁ K (elementarySymmetric B₁ K i Delta))
  crossed_trace_order : ∀ (z : B₂) (i : ℕ), i < p →
    (((p : ℤ) * ((p - 1) * D.t₂ - (i : ℤ) * D.t) : ℤ) : WithTop ℤ) +
      ord K (algebraMap B₂ K z) ≤
        ord K (algebraMap B₁ K (trace B₁ K (algebraMap B₂ K z * Delta ^ i)))
  s_order : (((p : ℤ) * (p - 1) * D.delta : ℤ) : WithTop ℤ) ≤
    ord K (algebraMap B₁ K (linearS D Delta))
  Y_order : ord K (algebraMap B₁ K (transitionY D Delta w)) =
    ((-((p : ℤ) ^ 2 * m) : ℤ) : WithTop ℤ)
  D_order : ord K (algebraMap B₁ K (transitionD D Delta w)) =
    ((-((p : ℤ) ^ 3 * m) : ℤ) : WithTop ℤ)
  D₀_order : ord K (algebraMap B₂ K (transitionD₀ D a w)) =
    ((-((p : ℤ) ^ 3 * m) : ℤ) : WithTop ℤ)
  C_order : ord B₂ (transitionC D a w) = 0
  denominator_order : ∀ X : K,
    ord K X = ((-((p : ℤ) * D.t) : ℤ) : WithTop ℤ) →
      ord K (1 + X / algebraMap F K (transitionNorm D w)) = 0
  power_order : ∀ (sigma : Gal(K/B₂)) (i : ℕ),
    ord K ((sigma Delta / algebraMap B₂ K (w : B₂)) ^ i) =
      (((i : ℤ) * ((p : ℤ) * m - D.t) : ℤ) : WithTop ℤ)

/-- Construct the setup for the prescribed genuine coordinate and norm
witness. The input `v_F((n₂w)⁻¹)=m` is precisely the notation in the paper;
all upper orders, coefficient bounds, and denominator unit conditions are
conclusions. Both equal and mixed characteristic are included. -/
theorem oddLinearData_construct
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (Delta : K) (a : B₂) (w : B₂ˣ) (m : ℤ)
    (hroot : Delta ^ p - Delta = algebraMap B₂ K a)
    (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ D.t) (hgen : Algebra.adjoin B₂ ({Delta} : Set K) = ⊤)
    (hm : ord F (transitionNorm D w)⁻¹ = (m : WithTop ℤ))
    (htransition : (D.t : ℤ) < (p : ℤ) * m) :
    OddLinearData D Delta a w m := by
  obtain ⟨_, hrF₁, hrK₁, heF₁, heK₁⟩ :=
    realization_tower_data hp hG hres B₁ D.degree_B₁
  obtain ⟨hd₂, hrF₂, hrK₂, heF₂, heK₂⟩ :=
    realization_tower_data hp hG hres B₂ D.degree_B₂
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have htpos : (0 : ℤ) < D.t := by exact_mod_cast D.t_pos
  have hmpos : 0 < m := by nlinarith
  have hW : ord F (transitionNorm D w) = ((-m : ℤ) : WithTop ℤ) := by
    have h := congrArg Neg.neg hm
    simpa only [ord_inv, neg_neg, ← WithTop.LinearOrderedAddCommGroup.coe_neg] using h
  have hw : ord B₂ (w : B₂) = ((-m : ℤ) : WithTop ℤ) := by
    simpa only [transitionNorm, ord_norm, hrF₂, one_nsmul] using hW
  have hwK : ord K (algebraMap B₂ K (w : B₂)) =
      ((-((p : ℤ) * m) : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, heK₂, hw, ← WithTop.coe_nsmul]
    congr 1
    simp only [nsmul_eq_mul, mul_neg]
  have hWF₁ : ord B₁ (algebraMap F B₁ (transitionNorm D w)) =
      ((-((p : ℤ) * m) : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, heF₁, hW, ← WithTop.coe_nsmul]
    congr 1
    simp only [nsmul_eq_mul, mul_neg]
  have hWF₂ : ord B₂ (algebraMap F B₂ (transitionNorm D w)) =
      ((-((p : ℤ) * m) : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, heF₂, hW, ← WithTop.coe_nsmul]
    congr 1
    simp only [nsmul_eq_mul, mul_neg]
  have hWK : ord K (algebraMap F K (transitionNorm D w)) =
      ((-((p : ℤ) ^ 2 * m) : ℤ) : WithTop ℤ) := by
    rw [IsScalarTower.algebraMap_apply F B₂ K, ord_algebraMap, heK₂,
      hWF₂, ← WithTop.coe_nsmul]
    congr 1
    simp only [nsmul_eq_mul]
    ring
  let pb := PowerBasis.ofAdjoinEqTop (IsAlgebraic.of_finite B₂ Delta).isIntegral hgen
  have hpb : pb.gen = Delta := PowerBasis.ofAdjoinEqTop_gen _ _
  have hnorm : norm B₂ K Delta = a := by
    have hdim : pb.dim = p := by rw [← pb.finrank]; exact hd₂
    simpa only [hpb] using Total.artinSchreier_norm pb hp D.odd_prime hdim a
      (by simpa only [hpb] using hroot)
  have ha : ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [← hnorm, ord_norm, hrK₂, one_nsmul, hDelta]
  have hb : ord B₁ (norm B₁ K Delta) = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_norm, hrK₁, one_nsmul, hDelta]
  have haK : ord K (algebraMap B₂ K a) =
      ((-((p : ℤ) * D.t) : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, heK₂, ha, ← WithTop.coe_nsmul]
    congr 1
    simp only [nsmul_eq_mul, mul_neg]
  have hbK : ord K (algebraMap B₁ K (norm B₁ K Delta)) =
      ((-((p : ℤ) * D.t) : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, heK₁, hb, ← WithTop.coe_nsmul]
    congr 1
    simp only [nsmul_eq_mul, mul_neg]
  have hgap : -((p : ℤ) ^ 2 * m) < -((p : ℤ) * D.t) := by
    nlinarith [mul_pos hpz (sub_pos.mpr htransition)]
  have hY : ord K (algebraMap B₁ K (transitionY D Delta w)) =
      ((-((p : ℤ) ^ 2 * m) : ℤ) : WithTop ℤ) := by
    simp only [transitionY, map_add, ← IsScalarTower.algebraMap_apply F B₁ K]
    rw [(ord K).map_add_eq_of_lt_left (by
      rw [hWK, hbK]; exact WithTop.coe_lt_coe.mpr hgap), hWK]
  have hD : ord K (algebraMap B₁ K (transitionD D Delta w)) =
      ((-((p : ℤ) ^ 3 * m) : ℤ) : WithTop ℤ) := by
    simp only [transitionD, map_sub, map_pow]
    convert negative_power_sub_order K hY
      (neg_neg_of_pos (mul_pos (sq_pos_of_pos hpz) hmpos)) hp.one_lt using 1
    congr 1
    ring
  have hD₀ : ord K (algebraMap B₂ K (transitionD₀ D a w)) =
      ((-((p : ℤ) ^ 3 * m) : ℤ) : WithTop ℤ) := by
    have hpowW := negative_power_sub_order K hWK (neg_neg_of_pos (mul_pos (sq_pos_of_pos hpz) hmpos)) hp.one_lt
    have hpowA : ord K (algebraMap B₂ K a ^ p) =
        ((-((p : ℤ) ^ 2 * D.t) : ℤ) : WithTop ℤ) := by
      rw [ord_pow, haK, ← WithTop.coe_nsmul]
      congr 1
      simp only [nsmul_eq_mul]
      ring
    simp only [transitionD₀, map_add, map_sub, map_pow,
      ← IsScalarTower.algebraMap_apply F B₂ K]
    rw [(ord K).map_add_eq_of_lt_left (by
      rw [hpowW, hpowA]
      apply WithTop.coe_lt_coe.mpr
      nlinarith [mul_pos hpz (sub_pos.mpr hgap)]), hpowW]
    congr 1
    ring
  obtain ⟨htr, _, hei, hs⟩ :=
    Models.realization_twistedEstimates_of_coordinate hp hG hres hchar D
      Delta a hroot hDelta hprime hgen
  refine
    { root := hroot, Delta_order := hDelta, prime_to_break := hprime, generates := hgen
      norm_eq_a := hnorm, transition := by omega, u_order := hm, W_order := hW
      w_order := hw, w_order_K := hwK, W_order_K := hWK, a_order := ha, b_order := hb
      a_order_K := haK, b_order_K := hbK, prime_order := ?_, symmetric_order := ?_
      crossed_trace_order := ?_, s_order := ?_, Y_order := hY, D_order := hD
      D₀_order := hD₀, C_order := ?_, denominator_order := ?_, power_order := ?_ }
  · simpa only [Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one] using
      Total.oddTotal_primeValuationBound hp hG hres D
  · intro i hi hip
    rw [ord_algebraMap, heK₁]
    simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using
      nsmul_le_nsmul_right (hei i hi hip) p
  · intro z i hip
    rw [ord_algebraMap, ord_algebraMap, heK₁, heK₂]
    simpa only [nsmul_add, ← WithTop.coe_nsmul, nsmul_eq_mul] using
      nsmul_le_nsmul_right (htr z i hip) p
  · rw [ord_algebraMap, heK₁]
    simpa only [linearS, ← WithTop.coe_nsmul, nsmul_eq_mul, mul_assoc] using
      nsmul_le_nsmul_right hs p
  · exact one_add_div_order B₂ ha hWF₂ (by omega)
  · intro X hX
    exact one_add_div_order K hX hWK hgap
  · intro sigma i
    rw [ord_pow, ord_div, ord_galoisConjugate, hDelta, hwK,
      ← WithTop.LinearOrderedAddCommGroup.coe_sub, ← WithTop.coe_nsmul]
    congr 1
    simp only [nsmul_eq_mul]
    ring

omit [Module.Free F K] in
/-- An actual upper automorphism carries the crossed norm to the crossed
norm of the conjugate. This is compatibility of the genuine field maps. -/
theorem conjugate_crossedNorm (Delta : K) (sigma : Gal(K/B₂)) :
    sigma (algebraMap B₁ K (norm B₁ K Delta)) =
      algebraMap B₁ K (norm B₁ K (sigma Delta)) := by
  let r := IntermediateField.restrictRestrictAlgEquivMapHom F B₁ B₂ K
  have h := Algebra.norm_eq_of_equiv_equiv (r sigma).toRingEquiv sigma.toRingEquiv
    (by ext c; exact IntermediateField.restrictRestrictAlgEquivMapHom_apply B₁ B₂ sigma c)
    Delta
  change norm B₁ K Delta = (r sigma).symm (norm B₁ K (sigma Delta)) at h
  have hn : r sigma (norm B₁ K Delta) = norm B₁ K (sigma Delta) := by
    simpa only [AlgEquiv.apply_symm_apply] using congrArg (r sigma) h
  rw [← hn]
  exact (IntermediateField.restrictRestrictAlgEquivMapHom_apply B₁ B₂ sigma _).symm

omit [Module.Free F K] in
/-- `W_i` is exactly the sum of the genuine conjugate terms. No translated
root or approximate upper norm is substituted in this equality. -/
theorem linearTrace_eq_sum (Delta : K) (w : B₂ˣ) (i : ℕ) :
    algebraMap B₂ K (linearTrace D Delta w i) =
      ∑ sigma : Gal(K/B₂),
        (sigma Delta / algebraMap B₂ K (w : B₂)) ^ i *
          (algebraMap B₁ K (norm B₁ K (sigma Delta)) /
            (1 + algebraMap B₁ K (norm B₁ K (sigma Delta)) /
              algebraMap F K (transitionNorm D w))) := by
  classical
  rw [linearTrace, trace, trace_eq_sum_automorphisms]
  apply Finset.sum_congr rfl
  intro sigma _
  have hW : sigma (algebraMap F K (transitionNorm D w)) =
      algebraMap F K (transitionNorm D w) := (sigma.restrictScalars F).commutes _
  simp only [map_mul, map_pow, map_div₀, map_add, map_one, AlgEquiv.commutes,
    conjugate_crossedNorm D, hW]

namespace OddLinearData

variable {D} {Delta : K} {a : D.B₂} {w : D.B₂ˣ} {m : ℤ}
  (L : OddLinearData D Delta a w m)

include L

omit [Module.Free F K] in
/-- Every conjugate crossed norm has the valuation used in the denominator
unit criterion, with the order normalized in the total field. -/
theorem conjugate_norm_order (sigma : Gal(K/B₂)) :
    ord K (algebraMap B₁ K (norm B₁ K (sigma Delta))) =
      ((-((p : ℤ) * D.t) : ℤ) : WithTop ℤ) := by
  rw [← conjugate_crossedNorm D, ord_galoisConjugate, L.b_order_K]

omit [Module.Free F K] in
/-- The denominators of all genuine conjugate summands are units of the
valuation ring, expressed through FML's subgroup `unitGroup`. -/
theorem denominator_unit (X : K)
    (hX : ord K X = ((-((p : ℤ) * D.t) : ℤ) : WithTop ℤ)) :
    ∃ u : unitGroup K,
      ((u : Kˣ) : K) = 1 + X / algebraMap F K (transitionNorm D w) := by
  have hzero := L.denominator_order X hX
  let u := Units.mk0 (1 + X / algebraMap F K (transitionNorm D w))
    (ne_zero_of_order K (n := 0) hzero)
  exact ⟨⟨u, (mem_unitGroup_iff_ord_eq_zero K u).2 hzero⟩, rfl⟩

omit [Module.Free F K] in
/-- Nonzero scalars in their own fields, before any division or character
application. `C` is moreover a valuation-ring unit by `C_order`. -/
theorem denominators_ne_zero :
    Delta ≠ 0 ∧ a ≠ 0 ∧ norm B₁ K Delta ≠ 0 ∧ transitionNorm D w ≠ 0 ∧
      transitionY D Delta w ≠ 0 ∧ transitionD D Delta w ≠ 0 ∧
      transitionD₀ D a w ≠ 0 ∧ transitionC D a w ≠ 0 := by
  refine ⟨ne_zero_of_order K L.Delta_order, ne_zero_of_order B₂ L.a_order,
    ne_zero_of_order B₁ L.b_order, ne_zero_of_order F L.W_order, ?_, ?_, ?_,
    ne_zero_of_order B₂ (n := 0) L.C_order⟩
  · exact fun h => ne_zero_of_order K L.Y_order (by rw [h, map_zero])
  · exact fun h => ne_zero_of_order K L.D_order (by rw [h, map_zero])
  · exact fun h => ne_zero_of_order K L.D₀_order (by rw [h, map_zero])

omit [Module.Free F K] in
/-- The whole power factor in each actual summand has positive depth.
Thus a norm-quotient error at depth `pt₂` gains the one step required for
modulus `K = 1 + pt₂`. -/
theorem power_order_pos (sigma : Gal(K/B₂)) {i : ℕ} (hi : 1 ≤ i) :
    (1 : WithTop ℤ) ≤ ord K ((sigma Delta / algebraMap B₂ K (w : B₂)) ^ i) := by
  rw [L.power_order]
  apply WithTop.coe_le_coe.mpr
  have hi' : (1 : ℤ) ≤ i := by exact_mod_cast hi
  have hdepth := L.transition
  nlinarith

omit [Module.Free F K] in
/-- Adding an integral scalar cannot create a pole at `Y`; this includes
all Teichmuller shifts in the later rational denominators. -/
theorem Y_add_order (xi : K) (hxi : 0 ≤ ord K xi) :
    ord K (algebraMap B₁ K (transitionY D Delta w) + xi) =
      ((-((p : ℤ) ^ 2 * m) : ℤ) : WithTop ℤ) := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have ht := L.transition
  have htzero : (0 : ℤ) ≤ D.t := Int.natCast_nonneg _
  have hmpos : 0 < m := by nlinarith
  have hneg : -((p : ℤ) ^ 2 * m) < 0 :=
    neg_neg_of_pos (mul_pos (sq_pos_of_pos hpz) hmpos)
  have hlt : ord K (algebraMap B₁ K (transitionY D Delta w)) < ord K xi := by
    rw [L.Y_order]
    exact (WithTop.coe_lt_coe.mpr hneg).trans_le hxi
  rw [(ord K).map_add_eq_of_lt_left hlt, L.Y_order]

/-- The actual root correction for every member of `{0} ∪ μ_{p-1} ⊂ F`.
The `WithTop` bound specializes to `eta = 0` in equal characteristic. -/
theorem actual_conjugate
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (xi : F) (hxi : xi = 0 ∨ xi ^ (p - 1) = 1) :
    ∃ (sigma : Gal(K/B₂)) (eta : K),
      sigma Delta = Delta + algebraMap F K xi + eta ∧
      ord K (p : K) - ((((p - 1) * D.t : ℕ) : ℤ) : WithTop ℤ) ≤ ord K eta := by
  rcases hxi with rfl | hxi
  · exact ⟨1, 0, by simp, by simp⟩
  obtain ⟨sigma, eta, heq, _, _, hcase⟩ :=
    Total.oddAS_actualConjugates_of_coordinate hp hG hres hchar D
      Delta a L.root L.Delta_order L.generates (algebraMap F B₂ xi)
        (by rw [← map_pow, hxi, map_one])
  refine ⟨sigma, eta, ?_, ?_⟩
  · simpa only [← IsScalarTower.algebraMap_apply F B₂ K] using heq
  · rcases hcase with ⟨_, rfl⟩ | ⟨_, V, hV, _, heta⟩
    · simp
    · rw [hV, ← WithTop.LinearOrderedAddCommGroup.coe_sub]
      exact heta

end OddLinearData

omit [Module.Free F K] [IsGalois F K] in
/-- The input order of the norm inverse follows from the exact parameter
choice `n₂w = gamma/alpha` in `O:P:parameters`. Subtraction is in `ℤ`, even
before imposing the strict transition inequality. -/
theorem transitionNorm_inv_order_of_parameters
    (alpha gamma : Fˣ) (w : B₂ˣ) (d r : ℤ)
    (halpha : ord F (alpha : F) = ((-d - 1 - D.t₂ : ℤ) : WithTop ℤ))
    (hgamma : ord F (gamma : F) = ((-d - 1 - r : ℤ) : WithTop ℤ))
    (hw : normUnits F B₂ w = gamma / alpha) :
    ord F (transitionNorm D w)⁻¹ = ((r - D.t₂ : ℤ) : WithTop ℤ) := by
  have hn : transitionNorm D w = (gamma : F) / (alpha : F) := by
    simpa only [transitionNorm, coe_normUnits, Units.val_div_eq_div_val] using
      congrArg (fun u : Fˣ => (u : F)) hw
  rw [hn, ord_inv, ord_div, hgamma, halpha,
    ← WithTop.LinearOrderedAddCommGroup.coe_sub,
    ← WithTop.LinearOrderedAddCommGroup.coe_neg]
  congr 1
  ring

/-- When no coordinate has yet been selected, the accepted AS constructor
supplies one from the genuine local-field diamond. -/
theorem oddLinearData_exists
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (w : B₂ˣ) (m : ℤ)
    (hm : ord F (transitionNorm D w)⁻¹ = (m : WithTop ℤ))
    (htransition : (D.t : ℤ) < (p : ℤ) * m) :
    ∃ (Delta : K) (a : B₂), OddLinearData D Delta a w m := by
  obtain ⟨Delta, a, hroot, hDelta, _, hprime, hgen⟩ :=
    Total.aSCoordinate hp hG hres hchar D
  exact ⟨Delta, a, oddLinearData_construct D hres hchar Delta a w m
    hroot hDelta hprime hgen hm htransition⟩

end Diamond
end
end LanglandsSecondMainLemma.Odd.Linear
