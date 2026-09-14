import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Transition.Projection
import LanglandsSecondMainLemma.Odd.Linear.Setup
import LanglandsSecondMainLemma.Odd.Transition.Denominators

/-!
# Odd / Transition / Representatives

Paper Lemma 9.25 (`O:T:representatives`), with the actual expressions
`O:T:XandY`. The power basis is prescribed, as is the exact lower norm
witness. Its constant projection supplies both genuine lower-field
representatives. All source depths and the weighted norm substitutions
are proved before applying the accepted denominator congruences.
-/

namespace LanglandsSecondMainLemma.Odd.Transition

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The two bounds of `O:T:projectdepth` for both actual numerators.
The transition inequality includes the boundary `p = 3`, `delta = 0`. -/
private theorem representative_depths (p t delta m : ℤ)
    (hp : 3 ≤ p) (ht : 0 ≤ t) (hd : 0 ≤ delta)
    (hm : t + 1 ≤ p * m) :
    let qs := (p - 2) * m + (p - 1) * delta
    let qT := 2 * (p - 1) * m - t + (p - 1) * delta
    (1 + t + p * delta ≤ p * qs ∧
      1 + t + delta + (p - 3) * t ≤ p * qs) ∧
    (1 + t + p * delta ≤ p * qT ∧
      1 + t + delta + (p - 3) * t ≤ p * qT) := by
  dsimp only
  have hs := mul_le_mul_of_nonneg_left hm (show 0 ≤ p - 2 by omega)
  have hT := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * (p - 1) by omega)
  have hpt := mul_nonneg (show 0 ≤ p - 3 by omega) ht
  have hd₁ := mul_nonneg (mul_nonneg (show 0 ≤ p by omega)
    (show 0 ≤ p - 2 by omega)) hd
  have hd₂ := mul_nonneg (show 0 ≤ p * (p - 1) - 1 by nlinarith) hd
  constructor <;> constructor <;> nlinarith

open private powerBasis_expansion constant_tail_mem from
  LanglandsSecondMainLemma.Odd.Transition.Projection
open private map_lattice from
  LanglandsSecondMainLemma.Odd.Total.ProjectionTransfer
open private realization_tower_data from
  LanglandsSecondMainLemma.Odd.Models.Realization

section Diamond

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]
  {p : ℕ} (hp : p.Prime)
  (hG : Nonempty
    (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
  (R : Total.OddTotalBreakData (F := F) (K := K) hp hG)

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

local notation "B₁" => R.B₁
local notation "B₂" => R.B₂

local instance : PrimeCyclicExtension F B₁ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₁
    (Basic.intermediateField_tower_compatible hp hG B₁ R.degree_B₁).2.2.2.2.2.2.2.2.2.2.2.1
local instance : PrimeCyclicExtension B₁ K :=
  PrimeCyclicExtension.ofCyclicPrimeExtension B₁ K
    (Basic.intermediateField_tower_compatible hp hG B₁ R.degree_B₁).2.2.2.2.2.2.2.2.2.2.2.2

/-- Apply the accepted projection argument to the prescribed basis, using
integer lower bounds on the two factors. The coefficient estimate is
constructed for this very generator; zero factors require no exception. -/
private theorem project_product
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (pb : PowerBasis B₂ K) (a : B₂)
    (hroot : pb.gen ^ p - pb.gen = algebraMap B₂ K a)
    (hDelta : ord K pb.gen = ((-(R.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ R.t)
    (x : B₂) (v : B₁) (qx qv : ℤ)
    (hx : x ∈ lattice B₂ qx) (hv : v ∈ lattice B₁ qv)
    (hfirst : 1 + (R.tPrime : ℤ) ≤ (p : ℤ) * (qx + qv))
    (hsecond : 1 + (R.t₂ : ℤ) + ((p : ℤ) - 3) * R.t ≤
      (p : ℤ) * (qx + qv)) :
    let z := algebraMap B₂ K x * algebraMap B₁ K v
    let y := constantProjection pb z
    z - algebraMap B₂ K y ∈ lattice K (1 + (p : ℤ) * R.t₂) ∧
      norm B₁ K z - algebraMap F B₁ (norm F B₂ y) ∈
        lattice B₁ (1 + (p : ℤ) * R.t₂) ∧
      y ∈ lattice B₂ (qx + qv) := by
  classical
  dsimp only
  obtain ⟨_, _, _, _, he₁⟩ := realization_tower_data hp hG hres B₁ R.degree_B₁
  obtain ⟨hd₂, _, _, _, he₂⟩ := realization_tower_data hp hG hres B₂ R.degree_B₂
  have hdim : pb.dim = p := by rw [← pb.finrank]; exact hd₂
  let W : Fin p → B₂ := fun i =>
    pb.basis.repr (algebraMap B₁ K v) (Fin.cast hdim.symm i)
  let Y : Fin p → B₂ := fun i => x * W i
  let z := algebraMap B₂ K x * algebraMap B₁ K v
  let y := constantProjection pb z
  have hexpv : algebraMap B₁ K v =
      ∑ i : Fin p, algebraMap B₂ K (W i) * pb.gen ^ (i : ℕ) :=
    powerBasis_expansion pb hdim _
  have hcoeff := Models.realization_coefficientExtraction_of_coordinate hp hG hres hchar R
    pb.gen a hroot hDelta hprime pb.adjoin_gen_eq_top v W hexpv
  have hY (i : Fin p) : Y i ∈ lattice B₂ (qx + qv + (i : ℕ) * (R.t : ℤ)) := by
    have hWi : W i ∈ lattice B₂ (qv + (i : ℕ) * (R.t : ℤ)) := by
      apply (mem_lattice B₂).2
      rw [WithTop.coe_add]
      refine (add_le_add ((mem_lattice B₁).1 hv) (le_refl _)).trans ?_
      simpa only [WithTop.coe_add, Nat.cast_mul] using hcoeff i
    simpa only [add_assoc] using mul_mem_lattice B₂ hx hWi
  have hexp : z = ∑ i : Fin p, algebraMap B₂ K (Y i) * pb.gen ^ (i : ℕ) := by
    dsimp only [z, Y]
    rw [hexpv, Finset.mul_sum]
    simp only [map_mul, mul_assoc]
  have hy : Y ⟨0, hp.pos⟩ = y := by
    change x * pb.basis.repr (algebraMap B₁ K v) (Fin.cast hdim.symm ⟨0, hp.pos⟩) =
      constantProjection pb (algebraMap B₂ K x * algebraMap B₁ K v)
    rw [← Algebra.smul_def, map_smul]
    rfl
  have htail := constant_tail_mem B₂ K hp.pos (Int.natCast_nonneg R.t)
    he₂ hDelta Y (qx + qv) hexp hY
  rw [hy] at htail
  have hK : 1 + (p : ℤ) * R.t₂ =
      1 + R.tPrime + ((p : ℤ) - 1) * R.t := by
    rw [R.t₂_eq, R.tPrime_eq]
    push_cast
    ring
  have hclose : z - algebraMap B₂ K y ∈ lattice K (1 + (p : ℤ) * R.t₂) :=
    lattice_antitone K (by rw [hK]; omega) htail
  have hz : z ∈ lattice K ((p : ℤ) * (qx + qv)) := by
    simpa only [mul_add] using
      mul_mem_lattice K (map_lattice B₂ K he₂ hx) (map_lattice B₁ K he₁ hv)
  have hnorm := Total.projectionTransfer hp hG hres hchar R x v y hclose
    ((WithTop.coe_le_coe.mpr hsecond).trans ((mem_lattice K).1 hz))
  exact ⟨hclose, hnorm, by simpa only [hy, Fin.val_zero, Nat.cast_zero,
    zero_mul, add_zero] using hY ⟨0, hp.pos⟩⟩

/-- Replace the power of the actual first-field factor by its lower
norm. The gain from `O:A:lem:power` and the outer weight are combined
before descending the congruence to the base field. -/
private theorem project_product_lowerNorm
    (hres : residueDegree F K = 1)
    (x y : B₂) (v : B₁) (qx qv : ℤ)
    (hx : x ∈ lattice B₂ qx) (hv : v ∈ lattice B₁ qv)
    (hfirst : 1 + (R.tPrime : ℤ) ≤ (p : ℤ) * (qx + qv))
    (hnorm : norm B₁ K (algebraMap B₂ K x * algebraMap B₁ K v) -
      algebraMap F B₁ (norm F B₂ y) ∈ lattice B₁ (1 + (p : ℤ) * R.t₂)) :
    norm F B₂ y - norm F B₂ x * norm F B₁ v ∈ lattice F (1 + (R.t₂ : ℤ)) := by
  obtain ⟨hd₁, hrF₁, _, heF₁, _⟩ :=
    realization_tower_data hp hG hres B₁ R.degree_B₁
  obtain ⟨_, hrF₂, _, _, _⟩ :=
    realization_tower_data hp hG hres B₂ R.degree_B₂
  have hdF₁ : Module.finrank F B₁ = p := R.degree_B₁
  have htotal : Module.finrank F K = p * p := by
    rw [← Module.finrank_mul_finrank F B₁ K, hdF₁, hd₁]
  have hcross : norm B₁ K (algebraMap B₂ K x) = algebraMap F B₁ (norm F B₂ x) :=
    Total.primeDiamond_norm_restrict B₁ B₂ hp htotal R.degree_B₁ R.degree_B₂ R.B₁_ne_B₂ x
  have hpow : v ^ p - algebraMap F B₁ (norm F B₁ v) ∈
      lattice B₁ ((p : ℤ) * qv + ((p : ℤ) - 1) * R.t) := by
    have hbound := add_le_add (nsmul_le_nsmul_right ((mem_lattice B₁).1 hv) p)
      (le_refl (((((p - 1) * R.t : ℕ) : ℤ)) : WithTop ℤ))
    have hpower := Total.powerNorm F B₁ p R.t R.degree_B₁ R.odd_prime
      R.B₁_breaks.1 R.t_pos hrF₁ v
    simpa only [mem_lattice, ← WithTop.coe_nsmul, ← WithTop.coe_add,
      nsmul_eq_mul, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one] using
      hbound.trans hpower
  have hnx : norm F B₂ x ∈ lattice F qx := by
    simpa only [mem_lattice, ord_norm, hrF₂, one_nsmul] using hx
  have hweighted := mul_mem_lattice B₁ (map_lattice F B₁ heF₁ hnx) hpow
  have hK : 1 + (p : ℤ) * R.t₂ =
      1 + R.tPrime + ((p : ℤ) - 1) * R.t := by
    rw [R.t₂_eq, R.tPrime_eq]
    push_cast
    ring
  have herror : algebraMap F B₁ (norm F B₂ x) *
      (v ^ p - algebraMap F B₁ (norm F B₁ v)) ∈
      lattice B₁ (1 + (p : ℤ) * R.t₂) :=
    lattice_antitone B₁ (by rw [hK]; linarith) hweighted
  have hnorm_eq : norm B₁ K (algebraMap B₂ K x * algebraMap B₁ K v) =
      algebraMap F B₁ (norm F B₂ x) * v ^ p := by
    rw [map_mul, hcross, LanglandsFirstMainLemma.norm_algebraMap, hd₁]
  have hmap : algebraMap F B₁ (norm F B₂ y - norm F B₂ x * norm F B₁ v) ∈
      lattice B₁ (1 + (p : ℤ) * R.t₂) := by
    convert (lattice B₁ _).sub_mem herror hnorm using 1
    rw [hnorm_eq, map_sub, map_mul]
    ring
  -- The exact intersection is A ∩ P₁^(1+p*t₂) = p_A^(1+t₂).
  by_cases hz : norm F B₂ y - norm F B₂ x * norm F B₁ v = 0
  · simp [hz]
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).2 hz)
  rw [mem_lattice, ord_algebraMap, heF₁, ← hq, ← WithTop.coe_nsmul,
    WithTop.coe_le_coe, nsmul_eq_mul] at hmap
  rw [mem_lattice, ← hq, WithTop.coe_le_coe]
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have htq : (R.t₂ : ℤ) < q := (mul_lt_mul_iff_right₀ hpZ).mp (by linarith)
  omega

set_option maxHeartbeats 1000000 in
/-- **All source and target depths, Paper Lemma 9.25.**

The prescribed power basis has the actual Artin--Schreier generator.
The witness `w` retains its exact lower norm `u⁻¹`. The linear setup and
the coefficient estimate are constructed for these inputs, in either
field characteristic. The two representatives are the literal constant
projections of `O:T:XandY`, with source modulus `1 + p*t₂` and lower norm
modulus `1 + t₂`. The full weights occur in both norm congruences.

The depth `m` and all lattice indices are integers. The positive integer
ceiling defining `c₂` is cast to an integer only after its computation.
No character evaluation or four-factor equality is a hypothesis. -/
theorem representatives
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (pb : PowerBasis B₂ K) (a : B₂)
    (hroot : pb.gen ^ p - pb.gen = algebraMap B₂ K a)
    (hDelta : ord K pb.gen = ((-(R.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ R.t)
    (m : ℤ) (hmt : (R.t : ℤ) < (p : ℤ) * m)
    (u : Fˣ) (hu : ord F (u : F) = (m : WithTop ℤ))
    (w : B₂ˣ) (hw : normUnits F B₂ w = u⁻¹) :
    let C := 1 + algebraMap F B₂ (u : F) * a
    let A₀ := norm F B₂ a
    let D := 1 + (u : F) ^ p * A₀
    let s := -elementarySymmetric B₁ K (p - 1) pb.gen
    let H := norm F B₁ s
    let T := trace B₁ K ((pb.gen / algebraMap B₂ K (w : B₂)) ^ (p - 1))
    let J := norm F B₁ T
    let Xs := algebraMap B₁ K s /
      (algebraMap B₂ K (w : B₂) ^ (p - 2) * algebraMap B₂ K C ^ 2)
    let XT := algebraMap B₂ K a * algebraMap B₁ K T /
      (algebraMap B₂ K (w : B₂) ^ (p - 1) * algebraMap B₂ K C ^ 2)
    let ys := constantProjection pb Xs
    let yT := constantProjection pb XT
    let c₂ : ℤ := ((1 + R.t₂) ⌈/⌉ p : ℕ)
    Xs - algebraMap B₂ K ys ∈ lattice K (1 + (p : ℤ) * R.t₂) ∧
      XT - algebraMap B₂ K yT ∈ lattice K (1 + (p : ℤ) * R.t₂) ∧
      norm F B₂ ys - (u : F) ^ (p - 2) * H / D ^ 2 ∈
        lattice F (1 + (R.t₂ : ℤ)) ∧
      norm F B₂ yT - (u : F) ^ (p - 1) * A₀ * J / D ^ 2 ∈
        lattice F (1 + (R.t₂ : ℤ)) ∧
      ys ∈ lattice B₂ c₂ ∧ yT ∈ lattice B₂ c₂ := by
  classical
  dsimp only
  let C := 1 + algebraMap F B₂ (u : F) * a
  let A₀ := norm F B₂ a
  let D := 1 + (u : F) ^ p * A₀
  let P := norm F B₂ C
  let s := -elementarySymmetric B₁ K (p - 1) pb.gen
  let H := norm F B₁ s
  let T := trace B₁ K ((pb.gen / algebraMap B₂ K (w : B₂)) ^ (p - 1))
  let J := norm F B₁ T
  let xs : B₂ := ((w : B₂) ^ (p - 2) * C ^ 2)⁻¹
  let xT : B₂ := a / ((w : B₂) ^ (p - 1) * C ^ 2)
  let Xs := algebraMap B₂ K xs * algebraMap B₁ K s
  let XT := algebraMap B₂ K xT * algebraMap B₁ K T
  let ys := constantProjection pb Xs
  let yT := constantProjection pb XT
  have hXs : algebraMap B₁ K s /
      (algebraMap B₂ K (w : B₂) ^ (p - 2) * algebraMap B₂ K C ^ 2) = Xs := by
    simp only [Xs, xs, map_inv₀, map_mul, map_pow, div_eq_mul_inv, mul_comm]
  have hXT : algebraMap B₂ K a * algebraMap B₁ K T /
      (algebraMap B₂ K (w : B₂) ^ (p - 1) * algebraMap B₂ K C ^ 2) = XT := by
    dsimp only [XT, xT]
    rw [map_div₀, map_mul, map_pow, map_pow]
    ring
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  rw [hXs, hXT]
  change Xs - algebraMap B₂ K ys ∈ lattice K (1 + (p : ℤ) * R.t₂) ∧
    XT - algebraMap B₂ K yT ∈ lattice K (1 + (p : ℤ) * R.t₂) ∧
    norm F B₂ ys - (u : F) ^ (p - 2) * H / D ^ 2 ∈ lattice F (1 + (R.t₂ : ℤ)) ∧
    norm F B₂ yT - (u : F) ^ (p - 1) * A₀ * J / D ^ 2 ∈ lattice F (1 + (R.t₂ : ℤ)) ∧
    ys ∈ lattice B₂ (((1 + R.t₂) ⌈/⌉ p : ℕ) : ℤ) ∧
    yT ∈ lattice B₂ (((1 + R.t₂) ⌈/⌉ p : ℕ) : ℤ)
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hp3 : (3 : ℤ) ≤ p := by have := R.odd_prime; omega
  have hmpos : 0 < m := by nlinarith [Int.natCast_nonneg R.t]
  have hmNat : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hmpos.le
  have hmtNat : R.t < p * m.toNat := by
    exact_mod_cast (show (R.t : ℤ) < (p : ℤ) * (m.toNat : ℤ) by simpa only [hmNat] using hmt)
  have hwNorm : norm F B₂ (w : B₂) = (u : F)⁻¹ := by
    simpa only [coe_normUnits, Units.val_inv_eq_inv_val] using congrArg Units.val hw
  have hmW : ord F (Linear.transitionNorm R w)⁻¹ = (m : WithTop ℤ) := by
    rw [Linear.transitionNorm, hwNorm, inv_inv, hu]
  have L := Linear.oddLinearData_construct R hres hchar pb.gen a w m
    hroot hDelta hprime pb.adjoin_gen_eq_top hmW hmt
  have hden := denominators hp hG R hres hmtNat pb.gen hDelta u
    (by simpa only [hmNat] using hu) w hw
  simp only [L.norm_eq_a] at hden
  obtain ⟨hC, _hD, _hP, _, hdenS, hdenT, _⟩ := hden
  change ord B₂ C = 0 at hC
  change (u : F) ^ (p - 2) * H * (P⁻¹ ^ 2 - D⁻¹ ^ 2) ∈
    lattice F (1 + (R.t₂ : ℤ)) at hdenS
  change (u : F) ^ (p - 1) * A₀ * J * (P⁻¹ ^ 2 - D⁻¹ ^ 2) ∈
    lattice F (1 + (R.t₂ : ℤ)) at hdenT
  obtain ⟨htrace, _, _, hs⟩ := Models.realization_twistedEstimates_of_coordinate
    hp hG hres hchar R pb.gen a hroot hDelta hprime pb.adjoin_gen_eq_top
  change ((((p : ℤ) - 1) * R.delta : ℤ) : WithTop ℤ) ≤ ord B₁ s at hs
  have hT : T ∈ lattice B₁ (((p : ℤ) - 1) * (m + R.delta)) := by
    have ht := htrace ((w : B₂)⁻¹ ^ (p - 1)) (p - 1) (by omega)
    have harg : algebraMap B₂ K ((w : B₂)⁻¹ ^ (p - 1)) * pb.gen ^ (p - 1) =
        (pb.gen / algebraMap B₂ K (w : B₂)) ^ (p - 1) := by
      rw [map_pow, map_inv₀, div_pow]
      simp only [div_eq_mul_inv, inv_pow, mul_comm]
    rw [harg, ord_pow, ord_inv, L.w_order] at ht
    simp only [← WithTop.LinearOrderedAddCommGroup.coe_neg, neg_neg,
      ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul,
      Nat.cast_sub hp.one_le, Nat.cast_one] at ht
    have hdepth : ((p : ℤ) - 1) * (m + R.delta) =
        ((p : ℤ) - 1) * R.t₂ - ((p : ℤ) - 1) * R.t + ((p : ℤ) - 1) * m := by
      rw [R.t₂_eq]
      push_cast
      ring
    rw [mem_lattice, hdepth]
    exact ht
  let qs : ℤ := ((p : ℤ) - 2) * m + ((p : ℤ) - 1) * R.delta
  let qT : ℤ := 2 * ((p : ℤ) - 1) * m - R.t + ((p : ℤ) - 1) * R.delta
  have harith := representative_depths p R.t R.delta m hp3 (Int.natCast_nonneg R.t)
    (Int.natCast_nonneg R.delta) (by omega)
  have hbounds : (1 + (R.tPrime : ℤ) ≤ (p : ℤ) * qs ∧
      1 + R.t₂ + ((p : ℤ) - 3) * R.t ≤ (p : ℤ) * qs) ∧
      (1 + (R.tPrime : ℤ) ≤ (p : ℤ) * qT ∧
      1 + R.t₂ + ((p : ℤ) - 3) * R.t ≤ (p : ℤ) * qT) := by
    simpa only [R.tPrime_eq, R.t₂_eq, Nat.cast_add, Nat.cast_mul,
      add_assoc, qs, qT] using harith
  have hxs : xs ∈ lattice B₂ (((p : ℤ) - 2) * m) := by
    rw [mem_lattice]
    have hxord : ord B₂ xs = ((((p : ℤ) - 2) * m : ℤ) : WithTop ℤ) := by
      simp only [xs, ord_inv, ord_mul, ord_pow, L.w_order, hC, nsmul_zero, add_zero,
        ← WithTop.coe_nsmul, ← WithTop.LinearOrderedAddCommGroup.coe_neg,
        nsmul_eq_mul, Nat.cast_sub (by omega : 2 ≤ p), Nat.cast_ofNat]
      congr 1
      ring
    exact hxord.ge
  have hxT : xT ∈ lattice B₂ (((p : ℤ) - 1) * m - R.t) := by
    rw [mem_lattice]
    have hxord : ord B₂ xT = ((((p : ℤ) - 1) * m - R.t : ℤ) : WithTop ℤ) := by
      simp only [xT, ord_div, ord_mul, ord_pow, L.w_order, L.a_order, hC,
        nsmul_zero, add_zero, ← WithTop.coe_nsmul,
        ← WithTop.LinearOrderedAddCommGroup.coe_sub,
        nsmul_eq_mul, Nat.cast_sub hp.one_le, Nat.cast_one]
      congr 1
      ring
    exact hxord.ge
  have hTdepth : ((p : ℤ) - 1) * m - R.t + ((p : ℤ) - 1) * (m + R.delta) = qT := by
    dsimp only [qT]
    ring
  obtain ⟨hcloseS, hnormS, hys⟩ := project_product hp hG R hres hchar pb a
    hroot hDelta hprime xs s (((p : ℤ) - 2) * m) (((p : ℤ) - 1) * R.delta)
    hxs hs hbounds.1.1 hbounds.1.2
  obtain ⟨hcloseT, hnormT, hyT⟩ := project_product hp hG R hres hchar pb a
    hroot hDelta hprime xT T (((p : ℤ) - 1) * m - R.t) (((p : ℤ) - 1) * (m + R.delta))
    hxT hT (by simpa only [hTdepth] using hbounds.2.1)
      (by simpa only [hTdepth] using hbounds.2.2)
  have hlowerS := project_product_lowerNorm hp hG R hres xs ys s
    (((p : ℤ) - 2) * m) (((p : ℤ) - 1) * R.delta) hxs hs hbounds.1.1 hnormS
  have hlowerT := project_product_lowerNorm hp hG R hres xT yT T
    (((p : ℤ) - 1) * m - R.t) (((p : ℤ) - 1) * (m + R.delta)) hxT hT
    (by simpa only [hTdepth] using hbounds.2.1) hnormT
  have hnxs : norm F B₂ xs * H = (u : F) ^ (p - 2) * H / P ^ 2 := by
    dsimp only [xs]
    rw [Algebra.norm_inv, map_mul, map_pow, map_pow, hwNorm]
    simp only [mul_inv_rev, inv_pow, inv_inv, div_eq_mul_inv, P]
    ring
  have hnxT : norm F B₂ xT * J = (u : F) ^ (p - 1) * A₀ * J / P ^ 2 := by
    dsimp only [xT]
    rw [div_eq_mul_inv, map_mul, Algebra.norm_inv, map_mul, map_pow, map_pow, hwNorm]
    simp only [mul_inv_rev, inv_pow, inv_inv, div_eq_mul_inv, P, A₀]
    ring
  rw [show norm F B₁ s = H from rfl, hnxs] at hlowerS
  rw [show norm F B₁ T = J from rfl, hnxT] at hlowerT
  have hfinalS : norm F B₂ ys - (u : F) ^ (p - 2) * H / D ^ 2 ∈
      lattice F (1 + (R.t₂ : ℤ)) := by
    convert (lattice F _).add_mem hlowerS hdenS using 1
    simp only [div_eq_mul_inv, inv_pow]
    ring
  have hfinalT : norm F B₂ yT - (u : F) ^ (p - 1) * A₀ * J / D ^ 2 ∈
      lattice F (1 + (R.t₂ : ℤ)) := by
    convert (lattice F _).add_mem hlowerT hdenT using 1
    simp only [div_eq_mul_inv, inv_pow]
    ring
  obtain ⟨_, _, _, _, he₂⟩ := realization_tower_data hp hG hres B₂ R.degree_B₂
  have hnonneg : 0 ≤ ((p : ℤ) - 3) * R.t :=
    mul_nonneg (by omega) (Int.natCast_nonneg R.t)
  have hysK : algebraMap B₂ K ys ∈ lattice K ((1 + R.t₂ : ℕ) : ℤ) :=
    lattice_antitone K (by push_cast; linarith [hbounds.1.2]) (map_lattice B₂ K he₂ hys)
  have hyTK : algebraMap B₂ K yT ∈ lattice K ((1 + R.t₂ : ℕ) : ℤ) :=
    lattice_antitone K (by rw [hTdepth]; push_cast; linarith [hbounds.2.2])
      (map_lattice B₂ K he₂ hyT)
  exact ⟨hcloseS, hcloseT, hfinalS, hfinalT,
    Models.monomialPhase_ceil_depth B₂ K hp.pos he₂ hysK,
    Models.monomialPhase_ceil_depth B₂ K hp.pos he₂ hyTK⟩

end Diamond

end

end LanglandsSecondMainLemma.Odd.Transition
