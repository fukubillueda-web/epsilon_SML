import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Odd.Transition.Representatives
import LanglandsSecondMainLemma.Odd.NormPhase

/-!
# Odd / Transition / Norm Half

Paper Lemma 9.26 (`O:T:actualnorm`). The rational half is applied after
the degree-`p` norm. An additive-character value has `p`-power order:
each argument reaches an open trivial lattice after multiplication by
a sufficiently large power of the residue characteristic. Consequently
a value whose square is one is one when `p` is odd.

The actual norm-character chart supplies the exact additive conductor
and the accepted whole-subgroup norm phase. The accepted representatives
then give the two weighted lower-norm substitutions at that conductor.
All traces, norms, and character arguments remain in their named fields.
-/

namespace LanglandsSecondMainLemma.Odd.Transition

noncomputable section

open LanglandsFirstMainLemma

open private residueCharacteristic_mem_lattice_one from
  LanglandsFirstMainLemma.Ramification.NormBelowBreak
open private additiveConductor_of_normCharacterChart from
  LanglandsSecondMainLemma.Odd.Models.Setup
open private realization_tower_data from
  LanglandsSecondMainLemma.Odd.Models.Realization

section RationalHalf

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Continuity and the valuation of the residue characteristic give
`p`-primary order for every additive-character value, including in
equal characteristic. The valuation of the argument may be negative. -/
private theorem addChar_prime_power_order {p : ℕ}
    (hchar : residueCharacteristic F = p) (Psi : ContinuousAddChar F) (x : F) :
    ∃ n : ℕ, Psi x ^ (p ^ n) = 1 := by
  obtain ⟨r, htriv⟩ := exists_addCharTrivialOnLattice F Psi
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).2 hx)
  have hxk : x ∈ lattice F k := by rw [mem_lattice, ← hk]
  have hp : (p : F) ∈ lattice F 1 := by
    simpa [hchar] using residueCharacteristic_mem_lattice_one F
  have hpow (n : ℕ) : (p : F) ^ n ∈ lattice F (n : ℤ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      simpa only [pow_succ, Nat.cast_add, Nat.cast_one] using mul_mem_lattice F ih hp
  let n := (r - k).toNat
  have hnx : (p : F) ^ n * x ∈ lattice F r :=
    lattice_antitone F (by have := Int.self_le_toNat (r - k); dsimp only [n]; omega)
      (mul_mem_lattice F (hpow n) hxk)
  refine ⟨n, ?_⟩
  calc
    Psi x ^ (p ^ n) = Psi ((p ^ n) • x) :=
      (Psi.toAddChar.map_nsmul_eq_pow _ _).symm
    _ = 1 := htriv _ (by simpa only [nsmul_eq_mul, Nat.cast_pow] using hnx)

private theorem ord_two {p : ℕ} (hchar : residueCharacteristic F = p)
    (hodd : 2 < p) : ord F (2 : F) = 0 :=
  ord_natCast_eq_zero_of_lt_residueCharacteristic F (j := 2) (by omega) (by omega)

/-- Rational halving preserves a trivial additive-character value in
odd residue characteristic. This only concerns the rational scalar `1/2`. -/
private theorem addChar_half_eq_one {p : ℕ} (hp : p.Prime)
    (hchar : residueCharacteristic F = p) (hodd : 2 < p)
    (Psi : ContinuousAddChar F) (x : F) (hx : Psi x = 1) :
    Psi (x / 2) = 1 := by
  have htwo : (2 : F) ≠ 0 := (ord_ne_top_iff F).1 (by rw [ord_two F hchar hodd]; simp)
  obtain ⟨n, hn⟩ := addChar_prime_power_order F hchar Psi (x / 2)
  have hsquare : Psi (x / 2) ^ 2 = 1 := by
    calc
      Psi (x / 2) ^ 2 = Psi (2 • (x / 2)) :=
        (Psi.toAddChar.map_nsmul_eq_pow 2 _).symm
      _ = Psi x := by congr 1; simp [nsmul_eq_mul, htwo, mul_div_cancel₀]
      _ = 1 := hx
  have hcoprime : (p ^ n).Coprime 2 :=
    (hp.odd_of_ne_two (by omega)).coprime_two_right.pow_left n
  exact (pow_eq_one_iff_of_coprime hcoprime).mp ⟨hn, hsquare⟩

private theorem half_mem_lattice {p : ℕ}
    (hchar : residueCharacteristic F = p) (hodd : 2 < p)
    {r : ℤ} {x : F} (hx : x ∈ lattice F r) : x / 2 ∈ lattice F r := by
  rw [mem_lattice, ord_div, ord_two F hchar hodd, sub_zero]
  exact hx

end RationalHalf

/-- The rational half of the actual whole-subgroup norm phase. The norm
argument is `y`, while the additive arguments are halved afterwards. -/
private theorem normPhase_half
    (F E : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Free F E] [Module.Finite F E] [PrimeCyclicExtension F E]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
    (hres : residueDegree F E = 1)
    (hchar : residueCharacteristic F = Module.finrank F E)
    (hodd : 2 < Module.finrank F E)
    (q : ℕ) (hq : q = (t + 1) ⌈/⌉ Module.finrank F E) (hqpos : 0 < q)
    (tau : NormCharacter F E) (htau : tau ≠ 1) (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (hchart : ∀ x : lattice F (q : ℤ),
      tau.1 (positiveUnitOfLattice F hqpos (-x)) =
        Psi (truncatedLog (Module.finrank F E) (x : F)))
    (y : E) (hy : y ∈ lattice E (q : ℤ)) :
    tracePullbackAddChar F E Psi (y / 2) = Psi (-norm F E y / 2) ∧
      tracePullbackAddChar F E Psi (-y / 2) = Psi (norm F E y / 2) := by
  have hphase := (normPhase F E ht htpos hres hchar (by omega)
    q hq hqpos tau htau Psi hPsi hchart y hy).1
  have hhalf := addChar_half_eq_one F (PrimeCyclicExtension.degree_prime F E)
    hchar hodd Psi (trace F E y + norm F E y) hphase
  have htrace : trace F E (y / 2) = trace F E y / 2 := by
    have h := (trace F E).map_smul (2 : F)⁻¹ y
    simpa only [Algebra.smul_def, smul_eq_mul, map_inv₀, map_ofNat,
      div_eq_mul_inv, mul_comm] using h
  have hfirst : tracePullbackAddChar F E Psi (y / 2) = Psi (-norm F E y / 2) := by
    rw [tracePullbackAddChar_apply, htrace]
    apply div_eq_one.mp
    change Psi.toAddChar _ / Psi.toAddChar _ = 1
    rw [← AddChar.map_sub_eq_div]
    change Psi (trace F E y / 2 - (-norm F E y / 2)) = 1
    rw [show trace F E y / 2 - (-norm F E y / 2) =
      (trace F E y + norm F E y) / 2 by ring]
    exact hhalf
  refine ⟨hfirst, ?_⟩
  calc
    tracePullbackAddChar F E Psi (-y / 2) =
        (tracePullbackAddChar F E Psi (y / 2))⁻¹ := by
      rw [neg_div]
      exact (tracePullbackAddChar F E Psi).toAddChar.map_neg_eq_inv _
    _ = (Psi (-norm F E y / 2))⁻¹ := congrArg Inv.inv hfirst
    _ = Psi (norm F E y / 2) := by
      rw [neg_div]
      change (Psi.toAddChar (-(norm F E y / 2)))⁻¹ = Psi.toAddChar (norm F E y / 2)
      rw [AddChar.map_neg_eq_inv, inv_inv]

section Diamond

set_option backward.isDefEq.respectTransparency false

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

local instance : PrimeCyclicExtension F B₂ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₂
    (Basic.intermediateField_tower_compatible hp hG B₂ R.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.1

/-- **Paper Lemma 9.26 (`O:T:actualnorm`, `O:T:normhalves`).**
For the prescribed coordinate and exact norm witness in the totally
ramified odd diamond, evaluate the two actual lower-field representatives
with the rational half outside the norm.

`Psi` is the full coefficient character of the nontrivial actual norm
character `tau` on its entire truncated-log chart. Its exact conductor
is proved from this chart. The source-depth estimates, norm congruences,
and representative choices are supplied by `representatives`, rather
than assumed as phase identities. The statement includes both field
characteristics and the boundary `p = 3`, `delta = 0`. -/
theorem normHalf
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (pb : PowerBasis B₂ K) (a : B₂)
    (hroot : pb.gen ^ p - pb.gen = algebraMap B₂ K a)
    (hDelta : ord K pb.gen = ((-(R.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ R.t)
    (m : ℤ) (hmt : (R.t : ℤ) < (p : ℤ) * m)
    (u : Fˣ) (hu : ord F (u : F) = (m : WithTop ℤ))
    (w : B₂ˣ) (hw : normUnits F B₂ w = u⁻¹)
    (c : ℕ) (hc : c = (R.t₂ + 1) ⌈/⌉ p) (hcpos : 0 < c)
    (tau : NormCharacter F B₂) (htau : tau ≠ 1) (Psi : ContinuousAddChar F)
    (hchart : ∀ x : lattice F (c : ℤ),
      tau.1 (positiveUnitOfLattice F hcpos (-x)) =
        Psi (truncatedLog p (x : F))) :
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
    tracePullbackAddChar F B₂ Psi (ys / 2) =
        Psi (-(u : F) ^ (p - 2) * H / (2 * D ^ 2)) ∧
      tracePullbackAddChar F B₂ Psi (-yT / 2) =
        Psi ((u : F) ^ (p - 1) * A₀ * J / (2 * D ^ 2)) := by
  classical
  dsimp only
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
  change tracePullbackAddChar F B₂ Psi (ys / 2) =
      Psi (-(u : F) ^ (p - 2) * H / (2 * D ^ 2)) ∧
    tracePullbackAddChar F B₂ Psi (-yT / 2) =
      Psi ((u : F) ^ (p - 1) * A₀ * J / (2 * D ^ 2))
  obtain ⟨_, hres₂, _, _, _⟩ := realization_tower_data hp hG hres B₂ R.degree_B₂
  have ht₂pos : 0 < R.t₂ := R.t_pos.trans_le R.t_le_t₂
  have hPsi := additiveConductor_of_normCharacterChart F B₂ hp R.odd_prime hchar
    R.degree_B₂ R.B₂_breaks.1 ht₂pos hres₂ hc hcpos tau htau Psi hchart
  have htriv : AddCharTrivialOnLattice F Psi (1 + (R.t₂ : ℤ)) := by
    simpa only [neg_neg, Nat.cast_add, Nat.cast_one, add_comm] using hPsi.trivial
  obtain ⟨_, _, hnormS, hnormT, hys, hyT⟩ :=
    representatives hp hG R hres hchar pb a hroot hDelta hprime m hmt u hu w hw
  change norm F B₂ ys - (u : F) ^ (p - 2) * H / D ^ 2 ∈
    lattice F (1 + (R.t₂ : ℤ)) at hnormS
  change norm F B₂ yT - (u : F) ^ (p - 1) * A₀ * J / D ^ 2 ∈
    lattice F (1 + (R.t₂ : ℤ)) at hnormT
  have hdomain : ((1 + R.t₂) ⌈/⌉ p : ℕ) = c := by rw [hc, Nat.add_comm 1]
  change ys ∈ lattice B₂ (((1 + R.t₂) ⌈/⌉ p : ℕ) : ℤ) at hys
  change yT ∈ lattice B₂ (((1 + R.t₂) ⌈/⌉ p : ℕ) : ℤ) at hyT
  rw [hdomain] at hys hyT
  have hdegree₂ : Module.finrank F B₂ = p := R.degree_B₂
  have hphase (y : B₂) (hy : y ∈ lattice B₂ (c : ℤ)) :=
    normPhase_half F B₂ R.B₂_breaks.1 ht₂pos hres₂
      (by rw [hdegree₂]; exact hchar) (by rw [hdegree₂]; exact R.odd_prime)
      c (by rw [hdegree₂]; exact hc) hcpos tau htau Psi hPsi
      (by simpa only [hdegree₂] using hchart) y hy
  have hhalfS := half_mem_lattice F hchar R.odd_prime hnormS
  have hhalfT := half_mem_lattice F hchar R.odd_prime hnormT
  constructor
  · rw [(hphase ys hys).1]
    apply div_eq_one.mp
    change Psi.toAddChar _ / Psi.toAddChar _ = 1
    rw [← AddChar.map_sub_eq_div]
    apply htriv
    convert (lattice F _).neg_mem hhalfS using 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · rw [(hphase yT hyT).2]
    apply div_eq_one.mp
    change Psi.toAddChar _ / Psi.toAddChar _ = 1
    rw [← AddChar.map_sub_eq_div]
    apply htriv
    convert hhalfT using 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

end Diamond

end

end LanglandsSecondMainLemma.Odd.Transition
