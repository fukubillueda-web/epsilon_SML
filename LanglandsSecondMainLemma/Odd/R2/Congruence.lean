import LanglandsFirstMainLemma.Ramification.NormRepresentatives
import LanglandsSecondMainLemma.Odd.R2.Normalization
import LanglandsSecondMainLemma.Odd.NormLog

/-!
# Odd / R2 / Congruence

Blueprint: blueprint/tasks/Odd/R2/Congruence.md
Paper: Theorem 8.14 (`O:R:R2`), with the setup at lines 2782--2810.

The actual characters agree on the entire shallow subgroup. The
truncated-logarithm bijection and the exact additive annihilator identify
the coefficient class. The cyclic norm filtration then descends this
class, retaining the permitted depth-`t` error in the approximate norm.
All additive congruence exponents, including the terminal modulus, are
integers.
-/

namespace LanglandsSecondMainLemma.Odd.R2

noncomputable section

open LanglandsFirstMainLemma

set_option backward.isDefEq.respectTransparency false

open private additivePhase_sub from LanglandsSecondMainLemma.Odd.Models.TwistFormula
open private trace_depths from LanglandsSecondMainLemma.Odd.R2.Trace

/-- Comparing phases on the entire positive ideal determines the
absolute coefficient class. In particular, no pointwise description of
the character kernel is used. -/
private theorem congruence_coefficient
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (p q : ℕ) (hp : p.Prime) (hq : 0 < q)
    (hchar : residueCharacteristic E = p)
    (Psi : ContinuousAddChar E) (T : ℤ)
    (hPsi : IsAdditiveConductor E Psi (-T)) (s v : E)
    (hphase : ∀ x : lattice E (q : ℤ),
      Psi ((1 - s) * truncatedLog p (x : E)) =
        Psi ((1 - v) * truncatedLog p (x : E))) :
    s - v ∈ lattice E (T - (q : ℤ)) := by
  let psi : LocalAddCharData E := ⟨Psi, -T, hPsi⟩
  apply (lamprechtAnnihilatorLeft E psi (Γ := 1) (M := T)
    (r := (q : ℤ)) (by simp [psi])).1
  intro y hy
  obtain ⟨x, hx⟩ := (truncatedLogOnLattice_bijective E p q hchar hp hq).2 ⟨y, hy⟩
  have hxy : truncatedLog p (x : E) = y := congrArg Subtype.val hx
  have heq := hphase x
  rw [hxy] at heq
  change Psi ((s - v) * y / 1) = 1
  rw [div_one, show (s - v) * y = (1 - v) * y - (1 - s) * y by ring,
    additivePhase_sub, heq]
  exact div_self' _

section NormDescent

variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

/-- Descend an absolute coefficient congruence through the cyclic norm
at a positive relative depth at most the break. The comparison element
has exact integer order `d`; zero is allowed for neither the denominator
nor its norm. -/
private theorem congruence_norm
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hr : 0 < r) (hrt : r ≤ t)
    (s v : E) (d : ℤ) (hv : ord E v = (d : WithTop ℤ))
    (hsv : s - v ∈ lattice E (d + (r : ℤ))) :
    norm F E s - norm F E v ∈ lattice F (d + (r : ℤ)) := by
  have hvne : v ≠ 0 := (ord_ne_top_iff E).1 (by rw [hv]; exact WithTop.coe_ne_top)
  have hz : (s - v) / v ∈ lattice E (r : ℤ) :=
    (div_mem_lattice_iff E v (s - v) d (r : ℤ) hv).2 hsv
  let u := positiveUnitOfLattice E hr ⟨(s - v) / v, hz⟩
  have hsu : s = v * ((u : Eˣ) : E) := by
    change s = v * (1 + (s - v) / v)
    field_simp
    ring
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have hnu : normUnits F E (u : Eˣ) ∈ unitFiltration F r :=
    normMapsUnitFiltration_belowBreak F E ht hrt hres pi hpi hgen _ u.property
  have hnsub : norm F E ((u : Eˣ) : E) - 1 ∈ lattice F (r : ℤ) := by
    have h := (mem_unitFiltration_succ_iff_sub_mem_lattice F (r - 1) _).1
      (by simpa only [Nat.sub_add_cancel hr] using hnu)
    simpa only [Nat.sub_add_cancel hr, coe_normUnits] using h
  have hnv : norm F E v ∈ lattice F d := by
    rw [mem_lattice, ord_norm, hres, one_nsmul, hv]
  have h := mul_mem_lattice F hnv hnsub
  rw [mul_sub_one, ← map_mul, ← hsu] at h
  exact h

end NormDescent

/-- The relative precision is a positive natural unit-filtration index,
with its exact integer value recorded before it is used in a lattice. -/
private theorem congruence_depth {p t : ℕ} (hp : 2 < p) (ht : 0 < t) :
    ∃ R₀ : ℕ, 0 < R₀ ∧ R₀ ≤ t ∧
      (R₀ : ℤ) = (t : ℤ) + 1 - ((t + 1) ⌈/⌉ p : ℕ) := by
  have hcpos : 0 < (t + 1) ⌈/⌉ p := (trace_depths (d := 0) hp ht).1
  have hct : (t + 1) ⌈/⌉ p ≤ t := by
    rw [ceilDiv_le_iff_le_mul (by omega : 0 < p)]
    have hmul := Nat.mul_le_mul_right t (show 2 ≤ p by omega)
    omega
  exact ⟨t + 1 - (t + 1) ⌈/⌉ p, by omega, by omega, by omega⟩

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
local instance : PrimeCyclicExtension F B₂ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₂
    (Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.1

open private realization_tower_data from LanglandsSecondMainLemma.Odd.Models.Realization
open private commutator_additiveConductor from LanglandsSecondMainLemma.Odd.R2.Commutator
open private normalization_of_shallow_phase from LanglandsSecondMainLemma.Odd.R2.Normalization

include hp hG hres hchar D

/-- **Paper Theorem 8.14 (`O:R:R2`).** For the actual coordinate and full
minimal model, the norm of the signed symmetric coefficient is congruent
to `rho^(p-1)` at the strong modulus and at every required transition
modulus. Here `Psi(z) = e_F(alpha*z)` and `rho = beta/alpha`; the two
nontrivial norm-character charts use precisely this same additive phase.

The approximate norm denominator and its error unit are constructed in
the proof. The whole-subgroup comparison follows from the actual
commutator and its proved normalization. The coordinate and full-model
hypotheses are supplied by `congruence_realization` below from the genuine
primitive compatible pair. Both characteristics and both break
configurations are retained. -/
theorem congruence
    (r₁ r₂ : ℕ) (hr₁ : r₁ = (D.t + 1) ⌈/⌉ p)
    (hr₂ : r₂ = (D.t₂ + 1) ⌈/⌉ p) (hr₁pos : 0 < r₁) (hr₂pos : 0 < r₂)
    (tau₁ : NormCharacter F B₁) (htau₁ : tau₁ ≠ 1)
    (tau₂ : NormCharacter F B₂) (htau₂ : tau₂ ≠ 1)
    (Psi : ContinuousAddChar F) (rho : Fˣ)
    (hrho : ord F (rho : F) = ((D.delta : ℤ) : WithTop ℤ))
    (hchart₁ : ∀ z : lattice F (r₁ : ℤ),
      tau₁.1 (positiveUnitOfLattice F hr₁pos (-z)) =
        Psi ((rho : F) * truncatedLog p (z : F)))
    (hchart₂ : ∀ z : lattice F (r₂ : ℤ),
      tau₂.1 (positiveUnitOfLattice F hr₂pos (-z)) = Psi (truncatedLog p (z : F)))
    (Delta : K) (a : B₂)
    (hroot : Delta ^ p - Delta = algebraMap B₂ K a)
    (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ D.t) (hgen : Algebra.adjoin B₂ ({Delta} : Set K) = ⊤)
    (chi : ContinuousQuasiChar B₁) (phi₂ : ContinuousQuasiChar B₂)
    (hcompat : normQuasiChar B₁ K chi = normQuasiChar B₂ K phi₂)
    (hprimitive : ¬ ∃ theta : ContinuousQuasiChar F,
      normQuasiChar F K theta = normQuasiChar B₂ K phi₂)
    (hmodel : ∀ u : unitFiltration B₁ (Models.firstModelDepth D),
      chi u = tracePullbackAddChar F B₁ Psi
        (norm B₁ K Delta * truncatedLog p (1 - ((u : B₁ˣ) : B₁)))) :
    let H := norm F B₁ (-elementarySymmetric B₁ K (p - 1) Delta)
    H - (rho : F) ^ (p - 1) ∈
        lattice F ((D.t : ℤ) + 1 - ((D.t + 1) ⌈/⌉ p : ℕ) +
          ((p : ℤ) - 1) * D.delta) ∧
      ∀ m : ℕ, D.t < p * m →
        H - (rho : F) ^ (p - 1) ∈
          lattice F (1 + (D.t₂ : ℤ) - ((p : ℤ) - 2) * m) := by
  let s := -elementarySymmetric B₁ K (p - 1) Delta
  let q := D.delta + (D.t + 1) ⌈/⌉ p
  let R : ℤ := (D.t : ℤ) + 1 - ((D.t + 1) ⌈/⌉ p : ℕ) +
    ((p : ℤ) - 1) * D.delta
  let ds : ℤ := ((p : ℤ) - 1) * D.delta
  have hdegree : Module.finrank F B₁ = p := D.degree_B₁
  obtain ⟨_, hres₁, _, hram₁, _⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  obtain ⟨c, epsilon, hnorm, hc, htrace⟩ := trace_realization hp hG hres hchar D
    r₁ r₂ hr₁ hr₂ hr₁pos hr₂pos tau₁ htau₁ tau₂ htau₂ Psi rho hrho hchart₁ hchart₂
  obtain ⟨sigma, _hnear, hphase⟩ := shift_commutator hp hG hres hchar D
    r₂ hr₂ hr₂pos tau₂ htau₂ Psi hchart₂ Delta a hroot hDelta hprime hgen chi hmodel
  let sigma₁ := IntermediateField.restrictRestrictAlgEquivMapHom F B₁ B₂ K sigma
  obtain ⟨mu, hmu, _⟩ := commutator_normCharacter hp hG hres hchar D
    chi phi₂ hcompat hprimitive sigma₁
  have hmuPhase (x : lattice B₁ (q : ℤ)) :
      mu.1 (positiveUnitOfLattice B₁ (commutator_depths hp hG D).1 (-x)) =
        tracePullbackAddChar F B₁ Psi ((1 - s) * truncatedLog p (x : B₁)) := by
    rw [hmu]
    exact hphase x
  have hnormalized := normalization_of_shallow_phase hp hG hres hchar D
    r₂ hr₂ hr₂pos tau₂ htau₂ Psi hchart₂ Delta a hroot hDelta hprime hgen mu hmuPhase
  let v := algebraMap F B₁ (rho : F) / (c : B₁)
  have hsv : s - v ∈ lattice B₁ R := by
    dsimp only [R]
    rw [← (shift_depth hp hG D).1]
    apply congruence_coefficient B₁ p q hp (commutator_depths hp hG D).1
      ((residueCharacteristic_extension_eq F B₁).trans hchar)
      (tracePullbackAddChar F B₁ Psi) ((D.tPrime + 1 : ℕ) : ℤ)
      (commutator_additiveConductor hp hG hres hchar D
        r₂ hr₂ hr₂pos tau₂ htau₂ Psi hchart₂)
    intro x
    rw [← hmuPhase, hnormalized]
    exact htrace x
  have hv : ord B₁ v = (ds : WithTop ℤ) := by
    dsimp only [v]
    rw [ord_div, ord_algebraMap, hram₁, hrho, hc]
    norm_cast
    simp only [nsmul_eq_mul, ds]
    ring
  obtain ⟨R₀, hR₀pos, hR₀t, hR₀⟩ := congruence_depth D.odd_prime D.t_pos
  have hR : ds + (R₀ : ℤ) = R := by rw [hR₀]; dsimp only [ds, R]; ring
  have hdesc : norm F B₁ s - norm F B₁ v ∈ lattice F R := by
    rw [← hR] at hsv ⊢
    exact congruence_norm F B₁ D.B₁_breaks.1 hres₁ hR₀pos hR₀t s v ds hv hsv
  have hnc : norm F B₁ (c : B₁) = (rho : F) * ((epsilon : Fˣ) : F) := by
    simpa only [coe_normUnits, Units.val_mul] using congrArg Units.val hnorm
  have hnv : norm F B₁ v = (rho : F) ^ (p - 1) * (((epsilon : Fˣ) : F)⁻¹) := by
    have hmul : norm F B₁ v * norm F B₁ (c : B₁) = (rho : F) ^ p := by
      rw [← map_mul]
      dsimp only [v]
      rw [div_mul_cancel₀ _ (Units.ne_zero c), LanglandsFirstMainLemma.norm_algebraMap,
        hdegree]
    have hpowp : (rho : F) ^ p = (rho : F) ^ (p - 1) * (rho : F) := by
      calc
        _ = (rho : F) ^ (p - 1 + 1) :=
          congrArg (fun n : ℕ ↦ (rho : F) ^ n) (Nat.sub_add_cancel hp.one_le).symm
        _ = _ := pow_succ _ _
    rw [hnc, hpowp] at hmul
    have hrne := Units.ne_zero rho
    have hene := Units.ne_zero (epsilon : Fˣ)
    apply (mul_right_cancel₀ (mul_ne_zero hrne hene))
    rw [hmul]
    field_simp
  have heinv : (((epsilon : Fˣ) : F)⁻¹) - 1 ∈ lattice F (D.t : ℤ) := by
    have h := (mem_unitFiltration_succ_iff_sub_mem_lattice F (D.t - 1)
      (epsilon : Fˣ)⁻¹).1 (by
        simpa only [Nat.sub_add_cancel D.t_pos] using
          (unitFiltration F D.t).inv_mem epsilon.property)
    simpa only [Nat.sub_add_cancel D.t_pos, Units.val_inv_eq_inv_val] using h
  have hpow : (rho : F) ^ (p - 1) ∈ lattice F ds := by
    rw [mem_lattice, ord_pow, hrho, ← WithTop.coe_nsmul, WithTop.coe_le_coe]
    simp only [nsmul_eq_mul, Nat.cast_sub hp.one_le, Nat.cast_one, ds, le_refl]
  have herror : norm F B₁ v - (rho : F) ^ (p - 1) ∈ lattice F R := by
    rw [hnv, ← mul_sub_one]
    apply lattice_antitone F _ (mul_mem_lattice F hpow heinv)
    rw [← hR]
    have : (R₀ : ℤ) ≤ D.t := by exact_mod_cast hR₀t
    omega
  have hstrong : norm F B₁ s - (rho : F) ^ (p - 1) ∈ lattice F R := by
    simpa only [sub_add_sub_cancel] using add_mem_lattice F hdesc herror
  refine ⟨hstrong, ?_⟩
  intro m hm
  apply lattice_antitone F _ hstrong
  have hcm : (D.t + 1) ⌈/⌉ p ≤ m :=
    (ceilDiv_le_iff_le_mul hp.pos).2 (by omega)
  have hcmZ : (((D.t + 1) ⌈/⌉ p : ℕ) : ℤ) ≤ m := by exact_mod_cast hcm
  have hpZ : (3 : ℤ) ≤ p := by have := D.odd_prime; omega
  have hdZ : (0 : ℤ) ≤ D.delta := by positivity
  have hmZ : (0 : ℤ) ≤ m := by positivity
  dsimp only [R]
  rw [D.t₂_eq, Nat.cast_add]
  nlinarith

open private twistNormCharacter_pow_ne_one from LanglandsSecondMainLemma.Odd.Models.TwistFormula

/-- Construct the coordinate and full first model used in `congruence`
from the prescribed primitive compatible pair. The two lower characters
are powered by the same nonzero residue exponent, so their coefficient
ratio `rho = beta/alpha` stays fixed. The first character is an allowed
Galois conjugate with the same canonical local constant. No auxiliary
commutator identity or exact norm representative is an input. -/
theorem congruence_realization
    (phi₁ : ContinuousQuasiChar B₁) (phi₂ : ContinuousQuasiChar B₂)
    (hcompat : normQuasiChar B₁ K phi₁ = normQuasiChar B₂ K phi₂)
    (hprimitive : ¬ ∃ theta : ContinuousQuasiChar F,
      normQuasiChar F K theta = normQuasiChar B₂ K phi₂)
    (hphi : QuasiCharTrivialOnUnitFiltration B₂ phi₂ (Models.secondModelConductor D))
    (r₁ r₂ : ℕ) (hr₁ : r₁ = (D.t + 1) ⌈/⌉ p)
    (hr₂ : r₂ = (D.t₂ + 1) ⌈/⌉ p) (hr₁pos : 0 < r₁) (hr₂pos : 0 < r₂)
    (tau₁ : NormCharacter F B₁) (htau₁ : tau₁ ≠ 1)
    (tau₂ : NormCharacter F B₂) (htau₂ : tau₂ ≠ 1)
    (Psi : ContinuousAddChar F) (rho : Fˣ)
    (hrho : ord F (rho : F) = ((D.delta : ℤ) : WithTop ℤ))
    (hchart₁ : ∀ z : lattice F (r₁ : ℤ),
      tau₁.1 (positiveUnitOfLattice F hr₁pos (-z)) =
        Psi ((rho : F) * truncatedLog p (z : F)))
    (hchart₂ : ∀ z : lattice F (r₂ : ℤ),
      tau₂.1 (positiveUnitOfLattice F hr₂pos (-z)) = Psi (truncatedLog p (z : F))) :
    ∃ (j : ℕ) (Delta : K) (a : B₂) (chi : ContinuousQuasiChar B₁) (sigma : Gal(B₁/F)),
      0 < j ∧ j < p ∧ tau₁ ^ j ≠ 1 ∧ tau₂ ^ j ≠ 1 ∧
      (∀ z : lattice F (r₁ : ℤ),
        (tau₁ ^ j).1 (positiveUnitOfLattice F hr₁pos (-z)) =
          (Psi ^ j) ((rho : F) * truncatedLog p (z : F))) ∧
      (∀ z : lattice F (r₂ : ℤ),
        (tau₂ ^ j).1 (positiveUnitOfLattice F hr₂pos (-z)) =
          (Psi ^ j) (truncatedLog p (z : F))) ∧
      Delta ^ p - Delta = algebraMap B₂ K a ∧
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ¬ p ∣ D.t ∧ Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ ∧ norm B₂ K Delta = a ∧
      chi = Basic.conjugateQuasiChar F B₁ sigma phi₁ ∧
      normQuasiChar B₁ K chi = normQuasiChar B₂ K phi₂ ∧
      IsMultiplicativeConductor B₁ chi (Models.firstModelConductor D) ∧
      (∀ u : unitFiltration B₁ (Models.firstModelDepth D),
        chi u = tracePullbackAddChar F B₁ (Psi ^ j)
          (norm B₁ K Delta * truncatedLog p (1 - ((u : B₁ˣ) : B₁)))) ∧
      (∀ psi : ContinuousAddChar F, psi ≠ 1 →
        localConstant B₁ chi (tracePullbackAddChar F B₁ psi) =
          localConstant B₁ phi₁ (tracePullbackAddChar F B₁ psi)) ∧
      (let H := norm F B₁ (-elementarySymmetric B₁ K (p - 1) Delta)
       H - (rho : F) ^ (p - 1) ∈
           lattice F ((D.t : ℤ) + 1 - ((D.t + 1) ⌈/⌉ p : ℕ) +
             ((p : ℤ) - 1) * D.delta) ∧
         ∀ m : ℕ, D.t < p * m →
           H - (rho : F) ^ (p - 1) ∈
             lattice F (1 + (D.t₂ : ℤ) - ((p : ℤ) - 2) * m)) := by
  obtain ⟨j, Delta, a, chi, sigma, hjpos, hjp, htau₂j, hchart₂j, hroot, hDelta,
      hprime, hgen, hnorm, hchi, hpull, hconductor, hmodel, hconstant, _hcommutator⟩ :=
    normalization_realization hp hG hres hchar D phi₁ phi₂ hcompat hprimitive hphi
      r₂ hr₂ hr₂pos tau₂ htau₂ Psi hchart₂
  obtain ⟨_, hres₁, _, _, _⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  have htau₁j := twistNormCharacter_pow_ne_one F B₁ D.degree_B₁ D.B₁_breaks.1
    hres₁ hjpos hjp tau₁ htau₁
  have hchart₁j : ∀ z : lattice F (r₁ : ℤ),
      (tau₁ ^ j).1 (positiveUnitOfLattice F hr₁pos (-z)) =
        (Psi ^ j) ((rho : F) * truncatedLog p (z : F)) := by
    intro z
    simpa only [NormCharacter.coe_pow, ContinuousMonoidHom.pow_apply,
      ContinuousAddChar.pow_apply] using congrArg (fun v : ℂˣ ↦ v ^ j) (hchart₁ z)
  exact ⟨j, Delta, a, chi, sigma, hjpos, hjp, htau₁j, htau₂j, hchart₁j, hchart₂j,
    hroot, hDelta, hprime, hgen, hnorm, hchi, hpull, hconductor, hmodel, hconstant,
    congruence hp hG hres hchar D r₁ r₂ hr₁ hr₂ hr₁pos hr₂pos
      (tau₁ ^ j) htau₁j (tau₂ ^ j) htau₂j (Psi ^ j) rho hrho hchart₁j hchart₂j
      Delta a hroot hDelta hprime hgen chi phi₂ hpull hprimitive hmodel⟩

end Diamond

end

end LanglandsSecondMainLemma.Odd.R2
