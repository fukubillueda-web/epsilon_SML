import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Q2.NormQuotient
import LanglandsSecondMainLemma.Odd.Total.TwistedEstimates

/-!
# Odd / Q2 / Moments

Paper Lemma 9.15 (`O:N:moments`). The coordinate and exact norm witness
are retained. The translated-root comparison and filtered coefficient
identity give the weighted power moments before Newton's identities.
All congruences use the integer lattice of the first lower field.
-/

namespace LanglandsSecondMainLemma.Odd.Q2

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

open private realization_tower_data realization_prime_mem from
  LanglandsSecondMainLemma.Odd.Models.Realization
open private exact_coordinate_orders_and_generation from
  LanglandsSecondMainLemma.Odd.Total.ASCoordinate
open private weighted_teichmuller_sum weighted_sum_zero_units from
  LanglandsSecondMainLemma.Odd.Total.WeightedDefect

/-- Newton comparison modulo a fractional lattice. Only the last positive
power moment can survive; all smaller differences multiply integral factors. -/
private theorem newton_comparison
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {p : ℕ} (hchar : residueCharacteristic E = p) (hodd : Odd p)
    (e₁ e₂ q₁ q₂ : ℕ → E) (he₁ : e₁ 0 = 1) (he₂ : e₂ 0 = 1)
    (hnewton₁ : ∀ i : ℕ, (i : E) * e₁ i = (-1 : E) ^ (i + 1) *
      ∑ b ∈ Finset.HasAntidiagonal.antidiagonal i with b.1 < i,
        (-1 : E) ^ b.1 * e₁ b.1 * q₁ b.2)
    (hnewton₂ : ∀ i : ℕ, (i : E) * e₂ i = (-1 : E) ^ (i + 1) *
      ∑ b ∈ Finset.HasAntidiagonal.antidiagonal i with b.1 < i,
        (-1 : E) ^ b.1 * e₂ b.1 * q₂ b.2)
    (heint : ∀ i, i < p → e₂ i ∈ lattice E 0)
    (hqint : ∀ i, 1 ≤ i → i < p → q₁ i ∈ lattice E 0)
    (c : E) (J : ℤ)
    (hmom : ∀ i, 1 ≤ i → i < p →
      q₁ i - q₂ i - (if i = p - 1 then ((p : E) - 1) * c else 0) ∈ lattice E J)
    (i : ℕ) (hi : 1 ≤ i) (hip : i < p) :
    e₁ i - e₂ i + (if i = p - 1 then c else 0) ∈ lattice E J := by
  classical
  induction i using Nat.strong_induction_on with
  | h i ih =>
    let S := (Finset.HasAntidiagonal.antidiagonal i).filter (fun b : ℕ × ℕ => b.1 < i)
    let f : ℕ × ℕ → E := fun b =>
      (-1 : E) ^ b.1 * (e₁ b.1 * q₁ b.2 - e₂ b.1 * q₂ b.2)
    have hzero : (0, i) ∈ S := by simp [S]; omega
    have hfzero : f (0, i) = q₁ i - q₂ i := by simp [f, he₁, he₂]
    let R : E := ∑ b ∈ S.erase (0, i), f b
    have hR : R ∈ lattice E J := by
      apply sum_mem_lattice E
      intro b hb
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hb
      obtain ⟨hadd, hlt⟩ := Finset.mem_filter.mp hmem
      have hadd' : b.1 + b.2 = i := by simpa using hadd
      have hb₁ : 1 ≤ b.1 := by
        by_contra h
        have hz : b.1 = 0 := by omega
        exact hne (Prod.ext hz (by omega))
      have hb₂ : 1 ≤ b.2 := by omega
      have he : e₁ b.1 - e₂ b.1 ∈ lattice E J := by
        simpa only [if_neg (by omega : b.1 ≠ p - 1), add_zero] using
          ih b.1 hlt hb₁ (by omega)
      have hq : q₁ b.2 - q₂ b.2 ∈ lattice E J := by
        simpa only [if_neg (by omega : b.2 ≠ p - 1), sub_zero] using
          hmom b.2 hb₂ (by omega)
      have hprod : e₁ b.1 * q₁ b.2 - e₂ b.1 * q₂ b.2 ∈ lattice E J := by
        have h₁ := mul_mem_lattice E he (hqint b.2 hb₂ (by omega))
        have h₂ := mul_mem_lattice E (heint b.1 (by omega)) hq
        simp only [add_zero, zero_add] at h₁ h₂
        convert (lattice E J).add_mem h₁ h₂ using 1
        ring
      simpa only [f, mem_lattice, ord_mul, ord_pow, ord_neg, ord_one,
        nsmul_zero, zero_add] using hprod
    have hsum : (∑ b ∈ S, f b) = q₁ i - q₂ i + R := by
      rw [← Finset.sum_erase_add S f hzero, hfzero]
      exact add_comm _ _
    have hn : (i : E) * (e₁ i - e₂ i) =
        (-1 : E) ^ (i + 1) * (q₁ i - q₂ i + R) := by
      rw [mul_sub, hnewton₁, hnewton₂, ← mul_sub, ← Finset.sum_sub_distrib]
      rw [← hsum]
      congr 1
      apply Finset.sum_congr rfl
      intro b _
      dsimp only [f]
      ring
    have hm := (lattice E J).add_mem (hmom i hi hip) hR
    have hscaled : (-1 : E) ^ (i + 1) *
        (q₁ i - q₂ i + R - (if i = p - 1 then ((p : E) - 1) * c else 0)) ∈
        lattice E J := by
      rw [mem_lattice]
      simpa only [mem_lattice, ord_mul, ord_pow, ord_neg, ord_one,
        nsmul_zero, zero_add, sub_add_eq_add_sub] using hm
    have hfinal : (i : E) * (e₁ i - e₂ i + (if i = p - 1 then c else 0)) ∈
        lattice E J := by
      convert hscaled using 1
      rw [mul_add, hn]
      by_cases hilast : i = p - 1
      · have hsucc : i + 1 = p := by omega
        have hcast : (i : E) = (p : E) - 1 := by
          rw [hilast, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
        simp only [if_pos hilast, hsucc, hodd.neg_one_pow, hcast]
        ring
      · simp only [if_neg hilast, mul_zero, add_zero, sub_zero]
    have hiord : ord E (i : E) = 0 :=
      ord_natCast_eq_zero_of_lt_residueCharacteristic E hi (by simpa [hchar] using hip)
    simpa only [mem_lattice, ord_mul, hiord, zero_add] using hfinal

private theorem integral_coefficients
    (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
    [PrimeCyclicExtension F E]
    {p t : ℕ} (hchar : residueCharacteristic F = p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (x : E) (hx : x ∈ lattice E 0) :
    (∀ j, 1 ≤ j → j < p → galoisPowerSum F E j x ∈ lattice F 0) ∧
    (∀ j, j < p → elementarySymmetric F E j x ∈ lattice F 0) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have htrace := traceIdealLowerBound_of_integralGenerator F E ht hres pi hpi hgen
  have hq (j : ℕ) : galoisPowerSum F E j x ∈ lattice F 0 := by
    have hxj : x ^ j ∈ lattice E 0 := by
      rw [mem_lattice, ord_pow]
      simpa using nsmul_le_nsmul_right ((mem_lattice E).1 hx) j
    have h := htrace 0 (x ^ j) ((mem_lattice E).1 hxj)
    apply (mem_lattice F).2
    apply (WithTop.coe_le_coe.mpr ?_).trans h
    positivity
  refine ⟨fun j _ _ => hq j, ?_⟩
  intro j hj
  by_cases hzero : j = 0
  · simp [hzero, elementarySymmetric_zero]
  have h := Total.twistedSymmetric_of_powerTrace F E x 0 0 (by omega)
    (by intro i _ _; simpa only [mul_zero, add_zero, mem_lattice, galoisPowerSum] using hq i)
    j (by omega) (by simpa [hchar] using hj)
  simpa only [mul_zero, add_zero, mem_lattice] using h

private theorem trace_base_mul_pow
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    (u : F) (x : E) (j : ℕ) :
    trace F E ((algebraMap F E u * x) ^ j) = u ^ j * trace F E (x ^ j) := by
  rw [mul_pow, ← map_pow, ← Algebra.smul_def, map_smul, smul_eq_mul]


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
local instance : PrimeCyclicExtension B₂ K :=
  PrimeCyclicExtension.ofCyclicPrimeExtension B₂ K
    (Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.2

include hres hchar

set_option maxHeartbeats 800000 in
/-- The first assertion of `O:N:moments`, with the actual coordinate and
norm witness. The degree-one estimate uses `O:A:thm:H14`; higher degrees
combine the two proved ingredients of `O:A:thm:h` with their exact weight. -/
private theorem power_moments
    (Delta : K) (a : B₂)
    (hroot : Delta ^ p - Delta = algebraMap B₂ K a)
    (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ D.t) (hgen : Algebra.adjoin B₂ ({Delta} : Set K) = ⊤)
    (u : Fˣ) (w : B₂ˣ) (hw : normUnits F B₂ w = u⁻¹)
    (m : ℤ) (hu : ord F (u : F) = (m : WithTop ℤ))
    (hm : (D.t : ℤ) < (p : ℤ) * m)
    (j : ℕ) (hj : 1 ≤ j) (hjp : j < p) :
    algebraMap F B₁ ((u : F) ^ j *
      (trace F B₁ (norm B₁ K Delta ^ j) - trace F B₂ (a ^ j))) -
      (if j = p - 1 then ((p : B₁) - 1) * algebraMap F B₁ ((u : F) ^ (p - 1)) *
        (1 - (-elementarySymmetric B₁ K (p - 1) Delta) ^ p) else 0) ∈
      lattice B₁ (1 + (p : ℤ) * ((D.t₂ : ℤ) + m)) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hp3 := D.odd_prime
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hdegreeF₁ : Module.finrank F B₁ = p := D.degree_B₁
  have hdegreeF₂ : Module.finrank F B₂ = p := D.degree_B₂
  obtain ⟨hdegree₁, _, _, hramF₁, hram₁K⟩ :=
    realization_tower_data hp hG hres B₁ D.degree_B₁
  obtain ⟨_, hresF₂, _, _, _⟩ :=
    realization_tower_data hp hG hres B₂ D.degree_B₂
  obtain ⟨_, _, hei, _⟩ := Models.realization_twistedEstimates_of_coordinate
    hp hG hres hchar D Delta a hroot hDelta hprime hgen
  by_cases hjone : j = 1
  · subst j
    have htrace := Total.traceNorm hp hG hres hchar D Delta a hroot hgen hei
    have hmul := mul_mem_lattice F ((mem_lattice F).2 hu.ge) htrace
    have h := nsmul_le_nsmul_right ((mem_lattice F).1 hmul) p
    simp only [pow_one, if_neg (by omega : 1 ≠ p - 1), sub_zero]
    rw [mem_lattice, ord_algebraMap, hramF₁]
    apply (WithTop.coe_le_coe.mpr ?_).trans h
    simp only [nsmul_eq_mul]
    nlinarith
  have hj2 : 2 ≤ j := by omega
  let x : B₂ := ((w⁻¹ : B₂ˣ) : B₂) ^ j
  let v : ℤ := (j : ℤ) * m
  let R : ℤ := (p : ℤ) * v - ((j : ℤ) - 1) * D.t
  let X : B₁ := algebraMap F B₁ ((u : F) ^ j)
  have hnormInv : norm F B₂ ((w⁻¹ : B₂ˣ) : B₂) = (u : F) := by
    have h := congrArg Units.val (congrArg Inv.inv hw)
    simpa [normUnits, LanglandsFirstMainLemma.norm, Algebra.norm_inv] using h
  have hx : x ∈ lattice B₂ v := by
    have hwi : ord B₂ ((w⁻¹ : B₂ˣ) : B₂) = (m : WithTop ℤ) := by
      have h := congrArg (ord F) hnormInv
      simpa only [ord_norm, hresF₂, one_nsmul, hu] using h
    simp only [x, v, mem_lattice, ord_pow, hwi, ← WithTop.coe_nsmul, nsmul_eq_mul,
      le_refl]
  have hnormx : norm F B₂ x = (u : F) ^ j := by
    dsimp only [x]
    rw [map_pow, hnormInv]
  have hR : 1 ≤ R := by
    have hjZ : (2 : ℤ) ≤ j := by exact_mod_cast hj2
    have htZ : (0 : ℤ) < D.t := by exact_mod_cast D.t_pos
    dsimp only [R, v]
    nlinarith
  have hdepth : 1 + (p : ℤ) * ((D.t₂ : ℤ) + m) ≤ (p : ℤ) * D.t₂ + R := by
    have hjZ : (2 : ℤ) ≤ j := by exact_mod_cast hj2
    dsimp only [R, v]
    nlinarith
  have hX : X ∈ lattice B₁ (R + ((j : ℤ) - 1) * D.t) := by
    dsimp only [X]
    rw [mem_lattice, ord_algebraMap, hramF₁, ord_pow, hu,
      ← WithTop.coe_nsmul, ← WithTop.coe_nsmul, WithTop.coe_le_coe]
    dsimp only [R, v]
    simp only [nsmul_eq_mul]
    ring_nf
    exact le_rfl
  have hchar₁ : residueCharacteristic B₁ = p :=
    (residueCharacteristic_extension_eq F B₁).trans hchar
  have ht₂ : (D.t₂ : ℤ) = (D.t : ℤ) + D.delta := by exact_mod_cast D.t₂_eq
  have hfiltered := Total.filteredCoefficients B₁ K (by omega) hchar₁ hdegree₁ hram₁K
    Delta D.t D.delta R (by positivity) (by positivity) hDelta
    (by intro i hi hip; simpa only [mem_lattice, ← ht₂] using hei i hi hip)
    (by simpa only [← ht₂] using realization_prime_mem hp hG hres D B₁ D.degree_B₁)
    hj hjp.le X hX
  have htranslate := Models.realization_translatedNorm_of_coordinate hp hG hres hchar D
    Delta a hroot hDelta hprime hgen x v j hx hj hjp.le hR
  rw [hnormx] at htranslate
  have hsum :
      (∑ z : ZMod p, norm B₁ K (Delta + algebraMap F K
        (primeTeichmuller F p hchar z : F)) ^ j) =
      norm B₁ K Delta ^ j + ∑ z : (ZMod p)ˣ, norm B₁ K
        (Delta + algebraMap B₁ K (primeTeichmuller B₁ p hchar₁ z)) ^ j := by
    have h := weighted_teichmuller_sum F B₁ hchar hchar₁
      (fun c => norm B₁ K (Delta + algebraMap B₁ K c) ^ j)
    simp only [← IsScalarTower.algebraMap_apply F B₁ K] at h
    rw [h, weighted_sum_zero_units]
    simp only [map_zero, Subring.coe_zero, add_zero]
  have hinf : B₁ ⊓ B₂ = ⊥ := by
    have hdvd := IntermediateField.finrank_dvd_of_le_right
      (show B₁ ⊓ B₂ ≤ B₁ from inf_le_left)
    rw [hdegreeF₁] at hdvd
    rcases (Nat.dvd_prime hp).1 hdvd with hone | heq
    · exact IntermediateField.finrank_eq_one_iff.mp hone
    · exact (D.B₁_ne_B₂ ((IntermediateField.eq_of_le_of_finrank_eq inf_le_left
        (heq.trans D.degree_B₁.symm)).symm.trans
          (IntermediateField.eq_of_le_of_finrank_eq inf_le_right
            (heq.trans D.degree_B₂.symm)))).elim
  have hdis := IntermediateField.LinearDisjoint.of_inf_eq_bot hinf
  have hsup : B₁ ⊔ B₂ = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [hdis.finrank_sup, hdegreeF₁, hdegreeF₂]
    have htotal : Module.finrank F K = p * p := by
      rw [← Module.finrank_mul_finrank F B₁ K, hdegreeF₁, hdegree₁]
    simpa using htotal.symm
  have htrace : trace B₁ K ((Delta ^ p - Delta) ^ j) =
      algebraMap F B₁ (trace F B₂ (a ^ j)) := by
    rw [hroot, ← map_pow]
    exact hdis.trace_algebraMap hsup _
  rw [htrace, ← ht₂] at hfiltered
  rw [hsum] at htranslate
  have hsign : 1 + elementarySymmetric B₁ K (p - 1) Delta ^ p =
      1 - (-elementarySymmetric B₁ K (p - 1) Delta) ^ p := by
    rw [hodd.neg_pow]; ring
  rw [hsign] at hfiltered
  apply lattice_antitone B₁ hdepth
  have h := (lattice B₁ ((p : ℤ) * D.t₂ + R)).add_mem htranslate hfiltered
  convert h using 1
  dsimp only [X]
  simp only [map_mul, map_sub]
  split_ifs with heq
  · rw [heq]; ring
  · ring

set_option maxHeartbeats 800000 in
/-- **Paper Lemma 9.15 (`O:N:moments`).**

For the prescribed exact Artin--Schreier coordinate in the genuine odd
Galois diamond, both weighted moment identities hold modulo `𝔭₁^(1+pr)`.
Here `a` and `b₀` are the actual upper norms, `s` is the actual upper
symmetric coefficient, and the exact lower norm witness is retained.
The coordinate assumptions are those supplied by the accepted coordinate
and realization constructors; its generation is proved from its order.

The character setup enters this algebraic step through the exact ratio
`u=alpha/gamma`, its integer order `m`, and the norm witness `n₂(w)=u⁻¹`.
The result holds for every such ratio and witness, in either characteristic.
No moment congruence, stationary model, or cancellation is assumed. -/
theorem moments
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
    let r := (D.t₂ : ℤ) + m
    (∀ j : ℕ, 1 ≤ j → j < p →
      algebraMap F B₁ ((u : F) ^ j * (trace F B₁ (b₀ ^ j) - trace F B₂ (a ^ j))) -
        (if j = p - 1 then ((p : B₁) - 1) * algebraMap F B₁ ((u : F) ^ (p - 1)) *
          (1 - s ^ p) else 0) ∈ lattice B₁ (1 + (p : ℤ) * r)) ∧
    (∀ i : ℕ, 1 ≤ i → i < p →
      algebraMap F B₁ ((u : F) ^ i *
        (elementarySymmetric F B₁ i b₀ - elementarySymmetric F B₂ i a)) +
        (if i = p - 1 then algebraMap F B₁ ((u : F) ^ (p - 1)) * (1 - s ^ p) else 0) ∈
        lattice B₁ (1 + (p : ℤ) * r)) := by
  classical
  dsimp only
  let a := norm B₂ K Delta
  let b := norm B₁ K Delta
  let x₁ := algebraMap F B₁ (u : F) * b
  let x₂ := algebraMap F B₂ (u : F) * a
  have hp3 := D.odd_prime
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨_, hresF₁, hres₁K, hramF₁, _⟩ :=
    realization_tower_data hp hG hres B₁ D.degree_B₁
  obtain ⟨hdegree₂, hresF₂, hres₂K, hramF₂, hram₂K⟩ :=
    realization_tower_data hp hG hres B₂ D.degree_B₂
  obtain ⟨_, hgen⟩ := exact_coordinate_orders_and_generation B₂ K hp D.t_pos
    hdegree₂ hram₂K Delta a hDelta hprime hroot
  have hpow := power_moments hp hG hres hchar D Delta a hroot hDelta hprime hgen
    u w hw m hu hm
  refine ⟨hpow, ?_⟩
  have hx₁ : x₁ ∈ lattice B₁ 0 := by
    rw [mem_lattice, show x₁ = algebraMap F B₁ (u : F) * norm B₁ K Delta from rfl,
      ord_mul, ord_algebraMap, hramF₁, hu, ord_norm, hres₁K, one_nsmul, hDelta,
      ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe]
    simp only [nsmul_eq_mul]
    omega
  have hx₂ : x₂ ∈ lattice B₂ 0 := by
    rw [mem_lattice, show x₂ = algebraMap F B₂ (u : F) * norm B₂ K Delta from rfl,
      ord_mul, ord_algebraMap, hramF₂, hu, ord_norm, hres₂K, one_nsmul, hDelta,
      ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe]
    simp only [nsmul_eq_mul]
    omega
  have ht₁ : PrimeCyclicExtension.IsLowerBreak F B₁ D.t := by
    simpa only [Total.OddTotalBreakData.B₁, Ramification.IntermediateBreakPair] using D.B₁_breaks.1
  have ht₂ : PrimeCyclicExtension.IsLowerBreak F B₂ D.t₂ := by
    simpa only [Total.OddTotalBreakData.B₂, Ramification.IntermediateBreakPair] using D.B₂_breaks.1
  have hc₁ := integral_coefficients F B₁ hchar ht₁ hresF₁ x₁ hx₁
  have hc₂ := integral_coefficients F B₂ hchar ht₂ hresF₂ x₂ hx₂
  have hmap {z : F} (hz : z ∈ lattice F 0) : algebraMap F B₁ z ∈ lattice B₁ 0 := by
    rw [mem_lattice, ord_algebraMap]
    simpa using nsmul_le_nsmul_right ((mem_lattice F).1 hz) (ramificationIndex F B₁)
  let e₁ := fun i => algebraMap F B₁ (elementarySymmetric F B₁ i x₁)
  let e₂ := fun i => algebraMap F B₁ (elementarySymmetric F B₂ i x₂)
  let q₁ := fun i => algebraMap F B₁ (galoisPowerSum F B₁ i x₁)
  let q₂ := fun i => algebraMap F B₁ (galoisPowerSum F B₂ i x₂)
  have hnew₁ (i : ℕ) : (i : B₁) * e₁ i = (-1 : B₁) ^ (i + 1) *
      ∑ c ∈ Finset.HasAntidiagonal.antidiagonal i with c.1 < i,
        (-1 : B₁) ^ c.1 * e₁ c.1 * q₁ c.2 := by
    simpa only [e₁, q₁, map_mul, map_natCast, map_pow, map_neg, map_one, map_sum] using
      congrArg (algebraMap F B₁) (elementarySymmetric_newton_identity F B₁ x₁ i)
  have hnew₂ (i : ℕ) : (i : B₁) * e₂ i = (-1 : B₁) ^ (i + 1) *
      ∑ c ∈ Finset.HasAntidiagonal.antidiagonal i with c.1 < i,
        (-1 : B₁) ^ c.1 * e₂ c.1 * q₂ c.2 := by
    simpa only [e₂, q₂, map_mul, map_natCast, map_pow, map_neg, map_one, map_sum] using
      congrArg (algebraMap F B₁) (elementarySymmetric_newton_identity F B₂ x₂ i)
  let c := algebraMap F B₁ ((u : F) ^ (p - 1)) *
    (1 - (-elementarySymmetric B₁ K (p - 1) Delta) ^ p)
  have hmom (i : ℕ) (hi : 1 ≤ i) (hip : i < p) :
      q₁ i - q₂ i - (if i = p - 1 then ((p : B₁) - 1) * c else 0) ∈
        lattice B₁ (1 + (p : ℤ) * ((D.t₂ : ℤ) + m)) := by
    simpa only [q₁, q₂, x₁, x₂, galoisPowerSum, trace_base_mul_pow,
      map_mul, map_sub, mul_sub, mul_assoc, c, a, b] using hpow i hi hip
  intro i hi hip
  have h := newton_comparison B₁ ((residueCharacteristic_extension_eq F B₁).trans hchar)
    hodd e₁ e₂ q₁ q₂ (by simp [e₁, elementarySymmetric_zero])
    (by simp [e₂, elementarySymmetric_zero]) hnew₁ hnew₂
    (fun j hj => hmap (hc₂.2 j hj)) (fun j hj hjp => hmap (hc₁.1 j hj hjp))
    c (1 + (p : ℤ) * ((D.t₂ : ℤ) + m)) hmom i hi hip
  simpa only [e₁, e₂, x₁, x₂, elementarySymmetric_algebraMap_mul,
    map_mul, map_sub, mul_sub, c, a, b] using h

end Diamond

end

end LanglandsSecondMainLemma.Odd.Q2
