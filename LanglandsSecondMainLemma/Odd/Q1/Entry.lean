import LanglandsSecondMainLemma.Odd.Parameters.FourFactors

/-!
# Odd / Q1 / Entry

Paper Lemma 9.12 (`O:Q:entry`), corrected source lines 3857--3913, with
the primitive pair from `O:M:realize` and the actual factors of `O:P:four`.

The exact Artin--Schreier polynomial gives the second norm of `1 + Delta/w`.
The cyclic power--norm estimate puts its difference from the normalized
second factor in the whole conductor ideal. Compatibility and the proved
common base-field restriction then identify the actual first factor.

The theorem constructs both relative arguments as field units, proves their
orders are zero, and proves the exact crossed-norm equality `n = u*b`.
All depths are integers, and neither field characteristic nor unitarity of
the continuous quasi-characters is restricted.
-/

namespace LanglandsSecondMainLemma.Odd.Q1
noncomputable section
open LanglandsFirstMainLemma
open Polynomial
set_option backward.isDefEq.respectTransparency false

/-- The exact norm polynomial, valid in both field characteristics. -/
theorem norm_one_add_artinSchreier
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    [Module.Free E L] [Module.Finite E L]
    (pb : PowerBasis E L) {p : ℕ} (hp : p.Prime) (hodd : 2 < p)
    (hdim : pb.dim = p) (a : E)
    (hroot : pb.gen ^ p - pb.gen = algebraMap E L a) (w : Eˣ) :
    norm E L (1 + pb.gen / algebraMap E L (w : E)) =
      1 - (w : E) / (w : E) ^ p + a / (w : E) ^ p := by
  have hdegree : Module.finrank E L = p := pb.finrank.trans hdim
  have hmin := Total.artinSchreier_minpoly pb hodd hdim a hroot
  have hchar : (Algebra.lmul E L pb.gen).charpoly = minpoly E pb.gen :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic pb.isIntegral_gen)
      (LinearMap.charpoly_monic _) (minpoly.dvd E pb.gen
        (Algebra.aeval_self_charpoly_lmul pb.gen))
      (by rw [LinearMap.charpoly_natDegree, pb.natDegree_minpoly, pb.finrank])
  have hev := LinearMap.eval_charpoly (Algebra.lmul E L pb.gen) (-(w : E))
  have hdet :
      (algebraMap E (Module.End E L) (-(w : E)) - Algebra.lmul E L pb.gen).det =
        norm E L (algebraMap E L (-(w : E)) - pb.gen) := by
    change _ = (Algebra.lmul E L (algebraMap E L (-(w : E)) - pb.gen)).det
    congr 1
    rw [map_sub, AlgHom.commutes]
  rw [hchar, hmin, hdet] at hev
  simp only [eval_sub, eval_pow, eval_X, eval_C] at hev
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  have hn : norm E L (algebraMap E L (w : E) + pb.gen) =
      (w : E) ^ p - (w : E) + a := by
    have hneg : algebraMap E L (-(w : E)) - pb.gen =
        (-1 : L) * (algebraMap E L (w : E) + pb.gen) := by simp; ring
    rw [hneg, map_mul, show (-1 : L) = algebraMap E L (-1) by simp,
      LanglandsFirstMainLemma.norm_algebraMap, hdegree, ho.neg_one_pow, neg_one_mul, ho.neg_pow] at hev
    linear_combination hev
  have hw0 : algebraMap E L (w : E) ≠ 0 := by
    simpa only [map_zero] using (algebraMap E L).injective.ne (Units.ne_zero w)
  have hdiv (x : L) : norm E L (x / algebraMap E L (w : E)) =
      norm E L x / (w : E) ^ p := by
    apply (eq_div_iff (pow_ne_zero _ (Units.ne_zero w))).2
    rw [← hdegree, ← LanglandsFirstMainLemma.norm_algebraMap, ← map_mul,
      div_mul_cancel₀ _ hw0]
  rw [show 1 + pb.gen / algebraMap E L (w : E) =
      (algebraMap E L (w : E) + pb.gen) / algebraMap E L (w : E) by
        field_simp, hdiv, hn]
  field_simp

/-- The conductor comparison includes the cubic boundary and integer depths. -/
theorem entry_depth_bound {p t t₂ : ℕ} {m : ℤ}
    (hp : 2 < p) (ht : 0 < t) (htt₂ : t ≤ t₂)
    (hm : (t : ℤ) < p * m) :
    (1 + t + t₂ : ℤ) ≤ ((p : ℤ) - 1) * t₂ + p * m - max (t : ℤ) m := by
  have hp' : (3 : ℤ) ≤ p := by exact_mod_cast hp
  have ht' : (1 : ℤ) ≤ t := by exact_mod_cast ht
  have htt₂' : (t : ℤ) ≤ t₂ := by exact_mod_cast htt₂
  have hmpos : 0 < m := by nlinarith
  by_cases hmt : m ≤ t
  · rw [max_eq_left hmt]
    have h := mul_nonneg (show 0 ≤ (p : ℤ) - 3 by omega)
      (show 0 ≤ (t : ℤ) by omega)
    have h' := mul_nonneg (show 0 ≤ (p : ℤ) - 2 by omega)
      (sub_nonneg.mpr htt₂')
    nlinarith
  · rw [max_eq_right (by omega)]
    have h := mul_nonneg (show 0 ≤ (p : ℤ) - 3 by omega)
      (show 0 ≤ (t₂ : ℤ) by omega)
    have h' := mul_nonneg (show 0 ≤ (p : ℤ) - 2 by omega)
      (show 0 ≤ m - t by omega)
    nlinarith


section Cyclic
variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E]
  [Module.Free F E] [Module.Finite F E] [PrimeCyclicExtension F E]

/-- The relative difference of the two actual denominator arguments lies
in the entire conductor ideal; negative orders are kept as integers. -/
theorem entry_norm_difference {p t t₂ : ℕ} {m : ℤ}
    (hdegree : Module.finrank F E = p) (hp : 2 < p)
    (ht : 0 < t) (htt₂ : t ≤ t₂)
    (hbreak : PrimeCyclicExtension.IsLowerBreak F E t₂)
    (hres : residueDegree F E = 1)
    (u : Fˣ) (hu : ord F (u : F) = (m : WithTop ℤ))
    (hm : (t : ℤ) < p * m) (w : Eˣ)
    (hw : normUnits F E w = u⁻¹) (a : E)
    (ha : ord E a = ((-(t : ℤ) : ℤ) : WithTop ℤ)) :
    (1 - algebraMap F E (u : F) * (w : E) + algebraMap F E (u : F) * a) -
      (1 - (w : E) / (w : E) ^ p + a / (w : E) ^ p) ∈
        lattice E (1 + t + t₂) := by
  have hram : ramificationIndex F E = p := by
    simpa only [hdegree, hres, mul_one] using
      (finrank_eq_ramificationIndex_mul_residueDegree F E).symm
  have hword : ord E (w : E) = ((-m : ℤ) : WithTop ℤ) := by
    have h := congrArg (fun x : Fˣ ↦ ord F (x : F)) hw
    simpa only [coe_normUnits, ord_norm, hres, one_nsmul,
      Units.val_inv_eq_inv_val, ord_inv, hu, ← WithTop.LinearOrderedAddCommGroup.coe_neg] using h
  have huord : ord E (algebraMap F E (u : F)) =
      (((p : ℤ) * m : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hram, hu, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have hpower := Total.powerNorm F E p t₂ hdegree hp hbreak
    (ht.trans_le htt₂) hres (w : E)
  rw [hword, ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul] at hpower
  have hpowmem : (w : E) ^ p - algebraMap F E (norm F E (w : E)) ∈
      lattice E (-((p : ℤ) * m) + ((p : ℤ) - 1) * t₂) := by
    simpa only [mem_lattice, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ p),
      Nat.cast_one, mul_neg] using hpower
  have herror : algebraMap F E (u : F) * (w : E) ^ p - 1 ∈
      lattice E (((p : ℤ) - 1) * t₂) := by
    have hmul := mul_mem_lattice E ((mem_lattice E).2 huord.ge) hpowmem
    have heq : algebraMap F E (u : F) *
        ((w : E) ^ p - algebraMap F E (norm F E (w : E))) =
          algebraMap F E (u : F) * (w : E) ^ p - 1 := by
      have hn := congrArg (fun x : Fˣ ↦ (x : F)) hw
      simp only [coe_normUnits, Units.val_inv_eq_inv_val] at hn
      rw [mul_sub, hn, ← map_mul, mul_inv_cancel₀ (Units.ne_zero u), map_one]
    simpa only [heq, add_neg_cancel_left] using hmul
  have haw : a - (w : E) ∈ lattice E (-max (t : ℤ) m) := by
    apply sub_mem_lattice E
    · exact lattice_antitone E (neg_le_neg (le_max_left _ _))
        ((mem_lattice E).2 ha.ge)
    · exact lattice_antitone E (neg_le_neg (le_max_right _ _))
        ((mem_lattice E).2 hword.ge)
  have hwPow : ord E ((w : E) ^ p) = ((-((p : ℤ) * m) : ℤ) : WithTop ℤ) := by
    rw [ord_pow, hword, ← WithTop.coe_nsmul, nsmul_eq_mul, mul_neg]
  have hquot : (a - (w : E)) / (w : E) ^ p ∈
      lattice E ((p : ℤ) * m - max (t : ℤ) m) := by
    rw [div_mem_lattice_iff E _ _ _ _ hwPow]
    convert haw using 1
    congr 1
    ring
  have hprod := mul_mem_lattice E herror hquot
  have heq :
      (1 - algebraMap F E (u : F) * (w : E) + algebraMap F E (u : F) * a) -
        (1 - (w : E) / (w : E) ^ p + a / (w : E) ^ p) =
      (algebraMap F E (u : F) * (w : E) ^ p - 1) *
        ((a - (w : E)) / (w : E) ^ p) := by
    field_simp
    ring
  rw [heq]
  apply lattice_antitone E _ hprod
  have hb := entry_depth_bound hp ht htt₂ hm
  linarith
end Cyclic

/-- Equality of genuine quasi-character values from the relative change
in the conductor subgroup, with the divisor's order checked explicitly. -/
theorem entry_character_eq
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (phi : ContinuousQuasiChar E) {k : ℕ} (hk : 0 < k)
    (hphi : IsMultiplicativeConductor E phi k)
    (C P : Eˣ) (hP : ord E (P : E) = 0)
    (hCP : (C : E) - (P : E) ∈ lattice E (k : ℤ)) : phi C = phi P := by
  have hrel : C / P ∈ unitFiltration E k := by
    rw [← Nat.sub_add_cancel hk, mem_unitFiltration_succ_iff_sub_mem_lattice]
    rw [Nat.sub_add_cancel hk]
    simp only [Units.val_div_eq_div_val]
    change (C : E) / (P : E) - 1 ∈ lattice E (k : ℤ)
    rw [show (C : E) / (P : E) - 1 = ((C : E) - (P : E)) / (P : E) by
      field_simp, div_mem_lattice_iff E _ _ 0 _ (by simpa using hP), zero_add]
    exact hCP
  exact div_eq_one.mp ((map_div phi C P).symm.trans (hphi.trivial _ hrel))


open private realization_tower_data from LanglandsSecondMainLemma.Odd.Models.Realization
open private exact_coordinate_orders_and_generation from
  LanglandsSecondMainLemma.Odd.Total.ASCoordinate
open private inf_eq_bot_of_prime_degree from LanglandsSecondMainLemma.Characters.Conjugacy
open private twistNormRanges_ne from LanglandsSecondMainLemma.Odd.Models.TwistFormula

section Diamond
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]
  {p : ℕ} (hp : p.Prime)
  (hG : Nonempty
    (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
  (hres : residueDegree F K = 1)
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

include hres

/-- Common base-field restriction of the actual primitive compatible pair.
The complete correction products are removed using their proved odd-degree values. -/
private theorem entry_restriction
    (chi : ContinuousQuasiChar B₁) (phi : ContinuousQuasiChar B₂)
    (hcompat : chi.compNorm (S := K) = phi.compNorm (S := K))
    (hprimitive : ¬ ∃ theta : ContinuousQuasiChar F,
      theta.compNorm (S := K) = phi.compNorm (S := K)) :
    Characters.restrictQuasiChar F B₁ chi = Characters.restrictQuasiChar F B₂ phi := by
  obtain ⟨_, hr, _, _, _⟩ := realization_tower_data hp hG hres B₂ D.degree_B₂
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F B₂ hr
  have hchar : residueCharacteristic F = p :=
    (residueCharacteristic_eq_degree_of_positive_isLowerBreak F B₂
      D.B₂_breaks.1 (D.t_pos.trans_le D.t_le_t₂) pi hpi hgen).trans D.degree_B₂
  obtain ⟨_, _, heq, hodd, _⟩ := Characters.conjugacy hp hG B₁ B₂
    D.degree_B₁ D.degree_B₂ (twistNormRanges_ne hp hG hres hchar D)
    chi phi (phi.compNorm (S := K)) hcompat rfl hprimitive
  obtain ⟨h₁, h₂⟩ := hodd (hp.odd_of_ne_two (by have := D.odd_prime; omega))
  rw [h₁, h₂] at heq
  apply ContinuousMonoidHom.ext
  intro x
  have hx := DFunLike.congr_fun heq x
  change chi (Units.map (algebraMap F B₁) x) * (1 : ℂˣ) =
    phi (Units.map (algebraMap F B₂) x) * (1 : ℂˣ) at hx
  change chi (Units.map (algebraMap F B₁) x) =
    phi (Units.map (algebraMap F B₂) x)
  simpa only [mul_one] using hx

set_option maxHeartbeats 800000 in
/-- **Paper 9.12 (`O:Q:entry`)**. All relative changes are constructed as
actual field units. The pair is the primitive compatible minimal pair from
the odd totally ramified setup; only its second conductor is needed here.
The two factor arguments are precisely those supplied by `fourFactors`.
The Artin--Schreier norm formula, conductor comparison, common restriction,
and exact equation `n = u*b` are proved, not imposed as hypotheses. -/
theorem entry
    (hprime : ¬ p ∣ D.t) (Delta : K) (a : B₂)
    (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hroot : Delta ^ p - Delta = algebraMap B₂ K a)
    (chi : ContinuousQuasiChar B₁) (phi : ContinuousQuasiChar B₂)
    (hphi : IsMultiplicativeConductor B₂ phi (Models.secondModelConductor D))
    (hcompat : chi.compNorm (S := K) = phi.compNorm (S := K))
    (hprimitive : ¬ ∃ theta : ContinuousQuasiChar F,
      theta.compNorm (S := K) = phi.compNorm (S := K))
    (alpha gamma : Fˣ) {m : ℤ}
    (hu : ord F ((alpha / gamma : Fˣ) : F) = (m : WithTop ℤ))
    (hm : (D.t : ℤ) < p * m)
    (w : B₂ˣ) (hw : normUnits F B₂ w = gamma / alpha)
    (A₁ : B₁ˣ) (C₂ : B₂ˣ)
    (hA₁ : (A₁ : B₁) = algebraMap F B₁ (gamma : F) +
      algebraMap F B₁ (alpha : F) * norm B₁ K Delta)
    (hC₂ : (C₂ : B₂) = algebraMap F B₂ (gamma : F) -
      algebraMap F B₂ (alpha : F) * (w : B₂) +
      algebraMap F B₂ (alpha : F) * norm B₂ K Delta) :
    let u : Fˣ := alpha / gamma
    let z : K := Delta / algebraMap B₂ K (w : B₂)
    let n : B₁ := norm B₁ K z
    n = algebraMap F B₁ (u : F) * norm B₁ K Delta ∧
    ∃ Z : Kˣ, ∃ N : B₁ˣ,
      (Z : K) = 1 + z ∧ (N : B₁) = 1 + n ∧
      ord K (Z : K) = 0 ∧ ord B₁ (N : B₁) = 0 ∧
      (chi A₁ / phi C₂)⁻¹ = chi (normUnits B₁ K Z / N) := by
  dsimp only
  let u : Fˣ := alpha / gamma
  have hwu : normUnits F B₂ w = u⁻¹ := by simpa only [u, inv_div] using hw
  obtain ⟨hd₁, hrF₁, hrK₁, he₁, heK₁⟩ :=
    realization_tower_data hp hG hres B₁ D.degree_B₁
  obtain ⟨hd₂, hrF₂, hrK₂, he₂, heK₂⟩ :=
    realization_tower_data hp hG hres B₂ D.degree_B₂
  obtain ⟨ha, hgen⟩ := exact_coordinate_orders_and_generation B₂ K hp D.t_pos
    hd₂ heK₂ Delta a hDelta hprime hroot
  let pb : PowerBasis B₂ K := PowerBasis.ofAdjoinEqTop
    (Algebra.IsIntegral.isIntegral Delta) hgen
  have hpbg : pb.gen = Delta := PowerBasis.ofAdjoinEqTop_gen _ _
  have hpbd : pb.dim = p := pb.finrank.symm.trans hd₂
  have hnormDelta : norm B₂ K Delta = a := by
    simpa only [hpbg] using Total.artinSchreier_norm pb hp D.odd_prime hpbd a
      (by simpa only [hpbg] using hroot)
  change ord F (u : F) = (m : WithTop ℤ) at hu
  have hword : ord B₂ (w : B₂) = ((-m : ℤ) : WithTop ℤ) := by
    have h := congrArg (fun x : Fˣ ↦ ord F (x : F)) hwu
    simpa only [coe_normUnits, ord_norm, hrF₂, one_nsmul,
      Units.val_inv_eq_inv_val, ord_inv, hu, ← WithTop.LinearOrderedAddCommGroup.coe_neg] using h
  let z : K := Delta / algebraMap B₂ K (w : B₂)
  have hzord : ord K z = (((p : ℤ) * m - D.t : ℤ) : WithTop ℤ) := by
    rw [ord_div, hDelta, ord_algebraMap, heK₂, hword, ← WithTop.coe_nsmul,
      ← WithTop.LinearOrderedAddCommGroup.coe_sub, nsmul_eq_mul]
    congr 1
    ring
  have hzpos : (0 : WithTop ℤ) < ord K z := by
    rw [hzord]
    exact WithTop.coe_lt_coe.mpr (by omega)
  have hZord : ord K (1 + z) = 0 := by
    rw [(ord K).map_add_eq_of_lt_left (by simpa only [ord_one] using hzpos), ord_one]
  let Z : Kˣ := Units.mk0 (1 + z) (by
    intro h; have := hZord; rw [h, ord_zero] at this; exact WithTop.top_ne_coe this)
  have hZ : (Z : K) = 1 + z := rfl
  have hinf := inf_eq_bot_of_prime_degree hp B₁ B₂ D.degree_B₁ D.degree_B₂ D.B₁_ne_B₂
  have hdisjoint : D.B₁.LinearDisjoint B₂ := IntermediateField.LinearDisjoint.of_inf_eq_bot hinf
  have hsup : B₁ ⊔ B₂ = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [hdisjoint.finrank_sup, IntermediateField.finrank_top']
    change Module.finrank F (IntermediateField.fixedField D.H₁) *
      Module.finrank F (IntermediateField.fixedField D.H₂) = _
    rw [D.degree_B₁, D.degree_B₂]
    exact (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.1.symm
  have hcross : normUnits B₁ K (Units.map (algebraMap B₂ K) w) =
      Units.map (algebraMap F B₁) u⁻¹ := by
    apply Units.ext
    change norm B₁ K (algebraMap B₂ K (w : B₂)) = _
    rw [hdisjoint.norm_algebraMap hsup]
    exact congrArg (algebraMap F B₁) (congrArg (fun x : Fˣ ↦ (x : F)) hwu)
  have hn : norm B₁ K z = algebraMap F B₁ (u : F) * norm B₁ K Delta := by
    have hDelta0 : Delta ≠ 0 := by
      intro h; rw [h, ord_zero] at hDelta; exact WithTop.top_ne_coe hDelta
    let du : Kˣ := Units.mk0 Delta hDelta0
    have h := congrArg (fun x : B₁ˣ ↦ (x : B₁))
      (map_div (normUnits B₁ K) du (Units.map (algebraMap B₂ K) w))
    simp only [Units.val_div_eq_div_val, Units.coe_map, hcross, map_inv] at h
    change norm B₁ K z = _ at h
    simpa only [du, Units.val_mk0, Units.coe_map, Units.val_inv_eq_inv_val,
      MonoidHom.coe_coe, inv_inv, div_eq_mul_inv, mul_comm] using h
  have hnord : ord B₁ (norm B₁ K z) =
      (((p : ℤ) * m - D.t : ℤ) : WithTop ℤ) := by
    rw [ord_norm, hrK₁, one_nsmul, hzord]
  have hNord : ord B₁ (1 + norm B₁ K z) = 0 := by
    rw [(ord B₁).map_add_eq_of_lt_left (by
      rw [ord_one, hnord]; exact WithTop.coe_lt_coe.mpr (by omega)), ord_one]
  let N : B₁ˣ := Units.mk0 (1 + norm B₁ K z) (by
    intro h; have := hNord; rw [h, ord_zero] at this; exact WithTop.top_ne_coe this)
  have hN : (N : B₁) = 1 + norm B₁ K z := rfl
  have hPord : ord B₂ ((normUnits B₂ K Z : B₂ˣ) : B₂) = 0 := by
    rw [coe_normUnits, ord_norm, hrK₂, one_nsmul, hZ, hZord]
  have hP : ((normUnits B₂ K Z : B₂ˣ) : B₂) =
      1 - (w : B₂) / (w : B₂) ^ p + a / (w : B₂) ^ p := by
    simpa only [coe_normUnits, hZ, z, hpbg] using
      norm_one_add_artinSchreier B₂ K pb hp D.odd_prime hpbd a
        (by simpa only [hpbg] using hroot) w
  let R : B₂ˣ := C₂ / Units.map (algebraMap F B₂) gamma
  have hR : (R : B₂) =
      1 - algebraMap F B₂ (u : F) * (w : B₂) + algebraMap F B₂ (u : F) * a := by
    simp only [R, Units.val_div_eq_div_val, Units.coe_map, hC₂, hnormDelta,
      u, Units.val_div_eq_div_val, MonoidHom.coe_coe, map_div₀]
    field_simp
  have heq : phi R = phi (normUnits B₂ K Z) := by
    apply entry_character_eq B₂ phi (by simp [Models.secondModelConductor]) hphi
      R (normUnits B₂ K Z) hPord
    rw [hR, hP]
    exact entry_norm_difference F B₂ D.degree_B₂ D.odd_prime D.t_pos D.t_le_t₂
      D.B₂_breaks.1 hrF₂ u hu hm w hwu a ha
  have hcompatZ : chi (normUnits B₁ K Z) = phi (normUnits B₂ K Z) :=
    DFunLike.congr_fun hcompat Z
  have hgamma : chi (Units.map (algebraMap F B₁) gamma) =
      phi (Units.map (algebraMap F B₂) gamma) :=
    DFunLike.congr_fun (entry_restriction hp hG hres D chi phi hcompat hprimitive) gamma
  have hAfactor : A₁ = Units.map (algebraMap F B₁) gamma * N := by
    apply Units.ext
    simp only [Units.val_mul, Units.coe_map, hN, hn, hA₁, u,
      Units.val_div_eq_div_val, MonoidHom.coe_coe, map_div₀]
    field_simp
  refine ⟨hn, Z, N, hZ, hN, hZord, hNord, ?_⟩
  rw [hAfactor, map_mul, hgamma, _root_.map_div]
  have hCfactor : C₂ = R * Units.map (algebraMap F B₂) gamma := by simp [R]
  rw [hCfactor, map_mul, heq, ← hcompatZ]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

end Diamond
end
end LanglandsSecondMainLemma.Odd.Q1
