import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Odd.Transition.Phase
import LanglandsSecondMainLemma.Odd.R1.Weighted
import LanglandsSecondMainLemma.Odd.R2.Congruence

/-!
# Odd transition cancellation

Paper `O:T:cancel` and `O:T:actual-local-factors`.
The actual coordinate, weights, denominators and character charts are retained.
-/

namespace LanglandsSecondMainLemma.Odd.Transition

noncomputable section

open LanglandsFirstMainLemma

set_option backward.isDefEq.respectTransparency false

section Diamond

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]
  {p : ℕ} {hp : p.Prime}
  {hG : Nonempty
    (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))}
  (R : Total.OddTotalBreakData (F := F) (K := K) hp hG)

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

local notation "B₁" => R.B₁
local notation "B₂" => R.B₂

open private realization_tower_data from LanglandsSecondMainLemma.Odd.Models.Realization
open private exact_coordinate_orders_and_generation from LanglandsSecondMainLemma.Odd.Total.ASCoordinate

set_option maxHeartbeats 800000 in
/-- **Paper `O:T:cancel`.** Both weighted terminal terms lie in the whole
trivial ideal of the actual scaled additive character. The R1 bounds and
the R2 congruence are proved for the same prescribed coordinate. -/
theorem cancel
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (Delta : K) (hDelta : ord K Delta = ((-(R.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ R.t)
    (hroot : Delta ^ p - Delta = algebraMap B₂ K (norm B₂ K Delta))
    (e : LocalAddCharData F) (alpha beta gamma : Fˣ)
    (halpha : ord F (alpha : F) =
      ((-e.conductor - (R.t₂ : ℤ) - 1 : ℤ) : WithTop ℤ))
    (chi : ContinuousQuasiChar B₁) (phi : ContinuousQuasiChar B₂)
    (hphi : IsMultiplicativeConductor B₂ phi (Models.secondModelConductor R))
    (hcompat : chi.compNorm (S := K) = phi.compNorm (S := K))
    (hprimitive : ¬ ∃ theta : ContinuousQuasiChar F,
      theta.compNorm (S := K) = phi.compNorm (S := K))
    (hchiFormula : ∀ z : unitFiltration B₁ (Models.firstModelDepth R),
      chi z = tracePullbackAddChar F B₁ e.character
        (algebraMap F B₁ (alpha : F) * norm B₁ K Delta *
          truncatedLog p (1 - ((z : B₁ˣ) : B₁))))
    (m : ℤ)
    (hmt : (R.t : ℤ) < (p : ℤ) * m)
    (lambda : LocalQuasiCharData F)
    (hn : (lambda.conductor : ℤ) = (R.t₂ : ℤ) + m + 1)
    (hgamma : ord F (gamma : F) =
      ((-e.conductor - (lambda.conductor : ℤ) : ℤ) : WithTop ℤ))
    (hlambdaFormula : ∀ z : unitFiltration F (lambda.conductor ⌈/⌉ p),
      lambda.character z = e.character
        ((gamma : F) * truncatedLog p (1 - ((z : Fˣ) : F))))
    (tau : NormCharacter F B₂) (htau : tau ≠ 1)
    (htauFormula : ∀ z : unitFiltration F ((R.t₂ + 1) ⌈/⌉ p),
      tau.1 z = e.character ((alpha : F) * truncatedLog p (1 - ((z : Fˣ) : F))))
    (nu : NormCharacter F B₁) (hnu : nu ≠ 1)
    (hbeta : ord F (beta : F) =
      ((-e.conductor - (R.t : ℤ) - 1 : ℤ) : WithTop ℤ))
    (hnuFormula : ∀ z : unitFiltration F ((R.t + 1) ⌈/⌉ p),
      nu.1 z = e.character ((beta : F) * truncatedLog p (1 - ((z : Fˣ) : F))))
    (w₁ : B₁ˣ) (hw₁ : normUnits F B₁ w₁ = gamma / beta)
    (w : B₂ˣ) (hw : normUnits F B₂ w = gamma / alpha)
    (A₁ C₁ : B₁ˣ) (C₂ : B₂ˣ)
    (hA₁ : (A₁ : B₁) = algebraMap F B₁ (gamma : F) +
      algebraMap F B₁ (alpha : F) * norm B₁ K Delta)
    (hC₁ : (C₁ : B₁) = (A₁ : B₁) -
      algebraMap F B₁ (beta : F) * (w₁ : B₁))
    (hC₂ : (C₂ : B₂) = algebraMap F B₂ (gamma : F) -
      algebraMap F B₂ (alpha : F) * (w : B₂) +
      algebraMap F B₂ (alpha : F) * norm B₂ K Delta) :
    (Parameters.fourFactorValues F B₁ B₂ chi phi lambda.character e.character
      alpha beta w₁ A₁ C₁ w C₂).product = 1 := by
  let u := (alpha : F) / (gamma : F)
  let v := (beta : F) / (alpha : F)
  let a := norm B₂ K Delta
  let A₀ := norm F B₂ a
  let D := 1 + u ^ p * A₀
  let H := norm F B₁ (-elementarySymmetric B₁ K (p - 1) Delta)
  let J := norm F B₁ (trace B₁ K ((Delta / algebraMap B₂ K (w : B₂)) ^ (p - 1)))
  let Psi := (scaleAddCharData F e alpha).character
  have hu : ord F u = (m : WithTop ℤ) := by
    rw [ord_div, halpha, hgamma, ← WithTop.LinearOrderedAddCommGroup.coe_sub, hn]
    congr 1
    ring
  have hv : ord F ((beta / alpha : Fˣ) : F) = ((R.delta : ℤ) : WithTop ℤ) := by
    rw [Units.val_div_eq_div_val, ord_div, hbeta, halpha,
      ← WithTop.LinearOrderedAddCommGroup.coe_sub, R.t₂_eq, Nat.cast_add]
    congr 1
    ring
  have hPsi : IsAdditiveConductor F Psi (-(1 + (R.t₂ : ℤ))) := by
    have halphaInt : unitOrder F alpha = -e.conductor - (R.t₂ : ℤ) - 1 := by
      rw [ord_coe_eq_unitOrder] at halpha
      exact WithTop.coe_injective halpha
    convert (scaleAddCharData F e alpha).isConductor using 1
    rw [scaleAddCharData_conductor, halphaInt]
    ring
  have hmpos : 0 < m := by
    have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
    nlinarith [Int.natCast_nonneg R.t]
  have hmNat : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hmpos.le
  have hmtNat : R.t < p * m.toNat := by
    exact_mod_cast (show (R.t : ℤ) < (p : ℤ) * (m.toNat : ℤ) by
      rw [hmNat]; exact hmt)
  obtain ⟨hd₂, hrF₂, _, _, he₂⟩ := realization_tower_data hp hG hres B₂ R.degree_B₂
  obtain ⟨ha, hgen⟩ := exact_coordinate_orders_and_generation B₂ K hp R.t_pos
    hd₂ he₂ Delta a hDelta hprime hroot
  obtain ⟨htr, hsym, _, _⟩ := Models.realization_twistedEstimates_of_coordinate
    hp hG hres hchar R Delta a hroot hDelta hprime hgen
  have hnormY : norm F B₂ ((w : B₂)⁻¹) = u := by
    have hw' : normUnits F B₂ w⁻¹ = alpha / gamma := by
      rw [map_inv, hw, inv_div]
    simpa only [coe_normUnits, Units.val_inv_eq_inv_val, Units.val_div_eq_div_val]
      using congrArg Units.val hw'
  have hY : ord B₂ ((w : B₂)⁻¹) = (m : WithTop ℤ) := by
    rw [← hnormY, ord_norm, hrF₂, one_nsmul] at hu
    exact hu
  have hA₀ : ord F A₀ = ((-(R.t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_norm, hrF₂, one_nsmul, ha]
  have hsmall : ord F (u ^ p * A₀) = (((p : ℤ) * m - R.t : ℤ) : WithTop ℤ) := by
    rw [ord_mul, ord_pow, hu, hA₀]
    simp only [← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul, sub_eq_add_neg]
  have hD : ord F D = 0 := by
    rw [(ord F).map_add_eq_of_lt_left (by
      simpa only [ord_one, hsmall, WithTop.coe_pos] using sub_pos.mpr hmt), ord_one]
  have hfirst : Psi (u ^ (p - 1) * A₀ * (J + u ^ (p - 1) * H) /
      (2 * D ^ 2)) = 1 := by
    have h := R1.weighted_phase hp hG hres hchar R Delta a hDelta ha htr hsym
      ((w : B₂)⁻¹) m hY hmt Psi D hPsi hD
    have hz : algebraMap B₂ K ((w : B₂)⁻¹) * Delta =
        Delta / algebraMap B₂ K (w : B₂) := by
      rw [map_inv₀, div_eq_mul_inv, mul_comm]
    rw [hnormY, hz] at h
    exact h
  have hr₁pos : 0 < (R.t + 1) ⌈/⌉ p := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_pos (by omega) hp.pos
  have hr₂pos : 0 < (R.t₂ + 1) ⌈/⌉ p := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_pos (by omega) hp.pos
  have hchart₁ : ∀ z : lattice F (((R.t + 1) ⌈/⌉ p : ℕ) : ℤ),
      nu.1 (positiveUnitOfLattice F hr₁pos (-z)) =
        Psi (((beta / alpha : Fˣ) : F) * truncatedLog p (z : F)) := by
    intro z
    rw [hnuFormula]
    simp only [coe_positiveUnitOfLattice, Submodule.coe_neg, Psi,
      scaleAddCharData_character_apply, Units.val_div_eq_div_val,
      sub_add_eq_sub_sub, sub_self, zero_sub, neg_neg]
    congr 1
    field_simp
  have hchart₂ : ∀ z : lattice F (((R.t₂ + 1) ⌈/⌉ p : ℕ) : ℤ),
      tau.1 (positiveUnitOfLattice F hr₂pos (-z)) = Psi (truncatedLog p (z : F)) := by
    intro z
    simpa only [Psi, scaleAddCharData_character_apply, coe_positiveUnitOfLattice,
      Submodule.coe_neg, sub_add_eq_sub_sub, sub_self, zero_sub, neg_neg]
      using htauFormula (positiveUnitOfLattice F hr₂pos (-z))
  have hmodel : ∀ z : unitFiltration B₁ (Models.firstModelDepth R),
      chi z = tracePullbackAddChar F B₁ Psi
        (norm B₁ K Delta * truncatedLog p (1 - ((z : B₁ˣ) : B₁))) := by
    intro z
    rw [hchiFormula]
    simp only [tracePullbackAddChar_apply, Psi, scaleAddCharData_character_apply, mul_assoc]
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hR₂ := (R2.congruence hp hG hres hchar R
    _ _ rfl rfl hr₁pos hr₂pos nu hnu tau htau Psi (beta / alpha) hv
    hchart₁ hchart₂ Delta a hroot hDelta hprime hgen chi phi
    hcompat hprimitive hmodel).2 m.toNat hmtNat
  rw [Units.val_div_eq_div_val] at hR₂
  change H - v ^ (p - 1) ∈ _ at hR₂
  rw [hmNat] at hR₂
  have htwo : ord F (2 : F) = 0 :=
    ord_natCast_eq_zero_of_lt_residueCharacteristic F (j := 2) (by omega)
      (by rw [hchar]; exact R.odd_prime)
  have hweight : u ^ (p - 2) / (2 * D) ∈ lattice F (((p : ℤ) - 2) * m) := by
    rw [mem_lattice, ord_div, ord_pow, ord_mul, htwo, hD, zero_add, sub_zero, hu,
      ← WithTop.coe_nsmul, WithTop.coe_le_coe, nsmul_eq_mul, Nat.cast_sub
        (by have := R.odd_prime; omega), Nat.cast_ofNat]
  have hsecond : Psi (u ^ (p - 2) / (2 * D) * (H - v ^ (p - 1))) = 1 := by
    apply hPsi.trivial
    simpa only [neg_neg, add_sub_cancel] using mul_mem_lattice F hweight hR₂
  have hphase := phase R hres hchar Delta hDelta hprime hroot e alpha beta gamma halpha
    chi phi hphi hcompat hprimitive hchiFormula m hmt lambda hn hgamma hlambdaFormula
    tau htau htauFormula nu hnu hbeta hnuFormula w₁ hw₁ w hw A₁ C₁ C₂ hA₁ hC₁ hC₂
  apply inv_eq_one.mp
  rw [hphase, phase_factorization (by have := R.odd_prime; omega) _ _ _ _ _
    (div_ne_zero (Units.ne_zero alpha) (Units.ne_zero gamma))
    (by intro h; rw [h, ord_zero] at htwo; exact WithTop.top_ne_zero htwo)]
  change Psi (_ + _) = 1
  rw [Psi.map_add_eq_mul, hfirst, hsecond, mul_one]

open private twistNormRanges_ne from LanglandsSecondMainLemma.Odd.Models.TwistFormula

/-- **Paper `O:T:actual-local-factors`.** The full Lamprecht quotient retains
its evaluated fourth-root factor. The trace--norm bound and `cancel` put
the quotient in fourth roots of unity; the independent FML common odd
power removes this ambiguity for the actual base-twisted pair. -/
theorem actual_local_factors
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (Delta : K) (hDelta : ord K Delta = ((-(R.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ R.t)
    (hroot : Delta ^ p - Delta = algebraMap B₂ K (norm B₂ K Delta))
    (e : LocalAddCharData F) (alpha beta gamma : Fˣ)
    (halpha : ord F (alpha : F) =
      ((-e.conductor - (R.t₂ : ℤ) - 1 : ℤ) : WithTop ℤ))
    (chi : ContinuousQuasiChar B₁) (phi : ContinuousQuasiChar B₂)
    (hchi : IsMultiplicativeConductor B₁ chi (Models.firstModelConductor R))
    (hphi : IsMultiplicativeConductor B₂ phi (Models.secondModelConductor R))
    (hcompat : chi.compNorm (S := K) = phi.compNorm (S := K))
    (hprimitive : ¬ ∃ theta : ContinuousQuasiChar F,
      theta.compNorm (S := K) = phi.compNorm (S := K))
    (hchiFormula : ∀ z : unitFiltration B₁ (Models.firstModelDepth R),
      chi z = tracePullbackAddChar F B₁ e.character
        (algebraMap F B₁ (alpha : F) * norm B₁ K Delta *
          truncatedLog p (1 - ((z : B₁ˣ) : B₁))))
    (hphiFormula : ∀ z : unitFiltration B₂ (Models.secondModelDepth R),
      phi z = tracePullbackAddChar F B₂ e.character
        (algebraMap F B₂ (alpha : F) * norm B₂ K Delta *
          truncatedLog p (1 - ((z : B₂ˣ) : B₂))))
    (m : ℤ)
    (hmt : (R.t : ℤ) < (p : ℤ) * m)
    (lambda : LocalQuasiCharData F)
    (hn : (lambda.conductor : ℤ) = (R.t₂ : ℤ) + m + 1)
    (hgamma : ord F (gamma : F) =
      ((-e.conductor - (lambda.conductor : ℤ) : ℤ) : WithTop ℤ))
    (hlambdaFormula : ∀ z : unitFiltration F (lambda.conductor ⌈/⌉ p),
      lambda.character z = e.character
        ((gamma : F) * truncatedLog p (1 - ((z : Fˣ) : F))))
    (tau : NormCharacter F B₂) (htau : tau ≠ 1)
    (htauFormula : ∀ z : unitFiltration F ((R.t₂ + 1) ⌈/⌉ p),
      tau.1 z = e.character ((alpha : F) * truncatedLog p (1 - ((z : Fˣ) : F))))
    (nu : NormCharacter F B₁) (hnu : nu ≠ 1)
    (hbeta : ord F (beta : F) =
      ((-e.conductor - (R.t : ℤ) - 1 : ℤ) : WithTop ℤ))
    (hnuFormula : ∀ z : unitFiltration F ((R.t + 1) ⌈/⌉ p),
      nu.1 z = e.character ((beta : F) * truncatedLog p (1 - ((z : Fˣ) : F))))
    (w₁ : B₁ˣ) (hw₁ : normUnits F B₁ w₁ = gamma / beta)
    (w : B₂ˣ) (hw : normUnits F B₂ w = gamma / alpha)
    : localConstant B₁ (chi * lambda.character.compNorm (S := B₁))
        (tracePullbackAddChar F B₁ e.character) =
      localConstant B₂ (phi * lambda.character.compNorm (S := B₂))
        (tracePullbackAddChar F B₂ e.character) := by
  have hmpos : 0 < m := by
    have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
    nlinarith [Int.natCast_nonneg R.t]
  have hmNat : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hmpos.le
  have hmtNat : R.t < p * m.toNat := by
    exact_mod_cast (show (R.t : ℤ) < (p : ℤ) * (m.toNat : ℤ) by
      rw [hmNat]; exact hmt)
  have hnNat : lambda.conductor = R.t₂ + m.toNat + 1 := by omega
  have hgammaNat : ord F (gamma : F) =
      ((-e.conductor - ((R.t₂ + m.toNat : ℕ) : ℤ) - 1 : ℤ) : WithTop ℤ) := by
    rw [hgamma, hnNat]
    simp only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub]
  obtain ⟨_, _, A₁, C₁, A₂, C₂, hA₁, hC₁, _hA₂, hC₂, _, _, _, _,
      g₁, g₂, _hg₁, _hg₂, _hratio, hfour⟩ :=
    Parameters.fourFactors hp hG hres R e alpha beta gamma Delta hDelta
      chi phi hchi hphi hcompat hchiFormula hphiFormula
      (r := R.t₂ + m.toNat) (by simpa only [Nat.add_sub_cancel_left] using hmtNat)
      lambda.character (by rw [← hnNat]; exact lambda.isConductor) hgammaNat
      (by rw [← hnNat]; exact hlambdaFormula)
      nu hnu tau htau hbeta halpha hnuFormula htauFormula w₁ hw₁ w hw
  have hcancel := cancel R hres hchar Delta hDelta hprime hroot e alpha beta gamma halpha
    chi phi hphi hcompat hprimitive hchiFormula m hmt lambda hn hgamma hlambdaFormula
    tau htau htauFormula nu hnu hbeta hnuFormula w₁ hw₁ w hw A₁ C₁ C₂ hA₁
    (by rw [hC₁, hA₁]; ring) hC₂
  obtain ⟨hd₂, _, _, _, he₂⟩ := realization_tower_data hp hG hres B₂ R.degree_B₂
  obtain ⟨_, hgen⟩ := exact_coordinate_orders_and_generation B₂ K hp R.t_pos
    hd₂ he₂ Delta (norm B₂ K Delta) hDelta hprime hroot
  obtain ⟨_, _, hei, _⟩ := Models.realization_twistedEstimates_of_coordinate
    hp hG hres hchar R Delta (norm B₂ K Delta) hroot hDelta hprime hgen
  have htrace := Total.traceNorm hp hG hres hchar R Delta (norm B₂ K Delta) hroot hgen hei
  have hresidual : e.character ((alpha : F) *
      (trace F B₁ (norm B₁ K Delta) - trace F B₂ (norm B₂ K Delta))) = 1 := by
    apply e.isConductor.trivial
    have ha : (alpha : F) ∈ lattice F (-e.conductor - (R.t₂ : ℤ) - 1) := by
      rw [mem_lattice, halpha]
    convert mul_mem_lattice F ha htrace using 1
    congr 1
    ring
  have hfourth := hfour hresidual (by rw [hcancel, inv_one])
  let theta₁ := chi * lambda.character.compNorm (S := B₁)
  let theta₂ := phi * lambda.character.compNorm (S := B₂)
  have hnorm₁ (x : Kˣ) : normUnits F B₁ (normUnits B₁ K x) = normUnits F K x := by
    apply Units.ext
    exact Algebra.norm_norm
  have hnorm₂ (x : Kˣ) : normUnits F B₂ (normUnits B₂ K x) = normUnits F K x := by
    apply Units.ext
    exact Algebra.norm_norm
  have hcompat' : normQuasiChar B₁ K theta₁ = normQuasiChar B₂ K theta₂ := by
    apply ContinuousMonoidHom.ext
    intro x
    have h := DFunLike.congr_fun hcompat x
    change chi (normUnits B₁ K x) = phi (normUnits B₂ K x) at h
    change chi (normUnits B₁ K x) * lambda.character (normUnits F B₁ (normUnits B₁ K x)) =
      phi (normUnits B₂ K x) * lambda.character (normUnits F B₂ (normUnits B₂ K x))
    rw [hnorm₁, hnorm₂, h]
  have hprimitive' : ¬ ∃ eta : ContinuousQuasiChar F,
      normQuasiChar F K eta = normQuasiChar B₂ K theta₂ := by
    rintro ⟨eta, heta⟩
    apply hprimitive
    refine ⟨eta / lambda.character, ?_⟩
    apply ContinuousMonoidHom.ext
    intro x
    have h := DFunLike.congr_fun heta x
    change eta (normUnits F K x) =
      phi (normUnits B₂ K x) * lambda.character (normUnits F B₂ (normUnits B₂ K x)) at h
    change eta (normUnits F K x) / lambda.character (normUnits F K x) =
      phi (normUnits B₂ K x)
    rw [h, hnorm₂, mul_div_cancel_right]
  have hodd : Odd p := hp.odd_of_ne_two (by have := R.odd_prime; omega)
  obtain ⟨_, _, hprod₂, hprod₁, hpower⟩ := Characters.oddPower hp hodd hG
    B₂ B₁ R.degree_B₂ R.degree_B₁ (twistNormRanges_ne hp hG hres hchar R).symm
    theta₂ theta₁ (normQuasiChar B₂ K theta₂) rfl hcompat' hprimitive'
    e.character e.isConductor.character_ne_one
  rw [hprod₁, hprod₂, mul_one, mul_one] at hpower
  have hcoprime : p.Coprime 4 := hodd.coprime_two_right.pow_right 2
  have hratio := (pow_eq_one_iff_of_coprime hcoprime).mp
    ⟨hpower, hfourth⟩
  have hnonzero := (localConstant_isDeltaFinite B₁).apply_ne_zero
    (canonicalLocalQuasiCharData B₁ theta₁)
    (canonicalLocalAddCharData B₁ (tracePullbackAddChar F B₁ e.character)
      (Basic.tracePullbackAddChar_ne_one F B₁ e.character e.isConductor.character_ne_one))
  exact ((div_eq_one_iff_eq hnonzero).mp hratio).symm

end Diamond

end

end LanglandsSecondMainLemma.Odd.Transition
