import LanglandsFirstMainLemma.Ramification.NormRepresentatives
import LanglandsSecondMainLemma.Odd.Models.GlobalExtension
import LanglandsSecondMainLemma.Odd.NormLog
import LanglandsSecondMainLemma.Odd.NormPhase
import LanglandsSecondMainLemma.Characters.Conjugacy
import LanglandsSecondMainLemma.Odd.EnhancedStationary

/-!
# Odd / Models / Twist Formula

Paper `O:M:q0`, `O:M:approx`, and `O:M:lambdaformula` (8.7).
The auxiliary results below keep the integer coefficient depth, allow a zero
coefficient, and use only the ordinary subcritical norm approximation.

`twistFormula` constructs initial models using `globalExtension` and the
two actual commutator isomorphisms using `Characters.conjugacy`. Norm
separation is derived from the given break data. A common exponent
`1 ≤ j < p` gives the global descending character
`phi₂ = theta₂ ^ j * normQuasiChar F B₂ lambda` (lines 2681--2693).

The conductor bound and `enhancedCoefficient_exists_unique_mod` then
construct the full coefficient chart for `Psi' = Psi ^ j` (2704--2710).
Triviality on the whole chart selects `gamma = w = 0`. Otherwise FML's
ordinary subcritical norm representative retains the exact coefficient
order and only the permitted norm congruence. The existing evaluation
lemmas finish the full formula on the second model's logarithm domain,
with both the negative norm phase and the power--norm error accounted for.
-/

namespace LanglandsSecondMainLemma.Odd.Models

noncomputable section

open LanglandsFirstMainLemma

set_option backward.isDefEq.respectTransparency false

/-- The exponent-matching step of `O:M:actual2`. Two isomorphisms from
a group of prime order differ by one common nonzero exponent. The input
isomorphisms must still be constructed from the actual compatible pairs. -/
theorem twistExponent_exists {G H : Type*} [Group G] [Group H]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card G = p)
    (f g : G ≃* H) :
    ∃ j : ℕ, 0 < j ∧ j < p ∧ ∀ s : G, f s = g s ^ j := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsCyclic G := isCyclic_of_prime_card hcard
  obtain ⟨m, hm⟩ := (f.trans g.symm).toMonoidHom.map_cyclic
  let j := (m % (p : ℤ)).toNat
  have hjcast : (j : ℤ) = m % (p : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.ne_zero))
  have hjlt : j < p := by
    have := Int.emod_lt_of_pos m (by exact_mod_cast hp.pos : (0 : ℤ) < p)
    omega
  have hmatch (s : G) : f s = g s ^ j := by
    have hs : g.symm (f s) = s ^ j := by
      calc
        g.symm (f s) = s ^ m := hm s
        _ = s ^ (m % (p : ℤ)) := by rw [← hcard, zpow_mod_natCard]
        _ = s ^ j := by rw [← hjcast, zpow_natCast]
    simpa only [MulEquiv.apply_symm_apply, map_pow] using congrArg g hs
  have hjpos : 0 < j := by
    by_contra hn
    have hjzero : j = 0 := by omega
    have hsub : Subsingleton G := ⟨fun x y ↦ f.injective (by
      rw [hmatch x, hmatch y, hjzero, pow_zero, pow_zero])⟩
    have hcardOne : Nat.card G = 1 := @Nat.card_unique G ⟨1⟩ hsub
    have := hp.one_lt
    omega
  exact ⟨j, hjpos, hjlt, hmatch⟩

/-- The depths in `O:M:q0`. No coprimality assumption on the lower break
`t₂` is needed. The final inequality is the precise power--norm error bound. -/
theorem twistDepth_bounds {p t t₂ : ℕ} (hp : 2 < p) (ht : 0 < t)
    (htt₂ : t ≤ t₂) :
    let h := t / p
    let c := (t₂ + 1) ⌈/⌉ p
    let q₀ := h + c
    let q₂ := (1 + t + t₂) ⌈/⌉ p
    0 < c ∧ 0 < q₀ ∧ 0 < q₂ ∧ q₀ ≤ q₂ ∧ q₀ ≤ t₂ ∧
      t₂ + 1 + h ≤ p * q₀ ∧
      (t₂ : ℤ) + 1 ≤ -(p : ℤ) * h + (p - 1 : ℕ) * (t₂ : ℤ) + q₂ := by
  dsimp only
  let h := t / p
  let c := (t₂ + 1) ⌈/⌉ p
  let q₂ := (1 + t + t₂) ⌈/⌉ p
  have hp0 : 0 < p := by omega
  have hph : p * h ≤ t := by simpa [h, Nat.mul_comm] using Nat.div_mul_le_self t p
  have hc : t₂ + 1 ≤ p * c := by
    simpa [c, smul_eq_mul] using (le_smul_ceilDiv (b := t₂ + 1) hp0)
  have hq₂ : 1 + t + t₂ ≤ p * q₂ := by
    simpa [q₂, smul_eq_mul] using (le_smul_ceilDiv (b := 1 + t + t₂) hp0)
  have hcpos : 0 < c := by
    by_contra hn
    have hz : c = 0 := by omega
    rw [hz, mul_zero] at hc
    omega
  have hqpos : 0 < q₂ := by
    by_contra hn
    have hz : q₂ = 0 := by omega
    rw [hz, mul_zero] at hq₂
    omega
  have hhq : h ≤ q₂ := by nlinarith
  have hhT : h ≤ t₂ := by nlinarith
  have hq : h + c ≤ q₂ := by
    have hcq : c ≤ q₂ - h := by
      rw [show c = (t₂ + 1) ⌈/⌉ p from rfl, ceilDiv_le_iff_le_mul hp0]
      have hsub : p * (q₂ - h) = p * q₂ - p * h := Nat.mul_sub_left_distrib ..
      rw [hsub]
      omega
    omega
  have hqT : h + c ≤ t₂ := by
    have hct : c ≤ t₂ - h := by
      rw [show c = (t₂ + 1) ⌈/⌉ p from rfl, ceilDiv_le_iff_le_mul hp0]
      have hsub : p * (t₂ - h) + p * h = p * t₂ := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hhT]
      have ht₂pos : 0 < t₂ := ht.trans_le htt₂
      have hmul : 3 * t₂ ≤ p * t₂ := Nat.mul_le_mul_right t₂ hp
      nlinarith
    omega
  refine ⟨hcpos, by change 0 < h + c; exact hcpos.trans_le (Nat.le_add_left c h), hqpos, hq, hqT, ?_, ?_⟩
  · change t₂ + 1 + h ≤ p * (h + c)
    nlinarith
  · have hphZ : (p : ℤ) * h ≤ t := by exact_mod_cast hph
    have hT : (t : ℤ) ≤ t₂ := by exact_mod_cast htt₂
    have hqZ : (1 : ℤ) ≤ q₂ := by exact_mod_cast hqpos
    have hpred : (2 : ℤ) ≤ (p - 1 : ℕ) := by exact_mod_cast (show 2 ≤ p - 1 by omega)
    change (t₂ : ℤ) + 1 ≤ -(p : ℤ) * h + (p - 1 : ℕ) * (t₂ : ℤ) + q₂
    nlinarith

private theorem additivePhase_sub {L : Type*} [Field L] [TopologicalSpace L]
    (Psi : ContinuousAddChar L) (x y : L) : Psi (x - y) = Psi x / Psi y :=
  Psi.toAddChar.map_sub_eq_div x y

/-- Construct the full logarithm coefficient from a conductor bound.
The restriction which is trivial on the whole chart has coefficient zero;
otherwise the enhanced coefficient theorem applies at the actual conductor. -/
theorem twistCoefficient_exists (F : Type*) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {p q M : ℕ} {J : ℤ} (hp : p.Prime)
    (hchar : residueCharacteristic F = p) (hq : 0 < q) (hlog : M ≤ p * q)
    (lambda : ContinuousQuasiChar F)
    (hlambda : QuasiCharTrivialOnUnitFiltration F lambda M)
    (Psi : ContinuousAddChar F) (hPsi : IsAdditiveConductor F Psi (-J)) :
    ∃ gamma : F, gamma ∈ lattice F (J - (M : ℤ)) ∧
      (QuasiCharTrivialOnUnitFiltration F lambda q → gamma = 0) ∧
      ∀ z : lattice F (q : ℤ),
        lambda (positiveUnitOfLattice F hq (-z)) =
          Psi (gamma * truncatedLog p (z : F)) := by
  by_cases htriv : QuasiCharTrivialOnUnitFiltration F lambda q
  · refine ⟨0, by simp, fun _ ↦ rfl, ?_⟩
    intro z
    simpa using htriv _ (positiveUnitOfLattice F hq (-z)).property
  obtain ⟨m, hm⟩ := exists_isMultiplicativeConductor F lambda
  have hmM : m ≤ M := hm.minimal M hlambda
  have hqm : q < m := hm.not_trivialOnUnitFiltration_iff.mp htriv
  let theta : LocalQuasiCharData F := ⟨lambda, m, hm⟩
  let psi : LocalAddCharData F := ⟨Psi, -J, hPsi⟩
  obtain ⟨B, hB, _⟩ := enhancedCoefficient_exists_unique_mod F theta psi p q J
    hchar hp hq (by exact hqm.le) (by exact hmM.trans hlog)
    (by simp [psi]) (by change 1 < m; omega) (by exact hqm)
  refine ⟨(B : F), ?_, fun h ↦ (htriv h).elim, hB.2⟩
  apply lattice_antitone F
    (sub_le_sub_left (show (m : ℤ) ≤ M by exact_mod_cast hmM) J)
  rw [mem_lattice, hB.1]

section Cyclic
variable (F E : Type) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E]
  [Module.Free F E] [Module.Finite F E] [PrimeCyclicExtension F E]

/-- The conductor bound preceding `O:M:q0`. This uses the actual norm
image above the break and needs only triviality of the pullback at `m₂`. -/
theorem twistConductor_bound {p t t₂ : ℕ}
    (hdegree : Module.finrank F E = p)
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F E t₂)
    (hres : residueDegree F E = 1) (lambda : ContinuousQuasiChar F)
    (hpull : QuasiCharTrivialOnUnitFiltration E (normQuasiChar F E lambda)
      (1 + t + t₂)) :
    QuasiCharTrivialOnUnitFiltration F lambda (t₂ + 1 + t / p) := by
  have hp : 0 < p := hdegree ▸ Module.finrank_pos (R := F) (M := E)
  have hquot : (0 : ℤ) ≤ ((t / p : ℕ) : ℤ) := Int.natCast_nonneg _
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  let NF := cyclicPrimeNormFiltration F E ht₂ hres pi hpi hgen
  have hsource : 1 + t + t₂ ≤
      herbrandPsiNat t₂ (Module.finrank F E) (t₂ + 1 + t / p) := by
    rw [hdegree, herbrandPsiNat_of_break_le _ _ (by omega)]
    have hdiv : t < p * (t / p + 1) := Nat.lt_mul_div_succ t hp
    have hsub : t₂ + 1 + t / p - t₂ = 1 + t / p := by omega
    rw [hsub]
    nlinarith
  intro u hu
  rw [← NF.above_image (t₂ + 1 + t / p) (by omega)] at hu
  obtain ⟨z, hz, rfl⟩ := hu
  exact hpull z (unitFiltration_antitone E hsource hz)

/-- The conductor bound applied to the global identity `O:M:actual2`.
Only the actual characters' triviality at `m₂` is used, so no exact
conductor or unitarity is required for their quotient. -/
theorem twistConductor_bound_of_identity {p t t₂ j : ℕ}
    (hdegree : Module.finrank F E = p)
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F E t₂)
    (hres : residueDegree F E = 1)
    (phi theta : ContinuousQuasiChar E) (lambda : ContinuousQuasiChar F)
    (hphi : QuasiCharTrivialOnUnitFiltration E phi (1 + t + t₂))
    (htheta : QuasiCharTrivialOnUnitFiltration E theta (1 + t + t₂))
    (hidentity : phi = theta ^ j * normQuasiChar F E lambda) :
    QuasiCharTrivialOnUnitFiltration F lambda (t₂ + 1 + t / p) := by
  apply twistConductor_bound F E hdegree ht₂ hres lambda
  intro u hu
  have hvalue := DFunLike.congr_fun hidentity u
  simpa only [ContinuousMonoidHom.mul_apply, ContinuousMonoidHom.pow_apply,
    hphi u hu, htheta u hu, one_pow, one_mul] using hvalue.symm

/-- Once the actual commutators match, construct the global descending
twist in `O:M:actual2` and prove its conductor bound. The quotient is a
continuous group character; no unitarity or exact conductor of the
descending character is required. The inverse on `sigma` agrees with the
paper's conjugation convention. -/
theorem twistDescends_of_commutator_match {p t t₂ j : ℕ}
    (hdegree : Module.finrank F E = p)
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F E t₂)
    (hres : residueDegree F E = 1)
    (phi theta : ContinuousQuasiChar E)
    (hphi : QuasiCharTrivialOnUnitFiltration E phi (1 + t + t₂))
    (htheta : QuasiCharTrivialOnUnitFiltration E theta (1 + t + t₂))
    (hmatch : ∀ (sigma : Gal(E/F)) (x : Eˣ),
      phi (Units.map sigma.symm.toMonoidHom x) / phi x =
        (theta (Units.map sigma.symm.toMonoidHom x) / theta x) ^ j) :
    ∃ lambda : ContinuousQuasiChar F,
      phi = theta ^ j * normQuasiChar F E lambda ∧
      QuasiCharTrivialOnUnitFiltration F lambda (t₂ + 1 + t / p) := by
  obtain ⟨lambda, hlambda⟩ :=
    Local.invariantCharacter_descends F E (phi / theta ^ j) (by
      intro sigma x
      have h := hmatch sigma.symm x
      simp only [AlgEquiv.symm_symm, div_pow] at h
      simp only [div_eq_mul_inv, ContinuousQuasiChar.mul_apply,
        ContinuousQuasiChar.inv_apply, ContinuousQuasiChar.pow_apply]
      simpa only [div_eq_mul_inv] using (div_eq_div_iff_div_eq_div.mp h))
  have hidentity : phi = theta ^ j * normQuasiChar F E lambda := by
    simp [hlambda]
  exact ⟨lambda, hidentity,
    twistConductor_bound_of_identity F E hdegree ht₂ hres phi theta lambda
      hphi htheta hidentity⟩

/-- Paper `O:M:approx`, including `gamma = 0`. For nonzero coefficients the
source order equals the actual coefficient order; the norm is only congruent
to the coefficient at the permitted subcritical precision. -/
theorem twistNormRepresentative {t₂ h : ℕ}
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F E t₂)
    (hres : residueDegree F E = 1) (gamma : F)
    (hgamma : gamma ∈ lattice F (-(h : ℤ))) :
    ∃ w : E, w ∈ lattice E (-(h : ℤ)) ∧
      (gamma = 0 → w = 0) ∧
      (gamma ≠ 0 → ∃ k : ℤ,
        -(h : ℤ) ≤ k ∧ ord F gamma = (k : WithTop ℤ) ∧
        ord E w = (k : WithTop ℤ) ∧
        gamma - norm F E w ∈ lattice F (k + (t₂ : ℤ))) ∧
      gamma - norm F E w ∈ lattice F (-(h : ℤ) + (t₂ : ℤ)) := by
  by_cases hg : gamma = 0
  · subst gamma
    refine ⟨0, by simp, fun _ ↦ rfl, fun hn ↦ (hn rfl).elim, ?_⟩
    simp
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).2 hg)
  have hkg : -(h : ℤ) ≤ k := by
    rw [mem_lattice, ← hk] at hgamma
    exact_mod_cast hgamma
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  obtain ⟨w, hw⟩ := normRepresentative_subcritical F E ht₂ hres pi hpi hgen
    (le_rfl : t₂ ≤ t₂) (Units.mk0 gamma hg) hk.symm
  refine ⟨(w : E), ?_, fun hzero ↦ (hg hzero).elim,
    fun _ ↦ ⟨k, hkg, hk.symm, hw.source_order, hw.norm_congruent⟩, ?_⟩
  · exact lattice_antitone E hkg hw.source_exactDepth.1
  · exact lattice_antitone F (by omega) hw.norm_congruent

open private additiveConductor_of_normCharacterChart from
  LanglandsSecondMainLemma.Odd.Models.Setup

/-- Evaluation step of Paper 8.7, starting with the descending character's
full logarithmic chart. The norm representative is constructed, including
zero. This auxiliary theorem does not construct that chart or the descending
character from a prescribed compatible pair. -/
theorem twistFormula_of_chart
    {p t t₂ h c q₂ : ℕ}
    (hdegree : Module.finrank F E = p) (hodd : 2 < p)
    (ht : 0 < t) (htt₂ : t ≤ t₂)
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F E t₂)
    (hres : residueDegree F E = 1) (hchar : residueCharacteristic F = p)
    (hh : h = t / p) (hc : c = (t₂ + 1) ⌈/⌉ p)
    (hq₂ : q₂ = (1 + t + t₂) ⌈/⌉ p)
    (hcpos : 0 < c) (hq₂pos : 0 < q₂)
    (tau : NormCharacter F E) (htau : tau ≠ 1)
    (Psi : ContinuousAddChar F)
    (htauChart : ∀ z : lattice F (c : ℤ),
      tau.1 (positiveUnitOfLattice F hcpos (-z)) =
        Psi (truncatedLog p (z : F)))
    (lambda : ContinuousQuasiChar F) (gamma : F)
    (hgamma : gamma ∈ lattice F (-(h : ℤ)))
    (hlambdaChart : ∀ z : lattice F ((h + c : ℕ) : ℤ),
      lambda (positiveUnitOfLattice F (by omega : 0 < h + c) (-z)) =
        Psi (gamma * truncatedLog p (z : F))) :
    ∃ w : E, w ∈ lattice E (-(h : ℤ)) ∧ (gamma = 0 → w = 0) ∧
      (gamma ≠ 0 → ∃ k : ℤ,
        -(h : ℤ) ≤ k ∧ ord F gamma = (k : WithTop ℤ) ∧
        ord E w = (k : WithTop ℤ) ∧
        gamma - norm F E w ∈ lattice F (k + (t₂ : ℤ))) ∧
      gamma - norm F E w ∈ lattice F (-(h : ℤ) + (t₂ : ℤ)) ∧
      ∀ x : lattice E (q₂ : ℤ),
        normQuasiChar F E lambda (positiveUnitOfLattice E hq₂pos (-x)) =
          tracePullbackAddChar F E Psi ((w ^ p - w) * truncatedLog p (x : E)) := by
  have hp : p.Prime := hdegree ▸ PrimeCyclicExtension.degree_prime F E
  have ht₂pos : 0 < t₂ := ht.trans_le htt₂
  have hbounds := twistDepth_bounds hodd ht htt₂
  rw [← hh, ← hc, ← hq₂] at hbounds
  obtain ⟨_, hq₀pos, _, hq₀q₂, hq₀t₂, _, hpowerDepth⟩ := hbounds
  have hPsi := additiveConductor_of_normCharacterChart F E hp hodd hchar
    hdegree ht₂ ht₂pos hres hc hcpos tau htau Psi htauChart
  have hPsiTriv : AddCharTrivialOnLattice F Psi ((t₂ + 1 : ℕ) : ℤ) := by
    simpa only [neg_neg] using hPsi.trivial
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have hPsiE : IsAdditiveConductor E (tracePullbackAddChar F E Psi)
      (-((t₂ + 1 : ℕ) : ℤ)) := by
    have he := additiveConductor_compTrace_cyclicPrime F E ht₂ hres pi hpi hgen hPsi
    have hindex : (Module.finrank F E : ℤ) * -((t₂ + 1 : ℕ) : ℤ) +
        (((Module.finrank F E - 1) * (t₂ + 1) : ℕ) : ℤ) =
          -((t₂ + 1 : ℕ) : ℤ) := by
      rw [hdegree, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ p)]
      ring
    rw [hindex] at he
    exact he
  have hPsiETriv : AddCharTrivialOnLattice E (tracePullbackAddChar F E Psi)
      ((t₂ + 1 : ℕ) : ℤ) := by
    simpa only [neg_neg] using hPsiE.trivial
  obtain ⟨w, hw, hwzero, hwexact, happrox⟩ :=
    twistNormRepresentative F E ht₂ hres gamma hgamma
  refine ⟨w, hw, hwzero, hwexact, happrox, ?_⟩
  intro x
  have hcharE : residueCharacteristic E = p :=
    (residueCharacteristic_extension_eq F E).trans hchar
  have hPx : truncatedLog p (x : E) ∈ lattice E (q₂ : ℤ) := by
    rw [mem_lattice, ord_truncatedLog E p hcharE
      (lattice_antitone E (by exact_mod_cast hq₂pos) x.property)]
    exact x.property
  let ux := positiveUnitOfLattice E hq₂pos (-x)
  have hnormUnit : normUnits F E (ux : Eˣ) ∈ unitFiltration F (h + c) :=
    normMapsUnitFiltration_belowBreak F E ht₂ hq₀t₂ hres pi hpi hgen _
      (unitFiltration_antitone E hq₀q₂ ux.property)
  have hnormCoe : (normUnits F E (ux : Eˣ) : F) = norm F E (1 - (x : E)) := by
    simp [ux, sub_eq_add_neg]
  let u : F := 1 - norm F E (1 - (x : E))
  have hu : u ∈ lattice F ((h + c : ℕ) : ℤ) := by
    have hd := (mem_unitFiltration_succ_iff_sub_mem_lattice F (h + c - 1)
      (normUnits F E (ux : Eˣ))).1 (by
        simpa only [Nat.sub_add_cancel hq₀pos] using hnormUnit)
    rw [Nat.sub_add_cancel hq₀pos, hnormCoe] at hd
    simpa [u] using neg_mem_lattice F hd
  let uq : lattice F ((h + c : ℕ) : ℤ) := ⟨u, hu⟩
  have huUnit : (positiveUnitOfLattice F hq₀pos (-uq) : Fˣ) =
      normUnits F E (ux : Eˣ) := by
    apply Units.ext
    simp only [coe_positiveUnitOfLattice, Submodule.coe_neg, uq]
    rw [hnormCoe]
    simp [u]
  have hPu : truncatedLog p u ∈ lattice F ((h + c : ℕ) : ℤ) := by
    rw [mem_lattice, ord_truncatedLog F p hchar
      (lattice_antitone F (by exact_mod_cast hq₀pos) hu)]
    exact hu
  have hreplace : Psi (gamma * truncatedLog p u) =
      Psi (norm F E w * truncatedLog p u) := by
    apply div_eq_one.mp
    rw [← additivePhase_sub Psi, ← sub_mul]
    apply hPsiTriv
    apply lattice_antitone F (show ((t₂ + 1 : ℕ) : ℤ) ≤
      -(h : ℤ) + (t₂ : ℤ) + ((h + c : ℕ) : ℤ) by omega)
    exact mul_mem_lattice F happrox hPu
  have hlog := normLog F E ht₂ ht₂pos hres (hchar.trans hdegree.symm)
    (by omega) h (x : E) (by
      rw [hdegree, ← hc]
      exact lattice_antitone E (by exact_mod_cast hq₀q₂) x.property)
  have hnormW : norm F E w ∈ lattice F (-(h : ℤ)) := by
    rw [mem_lattice, ord_norm, hres, one_nsmul]
    exact hw
  have hlogPhase : Psi (norm F E w * truncatedLog p u) =
      Psi (norm F E w * (trace F E (truncatedLog p (x : E)) +
        norm F E (truncatedLog p (x : E)))) := by
    apply div_eq_one.mp
    rw [← additivePhase_sub Psi]
    have herr := mul_mem_lattice F hnormW hlog
    have heq : norm F E w * truncatedLog p u - norm F E w *
        (trace F E (truncatedLog p (x : E)) + norm F E (truncatedLog p (x : E))) =
      norm F E w * (truncatedLog p u - trace F E (truncatedLog p (x : E)) -
        norm F E (truncatedLog p (x : E))) := by ring
    rw [heq]
    apply hPsiTriv
    convert herr using 1 <;> simp [hdegree, u]
  have hwPx : w * truncatedLog p (x : E) ∈ lattice E (c : ℤ) :=
    lattice_antitone E (by omega) (mul_mem_lattice E hw hPx)
  have hconversion := (normPhase F E ht₂ ht₂pos hres (hchar.trans hdegree.symm)
    (by omega) c (by simpa [hdegree] using hc) hcpos tau htau Psi hPsi
    (by simpa [hdegree] using htauChart) _ hwPx).1
  have hconvertNorm : Psi (norm F E (w * truncatedLog p (x : E))) =
      tracePullbackAddChar F E Psi (-(w * truncatedLog p (x : E))) := by
    apply div_eq_one.mp
    rw [tracePullbackAddChar_apply, map_neg, ← additivePhase_sub Psi]
    convert hconversion using 1
    congr 1
    ring
  have hpower := Total.powerNorm F E p t₂ hdegree hodd ht₂ ht₂pos hres w
  have hpowerMem : w ^ p - algebraMap F E (norm F E w) ∈
      lattice E (-(p : ℤ) * h + ((p - 1 : ℕ) : ℤ) * t₂) := by
    have hscaled := nsmul_le_nsmul_right
      (show ((-(h : ℤ)) : WithTop ℤ) ≤ ord E w from hw) p
    have hbound := add_le_add hscaled
      (le_refl (((((p - 1) * t₂ : ℕ) : ℤ) : WithTop ℤ)))
    have htot := hbound.trans hpower
    simpa only [mem_lattice, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul,
      Nat.cast_mul, mul_neg, neg_mul] using htot
  have hreplacePower : tracePullbackAddChar F E Psi
      ((algebraMap F E (norm F E w) - w) * truncatedLog p (x : E)) =
      tracePullbackAddChar F E Psi ((w ^ p - w) * truncatedLog p (x : E)) := by
    apply Eq.symm
    apply div_eq_one.mp
    rw [← additivePhase_sub (tracePullbackAddChar F E Psi)]
    apply hPsiETriv
    have herr : (w ^ p - algebraMap F E (norm F E w)) * truncatedLog p (x : E) ∈
        lattice E ((t₂ + 1 : ℕ) : ℤ) :=
      lattice_antitone E (by simpa using hpowerDepth) (mul_mem_lattice E hpowerMem hPx)
    convert herr using 1
    ring
  calc
    normQuasiChar F E lambda (positiveUnitOfLattice E hq₂pos (-x)) =
        lambda (positiveUnitOfLattice F hq₀pos (-uq)) := congrArg lambda huUnit.symm
    _ = Psi (gamma * truncatedLog p u) := hlambdaChart uq
    _ = Psi (norm F E w * truncatedLog p u) := hreplace
    _ = Psi (norm F E w * (trace F E (truncatedLog p (x : E)) +
          norm F E (truncatedLog p (x : E)))) := hlogPhase
    _ = tracePullbackAddChar F E Psi
          (algebraMap F E (norm F E w) * truncatedLog p (x : E)) *
        Psi (norm F E (w * truncatedLog p (x : E))) := by
      rw [mul_add, ContinuousAddChar.map_add_eq_mul,
        map_mul (norm F E), tracePullbackAddChar_apply]
      congr 2
      symm
      simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self_apply] using
        (trace F E).map_smul (norm F E w) (truncatedLog p (x : E))
    _ = tracePullbackAddChar F E Psi
          ((algebraMap F E (norm F E w) - w) * truncatedLog p (x : E)) := by
      rw [hconvertNorm, ← ContinuousAddChar.map_add_eq_mul]
      congr 1
      ring
    _ = tracePullbackAddChar F E Psi
          ((w ^ p - w) * truncatedLog p (x : E)) := hreplacePower

private theorem twistNormCharacter_pow_ne_one {p t₂ j : ℕ}
    (hdegree : Module.finrank F E = p)
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F E t₂)
    (hres : residueDegree F E = 1) (hjpos : 0 < j) (hjp : j < p)
    (tau : NormCharacter F E) (htau : tau ≠ 1) : tau ^ j ≠ 1 := by
  have hp : p.Prime := hdegree ▸ PrimeCyclicExtension.degree_prime F E
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have hcard : Nat.card (NormCharacter F E) = p :=
    (ramifiedNormCharacter_card F E ht₂ hres pi hpi hgen).trans hdegree
  have horder : orderOf tau = p :=
    orderOf_eq_prime (by rw [← hcard]; exact pow_card_eq_one') htau
  exact pow_ne_one_of_lt_orderOf (Nat.ne_of_gt hjpos) (by rwa [horder])

/-- Evaluation for the paper's powered character `Psi' = Psi ^ j`.
Nontriviality of `tau ^ j` is proved from the actual norm-character group's
prime cardinality, rather than assumed. The coefficient chart remains an
explicit premise of this auxiliary result. -/
theorem twistFormula_of_power_chart
    {p t t₂ h c q₂ j : ℕ}
    (hdegree : Module.finrank F E = p) (hodd : 2 < p)
    (ht : 0 < t) (htt₂ : t ≤ t₂)
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F E t₂)
    (hres : residueDegree F E = 1) (hchar : residueCharacteristic F = p)
    (hh : h = t / p) (hc : c = (t₂ + 1) ⌈/⌉ p)
    (hq₂ : q₂ = (1 + t + t₂) ⌈/⌉ p)
    (hcpos : 0 < c) (hq₂pos : 0 < q₂) (hjpos : 0 < j) (hjp : j < p)
    (tau : NormCharacter F E) (htau : tau ≠ 1)
    (Psi : ContinuousAddChar F)
    (htauChart : ∀ z : lattice F (c : ℤ),
      tau.1 (positiveUnitOfLattice F hcpos (-z)) =
        Psi (truncatedLog p (z : F)))
    (lambda : ContinuousQuasiChar F) (gamma : F)
    (hgamma : gamma ∈ lattice F (-(h : ℤ)))
    (hlambdaChart : ∀ z : lattice F ((h + c : ℕ) : ℤ),
      lambda (positiveUnitOfLattice F (by omega : 0 < h + c) (-z)) =
        (Psi ^ j) (gamma * truncatedLog p (z : F))) :
    ∃ w : E, w ∈ lattice E (-(h : ℤ)) ∧ (gamma = 0 → w = 0) ∧
      (gamma ≠ 0 → ∃ k : ℤ,
        -(h : ℤ) ≤ k ∧ ord F gamma = (k : WithTop ℤ) ∧
        ord E w = (k : WithTop ℤ) ∧
        gamma - norm F E w ∈ lattice F (k + (t₂ : ℤ))) ∧
      gamma - norm F E w ∈ lattice F (-(h : ℤ) + (t₂ : ℤ)) ∧
      ∀ x : lattice E (q₂ : ℤ),
        normQuasiChar F E lambda (positiveUnitOfLattice E hq₂pos (-x)) =
          tracePullbackAddChar F E (Psi ^ j)
            ((w ^ p - w) * truncatedLog p (x : E)) := by
  have htauj : tau ^ j ≠ 1 :=
    twistNormCharacter_pow_ne_one F E hdegree ht₂ hres hjpos hjp tau htau
  have hchartj : ∀ z : lattice F (c : ℤ),
      (tau ^ j).1 (positiveUnitOfLattice F hcpos (-z)) =
        (Psi ^ j) (truncatedLog p (z : F)) := by
    intro z
    simpa only [NormCharacter.coe_pow, ContinuousMonoidHom.pow_apply,
      ContinuousAddChar.pow_apply] using congrArg (fun v : ℂˣ ↦ v ^ j) (htauChart z)
  exact twistFormula_of_chart F E hdegree hodd ht htt₂ ht₂ hres hchar hh hc hq₂
    hcpos hq₂pos (tau ^ j) htauj (Psi ^ j) hchartj lambda gamma hgamma hlambdaChart

/-- Construct the coefficient and the approximate norm representative from
the actual descending character. This includes a chart which is trivial,
without imposing an exact conductor on `lambda`. -/
theorem twistFormula_of_conductor
    {p t t₂ c q₂ : ℕ}
    (hdegree : Module.finrank F E = p) (hodd : 2 < p)
    (ht : 0 < t) (htt₂ : t ≤ t₂)
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F E t₂)
    (hres : residueDegree F E = 1) (hchar : residueCharacteristic F = p)
    (hc : c = (t₂ + 1) ⌈/⌉ p) (hq₂ : q₂ = (1 + t + t₂) ⌈/⌉ p)
    (hcpos : 0 < c) (hq₂pos : 0 < q₂)
    (tau : NormCharacter F E) (htau : tau ≠ 1)
    (Psi : ContinuousAddChar F)
    (htauChart : ∀ z : lattice F (c : ℤ),
      tau.1 (positiveUnitOfLattice F hcpos (-z)) =
        Psi (truncatedLog p (z : F)))
    (lambda : ContinuousQuasiChar F)
    (hlambda : QuasiCharTrivialOnUnitFiltration F lambda (t₂ + 1 + t / p)) :
    ∃ (gamma : F) (w : E),
      gamma ∈ lattice F (-((t / p : ℕ) : ℤ)) ∧
      w ∈ lattice E (-((t / p : ℕ) : ℤ)) ∧
      (QuasiCharTrivialOnUnitFiltration F lambda (t / p + c) → gamma = 0 ∧ w = 0) ∧
      (gamma = 0 → w = 0) ∧
      (gamma ≠ 0 → ∃ k : ℤ,
        -((t / p : ℕ) : ℤ) ≤ k ∧ ord F gamma = (k : WithTop ℤ) ∧
        ord E w = (k : WithTop ℤ) ∧
        gamma - norm F E w ∈ lattice F (k + (t₂ : ℤ))) ∧
      gamma - norm F E w ∈ lattice F (-((t / p : ℕ) : ℤ) + (t₂ : ℤ)) ∧
      (∀ z : lattice F ((t / p + c : ℕ) : ℤ),
        lambda (positiveUnitOfLattice F
          (hcpos.trans_le (Nat.le_add_left c (t / p))) (-z)) =
          Psi (gamma * truncatedLog p (z : F))) ∧
      ∀ x : lattice E (q₂ : ℤ),
        normQuasiChar F E lambda (positiveUnitOfLattice E hq₂pos (-x)) =
          tracePullbackAddChar F E Psi ((w ^ p - w) * truncatedLog p (x : E)) := by
  have hp : p.Prime := hdegree ▸ PrimeCyclicExtension.degree_prime F E
  have hbounds := twistDepth_bounds hodd ht htt₂
  rw [← hc, ← hq₂] at hbounds
  obtain ⟨_, hq₀pos, _, _, _, hlog, _⟩ := hbounds
  have hPsi := additiveConductor_of_normCharacterChart F E hp hodd hchar
    hdegree ht₂ (ht.trans_le htt₂) hres hc hcpos tau htau Psi htauChart
  obtain ⟨gamma, hgamma, hzero, hchart⟩ :=
    twistCoefficient_exists F hp hchar hq₀pos hlog lambda hlambda Psi hPsi
  have hg : gamma ∈ lattice F (-((t / p : ℕ) : ℤ)) := by
    have hdepth : ((t₂ + 1 : ℕ) : ℤ) - ((t₂ + 1 + t / p : ℕ) : ℤ) =
        -((t / p : ℕ) : ℤ) := by omega
    simpa only [hdepth] using hgamma
  obtain ⟨w, hw, hwzero, hwexact, happrox, hformula⟩ :=
    twistFormula_of_chart F E hdegree hodd ht htt₂ ht₂ hres hchar rfl hc hq₂
      hcpos hq₂pos tau htau Psi htauChart lambda gamma hg hchart
  exact ⟨gamma, w, hg, hw, fun h ↦ ⟨hzero h, hwzero (hzero h)⟩,
    hwzero, hwexact, happrox, hchart, hformula⟩

end Cyclic

open private norm_tower_residueDegrees from
  LanglandsSecondMainLemma.Odd.Models.PolynomialCoefficients

/-- The chosen break data select the distinguished norm subgroup when the
breaks differ. When they coincide, norm separation applies to every pair
of distinct lines. Thus the conjugacy API needs no extra geometric premise. -/
private theorem twistNormRanges_ne
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (D : Total.OddTotalBreakData (F := F) (K := K) hp hG) :
    Ramification.intermediateNormRange D.B₁ ≠ Ramification.intermediateNormRange D.B₂ := by
  let B₁ := D.B₁
  let B₂ := D.B₂
  letI := Basic.intermediateFieldValuativeRel B₁
  letI := Basic.intermediateFieldTopology B₁
  letI := Basic.intermediateField_localField B₁
  letI := Basic.intermediateField_lowerValuativeExtension B₁
  letI := Basic.intermediateField_upperValuativeExtension B₁
  letI := Basic.intermediateFieldValuativeRel B₂
  letI := Basic.intermediateFieldTopology B₂
  letI := Basic.intermediateField_localField B₂
  letI := Basic.intermediateField_lowerValuativeExtension B₂
  letI := Basic.intermediateField_upperValuativeExtension B₂
  let E₁ := Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁
  let E₂ := Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
  letI : PrimeCyclicExtension F B₁ := PrimeCyclicExtension.ofCyclicPrimeExtension F B₁
    E₁.2.2.2.2.2.2.2.2.2.2.2.1
  letI : PrimeCyclicExtension F B₂ := PrimeCyclicExtension.ofCyclicPrimeExtension F B₂
    E₂.2.2.2.2.2.2.2.2.2.2.2.1
  letI : PrimeCyclicExtension B₂ K := PrimeCyclicExtension.ofCyclicPrimeExtension B₂ K
    E₂.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨P, hsep, hequal⟩ :=
    (Ramification.normSeparation hp hG).totally_ramified hres hchar
  by_cases hone : P.t = P.b
  · exact hequal hone D.H₁ D.H₂ D.card_H₁ D.card_H₂ D.lines_ne
  have hH₁ : D.H₁ = P.H₀ := by
    by_contra hne
    obtain ⟨s, hs, _, _, hb⟩ := P.other_breaks D.H₁ D.card_H₁ hne
    have hs' : s = D.t :=
      PrimeCyclicExtension.isLowerBreak_unique F B₁ hs.1 D.B₁_breaks.1
    by_cases hH₂ : D.H₂ = P.H₀
    · have hpair : Ramification.IntermediateBreakPair hp hG D.H₂ D.card_H₂ P.t P.b := by
        simpa only [hH₂] using P.distinguished_breaks
      have hlow : P.t = D.t₂ :=
        PrimeCyclicExtension.isLowerBreak_unique F B₂ hpair.1 D.B₂_breaks.1
      have hupp : P.b = D.t :=
        PrimeCyclicExtension.isLowerBreak_unique B₂ K hpair.2 D.B₂_breaks.2
      have := P.t_le_b
      have := D.t_le_t₂
      exact hone (by omega)
    · obtain ⟨_, hpair, _⟩ := P.other_breaks D.H₂ D.card_H₂ hH₂
      have hupp : P.t = D.t :=
        PrimeCyclicExtension.isLowerBreak_unique B₂ K hpair.2 D.B₂_breaks.2
      rw [hs', hupp, Nat.sub_self, mul_zero, add_zero] at hb
      exact hone (hupp.trans hb.symm)
  have hH₂ : D.H₂ ≠ P.H₀ := by
    rw [← hH₁]
    exact D.lines_ne.symm
  simpa only [← hH₁, Total.OddTotalBreakData.B₁, Total.OddTotalBreakData.B₂]
    using hsep D.H₂ D.card_H₂ hH₂

/-- Paper `O:M:actual2`, `O:M:approx`, and `O:M:lambdaformula` (8.7).
For a prescribed primitive compatible pair, construct initial global models,
match the actual second commutators, and construct the descending twist and
its full logarithm formula. Geometric norm separation is proved from the
break data before applying `Characters.conjugacy`; no commutator map, descending chart, or norm
representative is assumed. The first character needs only compatibility;
the second needs only the stated conductor bound. -/
theorem twistFormula
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (D : Total.OddTotalBreakData (F := F) (K := K) hp hG) :
    let B₁ := D.B₁
    let B₂ := D.B₂
    letI := Basic.intermediateFieldValuativeRel B₁
    letI := Basic.intermediateFieldTopology B₁
    letI := Basic.intermediateField_localField B₁
    letI := Basic.intermediateField_lowerValuativeExtension B₁
    letI := Basic.intermediateField_upperValuativeExtension B₁
    letI := Basic.intermediateFieldValuativeRel B₂
    letI := Basic.intermediateFieldTopology B₂
    letI := Basic.intermediateField_localField B₂
    letI := Basic.intermediateField_lowerValuativeExtension B₂
    letI := Basic.intermediateField_upperValuativeExtension B₂
    ∀ (phi₁ : ContinuousQuasiChar B₁) (phi₂ : ContinuousQuasiChar B₂),
      normQuasiChar B₁ K phi₁ = normQuasiChar B₂ K phi₂ →
      (¬ ∃ chi : ContinuousQuasiChar F,
        normQuasiChar F K chi = normQuasiChar B₂ K phi₂) →
      QuasiCharTrivialOnUnitFiltration B₂ phi₂ (secondModelConductor D) →
      ∀ (c : ℕ) (_hc : c = (D.t₂ + 1) ⌈/⌉ p) (hcpos : 0 < c)
        (tau : NormCharacter F B₂) (_htau : tau ≠ 1) (Psi : ContinuousAddChar F),
        (∀ z : lattice F (c : ℤ),
          tau.1 (positiveUnitOfLattice F hcpos (-z)) =
            Psi (truncatedLog p (z : F))) →
        ∃ (Delta : K) (a : B₂),
          Delta ^ p - Delta = algebraMap B₂ K a ∧
          ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
          ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
          ¬ p ∣ D.t ∧ Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ ∧
          norm B₂ K Delta = a ∧
          ∃ M : OddMinimalCharacterModels B₁ B₂ p
              (firstModelDepth D) (firstModelConductor D)
              (secondModelDepth D) (secondModelConductor D)
              (tracePullbackAddChar F B₁ Psi) (tracePullbackAddChar F B₂ Psi)
              (norm B₁ K Delta) a,
            ∃ (theta₁ : ContinuousQuasiChar B₁) (theta₂ : ContinuousQuasiChar B₂),
              theta₁.toMonoidHom.comp (unitFiltration B₁ (firstModelDepth D)).subtype = M.R₁ ∧
              theta₂.toMonoidHom.comp (unitFiltration B₂ (secondModelDepth D)).subtype = M.R₂ ∧
              normQuasiChar B₁ K theta₁ = normQuasiChar B₂ K theta₂ ∧
              IsMultiplicativeConductor B₁ theta₁ (firstModelConductor D) ∧
              IsMultiplicativeConductor B₂ theta₂ (secondModelConductor D) ∧
              ∃ (j : ℕ) (lambda : ContinuousQuasiChar F) (gamma : F) (w : B₂),
                0 < j ∧ j < p ∧ phi₂ = theta₂ ^ j * normQuasiChar F B₂ lambda ∧
                (∀ (sigma : Gal(B₂/F)) (x : B₂ˣ),
                  phi₂ (Units.map sigma.symm.toMonoidHom x) / phi₂ x =
                    (theta₂ (Units.map sigma.symm.toMonoidHom x) / theta₂ x) ^ j) ∧
                QuasiCharTrivialOnUnitFiltration F lambda (D.t₂ + 1 + D.t / p) ∧
                gamma ∈ lattice F (-((D.t / p : ℕ) : ℤ)) ∧
                w ∈ lattice B₂ (-((D.t / p : ℕ) : ℤ)) ∧
                (QuasiCharTrivialOnUnitFiltration F lambda (D.t / p + c) →
                  gamma = 0 ∧ w = 0) ∧
                (gamma = 0 → w = 0) ∧
                (gamma ≠ 0 → ∃ k : ℤ,
                  -((D.t / p : ℕ) : ℤ) ≤ k ∧ ord F gamma = (k : WithTop ℤ) ∧
                  ord B₂ w = (k : WithTop ℤ) ∧
                  gamma - norm F B₂ w ∈ lattice F (k + (D.t₂ : ℤ))) ∧
                gamma - norm F B₂ w ∈ lattice F (-((D.t / p : ℕ) : ℤ) + (D.t₂ : ℤ)) ∧
                (∀ z : lattice F ((D.t / p + c : ℕ) : ℤ),
                  lambda (positiveUnitOfLattice F
                    (hcpos.trans_le (Nat.le_add_left c (D.t / p))) (-z)) =
                      (Psi ^ j) (gamma * truncatedLog p (z : F))) ∧
                ∀ (hq₂pos : 0 < secondModelDepth D)
                  (x : lattice B₂ (secondModelDepth D : ℤ)),
                  normQuasiChar F B₂ lambda (positiveUnitOfLattice B₂ hq₂pos (-x)) =
                    tracePullbackAddChar F B₂ (Psi ^ j)
                      ((w ^ p - w) * truncatedLog p (x : B₂)) := by
  dsimp only
  let B₁ := D.B₁
  let B₂ := D.B₂
  letI := Basic.intermediateFieldValuativeRel B₁
  letI := Basic.intermediateFieldTopology B₁
  letI := Basic.intermediateField_localField B₁
  letI := Basic.intermediateField_lowerValuativeExtension B₁
  letI := Basic.intermediateField_upperValuativeExtension B₁
  letI := Basic.intermediateFieldValuativeRel B₂
  letI := Basic.intermediateFieldTopology B₂
  letI := Basic.intermediateField_localField B₂
  letI := Basic.intermediateField_lowerValuativeExtension B₂
  letI := Basic.intermediateField_upperValuativeExtension B₂
  intro phi₁ phi₂ hcompat hprimitive hphi c hc hcpos tau htau Psi htauChart
  let E₂ := Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
  letI : PrimeCyclicExtension F B₂ := PrimeCyclicExtension.ofCyclicPrimeExtension F B₂
    E₂.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hrF₂, _⟩ := norm_tower_residueDegrees B₂ hres
  obtain ⟨Delta, a, hroot, hDelta, ha, hprime, hgen, hnorm, hmodels⟩ :=
    globalExtension hp hG hres hchar D
  obtain ⟨M, ⟨theta₂, hext₂⟩, hextend⟩ := hmodels c hc hcpos tau htau Psi htauChart
  obtain ⟨theta₁, hext₁, hthetaCompat, hc₁, hc₂, _, hthetaPrimitive, _⟩ :=
    hextend theta₂ hext₂
  have hne := twistNormRanges_ne hp hG hres hchar D
  obtain ⟨_, ⟨Dphi⟩, _⟩ := Characters.conjugacy hp hG B₁ B₂
    D.degree_B₁ D.degree_B₂ hne phi₁ phi₂ (normQuasiChar B₂ K phi₂)
    hcompat rfl hprimitive
  obtain ⟨_, ⟨Dtheta⟩, _⟩ := Characters.conjugacy hp hG B₁ B₂
    D.degree_B₁ D.degree_B₂ hne theta₁ theta₂ (normQuasiChar B₂ K theta₂)
    hthetaCompat rfl hthetaPrimitive
  obtain ⟨j, hjpos, hjp, hj⟩ := twistExponent_exists hp
    ((IsGalois.card_aut_eq_finrank F B₂).trans D.degree_B₂)
    Dphi.quotientEquiv Dtheta.quotientEquiv
  have hmatch (sigma : Gal(B₂/F)) (x : B₂ˣ) :
      phi₂ (Units.map sigma.symm.toMonoidHom x) / phi₂ x =
        (theta₂ (Units.map sigma.symm.toMonoidHom x) / theta₂ x) ^ j := by
    have hphiValue : (Dphi.quotientEquiv sigma).1 x =
        phi₂ (Units.map sigma.symm.toMonoidHom x) / phi₂ x := by
      rw [Dphi.quotient_eq]
      rfl
    have hthetaValue : (Dtheta.quotientEquiv sigma).1 x =
        theta₂ (Units.map sigma.symm.toMonoidHom x) / theta₂ x := by
      rw [Dtheta.quotient_eq]
      rfl
    rw [← hphiValue, hj sigma, NormCharacter.coe_pow,
      ContinuousMonoidHom.pow_apply, hthetaValue]
  obtain ⟨lambda, hidentity, hlambda⟩ := twistDescends_of_commutator_match F B₂
    D.degree_B₂ D.B₂_breaks.1 hrF₂ phi₂ theta₂ hphi hc₂.trivial hmatch
  have htauj := twistNormCharacter_pow_ne_one F B₂ D.degree_B₂ D.B₂_breaks.1
    hrF₂ hjpos hjp tau htau
  have hchartj : ∀ z : lattice F (c : ℤ),
      (tau ^ j).1 (positiveUnitOfLattice F hcpos (-z)) =
        (Psi ^ j) (truncatedLog p (z : F)) := by
    intro z
    simpa only [NormCharacter.coe_pow, ContinuousMonoidHom.pow_apply,
      ContinuousAddChar.pow_apply] using congrArg (fun v : ℂˣ ↦ v ^ j) (htauChart z)
  have hq₂pos : 0 < secondModelDepth D := (domains_original D hres).2.1
  obtain ⟨gamma, w, hgamma, hw, hzero, hwzero, hexact, happrox, hchart, hformula⟩ :=
    twistFormula_of_conductor F B₂ D.degree_B₂ D.odd_prime D.t_pos D.t_le_t₂
      D.B₂_breaks.1 hrF₂ hchar hc rfl hcpos hq₂pos
      (tau ^ j) htauj (Psi ^ j) hchartj lambda hlambda
  exact ⟨Delta, a, hroot, hDelta, ha, hprime, hgen, hnorm, M,
    theta₁, theta₂, hext₁, hext₂, hthetaCompat, hc₁, hc₂,
    j, lambda, gamma, w, hjpos, hjp, hidentity, hmatch, hlambda,
    hgamma, hw, hzero, hwzero, hexact, happrox, hchart, fun _ ↦ hformula⟩

end
end LanglandsSecondMainLemma.Odd.Models
