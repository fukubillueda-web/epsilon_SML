import LanglandsSecondMainLemma.Odd.Conductors.Reduction
import LanglandsSecondMainLemma.Odd.Conductors.Minimal
import LanglandsSecondMainLemma.Odd.Transition.Cancel
import LanglandsSecondMainLemma.Characters.InducingChoice

/-!
# The totally ramified odd branch

Paper `O:G:totalbranch`, with the setup at lines 1803–1837 and 4962–4982.
The simultaneous full coefficients are constructed after realization, and
`O:P:preserve` retains both models when choosing the exact norms.
-/

namespace LanglandsSecondMainLemma.Odd.Total

open LanglandsFirstMainLemma
open scoped BigOperators

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The full logarithm coefficient on the entire ceiling-depth unit group. -/
private theorem fullCoefficient (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {p : ℕ} (hp : p.Prime) (hodd : 2 < p) (hchar : residueCharacteristic F = p)
    (theta : LocalQuasiCharData F) (e : LocalAddCharData F)
    (hn : 1 < theta.conductor) :
    ∃ A : Fˣ, ord F (A : F) =
        ((-e.conductor - (theta.conductor : ℤ) : ℤ) : WithTop ℤ) ∧
      ∀ u : unitFiltration F (theta.conductor ⌈/⌉ p),
        theta.character u = e.character
          ((A : F) * truncatedLog p (1 - ((u : Fˣ) : F))) := by
  let c := theta.conductor ⌈/⌉ p
  have hcover : theta.conductor ≤ p * c := le_smul_ceilDiv hp.pos
  have hc : 0 < c := by
    by_contra h
    have : c = 0 := by omega
    rw [this, mul_zero] at hcover
    omega
  have hclt : c < theta.conductor := by
    apply (show c ≤ theta.conductor - 1 from
      (ceilDiv_le_iff_le_mul hp.pos).2 (by
        have hnsub : theta.conductor - 1 + 1 = theta.conductor := Nat.sub_add_cancel (by omega)
        nlinarith)).trans_lt
    omega
  obtain ⟨A, hA, _⟩ := enhancedCoefficient_exists_unique_mod F theta e p c
    (-e.conductor) hchar hp hc hclt.le hcover rfl hn (by omega)
  refine ⟨A, hA.1, ?_⟩
  intro u
  have hz : 1 - ((u : Fˣ) : F) ∈ lattice F (c : ℤ) := by
    have hu := (mem_unitFiltration_succ_iff_sub_mem_lattice F (c - 1) (u : Fˣ)).1
      (by simpa only [Nat.sub_add_cancel hc] using u.property)
    simpa only [Nat.sub_add_cancel hc, neg_sub] using neg_mem_lattice F hu
  have hu : (positiveUnitOfLattice F hc (-⟨_, hz⟩) : Fˣ) = (u : Fˣ) := by
    apply Units.ext
    change 1 + -(1 - ((u : Fˣ) : F)) = ((u : Fˣ) : F)
    ring
  simpa only [hu] using hA.2 ⟨_, hz⟩

private theorem normCharacter_exists (F E : Type) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
    [PrimeCyclicExtension F E] {p t : ℕ} (hp : p.Prime)
    (hd : Module.finrank F E = p) (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hr : residueDegree F E = 1) :
    ∃ tau : NormCharacter F E, tau ≠ 1 ∧ IsMultiplicativeConductor F tau.1 (t + 1) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hr
  letI := primeCyclicNormCharacter_finite F E
  letI : Nontrivial (NormCharacter F E) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [ramifiedNormCharacter_card F E ht hr pi hpi hgen, hd]
    exact hp.one_lt)
  obtain ⟨tau, htau⟩ := exists_ne (1 : NormCharacter F E)
  exact ⟨tau, htau, ramifiedNormCharacter_conductor F E ht hr pi hpi hgen tau htau⟩

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
  (D : OddTotalBreakData (F := F) (K := K) hp hG)

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

open private norm_tower_residueDegrees from
  LanglandsSecondMainLemma.Odd.Models.PolynomialCoefficients
open private twistNormRanges_ne from
  LanglandsSecondMainLemma.Odd.Models.TwistFormula
open private additiveConductor_of_normCharacterChart from
  LanglandsSecondMainLemma.Odd.Models.Setup

include hp hG hres hchar D in
/-- Realize the given minimal pair and express its full models using the
original additive character. Only the first character is conjugated. -/
private theorem realizedModels
    (chi : ContinuousQuasiChar B₁) (phi : ContinuousQuasiChar B₂)
    (hcompat : normQuasiChar B₁ K chi = normQuasiChar B₂ K phi)
    (hprimitive : ¬ ∃ eta : ContinuousQuasiChar F,
      normQuasiChar F K eta = normQuasiChar B₂ K phi)
    (hphi : IsMultiplicativeConductor B₂ phi (Models.secondModelConductor D))
    (e : LocalAddCharData F) :
    ∃ (Delta : K) (alpha : Fˣ) (tau : NormCharacter F B₂) (sigma : Gal(B₁/F)),
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ¬ p ∣ D.t ∧
      Delta ^ p - Delta = algebraMap B₂ K (norm B₂ K Delta) ∧
      ord F (alpha : F) = ((-e.conductor - (D.t₂ : ℤ) - 1 : ℤ) : WithTop ℤ) ∧
      tau ≠ 1 ∧
      (∀ u : unitFiltration F ((D.t₂ + 1) ⌈/⌉ p),
        tau.1 u = e.character ((alpha : F) * truncatedLog p (1 - ((u : Fˣ) : F)))) ∧
      IsMultiplicativeConductor B₁ (Basic.conjugateQuasiChar F B₁ sigma chi)
        (Models.firstModelConductor D) ∧
      normQuasiChar B₁ K (Basic.conjugateQuasiChar F B₁ sigma chi) =
        normQuasiChar B₂ K phi ∧
      (∀ u : unitFiltration B₁ (Models.firstModelDepth D),
        Basic.conjugateQuasiChar F B₁ sigma chi u = tracePullbackAddChar F B₁ e.character
          (algebraMap F B₁ (alpha : F) * norm B₁ K Delta *
            truncatedLog p (1 - ((u : B₁ˣ) : B₁)))) ∧
      (∀ u : unitFiltration B₂ (Models.secondModelDepth D),
        phi u = tracePullbackAddChar F B₂ e.character
          (algebraMap F B₂ (alpha : F) * norm B₂ K Delta *
            truncatedLog p (1 - ((u : B₂ˣ) : B₂)))) := by
  have ht₂ := D.t_pos.trans_le D.t_le_t₂
  have hr₂ := (norm_tower_residueDegrees B₂ hres).1
  obtain ⟨tau, htau, htauC⟩ := normCharacter_exists F B₂ hp D.degree_B₂ D.B₂_breaks.1 hr₂
  let tauData : LocalQuasiCharData F := ⟨tau.1, D.t₂ + 1, htauC⟩
  obtain ⟨alpha₀, halpha₀, hformula⟩ := fullCoefficient F hp D.odd_prime hchar tauData e
    (by dsimp [tauData]; omega)
  let c := (D.t₂ + 1) ⌈/⌉ p
  have hc : 0 < c := by
    have hcover : D.t₂ + 1 ≤ p * c := le_smul_ceilDiv hp.pos
    by_contra h
    have : c = 0 := by omega
    rw [this, mul_zero] at hcover
    omega
  let Psi := (scaleAddCharData F e alpha₀).character
  have hchart : ∀ z : lattice F (c : ℤ),
      tau.1 (positiveUnitOfLattice F hc (-z)) = Psi (truncatedLog p (z : F)) := by
    intro z
    simpa [Psi] using hformula (positiveUnitOfLattice F hc (-z))
  obtain ⟨j, Delta, a, _, _, htauj, hchartj, hpower, hroot, hDelta, _,
      hprime, _, hnorm, M, hext₂, _, sigma, hext₁, hpull, hc₁, _⟩ :=
    Models.realization hp hG hres hchar D chi phi hcompat hprimitive hphi.trivial
      c rfl hc tau htau Psi hchart
  have hPsi := additiveConductor_of_normCharacterChart F B₂ hp D.odd_prime hchar
    D.degree_B₂ D.B₂_breaks.1 ht₂ hr₂ rfl hc (tau ^ j) htauj (Psi ^ j) hchartj
  have hphase : ∀ x : F, (Psi ^ j) x = e.character (((j : F) * (alpha₀ : F)) * x) :=
    hpower e.character alpha₀ (fun _ => rfl)
  have ha0 : (j : F) * (alpha₀ : F) ≠ 0 := by
    intro hz
    apply hPsi.character_ne_one
    apply ContinuousAddChar.ext
    intro x
    rw [hphase, hz, zero_mul]
    exact e.character.toAddChar.map_zero_eq_one
  let alpha : Fˣ := Units.mk0 ((j : F) * (alpha₀ : F)) ha0
  have hscale : (scaleAddCharData F e alpha).character = Psi ^ j := by
    apply ContinuousAddChar.ext
    intro x
    exact (hphase x).symm
  have halpha : ord F (alpha : F) =
      ((-e.conductor - (D.t₂ : ℤ) - 1 : ℤ) : WithTop ℤ) := by
    have heq := (scaleAddCharData F e alpha).isConductor.unique (hscale ▸ hPsi)
    rw [scaleAddCharData_conductor] at heq
    rw [ord_coe_eq_unitOrder]
    congr 1
    push_cast at heq
    omega
  have htrace (L : IntermediateField F K) (x : L) :
      tracePullbackAddChar F L (Psi ^ j) x =
        tracePullbackAddChar F L e.character (algebraMap F L (alpha : F) * x) := by
    change (Psi ^ j) (trace F L x) = e.character (trace F L _)
    rw [hphase, ← Algebra.smul_def, map_smul, smul_eq_mul]
    rfl
  refine ⟨Delta, alpha, tau ^ j, sigma, hDelta, hprime, by rwa [hnorm], halpha,
    htauj, ?_, hc₁, hpull, ?_, ?_⟩
  · intro u
    have hz : 1 - ((u : Fˣ) : F) ∈ lattice F (c : ℤ) := by
      have hu := (mem_unitFiltration_succ_iff_sub_mem_lattice F (c - 1) (u : Fˣ)).1
        (by simpa only [Nat.sub_add_cancel hc] using u.property)
      simpa only [Nat.sub_add_cancel hc, neg_sub] using neg_mem_lattice F hu
    have hu : (positiveUnitOfLattice F hc (-⟨_, hz⟩) : Fˣ) = (u : Fˣ) := by
      apply Units.ext
      change 1 + -(1 - ((u : Fˣ) : F)) = ((u : Fˣ) : F)
      ring
    simpa only [hu, hphase, alpha, Units.val_mk0] using hchartj ⟨_, hz⟩
  · intro u
    exact (DFunLike.congr_fun hext₁ u).trans ((M.R₁_apply u).trans (by
      rw [htrace, mul_assoc]))
  · intro u
    exact (DFunLike.congr_fun hext₂ u).trans ((M.R₂_apply u).trans (by
      rw [htrace, hnorm, mul_assoc]))

include hp hG hres hchar D in
/-- The higher row, with every coordinate and exact norm choice constructed
from the actual minimal pair and the common base twist. -/
private theorem higher
    (chi : ContinuousQuasiChar B₁) (phi : ContinuousQuasiChar B₂)
    (hcompat : normQuasiChar B₁ K chi = normQuasiChar B₂ K phi)
    (hprimitive : ¬ ∃ eta : ContinuousQuasiChar F,
      normQuasiChar F K eta = normQuasiChar B₂ K phi)
    (hphi : IsMultiplicativeConductor B₂ phi (Models.secondModelConductor D))
    (lambda : LocalQuasiCharData F) (r : ℕ)
    (hn : lambda.conductor = r + 1) (hr : D.t₂ < r)
    (hlarge : (D.t : ℤ) < (p : ℤ) * ((r : ℤ) - D.t₂))
    (e : LocalAddCharData F) :
    localConstant B₁ (chi * normQuasiChar F B₁ lambda.character)
        (tracePullbackAddChar F B₁ e.character) =
      localConstant B₂ (phi * normQuasiChar F B₂ lambda.character)
        (tracePullbackAddChar F B₂ e.character) := by
  obtain ⟨Delta, alpha, tau, sigma, hDelta, hprime, hroot, halpha,
    htau, htauFormula, hchi, hcompat', hchiFormula, hphiFormula⟩ :=
    realizedModels hp hG hres hchar D chi phi hcompat hprimitive hphi e
  obtain ⟨gamma, hgamma, hlambdaFormula⟩ := fullCoefficient F hp D.odd_prime hchar
    lambda e (by omega)
  have hr₁ := (norm_tower_residueDegrees B₁ hres).1
  have hr₂ := (norm_tower_residueDegrees B₂ hres).1
  obtain ⟨nu, hnu, hnuC⟩ := normCharacter_exists F B₁ hp D.degree_B₁ D.B₁_breaks.1 hr₁
  let nuData : LocalQuasiCharData F := ⟨nu.1, D.t + 1, hnuC⟩
  obtain ⟨beta, hbeta, hnuFormula⟩ := fullCoefficient F hp D.odd_prime hchar nuData e
    (by dsimp [nuData]; have := D.t_pos; omega)
  have hbeta' : ord F (beta : F) =
      ((-e.conductor - (D.t : ℤ) - 1 : ℤ) : WithTop ℤ) := by
    simpa only [nuData, Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using hbeta
  obtain ⟨beta', _, hbeta', _, hnuFormula', _, w₁, hw₁, _⟩ :=
    Parameters.normChoice F B₁ D.degree_B₁ D.odd_prime D.B₁_breaks.1 D.t_pos hr₁
      nu hnu e beta gamma hbeta' hnuFormula
  obtain ⟨alpha', hratio, halpha', _, htauFormula', _, w₂, hw₂, _⟩ :=
    Parameters.normChoice F B₂ D.degree_B₂ D.odd_prime D.B₂_breaks.1
      (D.t_pos.trans_le D.t_le_t₂) hr₂ tau htau e alpha gamma halpha htauFormula
  let h : unitFiltration F D.t₂ := ⟨alpha' / alpha, hratio⟩
  have ha : alpha * (h : Fˣ) = alpha' := by simp [h, div_eq_mul_inv]
  obtain ⟨hchiFormula', hphiFormula', _, _⟩ := Parameters.preservation hp hG hres hchar D
    e alpha tau htau htauFormula Delta hDelta
    (Basic.conjugateQuasiChar F B₁ sigma chi) phi hchiFormula hphiFormula h
  rw [ha] at hchiFormula' hphiFormula'
  have heq := Transition.actual_local_factors D hres hchar Delta hDelta hprime hroot
    e alpha' beta' gamma halpha'
    (Basic.conjugateQuasiChar F B₁ sigma chi) phi hchi hphi hcompat' hprimitive
    hchiFormula' hphiFormula' ((r : ℤ) - D.t₂) hlarge lambda
    (by rw [hn]; push_cast; ring) hgamma hlambdaFormula
    tau htau htauFormula' nu hnu hbeta' hnuFormula' w₁ hw₁ w₂ hw₂
  have hconj : Basic.conjugateQuasiChar F B₁ sigma
      (chi * normQuasiChar F B₁ lambda.character) =
      Basic.conjugateQuasiChar F B₁ sigma chi * normQuasiChar F B₁ lambda.character := by
    apply ContinuousMonoidHom.ext
    intro x
    change chi (Units.map sigma.symm.toMonoidHom x) *
        lambda.character (normUnits F B₁ (Units.map sigma.symm.toMonoidHom x)) =
      chi (Units.map sigma.symm.toMonoidHom x) * lambda.character (normUnits F B₁ x)
    congr 2
    apply Units.ext
    exact Algebra.norm_eq_of_algEquiv sigma.symm (x : B₁)
  change localConstant B₁
    (Basic.conjugateQuasiChar F B₁ sigma chi * normQuasiChar F B₁ lambda.character)
    (tracePullbackAddChar F B₁ e.character) =
    localConstant B₂ (phi * normQuasiChar F B₂ lambda.character)
      (tracePullbackAddChar F B₂ e.character) at heq
  rw [← hconj] at heq
  have hc := Basic.localConstant_conjugate F B₁ sigma
    (chi * normQuasiChar F B₁ lambda.character)
    (tracePullbackAddChar F B₁ e.character)
    (Basic.tracePullbackAddChar_ne_one F B₁ e.character e.isConductor.character_ne_one)
    (fun x => by
      change e.character (trace F B₁ (sigma x)) = e.character (trace F B₁ x)
      rw [trace_galoisConjugate])
  exact hc.symm.trans heq

open private high_pullback_conductor from
  LanglandsSecondMainLemma.Odd.Conductors.Reduction

include hp hG hres hchar D in
/-- Complete comparison for the distinguished pair, splitting at the exact
second conductor. The lower products are retained through both cases. -/
private theorem distinguished
    (psi₁ : ContinuousQuasiChar B₁) (psi₂ : ContinuousQuasiChar B₂)
    (hcompat : normQuasiChar B₁ K psi₁ = normQuasiChar B₂ K psi₂)
    (hprimitive : ¬ ∃ eta : ContinuousQuasiChar F,
      normQuasiChar F K eta = normQuasiChar B₂ K psi₂)
    (psi : ContinuousAddChar F) (hpsi : psi ≠ 1) :
    Characters.inducingFactor hp hG psi B₁ D.degree_B₁ psi₁ =
      Characters.inducingFactor hp hG psi B₂ D.degree_B₂ psi₂ := by
  letI := primeCyclicNormCharacter_finite F B₁
  letI := primeCyclicNormCharacter_finite F B₂
  letI := Fintype.ofFinite (NormCharacter F B₁)
  letI := Fintype.ofFinite (NormCharacter F B₂)
  have hne := twistNormRanges_ne hp hG hres hchar D
  let a₁ := multiplicativeConductorExponent B₁ psi₁
  let a₂ := multiplicativeConductorExponent B₂ psi₂
  have hc₁ := multiplicativeConductorExponent_isConductor B₁ psi₁
  have hc₂ := multiplicativeConductorExponent_isConductor B₂ psi₂
  obtain ⟨hlow₁, hlow₂⟩ := Conductors.lower hp hG hres D hne psi₁ psi₂
    (normQuasiChar B₂ K psi₂) a₁ a₂ hcompat rfl hprimitive hc₁ hc₂
  by_cases hmin : a₂ = 1 + D.t + D.t₂
  · letI := PrimeCyclicExtension.ofCyclicPrimeExtension B₁ K
      (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.2.2.2.2
    letI := PrimeCyclicExtension.ofCyclicPrimeExtension B₂ K
      (Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.2
    have hr₁ := (norm_tower_residueDegrees B₁ hres).2
    have hr₂ := (norm_tower_residueDegrees B₂ hres).2
    have hd₁ := (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.2.2.1
    have hd₂ := (Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂).2.2.2.2.2.2.2.2.2.2.1
    have hhigh₁ := high_pullback_conductor (F := B₁) (E := K) D.B₁_breaks.2 hr₁ hc₁
      (by have := D.t_pos; change D.tPrime + 1 < a₁; omega)
    have hhigh₂ := high_pullback_conductor (F := B₂) (E := K) D.B₂_breaks.2 hr₂ hc₂
      (by have := D.t_pos; have := D.t_le_t₂; change D.t + 1 < a₂; omega)
    rw [hcompat, hd₁] at hhigh₁
    rw [hd₂] at hhigh₂
    have heq := hhigh₁.symm.trans hhigh₂
    have ha₁ : a₁ = 1 + D.t + D.tPrime := by
      change (p : ℤ) * (a₁ : ℤ) - _ = (p : ℤ) * (a₂ : ℤ) - _ at heq
      rw [hmin, D.tPrime_eq, D.t₂_eq] at heq
      rw [D.tPrime_eq]
      push_cast [Nat.cast_sub hp.one_le] at heq
      have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
      have hzero : (a₁ : ℤ) = 1 + D.t + (D.t + p * D.delta) := by nlinarith [heq]
      exact_mod_cast hzero
    have hm₁ : IsMultiplicativeConductor B₁ psi₁ (Models.firstModelConductor D) := by
      convert hc₁ using 1
      dsimp [Models.firstModelConductor]
      omega
    have hm₂ : IsMultiplicativeConductor B₂ psi₂ (Models.secondModelConductor D) := by
      convert hc₂ using 1
      simp only [Models.secondModelConductor]
      omega
    exact Conductors.minimal hp hG hres hchar D psi₁ psi₂ hcompat hprimitive hm₁ hm₂ psi hpsi
  · have hlarge : 1 + D.t + D.t₂ < a₂ := by omega
    obtain ⟨_, _, _, _, _, hprime, _⟩ := aSCoordinate hp hG hres hchar D
    obtain ⟨lam, chi, phi, hpsi₁, hpsi₂, hc, hprim, hm₁, hm₂, hhigh⟩ :=
      Conductors.reduction hp hG hres D hprime hne psi₁ psi₂
        (normQuasiChar B₂ K psi₂) hcompat rfl hprimitive
    obtain ⟨r, hrcond, hr, hrange, _⟩ := hhigh hlarge
    let lambda : LocalQuasiCharData F := ⟨lam, 1 + r, hrcond⟩
    have hprim' : ¬ ∃ eta : ContinuousQuasiChar F,
        normQuasiChar F K eta = normQuasiChar B₂ K phi := by rwa [hc] at hprim
    have hphi : IsMultiplicativeConductor B₂ phi (Models.secondModelConductor D) := by
      simpa only [Models.secondModelConductor] using hm₂
    have heq := higher hp hG hres hchar D chi phi hc hprim' hphi lambda r
      (by dsimp [lambda]; omega) hr hrange (canonicalLocalAddCharData F psi hpsi)
    have hodd : Odd p := hp.odd_of_ne_two (by have := D.odd_prime; omega)
    obtain ⟨_, _, hprod₁, hprod₂, _⟩ := Characters.oddPower hp hodd hG
      B₁ B₂ D.degree_B₁ D.degree_B₂ hne psi₁ psi₂
      (normQuasiChar B₂ K psi₂) hcompat rfl hprimitive psi hpsi
    change localConstant B₁ psi₁ (tracePullbackAddChar F B₁ psi) *
        (∏ nu : NormCharacter F B₁, localConstant F nu.1 psi) =
      localConstant B₂ psi₂ (tracePullbackAddChar F B₂ psi) *
        (∏ nu : NormCharacter F B₂, localConstant F nu.1 psi)
    rw [hprod₁, hprod₂, mul_one, mul_one, hpsi₁, hpsi₂]
    exact heq

open private fixedField_line_finrank exists_line_ne from
  LanglandsSecondMainLemma.Odd.Total.Setup

/-- Construct the distinguished break data for any other lower line of
one fixed ramification profile. -/
private def profilePair (hodd : 2 < p)
    (P : Ramification.TotallyRamifiedDiamondBreaks (F := F) (K := K) hp hG)
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p) (hne : H ≠ P.H₀) :
    OddTotalBreakData (F := F) (K := K) hp hG := by
  let s := Classical.choose (P.other_breaks H hH hne)
  have hs := Classical.choose_spec (P.other_breaks H hH hne)
  have hst := hs.2.2.1
  have hb := hs.2.2.2
  have hle : P.t ≤ s := (Nat.le_add_right P.t _).trans_eq hst.symm
  exact
    { odd_prime := hodd
      H₁ := P.H₀
      H₂ := H
      card_H₁ := P.card_H₀
      card_H₂ := hH
      lines_ne := hne.symm
      t := P.t
      t₂ := s
      tPrime := P.b
      delta := s - P.t
      t_pos := P.t_pos
      t_le_t₂ := hle
      t₂_eq := (Nat.add_sub_of_le hle).symm
      tPrime_eq := hb
      B₁_breaks := P.distinguished_breaks
      B₂_breaks := hs.1
      degree_B₁ := fixedField_line_finrank hp hG P.H₀ P.card_H₀
      degree_B₂ := fixedField_line_finrank hp hG H hH }

include hp hG hres hchar in
/-- Compare arbitrary inducing choices using a single distinguished field.
Its inducing character is supplied by actual continuous cyclic norm descent. -/
private theorem invariantComparison (hodd : 2 < p)
    (Theta : ContinuousQuasiChar K)
    (hinv : ∀ sigma : Gal(K/F), Basic.conjugateQuasiChar F K sigma Theta = Theta)
    (hprimitive : ¬ ∃ eta : ContinuousQuasiChar F, normQuasiChar F K eta = Theta)
    (psi : ContinuousAddChar F) (hpsi : psi ≠ 1)
    (I J : IntermediateField F K) (hI : Module.finrank F I = p)
    (hJ : Module.finrank F J = p)
    (chiI : ContinuousQuasiChar I) (chiJ : ContinuousQuasiChar J)
    (hcI : normQuasiChar I K chiI = Theta) (hcJ : normQuasiChar J K chiJ = Theta) :
    Characters.inducingFactor hp hG psi I hI chiI =
      Characters.inducingFactor hp hG psi J hJ chiJ := by
  classical
  let P := Classical.choice ((Ramification.diamondBreaks hp hG hchar).1 hres)
  obtain ⟨H, hH, hne⟩ := exists_line_ne hp hG P.H₀
  let D₀ := profilePair hp hG hodd P H hH hne
  have hsep := twistNormRanges_ne hp hG hres hchar D₀
  have hcompare : ∀ (L : IntermediateField F K) (hL : Module.finrank F L = p),
      L ≠ D₀.B₁ → ∀ (theta₀ : ContinuousQuasiChar D₀.B₁) (thetaL : ContinuousQuasiChar L),
        normQuasiChar D₀.B₁ K theta₀ = Theta → normQuasiChar L K thetaL = Theta →
        Characters.inducingFactor hp hG psi D₀.B₁ D₀.degree_B₁ theta₀ =
          Characters.inducingFactor hp hG psi L hL thetaL := by
    intro L hL hneL
    have hcard : Nat.card L.fixingSubgroup = p := by
      rw [IsGalois.card_fixingSubgroup_eq_finrank]
      exact (Basic.intermediateField_tower_compatible hp hG L hL).2.2.2.2.2.2.2.2.2.2.1
    have hneH : L.fixingSubgroup ≠ P.H₀ := by
      intro heq
      apply hneL
      change L = IntermediateField.fixedField P.H₀
      rw [← heq, IsGalois.fixedField_fixingSubgroup]
    let DL := profilePair hp hG hodd P L.fixingSubgroup hcard hneH
    have hfix : DL.B₂ = L := IsGalois.fixedField_fixingSubgroup L
    have htransport : ∀ (L' : IntermediateField F K) (hL' : Module.finrank F L' = p),
        DL.B₂ = L' → ∀ (theta₀ : ContinuousQuasiChar D₀.B₁) (thetaL : ContinuousQuasiChar L'),
          normQuasiChar D₀.B₁ K theta₀ = Theta → normQuasiChar L' K thetaL = Theta →
          Characters.inducingFactor hp hG psi D₀.B₁ D₀.degree_B₁ theta₀ =
            Characters.inducingFactor hp hG psi L' hL' thetaL := by
      intro L' hL' heq
      subst L'
      intro theta₀ thetaL hc₀ hcL
      exact distinguished hp hG hres hchar DL theta₀ thetaL (hc₀.trans hcL.symm)
        (by rwa [hcL]) psi hpsi
    exact htransport L hL hfix
  obtain ⟨_, _, hfamily⟩ := Characters.distinguishedComparisons_imply_family hp hG
    D₀.B₁ D₀.B₂ D₀.degree_B₁ D₀.degree_B₂ hsep Theta hinv hprimitive psi hpsi hcompare
  exact hfamily I J hI hJ chiI chiJ hcI hcJ

open private inf_eq_bot_of_prime_degree compatible_invariant from
  LanglandsSecondMainLemma.Characters.Conjugacy

include hp hG hres hchar in
/-- **Paper Theorem 9.36 (`O:G:totalbranch`).** Every compatible
non-descending pair on two distinct degree-`p` intermediate fields of a
totally ramified `C_p × C_p` extension has equal complete induction factors.

The fields, continuous group quasi-characters, norms, trace pullbacks and
canonical local constants are actual ones. The common pullback's invariance
is proved from compatibility on the two distinct upper cyclic subgroups.
All lower norm characters, including the trivial character, occur in each
factor. Both field characteristics, `p = 3`, and nonunitary characters are
included; no stationary data or comparison identity is an input. -/
theorem comparison (hodd : 2 < p)
    (I J : IntermediateField F K) (hI : Module.finrank F I = p)
    (hJ : Module.finrank F J = p) (hne : I ≠ J)
    (chiI : ContinuousQuasiChar I) (chiJ : ContinuousQuasiChar J)
    (Theta : ContinuousQuasiChar K)
    (hcI : normQuasiChar I K chiI = Theta) (hcJ : normQuasiChar J K chiJ = Theta)
    (hprimitive : ¬ ∃ eta : ContinuousQuasiChar F, normQuasiChar F K eta = Theta)
    (psi : ContinuousAddChar F) (hpsi : psi ≠ 1) :
    Characters.inducingFactor hp hG psi I hI chiI =
      Characters.inducingFactor hp hG psi J hJ chiJ := by
  have hinv := compatible_invariant I J (inf_eq_bot_of_prime_degree hp I J hI hJ hne)
    chiI chiJ Theta hcI hcJ
  apply invariantComparison hp hG hres hchar hodd Theta _ hprimitive psi hpsi
    I J hI hJ chiI chiJ hcI hcJ
  intro sigma
  apply ContinuousMonoidHom.ext
  intro x
  exact hinv sigma.symm x

end Diamond
end
end LanglandsSecondMainLemma.Odd.Total
