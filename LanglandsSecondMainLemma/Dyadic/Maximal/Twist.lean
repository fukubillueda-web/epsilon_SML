import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Dyadic.Maximal.Models
import LanglandsSecondMainLemma.Characters.Conjugacy

/-!
# Dyadic / Maximal / Twist

Paper Lemma 12.7 (`D:MX:realize`). Realization uses descent of the quotient
of actual characters and the conjugation orbit, with canonical local
constants preserved. Conductor comparisons retain the critical norm case.
-/

namespace LanglandsSecondMainLemma.Dyadic.Maximal

open LanglandsFirstMainLemma

noncomputable section

/-- A quadratic norm pullback has the exact high conductor, and is bounded
by the critical conductor throughout the lower range. -/
private theorem quadraticPullbackConductors
    (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
    [PrimeCyclicExtension F E]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hdeg : Module.finrank F E = 2)
    (lambda : ContinuousQuasiChar F) :
    let n := multiplicativeConductorExponent F lambda
    let m := multiplicativeConductorExponent E (normQuasiChar F E lambda)
    (n ≤ t + 1 → m ≤ t + 1) ∧
      (t + 1 < n → (m : ℤ) = 2 * (n : ℤ) - (t + 1 : ℕ)) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  let c := canonicalLocalQuasiCharData F lambda
  let d := canonicalLocalQuasiCharData E (normQuasiChar F E lambda)
  change (c.conductor ≤ t + 1 → d.conductor ≤ t + 1) ∧
    (t + 1 < c.conductor → (d.conductor : ℤ) =
      2 * (c.conductor : ℤ) - (t + 1 : ℕ))
  constructor
  · intro hn
    by_cases hbelow : c.conductor ≤ t
    · rw [c.conductor_compNorm_eq_belowBreak F E ht hres pi hpi hgen d rfl hbelow]
      exact hn
    · exact c.conductor_compNorm_le_critical F E ht hres pi hpi hgen d rfl (by omega)
  · intro hn
    simpa only [hdeg, Nat.cast_ofNat, Nat.reduceSub, one_mul] using
      c.conductor_compNorm_eq_high_explicit F E ht hres pi hpi hgen d rfl hn

/-- The conductor and parity alternatives in `D:MX:realize`, for arbitrary
actual cores of the stated conductors and every continuous base twist.
The high formulas are equalities in `ℤ`. -/
theorem twist_conductors
    (F E₁ E₂ : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E₁] [ValuativeRel E₁] [TopologicalSpace E₁]
    [IsNonarchimedeanLocalField E₁]
    [Field E₂] [ValuativeRel E₂] [TopologicalSpace E₂]
    [IsNonarchimedeanLocalField E₂]
    [Algebra F E₁] [ValuativeExtension F E₁] [Module.Finite F E₁]
    [Algebra F E₂] [ValuativeExtension F E₂] [Module.Finite F E₂]
    [PrimeCyclicExtension F E₁] [PrimeCyclicExtension F E₂]
    {e a : ℕ} (ha : 1 ≤ a) (hae : a ≤ e)
    (ht₁ : PrimeCyclicExtension.IsLowerBreak F E₁ (2 * a - 1))
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F E₂ (2 * e))
    (hres₁ : residueDegree F E₁ = 1) (hres₂ : residueDegree F E₂ = 1)
    (hdeg₁ : Module.finrank F E₁ = 2) (hdeg₂ : Module.finrank F E₂ = 2)
    (chi₁ : ContinuousQuasiChar E₁) (chi₂ : ContinuousQuasiChar E₂)
    (hc₁ : IsMultiplicativeConductor E₁ chi₁ (4 * e + 1))
    (hc₂ : IsMultiplicativeConductor E₂ chi₂ (2 * e + 2 * a))
    (lambda : ContinuousQuasiChar F) :
    let n := multiplicativeConductorExponent F lambda
    let M₁ := multiplicativeConductorExponent E₁ (chi₁ * normQuasiChar F E₁ lambda)
    let M₂ := multiplicativeConductorExponent E₂ (chi₂ * normQuasiChar F E₂ lambda)
    (n ≤ 2 * e + a → M₁ = 4 * e + 1 ∧ M₂ = 2 * e + 2 * a ∧
      Odd M₁ ∧ Even M₂) ∧
    (2 * e + a + 1 ≤ n →
      (M₁ : ℤ) = 2 * (n : ℤ) - 2 * (a : ℤ) ∧
      (M₂ : ℤ) = 2 * (n : ℤ) - (2 * (e : ℤ) + 1) ∧
      Even M₁ ∧ Odd M₂) := by
  let n := multiplicativeConductorExponent F lambda
  let r₁ := multiplicativeConductorExponent E₁ (normQuasiChar F E₁ lambda)
  let r₂ := multiplicativeConductorExponent E₂ (normQuasiChar F E₂ lambda)
  have hr₁ := multiplicativeConductorExponent_isConductor E₁ (normQuasiChar F E₁ lambda)
  have hr₂ := multiplicativeConductorExponent_isConductor E₂ (normQuasiChar F E₂ lambda)
  have hp₁ := quadraticPullbackConductors F E₁ ht₁ hres₁ hdeg₁ lambda
  have hp₂ := quadraticPullbackConductors F E₂ ht₂ hres₂ hdeg₂ lambda
  change (n ≤ 2 * a - 1 + 1 → r₁ ≤ 2 * a - 1 + 1) ∧
    (2 * a - 1 + 1 < n → (r₁ : ℤ) = 2 * (n : ℤ) - (2 * a - 1 + 1 : ℕ)) at hp₁
  change (n ≤ 2 * e + 1 → r₂ ≤ 2 * e + 1) ∧
    (2 * e + 1 < n → (r₂ : ℤ) = 2 * (n : ℤ) - (2 * e + 1 : ℕ)) at hp₂
  rw [show 2 * a - 1 + 1 = 2 * a by omega] at hp₁
  push_cast at hp₁ hp₂
  dsimp only
  constructor
  · intro hn
    have hsmall₁ : r₁ < 4 * e + 1 := by
      by_cases h : n ≤ 2 * a
      · have := hp₁.1 h; omega
      · have := hp₁.2 (by omega); omega
    have hsmall₂ : r₂ < 2 * e + 2 * a := by
      by_cases h : n ≤ 2 * e + 1
      · have := hp₂.1 h; omega
      · have := hp₂.2 (by omega); omega
    have hM₁ := multiplicativeConductorExponent_eq_of_isConductor E₁ _
      (hc₁.mul_of_gt hr₁ hsmall₁)
    have hM₂ := multiplicativeConductorExponent_eq_of_isConductor E₂ _
      (hc₂.mul_of_gt hr₂ hsmall₂)
    refine ⟨hM₁, hM₂, ?_, ?_⟩
    · rw [hM₁]; exact ⟨2 * e, by omega⟩
    · rw [hM₂]; exact ⟨e + a, by omega⟩
  · intro hn
    have hhigh₁ := hp₁.2 (by omega)
    have hhigh₂ := hp₂.2 (by omega)
    have hlarge₁ : 4 * e + 1 < r₁ := by omega
    have hlarge₂ : 2 * e + 2 * a < r₂ := by omega
    have hM₁ := multiplicativeConductorExponent_eq_of_isConductor E₁ _
      (hc₁.mul_of_lt hr₁ hlarge₁)
    have hM₂ := multiplicativeConductorExponent_eq_of_isConductor E₂ _
      (hc₂.mul_of_lt hr₂ hlarge₂)
    rw [hM₁, hM₂]
    refine ⟨hhigh₁, hhigh₂, ?_, ?_⟩
    · exact ⟨n - a, by omega⟩
    · exact ⟨n - e - 1, by omega⟩

/-- Any two isomorphisms from a group of order two agree. -/
private theorem quadraticEquiv_unique
    {G H : Type*} [Group G] [Group H] (hc : Nat.card G = 2)
    (f g : G ≃* H) : f = g := by
  apply MulEquiv.ext
  intro x
  by_cases hx : x = 1
  · simp [hx]
  · have hcard : Nat.card H = 2 := (Nat.card_congr f.toEquiv).symm.trans hc
    have hu := (Nat.card_eq_two_iff' (1 : H)).mp hcard
    exact hu.unique ((map_ne_one_iff f f.injective).2 hx) ((map_ne_one_iff g g.injective).2 hx)

section Pair
variable {F E₁ E₂ K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field E₁] [ValuativeRel E₁] [TopologicalSpace E₁] [IsNonarchimedeanLocalField E₁]
  [Field E₂] [ValuativeRel E₂] [TopologicalSpace E₂] [IsNonarchimedeanLocalField E₂]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F E₁] [Algebra F E₂] [Algebra F K] [Algebra E₁ K] [Algebra E₂ K]
  [IsScalarTower F E₁ K] [IsScalarTower F E₂ K]
  [ValuativeExtension F E₁] [ValuativeExtension F E₂]
  [ValuativeExtension E₁ K] [ValuativeExtension E₂ K] [ValuativeExtension F K]
  [Module.Finite F E₁] [Module.Finite F E₂]
  [Module.Finite E₁ K] [Module.Finite E₂ K] [Module.Finite F K]
  [PrimeCyclicExtension F E₂]

omit [ValuativeExtension F K] [Module.Finite F K] in
private theorem pairRealization
    (hdeg₂ : Module.finrank F E₂ = 2)
    (theta₁ chi₁ : ContinuousQuasiChar E₁)
    (theta₂ chi₂ : ContinuousQuasiChar E₂)
    (hc : normQuasiChar E₁ K chi₁ = normQuasiChar E₂ K chi₂)
    (ht : normQuasiChar E₁ K theta₁ = normQuasiChar E₂ K theta₂)
    (Dt₁ : Characters.ConjugateTwistData F E₁ K theta₁)
    (Dt₂ : Characters.ConjugateTwistData F E₂ K theta₂)
    (Dc₂ : Characters.ConjugateTwistData F E₂ K chi₂) :
    ∃ (lambda : ContinuousQuasiChar F) (sigma : Gal(E₁/F)),
      Basic.conjugateQuasiChar F E₁ sigma theta₁ = chi₁ * normQuasiChar F E₁ lambda ∧
      theta₂ = chi₂ * normQuasiChar F E₂ lambda := by
  have heq : Dt₂.quotientEquiv = Dc₂.quotientEquiv :=
    quadraticEquiv_unique ((IsGalois.card_aut_eq_finrank F E₂).trans hdeg₂) _ _
  have hinv (sigma : Gal(E₂/F)) (x : E₂ˣ) :
      (theta₂ / chi₂) (Units.map sigma.toMonoidHom x) = (theta₂ / chi₂) x := by
    have hq := congrArg (fun f : Gal(E₂/F) ≃* NormCharacter E₂ K =>
      (f sigma.symm).1) heq
    rw [Dt₂.quotient_eq, Dc₂.quotient_eq] at hq
    have hx := DFunLike.congr_fun hq x
    change theta₂ (Units.map sigma.toMonoidHom x) / theta₂ x =
      chi₂ (Units.map sigma.toMonoidHom x) / chi₂ x at hx
    change theta₂ (Units.map sigma.toMonoidHom x) / chi₂ (Units.map sigma.toMonoidHom x) =
      theta₂ x / chi₂ x
    apply (div_eq_div_iff_mul_eq_mul).2
    exact ((div_eq_div_iff_mul_eq_mul).1 hx).trans (mul_comm _ _)
  obtain ⟨lambda, hlambda⟩ := Local.invariantCharacter_descends F E₂ (theta₂ / chi₂) hinv
  have ht₂ : theta₂ = chi₂ * normQuasiChar F E₂ lambda := by
    rw [hlambda]; simp [div_eq_mul_inv]
  let target := chi₁ * normQuasiChar F E₁ lambda
  have htarget : normQuasiChar E₁ K target = normQuasiChar E₁ K theta₁ := by
    apply ContinuousMonoidHom.ext
    intro z
    have hcZ := DFunLike.congr_fun hc z
    have htZ := DFunLike.congr_fun ht z
    have htw : normUnits F E₁ (normUnits E₁ K z) =
        normUnits F E₂ (normUnits E₂ K z) :=
      Units.ext ((Basic.norm_tower (F := F) (L := E₁) (z : K)).trans
        (Basic.norm_tower (F := F) (L := E₂) (z : K)).symm)
    change chi₁ (normUnits E₁ K z) * lambda (normUnits F E₁ (normUnits E₁ K z)) =
      theta₁ (normUnits E₁ K z)
    change chi₁ (normUnits E₁ K z) = chi₂ (normUnits E₂ K z) at hcZ
    change theta₁ (normUnits E₁ K z) = theta₂ (normUnits E₂ K z) at htZ
    rw [hcZ, htw, htZ, ht₂]
    rfl
  let mu : NormCharacter E₁ K := ⟨target / theta₁, by
    apply ContinuousMonoidHom.ext
    intro z
    change target (normUnits E₁ K z) / theta₁ (normUnits E₁ K z) = 1
    rw [div_eq_one]
    exact DFunLike.congr_fun htarget z⟩
  obtain ⟨sigma, hsigma⟩ := Dt₁.quotientEquiv.surjective mu
  refine ⟨lambda, sigma, ?_, ht₂⟩
  rw [Dt₁.conjugate_eq_twist, hsigma]
  change theta₁ * (target / theta₁) = target
  simp [div_eq_mul_inv]

end Pair

/-- Total ramification descends to every intermediate field. This follows
already from norm transitivity applied to an element of order one. -/
private theorem lowerResidueDegree_one
    {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]
    (E : IntermediateField F K)
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeExtension F E] [ValuativeExtension E K]
    (hres : residueDegree F K = 1) : residueDegree F E = 1 := by
  obtain ⟨x, hx⟩ := exists_ord_eq K 1
  have h := congrArg (ord F) (Basic.norm_tower (F := F) (L := E) x)
  rw [ord_norm, ord_norm, ord_norm, hres, hx] at h
  have hmul : residueDegree F E * residueDegree E K = 1 := by
    have hz : residueDegree F E • residueDegree E K • (1 : ℤ) = 1 • (1 : ℤ) := by
      exact_mod_cast h
    have hz' : (residueDegree F E : ℤ) * (residueDegree E K : ℤ) = 1 := by
      simpa [nsmul_eq_mul] using hz
    exact_mod_cast hz'
  exact (mul_eq_one.mp hmul).1

/-- Distinct quadratic breaks force distinct lower norm subgroups. -/
private theorem quadraticNormRanges_ne
    (F E₁ E₂ : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Field E₁] [ValuativeRel E₁] [TopologicalSpace E₁] [IsNonarchimedeanLocalField E₁]
    [Field E₂] [ValuativeRel E₂] [TopologicalSpace E₂] [IsNonarchimedeanLocalField E₂]
    [Algebra F E₁] [ValuativeExtension F E₁] [Module.Finite F E₁]
    [Algebra F E₂] [ValuativeExtension F E₂] [Module.Finite F E₂]
    [PrimeCyclicExtension F E₁] [PrimeCyclicExtension F E₂]
    {t₁ t₂ : ℕ} (ht₁ : PrimeCyclicExtension.IsLowerBreak F E₁ t₁)
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F E₂ t₂)
    (hres₁ : residueDegree F E₁ = 1) (hres₂ : residueDegree F E₂ = 1)
    (hdeg₁ : Module.finrank F E₁ = 2) (hne : t₁ ≠ t₂) :
    (normUnits F E₁).range ≠ (normUnits F E₂).range := by
  obtain ⟨pi₁, hp₁, hg₁⟩ := monogenicUniformizer F E₁ hres₁
  obtain ⟨pi₂, hp₂, hg₂⟩ := monogenicUniformizer F E₂ hres₂
  have hcard : Nat.card (NormCharacter F E₁) = 2 :=
    (ramifiedNormCharacter_card F E₁ ht₁ hres₁ pi₁ hp₁ hg₁).trans hdeg₁
  obtain ⟨omega₁, ho₁, _⟩ := (Nat.card_eq_two_iff' (1 : NormCharacter F E₁)).mp hcard
  intro hrange
  let omega₂ : NormCharacter F E₂ := ⟨omega₁.1, by
    apply ContinuousMonoidHom.ext
    intro x
    change omega₁.1 (normUnits F E₂ x) = 1
    apply omega₁.eq_one_on_normRange
    rw [hrange]
    exact ⟨x, rfl⟩⟩
  have ho₂ : omega₂ ≠ 1 := by
    intro h
    exact ho₁ (Subtype.ext (congrArg (fun q : NormCharacter F E₂ => q.1) h))
  have h₁ := ramifiedNormCharacter_conductor F E₁ ht₁ hres₁ pi₁ hp₁ hg₁ omega₁ ho₁
  have h₂ := ramifiedNormCharacter_conductor F E₂ ht₂ hres₂ pi₂ hp₂ hg₂ omega₂ ho₂
  exact hne (Nat.add_right_cancel (h₁.unique h₂))

/-- In degree two the nonidentity conjugate quotient is exactly the
crossed lower norm character. -/
private theorem quadraticConjugateQuotient
    {F E J K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Field J] [ValuativeRel J] [TopologicalSpace J] [IsNonarchimedeanLocalField J]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F E] [Algebra F J] [Algebra F K] [Algebra E K] [Algebra J K]
    [IsScalarTower F E K] [IsScalarTower F J K]
    [ValuativeExtension F E] [ValuativeExtension F J] [ValuativeExtension E K]
    [Module.Finite F E] [Module.Finite F J] [Module.Finite E K] [Module.Finite J K]
    [PrimeCyclicExtension F E] [PrimeCyclicExtension F J] [PrimeCyclicExtension E K]
    (hE : Module.finrank F E = 2) (hJ : Module.finrank F J = 2)
    (hEK : Module.finrank E K = 2)
    (hne : (normUnits F E).range ≠ (normUnits F J).range)
    {theta : ContinuousQuasiChar E} (D : Characters.ConjugateTwistData F E K theta)
    (omegaJ : NormCharacter F J) (ho : omegaJ ≠ 1) :
    ∀ sigma : Gal(E/F), sigma ≠ 1 →
      Basic.conjugateQuasiChar F E sigma theta / theta = normQuasiChar F E omegaJ.1 := by
  let c := Characters.crossedNormEquivOfTowers F E J K Nat.prime_two hE hJ hEK hne
  have hcard : Nat.card (NormCharacter E K) = 2 :=
    (Nat.card_congr D.quotientEquiv.toEquiv).symm.trans
      ((IsGalois.card_aut_eq_finrank F E).trans hE)
  have hu := (Nat.card_eq_two_iff' (1 : NormCharacter E K)).mp hcard
  intro sigma hs
  have heq : D.quotientEquiv sigma = c omegaJ := hu.unique
    ((map_ne_one_iff D.quotientEquiv D.quotientEquiv.injective).2 hs)
    ((map_ne_one_iff c c.injective).2 ho)
  rw [← D.quotient_eq, heq]
  rfl

/-- Conjugation preserves the canonical conductor, including zero. -/
private theorem conductor_conjugate
    (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
    (sigma : Gal(E/F)) (theta : ContinuousQuasiChar E) :
    multiplicativeConductorExponent E (Basic.conjugateQuasiChar F E sigma theta) =
      multiplicativeConductorExponent E theta := by
  have hmem (rho : Gal(E/F)) (n : ℕ) (u : Eˣ) :
      Units.map rho.toMonoidHom u ∈ unitFiltration E n ↔ u ∈ unitFiltration E n := by
    cases n with
    | zero =>
      simp only [mem_unitFiltration_zero, Units.coe_map]
      change ord E (rho (u : E)) = 0 ↔ ord E (u : E) = 0
      rw [ord_galoisConjugate]
    | succ n =>
      simp only [mem_unitFiltration_succ, Units.coe_map]
      change CongruentAtDepth ((n + 1 : ℕ) : ℤ) (rho (u : E)) 1 ↔ _
      simp only [CongruentAtDepth]
      rw [show rho (u : E) - 1 = rho ((u : E) - 1) by simp, ord_galoisConjugate]
  have hc := multiplicativeConductorExponent_isConductor E theta
  apply multiplicativeConductorExponent_eq_of_isConductor E _
  constructor
  · intro u hu
    exact hc.trivial _ ((hmem sigma.symm _ u).2 hu)
  · intro r hr
    apply hc.minimal r
    intro u hu
    have h := hr (Units.map sigma.toMonoidHom u) ((hmem sigma r u).2 hu)
    have huval : Units.map sigma.symm.toMonoidHom (Units.map sigma.toMonoidHom u) = u := by
      apply Units.ext
      exact sigma.symm_apply_apply (u : E)
    change theta (Units.map sigma.symm.toMonoidHom (Units.map sigma.toMonoidHom u)) = 1 at h
    rwa [huval] at h

section Conjugation

variable {F E K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F E] [Algebra E K]
  [ValuativeExtension F E] [ValuativeExtension E K]
  [Module.Finite F E] [Module.Finite E K]

/-- The conjugate quotient is an upper norm character, so the pullback is unchanged. -/
private theorem normPullback_conjugate
    {theta : ContinuousQuasiChar E} (D : Characters.ConjugateTwistData F E K theta)
    (sigma : Gal(E/F)) :
    normQuasiChar E K (Basic.conjugateQuasiChar F E sigma theta) =
      normQuasiChar E K theta := by
  rw [D.conjugate_eq_twist]
  exact (congrArg (normQuasiChar E K) (mul_comm theta (D.quotientEquiv sigma).1)).trans
    (normQuasiChar_normCharacter_mul E K (D.quotientEquiv sigma) theta)

/-- A trace additive character is invariant under the conjugation change of variables. -/
private theorem localConstant_conjugate_tracePullback
    [Algebra.IsSeparable F E] (sigma : Gal(E/F)) (theta : ContinuousQuasiChar E)
    (psi : ContinuousAddChar F) (hpsi : psi ≠ 1) :
    localConstant E (Basic.conjugateQuasiChar F E sigma theta)
        (tracePullbackAddChar F E psi) =
      localConstant E theta (tracePullbackAddChar F E psi) := by
  apply Basic.localConstant_conjugate F E sigma theta _
    (Basic.tracePullbackAddChar_ne_one F E psi hpsi)
  intro x
  change psi (Algebra.trace F E (sigma x)) = psi (Algebra.trace F E x)
  rw [Basic.trace_conjugate]

end Conjugation

section Realization

-- Use the canonical structures already present in the public statement.
attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

/-- The two cyclic edges and upper degree of an actual quadratic intermediate field. -/
private class QuadraticTower (E : IntermediateField F K) : Prop where
  lower : PrimeCyclicExtension F E
  upper : PrimeCyclicExtension E K
  upper_degree : Module.finrank E K = 2

attribute [local instance] QuadraticTower.lower QuadraticTower.upper

private theorem quadraticTower
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (E : IntermediateField F K) (hE : Module.finrank F E = 2) :
    QuadraticTower E := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hdegree, hlower, hupper⟩ :=
    Basic.intermediateField_tower_compatible Nat.prime_two hG E hE
  exact ⟨PrimeCyclicExtension.ofCyclicPrimeExtension F E hlower,
    PrimeCyclicExtension.ofCyclicPrimeExtension E K hupper, hdegree⟩

/-- Quadratic conjugacy supplies the crossed quotients and one corrected restriction
for all three characters, together with the orbit data needed to realize the pair. -/
private theorem quadraticFamilyConjugacy
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (E₁ E₂ E₃ : IntermediateField F K)
    [QuadraticTower E₁] [QuadraticTower E₂] [QuadraticTower E₃]
    (hdeg₁ : Module.finrank F E₁ = 2) (hdeg₂ : Module.finrank F E₂ = 2)
    (hdeg₃ : Module.finrank F E₃ = 2)
    (hne₁₂ : (normUnits F E₁).range ≠ (normUnits F E₂).range)
    (hne₁₃ : (normUnits F E₁).range ≠ (normUnits F E₃).range)
    (theta₁ : ContinuousQuasiChar E₁) (theta₂ : ContinuousQuasiChar E₂)
    (theta₃ : ContinuousQuasiChar E₃) (Theta : ContinuousQuasiChar K)
    (htComp₁ : normQuasiChar E₁ K theta₁ = Theta)
    (htComp₂ : normQuasiChar E₂ K theta₂ = Theta)
    (htComp₃ : normQuasiChar E₃ K theta₃ = Theta)
    (hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Theta) :
    ∃ (_Dt₁ : Characters.ConjugateTwistData F E₁ K theta₁)
      (_Dt₂ : Characters.ConjugateTwistData F E₂ K theta₂)
      (omega₁ : NormCharacter F E₁) (omega₂ : NormCharacter F E₂)
      (omega₃ : NormCharacter F E₃),
      omega₁ ≠ 1 ∧ omega₂ ≠ 1 ∧ omega₃ ≠ 1 ∧
      (∀ sigma : Gal(E₁/F), sigma ≠ 1 →
        Basic.conjugateQuasiChar F E₁ sigma theta₁ / theta₁ = normQuasiChar F E₁ omega₂.1) ∧
      (∀ sigma : Gal(E₂/F), sigma ≠ 1 →
        Basic.conjugateQuasiChar F E₂ sigma theta₂ / theta₂ = normQuasiChar F E₂ omega₁.1) ∧
      (∀ sigma : Gal(E₃/F), sigma ≠ 1 →
        Basic.conjugateQuasiChar F E₃ sigma theta₃ / theta₃ = normQuasiChar F E₃ omega₁.1) ∧
      Characters.restrictQuasiChar F E₁ theta₁ * omega₁.1 =
        Characters.restrictQuasiChar F E₂ theta₂ * omega₂.1 ∧
      Characters.restrictQuasiChar F E₃ theta₃ * omega₃.1 =
        Characters.restrictQuasiChar F E₂ theta₂ * omega₂.1 := by
  obtain ⟨⟨Dt₁⟩, ⟨Dt₂⟩, hdet₁₂, _, hquadratic₁₂⟩ :=
    Characters.conjugacy Nat.prime_two hG E₁ E₂ hdeg₁ hdeg₂ hne₁₂
      theta₁ theta₂ Theta htComp₁ htComp₂ hprimitive
  obtain ⟨_, ⟨Dt₃⟩, hdet₁₃, _, hquadratic₁₃⟩ :=
    Characters.conjugacy Nat.prime_two hG E₁ E₃ hdeg₁ hdeg₃ hne₁₃
      theta₁ theta₃ Theta htComp₁ htComp₃ hprimitive
  obtain ⟨omega₁, omega₂, ho₁, ho₂, he₁, he₂⟩ := hquadratic₁₂ rfl
  obtain ⟨_, omega₃, _, ho₃, _, he₃⟩ := hquadratic₁₃ rfl
  rw [he₁, he₂] at hdet₁₂
  rw [he₁, he₃] at hdet₁₃
  exact ⟨Dt₁, Dt₂, omega₁, omega₂, omega₃, ho₁, ho₂, ho₃,
    quadraticConjugateQuotient hdeg₁ hdeg₂ (QuadraticTower.upper_degree (E := E₁))
      hne₁₂ Dt₁ omega₂ ho₂,
    quadraticConjugateQuotient hdeg₂ hdeg₁ (QuadraticTower.upper_degree (E := E₂))
      hne₁₂.symm Dt₂ omega₁ ho₁,
    quadraticConjugateQuotient hdeg₃ hdeg₁ (QuadraticTower.upper_degree (E := E₃))
      hne₁₃.symm Dt₃ omega₁ ho₁,
    hdet₁₂, hdet₁₃.symm.trans hdet₁₂⟩

set_option maxHeartbeats 2000000 in
/-- **Paper Lemma 12.7 (`D:MX:realize`).** Every actual primitive compatible
family admits the common base twist of cores constructed by `models`.
The first character is replaced only by an actual conjugate, preserving
its canonical local constant and its norm pullback. Corrected restrictions
agree on all three fields. The exact conductor threshold and both parity
patterns are asserted for the original given characters.

The aligned origin and lower-character data are precisely the constructed
inputs of `models`; no realization or commutator identity is assumed. -/
theorem twist
    {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {pi : ringOfIntegers F} {e a b : ℕ}
    {u0 w0 : (ringOfIntegers F)ˣ} {s R0 : K}
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = 2)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (ha : 1 ≤ a) (hae : a ≤ e) (hb : b = 2 * e - 2 * a + 1)
    (D : AlignmentData pi e a b u0 w0 s R0)
    (O : OriginData D) :
    letI : ValuativeRel D.firstField :=
      Basic.intermediateFieldValuativeRel D.firstField
    letI : TopologicalSpace D.firstField :=
      Basic.intermediateFieldTopology D.firstField
    letI : ValuativeRel D.secondField :=
      Basic.intermediateFieldValuativeRel D.secondField
    letI : TopologicalSpace D.secondField :=
      Basic.intermediateFieldTopology D.secondField
    letI : ValuativeRel D.thirdField :=
      Basic.intermediateFieldValuativeRel D.thirdField
    letI : TopologicalSpace D.thirdField :=
      Basic.intermediateFieldTopology D.thirdField
    let E₁ := Basic.intermediateField_tower_compatible Nat.prime_two hG
      D.firstField O.first_degree
    let E₂ := Basic.intermediateField_tower_compatible Nat.prime_two hG
      D.secondField O.second_degree
    let E₃ := Basic.intermediateField_tower_compatible Nat.prime_two hG
      D.thirdField O.third_degree
    letI : IsNonarchimedeanLocalField D.firstField := E₁.1
    letI : Module.Free F D.firstField := E₁.2.1
    letI : Module.Finite F D.firstField := E₁.2.2.1
    letI : Module.Free D.firstField K := E₁.2.2.2.1
    letI : Module.Finite D.firstField K := E₁.2.2.2.2.1
    letI : IsScalarTower F D.firstField K := E₁.2.2.2.2.2.1
    letI : ValuativeExtension F D.firstField := E₁.2.2.2.2.2.2.1
    letI : ValuativeExtension D.firstField K := E₁.2.2.2.2.2.2.2.1
    letI : CyclicPrimeExtension F D.firstField :=
      E₁.2.2.2.2.2.2.2.2.2.2.2.1
    letI : CyclicPrimeExtension D.firstField K :=
      E₁.2.2.2.2.2.2.2.2.2.2.2.2
    letI : IsNonarchimedeanLocalField D.secondField := E₂.1
    letI : Module.Free F D.secondField := E₂.2.1
    letI : Module.Finite F D.secondField := E₂.2.2.1
    letI : Module.Free D.secondField K := E₂.2.2.2.1
    letI : Module.Finite D.secondField K := E₂.2.2.2.2.1
    letI : IsScalarTower F D.secondField K := E₂.2.2.2.2.2.1
    letI : ValuativeExtension F D.secondField := E₂.2.2.2.2.2.2.1
    letI : ValuativeExtension D.secondField K := E₂.2.2.2.2.2.2.2.1
    letI : CyclicPrimeExtension F D.secondField :=
      E₂.2.2.2.2.2.2.2.2.2.2.2.1
    letI : CyclicPrimeExtension D.secondField K :=
      E₂.2.2.2.2.2.2.2.2.2.2.2.2
    letI : IsNonarchimedeanLocalField D.thirdField := E₃.1
    letI : Module.Free F D.thirdField := E₃.2.1
    letI : Module.Finite F D.thirdField := E₃.2.2.1
    letI : Module.Free D.thirdField K := E₃.2.2.2.1
    letI : Module.Finite D.thirdField K := E₃.2.2.2.2.1
    letI : IsScalarTower F D.thirdField K := E₃.2.2.2.2.2.1
    letI : ValuativeExtension F D.thirdField := E₃.2.2.2.2.2.2.1
    letI : ValuativeExtension D.thirdField K := E₃.2.2.2.2.2.2.2.1
    letI : CyclicPrimeExtension F D.thirdField :=
      E₃.2.2.2.2.2.2.2.2.2.2.2.1
    letI : CyclicPrimeExtension D.thirdField K :=
      E₃.2.2.2.2.2.2.2.2.2.2.2.2
    ∀ (_htLower₁ : PrimeCyclicExtension.IsLowerBreak F D.firstField
        (2 * a - 1))
      (_htLower₂ : PrimeCyclicExtension.IsLowerBreak F D.secondField (2 * e))
      (_htLower₃ : PrimeCyclicExtension.IsLowerBreak F D.thirdField (2 * e))
      (_ht₁ : PrimeCyclicExtension.IsLowerBreak D.firstField K
        (4 * e - 2 * a + 1))
      (_ht₂ : PrimeCyclicExtension.IsLowerBreak D.secondField K (2 * a - 1))
      (_ht₃ : PrimeCyclicExtension.IsLowerBreak D.thirdField K (2 * a - 1))
      (tau₁ : NormCharacter F D.firstField)
      (tau₂ : NormCharacter F D.secondField)
      (tau₃ : NormCharacter F D.thirdField) (_htau₃ : tau₃ ≠ 1)
      (PsiF : ContinuousAddChar F)
      (_H : LowerCharacterData F D.firstField D.secondField D.thirdField
        a e ha tau₁ tau₂ tau₃ PsiF D.beta1 D.beta2 D.beta3
        D.h1 D.h2 D.h3)
      (theta₁ : ContinuousQuasiChar D.firstField)
      (theta₂ : ContinuousQuasiChar D.secondField)
      (theta₃ : ContinuousQuasiChar D.thirdField) (Theta : ContinuousQuasiChar K)
      (_htComp₁ : normQuasiChar D.firstField K theta₁ = Theta)
      (_htComp₂ : normQuasiChar D.secondField K theta₂ = Theta)
      (_htComp₃ : normQuasiChar D.thirdField K theta₃ = Theta)
      (_hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Theta)
      (psiF : ContinuousAddChar F) (_hpsi : psiF ≠ 1),
      ∃ (chi₁ : ContinuousQuasiChar D.firstField)
        (chi₂ : ContinuousQuasiChar D.secondField)
        (chi₃ : ContinuousQuasiChar D.thirdField),
        IsMultiplicativeConductor D.firstField chi₁ (4 * e + 1) ∧
        IsMultiplicativeConductor D.secondField chi₂ (2 * e + 2 * a) ∧
        IsMultiplicativeConductor D.thirdField chi₃ (2 * e + 2 * a) ∧
        normQuasiChar D.firstField K chi₁ = normQuasiChar D.secondField K chi₂ ∧
        normQuasiChar D.thirdField K chi₃ = normQuasiChar D.secondField K chi₂ ∧
        (¬ ∃ lambda : ContinuousQuasiChar F,
          normQuasiChar F K lambda = normQuasiChar D.secondField K chi₂) ∧
        (∀ u : unitFiltration D.firstField (2 * e + 1),
          chi₁ (u : D.firstFieldˣ) = corePhaseValue D.firstField
            (tracePullbackAddChar F D.firstField PsiF) D.a1 (u : D.firstFieldˣ)) ∧
        (∀ u : unitFiltration D.secondField (e + a),
          chi₂ (u : D.secondFieldˣ) = corePhaseValue D.secondField
            (tracePullbackAddChar F D.secondField PsiF) D.a2 (u : D.secondFieldˣ)) ∧
        (∀ u : unitFiltration D.thirdField (e + a),
          chi₃ (u : D.thirdFieldˣ) = corePhaseValue D.thirdField
            (tracePullbackAddChar F D.thirdField PsiF) D.a3 (u : D.thirdFieldˣ)) ∧
        ∃ (lambda : ContinuousQuasiChar F) (sigma₁ : Gal(D.firstField/F))
          (omega₁ : NormCharacter F D.firstField)
          (omega₂ : NormCharacter F D.secondField)
          (omega₃ : NormCharacter F D.thirdField),
          omega₁ ≠ 1 ∧ omega₂ ≠ 1 ∧ omega₃ ≠ 1 ∧
          (∀ sigma : Gal(D.firstField/F), sigma ≠ 1 →
            Basic.conjugateQuasiChar F D.firstField sigma theta₁ / theta₁ =
              normQuasiChar F D.firstField omega₂.1) ∧
          (∀ sigma : Gal(D.secondField/F), sigma ≠ 1 →
            Basic.conjugateQuasiChar F D.secondField sigma theta₂ / theta₂ =
              normQuasiChar F D.secondField omega₁.1) ∧
          (∀ sigma : Gal(D.thirdField/F), sigma ≠ 1 →
            Basic.conjugateQuasiChar F D.thirdField sigma theta₃ / theta₃ =
              normQuasiChar F D.thirdField omega₁.1) ∧
          Characters.restrictQuasiChar F D.firstField theta₁ * omega₁.1 =
            Characters.restrictQuasiChar F D.secondField theta₂ * omega₂.1 ∧
          Characters.restrictQuasiChar F D.thirdField theta₃ * omega₃.1 =
            Characters.restrictQuasiChar F D.secondField theta₂ * omega₂.1 ∧
          Basic.conjugateQuasiChar F D.firstField sigma₁ theta₁ =
            chi₁ * normQuasiChar F D.firstField lambda ∧
          theta₂ = chi₂ * normQuasiChar F D.secondField lambda ∧
          normQuasiChar D.firstField K
            (Basic.conjugateQuasiChar F D.firstField sigma₁ theta₁) = Theta ∧
          localConstant D.firstField (chi₁ * normQuasiChar F D.firstField lambda)
              (tracePullbackAddChar F D.firstField psiF) =
            localConstant D.firstField theta₁ (tracePullbackAddChar F D.firstField psiF) ∧
          localConstant D.secondField (chi₂ * normQuasiChar F D.secondField lambda)
              (tracePullbackAddChar F D.secondField psiF) =
            localConstant D.secondField theta₂ (tracePullbackAddChar F D.secondField psiF) ∧
          (let n := multiplicativeConductorExponent F lambda
           let M₁ := multiplicativeConductorExponent D.firstField theta₁
           let M₂ := multiplicativeConductorExponent D.secondField theta₂
           (n ≤ 2 * e + a → M₁ = 4 * e + 1 ∧ M₂ = 2 * e + 2 * a ∧
             Odd M₁ ∧ Even M₂) ∧
           (2 * e + a + 1 ≤ n →
             (M₁ : ℤ) = 2 * (n : ℤ) - 2 * (a : ℤ) ∧
             (M₂ : ℤ) = 2 * (n : ℤ) - (2 * (e : ℤ) + 1) ∧
             Even M₁ ∧ Odd M₂)) := by
  dsimp only
  letI := quadraticTower hG D.firstField O.first_degree
  letI := quadraticTower hG D.secondField O.second_degree
  letI := quadraticTower hG D.thirdField O.third_degree
  intro htLower₁ htLower₂ htLower₃ ht₁ ht₂ ht₃ tau₁ tau₂ tau₃ htau₃ PsiF H
    theta₁ theta₂ theta₃ Theta htComp₁ htComp₂ htComp₃ hprimitive psiF hpsi
  classical
  obtain ⟨chi₁, chi₂, chi₃, hc₁, hc₂, hc₃, hcComp₁, hcComp₃,
    hcPrimitive, hR₁, hR₂, hR₃⟩ :=
    models hG hres hchar htwo ha hae hb D O htLower₁ htLower₂ htLower₃
      ht₁ ht₂ ht₃ tau₁ tau₂ tau₃ htau₃ PsiF H
  have hres₁ := lowerResidueDegree_one D.firstField hres
  have hres₂ := lowerResidueDegree_one D.secondField hres
  have hres₃ := lowerResidueDegree_one D.thirdField hres
  have hne₁₂ := quadraticNormRanges_ne F D.firstField D.secondField htLower₁ htLower₂
    hres₁ hres₂ O.first_degree (by omega)
  have hne₁₃ := quadraticNormRanges_ne F D.firstField D.thirdField htLower₁ htLower₃
    hres₁ hres₃ O.first_degree (by omega)
  obtain ⟨Dt₁, Dt₂, omega₁, omega₂, omega₃, ho₁, ho₂, ho₃,
    hquot₁, hquot₂, hquot₃, hdet₁₂, hdet₃₂⟩ :=
    quadraticFamilyConjugacy hG D.firstField D.secondField D.thirdField
      O.first_degree O.second_degree O.third_degree hne₁₂ hne₁₃
      theta₁ theta₂ theta₃ Theta htComp₁ htComp₂ htComp₃ hprimitive
  obtain ⟨_, ⟨Dc₂⟩, _⟩ :=
    Characters.conjugacy Nat.prime_two hG D.firstField D.secondField
      O.first_degree O.second_degree hne₁₂ chi₁ chi₂
      (normQuasiChar D.secondField K chi₂) hcComp₁ rfl hcPrimitive
  obtain ⟨lambda, sigma₁, hreal₁, hreal₂⟩ := pairRealization O.second_degree
    theta₁ chi₁ theta₂ chi₂ hcComp₁ (htComp₁.trans htComp₂.symm) Dt₁ Dt₂ Dc₂
  refine ⟨chi₁, chi₂, chi₃, hc₁, hc₂, hc₃, hcComp₁, hcComp₃,
    hcPrimitive, hR₁, hR₂, hR₃, lambda, sigma₁, omega₁, omega₂, omega₃,
    ho₁, ho₂, ho₃, hquot₁, hquot₂, hquot₃, hdet₁₂, hdet₃₂,
    hreal₁, hreal₂, ?_, ?_, ?_, ?_⟩
  · exact (normPullback_conjugate Dt₁ sigma₁).trans htComp₁
  · rw [← hreal₁]
    exact localConstant_conjugate_tracePullback sigma₁ theta₁ psiF hpsi
  · rw [← hreal₂]
  · have hconductors := twist_conductors F D.firstField D.secondField ha hae
      htLower₁ htLower₂ hres₁ hres₂ O.first_degree O.second_degree chi₁ chi₂ hc₁ hc₂ lambda
    rw [← hreal₁, ← hreal₂, conductor_conjugate] at hconductors
    exact hconductors

end Realization

end
end LanglandsSecondMainLemma.Dyadic.Maximal
