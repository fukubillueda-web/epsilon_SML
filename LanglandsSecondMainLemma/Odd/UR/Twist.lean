import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Odd.UR.Models
import LanglandsSecondMainLemma.Characters.Conjugacy

/-!
# Odd / UR / Twist

Paper: `O:I:actualtwist`, lines 1388--1414, in the local-field setup
1060--1128. The critical conductor is handled by the actual conjugation
orbit and FML's no-cancellation theorem.
-/

namespace LanglandsSecondMainLemma.Odd.UR

noncomputable section
open LanglandsFirstMainLemma

section ConjugateConductors
variable (F U : Type) [Field F] [Field U] [Algebra F U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeExtension F U] [Module.Finite F U] [IsGalois F U]

omit [IsGalois F U] in
private theorem automorphism_mem_units (g : Gal(U/F)) (n : ℕ) (u : Uˣ) :
    Units.map g.toMonoidHom u ∈ unitFiltration U n ↔ u ∈ unitFiltration U n := by
  cases n with
  | zero =>
    simp only [mem_unitFiltration_zero, Units.coe_map]
    change ord U (g (u : U)) = 0 ↔ _
    rw [ord_galoisConjugate]
  | succ n =>
    simp only [mem_unitFiltration_succ, Units.coe_map, CongruentAtDepth]
    change _ ≤ ord U (g (u : U) - 1) ↔ _
    rw [show g (u : U) - 1 = g ((u : U) - 1) by simp, ord_galoisConjugate]

/-- Conjugation preserves the exact conductor, including depth zero. -/
theorem conjugate_conductor (g : Gal(U/F)) (chi : ContinuousQuasiChar U)
    {m : ℕ} (hchi : IsMultiplicativeConductor U chi m) :
    IsMultiplicativeConductor U (Basic.conjugateQuasiChar F U g chi) m := by
  refine ⟨?_, ?_⟩
  · intro u hu
    exact hchi.trivial _ ((automorphism_mem_units F U g.symm m u).2 hu)
  · intro r hr
    apply hchi.minimal r
    intro u hu
    have hv := hr (Units.map g.toMonoidHom u)
      ((automorphism_mem_units F U g r u).2 hu)
    have he : Units.map g.symm.toMonoidHom (Units.map g.toMonoidHom u) = u := by
      apply Units.ext
      exact g.symm_apply_apply (u : U)
    change chi (Units.map g.symm.toMonoidHom (Units.map g.toMonoidHom u)) = 1 at hv
    rwa [he] at hv

/-- A commutator cannot have larger conductor than its original character. -/
theorem commutator_conductor_le (g : Gal(U/F)) (chi tau : ContinuousQuasiChar U)
    {m T : ℕ} (hchi : IsMultiplicativeConductor U chi m)
    (htau : IsMultiplicativeConductor U tau T)
    (hcomm : Basic.conjugateQuasiChar F U g chi / chi = tau) : T ≤ m := by
  have hc := (conjugate_conductor F U g chi hchi).mul_conductor_le_max hchi.inv
    (show IsMultiplicativeConductor U
      (Basic.conjugateQuasiChar F U g chi * chi⁻¹) T by
      simpa only [← div_eq_mul_inv, hcomm] using htau)
  simpa using hc
end ConjugateConductors

section Descent
variable (F U : Type) [Field F] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U]
  [PrimeCyclicExtension F U]

/-- Matching the actual commutator is sufficient for continuous norm descent
of the quotient. The character on the norm image is extended by Hilbert 90. -/
theorem common_twist_of_commutator (phi : Gal(U/F))
    (hgen : ∀ g : Gal(U/F), g ∈ Subgroup.zpowers phi)
    (theta chi : ContinuousQuasiChar U)
    (hcomm : Basic.conjugateQuasiChar F U phi theta / theta =
      Basic.conjugateQuasiChar F U phi chi / chi) :
    ∃ lambda : ContinuousQuasiChar F, theta = chi * normQuasiChar F U lambda := by
  have hgen' : ∀ g : Gal(U/F), g ∈ Subgroup.zpowers phi.symm := by
    change ∀ g : Gal(U/F), g ∈ Subgroup.zpowers phi⁻¹
    simpa only [Subgroup.zpowers_inv] using hgen
  have hfixed := invariant_on_kernel_of_commutator F U phi.symm hgen'
    (theta / chi).toMonoidHom (1 : Uˣ →* ℂˣ) (by intros; rfl) (by
      intro x
      have hx := DFunLike.congr_fun hcomm x
      change theta (Units.map phi.symm.toMonoidHom x) / theta x =
        chi (Units.map phi.symm.toMonoidHom x) / chi x at hx
      change (theta (Units.map phi.symm.toMonoidHom x) /
        chi (Units.map phi.symm.toMonoidHom x)) / (theta x / chi x) = 1
      apply div_eq_one.mpr
      apply div_eq_div_iff_mul_eq_mul.mpr
      simpa only [mul_comm] using div_eq_div_iff_mul_eq_mul.mp hx)
  obtain ⟨lambda, hlambda⟩ := Local.invariantCharacter_descends F U (theta / chi)
    (fun g x => hfixed g x rfl)
  refine ⟨lambda, ?_⟩
  rw [hlambda]
  simp [div_eq_mul_inv]

/-- Unramified norm pullback determines the common twist's conductor. -/
theorem common_twist_conductor (hunr : ramificationIndex F U = 1)
    (theta chi : ContinuousQuasiChar U) (lambda : ContinuousQuasiChar F)
    {T m : ℕ} (hchi : IsMultiplicativeConductor U chi T)
    (htheta : IsMultiplicativeConductor U theta m) (hle : T ≤ m)
    (heq : theta = chi * normQuasiChar F U lambda) :
    multiplicativeConductorExponent F lambda ≤ m ∧
      (T < m → IsMultiplicativeConductor F lambda m) := by
  let n := multiplicativeConductorExponent F lambda
  have hn := multiplicativeConductorExponent_isConductor F lambda
  have hnU := (unramified_multiplicativeConductor_compNorm F U hunr lambda n).2 hn
  have hquot : normQuasiChar F U lambda = theta * chi⁻¹ := by
    rw [heq]; simp [mul_assoc]
  have hnU' : IsMultiplicativeConductor U (theta * chi⁻¹) n := hquot ▸ hnU
  have hnm : n ≤ m := by
    simpa only [max_eq_left hle] using htheta.mul_conductor_le_max hchi.inv hnU'
  refine ⟨hnm, ?_⟩
  intro hlt
  have he := hnU'.unique (htheta.mul_of_gt hchi.inv hlt)
  exact he ▸ hn
end Descent

section Orbit
variable (F U K : Type) [Field F] [Field U] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F U] [Algebra U K] [Algebra F K] [IsScalarTower F U K]
  [ValuativeExtension F U] [ValuativeExtension U K]
  [Module.Finite F U] [Module.Finite U K] [IsGalois F U]

/-- Every upper norm-character twist has the original exact conductor.
This is the critical no-drop input, proved from the full conjugation orbit. -/
theorem orbit_twist_conductor (theta : ContinuousQuasiChar U)
    (D : Characters.ConjugateTwistData F U K theta)
    {m : ℕ} (hm : IsMultiplicativeConductor U theta m)
    (mu : NormCharacter U K) : IsMultiplicativeConductor U (mu.1 * theta) m := by
  obtain ⟨g, hg⟩ := D.quotientEquiv.surjective mu
  have he : Basic.conjugateQuasiChar F U g theta = mu.1 * theta := by
    rw [D.conjugate_eq_twist, hg]
    apply ContinuousMonoidHom.ext
    intro x
    exact mul_comm (theta x) (mu.1 x)
  exact he ▸ conjugate_conductor F U g theta hm

/-- The full orbit gives `T+p*h` upstairs, including the critical endpoint. -/
theorem orbit_pullback_conductor [PrimeCyclicExtension U K]
    {p t h : ℕ} (hp : p.Prime) (hdegree : Module.finrank U K = p)
    (ht : PrimeCyclicExtension.IsLowerBreak U K t) (hres : residueDegree U K = 1)
    (theta : ContinuousQuasiChar U) (D : Characters.ConjugateTwistData F U K theta)
    (hm : IsMultiplicativeConductor U theta (t + 1 + h)) :
    IsMultiplicativeConductor K (normQuasiChar U K theta) (t + 1 + p * h) := by
  obtain ⟨pi, hpi, hgen⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one U K hres
  let chiU : LocalQuasiCharData U := ⟨theta, t + 1 + h, hm⟩
  let chiK := canonicalLocalQuasiCharData K (normQuasiChar U K theta)
  have hformula := chiU.conductor_compNorm_eq_atOrAboveCritical_of_minimalOrbit
    U K ht hres pi hpi hgen chiK rfl (by dsimp [chiU]; omega) (by
      intro mu q hq
      exact le_of_eq ((orbit_twist_conductor F U K theta D hm mu).unique hq))
  have hcond : chiK.conductor = t + 1 + p * h := by
    dsimp only [chiU] at hformula
    rw [hdegree] at hformula
    have hp1 : 1 ≤ p := hp.one_lt.le
    push_cast [Nat.cast_sub hp1] at hformula
    exact_mod_cast (show (chiK.conductor : ℤ) = (t : ℤ) + 1 + (p : ℤ) * h by
      linear_combination hformula)
  exact hcond ▸ chiK.isConductor
end Orbit

section Absorption
variable (F E U K : Type) [Field F] [Field E] [Field U] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F E] [Algebra F U] [Algebra F K] [Algebra E K] [Algebra U K]
  [IsScalarTower F E K] [IsScalarTower F U K]
  [ValuativeExtension F E] [ValuativeExtension F U] [ValuativeExtension F K]
  [ValuativeExtension U K] [ValuativeExtension E K]
  [Module.Finite F E] [Module.Finite F U] [Module.Finite E K]
  [Module.Finite U K] [Module.Finite F K] [IsGalois F U]

/-- The discrepancy over `E` is an actual upper norm character, hence has
conductor zero. Its absorption retains the entire model unit chart. -/
theorem absorb_unramified_discrepancy
    {p T q : ℕ} (hq : 0 < q) (hT : 0 < T)
    (tau : ContinuousQuasiChar F) (Psi : ContinuousAddChar F) (c : F) (d : U)
    (M : CompatibleModels F E U K p T q hq tau Psi c d)
    (hunr : ramificationIndex E K = 1)
    (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
    (hc : normQuasiChar U K thetaU = normQuasiChar E K thetaE)
    (lambda : ContinuousQuasiChar F)
    (hU : thetaU = M.chiU * normQuasiChar F U lambda) :
    ∃ rho : NormCharacter E K,
      IsMultiplicativeConductor E rho.1 0 ∧
      thetaE = (M.chiE * rho.1) * normQuasiChar F E lambda ∧
      IsMultiplicativeConductor E (M.chiE * rho.1) T ∧
      (∀ z : lattice E (q : ℤ),
        (M.chiE * rho.1) (positiveUnitOfLattice E hq (-z)) =
          tracePullbackAddChar F E Psi (algebraMap F E c * truncatedLog p (z : E))) ∧
      normQuasiChar E K (M.chiE * rho.1) = normQuasiChar U K M.chiU := by
  let rho : NormCharacter E K := ⟨thetaE / (M.chiE * normQuasiChar F E lambda), by
    apply ContinuousMonoidHom.ext
    intro x
    have hactual := DFunLike.congr_fun hc x
    have hmodel := DFunLike.congr_fun M.compatible x
    have htwist := DFunLike.congr_fun hU (normUnits U K x)
    have hn : normUnits F U (normUnits U K x) = normUnits F E (normUnits E K x) := by
      apply Units.ext
      exact (Basic.norm_tower (F := F) (L := U) (K := K) (x : K)).trans
        (Basic.norm_tower (F := F) (L := E) (K := K) (x : K)).symm
    change thetaU (normUnits U K x) = thetaE (normUnits E K x) at hactual
    change M.chiU (normUnits U K x) = M.chiE (normUnits E K x) at hmodel
    change thetaU (normUnits U K x) = M.chiU (normUnits U K x) *
      lambda (normUnits F U (normUnits U K x)) at htwist
    change thetaE (normUnits E K x) /
      (M.chiE (normUnits E K x) * lambda (normUnits F E (normUnits E K x))) = 1
    rw [← hactual, htwist, hmodel, hn, div_self']⟩
  have hrho := unramifiedNormCharacter_conductor E K hunr rho
  refine ⟨rho, hrho, ?_, M.conductorE.mul_of_gt hrho hT, ?_, ?_⟩
  · apply ContinuousMonoidHom.ext
    intro x
    change thetaE x = (M.chiE x * (thetaE x /
      (M.chiE x * lambda (normUnits F E x)))) * lambda (normUnits F E x)
    symm
    calc
      _ = (thetaE x / (M.chiE x * lambda (normUnits F E x))) *
        (M.chiE x * lambda (normUnits F E x)) := by ac_rfl
      _ = thetaE x := div_mul_cancel _ _
  · intro z
    change M.chiE (positiveUnitOfLattice E hq (-z)) *
      rho.1 (positiveUnitOfLattice E hq (-z)) = _
    rw [hrho.trivial _ (unitFiltration_antitone E (Nat.zero_le q)
      (positiveUnitOfLattice E hq (-z)).property), mul_one, M.logE]
  · apply ContinuousMonoidHom.ext
    intro x
    change M.chiE (normUnits E K x) * rho.1 (normUnits E K x) =
      M.chiU (normUnits U K x)
    have hzero : rho.1 (normUnits E K x) = 1 := DFunLike.congr_fun rho.property x
    rw [hzero, mul_one]
    exact (DFunLike.congr_fun M.compatible x).symm
/-- All conclusions of the actual-common-twist proposition. `rho` records
precisely the allowed change of the ramified model's unramified value. -/
structure ActualTwist
    {p T q : ℕ} {hq : 0 < q}
    {tau : ContinuousQuasiChar F} {Psi : ContinuousAddChar F} {c : F} {d : U}
    (M : CompatibleModels F E U K p T q hq tau Psi c d)
    (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E) where
  lambda : ContinuousQuasiChar F
  rho : NormCharacter E K
  rho_conductor : IsMultiplicativeConductor E rho.1 0
  twistU : thetaU = M.chiU * normQuasiChar F U lambda
  twistE : thetaE = (M.chiE * rho.1) * normQuasiChar F E lambda
  adjusted_conductor : IsMultiplicativeConductor E (M.chiE * rho.1) T
  adjusted_log : ∀ z : lattice E (q : ℤ),
    (M.chiE * rho.1) (positiveUnitOfLattice E hq (-z)) =
      tracePullbackAddChar F E Psi (algebraMap F E c * truncatedLog p (z : E))
  adjusted_compatible : normQuasiChar E K (M.chiE * rho.1) = normQuasiChar U K M.chiU
  h : ℕ
  conductorU : IsMultiplicativeConductor U thetaU (T + h)
  conductorE : IsMultiplicativeConductor E thetaE (T + p * h)
  conductorK : IsMultiplicativeConductor K (normQuasiChar U K thetaU) (T + p * h)
  lambda_bound : multiplicativeConductorExponent F lambda ≤ T + h
  lambda_high : 0 < h → IsMultiplicativeConductor F lambda (T + h)
  orbit_conductor : ∀ mu : NormCharacter U K,
    IsMultiplicativeConductor U (mu.1 * thetaU) (T + h)

/-- Descent, unramified absorption, and the critical no-drop argument for
models whose commutator has been matched to the given pair. -/
theorem actualTwist_of_matched_models
    [PrimeCyclicExtension F U] [PrimeCyclicExtension U K]
    {p t T q : ℕ} (hp : p.Prime) (hq : 0 < q) (hT : T = t + 1)
    (hUK : Module.finrank U K = p)
    (htUK : PrimeCyclicExtension.IsLowerBreak U K t) (hresUK : residueDegree U K = 1)
    (hunrFU : ramificationIndex F U = 1) (hunrEK : ramificationIndex E K = 1)
    (tau : ContinuousQuasiChar F) (htau : IsMultiplicativeConductor F tau T)
    (Psi : ContinuousAddChar F) (c : F) (d : U)
    (M : CompatibleModels F E U K p T q hq tau Psi c d)
    (hgen : ∀ g : Gal(U/F), g ∈ Subgroup.zpowers M.phi)
    (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
    (hc : normQuasiChar U K thetaU = normQuasiChar E K thetaE)
    (D : Characters.ConjugateTwistData F U K thetaU)
    (hmatch : Basic.conjugateQuasiChar F U M.phi thetaU / thetaU = normQuasiChar F U tau) :
    Nonempty (ActualTwist F E U K M thetaU thetaE) := by
  subst T
  have hmodel : Basic.conjugateQuasiChar F U M.phi M.chiU / M.chiU =
      normQuasiChar F U tau := by
    apply ContinuousMonoidHom.ext
    exact M.commutator
  obtain ⟨lambda, hlambda⟩ := common_twist_of_commutator F U M.phi hgen
    thetaU M.chiU (hmatch.trans hmodel.symm)
  let m := multiplicativeConductorExponent U thetaU
  have hm := multiplicativeConductorExponent_isConductor U thetaU
  have hT : t + 1 ≤ m := commutator_conductor_le F U M.phi thetaU
    (normQuasiChar F U tau) hm
    ((unramified_multiplicativeConductor_compNorm F U hunrFU tau (t + 1)).2 htau) hmatch
  obtain ⟨h, heq⟩ := Nat.exists_eq_add_of_le hT
  have hm' : IsMultiplicativeConductor U thetaU (t + 1 + h) := heq ▸ hm
  have hK := orbit_pullback_conductor F U K hp hUK htUK hresUK thetaU D hm'
  have hE : IsMultiplicativeConductor E thetaE (t + 1 + p * h) :=
    (unramified_multiplicativeConductor_compNorm E K hunrEK thetaE _).1 (by
      change IsMultiplicativeConductor K (normQuasiChar E K thetaE) _
      rw [← hc]
      exact hK)
  obtain ⟨hbound, hhigh⟩ := common_twist_conductor F U hunrFU thetaU M.chiU lambda
    M.conductorU hm' (by omega) hlambda
  obtain ⟨rho, hrho, hthetaE, hadj, hlog, hcomp⟩ :=
    absorb_unramified_discrepancy F E U K hq (by omega) tau Psi c d M hunrEK
      thetaU thetaE hc lambda hlambda
  exact ⟨⟨lambda, rho, hrho, hlambda, hthetaE, hadj, hlog, hcomp,
    h, hm', hE, hK, hbound, fun hh => hhigh (by omega),
    orbit_twist_conductor F U K thetaU D hm'⟩⟩
end Absorption

section Frobenius
variable (F U : Type) [Field F] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U] [IsGalois F U]

/-- On an unramified edge the residue action determines the automorphism. -/
theorem unramified_residueAction_injective (hunr : ramificationIndex F U = 1) :
    Function.Injective (Ramification.residueAction (F := F) (K := U)) := by
  apply ((Nat.bijective_iff_surjective_and_card _).2
    ⟨Ramification.residueAction_surjective, ?_⟩).1
  letI : Module.Finite (ResidueField F) (ResidueField U) := Module.Finite.of_finite
  rw [IsGalois.card_aut_eq_finrank F U,
    IsGalois.card_aut_eq_finrank (ResidueField F) (ResidueField U),
    ← residueDegree_eq_finrank_residueField,
    finrank_eq_ramificationIndex_mul_residueDegree F U, hunr, one_mul]
end Frobenius

section GenuinePair
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] [Module.Free F K] in
private theorem twistField_degree {p : ℕ} (hp : p.Prime)
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p) :
    Module.finrank F (IntermediateField.fixedField H) = p := by
  have h := Module.finrank_mul_finrank F (IntermediateField.fixedField H) K
  rw [IntermediateField.finrank_fixedField_eq_card H, hH,
    ← IsGalois.card_aut_eq_finrank F K, Nat.card_congr (Classical.choice hG).toEquiv,
    Nat.card_prod] at h
  have hc : Nat.card (Multiplicative (ZMod p)) = p :=
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod p)
  rw [hc] at h
  exact Nat.mul_right_cancel hp.pos h

omit [Module.Free F K] in
private theorem twistField_primeCyclic {p : ℕ} (hp : p.Prime)
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p) :
    PrimeCyclicExtension F (IntermediateField.fixedField H) ∧
      PrimeCyclicExtension (IntermediateField.fixedField H) K := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hFL, hLK⟩ :=
    Basic.intermediateField_tower_compatible hp hG (IntermediateField.fixedField H)
      (twistField_degree hp hG H hH)
  exact ⟨PrimeCyclicExtension.ofCyclicPrimeExtension F _ hFL,
    PrimeCyclicExtension.ofCyclicPrimeExtension _ K hLK⟩

set_option maxHeartbeats 800000 in
/-- **Paper Proposition `O:I:actualtwist`.** Starting with the genuine
primitive compatible pair, choose the norm-character generator to match its
arithmetic-Frobenius commutator, construct the global logarithm models, and
remove a single continuous base twist. Only an unramified upper norm
character is absorbed in the `E` model. The conductors are `T+h` and
`T+p*h`, including `h=0`; all upper norm-character twists have the same
conductor. Both field characteristics and nonunitary characters are retained.

The scalar `alpha` normalizes the given additive character, and the returned
models retain the full `d^p P` and `c P` charts on the entire depth `q0`.
Neither a matched commutator nor a no-drop condition is an input. -/
theorem twist {p : ℕ} (hp : p.Prime)
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hI : Nat.card (Ramification.inertiaSubgroup (F := F) (K := K)) = p)
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p)
    (hne : H ≠ Ramification.inertiaSubgroup) (hchar : residueCharacteristic F = p)
    (s : OddURSetup hp hG hI H hH hne hchar)
    (psiF : ContinuousAddChar F) (hpsiF : psiF ≠ 1) :
    let U := UnramifiedField F K
    let E := RamifiedField F K H
    letI : ValuativeRel U := Basic.intermediateFieldValuativeRel U
    letI : TopologicalSpace U := Basic.intermediateFieldTopology U
    letI : IsNonarchimedeanLocalField U := Basic.intermediateField_localField U
    letI : ValuativeExtension F U := Basic.intermediateField_lowerValuativeExtension U
    letI : ValuativeExtension U K := Basic.intermediateField_upperValuativeExtension U
    letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E
    letI : TopologicalSpace E := Basic.intermediateFieldTopology E
    letI : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E
    letI : ValuativeExtension F E := Basic.intermediateField_lowerValuativeExtension E
    letI : ValuativeExtension E K := Basic.intermediateField_upperValuativeExtension E
    letI : PrimeCyclicExtension F U := (twistField_primeCyclic hp hG _ hI).1
    ∀ (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E),
      normQuasiChar U K thetaU = normQuasiChar E K thetaE →
      (¬ ∃ lambda : ContinuousQuasiChar F,
        normQuasiChar F K lambda = normQuasiChar U K thetaU) →
      ∃ (tau : NormCharacter F E) (alpha : Fˣ),
        tau ≠ 1 ∧ IsMultiplicativeConductor F tau.1 s.T ∧
        ord F (alpha : F) = ((-(canonicalLocalAddCharData F psiF hpsiF).conductor -
          (s.T : ℤ) : ℤ) : WithTop ℤ) ∧
        let Psi := scaleAddCharData F (canonicalLocalAddCharData F psiF hpsiF) alpha
        Psi.conductor = -(s.T : ℤ) ∧
        (∀ z : lattice F (s.q0 : ℤ), tau.1 (positiveUnitOfLattice F s.q0_pos (-z)) =
          Psi.character (truncatedLog p (z : F))) ∧
        ∃ M : CompatibleModels F E U K p s.T s.q0 s.q0_pos
            tau.1 Psi.character (s.c : F) (s.d : U),
          (Basic.conjugateQuasiChar F U M.phi thetaU / thetaU = normQuasiChar F U tau.1) ∧
          Nonempty (ActualTwist F E U K M thetaU thetaE) := by
  let U := UnramifiedField F K
  let E := RamifiedField F K H
  letI : ValuativeRel U := Basic.intermediateFieldValuativeRel U
  letI : TopologicalSpace U := Basic.intermediateFieldTopology U
  letI : IsNonarchimedeanLocalField U := Basic.intermediateField_localField U
  letI : ValuativeExtension F U := Basic.intermediateField_lowerValuativeExtension U
  letI : ValuativeExtension U K := Basic.intermediateField_upperValuativeExtension U
  letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E
  letI : TopologicalSpace E := Basic.intermediateFieldTopology E
  letI : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E
  letI : ValuativeExtension F E := Basic.intermediateField_lowerValuativeExtension E
  letI : ValuativeExtension E K := Basic.intermediateField_upperValuativeExtension E
  letI : PrimeCyclicExtension F U := (twistField_primeCyclic hp hG _ hI).1
  letI : PrimeCyclicExtension U K := (twistField_primeCyclic hp hG _ hI).2
  letI : PrimeCyclicExtension F E := (twistField_primeCyclic hp hG H hH).1
  letI : PrimeCyclicExtension E K := (twistField_primeCyclic hp hG H hH).2
  change ∀ (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E), _
  intro thetaU thetaE hc hprimitive
  have hFU : Module.finrank F U = p := twistField_degree hp hG _ hI
  have hFE : Module.finrank F E = p := twistField_degree hp hG H hH
  have hUK : Module.finrank U K = p := by
    change Module.finrank (IntermediateField.fixedField _) K = p
    rw [IntermediateField.finrank_fixedField_eq_card, hI]
  have hEK : Module.finrank E K = p := by
    change Module.finrank (IntermediateField.fixedField H) K = p
    rw [IntermediateField.finrank_fixedField_eq_card, hH]
  have hb : residueDegree F E = 1 ∧ ramificationIndex E K = 1 ∧
      PrimeCyclicExtension.IsLowerBreak F E s.t ∧
      PrimeCyclicExtension.IsLowerBreak U K s.t := by
    simpa only [Ramification.UnramifiedBaseChangeBreakPair, U, E,
      UnramifiedField, RamifiedField] using s.breaks
  have hunr : ramificationIndex F U = 1 :=
    ((Ramification.diamondBreaks hp hG hchar).2 hI).unramified_lower.1
  have hresUK : residueDegree U K = 1 := by
    obtain ⟨L, hL, hLres⟩ := Ramification.exists_inertiaUniformizer (F := F) (K := K)
    subst L
    exact hLres.1
  have hsep : (normUnits F U).range ≠ (normUnits F E).range :=
    (Ramification.normSeparation hp hG).unramified_lower hI H hH hne
  obtain ⟨⟨D⟩, _⟩ := Characters.conjugacy hp hG U E hFU hFE hsep
    thetaU thetaE (normQuasiChar U K thetaU) rfl hc.symm hprimitive
  -- A first model supplies the arithmetic Frobenius; only the second,
  -- matched model below enters the result.
  obtain ⟨alpha0, _, _, _, ⟨M0⟩⟩ := models hp hG hI H hH hne hchar s psiF hpsiF
  have htau0 : IsMultiplicativeConductor U (normQuasiChar F U s.tauF.1) s.T :=
    (unramified_multiplicativeConductor_compNorm F U hunr s.tauF.1 s.T).2 s.tauF_conductor
  have hphi0 : M0.phi ≠ 1 := by
    intro hz
    have hzero : normQuasiChar F U s.tauF.1 = 1 := by
      apply ContinuousMonoidHom.ext
      intro x
      have hx := M0.commutator x
      have hu : Units.map M0.phi.symm.toMonoidHom x = x := by rw [hz]; rfl
      rw [hu, div_self'] at hx
      exact hx.symm
    have hle : s.T ≤ 0 := htau0.minimal 0 (by
      intro u _; rw [hzero]; rfl)
    have := s.T_eq
    omega
  let e := Characters.crossedNormEquivOfTowers F U E K hp hFU hFE hUK hsep
  let tau : NormCharacter F E := e.symm (D.quotientEquiv M0.phi)
  have htau_ne : tau ≠ 1 := by
    intro hz
    have hzero : D.quotientEquiv M0.phi = 1 := by
      have he := e.apply_symm_apply (D.quotientEquiv M0.phi)
      change e tau = D.quotientEquiv M0.phi at he
      rw [hz, map_one] at he
      exact he.symm
    exact hphi0 (D.quotientEquiv.injective (hzero.trans (map_one _).symm))
  obtain ⟨piE, hpiE, hgenE⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one F E hb.1
  have htau : IsMultiplicativeConductor F tau.1 (s.t + 1) :=
    ramifiedNormCharacter_conductor F E hb.2.2.1 hb.1 piE hpiE hgenE tau htau_ne
  have hqeq : s.q0 = (s.t + 1) ⌈/⌉ p := by rw [s.q0_eq, s.T_eq]
  have hqt : s.q0 ≤ s.t := by
    rw [hqeq, ceilDiv_le_iff_le_mul hp.pos]
    have htpos := s.t_pos
    have hp2 := hp.two_le
    nlinarith
  have hcover : s.t + 1 ≤ p * s.q0 := by rw [hqeq]; exact le_smul_ceilDiv hp.pos
  let psi := canonicalLocalAddCharData F psiF hpsiF
  let tauData : LocalQuasiCharData F := ⟨tau.1, s.t + 1, htau⟩
  obtain ⟨alpha, halpha, _⟩ := enhancedCoefficient_exists_unique_mod F tauData psi p s.q0
    (-psi.conductor) hchar hp s.q0_pos (by dsimp [tauData]; omega) hcover rfl
    (by have := s.t_pos; dsimp [tauData]; omega) (by dsimp [tauData]; omega)
  let Psi := scaleAddCharData F psi alpha
  have halpha' : ord F (alpha : F) =
      ((-psi.conductor - (s.T : ℤ) : ℤ) : WithTop ℤ) := by
    simpa only [tauData, s.T_eq] using halpha.1
  have hn : Psi.conductor = -(s.T : ℤ) := by
    have ho : unitOrder F alpha = -psi.conductor - (s.T : ℤ) :=
      WithTop.coe_inj.mp ((ord_coe_eq_unitOrder F alpha).symm.trans halpha')
    dsimp only [Psi]
    rw [scaleAddCharData_conductor, ho]
    ring
  have hchart : ∀ z : lattice F (s.q0 : ℤ),
      tau.1 (positiveUnitOfLattice F s.q0_pos (-z)) =
        Psi.character (truncatedLog p (z : F)) := halpha.2
  have hPsi : IsAdditiveConductor F Psi.character (-((s.t + 1 : ℕ) : ℤ)) := by
    simpa only [hn, s.T_eq] using Psi.isConductor
  have hq : 0 < (s.t + 1) ⌈/⌉ p := hqeq ▸ s.q0_pos
  have hchartUnits := (one_sub_chart_iff_units F p s.q0 s.q0_pos tau.1 Psi.character 1).1
    (by simpa only [one_mul] using hchart)
  obtain ⟨M'⟩ := compatibleModels_of_normalized_data F E U K hp
    (by have := s.odd_prime; omega) s.t_pos hFE hFU hUK hEK hb.2.2.1 hb.2.2.2 hb.1
    hresUK hunr hb.2.1 hchar hsep hq tau htau_ne Psi.character hPsi (by
      rw [← hqeq]; simpa only [one_mul] using hchartUnits)
    s.c s.d s.artinSchreier.1 s.artinSchreier.2.2.1
  let M : CompatibleModels F E U K p s.T s.q0 s.q0_pos
      tau.1 Psi.character (s.c : F) (s.d : U) := by
    simpa only [s.T_eq, hqeq] using M'
  have hphi : M.phi = M0.phi := by
    apply unramified_residueAction_injective F U hunr
    apply AlgEquiv.ext
    intro x
    exact (M.frobenius x).trans (M0.frobenius x).symm
  have hmatch : Basic.conjugateQuasiChar F U M.phi thetaU / thetaU =
      normQuasiChar F U tau.1 := by
    rw [hphi, ← D.quotient_eq]
    exact (congrArg Subtype.val (e.apply_symm_apply (D.quotientEquiv M0.phi))).symm
  have hgen : ∀ g : Gal(U/F), g ∈ Subgroup.zpowers M.phi := by
    letI : Fact p.Prime := ⟨hp⟩
    intro g
    exact mem_zpowers_of_prime_card ((IsGalois.card_aut_eq_finrank F U).trans hFU)
      (hphi ▸ hphi0)
  refine ⟨tau, alpha, htau_ne, ?_, halpha', hn, hchart, M, hmatch, ?_⟩
  · simpa only [s.T_eq] using htau
  · have htauT : IsMultiplicativeConductor F tau.1 s.T := by
      simpa only [s.T_eq] using htau
    exact actualTwist_of_matched_models F E U K hp s.q0_pos s.T_eq hUK hb.2.2.2 hresUK
      hunr hb.2.1 tau.1 htauT Psi.character (s.c : F) (s.d : U) M hgen
      thetaU thetaE hc D hmatch
end GenuinePair

end

end LanglandsSecondMainLemma.Odd.UR
