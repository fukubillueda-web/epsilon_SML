import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Dyadic.UR.Models
import LanglandsSecondMainLemma.Characters.Conjugacy

/-!
# Realizing a dyadic unramified--ramified pair

Paper Proposition `D:UR:actual`, equations `D:UR:twistpair` and
`D:UR:conductors`. The critical endpoint follows from the actual conjugacy
orbit and FML's norm-character cancellation criterion. All characters are
continuous group homomorphisms on the full multiplicative groups.
-/

namespace LanglandsSecondMainLemma.Dyadic.UR

noncomputable section

open LanglandsFirstMainLemma

section Conjugation

variable (F U : Type) [Field F] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U]

/-- Transport the whole unit layer, including depth zero. -/
private theorem twist_conjugate_mem (sigma : Gal(U/F)) (n : ℕ) (u : Uˣ) :
    Units.map sigma.toMonoidHom u ∈ unitFiltration U n ↔
      u ∈ unitFiltration U n := by
  cases n with
  | zero =>
    simp only [mem_unitFiltration_zero, Units.coe_map]
    change ord U (sigma (u : U)) = 0 ↔ ord U (u : U) = 0
    rw [ord_galoisConjugate]
  | succ n =>
    simp only [mem_unitFiltration_succ, Units.coe_map, CongruentAtDepth]
    change (((n + 1 : ℕ) : ℤ) : WithTop ℤ) ≤ ord U (sigma (u : U) - 1) ↔ _
    rw [show sigma (u : U) - 1 = sigma ((u : U) - 1) by simp,
      ord_galoisConjugate]

private theorem twist_conjugate_conductor (sigma : Gal(U/F))
    {theta : ContinuousQuasiChar U} {m : ℕ}
    (hcond : IsMultiplicativeConductor U theta m) :
    IsMultiplicativeConductor U (Basic.conjugateQuasiChar F U sigma theta) m := by
  constructor
  · intro u hu
    exact hcond.trivial _ ((twist_conjugate_mem F U sigma.symm m u).2 hu)
  · intro r hr
    apply hcond.minimal r
    intro u hu
    have h := hr (Units.map sigma.toMonoidHom u)
      ((twist_conjugate_mem F U sigma r u).2 hu)
    change theta (Units.map sigma.symm.toMonoidHom (Units.map sigma.toMonoidHom u)) = 1 at h
    have heq : Units.map sigma.symm.toMonoidHom (Units.map sigma.toMonoidHom u) = u := by
      apply Units.ext
      exact sigma.symm_apply_apply u.val
    rwa [heq] at h

end Conjugation

section Orbit

variable (F U K : Type) [Field F] [Field U] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F U] [Algebra U K]
  [ValuativeExtension F U] [ValuativeExtension U K]
  [Module.Finite F U] [Module.Finite U K]

/-- Every upper norm-character twist has the original exact conductor.
This proves the no-drop hypothesis used at the critical break. -/
private theorem twist_orbit_conductor
    {theta : ContinuousQuasiChar U} (D : Characters.ConjugateTwistData F U K theta)
    {m : ℕ} (hcond : IsMultiplicativeConductor U theta m)
    (mu : NormCharacter U K) :
    IsMultiplicativeConductor U (mu.1 * theta) m := by
  obtain ⟨sigma, hsigma⟩ := D.quotientEquiv.surjective mu
  have heq := D.conjugate_eq_twist sigma
  rw [hsigma] at heq
  rw [mul_comm mu.1 theta, ← heq]
  exact twist_conjugate_conductor F U sigma hcond

/-- In degree two the two quotient equivalences agree, so the quotient
of the actual character and the model descends through the lower norm. -/
private theorem twist_descends [PrimeCyclicExtension F U]
    (hdegree : Module.finrank F U = 2)
    {theta chi : ContinuousQuasiChar U}
    (D : Characters.ConjugateTwistData F U K theta)
    (D0 : Characters.ConjugateTwistData F U K chi) :
    ∃ lambda : ContinuousQuasiChar F, theta = chi * normQuasiChar F U lambda := by
  have hcard : Nat.card (NormCharacter U K) = 2 :=
    (Nat.card_congr D.quotientEquiv.toEquiv).symm.trans
      ((IsGalois.card_aut_eq_finrank F U).trans hdegree)
  have hequiv (sigma : Gal(U/F)) : D.quotientEquiv sigma = D0.quotientEquiv sigma := by
    by_cases hs : sigma = 1
    · simp [hs]
    · exact ((Nat.card_eq_two_iff' (1 : NormCharacter U K)).mp hcard).unique
        ((map_ne_one_iff D.quotientEquiv D.quotientEquiv.injective).2 hs)
        ((map_ne_one_iff D0.quotientEquiv D0.quotientEquiv.injective).2 hs)
  obtain ⟨lambda, hlambda⟩ := Local.invariantCharacter_descends F U (theta / chi) (by
    intro sigma u
    have h := congrArg (fun mu : NormCharacter U K => mu.1 u) (hequiv sigma.symm)
    rw [D.quotient_eq, D0.quotient_eq] at h
    change theta (Units.map sigma.toMonoidHom u) / theta u =
      chi (Units.map sigma.toMonoidHom u) / chi u at h
    change theta (Units.map sigma.toMonoidHom u) / chi (Units.map sigma.toMonoidHom u) =
      theta u / chi u
    exact (div_eq_div_iff_mul_eq_mul).2 (by
      simpa only [mul_comm] using (div_eq_div_iff_mul_eq_mul).1 h))
  refine ⟨lambda, ?_⟩
  rw [hlambda]
  simp [div_eq_mul_inv]

end Orbit

section BaseConductor

variable (F U : Type) [Field F] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U]

/-- The larger conductor is the base-twist conductor; at equality the
base twist is bounded by the model conductor. -/
private theorem twist_base_conductor
    (hunr : ramificationIndex F U = 1)
    (theta chi : ContinuousQuasiChar U) (lambda : ContinuousQuasiChar F)
    {T h : ℕ} (hchi : IsMultiplicativeConductor U chi T)
    (htheta : IsMultiplicativeConductor U theta (T + h))
    (heq : theta = chi * normQuasiChar F U lambda) :
    (0 < h → IsMultiplicativeConductor F lambda (T + h)) ∧
      (h = 0 → multiplicativeConductorExponent F lambda ≤ T) := by
  have hlambda : normQuasiChar F U lambda = chi⁻¹ * theta := by
    rw [heq, ← mul_assoc, inv_mul_cancel, one_mul]
  constructor
  · intro hh
    apply (unramified_multiplicativeConductor_compNorm F U hunr lambda (T + h)).mp
    change IsMultiplicativeConductor U (normQuasiChar F U lambda) (T + h)
    rw [hlambda]
    exact hchi.inv.mul_of_lt htheta (by omega)
  · intro hh
    subst h
    have hcond := multiplicativeConductorExponent_isConductor F lambda
    have hpull := (unramified_multiplicativeConductor_compNorm F U hunr lambda _).mpr hcond
    change IsMultiplicativeConductor U (normQuasiChar F U lambda) _ at hpull
    rw [hlambda] at hpull
    have hle := hchi.inv.mul_conductor_le_max htheta hpull
    simpa only [Nat.add_zero, max_self] using hle

end BaseConductor

section DiamondEdges

variable (F U E K : Type) [Field F] [Field U] [Field E] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F U] [Algebra F E] [Algebra F K] [Algebra U K] [Algebra E K]
  [IsScalarTower F U K] [IsScalarTower F E K]
  [ValuativeExtension F U] [ValuativeExtension F E]
  [ValuativeExtension U K] [ValuativeExtension E K]
  [Module.Finite F U] [Module.Finite F E]
  [Module.Finite U K] [Module.Finite E K]
  [PrimeCyclicExtension F U] [PrimeCyclicExtension F E]
  [PrimeCyclicExtension U K] [PrimeCyclicExtension E K]

omit [ValuativeExtension E K] [PrimeCyclicExtension F U] [PrimeCyclicExtension E K] in
/-- Recover the upper break from the conductor of the crossed actual norm
character. At the same time prove separation of the two lower norm images. -/
private theorem twist_ramified_edge
    (hunr : ramificationIndex F U = 1)
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1)
    (tau : NormCharacter F E) (htau : tau ≠ 1) :
    (normUnits F U).range ≠ (normUnits F E).range ∧
      PrimeCyclicExtension.IsLowerBreak U K t ∧ residueDegree U K = 1 ∧
      IsMultiplicativeConductor U
        (Characters.crossedNormHom F U E K tau).1 (t + 1) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have hc := ramifiedNormCharacter_conductor F E ht hres pi hpi hgen tau htau
  let tauU := Characters.crossedNormHom F U E K tau
  have hcU : IsMultiplicativeConductor U tauU.1 (t + 1) :=
    (unramified_multiplicativeConductor_compNorm F U hunr tau.1 (t + 1)).mpr hc
  have hne : (normUnits F U).range ≠ (normUnits F E).range := by
    intro heq
    have hzero : QuasiCharTrivialOnUnitFiltration F tau.1 0 := by
      intro u hu
      apply tau.eq_one_on_normRange F E
      rw [← heq]
      obtain ⟨v, _, hv⟩ := (unramified_norm_unitFiltration F U hunr 0).2 u hu
      exact ⟨v, hv⟩
    have := hc.minimal 0 hzero
    omega
  have htauU : tauU ≠ 1 := by
    intro heq
    have hzero : QuasiCharTrivialOnUnitFiltration U tauU.1 0 := by
      intro u _
      rw [heq]
      rfl
    have := hcU.minimal 0 hzero
    omega
  have hram : ramificationIndex U K ≠ 1 := by
    intro hunrUK
    have hzero := unramifiedNormCharacter_conductor U K hunrUK tauU
    have := hcU.unique hzero
    omega
  let P := primeCyclicPreparation U K hram
  have hc' := ramifiedNormCharacter_conductor U K P.ht P.hres P.piK P.hpiK P.hgen
    tauU htauU
  have heqt : P.t = t := by have := hc'.unique hcU; omega
  exact ⟨hne, heqt ▸ P.ht, P.hres, hcU⟩

omit [Module.Finite F U] [Module.Finite E K] [PrimeCyclicExtension F U]
  [PrimeCyclicExtension F E] [PrimeCyclicExtension U K] [PrimeCyclicExtension E K] in
/-- The two valuation towers force the edge above the ramified lower
field to be unramified. -/
private theorem twist_unramified_edge
    (hunr : ramificationIndex F U = 1)
    (hE : Module.finrank F E = 2) (hUK : Module.finrank U K = 2)
    (hres : residueDegree F E = 1) : ramificationIndex E K = 1 := by
  have hEram : ramificationIndex F E = 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa only [hE, hres, mul_one] using h.symm
  obtain ⟨pi, hpi⟩ := exists_ord_eq F 1
  have hval : ord K (algebraMap U K (algebraMap F U pi)) =
      ord K (algebraMap E K (algebraMap F E pi)) := by
    rw [← IsScalarTower.algebraMap_apply F U K, ← IsScalarTower.algebraMap_apply F E K]
  rw [ord_algebraMap, ord_algebraMap, ord_algebraMap, ord_algebraMap,
    hunr, hEram, hpi, one_nsmul] at hval
  have heq : (ramificationIndex U K : ℤ) = (ramificationIndex E K : ℤ) * 2 := by
    exact WithTop.coe_injective (by simpa only [← WithTop.coe_nsmul,
      nsmul_eq_mul, Nat.cast_ofNat, mul_one] using hval)
  have hdeg := finrank_eq_ramificationIndex_mul_residueDegree U K
  have hpos := residueDegree_pos U K
  have hepos := ramificationIndex_pos E K
  have hbound : ramificationIndex U K ≤ 2 := by
    rw [hUK] at hdeg
    nlinarith
  omega

end DiamondEdges

section PairConductors

variable (F U E K : Type) [Field F] [Field U] [Field E] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F U] [Algebra U K] [Algebra E K]
  [ValuativeExtension F U] [ValuativeExtension U K] [ValuativeExtension E K]
  [Module.Finite F U] [Module.Finite U K] [Module.Finite E K]
  [PrimeCyclicExtension U K]

/-- The commutator bounds the lower conductor. The entire conjugacy
orbit then proves the critical no-drop case as well as the high formula. -/
private theorem twist_pair_conductors
    (hUK : Module.finrank U K = 2)
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak U K t)
    (hres : residueDegree U K = 1) (hunr : ramificationIndex E K = 1)
    (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
    (hcomp : normQuasiChar U K thetaU = normQuasiChar E K thetaE)
    (D : Characters.ConjugateTwistData F U K thetaU)
    (tauU : NormCharacter U K)
    (htauU : IsMultiplicativeConductor U tauU.1 (t + 1)) :
    ∃ h : ℕ, IsMultiplicativeConductor U thetaU (t + 1 + h) ∧
      IsMultiplicativeConductor E thetaE (t + 1 + 2 * h) := by
  let m := multiplicativeConductorExponent U thetaU
  have hm : IsMultiplicativeConductor U thetaU m :=
    multiplicativeConductorExponent_isConductor U thetaU
  obtain ⟨sigma, hsigma⟩ := D.quotientEquiv.surjective tauU
  have hquot : Basic.conjugateQuasiChar F U sigma thetaU * thetaU⁻¹ = tauU.1 := by
    rw [← div_eq_mul_inv, ← D.quotient_eq, hsigma]
  have hle : t + 1 ≤ m := by
    have h := (twist_conjugate_conductor F U sigma hm).mul_conductor_le_max hm.inv
      (hquot.symm ▸ htauU)
    simpa only [max_self] using h
  obtain ⟨h, heq⟩ := Nat.exists_eq_add_of_le hle
  have hm' : IsMultiplicativeConductor U thetaU (t + 1 + h) := heq ▸ hm
  let dataU : LocalQuasiCharData U := ⟨thetaU, t + 1 + h, hm'⟩
  let dataK := canonicalLocalQuasiCharData K (normQuasiChar U K thetaU)
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer U K hres
  have hformula := dataU.conductor_compNorm_eq_atOrAboveCritical_of_minimalOrbit
    U K ht hres pi hpi hgen dataK rfl (by dsimp [dataU]; omega) (by
      intro mu q hq
      exact Nat.le_of_eq ((twist_orbit_conductor F U K D hm' mu).unique hq))
  have hcondK : IsMultiplicativeConductor K (normQuasiChar U K thetaU)
      (t + 1 + 2 * h) := by
    have heqK : dataK.conductor = t + 1 + 2 * h := by
      change (dataK.conductor : ℤ) =
        (Module.finrank U K : ℤ) * ((t + 1 + h : ℕ) : ℤ) -
          (((Module.finrank U K - 1) * (t + 1) : ℕ) : ℤ) at hformula
      rw [hUK] at hformula
      norm_num at hformula
      omega
    exact heqK ▸ dataK.isConductor
  refine ⟨h, hm', ?_⟩
  apply (unramified_multiplicativeConductor_compNorm E K hunr thetaE _).mp
  change IsMultiplicativeConductor K (normQuasiChar E K thetaE) _
  rw [← hcomp]
  exact hcondK

end PairConductors

section Adjustment

variable (F U E K : Type) [Field F] [Field U] [Field E] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F U] [Algebra F E] [Algebra F K] [Algebra U K] [Algebra E K]
  [IsScalarTower F U K] [IsScalarTower F E K]
  [ValuativeExtension F U] [ValuativeExtension F E]
  [ValuativeExtension U K] [ValuativeExtension E K]
  [Module.Finite F U] [Module.Finite F E]
  [Module.Finite U K] [Module.Finite E K]

/-- Compatibility leaves precisely an upper norm character as the
remaining discrepancy on `E`; both full norm towers are retained. -/
private theorem twist_adjustment
    (chiU thetaU : ContinuousQuasiChar U) (chiE thetaE : ContinuousQuasiChar E)
    (lambda : ContinuousQuasiChar F)
    (hc0 : normQuasiChar U K chiU = normQuasiChar E K chiE)
    (hc : normQuasiChar U K thetaU = normQuasiChar E K thetaE)
    (hreal : thetaU = chiU * normQuasiChar F U lambda) :
    ∃ nu : NormCharacter E K,
      thetaE = (chiE * nu.1) * normQuasiChar F E lambda := by
  have hvalues (x : Kˣ) : thetaE (normUnits E K x) =
      chiE (normUnits E K x) * lambda (normUnits F E (normUnits E K x)) := by
    have h := DFunLike.congr_fun hc x
    have h0 := DFunLike.congr_fun hc0 x
    change chiU (normUnits U K x) = chiE (normUnits E K x) at h0
    rw [hreal] at h
    change chiU (normUnits U K x) * lambda (normUnits F U (normUnits U K x)) =
      thetaE (normUnits E K x) at h
    have htower : normUnits F U (normUnits U K x) =
        normUnits F E (normUnits E K x) := by
      apply Units.ext
      change Algebra.norm F (Algebra.norm U x.val) = Algebra.norm F (Algebra.norm E x.val)
      rw [Basic.norm_tower, Basic.norm_tower]
    rw [h0, htower] at h
    exact h.symm
  let nu : NormCharacter E K := ⟨thetaE / (chiE * normQuasiChar F E lambda), by
    apply ContinuousMonoidHom.ext
    intro x
    change thetaE (normUnits E K x) /
      (chiE (normUnits E K x) * lambda (normUnits F E (normUnits E K x))) = 1
    rw [hvalues, div_self']⟩
  refine ⟨nu, ?_⟩
  change thetaE = (chiE * (thetaE / (chiE * normQuasiChar F E lambda))) *
    normQuasiChar F E lambda
  apply ContinuousMonoidHom.ext
  intro u
  change thetaE u = (chiE u * (thetaE u / (chiE u * lambda (normUnits F E u)))) *
    lambda (normUnits F E u)
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

end Adjustment

section Realization

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

/-- **Realizing any given pair** (paper Proposition `D:UR:actual`).

The stationary data are exactly the inputs of the accepted constructor
`models`. The result constructs the model characters, a common base twist,
and the permitted unramified adjustment. The adjusted model on `E` retains
its conductor and its full stationary chart. Its common pullback with the
model on `U` remains primitive. The natural height is a nonnegative integer;
all ideal depths and all conductor calculations before this height is
introduced use the original FML conventions.

The actual primitive pair supplies the conjugate quotient and the critical
no-drop condition inside the proof. No commutator or conductor conclusion
is imposed on that pair, and no unitarity or field-characteristic assumption
is added. -/
theorem twist
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (U E : IntermediateField F K)
    (hU : Module.finrank F U = 2) (hE : Module.finrank F E = 2) :
    letI := Basic.intermediateFieldValuativeRel U
    letI := Basic.intermediateFieldTopology U
    letI := Basic.intermediateField_localField U
    letI := Basic.intermediateField_lowerValuativeExtension U
    letI := Basic.intermediateField_upperValuativeExtension U
    letI := Basic.intermediateFieldValuativeRel E
    letI := Basic.intermediateFieldTopology E
    letI := Basic.intermediateField_localField E
    letI := Basic.intermediateField_lowerValuativeExtension E
    letI := Basic.intermediateField_upperValuativeExtension E
    ∀ (_hunr : ramificationIndex F U = 1)
      (t : ℕ) (_ht : PrimeCyclicExtension.IsLowerBreak F E t)
      (_htpos : 0 < t) (_hres : residueDegree F E = 1)
      (tau : NormCharacter F E) (_htau : tau ≠ 1)
      (Psi : ContinuousAddChar F)
      (_hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
      (_hchart : ∀ (x : F) (hx : x ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
        tau.1 (principalUnitOf F (t / 2) (-x) (neg_mem_lattice F hx)) = Psi x)
      (sigma : Gal(U/F)) (_hsigma : sigma ≠ 1)
      (c : F) (_hc : ord F c = 0) (d : U) (_hd : ord U d = 0)
      (_hdc : d ^ 2 - d = algebraMap F U c) (_hconj : sigma d = 1 - d)
      (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
      (_hcomp : normQuasiChar U K thetaU = normQuasiChar E K thetaE)
      (_hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F,
        normQuasiChar F K lambda = normQuasiChar U K thetaU),
      ∃ (chiU : ContinuousQuasiChar U) (chiE : ContinuousQuasiChar E)
        (lambda : ContinuousQuasiChar F) (nu : NormCharacter E K) (h : ℕ),
        IsMultiplicativeConductor U chiU (t + 1) ∧
        IsMultiplicativeConductor E chiE (t + 1) ∧
        IsMultiplicativeConductor E nu.1 0 ∧
        IsMultiplicativeConductor E (chiE * nu.1) (t + 1) ∧
        normQuasiChar U K chiU = normQuasiChar E K (chiE * nu.1) ∧
        (¬ ∃ lambda0 : ContinuousQuasiChar F,
          normQuasiChar F K lambda0 = normQuasiChar U K chiU) ∧
        (∀ v : Uˣ, chiU (Units.map sigma.toMonoidHom v) / chiU v =
          normQuasiChar F U tau.1 v) ∧
        (∀ (z : U) (hz : z ∈ lattice U ((t / 2 + 1 : ℕ) : ℤ)),
          chiU (principalUnitOf U (t / 2) (-z) (neg_mem_lattice U hz)) =
            tracePullbackAddChar F U Psi (d ^ 2 * z)) ∧
        (∀ (z : E) (hz : z ∈ lattice E ((t / 2 + 1 : ℕ) : ℤ)),
          (chiE * nu.1) (principalUnitOf E (t / 2) (-z) (neg_mem_lattice E hz)) =
            tracePullbackAddChar F E Psi (algebraMap F E c * z)) ∧
        thetaU = chiU * normQuasiChar F U lambda ∧
        thetaE = (chiE * nu.1) * normQuasiChar F E lambda ∧
        IsMultiplicativeConductor U thetaU (t + 1 + h) ∧
        IsMultiplicativeConductor E thetaE (t + 1 + 2 * h) ∧
        (0 < h → IsMultiplicativeConductor F lambda (t + 1 + h)) ∧
        (h = 0 → multiplicativeConductorExponent F lambda ≤ t + 1) := by
  letI := Basic.intermediateFieldValuativeRel U
  letI := Basic.intermediateFieldTopology U
  letI := Basic.intermediateField_localField U
  letI := Basic.intermediateField_lowerValuativeExtension U
  letI := Basic.intermediateField_upperValuativeExtension U
  letI := Basic.intermediateFieldValuativeRel E
  letI := Basic.intermediateFieldTopology E
  letI := Basic.intermediateField_localField E
  letI := Basic.intermediateField_lowerValuativeExtension E
  letI := Basic.intermediateField_upperValuativeExtension E
  intro hunr t ht htpos hres tau htau Psi hPsi hchart sigma hsigma c hc d hd hdc hconj
    thetaU thetaE hcomp hprimitive
  have dataU := Basic.intermediateField_tower_compatible Nat.prime_two hG U hU
  have dataE := Basic.intermediateField_tower_compatible Nat.prime_two hG E hE
  have hUK := dataU.2.2.2.2.2.2.2.2.2.2.1
  have hEK := dataE.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F U dataU.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension U K dataU.2.2.2.2.2.2.2.2.2.2.2.2
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E dataE.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension E K dataE.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨hne, htUK, hresUK, htauU⟩ :=
    twist_ramified_edge F U E K hunr ht hres tau htau
  have hunrEK := twist_unramified_edge F U E K hunr hE hUK hres
  obtain ⟨chiU, chiE, hcU, hcE, hc0, hp0, hcomm, hchartU, hchartE⟩ :=
    models F U E K hunr hU hE hUK hEK ht htpos hres tau htau
      Psi hPsi hchart sigma hsigma c hc d hd hdc hconj
  have hp0' : ¬ ∃ lambda : ContinuousQuasiChar F,
      normQuasiChar F K lambda = normQuasiChar U K chiU := by
    rintro ⟨lambda, hlambda⟩
    exact hp0 ⟨lambda, hlambda.symm⟩
  obtain ⟨⟨D⟩, _⟩ := Characters.conjugacy Nat.prime_two hG U E hU hE hne
    thetaU thetaE (normQuasiChar U K thetaU) rfl hcomp.symm hprimitive
  obtain ⟨⟨D0⟩, _⟩ := Characters.conjugacy Nat.prime_two hG U E hU hE hne
    chiU chiE (normQuasiChar U K chiU) rfl hc0.symm hp0'
  obtain ⟨lambda, hrealU⟩ := twist_descends F U K hU D D0
  obtain ⟨nu, hrealE⟩ := twist_adjustment F U E K chiU thetaU chiE thetaE lambda
    hc0 hcomp hrealU
  have hnu := unramifiedNormCharacter_conductor E K hunrEK nu
  have hcE' := hcE.mul_of_gt hnu (by omega)
  have hc0' : normQuasiChar U K chiU = normQuasiChar E K (chiE * nu.1) := by
    rw [hc0]
    apply ContinuousMonoidHom.ext
    intro x
    change chiE (normUnits E K x) =
      chiE (normUnits E K x) * nu.1 (normUnits E K x)
    rw [nu.eq_one_on_normRange E K _ ⟨x, rfl⟩, mul_one]
  have hchartE' (z : E) (hz : z ∈ lattice E ((t / 2 + 1 : ℕ) : ℤ)) :
      (chiE * nu.1) (principalUnitOf E (t / 2) (-z) (neg_mem_lattice E hz)) =
        tracePullbackAddChar F E Psi (algebraMap F E c * z) := by
    rw [ContinuousQuasiChar.mul_apply, hchartE z hz,
      hnu.trivial _ (unitFiltration_antitone E (Nat.zero_le _) (principalUnitOf_mem E _ _ _)),
      mul_one]
  obtain ⟨h, hthetaU, hthetaE⟩ := twist_pair_conductors F U E K hUK htUK hresUK hunrEK
    thetaU thetaE hcomp D (Characters.crossedNormHom F U E K tau) htauU
  have hlambda := twist_base_conductor F U hunr thetaU chiU lambda hcU hthetaU hrealU
  exact ⟨chiU, chiE, lambda, nu, h, hcU, hcE, hnu, hcE', hc0', hp0', hcomm,
    hchartU, hchartE', hrealU, hrealE, hthetaU, hthetaE, hlambda⟩

end Realization

end

end LanglandsSecondMainLemma.Dyadic.UR
