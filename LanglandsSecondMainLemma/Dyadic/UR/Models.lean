import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Dyadic.UR.NormPhase
import LanglandsSecondMainLemma.Characters.CrossedNorm
import LanglandsSecondMainLemma.Local.NormDescent

/-!
# Dyadic / UR / Models

Blueprint: blueprint/tasks/Dyadic/UR/Models.md
Paper: D:UR:models

The construction first establishes agreement on the entire intersection
of the commutator image and the stationary subgroup. The character on
their product is then constructed by descent from a product of groups;
multiplicativity is proved before continuous character extension.
-/

namespace LanglandsSecondMainLemma.Dyadic.UR

noncomputable section

open LanglandsFirstMainLemma

private theorem addChar_sub {L : Type*} [AddCommGroup L] [TopologicalSpace L]
    (Psi : ContinuousAddChar L) (x y : L) :
    Psi (x - y) = Psi x / Psi y := Psi.toAddChar.map_sub_eq_div x y

/-- Extend a stationary subgroup character together with a commutator
prescription. The intersection condition is used to prove the kernel
condition for descent from `Eˣ × H`, so the character on the generated
subgroup is constructed, rather than postulated. -/
private theorem extendCommutatorChart
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (delta : Eˣ →* Eˣ) (tau : Eˣ →* ℂˣ)
    (H : Subgroup Eˣ) (kappa : H →* ℂˣ)
    (hoverlap : ∀ (v : Eˣ) (hv : delta v ∈ H),
      kappa ⟨delta v, hv⟩ = tau v)
    (m : ℕ) (hm : 1 ≤ m) (hdeep : unitFiltration E m ≤ H)
    (htrivial : ∀ (u : Eˣ) (hu : u ∈ unitFiltration E m),
      kappa ⟨u, hdeep hu⟩ = 1) :
    ∃ chi : ContinuousQuasiChar E,
      (∀ u : H, chi u = kappa u) ∧
      (∀ v : Eˣ, chi (delta v) = tau v) := by
  let assemble : Eˣ × H →* Eˣ :=
    { toFun := fun p => delta p.1 * p.2
      map_one' := by simp
      map_mul' := by
        intro p r
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Subgroup.coe_mul]
        exact mul_mul_mul_comm _ _ _ _ }
  let prescribed : Eˣ × H →* ℂˣ :=
    { toFun := fun p => tau p.1 * kappa p.2
      map_one' := by simp
      map_mul' := by
        intro p r
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
        exact mul_mul_mul_comm _ _ _ _ }
  have hker : assemble.rangeRestrict.ker ≤ prescribed.ker := by
    rintro ⟨v, h⟩ hp
    have heq : delta v * (h : Eˣ) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hp)
    have hd : delta v = (h : Eˣ)⁻¹ := (eq_inv_iff_mul_eq_one).2 heq
    have hdH : delta v ∈ H := hd ▸ H.inv_mem h.property
    have hk := hoverlap v hdH
    have hsub : (⟨delta v, hdH⟩ : H) = h⁻¹ := Subtype.ext hd
    rw [hsub, map_inv] at hk
    change tau v * kappa h = 1
    rw [← hk, inv_mul_cancel]
  let generated : assemble.range →* ℂˣ :=
    assemble.rangeRestrict.liftOfSurjective
      assemble.rangeRestrict_surjective ⟨prescribed, hker⟩
  have hgenerated (p : Eˣ × H) :
      generated (assemble.rangeRestrict p) = prescribed p := by
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hH : H ≤ assemble.range := by
    intro u hu
    refine ⟨(1, ⟨u, hu⟩), ?_⟩
    simp [assemble]
  have hdeep' : unitFiltration E m ≤ assemble.range := hdeep.trans hH
  have hgeneratedH (u : H) : generated ⟨u, hH u.property⟩ = kappa u := by
    have heq : (⟨(u : Eˣ), hH u.property⟩ : assemble.range) =
        assemble.rangeRestrict (1, u) := by
      apply Subtype.ext
      simp [assemble]
    rw [heq, hgenerated]
    simp [prescribed]
  have hgeneratedTrivial :
      generated.comp (Subgroup.inclusion hdeep') = 1 := by
    apply MonoidHom.ext
    intro u
    exact (hgeneratedH ⟨u, hdeep u.property⟩).trans (htrivial u u.property)
  obtain ⟨chi, hchi⟩ := Local.characterExtension E assemble.range m hm
    hdeep' generated hgeneratedTrivial
  refine ⟨chi, ?_, ?_⟩
  · intro u
    exact (DFunLike.congr_fun hchi ⟨u, hH u.property⟩).trans (hgeneratedH u)
  · intro v
    have hv := DFunLike.congr_fun hchi (assemble.rangeRestrict (v, 1))
    rw [hgenerated] at hv
    simpa [assemble, prescribed] using hv

section StationaryChart

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

private theorem oneSub_mem_of_unitFiltration (r : ℕ)
    (u : unitFiltration L (r + 1)) :
    1 - (u : Lˣ).val ∈ lattice L ((r + 1 : ℕ) : ℤ) := by
  simpa only [neg_sub] using neg_mem_lattice L
    ((mem_unitFiltration_succ_iff_sub_mem_lattice L r u).mp u.property)

/-- The full positive-depth linear chart is a group homomorphism when
its multiplication error lies in the additive character's trivial ideal. -/
private def stationaryChart
    (Psi : ContinuousAddChar L) (a : L) (ha : a ∈ lattice L 0)
    (r T : ℕ) (hdepth : T ≤ 2 * (r + 1))
    (hPsi : AddCharTrivialOnLattice L Psi (T : ℤ)) :
    unitFiltration L (r + 1) →* ℂˣ where
  toFun u := Psi (a * (1 - (u : Lˣ).val))
  map_one' := by simp [ContinuousAddChar.map_zero_eq_one]
  map_mul' u v := by
    have herror : a * ((1 - (u : Lˣ).val) * (1 - (v : Lˣ).val)) ∈
        lattice L (T : ℤ) := by
      apply lattice_antitone L (show (T : ℤ) ≤ 0 +
        (((r + 1 : ℕ) : ℤ) + ((r + 1 : ℕ) : ℤ)) by omega)
      exact mul_mem_lattice L ha (mul_mem_lattice L
        (oneSub_mem_of_unitFiltration L r u)
        (oneSub_mem_of_unitFiltration L r v))
    change Psi (a * (1 - (u : Lˣ).val * (v : Lˣ).val)) = _
    rw [show a * (1 - (u : Lˣ).val * (v : Lˣ).val) =
      a * (1 - (u : Lˣ).val) + a * (1 - (v : Lˣ).val) -
        a * ((1 - (u : Lˣ).val) * (1 - (v : Lˣ).val)) by ring]
    rw [addChar_sub, ContinuousAddChar.map_add_eq_mul,
      hPsi _ herror, div_one]

end StationaryChart

section QuadraticAlgebra

variable (F U : Type*) [Field F] [Field U] [Algebra F U]
  [Module.Finite F U] [IsGalois F U]

private theorem quadraticAutomorphisms (hdegree : Module.finrank F U = 2)
    (sigma : Gal(U/F)) (hsigma : sigma ≠ 1) (rho : Gal(U/F)) :
    rho = 1 ∨ rho = sigma := by
  obtain ⟨s, hs, hunique⟩ := (Nat.card_eq_two_iff' (1 : Gal(U/F))).mp
    ((IsGalois.card_aut_eq_finrank F U).trans hdegree)
  by_cases hrho : rho = 1
  · exact Or.inl hrho
  · exact Or.inr ((hunique rho hrho).trans (hunique sigma hsigma).symm)

private theorem quadraticInvolution (hdegree : Module.finrank F U = 2)
    (sigma : Gal(U/F)) (hsigma : sigma ≠ 1) : sigma * sigma = 1 := by
  rcases quadraticAutomorphisms F U hdegree sigma hsigma (sigma * sigma) with h | h
  · exact h
  · exact (hsigma ((mul_left_cancel (a := sigma)
      (h.trans (mul_one sigma).symm)))).elim

private theorem quadraticTrace (hdegree : Module.finrank F U = 2)
    (sigma : Gal(U/F)) (hsigma : sigma ≠ 1) (x : U) :
    algebraMap F U (trace F U x) = x + sigma x := by
  classical
  have huniv : (Finset.univ : Finset Gal(U/F)) = {1, sigma} := by
    ext rho
    simpa only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff] using quadraticAutomorphisms F U hdegree sigma hsigma rho
  rw [show trace F U x = Algebra.trace F U x from rfl,
    trace_eq_sum_automorphisms, huniv]
  simp [hsigma.symm]

private theorem quadraticNorm (hdegree : Module.finrank F U = 2)
    (sigma : Gal(U/F)) (hsigma : sigma ≠ 1) (x : U) :
    algebraMap F U (norm F U x) = x * sigma x := by
  classical
  have huniv : (Finset.univ : Finset Gal(U/F)) = {1, sigma} := by
    ext rho
    simpa only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff] using quadraticAutomorphisms F U hdegree sigma hsigma rho
  rw [show norm F U x = Algebra.norm F x from rfl,
    Algebra.norm_eq_prod_automorphisms, huniv]
  simp [hsigma.symm]

private theorem quadraticNorm_oneSub (hdegree : Module.finrank F U = 2)
    (sigma : Gal(U/F)) (hsigma : sigma ≠ 1) (x : U) :
    norm F U (1 - x) = 1 - trace F U x + norm F U x := by
  apply (algebraMap F U).injective
  rw [map_add (algebraMap F U), map_sub (algebraMap F U), map_one (algebraMap F U),
    quadraticNorm F U hdegree sigma hsigma,
    quadraticNorm F U hdegree sigma hsigma, quadraticTrace F U hdegree sigma hsigma,
    map_sub, map_one]
  ring

/-- The orientation used in paper `D:UR:modelcomm`. -/
private def modelCommutator (sigma : Gal(U/F)) : Uˣ →* Uˣ :=
  (Units.map sigma.toMonoidHom) / MonoidHom.id Uˣ

omit [Module.Finite F U] [IsGalois F U] in
private theorem modelCommutator_apply (sigma : Gal(U/F)) (v : Uˣ) :
    modelCommutator F U sigma v = Units.map sigma.toMonoidHom v / v := rfl

end QuadraticAlgebra

section QuadraticOverlap

variable (F U : Type*) [Field F] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F U] [ValuativeExtension F U]
  [Module.Finite F U] [IsGalois F U]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeExtension F U] in
/-- A trace-one integral element gives an exact base-field representative
of a multiplicative class fixed modulo a positive-depth ideal. This proves
the overlap lifting step of `D:UR:models` on all of `Uˣ`.

The representative is `Tr(d*v)`. The identity
`Tr(d*v)/v = 1 + (1-d)*(sigma(v)/v - 1)` proves it is nonzero and
congruent to `v`, without division by two or a choice of norm preimage. -/
theorem modelCommutator_decomposition
    (hdegree : Module.finrank F U = 2)
    (sigma : Gal(U/F)) (hsigma : sigma ≠ 1)
    (d : U) (hd : d ∈ lattice U 0) (hconj : sigma d = 1 - d)
    (r : ℕ) (v : Uˣ)
    (hv : Units.map sigma.toMonoidHom v / v ∈ unitFiltration U (r + 1)) :
    ∃ (f : Fˣ) (h : unitFiltration U (r + 1)),
      v = Units.map (algebraMap F U).toMonoidHom f * (h : Uˣ) := by
  let delta : Uˣ := Units.map sigma.toMonoidHom v / v
  have hdelta : delta.val - 1 ∈ lattice U ((r + 1 : ℕ) : ℤ) :=
    (mem_unitFiltration_succ_iff_sub_mem_lattice U r delta).mp hv
  have h1d : 1 - d ∈ lattice U 0 := sub_mem_lattice U (by simp) hd
  let z : U := (1 - d) * (delta.val - 1)
  have hz : z ∈ lattice U ((r + 1 : ℕ) : ℤ) := by
    simpa only [zero_add] using mul_mem_lattice U h1d hdelta
  let w : Uˣ := principalUnitOf U r z hz
  have hw : w ∈ unitFiltration U (r + 1) := principalUnitOf_mem U r z hz
  let f : F := trace F U (d * v.val)
  have hf : algebraMap F U f = w.val * v.val := by
    rw [show f = trace F U (d * v.val) from rfl,
      quadraticTrace F U hdegree sigma hsigma, map_mul, hconj]
    change d * v.val + (1 - d) * sigma v.val = (1 + z) * v.val
    dsimp only [z, delta]
    rw [Units.val_div_eq_div_val, Units.coe_map]
    change d * v.val + (1 - d) * sigma v.val =
      (1 + (1 - d) * (sigma v.val / v.val - 1)) * v.val
    field_simp
    ring
  have hf0 : f ≠ 0 := by
    intro hzero
    have := hf
    rw [hzero, map_zero] at this
    exact (mul_ne_zero w.ne_zero v.ne_zero) this.symm
  refine ⟨Units.mk0 f hf0, ⟨w⁻¹, (unitFiltration U (r + 1)).inv_mem hw⟩, ?_⟩
  apply Units.ext
  change v.val = algebraMap F U f * w.val⁻¹
  rw [hf]
  field_simp

end QuadraticOverlap

section UnramifiedChart

variable (F U : Type*) [Field F] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F U] [ValuativeExtension F U]
  [Module.Finite F U] [IsGalois F U]

omit [IsGalois F U] in
private theorem modelConjugate_mem (sigma : Gal(U/F)) (r : ℕ)
    (u : Uˣ) (hu : u ∈ unitFiltration U (r + 1)) :
    Units.map sigma.toMonoidHom u ∈ unitFiltration U (r + 1) := by
  rw [mem_unitFiltration_succ_iff_sub_mem_lattice, mem_lattice]
  change (((r + 1 : ℕ) : ℤ) : WithTop ℤ) ≤ ord U (sigma u.val - 1)
  rw [← map_one sigma, ← map_sub, ord_galoisConjugate F U sigma]
  exact (mem_unitFiltration_succ_iff_ord U r u).mp hu

/-- Unramified norm expansion transports the actual lower norm-character
chart to the whole half-conductor unit subgroup upstairs. -/
theorem unramifiedNormChart
    (hunr : ramificationIndex F U = 1) (hdegree : Module.finrank F U = 2)
    (sigma : Gal(U/F)) (hsigma : sigma ≠ 1)
    (r T : ℕ) (hT : T ≤ 2 * (r + 1))
    (tau : ContinuousQuasiChar F) (Psi : ContinuousAddChar F)
    (hPsi : AddCharTrivialOnLattice F Psi (T : ℤ))
    (hchart : ∀ (x : F) (hx : x ∈ lattice F ((r + 1 : ℕ) : ℤ)),
      tau (principalUnitOf F r (-x) (neg_mem_lattice F hx)) = Psi x)
    (u : Uˣ) (hu : u ∈ unitFiltration U (r + 1)) :
    normQuasiChar F U tau u = tracePullbackAddChar F U Psi (1 - u.val) := by
  let z : U := 1 - u.val
  have hz : z ∈ lattice U ((r + 1 : ℕ) : ℤ) :=
    oneSub_mem_of_unitFiltration U r ⟨u, hu⟩
  have htrace : trace F U z ∈ lattice F ((r + 1 : ℕ) : ℤ) :=
    trace_mem_lattice F U hunr _ hz
  have hres : residueDegree F U = 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F U
    simpa only [hunr, one_mul, hdegree] using h.symm
  have hnorm : norm F U z ∈ lattice F (2 * ((r + 1 : ℕ) : ℤ)) := by
    rw [mem_lattice, ord_norm, hres]
    have h := add_le_add ((mem_lattice U).mp hz) ((mem_lattice U).mp hz)
    simpa only [two_nsmul, two_mul, WithTop.coe_add] using h
  have hy : trace F U z - norm F U z ∈ lattice F ((r + 1 : ℕ) : ℤ) :=
    sub_mem_lattice F htrace (lattice_antitone F (by omega) hnorm)
  have hnormUnit : normUnits F U u = principalUnitOf F r
      (-(trace F U z - norm F U z)) (neg_mem_lattice F hy) := by
    apply Units.ext
    rw [coe_normUnits, coe_principalUnitOf]
    rw [show u.val = 1 - z by dsimp [z]; ring,
      quadraticNorm_oneSub F U hdegree sigma hsigma]
    ring
  change tau (normUnits F U u) = Psi (trace F U z)
  rw [hnormUnit, hchart _ hy, addChar_sub, hPsi _
    (lattice_antitone F (by omega) hnorm), div_one]

/-- Once the chart has its required conjugate quotient on the whole
stationary subgroup, the trace representative proves the entire overlap
condition and yields a continuous character on `Uˣ`. -/
private theorem extendQuadraticChart
    (hdegree : Module.finrank F U = 2)
    (sigma : Gal(U/F)) (hsigma : sigma ≠ 1)
    (d : U) (hd : d ∈ lattice U 0) (hconj : sigma d = 1 - d)
    (r T : ℕ) (hTpos : 1 ≤ T) (hrT : r + 1 ≤ T)
    (tau : Uˣ →* ℂˣ)
    (hbase : ∀ f : Fˣ, tau (Units.map (algebraMap F U).toMonoidHom f) = 1)
    (kappa : unitFiltration U (r + 1) →* ℂˣ)
    (hlocal : ∀ u : unitFiltration U (r + 1),
      kappa ⟨Units.map sigma.toMonoidHom u,
        modelConjugate_mem F U sigma r u u.property⟩ / kappa u = tau u)
    (htrivial : ∀ (u : Uˣ) (hu : u ∈ unitFiltration U T),
      kappa ⟨u, unitFiltration_antitone U hrT hu⟩ = 1) :
    ∃ chi : ContinuousQuasiChar U,
      (∀ u : unitFiltration U (r + 1), chi u = kappa u) ∧
      (∀ v : Uˣ, chi (Units.map sigma.toMonoidHom v) / chi v = tau v) := by
  have hoverlap (v : Uˣ)
      (hv : modelCommutator F U sigma v ∈ unitFiltration U (r + 1)) :
      kappa ⟨modelCommutator F U sigma v, hv⟩ = tau v := by
    obtain ⟨f, h, hfactor⟩ :=
      modelCommutator_decomposition F U hdegree sigma hsigma d hd hconj r v hv
    have hdelta : modelCommutator F U sigma v =
        Units.map sigma.toMonoidHom h / (h : Uˣ) := by
      rw [hfactor, map_mul, modelCommutator_apply, modelCommutator_apply]
      have hfixed : Units.map sigma.toMonoidHom
          (Units.map (algebraMap F U).toMonoidHom f) =
          Units.map (algebraMap F U).toMonoidHom f := by
        apply Units.ext
        exact sigma.commutes f.val
      rw [hfixed, div_self', one_mul]
    have heq : (⟨modelCommutator F U sigma v, hv⟩ : unitFiltration U (r + 1)) =
        ⟨Units.map sigma.toMonoidHom h,
          modelConjugate_mem F U sigma r h h.property⟩ / h := Subtype.ext hdelta
    rw [heq, map_div, hlocal, hfactor, map_mul, hbase, one_mul]
  obtain ⟨chi, hchi, hcomm⟩ := extendCommutatorChart U
    (modelCommutator F U sigma) tau (unitFiltration U (r + 1)) kappa
    hoverlap T hTpos (unitFiltration_antitone U hrT) htrivial
  refine ⟨chi, hchi, ?_⟩
  intro v
  simpa only [modelCommutator_apply, map_div] using hcomm v

end UnramifiedChart

section ExactConductor

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- A full stationary chart with a unit coefficient forces the exact
conductor, including nontriviality on the entire preceding ideal. -/
theorem modelChart_conductor
    (r t : ℕ) (hrt : r + 1 ≤ t)
    (Psi : ContinuousAddChar L)
    (hPsi : IsAdditiveConductor L Psi (-((t + 1 : ℕ) : ℤ)))
    (a : L) (ha : ord L a = 0)
    (chi : ContinuousQuasiChar L)
    (hchart : ∀ (u : Lˣ), u ∈ unitFiltration L (r + 1) →
      chi u = Psi (a * (1 - u.val))) :
    IsMultiplicativeConductor L chi (t + 1) := by
  have ha0 : a ≠ 0 := (ord_ne_top_iff L).mp (by simp [ha])
  have haIntegral : a ∈ lattice L 0 := by rw [mem_lattice, ha]; simp
  have htrivial : AddCharTrivialOnLattice L Psi ((t + 1 : ℕ) : ℤ) := by
    simpa only [neg_neg] using hPsi.trivial
  apply IsMultiplicativeConductor.of_succ_boundary
  · intro u hu
    rw [hchart u (unitFiltration_antitone L (by omega) hu)]
    apply htrivial
    simpa only [zero_add] using mul_mem_lattice L haIntegral
      (oneSub_mem_of_unitFiltration L t ⟨u, hu⟩)
  · intro hprev
    obtain ⟨x, hx, _, hxne⟩ := hPsi.exists_ne_one_on_predecessor
    have hx' : x ∈ lattice L (t : ℤ) := by
      simpa only [neg_neg, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hx
    have hz : x / a ∈ lattice L (t : ℤ) := by
      apply (div_mem_lattice_iff L a x 0 (t : ℤ) ha).mpr
      simpa only [zero_add] using hx'
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (show t ≠ 0 by omega)
    subst t
    let u := principalUnitOf L s (-(x / a)) (neg_mem_lattice L hz)
    have hu : u ∈ unitFiltration L (s + 1) := principalUnitOf_mem L s _ _
    have hv := hchart u (unitFiltration_antitone L hrt hu)
    rw [hprev u hu] at hv
    apply hxne
    have harg : a * (1 - u.val) = x := by
      change a * (1 - (1 + -(x / a))) = x
      field_simp
      ring
    rw [harg] at hv
    exact hv.symm

end ExactConductor

section NormCharacterSquares

variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]

private theorem normCharacter_square (hdegree : Module.finrank F E = 2)
    (tau : NormCharacter F E) (f : Fˣ) : tau.1 (f ^ 2) = 1 := by
  have hnorm : normUnits F E (Units.map (algebraMap F E).toMonoidHom f) = f ^ 2 := by
    apply Units.ext
    change norm F E (algebraMap F E f.val) = f.val ^ 2
    rw [LanglandsFirstMainLemma.norm_algebraMap, hdegree]
  rw [← hnorm]
  exact tau.eq_one_on_normRange F E _ ⟨_, rfl⟩

/-- The actual quadratic norm character kills the mixed-characteristic
`2*y` error on its whole chart. No replacement of `1-d` by `-d` is made. -/
private theorem normCharacter_chart_double
    (hdegree : Module.finrank F E = 2) (tau : NormCharacter F E)
    (Psi : ContinuousAddChar F) (r : ℕ)
    (hchart : ∀ (x : F) (hx : x ∈ lattice F ((r + 1 : ℕ) : ℤ)),
      tau.1 (principalUnitOf F r (-x) (neg_mem_lattice F hx)) = Psi x)
    (y : F) (hy : y ∈ lattice F ((r + 1 : ℕ) : ℤ)) : Psi (y + y) = 1 := by
  rw [ContinuousAddChar.map_add_eq_mul, ← hchart y hy, ← pow_two, ← map_pow]
  exact normCharacter_square F E hdegree tau _

end NormCharacterSquares

section UnramifiedModel

variable (F U E : Type*) [Field F] [Field U] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U] [IsGalois F U]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]

/-- The unramified-field character in paper `D:UR:models`, constructed
from the actual quadratic norm character and its additive chart. Its
commutator identity holds on all of `Uˣ`, and its stationary identity
holds on all of `p_U^(t/2+1)`. -/
theorem unramifiedModel
    (hunr : ramificationIndex F U = 1)
    (hUdegree : Module.finrank F U = 2) (hEdegree : Module.finrank F E = 2)
    (sigma : Gal(U/F)) (hsigma : sigma ≠ 1)
    (d : U) (hd : ord U d = 0) (hconj : sigma d = 1 - d)
    (t : ℕ) (htpos : 0 < t)
    (tau : NormCharacter F E) (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (hchart : ∀ (x : F) (hx : x ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
      tau.1 (principalUnitOf F (t / 2) (-x) (neg_mem_lattice F hx)) = Psi x) :
    ∃ chi : ContinuousQuasiChar U,
      IsMultiplicativeConductor U chi (t + 1) ∧
      (∀ v : Uˣ, chi (Units.map sigma.toMonoidHom v) / chi v =
        normQuasiChar F U tau.1 v) ∧
      (∀ (z : U) (hz : z ∈ lattice U ((t / 2 + 1 : ℕ) : ℤ)),
        chi (principalUnitOf U (t / 2) (-z) (neg_mem_lattice U hz)) =
          tracePullbackAddChar F U Psi (d ^ 2 * z)) := by
  let PsiU := tracePullbackAddChar F U Psi
  have hPsiU : IsAdditiveConductor U PsiU (-((t + 1 : ℕ) : ℤ)) :=
    (unramified_additiveConductor_compTrace F U hunr Psi _).mpr hPsi
  have htrivial : AddCharTrivialOnLattice U PsiU ((t + 1 : ℕ) : ℤ) := by
    simpa only [neg_neg] using hPsiU.trivial
  have htrivialF : AddCharTrivialOnLattice F Psi ((t + 1 : ℕ) : ℤ) := by
    simpa only [neg_neg] using hPsi.trivial
  have hdIntegral : d ∈ lattice U 0 := by rw [mem_lattice, hd]; simp
  have hd2 : ord U (d ^ 2) = 0 := by rw [ord_pow, hd]; simp
  have hd2Integral : d ^ 2 ∈ lattice U 0 := by rw [mem_lattice, hd2]; simp
  have hdepth : t + 1 ≤ 2 * (t / 2 + 1) := by omega
  let kappa := stationaryChart U PsiU (d ^ 2) hd2Integral (t / 2) (t + 1)
    hdepth htrivial
  have hbase (f : Fˣ) :
      normQuasiChar F U tau.1 (Units.map (algebraMap F U).toMonoidHom f) = 1 := by
    have hnorm : normUnits F U (Units.map (algebraMap F U).toMonoidHom f) = f ^ 2 := by
      apply Units.ext
      change norm F U (algebraMap F U f.val) = f.val ^ 2
      rw [LanglandsFirstMainLemma.norm_algebraMap, hUdegree]
    change tau.1 (normUnits F U _) = 1
    rw [hnorm]
    exact normCharacter_square F E hEdegree tau f
  have hlocal (u : unitFiltration U (t / 2 + 1)) :
      kappa ⟨Units.map sigma.toMonoidHom u,
        modelConjugate_mem F U sigma (t / 2) u u.property⟩ / kappa u =
        normQuasiChar F U tau.1 u := by
    let x : U := 1 - (u : Uˣ).val
    have hx : x ∈ lattice U ((t / 2 + 1 : ℕ) : ℤ) :=
      oneSub_mem_of_unitFiltration U (t / 2) u
    have hinvariant (z : U) : PsiU (sigma z) = PsiU z :=
      congrArg Psi (Algebra.trace_eq_of_algEquiv sigma z)
    have hinvol (z : U) : sigma (sigma z) = z := by
      rw [← AlgEquiv.mul_apply, quadraticInvolution F U hUdegree sigma hsigma]
      rfl
    have hconjugate : PsiU (d ^ 2 * (1 - sigma (u : Uˣ).val)) =
        PsiU ((1 - d) ^ 2 * x) := by
      rw [← hinvariant (d ^ 2 * (1 - sigma (u : Uˣ).val))]
      simp only [map_mul, map_pow, map_sub, map_one, hconj, hinvol]
      rfl
    have hdx : d * x ∈ lattice U ((t / 2 + 1 : ℕ) : ℤ) := by
      simpa only [zero_add] using mul_mem_lattice U hdIntegral hx
    have hdouble : PsiU (d * x + d * x) = 1 := by
      change Psi (trace F U (d * x + d * x)) = 1
      rw [map_add]
      exact normCharacter_chart_double F E hEdegree tau Psi (t / 2) hchart _
        (trace_mem_lattice F U hunr _ hdx)
    change PsiU (d ^ 2 * (1 - sigma (u : Uˣ).val)) / PsiU (d ^ 2 * x) = _
    rw [hconjugate, ← addChar_sub,
      show (1 - d) ^ 2 * x - d ^ 2 * x = x - (d * x + d * x) by ring,
      addChar_sub, hdouble, div_one]
    exact (unramifiedNormChart F U hunr hUdegree sigma hsigma (t / 2) (t + 1)
      hdepth tau.1 Psi htrivialF hchart u u.property).symm
  have hkTrivial (u : Uˣ) (hu : u ∈ unitFiltration U (t + 1)) :
      kappa ⟨u, unitFiltration_antitone U (show t / 2 + 1 ≤ t + 1 by omega) hu⟩ = 1 := by
    apply htrivial
    simpa only [zero_add] using mul_mem_lattice U hd2Integral
      (oneSub_mem_of_unitFiltration U t ⟨u, hu⟩)
  obtain ⟨chi, hchi, hcomm⟩ := extendQuadraticChart F U hUdegree sigma hsigma
    d hdIntegral hconj (t / 2) (t + 1) (by omega) (by omega)
    (normQuasiChar F U tau.1).toMonoidHom hbase kappa hlocal hkTrivial
  have hunitChart (u : Uˣ) (hu : u ∈ unitFiltration U (t / 2 + 1)) :
      chi u = PsiU (d ^ 2 * (1 - u.val)) := hchi ⟨u, hu⟩
  refine ⟨chi, modelChart_conductor U (t / 2) t (by omega) PsiU hPsiU
    (d ^ 2) hd2 chi hunitChart, hcomm, ?_⟩
  intro z hz
  rw [hunitChart _ (principalUnitOf_mem U (t / 2) _ _), coe_principalUnitOf]
  congr 2
  ring

end UnramifiedModel

section NormInvariance

variable (F U K : Type*) [Field F] [Field U] [Field K]
  [Algebra F U] [Algebra U K] [Algebra F K] [IsScalarTower F U K]
  [Normal F U]

/-- Naturality of the actual norm under restriction of an automorphism. -/
private theorem normUnits_restrictNormal (rho : Gal(K/F)) (x : Kˣ) :
    normUnits U K (Units.map rho.toMonoidHom x) =
      Units.map (rho.restrictNormal U).toMonoidHom (normUnits U K x) := by
  have hcompat : (algebraMap U K).comp (rho.restrictNormal U).toRingHom =
      rho.toRingHom.comp (algebraMap U K) := by
    apply RingHom.ext
    exact rho.restrictNormal_commutes U
  have h := Algebra.norm_eq_of_equiv_equiv
    (rho.restrictNormal U).toRingEquiv rho.toRingEquiv hcompat x.val
  have h' := congrArg (rho.restrictNormal U) h
  apply Units.ext
  change Algebra.norm U (rho x.val) = rho.restrictNormal U (Algebra.norm U x.val)
  exact (h'.trans ((rho.restrictNormal U).apply_symm_apply _)).symm

end NormInvariance

section ModelDescent

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
  [IsGalois F U] [PrimeCyclicExtension E K]

/-- The full commutator identity makes the common pullback invariant,
so the accepted local Hilbert-90 descent constructs a character of `Eˣ`.
No surjectivity of the ramified norm is assumed. -/
theorem model_descends
    (hUdegree : Module.finrank F U = 2)
    (sigma : Gal(U/F)) (hsigma : sigma ≠ 1)
    (tau : NormCharacter F E) (chiU : ContinuousQuasiChar U)
    (hcomm : ∀ v : Uˣ, chiU (Units.map sigma.toMonoidHom v) / chiU v =
      normQuasiChar F U tau.1 v) :
    ∃ chiE : ContinuousQuasiChar E,
      normQuasiChar E K chiE = normQuasiChar U K chiU := by
  let tauU := Characters.crossedNormHom F U E K tau
  apply Local.invariantCharacter_descends E K (normQuasiChar U K chiU)
  intro rho x
  let rhoF : Gal(K/F) := rho.restrictScalars F
  change chiU (normUnits U K (Units.map rhoF.toMonoidHom x)) =
    chiU (normUnits U K x)
  rw [normUnits_restrictNormal F U K]
  rcases quadraticAutomorphisms F U hUdegree sigma hsigma (rhoF.restrictNormal U)
      with h | h
  · rw [h]
    rfl
  · rw [h]
    have hc := hcomm (normUnits U K x)
    have htau : normQuasiChar F U tau.1 (normUnits U K x) = 1 :=
      tauU.eq_one_on_normRange U K _ ⟨x, rfl⟩
    rw [htau] at hc
    exact div_eq_one.mp hc

end ModelDescent

section RamifiedChart

variable (U K : Type*) [Field U] [Field K]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra U K] [ValuativeExtension U K] [Module.Finite U K]
  [PrimeCyclicExtension U K]

private theorem quadraticTrace_mem_depth
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak U K t)
    (hres : residueDegree U K = 1) (hdegree : Module.finrank U K = 2)
    (j : ℤ) (hj : j ≤ (t + 1 : ℕ)) (z : K) (hz : z ∈ lattice K j) :
    trace U K z ∈ lattice U j := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer U K hres
  have hmem : trace U K z ∈
      Submodule.map ((trace U K).restrictScalars (ringOfIntegers U))
        ((lattice K j).restrictScalars (ringOfIntegers U)) :=
    Submodule.mem_map.mpr ⟨z, hz, rfl⟩
  rw [cyclicPrime_trace_lattice_image_eq U K ht hres pi hpi hgen, hdegree] at hmem
  apply lattice_antitone U (show j ≤
    (j + (((2 - 1) * (t + 1) : ℕ) : ℤ)) / (2 : ℤ) by norm_num; omega) hmem

/-- The ramified norm changes the coefficient `d²` into `d²-d`, by
applying the actual norm phase to `d*z`. The equality holds on the entire
half-conductor subgroup upstairs. -/
theorem ramifiedModel_pullbackChart
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak U K t) (htpos : 0 < t)
    (hres : residueDegree U K = 1) (hdegree : Module.finrank U K = 2)
    (tau : NormCharacter U K) (htau : tau ≠ 1)
    (Psi : ContinuousAddChar U)
    (hchart : ∀ (x : U) (hx : x ∈ lattice U ((t / 2 + 1 : ℕ) : ℤ)),
      tau.1 (principalUnitOf U (t / 2) (-x) (neg_mem_lattice U hx)) = Psi x)
    (d : U) (hd : ord U d = 0)
    (chi : ContinuousQuasiChar U)
    (hchi : ∀ (x : U) (hx : x ∈ lattice U ((t / 2 + 1 : ℕ) : ℤ)),
      chi (principalUnitOf U (t / 2) (-x) (neg_mem_lattice U hx)) = Psi (d ^ 2 * x))
    (v : Kˣ) (hv : v ∈ unitFiltration K (t / 2 + 1)) :
    normQuasiChar U K chi v = tracePullbackAddChar U K Psi
      (algebraMap U K (d ^ 2 - d) * (1 - v.val)) := by
  let z : K := 1 - v.val
  have hz : z ∈ lattice K ((t / 2 + 1 : ℕ) : ℤ) :=
    oneSub_mem_of_unitFiltration K (t / 2) ⟨v, hv⟩
  have htrace : trace U K z ∈ lattice U ((t / 2 + 1 : ℕ) : ℤ) :=
    quadraticTrace_mem_depth U K ht hres hdegree _ (by omega) z hz
  have hnorm : norm U K z ∈ lattice U ((t / 2 + 1 : ℕ) : ℤ) := by
    rw [mem_lattice, ord_norm, hres, one_nsmul]
    exact (mem_lattice K).mp hz
  have hy := sub_mem_lattice U htrace hnorm
  have hnormUnit : normUnits U K v = principalUnitOf U (t / 2)
      (-(trace U K z - norm U K z)) (neg_mem_lattice U hy) := by
    apply Units.ext
    rw [coe_normUnits, coe_principalUnitOf,
      show v.val = 1 - z by dsimp [z]; ring,
      quadraticNorm_oneSub U K hdegree (PrimeCyclicExtension.generator U K)
        (PrimeCyclicExtension.generator_ne_one U K)]
    ring
  have hdIntegral : algebraMap U K d ∈ lattice K 0 := by
    rw [mem_lattice, ord_algebraMap, hd, nsmul_zero]
    simp
  have hdz : algebraMap U K d * z ∈ lattice K ((t / 2 + 1 : ℕ) : ℤ) := by
    simpa only [zero_add] using mul_mem_lattice K hdIntegral hz
  have hphase := normPhase U K ht htpos hres hdegree tau htau Psi hchart
    (algebraMap U K d * z) hdz
  rw [map_mul (norm U K), LanglandsFirstMainLemma.norm_algebraMap, hdegree] at hphase
  have htraceMul (a : U) : trace U K (algebraMap U K a * z) = a * trace U K z := by
    rw [← Algebra.smul_def, map_smul]
    rfl
  change chi (normUnits U K v) = _
  rw [hnormUnit, hchi _ hy,
    show d ^ 2 * (trace U K z - norm U K z) =
      d ^ 2 * trace U K z - d ^ 2 * norm U K z by ring,
    addChar_sub, ← hphase, ← htraceMul (d ^ 2)]
  change tracePullbackAddChar U K Psi (algebraMap U K (d ^ 2) * z) /
    tracePullbackAddChar U K Psi (algebraMap U K d * z) = _
  rw [← addChar_sub]
  congr 1
  rw [map_sub]
  dsimp only [z]
  ring

end RamifiedChart

section DescendedChart

variable (E K : Type) [Field E] [Field K]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra E K] [ValuativeExtension E K] [Module.Finite E K]
  [PrimeCyclicExtension E K]

/-- Surjectivity of the unramified norm on the specified unit layer
transports a full upstairs chart to the descended character. -/
theorem modelChart_of_unramifiedNorm
    (hunr : ramificationIndex E K = 1) (hdegree : Module.finrank E K = 2)
    (r T : ℕ) (hT : T ≤ 2 * (r + 1))
    (Psi : ContinuousAddChar E) (hPsi : AddCharTrivialOnLattice E Psi (T : ℤ))
    (c : E) (hc : c ∈ lattice E 0)
    (chi : ContinuousQuasiChar E)
    (hchart : ∀ (v : Kˣ), v ∈ unitFiltration K (r + 1) →
      normQuasiChar E K chi v = tracePullbackAddChar E K Psi
        (algebraMap E K c * (1 - v.val)))
    (u : Eˣ) (hu : u ∈ unitFiltration E (r + 1)) :
    chi u = Psi (c * (1 - u.val)) := by
  obtain ⟨v, hv, hnormv⟩ := (unramified_norm_unitFiltration E K hunr (r + 1)).2 u hu
  let z : K := 1 - v.val
  have hz : z ∈ lattice K ((r + 1 : ℕ) : ℤ) :=
    oneSub_mem_of_unitFiltration K r ⟨v, hv⟩
  have hres : residueDegree E K = 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree E K
    simpa only [hunr, one_mul, hdegree] using h.symm
  have hnorm : norm E K z ∈ lattice E (2 * ((r + 1 : ℕ) : ℤ)) := by
    rw [mem_lattice, ord_norm, hres]
    have h := add_le_add ((mem_lattice K).mp hz) ((mem_lattice K).mp hz)
    simpa only [two_nsmul, two_mul, WithTop.coe_add] using h
  have herror : c * norm E K z ∈ lattice E (T : ℤ) :=
    lattice_antitone E (by omega) (mul_mem_lattice E hc hnorm)
  have hnormField : 1 - u.val = trace E K z - norm E K z := by
    rw [← hnormv, coe_normUnits,
      show v.val = 1 - z by dsimp [z]; ring,
      quadraticNorm_oneSub E K hdegree (PrimeCyclicExtension.generator E K)
        (PrimeCyclicExtension.generator_ne_one E K)]
    ring
  have hvChart := hchart v hv
  change chi (normUnits E K v) = Psi (trace E K (algebraMap E K c * z)) at hvChart
  rw [hnormv, ← Algebra.smul_def, map_smul] at hvChart
  rw [hvChart, hnormField, mul_sub, addChar_sub, hPsi _ herror, div_one]
  rfl

/-- Exact positive conductor of an actual norm character recovers the
ramified edge and its lower break from FML's norm-character theorem. -/
private theorem modelNormCharacter_break
    (t : ℕ) (tau : NormCharacter E K)
    (hcond : IsMultiplicativeConductor E tau.1 (t + 1)) :
    PrimeCyclicExtension.IsLowerBreak E K t ∧ residueDegree E K = 1 ∧ tau ≠ 1 := by
  have htau : tau ≠ 1 := by
    intro h
    have hzero : QuasiCharTrivialOnUnitFiltration E tau.1 0 := by
      intro u _
      rw [h]
      rfl
    have := hcond.minimal 0 hzero
    omega
  have hram : ramificationIndex E K ≠ 1 := by
    intro hunr
    have hzero : QuasiCharTrivialOnUnitFiltration E tau.1 0 := by
      intro u hu
      obtain ⟨v, _, hv⟩ := (unramified_norm_unitFiltration E K hunr 0).2 u hu
      exact tau.eq_one_on_normRange E K u ⟨v, hv⟩
    have := hcond.minimal 0 hzero
    omega
  let P := primeCyclicPreparation E K hram
  have hcond' := ramifiedNormCharacter_conductor E K P.ht P.hres P.piK P.hpiK P.hgen tau htau
  have ht : P.t = t := by have := hcond'.unique hcond; omega
  exact ⟨ht ▸ P.ht, P.hres, htau⟩

end DescendedChart

section PrimitiveModel

variable (F U E K : Type) [Field F] [Field U] [Field E] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F U] [Algebra F E] [Algebra F K] [Algebra U K] [Algebra E K]
  [IsScalarTower F U K] [IsScalarTower F E K]
  [ValuativeExtension F U] [ValuativeExtension F E]
  [ValuativeExtension U K] [ValuativeExtension F K]
  [Module.Finite F U] [Module.Finite F E] [Module.Finite F K]
  [Module.Finite U K] [Module.Finite E K]
  [PrimeCyclicExtension F U] [PrimeCyclicExtension F E] [PrimeCyclicExtension U K]

/-- Crossed norm characters prove that a nontrivial commutator prevents
the common pullback from descending from `F`. The descent is excluded
for every continuous quasi-character, with no unitary restriction. -/
theorem model_primitive
    (hUdegree : Module.finrank F U = 2) (hEdegree : Module.finrank F E = 2)
    (hKdegree : Module.finrank U K = 2)
    (hne : (normUnits F U).range ≠ (normUnits F E).range)
    (sigma : Gal(U/F)) (tau : NormCharacter U K) (htau : tau ≠ 1)
    (chi : ContinuousQuasiChar U)
    (hcomm : ∀ v : Uˣ, chi (Units.map sigma.toMonoidHom v) / chi v = tau.1 v) :
    ¬ ∃ lambda : ContinuousQuasiChar F,
      normQuasiChar U K chi = normQuasiChar F K lambda := by
  rintro ⟨lambda, hlambda⟩
  have htower (x : Kˣ) : normUnits F U (normUnits U K x) = normUnits F K x := by
    apply Units.ext
    exact Basic.norm_tower x.val
  let mu : NormCharacter U K := ⟨chi / normQuasiChar F U lambda, by
    apply ContinuousMonoidHom.ext
    intro x
    change chi (normUnits U K x) / lambda (normUnits F U (normUnits U K x)) = 1
    have h := DFunLike.congr_fun hlambda x
    change chi (normUnits U K x) = lambda (normUnits F K x) at h
    rw [htower, h, div_self']⟩
  let e := Characters.crossedNormEquivOfTowers F U E K Nat.prime_two
    hUdegree hEdegree hKdegree hne
  let omega := e.symm mu
  have hmu : normQuasiChar F U omega.1 = chi / normQuasiChar F U lambda :=
    congrArg Subtype.val (e.apply_symm_apply mu)
  have hvalue (v : Uˣ) :
      chi v = omega.1 (normUnits F U v) * lambda (normUnits F U v) := by
    have h := DFunLike.congr_fun hmu v
    change omega.1 (normUnits F U v) = chi v / lambda (normUnits F U v) at h
    have h' := congrArg (fun z : ℂˣ => z * lambda (normUnits F U v)) h
    simpa only [div_mul_cancel] using h'.symm
  apply htau
  apply NormCharacter.ext
  apply ContinuousMonoidHom.ext
  intro v
  have hnorm : normUnits F U (Units.map sigma.toMonoidHom v) = normUnits F U v := by
    apply Units.ext
    exact Algebra.norm_eq_of_algEquiv sigma v.val
  have h := hcomm v
  rw [hvalue, hvalue, hnorm, div_self'] at h
  exact h.symm

end PrimitiveModel

section Models

variable (F U E K : Type) [Field F] [Field U] [Field E] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F U] [Algebra F E] [Algebra F K] [Algebra U K] [Algebra E K]
  [IsScalarTower F U K] [IsScalarTower F E K]
  [ValuativeExtension F U] [ValuativeExtension F E]
  [ValuativeExtension U K] [ValuativeExtension E K] [ValuativeExtension F K]
  [Module.Finite F U] [Module.Finite F E] [Module.Finite F K]
  [Module.Finite U K] [Module.Finite E K]
  [PrimeCyclicExtension F U] [PrimeCyclicExtension F E]
  [PrimeCyclicExtension U K] [PrimeCyclicExtension E K]

omit [ValuativeExtension F K] [Module.Finite F U] [Module.Finite F E]
  [Module.Finite F K] [Module.Finite E K] [PrimeCyclicExtension F U]
  [PrimeCyclicExtension F E] [PrimeCyclicExtension U K] [PrimeCyclicExtension E K] in
private theorem model_upper_unramified
    (hunr : ramificationIndex F U = 1) (hEram : ramificationIndex F E = 2)
    (hKdegree : Module.finrank U K = 2) : ramificationIndex E K = 1 := by
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
    rw [hKdegree] at hdeg
    nlinarith
  omega

/-- **Compatible minimal characters on the full multiplicative groups**
(paper Theorem `D:UR:models`).

The four prime-cyclic degree-two edges and the two scalar towers are the
actual biquadratic local-field diamond. Only the lower unramified edge
and the lower ramified break are inputs; the upper unramified edge and
the upper ramified break are proved in the construction.

`Psi` is the scaled additive character from `D:UR:tauchart`. The given
units `c,d` satisfy the paper's exact equation and actual conjugation.
The result constructs both global continuous group homomorphisms, their
exact conductors, a primitive common norm pullback, and all three full
subgroup identities. Both field characteristics and arbitrary continuous
quasi-characters in the non-descent assertion are retained. -/
theorem models
    (hunr : ramificationIndex F U = 1)
    (hUdegree : Module.finrank F U = 2) (hEdegree : Module.finrank F E = 2)
    (hUKdegree : Module.finrank U K = 2) (hEKdegree : Module.finrank E K = 2)
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (htpos : 0 < t) (hres : residueDegree F E = 1)
    (tau : NormCharacter F E) (htau : tau ≠ 1)
    (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (hchart : ∀ (x : F) (hx : x ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
      tau.1 (principalUnitOf F (t / 2) (-x) (neg_mem_lattice F hx)) = Psi x)
    (sigma : Gal(U/F)) (hsigma : sigma ≠ 1)
    (c : F) (hc : ord F c = 0) (d : U) (hd : ord U d = 0)
    (hdc : d ^ 2 - d = algebraMap F U c) (hconj : sigma d = 1 - d) :
    ∃ (chiU : ContinuousQuasiChar U) (chiE : ContinuousQuasiChar E),
      IsMultiplicativeConductor U chiU (t + 1) ∧
      IsMultiplicativeConductor E chiE (t + 1) ∧
      normQuasiChar U K chiU = normQuasiChar E K chiE ∧
      (¬ ∃ lambda : ContinuousQuasiChar F,
        normQuasiChar U K chiU = normQuasiChar F K lambda) ∧
      (∀ v : Uˣ, chiU (Units.map sigma.toMonoidHom v) / chiU v =
        normQuasiChar F U tau.1 v) ∧
      (∀ (z : U) (hz : z ∈ lattice U ((t / 2 + 1 : ℕ) : ℤ)),
        chiU (principalUnitOf U (t / 2) (-z) (neg_mem_lattice U hz)) =
          tracePullbackAddChar F U Psi (d ^ 2 * z)) ∧
      (∀ (z : E) (hz : z ∈ lattice E ((t / 2 + 1 : ℕ) : ℤ)),
        chiE (principalUnitOf E (t / 2) (-z) (neg_mem_lattice E hz)) =
          tracePullbackAddChar F E Psi (algebraMap F E c * z)) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have hEram : ramificationIndex F E = 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa only [hEdegree, hres, mul_one] using h.symm
  have hunrEK := model_upper_unramified F U E K hunr hEram hUKdegree
  have hcondTau := ramifiedNormCharacter_conductor F E ht hres pi hpi hgen tau htau
  let tauU := Characters.crossedNormHom F U E K tau
  have hcondTauU : IsMultiplicativeConductor U tauU.1 (t + 1) :=
    (unramified_multiplicativeConductor_compNorm F U hunr tau.1 (t + 1)).mpr hcondTau
  obtain ⟨htUK, hresUK, htauU⟩ := modelNormCharacter_break U K t tauU hcondTauU
  have hne : (normUnits F U).range ≠ (normUnits F E).range := by
    intro heq
    apply htauU
    apply NormCharacter.ext
    apply ContinuousMonoidHom.ext
    intro v
    change tau.1 (normUnits F U v) = 1
    apply tau.eq_one_on_normRange F E
    rw [← heq]
    exact ⟨v, rfl⟩
  obtain ⟨chiU, hcondU, hcomm, hchartU⟩ :=
    unramifiedModel F U E hunr hUdegree hEdegree sigma hsigma d hd hconj
      t htpos tau Psi hPsi hchart
  obtain ⟨chiE, hcompatible⟩ := model_descends F U E K hUdegree sigma hsigma tau chiU hcomm
  let PsiU := tracePullbackAddChar F U Psi
  let PsiE := tracePullbackAddChar F E Psi
  have hPsiE : IsAdditiveConductor E PsiE (-((t + 1 : ℕ) : ℤ)) := by
    have h := additiveConductor_compTrace_cyclicPrime F E ht hres pi hpi hgen hPsi
    rw [hEdegree] at h
    have hindex : (2 : ℤ) * (-((t + 1 : ℕ) : ℤ)) +
        (((2 - 1) * (t + 1) : ℕ) : ℤ) = -((t + 1 : ℕ) : ℤ) := by
      norm_num
      omega
    exact hindex ▸ h
  have hPsiTrivF : AddCharTrivialOnLattice F Psi ((t + 1 : ℕ) : ℤ) := by
    simpa only [neg_neg] using hPsi.trivial
  have hTauUChart (x : U) (hx : x ∈ lattice U ((t / 2 + 1 : ℕ) : ℤ)) :
      tauU.1 (principalUnitOf U (t / 2) (-x) (neg_mem_lattice U hx)) = PsiU x := by
    change normQuasiChar F U tau.1
      (principalUnitOf U (t / 2) (-x) (neg_mem_lattice U hx)) = tracePullbackAddChar F U Psi x
    have h := unramifiedNormChart F U hunr hUdegree sigma hsigma (t / 2) (t + 1)
      (by omega) tau.1 Psi hPsiTrivF hchart
      (principalUnitOf U (t / 2) (-x) (neg_mem_lattice U hx))
      (principalUnitOf_mem U (t / 2) _ _)
    simpa only [coe_principalUnitOf, sub_add_eq_sub_sub, sub_self, zero_sub, neg_neg] using h
  have hKChart (v : Kˣ) (hv : v ∈ unitFiltration K (t / 2 + 1)) :
      normQuasiChar E K chiE v = tracePullbackAddChar E K PsiE
        (algebraMap E K (algebraMap F E c) * (1 - v.val)) := by
    rw [hcompatible, ramifiedModel_pullbackChart U K htUK htpos hresUK hUKdegree
      tauU htauU PsiU hTauUChart d hd chiU hchartU v hv]
    change Psi (trace F U (trace U K (algebraMap U K (d ^ 2 - d) * (1 - v.val)))) =
      Psi (trace F E (trace E K (algebraMap E K (algebraMap F E c) * (1 - v.val))))
    rw [hdc, ← IsScalarTower.algebraMap_apply F U K,
      ← IsScalarTower.algebraMap_apply F E K]
    change Psi (Algebra.trace F U (Algebra.trace U K _)) =
      Psi (Algebra.trace F E (Algebra.trace E K _))
    rw [Basic.trace_tower, Basic.trace_tower]
  have hcE : ord E (algebraMap F E c) = 0 := by rw [ord_algebraMap, hc, nsmul_zero]
  have hcIntegral : algebraMap F E c ∈ lattice E 0 := by rw [mem_lattice, hcE]; simp
  have hPsiTrivE : AddCharTrivialOnLattice E PsiE ((t + 1 : ℕ) : ℤ) := by
    simpa only [neg_neg] using hPsiE.trivial
  have hchartE (u : Eˣ) (hu : u ∈ unitFiltration E (t / 2 + 1)) :
      chiE u = PsiE (algebraMap F E c * (1 - u.val)) :=
    modelChart_of_unramifiedNorm E K hunrEK hEKdegree (t / 2) (t + 1) (by omega)
      PsiE hPsiTrivE (algebraMap F E c) hcIntegral chiE hKChart u hu
  have hcondE := modelChart_conductor E (t / 2) t (by omega) PsiE hPsiE
    (algebraMap F E c) hcE chiE hchartE
  refine ⟨chiU, chiE, hcondU, hcondE, hcompatible.symm,
    model_primitive F U E K hUdegree hEdegree hUKdegree hne sigma tauU htauU chiU hcomm,
    hcomm, hchartU, ?_⟩
  intro z hz
  rw [hchartE _ (principalUnitOf_mem E (t / 2) _ _), coe_principalUnitOf]
  congr 2
  ring

end Models

end

end LanglandsSecondMainLemma.Dyadic.UR
