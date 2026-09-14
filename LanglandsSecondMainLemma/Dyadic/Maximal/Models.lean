import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Dyadic.Maximal.Compatibility
import LanglandsSecondMainLemma.Local.NormDescent
import LanglandsSecondMainLemma.Ramification.LeadingTerm

/-!
# Dyadic / Maximal / Models

The construction of the actual global core characters in Paper Theorem
`D:MX:cores`.  In particular, compatibility of the three deep charts is
used to prove that a genuine commutator character kills the upper norm
range; it is not treated as an extension theorem by itself.
-/

namespace LanglandsSecondMainLemma.Dyadic.Maximal

open LanglandsFirstMainLemma

noncomputable section

/-! ## Algebraic and ramification bridges used by the construction -/

/-- The continuous action of a local-field automorphism on nonzero
elements. -/
private noncomputable def galoisUnitsHom
    (F E : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [ValuativeExtension F E]
    [Module.Finite F E]
    (sigma : Gal(E/F)) : ContinuousMonoidHom Eˣ Eˣ :=
  ⟨Units.map sigma.toRingEquiv.toMonoidHom,
    (by
      have hsigma : Continuous sigma := by
        apply continuous_of_continuousAt_zero sigma.toAlgHom.toAddMonoidHom
        change Filter.Tendsto (fun x : E => sigma x) (nhds 0) (nhds (sigma 0))
        rw [map_zero, (lattice_nhds_zero_hasBasis E).tendsto_right_iff]
        intro n _
        filter_upwards [(lattice_isOpen E n).mem_nhds (by simp)] with x hx
        change (n : WithTop ℤ) ≤ ord E (sigma x)
        rw [ord_galoisConjugate]
        exact hx
      exact hsigma.units_map _)⟩

@[simp]
private theorem galoisUnitsHom_apply
    (F E : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [ValuativeExtension F E]
    [Module.Finite F E]
    (sigma : Gal(E/F)) (x : Eˣ) :
    galoisUnitsHom F E sigma x =
      Units.map sigma.toRingEquiv.toMonoidHom x := rfl

/-- Norm is equivariant for an automorphism of a normal tower and its
restriction to the intermediate field. -/
private theorem norm_restrictNormal
    (F L K : Type*) [Field F] [Field L] [Field K]
    [Algebra F L] [Algebra L K] [Algebra F K]
    [IsScalarTower F L K] [Module.Free L K] [Module.Finite L K]
    [Normal F L]
    (sigma : Gal(K/F)) (x : K) :
    Algebra.norm L (sigma x) =
      AlgEquiv.restrictNormalHom L sigma (Algebra.norm L x) := by
  let rho : Gal(L/F) := AlgEquiv.restrictNormalHom L sigma
  have hcomm :
      (algebraMap L K).comp rho.toRingEquiv.toRingHom =
        sigma.toRingEquiv.toRingHom.comp (algebraMap L K) := by
    ext y
    exact AlgEquiv.restrictNormal_commutes sigma L y
  have htransport := Algebra.norm_eq_of_equiv_equiv
    rho.toRingEquiv sigma.toRingEquiv hcomm x
  calc
    Algebra.norm L (sigma x) = rho (rho.symm (Algebra.norm L (sigma x))) :=
      (rho.apply_symm_apply _).symm
    _ = rho (Algebra.norm L x) := congrArg rho htransport.symm

/-- Residue degrees multiply through the accepted valuation-compatible
structure on an actual intermediate field. -/
private theorem intermediate_residueDegree_mul
    {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]
    (L : IntermediateField F K) :
    letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
    letI : TopologicalSpace L := Basic.intermediateFieldTopology L
    letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
    letI : ValuativeExtension F L :=
      Basic.intermediateField_lowerValuativeExtension L
    letI : ValuativeExtension L K :=
      Basic.intermediateField_upperValuativeExtension L
    residueDegree F L * residueDegree L K = residueDegree F K := by
  letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
  letI : TopologicalSpace L := Basic.intermediateFieldTopology L
  letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
  letI : ValuativeExtension F L :=
    Basic.intermediateField_lowerValuativeExtension L
  letI : ValuativeExtension L K :=
    Basic.intermediateField_upperValuativeExtension L
  letI : IsScalarTower
      (ringOfIntegers F) (ringOfIntegers L) (ringOfIntegers K) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap F K (x : F) = algebraMap L K (algebraMap F L (x : F))
      rw [← IsScalarTower.algebraMap_apply F L K])
  letI : IsLocalHom
      (algebraMap (ringOfIntegers F) (ringOfIntegers L)) := inferInstance
  letI : IsLocalHom
      (algebraMap (ringOfIntegers L) (ringOfIntegers K)) := inferInstance
  rw [residueDegree_eq_finrank_residueField,
    residueDegree_eq_finrank_residueField,
    residueDegree_eq_finrank_residueField]
  exact Module.finrank_mul_finrank
    (ResidueField F) (ResidueField L) (ResidueField K)

private def supAssemble
    {G : Type*} [CommGroup G] (H₁ H₂ : Subgroup G) :
    H₁ × H₂ →* ↑(H₁ ⊔ H₂) :=
  { toFun := fun x ↦ ⟨(x.1 : G) * (x.2 : G),
        (H₁ ⊔ H₂).mul_mem (Subgroup.mem_sup_left x.1.property)
          (Subgroup.mem_sup_right x.2.property)⟩
    map_one' := by ext; simp
    map_mul' := by
      intro x y
      ext
      simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
      ac_rfl }

private def supPrescribed
    {G A : Type*} [CommGroup G] [CommGroup A]
    (H₁ H₂ : Subgroup G) (chi₁ : H₁ →* A) (chi₂ : H₂ →* A) :
    H₁ × H₂ →* A :=
  (chi₁.comp (MonoidHom.fst H₁ H₂)) *
    (chi₂.comp (MonoidHom.snd H₁ H₂))

/-- Two characters on subgroups of an abelian group which agree on their
intersection define a genuine character on the generated subgroup.  This
is the algebraic datum required by `compatiblePair_extendFamily`. -/
private noncomputable def characterOnSup
    {G A : Type*} [CommGroup G] [CommGroup A]
    (H₁ H₂ : Subgroup G) (chi₁ : H₁ →* A) (chi₂ : H₂ →* A)
    (hagree : ∀ (x₁ : H₁) (x₂ : H₂), (x₁ : G) = (x₂ : G) →
      chi₁ x₁ = chi₂ x₂) :
    ↑(H₁ ⊔ H₂) →* A := by
  have hassemble : Function.Surjective (supAssemble H₁ H₂) := by
    intro x
    obtain ⟨y, z, hyz⟩ := (Subgroup.mem_sup'.mp x.property)
    refine ⟨(y, z), ?_⟩
    exact Subtype.ext hyz
  have hker : (supAssemble H₁ H₂).ker ≤
      (supPrescribed H₁ H₂ chi₁ chi₂).ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hprod : (x.1 : G) * (x.2 : G) = 1 := congrArg Subtype.val hx
    have hx₁mem₂ : (x.1 : G) ∈ H₂ := by
      have heq : (x.1 : G) = (x.2 : G)⁻¹ :=
        eq_inv_of_mul_eq_one_left hprod
      rw [heq]
      exact H₂.inv_mem x.2.property
    have hcompat := hagree x.1 ⟨x.1, hx₁mem₂⟩ rfl
    change chi₁ x.1 * chi₂ x.2 = 1
    have hx₂ : x.2 = (⟨x.1, hx₁mem₂⟩ : H₂)⁻¹ := by
      apply Subtype.ext
      exact eq_inv_of_mul_eq_one_right hprod
    rw [hx₂, map_inv, ← hcompat]
    simp
  exact (supAssemble H₁ H₂).liftOfSurjective hassemble
    ⟨supPrescribed H₁ H₂ chi₁ chi₂, hker⟩

private theorem characterOnSup_assemble
    {G A : Type*} [CommGroup G] [CommGroup A]
    (H₁ H₂ : Subgroup G) (chi₁ : H₁ →* A) (chi₂ : H₂ →* A)
    (hagree : ∀ (x₁ : H₁) (x₂ : H₂), (x₁ : G) = (x₂ : G) →
      chi₁ x₁ = chi₂ x₂) (x : H₁ × H₂) :
    characterOnSup H₁ H₂ chi₁ chi₂ hagree (supAssemble H₁ H₂ x) =
      chi₁ x.1 * chi₂ x.2 := by
  unfold characterOnSup
  apply MonoidHom.liftOfRightInverse_comp_apply

private theorem characterOnSup_left
    {G A : Type*} [CommGroup G] [CommGroup A]
    (H₁ H₂ : Subgroup G) (chi₁ : H₁ →* A) (chi₂ : H₂ →* A)
    (hagree : ∀ (x₁ : H₁) (x₂ : H₂), (x₁ : G) = (x₂ : G) →
      chi₁ x₁ = chi₂ x₂) :
    (characterOnSup H₁ H₂ chi₁ chi₂ hagree).comp
        (Subgroup.inclusion le_sup_left) = chi₁ := by
  apply MonoidHom.ext
  intro x
  have h := characterOnSup_assemble H₁ H₂ chi₁ chi₂ hagree (x, 1)
  change characterOnSup H₁ H₂ chi₁ chi₂ hagree
    ⟨x, Subgroup.mem_sup_left x.property⟩ = chi₁ x
  rw [show ⟨(x : G), Subgroup.mem_sup_left x.property⟩ =
    supAssemble H₁ H₂ (x, 1) by ext; simp [supAssemble]]
  simpa using h

private theorem characterOnSup_right
    {G A : Type*} [CommGroup G] [CommGroup A]
    (H₁ H₂ : Subgroup G) (chi₁ : H₁ →* A) (chi₂ : H₂ →* A)
    (hagree : ∀ (x₁ : H₁) (x₂ : H₂), (x₁ : G) = (x₂ : G) →
      chi₁ x₁ = chi₂ x₂) :
    (characterOnSup H₁ H₂ chi₁ chi₂ hagree).comp
        (Subgroup.inclusion le_sup_right) = chi₂ := by
  apply MonoidHom.ext
  intro x
  have h := characterOnSup_assemble H₁ H₂ chi₁ chi₂ hagree (1, x)
  change characterOnSup H₁ H₂ chi₁ chi₂ hagree
    ⟨x, Subgroup.mem_sup_right x.property⟩ = chi₂ x
  rw [show ⟨(x : G), Subgroup.mem_sup_right x.property⟩ =
    supAssemble H₁ H₂ (1, x) by ext; simp [supAssemble]]
  simpa using h

/-- A chosen generator at a positive lower break admits the normalized
uniformizer expansion required by the leading-term lemma. -/
private theorem generatorExpansion
    (E M : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    [Algebra E M] [ValuativeExtension E M]
    [Module.Free E M] [Module.Finite E M] [PrimeCyclicExtension E M]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak E M t)
    (htpos : 1 ≤ t) :
    ∃ (sigma : lowerRamificationGroup E M 0) (pi c : M),
      (sigma : Gal(M/E)) = PrimeCyclicExtension.generator E M ∧
      (ValuativeRel.valuation M).IsUniformizer pi ∧
      ord M c = 0 ∧
      (sigma : Gal(M/E)) pi = pi * (1 + c * pi ^ t) := by
  let g : Gal(M/E) := PrimeCyclicExtension.generator E M
  have hgshell :=
    PrimeCyclicExtension.generator_mem_break_and_not_mem_succ E M ht
  have hgzero : g ∈ lowerRamificationGroup E M 0 :=
    lowerRamificationGroup_mono E M (by omega) hgshell.1
  let sigma : lowerRamificationGroup E M 0 := ⟨g, hgzero⟩
  let pi : M := Ramification.inertiaUniformizer (F := E) (K := M)
  have hpi : (ValuativeRel.valuation M).IsUniformizer pi :=
    Ramification.inertiaUniformizer_isUniformizer (F := E) (K := M)
  have hlower : (((t : ℤ) + 1 : ℤ) : WithTop ℤ) ≤
      ord M ((sigma : Gal(M/E)) pi - pi) := by
    exact (Ramification.mem_lowerRamificationGroup_iff_inertiaUniformizer
      (F := E) (K := M) sigma (t : ℤ)).1 hgshell.1
  have hnot : ¬ ((((t : ℤ) + 2 : ℤ) : WithTop ℤ) ≤
      ord M ((sigma : Gal(M/E)) pi - pi)) := by
    intro hdeep
    apply hgshell.2
    apply (Ramification.mem_lowerRamificationGroup_iff_inertiaUniformizer
      (F := E) (K := M) sigma ((t : ℤ) + 1)).2
    exact hdeep
  have hdiff : ord M ((sigma : Gal(M/E)) pi - pi) =
      (((t : ℤ) + 1 : ℤ) : WithTop ℤ) := by
    rw [← withTopInt_le_and_not_succ_le_iff_eq]
    simpa only [add_assoc, one_add_one_eq_two] using ⟨hlower, hnot⟩
  let c : M := ((sigma : Gal(M/E)) pi - pi) / pi ^ (t + 1)
  have hc : ord M c = 0 := by
    dsimp only [c]
    rw [ord_div, hdiff, ord_pow, ord_uniformizer M hpi]
    norm_num
  refine ⟨sigma, pi, c, rfl, hpi, hc, ?_⟩
  dsimp only [c]
  have hpipow : pi ^ (t + 1) ≠ 0 := pow_ne_zero _ hpi.ne_zero
  field_simp
  ring

/-- Every multiplicative element is moved by the chosen upper generator by
a principal unit at least as deep as the lower break. -/
private theorem generatorRatio_mem
    (E M : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    [Algebra E M] [ValuativeExtension E M]
    [Module.Free E M] [Module.Finite E M] [PrimeCyclicExtension E M]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak E M t)
    (htpos : 1 ≤ t) (x : Mˣ) :
    Units.map (PrimeCyclicExtension.generator E M).toRingEquiv.toMonoidHom x / x
      ∈ unitFiltration M t := by
  obtain ⟨sigma, pi, c, hsigma, hpi, hc, hexpansion⟩ :=
    generatorExpansion E M ht htpos
  let m : ℤ := localUnitOrder M x
  have hxord : ord M (x : M) = (m : WithTop ℤ) := by
    simpa only [m] using (coe_localUnitOrder M x).symm
  have hsigmaord : ord M ((sigma : Gal(M/E)) (x : M)) =
      (m : WithTop ℤ) := by rw [ord_galoisConjugate, hxord]
  have hbound := Ramification.leadingTerm_lowerBound sigma pi c hpi
    htpos hc hexpansion (Units.ne_zero x) hxord
  have hratioOrder : ord M
      (((Units.map (sigma : Gal(M/E)).toRingEquiv.toMonoidHom x / x : Mˣ) : M)) = 0 := by
    simp only [Units.val_div_eq_div_val, Units.coe_map]
    rw [show (sigma : Gal(M/E)).toRingEquiv.toMonoidHom (x : M) =
      (sigma : Gal(M/E)) (x : M) by rfl]
    rw [ord_div, ord_galoisConjugate, hxord]
    simp
  have hratioUnit :
      Units.map (sigma : Gal(M/E)).toRingEquiv.toMonoidHom x / x ∈
        unitGroup M :=
    (mem_unitGroup_iff_ord_eq_zero M _).2 hratioOrder
  have hquotient : (((sigma : Gal(M/E)) (x : M) - (x : M)) / (x : M))
      ∈ lattice M (t : ℤ) := by
    apply (div_mem_lattice_iff M (x : M)
      ((sigma : Gal(M/E)) (x : M) - (x : M)) m (t : ℤ) hxord).2
    rw [mem_lattice]
    simpa only [WithTop.coe_add] using hbound
  have hcongruent : CongruentAtDepth (t : ℤ)
      ((Units.map (sigma : Gal(M/E)).toRingEquiv.toMonoidHom x / x : Mˣ) : M) 1 := by
    rw [congruentAtDepth_iff_sub_mem_lattice]
    simp only [Units.val_div_eq_div_val, Units.coe_map]
    rw [show (sigma : Gal(M/E)).toRingEquiv.toMonoidHom (x : M) =
      (sigma : Gal(M/E)) (x : M) by rfl]
    rw [div_sub_one (Units.ne_zero x)]
    exact hquotient
  have hmem := (div_mem_unitFiltration_iff_congruentAtDepth M t
    (Units.map (sigma : Gal(M/E)).toRingEquiv.toMonoidHom x / x) 1
    hratioUnit (unitGroup M).one_mem).2 hcongruent
  rw [div_one, hsigma] at hmem
  exact hmem

/-- At a positive ramification break, the conjugate-ratio map on an
odd (more generally residue-prime-to) positive unit row maps onto the
row obtained by adding the break.  This is the graded form of the first
nonzero lower ramification term used in the paper. -/
private theorem generatorRatio_graded_surjective
    (E M : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    [Algebra E M] [ValuativeExtension E M]
    [Module.Free E M] [Module.Finite E M] [PrimeCyclicExtension E M]
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak E M t)
    (htpos : 1 ≤ t) (hrpos : 1 ≤ r)
    (hrprime : ¬ (residueCharacteristic M : ℤ) ∣ (r : ℤ))
    (v : unitFiltration M (r + t)) :
    ∃ u : unitFiltration M r,
      (Units.map (PrimeCyclicExtension.generator E M).toRingEquiv.toMonoidHom
          (u : Mˣ) / (u : Mˣ)) / (v : Mˣ) ∈
        unitFiltration M (r + t + 1) := by
  classical
  obtain ⟨sigma, pi, c, hsigma, hpi, hc, hexpansion⟩ :=
    generatorExpansion E M ht htpos
  let g : Gal(M/E) := PrimeCyclicExtension.generator E M
  have hratioMem (d : ℕ) (hdpos : 1 ≤ d)
      (u : unitFiltration M d) :
      Units.map g.toRingEquiv.toMonoidHom (u : Mˣ) / (u : Mˣ) ∈
        unitFiltration M (d + t) := by
    let y : M := ((u : Mˣ) : M) - 1
    have huord : ord M ((u : Mˣ) : M) = 0 :=
      (mem_unitGroup_iff_ord_eq_zero M (u : Mˣ)).1
        (unitFiltration_le_unitGroup M d u.property)
    have hmove : (((d + t : ℕ) : ℤ) : WithTop ℤ) ≤
        ord M (g ((u : Mˣ) : M) - ((u : Mˣ) : M)) := by
      by_cases hy : y = 0
      · have hu : ((u : Mˣ) : M) = 1 := sub_eq_zero.mp hy
        rw [hu, map_one, sub_self, ord_zero]
        exact le_top
      · let yu : Mˣ := Units.mk0 y hy
        let m : ℤ := localUnitOrder M yu
        have hyord : ord M y = (m : WithTop ℤ) := by
          simpa only [yu, Units.val_mk0, m] using (coe_localUnitOrder M yu).symm
        have hymem : y ∈ lattice M (d : ℤ) := by
          have hdisp := (mem_unitFiltration_succ_iff_sub_mem_lattice M
            (d - 1) (u : Mˣ)).1 (by
              simpa only [Nat.sub_add_cancel hdpos] using u.property)
          simpa only [Nat.sub_add_cancel hdpos, y] using hdisp
        have hyd : ((d : ℤ) : WithTop ℤ) ≤ ord M y := by
          rw [mem_lattice] at hymem
          exact hymem
        have hdm : (d : ℤ) ≤ m := by
          rw [hyord] at hyd
          exact WithTop.coe_le_coe.mp hyd
        have hbound := Ramification.leadingTerm_lowerBound sigma pi c hpi
          htpos hc hexpansion hy hyord
        have hmono : (((d + t : ℕ) : ℤ) : WithTop ℤ) ≤
            ((m + (t : ℤ)) : WithTop ℤ) := by
          norm_cast
          push_cast
          omega
        have haction : (sigma : Gal(M/E)) y - y =
            g ((u : Mˣ) : M) - ((u : Mˣ) : M) := by
          rw [show (sigma : Gal(M/E)) = g by exact hsigma]
          dsimp only [y]
          rw [map_sub, map_one]
          ring
        rw [← haction]
        exact hmono.trans hbound
    have hquot :
        (g ((u : Mˣ) : M) - ((u : Mˣ) : M)) / ((u : Mˣ) : M) ∈
          lattice M ((d + t : ℕ) : ℤ) := by
      apply (div_mem_lattice_iff M ((u : Mˣ) : M)
        (g ((u : Mˣ) : M) - ((u : Mˣ) : M))
        0 ((d + t : ℕ) : ℤ) huord).2
      rw [mem_lattice]
      simpa only [zero_add] using hmove
    rw [show d + t = (d + t - 1) + 1 by omega,
      mem_unitFiltration_succ_iff_sub_mem_lattice]
    simp only [Units.val_div_eq_div_val, Units.coe_map]
    rw [div_sub_one (Units.ne_zero (u : Mˣ))]
    change (g ((u : Mˣ) : M) - ((u : Mˣ) : M)) /
      ((u : Mˣ) : M) ∈ lattice M (((d + t - 1 + 1 : ℕ) : ℤ))
    simpa only [Nat.sub_add_cancel (show 1 ≤ d + t by omega)] using hquot
  let ratioHom : unitFiltration M r →* unitFiltration M (r + t) :=
    { toFun := fun u ↦
        ⟨Units.map g.toRingEquiv.toMonoidHom (u : Mˣ) / (u : Mˣ),
          hratioMem r hrpos u⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        change Units.map g.toRingEquiv.toMonoidHom
            ((x : Mˣ) * (y : Mˣ)) / ((x : Mˣ) * (y : Mˣ)) =
          (Units.map g.toRingEquiv.toMonoidHom (x : Mˣ) / (x : Mˣ)) *
            (Units.map g.toRingEquiv.toMonoidHom (y : Mˣ) / (y : Mˣ))
        rw [map_mul]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ac_rfl }
  have hdenominator : unitFiltrationInside M (Nat.le_succ r) ≤
      ((unitGradedMk M (r + t)).comp ratioHom).ker := by
    intro u hu
    rw [MonoidHom.mem_ker]
    change unitGradedMk M (r + t) (ratioHom u) = 1
    rw [unitGradedMk_eq_one_iff]
    have hu' : (u : Mˣ) ∈ unitFiltration M (r + 1) :=
      (mem_unitFiltrationInside M (Nat.le_succ r) u).1 hu
    have hdeep := hratioMem (r + 1) (by omega) ⟨u, hu'⟩
    change Units.map g.toRingEquiv.toMonoidHom (u : Mˣ) / (u : Mˣ) ∈
      unitFiltration M (r + t + 1)
    have heq : r + 1 + t = r + t + 1 := by omega
    rw [← heq]
    exact hdeep
  let gradedHom : UnitGradedPiece M r →* UnitGradedPiece M (r + t) :=
    QuotientGroup.lift (unitFiltrationInside M (Nat.le_succ r))
      ((unitGradedMk M (r + t)).comp ratioHom) hdenominator
  have hgradedMk (u : unitFiltration M r) :
      gradedHom (unitGradedMk M r u) =
        unitGradedMk M (r + t) (ratioHom u) := by
    exact QuotientGroup.lift_mk _ hdenominator u
  have hinjective : Function.Injective gradedHom := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_bot]
      obtain ⟨u, rfl⟩ := unitGradedMk_surjective M r x
      rw [MonoidHom.mem_ker, hgradedMk,
        unitGradedMk_eq_one_iff] at hx
      apply (unitGradedMk_eq_one_iff M r u).2
      by_contra huNot
      have hyord : ord M (((u : Mˣ) : M) - 1) =
          ((r : ℤ) : WithTop ℤ) := by
        have hshell := (mem_unitFiltration_and_not_mem_succ_iff M
          (r - 1) (u : Mˣ)).1 ⟨by
            simpa only [Nat.sub_add_cancel hrpos] using u.property, by
            have heq : r - 1 + 2 = r + 1 := by omega
            rw [heq]
            exact huNot⟩
        simpa only [Nat.sub_add_cancel hrpos] using hshell
      have hyne : ((u : Mˣ) : M) - 1 ≠ 0 := by
        intro hy
        rw [hy, ord_zero] at hyord
        exact WithTop.top_ne_coe hyord
      have hexact := Ramification.leadingTerm sigma pi c hpi htpos hc
        hexpansion hyne hyord hrprime
      have haction :
          (sigma : Gal(M/E)) (((u : Mˣ) : M) - 1) -
              (((u : Mˣ) : M) - 1) =
            g ((u : Mˣ) : M) - ((u : Mˣ) : M) := by
        rw [show (sigma : Gal(M/E)) = g by exact hsigma]
        rw [map_sub, map_one]
        ring
      rw [haction] at hexact
      have huord : ord M ((u : Mˣ) : M) = 0 :=
        (mem_unitGroup_iff_ord_eq_zero M (u : Mˣ)).1
          (unitFiltration_le_unitGroup M r u.property)
      change Units.map g.toRingEquiv.toMonoidHom (u : Mˣ) / (u : Mˣ) ∈
        unitFiltration M (r + t + 1) at hx
      have hquot := (mem_unitFiltration_succ_iff_sub_mem_lattice M
        (r + t)
        (Units.map g.toRingEquiv.toMonoidHom (u : Mˣ) / (u : Mˣ))).1 hx
      have hquot' :
          (g ((u : Mˣ) : M) - ((u : Mˣ) : M)) /
              ((u : Mˣ) : M) ∈
            lattice M ((r + t + 1 : ℕ) : ℤ) := by
        simp only [Units.val_div_eq_div_val, Units.coe_map] at hquot
        have happ : g.toRingEquiv.toMonoidHom ((u : Mˣ) : M) =
            g ((u : Mˣ) : M) := rfl
        rw [happ] at hquot
        rw [div_sub_one (Units.ne_zero (u : Mˣ))] at hquot
        exact hquot
      have hmoveDeep : (((r + t + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
          ord M (g ((u : Mˣ) : M) - ((u : Mˣ) : M)) := by
        have := (div_mem_lattice_iff M ((u : Mˣ) : M)
          (g ((u : Mˣ) : M) - ((u : Mˣ) : M)) 0
          ((r + t + 1 : ℕ) : ℤ) huord).1 hquot'
        rw [mem_lattice] at this
        simpa only [zero_add] using this
      rw [hexact] at hmoveDeep
      exact (not_le_of_gt (WithTop.coe_lt_coe.mpr (by omega))) hmoveDeep
    · intro hx
      rw [hx]
      exact Subgroup.one_mem _
  letI : Fintype (UnitGradedPiece M r) := Fintype.ofFinite _
  letI : Fintype (UnitGradedPiece M (r + t)) := Fintype.ofFinite _
  have hcard : Fintype.card (UnitGradedPiece M r) =
      Fintype.card (UnitGradedPiece M (r + t)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      ((criticalNormPositiveUnitGradedResidueAddEquiv M (t := r)
          (by omega) pi hpi).toEquiv.trans
        (criticalNormPositiveUnitGradedResidueAddEquiv M (t := r + t)
          (by omega) pi hpi).toEquiv.symm)
  have hsurjective : Function.Surjective gradedHom :=
    ((Fintype.bijective_iff_injective_and_card gradedHom).2
      ⟨hinjective, hcard⟩).2
  obtain ⟨z, hz⟩ := hsurjective (unitGradedMk M (r + t) v)
  obtain ⟨u, rfl⟩ := unitGradedMk_surjective M r z
  rw [hgradedMk] at hz
  refine ⟨u, ?_⟩
  exact (unitFiltrationQuotientMk_eq_mk_iff M (Nat.le_succ (r + t))
    (ratioHom u) v).1 hz

/-- The stationary phase vanishes once the coefficient shifts the whole
unit displacement ideal into the additive character's trivial ideal. -/
private theorem corePhaseValue_eq_one_of_mem
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (Psi : ContinuousAddChar E) (c : E) {n : ℕ} {h J : ℤ}
    (hc : ord E c = (h : WithTop ℤ)) (hrel : h + (n + 1 : ℕ) = J)
    (hPsi : IsAdditiveConductor E Psi (-J)) (u : Eˣ)
    (hu : u ∈ unitFiltration E (n + 1)) : corePhaseValue E Psi c u = 1 := by
  apply hPsi.trivial
  have hdisp := (mem_unitFiltration_succ_iff_sub_mem_lattice E n u).1 hu
  have hneg : 1 - (u : E) ∈ lattice E (((n + 1 : ℕ) : ℤ)) := by
    simpa only [neg_sub] using neg_mem_lattice E hdisp
  have hmul := mul_mem_lattice E (show c ∈ lattice E h by rw [mem_lattice, hc]) hneg
  simpa only [corePhaseValue, neg_neg, hrel] using hmul

/-- A full stationary chart with an exact additive boundary gives the exact
multiplicative conductor; the predecessor witness is transported by the
actual coefficient, so no leading-class surrogate is used. -/
private theorem stationaryChart_exactConductor
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (Psi : ContinuousAddChar E) (c : E) (chi : ContinuousQuasiChar E)
    {d n : ℕ} (hn : 1 ≤ n) (hdn : d ≤ n)
    {h J : ℤ} (hc : ord E c = (h : WithTop ℤ))
    (hrel : h + (n + 1 : ℕ) = J)
    (hPsi : IsAdditiveConductor E Psi (-J))
    (hchart : ∀ u : unitFiltration E d,
      chi (u : Eˣ) = corePhaseValue E Psi c (u : Eˣ)) :
    IsMultiplicativeConductor E chi (n + 1) := by
  apply IsMultiplicativeConductor.of_succ_boundary
  · intro u hu
    have hud : u ∈ unitFiltration E d :=
      unitFiltration_antitone E (by omega) hu
    rw [hchart ⟨u, hud⟩]
    exact corePhaseValue_eq_one_of_mem E Psi c hc hrel hPsi u hu
  · intro htrivial
    obtain ⟨y, hyord, hPsiY⟩ := hPsi.exists_ord_eq_predecessor
    let z : E := y / c
    have hcne : c ≠ 0 := by
      intro hzero
      rw [hzero, ord_zero] at hc
      exact WithTop.coe_ne_top hc.symm
    have hzord : ord E z = ((n : ℤ) : WithTop ℤ) := by
      dsimp only [z]
      rw [ord_div, hyord, hc]
      have hinter : - -J - 1 - h = (n : ℤ) := by
        push_cast at hrel
        omega
      norm_cast
    have hz : z ∈ lattice E (n : ℤ) := by
      rw [mem_lattice, hzord]
    let u : Eˣ := lowerOneSubUnit E n (by omega) z hz
    have hu : u ∈ unitFiltration E n := by
      rw [show n = n - 1 + 1 by omega,
        mem_unitFiltration_succ_iff_sub_mem_lattice]
      have hneg := neg_mem_lattice E hz
      simpa only [u, coe_lowerOneSubUnit, sub_sub_cancel_left,
        Nat.sub_add_cancel hn] using hneg
    have hud : u ∈ unitFiltration E d :=
      unitFiltration_antitone E hdn hu
    have hcy : c * z = y := by
      dsimp only [z]
      field_simp
    have hvalue : chi u = Psi y := by
      rw [hchart ⟨u, hud⟩]
      simp only [corePhaseValue, u, coe_lowerOneSubUnit]
      rw [show 1 - (1 - z) = z by ring, hcy]
    exact hPsiY (hvalue.symm.trans (htrivial u hu))

/-- Extend a stationary character from its prescribed full unit layer and
retain both that literal restriction and its exact conductor. -/
private theorem extendStationaryCharacter
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (Psi : ContinuousAddChar E) (c : E)
    {d n : ℕ} (hn : 1 ≤ n) (hdn : d ≤ n)
    {h J : ℤ} (hc : ord E c = (h : WithTop ℤ))
    (hrel : h + (n + 1 : ℕ) = J)
    (hPsi : IsAdditiveConductor E Psi (-J))
    (R : unitFiltration E d →* ℂˣ)
    (hchart : ∀ u : unitFiltration E d,
      R u = corePhaseValue E Psi c (u : Eˣ)) :
    ∃ chi : ContinuousQuasiChar E,
      chi.toMonoidHom.comp (unitFiltration E d).subtype = R ∧
        IsMultiplicativeConductor E chi (n + 1) := by
  have hU : unitFiltration E (n + 1) ≤ unitFiltration E d :=
    unitFiltration_antitone E (by omega)
  have htrivial : R.comp (Subgroup.inclusion hU) = 1 := by
    apply MonoidHom.ext
    intro u
    rw [MonoidHom.one_apply]
    change R ⟨(u : Eˣ), hU u.property⟩ = 1
    rw [hchart]
    exact corePhaseValue_eq_one_of_mem E Psi c hc hrel hPsi (u : Eˣ) u.property
  obtain ⟨chi, hchiR⟩ := Local.characterExtension E
    (unitFiltration E d) (n + 1) (by omega) hU R htrivial
  have hchiChart : ∀ u : unitFiltration E d,
      chi (u : Eˣ) = corePhaseValue E Psi c (u : Eˣ) := by
    intro u
    have hu := DFunLike.congr_fun hchiR u
    exact hu.trans (hchart u)
  exact ⟨chi, hchiR,
    stationaryChart_exactConductor E Psi c chi hn hdn hc hrel hPsi hchiChart⟩

/-- A group with two elements has a unique nonidentity element. -/
private theorem eq_of_ne_one_of_card_two {G : Type*} [One G]
    (hcard : Nat.card G = 2) {x y : G} (hx : x ≠ 1) (hy : y ≠ 1) : x = y := by
  obtain ⟨_, _, hunique⟩ := (Nat.card_eq_two_iff' (1 : G)).mp hcard
  exact (hunique x hx).trans (hunique y hy).symm

/-- A norm character for a quadratic upper edge is fixed by every lower
automorphism which lifts to the normal tower. -/
private theorem quadraticNormCharacter_invariant
    (F L K : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F L] [Algebra L K] [Algebra F K] [IsScalarTower F L K]
    [ValuativeExtension F L] [ValuativeExtension L K]
    [Module.Free F L] [Module.Finite F L]
    [Module.Free L K] [Module.Finite L K]
    [PrimeCyclicExtension L K] [Normal F L]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak L K t)
    (hres : residueDegree L K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers L)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank L K = 2) (sigma : Gal(K/F))
    (mu : NormCharacter L K) :
    mu.1.pullback (galoisUnitsHom F L
      (AlgEquiv.restrictNormalHom L sigma)) = mu.1 := by
  let rho : Gal(L/F) := AlgEquiv.restrictNormalHom L sigma
  let muConj : ContinuousQuasiChar L :=
    mu.1.pullback (galoisUnitsHom F L rho)
  have hmuConjNorm : normQuasiChar L K muConj = 1 := by
    apply ContinuousMonoidHom.ext
    intro z
    rw [normQuasiChar_apply, ContinuousQuasiChar.one_apply]
    have hnorm : continuousNormUnits L K
        (Units.map sigma.toRingEquiv.toMonoidHom z) =
          Units.map rho.toRingEquiv.toMonoidHom (continuousNormUnits L K z) := by
      apply Units.ext
      simp only [Units.coe_map, coe_continuousNormUnits]
      exact norm_restrictNormal F L K sigma (z : K)
    have hkill := DFunLike.congr_fun mu.property
      (Units.map sigma.toRingEquiv.toMonoidHom z)
    dsimp only [muConj]
    change mu.1 (Units.map rho.toRingEquiv.toMonoidHom
      (continuousNormUnits L K z)) = 1
    rw [← hnorm]
    simpa only [normQuasiChar_apply, ContinuousQuasiChar.one_apply] using hkill
  let muConjNorm : NormCharacter L K := ⟨muConj, hmuConjNorm⟩
  letI : Finite (NormCharacter L K) :=
    ramifiedNormCharacter_finite L K ht hres pi hpi hgen
  have hcard : Nat.card (NormCharacter L K) = 2 := by
    rw [ramifiedNormCharacter_card L K ht hres pi hpi hgen]
    exact hdegree
  have hsubtype : muConjNorm = mu := by
    by_cases hmu : mu = 1
    · have hmuChar : mu.1 = 1 := congrArg Subtype.val hmu
      apply NormCharacter.ext
      dsimp only [muConjNorm, muConj]
      rw [hmuChar]
      apply ContinuousMonoidHom.ext
      intro x
      simp
    · have hmuConjNe : muConjNorm ≠ 1 := by
        intro hconj
        apply hmu
        have hconjChar : muConj = 1 := congrArg Subtype.val hconj
        apply NormCharacter.ext
        change mu.1 = 1
        apply ContinuousMonoidHom.ext
        intro x
        let y : Lˣ := Units.map rho.symm.toRingEquiv.toMonoidHom x
        have hy := DFunLike.congr_fun hconjChar y
        dsimp only [muConj] at hy
        rw [ContinuousQuasiChar.one_apply] at hy
        change mu.1 (Units.map rho.toRingEquiv.toMonoidHom y) = 1 at hy
        have hrho : Units.map rho.toRingEquiv.toMonoidHom y = x := by
          apply Units.ext
          simp only [Units.coe_map, y]
          exact rho.apply_symm_apply (x : L)
        rw [hrho] at hy
        exact hy
      exact eq_of_ne_one_of_card_two hcard hmuConjNe hmu
  exact congrArg Subtype.val hsubtype

/-! ## The canonical quadratic towers and compatible stationary charts -/

section Construction

variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]

-- These local instances use exactly the valuation and topology in `models`.
private abbrev modelFieldValuation (L : IntermediateField F K) : ValuativeRel L :=
  Basic.intermediateFieldValuativeRel L
attribute [local instance] modelFieldValuation

private abbrev modelFieldTopology (L : IntermediateField F K) : TopologicalSpace L :=
  Basic.intermediateFieldTopology L
attribute [local instance] modelFieldTopology

private abbrev modelFieldLocal (L : IntermediateField F K) :
    IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
attribute [local instance] modelFieldLocal

private abbrev modelFieldLowerValuation (L : IntermediateField F K) :
    ValuativeExtension F L := Basic.intermediateField_lowerValuativeExtension L
attribute [local instance] modelFieldLowerValuation

private abbrev modelFieldUpperValuation (L : IntermediateField F K) :
    ValuativeExtension L K := Basic.intermediateField_upperValuativeExtension L
attribute [local instance] modelFieldUpperValuation

/-- The algebraic part of the canonical tower, with named fields for the
information used below. Its constructor derives both cyclic edges from `hG`. -/
private class QuadraticTower (L : IntermediateField F K) : Prop where
  lower : PrimeCyclicExtension F L
  upper : PrimeCyclicExtension L K
  upper_degree : Module.finrank L K = 2
attribute [local instance] QuadraticTower.lower QuadraticTower.upper

private theorem quadraticTower [IsGalois F K]
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (L : IntermediateField F K) (hL : Module.finrank F L = 2) :
    QuadraticTower L := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hdegree, hlower, hupper⟩ :=
    Basic.intermediateField_tower_compatible Nat.prime_two hG L hL
  exact ⟨PrimeCyclicExtension.ofCyclicPrimeExtension F L hlower,
    PrimeCyclicExtension.ofCyclicPrimeExtension L K hupper, hdegree⟩

private theorem intermediate_residueDegrees_one
    (L : IntermediateField F K) (hres : residueDegree F K = 1) :
    residueDegree F L = 1 ∧ residueDegree L K = 1 := by
  have hmul := intermediate_residueDegree_mul L
  rw [hres] at hmul
  exact mul_eq_one.mp hmul

private def liftUpperAutomorphism (L : IntermediateField F K)
    (sigma : Gal(K/L)) : Gal(K/F) :=
  ((IntermediateField.fixingSubgroupEquiv L).symm sigma).1

/-- Invariance under the full Galois group supplies every intermediate
invariance hypothesis needed by the existing Hilbert 90 descent theorem. -/
private theorem invariantCharacter_descends_intermediate
    (L : IntermediateField F K) [PrimeCyclicExtension L K]
    (Theta : ContinuousQuasiChar K)
    (hinvariant : ∀ (sigma : Gal(K/F)) (z : Kˣ),
      Theta (Units.map sigma.toRingEquiv.toMonoidHom z) = Theta z) :
    ∃ chi : ContinuousQuasiChar L, normQuasiChar L K chi = Theta := by
  apply Local.invariantCharacter_descends L K Theta
  intro sigma z
  exact hinvariant (liftUpperAutomorphism L sigma) z

section Charts

variable {pi : ringOfIntegers F} {e a b : ℕ}
  {u0 w0 : (ringOfIntegers F)ˣ} {s R0 : K}
  (D : AlignmentData pi e a b u0 w0 s R0)

/-- Compatibility evaluated on an actual deep unit, with named norm endpoints. -/
private structure DeepNormCompatibility
    (R₁ : unitFiltration D.firstField (2 * e + 1) →* ℂˣ)
    (R₂ : unitFiltration D.secondField (e + a) →* ℂˣ)
    (R₃ : unitFiltration D.thirdField (e + a) →* ℂˣ) (z : Kˣ) : Prop where
  first_mem : normUnits D.firstField K z ∈ unitFiltration D.firstField (2 * e + 1)
  second_mem : normUnits D.secondField K z ∈ unitFiltration D.secondField (e + a)
  third_mem : normUnits D.thirdField K z ∈ unitFiltration D.thirdField (e + a)
  first_eq_second : R₁ ⟨normUnits D.firstField K z, first_mem⟩ =
    R₂ ⟨normUnits D.secondField K z, second_mem⟩
  third_eq_second : R₃ ⟨normUnits D.thirdField K z, third_mem⟩ =
    R₂ ⟨normUnits D.secondField K z, second_mem⟩

/-- The three literal stationary charts and their agreement on deep upper norms. -/
private structure StationaryCharts (PsiF : ContinuousAddChar F) where
  first : unitFiltration D.firstField (2 * e + 1) →* ℂˣ
  second : unitFiltration D.secondField (e + a) →* ℂˣ
  third : unitFiltration D.thirdField (e + a) →* ℂˣ
  first_chart : ∀ u, first u = corePhaseValue D.firstField
    (tracePullbackAddChar F D.firstField PsiF) D.a1 (u : D.firstFieldˣ)
  second_chart : ∀ u, second u = corePhaseValue D.secondField
    (tracePullbackAddChar F D.secondField PsiF) D.a2 (u : D.secondFieldˣ)
  third_chart : ∀ u, third u = corePhaseValue D.thirdField
    (tracePullbackAddChar F D.thirdField PsiF) D.a3 (u : D.thirdFieldˣ)
  compatible : ∀ z : unitFiltration K (2 * e + 1),
    DeepNormCompatibility D first second third (z : Kˣ)

variable {PsiF : ContinuousAddChar F}

/-- Convert the paper's `1 - delta` compatibility to a reusable statement
on arbitrary deep units, once for all three later applications. -/
private theorem exists_stationaryCharts
    [IsGalois F K] [QuadraticTower D.firstField]
    [QuadraticTower D.secondField] [QuadraticTower D.thirdField]
    (ha : 1 ≤ a) (hae : a ≤ e) (O : OriginData D)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (hres : residueDegree F K = 1) (hb : b = 2 * e - 2 * a + 1)
    (htLower₁ : PrimeCyclicExtension.IsLowerBreak F D.firstField (2 * a - 1))
    (htLower₂ : PrimeCyclicExtension.IsLowerBreak F D.secondField (2 * e))
    (htLower₃ : PrimeCyclicExtension.IsLowerBreak F D.thirdField (2 * e))
    (ht₁ : PrimeCyclicExtension.IsLowerBreak D.firstField K (4 * e - 2 * a + 1))
    (ht₂ : PrimeCyclicExtension.IsLowerBreak D.secondField K (2 * a - 1))
    (ht₃ : PrimeCyclicExtension.IsLowerBreak D.thirdField K (2 * a - 1))
    (tau₁ : NormCharacter F D.firstField) (tau₂ : NormCharacter F D.secondField)
    (tau₃ : NormCharacter F D.thirdField) (htau₃ : tau₃ ≠ 1)
    (H : LowerCharacterData F D.firstField D.secondField D.thirdField
      a e ha tau₁ tau₂ tau₃ PsiF D.beta1 D.beta2 D.beta3 D.h1 D.h2 D.h3) :
    Nonempty (StationaryCharts D PsiF) := by
  obtain ⟨R₁, R₂, R₃, hR₁, hR₂, hR₃, hcompat⟩ :=
    compatibility hG hres ha hae hb D O htLower₁ htLower₂ htLower₃
      ht₁ ht₂ ht₃ tau₁ tau₂ tau₃ htau₃ PsiF H
  refine ⟨⟨R₁, R₂, R₃, hR₁, hR₂, hR₃, ?_⟩⟩
  intro z
  let delta : K := 1 - ((z : Kˣ) : K)
  have hdelta : delta ∈ lattice K ((2 * e + 1 : ℕ) : ℤ) := by
    have hdisp := (mem_unitFiltration_succ_iff_sub_mem_lattice K
      (2 * e) (z : Kˣ)).1 z.property
    simpa only [delta, neg_sub] using neg_mem_lattice K hdisp
  have hunit : lowerOneSubUnit K (2 * e + 1) (by omega) delta hdelta = (z : Kˣ) := by
    apply Units.ext
    simp only [coe_lowerOneSubUnit, delta]
    ring
  have hvalues := hcompat delta hdelta
  dsimp only at hvalues
  rw [hunit] at hvalues
  obtain ⟨hu₁, hu₂, hu₃, hval₁, hval₂, hval₃⟩ := hvalues
  exact ⟨hu₁, hu₂, hu₃, hval₁.trans hval₂.symm, hval₃.trans hval₂.symm⟩

/-! ## Additive boundaries and extension of the second chart -/

private structure ChartConductors (PsiF : ContinuousAddChar F) : Prop where
  first : IsAdditiveConductor D.firstField
    (tracePullbackAddChar F D.firstField PsiF) (-((4 * e - 2 * a + 2 : ℕ) : ℤ))
  second : IsAdditiveConductor D.secondField
    (tracePullbackAddChar F D.secondField PsiF) (-((2 * e + 1 : ℕ) : ℤ))
  third : IsAdditiveConductor D.thirdField
    (tracePullbackAddChar F D.thirdField PsiF) (-((2 * e + 1 : ℕ) : ℤ))

/-- The normalized third lower character fixes the additive boundary on `F`;
trace and the lower breaks then give the three boundaries in `D:MX:J`. -/
private theorem chartConductors
    [IsGalois F K] [QuadraticTower D.firstField]
    [QuadraticTower D.secondField] [QuadraticTower D.thirdField]
    (ha : 1 ≤ a) (hae : a ≤ e) (O : OriginData D)
    (hres : residueDegree F K = 1)
    (htLower₁ : PrimeCyclicExtension.IsLowerBreak F D.firstField (2 * a - 1))
    (htLower₂ : PrimeCyclicExtension.IsLowerBreak F D.secondField (2 * e))
    (htLower₃ : PrimeCyclicExtension.IsLowerBreak F D.thirdField (2 * e))
    (tau₁ : NormCharacter F D.firstField) (tau₂ : NormCharacter F D.secondField)
    (tau₃ : NormCharacter F D.thirdField) (htau₃ : tau₃ ≠ 1)
    (H : LowerCharacterData F D.firstField D.secondField D.thirdField
      a e ha tau₁ tau₂ tau₃ PsiF D.beta1 D.beta2 D.beta3 D.h1 D.h2 D.h3) :
    ChartConductors D PsiF := by
  have hresF₁ := (intermediate_residueDegrees_one D.firstField hres).1
  have hresF₂ := (intermediate_residueDegrees_one D.secondField hres).1
  have hresF₃ := (intermediate_residueDegrees_one D.thirdField hres).1
  obtain ⟨piF₃, hpiF₃, hgenF₃⟩ := monogenicUniformizer F D.thirdField hresF₃
  have htauConductor₃ : IsMultiplicativeConductor F tau₃.1 (2 * e + 1) :=
    ramifiedNormCharacter_conductor F D.thirdField htLower₃ hresF₃
      piF₃ hpiF₃ hgenF₃ tau₃ htau₃
  have hPsiTrivial : AddCharTrivialOnLattice F PsiF ((2 * e + 1 : ℕ) : ℤ) := by
    intro x hx
    have hxq : x ∈ lattice F ((e + 1 : ℕ) : ℤ) :=
      lattice_antitone F (by exact_mod_cast (show e + 1 ≤ 2 * e + 1 by omega)) hx
    calc
      PsiF x = PsiF (D.beta3 * x) := by rw [O.beta3_table, one_mul]
      _ = tau₃.1 (lowerOneSubUnit F (e + 1) (by omega) x hxq) :=
        (H.third_formula x hxq).symm
      _ = 1 := by
        apply htauConductor₃.trivial
        rw [mem_unitFiltration_succ_iff_sub_mem_lattice F (2 * e)]
        simp only [coe_lowerOneSubUnit]
        convert neg_mem_lattice F hx using 1
        ring
  have hPsiNontrivial :
      ¬ AddCharTrivialOnLattice F PsiF ((2 * e : ℕ) : ℤ) := by
    intro htriv
    apply htauConductor₃.not_trivialOnPredecessor
    intro u hu
    have hdisp : (u : F) - 1 ∈ lattice F ((2 * e : ℕ) : ℤ) := by
      have hpred : 2 * e - 1 + 1 = 2 * e := by omega
      have hu' : u ∈ unitFiltration F (2 * e - 1 + 1) := by
        simpa only [hpred] using hu
      simpa only [hpred] using
        (mem_unitFiltration_succ_iff_sub_mem_lattice F (2 * e - 1) u).1 hu'
    let x : F := 1 - (u : F)
    have hx : x ∈ lattice F ((2 * e : ℕ) : ℤ) := by
      simpa only [x, neg_sub] using neg_mem_lattice F hdisp
    have hxq : x ∈ lattice F ((e + 1 : ℕ) : ℤ) :=
      lattice_antitone F (by exact_mod_cast (show e + 1 ≤ 2 * e by omega)) hx
    have hunit : lowerOneSubUnit F (e + 1) (by omega) x hxq = u := by
      apply Units.ext
      simp only [coe_lowerOneSubUnit, x]
      ring
    calc
      tau₃.1 u = tau₃.1 (lowerOneSubUnit F (e + 1) (by omega) x hxq) :=
        congrArg tau₃.1 hunit.symm
      _ = PsiF x := by simpa only [O.beta3_table, one_mul] using H.third_formula x hxq
      _ = 1 := htriv x hx
  have hPsi : IsAdditiveConductor F PsiF (-((2 * e + 1 : ℕ) : ℤ)) := by
    apply IsAdditiveConductor.of_boundary
    · simpa only [neg_neg] using hPsiTrivial
    · have hdepth : -(-((2 * e + 1 : ℕ) : ℤ)) - 1 = (2 * e : ℕ) := by
        push_cast
        omega
      rw [hdepth]
      exact hPsiNontrivial
  obtain ⟨piF₁, hpiF₁, hgenF₁⟩ := monogenicUniformizer F D.firstField hresF₁
  obtain ⟨piF₂, hpiF₂, hgenF₂⟩ := monogenicUniformizer F D.secondField hresF₂
  have hPsi₁ : IsAdditiveConductor D.firstField
      (tracePullbackAddChar F D.firstField PsiF) (-((4 * e - 2 * a + 2 : ℕ) : ℤ)) := by
    convert additiveConductor_compTrace_cyclicPrime F D.firstField htLower₁
      hresF₁ piF₁ hpiF₁ hgenF₁ hPsi using 1
    · apply ContinuousAddChar.ext
      intro x
      rfl
    · norm_num [O.first_degree]
      rw [Nat.cast_sub (by omega : 2 * a ≤ 4 * e)]
      push_cast
      omega
  have hPsi₂ : IsAdditiveConductor D.secondField
      (tracePullbackAddChar F D.secondField PsiF) (-((2 * e + 1 : ℕ) : ℤ)) := by
    convert additiveConductor_compTrace_cyclicPrime F D.secondField htLower₂
      hresF₂ piF₂ hpiF₂ hgenF₂ hPsi using 1
    · apply ContinuousAddChar.ext
      intro x
      rfl
    · norm_num [O.second_degree]
      omega
  have hPsi₃ : IsAdditiveConductor D.thirdField
      (tracePullbackAddChar F D.thirdField PsiF) (-((2 * e + 1 : ℕ) : ℤ)) := by
    convert additiveConductor_compTrace_cyclicPrime F D.thirdField htLower₃
      hresF₃ piF₃ hpiF₃ hgenF₃ hPsi using 1
    · apply ContinuousAddChar.ext
      intro x
      rfl
    · norm_num [O.third_degree]
      omega
  exact ⟨hPsi₁, hPsi₂, hPsi₃⟩

private theorem extendSecondChart
    (ha : 1 ≤ a) (O : OriginData D)
    (C : StationaryCharts D PsiF) (J : ChartConductors D PsiF) :
    ∃ chi : ContinuousQuasiChar D.secondField,
      chi.toMonoidHom.comp (unitFiltration D.secondField (e + a)).subtype = C.second ∧
      IsMultiplicativeConductor D.secondField chi (2 * e + 2 * a) := by
  have ha₂order : ord D.secondField D.a2 =
      (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ) := by
    simpa only [intermediateOrder] using O.a2_order
  obtain ⟨chi₂, hchi₂R, hchi₂cond⟩ := extendStationaryCharacter
    D.secondField (tracePullbackAddChar F D.secondField PsiF) D.a2
    (n := 2 * e + 2 * a - 1) (by omega) (by omega) ha₂order
    (show ((1 : ℤ) - 2 * a) + (2 * e + 2 * a - 1 + 1 : ℕ) =
      (2 * e + 1 : ℕ) by push_cast; omega)
    J.second C.second C.second_chart
  have hchi₂cond' : IsMultiplicativeConductor D.secondField chi₂
      (2 * e + 2 * a) := by
    convert hchi₂cond using 1
    omega
  exact ⟨chi₂, hchi₂R, hchi₂cond'⟩

/-! ## The nontrivial commutator and the invariant common pullback -/

private def firstGeneratorLift [QuadraticTower D.firstField] : Gal(K/F) :=
  liftUpperAutomorphism D.firstField (PrimeCyclicExtension.generator D.firstField K)

/-- The first upper generator acts nontrivially on the second lower field:
otherwise its ramification depth would contradict the second upper break. -/
private theorem firstGenerator_restriction_ne_one
    [IsGalois F K] [QuadraticTower D.firstField] [QuadraticTower D.secondField]
    (ha : 1 ≤ a) (hae : a ≤ e)
    (ht₁ : PrimeCyclicExtension.IsLowerBreak D.firstField K (4 * e - 2 * a + 1))
    (ht₂ : PrimeCyclicExtension.IsLowerBreak D.secondField K (2 * a - 1)) :
    AlgEquiv.restrictNormalHom D.secondField (firstGeneratorLift D) ≠ 1 := by
  let gammaUpper : Gal(K/D.firstField) :=
    PrimeCyclicExtension.generator D.firstField K
  let gammaSub : D.firstField.fixingSubgroup :=
    (IntermediateField.fixingSubgroupEquiv D.firstField).symm gammaUpper
  let gamma : Gal(K/F) := gammaSub.1
  have hgammaApply (x : K) : gamma x = gammaUpper x := by rfl
  have hgammaNe : gamma ≠ 1 := by
    intro hgamma
    apply PrimeCyclicExtension.generator_ne_one D.firstField K
    have hsub : gammaSub = 1 := Subtype.ext hgamma
    have heq := congrArg (IntermediateField.fixingSubgroupEquiv D.firstField) hsub
    simpa only [gammaSub, gammaUpper, MulEquiv.apply_symm_apply, map_one] using heq
  let q₂ : Gal(D.secondField/F) := AlgEquiv.restrictNormalHom D.secondField gamma
  intro hq
  change q₂ = 1 at hq
  have hgammaFix₂ : gamma ∈ D.secondField.fixingSubgroup := by
    intro x
    have hx := DFunLike.congr_fun hq x
    change gamma (x : K) = (x : K)
    dsimp only [q₂] at hx
    have hx' := congrArg Subtype.val hx
    rw [AlgEquiv.restrictNormalHom_apply] at hx'
    exact hx'
  let gammaUpper₂ : Gal(K/D.secondField) :=
    IntermediateField.fixingSubgroupEquiv D.secondField
      ⟨gamma, hgammaFix₂⟩
  have hgammaUpper₂Ne : gammaUpper₂ ≠ 1 := by
    intro hone
    apply hgammaNe
    have heq := congrArg
      (IntermediateField.fixingSubgroupEquiv D.secondField).symm hone
    exact congrArg Subtype.val (by simpa only [gammaUpper₂,
      MulEquiv.symm_apply_apply, map_one] using heq)
  have hcardUpper₂ : Nat.card Gal(K/D.secondField) = 2 := by
    rw [IsGalois.card_aut_eq_finrank]
    exact QuadraticTower.upper_degree (L := D.secondField)
  have hupper₂eq : gammaUpper₂ =
      PrimeCyclicExtension.generator D.secondField K := by
    exact eq_of_ne_one_of_card_two hcardUpper₂ hgammaUpper₂Ne
      (PrimeCyclicExtension.generator_ne_one D.secondField K)
  have haction (x : K) :
      PrimeCyclicExtension.generator D.secondField K x = gammaUpper x := by
    rw [← hupper₂eq]
    exact hgammaApply x
  have hshell₁ := PrimeCyclicExtension.generator_mem_break_and_not_mem_succ
    D.firstField K ht₁
  have hshell₂ := PrimeCyclicExtension.generator_mem_break_and_not_mem_succ
    D.secondField K ht₂
  apply hshell₂.2
  rw [mem_lowerRamificationGroup]
  intro x
  have hx := (mem_lowerRamificationGroup D.firstField K
    (PrimeCyclicExtension.generator D.firstField K)
    (4 * e - 2 * a + 1 : ℕ)).1 hshell₁.1 x
  rw [haction]
  exact CongruentAtDepth.mono (by
    push_cast
    omega) hx

/-- Compatibility kills the second commutator on every upper norm. The
first norm of the lifted generator ratio is exactly one. -/
private theorem commutator_trivial_on_norms
    [IsGalois F K] [QuadraticTower D.firstField] [QuadraticTower D.secondField]
    (hae : a ≤ e)
    (C : StationaryCharts D PsiF)
    (ht₁ : PrimeCyclicExtension.IsLowerBreak D.firstField K (4 * e - 2 * a + 1))
    (chi₂ : ContinuousQuasiChar D.secondField)
    (hchi₂R : chi₂.toMonoidHom.comp
      (unitFiltration D.secondField (e + a)).subtype = C.second) :
    normQuasiChar D.secondField K
      (chi₂.pullback (galoisUnitsHom F D.secondField
        (AlgEquiv.restrictNormalHom D.secondField (firstGeneratorLift D))) / chi₂) = 1 := by
  let gamma := firstGeneratorLift D
  let gammaUpper := PrimeCyclicExtension.generator D.firstField K
  let q₂ := AlgEquiv.restrictNormalHom D.secondField gamma
  have hgammaApply (x : K) : gamma x = gammaUpper x := rfl
  apply ContinuousMonoidHom.ext
  intro z
  let w : Kˣ := Units.map gamma.toRingEquiv.toMonoidHom z / z
  have hwdeep : w ∈ unitFiltration K (4 * e - 2 * a + 1) := by
    have hw := generatorRatio_mem D.firstField K ht₁ (by omega) z
    have hhom : gamma.toRingEquiv.toMonoidHom =
        gammaUpper.toRingEquiv.toMonoidHom := by
      ext x
      exact hgammaApply x
    simpa only [w, hhom] using hw
  have hwT : w ∈ unitFiltration K (2 * e + 1) :=
    unitFiltration_antitone K (by omega) hwdeep
  have hcompat := C.compatible ⟨w, hwT⟩
  have hnorm₁w : normUnits D.firstField K w = 1 := by
    apply Units.ext
    simp only [w, Units.val_div_eq_div_val, Units.coe_map]
    rw [show gamma.toRingEquiv.toMonoidHom (z : K) = gammaUpper (z : K) by
      exact hgammaApply (z : K)]
    change Algebra.norm D.firstField (gammaUpper (z : K) / (z : K)) = 1
    rw [div_eq_mul_inv, map_mul, Algebra.norm_inv,
      Basic.norm_conjugate gammaUpper]
    exact mul_inv_cancel₀ ((Algebra.norm_ne_zero_iff).2 (Units.ne_zero z))
  have hnorm₂w : normUnits D.secondField K w =
      Units.map q₂.toRingEquiv.toMonoidHom (normUnits D.secondField K z) /
        normUnits D.secondField K z := by
    apply Units.ext
    simp only [w, Units.val_div_eq_div_val, Units.coe_map]
    change Algebra.norm D.secondField (gamma (z : K) / (z : K)) =
      q₂ (Algebra.norm D.secondField (z : K)) /
        Algebra.norm D.secondField (z : K)
    rw [div_eq_mul_inv, map_mul, Algebra.norm_inv,
      norm_restrictNormal F D.secondField K gamma (z : K)]
    rw [div_eq_mul_inv]
  have hR₂one : C.second ⟨normUnits D.secondField K w, hcompat.second_mem⟩ = 1 := by
    rw [← hcompat.first_eq_second]
    have hone : (⟨normUnits D.firstField K w, hcompat.first_mem⟩ :
        unitFiltration D.firstField (2 * e + 1)) = 1 := Subtype.ext hnorm₁w
    rw [hone, map_one]
  have hchi₂one : chi₂ (normUnits D.secondField K w) = 1 := by
    have hev := DFunLike.congr_fun hchi₂R
      ⟨normUnits D.secondField K w, hcompat.second_mem⟩
    exact hev.trans hR₂one
  change chi₂ (Units.map q₂.toRingEquiv.toMonoidHom
    (normUnits D.secondField K z)) / chi₂ (normUnits D.secondField K z) = 1
  rw [← map_div, ← hnorm₂w, hchi₂one]

/-- The odd source row maps onto the last nontrivial conductor row, so
the lower conjugate quotient cannot be the trivial character. -/
private theorem commutator_ne_one
    [IsGalois F K] [QuadraticTower D.secondField]
    (ha : 1 ≤ a) (hae : a ≤ e) (O : OriginData D)
    (hchar : residueCharacteristic F = 2)
    (htLower₂ : PrimeCyclicExtension.IsLowerBreak F D.secondField (2 * e))
    (chi₂ : ContinuousQuasiChar D.secondField)
    (hchi₂cond : IsMultiplicativeConductor D.secondField chi₂ (2 * e + 2 * a))
    (q₂ : Gal(D.secondField/F)) (hq₂ : q₂ ≠ 1) :
    chi₂.pullback (galoisUnitsHom F D.secondField q₂) / chi₂ ≠ 1 := by
  have hcardLower₂ : Nat.card Gal(D.secondField/F) = 2 := by
    rw [IsGalois.card_aut_eq_finrank]
    exact O.second_degree
  have hq₂gen : q₂ = PrimeCyclicExtension.generator F D.secondField := by
    exact eq_of_ne_one_of_card_two hcardLower₂ hq₂
      (PrimeCyclicExtension.generator_ne_one F D.secondField)
  intro hnu
  have hconductor : IsMultiplicativeConductor D.secondField chi₂
      (2 * e + 2 * a - 1 + 1) := by
    convert hchi₂cond using 1
    omega
  have hnottrivial := hconductor.not_trivialOnPredecessor
  simp only [QuasiCharTrivialOnUnitFiltration] at hnottrivial
  push Not at hnottrivial
  obtain ⟨v, hv, hchiv⟩ := hnottrivial
  have hrowDepth : (2 * a - 1) + 2 * e = 2 * e + 2 * a - 1 := by
    omega
  let vrow : unitFiltration D.secondField ((2 * a - 1) + 2 * e) :=
    ⟨v, by
      rw [hrowDepth]
      exact hv⟩
  have hchar₂ : residueCharacteristic D.secondField = 2 :=
    (residueCharacteristic_extension_eq F D.secondField).trans hchar
  have hodd : ¬ (residueCharacteristic D.secondField : ℤ) ∣
      ((2 * a - 1 : ℕ) : ℤ) := by
    rw [hchar₂]
    norm_num
    omega
  obtain ⟨u, hu⟩ := generatorRatio_graded_surjective F D.secondField
    htLower₂ (by omega) (by omega) hodd vrow
  let ratio : D.secondFieldˣ :=
    Units.map (PrimeCyclicExtension.generator F
      D.secondField).toRingEquiv.toMonoidHom (u : D.secondFieldˣ) /
        (u : D.secondFieldˣ)
  have hquotient : ratio / v ∈
      unitFiltration D.secondField (2 * e + 2 * a) := by
    have hrowCoe : (vrow : D.secondFieldˣ) = v := rfl
    rw [hrowCoe] at hu
    have hnextDepth : (2 * a - 1) + 2 * e + 1 = 2 * e + 2 * a := by
      omega
    rw [hnextDepth] at hu
    simpa only [ratio] using hu
  have hchiQuotient : chi₂ (ratio / v) = 1 :=
    hchi₂cond.trivial (ratio / v) hquotient
  have hchiRatio : chi₂ ratio = chi₂ v := by
    rw [map_div, div_eq_one] at hchiQuotient
    exact hchiQuotient
  have hnuAt := DFunLike.congr_fun hnu (u : D.secondFieldˣ)
  change chi₂ (Units.map q₂.toRingEquiv.toMonoidHom
      (u : D.secondFieldˣ)) / chi₂ (u : D.secondFieldˣ) = 1 at hnuAt
  rw [← map_div, hq₂gen] at hnuAt
  have hratioOne : chi₂ ratio = 1 := by
    simpa only [ratio] using hnuAt
  exact hchiv (hchiRatio.symm.trans hratioOne)

/-- A quadratic lower Galois group has only the identity and the chosen
nontrivial restriction; norm triviality of the commutator handles the latter. -/
private theorem commonPullback_invariant
    [IsGalois F K] [QuadraticTower D.secondField]
    (O : OriginData D)
    (chi₂ : ContinuousQuasiChar D.secondField)
    (q₂ : Gal(D.secondField/F)) (hq₂ : q₂ ≠ 1)
    (hnu₂Norm : normQuasiChar D.secondField K
      (chi₂.pullback (galoisUnitsHom F D.secondField q₂) / chi₂) = 1)
    (sigmaF : Gal(K/F)) (z : Kˣ) :
    normQuasiChar D.secondField K chi₂
        (Units.map sigmaF.toRingEquiv.toMonoidHom z) =
      normQuasiChar D.secondField K chi₂ z := by
  have hcardLower₂ : Nat.card Gal(D.secondField/F) = 2 := by
    rw [IsGalois.card_aut_eq_finrank]
    exact O.second_degree
  let rho : Gal(D.secondField/F) :=
    AlgEquiv.restrictNormalHom D.secondField sigmaF
  have hrho : rho = 1 ∨ rho = q₂ := by
    by_cases h : rho = 1
    · exact Or.inl h
    · exact Or.inr (eq_of_ne_one_of_card_two hcardLower₂ h hq₂)
  have hnorm : normUnits D.secondField K
      (Units.map sigmaF.toRingEquiv.toMonoidHom z) =
        Units.map rho.toRingEquiv.toMonoidHom
          (normUnits D.secondField K z) := by
    apply Units.ext
    simp only [Units.coe_map]
    exact norm_restrictNormal F D.secondField K sigmaF (z : K)
  change chi₂ (normUnits D.secondField K
    (Units.map sigmaF.toRingEquiv.toMonoidHom z)) =
      chi₂ (normUnits D.secondField K z)
  rw [hnorm]
  rcases hrho with hrho | hrho
  · rw [hrho]
    apply congrArg chi₂
    apply Units.ext
    simp only [Units.coe_map]
    rfl
  · rw [hrho]
    have hnuAt := DFunLike.congr_fun hnu₂Norm z
    change chi₂ (Units.map q₂.toRingEquiv.toMonoidHom
        (normUnits D.secondField K z)) /
          chi₂ (normUnits D.secondField K z) = 1 at hnuAt
    exact (div_eq_one.mp hnuAt)

/-! ## Descent on the third field and extension on the first field -/

/-- Above the third upper break, norm surjectivity transports the full
third chart to any descent of the common pullback. -/
private theorem descendedThirdChart
    [IsGalois F K] [QuadraticTower D.thirdField]
    (ha : 1 ≤ a) (hae : a ≤ e)
    (hres : residueDegree F K = 1)
    (ht₃ : PrimeCyclicExtension.IsLowerBreak D.thirdField K (2 * a - 1))
    (C : StationaryCharts D PsiF)
    (chi₂ : ContinuousQuasiChar D.secondField) (chi₃ : ContinuousQuasiChar D.thirdField)
    (hchi₂R : chi₂.toMonoidHom.comp
      (unitFiltration D.secondField (e + a)).subtype = C.second)
    (hchi₃Norm : normQuasiChar D.thirdField K chi₃ = normQuasiChar D.secondField K chi₂) :
    ∀ u : unitFiltration D.thirdField (e + a), chi₃ (u : D.thirdFieldˣ) = C.third u := by
  have hres₃ := (intermediate_residueDegrees_one D.thirdField hres).2
  obtain ⟨pi₃, hpi₃, hgen₃⟩ := monogenicUniformizer D.thirdField K hres₃
  have hdegree₃ : Module.finrank D.thirdField K = 2 :=
    QuadraticTower.upper_degree (L := D.thirdField)
  have hsource₃ : aboveBreakSourceDepth (2 * a - 1)
      (Module.finrank D.thirdField K) (e + a) = 2 * e + 1 := by
    rw [aboveBreakSourceDepth_eq (2 * a - 1)
      (Module.finrank D.thirdField K) (by omega), hdegree₃]
    omega
  intro u
  obtain ⟨z, hz, hnormz⟩ := norm_unitFiltration_surjective_aboveBreak
    D.thirdField K ht₃ (by omega) hres₃ pi₃ hpi₃ hgen₃
    (u : D.thirdFieldˣ) u.property
  have hzT : z ∈ unitFiltration K (2 * e + 1) := by
    rw [← hsource₃]
    exact hz
  have hcompat := C.compatible ⟨z, hzT⟩
  have hpre₃ := DFunLike.congr_fun hchi₃Norm z
  have hpre₂ := DFunLike.congr_fun hchi₂R
    ⟨normUnits D.secondField K z, hcompat.second_mem⟩
  change chi₃ (normUnits D.thirdField K z) =
    chi₂ (normUnits D.secondField K z) at hpre₃
  calc
    chi₃ (u : D.thirdFieldˣ) =
        chi₃ (normUnits D.thirdField K z) := congrArg chi₃ hnormz.symm
    _ = chi₂ (normUnits D.secondField K z) := hpre₃
    _ = C.second ⟨normUnits D.secondField K z, hcompat.second_mem⟩ := hpre₂
    _ = C.third ⟨normUnits D.thirdField K z, hcompat.third_mem⟩ := hcompat.third_eq_second.symm
    _ = C.third u := by
      apply congrArg C.third
      apply Subtype.ext
      exact hnormz

private theorem thirdChart_conductor
    (ha : 1 ≤ a) (O : OriginData D)
    (C : StationaryCharts D PsiF) (J : ChartConductors D PsiF)
    (chi₃ : ContinuousQuasiChar D.thirdField)
    (hchi₃chart : ∀ u : unitFiltration D.thirdField (e + a),
      chi₃ (u : D.thirdFieldˣ) = C.third u) :
    IsMultiplicativeConductor D.thirdField chi₃ (2 * e + 2 * a) := by
  have ha₃order : ord D.thirdField D.a3 =
      (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ) := by
    simpa only [intermediateOrder] using O.a3_order
  convert stationaryChart_exactConductor D.thirdField
    (tracePullbackAddChar F D.thirdField PsiF) D.a3 chi₃
    (n := 2 * e + 2 * a - 1) (by omega) (by omega) ha₃order
    (show ((1 : ℤ) - 2 * a) + (2 * e + 2 * a - 1 + 1 : ℕ) =
      (2 * e + 1 : ℕ) by push_cast; omega)
    J.third (fun u ↦ (hchi₃chart u).trans (C.third_chart u)) using 1
  omega

/-- Below the first upper break, graded norm injectivity forces every
preimage of a deep norm to be deep. This gives agreement on the overlap. -/
private theorem firstChart_agrees_on_norms
    [IsGalois F K] [QuadraticTower D.firstField]
    (hae : a ≤ e)
    (hres : residueDegree F K = 1)
    (ht₁ : PrimeCyclicExtension.IsLowerBreak D.firstField K (4 * e - 2 * a + 1))
    (C : StationaryCharts D PsiF)
    (chi₂ : ContinuousQuasiChar D.secondField) (chi₁pre : ContinuousQuasiChar D.firstField)
    (hchi₂R : chi₂.toMonoidHom.comp
      (unitFiltration D.secondField (e + a)).subtype = C.second)
    (hchi₁preNorm : normQuasiChar D.firstField K chi₁pre =
      normQuasiChar D.secondField K chi₂)
    (xNorm : (normUnits D.firstField K).range)
    (xUnit : unitFiltration D.firstField (2 * e + 1))
    (hx : (xNorm : D.firstFieldˣ) = (xUnit : D.firstFieldˣ)) :
    chi₁pre (xNorm : D.firstFieldˣ) = C.first xUnit := by
  have hres₁ := (intermediate_residueDegrees_one D.firstField hres).2
  obtain ⟨pi₁, hpi₁, hgen₁⟩ := monogenicUniformizer D.firstField K hres₁
  obtain ⟨z, hzNorm⟩ := xNorm.property
  have hzNormDeep : normUnits D.firstField K z ∈
      unitFiltration D.firstField (2 * e + 1) := by
    rw [hzNorm]
    rw [hx]
    exact xUnit.property
  have hzZero : z ∈ unitFiltration K 0 := by
    rw [mem_unitFiltration_zero]
    have hnormZero := (mem_unitFiltration_zero D.firstField
      (normUnits D.firstField K z)).1
      (unitFiltration_antitone D.firstField (Nat.zero_le _) hzNormDeep)
    rw [coe_normUnits, ord_norm, hres₁, one_nsmul] at hnormZero
    exact hnormZero
  have hsourceDeep : z ∈ unitFiltration K (2 * e + 1) := by
    apply mem_unitFiltration_of_norm_mem_of_graded_injective
      D.firstField K (Nat.zero_le (2 * e + 1))
      (fun i _ hi ↦ normMapsUnitFiltration_belowBreak D.firstField K ht₁
        (hi.trans (show 2 * e + 1 ≤ 4 * e - 2 * a + 1 by omega))
        hres₁ pi₁ hpi₁ hgen₁)
      (fun i _ hi ↦ by
        simpa only using
          (gradedNorm_bijective_belowBreak D.firstField K ht₁
            (hi.trans_le (show 2 * e + 1 ≤ 4 * e - 2 * a + 1 by omega))
            hres₁ pi₁ hpi₁ hgen₁).1)
      z hzZero hzNormDeep
  have hcompat := C.compatible ⟨z, hsourceDeep⟩
  have hpre₁ := DFunLike.congr_fun hchi₁preNorm z
  have hpre₂ := DFunLike.congr_fun hchi₂R
    ⟨normUnits D.secondField K z, hcompat.second_mem⟩
  change chi₁pre (normUnits D.firstField K z) =
    chi₂ (normUnits D.secondField K z) at hpre₁
  calc
    chi₁pre (xNorm : D.firstFieldˣ) =
        chi₁pre (normUnits D.firstField K z) := congrArg chi₁pre hzNorm.symm
    _ = chi₂ (normUnits D.secondField K z) := hpre₁
    _ = C.second ⟨normUnits D.secondField K z, hcompat.second_mem⟩ := hpre₂
    _ = C.first ⟨normUnits D.firstField K z, hcompat.first_mem⟩ := hcompat.first_eq_second.symm
    _ = C.first xUnit := by
      apply congrArg C.first
      apply Subtype.ext
      exact hzNorm.trans hx

/-- Extend the compatible norm-range and first-chart prescriptions on their
supremum, preserving the common pullback and the exact first conductor. -/
private theorem extendFirstChart
    [IsGalois F K] [QuadraticTower D.firstField]
    (ha : 1 ≤ a) (hae : a ≤ e) (O : OriginData D)
    (hres : residueDegree F K = 1)
    (ht₁ : PrimeCyclicExtension.IsLowerBreak D.firstField K (4 * e - 2 * a + 1))
    (C : StationaryCharts D PsiF) (J : ChartConductors D PsiF)
    (chi₂ : ContinuousQuasiChar D.secondField) (chi₁pre : ContinuousQuasiChar D.firstField)
    (hchi₂R : chi₂.toMonoidHom.comp
      (unitFiltration D.secondField (e + a)).subtype = C.second)
    (hchi₁preNorm : normQuasiChar D.firstField K chi₁pre =
      normQuasiChar D.secondField K chi₂) :
    ∃ chi₁ : ContinuousQuasiChar D.firstField,
      normQuasiChar D.firstField K chi₁ = normQuasiChar D.secondField K chi₂ ∧
      (∀ u : unitFiltration D.firstField (2 * e + 1),
        chi₁ (u : D.firstFieldˣ) = C.first u) ∧
      IsMultiplicativeConductor D.firstField chi₁ (4 * e + 1) := by
  let Hnorm₁ : Subgroup D.firstFieldˣ := (normUnits D.firstField K).range
  let Hunit₁ : Subgroup D.firstFieldˣ := unitFiltration D.firstField (2 * e + 1)
  let chiNorm₁ : Hnorm₁ →* ℂˣ :=
    chi₁pre.toMonoidHom.comp Hnorm₁.subtype
  have hagree₁ := firstChart_agrees_on_norms D hae hres ht₁ C chi₂ chi₁pre
    hchi₂R hchi₁preNorm
  let generated₁ : ↑(Hnorm₁ ⊔ Hunit₁) →* ℂˣ :=
    characterOnSup Hnorm₁ Hunit₁ chiNorm₁ C.first hagree₁
  have hgeneratedNorm₁ : generated₁.comp
      (Subgroup.inclusion le_sup_left) = chiNorm₁ :=
    characterOnSup_left Hnorm₁ Hunit₁ chiNorm₁ C.first hagree₁
  have hgeneratedUnit₁ : generated₁.comp
      (Subgroup.inclusion le_sup_right) = C.first :=
    characterOnSup_right Hnorm₁ Hunit₁ chiNorm₁ C.first hagree₁
  have hdeepUnit₁ : unitFiltration D.firstField (4 * e + 1) ≤
      Hnorm₁ ⊔ Hunit₁ := by
    intro u hu
    exact Subgroup.mem_sup_right
      (unitFiltration_antitone D.firstField (by omega) hu)
  have ha₁order : ord D.firstField D.a1 =
      (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ) := by
    simpa only [intermediateOrder] using O.a1_order
  have hgeneratedTrivial₁ : generated₁.comp
      (Subgroup.inclusion hdeepUnit₁) = 1 := by
    apply MonoidHom.ext
    intro u
    rw [MonoidHom.one_apply]
    have huLayer : (u : D.firstFieldˣ) ∈ Hunit₁ :=
      unitFiltration_antitone D.firstField (by omega) u.property
    let uLayer : Hunit₁ := ⟨u, huLayer⟩
    have hgenerated : generated₁ ⟨u, hdeepUnit₁ u.property⟩ = C.first uLayer :=
      DFunLike.congr_fun hgeneratedUnit₁ uLayer
    change generated₁ ⟨u, hdeepUnit₁ u.property⟩ = 1
    rw [hgenerated, C.first_chart]
    exact corePhaseValue_eq_one_of_mem D.firstField
      (tracePullbackAddChar F D.firstField PsiF) D.a1 ha₁order
      (show ((1 : ℤ) - 2 * a) + (4 * e + 1 : ℕ) = (4 * e - 2 * a + 2 : ℕ) by
        push_cast
        omega)
      J.first (u : D.firstFieldˣ) u.property
  obtain ⟨chi₁, hchi₁NormRange, hchi₁R⟩ :=
    Local.compatiblePair_extendFamily D.firstField Hnorm₁ Hunit₁
      chiNorm₁ C.first generated₁ hgeneratedNorm₁ hgeneratedUnit₁
      (4 * e + 1) (by omega) hdeepUnit₁ hgeneratedTrivial₁
  have hchi₁Norm : normQuasiChar D.firstField K chi₁ =
      normQuasiChar D.secondField K chi₂ := by
    apply ContinuousMonoidHom.ext
    intro z
    have hnew := DFunLike.congr_fun hchi₁NormRange
      ((normUnits D.firstField K).rangeRestrict z)
    have hpre := DFunLike.congr_fun hchi₁preNorm z
    change chi₁ (normUnits D.firstField K z) =
      chi₁pre (normUnits D.firstField K z) at hnew
    exact hnew.trans hpre
  have hchi₁chart (u : unitFiltration D.firstField (2 * e + 1)) :
      chi₁ (u : D.firstFieldˣ) = C.first u := by
    exact DFunLike.congr_fun hchi₁R u
  have hchi₁cond : IsMultiplicativeConductor D.firstField chi₁
      (4 * e + 1) := by
    exact stationaryChart_exactConductor D.firstField
      (tracePullbackAddChar F D.firstField PsiF) D.a1 chi₁
      (n := 4 * e) (by omega) (by omega) ha₁order
      (show ((1 : ℤ) - 2 * a) + (4 * e + 1 : ℕ) =
        (4 * e - 2 * a + 2 : ℕ) by
          push_cast
          omega)
      J.first (fun u ↦ (hchi₁chart u).trans (C.first_chart u))
  exact ⟨chi₁, hchi₁Norm, hchi₁chart, hchi₁cond⟩

/-! ## The obstruction to descent to the base field -/

/-- A base pullback and an upper quadratic norm character are both invariant
under the lower restriction, contradicting the nontrivial commutator. -/
private theorem commonPullback_not_from_base
    [IsGalois F K] [QuadraticTower D.secondField]
    (hres : residueDegree F K = 1)
    (ht₂ : PrimeCyclicExtension.IsLowerBreak D.secondField K (2 * a - 1))
    (chi₂ : ContinuousQuasiChar D.secondField) (gamma : Gal(K/F))
    (hnu₂Ne : chi₂.pullback (galoisUnitsHom F D.secondField
      (AlgEquiv.restrictNormalHom D.secondField gamma)) / chi₂ ≠ 1) :
    ¬ ∃ lambda : ContinuousQuasiChar F,
      normQuasiChar F K lambda = normQuasiChar D.secondField K chi₂ := by
  let q₂ := AlgEquiv.restrictNormalHom D.secondField gamma
  let nu₂ := chi₂.pullback (galoisUnitsHom F D.secondField q₂) / chi₂
  have hres₂ := (intermediate_residueDegrees_one D.secondField hres).2
  rintro ⟨lambda, hlambda⟩
  let lambda₂ : ContinuousQuasiChar D.secondField :=
    normQuasiChar F D.secondField lambda
  let mu : ContinuousQuasiChar D.secondField := chi₂ / lambda₂
  have hmuNorm : normQuasiChar D.secondField K mu = 1 := by
    apply ContinuousMonoidHom.ext
    intro z
    rw [normQuasiChar_apply, ContinuousQuasiChar.one_apply]
    have htower : continuousNormUnits F D.secondField
        (continuousNormUnits D.secondField K z) =
          continuousNormUnits F K z := by
      apply Units.ext
      simp only [coe_continuousNormUnits]
      exact Basic.norm_tower (F := F) (L := D.secondField)
        (K := K) (z : K)
    have hdescent := DFunLike.congr_fun hlambda z
    rw [normQuasiChar_apply, normQuasiChar_apply] at hdescent
    dsimp only [mu, lambda₂]
    change chi₂ (continuousNormUnits D.secondField K z) /
      lambda (continuousNormUnits F D.secondField
        (continuousNormUnits D.secondField K z)) = 1
    rw [htower, div_eq_one]
    exact hdescent.symm
  let muNorm : NormCharacter D.secondField K := ⟨mu, hmuNorm⟩
  obtain ⟨pi₂, hpi₂, hgen₂⟩ := monogenicUniformizer D.secondField K hres₂
  have hmuInvariant : mu.pullback
      (galoisUnitsHom F D.secondField q₂) = mu := by
    simpa only [q₂] using quadraticNormCharacter_invariant
      F D.secondField K ht₂ hres₂ pi₂ hpi₂ hgen₂
      (QuadraticTower.upper_degree (L := D.secondField)) gamma muNorm
  have hlambda₂Invariant (x : D.secondFieldˣ) :
      lambda₂ (Units.map q₂.toRingEquiv.toMonoidHom x) = lambda₂ x := by
    change lambda (continuousNormUnits F D.secondField
        (Units.map q₂.toRingEquiv.toMonoidHom x)) =
      lambda (continuousNormUnits F D.secondField x)
    apply congrArg lambda
    apply Units.ext
    simp only [coe_continuousNormUnits, Units.coe_map]
    exact Basic.norm_conjugate q₂ (x : D.secondField)
  have hnuOne : nu₂ = 1 := by
    apply ContinuousMonoidHom.ext
    intro x
    rw [ContinuousQuasiChar.one_apply]
    change chi₂ (Units.map q₂.toRingEquiv.toMonoidHom x) / chi₂ x = 1
    have hmuAt := DFunLike.congr_fun hmuInvariant x
    change mu (Units.map q₂.toRingEquiv.toMonoidHom x) = mu x at hmuAt
    have hdecomp (y : D.secondFieldˣ) :
        chi₂ y = mu y * lambda₂ y := by
      change chi₂ y = (chi₂ y / lambda₂ y) * lambda₂ y
      exact (div_mul_cancel _ _).symm
    rw [hdecomp, hdecomp, hmuAt, hlambda₂Invariant]
    simp
  exact hnu₂Ne hnuOne

end Charts

/-- **Paper Theorem 12.6 (`D:MX:cores`).**  The three stationary charts
extend to genuine characters on the full multiplicative groups.  Their
actual norm pullbacks agree and do not descend to the base field. -/
theorem models
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
    (_htwo : ord F (2 : F) = (e : WithTop ℤ))
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
        D.h1 D.h2 D.h3),
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
            (tracePullbackAddChar F D.thirdField PsiF) D.a3 (u : D.thirdFieldˣ)) := by
  dsimp only
  letI := quadraticTower hG D.firstField O.first_degree
  letI := quadraticTower hG D.secondField O.second_degree
  letI := quadraticTower hG D.thirdField O.third_degree
  intro htLower₁ htLower₂ htLower₃ ht₁ ht₂ ht₃ tau₁ tau₂ tau₃ htau₃ PsiF H
  classical
  obtain ⟨charts⟩ := exists_stationaryCharts D ha hae O hG hres hb
    htLower₁ htLower₂ htLower₃ ht₁ ht₂ ht₃ tau₁ tau₂ tau₃ htau₃ H
  have conductors := chartConductors D ha hae O hres
    htLower₁ htLower₂ htLower₃ tau₁ tau₂ tau₃ htau₃ H
  obtain ⟨chi₂, hchi₂R, hchi₂cond⟩ := extendSecondChart D ha O charts conductors
  let gamma := firstGeneratorLift D
  let q₂ := AlgEquiv.restrictNormalHom D.secondField gamma
  have hq₂ := firstGenerator_restriction_ne_one D ha hae ht₁ ht₂
  have hnuNorm := commutator_trivial_on_norms D hae charts ht₁ chi₂ hchi₂R
  have hnuNe := commutator_ne_one D ha hae O hchar htLower₂ chi₂ hchi₂cond q₂ hq₂
  have hinvariant := commonPullback_invariant D O chi₂ q₂ hq₂ hnuNorm
  obtain ⟨chi₁pre, hchi₁preNorm⟩ := invariantCharacter_descends_intermediate
    D.firstField (normQuasiChar D.secondField K chi₂) hinvariant
  obtain ⟨chi₃, hchi₃Norm⟩ := invariantCharacter_descends_intermediate
    D.thirdField (normQuasiChar D.secondField K chi₂) hinvariant
  have hchi₃chart := descendedThirdChart D ha hae hres ht₃ charts chi₂ chi₃ hchi₂R hchi₃Norm
  have hchi₃cond := thirdChart_conductor D ha O charts conductors chi₃ hchi₃chart
  obtain ⟨chi₁, hchi₁Norm, hchi₁chart, hchi₁cond⟩ :=
    extendFirstChart D ha hae O hres ht₁ charts conductors chi₂ chi₁pre hchi₂R hchi₁preNorm
  exact ⟨chi₁, chi₂, chi₃, hchi₁cond, hchi₂cond, hchi₃cond, hchi₁Norm, hchi₃Norm,
    commonPullback_not_from_base D hres ht₂ chi₂ gamma hnuNe,
    fun u ↦ (hchi₁chart u).trans (charts.first_chart u),
    fun u ↦ (DFunLike.congr_fun hchi₂R u).trans (charts.second_chart u),
    fun u ↦ (hchi₃chart u).trans (charts.third_chart u)⟩

end Construction

end

end LanglandsSecondMainLemma.Dyadic.Maximal
