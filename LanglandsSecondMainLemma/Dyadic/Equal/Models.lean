import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Dyadic.Equal.Commutator
import LanglandsSecondMainLemma.Dyadic.Equal.Compatibility
import LanglandsSecondMainLemma.Local.NormDescent

/-!
# Dyadic / Equal / Models

Paper Theorem 11.6, `D:EQ:core-exists`. The character on the generated
subgroup is constructed by descending a product homomorphism. The exact
stationary charts determine conductors on whole unit groups.
-/

namespace LanglandsSecondMainLemma.Dyadic.Equal

open LanglandsFirstMainLemma
noncomputable section

section Extension
variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- Construct the product prescription before extending it. Agreement is
required for every preimage of the stationary subgroup, which also proves
well-definedness of the prescription on the image of `c`. -/
private theorem prescriptionExtension {G : Type*} [CommGroup G]
    (c : G →* Eˣ) (ν : G →* ℂˣ) (s m : ℕ) (hm : 1 ≤ m) (hsm : s ≤ m)
    (R : unitFiltration E s →* ℂˣ)
    (hcompat : ∀ v (hv : c v ∈ unitFiltration E s), R ⟨c v, hv⟩ = ν v)
    (htrivial : ∀ u (hu : u ∈ unitFiltration E m),
      R ⟨u, unitFiltration_antitone E hsm hu⟩ = 1) :
    ∃ χ : ContinuousQuasiChar E,
      (∀ u (hu : u ∈ unitFiltration E s), χ u = R ⟨u, hu⟩) ∧
      ∀ v, χ (c v) = ν v := by
  let U := unitFiltration E s
  let f : G × U →* Eˣ :=
    (c.comp (MonoidHom.fst G U)) * (U.subtype.comp (MonoidHom.snd G U))
  let q : G × U →* ℂˣ :=
    (ν.comp (MonoidHom.fst G U)) * (R.comp (MonoidHom.snd G U))
  have hk : f.rangeRestrict.ker ≤ q.ker := by
    intro x hx
    have he : c x.1 * (x.2 : Eˣ) = 1 := congrArg Subtype.val hx
    have hc : c x.1 = (x.2 : Eˣ)⁻¹ := (mul_eq_one_iff_eq_inv).mp he
    have hu : c x.1 ∈ U := hc ▸ U.inv_mem x.2.property
    have hvalue : ν x.1 = (R x.2)⁻¹ := by
      rw [← hcompat x.1 hu]
      have heq : (⟨c x.1, hu⟩ : U) = x.2⁻¹ := Subtype.ext hc
      rw [heq, map_inv]
    change ν x.1 * R x.2 = 1
    rw [hvalue, inv_mul_cancel]
  let S : f.range →* ℂˣ :=
    f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨q, hk⟩
  have hS (x : G × U) : S (f.rangeRestrict x) = q x :=
    f.rangeRestrict.liftOfRightInverse_comp_apply _ _ _ x
  have hU : unitFiltration E m ≤ f.range := by
    intro u hu
    refine ⟨(1, ⟨u, unitFiltration_antitone E hsm hu⟩), ?_⟩
    simp [f]
  have hSunit (u : Eˣ) (hu : u ∈ U) :
      S ⟨u, ⟨(1, ⟨u, hu⟩), by simp [f]⟩⟩ = R ⟨u, hu⟩ := by
    have heq : (⟨u, ⟨(1, ⟨u, hu⟩), by simp [f]⟩⟩ : f.range) =
        f.rangeRestrict (1, ⟨u, hu⟩) := Subtype.ext (by simp [f])
    rw [heq]
    simpa [q] using hS (1, ⟨u, hu⟩)
  have hkill : S.comp (Subgroup.inclusion hU) = 1 := by
    apply MonoidHom.ext
    intro u
    exact (hSunit u (unitFiltration_antitone E hsm u.property)).trans
      (htrivial u u.property)
  obtain ⟨χ, hχ⟩ := Local.characterExtension E f.range m hm hU S hkill
  refine ⟨χ, ?_, ?_⟩
  · intro u hu
    exact (DFunLike.congr_fun hχ ⟨u, ⟨(1, ⟨u, hu⟩), by simp [f]⟩⟩).trans
      (hSunit u hu)
  · intro v
    have he := DFunLike.congr_fun hχ (f.rangeRestrict (v, 1))
    have hs := hS (v, 1)
    simpa [f, q] using he.trans hs

end Extension

section Conductors
variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

private theorem one_sub_mem_of_unit {s : ℕ} (hs : 0 < s) (u : Eˣ)
    (hu : u ∈ unitFiltration E s) : 1 - (u : E) ∈ lattice E (s : ℤ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  have h := (mem_unitFiltration_succ_iff_sub_mem_lattice E n u).mp hu
  simpa only [neg_sub] using (lattice E ((n + 1 : ℕ) : ℤ)).neg_mem h

private theorem linearPhase_trivial (ψ : ContinuousAddChar E) {n v : ℤ}
    (hψ : IsAdditiveConductor E ψ n) (a : E) (ha : ord E a = (v : WithTop ℤ))
    {m : ℕ} (hm : 0 < m) (hbalance : (m : ℤ) = -n - v)
    (u : Eˣ) (hu : u ∈ unitFiltration E m) : ψ (a * (1 - (u : E))) = 1 := by
  apply hψ.trivial
  have h := mul_mem_lattice E ha.ge (one_sub_mem_of_unit hm u hu)
  have he : v + (m : ℤ) = -n := by omega
  rwa [he] at h

/-- A full linear chart determines the exact conductor. Nontriviality is
proved by transporting a point from the entire additive predecessor ideal. -/
private theorem conductor_of_linearChart (ψ : ContinuousAddChar E) {n v : ℤ}
    (hψ : IsAdditiveConductor E ψ n) (a : E) (ha : ord E a = (v : WithTop ℤ))
    {s m : ℕ} (hs : 0 < s) (hsm : s ≤ m)
    (hbalance : ((m + 1 : ℕ) : ℤ) = -n - v)
    (χ : ContinuousQuasiChar E)
    (hchart : ∀ u, u ∈ unitFiltration E s → χ u = ψ (a * (1 - (u : E)))) :
    IsMultiplicativeConductor E χ (m + 1) := by
  apply IsMultiplicativeConductor.of_succ_boundary
  · intro u hu
    rw [hchart u (unitFiltration_antitone E (by omega) hu)]
    exact linearPhase_trivial ψ hψ a ha (by omega) hbalance u hu
  · intro htriv
    obtain ⟨y, hy, hvalue⟩ := hψ.exists_ord_eq_predecessor
    have ha0 : a ≠ 0 := by
      intro hzero
      rw [hzero, ord_zero] at ha
      exact WithTop.top_ne_coe ha
    have hz : y / a ∈ lattice E (m : ℤ) := by
      change (m : WithTop ℤ) ≤ ord E (y / a)
      rw [ord_div, hy, ha, ← WithTop.LinearOrderedAddCommGroup.coe_sub]
      exact WithTop.coe_le_coe.mpr (by omega)
    have hz0 : 1 - y / a ≠ 0 := by
      intro he
      have he' : y / a = 1 := (sub_eq_zero.mp he).symm
      have hbound : (m : WithTop ℤ) ≤ ord E (y / a) := hz
      rw [he', ord_one] at hbound
      have h := WithTop.coe_le_coe.mp hbound
      omega
    let u : Eˣ := Units.mk0 (1 - y / a) hz0
    have hu : u ∈ unitFiltration E m := by
      obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      rw [hr, mem_unitFiltration_succ_iff_sub_mem_lattice]
      change (1 - y / a) - 1 ∈ lattice E ((r + 1 : ℕ) : ℤ)
      simpa only [sub_sub_cancel_left, hr] using (lattice E (m : ℤ)).neg_mem hz
    have hc := hchart u (unitFiltration_antitone E hsm hu)
    have he : a * (1 - (u : E)) = y := by
      dsimp [u]
      field_simp
      ring
    rw [he, htriv u hu] at hc
    exact hvalue hc.symm

end Conductors

open private originLine_degrees origin_residueDegrees origin_group_equiv
  originLine_norm_trace from LanglandsSecondMainLemma.Dyadic.Equal.Origin
open private depth_ledger edge_ramification from
  LanglandsSecondMainLemma.Dyadic.Equal.Compatibility

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  [CharP F 2] [CharP K 2] [IsKleinFour Gal(K/F)]

local instance modelsIntermediateValuation (L : IntermediateField F K) : ValuativeRel L :=
  Basic.intermediateFieldValuativeRel L
local instance modelsIntermediateTopology (L : IntermediateField F K) : TopologicalSpace L :=
  Basic.intermediateFieldTopology L
local instance modelsIntermediateLocalField (L : IntermediateField F K) : IsNonarchimedeanLocalField L :=
  Basic.intermediateField_localField L
local instance modelsLowerValuativeExtension (L : IntermediateField F K) : ValuativeExtension F L :=
  Basic.intermediateField_lowerValuativeExtension L
local instance modelsUpperValuativeExtension (L : IntermediateField F K) : ValuativeExtension L K :=
  Basic.intermediateField_upperValuativeExtension L
local instance modelsIntermediateGalois (L : IntermediateField F K) : IsGalois F L := by
  letI : IsMulCommutative Gal(K/F) := IsKleinFour.isMulCommutative
  letI : L.fixingSubgroup.Normal := inferInstance
  have h := IsGalois.of_fixedField_normal_subgroup L.fixingSubgroup
  rwa [IsGalois.fixedField_fixingSubgroup L] at h

namespace SimultaneousASGenerators
variable {P : Residues.EqualCharacteristicPresentation F}
  (A : SimultaneousASGenerators F K P)

/-- The exact odd conductors of (D:EQ:coreledger), without truncated depths. -/
def minimalConductor (i : Fin 3) : ℕ :=
  if i = 0 then 2 * A.t 1 + 1 else A.t 0 + A.t 1 + 1

/-- The integer exponents of the largest trivial additive ideals (D:EQ:Jledger). -/
def additiveModulus (i : Fin 3) : ℤ :=
  2 * ((A.t 1 : ℤ) + 1) - ((A.t i : ℤ) + 1)

omit [IsGalois F K] [CharP F 2] [CharP K 2] in
private theorem model_ledger (i : Fin 3) :
    2 ≤ A.stationaryDepth i ∧ A.stationaryDepth i ≤ A.minimalConductor i - 1 ∧
      A.minimalConductor i = 2 * A.stationaryDepth i - 1 ∧
      (A.minimalConductor i : ℤ) = A.additiveModulus i + A.t 0 ∧
      Odd (A.minimalConductor i) := by
  have h₀ := (A.edge 0).2.2.2.1
  have h₁ := (A.edge 1).2.2.2.1
  obtain ⟨a, ha⟩ := (A.edge 0).2.2.2.2.1
  obtain ⟨b, hb⟩ := (A.edge 1).2.2.2.2.1
  have ht := A.third_break
  have h : 2 ≤ A.stationaryDepth i ∧
      A.stationaryDepth i ≤ A.minimalConductor i - 1 ∧
      A.minimalConductor i = 2 * A.stationaryDepth i - 1 ∧
      (A.minimalConductor i : ℤ) = A.additiveModulus i + A.t 0 := by
    fin_cases i <;> simp only [minimalConductor, stationaryDepth, additiveModulus]
    all_goals norm_num
    all_goals try rw [show A.t ⟨2, by decide⟩ = A.t 1 from ht]
    all_goals omega
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, A.stationaryDepth i - 1, by omega⟩

/-- Trace pullback has the exact additive conductor on each actual field. -/
theorem modelAddChar_conductor (hres : residueDegree F K = 1) (i : Fin 3) :
    IsAdditiveConductor (A.field i)
      (tracePullbackAddChar F (A.field i) (originAddChar F P ((A.t 1 : ℤ) + 1)))
      (-A.additiveModulus i) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F (A.field i)
    (origin_residueDegrees F K hres (A.field i)).1
  have h := additiveConductor_compTrace F (A.field i) pi hpi hgen
    (originAddChar_conductor F P ((A.t 1 : ℤ) + 1))
  have he := (edge_ramification A hres i).1
  rw [he, (A.edge i).2.2.2.2.2.2.2.2] at h
  convert h using 1
  · rfl
  · ext x
    rfl
  · simp only [additiveModulus, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring

/-- The prescribed character is trivial at the claimed conductor depth. -/
theorem modelValue_trivial (hres : residueDegree F K = 1) (i : Fin 3)
    (u : (A.field i)ˣ) (hu : u ∈ unitFiltration (A.field i) (A.minimalConductor i)) :
    A.modelValue i u = 1 := by
  apply linearPhase_trivial (m := A.minimalConductor i) _ (A.modelAddChar_conductor hres i) _
    ((A.origin_orders hres).2.1 i).1
  · have h := A.model_ledger i
    omega
  · have h := (A.model_ledger i).2.2.2.1
    omega
  · exact hu

/-- Every extension with the whole stationary chart has the exact odd
minimal conductor. This applies equally to the two descended characters. -/
theorem conductor_of_modelChart (hres : residueDegree F K = 1) (i : Fin 3)
    (χ : ContinuousQuasiChar (A.field i))
    (hchart : ∀ u, u ∈ unitFiltration (A.field i) (A.stationaryDepth i) →
      χ u = A.modelValue i u) :
    IsMultiplicativeConductor (A.field i) χ (A.minimalConductor i) := by
  have h := A.model_ledger i
  have hm : A.minimalConductor i - 1 + 1 = A.minimalConductor i := by omega
  rw [← hm]
  apply conductor_of_linearChart _ (A.modelAddChar_conductor hres i) _
    ((A.origin_orders hres).2.1 i).1 (by omega) h.2.1 _ χ hchart
  rw [hm]
  omega

/-- The nontrivial automorphism of the first lower quadratic field. -/
abbrev firstConjugation : Gal(A.field 0/F) :=
  AlgEquiv.restrictNormalHom (A.field 0) (A.g 1)

omit [CharP F 2] [CharP K 2] in
theorem firstConjugation_ne_one : A.firstConjugation ≠ 1 := by
  have hz : A.firstConjugation (A.z 0) = A.z 0 + 1 := by
    apply Subtype.ext
    change ((AlgEquiv.restrictNormalHom (A.field 0) (A.g 1)) (A.z 0) : K) = _
    rw [AlgEquiv.restrictNormalHom_apply]
    exact A.second_action
  intro he
  rw [he, AlgEquiv.one_apply] at hz
  exact one_ne_zero (add_eq_left.mp hz.symm)

/-- The first extension retains the prescribed commutator globally. -/
theorem first_model_exists (hres : residueDegree F K = 1)
    (ω : NormCharacter F (A.field 1)) (hω : ω ≠ 1) :
    ∃ χ : ContinuousQuasiChar (A.field 0),
      (∀ u, u ∈ unitFiltration (A.field 0) (A.stationaryDepth 0) →
        χ u = A.modelValue 0 u) ∧
      ∀ v, χ (Units.map A.firstConjugation.toMonoidHom v / v) =
        (Characters.crossedNormHom F (A.field 0) (A.field 1) K ω).1 v := by
  let c : (A.field 0)ˣ →* (A.field 0)ˣ :=
    (Units.map A.firstConjugation.toMonoidHom) / MonoidHom.id _
  let ν := Characters.crossedNormHom F (A.field 0) (A.field 1) K ω
  have h := A.model_ledger 0
  have hcompat (v) (hv : c v ∈ unitFiltration (A.field 0) (A.stationaryDepth 0)) :
      A.stationaryCharacter hres 0 ⟨c v, hv⟩ = ν.1 v := by
    apply Units.ext
    change (A.modelValue 0 (c v) : ℂ) = _
    simp only [modelValue, c, MonoidHom.div_apply, MonoidHom.id_apply,
      Units.val_div_eq_div_val, Units.coe_map]
    exact commutator F K hres P A ω hω v hv
  obtain ⟨χ, hchart, hcomm⟩ := prescriptionExtension c ν.1.toMonoidHom
    (A.stationaryDepth 0) (A.minimalConductor 0) (by omega) (by omega)
    (A.stationaryCharacter hres 0) hcompat (A.modelValue_trivial hres 0)
  exact ⟨χ, hchart, hcomm⟩

omit [IsGalois F K] [CharP F 2] [CharP K 2] in
private theorem field_injective : Function.Injective A.field := by
  have h02 : A.g 0 ≠ A.g 2 := by
    rw [A.third_automorphism]
    intro he
    exact A.nontrivial 1 (mul_eq_left.mp he.symm)
  have h12 : A.g 1 ≠ A.g 2 := by
    rw [A.third_automorphism]
    intro he
    exact A.nontrivial 0 (mul_eq_right.mp he.symm)
  have hg : Function.Injective A.g := by
    intro i j he
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact (A.distinct he).elim
      | exact (A.distinct he.symm).elim
      | exact (h02 he).elim
      | exact (h02 he.symm).elim
      | exact (h12 he).elim
      | exact (h12 he.symm).elim
  intro i j he
  have hline : originLine (A.g i) = originLine (A.g j) := by
    simpa only [field, IntermediateField.fixingSubgroup_fixedField] using
      congrArg IntermediateField.fixingSubgroup he
  have hmem : A.g i ∈ originLine (A.g j) := hline ▸ (Or.inr rfl : A.g i ∈ originLine (A.g i))
  exact hg (hmem.resolve_left (A.nontrivial i))

omit [CharP F 2] [CharP K 2] in
/-- Norms commute with restriction of the actual automorphisms. -/
private theorem norm_restrict (i : Fin 3) (τ : Gal(K/F)) (x : Kˣ) :
    Units.map (AlgEquiv.restrictNormalHom (A.field i) τ).toMonoidHom
      (normUnits (A.field i) K x) =
        normUnits (A.field i) K (Units.map τ.toMonoidHom x) := by
  letI : IsMulCommutative Gal(K/F) := IsKleinFour.isMulCommutative
  apply Units.ext
  apply (algebraMap (A.field i) K).injective
  change ((AlgEquiv.restrictNormalHom (A.field i) τ)
    (Algebra.norm (A.field i) (x : K)) : K) = _
  rw [AlgEquiv.restrictNormalHom_apply]
  change τ (algebraMap (A.field i) K (Algebra.norm (A.field i) (x : K))) =
    algebraMap (A.field i) K (Algebra.norm (A.field i) (τ (x : K)))
  rw [(originLine_norm_trace F K (A.g i) (A.nontrivial i) (x : K)).1,
    (originLine_norm_trace F K (A.g i) (A.nontrivial i) (τ (x : K))).1, map_mul]
  congr 1
  exact DFunLike.congr_fun (mul_comm' τ (A.g i)) (x : K)

/-- The prescribed commutator makes the first norm pullback invariant under
the entire actual Klein four group. -/
theorem first_pullback_invariant (ω : NormCharacter F (A.field 1))
    (χ : ContinuousQuasiChar (A.field 0))
    (hcomm : ∀ v, χ (Units.map A.firstConjugation.toMonoidHom v / v) =
      (Characters.crossedNormHom F (A.field 0) (A.field 1) K ω).1 v) :
    ∀ (τ : Gal(K/F)) (x : Kˣ),
      normQuasiChar (A.field 0) K χ (Units.map τ.toMonoidHom x) =
        normQuasiChar (A.field 0) K χ x := by
  intro τ x
  change χ (normUnits (A.field 0) K (Units.map τ.toMonoidHom x)) = _
  rw [← A.norm_restrict]
  let ρ := AlgEquiv.restrictNormalHom (A.field 0) τ
  by_cases hρ : ρ = 1
  · change χ (Units.map ρ.toMonoidHom (normUnits (A.field 0) K x)) = _
    rw [hρ]
    rfl
  · have hcard : Nat.card Gal(A.field 0/F) = 2 :=
      (IsGalois.card_aut_eq_finrank F (A.field 0)).trans
        (originLine_degrees F K (A.g 0) (A.nontrivial 0)).1
    have heq : ρ = A.firstConjugation :=
      ((Nat.card_eq_two_iff' (1 : Gal(A.field 0/F))).mp hcard).unique
        hρ A.firstConjugation_ne_one
    change χ (Units.map ρ.toMonoidHom (normUnits (A.field 0) K x)) = _
    rw [heq]
    have h := hcomm (normUnits (A.field 0) K x)
    have hν := (Characters.crossedNormHom F (A.field 0) (A.field 1) K ω).eq_one_on_normRange
      (A.field 0) K _ ⟨x, rfl⟩
    rw [map_div, hν] at h
    exact div_eq_one.mp h

omit [CharP F 2] [CharP K 2] in
private theorem upperCyclic (i : Fin 3) : PrimeCyclicExtension (A.field i) K := by
  have hd := (originLine_degrees F K (A.g i) (A.nontrivial i)).2
  letI : IsCyclic Gal(K/A.field i) := isCyclic_of_prime_card
    ((IsGalois.card_aut_eq_finrank (A.field i) K).trans hd)
  exact ⟨inferInstance, inferInstance, by rw [hd]; exact Nat.prime_two⟩

/-- Every other stationary unit is the norm of an element in the full
common compatibility group. The exact image used is `Nᵢ(U_K^{T₂+1})`. -/
theorem stationary_norm_image (hres : residueDegree F K = 1)
    (i : Fin 3) (hi : i ≠ 0) :
    Subgroup.map (normUnits (A.field i) K) (unitFiltration K (A.t 1 + 2)) =
      unitFiltration (A.field i) (A.stationaryDepth i) := by
  letI := A.upperCyclic i
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer (A.field i) K
    (origin_residueDegrees F K hres (A.field i)).2
  have ht : PrimeCyclicExtension.IsLowerBreak (A.field i) K (A.t 0) := by
    simpa only [if_neg hi] using A.upper_break i
  have hs : A.t 0 < A.stationaryDepth i := by
    obtain ⟨a, ha⟩ := (A.edge 0).2.2.2.2.1
    obtain ⟨b, hb⟩ := (A.edge 1).2.2.2.2.1
    have h := A.smallest
    simp only [stationaryDepth, if_neg hi]
    omega
  have himage := (cyclicPrimeNormFiltration (A.field i) K ht
    (origin_residueDegrees F K hres (A.field i)).2 pi hpi hgen).above_image
      (A.stationaryDepth i) hs
  have he : herbrandPsiNat (A.t 0) (Module.finrank (A.field i) K)
      (A.stationaryDepth i) = A.t 1 + 2 := by
    rw [(originLine_degrees F K (A.g i) (A.nontrivial i)).2,
      herbrandPsiNat_of_break_le _ _ hs.le]
    obtain ⟨a, ha⟩ := (A.edge 0).2.2.2.2.1
    obtain ⟨b, hb⟩ := (A.edge 1).2.2.2.2.1
    simp only [stationaryDepth, if_neg hi] at *
    omega
  rwa [he] at himage

/-- Norm descent preserves the entire stationary prescription, using the
proved surjectivity on the precise above-break unit layer. -/
theorem descended_modelChart (hres : residueDegree F K = 1)
    (χ₁ : ContinuousQuasiChar (A.field 0))
    (hchart₁ : ∀ u, u ∈ unitFiltration (A.field 0) (A.stationaryDepth 0) →
      χ₁ u = A.modelValue 0 u)
    (i : Fin 3) (hi : i ≠ 0) (χ : ContinuousQuasiChar (A.field i))
    (hχ : normQuasiChar (A.field i) K χ = normQuasiChar (A.field 0) K χ₁) :
    ∀ u, u ∈ unitFiltration (A.field i) (A.stationaryDepth i) →
      χ u = A.modelValue i u := by
  intro u hu
  have himage : u ∈ Subgroup.map (normUnits (A.field i) K)
      (unitFiltration K (A.t 1 + 2)) := by
    rw [A.stationary_norm_image hres i hi]
    exact hu
  obtain ⟨x, hx, hxu⟩ := himage
  let z : K := 1 - (x : K)
  have hz : z ∈ lattice K ((A.t 1 : ℤ) + 1) :=
    lattice_antitone K (by omega : (A.t 1 : ℤ) + 1 ≤ (A.t 1 + 2 : ℕ))
      (one_sub_mem_of_unit (by omega) x hx)
  obtain ⟨hz0, hcompat⟩ := compatibility hres P A z hz
  have hxunit : Units.mk0 (1 - z) hz0 = x := by
    apply Units.ext
    simp [z]
  obtain ⟨hu₁, he₁⟩ := hcompat 0
  obtain ⟨_, heᵢ⟩ := hcompat i
  change A.modelValue 0 (normUnits (A.field 0) K (Units.mk0 (1 - z) hz0)) = _ at he₁
  change A.modelValue i (normUnits (A.field i) K (Units.mk0 (1 - z) hz0)) = _ at heᵢ
  rw [hxunit] at he₁ heᵢ hu₁
  calc
    χ u = χ (normUnits (A.field i) K x) := congrArg χ hxu.symm
    _ = χ₁ (normUnits (A.field 0) K x) := DFunLike.congr_fun hχ x
    _ = A.modelValue 0 (normUnits (A.field 0) K x) := hchart₁ _ hu₁
    _ = A.modelValue i (normUnits (A.field i) K x) := he₁.trans heᵢ.symm
    _ = A.modelValue i u := congrArg (A.modelValue i) hxu

omit [CharP F 2] [CharP K 2] in
/-- A nontrivial prescribed commutator obstructs descent from the base.
The crossed norm equivalence used here is supplied by the proved quadratic
norm-character theorem, not by a primitivity assumption. -/
private theorem first_pullback_primitive
    (e : NormCharacter F (A.field 1) ≃* NormCharacter (A.field 0) K)
    (he : ∀ (ω : NormCharacter F (A.field 1)) (v : (A.field 0)ˣ),
      (e ω).1 v = ω.1 (normUnits F (A.field 0) v))
    (ω : NormCharacter F (A.field 1)) (hω : ω ≠ 1)
    (χ : ContinuousQuasiChar (A.field 0))
    (hcomm : ∀ v, χ (Units.map A.firstConjugation.toMonoidHom v / v) =
      (Characters.crossedNormHom F (A.field 0) (A.field 1) K ω).1 v) :
    ¬ ∃ lambda : ContinuousQuasiChar F,
      normQuasiChar F K lambda = normQuasiChar (A.field 0) K χ := by
  rintro ⟨lambda, hlambda⟩
  let μ : NormCharacter (A.field 0) K := ⟨χ / normQuasiChar F (A.field 0) lambda, by
    apply ContinuousMonoidHom.ext
    intro x
    change χ (normUnits (A.field 0) K x) /
      lambda (normUnits F (A.field 0) (normUnits (A.field 0) K x)) = 1
    have hn : normUnits F (A.field 0) (normUnits (A.field 0) K x) = normUnits F K x := by
      apply Units.ext
      exact Basic.norm_tower (F := F) (L := A.field 0) (x : K)
    rw [hn]
    exact div_eq_one.mpr (DFunLike.congr_fun hlambda x).symm⟩
  obtain ⟨η, hη⟩ := e.surjective μ
  have hfixed (v : (A.field 0)ˣ) :
      χ (Units.map A.firstConjugation.toMonoidHom v) = χ v := by
    have hn : normUnits F (A.field 0) (Units.map A.firstConjugation.toMonoidHom v) =
        normUnits F (A.field 0) v := by
      apply Units.ext
      exact Algebra.norm_eq_of_algEquiv A.firstConjugation (v : A.field 0)
    have hμ : μ.1 (Units.map A.firstConjugation.toMonoidHom v) = μ.1 v := by
      rw [← hη, he, he, hn]
    change χ (Units.map A.firstConjugation.toMonoidHom v) /
      lambda (normUnits F (A.field 0) (Units.map A.firstConjugation.toMonoidHom v)) =
        χ v / lambda (normUnits F (A.field 0) v) at hμ
    rw [hn] at hμ
    exact div_left_inj.mp hμ
  apply hω
  apply e.injective
  rw [map_one]
  apply NormCharacter.ext
  apply ContinuousMonoidHom.ext
  intro v
  have h := hcomm v
  change χ (Units.map A.firstConjugation.toMonoidHom v / v) =
    ω.1 (normUnits F (A.field 0) v) at h
  rw [map_div, hfixed, div_self'] at h
  exact (he ω v).trans h.symm

/-- FML's high conductor formula gives the common conductor in the paper. -/
theorem first_pullback_conductor (hres : residueDegree F K = 1)
    (χ : ContinuousQuasiChar (A.field 0))
    (hχ : IsMultiplicativeConductor (A.field 0) χ (A.minimalConductor 0)) :
    IsMultiplicativeConductor K (normQuasiChar (A.field 0) K χ)
      (A.t 0 + 2 * A.t 1 + 1) := by
  letI := A.upperCyclic 0
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer (A.field 0) K
    (origin_residueDegrees F K hres (A.field 0)).2
  have ht : PrimeCyclicExtension.IsLowerBreak (A.field 0) K
      (A.t 0 + 2 * (A.t 1 - A.t 0)) := by simpa using A.upper_break 0
  have hpos := (A.edge 0).2.2.2.1
  have hsmall := A.smallest
  have hm : A.t 0 + 2 * (A.t 1 - A.t 0) + 1 < A.minimalConductor 0 := by
    simp only [minimalConductor, ↓reduceIte]
    omega
  have hc := multiplicativeConductor_compNorm_high (A.field 0) K ht
    (origin_residueDegrees F K hres (A.field 0)).2 pi hpi hgen hm hχ
  rw [(originLine_degrees F K (A.g 0) (A.nontrivial 0)).2,
    herbrandPsiNat_of_break_le _ _ (by omega)] at hc
  convert hc using 1
  · ext x
    rfl
  · simp only [minimalConductor, ↓reduceIte]
    omega

end SimultaneousASGenerators

/-- **Existence of actual minimal models (Theorem 11.6, D:EQ:core-exists).**
The three continuous quasi-characters have their exact odd minimal
conductors and full stationary charts, and their common norm pullback is
invariant and primitive. All coefficients are the actual simultaneous
origin norms. The origin input itself is constructed from the totally
ramified diamond by `simultaneousASGenerators_exists`.

No character extension, descent, phase compatibility, or primitivity is
assumed in this statement. -/
theorem models (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (A : SimultaneousASGenerators F K P) :
    ∃ (Θ : ContinuousQuasiChar K) (χ : (i : Fin 3) → ContinuousQuasiChar (A.field i)),
      (∀ i, IsMultiplicativeConductor (A.field i) (χ i) (A.minimalConductor i) ∧
        Odd (A.minimalConductor i)) ∧
      IsMultiplicativeConductor K Θ (A.t 0 + 2 * A.t 1 + 1) ∧
      (∀ i, normQuasiChar (A.field i) K (χ i) = Θ) ∧
      (∀ (τ : Gal(K/F)) (x : Kˣ), Θ (Units.map τ.toMonoidHom x) = Θ x) ∧
      (¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Θ) ∧
      ∀ (i : Fin 3) (u : (A.field i)ˣ),
        u ∈ unitFiltration (A.field i) (A.stationaryDepth i) →
          χ i u = tracePullbackAddChar F (A.field i)
            (originAddChar F P ((A.t 1 : ℤ) + 1))
            (Algebra.norm (A.field i) A.Y * (1 - (u : A.field i))) := by
  obtain ⟨ω, hω, _, _, _, hcross⟩ := Characters.quadraticProduct F
    (origin_group_equiv F K) A.field
    (fun i ↦ (originLine_degrees F K (A.g i) (A.nontrivial i)).1) A.field_injective
  obtain ⟨e, he⟩ := hcross 0 1 (by decide)
  obtain ⟨χ₁, hchart₁, hcomm⟩ := A.first_model_exists hres (ω 1) (hω 1)
  let Θ := normQuasiChar (A.field 0) K χ₁
  have hinv := A.first_pullback_invariant (ω 1) χ₁ hcomm
  have hprim := A.first_pullback_primitive e he (ω 1) (hω 1) χ₁ hcomm
  have hfamily (i : Fin 3) :
      ∃ χ : ContinuousQuasiChar (A.field i), normQuasiChar (A.field i) K χ = Θ ∧
        ∀ u, u ∈ unitFiltration (A.field i) (A.stationaryDepth i) →
          χ u = A.modelValue i u := by
    by_cases hi : i = 0
    · subst i
      exact ⟨χ₁, rfl, hchart₁⟩
    · letI := A.upperCyclic i
      obtain ⟨χ, hχ⟩ := Local.invariantCharacter_descends (A.field i) K Θ
        (fun σ x ↦ hinv (σ.restrictScalars F) x)
      exact ⟨χ, hχ, A.descended_modelChart hres χ₁ hchart₁ i hi χ hχ⟩
  choose χ hnorm hchart using hfamily
  refine ⟨Θ, χ, fun i ↦ ⟨A.conductor_of_modelChart hres i (χ i) (hchart i),
    (A.model_ledger i).2.2.2.2⟩, ?_, hnorm, hinv, hprim, hchart⟩
  exact A.first_pullback_conductor hres χ₁ (A.conductor_of_modelChart hres 0 χ₁ hchart₁)

end

end LanglandsSecondMainLemma.Dyadic.Equal
