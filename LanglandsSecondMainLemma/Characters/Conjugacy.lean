import LanglandsSecondMainLemma.Characters.CrossedNorm
import LanglandsSecondMainLemma.Local.NormDescent
import LanglandsSecondMainLemma.Basic.LocalConstants
import Mathlib.FieldTheory.LinearDisjoint

/-!
# Conjugate twists and the corrected common restriction

Paper Lemma 4.2 (`U:determinant`, `U:conjugacy`), lines 545–589 of
`references/epsilon_SML.tex`; the crossed norm input is Lemma `D:crossed-norm`.

Compatibility makes the common character invariant under the two upper fixing
subgroups, which generate the actual Galois group. Its lower conjugate quotients
are therefore upper norm characters. Crossed norms make those characters fixed,
so the quotient map is a homomorphism. Prime degree and continuous norm descent
make it an equivalence when the common pullback is primitive.

For the corrected restriction, multiplication over the full Galois orbit is
reindexed by that equivalence. Mathlib's norm base-change theorem then proves
agreement on both lower norm images. Injectivity of the crossed norm map gives
agreement on the entire base multiplicative group. The complete products are
retained before specializing to odd degree or degree two.
-/

open LanglandsFirstMainLemma
open scoped BigOperators
namespace LanglandsSecondMainLemma.Characters
noncomputable section

private theorem inf_eq_bot_of_prime_degree
    {F K : Type} [Field F] [Field K] [Algebra F K] [Module.Finite F K]
    {p : ℕ} (hp : p.Prime) (I J : IntermediateField F K)
    (hI : Module.finrank F I = p) (hJ : Module.finrank F J = p) (hne : I ≠ J) :
    I ⊓ J = ⊥ := by
  have hdvd : Module.finrank F ↥(I ⊓ J) ∣ p := by
    rw [← hI]
    exact IntermediateField.finrank_dvd_of_le_right inf_le_left
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact IntermediateField.finrank_eq_one_iff.mp h
  · have heq : I ⊓ J = I :=
      IntermediateField.eq_of_le_of_finrank_eq inf_le_left (h.trans hI.symm)
    have hle : I ≤ J := by rw [← heq]; exact inf_le_right
    exact (hne (IntermediateField.eq_of_le_of_finrank_eq hle (hI.trans hJ.symm))).elim

private def characterFixingSubgroup
    {F E : Type} [Field F] [Field E] [Algebra F E] (χ : Eˣ →* ℂˣ) :
    Subgroup Gal(E/F) where
  carrier := {σ | ∀ x, χ (Units.map σ.toMonoidHom x) = χ x}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro σ τ hσ hτ x
    calc
      χ (Units.map (σ * τ).toMonoidHom x) =
          χ (Units.map σ.toMonoidHom (Units.map τ.toMonoidHom x)) := rfl
      _ = χ x := (hσ _).trans (hτ x)
  inv_mem' := by
    intro σ hσ x
    have h := hσ (Units.map σ.symm.toMonoidHom x)
    have hx : Units.map σ.toMonoidHom (Units.map σ.symm.toMonoidHom x) = x := by
      ext; simp
    rw [hx] at h
    exact h.symm

private theorem normUnits_automorphism
    {F E : Type} [Field F] [Field E] [Algebra F E]
    (σ : Gal(E/F)) (x : Eˣ) :
    normUnits F E (Units.map σ.toMonoidHom x) = normUnits F E x := by
  apply Units.ext
  exact Algebra.norm_eq_of_algEquiv σ (x : E)

private theorem normUnits_liftNormal
    {F E K : Type} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K] [Algebra E K] [IsScalarTower F E K]
    [Normal F K] (σ : Gal(E/F)) (x : Kˣ) :
    normUnits E K (Units.map (σ.liftNormal K).toMonoidHom x) =
      Units.map σ.toMonoidHom (normUnits E K x) := by
  apply Units.ext
  have h := Algebra.norm_eq_of_equiv_equiv σ.toRingEquiv
    (σ.liftNormal K).toRingEquiv (by ext y; simp) (x : K)
  simpa using (congrArg σ h).symm

section Pair
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  (I J : IntermediateField F K)
  [ValuativeRel I] [TopologicalSpace I] [IsNonarchimedeanLocalField I]
  [ValuativeRel J] [TopologicalSpace J] [IsNonarchimedeanLocalField J]
  [ValuativeExtension I K] [ValuativeExtension J K]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeExtension F K] in
private theorem compatible_invariant
    (hinf : I ⊓ J = ⊥) (θI : ContinuousQuasiChar I) (θJ : ContinuousQuasiChar J)
    (Θ : ContinuousQuasiChar K)
    (hcI : normQuasiChar I K θI = Θ) (hcJ : normQuasiChar J K θJ = Θ) :
    ∀ (σ : Gal(K/F)) (x : Kˣ), Θ (Units.map σ.toMonoidHom x) = Θ x := by
  have hsup : I.fixingSubgroup ⊔ J.fixingSubgroup = ⊤ := by
    have h := (IsGalois.intermediateFieldEquivSubgroup (F := F) (E := K)).map_inf I J
    change (I ⊓ J).fixingSubgroup = I.fixingSubgroup ⊔ J.fixingSubgroup at h
    rw [hinf, IntermediateField.fixingSubgroup_bot] at h
    exact h.symm
  have hI : I.fixingSubgroup ≤ characterFixingSubgroup Θ.toMonoidHom := by
    intro σ hσ x
    rw [← hcI]
    change θI (normUnits I K (Units.map σ.toMonoidHom x)) = θI (normUnits I K x)
    exact congrArg θI (normUnits_automorphism (I.fixingSubgroupEquiv ⟨σ, hσ⟩) x)
  have hJ : J.fixingSubgroup ≤ characterFixingSubgroup Θ.toMonoidHom := by
    intro σ hσ x
    rw [← hcJ]
    change θJ (normUnits J K (Units.map σ.toMonoidHom x)) = θJ (normUnits J K x)
    exact congrArg θJ (normUnits_automorphism (J.fixingSubgroupEquiv ⟨σ, hσ⟩) x)
  have htop : ⊤ ≤ characterFixingSubgroup Θ.toMonoidHom := hsup ▸ sup_le hI hJ
  exact fun σ => htop (Subgroup.mem_top σ)
end Pair
section Edge
variable (F E K : Type) [Field F] [Field E] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
  [ValuativeExtension F E] [ValuativeExtension E K]
  [Module.Finite F E] [Module.Finite E K]

/-- The full conjugation orbit is parametrized by the actual upper norm characters.
The quotient uses the manuscript's convention `θ^σ(x) = θ(σ⁻¹ x)`. -/
structure ConjugateTwistData (θ : ContinuousQuasiChar E) where
  quotientEquiv : Gal(E/F) ≃* NormCharacter E K
  quotient_eq : ∀ σ, (quotientEquiv σ).1 = Basic.conjugateQuasiChar F E σ θ / θ
  fixed : ∀ (μ : NormCharacter E K) (σ : Gal(E/F)),
    Basic.conjugateQuasiChar F E σ μ.1 = μ.1

variable {F E K}

private def conjugateQuotient
    [Normal F K] (θ : ContinuousQuasiChar E) (Θ : ContinuousQuasiChar K)
    (hc : normQuasiChar E K θ = Θ)
    (hinv : ∀ (σ : Gal(K/F)) (x : Kˣ), Θ (Units.map σ.toMonoidHom x) = Θ x)
    (σ : Gal(E/F)) : NormCharacter E K :=
  ⟨Basic.conjugateQuasiChar F E σ θ / θ, by
    apply ContinuousMonoidHom.ext
    intro x
    change θ (Units.map σ.symm.toMonoidHom (normUnits E K x)) /
      θ (normUnits E K x) = 1
    rw [← normUnits_liftNormal σ.symm x]
    have hy : ∀ y, θ (normUnits E K y) = Θ y := DFunLike.congr_fun hc
    rw [hy, hy, hinv]
    simp⟩

private def conjugateQuotientHom
    [Normal F K] (θ : ContinuousQuasiChar E) (Θ : ContinuousQuasiChar K)
    (hc : normQuasiChar E K θ = Θ)
    (hinv : ∀ (σ : Gal(K/F)) (x : Kˣ), Θ (Units.map σ.toMonoidHom x) = Θ x)
    (hfixed : ∀ (μ : NormCharacter E K) (σ : Gal(E/F)),
      Basic.conjugateQuasiChar F E σ μ.1 = μ.1) :
    Gal(E/F) →* NormCharacter E K where
  toFun := conjugateQuotient θ Θ hc hinv
  map_one' := by
    apply NormCharacter.ext
    apply ContinuousMonoidHom.ext
    intro x
    change θ x / θ x = 1
    simp
  map_mul' σ τ := by
    apply NormCharacter.ext
    apply ContinuousMonoidHom.ext
    intro x
    have h := DFunLike.congr_fun (hfixed (conjugateQuotient θ Θ hc hinv τ) σ) x
    change θ (Units.map τ.symm.toMonoidHom (Units.map σ.symm.toMonoidHom x)) /
      θ (Units.map σ.symm.toMonoidHom x) = θ (Units.map τ.symm.toMonoidHom x) / θ x at h
    change θ (Units.map (σ * τ).symm.toMonoidHom x) / θ x =
      (θ (Units.map σ.symm.toMonoidHom x) / θ x) *
      (θ (Units.map τ.symm.toMonoidHom x) / θ x)
    have hmap : Units.map (σ * τ).symm.toMonoidHom x =
        Units.map τ.symm.toMonoidHom (Units.map σ.symm.toMonoidHom x) := by
      ext; rfl
    rw [hmap, ← h]
    rw [mul_comm, div_mul_div_cancel]

private theorem conjugateTwistData_exists
    [Normal F K] [PrimeCyclicExtension F E] [PrimeCyclicExtension E K]
    {p : ℕ} (hp : p.Prime) (hE : Module.finrank F E = p)
    (hcard : Nat.card (NormCharacter E K) = p)
    (θ : ContinuousQuasiChar E) (Θ : ContinuousQuasiChar K)
    (hc : normQuasiChar E K θ = Θ)
    (hinv : ∀ (σ : Gal(K/F)) (x : Kˣ), Θ (Units.map σ.toMonoidHom x) = Θ x)
    (hprimitive : ¬ ∃ χ : ContinuousQuasiChar F, normQuasiChar F E χ = θ)
    (hfixed : ∀ (μ : NormCharacter E K) (σ : Gal(E/F)),
      Basic.conjugateQuasiChar F E σ μ.1 = μ.1) :
    Nonempty (ConjugateTwistData F E K θ) := by
  let f := conjugateQuotientHom θ Θ hc hinv hfixed
  have hGal : Nat.card Gal(E/F) = p := (IsGalois.card_aut_eq_finrank F E).trans hE
  letI : Fact (Nat.card Gal(E/F)).Prime := ⟨hGal ▸ hp⟩
  have hf : Function.Injective f := by
    rcases f.ker.eq_bot_or_eq_top_of_prime_card with h | h
    · exact (MonoidHom.ker_eq_bot_iff f).mp h
    · exfalso
      apply hprimitive
      apply Local.invariantCharacter_descends F E θ
      intro σ x
      have hq : f σ.symm = 1 := by
        change σ.symm ∈ f.ker
        rw [h]; exact Subgroup.mem_top _
      have hx := DFunLike.congr_fun (congrArg Subtype.val hq) x
      change θ (Units.map σ.symm.symm.toMonoidHom x) / θ x = 1 at hx
      exact div_eq_one.mp hx
  letI := primeCyclicNormCharacter_finite E K
  exact ⟨⟨MulEquiv.ofBijective f
    ((Nat.bijective_iff_injective_and_card f).2 ⟨hf, hGal.trans hcard.symm⟩),
    fun _ => rfl, hfixed⟩⟩

end Edge
section Products
variable (F E : Type) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]

/-- Restriction along the actual inclusion of the base field. -/
def restrictQuasiChar (θ : ContinuousQuasiChar E) : ContinuousQuasiChar F :=
  θ.comp ⟨Units.map (algebraMap F E),
    (LanglandsFirstMainLemma.continuous_algebraMap F E).units_map _⟩

/-- The complete lower norm-character product `ε = ∏ ω ∈ S(E/F), ω`.
Finiteness is supplied by FML on each prime cyclic edge. -/
def normCharacterProduct [Finite (NormCharacter F E)] : ContinuousQuasiChar F := by
  letI := normCharacterFintype F E
  exact (∏ ω : NormCharacter F E, ω).1

private def normCharacterEvaluation (x : Fˣ) : NormCharacter F E →* ℂˣ where
  toFun ω := ω.1 x
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem normCharacterProduct_apply [Finite (NormCharacter F E)] (x : Fˣ) :
    normCharacterProduct F E x =
      (normCharacterFinset F E).prod (fun ω => ω.1 x) := by
  letI := normCharacterFintype F E
  exact map_prod (normCharacterEvaluation F E x) _ _

private theorem normCharacterProduct_norm [Finite (NormCharacter F E)] (x : Eˣ) :
    normCharacterProduct F E (normUnits F E x) = 1 := by
  letI := normCharacterFintype F E
  exact (∏ ω : NormCharacter F E, ω).eq_one_on_normRange F E _ ⟨x, rfl⟩

private theorem primeNormCharacter_card [PrimeCyclicExtension F E] :
    Nat.card (NormCharacter F E) = Module.finrank F E := by
  by_cases h : ramificationIndex F E = 1
  · exact unramifiedNormCharacter_card F E h
  · let P := primeCyclicPreparation F E h
    exact ramifiedNormCharacter_card F E P.ht P.hres P.piK P.hpiK P.hgen

private theorem normCharacterProduct_odd [Finite (NormCharacter F E)]
    (hodd : Odd (Nat.card (NormCharacter F E))) : normCharacterProduct F E = 1 := by
  letI := normCharacterFintype F E
  suffices hprod : (∏ ω : NormCharacter F E, ω) = 1 from congrArg Subtype.val hprod
  apply Finset.prod_ninvolution Inv.inv
  · intro ω; exact mul_inv_cancel ω
  · intro ω hω hinv
    have hsq : ω ^ 2 = 1 := by simpa only [hinv, pow_two] using inv_mul_cancel ω
    have hpow := pow_card_eq_one' (x := ω)
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_add, pow_mul, hsq, one_pow, pow_one, one_mul] at hpow
    exact hω hpow
  · intro ω; exact Finset.mem_univ _
  · intro ω; exact inv_inv ω

private theorem normCharacterProduct_two [Finite (NormCharacter F E)]
    (hcard : Nat.card (NormCharacter F E) = 2)
    (ω : NormCharacter F E) (hω : ω ≠ 1) : normCharacterProduct F E = ω.1 := by
  classical
  letI := normCharacterFintype F E
  have huniv : (Finset.univ : Finset (NormCharacter F E)) = {1, ω} := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      have huniq := (Nat.card_eq_two_iff' (1 : NormCharacter F E)).mp hcard
      by_cases hx1 : x = 1
      · simp [hx1]
      · have hxeq : x = ω := huniq.unique hx1 hω
        simp [hxeq]
    · simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard] using
        (Finset.card_le_two (a := (1 : NormCharacter F E)) (b := ω))
  change (∏ ν : NormCharacter F E, ν).1 = ω.1
  rw [huniv]
  simp

end Products
section TwistConsequences
variable {F E K : Type} [Field F] [Field E] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F E] [Algebra E K]
  [ValuativeExtension F E] [ValuativeExtension E K]
  [Module.Finite F E] [Module.Finite E K]
  {θ : ContinuousQuasiChar E}

/-- Each Galois conjugate is the twist corresponding to its quotient. -/
theorem ConjugateTwistData.conjugate_eq_twist (D : ConjugateTwistData F E K θ)
    (σ : Gal(E/F)) : Basic.conjugateQuasiChar F E σ θ = θ * (D.quotientEquiv σ).1 := by
  rw [D.quotient_eq]
  simp [div_eq_mul_inv]

/-- A generator has a quotient generating the entire upper norm-character group. -/
theorem ConjugateTwistData.generates (D : ConjugateTwistData F E K θ)
    (σ : Gal(E/F)) (hσ : Subgroup.zpowers σ = ⊤) :
    Subgroup.zpowers (D.quotientEquiv σ) = ⊤ := by
  calc
    Subgroup.zpowers (D.quotientEquiv σ) =
        (Subgroup.zpowers σ).map D.quotientEquiv.toMonoidHom :=
      (D.quotientEquiv.toMonoidHom.map_zpowers σ).symm
    _ = ⊤ := by
      rw [hσ]
      exact Subgroup.map_top_of_surjective _ D.quotientEquiv.surjective

/-- Equality of the full orbit and the full set of norm-character twists. -/
theorem ConjugateTwistData.orbit_eq_twists (D : ConjugateTwistData F E K θ) :
    Set.range (fun σ : Gal(E/F) => Basic.conjugateQuasiChar F E σ θ) =
      Set.range (fun μ : NormCharacter E K => θ * μ.1) := by
  ext χ
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨D.quotientEquiv σ, (D.conjugate_eq_twist σ).symm⟩
  · rintro ⟨μ, rfl⟩
    obtain ⟨σ, rfl⟩ := D.quotientEquiv.surjective μ
    exact ⟨σ, D.conjugate_eq_twist σ⟩

private theorem ConjugateTwistData.norm_restriction
    [IsGalois F E] [Finite (NormCharacter E K)]
    (D : ConjugateTwistData F E K θ) (x : Eˣ) :
    restrictQuasiChar F E θ (normUnits F E x) =
      θ x ^ Nat.card (NormCharacter E K) * normCharacterProduct E K x := by
  classical
  letI := normCharacterFintype E K
  have hnorm : Units.map (algebraMap F E) (normUnits F E x) =
      ∏ σ : Gal(E/F), Units.map σ.symm.toMonoidHom x := by
    apply Units.ext
    change algebraMap F E (Algebra.norm F (x : E)) =
      Units.coeHom E (∏ σ : Gal(E/F), Units.map σ.symm.toMonoidHom x)
    rw [map_prod]
    change algebraMap F E (Algebra.norm F (x : E)) = ∏ σ : Gal(E/F), σ.symm (x : E)
    rw [Algebra.norm_eq_prod_automorphisms]
    exact (Equiv.prod_comp (Equiv.inv Gal(E/F)) (fun σ : Gal(E/F) => σ (x : E))).symm
  calc
    restrictQuasiChar F E θ (normUnits F E x) =
        ∏ σ : Gal(E/F), Basic.conjugateQuasiChar F E σ θ x := by
      change θ (Units.map (algebraMap F E) (normUnits F E x)) = _
      rw [hnorm, map_prod]
      rfl
    _ = ∏ μ : NormCharacter E K, (θ * μ.1) x :=
      Fintype.prod_equiv D.quotientEquiv.toEquiv _ _ (fun σ =>
        DFunLike.congr_fun (D.conjugate_eq_twist σ) x)
    _ = θ x ^ Nat.card (NormCharacter E K) * normCharacterProduct E K x := by
      simp only [ContinuousQuasiChar.mul_apply, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
      rw [normCharacterProduct_apply]
      rfl

end TwistConsequences
section TowerConsequences
variable {F I J K : Type} [Field F] [Field I] [Field J] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel I] [TopologicalSpace I] [IsNonarchimedeanLocalField I]
  [ValuativeRel J] [TopologicalSpace J] [IsNonarchimedeanLocalField J]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F I] [Algebra F J] [Algebra F K] [Algebra I K] [Algebra J K]
  [IsScalarTower F I K] [IsScalarTower F J K]
  [ValuativeExtension F I] [ValuativeExtension F J]
  [ValuativeExtension I K] [ValuativeExtension J K] [ValuativeExtension F K]
  [Module.Finite F I] [Module.Finite F J]
  [Module.Finite I K] [Module.Finite J K] [Module.Finite F K]

private theorem primitive_lower
    (θ : ContinuousQuasiChar I) (Θ : ContinuousQuasiChar K)
    (hc : normQuasiChar I K θ = Θ)
    (hprimitive : ¬ ∃ χ : ContinuousQuasiChar F, normQuasiChar F K χ = Θ) :
    ¬ ∃ χ : ContinuousQuasiChar F, normQuasiChar F I χ = θ := by
  rintro ⟨χ, hχ⟩
  apply hprimitive
  refine ⟨χ, ?_⟩
  rw [← hc, ← hχ]
  apply ContinuousMonoidHom.ext
  intro x
  change χ (normUnits F K x) = χ (normUnits F I (normUnits I K x))
  congr 1
  apply Units.ext
  exact (Basic.norm_tower (F := F) (L := I) (x : K)).symm

omit [ValuativeExtension J K] [ValuativeExtension F K] [Module.Finite F K] in
private theorem upperNormCharacter_fixed
    [PrimeCyclicExtension F I] [PrimeCyclicExtension F J] [PrimeCyclicExtension I K]
    {p : ℕ} (hp : p.Prime)
    (hI : Module.finrank F I = p) (hJ : Module.finrank F J = p)
    (hIK : Module.finrank I K = p)
    (hne : (normUnits F I).range ≠ (normUnits F J).range)
    (μ : NormCharacter I K) (σ : Gal(I/F)) :
    Basic.conjugateQuasiChar F I σ μ.1 = μ.1 := by
  obtain ⟨ω, rfl⟩ := (crossedNormEquivOfTowers F I J K hp hI hJ hIK hne).surjective μ
  apply ContinuousMonoidHom.ext
  intro x
  change ω.1 (normUnits F I (Units.map σ.symm.toMonoidHom x)) = ω.1 (normUnits F I x)
  rw [normUnits_automorphism]

omit [ValuativeExtension J K] [ValuativeExtension F K] [Module.Finite F K] in
private theorem crossedNorm_product
    [PrimeCyclicExtension F I] [PrimeCyclicExtension F J] [PrimeCyclicExtension I K]
    [Finite (NormCharacter F J)] [Finite (NormCharacter I K)]
    {p : ℕ} (hp : p.Prime)
    (hI : Module.finrank F I = p) (hJ : Module.finrank F J = p)
    (hIK : Module.finrank I K = p)
    (hne : (normUnits F I).range ≠ (normUnits F J).range) (x : Iˣ) :
    normCharacterProduct F J (normUnits F I x) = normCharacterProduct I K x := by
  letI := normCharacterFintype F J
  letI := normCharacterFintype I K
  simp only [normCharacterProduct_apply]
  exact Fintype.prod_equiv
    (crossedNormEquivOfTowers F I J K hp hI hJ hIK hne).toEquiv _ _ (fun _ => rfl)

omit [ValuativeExtension J K] [ValuativeExtension F K] [Module.Finite F K] in
private theorem restriction_eq_of_norms
    [PrimeCyclicExtension F I] [PrimeCyclicExtension F J] [PrimeCyclicExtension I K]
    {p : ℕ} (hp : p.Prime)
    (hI : Module.finrank F I = p) (hJ : Module.finrank F J = p)
    (hIK : Module.finrank I K = p)
    (hne : (normUnits F I).range ≠ (normUnits F J).range)
    (χ ψ : ContinuousQuasiChar F)
    (heqI : ∀ x : Iˣ, χ (normUnits F I x) = ψ (normUnits F I x))
    (heqJ : ∀ x : Jˣ, χ (normUnits F J x) = ψ (normUnits F J x)) : χ = ψ := by
  let ω : NormCharacter F J := ⟨χ / ψ, by
    apply ContinuousMonoidHom.ext
    intro x
    change χ (normUnits F J x) / ψ (normUnits F J x) = 1
    rw [heqJ]; simp⟩
  let e := crossedNormEquivOfTowers F I J K hp hI hJ hIK hne
  have hω : e ω = 1 := by
    apply NormCharacter.ext
    apply ContinuousMonoidHom.ext
    intro x
    change χ (normUnits F I x) / ψ (normUnits F I x) = 1
    rw [heqI]; simp
  have hω1 : ω = 1 := e.injective (hω.trans e.map_one.symm)
  exact div_eq_one.mp (congrArg Subtype.val hω1)

end TowerConsequences

section DiamondAlgebra
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  (I J : IntermediateField F K)
  [ValuativeRel I] [TopologicalSpace I] [IsNonarchimedeanLocalField I]
  [ValuativeRel J] [TopologicalSpace J] [IsNonarchimedeanLocalField J]
  [ValuativeExtension F I] [ValuativeExtension F J]
  [ValuativeExtension I K] [ValuativeExtension J K]

omit [ValuativeExtension F K] [ValuativeExtension F J] in
private theorem compatible_cross_value
    {p : ℕ} (hJK : Module.finrank J K = p)
    (hdisjoint : I.LinearDisjoint J) (hsup : I ⊔ J = ⊤)
    (θI : ContinuousQuasiChar I) (θJ : ContinuousQuasiChar J) (Θ : ContinuousQuasiChar K)
    (hcI : normQuasiChar I K θI = Θ) (hcJ : normQuasiChar J K θJ = Θ) (x : Jˣ) :
    restrictQuasiChar F I θI (normUnits F J x) = θJ x ^ p := by
  have hcross : normUnits I K (Units.map (algebraMap J K) x) =
      Units.map (algebraMap F I) (normUnits F J x) := by
    apply Units.ext
    exact hdisjoint.norm_algebraMap hsup (x : J)
  have hscalar : normUnits J K (Units.map (algebraMap J K) x) = x ^ p := by
    apply Units.ext
    change Algebra.norm J (algebraMap J K (x : J)) = (x : J) ^ p
    rw [Algebra.norm_algebraMap, hJK]
  have hcomp := (DFunLike.congr_fun hcI (Units.map (algebraMap J K) x)).trans
    (DFunLike.congr_fun hcJ (Units.map (algebraMap J K) x)).symm
  change θI (normUnits I K (Units.map (algebraMap J K) x)) =
    θJ (normUnits J K (Units.map (algebraMap J K) x)) at hcomp
  change θI (Units.map (algebraMap F I) (normUnits F J x)) = _
  rw [← hcross, hcomp, hscalar, map_pow]

end DiamondAlgebra
section Diamond
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

/-- The paper's lower correction character for an actual intermediate field.
The canonical restricted topology and the finiteness of `S(I/F)` are constructed
from the genuine prime-square diamond. -/
def intermediateNormCharacterProduct
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (I : IntermediateField F K) (hI : Module.finrank F I = p) : ContinuousQuasiChar F := by
  letI := Basic.intermediateFieldValuativeRel I
  letI := Basic.intermediateFieldTopology I
  letI := Basic.intermediateField_localField I
  letI := Basic.intermediateField_lowerValuativeExtension I
  have hdata := Basic.intermediateField_tower_compatible hp hG I hI
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F I hdata.2.2.2.2.2.2.2.2.2.2.2.1
  letI := primeCyclicNormCharacter_finite F I
  exact normCharacterProduct F I

/-- **Paper Lemma 4.2 (`U:determinant`, `U:conjugacy`).**
For a primitive compatible pair on distinct lower norm subgroups, each lower
Galois group is identified with its upper norm-character group by
`σ ↦ θ^σ / θ`. The data give invariance of every upper norm character,
and `ConjugateTwistData.generates` and `.orbit_eq_twists` give precisely the
paper's generator and orbit assertions. The restrictions corrected by the
*complete* lower norm-character products agree. Those products are trivial
in odd degree and are the nontrivial lower norm characters in degree two.

Only the actual pair, its common norm pullback, and failure of descent to `F`
are character hypotheses. Invariance of that common pullback, all edge
structures, the conjugate quotients, and the required equivalences are proved.
No residue-characteristic, ramification, conductor, or unitarity restriction
is imposed. -/
theorem conjugacy
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (I J : IntermediateField F K)
    (hI : Module.finrank F I = p) (hJ : Module.finrank F J = p)
    (hne : Ramification.intermediateNormRange I ≠ Ramification.intermediateNormRange J) :
    letI := Basic.intermediateFieldValuativeRel I
    letI := Basic.intermediateFieldTopology I
    letI := Basic.intermediateField_localField I
    letI := Basic.intermediateField_lowerValuativeExtension I
    letI := Basic.intermediateField_upperValuativeExtension I
    letI := Basic.intermediateFieldValuativeRel J
    letI := Basic.intermediateFieldTopology J
    letI := Basic.intermediateField_localField J
    letI := Basic.intermediateField_lowerValuativeExtension J
    letI := Basic.intermediateField_upperValuativeExtension J
    ∀ (θI : ContinuousQuasiChar I) (θJ : ContinuousQuasiChar J) (Θ : ContinuousQuasiChar K),
      normQuasiChar I K θI = Θ → normQuasiChar J K θJ = Θ →
      (¬ ∃ χ : ContinuousQuasiChar F, normQuasiChar F K χ = Θ) →
      Nonempty (ConjugateTwistData F I K θI) ∧
      Nonempty (ConjugateTwistData F J K θJ) ∧
      restrictQuasiChar F I θI * intermediateNormCharacterProduct hp hG I hI =
        restrictQuasiChar F J θJ * intermediateNormCharacterProduct hp hG J hJ ∧
      (Odd p → intermediateNormCharacterProduct hp hG I hI = 1 ∧
        intermediateNormCharacterProduct hp hG J hJ = 1) ∧
      (p = 2 → ∃ (ωI : NormCharacter F I) (ωJ : NormCharacter F J),
        ωI ≠ 1 ∧ ωJ ≠ 1 ∧
        intermediateNormCharacterProduct hp hG I hI = ωI.1 ∧
        intermediateNormCharacterProduct hp hG J hJ = ωJ.1) := by
  letI := Basic.intermediateFieldValuativeRel I
  letI := Basic.intermediateFieldTopology I
  letI := Basic.intermediateField_localField I
  letI := Basic.intermediateField_lowerValuativeExtension I
  letI := Basic.intermediateField_upperValuativeExtension I
  letI := Basic.intermediateFieldValuativeRel J
  letI := Basic.intermediateFieldTopology J
  letI := Basic.intermediateField_localField J
  letI := Basic.intermediateField_lowerValuativeExtension J
  letI := Basic.intermediateField_upperValuativeExtension J
  intro θI θJ Θ hcI hcJ hprimitive
  have hdataI := Basic.intermediateField_tower_compatible hp hG I hI
  have hdataJ := Basic.intermediateField_tower_compatible hp hG J hJ
  have hIK := hdataI.2.2.2.2.2.2.2.2.2.2.1
  have hJK := hdataJ.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F I hdataI.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension I K hdataI.2.2.2.2.2.2.2.2.2.2.2.2
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F J hdataJ.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension J K hdataJ.2.2.2.2.2.2.2.2.2.2.2.2
  have hIJ : I ≠ J := fun h => hne (congrArg Ramification.intermediateNormRange h)
  have hinf := inf_eq_bot_of_prime_degree hp I J hI hJ hIJ
  have hdisjoint : I.LinearDisjoint J := IntermediateField.LinearDisjoint.of_inf_eq_bot hinf
  have hsup : I ⊔ J = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [hdisjoint.finrank_sup, IntermediateField.finrank_top', hI, hJ]
    exact hdataI.2.2.2.2.2.2.2.2.1.symm
  have hinv := compatible_invariant I J hinf θI θJ Θ hcI hcJ
  obtain ⟨DI⟩ := conjugateTwistData_exists hp hI
    ((primeNormCharacter_card I K).trans hIK) θI Θ hcI hinv
    (primitive_lower θI Θ hcI hprimitive)
    (upperNormCharacter_fixed (K := K) hp hI hJ hIK hne)
  obtain ⟨DJ⟩ := conjugateTwistData_exists hp hJ
    ((primeNormCharacter_card J K).trans hJK) θJ Θ hcJ hinv
    (primitive_lower θJ Θ hcJ hprimitive)
    (upperNormCharacter_fixed (K := K) hp hJ hI hJK hne.symm)
  letI := primeCyclicNormCharacter_finite F I
  letI := primeCyclicNormCharacter_finite F J
  letI := primeCyclicNormCharacter_finite I K
  letI := primeCyclicNormCharacter_finite J K
  change Nonempty (ConjugateTwistData F I K θI) ∧
    Nonempty (ConjugateTwistData F J K θJ) ∧
    restrictQuasiChar F I θI * normCharacterProduct F I =
      restrictQuasiChar F J θJ * normCharacterProduct F J ∧
    (Odd p → normCharacterProduct F I = 1 ∧ normCharacterProduct F J = 1) ∧
    (p = 2 → ∃ (ωI : NormCharacter F I) (ωJ : NormCharacter F J),
      ωI ≠ 1 ∧ ωJ ≠ 1 ∧ normCharacterProduct F I = ωI.1 ∧
      normCharacterProduct F J = ωJ.1)
  refine ⟨⟨DI⟩, ⟨DJ⟩, ?_, ?_, ?_⟩
  · apply restriction_eq_of_norms (K := K) hp hI hJ hIK hne
    · intro x
      rw [ContinuousQuasiChar.mul_apply, ContinuousQuasiChar.mul_apply,
        normCharacterProduct_norm, mul_one,
        compatible_cross_value J I hIK hdisjoint.symm (by rwa [sup_comm]) θJ θI Θ hcJ hcI,
        DI.norm_restriction, primeNormCharacter_card, hIK,
        ← crossedNorm_product hp hI hJ hIK hne]
    · intro x
      rw [ContinuousQuasiChar.mul_apply, ContinuousQuasiChar.mul_apply,
        normCharacterProduct_norm, mul_one,
        compatible_cross_value I J hJK hdisjoint hsup θI θJ Θ hcI hcJ,
        DJ.norm_restriction, primeNormCharacter_card, hJK,
        ← crossedNorm_product hp hJ hI hJK hne.symm]
  · intro hodd
    exact ⟨normCharacterProduct_odd F I (by rwa [primeNormCharacter_card, hI]),
      normCharacterProduct_odd F J (by rwa [primeNormCharacter_card, hJ])⟩
  · intro hp2
    have hcFI : Nat.card (NormCharacter F I) = 2 :=
      (primeNormCharacter_card F I).trans (hI.trans hp2)
    have hcFJ : Nat.card (NormCharacter F J) = 2 :=
      (primeNormCharacter_card F J).trans (hJ.trans hp2)
    obtain ⟨ωI, hωI, _⟩ := (Nat.card_eq_two_iff' (1 : NormCharacter F I)).mp hcFI
    obtain ⟨ωJ, hωJ, _⟩ := (Nat.card_eq_two_iff' (1 : NormCharacter F J)).mp hcFJ
    exact ⟨ωI, ωJ, hωI, hωJ, normCharacterProduct_two F I hcFI ωI hωI,
      normCharacterProduct_two F J hcFJ ωJ hωJ⟩

end Diamond
end
end LanglandsSecondMainLemma.Characters
