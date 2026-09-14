import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Ramification.NormSeparation
import LanglandsSecondMainLemma.Basic.Characters
import LanglandsSecondMainLemma.Basic.NormTrace

/-!
# Crossed norm characters

Paper Lemma D.5 (`D:crossed-norm`). Norm transitivity constructs the pullback.
Distinct lower norm subgroups of prime index generate the base unit group,
so this pullback is injective. FML computes both character-group orders,
which proves surjectivity. The public equivalence uses genuine intermediate
fields with their accepted restricted valuations and topologies.
-/

namespace LanglandsSecondMainLemma.Characters

open LanglandsFirstMainLemma

noncomputable section

private theorem eq_of_le_of_index_eq
    {G : Type*} [Group G] {H J : Subgroup G} (hle : H ≤ J)
    (hindex : H.index = J.index) (hne : J.index ≠ 0) : H = J := by
  apply le_antisymm hle
  apply Subgroup.relIndex_eq_one.mp
  have h := Subgroup.relIndex_mul_index hle
  rw [hindex] at h
  exact Nat.mul_right_cancel (Nat.pos_of_ne_zero hne) (by simpa using h)

/-- Distinct subgroups of the same prime index generate the whole group. -/
private theorem sup_eq_top_of_distinct_prime_index
    {G : Type*} [Group G] {H J : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hH : H.index = p) (hJ : J.index = p)
    (hne : H ≠ J) : H ⊔ J = ⊤ := by
  have hdvd : (H ⊔ J).index ∣ p := by
    rw [← hH]
    exact Subgroup.index_dvd_of_le le_sup_left
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact Subgroup.index_eq_one.mp h
  · have heqH : H = H ⊔ J :=
      eq_of_le_of_index_eq le_sup_left (hH.trans h.symm) (h.trans_ne hp.ne_zero)
    have heqJ : J = H ⊔ J :=
      eq_of_le_of_index_eq le_sup_right (hJ.trans h.symm) (h.trans_ne hp.ne_zero)
    exact (hne (heqH.trans heqJ.symm)).elim

section PrimeEdge

variable (F E : Type) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E]
  [Module.Free F E] [Module.Finite F E] [PrimeCyclicExtension F E]

/-- Both prime norm-index computations, without restricting the ramification case. -/
private theorem primeNormCards :
    (normUnits F E).range.index = Module.finrank F E ∧
      Nat.card (NormCharacter F E) = Module.finrank F E := by
  by_cases hunr : ramificationIndex F E = 1
  · exact ⟨unramifiedNormQuotient_card F E hunr,
      unramifiedNormCharacter_card F E hunr⟩
  · let P := primeCyclicPreparation F E hunr
    exact ⟨normQuotient_card F E P.ht P.hres P.piK P.hpiK P.hgen,
      ramifiedNormCharacter_card F E P.ht P.hres P.piK P.hpiK P.hgen⟩

end PrimeEdge

section Towers

variable (F I J K : Type) [Field F] [Field I] [Field J] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel I] [TopologicalSpace I] [IsNonarchimedeanLocalField I]
  [ValuativeRel J] [TopologicalSpace J] [IsNonarchimedeanLocalField J]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F I] [Algebra F J] [Algebra F K] [Algebra I K] [Algebra J K]
  [IsScalarTower F I K] [IsScalarTower F J K]
  [ValuativeExtension F I] [ValuativeExtension F J]
  [ValuativeExtension I K]
  [Module.Finite F I] [Module.Finite F J]
  [Module.Finite I K] [Module.Finite J K]

/-- The crossed pullback is norm-trivial by the two actual norm towers. -/
def crossedNormHom : NormCharacter F J →* NormCharacter I K where
  toFun ω := ⟨normQuasiChar F I ω.1, by
    apply ContinuousMonoidHom.ext
    intro x
    change ω.1 (normUnits F I (normUnits I K x)) = 1
    have htower : normUnits F I (normUnits I K x) =
        normUnits F J (normUnits J K x) := by
      apply Units.ext
      change Algebra.norm F (Algebra.norm I (x : K)) =
        Algebra.norm F (Algebra.norm J (x : K))
      rw [Basic.norm_tower, Basic.norm_tower]
    rw [htower]
    exact ω.eq_one_on_normRange F J _ ⟨normUnits J K x, rfl⟩⟩
  map_one' := by
    apply NormCharacter.ext
    apply ContinuousMonoidHom.ext
    intro x
    rfl
  map_mul' ω ν := by
    apply NormCharacter.ext
    apply ContinuousMonoidHom.ext
    intro x
    rfl

@[simp]
theorem crossedNormHom_apply (ω : NormCharacter F J) (x : Iˣ) :
    (crossedNormHom F I J K ω).1 x = ω.1 (normUnits F I x) := rfl

private theorem crossedNormHom_injective
    [PrimeCyclicExtension F I] [PrimeCyclicExtension F J]
    {p : ℕ} (hp : p.Prime)
    (hI : Module.finrank F I = p) (hJ : Module.finrank F J = p)
    (hne : (normUnits F I).range ≠ (normUnits F J).range) :
    Function.Injective (crossedNormHom F I J K) := by
  apply (injective_iff_map_eq_one (crossedNormHom F I J K)).2
  intro ω hω
  have hsup : (normUnits F I).range ⊔ (normUnits F J).range = ⊤ :=
    sup_eq_top_of_distinct_prime_index hp
      ((primeNormCards F I).1.trans hI) ((primeNormCards F J).1.trans hJ) hne
  have hker : (⊤ : Subgroup Fˣ) ≤ ω.1.toMonoidHom.ker := by
    rw [← hsup]
    apply sup_le
    · rintro x ⟨y, rfl⟩
      have h := DFunLike.congr_fun (congrArg Subtype.val hω) y
      exact h
    · intro x hx
      exact ω.eq_one_on_normRange F J x hx
  apply NormCharacter.ext
  apply ContinuousMonoidHom.ext
  intro x
  exact hker (Subgroup.mem_top x)

/-- Prime cyclic edges of the two towers give an equivalence, with no
ramification or characteristic restriction. -/
def crossedNormEquivOfTowers
    [PrimeCyclicExtension F I] [PrimeCyclicExtension F J]
    [PrimeCyclicExtension I K]
    {p : ℕ} (hp : p.Prime)
    (hI : Module.finrank F I = p) (hJ : Module.finrank F J = p)
    (hIK : Module.finrank I K = p)
    (hne : (normUnits F I).range ≠ (normUnits F J).range) :
    NormCharacter F J ≃* NormCharacter I K := by
  letI := primeCyclicNormCharacter_finite I K
  apply MulEquiv.ofBijective (crossedNormHom F I J K)
  apply (Nat.bijective_iff_injective_and_card _).2
  exact ⟨crossedNormHom_injective F I J K hp hI hJ hne,
    ((primeNormCards F J).2.trans hJ).trans
      ((primeNormCards I K).2.trans hIK).symm⟩

@[simp]
theorem crossedNormEquivOfTowers_apply
    [PrimeCyclicExtension F I] [PrimeCyclicExtension F J]
    [PrimeCyclicExtension I K]
    {p : ℕ} (hp : p.Prime)
    (hI : Module.finrank F I = p) (hJ : Module.finrank F J = p)
    (hIK : Module.finrank I K = p)
    (hne : (normUnits F I).range ≠ (normUnits F J).range)
    (ω : NormCharacter F J) (x : Iˣ) :
    (crossedNormEquivOfTowers F I J K hp hI hJ hIK hne ω).1 x =
      ω.1 (normUnits F I x) := rfl

end Towers

section Diamond

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

/-- **Paper Lemma D.5.** For degree-`p` lower fields of an actual `C_p × C_p`
Galois local-field extension, distinct lower norm subgroups give the crossed
norm-character isomorphism `S(J/F) ≃* S(K/I)`. Its forward map is pullback
along `N_{I/F}`. Distinctness uses exactly the subgroups occurring in
`Ramification.normSeparation`; it also implies that the fields are distinct.
All edge structures and prime cyclicity are constructed from the diamond. -/
def crossedNorm
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (I J : IntermediateField F K)
    (hI : Module.finrank F I = p) (hJ : Module.finrank F J = p)
    (hne : Ramification.intermediateNormRange I ≠
      Ramification.intermediateNormRange J) :
    letI := Basic.intermediateFieldValuativeRel I
    letI := Basic.intermediateFieldTopology I
    letI := Basic.intermediateField_localField I
    letI := Basic.intermediateFieldValuativeRel J
    letI := Basic.intermediateFieldTopology J
    letI := Basic.intermediateField_localField J
    letI := Basic.intermediateField_lowerValuativeExtension J
    letI := Basic.intermediateField_upperValuativeExtension I
    NormCharacter F J ≃* NormCharacter I K := by
  letI := Basic.intermediateFieldValuativeRel I
  letI := Basic.intermediateFieldTopology I
  letI := Basic.intermediateField_localField I
  letI := Basic.intermediateFieldValuativeRel J
  letI := Basic.intermediateFieldTopology J
  letI := Basic.intermediateField_localField J
  letI := Basic.intermediateField_lowerValuativeExtension I
  letI := Basic.intermediateField_upperValuativeExtension I
  letI := Basic.intermediateField_lowerValuativeExtension J
  letI := Basic.intermediateField_upperValuativeExtension J
  have hdataI := Basic.intermediateField_tower_compatible hp hG I hI
  have hdataJ := Basic.intermediateField_tower_compatible hp hG J hJ
  have hIK := hdataI.2.2.2.2.2.2.2.2.2.2.1
  have hcycI := hdataI.2.2.2.2.2.2.2.2.2.2.2.1
  have hcycIK := hdataI.2.2.2.2.2.2.2.2.2.2.2.2
  have hcycJ := hdataJ.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F I hcycI
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension I K hcycIK
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F J hcycJ
  exact crossedNormEquivOfTowers F I J K hp hI hJ hIK hne

/-- The forward map of the diamond equivalence is the paper's displayed
norm pullback, evaluated on an arbitrary nonzero element of `I`. -/
@[simp]
theorem crossedNorm_apply
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (I J : IntermediateField F K)
    (hI : Module.finrank F I = p) (hJ : Module.finrank F J = p)
    (hne : Ramification.intermediateNormRange I ≠
      Ramification.intermediateNormRange J) :
    letI := Basic.intermediateFieldValuativeRel I
    letI := Basic.intermediateFieldTopology I
    letI := Basic.intermediateField_localField I
    letI := Basic.intermediateFieldValuativeRel J
    letI := Basic.intermediateFieldTopology J
    letI := Basic.intermediateField_localField J
    letI := Basic.intermediateField_lowerValuativeExtension J
    letI := Basic.intermediateField_upperValuativeExtension I
    ∀ (ω : NormCharacter F J) (x : Iˣ),
      (crossedNorm hp hG I J hI hJ hne ω).1 x = ω.1 (normUnits F I x) := by
  intros
  rfl

end Diamond

end

end LanglandsSecondMainLemma.Characters
