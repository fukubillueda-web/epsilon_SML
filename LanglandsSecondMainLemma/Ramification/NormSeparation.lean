import LanglandsSecondMainLemma.Ramification.DiamondBreaks
import LanglandsSecondMainLemma.Basic.NormTrace
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace
import LanglandsFirstMainLemma.Ramification.NormCharacters

/-!
# Ramification norm separation

This module proves Paper Proposition D.4.  Conductor separation handles the
unramified and two-break comparisons.  In the totally ramified one-break case,
the critical norm polynomial is transported through each genuine intermediate
field and its scaled trace-kernel range is separated by the two-dimensional
ramification-residue determinant.
-/

namespace LanglandsSecondMainLemma.Ramification

open LanglandsFirstMainLemma

noncomputable section

private theorem extensionResidueMap_tower
    {A B K : Type} [Field A] [Field B] [Field K]
    [ValuativeRel A] [TopologicalSpace A] [IsNonarchimedeanLocalField A]
    [ValuativeRel B] [TopologicalSpace B] [IsNonarchimedeanLocalField B]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra A B] [Algebra B K] [Algebra A K]
    [IsScalarTower A B K]
    [ValuativeExtension A B] [ValuativeExtension B K]
    [ValuativeExtension A K] (x : ResidueField A) :
    extensionResidueMap B K (extensionResidueMap A B x) =
      extensionResidueMap A K x := by
  letI : IsScalarTower
      (ringOfIntegers A) (ringOfIntegers B) (ringOfIntegers K) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext y
      change algebraMap A K (y : A) = algebraMap B K (algebraMap A B (y : A))
      rw [← IsScalarTower.algebraMap_apply A B K])
  exact IsScalarTower.algebraMap_apply (ResidueField A)
    (ResidueField B) (ResidueField K) x |>.symm

private def residueEquivOfDegreeOne
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    (hres : residueDegree F K = 1) :
    ResidueField F ≃+* ResidueField K := by
  apply RingEquiv.ofBijective (extensionResidueMap F K)
  constructor
  · exact (extensionResidueMap F K).injective
  · have hfin : Module.finrank (ResidueField F) (ResidueField K) = 1 := by
      rw [← residueDegree_eq_finrank_residueField F K, hres]
    have hdim : Module.finrank (ResidueField F) (ResidueField F) =
        Module.finrank (ResidueField F) (ResidueField K) := by
      simp [hfin]
    have hinj : Function.Injective
        (Algebra.linearMap (ResidueField F) (ResidueField K)) :=
      (algebraMap (ResidueField F) (ResidueField K)).injective
    have hsurj :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨x, by simpa only [Algebra.linearMap_apply] using hx⟩

/-- The genuine lower norm subgroup attached to an intermediate field. -/
def intermediateNormRange
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]
    (L : IntermediateField F K) : Subgroup Fˣ := by
  letI := Basic.intermediateFieldValuativeRel L
  letI := Basic.intermediateFieldTopology L
  letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
  letI : ValuativeExtension F L := Basic.intermediateField_lowerValuativeExtension L
  exact (normUnits F L).range

private theorem finrank_fixedField_line'
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p) :
    Module.finrank F (IntermediateField.fixedField H) = p := by
  let L := IntermediateField.fixedField H
  have htower := Module.finrank_mul_finrank F L K
  have hcardG : Nat.card Gal(K/F) = p ^ 2 := by
    let e := Classical.choice hG
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    have hcard : Nat.card (Multiplicative (ZMod p)) = p :=
      (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod p)
    rw [hcard, pow_two]
  rw [IntermediateField.finrank_fixedField_eq_card H, hH,
    ← IsGalois.card_aut_eq_finrank F K, hcardG] at htower
  exact Nat.mul_right_cancel hp.pos (by simpa [pow_two] using htower)

private theorem inf_eq_bot_of_distinct_lines'
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (H J : Subgroup G) (hH : Nat.card H = p)
    (hJ : Nat.card J = p) (hne : H ≠ J) : H ⊓ J = ⊥ := by
  letI : Fact (Nat.card H).Prime := ⟨hH.symm ▸ hp⟩
  rcases (J.comap H.subtype).eq_bot_or_eq_top_of_prime_card with hbot | htop
  · apply le_antisymm _ bot_le
    intro x hx
    have hx' : (⟨x, hx.1⟩ : H) ∈ J.comap H.subtype := hx.2
    rw [hbot, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  · exfalso
    apply hne
    apply Subgroup.eq_of_le_of_card_ge
    · intro x hx
      have hx' : (⟨x, hx⟩ : H) ∈ J.comap H.subtype := by
        rw [htop]
        trivial
      exact hx'
    · rw [hH, hJ]

private theorem intermediate_residueDegree_mul
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (L : IntermediateField F K) :
    letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
    letI : TopologicalSpace L := Basic.intermediateFieldTopology L
    letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
    letI : ValuativeExtension F L := Basic.intermediateField_lowerValuativeExtension L
    letI : ValuativeExtension L K := Basic.intermediateField_upperValuativeExtension L
    residueDegree F L * residueDegree L K = residueDegree F K := by
  letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
  letI : TopologicalSpace L := Basic.intermediateFieldTopology L
  letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
  letI : ValuativeExtension F L := Basic.intermediateField_lowerValuativeExtension L
  letI : ValuativeExtension L K := Basic.intermediateField_upperValuativeExtension L
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

private theorem lowerRamificationGroup_zero_eq_top_of_residueDegree_one'
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (hres : residueDegree F K = 1) :
    lowerRamificationGroup F K 0 = ⊤ := by
  letI : Module.Finite (ResidueField F) (ResidueField K) :=
    Module.Finite.of_finite
  letI : IsGalois (ResidueField F) (ResidueField K) := inferInstance
  let e := residueActionQuotientEquiv (F := F) (K := K)
  have hcard :
      Nat.card (Gal(K/F) ⧸ inertiaSubgroup (F := F) (K := K)) = 1 := by
    rw [Nat.card_congr e.toEquiv, IsGalois.card_aut_eq_finrank,
      ← residueDegree_eq_finrank_residueField, hres]
  have hindex : (inertiaSubgroup (F := F) (K := K)).index = 1 := by
    rw [(inertiaSubgroup (F := F) (K := K)).index_eq_card]
    exact hcard
  rw [← inertiaSubgroup_eq_lowerRamificationGroup_zero]
  exact Subgroup.index_eq_one.mp hindex

private theorem oneBreak_intermediateBreakPair
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (P : TotallyRamifiedDiamondBreaks (F := F) (K := K) hp hG)
    (hone : P.t = P.b) (H : Subgroup Gal(K/F))
    (hH : Nat.card H = p) :
    IntermediateBreakPair hp hG H hH P.t P.t := by
  by_cases heq : H = P.H₀
  · subst H
    simpa only [hone] using P.distinguished_breaks
  · obtain ⟨s, hsPair, _hdvd, hs, _hb⟩ := P.other_breaks H hH heq
    have hst : s = P.t := by
      rw [← hone, Nat.sub_self, Nat.zero_div, Nat.add_zero] at hs
      exact hs
    simpa only [hst] using hsPair

private theorem norm_commutes_with_restriction
    {F B K : Type} [Field F] [Field B] [Field K]
    [Algebra F B] [Algebra B K] [Algebra F K]
    [IsScalarTower F B K]
    [Module.Free B K] [Module.Finite B K]
    [IsGalois F B] [IsGalois F K] [IsGalois B K]
    [IsMulCommutative Gal(K/F)] (tau : Gal(K/F)) (x : K) :
    norm B K (tau x) = (tau.restrictNormal B) (norm B K x) := by
  apply (algebraMap B K).injective
  rw [Algebra.norm_eq_prod_automorphisms,
    AlgEquiv.restrictNormal_commutes,
    Algebra.norm_eq_prod_automorphisms, map_prod]
  apply Finset.prod_congr rfl
  intro sigma _
  have hcomm := mul_comm' tau (sigma.restrictScalars F)
  simpa using DFunLike.congr_fun hcomm.symm x

private theorem normRange_ne_of_conductor_ne
    {F E₁ E₂ : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E₁] [ValuativeRel E₁] [TopologicalSpace E₁]
    [IsNonarchimedeanLocalField E₁]
    [Field E₂] [ValuativeRel E₂] [TopologicalSpace E₂]
    [IsNonarchimedeanLocalField E₂]
    [Algebra F E₁] [ValuativeExtension F E₁]
    [Module.Free F E₁] [Module.Finite F E₁]
    [Algebra F E₂] [ValuativeExtension F E₂]
    [Module.Free F E₂] [Module.Finite F E₂]
    {p m₁ m₂ : ℕ} (hp : p.Prime)
    (hcard : Nat.card (NormCharacter F E₁) = p)
    (hfinite : Finite (NormCharacter F E₁))
    (hcond₁ : ∀ μ : NormCharacter F E₁, μ ≠ 1 →
      IsMultiplicativeConductor F μ.1 m₁)
    (hcond₂ : ∀ μ : NormCharacter F E₂, μ ≠ 1 →
      IsMultiplicativeConductor F μ.1 m₂)
    (hne : m₁ ≠ m₂) :
    (normUnits F E₁).range ≠ (normUnits F E₂).range := by
  letI : Finite (NormCharacter F E₁) := hfinite
  have hcardgt : 1 < Nat.card (NormCharacter F E₁) := by
    rw [hcard]
    exact hp.one_lt
  letI : Nontrivial (NormCharacter F E₁) :=
    Finite.one_lt_card_iff_nontrivial.mp hcardgt
  obtain ⟨μ, hμ⟩ := exists_ne (1 : NormCharacter F E₁)
  intro hrange
  let ν : NormCharacter F E₂ := by
    refine ⟨μ.1, ?_⟩
    apply ContinuousMonoidHom.ext
    intro x
    rw [normQuasiChar_apply, ContinuousQuasiChar.one_apply]
    apply μ.eq_one_on_normRange F E₁
    rw [hrange]
    exact ⟨x, rfl⟩
  have hν : ν ≠ 1 := by
    intro h
    apply hμ
    apply NormCharacter.ext
    have hcoe := congrArg (fun x : NormCharacter F E₂ => x.1) h
    exact hcoe
  apply hne
  exact (hcond₁ μ hμ).unique (hcond₂ ν hν)

private theorem unramified_normRange_ne_ramified
    {F E₀ E : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E₀] [ValuativeRel E₀] [TopologicalSpace E₀]
    [IsNonarchimedeanLocalField E₀]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E₀] [ValuativeExtension F E₀]
    [Module.Free F E₀] [Module.Finite F E₀]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Free F E] [Module.Finite F E]
    [PrimeCyclicExtension F E]
    {p t : ℕ} (hp : p.Prime)
    (hdeg₀ : Module.finrank F E₀ = p)
    (hunr : ramificationIndex F E₀ = 1)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) :
    (normUnits F E₀).range ≠ (normUnits F E).range := by
  obtain ⟨pi, hpi, hgen⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one
      F E hres
  apply normRange_ne_of_conductor_ne hp
      (m₁ := 0) (m₂ := t + 1)
      ((unramifiedNormCharacter_card F E₀ hunr).trans hdeg₀)
      (unramifiedNormCharacter_finite F E₀ hunr)
      (fun μ _ ↦ unramifiedNormCharacter_conductor F E₀ hunr μ)
      (fun μ hμ ↦ ramifiedNormCharacter_conductor F E ht hres pi hpi hgen μ hμ)
  omega

private theorem ramified_normRange_ne_of_break_ne
    {F E₁ E₂ : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E₁] [ValuativeRel E₁] [TopologicalSpace E₁]
    [IsNonarchimedeanLocalField E₁]
    [Field E₂] [ValuativeRel E₂] [TopologicalSpace E₂]
    [IsNonarchimedeanLocalField E₂]
    [Algebra F E₁] [ValuativeExtension F E₁]
    [Module.Free F E₁] [Module.Finite F E₁]
    [Algebra F E₂] [ValuativeExtension F E₂]
    [Module.Free F E₂] [Module.Finite F E₂]
    [PrimeCyclicExtension F E₁] [PrimeCyclicExtension F E₂]
    {p t₁ t₂ : ℕ} (hp : p.Prime)
    (hdeg₁ : Module.finrank F E₁ = p)
    (ht₁ : PrimeCyclicExtension.IsLowerBreak F E₁ t₁)
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F E₂ t₂)
    (hres₁ : residueDegree F E₁ = 1)
    (hres₂ : residueDegree F E₂ = 1)
    (hne : t₁ ≠ t₂) :
    (normUnits F E₁).range ≠ (normUnits F E₂).range := by
  obtain ⟨pi₁, hpi₁, hgen₁⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one
      F E₁ hres₁
  obtain ⟨pi₂, hpi₂, hgen₂⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one
      F E₂ hres₂
  apply normRange_ne_of_conductor_ne hp
      (m₁ := t₁ + 1) (m₂ := t₂ + 1)
      ((ramifiedNormCharacter_card F E₁ ht₁ hres₁ pi₁ hpi₁ hgen₁).trans hdeg₁)
      (ramifiedNormCharacter_finite F E₁ ht₁ hres₁ pi₁ hpi₁ hgen₁)
      (fun μ hμ ↦ ramifiedNormCharacter_conductor
        F E₁ ht₁ hres₁ pi₁ hpi₁ hgen₁ μ hμ)
      (fun μ hμ ↦ ramifiedNormCharacter_conductor
        F E₂ ht₂ hres₂ pi₂ hpi₂ hgen₂ μ hμ)
  omega

private theorem trace_annihilator_eq_primeField
    (k : Type) [Field k] [Finite k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (hpchar : ringChar k = p) (a : k) :
    (∀ y : k, Algebra.trace (ZMod p) k y = 0 →
      Algebra.trace (ZMod p) k (a * y) = 0) ↔
      a ∈ (⊥ : Subfield k) := by
  subst p
  let p := ringChar k
  let tr : k →ₗ[ZMod p] ZMod p := Algebra.trace (ZMod p) k
  constructor
  · intro h
    obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate k
      (a := (1 : k)) one_ne_zero
    simp only [one_mul] at hb
    let r : ZMod p := tr (a * b) / tr b
    have hfun (x : k) : tr (a * x) = r * tr x := by
      let y : k := x - algebraMap (ZMod p) k (tr x / tr b) * b
      have hy : tr y = 0 := by
        dsimp only [y]
        rw [map_sub, ← Algebra.smul_def, map_smul]
        change tr x - (tr x / tr b) * tr b = 0
        rw [div_mul_cancel₀ _ hb, sub_self]
      have hay := h y hy
      have heqfield : a * y = a * x -
          algebraMap (ZMod p) k (tr x / tr b) * (a * b) := by
        dsimp only [y]
        ring
      rw [heqfield, map_sub, ← Algebra.smul_def, map_smul] at hay
      dsimp only [r]
      apply sub_eq_zero.mp
      calc
        tr (a * x) - tr (a * b) / tr b * tr x =
            tr (a * x) - (tr x / tr b) * tr (a * b) := by ring
        _ = 0 := hay
    have ha : a = algebraMap (ZMod p) k r := by
      by_contra hne
      obtain ⟨x, hx⟩ := FiniteField.trace_to_zmod_nondegenerate k
        (a := a - algebraMap (ZMod p) k r) (sub_ne_zero.mpr hne)
      apply hx
      rw [sub_mul, map_sub, hfun, ← Algebra.smul_def, map_smul]
      change r * tr x - r * tr x = 0
      ring
    rw [ha, Subfield.mem_bot_iff_pow_eq_self k p]
    rw [← map_pow]
    congr 1
    exact ZMod.pow_card r
  · intro ha y hy
    rw [mem_bot_iff_intCast p k] at ha
    obtain ⟨n, hn⟩ := ha
    rw [← hn]
    change tr ((n : k) * y) = 0
    rw [show (n : k) = algebraMap (ZMod p) k (n : ZMod p) by simp,
      ← Algebra.smul_def, map_smul, hy]
    simp

private theorem scaledTraceKernels_ne
    (k : Type) [Field k] [Finite k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (hpchar : ringChar k = p) {lambda mu : k}
    (hlambda : lambda ≠ 0)
    (hratio : mu / lambda ∉ (⊥ : Subfield k)) :
    Set.range (fun y : (Algebra.trace (ZMod p) k).ker ↦
        lambda ^ p * (y : k)) ≠
      Set.range (fun y : (Algebra.trace (ZMod p) k).ker ↦
        mu ^ p * (y : k)) := by
  subst p
  let p := ringChar k
  intro heq
  have hannLambda : ∀ y : k,
      Algebra.trace (ZMod p) k y = 0 →
      Algebra.trace (ZMod p) k (lambda⁻¹ ^ p *
        (lambda ^ p * y)) = 0 := by
    intro y hy
    rw [← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero p hlambda), one_mul, hy]
  have hannMu : ∀ y : k,
      Algebra.trace (ZMod p) k y = 0 →
      Algebra.trace (ZMod p) k (lambda⁻¹ ^ p *
        (mu ^ p * y)) = 0 := by
    intro y hy
    have hmem : mu ^ p * y ∈ Set.range
        (fun z : (Algebra.trace (ZMod p) k).ker ↦ mu ^ p * (z : k)) :=
      ⟨⟨y, by simpa only [LinearMap.mem_ker] using hy⟩, rfl⟩
    rw [← heq] at hmem
    obtain ⟨z, hz⟩ := hmem
    rw [← hz]
    exact hannLambda (z : k) (by simpa only [LinearMap.mem_ker] using z.property)
  have hbot : lambda⁻¹ ^ p * mu ^ p ∈ (⊥ : Subfield k) :=
    (trace_annihilator_eq_primeField k p rfl
      (lambda⁻¹ ^ p * mu ^ p)).mp (by
        intro y hy
        simpa only [mul_assoc] using hannMu y hy)
  have hpow : (mu / lambda) ^ p ∈ (⊥ : Subfield k) := by
    simpa only [div_eq_mul_inv, mul_pow, mul_comm] using hbot
  apply hratio
  rw [Subfield.mem_bot_iff_pow_eq_self k p] at hpow ⊢
  apply frobenius_inj k p
  change ((mu / lambda) ^ p) ^ p = (mu / lambda) ^ p
  exact hpow

private theorem criticalNormPolynomial_range_eq_image
    (F E : Type) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Free F E] [Module.Finite F E] [PrimeCyclicExtension F E]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
    (hres : residueDegree F E = 1) (pi : ringOfIntegers E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers E)) = ⊤) :
    Set.range (criticalNormPolynomialValue F E ht htpos hres pi hpi hgen) =
      (fun q : UnitGradedPiece F t ↦
        criticalNormPositiveUnitGradedResidueAddEquiv F htpos
          (criticalNormLowerUniformizer F E pi)
          (criticalNormLowerUniformizer_isUniformizer F E hres pi hpi)
          (Additive.ofMul q)) ''
        ((criticalGradedNorm F E ht hres pi hpi hgen).range :
          Set (UnitGradedPiece F t)) := by
  let sourceCoord := criticalNormPositiveUnitGradedResidueAddEquiv E htpos
    (pi : E) hpi
  let targetCoord := criticalNormPositiveUnitGradedResidueAddEquiv F htpos
    (criticalNormLowerUniformizer F E pi)
    (criticalNormLowerUniformizer_isUniformizer F E hres pi hpi)
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    let q := criticalGradedNorm F E ht hres pi hpi hgen
      (unitGradedMk E t (criticalNormSourceUnit F E htpos pi hpi z))
    refine ⟨q, ⟨_, rfl⟩, ?_⟩
    rfl
  · rintro ⟨q, ⟨x, rfl⟩, rfl⟩
    let z : ResidueField F :=
      (criticalNormResidueEquiv F E hres).symm
        (sourceCoord (Additive.ofMul x))
    have hxclass :
        unitGradedMk E t (criticalNormSourceUnit F E htpos pi hpi z) = x := by
      have hadd : Additive.ofMul
          (unitGradedMk E t (criticalNormSourceUnit F E htpos pi hpi z)) =
          Additive.ofMul x := by
        apply sourceCoord.injective
        dsimp only [sourceCoord]
        rw [criticalNormSourceCoordinate F E htpos pi hpi]
        change criticalNormResidueEquiv F E hres z = sourceCoord (Additive.ofMul x)
        exact (criticalNormResidueEquiv F E hres).apply_symm_apply _
      exact congrArg Additive.toMul hadd
    refine ⟨z, ?_⟩
    rw [criticalNormPolynomialValue, hxclass]

private theorem criticalCoordinate_congr
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {t : ℕ} (htpos : 0 < t)
    {pi pi' : F}
    (hpi : (ValuativeRel.valuation F).IsUniformizer pi)
    (hpi' : (ValuativeRel.valuation F).IsUniformizer pi')
    (h : pi = pi') :
    criticalNormPositiveUnitGradedResidueAddEquiv F htpos pi hpi =
      criticalNormPositiveUnitGradedResidueAddEquiv F htpos pi' hpi' := by
  subst pi'
  rfl

private theorem criticalGradedNorm_ranges_ne_of_lambda_ratio
    {F E₁ E₂ : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E₁] [ValuativeRel E₁] [TopologicalSpace E₁]
    [IsNonarchimedeanLocalField E₁]
    [Field E₂] [ValuativeRel E₂] [TopologicalSpace E₂]
    [IsNonarchimedeanLocalField E₂]
    [Algebra F E₁] [ValuativeExtension F E₁]
    [Module.Free F E₁] [Module.Finite F E₁]
    [Algebra F E₂] [ValuativeExtension F E₂]
    [Module.Free F E₂] [Module.Finite F E₂]
    [PrimeCyclicExtension F E₁] [PrimeCyclicExtension F E₂]
    {p t : ℕ} [Fact p.Prime]
    (hpchar : ringChar (ResidueField F) = p)
    (hdeg₁ : Module.finrank F E₁ = p)
    (hdeg₂ : Module.finrank F E₂ = p)
    (htpos : 0 < t)
    (ht₁ : PrimeCyclicExtension.IsLowerBreak F E₁ t)
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F E₂ t)
    (hres₁ : residueDegree F E₁ = 1)
    (hres₂ : residueDegree F E₂ = 1)
    (pi₁ : ringOfIntegers E₁) (pi₂ : ringOfIntegers E₂)
    (hpi₁ : (ValuativeRel.valuation E₁).IsUniformizer (pi₁ : E₁))
    (hpi₂ : (ValuativeRel.valuation E₂).IsUniformizer (pi₂ : E₂))
    (hgen₁ : Algebra.adjoin (ringOfIntegers F)
      ({pi₁} : Set (ringOfIntegers E₁)) = ⊤)
    (hgen₂ : Algebra.adjoin (ringOfIntegers F)
      ({pi₂} : Set (ringOfIntegers E₂)) = ⊤)
    (hpiF : criticalNormLowerUniformizer F E₁ pi₁ =
      criticalNormLowerUniformizer F E₂ pi₂)
    (hratio : criticalNormRamificationLambda F E₂ ht₂ hres₂ pi₂ hpi₂ /
      criticalNormRamificationLambda F E₁ ht₁ hres₁ pi₁ hpi₁ ∉
        (⊥ : Subfield (ResidueField F))) :
    (criticalGradedNorm F E₁ ht₁ hres₁ pi₁ hpi₁ hgen₁).range ≠
      (criticalGradedNorm F E₂ ht₂ hres₂ pi₂ hpi₂ hgen₂).range := by
  letI : CharP (ResidueField F) p := hpchar ▸ inferInstance
  letI : Algebra (ZMod p) (ResidueField F) :=
    (ZMod.castHom (m := p) dvd_rfl (ResidueField F)).toAlgebra
  let lambda₁ := criticalNormRamificationLambda F E₁ ht₁ hres₁ pi₁ hpi₁
  let lambda₂ := criticalNormRamificationLambda F E₂ ht₂ hres₂ pi₂ hpi₂
  have hlambda₁ : lambda₁ ≠ 0 :=
    criticalNormRamificationLambda_ne_zero F E₁ ht₁ hres₁ pi₁ hpi₁ hgen₁
  have hlambda₂ : lambda₂ ≠ 0 :=
    criticalNormRamificationLambda_ne_zero F E₂ ht₂ hres₂ pi₂ hpi₂ hgen₂
  have hscaled := scaledTraceKernels_ne (ResidueField F) p hpchar
    hlambda₁ hratio
  intro hrange
  apply hscaled
  rw [← finiteField_scaledFrobeniusSub_range_eq_scaledTraceKer
      (ResidueField F) p hpchar lambda₁ hlambda₁,
    ← finiteField_scaledFrobeniusSub_range_eq_scaledTraceKer
      (ResidueField F) p hpchar lambda₂ hlambda₂]
  have hpoly₁ := criticalNormPolynomial_range_eq_image
    F E₁ ht₁ htpos hres₁ pi₁ hpi₁ hgen₁
  have hpoly₂ := criticalNormPolynomial_range_eq_image
    F E₂ ht₂ htpos hres₂ pi₂ hpi₂ hgen₂
  have hfun₁ : criticalNormPolynomialValue F E₁ ht₁ htpos hres₁ pi₁ hpi₁ hgen₁ =
      fun z ↦ z ^ p - lambda₁ ^ (p - 1) * z := by
    funext z
    rw [criticalNormPolynomialValue_exact_of_positiveBreak
      F E₁ ht₁ htpos hres₁ pi₁ hpi₁ hgen₁, hdeg₁]
  have hfun₂ : criticalNormPolynomialValue F E₂ ht₂ htpos hres₂ pi₂ hpi₂ hgen₂ =
      fun z ↦ z ^ p - lambda₂ ^ (p - 1) * z := by
    funext z
    rw [criticalNormPolynomialValue_exact_of_positiveBreak
      F E₂ ht₂ htpos hres₂ pi₂ hpi₂ hgen₂, hdeg₂]
  rw [hfun₁] at hpoly₁
  rw [hfun₂] at hpoly₂
  have hcoord := criticalCoordinate_congr F htpos
    (criticalNormLowerUniformizer_isUniformizer F E₁ hres₁ pi₁ hpi₁)
    (criticalNormLowerUniformizer_isUniformizer F E₂ hres₂ pi₂ hpi₂) hpiF
  calc
    _ = (fun q : UnitGradedPiece F t ↦
          criticalNormPositiveUnitGradedResidueAddEquiv F htpos
            (criticalNormLowerUniformizer F E₁ pi₁)
            (criticalNormLowerUniformizer_isUniformizer F E₁ hres₁ pi₁ hpi₁)
            (Additive.ofMul q)) ''
          ((criticalGradedNorm F E₁ ht₁ hres₁ pi₁ hpi₁ hgen₁).range :
            Set (UnitGradedPiece F t)) := hpoly₁
    _ = (fun q : UnitGradedPiece F t ↦
          criticalNormPositiveUnitGradedResidueAddEquiv F htpos
            (criticalNormLowerUniformizer F E₂ pi₂)
            (criticalNormLowerUniformizer_isUniformizer F E₂ hres₂ pi₂ hpi₂)
            (Additive.ofMul q)) ''
          ((criticalGradedNorm F E₂ ht₂ hres₂ pi₂ hpi₂ hgen₂).range :
            Set (UnitGradedPiece F t)) := by
              rw [hrange, hcoord]
    _ = _ := hpoly₂.symm

private theorem normRange_ne_of_criticalGradedNorm_range_ne
    {F E₁ E₂ : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E₁] [ValuativeRel E₁] [TopologicalSpace E₁]
    [IsNonarchimedeanLocalField E₁]
    [Field E₂] [ValuativeRel E₂] [TopologicalSpace E₂]
    [IsNonarchimedeanLocalField E₂]
    [Algebra F E₁] [ValuativeExtension F E₁]
    [Module.Free F E₁] [Module.Finite F E₁]
    [Algebra F E₂] [ValuativeExtension F E₂]
    [Module.Free F E₂] [Module.Finite F E₂]
    [PrimeCyclicExtension F E₁] [PrimeCyclicExtension F E₂]
    {t : ℕ}
    (ht₁ : PrimeCyclicExtension.IsLowerBreak F E₁ t)
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F E₂ t)
    (hres₁ : residueDegree F E₁ = 1)
    (hres₂ : residueDegree F E₂ = 1)
    (pi₁ : ringOfIntegers E₁) (pi₂ : ringOfIntegers E₂)
    (hpi₁ : (ValuativeRel.valuation E₁).IsUniformizer (pi₁ : E₁))
    (hpi₂ : (ValuativeRel.valuation E₂).IsUniformizer (pi₂ : E₂))
    (hgen₁ : Algebra.adjoin (ringOfIntegers F)
      ({pi₁} : Set (ringOfIntegers E₁)) = ⊤)
    (hgen₂ : Algebra.adjoin (ringOfIntegers F)
      ({pi₂} : Set (ringOfIntegers E₂)) = ⊤)
    (hne : (criticalGradedNorm F E₁ ht₁ hres₁ pi₁ hpi₁ hgen₁).range ≠
      (criticalGradedNorm F E₂ ht₂ hres₂ pi₂ hpi₂ hgen₂).range) :
    (normUnits F E₁).range ≠ (normUnits F E₂).range := by
  intro hrange
  apply hne
  ext q
  obtain ⟨u, rfl⟩ := unitGradedMk_surjective F t q
  change u ∈ criticalNormTargetImage F E₁ ht₁ hres₁ pi₁ hpi₁ hgen₁ ↔
    u ∈ criticalNormTargetImage F E₂ ht₂ hres₂ pi₂ hpi₂ hgen₂
  rw [← normRangeSubgroupOfCritical_eq F E₁ ht₁ hres₁ pi₁ hpi₁ hgen₁,
    ← normRangeSubgroupOfCritical_eq F E₂ ht₂ hres₂ pi₂ hpi₂ hgen₂]
  change (u : Fˣ) ∈ (normUnits F E₁).range ↔
    (u : Fˣ) ∈ (normUnits F E₂).range
  rw [hrange]

private theorem ramificationCoordinate
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {t : ℕ} (htpos : 0 < t) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (sigma : lowerRamificationGroup F K (t : ℤ)) :
    criticalNormPositiveUnitGradedResidueAddEquiv K htpos (pi : K) hpi
        (Additive.ofMul
          (ramificationUnitGradedHom F K t pi hpi hgen
            (lowerRamificationGradedMk F K (t : ℤ) sigma))) =
      lowerRamificationResidueDisplacement F K sigma (pi : K) hpi := by
  rw [ramificationUnitGradedHom_mk,
    criticalNormPositiveUnitGradedResidueAddEquiv_mk]
  simp only [lowerRamificationResidueDisplacement,
    lowerRamificationNormalizedDisplacement]
  apply (reduce_eq_reduce_iff K _ _).2
  apply (congruentAtDepth_iff_sub_mem_lattice K 1 _ _).2
  have hpi0 : (pi : K) ≠ 0 := hpi.ne_zero
  have heq :
      (((sigma : Gal(K/F)) (pi : K) / (pi : K) - 1) / (pi : K) ^ t) =
        ((sigma : Gal(K/F)) (pi : K) - (pi : K)) /
          (pi : K) ^ ((t : ℤ) + 1) := by
    rw [div_sub_one hpi0, div_div, zpow_add₀ hpi0]
    congr 1
    simp only [zpow_natCast, zpow_one]
    ac_rfl
  rw [coe_ramificationRatioUnit]
  change (((sigma : Gal(K/F)) (pi : K) / (pi : K) - 1) / (pi : K) ^ t) -
      ((sigma : Gal(K/F)) (pi : K) - (pi : K)) /
        (pi : K) ^ ((t : ℤ) + 1) ∈ lattice K 1
  rw [heq, sub_self]
  exact (lattice K 1).zero_mem

private theorem lowerRamificationResidueDisplacement_mul
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {t : ℕ} (htpos : 0 < t) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (sigma tau : lowerRamificationGroup F K (t : ℤ)) :
    lowerRamificationResidueDisplacement F K (sigma * tau) (pi : K) hpi =
      lowerRamificationResidueDisplacement F K sigma (pi : K) hpi +
        lowerRamificationResidueDisplacement F K tau (pi : K) hpi := by
  rw [← ramificationCoordinate (F := F) (K := K) htpos pi hpi hgen,
    ← ramificationCoordinate (F := F) (K := K) htpos pi hpi hgen,
    ← ramificationCoordinate (F := F) (K := K) htpos pi hpi hgen,
    map_mul, map_mul, ofMul_mul, map_add]

private theorem lowerRamificationResidueDisplacement_pow
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {t n : ℕ} (htpos : 0 < t) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (sigma : lowerRamificationGroup F K (t : ℤ)) :
    lowerRamificationResidueDisplacement F K (sigma ^ n) (pi : K) hpi =
      n • lowerRamificationResidueDisplacement F K sigma (pi : K) hpi := by
  rw [← ramificationCoordinate (F := F) (K := K) htpos pi hpi hgen,
    ← ramificationCoordinate (F := F) (K := K) htpos pi hpi hgen,
    map_pow, map_pow, ofMul_pow, map_nsmul]

private def oneBreakResidueHom
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {t : ℕ} (htop : lowerRamificationGroup F K (t : ℤ) = ⊤)
    (htpos : 0 < t) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Additive Gal(K/F) →+ ResidueField K where
  toFun sigma := lowerRamificationResidueDisplacement F K
    ⟨sigma.toMul, by rw [htop]; trivial⟩ (pi : K) hpi
  map_zero' := by
    simp only [lowerRamificationResidueDisplacement,
      lowerRamificationNormalizedDisplacement]
    change reduce K (((pi : K) - (pi : K)) /
      (pi : K) ^ ((t : ℤ) + 1)) _ =
        reduce K 0 (lattice K 0).zero_mem
    apply (reduce_eq_reduce_iff K _ _).2
    simp [CongruentAtDepth]
  map_add' sigma tau := by
    change lowerRamificationResidueDisplacement F K
      (⟨sigma.toMul * tau.toMul, _⟩ :
        lowerRamificationGroup F K (t : ℤ)) (pi : K) hpi = _
    exact lowerRamificationResidueDisplacement_mul (F := F) (K := K)
        htpos pi hpi hgen
        (⟨sigma.toMul, by rw [htop]; trivial⟩ :
          lowerRamificationGroup F K (t : ℤ))
        ⟨tau.toMul, by rw [htop]; trivial⟩

private theorem oneBreakResidueHom_injective
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {t : ℕ} (htop : lowerRamificationGroup F K (t : ℤ) = ⊤)
    (hbot : lowerRamificationGroup F K ((t : ℤ) + 1) = ⊥)
    (htpos : 0 < t) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Function.Injective (oneBreakResidueHom htop htpos pi hpi hgen) := by
  intro sigma tau heq
  have hzero : oneBreakResidueHom htop htpos pi hpi hgen (sigma - tau) = 0 := by
    rw [map_sub, heq, sub_self]
  change lowerRamificationResidueDisplacement F K
    ⟨(sigma - tau).toMul, _⟩ (pi : K) hpi = 0 at hzero
  rw [lowerRamificationResidueDisplacement_eq_zero_iff F K _ pi hpi hgen,
    hbot, Subgroup.mem_bot] at hzero
  change sigma - tau = 0 at hzero
  exact sub_eq_zero.mp hzero

private theorem criticalNormPolynomialValue_eq_of_graded_coordinate
    {B K : Type} [Field B] [Field K]
    [ValuativeRel B] [TopologicalSpace B] [IsNonarchimedeanLocalField B]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra B K] [ValuativeExtension B K]
    [Module.Free B K] [Module.Finite B K] [PrimeCyclicExtension B K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak B K t)
    (htpos : 0 < t) (hres : residueDegree B K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers B)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (u : unitFiltration K t) (v : unitFiltration B t)
    (z : ResidueField B)
    (hcoord : criticalNormPositiveUnitGradedResidueAddEquiv K htpos
        (pi : K) hpi (Additive.ofMul (unitGradedMk K t u)) =
      extensionResidueMap B K z)
    (hnorm : normBelowBreakUnitFiltrationHom B K t t
        (normMapsUnitFiltration_atBreak B K ht hres pi hpi hgen) u = v) :
    criticalNormPolynomialValue B K ht htpos hres pi hpi hgen z =
      criticalNormPositiveUnitGradedResidueAddEquiv B htpos
        (criticalNormLowerUniformizer B K pi)
        (criticalNormLowerUniformizer_isUniformizer B K hres pi hpi)
        (Additive.ofMul (unitGradedMk B t v)) := by
  have hsource : unitGradedMk K t u =
      unitGradedMk K t (criticalNormSourceUnit B K htpos pi hpi z) := by
    have hadd : Additive.ofMul (unitGradedMk K t u) =
        Additive.ofMul
          (unitGradedMk K t (criticalNormSourceUnit B K htpos pi hpi z)) := by
      apply (criticalNormPositiveUnitGradedResidueAddEquiv K htpos
        (pi : K) hpi).injective
      rw [criticalNormSourceCoordinate B K htpos pi hpi]
      exact hcoord
    exact congrArg Additive.toMul hadd
  rw [criticalNormPolynomialValue, ← hsource, criticalGradedNorm_mk, hnorm]

private theorem towerDisplacement_eq_criticalNormPolynomialValue
    {A B K : Type} [Field A] [Field B] [Field K]
    [ValuativeRel A] [TopologicalSpace A] [IsNonarchimedeanLocalField A]
    [ValuativeRel B] [TopologicalSpace B] [IsNonarchimedeanLocalField B]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra A B] [Algebra B K] [Algebra A K]
    [ValuativeExtension A B] [ValuativeExtension B K]
    [ValuativeExtension A K]
    [Module.Free A B] [Module.Finite A B]
    [Module.Free B K] [Module.Finite B K]
    [Module.Free A K] [Module.Finite A K]
    [IsGalois A B] [IsGalois A K]
    [PrimeCyclicExtension A B] [PrimeCyclicExtension B K]
    {t : ℕ} (htAKtop : lowerRamificationGroup A K (t : ℤ) = ⊤)
    (htBK : PrimeCyclicExtension.IsLowerBreak B K t)
    (htpos : 0 < t) (hresBK : residueDegree B K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgenAK : Algebra.adjoin (ringOfIntegers A)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hgenBK : Algebra.adjoin (ringOfIntegers B)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (piB : ringOfIntegers B)
    (hpiB : (ValuativeRel.valuation B).IsUniformizer (piB : B))
    (hgenAB : Algebra.adjoin (ringOfIntegers A)
      ({piB} : Set (ringOfIntegers B)) = ⊤)
    (tauK : Gal(K/A)) (tauB : Gal(B/A))
    (htauB : tauB ∈ lowerRamificationGroup A B (t : ℤ))
    (hpiBeq : (piB : B) = criticalNormLowerUniformizer B K pi)
    (hnormRatio : norm B K
        (tauK (pi : K) / (pi : K)) = tauB (piB : B) / (piB : B)) :
    let tauKt : lowerRamificationGroup A K (t : ℤ) :=
      ⟨tauK, by rw [htAKtop]; trivial⟩
    let tauBt : lowerRamificationGroup A B (t : ℤ) := ⟨tauB, htauB⟩
    let z : ResidueField B := (criticalNormResidueEquiv B K hresBK).symm
      (lowerRamificationResidueDisplacement A K tauKt (pi : K) hpi)
    criticalNormPolynomialValue B K htBK htpos hresBK pi hpi hgenBK z =
      lowerRamificationResidueDisplacement A B tauBt (piB : B) hpiB := by
  dsimp only
  let tauKt : lowerRamificationGroup A K (t : ℤ) :=
    ⟨tauK, by rw [htAKtop]; trivial⟩
  let tauBt : lowerRamificationGroup A B (t : ℤ) := ⟨tauB, htauB⟩
  let u : unitFiltration K t :=
    ⟨ramificationRatioUnit A K t tauKt (pi : K) hpi,
      ramificationRatioUnit_mem A K t tauKt (pi : K) hpi⟩
  let v : unitFiltration B t :=
    ⟨ramificationRatioUnit A B t tauBt (piB : B) hpiB,
      ramificationRatioUnit_mem A B t tauBt (piB : B) hpiB⟩
  let z : ResidueField B := (criticalNormResidueEquiv B K hresBK).symm
    (lowerRamificationResidueDisplacement A K tauKt (pi : K) hpi)
  have hcoord : criticalNormPositiveUnitGradedResidueAddEquiv K htpos
      (pi : K) hpi (Additive.ofMul (unitGradedMk K t u)) =
      extensionResidueMap B K z := by
    have hram := ramificationCoordinate (F := A) (K := K)
      htpos pi hpi hgenAK tauKt
    rw [ramificationUnitGradedHom_mk] at hram
    change criticalNormPositiveUnitGradedResidueAddEquiv K htpos
      (pi : K) hpi (Additive.ofMul (unitGradedMk K t u)) = _ at hram
    rw [hram]
    change _ = criticalNormResidueEquiv B K hresBK z
    exact (criticalNormResidueEquiv B K hresBK).apply_symm_apply _ |>.symm
  have hnorm : normBelowBreakUnitFiltrationHom B K t t
      (normMapsUnitFiltration_atBreak B K htBK hresBK pi hpi hgenBK) u = v := by
    apply Subtype.ext
    apply Units.ext
    change norm B K (tauK (pi : K) / (pi : K)) =
      tauB (piB : B) / (piB : B)
    exact hnormRatio
  have hpoly := criticalNormPolynomialValue_eq_of_graded_coordinate
    (B := B) (K := K) htBK htpos hresBK pi hpi hgenBK u v z hcoord hnorm
  rw [hpoly]
  have hcoordCongr := criticalCoordinate_congr B htpos
    (criticalNormLowerUniformizer_isUniformizer B K hresBK pi hpi)
    hpiB hpiBeq.symm
  rw [hcoordCongr]
  exact ramificationCoordinate (F := A) (K := B) htpos piB hpiB hgenAB tauBt

private theorem oneBreakPolynomialRatios_ne
    (k : Type) [Field k] [Finite k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    {c₁ c₂ : k} (hc₁ : c₁ ≠ 0)
    (hline : c₂ / c₁ ∉ (⊥ : Subfield k)) :
    let e := c₁ + c₂
    let d₁ := e ^ p - c₁ ^ (p - 1) * e
    let d₂ := e ^ p - c₂ ^ (p - 1) * e
    d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ d₂ / d₁ ∉ (⊥ : Subfield k) := by
  dsimp only
  let e := c₁ + c₂
  let d₁ := e ^ p - c₁ ^ (p - 1) * e
  let d₂ := e ^ p - c₂ ^ (p - 1) * e
  have hc₁pow : c₁ ^ p = c₁ ^ (p - 1) * c₁ := by
    calc
      c₁ ^ p = c₁ ^ (p - 1 + 1) := by
        rw [Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
      _ = c₁ ^ (p - 1) * c₁ := pow_succ _ _
  have hc₂pow : c₂ ^ p = c₂ ^ (p - 1) * c₂ := by
    calc
      c₂ ^ p = c₂ ^ (p - 1 + 1) := by
        rw [Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
      _ = c₂ ^ (p - 1) * c₂ := pow_succ _ _
  have hdet₁ : c₁ * d₁ = c₁ * c₂ ^ p - c₁ ^ p * c₂ := by
    dsimp only [d₁, e]
    rw [add_pow_char c₁ c₂ p, hc₁pow]
    ring
  have hdet₂ : c₂ * d₂ = -(c₁ * c₂ ^ p - c₁ ^ p * c₂) := by
    dsimp only [d₂, e]
    rw [add_pow_char c₁ c₂ p, hc₂pow]
    ring
  have hdetne : c₁ * c₂ ^ p - c₁ ^ p * c₂ ≠ 0 := by
    intro hzero
    apply hline
    rw [Subfield.mem_bot_iff_pow_eq_self k p]
    rw [div_pow]
    apply (div_eq_div_iff (pow_ne_zero p hc₁) hc₁).2
    linear_combination hzero
  have hd₁ : d₁ ≠ 0 := by
    intro hz
    apply hdetne
    rw [← hdet₁, hz, mul_zero]
  have hd₂ : d₂ ≠ 0 := by
    intro hz
    apply hdetne
    rw [← neg_eq_zero, ← hdet₂, hz, mul_zero]
  refine ⟨hd₁, hd₂, ?_⟩
  intro hr
  apply hline
  have hratioEq : c₂ / c₁ = -(d₁ / d₂) := by
    field_simp
    linear_combination hdet₁ + hdet₂
  rw [hratioEq]
  apply Subfield.neg_mem
  have hinv : (d₂ / d₁)⁻¹ ∈ (⊥ : Subfield k) := Subfield.inv_mem _ hr
  convert hinv using 1
  field_simp

private theorem image_ratio_not_primeField_of_distinct_lines
    {G k : Type} [Group G] [Field k] [Finite k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (phi : Additive G →+ k) (hphi : Function.Injective phi)
    (H J : Subgroup G) (sigmaH sigmaJ : G)
    (hsigmaH : sigmaH ∈ H) (hsigmaJ : sigmaJ ∈ J)
    (hinter : H ⊓ J = ⊥) (hsigmaHne : sigmaH ≠ 1)
    (hsigmaJne : sigmaJ ≠ 1) :
    phi (Additive.ofMul sigmaJ) / phi (Additive.ofMul sigmaH) ∉
      (⊥ : Subfield k) := by
  intro hratio
  rw [mem_bot_iff_intCast p k] at hratio
  obtain ⟨n, hn⟩ := hratio
  have hcH : phi (Additive.ofMul sigmaH) ≠ 0 := by
    intro hz
    have : Additive.ofMul sigmaH = 0 := hphi (hz.trans (map_zero phi).symm)
    exact hsigmaHne (congrArg Additive.toMul this)
  have hscalar : phi (Additive.ofMul sigmaJ) =
      n • phi (Additive.ofMul sigmaH) := by
    have := (div_eq_iff hcH).mp hn.symm
    simpa only [zsmul_eq_mul] using this
  have hgroup : Additive.ofMul sigmaJ = n • Additive.ofMul sigmaH := by
    apply hphi
    rw [map_zsmul]
    exact hscalar
  have hmem : sigmaJ ∈ H ⊓ J := by
    refine ⟨?_, hsigmaJ⟩
    have hpowers : sigmaH ^ n ∈ H := H.zpow_mem hsigmaH n
    have hgroup' : sigmaJ = sigmaH ^ n := congrArg Additive.toMul hgroup
    exact hgroup' ▸ hpowers
  rw [hinter, Subgroup.mem_bot] at hmem
  exact hsigmaJne hmem

private theorem ratio_not_primeField_of_prime_scalars
    {k : Type} [Field k] {a₁ a₂ lambda₁ lambda₂ d₁ d₂ : k}
    (ha₁ : a₁ ∈ (⊥ : Subfield k)) (ha₂ : a₂ ∈ (⊥ : Subfield k))
    (hd₁ : d₁ = a₁ * lambda₁) (hd₂ : d₂ = a₂ * lambda₂)
    (hratio : d₂ / d₁ ∉ (⊥ : Subfield k)) :
    lambda₂ / lambda₁ ∉ (⊥ : Subfield k) := by
  intro hlambda
  apply hratio
  rw [hd₁, hd₂, mul_div_mul_comm]
  exact Subfield.mul_mem _ (Subfield.div_mem _ ha₂ ha₁) hlambda

/-- Both edges of a line's fixed-field tower have degree `p` and are prime cyclic. -/
private theorem oneBreak_fixedFieldTowerData
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p) :
    let L := IntermediateField.fixedField H
    Module.finrank F L = p ∧ Module.finrank L K = p ∧
      PrimeCyclicExtension F L ∧ PrimeCyclicExtension L K := by
  let L := IntermediateField.fixedField H
  letI := Basic.intermediateFieldValuativeRel L
  letI := Basic.intermediateFieldTopology L
  obtain ⟨_hLocal, _hFreeLower, _hFiniteLower, _hFreeUpper, _hFiniteUpper,
      _hScalarTower, _hValLower, _hValUpper, _hTotalDegree,
      hLowerDegree, hUpperDegree, hCyclicLower, hCyclicUpper⟩ :=
    Basic.intermediateField_tower_compatible hp hG L (finrank_fixedField_line' hp hG H hH)
  exact ⟨hLowerDegree, hUpperDegree,
    PrimeCyclicExtension.ofCyclicPrimeExtension F L hCyclicLower,
    PrimeCyclicExtension.ofCyclicPrimeExtension L K hCyclicUpper⟩

/-- Total ramification and the one-break ledger supply the data for either tower. -/
private theorem oneBreak_fixedField_breakData
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1)
    (P : TotallyRamifiedDiamondBreaks (F := F) (K := K) hp hG)
    (hone : P.t = P.b) (H : Subgroup Gal(K/F)) (hH : Nat.card H = p) :
    let L := IntermediateField.fixedField H
    letI := Basic.intermediateFieldValuativeRel L
    letI := Basic.intermediateFieldTopology L
    letI := Basic.intermediateField_localField L
    letI := Basic.intermediateField_lowerValuativeExtension L
    letI := Basic.intermediateField_upperValuativeExtension L
    PrimeCyclicExtension.IsLowerBreak F L P.t ∧
      PrimeCyclicExtension.IsLowerBreak L K P.t ∧
      residueDegree F L = 1 ∧ residueDegree L K = 1 := by
  let L := IntermediateField.fixedField H
  letI := Basic.intermediateFieldValuativeRel L
  letI := Basic.intermediateFieldTopology L
  letI := Basic.intermediateField_localField L
  letI := Basic.intermediateField_lowerValuativeExtension L
  letI := Basic.intermediateField_upperValuativeExtension L
  have hpair := oneBreak_intermediateBreakPair hp hG P hone H hH
  have hresmul := intermediate_residueDegree_mul L
  rw [hres] at hresmul
  exact ⟨hpair.1, hpair.2, (mul_eq_one.mp hresmul).1, (mul_eq_one.mp hresmul).2⟩

/-- Lift the canonical upper generator to a nonidentity element of its line. -/
private theorem fixedField_generator_lift
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Module.Finite F K] [IsGalois F K]
    (H : Subgroup Gal(K/F)) [PrimeCyclicExtension (IntermediateField.fixedField H) K] :
    ∃ sigma : Gal(K/F), sigma ∈ H ∧ sigma ≠ 1 ∧
      (PrimeCyclicExtension.generator (IntermediateField.fixedField H) K).restrictScalars F =
        sigma := by
  let L := IntermediateField.fixedField H
  let sigma : H := (IntermediateField.subgroupEquivAlgEquiv H).symm
    (PrimeCyclicExtension.generator L K)
  have hmap := (IntermediateField.subgroupEquivAlgEquiv H).apply_symm_apply
    (PrimeCyclicExtension.generator L K)
  refine ⟨sigma, sigma.property, ?_, ?_⟩
  · intro hs
    apply PrimeCyclicExtension.generator_ne_one L K
    have hsub : sigma = 1 := Subtype.ext hs
    have hmapped := congrArg (IntermediateField.subgroupEquivAlgEquiv H) hsub
    rw [map_one] at hmapped
    exact hmap.symm.trans hmapped
  · apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun hmap.symm x

/-- Every lower displacement is a prime-field multiple of the canonical lambda. -/
private theorem criticalDisplacement_eq_primeScalar_mul_lambda
    {F E : Type} [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Free F E] [Module.Finite F E] [PrimeCyclicExtension F E]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
    (hres : residueDegree F E = 1) (pi : ringOfIntegers E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers E)) = ⊤)
    (tau : Gal(E/F)) (htau : tau ∈ lowerRamificationGroup F E (t : ℤ)) :
    ∃ a ∈ (⊥ : Subfield (ResidueField F)),
      lowerRamificationResidueDisplacement F E ⟨tau, htau⟩ (pi : E) hpi =
        extensionResidueMap F E
          (a * criticalNormRamificationLambda F E ht hres pi hpi) := by
  let u : ZMod (Module.finrank F E) := Multiplicative.toAdd
    ((criticalNormGaloisZModEquiv F E).symm tau)
  refine ⟨(u.val : ResidueField F), natCast_mem (⊥ : Subfield (ResidueField F)) _, ?_⟩
  have hz := criticalNormResidueDisplacement_zmod F E ht htpos pi hpi hgen u
  have haut : criticalNormGaloisZModEquiv F E (Multiplicative.ofAdd u) = tau :=
    (criticalNormGaloisZModEquiv F E).apply_symm_apply tau
  have hsub : criticalNormLowerBreakElement F E ht
      (criticalNormGaloisZModEquiv F E (Multiplicative.ofAdd u)) =
      (⟨tau, htau⟩ : lowerRamificationGroup F E (t : ℤ)) := Subtype.ext haut
  rw [hsub] at hz
  have hlambda : extensionResidueMap F E
      (criticalNormRamificationLambda F E ht hres pi hpi) =
      criticalNormUpperRamificationLambda F E ht pi hpi :=
    criticalNormResidueEquiv_ramificationLambda F E ht hres pi hpi
  rw [map_mul, hlambda]
  simpa only [map_natCast] using hz

/-- Transport the upper critical polynomial to the lower displacement in one tower.
The lower uniformizer is required to be the actual norm of the chosen upper one. -/
private theorem oneBreak_towerPolynomial_eq_primeScalar_mul_lambda
    {F B K : Type} [Field F] [Field B] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel B] [TopologicalSpace B] [IsNonarchimedeanLocalField B]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F B] [Algebra B K] [Algebra F K] [IsScalarTower F B K]
    [ValuativeExtension F B] [ValuativeExtension B K] [ValuativeExtension F K]
    [Module.Free F B] [Module.Finite F B]
    [Module.Free B K] [Module.Finite B K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    [PrimeCyclicExtension F B] [PrimeCyclicExtension B K]
    [IsMulCommutative Gal(K/F)]
    {p t : ℕ} (hdeg : Module.finrank B K = p)
    (htop : lowerRamificationGroup F K (t : ℤ) = ⊤)
    (htFB : PrimeCyclicExtension.IsLowerBreak F B t)
    (htBK : PrimeCyclicExtension.IsLowerBreak B K t) (htpos : 0 < t)
    (hresFB : residueDegree F B = 1) (hresBK : residueDegree B K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgenFK : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hgenBK : Algebra.adjoin (ringOfIntegers B) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (piB : ringOfIntegers B)
    (hpiB : (ValuativeRel.valuation B).IsUniformizer (piB : B))
    (hgenFB : Algebra.adjoin (ringOfIntegers F) ({piB} : Set (ringOfIntegers B)) = ⊤)
    (hpiBeq : (piB : B) = criticalNormLowerUniformizer B K pi)
    (sigma tau : Gal(K/F))
    (hsigma : (PrimeCyclicExtension.generator B K).restrictScalars F = sigma)
    (c e : ResidueField F)
    (hc : extensionResidueMap F K c = lowerRamificationResidueDisplacement F K
      (⟨sigma, by rw [htop]; trivial⟩ : lowerRamificationGroup F K (t : ℤ)) (pi : K) hpi)
    (he : extensionResidueMap F K e = lowerRamificationResidueDisplacement F K
      (⟨tau, by rw [htop]; trivial⟩ : lowerRamificationGroup F K (t : ℤ)) (pi : K) hpi) :
    ∃ a ∈ (⊥ : Subfield (ResidueField F)),
      e ^ p - c ^ (p - 1) * e =
        a * criticalNormRamificationLambda F B htFB hresFB piB hpiB := by
  let tauB := tau.restrictNormal B
  have htauB : tauB ∈ lowerRamificationGroup F B (t : ℤ) := by
    rw [htFB.1]
    trivial
  obtain ⟨a, ha, hlow⟩ := criticalDisplacement_eq_primeScalar_mul_lambda
    htFB htpos hresFB piB hpiB hgenFB tauB htauB
  refine ⟨a, ha, ?_⟩
  have hnormRatio : norm B K (tau (pi : K) / (pi : K)) =
      tauB (piB : B) / (piB : B) := by
    have hnormPi : norm B K (pi : K) = (piB : B) := hpiBeq.symm
    rw [div_eq_mul_inv, map_mul, Algebra.norm_inv,
      norm_commutes_with_restriction tau, hnormPi]
    rw [div_eq_mul_inv]
  have hpoly := towerDisplacement_eq_criticalNormPolynomialValue
    (A := F) (B := B) (K := K) htop htBK htpos hresBK
      pi hpi hgenFK hgenBK piB hpiB hgenFB tau tauB htauB hpiBeq hnormRatio
  let z : ResidueField B := (criticalNormResidueEquiv B K hresBK).symm
    (lowerRamificationResidueDisplacement F K
      (⟨tau, by rw [htop]; trivial⟩ : lowerRamificationGroup F K (t : ℤ)) (pi : K) hpi)
  change criticalNormPolynomialValue B K htBK htpos hresBK pi hpi hgenBK z = _ at hpoly
  have hz : extensionResidueMap B K z = extensionResidueMap F K e := by
    rw [he]
    exact (criticalNormResidueEquiv B K hresBK).apply_symm_apply _
  have hdisp : lowerRamificationResidueDisplacement F K
      (⟨sigma, by rw [htop]; trivial⟩ : lowerRamificationGroup F K (t : ℤ))
      (pi : K) hpi = criticalNormUpperRamificationLambda B K htBK pi hpi := by
    simp only [criticalNormUpperRamificationLambda, criticalNormBreakGenerator,
      lowerRamificationResidueDisplacement, lowerRamificationNormalizedDisplacement]
    apply (reduce_eq_reduce_iff K _ _).2
    apply (congruentAtDepth_iff_sub_mem_lattice K 1 _ _).2
    have hact : (PrimeCyclicExtension.generator B K) (pi : K) = sigma (pi : K) :=
      DFunLike.congr_fun hsigma (pi : K)
    rw [hact, sub_self]
    exact (lattice K 1).zero_mem
  have hlambda : extensionResidueMap B K
      (criticalNormRamificationLambda B K htBK hresBK pi hpi) =
      extensionResidueMap F K c :=
    (criticalNormResidueEquiv_ramificationLambda B K htBK hresBK pi hpi).trans
      (hc.trans hdisp).symm
  apply (extensionResidueMap F K).injective
  calc
    extensionResidueMap F K (e ^ p - c ^ (p - 1) * e) =
        extensionResidueMap B K (criticalNormPolynomialValue B K htBK htpos
          hresBK pi hpi hgenBK z) := by
      rw [criticalNormPolynomialValue_exact_of_positiveBreak, hdeg]
      simp only [map_sub, map_pow, map_mul, hz, hlambda]
    _ = extensionResidueMap B K (extensionResidueMap F B
        (a * criticalNormRamificationLambda F B htFB hresFB piB hpiB)) := by
      rw [hpoly, hlow]
    _ = _ := extensionResidueMap_tower _

/-- The two residue polynomials have ratios outside the prime field. -/
private theorem oneBreak_residuePolynomial_ratio
    {G k : Type} [Group G] [Field k] [Finite k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (phi : Additive G →+ k) (hphi : Function.Injective phi)
    (H J : Subgroup G) (sigmaH sigmaJ : G)
    (hsigmaH : sigmaH ∈ H) (hsigmaJ : sigmaJ ∈ J)
    (hinter : H ⊓ J = ⊥) (hsigmaHne : sigmaH ≠ 1) (hsigmaJne : sigmaJ ≠ 1) :
    let cH := phi (Additive.ofMul sigmaH)
    let cJ := phi (Additive.ofMul sigmaJ)
    let e := phi (Additive.ofMul (sigmaH * sigmaJ))
    (e ^ p - cJ ^ (p - 1) * e) / (e ^ p - cH ^ (p - 1) * e) ∉
      (⊥ : Subfield k) := by
  have hcH : phi (Additive.ofMul sigmaH) ≠ 0 := by
    intro hz
    have hz' : Additive.ofMul sigmaH = 0 := hphi (hz.trans (map_zero phi).symm)
    exact hsigmaHne (congrArg Additive.toMul hz')
  have hratio := image_ratio_not_primeField_of_distinct_lines
    p phi hphi H J sigmaH sigmaJ hsigmaH hsigmaJ hinter hsigmaHne hsigmaJne
  have he : phi (Additive.ofMul (sigmaH * sigmaJ)) =
      phi (Additive.ofMul sigmaH) + phi (Additive.ofMul sigmaJ) := phi.map_add _ _
  simpa only [he] using (oneBreakPolynomialRatios_ne k p hcH hratio).2.2

/-- A separated lambda ratio separates the critical images and hence the full norm ranges. -/
private theorem normRange_ne_of_lambda_ratio
    {F E₁ E₂ : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E₁] [ValuativeRel E₁] [TopologicalSpace E₁]
    [IsNonarchimedeanLocalField E₁]
    [Field E₂] [ValuativeRel E₂] [TopologicalSpace E₂]
    [IsNonarchimedeanLocalField E₂]
    [Algebra F E₁] [ValuativeExtension F E₁]
    [Module.Free F E₁] [Module.Finite F E₁]
    [Algebra F E₂] [ValuativeExtension F E₂]
    [Module.Free F E₂] [Module.Finite F E₂]
    [PrimeCyclicExtension F E₁] [PrimeCyclicExtension F E₂]
    {p t : ℕ} [Fact p.Prime]
    (hpchar : ringChar (ResidueField F) = p)
    (hdeg₁ : Module.finrank F E₁ = p)
    (hdeg₂ : Module.finrank F E₂ = p)
    (htpos : 0 < t)
    (ht₁ : PrimeCyclicExtension.IsLowerBreak F E₁ t)
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F E₂ t)
    (hres₁ : residueDegree F E₁ = 1)
    (hres₂ : residueDegree F E₂ = 1)
    (pi₁ : ringOfIntegers E₁) (pi₂ : ringOfIntegers E₂)
    (hpi₁ : (ValuativeRel.valuation E₁).IsUniformizer (pi₁ : E₁))
    (hpi₂ : (ValuativeRel.valuation E₂).IsUniformizer (pi₂ : E₂))
    (hgen₁ : Algebra.adjoin (ringOfIntegers F)
      ({pi₁} : Set (ringOfIntegers E₁)) = ⊤)
    (hgen₂ : Algebra.adjoin (ringOfIntegers F)
      ({pi₂} : Set (ringOfIntegers E₂)) = ⊤)
    (hpiF : criticalNormLowerUniformizer F E₁ pi₁ =
      criticalNormLowerUniformizer F E₂ pi₂)
    (hratio : criticalNormRamificationLambda F E₂ ht₂ hres₂ pi₂ hpi₂ /
      criticalNormRamificationLambda F E₁ ht₁ hres₁ pi₁ hpi₁ ∉
        (⊥ : Subfield (ResidueField F))) :
    (normUnits F E₁).range ≠ (normUnits F E₂).range := by
  apply normRange_ne_of_criticalGradedNorm_range_ne ht₁ ht₂ hres₁ hres₂
    pi₁ pi₂ hpi₁ hpi₂ hgen₁ hgen₂
  exact criticalGradedNorm_ranges_ne_of_lambda_ratio hpchar hdeg₁ hdeg₂ htpos
    ht₁ ht₂ hres₁ hres₂ pi₁ pi₂ hpi₁ hpi₂ hgen₁ hgen₂ hpiF hratio

private theorem oneBreak_normRanges_ne
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = p)
    (P : TotallyRamifiedDiamondBreaks (F := F) (K := K) hp hG)
    (hone : P.t = P.b)
    (H J : Subgroup Gal(K/F)) (hH : Nat.card H = p)
    (hJ : Nat.card J = p) (hne : H ≠ J) :
    intermediateNormRange (F := F) (K := K)
        (IntermediateField.fixedField H) ≠
      intermediateNormRange (F := F) (K := K)
        (IntermediateField.fixedField J) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let hGe := Classical.choice hG
  letI : IsMulCommutative Gal(K/F) := by
    apply IsMulCommutative.of_comm
    intro sigma tau
    apply hGe.injective
    simpa only [map_mul] using mul_comm (hGe sigma) (hGe tau)
  have hinter : H ⊓ J = ⊥ :=
    inf_eq_bot_of_distinct_lines' hp H J hH hJ hne
  have htop : lowerRamificationGroup F K (P.t : ℤ) = ⊤ := by
    rw [P.filtration P.t, if_pos le_rfl]
  have hbot : lowerRamificationGroup F K ((P.t : ℤ) + 1) = ⊥ := by
    rw [show (P.t : ℤ) + 1 = ((P.t + 1 : ℕ) : ℤ) by omega,
      P.filtration (P.t + 1), if_neg (by omega), ← hone,
      if_neg (by omega)]
  let LH := IntermediateField.fixedField H
  let LJ := IntermediateField.fixedField J
  letI := Basic.intermediateFieldValuativeRel LH
  letI := Basic.intermediateFieldTopology LH
  letI := Basic.intermediateFieldValuativeRel LJ
  letI := Basic.intermediateFieldTopology LJ
  obtain ⟨hdegFH, hdegHK, hcycFH, hcycHK⟩ := oneBreak_fixedFieldTowerData hp hG H hH
  obtain ⟨hdegFJ, hdegJK, hcycFJ, hcycJK⟩ := oneBreak_fixedFieldTowerData hp hG J hJ
  letI := Basic.intermediateField_localField LH
  letI := Basic.intermediateField_lowerValuativeExtension LH
  letI := Basic.intermediateField_upperValuativeExtension LH
  letI := hcycFH
  letI := hcycHK
  letI := Basic.intermediateField_localField LJ
  letI := Basic.intermediateField_lowerValuativeExtension LJ
  letI := Basic.intermediateField_upperValuativeExtension LJ
  letI := hcycFJ
  letI := hcycJK
  obtain ⟨htFH, htHK, hresFH, hresHK⟩ := oneBreak_fixedField_breakData hp hG hres P hone H hH
  obtain ⟨htFJ, htJK, hresFJ, hresJK⟩ := oneBreak_fixedField_breakData hp hG hres P hone J hJ
  obtain ⟨pi, hpi, hgenFK⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one F K hres
  have hgenHK := algebra_adjoin_uniformizer_eq_top_of_residueDegree_eq_one
    LH K hresHK pi hpi
  have hgenJK := algebra_adjoin_uniformizer_eq_top_of_residueDegree_eq_one
    LJ K hresJK pi hpi
  let piH : ringOfIntegers LH := integralNorm LH K pi
  let piJ : ringOfIntegers LJ := integralNorm LJ K pi
  have hpiH : (ValuativeRel.valuation LH).IsUniformizer (piH : LH) := by
    rw [coe_integralNorm]
    exact criticalNormLowerUniformizer_isUniformizer LH K hresHK pi hpi
  have hpiJ : (ValuativeRel.valuation LJ).IsUniformizer (piJ : LJ) := by
    rw [coe_integralNorm]
    exact criticalNormLowerUniformizer_isUniformizer LJ K hresJK pi hpi
  have hgenFH := algebra_adjoin_uniformizer_eq_top_of_residueDegree_eq_one
    F LH hresFH piH hpiH
  have hgenFJ := algebra_adjoin_uniformizer_eq_top_of_residueDegree_eq_one
    F LJ hresFJ piJ hpiJ
  obtain ⟨sigmaH, hsigmaH, hsigmaHne, hupperAutH⟩ := fixedField_generator_lift H
  obtain ⟨sigmaJ, hsigmaJ, hsigmaJne, hupperAutJ⟩ := fixedField_generator_lift J
  let tau := sigmaH * sigmaJ
  let phiK := oneBreakResidueHom htop P.t_pos pi hpi hgenFK
  let phi : Additive Gal(K/F) →+ ResidueField F :=
    (residueEquivOfDegreeOne hres).symm.toAddMonoidHom.comp phiK
  have hphi : Function.Injective phi :=
    (residueEquivOfDegreeOne hres).symm.injective.comp
      (oneBreakResidueHom_injective htop hbot P.t_pos pi hpi hgenFK)
  let cH := phi (Additive.ofMul sigmaH)
  let cJ := phi (Additive.ofMul sigmaJ)
  let e := phi (Additive.ofMul tau)
  have hpchar : ringChar (ResidueField F) = p := by
    simpa only [residueCharacteristic] using hchar
  letI : CharP (ResidueField F) p := hpchar ▸ inferInstance
  have hphiMap (g : Gal(K/F)) : extensionResidueMap F K
      (phi (Additive.ofMul g)) =
      lowerRamificationResidueDisplacement F K
        (⟨g, by rw [htop]; trivial⟩ :
          lowerRamificationGroup F K (P.t : ℤ)) (pi : K) hpi := by
    change residueEquivOfDegreeOne hres
      ((residueEquivOfDegreeOne hres).symm
        (lowerRamificationResidueDisplacement F K
          (⟨g, by rw [htop]; trivial⟩ :
            lowerRamificationGroup F K (P.t : ℤ)) (pi : K) hpi)) = _
    exact (residueEquivOfDegreeOne hres).apply_symm_apply _
  have hdRatio := oneBreak_residuePolynomial_ratio p phi hphi H J sigmaH sigmaJ
    hsigmaH hsigmaJ hinter hsigmaHne hsigmaJne
  obtain ⟨aH, haH, hdFormulaH⟩ := oneBreak_towerPolynomial_eq_primeScalar_mul_lambda
    hdegHK htop htFH htHK P.t_pos hresFH hresHK pi hpi hgenFK hgenHK
    piH hpiH hgenFH (coe_integralNorm LH K pi) sigmaH tau hupperAutH cH e
    (hphiMap sigmaH) (hphiMap tau)
  obtain ⟨aJ, haJ, hdFormulaJ⟩ := oneBreak_towerPolynomial_eq_primeScalar_mul_lambda
    hdegJK htop htFJ htJK P.t_pos hresFJ hresJK pi hpi hgenFK hgenJK
    piJ hpiJ hgenFJ (coe_integralNorm LJ K pi) sigmaJ tau hupperAutJ cJ e
    (hphiMap sigmaJ) (hphiMap tau)
  have hlambdaRatio :=
    ratio_not_primeField_of_prime_scalars haH haJ hdFormulaH hdFormulaJ hdRatio
  have hpiF : criticalNormLowerUniformizer F LH piH =
      criticalNormLowerUniformizer F LJ piJ := by
    change norm F LH (piH : LH) = norm F LJ (piJ : LJ)
    rw [coe_integralNorm, coe_integralNorm,
      Basic.norm_tower (F := F) (L := LH) (K := K),
      Basic.norm_tower (F := F) (L := LJ) (K := K)]
  exact normRange_ne_of_lambda_ratio hpchar hdegFH hdegFJ
    P.t_pos htFH htFJ hresFH hresFJ piH piJ hpiH hpiJ hgenFH hgenFJ hpiF hlambdaRatio

private theorem intermediateNormRange_ne_of_break_ne
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p tH uH tJ uJ : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1)
    (H J : Subgroup Gal(K/F)) (hH : Nat.card H = p)
    (hJ : Nat.card J = p)
    (hpairH : IntermediateBreakPair hp hG H hH tH uH)
    (hpairJ : IntermediateBreakPair hp hG J hJ tJ uJ)
    (hne : tH ≠ tJ) :
    intermediateNormRange (F := F) (K := K)
        (IntermediateField.fixedField H) ≠
      intermediateNormRange (F := F) (K := K)
        (IntermediateField.fixedField J) := by
  let LH := IntermediateField.fixedField H
  let LJ := IntermediateField.fixedField J
  letI : ValuativeRel LH := Basic.intermediateFieldValuativeRel LH
  letI : TopologicalSpace LH := Basic.intermediateFieldTopology LH
  letI : ValuativeRel LJ := Basic.intermediateFieldValuativeRel LJ
  letI : TopologicalSpace LJ := Basic.intermediateFieldTopology LJ
  have hdegFH : Module.finrank F LH = p := finrank_fixedField_line' hp hG H hH
  have hdegFJ : Module.finrank F LJ = p := finrank_fixedField_line' hp hG J hJ
  obtain ⟨hLocalH, hFreeFH, hFiniteFH, _hFreeHK, _hFiniteHK, _hScalarH,
      hValFH, hValHK, _htotalH, _hdegFH, _hdegHK, hcycFH, _hcycHK⟩ :=
    Basic.intermediateField_tower_compatible hp hG LH hdegFH
  obtain ⟨hLocalJ, hFreeFJ, hFiniteFJ, _hFreeJK, _hFiniteJK, _hScalarJ,
      hValFJ, hValJK, _htotalJ, _hdegFJ, _hdegJK, hcycFJ, _hcycJK⟩ :=
    Basic.intermediateField_tower_compatible hp hG LJ hdegFJ
  letI : IsNonarchimedeanLocalField LH := hLocalH
  letI : Module.Free F LH := hFreeFH
  letI : Module.Finite F LH := hFiniteFH
  letI : ValuativeExtension F LH := hValFH
  letI : ValuativeExtension LH K := hValHK
  letI : PrimeCyclicExtension F LH :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F LH hcycFH
  letI : IsNonarchimedeanLocalField LJ := hLocalJ
  letI : Module.Free F LJ := hFreeFJ
  letI : Module.Finite F LJ := hFiniteFJ
  letI : ValuativeExtension F LJ := hValFJ
  letI : ValuativeExtension LJ K := hValJK
  letI : PrimeCyclicExtension F LJ :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F LJ hcycFJ
  change PrimeCyclicExtension.IsLowerBreak F LH tH ∧ _ at hpairH
  change PrimeCyclicExtension.IsLowerBreak F LJ tJ ∧ _ at hpairJ
  have hresmulH := intermediate_residueDegree_mul LH
  have hresmulJ := intermediate_residueDegree_mul LJ
  rw [hres] at hresmulH hresmulJ
  have hresFH : residueDegree F LH = 1 := (mul_eq_one.mp hresmulH).1
  have hresFJ : residueDegree F LJ = 1 := (mul_eq_one.mp hresmulJ).1
  exact ramified_normRange_ne_of_break_ne hp hdegFH hpairH.1 hpairJ.1
    hresFH hresFJ hne

private theorem inertiaLine_normRanges_ne
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hI : Nat.card (inertiaSubgroup (F := F) (K := K)) = p)
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p)
    (hne : H ≠ inertiaSubgroup (F := F) (K := K)) :
    intermediateNormRange (F := F) (K := K)
        (IntermediateField.fixedField
          (inertiaSubgroup (F := F) (K := K))) ≠
      intermediateNormRange (F := F) (K := K)
        (IntermediateField.fixedField H) := by
  let I := inertiaSubgroup (F := F) (K := K)
  let U := IntermediateField.fixedField I
  let E := IntermediateField.fixedField H
  letI : ValuativeRel U := Basic.intermediateFieldValuativeRel U
  letI : TopologicalSpace U := Basic.intermediateFieldTopology U
  letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E
  letI : TopologicalSpace E := Basic.intermediateFieldTopology E
  have hdegFU : Module.finrank F U = p := finrank_fixedField_line' hp hG I hI
  have hdegFE : Module.finrank F E = p := finrank_fixedField_line' hp hG H hH
  obtain ⟨hLocalU, hFreeFU, hFiniteFU, hFreeUK, hFiniteUK, hScalarU,
      hValFU, hValUK, _htotalU, _hdegFU, _hdegUK, hcycFU, hcycUK⟩ :=
    Basic.intermediateField_tower_compatible hp hG U hdegFU
  obtain ⟨hLocalE, hFreeFE, hFiniteFE, hFreeEK, hFiniteEK, hScalarE,
      hValFE, hValEK, _htotalE, _hdegFE, hdegEK, hcycFE, hcycEK⟩ :=
    Basic.intermediateField_tower_compatible hp hG E hdegFE
  letI : IsNonarchimedeanLocalField U := hLocalU
  letI : Module.Free F U := hFreeFU
  letI : Module.Finite F U := hFiniteFU
  letI : Module.Free U K := hFreeUK
  letI : Module.Finite U K := hFiniteUK
  letI : IsScalarTower F U K := hScalarU
  letI : ValuativeExtension F U := hValFU
  letI : ValuativeExtension U K := hValUK
  letI : PrimeCyclicExtension F U :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F U hcycFU
  letI : PrimeCyclicExtension U K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension U K hcycUK
  letI : IsNonarchimedeanLocalField E := hLocalE
  letI : Module.Free F E := hFreeFE
  letI : Module.Finite F E := hFiniteFE
  letI : Module.Free E K := hFreeEK
  letI : Module.Finite E K := hFiniteEK
  letI : IsScalarTower F E K := hScalarE
  letI : ValuativeExtension F E := hValFE
  letI : ValuativeExtension E K := hValEK
  letI : PrimeCyclicExtension F E :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F E hcycFE
  letI : PrimeCyclicExtension E K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension E K hcycEK
  have hUdata := inertiaFixedField_unramified (F := F) (K := K)
  change IsGalois F U ∧ ramificationIndex F U = 1 ∧
    residueDegree F U = residueDegree F K at hUdata
  have hunrFU : ramificationIndex F U = 1 := hUdata.2.1
  have hresFU : residueDegree F U = p := by
    have hdegree := finrank_eq_ramificationIndex_mul_residueDegree F U
    rw [hdegFU, hunrFU, one_mul] at hdegree
    exact hdegree.symm
  have hresFK : residueDegree F K = p := hUdata.2.2.symm.trans hresFU
  have hinter : H ⊓ I = ⊥ :=
    inf_eq_bot_of_distinct_lines' hp H I hH hI hne
  have hcomapI : I.comap H.subtype = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hx' : (x : Gal(K/F)) ∈ H ⊓ I := ⟨x.prop, hx⟩
    rw [hinter, Subgroup.mem_bot] at hx'
    exact hx'
  have hzeroEK : lowerRamificationGroup E K 0 = ⊥ := by
    let eH := IntermediateField.subgroupEquivAlgEquiv H
    apply (Subgroup.comap_injective (f := eH.toMonoidHom) eH.surjective)
    rw [lowerRamificationGroup_fixedField H 0,
      ← inertiaSubgroup_eq_lowerRamificationGroup_zero, hcomapI]
    exact ((MonoidHom.comap_bot eH.toMonoidHom).trans
      (eH.toMonoidHom.ker_eq_bot eH.injective)).symm
  have hunrEK : ramificationIndex E K = 1 := by
    rcases unramified_or_totallyRamified E K with hunr | hresEK
    · exact hunr
    · have htopEK : lowerRamificationGroup E K 0 = ⊤ :=
        lowerRamificationGroup_zero_eq_top_of_residueDegree_one' hresEK
      exact (PrimeCyclicExtension.galoisSubgroup_top_ne_bot E K
        (htopEK.symm.trans hzeroEK)).elim
  have hresEK : residueDegree E K = p := by
    have hdegree := finrank_eq_ramificationIndex_mul_residueDegree E K
    rw [hdegEK, hunrEK, one_mul] at hdegree
    exact hdegree.symm
  have hresmulE := intermediate_residueDegree_mul E
  have hresFE : residueDegree F E = 1 := by
    rw [hresEK, hresFK] at hresmulE
    exact Nat.mul_right_cancel hp.pos (by simpa using hresmulE)
  have hzeroFE : lowerRamificationGroup F E 0 = ⊤ :=
    lowerRamificationGroup_zero_eq_top_of_residueDegree_one' hresFE
  let t := PrimeCyclicExtension.lowerBreakIndex F E hzeroFE
  have htFE : PrimeCyclicExtension.IsLowerBreak F E t :=
    PrimeCyclicExtension.lowerBreakIndex_isLowerBreak F E hzeroFE
  exact unramified_normRange_ne_ramified hp hdegFU hunrFU htFE hresFE

/-- The three norm-subgroup separation assertions of Paper Proposition D.4. -/
structure NormSeparationResult
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))) :
    Prop where
  unramified_lower :
    ∀ (_hI : Nat.card (inertiaSubgroup (F := F) (K := K)) = p)
      (H : Subgroup Gal(K/F)) (_hH : Nat.card H = p),
      H ≠ inertiaSubgroup (F := F) (K := K) →
        intermediateNormRange (F := F) (K := K)
            (IntermediateField.fixedField
              (inertiaSubgroup (F := F) (K := K))) ≠
          intermediateNormRange (F := F) (K := K)
            (IntermediateField.fixedField H)
  totally_ramified :
    ∀ _hres : residueDegree F K = 1,
      residueCharacteristic F = p →
      ∃ P : TotallyRamifiedDiamondBreaks (F := F) (K := K) hp hG,
        (∀ (H : Subgroup Gal(K/F)) (_hH : Nat.card H = p), H ≠ P.H₀ →
          intermediateNormRange (F := F) (K := K)
              (IntermediateField.fixedField P.H₀) ≠
            intermediateNormRange (F := F) (K := K)
              (IntermediateField.fixedField H)) ∧
        (P.t = P.b →
          ∀ (H J : Subgroup Gal(K/F)) (_hH : Nat.card H = p)
            (_hJ : Nat.card J = p), H ≠ J →
              intermediateNormRange (F := F) (K := K)
                  (IntermediateField.fixedField H) ≠
                intermediateNormRange (F := F) (K := K)
                  (IntermediateField.fixedField J))

/-- **Paper Proposition D.4 (separation of the norm kernels needed for SML).**

For an inertia line, its unramified fixed field has norm subgroup distinct
from every ramified lower field.  In total ramification, the distinguished
field supplied by `diamondBreaks` is separated from every other lower field;
when the two breaks coalesce, all lower norm subgroups are pairwise distinct.
The residue-characteristic equality is requested only in the totally ramified
wild branch where `diamondBreaks` uses it; the inertia-line assertion remains
valid for every prime degree. -/
theorem normSeparation
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))) :
    NormSeparationResult hp hG := by
  constructor
  · intro hI H hH hne
    exact inertiaLine_normRanges_ne hp hG hI H hH hne
  · intro hres hchar
    let D := diamondBreaks (F := F) (K := K) hp hG hchar
    let P := Classical.choice (D.1 hres)
    refine ⟨P, ?_, ?_⟩
    · intro H hH hne
      by_cases hone : P.t = P.b
      · exact oneBreak_normRanges_ne hp hG hres hchar P hone
          P.H₀ H P.card_H₀ hH hne.symm
      · obtain ⟨s, hsPair, _hdvd, _hs, hb⟩ := P.other_breaks H hH hne
        have hts : P.t ≠ s := by
          intro heq
          apply hone
          rw [← heq, Nat.sub_self, mul_zero, add_zero] at hb
          exact hb.symm
        exact intermediateNormRange_ne_of_break_ne hp hG hres
          P.H₀ H P.card_H₀ hH P.distinguished_breaks hsPair hts
    · intro hone H J hH hJ hne
      exact oneBreak_normRanges_ne hp hG hres hchar P hone H J hH hJ hne

end

end LanglandsSecondMainLemma.Ramification
