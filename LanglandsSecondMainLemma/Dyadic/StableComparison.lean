import LanglandsFirstMainLemma.Delta.FirstMainStatement
import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsFirstMainLemma.Main
import LanglandsSecondMainLemma.Dyadic.HighCovectors
import LanglandsSecondMainLemma.Characters.Conjugacy

/-!
# Exact stable comparison

Paper Theorem 10.18 (`D:UR:stable`), including the complete lower
norm-character product. The stationary covectors are constructed from FML's
stationary numerator classes; the stable-twist identity uses the canonical
local constant and retains the inverse covector as its character argument.
The corrected restriction is compared through a constructed character on
the distinguished lower field, using the proved norm-separation theorem.
-/

namespace LanglandsSecondMainLemma.Dyadic

open LanglandsFirstMainLemma
open scoped BigOperators

noncomputable section

section Covectors
variable (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- Construct a stationary covector from the released FML quotient class. -/
theorem stationaryCovector_exists
    (chi : ContinuousQuasiChar E) (psi : ContinuousAddChar E)
    (q : ℕ) (npsi : ℤ)
    (hchi : IsMultiplicativeConductor E chi q)
    (hpsi : IsAdditiveConductor E psi npsi) (hq : 1 < q) :
    ∃ b : Eˣ, IsStationaryCovectorAtDepth E chi psi q npsi
      (stationaryCovectorDepth q) b := by
  let chiData := continuousQuasiChar_toData E chi q hchi
  let psiData := continuousAddChar_toData E psi npsi hpsi
  have hr : IsLamprechtStationaryDepth chiData.conductor
      (stationaryCovectorDepth q) := by
    constructor
    · exact hq
    · dsimp [chiData, stationaryCovectorDepth]; omega
    · dsimp [chiData, stationaryCovectorDepth]; omega
  obtain ⟨Gamma⟩ := AdmissibleGamma.exists_admissible (F := E)
    (χ := chiData) (ψ := psiData)
  obtain ⟨c, hc⟩ := latticeQuotientMk_surjective E
    (sub_le_sub_left hr.int_le_conductor (chiData.conductor : ℤ))
    (stationaryNumeratorClass E chiData psiData (chiData.conductor : ℤ)
      hr Gamma Gamma.property)
  let beta := stableStationaryRepresentativeUnit E chiData psiData hr Gamma c hc
  refine ⟨beta / (Gamma : Eˣ), ?_⟩
  exact isStationaryCovectorAtDepth_of_stationaryNumeratorClass E
    chiData psiData hr Gamma Gamma.property c hc _ (by simp [beta, Units.val_div_eq_div_val])

/-- Exact stable twisting at any actual covector. The admissible denominator
is its inverse and the numerator is literally one, whose stationary class
is proved by whole-lattice linearization. -/
theorem localConstant_stableTwist_covector
    (nu theta : ContinuousQuasiChar E) (psi : ContinuousAddChar E)
    (a q : ℕ) (npsi : ℤ) (b : Eˣ)
    (hnu : IsMultiplicativeConductor E nu a)
    (hb : IsStationaryCovectorAtDepth E theta psi q npsi
      (stationaryCovectorDepth q) b)
    (hstable : 2 * a ≤ q) :
    localConstant E (nu * theta) psi =
      (nu b⁻¹ : ℂ) * localConstant E theta psi := by
  let nuData := continuousQuasiChar_toData E nu a hnu
  let thetaData := continuousQuasiChar_toData E theta q hb.multiplicativeConductor
  let psiData := continuousAddChar_toData E psi npsi hb.additiveConductor
  have hrepr : thetaData.conductor = 2 * (q / 2) + q % 2 := by
    dsimp [thetaData]; omega
  have heps : q % 2 ≤ 1 := by omega
  have hlarge : 1 < thetaData.conductor := hb.depth.conductor_gt_one
  have hlow : nuData.conductor ≤ q / 2 := by dsimp [nuData]; omega
  let hr := stableTwist_stationaryDepth E thetaData (q / 2) (q % 2)
    heps hrepr hlarge
  have hdepth : q / 2 + q % 2 = stationaryCovectorDepth q := by
    dsimp [stationaryCovectorDepth]; omega
  let Gamma : AdmissibleGamma E thetaData psiData := ⟨b⁻¹, by
    change ord E ((b⁻¹ : Eˣ) : E) = (((q : ℤ) + npsi : ℤ) : WithTop ℤ)
    rw [Units.val_inv_eq_inv_val, ord_inv, hb.order]
    norm_cast
    ring⟩
  let c : lattice E ((thetaData.conductor : ℤ) - (thetaData.conductor : ℤ)) :=
    ⟨1, by simp⟩
  have hc : latticeQuotientMk E
      (sub_le_sub_left hr.int_le_conductor (thetaData.conductor : ℤ)) c =
      stationaryNumeratorClass E thetaData psiData (thetaData.conductor : ℤ)
        hr Gamma Gamma.property := by
    apply (latticeQuotientMk_eq_stationaryNumeratorClass_iff E
      thetaData psiData (thetaData.conductor : ℤ) hr Gamma Gamma.property c).2
    intro z
    have hlin := hb.linearization ⟨(z : E), by simpa only [← hdepth] using z.property⟩
    convert hlin using 1 <;> simp [thetaData, psiData, c, Gamma, div_eq_mul_inv, mul_comm]
    congr 1
  have hfactor : stableStationaryRepresentativeUnit E thetaData psiData hr Gamma c hc = 1 := by
    apply Units.ext
    rfl
  have h := LanglandsFirstMainLemma.stableTwist E nuData thetaData psiData
    (q / 2) (q % 2) heps hrepr hlarge hlow Gamma c hc
  dsimp only at h
  rw [← localConstant_isDeltaFinite E, ← localConstant_isDeltaFinite E] at h
  rw [hfactor, div_one] at h
  exact h

end Covectors

section Edge
variable (F L : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra F L] [ValuativeExtension F L] [Module.Free F L] [Module.Finite F L]
  [PrimeCyclicExtension F L]

/-- The complete expression on a quadratic edge, with the identity norm
character and every other lower norm character included. -/
def stableComparisonFactor (theta : ContinuousQuasiChar L)
    (psi : ContinuousAddChar F) : ℂ := by
  letI := primeCyclicNormCharacter_finite F L
  letI := Fintype.ofFinite (NormCharacter F L)
  exact localConstant L theta (tracePullbackAddChar F L psi) *
    ∏ mu : NormCharacter F L, localConstant F mu.1 psi

private theorem quadratic_normCharacter_card (hdegree : Module.finrank F L = 2) :
    Nat.card (NormCharacter F L) = 2 := by
  by_cases hunr : ramificationIndex F L = 1
  · exact (unramifiedNormCharacter_card F L hunr).trans hdegree
  · let P := primeCyclicPreparation F L hunr
    exact (ramifiedNormCharacter_card F L P.ht P.hres P.piK P.hpiK P.hgen).trans hdegree

/-- Single-edge exact comparison. The ramified hypotheses are precisely
`n > delta`, `a + delta ≤ n`, and `2 * delta ≤ n`; the unramified
hypothesis is `2 * a ≤ n`. Here `delta` is the actual lower quadratic
character conductor, not an independently supplied different exponent. -/
theorem stableComparison_edge
    (hdegree : Module.finrank F L = 2)
    (chi : ContinuousQuasiChar L) (lambda : ContinuousQuasiChar F)
    (psi : ContinuousAddChar F) (omegaL : NormCharacter F L) (homega : omegaL ≠ 1)
    (a delta n : ℕ) (npsi : ℤ)
    (hchi : IsMultiplicativeConductor L chi a)
    (hdelta : IsMultiplicativeConductor F omegaL.1 delta)
    (bF : Fˣ)
    (hbF : IsStationaryCovectorAtDepth F lambda psi n npsi
      (stationaryCovectorDepth n) bF)
    (hram : ramificationIndex F L ≠ 1 →
      delta < n ∧ a + delta ≤ n ∧ 2 * delta ≤ n)
    (hunr : ramificationIndex F L = 1 → 2 * a ≤ n) :
    stableComparisonFactor F L (chi * normQuasiChar F L lambda) psi =
      ((Characters.restrictQuasiChar F L chi * omegaL.1) bF⁻¹ : ℂ) *
        localConstant F lambda psi ^ 2 := by
  have hupper : localConstant L (chi * normQuasiChar F L lambda)
      (tracePullbackAddChar F L psi) =
      (chi (Units.map (algebraMap F L) bF⁻¹) : ℂ) *
        localConstant L (normQuasiChar F L lambda) (tracePullbackAddChar F L psi) := by
    by_cases he : ramificationIndex F L = 1
    · have hbL := highCovectors_unramified F L lambda psi n npsi hdegree he bF hbF
      simpa only [map_inv] using localConstant_stableTwist_covector L
        chi (normQuasiChar F L lambda) (tracePullbackAddChar F L psi)
        a n npsi (Units.map (algebraMap F L) bF) hchi hbL (hunr he)
    · let P := primeCyclicPreparation F L he
      have he2 : ramificationIndex F L = 2 :=
        (P.ramificationIndex_eq_degree F L).trans hdegree
      have hd : differentExponent F L = delta := by
        rw [differentExponent_wildQuadratic_eq F L P.ht hdegree P.piK P.hpiK P.hgen]
        exact (ramifiedNormCharacter_conductor F L P.ht P.hres P.piK P.hpiK P.hgen
          omegaL homega).unique hdelta
      have ht : P.t + 1 = delta := by
        rw [← hd]
        exact (differentExponent_wildQuadratic_eq F L P.ht hdegree P.piK P.hpiK P.hgen).symm
      obtain ⟨hhigh, halow, hdlow⟩ := hram he
      have hpull : IsMultiplicativeConductor L (normQuasiChar F L lambda)
          (2 * n - differentExponent F L) := by
        change IsMultiplicativeConductor L lambda.compNorm _
        have h := multiplicativeConductor_compNorm_high F L P.ht P.hres
          P.piK P.hpiK P.hgen (by omega : P.t + 1 < n) hbF.multiplicativeConductor
        have hcast := highConductor_cast_eq_degree_mul_sub_different F L
          (t := P.t) (by omega : P.t + 1 < n)
        rw [hdegree] at hcast
        norm_num at hcast
        have hdepth : herbrandPsiNat P.t (Module.finrank F L) (n - 1) + 1 =
            2 * n - differentExponent F L := by
          rw [hdegree, hd]
          omega
        simpa only [hdepth] using h
      have hpsiL : IsAdditiveConductor L (tracePullbackAddChar F L psi)
          (2 * npsi + (differentExponent F L : ℤ)) := by
        change IsAdditiveConductor L psi.compTrace _
        have h := additiveConductor_compTrace F L P.piK P.hpiK P.hgen hbF.additiveConductor
        simpa only [he2, Nat.cast_ofNat] using h
      obtain ⟨bL, hbL⟩ := stationaryCovector_exists L
        (normQuasiChar F L lambda) (tracePullbackAddChar F L psi)
        (2 * n - differentExponent F L) (2 * npsi + (differentExponent F L : ℤ))
        hpull hpsiL (by rw [hd]; have := hbF.depth.conductor_gt_one; omega)
      have hclose := highCovectors F L lambda psi n npsi hdegree he2
        (by rwa [hd]) bF bL hbF hbL
      have htriv : chi (bL / Units.map (algebraMap F L) bF) = 1 :=
        hchi.trivial _ (unitFiltration_antitone L (by rw [hd]; omega) hclose)
      have hvalue : chi bL = chi (Units.map (algebraMap F L) bF) := by
        apply div_eq_one.mp
        rwa [← map_div]
      have hinv : chi bL⁻¹ = chi (Units.map (algebraMap F L) bF⁻¹) := by
        rw [map_inv, map_inv, map_inv, hvalue]
      rw [localConstant_stableTwist_covector L chi (normQuasiChar F L lambda)
        (tracePullbackAddChar F L psi) a (2 * n - differentExponent F L)
        (2 * npsi + (differentExponent F L : ℤ)) bL hchi hbL (by rw [hd]; omega), hinv]
  have hdlow : 2 * delta ≤ n := by
    by_cases he : ramificationIndex F L = 1
    · have hd0 := hdelta.unique (unramifiedNormCharacter_conductor F L he omegaL)
      omega
    · exact (hram he).2.2
  have hbase := localConstant_stableTwist_covector F omegaL.1 lambda psi
    delta n npsi bF hdelta hbF hdlow
  letI := primeCyclicNormCharacter_finite F L
  letI := Fintype.ofFinite (NormCharacter F L)
  have hcard := quadratic_normCharacter_card F L hdegree
  have hfml := firstMainLemma F L (PrimeCyclicExtension.toCyclicPrimeExtension (F := F) (K := L))
    lambda psi hbF.additiveConductor.character_ne_one
  change localConstant L (normQuasiChar F L lambda) (tracePullbackAddChar F L psi) *
      (∏ mu : NormCharacter F L, localConstant F mu.1 psi) =
      ∏ mu : NormCharacter F L, localConstant F (mu.1 * lambda) psi at hfml
  have hprod : (∏ mu : NormCharacter F L, localConstant F (mu.1 * lambda) psi) =
      localConstant F lambda psi * localConstant F (omegaL.1 * lambda) psi := by
    rw [Fintype.prod_eq_mul (1 : NormCharacter F L) omegaL homega.symm]
    · exact congrArg (fun eta : ContinuousQuasiChar F =>
        localConstant F eta psi * localConstant F (omegaL.1 * lambda) psi)
        ((congrArg (fun eta : ContinuousQuasiChar F => eta * lambda)
          (NormCharacter.coe_one (F := F) (K := L))).trans (one_mul lambda))
    · intro mu hmu
      exact (hmu.2 (((Nat.card_eq_two_iff' (1 : NormCharacter F L)).mp hcard).unique
        hmu.1 homega)).elim
  rw [hprod, hbase] at hfml
  change localConstant L (chi * normQuasiChar F L lambda) (tracePullbackAddChar F L psi) *
    (∏ mu : NormCharacter F L, localConstant F mu.1 psi) = _
  rw [hupper, mul_assoc, hfml]
  change _ = ((chi (Units.map (algebraMap F L) bF⁻¹) * omegaL.1 bF⁻¹ : ℂˣ) : ℂ) * _
  push_cast
  ring

end Edge

section Diamond
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

private theorem cyclic_card_le_two {G : Type*} [Group G] [IsCyclic G]
    (hsq : ∀ g : G, g ^ 2 = 1) : Nat.card G ≤ 2 := by
  by_contra h
  obtain ⟨g, hg⟩ := exists_pow_ne_one_of_isCyclic (G := G) (by decide : 2 ≠ 0)
    (by omega : 2 < Nat.card G)
  exact hg (hsq g)

section GaloisAlgebra
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

private theorem biquadratic_card
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))) :
    Nat.card Gal(K/F) = 4 := by
  rw [Nat.card_congr hG.some.toEquiv, Nat.card_prod]
  norm_num [Nat.card_congr Multiplicative.toAdd]

private theorem biquadratic_sq
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))) (g : Gal(K/F)) :
    g ^ 2 = 1 := by
  apply hG.some.injective
  rw [map_pow, map_one]
  apply Prod.ext
  · simpa [Nat.card_congr Multiplicative.toAdd] using
      (pow_card_eq_one' (x := (hG.some g).1))
  · simpa [Nat.card_congr Multiplicative.toAdd] using
      (pow_card_eq_one' (x := (hG.some g).2))

end GaloisAlgebra

/-- There is a lower field whose norm subgroup is separated from every
other lower field. This uses the proved ramification separation theorem,
including its residue-characteristic hypothesis in total ramification. -/
private theorem separating_lower_field
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))) :
    ∃ B : IntermediateField F K, Module.finrank F B = 2 ∧
      ∀ L : IntermediateField F K, Module.finrank F L = 2 → L ≠ B →
        Ramification.intermediateNormRange B ≠ Ramification.intermediateNormRange L := by
  let G := Gal(K/F)
  have hcard := biquadratic_card hG
  have hline : ∃ H : Subgroup G, Nat.card H = 2 ∧
      ∀ J : Subgroup G, Nat.card J = 2 → J ≠ H →
        Ramification.intermediateNormRange (IntermediateField.fixedField H) ≠
          Ramification.intermediateNormRange (IntermediateField.fixedField J) := by
    let T := Ramification.inertiaSubgroup (F := F) (K := K)
    letI : IsCyclic (G ⧸ T) := Ramification.residueActionQuotient_cyclic
    have hquot : Nat.card (G ⧸ T) ≤ 2 := by
      apply cyclic_card_le_two
      intro g
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      change QuotientGroup.mk (g ^ 2) = QuotientGroup.mk (1 : G)
      rw [biquadratic_sq hG]
    have hrescard : Nat.card (G ⧸ T) = residueDegree F K := by
      rw [Nat.card_congr (Ramification.residueActionQuotientEquiv
        (F := F) (K := K)).toEquiv, IsGalois.card_aut_eq_finrank,
        ← residueDegree_eq_finrank_residueField]
    have hsep := Ramification.normSeparation Nat.prime_two hG
    by_cases hres : residueDegree F K = 1
    · have hzero : lowerRamificationGroup F K 0 = ⊤ := by
        rw [← Ramification.inertiaSubgroup_eq_lowerRamificationGroup_zero]
        apply Subgroup.index_eq_one.mp
        rw [Subgroup.index_eq_card, hrescard, hres]
      have hchar : residueCharacteristic F = 2 := by
        let W := lowerRamificationGroup F K 1
        have hW : W ≠ ⊥ := by
          intro hbot
          letI : IsCyclic (LowerRamificationGraded F K 0) :=
            (Ramification.tameInertia_cyclic (F := F) (K := K)).1
          have htame : Nat.card (LowerRamificationGraded F K 0) ≤ 2 := by
            apply cyclic_card_le_two
            intro x
            obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
            have hg : g ^ 2 = 1 := Subtype.ext (biquadratic_sq hG g.val)
            change QuotientGroup.mk (g ^ 2) =
              QuotientGroup.mk (1 : lowerRamificationGroup F K 0)
            rw [hg]
          have hinside : lowerRamificationGroupInside F K (show (0 : ℤ) ≤ 1 by omega) = ⊥ := by
            ext g
            simp only [mem_lowerRamificationGroupInside, show lowerRamificationGroup F K 1 = ⊥ from hbot,
              Subgroup.mem_bot, Subtype.ext_iff, OneMemClass.coe_one]
          change Nat.card (lowerRamificationGroup F K 0 ⧸
            lowerRamificationGroupInside F K (show (0 : ℤ) ≤ 1 by omega)) ≤ 2 at htame
          rw [lowerRamificationQuotient_natCard F K, hinside, Subgroup.index_bot,
            hzero, Subgroup.card_top, hcard] at htame
          omega
        obtain ⟨g, hg, hgone⟩ := W.bot_or_exists_ne_one.resolve_left hW
        letI : Fact (residueCharacteristic F).Prime := ⟨residueCharacteristic_prime F⟩
        have hdiv := (Ramification.wildInertia_isPGroup (F := F) (K := K)).dvd_orderOf
          (g := (⟨g, hg⟩ : W)) (by simpa using hgone)
        have hord : orderOf (⟨g, hg⟩ : W) ∣ 2 :=
          orderOf_dvd_of_pow_eq_one (Subtype.ext (biquadratic_sq hG g))
        exact ((Nat.dvd_prime Nat.prime_two).mp (hdiv.trans hord)).resolve_left
          (residueCharacteristic_prime F).ne_one
      obtain ⟨P, hP, _⟩ := hsep.totally_ramified hres hchar
      exact ⟨P.H₀, P.card_H₀, fun J hJ hne => hP J hJ hne⟩
    · have hf : residueDegree F K = 2 := by
        have := residueDegree_pos F K
        omega
      have hT : Nat.card T = 2 := by
        have h := T.card_mul_index
        rw [Subgroup.index_eq_card, hrescard, hf, hcard] at h
        omega
      exact ⟨T, hT, fun J hJ hne => hsep.unramified_lower hT J hJ hne⟩
  obtain ⟨H, hH, hsep⟩ := hline
  have hB : Module.finrank F (IntermediateField.fixedField H) = 2 := by
    have h := Module.finrank_mul_finrank F (IntermediateField.fixedField H) K
    rw [IntermediateField.finrank_fixedField_eq_card H, hH,
      ← IsGalois.card_aut_eq_finrank F K, hcard] at h
    omega
  refine ⟨IntermediateField.fixedField H, hB, ?_⟩
  intro L hL hne
  have hfix : Nat.card L.fixingSubgroup = 2 := by
    have h := Module.finrank_mul_finrank F L K
    rw [← IsGalois.card_aut_eq_finrank F K, hcard, hL,
      ← IsGalois.fixedField_fixingSubgroup L,
      IntermediateField.finrank_fixedField_eq_card] at h
    omega
  have hne' : L.fixingSubgroup ≠ H := by
    intro h
    apply hne
    rw [← IsGalois.fixedField_fixingSubgroup L, h]
  simpa only [IsGalois.fixedField_fixingSubgroup] using hsep L.fixingSubgroup hfix hne'

/-- The corrected restriction for any distinct biquadratic pair. A descent
to the separating lower field supplies the bridge when the original pair
is not one of the distinguished norm-separation comparisons. -/
private theorem corrected_restriction
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (I J : IntermediateField F K)
    (hI : Module.finrank F I = 2) (hJ : Module.finrank F J = 2) (hne : I ≠ J) :
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
    ∀ (chiI : ContinuousQuasiChar I) (chiJ : ContinuousQuasiChar J)
      (Theta : ContinuousQuasiChar K),
      normQuasiChar I K chiI = Theta → normQuasiChar J K chiJ = Theta →
      (¬ ∃ chi : ContinuousQuasiChar F, normQuasiChar F K chi = Theta) →
      Characters.restrictQuasiChar F I chiI *
          Characters.intermediateNormCharacterProduct Nat.prime_two hG I hI =
        Characters.restrictQuasiChar F J chiJ *
          Characters.intermediateNormCharacterProduct Nat.prime_two hG J hJ ∧
      ∃ (omegaI : NormCharacter F I) (omegaJ : NormCharacter F J),
        omegaI ≠ 1 ∧ omegaJ ≠ 1 ∧
        Characters.intermediateNormCharacterProduct Nat.prime_two hG I hI = omegaI.1 ∧
        Characters.intermediateNormCharacterProduct Nat.prime_two hG J hJ = omegaJ.1 := by
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
  intro chiI chiJ Theta hcI hcJ hprimitive
  obtain ⟨B, hB, hsep⟩ := separating_lower_field hG
  by_cases hIB : I = B
  · have hnorm := hsep J hJ (by simpa only [← hIB] using hne.symm)
    rw [← hIB] at hnorm
    obtain ⟨_, _, hD, _, hquadratic⟩ := Characters.conjugacy Nat.prime_two hG
      I J hI hJ hnorm chiI chiJ Theta hcI hcJ hprimitive
    exact ⟨hD, hquadratic rfl⟩
  by_cases hJB : J = B
  · have hnorm := hsep I hI (by simpa only [← hJB] using hne)
    rw [← hJB] at hnorm
    obtain ⟨_, _, hD, _, hquadratic⟩ := Characters.conjugacy Nat.prime_two hG
      I J hI hJ hnorm.symm chiI chiJ Theta hcI hcJ hprimitive
    exact ⟨hD, hquadratic rfl⟩
  letI := Basic.intermediateFieldValuativeRel B
  letI := Basic.intermediateFieldTopology B
  letI := Basic.intermediateField_localField B
  letI := Basic.intermediateField_lowerValuativeExtension B
  letI := Basic.intermediateField_upperValuativeExtension B
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension B K
    (Basic.intermediateField_tower_compatible Nat.prime_two hG B hB).2.2.2.2.2.2.2.2.2.2.2.2
  have hinf : I ⊓ J = ⊥ := by
    have hdiv : Module.finrank F ↥(I ⊓ J) ∣ 2 := by
      rw [← hI]
      exact IntermediateField.finrank_dvd_of_le_right inf_le_left
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
    · exact IntermediateField.finrank_eq_one_iff.mp h
    · have heq : I ⊓ J = I :=
        IntermediateField.eq_of_le_of_finrank_eq inf_le_left (h.trans hI.symm)
      have hle : I ≤ J := by rw [← heq]; exact inf_le_right
      exact (hne (IntermediateField.eq_of_le_of_finrank_eq hle (hI.trans hJ.symm))).elim
  have hsup : I.fixingSubgroup ⊔ J.fixingSubgroup = ⊤ := by
    have h := (IsGalois.intermediateFieldEquivSubgroup (F := F) (E := K)).map_inf I J
    change (I ⊓ J).fixingSubgroup = I.fixingSubgroup ⊔ J.fixingSubgroup at h
    rw [hinf, IntermediateField.fixingSubgroup_bot] at h
    exact h.symm
  letI : IsMulCommutative Gal(K/F) := IsMulCommutative.of_comm fun s t =>
    hG.some.injective (by simpa only [map_mul] using mul_comm (hG.some s) (hG.some t))
  have hinvariant : ∀ (s : Gal(K/F)) (x : Kˣ),
      Theta (Units.map s.toMonoidHom x) = Theta x := by
    intro s x
    have hs : s ∈ I.fixingSubgroup ⊔ J.fixingSubgroup := hsup ▸ Subgroup.mem_top s
    obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hs
    have hfixedI (y : Kˣ) : Theta (Units.map u.toMonoidHom y) = Theta y := by
      rw [← hcI]
      apply congrArg chiI
      apply Units.ext
      exact Algebra.norm_eq_of_algEquiv (I.fixingSubgroupEquiv ⟨u, hu⟩) (y : K)
    have hfixedJ (y : Kˣ) : Theta (Units.map v.toMonoidHom y) = Theta y := by
      rw [← hcJ]
      apply congrArg chiJ
      apply Units.ext
      exact Algebra.norm_eq_of_algEquiv (J.fixingSubgroupEquiv ⟨v, hv⟩) (y : K)
    change Theta (Units.map u.toMonoidHom (Units.map v.toMonoidHom x)) = Theta x
    rw [hfixedI, hfixedJ]
  obtain ⟨chiB, hcB⟩ := Local.invariantCharacter_descends B K Theta
    (fun s x => hinvariant (s.restrictScalars F) x)
  obtain ⟨_, _, hDI, _, hquadI⟩ := Characters.conjugacy Nat.prime_two hG
    I B hI hB (hsep I hI hIB).symm chiI chiB Theta hcI hcB hprimitive
  obtain ⟨_, _, hDJ, _, hquadJ⟩ := Characters.conjugacy Nat.prime_two hG
    J B hJ hB (hsep J hJ hJB).symm chiJ chiB Theta hcJ hcB hprimitive
  obtain ⟨omegaI, _, homegaI, _, hprodI, _⟩ := hquadI rfl
  obtain ⟨omegaJ, _, homegaJ, _, hprodJ, _⟩ := hquadJ rfl
  exact ⟨hDI.trans hDJ.symm, omegaI, omegaJ, homegaI, homegaJ, hprodI, hprodJ⟩

/-- Paper Theorem 10.18 (`D:UR:stable`). For an actual primitive compatible
pair on distinct lower fields, every common twist in the stated
sufficient high range has the same complete induction expression:
`D(bF⁻¹) * localConstant F lambda psi ^ 2`.

Here `D` is the common restriction corrected by the complete lower
norm-character product. The lower quadratic character conductors are
specified by exact conductor predicates, so all three ramified inequalities
and the unramified inequality are imposed at their original depths.
The covector is constructed, not assumed. The actual norm pullbacks and
all lower local-constant factors are retained. No restriction on field
characteristic, residue characteristic, or unitarity is imposed. -/
theorem stableComparison
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (I J : IntermediateField F K)
    (hI : Module.finrank F I = 2) (hJ : Module.finrank F J = 2)
    (hne : I ≠ J) :
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
    letI := PrimeCyclicExtension.ofCyclicPrimeExtension F I
      (Basic.intermediateField_tower_compatible Nat.prime_two hG I hI).2.2.2.2.2.2.2.2.2.2.2.1
    letI := PrimeCyclicExtension.ofCyclicPrimeExtension F J
      (Basic.intermediateField_tower_compatible Nat.prime_two hG J hJ).2.2.2.2.2.2.2.2.2.2.2.1
    ∀ (chiI : ContinuousQuasiChar I) (chiJ : ContinuousQuasiChar J)
      (Theta : ContinuousQuasiChar K),
      normQuasiChar I K chiI = Theta → normQuasiChar J K chiJ = Theta →
      (¬ ∃ chi : ContinuousQuasiChar F, normQuasiChar F K chi = Theta) →
      ∀ (lambda : ContinuousQuasiChar F) (psi : ContinuousAddChar F)
        (aI aJ deltaI deltaJ n : ℕ) (npsi : ℤ),
        IsMultiplicativeConductor I chiI aI → IsMultiplicativeConductor J chiJ aJ →
        IsMultiplicativeConductor F
          (Characters.intermediateNormCharacterProduct Nat.prime_two hG I hI) deltaI →
        IsMultiplicativeConductor F
          (Characters.intermediateNormCharacterProduct Nat.prime_two hG J hJ) deltaJ →
        IsMultiplicativeConductor F lambda n → IsAdditiveConductor F psi npsi →
        2 ≤ n →
        (ramificationIndex F I ≠ 1 → deltaI < n ∧ aI + deltaI ≤ n ∧ 2 * deltaI ≤ n) →
        (ramificationIndex F J ≠ 1 → deltaJ < n ∧ aJ + deltaJ ≤ n ∧ 2 * deltaJ ≤ n) →
        (ramificationIndex F I = 1 → 2 * aI ≤ n) →
        (ramificationIndex F J = 1 → 2 * aJ ≤ n) →
        ∃ bF : Fˣ,
          IsStationaryCovectorAtDepth F lambda psi n npsi (stationaryCovectorDepth n) bF ∧
          stableComparisonFactor F I (chiI * normQuasiChar F I lambda) psi =
            ((Characters.restrictQuasiChar F I chiI *
              Characters.intermediateNormCharacterProduct Nat.prime_two hG I hI) bF⁻¹ : ℂ) *
              localConstant F lambda psi ^ 2 ∧
          stableComparisonFactor F J (chiJ * normQuasiChar F J lambda) psi =
            ((Characters.restrictQuasiChar F I chiI *
              Characters.intermediateNormCharacterProduct Nat.prime_two hG I hI) bF⁻¹ : ℂ) *
              localConstant F lambda psi ^ 2 ∧
          stableComparisonFactor F I (chiI * normQuasiChar F I lambda) psi =
            stableComparisonFactor F J (chiJ * normQuasiChar F J lambda) psi := by
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
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F I
    (Basic.intermediateField_tower_compatible Nat.prime_two hG I hI).2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F J
    (Basic.intermediateField_tower_compatible Nat.prime_two hG J hJ).2.2.2.2.2.2.2.2.2.2.2.1
  intro chiI chiJ Theta hcI hcJ hprimitive lambda psi aI aJ deltaI deltaJ n npsi
    hchiI hchiJ hdI hdJ hlambda hpsi hn hramI hramJ hunrI hunrJ
  obtain ⟨hD, hquadratic⟩ := corrected_restriction hG
    I J hI hJ hne chiI chiJ Theta hcI hcJ hprimitive
  obtain ⟨omegaI, omegaJ, homegaI, homegaJ, hprodI, hprodJ⟩ := hquadratic
  obtain ⟨bF, hbF⟩ := stationaryCovector_exists F lambda psi n npsi hlambda hpsi (by omega)
  have hstableI := stableComparison_edge F I hI chiI lambda psi omegaI homegaI
    aI deltaI n npsi hchiI (by rwa [← hprodI]) bF hbF hramI hunrI
  have hstableJ := stableComparison_edge F J hJ chiJ lambda psi omegaJ homegaJ
    aJ deltaJ n npsi hchiJ (by rwa [← hprodJ]) bF hbF hramJ hunrJ
  rw [← hprodI] at hstableI
  rw [← hprodJ, ← hD] at hstableJ
  exact ⟨bF, hbF, hstableI, hstableJ, hstableI.trans hstableJ.symm⟩

end Diamond

end
end LanglandsSecondMainLemma.Dyadic
