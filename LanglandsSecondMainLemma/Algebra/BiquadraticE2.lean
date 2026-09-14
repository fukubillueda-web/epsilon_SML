import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.LocalField.Lattices
import LanglandsFirstMainLemma.LocalField.MonogenicUniformizer
import LanglandsFirstMainLemma.LocalField.Valuation
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# The second symmetric function in a biquadratic extension

This file proves the characteristic-free identity of `U:e2`. For a
biquadratic extension `K/F`, a quadratic intermediate field `L`, and `C : K`,
it identifies the second elementary symmetric function of the four Galois
conjugates with

`Tr_{L/F}(N_{K/L}(C)) + N_{L/F}(Tr_{K/L}(C))`.

The proof follows the paper: the nontrivial automorphism over `L` pairs the
four conjugates, and a lift of the nontrivial automorphism of `L/F` exchanges
the two pairs. Expanding the two resulting terms partitions the six pairwise
products. In particular, the proof never divides by two and applies in
characteristic two.
-/

namespace LanglandsSecondMainLemma.Algebra

noncomputable section

open LanglandsFirstMainLemma

open scoped BigOperators

/-- A field admitting a genuinely biquadratic finite Galois extension is infinite.

Indeed, every extension of finite fields has cyclic Galois group, whereas a
Klein-four group is not cyclic. This supplies the infinitude needed by FML's
conjugate-coefficient theorem without imposing an infinitude hypothesis on
`biquadraticE2`. -/
private theorem infinite_of_genuine_biquadratic
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Finite F K] [IsKleinFour Gal(K/F)] : Infinite F := by
  rw [← not_finite_iff_infinite]
  intro hF
  letI : Finite F := hF
  letI : Finite K := Module.finite_of_finite F
  exact IsKleinFour.not_isCyclic (G := Gal(K/F)) inferInstance

/-- In a quadratic Galois extension, trace is the sum of an element and its
image under the nontrivial automorphism. -/
private theorem trace_eq_self_add_nontrivial
    {E M : Type*} [Field E] [Field M] [Algebra E M]
    [FiniteDimensional E M] [IsGalois E M]
    (sigma : Gal(M/E)) (hsigma : sigma ≠ 1)
    (hcard : Fintype.card Gal(M/E) = 2) (x : M) :
    algebraMap E M (trace E M x) = x + sigma x := by
  classical
  rw [trace_eq_sum_automorphisms]
  have huniv : ({sigma, (1 : Gal(M/E))} : Finset Gal(M/E)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simpa using hsigma), Finset.card_singleton, hcard]
  rw [← huniv]
  simp [hsigma, add_comm]

/-- In a quadratic Galois extension, norm is the product of an element and its
image under the nontrivial automorphism. -/
private theorem norm_eq_self_mul_nontrivial
    {E M : Type*} [Field E] [Field M] [Algebra E M]
    [FiniteDimensional E M] [IsGalois E M]
    (sigma : Gal(M/E)) (hsigma : sigma ≠ 1)
    (hcard : Fintype.card Gal(M/E) = 2) (x : M) :
    algebraMap E M (norm E M x) = x * sigma x := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms]
  have huniv : ({sigma, (1 : Gal(M/E))} : Finset Gal(M/E)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simpa using hsigma), Finset.card_singleton, hcard]
  rw [← huniv]
  simp [hsigma, mul_comm]

/-- The six pairwise products of a Klein-four orbit split into the two
within-pair products and the four cross-pair products. -/
private theorem biquadraticE2_map
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    [IsKleinFour Gal(K/F)]
    (sigma tau : Gal(K/F)) (hsigma : sigma ≠ 1) (htau : tau ≠ 1)
    (hne : sigma ≠ tau) (C : K) :
    algebraMap F K (elementarySymmetric F K 2 C) =
      C * sigma C + tau C * (sigma * tau) C +
        (C + sigma C) * (tau C + (sigma * tau) C) := by
  classical
  letI : Infinite F := infinite_of_genuine_biquadratic F K
  rw [algebraMap_elementarySymmetric_eq_esymm_galois, galoisConjugates]
  rw [← IsKleinFour.eq_finset_univ hsigma htau hne]
  have hst_sigma : sigma * tau ≠ sigma := by
    intro h
    apply htau
    have h' := congrArg (fun x => sigma⁻¹ * x) h
    simpa using h'
  have hst_tau : sigma * tau ≠ tau := by
    intro h
    apply hsigma
    have h' := congrArg (fun x => x * tau⁻¹) h
    simpa using h'
  have hst_one : sigma * tau ≠ 1 := by
    intro h
    apply hne
    have heq : sigma = tau⁻¹ := (mul_eq_one_iff_eq_inv).mp h
    simpa only [IsKleinFour.inv_eq_self] using heq
  have hval :
      ({sigma * tau, sigma, tau, (1 : Gal(K/F))} : Finset Gal(K/F)).val =
        sigma * tau ::ₘ sigma ::ₘ tau ::ₘ {(1 : Gal(K/F))} := by
    rw [Finset.insert_val_of_notMem (by simp [hst_sigma, hst_tau, hst_one]),
      Finset.insert_val_of_notMem (by simp [hne, hsigma]),
      Finset.insert_val_of_notMem (by simp [htau]), Finset.singleton_val]
  rw [hval]
  simp [galoisConjugate, Multiset.esymm, Multiset.powersetCard_one]
  ring

/-- **Characteristic-free biquadratic `E₂` identity (`U:e2`).**

For a genuinely biquadratic Galois extension `K/F` and any quadratic
intermediate field `L`, the second elementary symmetric function of `C` is
the lower trace of its upper norm plus the lower norm of its upper trace.
The equality is in the base field `F`. -/
theorem biquadraticE2
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    [IsKleinFour Gal(K/F)]
    (L : IntermediateField F K)
    [Algebra.IsQuadraticExtension F L]
    [Algebra.IsQuadraticExtension L K]
    (C : K) :
    elementarySymmetric F K 2 C =
      trace F L (norm L K C) + norm F L (trace L K C) := by
  classical
  letI : Algebra.IsSeparable F L :=
    Algebra.isSeparable_tower_bot_of_isSeparable F L K

  have hcardUpper : Fintype.card Gal(K/L) = 2 := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank,
      Algebra.IsQuadraticExtension.finrank_eq_two]
  obtain ⟨sigma, hsigma⟩ :=
    Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card Gal(K/L))
      (1 : Gal(K/L))

  -- Regard the nontrivial automorphism over `L` as an `F`-automorphism.
  let sigmaSub : L.fixingSubgroup :=
    (IntermediateField.fixingSubgroupEquiv L).symm sigma
  let sigmaK : Gal(K/F) := sigmaSub.1
  have hsigmaApply (x : K) : sigma x = sigmaK x := by
    have h := congrArg (fun phi : Gal(K/L) => phi x)
      ((IntermediateField.fixingSubgroupEquiv L).apply_symm_apply sigma)
    exact h.symm
  have hsigmaK : sigmaK ≠ 1 := by
    intro h
    apply hsigma
    have hsub : sigmaSub = 1 := Subtype.ext h
    have heq := congrArg (IntermediateField.fixingSubgroupEquiv L) hsub
    simpa [sigmaSub] using heq
  have hsigmaFix : AlgEquiv.restrictNormalHom L sigmaK = 1 := by
    ext x
    simp only [AlgEquiv.restrictNormalHom_apply, AlgEquiv.one_apply]
    exact sigmaSub.2 x

  have hcardLower : Fintype.card Gal(L/F) = 2 := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank,
      Algebra.IsQuadraticExtension.finrank_eq_two]
  obtain ⟨tau, htau⟩ :=
    Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card Gal(L/F))
      (1 : Gal(L/F))

  -- Normality of `K/F` lets the nontrivial automorphism of `L/F` lift to `K`.
  obtain ⟨tauK, htauRestrict⟩ :=
    AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := L) (E := K) tau
  have htauK : tauK ≠ 1 := by
    intro h
    apply htau
    rw [← htauRestrict, h, map_one]
  have hne : sigmaK ≠ tauK := by
    intro h
    apply htau
    rw [← htauRestrict, ← h, hsigmaFix]
  have htauApply (x : L) : ((tau x : L) : K) = tauK (x : K) := by
    have h := congrArg (fun phi : Gal(L/F) => ((phi x : L) : K)) htauRestrict
    simpa only [AlgEquiv.restrictNormalHom_apply] using h.symm

  have htraceUpper :
      algebraMap L K (trace L K C) = C + sigmaK C := by
    rw [trace_eq_self_add_nontrivial sigma hsigma hcardUpper, hsigmaApply]
  have hnormUpper :
      algebraMap L K (norm L K C) = C * sigmaK C := by
    rw [norm_eq_self_mul_nontrivial sigma hsigma hcardUpper, hsigmaApply]
  have htraceUpperCoe :
      ((trace L K C : L) : K) = C + sigmaK C := by
    simpa only [IntermediateField.algebraMap_apply] using htraceUpper
  have hnormUpperCoe :
      ((norm L K C : L) : K) = C * sigmaK C := by
    simpa only [IntermediateField.algebraMap_apply] using hnormUpper

  have htraceTerm :
      algebraMap F K (trace F L (norm L K C)) =
        C * sigmaK C + tauK C * (sigmaK * tauK) C := by
    rw [IsScalarTower.algebraMap_apply F L K]
    rw [trace_eq_self_add_nontrivial tau htau hcardLower]
    rw [map_add, hnormUpper, IntermediateField.algebraMap_apply, htauApply,
      hnormUpperCoe, map_mul]
    rw [← AlgEquiv.mul_apply]
    have hcomm : tauK * sigmaK = sigmaK * tauK :=
      mul_comm_of_exponent_two IsKleinFour.exponent_two tauK sigmaK
    rw [hcomm]
  have hnormTerm :
      algebraMap F K (norm F L (trace L K C)) =
        (C + sigmaK C) * (tauK C + (sigmaK * tauK) C) := by
    rw [IsScalarTower.algebraMap_apply F L K]
    rw [norm_eq_self_mul_nontrivial tau htau hcardLower]
    rw [map_mul, htraceUpper, IntermediateField.algebraMap_apply, htauApply,
      htraceUpperCoe, map_add]
    rw [← AlgEquiv.mul_apply]
    have hcomm : tauK * sigmaK = sigmaK * tauK :=
      mul_comm_of_exponent_two IsKleinFour.exponent_two tauK sigmaK
    rw [hcomm]

  apply (algebraMap F K).injective
  rw [map_add, htraceTerm, hnormTerm]
  exact biquadraticE2_map sigmaK tauK hsigmaK htauK hne C

end

end LanglandsSecondMainLemma.Algebra
