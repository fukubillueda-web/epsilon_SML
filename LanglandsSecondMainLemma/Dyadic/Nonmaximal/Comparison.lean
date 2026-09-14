import LanglandsFirstMainLemma.Delta.FirstMainStatement
import LanglandsFirstMainLemma.Main
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.UnequalBreaks
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.EqualBreaks
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.Higher
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.Twist
import LanglandsSecondMainLemma.Characters.QuadraticProduct
import LanglandsSecondMainLemma.Characters.InducingChoice

/-!
# Nonmaximal dyadic comparison

Paper `D:NM:main` and the completion at lines 8089–8102.

The generator construction preceding `D:NM:xy` and the conductor assembly
construct every origin, normalizing coefficient, core and stationary side.
The final `comparison` obtains the lower norm characters from
`Characters.quadraticProduct` and the upper breaks from the diamond ledger.
Both equal and unequal lower breaks and arbitrary nonunitary continuous
quasi-characters are retained. Total ramification supplies all six edge
residue degrees, and the finite order of two excludes characteristic two.
-/

namespace LanglandsSecondMainLemma.Dyadic.Nonmaximal

open LanglandsFirstMainLemma
noncomputable section

open private trace_eq_self_add_nontrivial norm_eq_self_mul_nontrivial from
  LanglandsSecondMainLemma.Dyadic.Nonmaximal.Origin
open private adjoin_affine_eq_top from LanglandsSecondMainLemma.Dyadic.Nonmaximal.Alignment
open private field_adjoin_eq_top_of_integer_adjoin_eq_top from
  LanglandsFirstMainLemma.Ramification.TraceIdeals

/-- The actual generator before `D:NM:xy`, obtained by dividing a
uniformizer by its nonzero trace. The coefficient has integer order `1-2a`. -/
theorem comparison_generator
    (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
    [Algebra.IsQuadraticExtension F E] [PrimeCyclicExtension F E]
    {a : ℕ} (ha : 1 ≤ a)
    (ht : PrimeCyclicExtension.IsLowerBreak F E (2 * a - 1))
    (hres : residueDegree F E = 1) :
    ∃ (x : E) (f : F), x ^ 2 + x = algebraMap F E f ∧
      Algebra.adjoin F ({x} : Set E) = ⊤ ∧
      ord F f = ((1 - 2 * (a : ℤ) : ℤ) : WithTop ℤ) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have hdeg := Algebra.IsQuadraticExtension.finrank_eq_two F E
  have hram : ramificationIndex F E = 2 := by
    simpa [hres, hdeg] using (finrank_eq_ramificationIndex_mul_residueDegree F E).symm
  have hdiff : differentExponent F E = 2 * a := by
    rw [differentExponent_eq F E ht pi hpi hgen, hdeg]
    omega
  have htr : ord F (trace F E (pi : E)) = (a : WithTop ℤ) :=
    (quadratic_trace_shell_iff F E pi hpi hgen (by norm_num) hram hdeg
      (by rw [hdiff]; push_cast; ring) (pi : E)
      (by simp [mem_lattice, ord_uniformizer E hpi])).2 (ord_uniformizer E hpi)
  let c := trace F E (pi : E)
  have hc : c ≠ 0 := (ord_ne_top_iff F).mp (by rw [htr]; exact WithTop.coe_ne_top)
  let x : E := -(pi : E) / algebraMap F E c
  let f : F := -norm F E (pi : E) / c ^ 2
  have hcE : algebraMap F E c ≠ 0 := (map_ne_zero _).mpr hc
  let sigma := PrimeCyclicExtension.generator F E
  have hsigma := PrimeCyclicExtension.generator_ne_one F E
  have hcard : Fintype.card Gal(E/F) = 2 := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, hdeg]
  have htrace := trace_eq_self_add_nontrivial sigma hsigma hcard (pi : E)
  have hnorm := norm_eq_self_mul_nontrivial sigma hsigma hcard (pi : E)
  refine ⟨x, f, ?_, ?_, ?_⟩
  · dsimp only [x, f]
    rw [map_div₀, map_neg, map_pow, hnorm]
    field_simp
    change algebraMap F E c = _ at htrace
    linear_combination -(pi : E) * htrace
  · apply adjoin_affine_eq_top F (pi : E) x (-c⁻¹) 0 (neg_ne_zero.mpr (inv_ne_zero hc))
    · simp [x, div_eq_mul_inv, mul_comm]
    · exact field_adjoin_eq_top_of_integer_adjoin_eq_top F E pi hgen
  · simp only [f, ord_div, ord_neg, ord_norm, hres, one_nsmul,
      ord_uniformizer E hpi, ord_pow, show ord F c = (a : WithTop ℤ) from htr]
    simp only [two_nsmul]
    change ((1 - ((a : ℤ) + a) : ℤ) : WithTop ℤ) = _
    congr 1
    ring


section Family

variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  (L : Fin 3 → IntermediateField F K)

attribute [local instance] Basic.intermediateFieldValuativeRel
  Basic.intermediateFieldTopology Basic.intermediateField_localField
  Basic.intermediateField_lowerValuativeExtension Basic.intermediateField_upperValuativeExtension

private def comparison_breaks (E : IntermediateField F K) (t u : ℕ) : Prop :=
  PrimeCyclicExtension.IsLowerBreak F E t ∧ PrimeCyclicExtension.IsLowerBreak E K u

variable [∀ i, Algebra.IsQuadraticExtension F (L i)] [∀ i, PrimeCyclicExtension F (L i)]
  [∀ i, Algebra.IsQuadraticExtension (L i) K] [∀ i, PrimeCyclicExtension (L i) K]

open private commonOrigin_kleinFour from LanglandsSecondMainLemma.Stationary.CommonOrigin
open private primeNormCharacter_card normCharacterProduct_two from
  LanglandsSecondMainLemma.Characters.Conjugacy
open private residueDegree_mul from LanglandsSecondMainLemma.Ramification.DiamondBreaks

omit [∀ i, PrimeCyclicExtension (L i) K]
    [∀ i, Algebra.IsQuadraticExtension (L i) K] in
private theorem comparison_lowerProduct
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (omega : (i : Fin 3) → NormCharacter F (L i)) (homega : ∀ i, omega i ≠ 1) (i : Fin 3) :
    Characters.intermediateNormCharacterProduct Nat.prime_two hG (L i)
      (Algebra.IsQuadraticExtension.finrank_eq_two F (L i)) = (omega i).1 := by
  letI := primeCyclicNormCharacter_finite F (L i)
  exact normCharacterProduct_two F (L i)
    ((primeNormCharacter_card F (L i)).trans (Algebra.IsQuadraticExtension.finrank_eq_two F (L i)))
    (omega i) (homega i)

set_option maxHeartbeats 1600000 in
/-- Comparison of the distinguished field with the second field.
Given the actual lower norm characters and their product and separation
identities, construct the origin, lower coefficients, cores, and adjusted
stationary data. `Characters.quadraticProduct` constructs these lower-character inputs
from the fields in the final wrapper. -/
private theorem comparison_pair
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (hinj : Function.Injective L)
    (omega : (i : Fin 3) → NormCharacter F (L i)) (homega : ∀ i, omega i ≠ 1)
    (hproduct : (omega 2).1 = (omega 0).1 * (omega 1).1)
    (hsep : Function.Injective (fun i => Ramification.intermediateNormRange (L i)))
    (e a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (hchar : ringChar F ≠ 2) (hreschar : residueCharacteristic F = 2)
    (htF : ∀ i, PrimeCyclicExtension.IsLowerBreak F (L i)
      (if i = 0 then 2 * a - 1 else 2 * r - 1))
    (htK : ∀ i, PrimeCyclicExtension.IsLowerBreak (L i) K
      (if i = 0 then 4 * r - 2 * a - 1 else 2 * a - 1))
    (hresF : ∀ i, residueDegree F (L i) = 1)
    (hresK : ∀ i, residueDegree (L i) K = 1)
    (theta : (i : Fin 3) → ContinuousQuasiChar (L i))
    (Theta : ContinuousQuasiChar K)
    (hc : ∀ i, normQuasiChar (L i) K (theta i) = Theta)
    (hprimitive : ¬ ∃ chi : ContinuousQuasiChar F, normQuasiChar F K chi = Theta)
    (psi : LocalAddCharData F) :
    localConstant (L 0) (theta 0) (tracePullbackAddChar F (L 0) psi.character) *
        localConstant F (Characters.intermediateNormCharacterProduct Nat.prime_two hG (L 0)
          (Algebra.IsQuadraticExtension.finrank_eq_two F (L 0))) psi.character =
      localConstant (L 1) (theta 1) (tracePullbackAddChar F (L 1) psi.character) *
        localConstant F (Characters.intermediateNormCharacterProduct Nat.prime_two hG (L 1)
          (Algebra.IsQuadraticExtension.finrank_eq_two F (L 1))) psi.character := by
  classical
  letI := commonOrigin_kleinFour hG
  letI : CharP (ResidueField K) 2 := ringChar.of_eq
    ((residueCharacteristic_extension_eq F K).trans hreschar)
  have htF0 := htF 0
  have htF1 := htF 1
  have htF2 := htF 2
  have htK0 := htK 0
  have htK1 := htK 1
  have htK2 := htK 2
  simp only [ite_true, ite_false, Fin.reduceEq] at htF0 htF1 htF2 htK0 htK1 htK2
  obtain ⟨x0, f0, hx0, hxgen, hf0⟩ := comparison_generator F (L 0) ha htF0 (hresF 0)
  obtain ⟨y, g, hy, hygen, hg⟩ := comparison_generator F (L 1) (ha.trans har) htF1 (hresF 1)
  obtain ⟨pi, hpi⟩ := Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial
    (ValuativeRel.valuation F)
  obtain ⟨pi2, hpi2, hgen2⟩ := monogenicUniformizer F (L 2) (hresF 2)
  have hdiff : differentExponent F (L 2) = 2 * r := by
    rw [differentExponent_eq F (L 2) htF2 pi2 hpi2 hgen2,
      Algebra.IsQuadraticExtension.finrank_eq_two F (L 2)]
    omega
  obtain ⟨x, f, d, z, ⟨O⟩⟩ := dyadicNonmaximal_origin_data_from_alignment F K (L 0) (L 1) (L 2)
    (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
    (hresF 0) (hresF 1) (hresF 2) (hresK 0) e a r ha har hre htwo hreschar
    pi hpi hdiff x0 y f0 g hx0 hy hxgen hygen hf0 hg
  obtain ⟨b, _, _, D⟩ := lowerCharacters F K (L 0) (L 1) (L 2) hchar e a r ha har hre htwo
    htF0 htF1 htF2 (hresF 0) (hresF 1) (hresF 2) x y z f g d O
    (omega 0) (omega 1) (omega 2) (homega 0) (homega 1) (homega 2) hproduct psi
  let alpha := b / normUnits F (L 1)
    (Units.mk0 (trace (L 1) K O.Y) O.upperTraces_ne_zero.2.1)
  obtain ⟨_, _, _, hdet, _, lambda, chi0, chi1, chi2, ht0, ht1, ht2,
      hm0, hm1, _, _, _, _, _, _, hs0, hs1, hs2, hlow, _⟩ :=
    twist (L 0) (L 1) (L 2) hG e a r ha har hre htwo htF0 htF1 htF2 htK0 htK1 htK2
      (hresF 0) (hresF 1) (hresF 2) (hresK 0) (hresK 1) (hresK 2)
      x y z f g d O (omega 0) (omega 1) (omega 2)
      (homega 0) (homega 1) (homega 2) hproduct psi alpha D
      (theta 0) (theta 1) (theta 2) Theta (hc 0) (hc 1) (hc 2) hprimitive
  have H : NormalizationFormulas F (L 0) (L 1) (L 2) a r
      (omega 0) (omega 1) (omega 2) psi
      (normUnits F (L 0) (Units.mk0 (trace (L 0) K O.Y) O.upperTraces_ne_zero.1))
      (normUnits F (L 1) (Units.mk0 (trace (L 1) K O.Y) O.upperTraces_ne_zero.2.1))
      (normUnits F (L 2) (Units.mk0 (trace (L 2) K O.Y) O.upperTraces_ne_zero.2.2))
      (norm (L 0) K O.Y) (norm (L 1) K O.Y) (norm (L 2) K O.Y) chi0 chi1 chi2 alpha :=
    ⟨D, hs0, hs1, hs2⟩
  let thetaD (i : Fin 3) := canonicalLocalQuasiCharData (L i) (theta i)
  let psiL (i : Fin 3) := canonicalLocalAddCharData (L i)
    (tracePullbackAddChar F (L i) psi.character)
    (Basic.tracePullbackAddChar_ne_one F (L i) psi.character psi.isConductor.character_ne_one)
  by_cases hn : multiplicativeConductorExponent F lambda ≤ 2 * r + a - 1
  · obtain ⟨hm0', hm1', hm2'⟩ := hlow hn
    obtain ⟨u, X, _, HU, _, hC, hC0, S0, S1, S2⟩ := minimalOrigin (L 0) (L 1) (L 2) O
      e ha har hre htwo htF0 htF1 htF2 (hresF 0) (hresF 1) (hresF 2) (hresK 2)
      (omega 0) (omega 1) (omega 2) (homega 2) psi alpha chi0 chi1 chi2 H
      (canonicalLocalQuasiCharData F lambda) hn (theta 0) (theta 1) (theta 2) ht0 ht1 ht2
    let alpha' := alpha * (u : Fˣ)
    let C := Units.mk0 (O.adjustedOrigin X) hC0
    by_cases heq : a = r
    · subst a
      have hm (i : Fin 3) : (thetaD i).conductor = 4 * r - 1 := by
        fin_cases i
        · exact hm0'
        · change multiplicativeConductorExponent (L 1) (theta 1) = _
          omega
        · change multiplicativeConductorExponent (L 2) (theta 2) = _
          omega
      have S (i : Fin 3) : MinimalOriginSide (L i) r (2 * r) 0 (omega i)
          (scaleAddCharData F psi alpha').character (thetaD i).character (C : K) := by
        fin_cases i
        · convert S0 using 1 <;> first | rfl | simp
        · convert S1 using 1 <;> first | rfl | omega
        · convert S2 rfl using 1 <;> first | rfl | omega
      exact equalBreaks L hG hsep ha (by rw [mem_lattice, htwo]; exact_mod_cast hre)
        (fun i => by simpa using htF i)
        (fun i => by convert htK i using 1; split_ifs <;> omega)
        hresF hresK thetaD hm omega homega psi psiL (fun _ => rfl)
        alpha' HU.1.base_conductor Theta hc hprimitive C hC S 0 1
    · have har' : a < r := lt_of_le_of_ne har heq
      let Psi := scaleAddCharData F psi alpha'
      let PsiL (i : Fin 3) := scaleAddCharData (L i) (psiL i)
        (Units.map (algebraMap F (L i)).toMonoidHom alpha')
      have hPsiL (i : Fin 3) : (PsiL i).character = Psi.character.compTrace := by
        apply ContinuousAddChar.ext
        intro v
        simp only [PsiL, Psi, scaleAddCharData_character_apply, psiL,
          canonicalLocalAddCharData_character, tracePullbackAddChar_apply,
          ContinuousAddChar.compTrace_apply, Units.coe_map]
        congr 1
        change trace F (L i) (algebraMap F (L i) (alpha' : F) * v) =
          (alpha' : F) * trace F (L i) v
        rw [← Algebra.smul_def, map_smul, smul_eq_mul]
      rw [comparison_lowerProduct L hG omega homega 0, comparison_lowerProduct L hG omega homega 1]
      exact unequalBreaks (L 0) (L 1) ha har' htF0 htF1 htK0 htK1
        (hresF 0) (hresF 1) (hresK 0) (hresK 1) (thetaD 0) (thetaD 1) hm0' hm1'
        (omega 0) (omega 1) (homega 0) (homega 1) Psi HU.1.base_conductor
        (PsiL 0) (PsiL 1) (hPsiL 0) (hPsiL 1) Theta (hc 0) (hc 1) C hC S0 S1
        hG (hsep.ne (by decide)) hprimitive psi (psiL 0) (psiL 1) alpha' rfl rfl rfl
  · have hn' : 2 * r + a ≤ multiplicativeConductorExponent F lambda := by omega
    let h := multiplicativeConductorExponent F lambda - 2 * r
    have hh : a ≤ h := by dsimp [h]; omega
    have hn'' : multiplicativeConductorExponent F lambda = 2 * r + h := by dsimp [h]; omega
    rw [comparison_lowerProduct L hG omega homega 0, comparison_lowerProduct L hG omega homega 1]
    rw [ht0, ht1]
    apply higher e ha har hre htwo htF0 htF1 htF2
      (hresF 0) (hresF 1) (hresF 2) (hresK 0) (hresK 1) (hresK 2) O
      (PrimeCyclicExtension.generator (L 0) K) (PrimeCyclicExtension.generator_ne_one (L 0) K)
      (PrimeCyclicExtension.generator (L 1) K) (PrimeCyclicExtension.generator_ne_one (L 1) K)
      (PrimeCyclicExtension.generator F (L 2)) (PrimeCyclicExtension.generator_ne_one F (L 2))
      (omega 0) (omega 1) (omega 2) (homega 0) (homega 1) (homega 2)
      psi alpha chi0 chi1 chi2 hm0 hm1 lambda h hh hn''
    · rw [← ht0, ← ht1, hc 0, hc 1]
    · rw [← ht0, ← ht1]
      exact hdet.symm
    · exact H

set_option maxHeartbeats 1600000 in
/-- All three complete factors agree for every conductor, given the
actual lower norm characters, their product relation and separated norm
ranges. These extra inputs are the output of `Characters.quadraticProduct`;
the final `comparison` constructs them from the fields.

No origin, stationary model, coefficient, or cancellation is assumed.
The two upper-break values are the ledger `D:NM:upper`. Total ramification
supplies the residue degrees on both sides of every intermediate field;
the finite order of two supplies characteristic different from two. -/
theorem comparison_of_lowerNormCharacters
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (hinj : Function.Injective L)
    (omega : (i : Fin 3) → NormCharacter F (L i)) (homega : ∀ i, omega i ≠ 1)
    (hproduct : (omega 2).1 = (omega 0).1 * (omega 1).1)
    (hsep : Function.Injective (fun i => Ramification.intermediateNormRange (L i)))
    (e a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (hreschar : residueCharacteristic F = 2)
    (htF : ∀ i, PrimeCyclicExtension.IsLowerBreak F (L i)
      (if i = 0 then 2 * a - 1 else 2 * r - 1))
    (htK : ∀ i, PrimeCyclicExtension.IsLowerBreak (L i) K
      (if i = 0 then 4 * r - 2 * a - 1 else 2 * a - 1))
    (hres : residueDegree F K = 1)
    (theta : (i : Fin 3) → ContinuousQuasiChar (L i))
    (Theta : ContinuousQuasiChar K)
    (hc : ∀ i, normQuasiChar (L i) K (theta i) = Theta)
    (hprimitive : ¬ ∃ chi : ContinuousQuasiChar F, normQuasiChar F K chi = Theta)
    (psi : LocalAddCharData F) :
    ∀ i j : Fin 3,
      localConstant (L i) (theta i) (tracePullbackAddChar F (L i) psi.character) *
        localConstant F (Characters.intermediateNormCharacterProduct Nat.prime_two hG (L i)
          (Algebra.IsQuadraticExtension.finrank_eq_two F (L i))) psi.character =
      localConstant (L j) (theta j) (tracePullbackAddChar F (L j) psi.character) *
        localConstant F (Characters.intermediateNormCharacterProduct Nat.prime_two hG (L j)
          (Algebra.IsQuadraticExtension.finrank_eq_two F (L j))) psi.character := by
  classical
  have hchar : ringChar F ≠ 2 := by
    intro h
    letI : CharP F 2 := ringChar.of_eq h
    have htwo0 : (2 : F) ≠ 0 := (ord_ne_top_iff F).mp (by
      rw [htwo]
      exact WithTop.coe_ne_top)
    exact htwo0 (CharP.cast_eq_zero F 2)
  have hresEdges (i : Fin 3) : residueDegree F (L i) = 1 ∧
      residueDegree (L i) K = 1 := by
    have h := (residueDegree_mul (L i)).trans hres
    exact ⟨Nat.eq_one_of_mul_eq_one_right h, Nat.eq_one_of_mul_eq_one_left h⟩
  have hresF (i : Fin 3) : residueDegree F (L i) = 1 := (hresEdges i).1
  have hresK (i : Fin 3) : residueDegree (L i) K = 1 := (hresEdges i).2
  let A (i : Fin 3) := localConstant (L i) (theta i)
    (tracePullbackAddChar F (L i) psi.character) *
    localConstant F (Characters.intermediateNormCharacterProduct Nat.prime_two hG (L i)
      (Algebra.IsQuadraticExtension.finrank_eq_two F (L i))) psi.character
  have h01 : A 0 = A 1 := comparison_pair L hG hinj omega homega hproduct hsep
    e a r ha har hre htwo hchar hreschar htF htK hresF hresK theta Theta hc hprimitive psi
  let p : Equiv.Perm (Fin 3) :=
    ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩
  have h01prod : (omega 1).1 = (omega 0).1 * (omega 2).1 := by
    have hsquare : (omega 0).1 * (omega 0).1 = 1 := by
      have h := pow_card_eq_one' (x := omega 0)
      rw [(primeNormCharacter_card F (L 0)).trans
        (Algebra.IsQuadraticExtension.finrank_eq_two F (L 0)), pow_two] at h
      exact congrArg Subtype.val h
    rw [hproduct, ← mul_assoc, hsquare]
    exact (one_mul ((omega 1).1 : ContinuousQuasiChar F)).symm
  have h02 : A 0 = A 2 := by
    have hF : ∀ i : Fin 3, PrimeCyclicExtension.IsLowerBreak F (L (p i))
        (if i = 0 then 2 * a - 1 else 2 * r - 1) := by
      intro i
      fin_cases i
      · convert htF 0 using 1 <;> rfl
      · convert htF 2 using 1 <;> rfl
      · convert htF 1 using 1 <;> rfl
    have hK : ∀ i : Fin 3, PrimeCyclicExtension.IsLowerBreak (L (p i)) K
        (if i = 0 then 4 * r - 2 * a - 1 else 2 * a - 1) := by
      intro i
      fin_cases i
      · convert htK 0 using 1 <;> rfl
      · convert htK 2 using 1 <;> rfl
      · convert htK 1 using 1 <;> rfl
    have h := comparison_pair (fun i => L (p i)) hG (hinj.comp p.injective)
      (fun i => omega (p i)) (fun i => homega (p i)) (by convert h01prod using 1 <;> rfl)
      (hsep.comp p.injective) e a r ha har hre htwo hchar hreschar hF hK
      (fun i => hresF (p i)) (fun i => hresK (p i))
      (fun i => theta (p i)) Theta (fun i => hc (p i)) hprimitive psi
    exact h
  have h0 (i : Fin 3) : A 0 = A i := by
    fin_cases i
    · rfl
    · exact h01
    · exact h02
  exact fun i j => (h0 i).symm.trans (h0 j)

open private exists_lower_involution from LanglandsSecondMainLemma.Characters.QuadraticProduct

omit [∀ i, PrimeCyclicExtension (L i) K] in
/-- Recover `D:NM:upper` from the three lower breaks, including the equal-break case. -/
private theorem comparison_upperBreaks
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (hinj : Function.Injective L) (a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r)
    (hres : residueDegree F K = 1) (hreschar : residueCharacteristic F = 2)
    (htF : ∀ i, PrimeCyclicExtension.IsLowerBreak F (L i)
      (if i = 0 then 2 * a - 1 else 2 * r - 1)) :
    ∀ i, PrimeCyclicExtension.IsLowerBreak (L i) K
      (if i = 0 then 4 * r - 2 * a - 1 else 2 * a - 1) := by
  classical
  letI := commonOrigin_kleinFour hG
  obtain ⟨P⟩ := (Ramification.diamondBreaks Nat.prime_two hG hreschar).1 hres
  have hcard (i : Fin 3) : Nat.card (L i).fixingSubgroup = 2 := by
    rw [IsGalois.card_fixingSubgroup_eq_finrank]
    exact Algebra.IsQuadraticExtension.finrank_eq_two (L i) K
  have hpair (i : Fin 3) (t u : ℕ)
      (h : Ramification.IntermediateBreakPair Nat.prime_two hG
        (L i).fixingSubgroup (hcard i) t u) :
      PrimeCyclicExtension.IsLowerBreak F (L i) t ∧
        PrimeCyclicExtension.IsLowerBreak (L i) K u := by
    have h' : comparison_breaks (IntermediateField.fixedField (L i).fixingSubgroup) t u := h
    have h'' : comparison_breaks (L i) t u := by
      simpa only [IsGalois.fixedField_fixingSubgroup] using h'
    exact h''
  have hdist (i : Fin 3) (hi : (L i).fixingSubgroup = P.H₀) :
      PrimeCyclicExtension.IsLowerBreak F (L i) P.t ∧
        PrimeCyclicExtension.IsLowerBreak (L i) K P.b := by
    apply hpair i P.t P.b
    simpa only [hi] using P.distinguished_breaks
  have hother (i : Fin 3) (hi : (L i).fixingSubgroup ≠ P.H₀) :
      ∃ s, (PrimeCyclicExtension.IsLowerBreak F (L i) s ∧
        PrimeCyclicExtension.IsLowerBreak (L i) K P.t) ∧
        s = P.t + (P.b - P.t) / 2 ∧ P.b = P.t + 2 * (s - P.t) := by
    obtain ⟨s, hs, _, heq, hb⟩ := P.other_breaks _ (hcard i) hi
    exact ⟨s, hpair i s P.t hs, heq, hb⟩
  have htotal : Module.finrank F K = 4 := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact IsKleinFour.card_four
  choose sigma hsigma hfixed huniq using fun i => exists_lower_involution htotal (L i)
    (Algebra.IsQuadraticExtension.finrank_eq_two F (L i))
  let f (i : Fin 3) : {g : Gal(K/F) // g ≠ 1} := ⟨sigma i, hsigma i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply hinj
    ext x
    rw [← hfixed i, ← hfixed j, show sigma i = sigma j from congrArg Subtype.val hij]
  have hsur : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, by
      simp [Fintype.card_subtype_compl]⟩).2
  obtain ⟨g, hg, hguniq⟩ := (Nat.card_eq_two_iff' (1 : P.H₀)).mp P.card_H₀
  have hg' : (g : Gal(K/F)) ≠ 1 := fun h => hg (Subtype.ext h)
  obtain ⟨d, hd⟩ := hsur ⟨g, hg'⟩
  have hline : (L d).fixingSubgroup = P.H₀ := by
    have hd' : sigma d = (g : Gal(K/F)) := congrArg Subtype.val hd
    ext x
    by_cases hx : x = 1
    · simp [hx]
    constructor
    · intro h
      rw [huniq d x hx h, hd']
      exact g.property
    · intro h
      have hxg : x = (g : Gal(K/F)) := congrArg Subtype.val
        (hguniq ⟨x, h⟩ (fun h => hx (congrArg Subtype.val h)))
      apply (IntermediateField.mem_fixingSubgroup_iff (L d) x).2
      intro y hy
      rw [hxg, ← hd']
      exact (hfixed d y).2 hy
  have ht := PrimeCyclicExtension.isLowerBreak_unique F (L d) (htF d) (hdist d hline).1
  have hne (i : Fin 3) (hi : i ≠ d) : (L i).fixingSubgroup ≠ P.H₀ := by
    intro h
    apply hi
    apply hinj
    simpa only [IsGalois.fixedField_fixingSubgroup] using
      congrArg IntermediateField.fixedField (h.trans hline.symm)
  have hd0 : d = 0 ∨ a = r := by
    by_cases hd0 : d = 0
    · exact Or.inl hd0
    · obtain ⟨s, hs, heq, _⟩ := hother 0 (hne 0 (Ne.symm hd0))
      have hsval := PrimeCyclicExtension.isLowerBreak_unique F (L 0) (htF 0) hs.1
      simp only [if_neg hd0] at ht
      simp only [ite_true] at hsval
      exact Or.inr (by omega)
  obtain ⟨j, hj⟩ := exists_ne d
  obtain ⟨s, hs, heq, hb⟩ := hother j (hne j hj)
  have hsval := PrimeCyclicExtension.isLowerBreak_unique F (L j) (htF j) hs.1
  have htval : P.t = 2 * a - 1 := by
    rcases hd0 with rfl | hequal
    · simpa using ht.symm
    · split_ifs at ht <;> omega
  have hbval : P.b = 4 * r - 2 * a - 1 := by
    rcases hd0 with rfl | hequal
    · simp only [if_neg hj] at hsval
      omega
    · split_ifs at hsval <;> omega
  intro i
  by_cases hi : i = d
  · subst i
    convert (hdist d hline).2 using 1
    split_ifs <;> rcases hd0 with hd0 | hequal <;> omega
  · obtain ⟨s, hs, _, _⟩ := hother i (hne i hi)
    convert hs.2 using 1
    split_ifs <;> rcases hd0 with hd0 | hequal <;> omega

/-- **Paper `D:NM:main`.** The three complete local-constant factors of a
primitive compatible family agree for all `1 ≤ a ≤ r ≤ e` and every conductor.
The actual lower characters and upper ramification breaks are constructed
from the biquadratic fields and their lower breaks. -/
theorem comparison
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (hinj : Function.Injective L)
    (e a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (hreschar : residueCharacteristic F = 2)
    (htF : ∀ i, PrimeCyclicExtension.IsLowerBreak F (L i)
      (if i = 0 then 2 * a - 1 else 2 * r - 1))
    (hres : residueDegree F K = 1)
    (theta : (i : Fin 3) → ContinuousQuasiChar (L i))
    (Theta : ContinuousQuasiChar K)
    (hc : ∀ i, normQuasiChar (L i) K (theta i) = Theta)
    (hprimitive : ¬ ∃ chi : ContinuousQuasiChar F, normQuasiChar F K chi = Theta)
    (psi : LocalAddCharData F) :
    ∀ i j : Fin 3,
      localConstant (L i) (theta i) (tracePullbackAddChar F (L i) psi.character) *
        localConstant F (Characters.intermediateNormCharacterProduct Nat.prime_two hG (L i)
          (Algebra.IsQuadraticExtension.finrank_eq_two F (L i))) psi.character =
      localConstant (L j) (theta j) (tracePullbackAddChar F (L j) psi.character) *
        localConstant F (Characters.intermediateNormCharacterProduct Nat.prime_two hG (L j)
          (Algebra.IsQuadraticExtension.finrank_eq_two F (L j))) psi.character := by
  obtain ⟨omega, homega, hproduct, _, hsep, _⟩ := Characters.quadraticProduct F hG L
    (fun i => Algebra.IsQuadraticExtension.finrank_eq_two F (L i)) hinj
  exact comparison_of_lowerNormCharacters L hG hinj omega homega hproduct hsep
    e a r ha har hre htwo hreschar htF
    (comparison_upperBreaks L hG hinj a r ha har hres hreschar htF)
    hres theta Theta hc hprimitive psi

end Family

end
end LanglandsSecondMainLemma.Dyadic.Nonmaximal
