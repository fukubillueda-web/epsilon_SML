import LanglandsFirstMainLemma.Delta.FirstMainStatement
import LanglandsFirstMainLemma.Main
import LanglandsSecondMainLemma.Classification.Exhaustion
import LanglandsSecondMainLemma.Tame.Comparison
import LanglandsSecondMainLemma.Odd.UR.Comparison
import LanglandsSecondMainLemma.Odd.Total.Comparison
import LanglandsSecondMainLemma.Dyadic.UR.Comparison
import LanglandsSecondMainLemma.Dyadic.Equal.Comparison
import LanglandsSecondMainLemma.Dyadic.Maximal.Comparison
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.Comparison
import LanglandsSecondMainLemma.Characters.InducingChoice
import LanglandsSecondMainLemma.Basic.SecondMainStatement

/-!
# Dispatch

The final assembly of Theorem `U:main`, following `U:dispatch` and the
proof in the completion section. The classifier and branch theorems
construct all auxiliary field, character, and stationary data.

Blueprint: `blueprint/tasks/Dispatch.md`.
Paper: lines 121--155 and 8185--8220.
-/

namespace LanglandsSecondMainLemma

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

open private fixedField_line_finrank exists_line_ne from
  LanglandsSecondMainLemma.Odd.Total.Setup
open private commonOrigin_kleinFour from LanglandsSecondMainLemma.Stationary.CommonOrigin

section ActualFields

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K]

/-- The branch factor is exactly the public expression, with the complete
finite product of lower norm characters. -/
private theorem inductionExpression_eq_inducingFactor {p : ℕ}
    (extension : Basic.PrimeSquareExtension F K p)
    (family : Basic.PrimitiveCompatibleFamily F K extension)
    (ψ : ContinuousAddChar F) (L : IntermediateField F K)
    (hL : Module.finrank F L = p) :
    letI : IsGalois F K := extension.isGalois
    Basic.inductionExpression F K extension family ψ L hL =
      Characters.inducingFactor extension.prime extension.galoisGroupEquiv ψ L hL
        (family.inducingCharacter L hL) := by
  letI : IsGalois F K := extension.isGalois
  unfold Basic.inductionExpression Characters.inducingFactor
  have hrec {P Q : Prop} (h : P ∧ Q) (f : P → Q → ℂ) :
      And.casesOn h f = f h.1 h.2 := by cases h; rfl
  simp only [hrec]
  rfl

variable [IsGalois F K]

omit [Module.Free F K] in
/-- Label all three actual quadratic fields, starting with any prescribed
order-two fixed field. This uses only the Klein-four group, in either
field characteristic. -/
private theorem quadraticFields
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (H₀ : Subgroup Gal(K/F)) (hH₀ : Nat.card H₀ = 2) :
    ∃ L : Fin 3 → IntermediateField F K,
      L 0 = IntermediateField.fixedField H₀ ∧
      (∀ i, Module.finrank F (L i) = 2) ∧ Function.Injective L ∧
      ∀ (I : IntermediateField F K), Module.finrank F I = 2 → ∃ i, L i = I := by
  classical
  letI := commonOrigin_kleinFour hG
  obtain ⟨g₁, g₂, hg₁, hg₂, hne, hline⟩ :=
    Dyadic.Equal.exists_origin_generators H₀ hH₀
  let g : Fin 3 → Gal(K/F) := ![g₁, g₂, g₁ * g₂]
  have hmul : g₁ * g₂ ≠ 1 := by
    intro h
    exact hne ((mul_eq_one_iff_eq_inv.mp h).trans (IsKleinFour.inv_eq_self g₂))
  have hm₁ : g₁ * g₂ ≠ g₁ := by simpa using hg₂
  have hm₂ : g₁ * g₂ ≠ g₂ := by simpa using hg₁
  have hg : ∀ i, g i ≠ 1 := by intro i; fin_cases i <;> assumption
  have hginj : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [g, Ne.symm]
  let L := fun i => IntermediateField.fixedField (Dyadic.Equal.originLine (g i))
  refine ⟨L, ?_, ?_, ?_, ?_⟩
  · change IntermediateField.fixedField (Dyadic.Equal.originLine g₁) = _
    rw [hline]
  · intro i
    exact fixedField_line_finrank Nat.prime_two hG _ (Dyadic.Equal.card_originLine _ (hg i))
  · intro i j hij
    have hlines := congrArg IntermediateField.fixingSubgroup hij
    dsimp [L] at hlines
    simp only [IntermediateField.fixingSubgroup_fixedField] at hlines
    have hm : g i ∈ Dyadic.Equal.originLine (g j) :=
      hlines ▸ (Or.inr rfl : g i ∈ Dyadic.Equal.originLine (g i))
    exact hginj (hm.resolve_left (hg i))
  · intro I hI
    have hc : Nat.card I.fixingSubgroup = 2 := by
      rw [IsGalois.card_fixingSubgroup_eq_finrank]
      exact (Basic.intermediateField_tower_compatible Nat.prime_two hG I hI).2.2.2.2.2.2.2.2.2.2.1
    obtain ⟨x, _, hx, _, _, hIx⟩ := Dyadic.Equal.exists_origin_generators I.fixingSubgroup hc
    have hfix : IntermediateField.fixedField (Dyadic.Equal.originLine x) = I := by
      rw [← hIx, IsGalois.fixedField_fixingSubgroup]
    by_cases hx₁ : x = g₁
    · exact ⟨0, by simpa [L, g, hx₁] using hfix⟩
    by_cases hx₂ : x = g₂
    · exact ⟨1, by simpa [L, g, hx₂] using hfix⟩
    have hx₃ := IsKleinFour.eq_mul_of_ne_all hg₁ hg₂ hne hx hx₁ hx₂
    exact ⟨2, by simpa [L, g, hx₃] using hfix⟩

/-- In the wild inertia-line case, compare through the actual inertia fixed
field. Cyclic descent and inducing-choice independence extend the branch
comparisons to every pair of fields and compatible inducing characters. -/
private theorem inertiaLine_comparison {p : ℕ} (hp : p.Prime)
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hchar : residueCharacteristic F = p)
    (hI : Nat.card (Ramification.inertiaSubgroup (F := F) (K := K)) = p)
    (fields : Classification.InertiaLineClassification hp hG hI)
    (Θ : ContinuousQuasiChar K)
    (hinv : ∀ σ : Gal(K/F), Basic.conjugateQuasiChar F K σ Θ = Θ)
    (hprimitive : ¬ ∃ χ : ContinuousQuasiChar F, normQuasiChar F K χ = Θ)
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1)
    (I J : IntermediateField F K) (hdegI : Module.finrank F I = p)
    (hdegJ : Module.finrank F J = p)
    (θI : ContinuousQuasiChar I) (θJ : ContinuousQuasiChar J)
    (hcI : normQuasiChar I K θI = Θ) (hcJ : normQuasiChar J K θJ = Θ) :
    Characters.inducingFactor hp hG ψ I hdegI θI =
      Characters.inducingFactor hp hG ψ J hdegJ θJ := by
  let T := Ramification.inertiaSubgroup (F := F) (K := K)
  let U := IntermediateField.fixedField T
  obtain ⟨H₀, hH₀, hne₀⟩ := exists_line_ne hp hG T
  have hU : Module.finrank F U = p := fixedField_line_finrank hp hG T hI
  have hE₀ := fixedField_line_finrank hp hG H₀ hH₀
  have hsep := (Ramification.normSeparation hp hG).unramified_lower hI H₀ hH₀ hne₀
  obtain ⟨_, _, hall⟩ := Characters.distinguishedComparisons_imply_family hp hG
    U (IntermediateField.fixedField H₀) hU hE₀ hsep Θ hinv hprimitive ψ hψ (by
      intro L hL hneL
      have hcard : Nat.card L.fixingSubgroup = p := by
        rw [IsGalois.card_fixingSubgroup_eq_finrank]
        exact (Basic.intermediateField_tower_compatible hp hG L hL).2.2.2.2.2.2.2.2.2.2.1
      have hneH : L.fixingSubgroup ≠ T := by
        intro heq
        apply hneL
        rw [← IsGalois.fixedField_fixingSubgroup L, heq]
      have htransport : ∀ (L' : IntermediateField F K) (hL' : Module.finrank F L' = p),
          IntermediateField.fixedField L.fixingSubgroup = L' →
          ∀ (θU : ContinuousQuasiChar U) (θL : ContinuousQuasiChar L'),
          normQuasiChar U K θU = Θ → normQuasiChar L' K θL = Θ →
          Characters.inducingFactor hp hG ψ U hU θU =
            Characters.inducingFactor hp hG ψ L' hL' θL := by
        intro L' hL' heq
        subst L'
        intro θU θL hcU hcL
        by_cases htwo : p = 2
        · subst htwo
          apply Dyadic.UR.comparison hG U (IntermediateField.fixedField L.fixingSubgroup)
            hU hL' _ hchar fields.unramified_lower.1 θU θL (hcU.trans hcL.symm) _ ψ hψ
          · intro heq
            apply hneH
            have h := congrArg IntermediateField.fixingSubgroup heq
            simpa only [U, IntermediateField.fixingSubgroup_fixedField] using h.symm
          · simpa only [hcU] using hprimitive
        · have hodd : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm htwo)
          exact (Odd.UR.comparison hp hodd hG hchar hI L.fixingSubgroup hcard hneH
            θU θL Θ hcU hcL hprimitive ψ hψ).2.2.2
      exact htransport L hL (IsGalois.fixedField_fixingSubgroup L))
  exact hall I J hdegI hdegJ θI θJ hcI hcJ

/-- Transfer the universal break ledger to a labeling of the actual three
quadratic fields. No representative or extra ramification condition is chosen. -/
private theorem quadraticFields_breaks
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (D : Ramification.TotallyRamifiedDiamondBreaks Nat.prime_two hG)
    (L : Fin 3 → IntermediateField F K)
    (hL : ∀ i, Module.finrank F (L i) = 2) (hinj : Function.Injective L)
    (hzero : L 0 = IntermediateField.fixedField D.H₀) :
    ∀ i, Dyadic.Maximal.actualLowerBreak hG (L i) (hL i)
      (if i = 0 then D.t else D.t + (D.b - D.t) / 2) := by
  intro i
  by_cases hi : i = 0
  · subst i
    simp only [ite_true]
    have htransport : ∀ (I : IntermediateField F K) (hI : Module.finrank F I = 2),
        I = IntermediateField.fixedField D.H₀ →
        Dyadic.Maximal.actualLowerBreak hG I hI D.t := by
      intro I hI heq
      subst I
      exact D.distinguished_breaks.1
    exact htransport (L 0) (hL 0) hzero
  · rw [if_neg hi]
    have hc : Nat.card (L i).fixingSubgroup = 2 := by
      rw [IsGalois.card_fixingSubgroup_eq_finrank]
      exact (Basic.intermediateField_tower_compatible Nat.prime_two hG (L i) (hL i)).2.2.2.2.2.2.2.2.2.2.1
    have hne : (L i).fixingSubgroup ≠ D.H₀ := by
      intro heq
      apply hi
      apply hinj
      rw [hzero, ← heq, IsGalois.fixedField_fixingSubgroup]
    obtain ⟨s, hs, _, hseq, _⟩ := D.other_breaks (L i).fixingSubgroup hc hne
    have htransport : ∀ (I : IntermediateField F K) (hI : Module.finrank F I = 2),
        IntermediateField.fixedField (L i).fixingSubgroup = I →
        Dyadic.Maximal.actualLowerBreak hG I hI s := by
      intro I hI heq
      subst I
      exact hs.1
    rw [← hseq]
    exact htransport (L i) (hL i) (IsGalois.fixedField_fixingSubgroup (L i))

/-- Both mixed-characteristic total branches use the same actual three-field
labeling. The maximal branch gives two equalities through the distinguished
field; the nonmaximal branch gives every pair directly. -/
private theorem mixedTotal_comparison
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (D : Ramification.TotallyRamifiedDiamondBreaks Nat.prime_two hG)
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = 2)
    (e a : ℕ) (ha : 1 ≤ a) (hae : a ≤ e)
    (htwo : ord F (2 : F) = ((e : ℤ) : WithTop ℤ))
    (ht : D.t + 1 = 2 * a)
    (hs : D.t + (D.b - D.t) / 2 = 2 * e ∨
      ∃ r : ℕ, a ≤ r ∧ r ≤ e ∧ D.t + (D.b - D.t) / 2 + 1 = 2 * r)
    (Θ : ContinuousQuasiChar K)
    (θ : ∀ (I : IntermediateField F K), Module.finrank F I = 2 → ContinuousQuasiChar I)
    (hc : ∀ (I : IntermediateField F K) (hI : Module.finrank F I = 2),
      normQuasiChar I K (θ I hI) = Θ)
    (hprimitive : ¬ ∃ χ : ContinuousQuasiChar F, normQuasiChar F K χ = Θ)
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1) :
    ∀ (I J : IntermediateField F K) (hI : Module.finrank F I = 2)
      (hJ : Module.finrank F J = 2),
      Characters.inducingFactor Nat.prime_two hG ψ I hI (θ I hI) =
        Characters.inducingFactor Nat.prime_two hG ψ J hJ (θ J hJ) := by
  classical
  obtain ⟨L, hzero, hL, hinj, hsurj⟩ := quadraticFields hG D.H₀ D.card_H₀
  have hbreaks := quadraticFields_breaks hG D L hL hinj hzero
  let ψdata := canonicalLocalAddCharData F ψ hψ
  have hall : ∀ i j : Fin 3,
      Characters.inducingFactor Nat.prime_two hG ψ (L i) (hL i) (θ (L i) (hL i)) =
        Characters.inducingFactor Nat.prime_two hG ψ (L j) (hL j) (θ (L j) (hL j)) := by
    rcases hs with hs | ⟨r, har, hre, hs⟩
    · have ht₀ : Dyadic.Maximal.actualLowerBreak hG (L 0) (hL 0) (2 * a - 1) := by
        convert hbreaks 0 using 1
        simp only [ite_true]
        omega
      have ht₁ : Dyadic.Maximal.actualLowerBreak hG (L 1) (hL 1) (2 * e) := by
        simpa only [show (1 : Fin 3) ≠ 0 by decide, ite_false, hs] using hbreaks 1
      have ht₂ : Dyadic.Maximal.actualLowerBreak hG (L 2) (hL 2) (2 * e) := by
        simpa only [show (2 : Fin 3) ≠ 0 by decide, ite_false, hs] using hbreaks 2
      obtain ⟨h₁, h₂⟩ := Dyadic.Maximal.comparison hG (L 0) (L 1) (L 2)
        (hL 0) (hL 1) (hL 2) (hinj.ne (by decide)) (hinj.ne (by decide))
        (hinj.ne (by decide)) hres hchar a e ha hae htwo ht₀ ht₁ ht₂
        (θ (L 0) (hL 0)) (θ (L 1) (hL 1)) (θ (L 2) (hL 2)) Θ
        (hc _ _) (hc _ _) (hc _ _) hprimitive ψdata
      have hto : ∀ i : Fin 3,
          Characters.inducingFactor Nat.prime_two hG ψ (L 0) (hL 0) (θ (L 0) (hL 0)) =
            Characters.inducingFactor Nat.prime_two hG ψ (L i) (hL i) (θ (L i) (hL i)) := by
        intro i
        fin_cases i
        · rfl
        · exact h₁
        · exact h₂
      exact fun i j => (hto i).symm.trans (hto j)
    · have hdata := fun i => Basic.intermediateField_tower_compatible Nat.prime_two hG (L i) (hL i)
      letI : ∀ i, Algebra.IsQuadraticExtension F (L i) := fun i => ⟨hL i⟩
      letI : ∀ i, Algebra.IsQuadraticExtension (L i) K :=
        fun i => ⟨(hdata i).2.2.2.2.2.2.2.2.2.2.1⟩
      letI : ∀ i, PrimeCyclicExtension F (L i) := fun i =>
        PrimeCyclicExtension.ofCyclicPrimeExtension F (L i) (hdata i).2.2.2.2.2.2.2.2.2.2.2.1
      letI : ∀ i, PrimeCyclicExtension (L i) K := fun i =>
        PrimeCyclicExtension.ofCyclicPrimeExtension (L i) K (hdata i).2.2.2.2.2.2.2.2.2.2.2.2
      have htF : ∀ i : Fin 3, PrimeCyclicExtension.IsLowerBreak F (L i)
          (if i = 0 then 2 * a - 1 else 2 * r - 1) := by
        intro i
        have hb := hbreaks i
        change PrimeCyclicExtension.IsLowerBreak F (L i) _ at hb
        convert hb using 1
        split_ifs <;> omega
      have heq := Dyadic.Nonmaximal.comparison L hG hinj e a r ha har hre htwo hchar
        htF hres (fun i => θ (L i) (hL i)) Θ (fun i => hc _ _) hprimitive ψdata
      intro i j
      change Characters.inducingFactor Nat.prime_two hG ψdata.character _ _ _ =
        Characters.inducingFactor Nat.prime_two hG ψdata.character _ _ _
      rw [Dyadic.Maximal.comparison_inducingFactor hG (L i) (hL i) _ ψdata,
        Dyadic.Maximal.comparison_inducingFactor hG (L j) (hL j) _ ψdata]
      exact heq i j
  intro I J hI hJ
  obtain ⟨i, rfl⟩ := hsurj I hI
  obtain ⟨j, rfl⟩ := hsurj J hJ
  exact hall i j

/-- Apply the seven proved comparisons to the exhaustive classifier. Every
argument involving a model or a choice is constructed inside those proofs. -/
private theorem actualFamily_comparison {p : ℕ} (hp : p.Prime)
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (Θ : ContinuousQuasiChar K)
    (hinv : ∀ σ : Gal(K/F), Basic.conjugateQuasiChar F K σ Θ = Θ)
    (θ : ∀ (I : IntermediateField F K), Module.finrank F I = p → ContinuousQuasiChar I)
    (hc : ∀ (I : IntermediateField F K) (hI : Module.finrank F I = p),
      normQuasiChar I K (θ I hI) = Θ)
    (hprimitive : ¬ ∃ χ : ContinuousQuasiChar F, normQuasiChar F K χ = Θ)
    (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1) :
    ∀ (I J : IntermediateField F K) (hI : Module.finrank F I = p)
      (hJ : Module.finrank F J = p),
      Characters.inducingFactor hp hG ψ I hI (θ I hI) =
        Characters.inducingFactor hp hG ψ J hJ (θ J hJ) := by
  rcases Classification.exhaustion hp hG with
    ⟨hchar, hI, hwild, hroots, fields⟩ |
    ⟨hchar, hodd, hI, fields⟩ |
    ⟨hchar, hodd, hres, D, hprime, hothers⟩ |
    ⟨hchar, hI, fields⟩ |
    ⟨hcharP, hchar, hres, D, ht, hs⟩ |
    ⟨hcharZero, hchar, hres, D, e, a, he, ha, hae, ht, hs⟩ |
    ⟨hcharZero, hchar, hres, D, e, a, r, he, ha, har, hre, ht, hs⟩
  · intro I J hdegI hdegJ
    exact Tame.comparison hp hchar hG Θ hinv hprimitive ψ hψ I J hdegI hdegJ
      (θ I hdegI) (θ J hdegJ) (hc _ _) (hc _ _)
  · intro I J hdegI hdegJ
    exact inertiaLine_comparison hp hG hchar hI fields Θ hinv hprimitive ψ hψ
      I J hdegI hdegJ (θ I hdegI) (θ J hdegJ) (hc _ _) (hc _ _)
  · intro I J hI hJ
    by_cases hne : I = J
    · subst J
      rfl
    · exact Odd.Total.comparison hp hG hres hchar hodd I J hI hJ hne
        (θ I hI) (θ J hJ) Θ (hc _ _) (hc _ _) hprimitive ψ hψ
  · rename_i hG
    intro I J hdegI hdegJ
    exact inertiaLine_comparison Nat.prime_two hG hchar hI fields Θ hinv hprimitive ψ hψ
      I J hdegI hdegJ (θ I hdegI) (θ J hdegJ) (hc _ _) (hc _ _)
  · rename_i hG
    letI : CharP F 2 := hcharP
    letI := commonOrigin_kleinFour hG
    intro I J hI hJ
    exact Dyadic.Equal.comparison hres Θ hinv hprimitive ψ hψ I J hI hJ
      (θ I hI) (θ J hJ) (hc _ _) (hc _ _)
  · rename_i hG
    exact mixedTotal_comparison hG D hres hchar e a ha hae he ht (Or.inl hs)
      Θ θ hc hprimitive ψ hψ
  · rename_i hG
    exact mixedTotal_comparison hG D hres hchar e a ha (har.trans hre) he ht
      (Or.inr ⟨r, har, hre, hs⟩) Θ θ hc hprimitive ψ hψ

end ActualFields

/-- **The Second Main identity from the actual local data**, Theorem `U:main`.

The actual prime-square Galois extension and primitive compatible family
provide every hypothesis of the exhaustive local classification and its
seven comparisons. Transitivity through the distinguished fields gives
independence for all intermediate fields. Both characteristics, every
prime, arbitrary nontrivial additive characters, and nonunitary continuous
quasi-characters are retained. Each expression uses FML's canonical
`localConstant` and the complete lower norm-character product.

No stationary model, conductor chart, exact norm representative, or
comparison identity is an additional hypothesis. -/
theorem secondMainIdentity_of_actualData
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K]
    {ℓ : ℕ} (extension : Basic.PrimeSquareExtension F K ℓ)
    (family : Basic.PrimitiveCompatibleFamily F K extension)
    (ψF : ContinuousAddChar F) (hψF : ψF ≠ 1) :
    Basic.SecondMainIdentity F K extension family ψF hψF := by
  letI : IsGalois F K := extension.isGalois
  have hall := actualFamily_comparison extension.prime extension.galoisGroupEquiv
    family.topCharacter family.invariant family.inducingCharacter family.compatible
    family.not_normPullback ψF hψF
  intro I J hI hJ
  rw [inductionExpression_eq_inducingFactor extension family ψF I hI,
    inductionExpression_eq_inducingFactor extension family ψF J hJ]
  exact hall I J hI hJ

end

end LanglandsSecondMainLemma
