import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Local.Hilbert90
import LanglandsSecondMainLemma.Local.CharacterExtension
import LanglandsSecondMainLemma.Basic.NormTrace

/-!
# Local / Norm Descent

This file supplies the character-descent construction used in the paper's
prime-degree edges. If a continuous quasi-character upstairs is invariant
under the actual cyclic Galois group, multiplicative Hilbert 90 makes it
constant on the fibres of the actual field norm. It therefore defines an
algebraic character on the norm image.

Continuity of the descended character is not assumed. A sufficiently deep
unit layer on which the upstairs character is trivial is chosen from
continuity. FML's exact norm-filtration theorem realizes the corresponding
downstairs layer by norms from that upstairs layer. The character-extension
lemma then extends the norm-image character to the whole downstairs unit
group. This treats unramified and ramified prime-cyclic edges separately and
does not require the norm map to be surjective.

The final theorem is the two-subgroup form of the paper's compatible
prescription convention: the supplied character on the generated subgroup
is explicit data, so agreement and multiplicativity are not inferred merely
from pointwise overlap agreement.

Paper: lines 121--136 and 394--405, with Lemmas `C:hilbert90` and
`C:character-extension` at lines 8583--8637.
-/

namespace LanglandsSecondMainLemma.Local

open LanglandsFirstMainLemma

noncomputable section

section AlgebraicDescent

variable (F E : Type) [Field F] [Field E] [Algebra F E]
  [Module.Free F E] [Module.Finite F E] [PrimeCyclicExtension F E]

/-- An invariant character has the same value on two elements having the
same actual field norm.

The proof is precisely the multiplicative part of cyclic Hilbert 90. The
orientation `y / sigma(y)` agrees with `Local.hilbert90`; invariance makes
the character of this quotient equal to one. -/
private theorem invariantCharacter_eq_of_norm_eq
    (Theta : Eˣ →* ℂˣ)
    (hinvariant : ∀ (sigma : Gal(E/F)) (x : Eˣ),
      Theta (Units.map sigma.toMonoidHom x) = Theta x)
    {x y : Eˣ} (hxy : normUnits F E x = normUnits F E y) :
    Theta x = Theta y := by
  let sigma : Gal(E/F) := PrimeCyclicExtension.generator F E
  have hgenerator : ∀ tau : Gal(E/F), tau ∈ Subgroup.zpowers sigma :=
    PrimeCyclicExtension.generator_mem_zpowers F E
  have hnormQuotient : x / y ∈ (normUnits F E).ker := by
    rw [MonoidHom.mem_ker, map_div, hxy]
    change (normUnits F E y) / normUnits F E y = (1 : Fˣ)
    simp
  have hcoboundary : x / y ∈ (multiplicativeCoboundary sigma).range := by
    rw [← (hilbert90 (F := F) (E := E) sigma hgenerator).1]
    exact hnormQuotient
  obtain ⟨z, hz⟩ := hcoboundary
  have hquotient : Theta (x / y) = 1 := by
    rw [← hz, multiplicativeCoboundary_apply, map_div,
      hinvariant sigma z]
    change Theta z / Theta z = (1 : ℂˣ)
    simp
  rw [map_div, div_eq_one] at hquotient
  exact hquotient

/-- The algebraic character on the actual norm image induced by an invariant
upstairs character.

This is deliberately only a `MonoidHom`. Its continuity is established
later by the exact norm-filtration argument, rather than being inserted as
an extra hypothesis. -/
private noncomputable def invariantCharacterOnNormRange
    (Theta : Eˣ →* ℂˣ)
    (hinvariant : ∀ (sigma : Gal(E/F)) (x : Eˣ),
      Theta (Units.map sigma.toMonoidHom x) = Theta x) :
    (normUnits F E).range →* ℂˣ where
  toFun z := Theta (Classical.choose z.property)
  map_one' := by
    have hnorm :
        normUnits F E (Classical.choose
          ((1 : (normUnits F E).range).property)) = normUnits F E 1 := by
      rw [Classical.choose_spec ((1 : (normUnits F E).range).property)]
      simp
    exact (invariantCharacter_eq_of_norm_eq F E Theta hinvariant
      hnorm).trans (map_one Theta)
  map_mul' a b := by
    have hnorm :
        normUnits F E (Classical.choose (a * b).property) =
          normUnits F E
            (Classical.choose a.property * Classical.choose b.property) := by
      rw [Classical.choose_spec (a * b).property, map_mul,
        Classical.choose_spec a.property, Classical.choose_spec b.property]
      rfl
    exact (invariantCharacter_eq_of_norm_eq F E Theta hinvariant hnorm).trans
      (map_mul Theta (Classical.choose a.property)
        (Classical.choose b.property))

/-- Evaluation of the norm-image character on an honest norm recovers the
given upstairs character. -/
@[simp]
private theorem invariantCharacterOnNormRange_norm
    (Theta : Eˣ →* ℂˣ)
    (hinvariant : ∀ (sigma : Gal(E/F)) (x : Eˣ),
      Theta (Units.map sigma.toMonoidHom x) = Theta x)
    (x : Eˣ) :
    invariantCharacterOnNormRange F E Theta hinvariant
        ((normUnits F E).rangeRestrict x) = Theta x := by
  apply invariantCharacter_eq_of_norm_eq F E Theta hinvariant
  exact Classical.choose_spec ((normUnits F E).rangeRestrict x).property

end AlgebraicDescent

section ContinuousDescent

variable (F E : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E]
  [Module.Free F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

/-- **Descent of an invariant character through a cyclic norm.**

Let `E/F` be an actual prime-cyclic extension of nonarchimedean local
fields. Every continuous group homomorphism `Theta : Eˣ → ℂˣ` invariant
under every element of the actual Galois group is the pullback along the
actual field norm of a continuous group homomorphism on `Fˣ`.

No unitary condition is imposed: in particular, the extension lemma retains
arbitrary nonzero complex values on uniformizers. The result asserts
existence, not uniqueness; two descents may differ by an element of
`NormCharacter F E`. -/
theorem invariantCharacter_descends
    (Theta : ContinuousQuasiChar E)
    (hinvariant : ∀ (sigma : Gal(E/F)) (x : Eˣ),
      Theta (Units.map sigma.toMonoidHom x) = Theta x) :
    ∃ theta : ContinuousQuasiChar F,
      normQuasiChar F E theta = Theta := by
  let H : Subgroup Fˣ := (normUnits F E).range
  let chi : H →* ℂˣ :=
    invariantCharacterOnNormRange F E Theta.toMonoidHom hinvariant
  obtain ⟨d, hTheta⟩ :=
    exists_quasiCharTrivialOnUnitFiltration E Theta
  by_cases hunramified : ramificationIndex F E = 1
  · let m : ℕ := d + 1
    have hm : 1 ≤ m := by
      simp only [m]
      omega
    have hUH : unitFiltration F m ≤ H := by
      intro u hu
      obtain ⟨x, hx, hxu⟩ :=
        (unramified_norm_unitFiltration F E hunramified m).2 u hu
      exact ⟨x, hxu⟩
    have htrivial : chi.comp (Subgroup.inclusion hUH) = 1 := by
      apply MonoidHom.ext
      intro u
      obtain ⟨x, hx, hxu⟩ :=
        (unramified_norm_unitFiltration F E hunramified m).2 u u.property
      have hThetaX : Theta x = 1 :=
        hTheta x (unitFiltration_antitone E (by simp [m]) hx)
      change chi ⟨(u : Fˣ), hUH u.property⟩ = 1
      have hsubtype :
          (⟨(u : Fˣ), hUH u.property⟩ : H) =
            (normUnits F E).rangeRestrict x := by
        apply Subtype.ext
        exact hxu.symm
      rw [hsubtype]
      exact (invariantCharacterOnNormRange_norm F E
        Theta.toMonoidHom hinvariant x).trans hThetaX
    obtain ⟨theta, htheta⟩ :=
      characterExtension F H m hm hUH chi htrivial
    refine ⟨theta, ?_⟩
    apply ContinuousMonoidHom.ext
    intro x
    have hrestriction := DFunLike.congr_fun htheta
      ((normUnits F E).rangeRestrict x)
    change theta (normUnits F E x) = Theta x
    calc
      theta (normUnits F E x) =
          chi ((normUnits F E).rangeRestrict x) := hrestriction
      _ = Theta x := invariantCharacterOnNormRange_norm F E
        Theta.toMonoidHom hinvariant x
  · let P : PrimeCyclicPreparation F E :=
      primeCyclicPreparation F E hunramified
    let m : ℕ := P.t + d + 1
    let sourceDepth : ℕ :=
      herbrandPsiNat P.t (Module.finrank F E) m
    have htm : P.t < m := by
      simp only [m]
      omega
    have hm : 1 ≤ m := by
      simp only [m]
      omega
    have hdegree : 0 < Module.finrank F E :=
      Module.finrank_pos
    have hdsource : d ≤ sourceDepth := by
      have hdm : d ≤ m := by
        simp only [m]
        omega
      exact hdm.trans
        (self_le_herbrandPsiNat P.t (Module.finrank F E) hdegree m)
    let normFiltration :=
      cyclicPrimeNormFiltration F E P.ht P.hres P.piK P.hpiK P.hgen
    have himage :
        Subgroup.map (normUnits F E) (unitFiltration E sourceDepth) =
          unitFiltration F m := by
      exact normFiltration.above_image m htm
    have hUH : unitFiltration F m ≤ H := by
      intro u hu
      have huImage :
          u ∈ Subgroup.map (normUnits F E)
            (unitFiltration E sourceDepth) := by
        rw [himage]
        exact hu
      obtain ⟨x, _hx, hxu⟩ := huImage
      exact ⟨x, hxu⟩
    have htrivial : chi.comp (Subgroup.inclusion hUH) = 1 := by
      apply MonoidHom.ext
      intro u
      have huImage :
          (u : Fˣ) ∈ Subgroup.map (normUnits F E)
            (unitFiltration E sourceDepth) := by
        rw [himage]
        exact u.property
      obtain ⟨x, hx, hxu⟩ := huImage
      have hThetaX : Theta x = 1 :=
        hTheta x (unitFiltration_antitone E hdsource hx)
      change chi ⟨(u : Fˣ), hUH u.property⟩ = 1
      have hsubtype :
          (⟨(u : Fˣ), hUH u.property⟩ : H) =
            (normUnits F E).rangeRestrict x := by
        apply Subtype.ext
        exact hxu.symm
      rw [hsubtype]
      exact (invariantCharacterOnNormRange_norm F E
        Theta.toMonoidHom hinvariant x).trans hThetaX
    obtain ⟨theta, htheta⟩ :=
      characterExtension F H m hm hUH chi htrivial
    refine ⟨theta, ?_⟩
    apply ContinuousMonoidHom.ext
    intro x
    have hrestriction := DFunLike.congr_fun htheta
      ((normUnits F E).rangeRestrict x)
    change theta (normUnits F E x) = Theta x
    calc
      theta (normUnits F E x) =
          chi ((normUnits F E).rangeRestrict x) := hrestriction
      _ = Theta x := invariantCharacterOnNormRange_norm F E
        Theta.toMonoidHom hinvariant x

end ContinuousDescent

section CompatiblePrescriptions

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- Extend a compatible pair of subgroup prescriptions to continuous
characters on the whole local multiplicative group.

The character `generatedCharacter` is a genuine homomorphism on
`H₁ ⊔ H₂`, and `hprescribed₁`, `hprescribed₂` say that its restrictions
are the given pair. Requiring this datum is the paper's explicit safeguard:
pairwise agreement on an overlap alone is not silently treated as a proof
that the prescriptions multiply consistently on the generated subgroup.
The conclusion is one continuous character satisfying both members of the
prescribed family. -/
theorem compatiblePair_extendFamily
    (H₁ H₂ : Subgroup Eˣ) (chi₁ : H₁ →* ℂˣ) (chi₂ : H₂ →* ℂˣ)
    (generatedCharacter : ↑(H₁ ⊔ H₂) →* ℂˣ)
    (hprescribed₁ : generatedCharacter.comp
      (Subgroup.inclusion le_sup_left) = chi₁)
    (hprescribed₂ : generatedCharacter.comp
      (Subgroup.inclusion le_sup_right) = chi₂)
    (m : ℕ) (hm : 1 ≤ m) (hU : unitFiltration E m ≤ H₁ ⊔ H₂)
    (htrivial : generatedCharacter.comp (Subgroup.inclusion hU) = 1) :
    ∃ extension : ContinuousQuasiChar E,
      extension.toMonoidHom.comp H₁.subtype = chi₁ ∧
        extension.toMonoidHom.comp H₂.subtype = chi₂ := by
  obtain ⟨extension, hextension⟩ :=
    characterExtension E (H₁ ⊔ H₂) m hm hU generatedCharacter htrivial
  refine ⟨extension, ?_, ?_⟩
  · calc
      extension.toMonoidHom.comp H₁.subtype =
          (extension.toMonoidHom.comp (H₁ ⊔ H₂).subtype).comp
            (Subgroup.inclusion le_sup_left) := by rfl
      _ = generatedCharacter.comp
            (Subgroup.inclusion le_sup_left) := by rw [hextension]
      _ = chi₁ := hprescribed₁
  · calc
      extension.toMonoidHom.comp H₂.subtype =
          (extension.toMonoidHom.comp (H₁ ⊔ H₂).subtype).comp
            (Subgroup.inclusion le_sup_right) := by rfl
      _ = generatedCharacter.comp
            (Subgroup.inclusion le_sup_right) := by rw [hextension]
      _ = chi₂ := hprescribed₂

end CompatiblePrescriptions

end

end LanglandsSecondMainLemma.Local
