import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.Models
import LanglandsSecondMainLemma.Characters.Conjugacy

/-!
# Dyadic / Nonmaximal / Twist

Paper Lemma 13.7 (`D:NM:realize`), with the setup `D:NM:breaks`,
`D:NM:upper`, and the actual charts `D:NM:Rcharts`.
-/

namespace LanglandsSecondMainLemma.Dyadic.Nonmaximal

open LanglandsFirstMainLemma
noncomputable section

/-- The odd core and even high pullback cannot have equal conductor.
The high formula is in integers, including its subtraction. -/
private theorem odd_core_twist_conductor
    (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
    [PrimeCyclicExtension F E] [Algebra.IsQuadraticExtension F E]
    (q m k : ℕ) (hq : 1 ≤ q) (hqm : 2 * q < m)
    (hboundary : m + 2 * q + 1 = 2 * k)
    (ht : PrimeCyclicExtension.IsLowerBreak F E (2 * q - 1))
    (hres : residueDegree F E = 1)
    (χ : ContinuousQuasiChar E) (hχ : IsMultiplicativeConductor E χ m)
    (lambda : ContinuousQuasiChar F) :
    let n := multiplicativeConductorExponent F lambda
    let M := multiplicativeConductorExponent E (χ * normQuasiChar F E lambda)
    (n < k → M = m) ∧
    (k ≤ n → (M : ℤ) = 2 * (n : ℤ) - 2 * (q : ℤ) ∧ Even M) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  let n := multiplicativeConductorExponent F lambda
  let P := canonicalLocalQuasiCharData E (normQuasiChar F E lambda)
  have hstep : 2 * q - 1 + 1 = 2 * q := by omega
  have hhigh (hn : 2 * q < n) :
      (P.conductor : ℤ) = 2 * (n : ℤ) - 2 * (q : ℤ) := by
    have h := (canonicalLocalQuasiCharData F lambda).conductor_compNorm_eq_high_explicit
      F E ht hres pi hpi hgen P rfl (by simpa only [hstep, canonicalLocalQuasiCharData] using hn)
    simpa only [Algebra.IsQuadraticExtension.finrank_eq_two F E,
      Nat.cast_ofNat, Nat.reduceSub, one_mul, hstep, Nat.cast_mul,
      canonicalLocalQuasiCharData] using h
  dsimp only
  constructor
  · intro hn
    have hsmall : P.conductor < m := by
      by_cases hlow : n ≤ 2 * q
      · have htriv : QuasiCharTrivialOnUnitFiltration F lambda (2 * q - 1 + 1) := by
          intro u hu
          apply (multiplicativeConductorExponent_isConductor F lambda).trivial
          exact unitFiltration_antitone F (by omega) hu
        have h := (quasiCharTrivialOnUnitFiltration_compNorm_iff_break_succ
          F E ht hres pi hpi hgen lambda).mpr htriv
        have := P.isConductor.minimal _ h
        omega
      · have := hhigh (by omega)
        omega
    exact multiplicativeConductorExponent_eq_of_isConductor E _
      (hχ.mul_of_gt P.isConductor hsmall)
  · intro hn
    have hp := hhigh (by omega)
    have hlarge : m < P.conductor := by omega
    have hM := multiplicativeConductorExponent_eq_of_isConductor E _
      (hχ.mul_of_lt P.isConductor hlarge)
    change multiplicativeConductorExponent E (χ * normQuasiChar F E lambda) =
      P.conductor at hM
    rw [hM]
    exact ⟨hp, ⟨n - q, by omega⟩⟩

/-- Absorb an actual upper norm character into either of the two other
cores. Its critical-successor triviality preserves the entire chart,
including the endpoint `a = r = 1`. -/
private theorem absorb_upper_character
    (E K : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra E K] [ValuativeExtension E K] [Module.Finite E K]
    [PrimeCyclicExtension E K]
    (a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r)
    (ht : PrimeCyclicExtension.IsLowerBreak E K (2 * a - 1))
    (hres : residueDegree E K = 1)
    (χ : ContinuousQuasiChar E)
    (hχ : IsMultiplicativeConductor E χ (2 * a + 2 * r - 1))
    (μ : NormCharacter E K) :
    IsMultiplicativeConductor E (χ * μ.1) (2 * a + 2 * r - 1) ∧
    (∀ u : unitFiltration E (a + r), (χ * μ.1) (u : Eˣ) = χ (u : Eˣ)) ∧
    normQuasiChar E K (χ * μ.1) = normQuasiChar E K χ := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer E K hres
  have hμ := ramifiedNormCharacter_trivialOn_break_succ E K ht hres pi hpi hgen μ
  have hle := (multiplicativeConductorExponent_isConductor E μ.1).minimal _ hμ
  refine ⟨hχ.mul_of_gt (multiplicativeConductorExponent_isConductor E μ.1)
    (by omega), ?_, ?_⟩
  · intro u
    change χ (u : Eˣ) * μ.1 (u : Eˣ) = χ (u : Eˣ)
    rw [hμ u (unitFiltration_antitone E (by omega) u.property), mul_one]
  · apply ContinuousMonoidHom.ext
    intro u
    change χ (normUnits E K u) * μ.1 (normUnits E K u) = χ (normUnits E K u)
    rw [μ.eq_one_on_normRange E K _ ⟨u, rfl⟩, mul_one]

open private primeNormCharacter_card from LanglandsSecondMainLemma.Characters.Conjugacy

section Quotients
variable (F E K : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
  [ValuativeExtension F E] [ValuativeExtension E K] [ValuativeExtension F K]
  [Module.Finite F E] [Module.Finite E K] [Module.Finite F K]
  [PrimeCyclicExtension F E] [Algebra.IsQuadraticExtension F E]

omit [Algebra F K] [IsScalarTower F E K] [ValuativeExtension F K] [Module.Finite F K] in
/-- The order-two quotient is forced by any specified nontrivial upper
norm character. This identifies the quotient of the given family itself. -/
private theorem quotient_eq_nontrivial
    (θ : ContinuousQuasiChar E) (D : Characters.ConjugateTwistData F E K θ)
    (ν : NormCharacter E K) (hν : ν ≠ 1) (σ : Gal(E/F)) (hσ : σ ≠ 1) :
    Basic.conjugateQuasiChar F E σ θ / θ = ν.1 := by
  have hc : Nat.card (NormCharacter E K) = 2 :=
    (Nat.card_congr D.quotientEquiv.toEquiv).symm.trans
      ((IsGalois.card_aut_eq_finrank F E).trans
        (Algebra.IsQuadraticExtension.finrank_eq_two F E))
  rw [← D.quotient_eq]
  exact congrArg Subtype.val (((Nat.card_eq_two_iff' (1 : NormCharacter E K)).mp hc).unique
    ((map_ne_one_iff D.quotientEquiv D.quotientEquiv.injective).mpr hσ) hν)

omit [Algebra F K] [IsScalarTower F E K] [ValuativeExtension F K] [Module.Finite F K] in
/-- Hilbert 90 descends the quotient of the first given character and the
first core, without changing either given character. -/
private theorem first_quotient_descends
    (θ χ : ContinuousQuasiChar E)
    (Dθ : Characters.ConjugateTwistData F E K θ)
    (Dχ : Characters.ConjugateTwistData F E K χ) :
    ∃ lambda : ContinuousQuasiChar F, θ = χ * normQuasiChar F E lambda := by
  have hinv (σ : Gal(E/F)) (u : Eˣ) :
      (θ / χ) (Units.map σ.toMonoidHom u) = (θ / χ) u := by
    by_cases hσ : σ = 1
    · subst σ; rfl
    have hs : σ.symm ≠ 1 := by
      change σ⁻¹ ≠ 1
      exact inv_ne_one.mpr hσ
    have heq := quotient_eq_nontrivial F E K θ Dθ (Dχ.quotientEquiv σ.symm)
      ((map_ne_one_iff Dχ.quotientEquiv Dχ.quotientEquiv.injective).mpr hs) σ.symm hs
    rw [Dχ.quotient_eq] at heq
    have hv := DFunLike.congr_fun heq u
    change θ (Units.map σ.toMonoidHom u) / θ u =
      χ (Units.map σ.toMonoidHom u) / χ u at hv
    change θ (Units.map σ.toMonoidHom u) / χ (Units.map σ.toMonoidHom u) = θ u / χ u
    apply (div_eq_div_iff_mul_eq_mul).mpr
    exact ((div_eq_div_iff_mul_eq_mul).mp hv).trans (mul_comm _ _)
  obtain ⟨lambda, hlambda⟩ := Local.invariantCharacter_descends F E (θ / χ) hinv
  refine ⟨lambda, ?_⟩
  rw [hlambda]
  simp [div_eq_mul_inv]

omit [PrimeCyclicExtension F E] in
/-- Norm transitivity for the actual twisted continuous character. -/
private theorem twisted_pullback (χ : ContinuousQuasiChar E) (lambda : ContinuousQuasiChar F) :
    normQuasiChar E K (χ * normQuasiChar F E lambda) =
      normQuasiChar E K χ * normQuasiChar F K lambda := by
  apply ContinuousMonoidHom.ext
  intro u
  change χ (normUnits E K u) * lambda (normUnits F E (normUnits E K u)) =
    χ (normUnits E K u) * lambda (normUnits F K u)
  congr 2
  exact Units.ext (Basic.norm_tower (F := F) (L := E) (u : K))

end Quotients

section ActualFamily
variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  (L₁ L₂ L₃ : IntermediateField F K)

attribute [local instance] Basic.intermediateFieldValuativeRel
  Basic.intermediateFieldTopology Basic.intermediateField_localField
  Basic.intermediateField_lowerValuativeExtension Basic.intermediateField_upperValuativeExtension

variable [Algebra.IsQuadraticExtension F L₁] [Algebra.IsQuadraticExtension L₁ K]
  [Algebra.IsQuadraticExtension F L₂] [Algebra.IsQuadraticExtension L₂ K]
  [Algebra.IsQuadraticExtension F L₃] [Algebra.IsQuadraticExtension L₃ K]
  [PrimeCyclicExtension F L₁] [PrimeCyclicExtension L₁ K]
  [PrimeCyclicExtension F L₂] [PrimeCyclicExtension L₂ K]
  [PrimeCyclicExtension F L₃] [PrimeCyclicExtension L₃ K]

set_option maxHeartbeats 1600000 in
/-- **Paper Lemma 13.7 (`D:NM:realize`).**

Every given primitive compatible family is exactly a common base twist of
cores with the original full stationary formulas. All three corrected
restrictions and all six crossed conjugate-quotient identities are retained.
The two conductor ranges are consecutive; the high conductors are even.

The origin and normalized lower data have the constructors in `Origin` and
`LowerCharacters`. The nontrivial lower characters and their product relation
are the same actual lower-character inputs as in `lowerCharacters`.
Intermediate fields carry the canonical restricted valuations and topologies.
-/
theorem twist
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (e a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (htLower₁ : PrimeCyclicExtension.IsLowerBreak F L₁ (2 * a - 1))
    (htLower₂ : PrimeCyclicExtension.IsLowerBreak F L₂ (2 * r - 1))
    (htLower₃ : PrimeCyclicExtension.IsLowerBreak F L₃ (2 * r - 1))
    (ht₁ : PrimeCyclicExtension.IsLowerBreak L₁ K (4 * r - 2 * a - 1))
    (ht₂ : PrimeCyclicExtension.IsLowerBreak L₂ K (2 * a - 1))
    (ht₃ : PrimeCyclicExtension.IsLowerBreak L₃ K (2 * a - 1))
    (hres₁ : residueDegree F L₁ = 1) (hres₂ : residueDegree F L₂ = 1)
    (hres₃ : residueDegree F L₃ = 1)
    (hres₁K : residueDegree L₁ K = 1) (hres₂K : residueDegree L₂ K = 1)
    (hres₃K : residueDegree L₃ K = 1)
    (x : L₁) (y : L₂) (z : L₃) (f g d : F)
    (O : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂) (ω₃ : NormCharacter F L₃)
    (hω₁ : ω₁ ≠ 1) (hω₂ : ω₂ ≠ 1) (hω₃ : ω₃ ≠ 1)
    (hproduct : ω₃.1 = ω₁.1 * ω₂.1)
    (ψ : LocalAddCharData F) (α : Fˣ)
    (D : LowerCharacterData F L₁ L₂ L₃ a r ω₁ ω₂ ω₃ ψ α
      (normUnits F L₁ (Units.mk0 (trace L₁ K O.Y) O.upperTraces_ne_zero.1))
      (normUnits F L₂ (Units.mk0 (trace L₂ K O.Y) O.upperTraces_ne_zero.2.1))
      (normUnits F L₃ (Units.mk0 (trace L₃ K O.Y) O.upperTraces_ne_zero.2.2)))
    (θ₁ : ContinuousQuasiChar L₁) (θ₂ : ContinuousQuasiChar L₂)
    (θ₃ : ContinuousQuasiChar L₃) (Θ : ContinuousQuasiChar K)
    (hcomp₁ : normQuasiChar L₁ K θ₁ = Θ)
    (hcomp₂ : normQuasiChar L₂ K θ₂ = Θ)
    (hcomp₃ : normQuasiChar L₃ K θ₃ = Θ)
    (hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Θ) :
    (∀ σ : Gal(L₁/F), σ ≠ 1 →
      Basic.conjugateQuasiChar F L₁ σ θ₁ / θ₁ = normQuasiChar F L₁ ω₂.1 ∧
      Basic.conjugateQuasiChar F L₁ σ θ₁ / θ₁ = normQuasiChar F L₁ ω₃.1) ∧
    (∀ σ : Gal(L₂/F), σ ≠ 1 →
      Basic.conjugateQuasiChar F L₂ σ θ₂ / θ₂ = normQuasiChar F L₂ ω₁.1 ∧
      Basic.conjugateQuasiChar F L₂ σ θ₂ / θ₂ = normQuasiChar F L₂ ω₃.1) ∧
    (∀ σ : Gal(L₃/F), σ ≠ 1 →
      Basic.conjugateQuasiChar F L₃ σ θ₃ / θ₃ = normQuasiChar F L₃ ω₁.1 ∧
      Basic.conjugateQuasiChar F L₃ σ θ₃ / θ₃ = normQuasiChar F L₃ ω₂.1) ∧
    Characters.restrictQuasiChar F L₂ θ₂ * ω₂.1 =
      Characters.restrictQuasiChar F L₁ θ₁ * ω₁.1 ∧
    Characters.restrictQuasiChar F L₃ θ₃ * ω₃.1 =
      Characters.restrictQuasiChar F L₁ θ₁ * ω₁.1 ∧
    let Ψ := (scaleAddCharData F ψ α).character
    ∃ (lambda : ContinuousQuasiChar F) (χ₁ : ContinuousQuasiChar L₁)
      (χ₂ : ContinuousQuasiChar L₂) (χ₃ : ContinuousQuasiChar L₃),
      θ₁ = χ₁ * normQuasiChar F L₁ lambda ∧
      θ₂ = χ₂ * normQuasiChar F L₂ lambda ∧
      θ₃ = χ₃ * normQuasiChar F L₃ lambda ∧
      IsMultiplicativeConductor L₁ χ₁ (4 * r - 1) ∧
      IsMultiplicativeConductor L₂ χ₂ (2 * a + 2 * r - 1) ∧
      IsMultiplicativeConductor L₃ χ₃ (2 * a + 2 * r - 1) ∧
      normQuasiChar L₂ K χ₂ = normQuasiChar L₁ K χ₁ ∧
      normQuasiChar L₃ K χ₃ = normQuasiChar L₁ K χ₁ ∧
      IsMultiplicativeConductor K (normQuasiChar L₁ K χ₁) (4 * r + 2 * a - 2) ∧
      (∀ (ρ : Gal(K/F)) (u : Kˣ),
        normQuasiChar L₁ K χ₁ (Units.map ρ.toMonoidHom u) = normQuasiChar L₁ K χ₁ u) ∧
      (¬ ∃ eta : ContinuousQuasiChar F, normQuasiChar F K eta = normQuasiChar L₁ K χ₁) ∧
      (∀ u : unitFiltration L₁ (2 * r), χ₁ (u : L₁ˣ) =
        tracePullbackAddChar F L₁ Ψ (norm L₁ K O.Y * (1 - ((u : L₁ˣ) : L₁)))) ∧
      (∀ u : unitFiltration L₂ (a + r), χ₂ (u : L₂ˣ) =
        tracePullbackAddChar F L₂ Ψ (norm L₂ K O.Y * (1 - ((u : L₂ˣ) : L₂)))) ∧
      (∀ u : unitFiltration L₃ (a + r), χ₃ (u : L₃ˣ) =
        tracePullbackAddChar F L₃ Ψ (norm L₃ K O.Y * (1 - ((u : L₃ˣ) : L₃)))) ∧
      (let n := multiplicativeConductorExponent F lambda
       let M₁ := multiplicativeConductorExponent L₁ θ₁
       let M₂ := multiplicativeConductorExponent L₂ θ₂
       let M₃ := multiplicativeConductorExponent L₃ θ₃
       (n ≤ 2 * r + a - 1 → M₁ = 4 * r - 1 ∧
         M₂ = 2 * a + 2 * r - 1 ∧ M₃ = 2 * a + 2 * r - 1) ∧
       (2 * r + a ≤ n →
         (M₁ : ℤ) = 2 * (n : ℤ) - 2 * (a : ℤ) ∧
         (M₂ : ℤ) = 2 * (n : ℤ) - 2 * (r : ℤ) ∧
         (M₃ : ℤ) = 2 * (n : ℤ) - 2 * (r : ℤ) ∧ Even M₁ ∧ Even M₂ ∧ Even M₃)) := by
  classical
  have deg₁ := Algebra.IsQuadraticExtension.finrank_eq_two F L₁
  have deg₂ := Algebra.IsQuadraticExtension.finrank_eq_two F L₂
  have deg₃ := Algebra.IsQuadraticExtension.finrank_eq_two F L₃
  have card₁ : Nat.card (NormCharacter F L₁) = 2 := (primeNormCharacter_card F L₁).trans deg₁
  have card₂ : Nat.card (NormCharacter F L₂) = 2 := (primeNormCharacter_card F L₂).trans deg₂
  have card₃ : Nat.card (NormCharacter F L₃) = 2 := (primeNormCharacter_card F L₃).trans deg₃
  have hsquare : ω₁.1 * ω₁.1 = 1 := by
    have h := pow_card_eq_one' (x := ω₁)
    rw [card₁, pow_two] at h
    exact congrArg Subtype.val h
  have ne₁₂ : ω₁.1 ≠ ω₂.1 := by
    intro h
    apply hω₃
    apply Subtype.ext
    change ω₃.1 = 1
    rw [hproduct, ← h, hsquare]
  have ne₁₃ : ω₁.1 ≠ ω₃.1 := by
    intro h
    apply hω₂
    apply Subtype.ext
    change ω₂.1 = 1
    apply ContinuousMonoidHom.ext
    intro u
    exact mul_eq_left.mp (DFunLike.congr_fun (hproduct.symm.trans h.symm) u)
  have ne₂₃ : ω₂.1 ≠ ω₃.1 := by
    intro h
    apply hω₁
    apply Subtype.ext
    change ω₁.1 = 1
    apply ContinuousMonoidHom.ext
    intro u
    exact mul_eq_right.mp (DFunLike.congr_fun (hproduct.symm.trans h.symm) u)
  -- Transport norm triviality, then use uniqueness of the nonidentity
  -- element in the actual quadratic norm-character group.
  have separate (I J : IntermediateField F K)
      [PrimeCyclicExtension F I] [Algebra.IsQuadraticExtension F I]
      (ω : NormCharacter F I) (ν : NormCharacter F J)
      (hω : ω ≠ 1) (hν : ν ≠ 1) (hne : ω.1 ≠ ν.1) :
      Ramification.intermediateNormRange I ≠ Ramification.intermediateNormRange J := by
    intro h
    change (normUnits F I).range = (normUnits F J).range at h
    let ν' : NormCharacter F I := ⟨ν.1, by
      apply ContinuousMonoidHom.ext
      intro u
      change ν.1 (normUnits F I u) = 1
      apply ν.eq_one_on_normRange F J
      rw [← h]
      exact ⟨u, rfl⟩⟩
    have hv : ν' ≠ 1 := fun heq =>
      hν (Subtype.ext (congrArg (fun eta : NormCharacter F I => eta.1) heq))
    have hc : Nat.card (NormCharacter F I) = 2 :=
      (primeNormCharacter_card F I).trans (Algebra.IsQuadraticExtension.finrank_eq_two F I)
    exact hne (congrArg Subtype.val (((Nat.card_eq_two_iff' (1 : NormCharacter F I)).mp hc).unique hω hv))
  have hn₁₂ := separate L₁ L₂ ω₁ ω₂ hω₁ hω₂ ne₁₂
  have hn₁₃ := separate L₁ L₃ ω₁ ω₃ hω₁ hω₃ ne₁₃
  have hn₂₃ := separate L₂ L₃ ω₂ ω₃ hω₂ hω₃ ne₂₃
  obtain ⟨⟨Dθ₁⟩, ⟨Dθ₂⟩, hdet₂, _, hquad₂⟩ :=
    Characters.conjugacy Nat.prime_two hG L₁ L₂ deg₁ deg₂ hn₁₂
      θ₁ θ₂ Θ hcomp₁ hcomp₂ hprimitive
  obtain ⟨_, ⟨Dθ₃⟩, hdet₃, _, hquad₃⟩ :=
    Characters.conjugacy Nat.prime_two hG L₁ L₃ deg₁ deg₃ hn₁₃
      θ₁ θ₃ Θ hcomp₁ hcomp₃ hprimitive
  obtain ⟨τ₁, τ₂, hτ₁, hτ₂, he₁, he₂⟩ := hquad₂ rfl
  obtain ⟨_, τ₃, _, hτ₃, _, he₃⟩ := hquad₃ rfl
  have eq₁ := ((Nat.card_eq_two_iff' (1 : NormCharacter F L₁)).mp card₁).unique hτ₁ hω₁
  have eq₂ := ((Nat.card_eq_two_iff' (1 : NormCharacter F L₂)).mp card₂).unique hτ₂ hω₂
  have eq₃ := ((Nat.card_eq_two_iff' (1 : NormCharacter F L₃)).mp card₃).unique hτ₃ hω₃
  rw [he₁, he₂, eq₁, eq₂] at hdet₂
  rw [he₁, he₃, eq₁, eq₃] at hdet₃
  have quotient (I J : IntermediateField F K)
      [PrimeCyclicExtension F I] [PrimeCyclicExtension F J] [PrimeCyclicExtension I K]
      [Algebra.IsQuadraticExtension F I] [Algebra.IsQuadraticExtension F J]
      [Algebra.IsQuadraticExtension I K]
      (hne : Ramification.intermediateNormRange I ≠ Ramification.intermediateNormRange J)
      (θ : ContinuousQuasiChar I) (Dθ : Characters.ConjugateTwistData F I K θ)
      (ω : NormCharacter F J) (hω : ω ≠ 1) (σ : Gal(I/F)) (hσ : σ ≠ 1) :
      Basic.conjugateQuasiChar F I σ θ / θ = normQuasiChar F I ω.1 := by
    let c := Characters.crossedNormEquivOfTowers F I J K Nat.prime_two
      (Algebra.IsQuadraticExtension.finrank_eq_two F I)
      (Algebra.IsQuadraticExtension.finrank_eq_two F J)
      (Algebra.IsQuadraticExtension.finrank_eq_two I K) hne
    exact quotient_eq_nontrivial F I K θ Dθ (c ω)
      ((map_ne_one_iff c c.injective).mpr hω) σ hσ
  refine ⟨(fun σ hσ => ⟨quotient L₁ L₂ hn₁₂ θ₁ Dθ₁ ω₂ hω₂ σ hσ,
      quotient L₁ L₃ hn₁₃ θ₁ Dθ₁ ω₃ hω₃ σ hσ⟩),
    (fun σ hσ => ⟨quotient L₂ L₁ hn₁₂.symm θ₂ Dθ₂ ω₁ hω₁ σ hσ,
      quotient L₂ L₃ hn₂₃ θ₂ Dθ₂ ω₃ hω₃ σ hσ⟩),
    (fun σ hσ => ⟨quotient L₃ L₁ hn₁₃.symm θ₃ Dθ₃ ω₁ hω₁ σ hσ,
      quotient L₃ L₂ hn₂₃.symm θ₃ Dθ₃ ω₂ hω₂ σ hσ⟩), hdet₂.symm, hdet₃.symm, ?_⟩
  letI : IsKleinFour Gal(K/F) := by
    let c := Classical.choice hG
    constructor
    · rw [Nat.card_congr c.toEquiv]; simp
    · rw [Monoid.exponent_eq_of_mulEquiv c]; simp [Monoid.exponent_prod]
  obtain ⟨χ₁, χ₂, χ₃, hc₁, hc₂, hc₃, hp₂, hp₃, htop, hinv, hprim, hR₁, hR₂, hR₃⟩ :=
    models F K L₁ L₂ L₃ e a r ha har hre htwo htLower₁ ht₁ ht₂ ht₃
      hres₁ hres₁K hres₂K hres₃K x y z f g d O ω₁ ω₂ ω₃ ψ α D
  have hprim' : ¬ ∃ eta : ContinuousQuasiChar F,
      normQuasiChar F K eta = normQuasiChar L₁ K χ₁ := by
    rintro ⟨eta, he⟩
    exact hprim ⟨eta, he.symm⟩
  obtain ⟨⟨Dχ₁⟩, _⟩ := Characters.conjugacy Nat.prime_two hG L₁ L₂ deg₁ deg₂ hn₁₂
    χ₁ χ₂ (normQuasiChar L₁ K χ₁) rfl hp₂ hprim'
  obtain ⟨lambda, hreal₁⟩ := first_quotient_descends F L₁ K θ₁ χ₁ Dθ₁ Dχ₁
  have hpull : Θ = normQuasiChar L₁ K χ₁ * normQuasiChar F K lambda := by
    rw [← hcomp₁, hreal₁, twisted_pullback]
  have discrepancy (I : IntermediateField F K)
      [PrimeCyclicExtension F I] [Algebra.IsQuadraticExtension F I]
      (θ χ : ContinuousQuasiChar I)
      (ht : normQuasiChar I K θ = Θ)
      (hc : normQuasiChar I K χ = normQuasiChar L₁ K χ₁) :
      ∃ μ : NormCharacter I K, θ = (χ * μ.1) * normQuasiChar F I lambda := by
    have he : normQuasiChar I K θ = normQuasiChar I K (χ * normQuasiChar F I lambda) := by
      rw [twisted_pullback, hc, ht, hpull]
    let μ : NormCharacter I K := ⟨θ / (χ * normQuasiChar F I lambda), by
      apply ContinuousMonoidHom.ext
      intro u
      change θ (normUnits I K u) / (χ * normQuasiChar F I lambda) (normUnits I K u) = 1
      exact div_eq_one.mpr (DFunLike.congr_fun he u)⟩
    refine ⟨μ, ?_⟩
    change θ = (χ * (θ / (χ * normQuasiChar F I lambda))) * normQuasiChar F I lambda
    apply ContinuousMonoidHom.ext
    intro u
    change θ u = (χ u * (θ u / (χ u * normQuasiChar F I lambda u))) *
      normQuasiChar F I lambda u
    simp [div_eq_mul_inv, mul_comm, mul_left_comm]
  obtain ⟨μ₂, hreal₂⟩ := discrepancy L₂ θ₂ χ₂ hcomp₂ hp₂
  obtain ⟨μ₃, hreal₃⟩ := discrepancy L₃ θ₃ χ₃ hcomp₃ hp₃
  obtain ⟨hc₂', hchart₂, hp₂'⟩ := absorb_upper_character L₂ K a r ha har ht₂ hres₂K χ₂ hc₂ μ₂
  obtain ⟨hc₃', hchart₃, hp₃'⟩ := absorb_upper_character L₃ K a r ha har ht₃ hres₃K χ₃ hc₃ μ₃
  refine ⟨lambda, χ₁, χ₂ * μ₂.1, χ₃ * μ₃.1, hreal₁, hreal₂, hreal₃,
    hc₁, hc₂', hc₃', hp₂'.trans hp₂, hp₃'.trans hp₃, htop, hinv, hprim',
    hR₁, (fun u => (hchart₂ u).trans (hR₂ u)), (fun u => (hchart₃ u).trans (hR₃ u)), ?_⟩
  have cond₁ := odd_core_twist_conductor F L₁ a (4 * r - 1) (2 * r + a)
    ha (by omega) (by omega) htLower₁ hres₁ χ₁ hc₁ lambda
  have cond₂ := odd_core_twist_conductor F L₂ r (2 * a + 2 * r - 1) (2 * r + a)
    (by omega) (by omega) (by omega) htLower₂ hres₂ (χ₂ * μ₂.1) hc₂' lambda
  have cond₃ := odd_core_twist_conductor F L₃ r (2 * a + 2 * r - 1) (2 * r + a)
    (by omega) (by omega) (by omega) htLower₃ hres₃ (χ₃ * μ₃.1) hc₃' lambda
  rw [← hreal₁] at cond₁
  rw [← hreal₂] at cond₂
  rw [← hreal₃] at cond₃
  constructor
  · intro hn
    exact ⟨cond₁.1 (by omega), cond₂.1 (by omega), cond₃.1 (by omega)⟩
  · intro hn
    exact ⟨(cond₁.2 hn).1, (cond₂.2 hn).1, (cond₃.2 hn).1,
      (cond₁.2 hn).2, (cond₂.2 hn).2, (cond₃.2 hn).2⟩

end ActualFamily
end
end LanglandsSecondMainLemma.Dyadic.Nonmaximal
