import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Characters.Conjugacy
import LanglandsSecondMainLemma.Local.NormDescent
import LanglandsSecondMainLemma.Ramification.Inertia

/-!
# Tame conductor reduction

Paper: the tame local diamond and the beginning of “Conductors greater than
one”, `references/epsilon_SML.tex`, lines 915–955.
-/

namespace LanglandsSecondMainLemma.Tame

open LanglandsFirstMainLemma
open scoped BigOperators

noncomputable section

section Conjugation
variable (F U : Type) [Field F] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F U] [ValuativeExtension F U]
  [Module.Finite F U]

private theorem conjugate_mem_unitFiltration (σ : Gal(U/F)) (n : ℕ) (u : Uˣ) :
    Units.map σ.toMonoidHom u ∈ unitFiltration U n ↔ u ∈ unitFiltration U n := by
  cases n with
  | zero =>
      simp only [mem_unitFiltration_zero, Units.coe_map]
      change ord U (σ (u : U)) = 0 ↔ ord U (u : U) = 0
      rw [ord_galoisConjugate]
  | succ n =>
      simp only [mem_unitFiltration_succ, Units.coe_map]
      change CongruentAtDepth ((n + 1 : ℕ) : ℤ) (σ (u : U)) 1 ↔ _
      simp only [CongruentAtDepth]
      rw [show σ (u : U) - 1 = σ ((u : U) - 1) by simp, ord_galoisConjugate]

private theorem conjugate_isConductor (σ : Gal(U/F))
    {θ : ContinuousQuasiChar U} {m : ℕ} (hθ : IsMultiplicativeConductor U θ m) :
    IsMultiplicativeConductor U (Basic.conjugateQuasiChar F U σ θ) m := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact hθ.trivial _ ((conjugate_mem_unitFiltration F U σ.symm m x).2 hx)
  · intro n hn
    apply hθ.minimal n
    intro x hx
    have h := hn (Units.map σ.toMonoidHom x)
      ((conjugate_mem_unitFiltration F U σ n x).2 hx)
    change θ (Units.map σ.symm.toMonoidHom (Units.map σ.toMonoidHom x)) = 1 at h
    have heq : Units.map σ.symm.toMonoidHom (Units.map σ.toMonoidHom x) = x := by
      ext; simp
    rwa [heq] at h

/-- A non-descending continuous character of a prime-cyclic local extension
has positive conductor.  In particular this proves `m_U ≥ 1` for the
primitive tame pair.  No unitarity or characteristic assumption is needed. -/
theorem tame_primitive_conductor_positive [PrimeCyclicExtension F U]
    (θ : ContinuousQuasiChar U) {m : ℕ} (hθ : IsMultiplicativeConductor U θ m)
    (hprimitive : ¬ ∃ lam : ContinuousQuasiChar F, normQuasiChar F U lam = θ) :
    0 < m := by
  by_contra hm
  have hmzero : m = 0 := by omega
  apply hprimitive
  apply Local.invariantCharacter_descends F U θ
  intro σ x
  have hu : Units.map σ.toMonoidHom x / x ∈ unitFiltration U 0 := by
    rw [mem_unitFiltration_zero, Units.val_div_eq_div_val, Units.coe_map,
      ord_div]
    change ord U (σ (x : U)) - ord U (x : U) = 0
    rw [ord_galoisConjugate]
    rw [← coe_localUnitOrder]
    simp
  have h := hθ.trivial _ (hmzero ▸ hu)
  simpa only [map_div, div_eq_one] using h

end Conjugation

section PrincipalUnits
variable (U : Type) [Field U]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]

/-- The restriction to principal units has order dividing the order of the
actual finite quotient through which it factors. -/
private theorem principal_character_pow_eq_one
    (θ : ContinuousQuasiChar U) {m : ℕ} (hm : 1 ≤ m)
    (hθ : QuasiCharTrivialOnUnitFiltration U θ m)
    (x : Uˣ) (hx : x ∈ unitFiltration U 1) :
    θ x ^ (residueCard U ^ (m - 1)) = 1 := by
  let f : UnitFiltrationQuotient U 1 m hm →* ℂˣ :=
    QuotientGroup.lift (unitFiltrationInside U hm)
      (θ.toMonoidHom.comp (unitFiltration U 1).subtype) (by
        intro u hu
        exact hθ u ((mem_unitFiltrationInside U hm u).1 hu))
  let z := unitFiltrationQuotientMk U hm ⟨x, hx⟩
  have hcard := positiveUnitFiltrationQuotient_card U (by omega : 0 < 1) hm
  have hz := pow_card_eq_one' (x := z)
  rw [hcard] at hz
  have hf := congrArg f hz
  simpa [f, z, map_pow] using hf

private theorem residueCard_coprime {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hne : ℓ ≠ residueCharacteristic U) : Nat.Coprime ℓ (residueCard U) := by
  letI := residueFieldFintype U
  obtain ⟨n, _, hn⟩ := FiniteField.card (ResidueField U) (residueCharacteristic U)
  change Nat.Coprime ℓ (Fintype.card (ResidueField U))
  rw [hn]
  exact ((hℓ.coprime_iff_not_dvd).2 (by
    intro hdiv
    exact hne ((Nat.dvd_prime (residueCharacteristic_prime U)).1 hdiv |>.resolve_left
      hℓ.ne_one))).pow_right _

end PrincipalUnits

private theorem quasiChar_zpow_apply {F : Type} [Field F] [TopologicalSpace F]
    (θ : ContinuousQuasiChar F) (a : ℤ) (x : Fˣ) : (θ ^ a) x = θ x ^ a := by
  cases a <;> simp [zpow_negSucc]

section EdgeReduction
variable (F U K : Type) [Field F] [Field U] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F U] [Algebra U K]
  [ValuativeExtension F U] [ValuativeExtension U K]
  [Module.Finite F U] [Module.Finite U K]
  [PrimeCyclicExtension F U]

private theorem conjugateTwists_power_invariant
    {ℓ : ℕ} (hdegree : Module.finrank F U = ℓ)
    (θ : ContinuousQuasiChar U) (D : Characters.ConjugateTwistData F U K θ) :
    ∀ (σ : Gal(U/F)) (x : Uˣ),
      (θ ^ ℓ) (Units.map σ.toMonoidHom x) = (θ ^ ℓ) x := by
  intro σ x
  have hσ : σ.symm ^ ℓ = 1 := by
    rw [← hdegree, ← IsGalois.card_aut_eq_finrank F U]
    exact pow_card_eq_one' (x := σ.symm)
  have hμ : D.quotientEquiv σ.symm ^ ℓ = 1 := by
    rw [← map_pow, hσ, map_one]
  have hμval := congrArg Subtype.val hμ
  rw [NormCharacter.coe_pow, NormCharacter.coe_one] at hμval
  have hμx := DFunLike.congr_fun hμval x
  simp only [ContinuousQuasiChar.pow_apply, ContinuousQuasiChar.one_apply] at hμx
  have h := DFunLike.congr_fun (D.conjugate_eq_twist σ.symm) x
  change θ (Units.map σ.toMonoidHom x) = θ x * (D.quotientEquiv σ.symm).1 x at h
  simp only [ContinuousQuasiChar.pow_apply]
  rw [h, mul_pow, hμx, mul_one]

/-- Descend a prime power of the character, then invert that prime on the
finite principal-unit quotient.  This constructs the removed base twist. -/
private theorem remove_principal_restriction
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hdegree : Module.finrank F U = ℓ)
    (hne : ℓ ≠ residueCharacteristic U)
    (θ : ContinuousQuasiChar U) (D : Characters.ConjugateTwistData F U K θ)
    {m : ℕ} (hm : 1 ≤ m) (hθ : IsMultiplicativeConductor U θ m) :
    ∃ lam : ContinuousQuasiChar F,
      QuasiCharTrivialOnUnitFiltration U (θ / normQuasiChar F U lam) 1 := by
  obtain ⟨ρ, hρ⟩ := Local.invariantCharacter_descends F U (θ ^ ℓ)
    (conjugateTwists_power_invariant F U K hdegree θ D)
  let Q := residueCard U ^ (m - 1)
  have hcop : Nat.Coprime ℓ Q := (residueCard_coprime U hℓ hne).pow_right _
  let a : ℤ := Nat.gcdA ℓ Q
  let b : ℤ := Nat.gcdB ℓ Q
  have hab : (ℓ : ℤ) * a + (Q : ℤ) * b = 1 := by
    have h := Nat.gcd_eq_gcd_ab ℓ Q
    rw [hcop.gcd_eq_one] at h
    exact h.symm
  refine ⟨ρ ^ a, ?_⟩
  intro x hx
  have hxQ : θ x ^ Q = 1 := principal_character_pow_eq_one U θ hm hθ.trivial x hx
  have hρx := DFunLike.congr_fun hρ x
  rw [ContinuousQuasiChar.pow_apply] at hρx
  change ρ (normUnits F U x) = θ x ^ ℓ at hρx
  change θ x / (ρ ^ a) (normUnits F U x) = 1
  rw [quasiChar_zpow_apply]
  rw [hρx, div_eq_one]
  calc
    θ x = θ x ^ ((ℓ : ℤ) * a + (Q : ℤ) * b) := by rw [hab, zpow_one]
    _ = (θ x ^ ℓ) ^ a := by
      rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hxQ,
        one_zpow, mul_one]

end EdgeReduction

section Towers
variable (F U K : Type) [Field F] [Field U] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F U] [Algebra U K] [Algebra F K] [IsScalarTower F U K]
  [ValuativeExtension F U] [ValuativeExtension U K] [ValuativeExtension F K]
  [Module.Finite F U] [Module.Finite U K] [Module.Finite F K]

private theorem normQuasiChar_tower (lam : ContinuousQuasiChar F) :
    normQuasiChar U K (normQuasiChar F U lam) = normQuasiChar F K lam := by
  apply ContinuousMonoidHom.ext
  intro x
  change lam (normUnits F U (normUnits U K x)) = lam (normUnits F K x)
  congr 1
  apply Units.ext
  exact Basic.norm_tower (F := F) (L := U) (x := (x : K))

private theorem lower_not_descends (θ : ContinuousQuasiChar U) (Θ : ContinuousQuasiChar K)
    (hc : normQuasiChar U K θ = Θ)
    (hprimitive : ¬ ∃ lam : ContinuousQuasiChar F, normQuasiChar F K lam = Θ) :
    ¬ ∃ lam : ContinuousQuasiChar F, normQuasiChar F U lam = θ := by
  rintro ⟨lam, hlam⟩
  apply hprimitive
  refine ⟨lam, ?_⟩
  rw [← normQuasiChar_tower F U K, hlam, hc]

omit [Module.Finite F U] [Module.Finite U K] [Module.Finite F K] in
private theorem ramificationIndex_tower :
    ramificationIndex F K = ramificationIndex F U * ramificationIndex U K := by
  obtain ⟨x, hx⟩ := exists_ord_eq F 1
  have h := congrArg (ord K) (IsScalarTower.algebraMap_apply F U K x)
  rw [ord_algebraMap, ord_algebraMap, ord_algebraMap, hx] at h
  simp only [← WithTop.coe_nsmul, nsmul_eq_mul] at h
  have hcast := WithTop.coe_injective h
  have hi : (ramificationIndex F K : ℤ) =
      (ramificationIndex F U : ℤ) * ramificationIndex U K := by
    simpa only [mul_one] using hcast.trans (mul_comm _ _)
  exact_mod_cast hi

end Towers

section Twisting
variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]

private theorem normQuasiChar_div (θ lam : ContinuousQuasiChar F) :
    normQuasiChar F K (θ / lam) = normQuasiChar F K θ / normQuasiChar F K lam := by
  ext x; rfl

private theorem twist_not_descends (Θ : ContinuousQuasiChar K)
    (hprimitive : ¬ ∃ lam : ContinuousQuasiChar F, normQuasiChar F K lam = Θ)
    (lam : ContinuousQuasiChar F) :
    ¬ ∃ ρ : ContinuousQuasiChar F,
      normQuasiChar F K ρ = Θ / normQuasiChar F K lam := by
  rintro ⟨ρ, hρ⟩
  apply hprimitive
  refine ⟨ρ * lam, ?_⟩
  apply ContinuousMonoidHom.ext
  intro x
  have hx := DFunLike.congr_fun hρ x
  change ρ (normUnits F K x) = Θ x / lam (normUnits F K x) at hx
  change ρ (normUnits F K x) * lam (normUnits F K x) = Θ x
  rw [hx, div_mul_cancel]

end Twisting

section ExactPullback
variable (F U K : Type) [Field F] [Field U] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F U] [Algebra U K]
  [ValuativeExtension F U] [ValuativeExtension U K]
  [Module.Finite F U] [Module.Finite U K] [PrimeCyclicExtension U K]

private theorem conductor_one_pullback
    (P : PrimeCyclicPreparation U K) (htame : IsTamelyRamified U K)
    (χ : ContinuousQuasiChar U) (hχ : IsMultiplicativeConductor U χ 1)
    (D : Characters.ConjugateTwistData F U K χ) :
    IsMultiplicativeConductor K (normQuasiChar U K χ) 1 := by
  let chiU : LocalQuasiCharData U := ⟨χ, 1, hχ⟩
  let chiK := canonicalLocalQuasiCharData K (normQuasiChar U K χ)
  have ht := P.isLowerBreak_zero_of_isTamelyRamified U K htame
  have hminimal : ∀ (mu : NormCharacter U K) (q : ℕ),
      IsMultiplicativeConductor U (mu.1 * χ) q → 1 ≤ q := by
    intro mu q hq
    obtain ⟨σ, hσ⟩ := D.quotientEquiv.surjective mu
    have hconj := conjugate_isConductor F U σ hχ
    rw [D.conjugate_eq_twist, hσ] at hconj
    have hcomm : χ * mu.1 = mu.1 * χ := by
      apply ContinuousMonoidHom.ext
      intro x
      change χ x * mu.1 x = mu.1 x * χ x
      exact mul_comm _ _
    rw [hcomm] at hconj
    exact Nat.le_of_eq (hconj.unique hq)
  have heq := chiU.conductor_compNorm_eq_of_minimalOrbit U K ht
    P.hres P.piK P.hpiK P.hgen chiK rfl (by change 1 ≤ 0 + 1; omega) hminimal
  have hc := chiK.isConductor
  rw [heq] at hc
  exact hc

end ExactPullback

section TamePreparation
variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

private theorem primeDegree_tame (P : PrimeCyclicPreparation F K)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hdegree : Module.finrank F K = ℓ)
    (hchar : ℓ ≠ residueCharacteristic F) : IsTamelyRamified F K := by
  change ¬ residueCharacteristic F ∣ ramificationIndex F K
  rw [P.ramificationIndex_eq_degree, hdegree]
  intro hdiv
  rcases (Nat.dvd_prime hℓ).1 hdiv with h | h
  · exact (residueCharacteristic_prime F).ne_one h
  · exact hchar h.symm

end TamePreparation

section Diamond
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

set_option maxHeartbeats 800000 in
/-- **The common base twist in the tame diamond**, paper lines 932–955.

The input is an actual compatible primitive pair in a `C_ℓ × C_ℓ` local
extension, with `U/F` unramified and `ℓ` different from the residue
characteristic.  The other lower field is specified by its distinct norm
subgroup, as in `Characters.conjugacy`.  Its ramification and the
unramifiedness of `K/E` are derived in the proof.

For `m > 1`, the same continuous base character removes the higher
conductor on both sides.  The remaining pair and its common pullback have
conductor exactly one and remain non-descending.  The two base pullbacks
have exact conductors `m` and `1 + ℓ(m-1)`; the integer equality records the
latter without truncated integer depths. -/
theorem tame_commonTwist
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hchar : ℓ ≠ residueCharacteristic F)
    (hG : Nonempty (Gal(K/F) ≃*
      (Multiplicative (ZMod ℓ) × Multiplicative (ZMod ℓ))))
    (U E : IntermediateField F K)
    (hU : Module.finrank F U = ℓ) (hE : Module.finrank F E = ℓ)
    (hne : Ramification.intermediateNormRange U ≠ Ramification.intermediateNormRange E) :
    letI := Basic.intermediateFieldValuativeRel U
    letI := Basic.intermediateFieldTopology U
    letI := Basic.intermediateField_localField U
    letI := Basic.intermediateField_lowerValuativeExtension U
    letI := Basic.intermediateField_upperValuativeExtension U
    letI := Basic.intermediateFieldValuativeRel E
    letI := Basic.intermediateFieldTopology E
    letI := Basic.intermediateField_localField E
    letI := Basic.intermediateField_lowerValuativeExtension E
    letI := Basic.intermediateField_upperValuativeExtension E
    ramificationIndex F U = 1 →
    ∀ (θU : ContinuousQuasiChar U) (θE : ContinuousQuasiChar E)
      (Θ : ContinuousQuasiChar K) (m : ℕ),
      IsMultiplicativeConductor U θU m → 1 < m →
      normQuasiChar U K θU = Θ → normQuasiChar E K θE = Θ →
      (¬ ∃ ρ : ContinuousQuasiChar F, normQuasiChar F K ρ = Θ) →
      ∃ (lam : ContinuousQuasiChar F) (χU : ContinuousQuasiChar U)
        (χE : ContinuousQuasiChar E) (Ξ : ContinuousQuasiChar K),
        θU = χU * normQuasiChar F U lam ∧
        θE = χE * normQuasiChar F E lam ∧
        normQuasiChar U K χU = Ξ ∧ normQuasiChar E K χE = Ξ ∧
        (¬ ∃ ρ : ContinuousQuasiChar F, normQuasiChar F K ρ = Ξ) ∧
        IsMultiplicativeConductor U χU 1 ∧
        IsMultiplicativeConductor E χE 1 ∧
        IsMultiplicativeConductor K Ξ 1 ∧
        IsMultiplicativeConductor F lam m ∧
        IsMultiplicativeConductor U (normQuasiChar F U lam) m ∧
        IsMultiplicativeConductor E (normQuasiChar F E lam) (ℓ * (m - 1) + 1) ∧
        IsMultiplicativeConductor E θE (ℓ * (m - 1) + 1) ∧
        ((ℓ * (m - 1) + 1 : ℕ) : ℤ) = 1 + (ℓ : ℤ) * ((m : ℤ) - 1) := by
  letI := Basic.intermediateFieldValuativeRel U
  letI := Basic.intermediateFieldTopology U
  letI := Basic.intermediateField_localField U
  letI := Basic.intermediateField_lowerValuativeExtension U
  letI := Basic.intermediateField_upperValuativeExtension U
  letI := Basic.intermediateFieldValuativeRel E
  letI := Basic.intermediateFieldTopology E
  letI := Basic.intermediateField_localField E
  letI := Basic.intermediateField_lowerValuativeExtension E
  letI := Basic.intermediateField_upperValuativeExtension E
  intro hunr θU θE Θ m hθU hm hcU hcE hprimitive
  have dataU := Basic.intermediateField_tower_compatible hℓ hG U hU
  have dataE := Basic.intermediateField_tower_compatible hℓ hG E hE
  have hUK := dataU.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F U
    dataU.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension U K
    dataU.2.2.2.2.2.2.2.2.2.2.2.2
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E
    dataE.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension E K
    dataE.2.2.2.2.2.2.2.2.2.2.2.2
  have hresU : residueDegree F U = ℓ := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F U
    rw [hunr, one_mul, hU] at h
    exact h.symm
  have hramE : ramificationIndex F E ≠ 1 := by
    intro he
    have hresE : residueDegree F E = ℓ := by
      have h := finrank_eq_ramificationIndex_mul_residueDegree F E
      rw [he, one_mul, hE] at h
      exact h.symm
    apply hne
    change (normUnits F U).range = (normUnits F E).range
    ext x
    rw [mem_unramified_norm_range_iff_order_dvd F U hunr,
      mem_unramified_norm_range_iff_order_dvd F E he, hresU, hresE]
  let PE := primeCyclicPreparation F E hramE
  have hindexU := ramificationIndex_tower F U K
  have hindexE := ramificationIndex_tower F E K
  have heE : ramificationIndex F E = ℓ := PE.ramificationIndex_eq_degree.trans hE
  have hramUK : ramificationIndex U K ≠ 1 := by
    intro he
    rw [hunr, he, one_mul] at hindexU
    rw [hindexU, heE] at hindexE
    have := ramificationIndex_pos E K
    have := hℓ.two_le
    nlinarith
  let PU := primeCyclicPreparation U K hramUK
  have heUK : ramificationIndex U K = ℓ := PU.ramificationIndex_eq_degree.trans hUK
  have hunrEK : ramificationIndex E K = 1 := by
    rw [hunr, heUK, one_mul] at hindexU
    rw [hindexU, heE] at hindexE
    exact Nat.mul_left_cancel hℓ.pos (by simpa using hindexE.symm)
  have hcharU : ℓ ≠ residueCharacteristic U := by
    rwa [residueCharacteristic_extension_eq F U]
  have htameE := primeDegree_tame F E PE hℓ hE hchar
  have htameUK := primeDegree_tame U K PU hℓ hUK hcharU
  obtain ⟨DU⟩ := (Characters.conjugacy hℓ hG U E hU hE hne θU θE Θ hcU hcE hprimitive).1
  obtain ⟨lam, hlam⟩ := remove_principal_restriction F U K hℓ hU hcharU θU DU
    (by omega) hθU
  let χU := θU / normQuasiChar F U lam
  let χE := θE / normQuasiChar F E lam
  let Ξ := Θ / normQuasiChar F K lam
  have hχU : normQuasiChar U K χU = Ξ := by
    dsimp only [χU, Ξ]
    rw [normQuasiChar_div, normQuasiChar_tower F U K, hcU]
  have hχE : normQuasiChar E K χE = Ξ := by
    dsimp only [χE, Ξ]
    rw [normQuasiChar_div, normQuasiChar_tower F E K, hcE]
  have hΞprimitive : ¬ ∃ ρ : ContinuousQuasiChar F, normQuasiChar F K ρ = Ξ :=
    twist_not_descends F K Θ hprimitive lam
  have hχUprimitive := lower_not_descends F U K χU Ξ hχU hΞprimitive
  let chiU := canonicalLocalQuasiCharData U χU
  have hχUpos := tame_primitive_conductor_positive F U χU chiU.isConductor hχUprimitive
  have hχUle : chiU.conductor ≤ 1 := chiU.isConductor.minimal 1 hlam
  have hcondU : IsMultiplicativeConductor U χU 1 := by
    have heq : chiU.conductor = 1 := by omega
    have h := chiU.isConductor
    rw [heq] at h
    exact h
  obtain ⟨DχU⟩ :=
    (Characters.conjugacy hℓ hG U E hU hE hne χU χE Ξ hχU hχE hΞprimitive).1
  have hcondK : IsMultiplicativeConductor K Ξ 1 := by
    rw [← hχU]
    exact conductor_one_pullback F U K PU htameUK χU hcondU DχU
  have hcondE : IsMultiplicativeConductor E χE 1 := by
    apply (unramified_multiplicativeConductor_compNorm E K hunrEK χE 1).1
    change IsMultiplicativeConductor K (normQuasiChar E K χE) 1
    rw [hχE]
    exact hcondK
  have hprodU : θU = χU * normQuasiChar F U lam := by
    dsimp only [χU]
    exact (div_mul_cancel _ _).symm
  have hprodE : θE = χE * normQuasiChar F E lam := by
    dsimp only [χE]
    exact (div_mul_cancel _ _).symm
  have hcondPullU : IsMultiplicativeConductor U (normQuasiChar F U lam) m := by
    have h := hcondU.inv.mul_of_lt hθU hm
    have heq : χU⁻¹ * θU = normQuasiChar F U lam := by
      rw [hprodU, ← mul_assoc, inv_mul_cancel, one_mul]
    rwa [heq] at h
  have hcondLam : IsMultiplicativeConductor F lam m :=
    (unramified_multiplicativeConductor_compNorm F U hunr lam m).1 hcondPullU
  have htE := PE.isLowerBreak_zero_of_isTamelyRamified F E htameE
  have hcondPullE :
      IsMultiplicativeConductor E (normQuasiChar F E lam) (ℓ * (m - 1) + 1) := by
    change IsMultiplicativeConductor E
      (ContinuousQuasiChar.compNorm (R := F) (S := E) lam) (ℓ * (m - 1) + 1)
    have h := multiplicativeConductor_compNorm_high F E htE
      PE.hres PE.piK PE.hpiK PE.hgen (by omega) hcondLam
    simpa [herbrandPsiNat, hE] using h
  have hθE : IsMultiplicativeConductor E θE (ℓ * (m - 1) + 1) := by
    rw [hprodE]
    apply hcondE.mul_of_lt hcondPullE
    have := Nat.mul_pos hℓ.pos (show 0 < m - 1 by omega)
    omega
  refine ⟨lam, χU, χE, Ξ, hprodU, hprodE, hχU, hχE, hΞprimitive,
    hcondU, hcondE, hcondK, hcondLam, hcondPullU, hcondPullE, hθE, ?_⟩
  push_cast [Nat.cast_sub (by omega : 1 ≤ m)]
  ring

end Diamond

end
end LanglandsSecondMainLemma.Tame
