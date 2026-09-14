import Mathlib.Algebra.Category.Grp.Injective
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Classification.OddSelection
import LanglandsSecondMainLemma.Classification.QuadraticConductors
import LanglandsSecondMainLemma.Ramification.Inertia
import LanglandsSecondMainLemma.Characters.QuadraticProduct

/-!
# Classification / Exhaustion

Blueprint: blueprint/tasks/Classification/Exhaustion.md
Paper: U:dispatch

The inertia alternatives refer to the kernel of the actual residue action.
The cyclic residue quotient rules out trivial inertia; in the tame case
the cyclic tame quotient also rules out total inertia.

The dyadic proof constructs additive charts from the actual norm characters
before applying the conductor classification. The public result is the
seven-constructor predicate `LocalProofBranch`, with genuine fixed fields
and the complete break ledgers, proved by `exhaustion`.
-/

namespace LanglandsSecondMainLemma.Classification

noncomputable section

open LanglandsFirstMainLemma
open Ramification

open private galoisCard_eq_prime_sq card_eq_prime_of_ne_bot_ne_top
  inertiaLineDiamondBreaks finrank_fixedField_line from
  LanglandsSecondMainLemma.Ramification.DiamondBreaks
open private intermediateField_lower_cyclicPrime from LanglandsSecondMainLemma.Basic.Fields

/-- Divisibility of the character codomain supplies the algebraic extension
used to construct additive charts; continuity is proved separately below. -/
private abbrev complexUnitsDivisible : DivisibleBy (Additive ℂˣ) ℤ := by
  letI : DivisibleBy (Additive ℂˣ) ℕ := divisibleByOfSMulRightSurj _ _ (by
    intro n hn u
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u.toMul : ℂ) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, zero_pow hn] at hz
      exact u.toMul.ne_zero hz.symm
    refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
    apply congrArg Additive.ofMul
    exact Units.ext hz)
  exact AddGroup.divisibleByIntOfDivisibleByNat _

/-- Extend FML's additive character of the finite half-conductor lattice
quotient to the field. It kills the full conductor lattice, so the extension
is continuous. Negation gives the paper's `χ(1-x)` convention. -/
private theorem normCharacterChart
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (χ : ContinuousQuasiChar F) {t : ℕ} (ht : 0 < t)
    (hχ : IsMultiplicativeConductor F χ (t + 1)) :
    ∃ Ψ : ContinuousAddChar F,
      ∀ (x : F) (hx : x ∈ lattice F (((t / 2 + 1 : ℕ) : ℤ))),
        χ (principalUnitOf F (t / 2) (-x) (neg_mem_lattice F hx)) = Ψ x := by
  let C : LocalQuasiCharData F := ⟨χ, t + 1, hχ⟩
  let r : ℕ := t / 2 + 1
  have hr : IsLamprechtStationaryDepth C.conductor r := ⟨by dsimp [C]; omega,
    by dsimp [C, r]; omega, by dsimp [C, r]; omega⟩
  let A := (stationaryLinearizationCharacterUnits F C hr).compAddMonoidHom
    (latticeQuotientMk F hr.int_le_conductor).toAddMonoidHom
  letI := complexUnitsDivisible
  obtain ⟨f, hf⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property_addMonoidHom
    (lattice F (r : ℤ)).subtype.toAddMonoidHom Subtype.val_injective A.toAddMonoidHom
  have hfval (x : lattice F (r : ℤ)) : f (x : F) = Additive.ofMul (A x) :=
    DFunLike.congr_fun hf x
  have hzero (x : F) (hx : x ∈ lattice F ((t + 1 : ℕ) : ℤ)) : f x = 0 := by
    let y : lattice F (r : ℤ) := ⟨x, lattice_antitone F hr.int_le_conductor hx⟩
    rw [show x = (y : F) from rfl, hfval]
    have hy : latticeQuotientMk F hr.int_le_conductor y = 0 := by
      exact (latticeQuotientMk_eq_zero_iff F hr.int_le_conductor).mpr hx
    change Additive.ofMul (stationaryLinearizationCharacterUnits F C hr
      (latticeQuotientMk F hr.int_le_conductor y)) = 0
    rw [hy, AddChar.map_zero_eq_one]
    rfl
  have hfcont : Continuous f := by
    apply continuous_of_continuousAt_zero f
    apply ContinuousAt.congr_of_eventuallyEq continuousAt_const
    filter_upwards [(lattice_isOpen F ((t + 1 : ℕ) : ℤ)).mem_nhds
      (show (0 : F) ∈ lattice F ((t + 1 : ℕ) : ℤ) by simp)] with x hx
    exact hzero x hx
  let Ψ : ContinuousAddChar F := ⟨AddChar.toAddMonoidHomEquiv.symm (-f),
    by exact continuous_toMul.comp (show Continuous (fun x => -f x) from hfcont.neg)⟩
  refine ⟨Ψ, ?_⟩
  intro x hx
  change χ _ = Additive.toMul ((-f) x)
  rw [AddMonoidHom.neg_apply, ← map_neg]
  exact (congrArg Additive.toMul (hfval ⟨-x, neg_mem_lattice F hx⟩)).symm

/-- Three distinct subgroup lines in the genuine biquadratic group. -/
private theorem three_lines {G : Type*} [Group G]
    (e : G ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    ∃ H : Fin 3 → Subgroup G,
      (∀ i, Nat.card (H i) = 2) ∧ Function.Injective H := by
  let g : Fin 3 → Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
    ![(Multiplicative.ofAdd 1, 1), (1, Multiplicative.ofAdd 1),
      (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)]
  have hg : ∀ i, orderOf (g i) = 2 := by
    intro i
    apply orderOf_eq_prime
    · fin_cases i <;> decide
    · fin_cases i <;> decide
  have hne : ∀ i, g i ≠ 1 := by intro i; fin_cases i <;> decide
  have hginj : Function.Injective g := by decide
  let J : Fin 3 → Subgroup (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    fun i => Subgroup.zpowers (g i)
  have hJ : ∀ i, Nat.card (J i) = 2 := by
    intro i
    exact (Nat.card_zpowers (g i)).trans (hg i)
  have hJinj : Function.Injective J := by
    intro i j hij
    have hmem : g i ∈ J j := hij ▸ Subgroup.mem_zpowers (g i)
    rw [mem_zpowers_iff_mem_range_orderOf, hg j] at hmem
    obtain ⟨a, ha, hval⟩ := Finset.mem_image.mp hmem
    have halt : a = 0 ∨ a = 1 := by have := Finset.mem_range.mp ha; omega
    have hijv : g i = 1 ∨ g i = g j := by
      rcases halt with rfl | rfl
      · exact Or.inl (by simpa using hval.symm)
      · exact Or.inr (by simpa using hval.symm)
    exact hginj (hijv.resolve_left (hne i))
  refine ⟨fun i => (J i).comap e.toMonoidHom, ?_, ?_⟩
  · intro i
    change Nat.card ((J i).comap e.toMonoidHom) = 2
    rw [Subgroup.comap_equiv_eq_map_symm']
    exact (Nat.card_congr (e.symm.subgroupMap (J i)).toEquiv).symm.trans (hJ i)
  · intro i j hij
    exact hJinj (Subgroup.comap_injective e.surjective hij)

section QuadraticEdges

variable (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Algebra F E] [ValuativeExtension F E]
  [Module.Finite F E] [PrimeCyclicExtension F E]

/-- The auxiliary choices for one quadratic edge, including its actual
nontrivial norm character and a constructed whole-ideal additive chart. -/
private structure QuadraticEdgeData (t : ℕ) where
  lowerBreak : PrimeCyclicExtension.IsLowerBreak F E t
  positive : 0 < t
  residue : residueDegree F E = 1
  degree : Module.finrank F E = 2
  pi : ringOfIntegers E
  uniformizer : (ValuativeRel.valuation E).IsUniformizer (pi : E)
  generates : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers E)) = ⊤
  tau : NormCharacter F E
  nontrivial : tau ≠ 1
  conductor : IsMultiplicativeConductor F tau.1 (t + 1)
  psi : ContinuousAddChar F
  chart : ∀ (x : F) (hx : x ∈ lattice F (((t / 2 + 1 : ℕ) : ℤ))),
    tau.1 (principalUnitOf F (t / 2) (-x) (neg_mem_lattice F hx)) = psi x

private def quadraticEdgeData {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hpos : 0 < t)
    (hres : residueDegree F E = 1) (hdeg : Module.finrank F E = 2)
    (tau : NormCharacter F E) (hne : tau ≠ 1) : QuadraticEdgeData F E t := by
  let hpiExists :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one F E hres
  let pi := hpiExists.choose
  have hpi := hpiExists.choose_spec.1
  have hgen := hpiExists.choose_spec.2
  have hc := ramifiedNormCharacter_conductor F E ht hres pi hpi hgen tau hne
  let hpsiExists := normCharacterChart F tau.1 hpos hc
  exact ⟨ht, hpos, hres, hdeg, pi, hpi, hgen, tau, hne, hc,
    hpsiExists.choose, hpsiExists.choose_spec⟩

open private primeNormCards from LanglandsSecondMainLemma.Characters.CrossedNorm

private theorem quadraticEdgeData_exists {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hpos : 0 < t)
    (hres : residueDegree F E = 1) (hdeg : Module.finrank F E = 2) :
    Nonempty (QuadraticEdgeData F E t) := by
  have hc : Nat.card (NormCharacter F E) = 2 := (primeNormCards F E).2.trans hdeg
  obtain ⟨tau, hne, _⟩ := (Nat.card_eq_two_iff' (1 : NormCharacter F E)).mp hc
  exact ⟨quadraticEdgeData F E ht hpos hres hdeg tau hne⟩

open private quadraticConductorShape from
  LanglandsSecondMainLemma.Classification.QuadraticConductors

private theorem QuadraticEdgeData.shape [CharZero F] {t : ℕ}
    (D : QuadraticEdgeData F E t) (hchar : residueCharacteristic F = 2)
    (e : ℕ) (he : ord F (2 : F) = ((e : ℤ) : WithTop ℤ)) :
    (∃ a : ℕ, 1 ≤ a ∧ a ≤ e ∧ t + 1 = 2 * a) ∨ t + 1 = 2 * e + 1 :=
  (quadraticConductorShape F E hchar e he D.lowerBreak D.positive D.residue
    D.degree D.pi D.uniformizer D.generates D.tau D.nontrivial D.psi D.chart).2

private theorem QuadraticEdgeData.odd_break [CharP F 2] {t : ℕ}
    (D : QuadraticEdgeData F E t) (hchar : residueCharacteristic F = 2) : Odd t := by
  rcases Nat.even_or_odd t with heven | hodd
  · have hodd : Odd (t + 1) := heven.add_odd (by decide)
    have hz := (Dyadic.UR.oddConductor F E hchar D.lowerBreak D.positive D.residue
      D.degree D.pi D.uniformizer D.generates D.tau D.nontrivial D.psi D.chart hodd).1
    letI : CharZero F := hz
    have htwo : (2 : F) ≠ 0 := by norm_num
    exact (htwo (CharP.cast_eq_zero F 2)).elim
  · exact hodd

end QuadraticEdges

private theorem QuadraticEdgeData.maximal_product
    (F E₁ E₂ : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    [Field E₁] [ValuativeRel E₁] [TopologicalSpace E₁]
    [IsNonarchimedeanLocalField E₁] [Algebra F E₁] [ValuativeExtension F E₁]
    [Module.Finite F E₁] [PrimeCyclicExtension F E₁]
    [Field E₂] [ValuativeRel E₂] [TopologicalSpace E₂]
    [IsNonarchimedeanLocalField E₂] [Algebra F E₂] [ValuativeExtension F E₂]
    [Module.Finite F E₂] [PrimeCyclicExtension F E₂]
    {t₁ t₂ : ℕ} (D₁ : QuadraticEdgeData F E₁ t₁) (D₂ : QuadraticEdgeData F E₂ t₂)
    (hchar : residueCharacteristic F = 2)
    (e : ℕ) (he : ord F (2 : F) = ((e : ℤ) : WithTop ℤ))
    (h₁ : t₁ + 1 = 2 * e + 1) (h₂ : t₂ + 1 = 2 * e + 1) :
    multiplicativeConductorExponent F (D₁.tau.1 * D₂.tau.1) ≤ 2 * e :=
  ((quadraticConductors F E₁ E₂ hchar e he
    D₁.lowerBreak D₁.positive D₁.residue D₁.degree D₁.pi D₁.uniformizer D₁.generates
    D₁.tau D₁.nontrivial D₁.psi D₁.chart
    D₂.lowerBreak D₂.positive D₂.residue D₂.degree D₂.pi D₂.uniformizer D₂.generates
    D₂.tau D₂.nontrivial D₂.psi D₂.chart).2.2 ⟨h₁, h₂⟩).2.2

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

private theorem primeSquare_not_cyclic {G : Type*} [Group G] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hG : Nonempty
      (G ≃* (Multiplicative (ZMod ℓ) × Multiplicative (ZMod ℓ)))) :
    ¬ IsCyclic G := by
  intro hcyc
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  letI : IsCyclic G := hcyc
  letI : IsCyclic (Multiplicative (ZMod ℓ) × Multiplicative (ZMod ℓ)) :=
    isCyclic_of_surjective hG.some.toMonoidHom hG.some.surjective
  have hc := coprime_card_of_isCyclic_prod
    (Multiplicative (ZMod ℓ)) (Multiplicative (ZMod ℓ))
  have hcard : Nat.card (Multiplicative (ZMod ℓ)) = ℓ :=
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod ℓ)
  rw [hcard, Nat.coprime_self] at hc
  exact hℓ.ne_one hc

/-- In a prime-square local diamond inertia is either a line or the full
group. The latter case is exactly total ramification. This is the first
step of the proof of paper Lemma `U:dispatch`. -/
theorem inertiaDichotomy {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod ℓ) × Multiplicative (ZMod ℓ)))) :
    Nat.card (inertiaSubgroup (F := F) (K := K)) = ℓ ∨
      (inertiaSubgroup (F := F) (K := K) = ⊤ ∧ residueDegree F K = 1) := by
  have hbot : inertiaSubgroup (F := F) (K := K) ≠ ⊥ := by
    intro h
    have hc := residueActionQuotient_cyclic (F := F) (K := K)
    letI := hc
    let e := (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot
    exact primeSquare_not_cyclic hℓ hG
      (isCyclic_of_surjective e.toMonoidHom e.surjective)
  by_cases htop : inertiaSubgroup (F := F) (K := K) = ⊤
  · right
    refine ⟨htop, ?_⟩
    letI : Module.Finite (ResidueField F) (ResidueField K) := Module.Finite.of_finite
    rw [residueDegree_eq_finrank_residueField, ← IsGalois.card_aut_eq_finrank,
      ← Nat.card_congr (residueActionQuotientEquiv (F := F) (K := K)).toEquiv,
      ← Subgroup.index_eq_card, htop, Subgroup.index_top]
  · exact Or.inl (card_eq_prime_of_ne_bot_ne_top hℓ hG _ hbot htop)

private theorem wildInertia_eq_bot_of_ne {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod ℓ) × Multiplicative (ZMod ℓ))))
    (hne : ℓ ≠ residueCharacteristic F) :
    lowerRamificationGroup F K 1 = ⊥ := by
  letI : Fact (residueCharacteristic F).Prime := ⟨residueCharacteristic_prime F⟩
  obtain ⟨n, hn⟩ := (wildInertia_isPGroup (F := F) (K := K)).exists_card_eq
  have hdiv := Subgroup.card_subgroup_dvd_card (lowerRamificationGroup F K 1)
  rw [galoisCard_eq_prime_sq hG, hn] at hdiv
  have hcop : Nat.Coprime (residueCharacteristic F) ℓ :=
    (residueCharacteristic_prime F).coprime_iff_not_dvd.mpr
      (fun h => hne ((Nat.prime_dvd_prime_iff_eq
        (residueCharacteristic_prime F) hℓ).mp h).symm)
  have hone : Nat.card (lowerRamificationGroup F K 1) = 1 := by
    rw [hn]
    exact ((hcop.pow_left n).pow_right 2).eq_one_of_dvd hdiv
  exact Subgroup.card_eq_one.mp hone

private theorem tameInertia_injective
    (hwild : lowerRamificationGroup F K 1 = ⊥) :
    Function.Injective (tameInertiaHom (F := F) (K := K)) := by
  apply (injective_iff_map_eq_one (tameInertiaHom (F := F) (K := K))).mpr
  intro σ hσ
  apply Subtype.ext
  have hmem := (tameInertiaHom_eq_one_iff (F := F) (K := K) σ).mp hσ
  simpa only [hwild, Subgroup.mem_bot, Subgroup.coe_one] using hmem

/-- The tame branch has inertia of order `ℓ`, and Frobenius conjugation
forces the root-of-unity condition `ℓ ∣ |k_F| - 1` in the base residue
field, not merely in the upstairs residue field. -/
theorem tameInertiaData {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod ℓ) × Multiplicative (ZMod ℓ))))
    (hne : ℓ ≠ residueCharacteristic F) :
    Nat.card (inertiaSubgroup (F := F) (K := K)) = ℓ ∧
      lowerRamificationGroup F K 1 = ⊥ ∧ ℓ ∣ residueCard F - 1 := by
  have hwild := wildInertia_eq_bot_of_ne hℓ hG hne
  have hinj := tameInertia_injective hwild
  have hcyc : IsCyclic (lowerRamificationGroup F K 0) :=
    isCyclic_of_injective (tameInertiaHom (F := F) (K := K)) hinj
  have hI : Nat.card (inertiaSubgroup (F := F) (K := K)) = ℓ := by
    rcases inertiaDichotomy hℓ hG with hI | ⟨htop, _⟩
    · exact hI
    · rw [inertiaSubgroup_eq_lowerRamificationGroup_zero] at htop
      rw [htop] at hcyc
      letI := hcyc
      exact (primeSquare_not_cyclic hℓ hG
        (isCyclic_of_surjective (⊤ : Subgroup Gal(K/F)).subtype
          (by intro σ; exact ⟨⟨σ, trivial⟩, rfl⟩))).elim
  refine ⟨hI, hwild, ?_⟩
  letI := hcyc
  have hcard : Nat.card (lowerRamificationGroup F K 0) = ℓ := by
    rwa [inertiaSubgroup_eq_lowerRamificationGroup_zero] at hI
  have hpow : ∀ σ : lowerRamificationGroup F K 0,
      σ ^ (residueCard F - 1) = 1 := by
    intro σ
    obtain ⟨φ, hφ⟩ := residueAction_surjective
      (F := F) (K := K) (residueFrobenius (F := F) (K := K))
    have hcomm : φ * (σ : Gal(K/F)) = (σ : Gal(K/F)) * φ := by
      apply hG.some.injective
      simp only [map_mul, mul_comm]
    have hconj : conjugateInertia φ σ = σ := by
      apply Subtype.ext
      simp only [conjugateInertia_coe, hcomm, mul_inv_cancel_right]
    have hq : σ = σ ^ residueCard F := by
      apply hinj
      rw [map_pow, ← tameInertiaHom_conjugate φ σ hφ, hconj]
    have hqpos : 0 < residueCard F := by
      exact (one_lt_residueCard F).trans' Nat.zero_lt_one
    have heq : σ ^ (residueCard F - 1) * σ = 1 * σ := by
      rw [← pow_succ, Nat.sub_add_cancel hqpos, ← hq, one_mul]
    exact mul_right_cancel heq
  rw [← hcard, ← IsCyclic.exponent_eq_card]
  exact Monoid.exponent_dvd_of_forall_pow_eq_one hpow

/-- The unramified inertia field and every ramified lower field, with the
break unchanged by unramified base change. The final equivalence records
exactly when the common edge break is tame (zero). -/
structure InertiaLineClassification {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod ℓ) × Multiplicative (ZMod ℓ))))
    (hI : Nat.card (inertiaSubgroup (F := F) (K := K)) = ℓ)
    extends InertiaLineDiamondBreaks hℓ hG hI where
  break_type : ∀ (H : Subgroup Gal(K/F)) (hH : Nat.card H = ℓ),
    H ≠ inertiaSubgroup (F := F) (K := K) →
      ∃ t : ℕ, UnramifiedBaseChangeBreakPair hℓ hG hI H hH t ∧
        (t = 0 ↔ ℓ ≠ residueCharacteristic F)

/-- Construct all the unramified--ramified classifier data from actual
inertia. FML's positive-break criterion supplies the tame/wild boundary. -/
theorem inertiaLineClassification {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod ℓ) × Multiplicative (ZMod ℓ))))
    (hI : Nat.card (inertiaSubgroup (F := F) (K := K)) = ℓ) :
    Nonempty (InertiaLineClassification hℓ hG hI) := by
  let D := inertiaLineDiamondBreaks hℓ hG hI
  refine ⟨{ toInertiaLineDiamondBreaks := D, break_type := ?_ }⟩
  intro H hH hne
  obtain ⟨t, ht⟩ := D.ramified_lower H hH hne
  refine ⟨t, ht, ?_⟩
  let E := IntermediateField.fixedField H
  letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E
  letI : TopologicalSpace E := Basic.intermediateFieldTopology E
  letI : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E
  letI : ValuativeExtension F E := Basic.intermediateField_lowerValuativeExtension E
  have hdegree : Module.finrank F E = ℓ :=
    finrank_fixedField_line hℓ hG H hH
  letI : PrimeCyclicExtension F E := PrimeCyclicExtension.ofCyclicPrimeExtension F E
    (intermediateField_lower_cyclicPrime hℓ hG.some E hdegree)
  have hres : residueDegree F E = 1 := ht.1
  have hbreak : PrimeCyclicExtension.IsLowerBreak F E t := ht.2.2.1
  obtain ⟨pi, hpi, hgen⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one F E hres
  constructor
  · intro ht0 heq
    have hram : ramificationIndex F E = ℓ := by
      have h := finrank_eq_ramificationIndex_mul_residueDegree F E
      rwa [hdegree, hres, mul_one, eq_comm] at h
    have htame := isTamelyRamified_of_isLowerBreak_zero F E hres pi hpi hgen (ht0 ▸ hbreak)
    exact htame (by rw [hram, heq])
  · intro htame
    by_contra ht0
    have hc := residueCharacteristic_eq_degree_of_positive_isLowerBreak F E
      hbreak (Nat.pos_of_ne_zero ht0) pi hpi hgen
    exact htame (hc.trans hdegree).symm

section TotalDyadic

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

local instance (L : IntermediateField F K) : ValuativeRel L :=
  Basic.intermediateFieldValuativeRel L
local instance (L : IntermediateField F K) : TopologicalSpace L :=
  Basic.intermediateFieldTopology L
local instance (L : IntermediateField F K) : IsNonarchimedeanLocalField L :=
  Basic.intermediateField_localField L
local instance (L : IntermediateField F K) : ValuativeExtension F L :=
  Basic.intermediateField_lowerValuativeExtension L
local instance (L : IntermediateField F K) : ValuativeExtension L K :=
  Basic.intermediateField_upperValuativeExtension L

open private finrank_fixedField_line residueDegree_mul from
  LanglandsSecondMainLemma.Ramification.DiamondBreaks
open private intermediateField_lower_cyclicPrime intermediateField_lower_isGalois from
  LanglandsSecondMainLemma.Basic.Fields
open private exists_line_ne from LanglandsSecondMainLemma.Odd.Total.Setup

private theorem lowerField_residue_one (hres : residueDegree F K = 1)
    (L : IntermediateField F K) : residueDegree F L = 1 := by
  have h := residueDegree_mul L
  rw [hres] at h
  exact (mul_eq_one.mp h).1

private theorem lineEdgeData_exists
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (hres : residueDegree F K = 1)
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = 2)
    {t u : ℕ} (hpos : 0 < t) (ht : IntermediateBreakPair Nat.prime_two hG H hH t u) :
    letI : PrimeCyclicExtension F (IntermediateField.fixedField H) :=
      PrimeCyclicExtension.ofCyclicPrimeExtension F (IntermediateField.fixedField H)
        (intermediateField_lower_cyclicPrime Nat.prime_two hG.some _
          (finrank_fixedField_line Nat.prime_two hG H hH))
    Nonempty (QuadraticEdgeData F (IntermediateField.fixedField H) t) := by
  letI : PrimeCyclicExtension F (IntermediateField.fixedField H) :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F (IntermediateField.fixedField H)
      (intermediateField_lower_cyclicPrime Nat.prime_two hG.some _
        (finrank_fixedField_line Nat.prime_two hG H hH))
  apply quadraticEdgeData_exists F (IntermediateField.fixedField H)
    (t := t) _ hpos (lowerField_residue_one hres _)
    (finrank_fixedField_line Nat.prime_two hG H hH)
  exact ht.1

/-- Three actual lower characters cannot all have maximal conductor.
Their product relation is the accepted theorem for these fixed fields. -/
private theorem not_all_maximal [CharZero F]
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = 2)
    (e : ℕ) (he : ord F (2 : F) = ((e : ℤ) : WithTop ℤ))
    (hepos : 0 < e)
    (hall : ∀ (H : Subgroup Gal(K/F)) (hH : Nat.card H = 2),
      ∃ u, IntermediateBreakPair Nat.prime_two hG H hH (2 * e) u) : False := by
  obtain ⟨H, hH, hHinj⟩ := three_lines hG.some
  let L : Fin 3 → IntermediateField F K := fun i => IntermediateField.fixedField (H i)
  have hdegree (i : Fin 3) : Module.finrank F (L i) = 2 :=
    finrank_fixedField_line Nat.prime_two hG (H i) (hH i)
  have hinj : Function.Injective L := by
    intro i j hij
    apply hHinj
    have h := congrArg IntermediateField.fixingSubgroup hij
    simpa only [L, IntermediateField.fixingSubgroup_fixedField] using h
  letI : ∀ i, PrimeCyclicExtension F (L i) := fun i =>
    PrimeCyclicExtension.ofCyclicPrimeExtension F (L i)
      (intermediateField_lower_cyclicPrime Nat.prime_two hG.some (L i) (hdegree i))
  obtain ⟨ω, hω, hprod, _hinj, _hranges, _hcrossed⟩ :=
    Characters.quadraticProduct F hG L hdegree hinj
  have hbreak (i : Fin 3) : PrimeCyclicExtension.IsLowerBreak F (L i) (2 * e) := by
    obtain ⟨u, hu⟩ := hall (H i) (hH i)
    exact hu.1
  let D (i : Fin 3) : QuadraticEdgeData F (L i) (2 * e) :=
    quadraticEdgeData F (L i) (hbreak i) (by omega)
      (lowerField_residue_one hres (L i)) (hdegree i) (ω i) (hω i)
  have hbound := QuadraticEdgeData.maximal_product F (L 0) (L 1)
    (D 0) (D 1) hchar e he rfl rfl
  change multiplicativeConductorExponent F ((ω 0).1 * (ω 1).1) ≤ 2 * e at hbound
  rw [← hprod] at hbound
  have hc := (D 2).conductor
  have hcond := multiplicativeConductorExponent_eq_of_isConductor F _ hc
  change multiplicativeConductorExponent F (ω 2).1 = 2 * e + 1 at hcond
  omega

private theorem dyadic_field_characteristic (hchar : residueCharacteristic F = 2) :
    CharZero F ∨ CharP F 2 := by
  rcases CharP.exists' F with hzero | ⟨p, hp, hcharP⟩
  · exact Or.inl hzero
  · letI : CharP F p := hcharP
    letI : CharP (ringOfIntegers F) p :=
      (SubringClass.subtype (ringOfIntegers F)).charP
        (fun x y hxy => Subtype.ext hxy) p
    have hresidue : CharP (ResidueField F) p :=
      CharP.of_ringHom_of_ne_zero (residueMap F) p hp.out.ne_zero
    have hp2 : p = 2 := CharP.eq (ResidueField F) hresidue (ringChar.of_eq hchar)
    exact Or.inr (hp2 ▸ hcharP)

private theorem ord_two_exists [CharZero F] :
    ∃ e : ℕ, ord F (2 : F) = ((e : ℤ) : WithTop ℤ) := by
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp
    ((ord_ne_top_iff F).mpr (by norm_num : (2 : F) ≠ 0))
  have hnonneg : 0 ≤ ord F (2 : F) :=
    (ord_nonneg_iff_mem_integer F (2 : F)).mpr (by simp)
  have hvpos : 0 ≤ v := by rw [← hv] at hnonneg; exact_mod_cast hnonneg
  exact ⟨v.toNat, by rw [Int.toNat_of_nonneg hvpos]; exact hv.symm⟩

/-- The distinguished lower break is the smaller one. All other lower
breaks are the single value `s`; the accepted ledger retains both upper
breaks and their different exponents. -/
private theorem totalDyadicShapes
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = 2)
    (D : TotallyRamifiedDiamondBreaks Nat.prime_two hG) :
    let s := D.t + (D.b - D.t) / 2
    (CharP F 2 ∧ Odd D.t ∧ Odd s) ∨
      (CharZero F ∧ ∃ e a : ℕ,
        ord F (2 : F) = ((e : ℤ) : WithTop ℤ) ∧
        1 ≤ a ∧ a ≤ e ∧ D.t + 1 = 2 * a ∧
        (s = 2 * e ∨ ∃ r : ℕ, a ≤ r ∧ r ≤ e ∧ s + 1 = 2 * r)) := by
  let s := D.t + (D.b - D.t) / 2
  have hts : D.t ≤ s := Nat.le_add_right _ _
  obtain ⟨H, hH, hne⟩ := exists_line_ne Nat.prime_two hG D.H₀
  obtain ⟨s', hpair, _, hs', hb⟩ := D.other_breaks H hH hne
  have hs : s' = s := hs'
  subst s'
  letI : PrimeCyclicExtension F (IntermediateField.fixedField D.H₀) :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F (IntermediateField.fixedField D.H₀)
      (intermediateField_lower_cyclicPrime Nat.prime_two hG.some _
        (finrank_fixedField_line Nat.prime_two hG D.H₀ D.card_H₀))
  letI : PrimeCyclicExtension F (IntermediateField.fixedField H) :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F (IntermediateField.fixedField H)
      (intermediateField_lower_cyclicPrime Nat.prime_two hG.some _
        (finrank_fixedField_line Nat.prime_two hG H hH))
  let A := Classical.choice (lineEdgeData_exists hG hres D.H₀ D.card_H₀
    D.t_pos D.distinguished_breaks)
  let B := Classical.choice (lineEdgeData_exists hG hres H hH
    (D.t_pos.trans_le hts) hpair)
  rcases dyadic_field_characteristic (F := F) hchar with hzero | htwo
  · letI : CharZero F := hzero
    obtain ⟨e, he⟩ := ord_two_exists (F := F)
    have hshapeA := QuadraticEdgeData.shape F _ A hchar e he
    have hshapeB := QuadraticEdgeData.shape F _ B hchar e he
    have hsupper : s ≤ 2 * e := by
      rcases hshapeB with ⟨r, _, hr, heq⟩ | heq <;> omega
    have htmax : D.t + 1 ≠ 2 * e + 1 := by
      intro hmax
      have ht : D.t = 2 * e := by omega
      have hsmax : s = 2 * e := by omega
      have htpos := D.t_pos
      apply not_all_maximal hG hres hchar e he (by omega)
      intro J hJ
      by_cases hJ0 : J = D.H₀
      · subst J
        exact ⟨D.b, ht ▸ D.distinguished_breaks⟩
      · obtain ⟨v, hv, _, hvEq, _⟩ := D.other_breaks J hJ hJ0
        have hvmax : v = 2 * e := hvEq.trans hsmax
        exact ⟨D.t, hvmax ▸ hv⟩
    obtain ⟨a, hapos, hae, ha⟩ := hshapeA.resolve_right htmax
    refine Or.inr ⟨hzero, e, a, he, hapos, hae, ha, ?_⟩
    rcases hshapeB with ⟨r, _, hre, hr⟩ | hr
    · exact Or.inr ⟨r, by omega, hre, hr⟩
    · exact Or.inl (by omega)
  · letI : CharP F 2 := htwo
    exact Or.inl ⟨htwo, QuadraticEdgeData.odd_break F _ A hchar,
      QuadraticEdgeData.odd_break F _ B hchar⟩

end TotalDyadic

section Dispatch

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

/-- The seven field configurations of paper Lemma `U:dispatch`.

Inertia-line branches retain the actual inertia fixed field and every other
lower edge, including its tame/wild break boundary. Total branches retain
the distinguished subgroup and the universal lower/upper break ledger.
Writing `s = D.t + (D.b - D.t)/2`, the dyadic lower breaks are `D.t,s,s`.
In mixed characteristic the equations with `+ 1` say precisely that these
are `(2a-1,2e,2e)` or `(2a-1,2r-1,2r-1)`. All parameters are positive as
in the paper. The upper breaks and different formulas remain in `D`.

This is classifier data only. There are no comparison identities, auxiliary
stationary models, or hypotheses concerning local constants. -/
inductive LocalProofBranch : {ℓ : ℕ} → (hℓ : ℓ.Prime) →
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod ℓ) × Multiplicative (ZMod ℓ)))) → Prop
  | tame {ℓ : ℕ} {hℓ : ℓ.Prime} {hG}
      (different_primes : ℓ ≠ residueCharacteristic F)
      (hI : Nat.card (inertiaSubgroup (F := F) (K := K)) = ℓ)
      (wild_trivial : lowerRamificationGroup F K 1 = ⊥)
      (roots_of_unity : ℓ ∣ residueCard F - 1)
      (fields : InertiaLineClassification hℓ hG hI) : LocalProofBranch hℓ hG
  | oddUR {ℓ : ℕ} {hℓ : ℓ.Prime} {hG}
      (wild : residueCharacteristic F = ℓ) (odd_prime : 2 < ℓ)
      (hI : Nat.card (inertiaSubgroup (F := F) (K := K)) = ℓ)
      (fields : InertiaLineClassification hℓ hG hI) : LocalProofBranch hℓ hG
  | oddTotal {ℓ : ℕ} {hℓ : ℓ.Prime} {hG}
      (wild : residueCharacteristic F = ℓ) (odd_prime : 2 < ℓ)
      (total : residueDegree F K = 1)
      (D : Odd.Total.OddTotalBreakData hℓ hG) (prime_to_break : ¬ ℓ ∣ D.t)
      (all_other_fields : ∀ (H : Subgroup Gal(K/F)) (hH : Nat.card H = ℓ), H ≠ D.H₁ →
        ∃ t₂ delta : ℕ, D.t ≤ t₂ ∧ t₂ = D.t + delta ∧
          IntermediateBreakPair hℓ hG H hH t₂ D.t ∧ D.tPrime = D.t + ℓ * delta) :
      LocalProofBranch hℓ hG
  | dyadicUR {hG} (dyadic : residueCharacteristic F = 2)
      (hI : Nat.card (inertiaSubgroup (F := F) (K := K)) = 2)
      (fields : InertiaLineClassification Nat.prime_two hG hI) :
      LocalProofBranch Nat.prime_two hG
  | equalTotal {hG} (equal_characteristic : CharP F 2)
      (dyadic : residueCharacteristic F = 2) (total : residueDegree F K = 1)
      (D : TotallyRamifiedDiamondBreaks Nat.prime_two hG)
      (first_odd : Odd D.t) (other_odd : Odd (D.t + (D.b - D.t) / 2)) :
      LocalProofBranch Nat.prime_two hG
  | mixedMaximal {hG} (mixed_characteristic : CharZero F)
      (dyadic : residueCharacteristic F = 2) (total : residueDegree F K = 1)
      (D : TotallyRamifiedDiamondBreaks Nat.prime_two hG)
      (e a : ℕ) (two_order : ord F (2 : F) = ((e : ℤ) : WithTop ℤ))
      (a_pos : 1 ≤ a) (a_le_e : a ≤ e) (first_break : D.t + 1 = 2 * a)
      (other_breaks : D.t + (D.b - D.t) / 2 = 2 * e) :
      LocalProofBranch Nat.prime_two hG
  | mixedNonmaximal {hG} (mixed_characteristic : CharZero F)
      (dyadic : residueCharacteristic F = 2) (total : residueDegree F K = 1)
      (D : TotallyRamifiedDiamondBreaks Nat.prime_two hG)
      (e a r : ℕ) (two_order : ord F (2 : F) = ((e : ℤ) : WithTop ℤ))
      (a_pos : 1 ≤ a) (a_le_r : a ≤ r) (r_le_e : r ≤ e)
      (first_break : D.t + 1 = 2 * a)
      (other_breaks : D.t + (D.b - D.t) / 2 + 1 = 2 * r) :
      LocalProofBranch Nat.prime_two hG

/-- **Exhaustive local classification**, paper Lemma 14.3 (`U:dispatch`).
Every genuine `C_ℓ × C_ℓ` local extension supplies one of the seven proof
configurations. The statement quantifies over every prime and both field
characteristics; no character, conductor chart, or branch comparison is
assumed. The charts needed internally are constructed from the actual
quadratic norm characters. -/
theorem exhaustion {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod ℓ) × Multiplicative (ZMod ℓ)))) :
    LocalProofBranch hℓ hG := by
  by_cases hwild : ℓ = residueCharacteristic F
  · rcases inertiaDichotomy hℓ hG with hI | ⟨_hfull, hres⟩
    · let D := Classical.choice (inertiaLineClassification hℓ hG hI)
      by_cases htwo : ℓ = 2
      · subst htwo
        exact LocalProofBranch.dyadicUR hwild.symm hI D
      · exact LocalProofBranch.oddUR hwild.symm (lt_of_le_of_ne hℓ.two_le (Ne.symm htwo)) hI D
    · by_cases htwo : ℓ = 2
      · subst htwo
        let D := Classical.choice ((diamondBreaks Nat.prime_two hG hwild.symm).1 hres)
        rcases totalDyadicShapes hG hres hwild.symm D with ⟨hchar, ht, hs⟩ |
          ⟨hchar, e, a, he, ha, hae, ht, hs⟩
        · exact LocalProofBranch.equalTotal hchar hwild.symm hres D ht hs
        · rcases hs with hs | ⟨r, har, hre, hs⟩
          · exact LocalProofBranch.mixedMaximal hchar hwild.symm hres D e a he ha hae ht hs
          · exact LocalProofBranch.mixedNonmaximal hchar hwild.symm hres D e a r he ha har hre ht hs
      · have hodd : 2 < ℓ := lt_of_le_of_ne hℓ.two_le (Ne.symm htwo)
        obtain ⟨D, hprime, hothers⟩ := oddSelection hℓ hodd hG hres hwild.symm
        exact LocalProofBranch.oddTotal hwild.symm hodd hres D hprime hothers
  · obtain ⟨hI, htrivial, hroots⟩ := tameInertiaData hℓ hG hwild
    exact LocalProofBranch.tame hwild hI htrivial hroots
      (Classical.choice (inertiaLineClassification hℓ hG hI))

end Dispatch

end

end LanglandsSecondMainLemma.Classification
