import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Odd.Conductors.Descent
import LanglandsSecondMainLemma.Local.CharacterExtension

/-!
# Common base twist and exact conductor reduction

Paper Proposition 9.34 (`O:G:reduce`), with the setup at lines 4962–4982.
Deep norm-kernel descent constructs a character on the actual norm image
of the first endpoint's minimal unit layer. FML's exact above-break norm
images supply an open layer on which this character is trivial, so the
accepted character-extension theorem supplies a continuous base twist.

Removing this same twist from both endpoints preserves compatibility and
non-descent. The primitive lower bound and the high cyclic conductor
formula give both exact minimal conductors. The final implication retains
the integer difference in the transition inequality and the exact conductor
of the original second endpoint.
-/

namespace LanglandsSecondMainLemma.Odd.Conductors

open LanglandsFirstMainLemma

noncomputable section

section NormImage

variable {F E : Type*} [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

/-- A character killing the norm kernel on one unit layer extends from
that layer's honest norm image. The deep exact norm image proves the
continuity condition required by `Local.characterExtension`. -/
private theorem extend_from_norm_layer
    {s m : ℕ} (hs : PrimeCyclicExtension.IsLowerBreak F E s)
    (hres : residueDegree F E = 1) (ψ : ContinuousQuasiChar E)
    (hker : ∀ x : Eˣ, x ∈ unitFiltration E m → normUnits F E x = 1 → ψ x = 1) :
    ∃ lam : ContinuousQuasiChar F,
      ∀ x : Eˣ, x ∈ unitFiltration E m → lam (normUnits F E x) = ψ x := by
  let U := unitFiltration E m
  let f : U →* Fˣ := (normUnits F E).comp U.subtype
  let g : U →* ℂˣ := ψ.toMonoidHom.comp U.subtype
  have hker' : f.rangeRestrict.ker ≤ g.ker := by
    intro x hx
    apply hker x x.property
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  let η : f.range →* ℂˣ :=
    f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨g, hker'⟩
  have hη (x : U) : η (f.rangeRestrict x) = ψ (x : Eˣ) := by
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
  obtain ⟨d, hd⟩ := exists_quasiCharTrivialOnUnitFiltration E ψ
  let r := s + m + d + 1
  let q := herbrandPsiNat s (Module.finrank F E) r
  have hr : s < r := by dsimp [r]; omega
  have hmq : m ≤ q :=
    (show m ≤ r by dsimp [r]; omega).trans
      (self_le_herbrandPsiNat s (Module.finrank F E) Module.finrank_pos r)
  have hdq : d ≤ q :=
    (show d ≤ r by dsimp [r]; omega).trans
      (self_le_herbrandPsiNat s (Module.finrank F E) Module.finrank_pos r)
  obtain ⟨π, hπ, hgen⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one F E hres
  have himage : Subgroup.map (normUnits F E) (unitFiltration E q) =
      unitFiltration F r :=
    norm_unitFiltration_map_eq_aboveBreak F E hs hr hres π hπ hgen
  have hU : unitFiltration F r ≤ f.range := by
    intro u hu
    obtain ⟨x, hx, hxu⟩ := (show u ∈ Subgroup.map (normUnits F E)
      (unitFiltration E q) by rwa [himage])
    exact ⟨⟨x, unitFiltration_antitone E hmq hx⟩, hxu⟩
  have htrivial : η.comp (Subgroup.inclusion hU) = 1 := by
    apply MonoidHom.ext
    intro u
    obtain ⟨x, hx, hxu⟩ := (show (u : Fˣ) ∈ Subgroup.map (normUnits F E)
      (unitFiltration E q) by rw [himage]; exact u.property)
    let xU : U := ⟨x, unitFiltration_antitone E hmq hx⟩
    have heq : Subgroup.inclusion hU u = f.rangeRestrict xU :=
      Subtype.ext hxu.symm
    change η (Subgroup.inclusion hU u) = 1
    rw [heq, hη]
    exact hd x (unitFiltration_antitone E hdq hx)
  obtain ⟨lam, hlam⟩ := Local.characterExtension F f.range r
    (by dsimp [r]; omega) hU η htrivial
  refine ⟨lam, fun x hx => ?_⟩
  exact (DFunLike.congr_fun hlam (f.rangeRestrict ⟨x, hx⟩)).trans (hη ⟨x, hx⟩)

/-- Integer form of FML's high conductor formula for the canonical
conductor of the actual continuous norm pullback. -/
private theorem high_pullback_conductor
    {s a : ℕ} (hs : PrimeCyclicExtension.IsLowerBreak F E s)
    (hres : residueDegree F E = 1) {χ : ContinuousQuasiChar F}
    (ha : IsMultiplicativeConductor F χ a) (hhigh : s + 1 < a) :
    (multiplicativeConductorExponent E (normQuasiChar F E χ) : ℤ) =
      (Module.finrank F E : ℤ) * a -
        (((Module.finrank F E - 1) * (s + 1) : ℕ) : ℤ) := by
  obtain ⟨π, hπ, hgen⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one F E hres
  have h := multiplicativeConductor_compNorm_high F E hs hres π hπ hgen hhigh ha
  rw [multiplicativeConductorExponent_eq_of_isConductor E (normQuasiChar F E χ) h]
  exact highConductor_cast_eq_degree_mul_sub_different F E hhigh

/-- If removing a smaller-conductor character leaves a lower norm twist,
the base character lies strictly above the break. This uses the full
critical-successor image, without asserting surjectivity at the break. -/
private theorem transition_conductor
    {s m a : ℕ} (hs : PrimeCyclicExtension.IsLowerBreak F E s)
    (hres : residueDegree F E = 1)
    (ψ φ : ContinuousQuasiChar E) (lam : ContinuousQuasiChar F)
    (hψ : ψ = φ * normQuasiChar F E lam)
    (hφ : IsMultiplicativeConductor E φ m)
    (ha : IsMultiplicativeConductor E ψ a) (hsm : s + 1 ≤ m) (hma : m < a) :
    ∃ r : ℕ, IsMultiplicativeConductor F lam (1 + r) ∧ s < r ∧
      (a : ℤ) = 1 + s + (Module.finrank F E : ℤ) * ((r : ℤ) - s) := by
  have hpull : IsMultiplicativeConductor E (normQuasiChar F E lam) a := by
    have h := hφ.inv.mul_of_lt ha hma
    simpa only [hψ, inv_mul_cancel_left] using h
  obtain ⟨b, hb⟩ := exists_isMultiplicativeConductor F lam
  obtain ⟨π, hπ, hgen⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one F E hres
  have hhigh : s + 1 < b := by
    by_contra h
    have htriv := (quasiCharTrivialOnUnitFiltration_compNorm_iff_break_succ
      F E hs hres π hπ hgen lam).2 (hb.trivialOnUnitFiltration_iff.2 (by omega))
    have := hpull.minimal (s + 1) htriv
    omega
  let r := b - 1
  have hr : s < r := by dsimp [r]; omega
  have hb' : IsMultiplicativeConductor F lam (1 + r) := by
    convert hb using 1
    dsimp [r]
    omega
  have hexact := hpull.unique
    (multiplicativeConductor_compNorm_aboveBreak F E hs hres π hπ hgen hr
      (by simpa only [Nat.add_comm] using hb'))
  refine ⟨r, hb', hr, ?_⟩
  rw [hexact, herbrandPsiNat_of_break_le s _ hr.le]
  push_cast [Nat.cast_sub hr.le]
  ring

end NormImage

section Twist

variable {F E K : Type*} [Field F] [Field E] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
  [ValuativeExtension F E] [ValuativeExtension E K] [ValuativeExtension F K]
  [Module.Finite F E] [Module.Finite E K] [Module.Finite F K]

/-- The same actual base norm twist pulls back through either edge of
the tower; this is transitivity of the field norm on units. -/
private theorem norm_twist (ψ : ContinuousQuasiChar E) (lam : ContinuousQuasiChar F) :
    normQuasiChar E K (ψ / normQuasiChar F E lam) =
      normQuasiChar E K ψ / normQuasiChar F K lam := by
  apply ContinuousMonoidHom.ext
  intro x
  change ψ (normUnits E K x) / lam (normUnits F E (normUnits E K x)) =
    ψ (normUnits E K x) / lam (normUnits F K x)
  have hn : normUnits F E (normUnits E K x) = normUnits F K x := by
    apply Units.ext
    exact Algebra.norm_norm
  rw [hn]

omit [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Algebra E K] [IsScalarTower F E K]
  [ValuativeExtension F E] [ValuativeExtension E K]
  [Module.Finite F E] [Module.Finite E K] in
/-- A common base twist preserves failure to descend to the base field. -/
private theorem twist_primitive (Θ : ContinuousQuasiChar K) (lam : ContinuousQuasiChar F)
    (hprimitive : ¬ ∃ ξ : ContinuousQuasiChar F, normQuasiChar F K ξ = Θ) :
    ¬ ∃ ξ : ContinuousQuasiChar F,
      normQuasiChar F K ξ = Θ / normQuasiChar F K lam := by
  rintro ⟨ξ, hξ⟩
  apply hprimitive
  refine ⟨ξ * lam, ?_⟩
  apply ContinuousMonoidHom.ext
  intro x
  have h := DFunLike.congr_fun hξ x
  change ξ (normUnits F K x) = Θ x / lam (normUnits F K x) at h
  change ξ (normUnits F K x) * lam (normUnits F K x) = Θ x
  rw [h, div_mul_cancel]

/-- Express total ramification on the two residue-field extensions, using
Mathlib's degree multiplication in the induced residue-field tower. -/
private theorem residue_degrees_in_tower (hres : residueDegree F K = 1) :
    residueDegree F E = 1 ∧ residueDegree E K = 1 := by
  letI : IsScalarTower (ringOfIntegers F) (ringOfIntegers E) (ringOfIntegers K) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap F K (x : F) = algebraMap E K (algebraMap F E (x : F))
      rw [← IsScalarTower.algebraMap_apply F E K])
  letI : IsLocalHom (algebraMap (ringOfIntegers F) (ringOfIntegers E)) := inferInstance
  letI : IsLocalHom (algebraMap (ringOfIntegers E) (ringOfIntegers K)) := inferInstance
  rw [residueDegree_eq_finrank_residueField] at hres
  rw [residueDegree_eq_finrank_residueField, residueDegree_eq_finrank_residueField]
  exact mul_eq_one.mp
    ((Module.finrank_mul_finrank (ResidueField F) (ResidueField E) (ResidueField K)).trans hres)

end Twist

section Diamond

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

/-- **Paper Proposition 9.34 (`O:G:reduce`).** Every primitive compatible
pair admits a common continuous base twist with endpoint conductors exactly
`1 + t + tPrime` and `1 + t + t₂`.

The setup is the actual totally ramified odd-prime diamond and the
distinguished fields of `OddTotalBreakData`. The paper's `p ∤ t` condition
is explicit. Norm-subgroup separation is the same input as for the accepted
primitive lower bound and deep descent. All intermediate field topologies
and valuations are canonical.

If the original second conductor is larger than the minimal one, the same
constructed base character has conductor `1 + r`, where `t₂ < r` and
`t < p * (r - t₂)`. The final equality records the exact original second
conductor. Both differences are in `ℤ`, so no negative depth is truncated.
The characters need not be unitary, and neither field characteristic is
excluded. -/
theorem reduction {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1)
    (D : Total.OddTotalBreakData (F := F) (K := K) hp hG)
    (htprime : ¬ p ∣ D.t)
    (hne : Ramification.intermediateNormRange D.B₁ ≠
      Ramification.intermediateNormRange D.B₂) :
    letI := Basic.intermediateFieldValuativeRel D.B₁
    letI := Basic.intermediateFieldTopology D.B₁
    letI := Basic.intermediateField_localField D.B₁
    letI := Basic.intermediateField_lowerValuativeExtension D.B₁
    letI := Basic.intermediateField_upperValuativeExtension D.B₁
    letI := Basic.intermediateFieldValuativeRel D.B₂
    letI := Basic.intermediateFieldTopology D.B₂
    letI := Basic.intermediateField_localField D.B₂
    letI := Basic.intermediateField_lowerValuativeExtension D.B₂
    letI := Basic.intermediateField_upperValuativeExtension D.B₂
    ∀ (ψ₁ : ContinuousQuasiChar D.B₁) (ψ₂ : ContinuousQuasiChar D.B₂)
      (ψB : ContinuousQuasiChar K),
      normQuasiChar D.B₁ K ψ₁ = ψB → normQuasiChar D.B₂ K ψ₂ = ψB →
      (¬ ∃ ξ : ContinuousQuasiChar F, normQuasiChar F K ξ = ψB) →
      ∃ (lam : ContinuousQuasiChar F) (χ : ContinuousQuasiChar D.B₁)
        (φ : ContinuousQuasiChar D.B₂),
        ψ₁ = χ * normQuasiChar F D.B₁ lam ∧
        ψ₂ = φ * normQuasiChar F D.B₂ lam ∧
        normQuasiChar D.B₁ K χ = normQuasiChar D.B₂ K φ ∧
        (¬ ∃ ξ : ContinuousQuasiChar F,
          normQuasiChar F K ξ = normQuasiChar D.B₁ K χ) ∧
        IsMultiplicativeConductor D.B₁ χ (1 + D.t + D.tPrime) ∧
        IsMultiplicativeConductor D.B₂ φ (1 + D.t + D.t₂) ∧
        (1 + D.t + D.t₂ < multiplicativeConductorExponent D.B₂ ψ₂ →
          ∃ r : ℕ, IsMultiplicativeConductor F lam (1 + r) ∧ D.t₂ < r ∧
            (D.t : ℤ) < (p : ℤ) * ((r : ℤ) - D.t₂) ∧
            (multiplicativeConductorExponent D.B₂ ψ₂ : ℤ) =
              1 + D.t₂ + (p : ℤ) * ((r : ℤ) - D.t₂)) := by
  letI := Basic.intermediateFieldValuativeRel D.B₁
  letI := Basic.intermediateFieldTopology D.B₁
  letI := Basic.intermediateField_localField D.B₁
  letI := Basic.intermediateField_lowerValuativeExtension D.B₁
  letI := Basic.intermediateField_upperValuativeExtension D.B₁
  letI := Basic.intermediateFieldValuativeRel D.B₂
  letI := Basic.intermediateFieldTopology D.B₂
  letI := Basic.intermediateField_localField D.B₂
  letI := Basic.intermediateField_lowerValuativeExtension D.B₂
  letI := Basic.intermediateField_upperValuativeExtension D.B₂
  intro ψ₁ ψ₂ ψB hc₁ hc₂ hprimitive
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hdegree₁, hcyclic₁, hupper₁⟩ :=
    Basic.intermediateField_tower_compatible hp hG D.B₁ D.degree_B₁
  obtain ⟨_, _, _, _, _, _, _, _, _, hdegreeLower₂, hdegree₂, hcyclic₂, hupper₂⟩ :=
    Basic.intermediateField_tower_compatible hp hG D.B₂ D.degree_B₂
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F D.B₁ hcyclic₁
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension D.B₁ K hupper₁
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F D.B₂ hcyclic₂
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension D.B₂ K hupper₂
  have hr₁ := residue_degrees_in_tower (E := D.B₁) hres
  have hr₂ := residue_degrees_in_tower (E := D.B₂) hres
  have hbreaks₁ : PrimeCyclicExtension.IsLowerBreak F D.B₁ D.t ∧
      PrimeCyclicExtension.IsLowerBreak D.B₁ K D.tPrime := D.B₁_breaks
  have hbreaks₂ : PrimeCyclicExtension.IsLowerBreak F D.B₂ D.t₂ ∧
      PrimeCyclicExtension.IsLowerBreak D.B₂ K D.t := D.B₂_breaks
  have htPrime : ¬ p ∣ D.tPrime := by
    rw [D.tPrime_eq]
    exact fun h => htprime ((Nat.dvd_add_iff_left (dvd_mul_right p D.delta)).mpr h)
  have hker := descent hp D.odd_prime hG D.B₁ D.B₂ D.degree_B₁ D.degree_B₂ hne
    D.t D.tPrime hbreaks₁.1 D.t_pos hbreaks₁.2 htPrime
    ψ₁ ψ₂ ψB hc₁ hc₂ hprimitive
  obtain ⟨lam, hlam⟩ := extend_from_norm_layer hbreaks₁.1 hr₁.1 ψ₁ hker
  let χ := ψ₁ / normQuasiChar F D.B₁ lam
  let φ := ψ₂ / normQuasiChar F D.B₂ lam
  let Θ := ψB / normQuasiChar F K lam
  have hχnorm : normQuasiChar D.B₁ K χ = Θ := by
    rw [norm_twist, hc₁]
  have hφnorm : normQuasiChar D.B₂ K φ = Θ := by
    rw [norm_twist, hc₂]
  have hprimitive' := twist_primitive ψB lam hprimitive
  obtain ⟨a₁, ha₁⟩ := exists_isMultiplicativeConductor D.B₁ χ
  obtain ⟨a₂, ha₂⟩ := exists_isMultiplicativeConductor D.B₂ φ
  have hlow := lower hp hG hres D hne χ φ Θ a₁ a₂
    hχnorm hφnorm hprimitive' ha₁ ha₂
  have hfirst : a₁ = 1 + D.t + D.tPrime := by
    apply Nat.le_antisymm _ hlow.1
    apply ha₁.minimal
    intro x hx
    change ψ₁ x / lam (normUnits F D.B₁ x) = 1
    exact div_eq_one.mpr (hlam x hx).symm
  have hχ : IsMultiplicativeConductor D.B₁ χ (1 + D.t + D.tPrime) := by
    rwa [hfirst] at ha₁
  have hhigh₁ := high_pullback_conductor hbreaks₁.2 hr₁.2 hχ
    (by have := D.t_pos; omega)
  have hhigh₂ := high_pullback_conductor hbreaks₂.2 hr₂.2 ha₂
    (by have := D.t_pos; have := D.t_le_t₂; omega)
  rw [hχnorm, hdegree₁] at hhigh₁
  rw [hφnorm, hdegree₂] at hhigh₂
  have heq := hhigh₁.symm.trans hhigh₂
  have hzero : (p : ℤ) * ((a₂ : ℤ) - (1 + D.t + D.t₂)) = 0 := by
    rw [D.tPrime_eq] at heq
    rw [D.t₂_eq]
    push_cast [Nat.cast_sub hp.one_le] at heq ⊢
    nlinarith only [heq]
  have hsecond : a₂ = 1 + D.t + D.t₂ := by
    have h := (mul_eq_zero.mp hzero).resolve_left (by exact_mod_cast hp.ne_zero)
    exact_mod_cast (sub_eq_zero.mp h)
  have hφ : IsMultiplicativeConductor D.B₂ φ (1 + D.t + D.t₂) := by
    rwa [hsecond] at ha₂
  have hψ₁ : ψ₁ = χ * normQuasiChar F D.B₁ lam := (div_mul_cancel _ _).symm
  have hψ₂ : ψ₂ = φ * normQuasiChar F D.B₂ lam := (div_mul_cancel _ _).symm
  refine ⟨lam, χ, φ, hψ₁, hψ₂, hχnorm.trans hφnorm.symm, ?_, hχ, hφ, ?_⟩
  · rwa [hχnorm]
  · intro hlarge
    obtain ⟨r, hr, htr, heq⟩ := transition_conductor hbreaks₂.1 hr₂.1 ψ₂ φ lam
      hψ₂ hφ (multiplicativeConductorExponent_isConductor D.B₂ ψ₂) (by omega) hlarge
    rw [hdegreeLower₂] at heq
    refine ⟨r, hr, htr, ?_, heq⟩
    have hlarge' : (1 + D.t + D.t₂ : ℤ) < multiplicativeConductorExponent D.B₂ ψ₂ :=
      by exact_mod_cast hlarge
    linarith

end Diamond

end

end LanglandsSecondMainLemma.Odd.Conductors
