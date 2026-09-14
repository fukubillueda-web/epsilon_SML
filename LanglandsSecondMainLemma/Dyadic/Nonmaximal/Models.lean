import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.Commutator
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.Compatibility
import LanglandsSecondMainLemma.Local.NormDescent

/-!
# Dyadic / Nonmaximal / Models

Paper Theorem 13.6, `D:NM:core-exists`, with the full setup
`D:NM:breaks`, `D:NM:upper`, `D:NM:origin`, `D:NM:J`, and `D:NM:Rcharts`.

The commutator and stationary prescriptions are assembled on their actual
generated subgroup before applying continuous character extension. Norm
descent and the above-break norm image preserve the other two full charts.
All coefficient depths below are integers, including the negative order
`1 - 2a` of the actual upper norms of the aligned origin.
-/

namespace LanglandsSecondMainLemma.Dyadic.Nonmaximal

open LanglandsFirstMainLemma

noncomputable section

section ChartConductors

variable (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

private theorem chart_displacement {s : ℕ} (hs : 0 < s)
    (u : Eˣ) (hu : u ∈ unitFiltration E s) :
    1 - (u : E) ∈ lattice E (s : ℤ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  simpa only [neg_sub] using neg_mem_lattice E
    ((mem_unitFiltration_succ_iff_sub_mem_lattice E n u).mp hu)

private theorem chart_trivial
    (Ψ : ContinuousAddChar E) (c : E) (h J : ℤ) (m : ℕ)
    (hc : ord E c = (h : WithTop ℤ))
    (hΨ : IsAdditiveConductor E Ψ (-J))
    (hm : 0 < m) (hdepth : J ≤ h + (m : ℤ))
    (u : Eˣ) (hu : u ∈ unitFiltration E m) :
    Ψ (c * (1 - (u : E))) = 1 := by
  apply hΨ.trivial
  simp only [neg_neg]
  apply lattice_antitone E hdepth
  exact mul_mem_lattice E (by rw [mem_lattice, hc])
    (chart_displacement E hm u hu)

/-- The full chart proves both triviality and nontriviality at its last
layer, using FML's whole-ideal additive conductor theorem. -/
private theorem chart_conductor
    (Ψ : ContinuousAddChar E) (c : E) (h J : ℤ) (s n : ℕ)
    (hc : ord E c = (h : WithTop ℤ))
    (hΨ : IsAdditiveConductor E Ψ (-J))
    (hn : 0 < n) (hsn : s ≤ n) (hdepth : h + (n + 1 : ℕ) = J)
    (χ : ContinuousQuasiChar E)
    (hchart : ∀ u : unitFiltration E s,
      χ (u : Eˣ) = Ψ (c * (1 - ((u : Eˣ) : E)))) :
    IsMultiplicativeConductor E χ (n + 1) := by
  apply IsMultiplicativeConductor.of_succ_boundary
  · intro u hu
    rw [hchart ⟨u, unitFiltration_antitone E (by omega) hu⟩]
    exact chart_trivial E Ψ c h J (n + 1) hc hΨ (by omega) hdepth.ge u hu
  · intro hprev
    obtain ⟨x, hx, _, hxne⟩ := hΨ.exists_ne_one_on_predecessor
    have hc0 : c ≠ 0 := (ord_ne_top_iff E).mp (by rw [hc]; simp)
    have hz : x / c ∈ lattice E (n : ℤ) := by
      apply (div_mem_lattice_iff E c x h (n : ℤ) hc).mpr
      convert hx using 1
      push_cast at hdepth
      congr 1
      omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    let u := principalUnitOf E k (-(x / c)) (neg_mem_lattice E hz)
    have hu : u ∈ unitFiltration E (k + 1) := principalUnitOf_mem E k _ _
    have hv := hchart ⟨u, unitFiltration_antitone E hsn hu⟩
    have harg : c * (1 - (u : E)) = x := by
      change c * (1 - (1 + -(x / c))) = x
      field_simp
      ring
    rw [harg, hprev u hu] at hv
    exact hxne hv.symm

end ChartConductors

section Extension

/-- Construct the prescription on the image of `(v,u) ↦ δ(v)u`.
The evaluated shallow commutator will discharge `hoverlap`; in particular
the kernel condition for this actual product homomorphism is proved. -/
private theorem extend_chart_with_commutator
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (δ : Eˣ →* Eˣ) (ν : Eˣ →* ℂˣ) (s m : ℕ)
    (R : unitFiltration E s →* ℂˣ)
    (hoverlap : ∀ v hv, R ⟨δ v, hv⟩ = ν v)
    (hm : 0 < m) (hsm : s ≤ m)
    (htrivial : ∀ u : unitFiltration E m,
      R ⟨u, unitFiltration_antitone E hsm u.property⟩ = 1) :
    ∃ χ : ContinuousQuasiChar E,
      (∀ u : unitFiltration E s, χ (u : Eˣ) = R u) ∧
      ∀ v, χ (δ v) = ν v := by
  let H := unitFiltration E s
  let A : Eˣ × H →* Eˣ :=
    (δ.comp (MonoidHom.fst Eˣ H)) * (H.subtype.comp (MonoidHom.snd Eˣ H))
  let P : Eˣ × H →* ℂˣ :=
    (ν.comp (MonoidHom.fst Eˣ H)) * (R.comp (MonoidHom.snd Eˣ H))
  have hker : A.rangeRestrict.ker ≤ P.ker := by
    rintro ⟨v, u⟩ hp
    have heq : δ v * (u : Eˣ) = 1 := congrArg Subtype.val hp
    have hδ : δ v = (u : Eˣ)⁻¹ := eq_inv_of_mul_eq_one_left heq
    have hδH : δ v ∈ H := hδ ▸ H.inv_mem u.property
    have hR := hoverlap v hδH
    have hu : (⟨δ v, hδH⟩ : H) = u⁻¹ := Subtype.ext hδ
    rw [hu, map_inv] at hR
    change ν v * R u = 1
    rw [← hR, inv_mul_cancel]
  let Q : A.range →* ℂˣ :=
    A.rangeRestrict.liftOfSurjective A.rangeRestrict_surjective ⟨P, hker⟩
  have hQ (v : Eˣ × H) : Q (A.rangeRestrict v) = P v :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hH : H ≤ A.range := by
    intro u hu
    exact ⟨(1, ⟨u, hu⟩), by simp [A]⟩
  have hQR (u : H) : Q ⟨u, hH u.property⟩ = R u := by
    have heq : (⟨(u : Eˣ), hH u.property⟩ : A.range) =
        A.rangeRestrict (1, u) := Subtype.ext (by simp [A])
    rw [heq, hQ]
    simp [P]
  let hmH : unitFiltration E m ≤ A.range :=
    (unitFiltration_antitone E hsm).trans hH
  obtain ⟨χ, hχ⟩ := Local.characterExtension E A.range m hm hmH Q (by
    apply MonoidHom.ext
    intro u
    exact (hQR ⟨u, unitFiltration_antitone E hsm u.property⟩).trans (htrivial u))
  refine ⟨χ, ?_, ?_⟩
  · intro u
    exact (DFunLike.congr_fun hχ ⟨u, hH u.property⟩).trans (hQR u)
  · intro v
    have hv := DFunLike.congr_fun hχ (A.rangeRestrict (v, 1))
    rw [hQ] at hv
    simpa [A, P] using hv

end Extension

section Norms

private theorem norm_restrict
    (F L K : Type) [Field F] [Field L] [Field K]
    [Algebra F L] [Algebra F K] [Algebra L K] [IsScalarTower F L K]
    [Normal F L] (ρ : Gal(K/F)) (u : Kˣ) :
    normUnits L K (Units.map ρ.toMonoidHom u) =
      Units.map (ρ.restrictNormal L).toMonoidHom (normUnits L K u) := by
  have hcompat : (algebraMap L K).comp (ρ.restrictNormal L).toRingHom =
      ρ.toRingHom.comp (algebraMap L K) := by
    apply RingHom.ext
    exact ρ.restrictNormal_commutes L
  have h := Algebra.norm_eq_of_equiv_equiv
    (ρ.restrictNormal L).toRingEquiv ρ.toRingEquiv hcompat (u : K)
  have h' := congrArg (ρ.restrictNormal L) h
  apply Units.ext
  exact (h'.trans ((ρ.restrictNormal L).apply_symm_apply _)).symm

private theorem quadratic_automorphisms
    (F L : Type) [Field F] [Field L] [Algebra F L]
    [Module.Finite F L] [IsGalois F L] [Algebra.IsQuadraticExtension F L]
    (σ : Gal(L/F)) (hσ : σ ≠ 1) (τ : Gal(L/F)) : τ = 1 ∨ τ = σ := by
  have hcard : Nat.card Gal(L/F) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two F L]
  obtain ⟨ρ, _, hρ⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/F))).mp hcard
  by_cases hτ : τ = 1
  · exact Or.inl hτ
  · exact Or.inr ((hρ τ hτ).trans (hρ σ hσ).symm)

/-- The upper pullback is invariant under every actual base automorphism.
The commutator character kills upper norms by norm transitivity through
the second lower field. -/
private theorem first_pullback_invariant
    (F L M K : Type) [Field F] [Field L] [Field M] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F L] [Algebra F M] [Algebra F K] [Algebra L K] [Algebra M K]
    [IsScalarTower F L K] [IsScalarTower F M K]
    [ValuativeExtension F L] [ValuativeExtension F M] [ValuativeExtension L K]
    [Module.Finite F L] [Module.Finite F M]
    [Module.Finite L K] [Module.Finite M K]
    [IsGalois F L] [Algebra.IsQuadraticExtension F L]
    (σ : Gal(L/F)) (hσ : σ ≠ 1) (ω : NormCharacter F M)
    (χ : ContinuousQuasiChar L)
    (hcomm : ∀ v, χ (Units.map σ.toMonoidHom v / v) = ω.1 (normUnits F L v)) :
    ∀ (ρ : Gal(K/F)) (u : Kˣ),
      normQuasiChar L K χ (Units.map ρ.toMonoidHom u) = normQuasiChar L K χ u := by
  intro ρ u
  change χ (normUnits L K (Units.map ρ.toMonoidHom u)) = χ (normUnits L K u)
  rw [norm_restrict F L K]
  rcases quadratic_automorphisms F L σ hσ (ρ.restrictNormal L) with hρ | hρ
  · rw [hρ]
    rfl
  · rw [hρ]
    have h := hcomm (normUnits L K u)
    have htower : normUnits F L (normUnits L K u) =
        normUnits F M (normUnits M K u) := by
      apply Units.ext
      exact (Basic.norm_tower (F := F) (L := L) (K := K) (u : K)).trans
        (Basic.norm_tower (F := F) (L := M) (K := K) (u : K)).symm
    rw [htower, ω.eq_one_on_normRange F M _ ⟨normUnits M K u, rfl⟩,
      map_div, div_eq_one] at h
    exact h

/-- A full high chart on either of the remaining sides is reached by
actual norms from `U_K^(2r+1)`, with upper break `2a-1`. -/
private theorem other_norm_image
    (L K : Type) [Field L] [Field K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra L K] [ValuativeExtension L K] [Module.Finite L K]
    [PrimeCyclicExtension L K] [Algebra.IsQuadraticExtension L K]
    (a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r)
    (ht : PrimeCyclicExtension.IsLowerBreak L K (2 * a - 1))
    (hres : residueDegree L K = 1) :
    Subgroup.map (normUnits L K) (unitFiltration K (2 * r + 1)) =
      unitFiltration L (a + r) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer L K hres
  have hh := norm_unitFiltration_map_eq_aboveBreak L K ht
    (r := a + r) (by omega) hres pi hpi hgen
  rw [Algebra.IsQuadraticExtension.finrank_eq_two L K] at hh
  dsimp only [aboveBreakSourceDepth] at hh
  rw [herbrandPsiNat_of_break_le _ _ (by omega)] at hh
  have hdepth : 2 * a - 1 + 2 * (a + r - (2 * a - 1)) = 2 * r + 1 := by omega
  rwa [hdepth] at hh

end Norms

section Primitive

variable (F L K : Type) [Field F] [Field L] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F L] [Algebra F K] [Algebra L K] [IsScalarTower F L K]
  [ValuativeExtension F L] [ValuativeExtension F K] [ValuativeExtension L K]
  [Module.Finite F L] [Module.Finite L K] [Module.Finite F K]
  [PrimeCyclicExtension F L] [PrimeCyclicExtension L K]
  [Algebra.IsQuadraticExtension F L]

/-- In the nonmaximal case primitivity also follows directly from the
local conductor formulas. An upper norm-character twist cannot change
`4r-1`; a lower base pullback with conductor above `2a` has even conductor.
This avoids any additional crossed-character input. -/
private theorem first_core_primitive
    (a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r)
    (ht : PrimeCyclicExtension.IsLowerBreak F L (2 * a - 1))
    (ht' : PrimeCyclicExtension.IsLowerBreak L K (4 * r - 2 * a - 1))
    (hres : residueDegree F L = 1) (hres' : residueDegree L K = 1)
    (χ : ContinuousQuasiChar L) (hχ : IsMultiplicativeConductor L χ (4 * r - 1)) :
    ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar L K χ = normQuasiChar F K lambda := by
  rintro ⟨lambda, hlambda⟩
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F L hres
  obtain ⟨pi', hpi', hgen'⟩ := monogenicUniformizer L K hres'
  let μ : NormCharacter L K := ⟨χ / normQuasiChar F L lambda, by
    apply ContinuousMonoidHom.ext
    intro u
    have h := DFunLike.congr_fun hlambda u
    change χ (normUnits L K u) = lambda (normUnits F K u) at h
    change χ (normUnits L K u) / lambda (normUnits F L (normUnits L K u)) = 1
    have hn : normUnits F L (normUnits L K u) = normUnits F K u :=
      Units.ext (Basic.norm_tower (u : K))
    rw [hn, h, div_self']⟩
  have hμ := ramifiedNormCharacter_trivialOn_break_succ L K ht' hres'
    pi' hpi' hgen' μ
  have hsame (u : Lˣ) (hu : u ∈ unitFiltration L (4 * r - 2)) :
      χ u = normQuasiChar F L lambda u := by
    exact div_eq_one.mp (hμ u (unitFiltration_antitone L (by omega) hu))
  have hpull : IsMultiplicativeConductor L (normQuasiChar F L lambda) (4 * r - 1) := by
    have hn : 4 * r - 2 + 1 = 4 * r - 1 := by omega
    rw [← hn]
    apply IsMultiplicativeConductor.of_succ_boundary
    · intro u hu
      rw [← hsame u (unitFiltration_antitone L (by omega) hu)]
      exact hχ.trivial u (by simpa only [hn] using hu)
    · intro hprev
      have hχ' : IsMultiplicativeConductor L χ (4 * r - 2 + 1) := by
        simpa only [hn] using hχ
      apply hχ'.not_trivialOnPredecessor
      intro u hu
      rw [hsame u hu]
      exact hprev u hu
  let B := canonicalLocalQuasiCharData F lambda
  have hhigh : 2 * a - 1 + 1 < B.conductor := by
    by_contra hlow
    have htriv : QuasiCharTrivialOnUnitFiltration F lambda (2 * a - 1 + 1) := by
      intro u hu
      exact B.isConductor.trivial u (unitFiltration_antitone F (by omega) hu)
    have htriv' := (quasiCharTrivialOnUnitFiltration_compNorm_iff_break_succ
      F L ht hres pi hpi hgen lambda).mpr htriv
    have hle := hpull.minimal _ htriv'
    omega
  have hcond := multiplicativeConductor_compNorm_high F L ht hres
    pi hpi hgen hhigh B.isConductor
  have heq := hpull.unique hcond
  have hint := highConductor_cast_eq_degree_mul_sub_different F L hhigh
  rw [← heq, Algebra.IsQuadraticExtension.finrank_eq_two F L] at hint
  push_cast at hint
  omega

end Primitive

section Models

variable (F K : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]
  [IsGalois F K] [IsKleinFour Gal(K/F)]
  (L₁ L₂ L₃ : IntermediateField F K)
  [ValuativeRel L₁] [TopologicalSpace L₁] [IsNonarchimedeanLocalField L₁]
  [ValuativeRel L₂] [TopologicalSpace L₂] [IsNonarchimedeanLocalField L₂]
  [ValuativeRel L₃] [TopologicalSpace L₃] [IsNonarchimedeanLocalField L₃]
  [ValuativeExtension F L₁] [ValuativeExtension L₁ K]
  [ValuativeExtension F L₂] [ValuativeExtension L₂ K]
  [ValuativeExtension F L₃] [ValuativeExtension L₃ K]
  [Module.Finite F L₁] [Module.Finite L₁ K]
  [Module.Finite F L₂] [Module.Finite L₂ K]
  [Module.Finite F L₃] [Module.Finite L₃ K]
  [Algebra.IsQuadraticExtension F L₁] [Algebra.IsQuadraticExtension L₁ K]
  [Algebra.IsQuadraticExtension F L₂] [Algebra.IsQuadraticExtension L₂ K]
  [Algebra.IsQuadraticExtension F L₃] [Algebra.IsQuadraticExtension L₃ K]
  [PrimeCyclicExtension F L₁] [PrimeCyclicExtension F L₂]
  [PrimeCyclicExtension L₁ K] [PrimeCyclicExtension L₂ K] [PrimeCyclicExtension L₃ K]

set_option maxHeartbeats 800000 in
/-- **Full global core models (Paper Theorem 13.6, `D:NM:core-exists`).**

From the actual aligned origin and normalized lower-character data,
construct continuous group characters on all three full multiplicative
groups. Their norm pullbacks agree, are invariant under `Gal(K/F)`, and
do not descend from any continuous base quasi-character. The conductors
are exactly `4r-1`, `2a+2r-1`, `2a+2r-1`; the common conductor is
`4r+2a-2`. Every element of each prescribed full stationary ideal is
covered, with the coefficient `N_i Y` and the original normalization.

The records `O` and `D` have proved constructors in the accepted `Origin`
and `LowerCharacters` prerequisites. Neither a commutator formula nor
compatible global characters are assumptions. -/
theorem models
    (e a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (ht : PrimeCyclicExtension.IsLowerBreak F L₁ (2 * a - 1))
    (ht₁ : PrimeCyclicExtension.IsLowerBreak L₁ K (4 * r - 2 * a - 1))
    (ht₂ : PrimeCyclicExtension.IsLowerBreak L₂ K (2 * a - 1))
    (ht₃ : PrimeCyclicExtension.IsLowerBreak L₃ K (2 * a - 1))
    (hres : residueDegree F L₁ = 1)
    (hres₁ : residueDegree L₁ K = 1) (hres₂ : residueDegree L₂ K = 1)
    (hres₃ : residueDegree L₃ K = 1)
    (x : L₁) (y : L₂) (z : L₃) (f g d : F)
    (O : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂) (ω₃ : NormCharacter F L₃)
    (ψ : LocalAddCharData F) (α : Fˣ)
    (D : LowerCharacterData F L₁ L₂ L₃ a r ω₁ ω₂ ω₃ ψ α
      (normUnits F L₁ (Units.mk0 (trace L₁ K O.Y) O.upperTraces_ne_zero.1))
      (normUnits F L₂ (Units.mk0 (trace L₂ K O.Y) O.upperTraces_ne_zero.2.1))
      (normUnits F L₃ (Units.mk0 (trace L₃ K O.Y) O.upperTraces_ne_zero.2.2))) :
    let Ψ := (scaleAddCharData F ψ α).character
    ∃ (χ₁ : ContinuousQuasiChar L₁) (χ₂ : ContinuousQuasiChar L₂)
      (χ₃ : ContinuousQuasiChar L₃),
      IsMultiplicativeConductor L₁ χ₁ (4 * r - 1) ∧
      IsMultiplicativeConductor L₂ χ₂ (2 * a + 2 * r - 1) ∧
      IsMultiplicativeConductor L₃ χ₃ (2 * a + 2 * r - 1) ∧
      normQuasiChar L₂ K χ₂ = normQuasiChar L₁ K χ₁ ∧
      normQuasiChar L₃ K χ₃ = normQuasiChar L₁ K χ₁ ∧
      IsMultiplicativeConductor K (normQuasiChar L₁ K χ₁) (4 * r + 2 * a - 2) ∧
      (∀ (ρ : Gal(K/F)) (u : Kˣ),
        normQuasiChar L₁ K χ₁ (Units.map ρ.toMonoidHom u) = normQuasiChar L₁ K χ₁ u) ∧
      (¬ ∃ lambda : ContinuousQuasiChar F,
        normQuasiChar L₁ K χ₁ = normQuasiChar F K lambda) ∧
      (∀ u : unitFiltration L₁ (2 * r), χ₁ (u : L₁ˣ) =
        tracePullbackAddChar F L₁ Ψ (norm L₁ K O.Y * (1 - ((u : L₁ˣ) : L₁)))) ∧
      (∀ u : unitFiltration L₂ (a + r), χ₂ (u : L₂ˣ) =
        tracePullbackAddChar F L₂ Ψ (norm L₂ K O.Y * (1 - ((u : L₂ˣ) : L₂)))) ∧
      (∀ u : unitFiltration L₃ (a + r), χ₃ (u : L₃ˣ) =
        tracePullbackAddChar F L₃ Ψ (norm L₃ K O.Y * (1 - ((u : L₃ˣ) : L₃)))) := by
  let Ψ := (scaleAddCharData F ψ α).character
  obtain ⟨R₁, R₂, R₃, hR₁, hR₂, hR₃, hcompat⟩ :=
    compatibility F K L₁ L₂ L₃ a r ha har ht₁ ht₂ ht₃ hres₁ hres₂ hres₃
      x y z f g d O ω₁ ω₂ ω₃ ψ α D
  let σ := PrimeCyclicExtension.generator F L₁
  have hσ : σ ≠ 1 := PrimeCyclicExtension.generator_ne_one F L₁
  let δ : L₁ˣ →* L₁ˣ := Units.map σ.toMonoidHom / MonoidHom.id L₁ˣ
  have hoverlap (v : L₁ˣ) (hv : δ v ∈ unitFiltration L₁ (2 * r)) :
      R₁ ⟨δ v, hv⟩ = ω₂.1 (normUnits F L₁ v) := by
    have hc := commutator F K L₁ L₂ L₃ e a r ha har hre htwo hres
      x y z f g d O ω₁ ω₂ ω₃ ψ α D σ hσ v hv
    exact (hR₁ ⟨δ v, hv⟩).trans hc
  have hsm : 2 * r ≤ 4 * r - 1 := by omega
  obtain ⟨χ₁, hχ₁R, hcomm⟩ := extend_chart_with_commutator L₁ δ
    (normQuasiChar F L₁ ω₂.1).toMonoidHom (2 * r) (4 * r - 1) R₁
    hoverlap (by omega) hsm (by
      intro u
      rw [hR₁]
      exact chart_trivial L₁ _ _ (1 - 2 * (a : ℤ)) (4 * (r : ℤ) - 2 * (a : ℤ))
        (4 * r - 1) O.upperNorm₁_order D.first_conductor (by omega) (by omega)
        u u.property)
  have hχ₁chart (u : unitFiltration L₁ (2 * r)) :
      χ₁ (u : L₁ˣ) = tracePullbackAddChar F L₁ Ψ
        (norm L₁ K O.Y * (1 - ((u : L₁ˣ) : L₁))) := (hχ₁R u).trans (hR₁ u)
  have hm₁ : 4 * r - 2 + 1 = 4 * r - 1 := by omega
  have hχ₁ : IsMultiplicativeConductor L₁ χ₁ (4 * r - 1) := by
    simpa only [hm₁] using chart_conductor L₁ _ _
      (1 - 2 * (a : ℤ)) (4 * (r : ℤ) - 2 * (a : ℤ)) (2 * r) (4 * r - 2)
      O.upperNorm₁_order D.first_conductor (by omega) (by omega) (by omega)
      χ₁ hχ₁chart
  have hinvariant := first_pullback_invariant F L₁ L₂ K σ hσ ω₂ χ₁ hcomm
  obtain ⟨χ₂, hpull₂⟩ := Local.invariantCharacter_descends L₂ K
    (normQuasiChar L₁ K χ₁) (fun ρ u => hinvariant (ρ.restrictScalars F) u)
  obtain ⟨χ₃, hpull₃⟩ := Local.invariantCharacter_descends L₃ K
    (normQuasiChar L₁ K χ₁) (fun ρ u => hinvariant (ρ.restrictScalars F) u)
  have hnorm₂ := other_norm_image L₂ K a r ha har ht₂ hres₂
  have hnorm₃ := other_norm_image L₃ K a r ha har ht₃ hres₃
  have hχ₂R (u : unitFiltration L₂ (a + r)) : χ₂ (u : L₂ˣ) = R₂ u := by
    have hu : (u : L₂ˣ) ∈ Subgroup.map (normUnits L₂ K)
        (unitFiltration K (2 * r + 1)) := by simpa only [hnorm₂] using u.property
    obtain ⟨V, hV, hVu⟩ := hu
    have hdisp : 1 - (V : K) ∈ lattice K (2 * (r : ℤ)) := by
      apply lattice_antitone K (by omega : 2 * (r : ℤ) ≤ (2 * r + 1 : ℕ))
      exact chart_displacement K (by omega) V hV
    obtain ⟨h₁, h₂, h₃, hv₁, hv₂, hv₃⟩ := hcompat V hdisp
    have h := DFunLike.congr_fun hpull₂ V
    change χ₂ (normUnits L₂ K V) = χ₁ (normUnits L₁ K V) at h
    have huR : (⟨normUnits L₂ K V, h₂⟩ : unitFiltration L₂ (a + r)) = u :=
      Subtype.ext hVu
    rw [hVu, hχ₁R ⟨_, h₁⟩, hv₁, ← hv₂, huR] at h
    exact h
  have hχ₃R (u : unitFiltration L₃ (a + r)) : χ₃ (u : L₃ˣ) = R₃ u := by
    have hu : (u : L₃ˣ) ∈ Subgroup.map (normUnits L₃ K)
        (unitFiltration K (2 * r + 1)) := by simpa only [hnorm₃] using u.property
    obtain ⟨V, hV, hVu⟩ := hu
    have hdisp : 1 - (V : K) ∈ lattice K (2 * (r : ℤ)) := by
      apply lattice_antitone K (by omega : 2 * (r : ℤ) ≤ (2 * r + 1 : ℕ))
      exact chart_displacement K (by omega) V hV
    obtain ⟨h₁, h₂, h₃, hv₁, hv₂, hv₃⟩ := hcompat V hdisp
    have h := DFunLike.congr_fun hpull₃ V
    change χ₃ (normUnits L₃ K V) = χ₁ (normUnits L₁ K V) at h
    have huR : (⟨normUnits L₃ K V, h₃⟩ : unitFiltration L₃ (a + r)) = u :=
      Subtype.ext hVu
    rw [hVu, hχ₁R ⟨_, h₁⟩, hv₁, ← hv₃, huR] at h
    exact h
  have hχ₂chart (u : unitFiltration L₂ (a + r)) :
      χ₂ (u : L₂ˣ) = tracePullbackAddChar F L₂ Ψ
        (norm L₂ K O.Y * (1 - ((u : L₂ˣ) : L₂))) := (hχ₂R u).trans (hR₂ u)
  have hχ₃chart (u : unitFiltration L₃ (a + r)) :
      χ₃ (u : L₃ˣ) = tracePullbackAddChar F L₃ Ψ
        (norm L₃ K O.Y * (1 - ((u : L₃ˣ) : L₃))) := (hχ₃R u).trans (hR₃ u)
  have hm₂ : 2 * a + 2 * r - 2 + 1 = 2 * a + 2 * r - 1 := by omega
  have hχ₂ : IsMultiplicativeConductor L₂ χ₂ (2 * a + 2 * r - 1) := by
    simpa only [hm₂] using chart_conductor L₂ _ _
      (1 - 2 * (a : ℤ)) (2 * (r : ℤ)) (a + r) (2 * a + 2 * r - 2)
      O.upperNorm₂_order D.second_conductor (by omega) (by omega) (by omega)
      χ₂ hχ₂chart
  have hχ₃ : IsMultiplicativeConductor L₃ χ₃ (2 * a + 2 * r - 1) := by
    simpa only [hm₂] using chart_conductor L₃ _ _
      (1 - 2 * (a : ℤ)) (2 * (r : ℤ)) (a + r) (2 * a + 2 * r - 2)
      O.upperNorm₃_order D.third_conductor (by omega) (by omega) (by omega)
      χ₃ hχ₃chart
  have htop : IsMultiplicativeConductor K (normQuasiChar L₁ K χ₁)
      (4 * r + 2 * a - 2) := by
    obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer L₁ K hres₁
    have hc := multiplicativeConductor_compNorm_high L₁ K ht₁ hres₁ pi hpi hgen
      (by omega : 4 * r - 2 * a - 1 + 1 < 4 * r - 1) hχ₁
    rw [Algebra.IsQuadraticExtension.finrank_eq_two L₁ K,
      herbrandPsiNat_of_break_le _ _ (by omega)] at hc
    have hdepth : 4 * r - 2 * a - 1 +
        2 * (4 * r - 1 - 1 - (4 * r - 2 * a - 1)) + 1 = 4 * r + 2 * a - 2 := by
      omega
    rwa [hdepth] at hc
  exact ⟨χ₁, χ₂, χ₃, hχ₁, hχ₂, hχ₃, hpull₂, hpull₃, htop, hinvariant,
    first_core_primitive F L₁ K a r ha har ht ht₁ hres hres₁ χ₁ hχ₁,
    hχ₁chart, hχ₂chart, hχ₃chart⟩

end Models

end

end LanglandsSecondMainLemma.Dyadic.Nonmaximal
