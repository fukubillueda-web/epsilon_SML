import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.Alignment
import LanglandsSecondMainLemma.Algebra.BiquadraticE2

/-!
# Dyadic / Nonmaximal / Origin

This is the exact origin calculation in Paper 13.2, equations
`D:NM:origin`--`D:NM:originvals`. The three fields in the statement are
actual intermediate fields of the biquadratic extension. Thus all traces
and norms are `Algebra.trace` and `Algebra.norm`, and every order is
normalized on its named field.

The hypotheses preceding the aligned coordinates have exactly the output
shape of `Dyadic.Nonmaximal.alignment`. The coordinate bridge constructs the third generator and proves cross-field
generation from the distinct quadratic fields. The norm and trace tables
are consequently proved rather than assumed as conjugation data.
-/

namespace LanglandsSecondMainLemma.Dyadic.Nonmaximal

open LanglandsFirstMainLemma

noncomputable section

private theorem trace_eq_self_add_nontrivial
    {E M : Type*} [Field E] [Field M] [Algebra E M]
    [FiniteDimensional E M] [IsGalois E M]
    (sigma : Gal(M/E)) (hsigma : sigma ≠ 1)
    (hcard : Fintype.card Gal(M/E) = 2) (u : M) :
    algebraMap E M (trace E M u) = u + sigma u := by
  classical
  rw [trace_eq_sum_automorphisms]
  have huniv : ({sigma, (1 : Gal(M/E))} : Finset Gal(M/E)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simpa using hsigma),
      Finset.card_singleton, hcard]
  rw [← huniv]
  simp [hsigma, add_comm]

private theorem norm_eq_self_mul_nontrivial
    {E M : Type*} [Field E] [Field M] [Algebra E M]
    [FiniteDimensional E M] [IsGalois E M]
    (sigma : Gal(M/E)) (hsigma : sigma ≠ 1)
    (hcard : Fintype.card Gal(M/E) = 2) (u : M) :
    algebraMap E M (norm E M u) = u * sigma u := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms]
  have huniv : ({sigma, (1 : Gal(M/E))} : Finset Gal(M/E)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simpa using hsigma),
      Finset.card_singleton, hcard]
  rw [← huniv]
  simp [hsigma, mul_comm]

/-- A nonidentity automorphism of a quadratic simple extension exchanges
the two roots of `X² + X - c`. -/
private theorem nontrivial_map_artinSchreier_root
    {E M : Type*} [Field E] [Field M] [Algebra E M]
    (u : M) (c : E)
    (hu : u ^ 2 + u = algebraMap E M c)
    (hgen : Algebra.adjoin E ({u} : Set M) = ⊤)
    (sigma : Gal(M/E)) (hsigma : sigma ≠ 1) :
    sigma u = -1 - u := by
  have hsigmaRoot : (sigma u) ^ 2 + sigma u = algebraMap E M c := by
    calc
      (sigma u) ^ 2 + sigma u = sigma (u ^ 2 + u) := by simp
      _ = sigma (algebraMap E M c) := congrArg sigma hu
      _ = algebraMap E M c := sigma.commutes c
  have hroot : sigma u = u ∨ sigma u + u + 1 = 0 := by
    have hp : (sigma u - u) * (sigma u + u + 1) = 0 := by
      calc
        (sigma u - u) * (sigma u + u + 1) =
          ((sigma u) ^ 2 + sigma u) - (u ^ 2 + u) := by ring
        _ = 0 := by rw [hsigmaRoot, hu, sub_self]
    rcases mul_eq_zero.mp hp with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr h
  rcases hroot with hsame | hother
  · exfalso
    apply hsigma
    apply AlgEquiv.ext
    have heq : sigma.toAlgHom = (1 : Gal(M/E)).toAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top hgen
      intro v hv
      rw [Set.mem_singleton_iff.mp hv]
      simpa using hsame
    intro v
    exact DFunLike.congr_fun heq v
  · linear_combination hother

/-- A generator of one quadratic field does not belong to a distinct one. -/
private theorem generator_not_mem
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (A B : IntermediateField F K)
    [Module.Finite F A] [Module.Finite F B]
    [Algebra.IsQuadraticExtension F A] [Algebra.IsQuadraticExtension F B]
    (hne : A ≠ B) (u : A) (hgen : Algebra.adjoin F ({u} : Set A) = ⊤) :
    (u : K) ∉ B := by
  intro hu
  have hle : Algebra.adjoin F ({u} : Set A) ≤ B.toSubalgebra.comap A.val := by
    apply Algebra.adjoin_le
    simpa using hu
  rw [hgen] at hle
  have hAB : A ≤ B := fun v hv => hle (show (⟨v, hv⟩ : A) ∈ ⊤ from trivial)
  apply hne
  exact IntermediateField.eq_of_le_of_finrank_eq hAB (by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two F A,
      Algebra.IsQuadraticExtension.finrank_eq_two F B])

/-- On a quadratic edge, every element outside the base generates. -/
private theorem quadratic_adjoin_of_not_mem_range
    {E M : Type*} [Field E] [Field M] [Algebra E M]
    [Algebra.IsQuadraticExtension E M]
    (u : M) (hu : u ∉ Set.range (algebraMap E M)) :
    Algebra.adjoin E ({u} : Set M) = ⊤ := by
  letI : IsSimpleOrder (Subalgebra E M) :=
    Subalgebra.isSimpleOrder_of_finrank_prime E M (by
      rw [Algebra.IsQuadraticExtension.finrank_eq_two E M]
      exact Nat.prime_two)
  rcases eq_bot_or_eq_top (Algebra.adjoin E ({u} : Set M)) with h | h
  · exfalso
    apply hu
    have hm : u ∈ Algebra.adjoin E ({u} : Set M) :=
      Algebra.subset_adjoin (Set.mem_singleton u)
    rw [h] at hm
    exact hm
  · exact h

private theorem cross_generation
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (A B : IntermediateField F K)
    [Module.Finite F A] [Module.Finite F B]
    [Algebra.IsQuadraticExtension F A] [Algebra.IsQuadraticExtension F B]
    [Algebra.IsQuadraticExtension B K]
    (hne : A ≠ B) (u : A) (hgen : Algebra.adjoin F ({u} : Set A) = ⊤) :
    Algebra.adjoin B ({(u : K)} : Set K) = ⊤ := by
  apply quadratic_adjoin_of_not_mem_range
  rintro ⟨v, hv⟩
  exact generator_not_mem A B hne u hgen (hv ▸ v.property)


/-- Construct the third coordinate and all four cross-field generators from
three distinct quadratic intermediate fields. -/
theorem dyadicNonmaximal_coordinate_bridge
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (L₁ L₂ L₃ : IntermediateField F K)
    [Module.Finite F L₁] [Module.Finite F L₂] [Module.Finite F L₃]
    [Module.Finite L₁ K] [Module.Finite L₃ K]
    [Algebra.IsQuadraticExtension F L₁]
    [Algebra.IsQuadraticExtension F L₂]
    [Algebra.IsQuadraticExtension F L₃]
    [Algebra.IsQuadraticExtension L₁ K]
    [Algebra.IsQuadraticExtension L₂ K]
    [Algebra.IsQuadraticExtension L₃ K]
    [IsGalois L₁ K] [IsGalois L₃ K]
    (h₁₂ : L₁ ≠ L₂) (h₁₃ : L₁ ≠ L₃) (h₂₃ : L₂ ≠ L₃)
    (htwo : (2 : K) ≠ 0)
    (x : L₁) (y : L₂) (f g : F)
    (hx : x ^ 2 + x = algebraMap F L₁ f)
    (hy : y ^ 2 + y = algebraMap F L₂ g)
    (hxgen : Algebra.adjoin F ({x} : Set L₁) = ⊤)
    (hygen : Algebra.adjoin F ({y} : Set L₂) = ⊤) :
    ∃ z : L₃,
      (z : K) = (x : K) + (y : K) + 2 * (x : K) * (y : K) ∧
      z ^ 2 + z = algebraMap F L₃ (f + g + 4 * f * g) ∧
      Algebra.adjoin F ({z} : Set L₃) = ⊤ ∧
      Algebra.adjoin L₁ ({(y : K)} : Set K) = ⊤ ∧
      Algebra.adjoin L₂ ({(x : K)} : Set K) = ⊤ ∧
      Algebra.adjoin L₃ ({(x : K)} : Set K) = ⊤ ∧
      Algebra.adjoin L₃ ({(y : K)} : Set K) = ⊤ := by
  classical
  have hygen₁ := cross_generation L₂ L₁ h₁₂.symm y hygen
  have hxgen₂ := cross_generation L₁ L₂ h₁₂ x hxgen
  have hxgen₃ := cross_generation L₁ L₃ h₁₃ x hxgen
  have hygen₃ := cross_generation L₂ L₃ h₂₃ y hygen
  have hxK : (x : K) ^ 2 + (x : K) = algebraMap F K f := by
    exact (congrArg (algebraMap L₁ K) hx).trans
      (IsScalarTower.algebraMap_apply F L₁ K f).symm
  have hyK : (y : K) ^ 2 + (y : K) = algebraMap F K g := by
    exact (congrArg (algebraMap L₂ K) hy).trans
      (IsScalarTower.algebraMap_apply F L₂ K g).symm
  let Z : K := (x : K) + (y : K) + 2 * (x : K) * (y : K)
  have hZ : Z ∈ Set.range (algebraMap L₃ K) := by
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro sigma
    by_cases hsigma : sigma = 1
    · simp [hsigma]
    have hsx := nontrivial_map_artinSchreier_root (x : K)
      (algebraMap F L₃ f)
      (hxK.trans (IsScalarTower.algebraMap_apply F L₃ K f)) hxgen₃ sigma hsigma
    have hsy := nontrivial_map_artinSchreier_root (y : K)
      (algebraMap F L₃ g)
      (hyK.trans (IsScalarTower.algebraMap_apply F L₃ K g)) hygen₃ sigma hsigma
    simp only [Z, map_add, map_mul, map_ofNat, hsx, hsy]
    ring
  obtain ⟨z, hz⟩ := hZ
  change (z : K) = Z at hz
  have hzpoly : z ^ 2 + z = algebraMap F L₃ (f + g + 4 * f * g) := by
    apply (algebraMap L₃ K).injective
    change (z : K) ^ 2 + (z : K) = algebraMap F K (f + g + 4 * f * g)
    rw [hz]
    dsimp [Z]
    rw [map_add, map_add, map_mul, map_mul, map_ofNat, ← hxK, ← hyK]
    ring
  have hxden : 2 * (x : K) + 1 ≠ 0 := by
    intro h
    have hxeq : (x : K) = algebraMap F K (-1 / 2) := by
      simp only [map_div₀, map_neg, map_one, map_ofNat]
      apply (eq_div_iff htwo).mpr
      linear_combination h
    apply generator_not_mem L₁ L₂ h₁₂ x hxgen
    rw [hxeq]
    exact L₂.algebraMap_mem _
  have hyden : 2 * (y : K) + 1 ≠ 0 := by
    intro h
    have hyeq : (y : K) = algebraMap F K (-1 / 2) := by
      simp only [map_div₀, map_neg, map_one, map_ofNat]
      apply (eq_div_iff htwo).mpr
      linear_combination h
    apply generator_not_mem L₂ L₁ h₁₂.symm y hygen
    rw [hyeq]
    exact L₁.algebraMap_mem _
  have hzgen : Algebra.adjoin F ({z} : Set L₃) = ⊤ := by
    apply quadratic_adjoin_of_not_mem_range
    rintro ⟨c, hc⟩
    have hcK : algebraMap F K c = Z := by
      rw [IsScalarTower.algebraMap_apply F L₃ K, hc]
      exact hz
    have hcard : Fintype.card Gal(K/L₁) = 2 := by
      rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank,
        Algebra.IsQuadraticExtension.finrank_eq_two L₁ K]
    obtain ⟨sigma, hsigma⟩ := Fintype.exists_ne_of_one_lt_card
      (by omega : 1 < Fintype.card Gal(K/L₁)) (1 : Gal(K/L₁))
    have hsy := nontrivial_map_artinSchreier_root (y : K)
      (algebraMap F L₁ g)
      (hyK.trans (IsScalarTower.algebraMap_apply F L₁ K g)) hygen₁ sigma hsigma
    have hsx : sigma (x : K) = (x : K) := sigma.commutes x
    have hsZ : sigma Z = Z := by
      rw [← hcK, IsScalarTower.algebraMap_apply F L₁ K]
      exact sigma.commutes _
    simp only [Z, map_add, map_mul, map_ofNat, hsx, hsy] at hsZ
    have hprod : (2 * (x : K) + 1) * (2 * (y : K) + 1) = 0 := by
      linear_combination -hsZ
    exact (mul_ne_zero hxden hyden) hprod
  exact ⟨z, hz, hzpoly, hzgen, hygen₁, hxgen₂, hxgen₃, hygen₃⟩

/-- A root of an Artin--Schreier-shaped equation with negative base order
has the expected normalized order on a totally ramified quadratic edge. -/
private theorem artinSchreier_root_order
    (E M : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    [Algebra E M] [ValuativeExtension E M]
    (u : M) (c : E) (q : ℕ)
    (hq : 1 ≤ q)
    (hram : ramificationIndex E M = 2)
    (hc : ord E c = (((1 : ℤ) - 2 * q : ℤ) : WithTop ℤ))
    (hu : u ^ 2 + u = algebraMap E M c) :
    ord M u = (((1 : ℤ) - 2 * q : ℤ) : WithTop ℤ) := by
  have hcmap : ord M (algebraMap E M c) =
      (((2 : ℤ) * (1 - 2 * q) : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hram, hc, ← WithTop.coe_nsmul]
    congr 1
  have hneg : ord M u < 0 := by
    by_contra hu0
    have hu0' : (0 : WithTop ℤ) ≤ ord M u := le_of_not_gt hu0
    have hsq0 : (0 : WithTop ℤ) ≤ ord M (u ^ 2) := by
      rw [ord_pow]
      exact nsmul_nonneg hu0' 2
    have hadd0 : (0 : WithTop ℤ) ≤ ord M (u ^ 2 + u) :=
      le_trans (le_min hsq0 hu0') (ord_add _ _ _)
    rw [hu, hcmap] at hadd0
    have hbad : (0 : ℤ) ≤ 2 * (1 - 2 * (q : ℤ)) :=
      WithTop.coe_le_coe.mp hadd0
    omega
  have hfinite : ord M u ≠ ⊤ := by
    intro htop
    rw [htop] at hneg
    simp at hneg
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hvneg : v < 0 := by
    rw [← hv] at hneg
    exact WithTop.coe_lt_coe.mp hneg
  have hpowlt : ord M (u ^ 2) < ord M u := by
    rw [ord_pow, ← hv, ← WithTop.coe_nsmul]
    exact_mod_cast (show 2 • v < v by simp only [two_nsmul]; omega)
  have hsum : ord M (u ^ 2 + u) = ord M (u ^ 2) := by
    rw [ord_add_eq_min M (ne_of_lt hpowlt), min_eq_left hpowlt.le]
  rw [hu, hcmap, ord_pow, two_nsmul] at hsum
  rw [← hv, ← WithTop.coe_add] at hsum
  have hInt : v + v = 2 * (1 - 2 * (q : ℤ)) := (WithTop.coe_eq_coe.mp hsum).symm
  rw [← hv]
  congr 1
  omega

/-- The complete exact data attached to the mixed-characteristic
nonmaximal origin `Y = x + d y`. The six coordinates are indices, so
the exported data refers to the supplied aligned coordinates definitionally. -/
structure DyadicNonmaximalOriginData
    (F K : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [Module.Finite F K]
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
    (a r : ℕ) (x : L₁) (y : L₂) (z : L₃) (f g d : F) where
  E : F
  k₀ : F
  Y : K
  x_polynomial : x ^ 2 + x = algebraMap F L₁ f
  y_polynomial : y ^ 2 + y = algebraMap F L₂ g
  z_polynomial : z ^ 2 + z = algebraMap F L₃ (f + g + 4 * f * g)
  x_generates : Algebra.adjoin F ({x} : Set L₁) = ⊤
  y_generates : Algebra.adjoin F ({y} : Set L₂) = ⊤
  z_generates : Algebra.adjoin F ({z} : Set L₃) = ⊤
  y_generates_over₁ : Algebra.adjoin L₁ ({(y : K)} : Set K) = ⊤
  x_generates_over₂ : Algebra.adjoin L₂ ({(x : K)} : Set K) = ⊤
  x_generates_over₃ : Algebra.adjoin L₃ ({(x : K)} : Set K) = ⊤
  y_generates_over₃ : Algebra.adjoin L₃ ({(y : K)} : Set K) = ⊤
  f_order : ord F f = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ)
  g_order : ord F g = (((1 : ℤ) - 2 * r : ℤ) : WithTop ℤ)
  d_order : ord F d = (((r : ℤ) - a : ℤ) : WithTop ℤ)
  x_order : ord L₁ x = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ)
  y_order : ord L₂ y = (((1 : ℤ) - 2 * r : ℤ) : WithTop ℤ)
  E_lattice : E ∈ lattice F (1 - (a : ℤ))
  k₀_order : ord F k₀ = 0
  E_eq : E = f + d ^ 2 * g
  k₀_eq : k₀ = 1 + d
  Y_eq : Y = (x : K) + algebraMap F K d * (y : K)
  z_eq : (z : K) = (x : K) + (y : K) + 2 * (x : K) * (y : K)
  upperTrace₁ : trace L₁ K Y = 2 * x - algebraMap F L₁ d
  upperTrace₂ : trace L₂ K Y = 2 * algebraMap F L₂ d * y - 1
  upperTrace₃ : trace L₃ K Y = -algebraMap F L₃ k₀
  upperNorm₁ : norm L₁ K Y =
    2 * algebraMap F L₁ f - algebraMap F L₁ E - algebraMap F L₁ k₀ * x
  upperNorm₂ : norm L₂ K Y =
    algebraMap F L₂ E - 2 * algebraMap F L₂ f - algebraMap F L₂ (d * k₀) * y
  upperNorm₃ : norm L₃ K Y = -algebraMap F L₃ E - algebraMap F L₃ d * z
  lowerNormTrace₁ : norm F L₁ (trace L₁ K Y) = d ^ 2 + 2 * d - 4 * f
  lowerNormTrace₂ : norm F L₂ (trace L₂ K Y) = 1 + 2 * d - 4 * d ^ 2 * g
  lowerNormTrace₃ : norm F L₃ (trace L₃ K Y) = k₀ ^ 2
  e2₁ : elementarySymmetric F K 2 Y =
    trace F L₁ (norm L₁ K Y) + norm F L₁ (trace L₁ K Y)
  e2₂ : elementarySymmetric F K 2 Y =
    trace F L₂ (norm L₂ K Y) + norm F L₂ (trace L₂ K Y)
  e2₃ : elementarySymmetric F K 2 Y =
    trace F L₃ (norm L₃ K Y) + norm F L₃ (trace L₃ K Y)
  z_order : ord L₃ z = (((1 : ℤ) - 2 * r : ℤ) : WithTop ℤ)
  Y_order : ord K Y = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ)
  upperNorm₁_order : ord L₁ (norm L₁ K Y) = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ)
  upperNorm₂_order : ord L₂ (norm L₂ K Y) = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ)
  upperNorm₃_order : ord L₃ (norm L₃ K Y) = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ)
  upperTrace₁_order : ord L₁ (trace L₁ K Y) =
    (((2 : ℤ) * (r - a) : ℤ) : WithTop ℤ)
  upperTrace₂_order : ord L₂ (trace L₂ K Y) = 0
  upperTrace₃_order : ord L₃ (trace L₃ K Y) = 0
  totalTrace : trace F K Y = -2 * k₀
  lowerNormTrace₁_order : ord F (norm F L₁ (trace L₁ K Y)) =
    (((2 : ℤ) * (r - a) : ℤ) : WithTop ℤ)
  lowerNormTrace₂_order : ord F (norm F L₂ (trace L₂ K Y)) = 0
  lowerNormTrace₃_order : ord F (norm F L₃ (trace L₃ K Y)) = 0
  upperTraces_ne_zero : trace L₁ K Y ≠ 0 ∧ trace L₂ K Y ≠ 0 ∧ trace L₃ K Y ≠ 0
  lowerNormTraces_ne_zero : norm F L₁ (trace L₁ K Y) ≠ 0 ∧
    norm F L₂ (trace L₂ K Y) ≠ 0 ∧ norm F L₃ (trace L₃ K Y) ≠ 0

/-! ## Quadratic tower and coordinate algebra -/

/-- The residue-degree-one hypothesis computes the ramification index on
any of the actual quadratic edges. -/
private theorem quadratic_ramificationIndex
    (E M : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    [Algebra E M] [ValuativeExtension E M] [Module.Finite E M]
    [Algebra.IsQuadraticExtension E M]
    (hres : residueDegree E M = 1) : ramificationIndex E M = 2 := by
  simpa [hres, Algebra.IsQuadraticExtension.finrank_eq_two E M] using
    (finrank_eq_ramificationIndex_mul_residueDegree E M).symm

private theorem quadratic_galois_card
    (E M : Type*) [Field E] [Field M] [Algebra E M]
    [Module.Finite E M] [IsGalois E M] [Algebra.IsQuadraticExtension E M] :
    Fintype.card Gal(M/E) = 2 := by
  rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank,
    Algebra.IsQuadraticExtension.finrank_eq_two E M]

section CoordinateAlgebra

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
variable {L₁ L₂ L₃ : IntermediateField F K}

/-- The coordinate bridge for the supplied third coordinate, with named
fields for its polynomial and cross-field generation statements. -/
private structure OriginCoordinateData (x : L₁) (y : L₂) (z : L₃) (f g : F) : Prop where
  z_polynomial : z ^ 2 + z = algebraMap F L₃ (f + g + 4 * f * g)
  z_generates : Algebra.adjoin F ({z} : Set L₃) = ⊤
  y_generates_over₁ : Algebra.adjoin L₁ ({(y : K)} : Set K) = ⊤
  x_generates_over₂ : Algebra.adjoin L₂ ({(x : K)} : Set K) = ⊤
  x_generates_over₃ : Algebra.adjoin L₃ ({(x : K)} : Set K) = ⊤
  y_generates_over₃ : Algebra.adjoin L₃ ({(y : K)} : Set K) = ⊤

private theorem origin_coordinate_data
    [Module.Finite F L₁] [Module.Finite F L₂] [Module.Finite F L₃]
    [Module.Finite L₁ K] [Module.Finite L₃ K]
    [Algebra.IsQuadraticExtension F L₁] [Algebra.IsQuadraticExtension F L₂]
    [Algebra.IsQuadraticExtension F L₃] [Algebra.IsQuadraticExtension L₁ K]
    [Algebra.IsQuadraticExtension L₂ K] [Algebra.IsQuadraticExtension L₃ K]
    [IsGalois L₁ K] [IsGalois L₃ K]
    (h₁₂ : L₁ ≠ L₂) (h₁₃ : L₁ ≠ L₃) (h₂₃ : L₂ ≠ L₃) (htwo : (2 : K) ≠ 0)
    (x : L₁) (y : L₂) (z : L₃) (f g : F)
    (hx : x ^ 2 + x = algebraMap F L₁ f)
    (hy : y ^ 2 + y = algebraMap F L₂ g)
    (hz : (z : K) = (x : K) + (y : K) + 2 * (x : K) * (y : K))
    (hxgen : Algebra.adjoin F ({x} : Set L₁) = ⊤)
    (hygen : Algebra.adjoin F ({y} : Set L₂) = ⊤) :
    OriginCoordinateData x y z f g := by
  obtain ⟨z', hz', hzpoly, hzgen, hygen₁, hxgen₂, hxgen₃, hygen₃⟩ :=
    dyadicNonmaximal_coordinate_bridge L₁ L₂ L₃ h₁₂ h₁₃ h₂₃ htwo x y f g
      hx hy hxgen hygen
  have hzz : z' = z := Subtype.ext (hz'.trans hz.symm)
  subst z'
  exact ⟨hzpoly, hzgen, hygen₁, hxgen₂, hxgen₃, hygen₃⟩

/-- The exact upper trace and norm tables in `D:NM:htable` and
`D:NM:atable`, before any valuation estimates. -/
private structure OriginUpperTable (x : L₁) (y : L₂) (z : L₃)
    (f d E k₀ : F) (Y : K) : Prop where
  trace₁ : trace L₁ K Y = 2 * x - algebraMap F L₁ d
  trace₂ : trace L₂ K Y = 2 * algebraMap F L₂ d * y - 1
  trace₃ : trace L₃ K Y = -algebraMap F L₃ k₀
  norm₁ : norm L₁ K Y =
    2 * algebraMap F L₁ f - algebraMap F L₁ E - algebraMap F L₁ k₀ * x
  norm₂ : norm L₂ K Y =
    algebraMap F L₂ E - 2 * algebraMap F L₂ f - algebraMap F L₂ (d * k₀) * y
  norm₃ : norm L₃ K Y = -algebraMap F L₃ E - algebraMap F L₃ d * z

private theorem origin_upper_table
    [Module.Finite L₁ K] [Module.Finite L₂ K] [Module.Finite L₃ K]
    [IsGalois L₁ K] [IsGalois L₂ K] [IsGalois L₃ K]
    [Algebra.IsQuadraticExtension L₁ K] [Algebra.IsQuadraticExtension L₂ K]
    [Algebra.IsQuadraticExtension L₃ K]
    (x : L₁) (y : L₂) (z : L₃) (f g d : F)
    (hx : x ^ 2 + x = algebraMap F L₁ f)
    (hy : y ^ 2 + y = algebraMap F L₂ g)
    (hz : (z : K) = (x : K) + (y : K) + 2 * (x : K) * (y : K))
    (C : OriginCoordinateData x y z f g) :
    OriginUpperTable x y z f d (f + d ^ 2 * g) (1 + d)
      ((x : K) + algebraMap F K d * (y : K)) := by
  classical
  let E : F := f + d ^ 2 * g
  let k₀ : F := 1 + d
  let Y : K := (x : K) + algebraMap F K d * (y : K)
  have hxK : (x : K) ^ 2 + (x : K) = algebraMap F K f := by
    calc
      (x : K) ^ 2 + (x : K) = algebraMap L₁ K (x ^ 2 + x) := by simp
      _ = algebraMap L₁ K (algebraMap F L₁ f) := congrArg (algebraMap L₁ K) hx
      _ = algebraMap F K f := (IsScalarTower.algebraMap_apply F L₁ K f).symm
  have hyK : (y : K) ^ 2 + (y : K) = algebraMap F K g := by
    calc
      (y : K) ^ 2 + (y : K) = algebraMap L₂ K (y ^ 2 + y) := by simp
      _ = algebraMap L₂ K (algebraMap F L₂ g) := congrArg (algebraMap L₂ K) hy
      _ = algebraMap F K g := (IsScalarTower.algebraMap_apply F L₂ K g).symm

  have hcard₁K := quadratic_galois_card L₁ K
  have hcard₂K := quadratic_galois_card L₂ K
  have hcard₃K := quadratic_galois_card L₃ K
  obtain ⟨sigma₁, hsigma₁⟩ := Fintype.exists_ne_of_one_lt_card
    (by omega : 1 < Fintype.card Gal(K/L₁)) (1 : Gal(K/L₁))
  obtain ⟨sigma₂, hsigma₂⟩ := Fintype.exists_ne_of_one_lt_card
    (by omega : 1 < Fintype.card Gal(K/L₂)) (1 : Gal(K/L₂))
  obtain ⟨sigma₃, hsigma₃⟩ := Fintype.exists_ne_of_one_lt_card
    (by omega : 1 < Fintype.card Gal(K/L₃)) (1 : Gal(K/L₃))
  have hyK₁ : (y : K) ^ 2 + (y : K) =
      algebraMap L₁ K (algebraMap F L₁ g) := by
    exact hyK.trans (IsScalarTower.algebraMap_apply F L₁ K g)
  have hxK₂ : (x : K) ^ 2 + (x : K) =
      algebraMap L₂ K (algebraMap F L₂ f) := by
    exact hxK.trans (IsScalarTower.algebraMap_apply F L₂ K f)
  have hxK₃ : (x : K) ^ 2 + (x : K) =
      algebraMap L₃ K (algebraMap F L₃ f) := by
    exact hxK.trans (IsScalarTower.algebraMap_apply F L₃ K f)
  have hyK₃ : (y : K) ^ 2 + (y : K) =
      algebraMap L₃ K (algebraMap F L₃ g) := by
    exact hyK.trans (IsScalarTower.algebraMap_apply F L₃ K g)
  have hsigma₁y : sigma₁ (y : K) = -1 - (y : K) :=
    nontrivial_map_artinSchreier_root (y : K) (algebraMap F L₁ g)
      hyK₁ C.y_generates_over₁ sigma₁ hsigma₁
  have hsigma₁x : sigma₁ (x : K) = (x : K) := sigma₁.commutes x
  have hsigma₁d : sigma₁ (algebraMap F K d) = algebraMap F K d := by
    rw [IsScalarTower.algebraMap_apply F L₁ K]
    exact sigma₁.commutes (algebraMap F L₁ d)
  have hsigma₂x : sigma₂ (x : K) = -1 - (x : K) :=
    nontrivial_map_artinSchreier_root (x : K) (algebraMap F L₂ f)
      hxK₂ C.x_generates_over₂ sigma₂ hsigma₂
  have hsigma₂y : sigma₂ (y : K) = (y : K) := sigma₂.commutes y
  have hsigma₂d : sigma₂ (algebraMap F K d) = algebraMap F K d := by
    rw [IsScalarTower.algebraMap_apply F L₂ K]
    exact sigma₂.commutes (algebraMap F L₂ d)
  have hsigma₃x : sigma₃ (x : K) = -1 - (x : K) :=
    nontrivial_map_artinSchreier_root (x : K) (algebraMap F L₃ f)
      hxK₃ C.x_generates_over₃ sigma₃ hsigma₃
  have hsigma₃y : sigma₃ (y : K) = -1 - (y : K) :=
    nontrivial_map_artinSchreier_root (y : K) (algebraMap F L₃ g)
      hyK₃ C.y_generates_over₃ sigma₃ hsigma₃
  have hsigma₃d : sigma₃ (algebraMap F K d) = algebraMap F K d := by
    rw [IsScalarTower.algebraMap_apply F L₃ K]
    exact sigma₃.commutes (algebraMap F L₃ d)

  have htrace₁ : trace L₁ K Y = 2 * x - algebraMap F L₁ d := by
    apply (algebraMap L₁ K).injective
    rw [trace_eq_self_add_nontrivial sigma₁ hsigma₁ hcard₁K]
    simp only [map_sub, map_mul, map_ofNat]
    simp_rw [← IsScalarTower.algebraMap_apply F L₁ K]
    simp only [IntermediateField.algebraMap_apply, Y, map_add, map_mul,
      hsigma₁x, hsigma₁d, hsigma₁y]
    ring
  have htrace₂ : trace L₂ K Y = 2 * algebraMap F L₂ d * y - 1 := by
    apply (algebraMap L₂ K).injective
    rw [trace_eq_self_add_nontrivial sigma₂ hsigma₂ hcard₂K]
    simp only [map_sub, map_mul, map_ofNat, map_one]
    simp_rw [← IsScalarTower.algebraMap_apply F L₂ K]
    simp only [IntermediateField.algebraMap_apply, Y, map_add, map_mul,
      hsigma₂x, hsigma₂d, hsigma₂y]
    ring
  have htrace₃ : trace L₃ K Y = -algebraMap F L₃ k₀ := by
    apply (algebraMap L₃ K).injective
    rw [trace_eq_self_add_nontrivial sigma₃ hsigma₃ hcard₃K]
    simp only [map_neg]
    simp_rw [← IsScalarTower.algebraMap_apply F L₃ K]
    simp only [Y, map_add, map_mul, hsigma₃x, hsigma₃y, hsigma₃d, k₀, map_one]
    ring
  have hnorm₁ : norm L₁ K Y =
      2 * algebraMap F L₁ f - algebraMap F L₁ E - algebraMap F L₁ k₀ * x := by
    apply (algebraMap L₁ K).injective
    rw [norm_eq_self_mul_nontrivial sigma₁ hsigma₁ hcard₁K]
    simp only [map_sub, map_mul, map_ofNat]
    simp_rw [← IsScalarTower.algebraMap_apply F L₁ K]
    simp only [IntermediateField.algebraMap_apply, Y, hsigma₁x, hsigma₁d, hsigma₁y,
      E, k₀, map_add, map_mul, map_pow, map_one]
    rw [← hxK, ← hyK]
    ring
  have hnorm₂ : norm L₂ K Y =
      algebraMap F L₂ E - 2 * algebraMap F L₂ f -
        algebraMap F L₂ (d * k₀) * y := by
    apply (algebraMap L₂ K).injective
    rw [norm_eq_self_mul_nontrivial sigma₂ hsigma₂ hcard₂K]
    simp only [map_sub, map_mul, map_ofNat]
    simp_rw [← IsScalarTower.algebraMap_apply F L₂ K]
    simp only [IntermediateField.algebraMap_apply, Y, hsigma₂x, hsigma₂d, hsigma₂y,
      E, k₀, map_add, map_mul, map_pow, map_one]
    rw [← hxK, ← hyK]
    ring
  have hnorm₃ : norm L₃ K Y =
      -algebraMap F L₃ E - algebraMap F L₃ d * z := by
    apply (algebraMap L₃ K).injective
    rw [norm_eq_self_mul_nontrivial sigma₃ hsigma₃ hcard₃K]
    simp only [map_neg, map_sub, map_mul]
    simp_rw [← IsScalarTower.algebraMap_apply F L₃ K]
    simp only [IntermediateField.algebraMap_apply, Y, hsigma₃x, hsigma₃y, hsigma₃d,
      E, map_add, map_mul, map_pow]
    rw [hz]
    rw [← hxK, ← hyK]
    ring

  exact ⟨htrace₁, htrace₂, htrace₃, hnorm₁, hnorm₂, hnorm₃⟩

/-- Norms of the exact upper traces (`D:NM:betatable`) and the total trace. -/
private theorem origin_lower_norm_traces
    [Module.Finite F K] [Module.Finite F L₁] [Module.Finite F L₂]
    [Module.Finite F L₃] [Module.Finite L₃ K]
    [IsGalois F L₁] [IsGalois F L₂]
    [Algebra.IsQuadraticExtension F L₁] [Algebra.IsQuadraticExtension F L₂]
    [Algebra.IsQuadraticExtension F L₃]
    (x : L₁) (y : L₂) (z : L₃) (f g d E k₀ : F) (Y : K)
    (hx : x ^ 2 + x = algebraMap F L₁ f)
    (hy : y ^ 2 + y = algebraMap F L₂ g)
    (hxgen : Algebra.adjoin F ({x} : Set L₁) = ⊤)
    (hygen : Algebra.adjoin F ({y} : Set L₂) = ⊤)
    (T : OriginUpperTable x y z f d E k₀ Y) :
    norm F L₁ (trace L₁ K Y) = d ^ 2 + 2 * d - 4 * f ∧
      norm F L₂ (trace L₂ K Y) = 1 + 2 * d - 4 * d ^ 2 * g ∧
      norm F L₃ (trace L₃ K Y) = k₀ ^ 2 ∧
      trace F K Y = -2 * k₀ := by
  classical
  have hdeg₃ := Algebra.IsQuadraticExtension.finrank_eq_two F L₃
  have hcard₁ := quadratic_galois_card F L₁
  have hcard₂ := quadratic_galois_card F L₂
  obtain ⟨tau₁, htau₁⟩ := Fintype.exists_ne_of_one_lt_card
    (by omega : 1 < Fintype.card Gal(L₁/F)) (1 : Gal(L₁/F))
  obtain ⟨tau₂, htau₂⟩ := Fintype.exists_ne_of_one_lt_card
    (by omega : 1 < Fintype.card Gal(L₂/F)) (1 : Gal(L₂/F))
  have htau₁x : tau₁ x = -1 - x :=
    nontrivial_map_artinSchreier_root x f hx hxgen tau₁ htau₁
  have htau₁d : tau₁ (algebraMap F L₁ d) = algebraMap F L₁ d := tau₁.commutes d
  have htau₂y : tau₂ y = -1 - y :=
    nontrivial_map_artinSchreier_root y g hy hygen tau₂ htau₂
  have htau₂d : tau₂ (algebraMap F L₂ d) = algebraMap F L₂ d := tau₂.commutes d
  have hbeta₁ : norm F L₁ (trace L₁ K Y) = d ^ 2 + 2 * d - 4 * f := by
    apply (algebraMap F L₁).injective
    rw [norm_eq_self_mul_nontrivial tau₁ htau₁ hcard₁]
    simp only [T.trace₁, map_sub, map_add, map_mul, map_pow, map_ofNat,
      htau₁x, htau₁d]
    rw [← hx]
    ring
  have hbeta₂ : norm F L₂ (trace L₂ K Y) = 1 + 2 * d - 4 * d ^ 2 * g := by
    apply (algebraMap F L₂).injective
    rw [norm_eq_self_mul_nontrivial tau₂ htau₂ hcard₂]
    simp only [T.trace₂, map_sub, map_add, map_mul, map_pow, map_ofNat, map_one,
      htau₂y, htau₂d]
    rw [← hy]
    ring
  have hbeta₃ : norm F L₃ (trace L₃ K Y) = k₀ ^ 2 := by
    rw [T.trace₃, ← map_neg, LanglandsFirstMainLemma.norm_algebraMap, hdeg₃]
    ring

  have htotalTrace : trace F K Y = -2 * k₀ := by
    rw [← Algebra.trace_trace (R := F) (S := L₃) (T := K) Y, T.trace₃]
    rw [map_neg, trace_algebraMap, hdeg₃]
    simp
  exact ⟨hbeta₁, hbeta₂, hbeta₃, htotalTrace⟩

end CoordinateAlgebra

/-! ## Valuation estimates -/

section OrderEstimates

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Subtracting a term of strictly smaller order determines the order. -/
private theorem ord_sub_of_right_lt (u v : F) (h : ord F v < ord F u) :
    ord F (u - v) = ord F v := by
  rw [sub_eq_add_neg, ord_add_eq_min F (by simpa using ne_of_gt h),
    ord_neg, min_eq_right h.le]

/-- At equal breaks the alignment unit prevents cancellation in `f + g`;
at unequal breaks `g` has strictly smaller order. -/
private theorem aligned_sum_order
    (e a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ)) (f g d : F)
    (hf : ord F f = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ))
    (hg : ord F g = (((1 : ℤ) - 2 * r : ℤ) : WithTop ℤ))
    (hE : f + d ^ 2 * g ∈ lattice F (1 - (a : ℤ)))
    (hk₀ : ord F (1 + d) = 0) :
    ord F (f + g) = (((1 : ℤ) - 2 * r : ℤ) : WithTop ℤ) := by
  let E : F := f + d ^ 2 * g
  by_cases hra : r = a
  · subst r
    have hminus : ord F (1 - d) = 0 := by
      have hepos : (0 : WithTop ℤ) < (e : WithTop ℤ) := by
        exact_mod_cast (show 0 < e by omega)
      rw [show 1 - d = 2 - (1 + d) by ring,
        ord_sub_of_right_lt F _ _ (by rw [htwo, hk₀]; exact hepos), hk₀]
    have honeSq : ord F (1 - d ^ 2) = 0 := by
      rw [show 1 - d ^ 2 = (1 - d) * (1 + d) by ring,
        ord_mul, hminus, hk₀, zero_add]
    have hterm : ord F ((1 - d ^ 2) * g) =
        (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ) := by
      rw [ord_mul, honeSq, hg, zero_add]
    have hEdeep : (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ) < ord F E := by
      have hmem : (((1 : ℤ) - a : ℤ) : WithTop ℤ) ≤ ord F E := by
        simpa [E, mem_lattice] using hE
      have hlt : (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ) <
          (((1 : ℤ) - a : ℤ) : WithTop ℤ) := by
        exact_mod_cast (show 1 - 2 * (a : ℤ) < 1 - a by omega)
      exact hlt.trans_le hmem
    rw [show f + g = E + (1 - d ^ 2) * g by simp only [E]; ring]
    rw [ord_add_eq_min F (by rw [hterm]; exact ne_of_gt hEdeep),
      hterm, min_eq_right hEdeep.le]
  · have hrg : (((1 : ℤ) - 2 * r : ℤ) : WithTop ℤ) <
        (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ) := by
      exact_mod_cast (show 1 - 2 * (r : ℤ) < 1 - 2 * a by omega)
    rw [ord_add_eq_min F (by rw [hf, hg]; exact ne_of_gt hrg),
      hf, hg, min_eq_right hrg.le]

/-- The correction `4fg` is strictly deeper than `f + g` in `D:NM:zpoly`. -/
private theorem third_polynomial_order
    (e a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ)) (f g d : F)
    (hf : ord F f = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ))
    (hg : ord F g = (((1 : ℤ) - 2 * r : ℤ) : WithTop ℤ))
    (hE : f + d ^ 2 * g ∈ lattice F (1 - (a : ℤ)))
    (hk₀ : ord F (1 + d) = 0) :
    ord F (f + g + 4 * f * g) = (((1 : ℤ) - 2 * r : ℤ) : WithTop ℤ) := by
  have hfg := aligned_sum_order F e a r ha har hre htwo f g d hf hg hE hk₀
  have hfourfg : (((1 : ℤ) - 2 * r : ℤ) : WithTop ℤ) < ord F (4 * f * g) := by
    rw [ord_mul, ord_mul, show (4 : F) = 2 * 2 by norm_num, ord_mul, htwo, hf, hg]
    exact_mod_cast (show 1 - 2 * (r : ℤ) <
      ((e : ℤ) + e) + (1 - 2 * a) + (1 - 2 * r) by omega)
  rw [ord_add_eq_min F (by rw [hfg]; exact ne_of_lt hfourfg),
    hfg, min_eq_left hfourfg.le]

variable {M : Type*} [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M]

/-- Lift the common base-field bound for a norm's constant term. -/
private theorem quadratic_constant_order (a : ℕ) (c : F)
    (hram : ramificationIndex F M = 2)
    (hc : (((1 : ℤ) - a : ℤ) : WithTop ℤ) ≤ ord F c) :
    (((2 : ℤ) - 2 * a : ℤ) : WithTop ℤ) ≤ ord M (algebraMap F M c) := by
  rw [ord_algebraMap, hram]
  calc
    (((2 : ℤ) - 2 * a : ℤ) : WithTop ℤ) =
        2 • (((1 : ℤ) - a : ℤ) : WithTop ℤ) := by
          exact_mod_cast (show 2 - 2 * (a : ℤ) = 2 * (1 - a) by ring)
    _ ≤ 2 • ord F c := nsmul_le_nsmul_right hc 2

/-- Each upper norm has a deeper constant term and a nonconstant term of
exact order `1 - 2a`. -/
private theorem norm_order_of_constant_bound
    (a : ℕ) (u v : F)
    (hu : (((2 : ℤ) - 2 * a : ℤ) : WithTop ℤ) ≤ ord F u)
    (hv : ord F v = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ)) :
    ord F (u - v) = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ) := by
  have hgap : (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ) <
      (((2 : ℤ) - 2 * a : ℤ) : WithTop ℤ) := by
    exact_mod_cast (show 1 - 2 * (a : ℤ) < 2 - 2 * a by omega)
  rw [ord_sub_of_right_lt F u v (by rw [hv]; exact hgap.trans_le hu), hv]

/-- Norms preserve normalized order when the residue degree is one. -/
private theorem norm_order_of_residueDegree_one
    [Module.Finite F M] (hres : residueDegree F M = 1) (u : M) :
    ord F (norm F M u) = ord M u := by
  rw [ord_norm, hres, one_nsmul]

private theorem ne_zero_of_order (u : F) (n : ℤ) (hu : ord F u = (n : WithTop ℤ)) :
    u ≠ 0 :=
  (ord_ne_top_iff F).mp (hu ▸ WithTop.coe_ne_top)

end OrderEstimates

section OriginOrders

variable {F K : Type*}
    [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Field K] [Algebra F K]
    {L₁ L₂ L₃ : IntermediateField F K}
    [ValuativeRel L₁] [TopologicalSpace L₁] [IsNonarchimedeanLocalField L₁]
    [ValuativeRel L₂] [TopologicalSpace L₂] [IsNonarchimedeanLocalField L₂]
    [ValuativeRel L₃] [TopologicalSpace L₃] [IsNonarchimedeanLocalField L₃]
    [ValuativeExtension F L₁] [ValuativeExtension F L₂] [ValuativeExtension F L₃]

private theorem origin_upper_norm_orders
    (e a r : ℕ) (hae : a ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (x : L₁) (y : L₂) (z : L₃) (f d E k₀ : F) (Y : K)
    (hram₁ : ramificationIndex F L₁ = 2)
    (hram₂ : ramificationIndex F L₂ = 2)
    (hram₃ : ramificationIndex F L₃ = 2)
    (hf : ord F f = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ))
    (hd : ord F d = (((r : ℤ) - a : ℤ) : WithTop ℤ))
    (hEord : (((1 : ℤ) - a : ℤ) : WithTop ℤ) ≤ ord F E)
    (hk₀ord : ord F k₀ = 0)
    (hxord : ord L₁ x = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ))
    (hyord : ord L₂ y = (((1 : ℤ) - 2 * r : ℤ) : WithTop ℤ))
    (hzord : ord L₃ z = (((1 : ℤ) - 2 * r : ℤ) : WithTop ℤ))
    (T : OriginUpperTable x y z f d E k₀ Y) :
    ord L₁ (norm L₁ K Y) = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ) ∧
      ord L₂ (norm L₂ K Y) = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ) ∧
      ord L₃ (norm L₃ K Y) = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ) := by
  have htwof : (((1 : ℤ) - a : ℤ) : WithTop ℤ) ≤ ord F (2 * f) := by
    rw [ord_mul, htwo, hf]
    exact_mod_cast (show 1 - (a : ℤ) ≤ (e : ℤ) + (1 - 2 * a) by omega)
  have hbase : (((1 : ℤ) - a : ℤ) : WithTop ℤ) ≤ ord F (2 * f - E) :=
    le_trans (le_min htwof hEord) (ord_sub _ _ _)
  have hconst₁ := quadratic_constant_order F (M := L₁) a (2 * f - E) hram₁ hbase
  have hconst₂ := quadratic_constant_order F (M := L₂) a (E - 2 * f) hram₂
    (by simpa only [ord_sub_swap] using hbase)
  have hconst₃ := quadratic_constant_order F (M := L₃) a (-E) hram₃
    (by simpa only [ord_neg] using hEord)
  simp only [map_sub, map_mul, map_ofNat] at hconst₁ hconst₂
  simp only [map_neg] at hconst₃
  have hvar₁ : ord L₁ (algebraMap F L₁ k₀ * x) =
      (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ) := by
    rw [ord_mul, ord_algebraMap, hram₁, hk₀ord, hxord]
    norm_num
  have hcoef₂ : ord L₂ (algebraMap F L₂ (d * k₀) * y) =
      (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ) := by
    rw [ord_mul, ord_algebraMap, hram₂, ord_mul, hd, hk₀ord, hyord]
    norm_num only [add_zero, two_nsmul]
    exact_mod_cast (show
      ((r : ℤ) - (a : ℤ)) + ((r : ℤ) - (a : ℤ)) +
        (1 - 2 * (r : ℤ)) = 1 - 2 * (a : ℤ) by ring)
  have hcoef₃ : ord L₃ (algebraMap F L₃ d * z) =
      (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ) := by
    rw [ord_mul, ord_algebraMap, hram₃, hd, hzord]
    norm_num only [two_nsmul]
    exact_mod_cast (show
      ((r : ℤ) - (a : ℤ)) + ((r : ℤ) - (a : ℤ)) +
        (1 - 2 * (r : ℤ)) = 1 - 2 * (a : ℤ) by ring)
  rw [T.norm₁, T.norm₂, T.norm₃]
  exact ⟨norm_order_of_constant_bound L₁ a _ _ hconst₁ hvar₁,
    norm_order_of_constant_bound L₂ a _ _ hconst₂ hcoef₂,
    norm_order_of_constant_bound L₃ a _ _ hconst₃ hcoef₃⟩

private theorem origin_upper_trace_orders
    (e a r : ℕ) (hae : a ≤ e) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (x : L₁) (y : L₂) (z : L₃) (f d E k₀ : F) (Y : K)
    (hram₁ : ramificationIndex F L₁ = 2)
    (hram₂ : ramificationIndex F L₂ = 2)
    (hram₃ : ramificationIndex F L₃ = 2)
    (hd : ord F d = (((r : ℤ) - a : ℤ) : WithTop ℤ))
    (hk₀ord : ord F k₀ = 0)
    (hxord : ord L₁ x = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ))
    (hyord : ord L₂ y = (((1 : ℤ) - 2 * r : ℤ) : WithTop ℤ))
    (T : OriginUpperTable x y z f d E k₀ Y) :
    ord L₁ (trace L₁ K Y) = (((2 : ℤ) * (r - a) : ℤ) : WithTop ℤ) ∧
      ord L₂ (trace L₂ K Y) = 0 ∧ ord L₃ (trace L₃ K Y) = 0 := by
  have htrace₁ord : ord L₁ (trace L₁ K Y) =
      (((2 : ℤ) * (r - a) : ℤ) : WithTop ℤ) := by
    rw [T.trace₁]
    have hxterm : ord L₁ (2 * x) =
        (((2 : ℤ) * e + 1 - 2 * a : ℤ) : WithTop ℤ) := by
      rw [show (2 : L₁) = algebraMap F L₁ (2 : F) by
          exact (map_ofNat (algebraMap F L₁) 2).symm,
        ord_mul, ord_algebraMap, hram₁, htwo, hxord]
      norm_num only [two_nsmul]
      exact_mod_cast (show
        (e : ℤ) + (e : ℤ) + (1 - 2 * (a : ℤ)) =
          2 * (e : ℤ) + 1 - 2 * (a : ℤ) by ring)
    have hdterm : ord L₁ (algebraMap F L₁ d) =
        (((2 : ℤ) * (r - a) : ℤ) : WithTop ℤ) := by
      rw [ord_algebraMap, hram₁, hd]
      norm_num only [two_nsmul]
      exact_mod_cast (show
        ((r : ℤ) - a) + (r - a) = 2 * (r - a) by ring)
    have hlt : (((2 : ℤ) * (r - a) : ℤ) : WithTop ℤ) <
        (((2 : ℤ) * e + 1 - 2 * a : ℤ) : WithTop ℤ) := by
      exact_mod_cast (show 2 * ((r : ℤ) - a) < 2 * e + 1 - 2 * a by omega)
    rw [ord_sub_of_right_lt L₁ _ _ (by rw [hxterm, hdterm]; exact hlt), hdterm]
  have htrace₂ord : ord L₂ (trace L₂ K Y) = 0 := by
    rw [T.trace₂]
    have hpos : (0 : WithTop ℤ) < ord L₂ (2 * algebraMap F L₂ d * y) := by
      rw [ord_mul, ord_mul,
        show (2 : L₂) = algebraMap F L₂ (2 : F) by
          exact (map_ofNat (algebraMap F L₂) 2).symm,
        ord_algebraMap, hram₂, htwo, ord_algebraMap, hram₂, hd, hyord]
      norm_num only [two_nsmul]
      exact_mod_cast (show 0 <
        (e : ℤ) + (e : ℤ) +
          (((r : ℤ) - (a : ℤ)) + ((r : ℤ) - (a : ℤ))) +
            (1 - 2 * (r : ℤ)) by omega)
    rw [ord_sub_of_right_lt L₂ _ _ (by simpa only [ord_one] using hpos), ord_one]
  have htrace₃ord : ord L₃ (trace L₃ K Y) = 0 := by
    rw [T.trace₃, ord_neg, ord_algebraMap, hram₃, hk₀ord]
    norm_num

  exact ⟨htrace₁ord, htrace₂ord, htrace₃ord⟩

end OriginOrders

/-- **Dyadic nonmaximal origin data (Paper 13.2).**

Starting from aligned generators in the three actual quadratic intermediate
fields, this constructs `Y = x + d y` and proves the complete exact
norm/trace tables and `D:NM:originvals`. The final hypotheses are the
valuation and unit assertions furnished by `alignment`; none of the norms,
traces, or resulting valuations is assumed.
-/
theorem dyadicNonmaximal_origin_data
    (F K : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    [IsKleinFour Gal(K/F)]
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
    [IsGalois F L₁] [IsGalois L₁ K]
    [IsGalois F L₂] [IsGalois L₂ K]
    [IsGalois F L₃] [IsGalois L₃ K]
    [Algebra.IsQuadraticExtension F L₁]
    [Algebra.IsQuadraticExtension L₁ K]
    [Algebra.IsQuadraticExtension F L₂]
    [Algebra.IsQuadraticExtension L₂ K]
    [Algebra.IsQuadraticExtension F L₃]
    [Algebra.IsQuadraticExtension L₃ K]
    (h₁₂ : L₁ ≠ L₂) (h₁₃ : L₁ ≠ L₃) (h₂₃ : L₂ ≠ L₃)
    (hres₁ : residueDegree F L₁ = 1) (hres₂ : residueDegree F L₂ = 1)
    (hres₃ : residueDegree F L₃ = 1)
    (hres₁K : residueDegree L₁ K = 1)
    (e a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (x : L₁) (y : L₂) (z : L₃) (f g d : F)
    (hx : x ^ 2 + x = algebraMap F L₁ f)
    (hy : y ^ 2 + y = algebraMap F L₂ g)
    (hz : (z : K) = (x : K) + (y : K) + 2 * (x : K) * (y : K))
    (hxgen : Algebra.adjoin F ({x} : Set L₁) = ⊤)
    (hygen : Algebra.adjoin F ({y} : Set L₂) = ⊤)
    (hf : ord F f = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ))
    (hg : ord F g = (((1 : ℤ) - 2 * r : ℤ) : WithTop ℤ))
    (hd : ord F d = (((r : ℤ) - a : ℤ) : WithTop ℤ))
    (hE : f + d ^ 2 * g ∈ lattice F (1 - (a : ℤ)))
    (hk₀ : ord F (1 + d) = 0) :
    Nonempty (DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d) := by
  classical
  have htwoF : (2 : F) ≠ 0 := (ord_ne_top_iff F).mp (by rw [htwo]; simp)
  have htwoK : (2 : K) ≠ 0 := by
    simpa only [map_ofNat] using ((map_ne_zero (algebraMap F K)).mpr htwoF)
  have C := origin_coordinate_data h₁₂ h₁₃ h₂₃ htwoK x y z f g hx hy hz hxgen hygen
  have hram₁ := quadratic_ramificationIndex F L₁ hres₁
  have hram₂ := quadratic_ramificationIndex F L₂ hres₂
  have hram₃ := quadratic_ramificationIndex F L₃ hres₃
  have hxord := artinSchreier_root_order F L₁ x f a ha hram₁ hf hx
  have hyord := artinSchreier_root_order F L₂ y g r (ha.trans har) hram₂ hg hy
  have hzord := artinSchreier_root_order F L₃ z (f + g + 4 * f * g) r
    (ha.trans har) hram₃
    (third_polynomial_order F e a r ha har hre htwo f g d hf hg hE hk₀) C.z_polynomial
  let E : F := f + d ^ 2 * g
  let k₀ : F := 1 + d
  let Y : K := (x : K) + algebraMap F K d * (y : K)
  have T : OriginUpperTable x y z f d E k₀ Y :=
    origin_upper_table x y z f g d hx hy hz C
  obtain ⟨hbeta₁, hbeta₂, hbeta₃, htotalTrace⟩ :=
    origin_lower_norm_traces x y z f g d E k₀ Y hx hy hxgen hygen T
  obtain ⟨ha₁ord, ha₂ord, ha₃ord⟩ := origin_upper_norm_orders e a r (har.trans hre)
    htwo x y z f d E k₀ Y hram₁ hram₂ hram₃ hf hd (by simpa [mem_lattice] using hE)
    hk₀ hxord hyord hzord T
  obtain ⟨htrace₁ord, htrace₂ord, htrace₃ord⟩ := origin_upper_trace_orders e a r
    (har.trans hre) hre htwo x y z f d E k₀ Y hram₁ hram₂ hram₃ hd hk₀ hxord hyord T
  have hbeta₁ord := (norm_order_of_residueDegree_one F hres₁ _).trans htrace₁ord
  have hbeta₂ord := (norm_order_of_residueDegree_one F hres₂ _).trans htrace₂ord
  have hbeta₃ord := (norm_order_of_residueDegree_one F hres₃ _).trans htrace₃ord

  exact ⟨{
    E := E
    k₀ := k₀
    Y := Y
    x_polynomial := hx
    y_polynomial := hy
    z_polynomial := C.z_polynomial
    x_generates := hxgen
    y_generates := hygen
    z_generates := C.z_generates
    y_generates_over₁ := C.y_generates_over₁
    x_generates_over₂ := C.x_generates_over₂
    x_generates_over₃ := C.x_generates_over₃
    y_generates_over₃ := C.y_generates_over₃
    f_order := hf
    g_order := hg
    d_order := hd
    x_order := hxord
    y_order := hyord
    E_lattice := hE
    k₀_order := hk₀
    E_eq := rfl
    k₀_eq := rfl
    Y_eq := rfl
    z_eq := hz
    upperTrace₁ := T.trace₁
    upperTrace₂ := T.trace₂
    upperTrace₃ := T.trace₃
    upperNorm₁ := T.norm₁
    upperNorm₂ := T.norm₂
    upperNorm₃ := T.norm₃
    lowerNormTrace₁ := hbeta₁
    lowerNormTrace₂ := hbeta₂
    lowerNormTrace₃ := hbeta₃
    e2₁ := LanglandsSecondMainLemma.Algebra.biquadraticE2 F K L₁ Y
    e2₂ := LanglandsSecondMainLemma.Algebra.biquadraticE2 F K L₂ Y
    e2₃ := LanglandsSecondMainLemma.Algebra.biquadraticE2 F K L₃ Y
    z_order := hzord
    Y_order := (norm_order_of_residueDegree_one L₁ hres₁K Y).symm.trans ha₁ord
    upperNorm₁_order := ha₁ord
    upperNorm₂_order := ha₂ord
    upperNorm₃_order := ha₃ord
    upperTrace₁_order := htrace₁ord
    upperTrace₂_order := htrace₂ord
    upperTrace₃_order := htrace₃ord
    totalTrace := htotalTrace
    lowerNormTrace₁_order := hbeta₁ord
    lowerNormTrace₂_order := hbeta₂ord
    lowerNormTrace₃_order := hbeta₃ord
    upperTraces_ne_zero := ⟨ne_zero_of_order L₁ _ _ htrace₁ord,
      ne_zero_of_order L₂ _ _ htrace₂ord, ne_zero_of_order L₃ _ _ htrace₃ord⟩
    lowerNormTraces_ne_zero := ⟨ne_zero_of_order F _ _ hbeta₁ord,
      ne_zero_of_order F _ _ hbeta₂ord, ne_zero_of_order F _ _ hbeta₃ord⟩ }⟩

/-- Construct the third coordinate and the origin data for supplied aligned
`x,y,f,g,d`. No third coordinate or cross-field generation is assumed. -/
theorem dyadicNonmaximal_origin_data_from_fields
    (F K : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    [IsKleinFour Gal(K/F)]
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
    [IsGalois F L₁] [IsGalois L₁ K]
    [IsGalois F L₂] [IsGalois L₂ K]
    [IsGalois F L₃] [IsGalois L₃ K]
    [Algebra.IsQuadraticExtension F L₁]
    [Algebra.IsQuadraticExtension L₁ K]
    [Algebra.IsQuadraticExtension F L₂]
    [Algebra.IsQuadraticExtension L₂ K]
    [Algebra.IsQuadraticExtension F L₃]
    [Algebra.IsQuadraticExtension L₃ K]
    (h₁₂ : L₁ ≠ L₂) (h₁₃ : L₁ ≠ L₃) (h₂₃ : L₂ ≠ L₃)
    (hres₁ : residueDegree F L₁ = 1) (hres₂ : residueDegree F L₂ = 1)
    (hres₃ : residueDegree F L₃ = 1)
    (hres₁K : residueDegree L₁ K = 1)
    (e a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (x : L₁) (y : L₂) (f g d : F)
    (hx : x ^ 2 + x = algebraMap F L₁ f)
    (hy : y ^ 2 + y = algebraMap F L₂ g)
    (hxgen : Algebra.adjoin F ({x} : Set L₁) = ⊤)
    (hygen : Algebra.adjoin F ({y} : Set L₂) = ⊤)
    (hf : ord F f = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ))
    (hg : ord F g = (((1 : ℤ) - 2 * r : ℤ) : WithTop ℤ))
    (hd : ord F d = (((r : ℤ) - a : ℤ) : WithTop ℤ))
    (hE : f + d ^ 2 * g ∈ lattice F (1 - (a : ℤ)))
    (hk₀ : ord F (1 + d) = 0) :
    ∃ z : L₃, Nonempty (DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d) := by
  have htwoF : (2 : F) ≠ 0 := (ord_ne_top_iff F).mp (by rw [htwo]; simp)
  have htwoK : (2 : K) ≠ 0 := by
    simpa only [map_ofNat] using ((map_ne_zero (algebraMap F K)).mpr htwoF)
  obtain ⟨z, hz, _⟩ := dyadicNonmaximal_coordinate_bridge
    L₁ L₂ L₃ h₁₂ h₁₃ h₂₃ htwoK x y f g hx hy hxgen hygen
  exact ⟨z, dyadicNonmaximal_origin_data F K L₁ L₂ L₃ h₁₂ h₁₃ h₂₃
    hres₁ hres₂ hres₃ hres₁K e a r ha har hre htwo
    x y z f g d hx hy hz hxgen hygen hf hg hd hE hk₀⟩

/-- Assemble alignment and origin from generators of the actual first two
quadratic fields. The bridge supplies the initial third generator needed by
`alignment`, then constructs the third coordinate for the resulting aligned
`x`. The supplied `y,g` are retained as indices in the conclusion. -/
theorem dyadicNonmaximal_origin_data_from_alignment
    (F K : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    [IsKleinFour Gal(K/F)]
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
    [IsGalois F L₁] [IsGalois L₁ K]
    [IsGalois F L₂] [IsGalois L₂ K]
    [IsGalois F L₃] [IsGalois L₃ K]
    [Algebra.IsQuadraticExtension F L₁]
    [Algebra.IsQuadraticExtension L₁ K]
    [Algebra.IsQuadraticExtension F L₂]
    [Algebra.IsQuadraticExtension L₂ K]
    [Algebra.IsQuadraticExtension F L₃]
    [Algebra.IsQuadraticExtension L₃ K]
    (h₁₂ : L₁ ≠ L₂) (h₁₃ : L₁ ≠ L₃) (h₂₃ : L₂ ≠ L₃)
    (hres₁ : residueDegree F L₁ = 1) (hres₂ : residueDegree F L₂ = 1)
    (hres₃ : residueDegree F L₃ = 1)
    (hres₁K : residueDegree L₁ K = 1)
    (e a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (hreschar : residueCharacteristic F = 2)
    (pi : ringOfIntegers F)
    (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F))
    (hdiff₃ : differentExponent F L₃ = 2 * r)
    (x₀ : L₁) (y : L₂) (f₀ g : F)
    (hx₀ : x₀ ^ 2 + x₀ = algebraMap F L₁ f₀)
    (hy : y ^ 2 + y = algebraMap F L₂ g)
    (hx₀gen : Algebra.adjoin F ({x₀} : Set L₁) = ⊤)
    (hygen : Algebra.adjoin F ({y} : Set L₂) = ⊤)
    (hf₀ : ord F f₀ = (((1 : ℤ) - 2 * a : ℤ) : WithTop ℤ))
    (hg : ord F g = (((1 : ℤ) - 2 * r : ℤ) : WithTop ℤ)) :
    ∃ (x : L₁) (f d : F) (z : L₃),
      Nonempty (DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d) := by
  have htwoF : (2 : F) ≠ 0 := (ord_ne_top_iff F).mp (by rw [htwo]; simp)
  have htwoK : (2 : K) ≠ 0 := by
    simpa only [map_ofNat] using ((map_ne_zero (algebraMap F K)).mpr htwoF)
  obtain ⟨z₀, _, hz₀poly, hz₀gen, _⟩ := dyadicNonmaximal_coordinate_bridge
    L₁ L₂ L₃ h₁₂ h₁₃ h₂₃ htwoK x₀ y f₀ g hx₀ hy hx₀gen hygen
  obtain ⟨x, f, d, hx, hxgen, hf, hd, hE, hk₀⟩ :=
    alignment F pi hpi e a r htwo hreschar ha har hre f₀ g x₀ z₀
      hf₀ hg hx₀ hx₀gen hz₀poly hz₀gen hres₃ hdiff₃
  obtain ⟨z, hdata⟩ := dyadicNonmaximal_origin_data_from_fields
    F K L₁ L₂ L₃ h₁₂ h₁₃ h₂₃ hres₁ hres₂ hres₃ hres₁K
    e a r ha har hre htwo x y f g d hx hy hxgen hygen hf hg hd hE hk₀
  exact ⟨x, f, d, z, hdata⟩

end

end LanglandsSecondMainLemma.Dyadic.Nonmaximal
