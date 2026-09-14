import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Characters.QuadraticSymbolProduct
import LanglandsSecondMainLemma.Characters.ArtinSchreierProduct
import LanglandsSecondMainLemma.Characters.CrossedNorm

/-!
# Characters / Quadratic Product

Blueprint: blueprint/tasks/Characters/QuadraticProduct.md
Paper: D:quadratic-norms

The parameter characters are connected to actual quadratic extensions by
transporting their algebraic norms. The characteristic-specific product
identities then apply to the genuine continuous norm characters.
-/

namespace LanglandsSecondMainLemma.Characters

noncomputable section

open LanglandsFirstMainLemma

open private Q qField qTopology qValuativeRel qLocalField qValuativeExtension
  qNormCharacter qNormCharacter_existsUnique quadraticNormCharacter_of_not_isSquare from
  LanglandsSecondMainLemma.Characters.QuadraticSymbolProduct

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A genuine nonscalar square root has nonsquare parameter. -/
theorem nonsquare_of_quadratic_generator
    (E : Type) [Field E] [Algebra F E] (a : Fˣ) (z : E)
    (hz : z ^ 2 = algebraMap F E (a : F))
    (hgen : z ∉ Set.range (algebraMap F E)) : ¬ IsSquare (a : F) := by
  rintro ⟨r, hr⟩
  have hs : z ^ 2 = (algebraMap F E r) ^ 2 := by
    rw [hz, hr, map_mul, pow_two]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · exact hgen ⟨r, h.symm⟩
  · exact hgen ⟨-r, by simpa using h.symm⟩

/-- The character constructed in `QuadraticSymbolProduct` is the nontrivial
norm character of any actual quadratic extension with the given square root.
Only algebraic norm transport is used; no topological equivalence is assumed. -/
theorem quadraticNormCharacter_eq_normCharacter
    (hchar : ringChar F ≠ 2)
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [ValuativeExtension F E]
    [Module.Finite F E]
    (hdegree : Module.finrank F E = 2) (a : Fˣ) (z : E)
    (hz : z ^ 2 = algebraMap F E (a : F))
    (hgen : z ∉ Set.range (algebraMap F E))
    (ω : NormCharacter F E) (hω : ω ≠ 1) :
    ω.1 = quadraticNormCharacter F hchar a := by
  have ha := nonsquare_of_quadratic_generator F E a z hz hgen
  letI : Field (Q F a) := qField F a ha
  letI : TopologicalSpace (Q F a) := qTopology F a ha
  letI : ValuativeRel (Q F a) := qValuativeRel F a ha
  letI : IsNonarchimedeanLocalField (Q F a) := qLocalField F a ha
  letI : ValuativeExtension F (Q F a) := qValuativeExtension F a ha
  let φ : Q F a →ₐ[F] E := QuadraticAlgebra.lift ⟨z, by
    simpa [pow_two, Algebra.smul_def] using hz⟩
  have hdim : Module.finrank F (Q F a) = Module.finrank F E := by
    rw [QuadraticAlgebra.finrank_eq_two, hdegree]
  let e : Q F a ≃ₐ[F] E := AlgEquiv.ofBijective φ
    ⟨φ.injective, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := φ.toLinearMap) hdim).mp
      φ.injective⟩
  let ν : NormCharacter F (Q F a) := ⟨ω.1, by
    apply ContinuousMonoidHom.ext
    intro u
    change ω.1 (normUnits F (Q F a) u) = 1
    have hn : normUnits F (Q F a) u =
        normUnits F E (Units.map e.toMonoidHom u) := by
      apply Units.ext
      exact (Algebra.norm_eq_of_algEquiv e (u : Q F a)).symm
    rw [hn]
    exact ω.eq_one_on_normRange F E _ ⟨_, rfl⟩⟩
  have hν : ν ≠ 1 := by
    intro h
    apply hω
    apply NormCharacter.ext
    exact congrArg (fun η : NormCharacter F (Q F a) ↦ η.1) h
  have heq : ν = qNormCharacter F hchar a ha :=
    (qNormCharacter_existsUnique F hchar a ha).choose_spec.2 ν hν
  rw [quadraticNormCharacter_of_not_isSquare F hchar a ha]
  exact congrArg Subtype.val heq

section QuadraticGenerators

variable (E : Type) [Field E] [Algebra F E] [Module.Finite F E] [IsGalois F E]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem quadratic_fixed_iff (hdegree : Module.finrank F E = 2)
    (σ : Gal(E/F)) (hσ : σ ≠ 1) (x : E) :
    σ x = x ↔ x ∈ Set.range (algebraMap F E) := by
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  constructor
  · intro hx τ
    by_cases hτ : τ = 1
    · simp [hτ]
    · have hc : Nat.card Gal(E/F) = 2 :=
        (IsGalois.card_aut_eq_finrank F E).trans hdegree
      have heq := (Nat.card_eq_two_iff' (1 : Gal(E/F))).mp hc
      rw [heq.unique hτ hσ]
      exact hx
  · exact fun h ↦ h σ

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Every separable quadratic extension in characteristic different from two
has a nonscalar square-root generator. The generator is constructed by
subtracting the nontrivial conjugate of an element it moves. -/
theorem exists_quadratic_generator (hchar : ringChar F ≠ 2)
    (hdegree : Module.finrank F E = 2) :
    ∃ (a : Fˣ) (z : E), z ^ 2 = algebraMap F E (a : F) ∧
      z ∉ Set.range (algebraMap F E) := by
  have hc : Nat.card Gal(E/F) = 2 :=
    (IsGalois.card_aut_eq_finrank F E).trans hdegree
  obtain ⟨σ, hσ, _⟩ := (Nat.card_eq_two_iff' (1 : Gal(E/F))).mp hc
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hσ
  have hxx : σ x ≠ x := hx
  have hσσ (y : E) : σ (σ y) = y := by
    have hs : σ ^ 2 = 1 := by simpa only [hc] using (pow_card_eq_one' (x := σ))
    simpa [pow_two, AlgEquiv.mul_apply] using DFunLike.congr_fun hs y
  let z := x - σ x
  have hz : z ≠ 0 := sub_ne_zero.mpr hxx.symm
  have hconj : σ z = -z := by simp [z, hσσ]
  have hfixed : σ (z ^ 2) = z ^ 2 := by rw [map_pow, hconj, neg_sq]
  obtain ⟨a, ha⟩ := (quadratic_fixed_iff F E hdegree σ hσ (z ^ 2)).mp hfixed
  have ha0 : a ≠ 0 := by
    intro h
    have : z ^ 2 = 0 := by simpa [h] using ha.symm
    exact hz (pow_eq_zero_iff (by decide : 2 ≠ 0) |>.mp this)
  refine ⟨Units.mk0 a ha0, z, ha.symm, ?_⟩
  intro hbase
  have hs := (quadratic_fixed_iff F E hdegree σ hσ z).mpr hbase
  rw [hconj] at hs
  have htwo : (2 : F) ≠ 0 := by
    intro h
    apply Ring.neg_one_ne_one_of_char_ne_two hchar
    linear_combination -h
  have htwoE : (2 : E) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap F E)).mpr htwo
  exact hz ((mul_eq_zero.mp (show (2 : E) * z = 0 by
    linear_combination -hs)).resolve_left htwoE)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- In characteristic two the normalized conjugate difference produces an
Artin--Schreier generator of every separable quadratic extension. -/
theorem exists_artinSchreier_generator [CharP F 2]
    (hdegree : Module.finrank F E = 2) :
    ∃ (a : F) (z : E), z ^ 2 + z = algebraMap F E a ∧
      z ∉ Set.range (algebraMap F E) := by
  letI : CharP E 2 := charP_of_injective_algebraMap (algebraMap F E).injective 2
  have hc : Nat.card Gal(E/F) = 2 :=
    (IsGalois.card_aut_eq_finrank F E).trans hdegree
  obtain ⟨σ, hσ, _⟩ := (Nat.card_eq_two_iff' (1 : Gal(E/F))).mp hc
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hσ
  have hxx : σ x ≠ x := hx
  have hσσ (y : E) : σ (σ y) = y := by
    have hs : σ ^ 2 = 1 := by simpa only [hc] using (pow_card_eq_one' (x := σ))
    simpa [pow_two, AlgEquiv.mul_apply] using DFunLike.congr_fun hs y
  have hd : x + σ x ≠ 0 := by
    intro h
    apply hxx
    simpa only [CharTwo.neg_eq] using (eq_neg_of_add_eq_zero_right h)
  let z := x / (x + σ x)
  have hconj : σ z = z + 1 := by
    dsimp [z]
    rw [map_div₀, map_add, hσσ, add_comm (σ x) x]
    apply (div_eq_iff hd).mpr
    rw [add_mul, div_mul_cancel₀ _ hd, one_mul]
    simp [← add_assoc, CharTwo.add_self_eq_zero]
  have hfixed : σ (z ^ 2 + z) = z ^ 2 + z := by
    rw [map_add, map_pow, hconj, CharTwo.add_sq, one_pow]
    calc
      z ^ 2 + 1 + (z + 1) = (z ^ 2 + z) + (1 + 1) := by ring
      _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]
  obtain ⟨a, ha⟩ := (quadratic_fixed_iff F E hdegree σ hσ _).mp hfixed
  refine ⟨a, z, ha.symm, ?_⟩
  intro hbase
  have hs := (quadratic_fixed_iff F E hdegree σ hσ z).mpr hbase
  rw [hconj] at hs
  exact one_ne_zero (add_eq_left.mp hs)

end QuadraticGenerators

section LowerFields

variable {F} {K : Type} [Field K] [Algebra F K]
  [Module.Finite F K] [IsGalois F K]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem lower_fixing_card (htotal : Module.finrank F K = 4)
    (I : IntermediateField F K) (hI : Module.finrank F I = 2) :
    Nat.card I.fixingSubgroup = 2 := by
  have h := Module.finrank_mul_finrank F I K
  rw [htotal, hI] at h
  rw [IsGalois.card_fixingSubgroup_eq_finrank]
  omega

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem exists_lower_involution (htotal : Module.finrank F K = 4)
    (I : IntermediateField F K) (hI : Module.finrank F I = 2) :
    ∃ σ : Gal(K/F), σ ≠ 1 ∧
      (∀ x : K, σ x = x ↔ x ∈ I) ∧
      (∀ τ : Gal(K/F), τ ≠ 1 → τ ∈ I.fixingSubgroup → τ = σ) := by
  have hc := lower_fixing_card htotal I hI
  obtain ⟨s, hs, huniq⟩ := (Nat.card_eq_two_iff' (1 : I.fixingSubgroup)).mp hc
  have hs' : (s : Gal(K/F)) ≠ 1 := fun h ↦ hs (Subtype.ext h)
  refine ⟨s, hs', ?_, ?_⟩
  · intro x
    conv_rhs => rw [← IsGalois.fixedField_fixingSubgroup I,
      IntermediateField.mem_fixedField_iff]
    constructor
    · intro hx τ hτ
      by_cases ht : τ = 1
      · simp [ht]
      · have ht' : (⟨τ, hτ⟩ : I.fixingSubgroup) ≠ 1 :=
          fun h ↦ ht (congrArg Subtype.val h)
        have heq := congrArg Subtype.val (huniq ⟨τ, hτ⟩ ht')
        change τ = (s : Gal(K/F)) at heq
        rw [heq]
        exact hx
    · exact fun h ↦ h s s.property
  · intro τ ht hτ
    exact congrArg Subtype.val (huniq ⟨τ, hτ⟩ (fun h ↦ ht (congrArg Subtype.val h)))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsGalois F K] in
private theorem involution_moves_other_generator
    (I J : IntermediateField F K) [IsGalois F J]
    (hJ : Module.finrank F J = 2) (hne : I ≠ J)
    (σ τ : Gal(K/F)) (hσ : σ ≠ 1)
    (hfixedI : ∀ x : K, σ x = x ↔ x ∈ I)
    (hfixedJ : ∀ x : K, τ x = x ↔ x ∈ J)
    (huniqJ : ∀ υ : Gal(K/F), υ ≠ 1 → υ ∈ J.fixingSubgroup → υ = τ)
    (z : J) (hgen : z ∉ Set.range (algebraMap F J)) :
    σ (z : K) ≠ (z : K) := by
  have hnot : σ ∉ J.fixingSubgroup := by
    intro h
    have heq := huniqJ σ hσ h
    apply hne
    ext x
    rw [← hfixedI, ← hfixedJ, heq]
  have hrestrict : AlgEquiv.restrictNormalHom J σ ≠ 1 := by
    intro h
    apply hnot
    rw [← IntermediateField.restrictNormalHom_ker]
    exact h
  intro h
  apply hgen
  apply (quadratic_fixed_iff F J hJ _ hrestrict z).mp
  apply Subtype.ext
  simpa only [AlgEquiv.restrictNormalHom_apply] using h

end LowerFields

section Labeling

variable {F} {K : Type} [Field K] [Algebra F K]
  [Module.Finite F K] [IsGalois F K]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem quadratic_labeling (hchar : ringChar F ≠ 2)
    (htotal : Module.finrank F K = 4)
    (L : Fin 3 → IntermediateField F K) [∀ i, IsGalois F (L i)]
    (hdegree : ∀ i, Module.finrank F (L i) = 2) (hne : Function.Injective L) :
    ∃ (a b : Fˣ) (x : L 0) (y : L 1) (z : L 2),
      x ^ 2 = algebraMap F (L 0) (a : F) ∧
      y ^ 2 = algebraMap F (L 1) (b : F) ∧
      z ^ 2 = algebraMap F (L 2) ((a * b : Fˣ) : F) ∧
      x ∉ Set.range (algebraMap F (L 0)) ∧
      y ∉ Set.range (algebraMap F (L 1)) ∧
      z ∉ Set.range (algebraMap F (L 2)) := by
  choose σ hσ hfixed huniq using fun i ↦ exists_lower_involution htotal (L i) (hdegree i)
  have hmove (i j : Fin 3) (hij : i ≠ j) (u : L j)
      (hu : u ∉ Set.range (algebraMap F (L j))) : σ i (u : K) ≠ (u : K) :=
    involution_moves_other_generator (L i) (L j) (hdegree j)
      (fun h ↦ hij (hne h)) (σ i) (σ j) (hσ i) (hfixed i) (hfixed j) (huniq j) u hu
  obtain ⟨a, x, hx, hxgen⟩ := exists_quadratic_generator F (L 0) hchar (hdegree 0)
  obtain ⟨b, y, hy, hygen⟩ := exists_quadratic_generator F (L 1) hchar (hdegree 1)
  have hxK : (x : K) ^ 2 = algebraMap F K (a : F) := by
    simpa only [map_pow, IsScalarTower.algebraMap_apply F (L 0) K,
      IntermediateField.algebraMap_apply] using
      congrArg (algebraMap (L 0) K) hx
  have hyK : (y : K) ^ 2 = algebraMap F K (b : F) := by
    simpa only [map_pow, IsScalarTower.algebraMap_apply F (L 1) K,
      IntermediateField.algebraMap_apply] using
      congrArg (algebraMap (L 1) K) hy
  have hneg (i : Fin 3) {u : K} {c : F} (hu : u ^ 2 = algebraMap F K c)
      (hmove : σ i u ≠ u) : σ i u = -u := by
    apply (sq_eq_sq_iff_eq_or_eq_neg.mp ?_).resolve_left hmove
    rw [← map_pow, hu, AlgEquiv.commutes]
  have hzmem : (x : K) * (y : K) ∈ L 2 := by
    apply (hfixed 2 _).mp
    rw [map_mul, hneg 2 hxK (hmove 2 0 (by decide) x hxgen),
      hneg 2 hyK (hmove 2 1 (by decide) y hygen), neg_mul_neg]
  let z : L 2 := ⟨(x : K) * (y : K), hzmem⟩
  have hz : z ^ 2 = algebraMap F (L 2) ((a * b : Fˣ) : F) := by
    apply (algebraMap (L 2) K).injective
    change ((x : K) * (y : K)) ^ 2 = algebraMap F K ((a : F) * (b : F))
    rw [mul_pow, hxK, hyK, map_mul]
  have hx0 : (x : K) ≠ 0 := by
    intro h
    have : algebraMap F K (a : F) = 0 := by rw [← hxK, h, zero_pow (by decide)]
    exact a.ne_zero ((map_eq_zero (algebraMap F K)).mp this)
  refine ⟨a, b, x, y, z, hx, hy, hz, hxgen, hygen, ?_⟩
  rintro ⟨c, hc⟩
  have hzbase : (x : K) * (y : K) = algebraMap F K c := by
    exact (congrArg (algebraMap (L 2) K) hc).symm
  have hprod : σ 0 ((x : K) * (y : K)) = (x : K) * (y : K) := by
    rw [hzbase, AlgEquiv.commutes]
  rw [map_mul, (hfixed 0 (x : K)).mpr x.property] at hprod
  exact hmove 0 1 (by decide) y hygen (mul_left_cancel₀ hx0 hprod)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem artinSchreier_labeling [CharP F 2]
    (htotal : Module.finrank F K = 4)
    (L : Fin 3 → IntermediateField F K) [∀ i, IsGalois F (L i)]
    (hdegree : ∀ i, Module.finrank F (L i) = 2) (hne : Function.Injective L) :
    ∃ (a b : F) (x : L 0) (y : L 1) (z : L 2),
      x ^ 2 + x = algebraMap F (L 0) a ∧
      y ^ 2 + y = algebraMap F (L 1) b ∧
      z ^ 2 + z = algebraMap F (L 2) (a + b) ∧
      x ∉ Set.range (algebraMap F (L 0)) ∧
      y ∉ Set.range (algebraMap F (L 1)) ∧
      z ∉ Set.range (algebraMap F (L 2)) := by
  letI : CharP K 2 := charP_of_injective_algebraMap (algebraMap F K).injective 2
  choose σ hσ hfixed huniq using fun i ↦ exists_lower_involution htotal (L i) (hdegree i)
  have hmove (i j : Fin 3) (hij : i ≠ j) (u : L j)
      (hu : u ∉ Set.range (algebraMap F (L j))) : σ i (u : K) ≠ (u : K) :=
    involution_moves_other_generator (L i) (L j) (hdegree j)
      (fun h ↦ hij (hne h)) (σ i) (σ j) (hσ i) (hfixed i) (hfixed j) (huniq j) u hu
  obtain ⟨a, x, hx, hxgen⟩ := exists_artinSchreier_generator F (L 0) (hdegree 0)
  obtain ⟨b, y, hy, hygen⟩ := exists_artinSchreier_generator F (L 1) (hdegree 1)
  have hxK : (x : K) ^ 2 + (x : K) = algebraMap F K a := by
    simpa only [map_add, map_pow, IsScalarTower.algebraMap_apply F (L 0) K,
      IntermediateField.algebraMap_apply] using
      congrArg (algebraMap (L 0) K) hx
  have hyK : (y : K) ^ 2 + (y : K) = algebraMap F K b := by
    simpa only [map_add, map_pow, IsScalarTower.algebraMap_apply F (L 1) K,
      IntermediateField.algebraMap_apply] using
      congrArg (algebraMap (L 1) K) hy
  have hshift (i : Fin 3) {u : K} {c : F} (hu : u ^ 2 + u = algebraMap F K c)
      (hmove : σ i u ≠ u) : σ i u = u + 1 := by
    have hv : (σ i u) ^ 2 + σ i u = u ^ 2 + u := by
      rw [← map_pow, ← map_add, hu, AlgEquiv.commutes]
    have hf : (σ i u - u) * (σ i u + u + 1) = 0 := by
      linear_combination hv
    have heq := (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hmove)
    have : σ i u = -(u + 1) := eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using heq)
    simpa only [CharTwo.neg_eq] using this
  have hzmem : (x : K) + (y : K) ∈ L 2 := by
    apply (hfixed 2 _).mp
    rw [map_add, hshift 2 hxK (hmove 2 0 (by decide) x hxgen),
      hshift 2 hyK (hmove 2 1 (by decide) y hygen)]
    calc
      (x : K) + 1 + ((y : K) + 1) = ((x : K) + (y : K)) + (1 + 1) := by ring
      _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]
  let z : L 2 := ⟨(x : K) + (y : K), hzmem⟩
  have hz : z ^ 2 + z = algebraMap F (L 2) (a + b) := by
    apply (algebraMap (L 2) K).injective
    change ((x : K) + (y : K)) ^ 2 + ((x : K) + (y : K)) = algebraMap F K (a + b)
    rw [CharTwo.add_sq, map_add, ← hxK, ← hyK]
    ring
  refine ⟨a, b, x, y, z, hx, hy, hz, hxgen, hygen, ?_⟩
  rintro ⟨c, hc⟩
  have hzbase : (x : K) + (y : K) = algebraMap F K c := by
    exact (congrArg (algebraMap (L 2) K) hc).symm
  have hsum : σ 0 ((x : K) + (y : K)) = (x : K) + (y : K) := by
    rw [hzbase, AlgEquiv.commutes]
  rw [map_add, (hfixed 0 (x : K)).mpr x.property] at hsum
  exact hmove 0 1 (by decide) y hygen (add_left_cancel hsum)

end Labeling

section Assembly

variable {F} {K : Type} [Field K] [Algebra F K]
  [Module.Finite F K] [IsGalois F K]

private theorem quadratic_product_values
    (htotal : Module.finrank F K = 4)
    (L : Fin 3 → IntermediateField F K) [∀ i, IsGalois F (L i)]
    [∀ i, ValuativeRel (L i)] [∀ i, TopologicalSpace (L i)]
    [∀ i, IsNonarchimedeanLocalField (L i)] [∀ i, ValuativeExtension F (L i)]
    (hdegree : ∀ i, Module.finrank F (L i) = 2) (hne : Function.Injective L)
    (ω : (i : Fin 3) → NormCharacter F (L i)) (hω : ∀ i, ω i ≠ 1) :
    (ω 2).1 = (ω 0).1 * (ω 1).1 ∧ (ω 0).1 ^ 2 = 1 := by
  by_cases hchar : ringChar F = 2
  · letI : CharP F 2 := ringChar.of_eq hchar
    obtain ⟨a, b, x, y, z, hx, hy, hz, hxgen, hygen, hzgen⟩ :=
      artinSchreier_labeling htotal L hdegree hne
    rw [artinSchreierNormCharacter_eq_normCharacter F (L 0) (hdegree 0)
        a x hx hxgen (ω 0) (hω 0),
      artinSchreierNormCharacter_eq_normCharacter F (L 1) (hdegree 1)
        b y hy hygen (ω 1) (hω 1),
      artinSchreierNormCharacter_eq_normCharacter F (L 2) (hdegree 2)
        (a + b) z hz hzgen (ω 2) (hω 2)]
    exact ⟨artinSchreierNormCharacter_add F a b, artinSchreierNormCharacter_sq F a⟩
  · obtain ⟨a, b, x, y, z, hx, hy, hz, hxgen, hygen, hzgen⟩ :=
      quadratic_labeling hchar htotal L hdegree hne
    rw [quadraticNormCharacter_eq_normCharacter F hchar (L 0) (hdegree 0)
        a x hx hxgen (ω 0) (hω 0),
      quadraticNormCharacter_eq_normCharacter F hchar (L 1) (hdegree 1)
        b y hy hygen (ω 1) (hω 1),
      quadraticNormCharacter_eq_normCharacter F hchar (L 2) (hdegree 2)
        (a * b) z hz hzgen (ω 2) (hω 2)]
    exact ⟨quadraticNormCharacter_mul F hchar a b, quadraticNormCharacter_sq F hchar a⟩

private theorem three_characters_injective {G : Type*} [Group G]
    (χ : Fin 3 → G) (hne : ∀ i, χ i ≠ 1)
    (hprod : χ 2 = χ 0 * χ 1) (hsq : χ 0 ^ 2 = 1) : Function.Injective χ := by
  have h01 : χ 0 ≠ χ 1 := by
    intro h
    apply hne 2
    rw [hprod, ← h, ← pow_two, hsq]
  have h02 : χ 0 ≠ χ 2 := by
    intro h
    apply hne 1
    exact mul_eq_left.mp (hprod.symm.trans h.symm)
  have h12 : χ 1 ≠ χ 2 := by
    intro h
    apply hne 0
    exact mul_eq_right.mp (hprod.symm.trans h.symm)
  intro i j h
  fin_cases i <;> fin_cases j <;> first
  | rfl
  | exact (h01 h).elim
  | exact (h01 h.symm).elim
  | exact (h02 h).elim
  | exact (h02 h.symm).elim
  | exact (h12 h).elim
  | exact (h12 h.symm).elim

end Assembly

open private primeNormCards from LanglandsSecondMainLemma.Characters.CrossedNorm

private theorem normRanges_ne_of_quadratic_characters_ne
    (E M : Type) [Field E] [Field M]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [Algebra F E] [Algebra F M] [ValuativeExtension F E] [ValuativeExtension F M]
    [Module.Finite F E] [Module.Finite F M] [PrimeCyclicExtension F E]
    (hdegree : Module.finrank F E = 2)
    (ω : NormCharacter F E) (ν : NormCharacter F M)
    (hω : ω ≠ 1) (hν : ν ≠ 1) (hne : ω.1 ≠ ν.1) :
    (normUnits F E).range ≠ (normUnits F M).range := by
  intro hrange
  let ν' : NormCharacter F E := ⟨ν.1, by
    apply ContinuousMonoidHom.ext
    intro u
    change ν.1 (normUnits F E u) = 1
    apply ν.eq_one_on_normRange F M
    rw [← hrange]
    exact ⟨u, rfl⟩⟩
  have hν' : ν' ≠ 1 := by
    intro h
    apply hν
    apply NormCharacter.ext
    exact congrArg (fun η : NormCharacter F E ↦ η.1) h
  have hc : Nat.card (NormCharacter F E) = 2 := (primeNormCards F E).2.trans hdegree
  have heq := ((Nat.card_eq_two_iff' (1 : NormCharacter F E)).mp hc).unique hω hν'
  exact hne (congrArg Subtype.val heq)

open private intermediateField_lower_isGalois intermediateField_lower_cyclicPrime
  primeSquare_totalDegree from LanglandsSecondMainLemma.Basic.Fields

/-- **Paper Lemma D.6 (`D:quadratic-norms`).** For any labeling of the three
distinct quadratic lower fields in a genuine biquadratic local extension,
their nontrivial continuous norm characters satisfy `ω₂ = ω₀ * ω₁` and
are pairwise distinct. Their lower norm subgroups are pairwise distinct,
and each opposite-edge map is an equivalence whose actual value is
pullback along the lower norm.

The field characteristics are unrestricted. Both parameter labelings and
all local-field and cyclic-edge structures are constructed from these
inputs; no square-root, Artin--Schreier, or norm-separation data are assumed. -/
theorem quadraticProduct
    {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Algebra F K] [ValuativeExtension F K]
    [Module.Finite F K] [IsGalois F K]
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (L : Fin 3 → IntermediateField F K)
    (hdegree : ∀ i, Module.finrank F (L i) = 2) (hdistinct : Function.Injective L) :
    letI : ∀ i, ValuativeRel (L i) := fun i ↦ Basic.intermediateFieldValuativeRel (L i)
    letI : ∀ i, TopologicalSpace (L i) := fun i ↦ Basic.intermediateFieldTopology (L i)
    letI : ∀ i, IsNonarchimedeanLocalField (L i) := fun i ↦ Basic.intermediateField_localField (L i)
    letI : ∀ i, ValuativeExtension F (L i) := fun i ↦ Basic.intermediateField_lowerValuativeExtension (L i)
    letI : ∀ i, ValuativeExtension (L i) K := fun i ↦ Basic.intermediateField_upperValuativeExtension (L i)
    ∃ ω : (i : Fin 3) → NormCharacter F (L i),
      (∀ i, ω i ≠ 1) ∧
      (ω 2).1 = (ω 0).1 * (ω 1).1 ∧
      Function.Injective (fun i ↦ (ω i).1) ∧
      Function.Injective (fun i ↦ Ramification.intermediateNormRange (L i)) ∧
      ∀ i j : Fin 3, i ≠ j →
        ∃ e : NormCharacter F (L j) ≃* NormCharacter (L i) K,
          ∀ (ν : NormCharacter F (L j)) (x : (L i)ˣ),
            (e ν).1 x = ν.1 (normUnits F (L i) x) := by
  letI : ∀ i, ValuativeRel (L i) := fun i ↦ Basic.intermediateFieldValuativeRel (L i)
  letI : ∀ i, TopologicalSpace (L i) := fun i ↦ Basic.intermediateFieldTopology (L i)
  letI : ∀ i, IsNonarchimedeanLocalField (L i) := fun i ↦ Basic.intermediateField_localField (L i)
  letI : ∀ i, ValuativeExtension F (L i) := fun i ↦ Basic.intermediateField_lowerValuativeExtension (L i)
  letI : ∀ i, ValuativeExtension (L i) K := fun i ↦ Basic.intermediateField_upperValuativeExtension (L i)
  letI : ∀ i, IsGalois F (L i) := fun i ↦ intermediateField_lower_isGalois hG.some (L i)
  letI : ∀ i, PrimeCyclicExtension F (L i) := fun i ↦
    PrimeCyclicExtension.ofCyclicPrimeExtension F (L i)
      (intermediateField_lower_cyclicPrime Nat.prime_two hG.some (L i) (hdegree i))
  have hc (i : Fin 3) : Nat.card (NormCharacter F (L i)) = 2 :=
    (primeNormCards F (L i)).2.trans (hdegree i)
  choose ω hω _ using fun i ↦ (Nat.card_eq_two_iff' (1 : NormCharacter F (L i))).mp (hc i)
  have hvalues := quadratic_product_values (primeSquare_totalDegree hG.some) L hdegree hdistinct ω hω
  have hinj : Function.Injective (fun i ↦ (ω i).1) :=
    three_characters_injective (fun i ↦ (ω i).1)
      (fun i h ↦ hω i (NormCharacter.ext h)) hvalues.1 hvalues.2
  have hrange : Function.Injective (fun i ↦ Ramification.intermediateNormRange (L i)) := by
    intro i j hij
    by_contra hne
    exact normRanges_ne_of_quadratic_characters_ne F (L i) (L j) (hdegree i)
      (ω i) (ω j) (hω i) (hω j) (fun h ↦ hne (hinj h)) hij
  refine ⟨ω, hω, hvalues.1, hinj, hrange, ?_⟩
  intro i j hij
  refine ⟨crossedNorm Nat.prime_two hG (L i) (L j) (hdegree i) (hdegree j)
    (fun h ↦ hij (hrange h)), ?_⟩
  intro ν x
  rfl

end

end LanglandsSecondMainLemma.Characters
