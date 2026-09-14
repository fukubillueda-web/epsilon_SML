import LanglandsSecondMainLemma.Dyadic.Maximal.Origin
import LanglandsSecondMainLemma.Dyadic.Mixed.UnitSymbol

namespace LanglandsSecondMainLemma.Dyadic.Maximal

open LanglandsFirstMainLemma
open LanglandsSecondMainLemma.Characters

noncomputable section

private theorem quadratic_norm_eq
    {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (sigma : Gal(E/F)) (hsigma : sigma ≠ 1)
    (hdegree : Module.finrank F E = 2) (x : E) :
    algebraMap F E (norm F E x) = x * sigma x := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms]
  have hcard : Fintype.card Gal(E/F) = 2 := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, hdegree]
  have huniv : ({sigma, (1 : Gal(E/F))} : Finset Gal(E/F)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simpa using hsigma),
      Finset.card_singleton, hcard]
  rw [← huniv]
  simp [hsigma, mul_comm]

private theorem quadraticNormCharacter_on_norm
    (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra F E] [Module.Free F E] [Module.Finite F E]
    [IsGalois F E]
    (hchar : ringChar F ≠ 2) (A : Fˣ)
    (pb : PowerBasis F E) (hdim : pb.dim = 2)
    (hgenSq : pb.gen ^ 2 = algebraMap F E (A : F))
    (sigma : Gal(E/F)) (hsigma : sigma ≠ 1)
    (hsigmaGen : sigma pb.gen = -pb.gen)
    (u : Eˣ) :
    quadraticNormCharacter F hchar A (normUnits F E u) = 1 := by
  classical
  let B : Module.Basis (Fin 2) F E := pb.basis.reindex (finCongr hdim)
  let c : F := B.repr (u : E) 0
  let d : F := B.repr (u : E) 1
  have hu : (u : E) = algebraMap F E c + algebraMap F E d * pb.gen := by
    have hrepr := B.sum_repr (u : E)
    have hB0 : B 0 = (1 : E) := by
      simp [B]
    have hB1 : B 1 = pb.gen := by
      simp [B]
    rw [Fin.sum_univ_two] at hrepr
    rw [hB0, hB1] at hrepr
    simpa [Algebra.smul_def] using hrepr.symm
  have hsigmau : sigma (u : E) =
      algebraMap F E c - algebraMap F E d * pb.gen := by
    rw [hu]
    simp only [map_add, map_mul, hsigmaGen]
    rw [sigma.commutes c, sigma.commutes d]
    ring
  apply (quadraticNormCharacter_eq_one_iff_conic F hchar A
    (normUnits F E u)).2
  refine ⟨c, d, 1, Or.inr (Or.inr one_ne_zero), ?_⟩
  have hnorm := quadratic_norm_eq sigma hsigma (by
    rw [PowerBasis.finrank pb, hdim]) (u : E)
  have hnormFormula : norm F E (u : E) = c ^ 2 - (A : F) * d ^ 2 := by
    apply (algebraMap F E).injective
    rw [hnorm, hsigmau, hu, map_sub, map_pow, map_mul]
    calc
      ((algebraMap F E c + algebraMap F E d * pb.gen) *
          (algebraMap F E c - algebraMap F E d * pb.gen)) =
          (algebraMap F E c) ^ 2 - (algebraMap F E d) ^ 2 * pb.gen ^ 2 := by ring
      _ = (algebraMap F E c) ^ 2 -
          algebraMap F E (A : F) * algebraMap F E (d ^ 2) := by
        rw [hgenSq, map_pow]
        ring
  simp only [coe_normUnits, one_pow, mul_one]
  rw [hnormFormula]
  ring

private theorem quadraticParameter_not_square
    (F E : Type) [Field F] [Field E] [Algebra F E]
    (A : Fˣ) (pb : PowerBasis F E)
    (hgenSq : pb.gen ^ 2 = algebraMap F E (A : F))
    (sigma : Gal(E/F)) (hsigma : sigma ≠ 1) :
    ¬ IsSquare (A : F) := by
  rintro ⟨r, hr⟩
  have hfactor :
      (pb.gen - algebraMap F E r) * (pb.gen + algebraMap F E r) = 0 := by
    calc
      _ = pb.gen ^ 2 - (algebraMap F E r) ^ 2 := by ring
      _ = 0 := by rw [hgenSq, ← map_pow, hr]; ring_nf
  have hfixed : sigma pb.gen = pb.gen := by
    rcases mul_eq_zero.mp hfactor with hminus | hplus
    · have hg : pb.gen = algebraMap F E r := sub_eq_zero.mp hminus
      rw [hg, sigma.commutes]
    · have hg : pb.gen = -algebraMap F E r := eq_neg_of_add_eq_zero_left hplus
      rw [hg, map_neg, sigma.commutes]
  apply hsigma
  apply AlgEquiv.coe_toAlgHom_injective
  apply pb.algHom_ext
  exact hfixed

private theorem quadratic_automorphism_gen_neg
    (F E : Type) [Field F] [Field E] [Algebra F E]
    (pb : PowerBasis F E) (A : F)
    (hgenSq : pb.gen ^ 2 = algebraMap F E A)
    (sigma : Gal(E/F)) (hsigma : sigma ≠ 1) :
    sigma pb.gen = -pb.gen := by
  have hsquare : (sigma pb.gen) ^ 2 = pb.gen ^ 2 := by
    rw [← map_pow, hgenSq, sigma.commutes]
  have hfactor :
      (sigma pb.gen - pb.gen) * (sigma pb.gen + pb.gen) = 0 := by
    calc
      _ = (sigma pb.gen) ^ 2 - pb.gen ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hsquare
  rcases mul_eq_zero.mp hfactor with hfixed | hneg
  · exfalso
    apply hsigma
    apply AlgEquiv.coe_toAlgHom_injective
    apply pb.algHom_ext
    exact sub_eq_zero.mp hfixed
  · exact eq_neg_of_add_eq_zero_left hneg

private theorem actualNormCharacter_eq_quadratic
    (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Free F E] [Module.Finite F E] [PrimeCyclicExtension F E]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1)
    (hdegree : Module.finrank F E = 2)
    (hchar : ringChar F ≠ 2) (A : Fˣ)
    (pb : PowerBasis F E)
    (hgenSq : pb.gen ^ 2 = algebraMap F E (A : F))
    (tau : NormCharacter F E) (htau : tau ≠ 1) :
    tau.1 = quadraticNormCharacter F hchar A := by
  classical
  have hdim : pb.dim = 2 := by rw [← PowerBasis.finrank pb, hdegree]
  have hcardGal : Fintype.card Gal(E/F) = 2 := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, hdegree]
  obtain ⟨sigma, hsigma⟩ := Fintype.exists_ne_of_one_lt_card
    (by omega : 1 < Fintype.card Gal(E/F)) (1 : Gal(E/F))
  have hsigmaGen := quadratic_automorphism_gen_neg F E pb (A : F) hgenSq sigma hsigma
  let tauA : NormCharacter F E := ⟨quadraticNormCharacter F hchar A, by
    apply ContinuousMonoidHom.ext
    intro u
    rw [normQuasiChar_apply, ContinuousQuasiChar.one_apply]
    exact quadraticNormCharacter_on_norm F E hchar A pb hdim hgenSq
      sigma hsigma hsigmaGen u⟩
  have htauA : tauA ≠ 1 := by
    intro h
    have hcoe := congrArg Subtype.val h
    have htriv : quadraticNormCharacter F hchar A = 1 := by
      simpa only [tauA, NormCharacter.coe_one] using hcoe
    exact (quadraticParameter_not_square F E A pb hgenSq sigma hsigma)
      ((quadraticNormCharacter_eq_one_iff_isSquare F hchar A).1 htriv)
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  letI : Finite (NormCharacter F E) :=
    ramifiedNormCharacter_finite F E ht hres pi hpi hgen
  have hcard : Nat.card (NormCharacter F E) = 2 := by
    simpa only [hdegree] using
      ramifiedNormCharacter_card F E ht hres pi hpi hgen
  have hunique := (Nat.card_eq_two_iff' (1 : NormCharacter F E)).mp hcard
  have heq : tau = tauA := hunique.unique htau htauA
  exact congrArg Subtype.val heq

/-- The canonical unit `1-z` at positive integral depth `q`. -/
noncomputable def lowerOneSubUnit
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (q : ℕ) (hq : 0 < q) (z : F) (hz : z ∈ lattice F (q : ℤ)) : Fˣ :=
  principalUnitOf F (q - 1) (-z) (by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.sub_add_cancel hq]
      using neg_mem_lattice F hz)

@[simp]
theorem coe_lowerOneSubUnit
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (q : ℕ) (hq : 0 < q) (z : F) (hz : z ∈ lattice F (q : ℤ)) :
    (lowerOneSubUnit F q hq z hz : F) = 1 - z := by
  simp [lowerOneSubUnit]
  ring

private theorem sub_one_mem_lattice_of_mem_unitFiltration
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {q : ℕ} (hq : 0 < q) (u : Fˣ) (hu : u ∈ unitFiltration F q) :
    (u : F) - 1 ∈ lattice F (q : ℤ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  exact (mem_unitFiltration_succ_iff_sub_mem_lattice F n u).1 hu

private theorem lowerOneSubUnit_eq
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (z : F)
    (hzq : z ∈ lattice F (q : ℤ)) (hzr : z ∈ lattice F (r : ℤ)) :
    lowerOneSubUnit F q hq z hzq = lowerOneSubUnit F r hr z hzr := by
  apply Units.ext
  simp only [coe_lowerOneSubUnit]

private theorem quadraticNormOneSub
    (F E : Type) [Field F] [Field E] [Algebra F E]
    [Module.Free F E] [Module.Finite F E]
    (hdegree : Module.finrank F E = 2) (z : E) :
    norm F E (1 - z) = 1 - trace F E z + norm F E z := by
  have h := norm_one_add_eq_one_add_sum_elementarySymmetric F E (-z)
  rw [hdegree] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h
  rw [elementarySymmetric_one] at h
  have hfin : elementarySymmetric F E 2 (-z) = norm F E (-z) := by
    rw [← hdegree]
    exact elementarySymmetric_finrank F E (-z)
  rw [hfin] at h
  have hnormneg : norm F E (-z) = norm F E z := by
    rw [show -z = algebraMap F E (-1 : F) * z by simp, map_mul,
      LanglandsFirstMainLemma.norm_algebraMap, hdegree]
    norm_num
  rw [map_neg, hnormneg] at h
  simpa only [sub_eq_add_neg, add_assoc] using h

private theorem normPhaseOfLowerFormula
    (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Free F E] [Module.Finite F E] [PrimeCyclicExtension F E]
    {t q : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1)
    (hdegree : Module.finrank F E = 2)
    (hq : 0 < q)
    (htraceDepth : (q : ℤ) ≤ ((q : ℤ) + (t + 1 : ℕ)) / 2)
    (tau : NormCharacter F E) (PsiF : ContinuousAddChar F) (beta : F)
    (hformula : ∀ (z : F) (hz : z ∈ lattice F (q : ℤ)),
      tau.1 (lowerOneSubUnit F q hq z hz) = PsiF (beta * z))
    (x : E) (hx : x ∈ lattice E (q : ℤ)) :
    tracePullbackAddChar F E PsiF (algebraMap F E beta * x) =
      PsiF (beta * norm F E x) := by
  have htrace : trace F E x ∈ lattice F (q : ℤ) := by
    obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
    have hmap : trace F E x ∈
        Submodule.map ((trace F E).restrictScalars (ringOfIntegers F))
          ((lattice E (q : ℤ)).restrictScalars (ringOfIntegers F)) := by
      apply Submodule.mem_map.mpr
      exact ⟨x, hx, rfl⟩
    rw [cyclicPrime_trace_lattice_image_eq F E ht hres pi hpi hgen,
      hdegree] at hmap
    norm_num at hmap
    exact lattice_antitone F htraceDepth hmap
  have hnorm : norm F E x ∈ lattice F (q : ℤ) := by
    rw [mem_lattice] at hx ⊢
    rw [ord_norm, hres, one_nsmul]
    exact hx
  let y : F := trace F E x - norm F E x
  have hy : y ∈ lattice F (q : ℤ) :=
    sub_mem_lattice F htrace hnorm
  let ux : Eˣ := lowerOneSubUnit E q hq x hx
  have hnormUnits : normUnits F E ux = lowerOneSubUnit F q hq y hy := by
    apply Units.ext
    simp only [coe_normUnits, ux, coe_lowerOneSubUnit]
    rw [quadraticNormOneSub F E hdegree x]
    dsimp only [y]
    ring
  have htauNorm : tau.1 (normUnits F E ux) = 1 :=
    tau.eq_one_on_normRange F E _ ⟨ux, rfl⟩
  have hphase : PsiF (beta * y) = 1 := by
    rw [← hformula y hy]
    calc
      tau.1 (lowerOneSubUnit F q hq y hy) =
          tau.1 (normUnits F E ux) := congrArg tau.1 hnormUnits.symm
      _ = 1 := htauNorm
  have htraceMul : trace F E (algebraMap F E beta * x) =
      beta * trace F E x := by
    simpa [Algebra.smul_def] using (trace F E).map_smul beta x
  rw [tracePullbackAddChar_apply, htraceMul]
  apply div_eq_one.mp
  calc
    PsiF (beta * trace F E x) / PsiF (beta * norm F E x) =
        PsiF (beta * trace F E x - beta * norm F E x) :=
      (PsiF.toAddChar.map_sub_eq_div _ _).symm
    _ = PsiF (beta * y) := by
      congr 1
      dsimp only [y]
      ring
    _ = 1 := hphase

/-- The complete conclusion of the paper's maximal lower-character lemma.
The three upper additive characters are the actual trace pullbacks. -/
structure LowerCharacterData
    (F L₁ L₂ L₃ : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field L₁] [ValuativeRel L₁] [TopologicalSpace L₁]
    [IsNonarchimedeanLocalField L₁] [Algebra F L₁]
    [Module.Free F L₁] [Module.Finite F L₁] [IsModuleTopology F L₁]
    [Field L₂] [ValuativeRel L₂] [TopologicalSpace L₂]
    [IsNonarchimedeanLocalField L₂] [Algebra F L₂]
    [Module.Free F L₂] [Module.Finite F L₂] [IsModuleTopology F L₂]
    [Field L₃] [ValuativeRel L₃] [TopologicalSpace L₃]
    [IsNonarchimedeanLocalField L₃] [Algebra F L₃]
    [Module.Free F L₃] [Module.Finite F L₃] [IsModuleTopology F L₃]
    (a e : ℕ) (ha : 0 < a)
    (tau₁ : NormCharacter F L₁) (tau₂ : NormCharacter F L₂)
    (tau₃ : NormCharacter F L₃) (PsiF : ContinuousAddChar F)
    (beta₁ beta₂ beta₃ : F) (h₁ : L₁) (h₂ : L₂) (h₃ : L₃) : Prop where
  first_formula : ∀ (z : F) (hz : z ∈ lattice F (a : ℤ)),
    tau₁.1 (lowerOneSubUnit F a ha z hz) = PsiF (beta₁ * z)
  second_formula : ∀ (z : F) (hz : z ∈ lattice F ((e + 1 : ℕ) : ℤ)),
    tau₂.1 (lowerOneSubUnit F (e + 1) (by omega) z hz) = PsiF (beta₂ * z)
  third_formula : ∀ (z : F) (hz : z ∈ lattice F ((e + 1 : ℕ) : ℤ)),
    tau₃.1 (lowerOneSubUnit F (e + 1) (by omega) z hz) = PsiF (beta₃ * z)
  first_beta_norm : beta₁ = norm F L₁ h₁
  second_beta_norm : beta₂ = norm F L₂ h₂
  third_beta_norm : beta₃ = norm F L₃ h₃
  first_phase : ∀ (x : L₁) (_hx : x ∈ lattice L₁ (a : ℤ)),
    tracePullbackAddChar F L₁ PsiF (algebraMap F L₁ beta₁ * x) =
      PsiF (beta₁ * norm F L₁ x)
  second_phase : ∀ (x : L₂) (_hx : x ∈ lattice L₂ ((e + 1 : ℕ) : ℤ)),
    tracePullbackAddChar F L₂ PsiF (algebraMap F L₂ beta₂ * x) =
      PsiF (beta₂ * norm F L₂ x)
  third_phase : ∀ (x : L₃) (_hx : x ∈ lattice L₃ ((e + 1 : ℕ) : ℤ)),
    tracePullbackAddChar F L₃ PsiF (algebraMap F L₃ beta₃ * x) =
      PsiF (beta₃ * norm F L₃ x)

private theorem intermediate_residueDegree_mul
    {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]
    (L : IntermediateField F K) :
    letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
    letI : TopologicalSpace L := Basic.intermediateFieldTopology L
    letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
    letI : ValuativeExtension F L :=
      Basic.intermediateField_lowerValuativeExtension L
    letI : ValuativeExtension L K :=
      Basic.intermediateField_upperValuativeExtension L
    residueDegree F L * residueDegree L K = residueDegree F K := by
  letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
  letI : TopologicalSpace L := Basic.intermediateFieldTopology L
  letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
  letI : ValuativeExtension F L :=
    Basic.intermediateField_lowerValuativeExtension L
  letI : ValuativeExtension L K :=
    Basic.intermediateField_upperValuativeExtension L
  letI : IsScalarTower
      (ringOfIntegers F) (ringOfIntegers L) (ringOfIntegers K) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap F K (x : F) = algebraMap L K (algebraMap F L (x : F))
      rw [← IsScalarTower.algebraMap_apply F L K])
  letI : IsLocalHom
      (algebraMap (ringOfIntegers F) (ringOfIntegers L)) := inferInstance
  letI : IsLocalHom
      (algebraMap (ringOfIntegers L) (ringOfIntegers K)) := inferInstance
  rw [residueDegree_eq_finrank_residueField,
    residueDegree_eq_finrank_residueField,
    residueDegree_eq_finrank_residueField]
  exact Module.finrank_mul_finrank
    (ResidueField F) (ResidueField L) (ResidueField K)

private theorem intermediate_residueDegree_eq_one
    {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]
    (L : IntermediateField F K) (hres : residueDegree F K = 1) :
    letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
    letI : TopologicalSpace L := Basic.intermediateFieldTopology L
    letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
    letI : ValuativeExtension F L :=
      Basic.intermediateField_lowerValuativeExtension L
    residueDegree F L = 1 := by
  have hmul := intermediate_residueDegree_mul L
  rw [hres] at hmul
  exact (mul_eq_one.mp hmul).1

private theorem unitSymbolAtDepth
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (hchar : ringChar F ≠ 2) (e m n : ℕ)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hsum : 2 * e < m + n)
    (u v : F) (hu : u ∈ lattice F (m : ℤ))
    (hv : v ∈ lattice F (n : ℤ)) :
    quadraticNormSymbol F hchar
      (Dyadic.Mixed.oneAddUnit F u (by
        exact_mod_cast (WithTop.coe_le_coe.mpr (show (1 : ℤ) ≤ m by exact_mod_cast hm)).trans
          ((mem_lattice F).1 hu)))
      (Dyadic.Mixed.oneAddUnit F v (by
        exact_mod_cast (WithTop.coe_le_coe.mpr (show (1 : ℤ) ≤ n by exact_mod_cast hn)).trans
          ((mem_lattice F).1 hv))) = 1 := by
  apply Dyadic.Mixed.unitSymbol F hchar
  rw [htwo]
  calc
    (e : WithTop ℤ) + (e : WithTop ℤ) =
        (((2 * e : ℕ) : ℤ) : WithTop ℤ) := by
      change ((e : ℤ) : WithTop ℤ) + ((e : ℤ) : WithTop ℤ) =
        (((2 * e : ℕ) : ℤ) : WithTop ℤ)
      rw [← WithTop.coe_add]
      congr 1
      push_cast
      ring
    _ < (((m + n : ℕ) : ℤ) : WithTop ℤ) := by exact_mod_cast hsum
    _ = ((m : ℤ) : WithTop ℤ) + ((n : ℤ) : WithTop ℤ) := by
      rw [← WithTop.coe_add]
      congr 1
    _ ≤ ord F u + ord F v := add_le_add ((mem_lattice F).1 hu) ((mem_lattice F).1 hv)

/-- The third lower chart transports both boundary conditions of the conductor. -/
private theorem additiveConductor_of_lowerChart
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (e : ℕ) (he : 1 ≤ e) (tau : ContinuousQuasiChar F)
    (htauConductor : IsMultiplicativeConductor F tau (2 * e + 1))
    (PsiF : ContinuousAddChar F)
    (hchart : ∀ (z : F) (hz : z ∈ lattice F ((e + 1 : ℕ) : ℤ)),
      tau (lowerOneSubUnit F (e + 1) (by omega) z hz) = PsiF z) :
    IsAdditiveConductor F PsiF (-((2 * e + 1 : ℕ) : ℤ)) := by
  have hPsiTrivial : AddCharTrivialOnLattice F PsiF ((2 * e + 1 : ℕ) : ℤ) := by
    intro x hx
    have hxq : x ∈ lattice F ((e + 1 : ℕ) : ℤ) :=
      lattice_antitone F (by
        exact_mod_cast (show e + 1 ≤ 2 * e + 1 by omega)) hx
    rw [← hchart x hxq]
    apply htauConductor.trivial
    rw [mem_unitFiltration_succ_iff_sub_mem_lattice F (2 * e)]
    simp only [coe_lowerOneSubUnit]
    convert neg_mem_lattice F hx using 1
    ring
  have hPsiNontrivial :
      ¬ AddCharTrivialOnLattice F PsiF ((2 * e : ℕ) : ℤ) := by
    intro htriv
    apply htauConductor.not_trivialOnPredecessor
    intro u hu
    have hdisp := sub_one_mem_lattice_of_mem_unitFiltration F
      (by omega : 0 < 2 * e) u hu
    let x : F := 1 - (u : F)
    have hx : x ∈ lattice F ((2 * e : ℕ) : ℤ) := by
      simpa only [x, neg_sub] using neg_mem_lattice F hdisp
    have hxq : x ∈ lattice F ((e + 1 : ℕ) : ℤ) :=
      lattice_antitone F (by
        exact_mod_cast (show e + 1 ≤ 2 * e by omega)) hx
    have hunit : lowerOneSubUnit F (e + 1) (by omega) x hxq = u := by
      apply Units.ext
      simp only [coe_lowerOneSubUnit, x]
      ring
    calc
      tau u = tau (lowerOneSubUnit F (e + 1) (by omega) x hxq) :=
        congrArg tau hunit.symm
      _ = PsiF x := hchart x hxq
      _ = 1 := htriv x hx
  apply IsAdditiveConductor.of_boundary
  · simpa only [neg_neg] using hPsiTrivial
  · have hdepth : -(-((2 * e + 1 : ℕ) : ℤ)) - 1 = (2 * e : ℕ) := by
      push_cast
      omega
    rw [hdepth]
    exact hPsiNontrivial

private theorem unitSymbolAtDepth_of_mem_unitFiltration
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (hchar : ringChar F ≠ 2) (e m n : ℕ)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hsum : 2 * e < m + n)
    (u : F) (hu : u ∈ lattice F (m : ℤ))
    (v : Fˣ) (hv : v ∈ unitFiltration F n) :
    quadraticNormSymbol F hchar
      (Dyadic.Mixed.oneAddUnit F u (by
        exact (WithTop.coe_le_coe.mpr (show (1 : ℤ) ≤ m by exact_mod_cast hm)).trans
          ((mem_lattice F).1 hu))) v = 1 := by
  have hv' := sub_one_mem_lattice_of_mem_unitFiltration F hn v hv
  have h := unitSymbolAtDepth F hchar e m n htwo hm hn hsum u ((v : F) - 1) hu hv'
  have hunit : Dyadic.Mixed.oneAddUnit F ((v : F) - 1) (by
      exact (WithTop.coe_le_coe.mpr (show (1 : ℤ) ≤ n by exact_mod_cast hn)).trans
        ((mem_lattice F).1 hv')) = v := by
    apply Units.ext
    simp [Dyadic.Mixed.coe_oneAddUnit]
  simpa only [hunit] using h

private theorem quadraticNormCharacter_product
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (hchar : ringChar F ≠ 2) (A R2 B : Fˣ) :
    quadraticNormCharacter F hchar R2 B =
      quadraticNormCharacter F hchar A B * quadraticNormCharacter F hchar (A * R2) B := by
  rw [quadraticNormCharacter_mul, ContinuousQuasiChar.mul_apply, ← mul_assoc, ← pow_two]
  change _ = quadraticNormSymbol F hchar A B ^ 2 * _
  rw [quadraticNormSymbol_sq, one_mul]

section AlignedLowerCharacters

variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Field K] [Algebra F K]
  {pi : ringOfIntegers F} {e a b : ℕ}
  {u0 w0 : (ringOfIntegers F)ˣ} {s R0 : K}
  (D : AlignmentData pi e a b u0 w0 s R0)

private theorem alignment_parameter_difference_mem (ha : 1 ≤ a) :
    D.epsilon - D.rSquare ∈ lattice F ((b + a : ℕ) : ℤ) := by
  have hrs0 : D.rSquare ≠ 0 :=
    (ord_ne_top_iff F).1 (by rw [D.rSquare_order]; exact WithTop.coe_ne_top)
  have hrsMem : D.rSquare ∈ lattice F (b : ℤ) := by
    rw [mem_lattice, D.rSquare_order]
    exact_mod_cast le_rfl
  have hratioMem := sub_one_mem_lattice_of_mem_unitFiltration F ha D.ratio D.ratio_mem
  have heq : D.epsilon - D.rSquare = D.rSquare * ((D.ratio : F) - 1) := by
    rw [D.ratio_coe]
    field_simp [hrs0]
  rw [heq]
  simpa only [Nat.cast_add] using mul_mem_lattice F hrsMem hratioMem

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] [Module.Finite F K] (O : OriginData D)

include O

/-- The Steinberg transformation gives the first formula on the entire layer. -/
private theorem firstLowerFormula
    (hchar : ringChar F ≠ 2)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (ha : 1 ≤ a) (hae : a ≤ e) (hb : b = 2 * e - 2 * a + 1)
    (A R2 : Fˣ) (hA : (A : F) = 1 + D.epsilon) (hR2 : (R2 : F) = D.rSquare)
    (tau₁ tau₃ : ContinuousQuasiChar F)
    (homega₁ : tau₁ = quadraticNormCharacter F hchar A)
    (homega₃ : tau₃ = quadraticNormCharacter F hchar (A * R2))
    (PsiF : ContinuousAddChar F)
    (hchart₃ : ∀ (z : F) (hz : z ∈ lattice F ((e + 1 : ℕ) : ℤ)),
      tau₃ (lowerOneSubUnit F (e + 1) (by omega) z hz) = PsiF z) :
    ∀ (z : F) (hz : z ∈ lattice F (a : ℤ)),
      tau₁ (lowerOneSubUnit F a ha z hz) = PsiF (D.beta1 * z) := by
  let AR2 : Fˣ := A * R2
  have hrs0 : D.rSquare ≠ 0 := by rw [← hR2]; exact R2.ne_zero
  have hba : b + a = 2 * e - a + 1 := by rw [hb]; omega
  have hbaOne : 1 ≤ b + a := by omega
  have hbaE : e + 1 ≤ b + a := by rw [hba]; omega
  have hbaSum : 2 * e < (b + a) + a := by rw [hba]; omega
  have heps0 : D.epsilon ≠ 0 :=
    (ord_ne_top_iff F).1 (by rw [D.epsilon_order]; exact WithTop.coe_ne_top)
  have hepsMem : D.epsilon ∈ lattice F (b : ℤ) := by
    rw [mem_lattice, D.epsilon_order]
    exact_mod_cast le_rfl

  intro z hz
  have hepsz : D.epsilon * z ∈ lattice F ((b + a : ℕ) : ℤ) := by
    simpa only [Nat.cast_add] using mul_mem_lattice F hepsMem hz
  have hepszOne : ((1 : ℤ) : WithTop ℤ) ≤ ord F (D.epsilon * z) :=
    (WithTop.coe_le_coe.mpr (by exact_mod_cast hbaOne)).trans
      ((mem_lattice F).1 hepsz)
  let B : Fˣ := lowerOneSubUnit F a ha z hz
  let C : Fˣ := Dyadic.Mixed.oneAddUnit F (D.epsilon * z) hepszOne
  let epsU : Fˣ := Units.mk0 D.epsilon heps0
  let minusEps : Fˣ := -epsU
  have hAne : (A : F) ≠ 1 := by
    intro h
    apply heps0
    simpa [hA] using sub_eq_zero.mpr h
  have hstein : quadraticNormSymbol F hchar A minusEps = 1 := by
    have h := Dyadic.Mixed.quadraticSymbol_one_sub F hchar A hAne
    have hminus : minusEps =
        Units.mk0 (1 - (A : F)) (sub_ne_zero.mpr hAne.symm) := by
      apply Units.ext
      simp [minusEps, epsU, hA]
    rw [hminus]
    exact h
  have hab : (A : F) + ((minusEps * B : Fˣ) : F) ≠ 0 := by
    have heq : (A : F) + ((minusEps * B : Fˣ) : F) = (C : F) := by
      simp [hA, minusEps, epsU, B, C,
        Dyadic.Mixed.coe_oneAddUnit, coe_lowerOneSubUnit]
      ring
    rw [heq]
    exact C.ne_zero
  have htransform : quadraticNormSymbol F hchar A (minusEps * B) =
      quadraticNormSymbol F hchar C (epsU * B * A) := by
    rw [Dyadic.Mixed.quadraticSymbol_transform F hchar A (minusEps * B) hab]
    congr 2
    · simp [hA, minusEps, epsU, B, coe_lowerOneSubUnit]
      ring
    · apply Units.ext
      simp [minusEps, epsU]
      ring
  have hBmem : B ∈ unitFiltration F a := by
    have haeq : a - 1 + 1 = a := Nat.sub_add_cancel ha
    rw [← haeq, mem_unitFiltration_succ_iff_sub_mem_lattice]
    simp only [haeq, B, coe_lowerOneSubUnit]
    convert neg_mem_lattice F hz using 1
    ring
  have hCB : quadraticNormCharacter F hchar C B = 1 :=
    unitSymbolAtDepth_of_mem_unitFiltration F hchar e (b + a) a htwo
      hbaOne ha hbaSum (D.epsilon * z) hepsz B hBmem
  have hCRatio : quadraticNormCharacter F hchar C D.ratio = 1 :=
    unitSymbolAtDepth_of_mem_unitFiltration F hchar e (b + a) a htwo
      hbaOne ha hbaSum (D.epsilon * z) hepsz D.ratio D.ratio_mem
  have hepsUnit : epsU = R2 * D.ratio := by
    apply Units.ext
    simp only [epsU, Units.val_mk0, Units.val_mul, hR2, D.ratio_coe]
    field_simp [hrs0]
  have hsymbols : quadraticNormSymbol F hchar A B =
      quadraticNormSymbol F hchar AR2 C := by
    calc
      quadraticNormSymbol F hchar A B =
          quadraticNormSymbol F hchar A (minusEps * B) := by
        have hmul := Dyadic.Mixed.quadraticSymbol_mul_right F hchar
          A minusEps B
        rw [hstein, one_mul] at hmul
        exact hmul.symm
      _ = quadraticNormSymbol F hchar C (epsU * B * A) := htransform
      _ = quadraticNormSymbol F hchar C (R2 * A) := by
        rw [hepsUnit]
        simp only [quadraticNormSymbol, map_mul, hCRatio, hCB, one_mul,
          mul_assoc]
      _ = quadraticNormSymbol F hchar (R2 * A) C :=
        Dyadic.Mixed.quadraticSymbol_symmetric F hchar C (R2 * A)
      _ = quadraticNormSymbol F hchar AR2 C := by
        rw [show R2 * A = AR2 by dsimp only [AR2]; exact mul_comm R2 A]
  have hCdeep : -(D.epsilon * z) ∈ lattice F ((e + 1 : ℕ) : ℤ) :=
    neg_mem_lattice F (lattice_antitone F (by exact_mod_cast hbaE) hepsz)
  have hchartC : tau₃ C = PsiF (-(D.epsilon * z)) := by
    have h := hchart₃ (-(D.epsilon * z)) hCdeep
    rw [← h]
    congr 1
    apply Units.ext
    simp [C, Dyadic.Mixed.coe_oneAddUnit, coe_lowerOneSubUnit]
  rw [homega₁]
  change quadraticNormSymbol F hchar A B = PsiF (D.beta1 * z)
  rw [hsymbols]
  change quadraticNormCharacter F hchar AR2 C = PsiF (D.beta1 * z)
  rw [← homega₃, hchartC, O.beta1_table]
  congr 1
  ring

/-- Multiplication of the quadratic characters, followed by the aligned error estimate. -/
private theorem secondLowerFormula
    (ha : 1 ≤ a) (hae : a ≤ e) (hb : b = 2 * e - 2 * a + 1)
    (tau₁ tau₂ tau₃ : ContinuousQuasiChar F)
    (hproduct : ∀ B, tau₂ B = tau₁ B * tau₃ B)
    (PsiF : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F PsiF (-((2 * e + 1 : ℕ) : ℤ)))
    (hformula₁ : ∀ (z : F) (hz : z ∈ lattice F (a : ℤ)),
      tau₁ (lowerOneSubUnit F a ha z hz) = PsiF (D.beta1 * z))
    (hchart₃ : ∀ (z : F) (hz : z ∈ lattice F ((e + 1 : ℕ) : ℤ)),
      tau₃ (lowerOneSubUnit F (e + 1) (by omega) z hz) = PsiF z) :
    ∀ (z : F) (hz : z ∈ lattice F ((e + 1 : ℕ) : ℤ)),
      tau₂ (lowerOneSubUnit F (e + 1) (by omega) z hz) = PsiF (D.beta2 * z) := by
  have hdiff := alignment_parameter_difference_mem D ha
  have hba : b + a = 2 * e - a + 1 := by rw [hb]; omega
  intro z hz
  let B : Fˣ := lowerOneSubUnit F (e + 1) (by omega) z hz
  have hza : z ∈ lattice F (a : ℤ) :=
    lattice_antitone F (by exact_mod_cast (show a ≤ e + 1 by omega)) hz
  have hBfirst : B = lowerOneSubUnit F a ha z hza :=
    lowerOneSubUnit_eq F (by omega) ha z hz hza
  rw [hproduct]
  rw [show tau₁ B = PsiF (-(D.epsilon * z)) by
    rw [hBfirst, hformula₁ z hza, O.beta1_table]
    congr 1
    ring]
  rw [show tau₃ B = PsiF z by exact hchart₃ z hz]
  rw [← ContinuousAddChar.map_add_eq_mul PsiF (-(D.epsilon * z)) z]
  have herr :
      (-(D.epsilon * z) + z) - ((1 - D.rSquare) * z) ∈
        lattice F ((2 * e + 1 : ℕ) : ℤ) := by
    have hmul : (D.epsilon - D.rSquare) * z ∈
        lattice F (((b + a) + (e + 1) : ℕ) : ℤ) := by
      simpa only [Nat.cast_add] using mul_mem_lattice F hdiff hz
    have hdepth : 2 * e + 1 ≤ (b + a) + (e + 1) := by
      rw [hba]
      omega
    have hdepth' :
        ((2 * e + 1 : ℕ) : ℤ) ≤
          (((b + a) + (e + 1) : ℕ) : ℤ) := by
      exact_mod_cast hdepth
    have hmem := lattice_antitone F hdepth' hmul
    convert neg_mem_lattice F hmem using 1
    ring
  have herrPhase :
      PsiF ((-(D.epsilon * z) + z) - ((1 - D.rSquare) * z)) = 1 :=
    hPsi.trivial _ herr
  have hphaseEq : PsiF (-(D.epsilon * z) + z) =
      PsiF ((1 - D.rSquare) * z) := by
    apply div_eq_one.mp
    calc
      PsiF (-(D.epsilon * z) + z) / PsiF ((1 - D.rSquare) * z) =
          PsiF ((-(D.epsilon * z) + z) - ((1 - D.rSquare) * z)) :=
        (PsiF.toAddChar.map_sub_eq_div _ _).symm
      _ = 1 := herrPhase
  rw [hphaseEq, O.beta2_table]

variable
  [ValuativeRel D.firstField] [TopologicalSpace D.firstField]
  [IsNonarchimedeanLocalField D.firstField] [ValuativeExtension F D.firstField]
  [Module.Free F D.firstField] [Module.Finite F D.firstField]
  [PrimeCyclicExtension F D.firstField]
  [ValuativeRel D.secondField] [TopologicalSpace D.secondField]
  [IsNonarchimedeanLocalField D.secondField] [ValuativeExtension F D.secondField]
  [Module.Free F D.secondField] [Module.Finite F D.secondField]
  [PrimeCyclicExtension F D.secondField]
  [ValuativeRel D.thirdField] [TopologicalSpace D.thirdField]
  [IsNonarchimedeanLocalField D.thirdField] [ValuativeExtension F D.thirdField]
  [Module.Free F D.thirdField] [Module.Finite F D.thirdField]
  [PrimeCyclicExtension F D.thirdField]

/-- Construct the Kummer units and identify all three supplied norm characters. -/
private theorem alignedNormCharacters
    (hchar : ringChar F ≠ 2) (hbpos : 0 < b)
    (ht₁ : PrimeCyclicExtension.IsLowerBreak F D.firstField (2 * a - 1))
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F D.secondField (2 * e))
    (ht₃ : PrimeCyclicExtension.IsLowerBreak F D.thirdField (2 * e))
    (hres₁ : residueDegree F D.firstField = 1)
    (hres₂ : residueDegree F D.secondField = 1)
    (hres₃ : residueDegree F D.thirdField = 1)
    (tau₁ : NormCharacter F D.firstField) (htau₁ : tau₁ ≠ 1)
    (tau₂ : NormCharacter F D.secondField) (htau₂ : tau₂ ≠ 1)
    (tau₃ : NormCharacter F D.thirdField) (htau₃ : tau₃ ≠ 1)
    : ∃ A R2 : Fˣ, (A : F) = 1 + D.epsilon ∧ (R2 : F) = D.rSquare ∧
      tau₁.1 = quadraticNormCharacter F hchar A ∧
      tau₂.1 = quadraticNormCharacter F hchar R2 ∧
      tau₃.1 = quadraticNormCharacter F hchar (A * R2) := by
  classical
  let pb₁ : PowerBasis F D.firstField :=
    IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral D.S)
  let pb₂ : PowerBasis F D.secondField :=
    IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral D.R)
  let pb₃ : PowerBasis F D.thirdField :=
    IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral (D.S * D.R))
  have honeEps : 1 + D.epsilon ≠ 0 := by
    intro hzero
    have heq : D.epsilon = -1 := by linear_combination hzero
    have hord : ord F D.epsilon = 0 := by rw [heq, ord_neg, ord_one]
    have hbtop : (b : WithTop ℤ) = 0 := D.epsilon_order.symm.trans hord
    change (((b : ℤ) : WithTop ℤ)) = (((0 : ℤ) : WithTop ℤ)) at hbtop
    have : b = 0 := by exact_mod_cast WithTop.coe_eq_coe.mp hbtop
    omega
  have hrs0 : D.rSquare ≠ 0 :=
    (ord_ne_top_iff F).1 (by rw [D.rSquare_order]; exact WithTop.coe_ne_top)
  let A : Fˣ := Units.mk0 (1 + D.epsilon) honeEps
  let R2 : Fˣ := Units.mk0 D.rSquare hrs0
  let AR2 : Fˣ := A * R2

  have hgenSq₁ : pb₁.gen ^ 2 = algebraMap F D.firstField (A : F) := by
    apply Subtype.ext
    exact D.S_sq
  have hgenSq₂ : pb₂.gen ^ 2 = algebraMap F D.secondField (R2 : F) := by
    apply Subtype.ext
    exact D.R_sq
  have hgenSq₃ : pb₃.gen ^ 2 = algebraMap F D.thirdField (AR2 : F) := by
    apply Subtype.ext
    change (D.S * D.R) ^ 2 = algebraMap F K ((1 + D.epsilon) * D.rSquare)
    rw [mul_pow, D.S_sq, D.R_sq, map_mul]

  have homega₁ : tau₁.1 = quadraticNormCharacter F hchar A :=
    actualNormCharacter_eq_quadratic F D.firstField ht₁ hres₁ O.first_degree
      hchar A pb₁ hgenSq₁ tau₁ htau₁
  have homega₂ : tau₂.1 = quadraticNormCharacter F hchar R2 :=
    actualNormCharacter_eq_quadratic F D.secondField ht₂ hres₂ O.second_degree
      hchar R2 pb₂ hgenSq₂ tau₂ htau₂
  have homega₃ : tau₃.1 = quadraticNormCharacter F hchar AR2 :=
    actualNormCharacter_eq_quadratic F D.thirdField ht₃ hres₃ O.third_degree
      hchar AR2 pb₃ hgenSq₃ tau₃ htau₃

  exact ⟨A, R2, rfl, rfl, homega₁, homega₂, homega₃⟩

/-- Assemble the full lower formulas with their actual norm representatives and phases. -/
private theorem lowerCharacterData_of_formulas
    (ha : 1 ≤ a) (hae : a ≤ e)
    (ht₁ : PrimeCyclicExtension.IsLowerBreak F D.firstField (2 * a - 1))
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F D.secondField (2 * e))
    (ht₃ : PrimeCyclicExtension.IsLowerBreak F D.thirdField (2 * e))
    (hres₁ : residueDegree F D.firstField = 1)
    (hres₂ : residueDegree F D.secondField = 1)
    (hres₃ : residueDegree F D.thirdField = 1)
    (tau₁ : NormCharacter F D.firstField) (tau₂ : NormCharacter F D.secondField)
    (tau₃ : NormCharacter F D.thirdField) (PsiF : ContinuousAddChar F)
    (hformula₁ : ∀ (z : F) (hz : z ∈ lattice F (a : ℤ)),
      tau₁.1 (lowerOneSubUnit F a ha z hz) = PsiF (D.beta1 * z))
    (hformula₂ : ∀ (z : F) (hz : z ∈ lattice F ((e + 1 : ℕ) : ℤ)),
      tau₂.1 (lowerOneSubUnit F (e + 1) (by omega) z hz) = PsiF (D.beta2 * z))
    (hformula₃ : ∀ (z : F) (hz : z ∈ lattice F ((e + 1 : ℕ) : ℤ)),
      tau₃.1 (lowerOneSubUnit F (e + 1) (by omega) z hz) = PsiF (D.beta3 * z)) :
    LowerCharacterData F D.firstField D.secondField D.thirdField
      a e ha tau₁ tau₂ tau₃ PsiF D.beta1 D.beta2 D.beta3 D.h1 D.h2 D.h3 := by
  have htraceDepth₁ : (a : ℤ) ≤
      ((a : ℤ) + ((2 * a - 1 + 1 : ℕ) : ℤ)) / 2 := by
    push_cast [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by omega : a ≠ 0))]
    omega
  have htraceDepth₂ : ((e + 1 : ℕ) : ℤ) ≤
      (((e + 1 : ℕ) : ℤ) + ((2 * e + 1 : ℕ) : ℤ)) / 2 := by
    push_cast
    omega

  refine
    { first_formula := hformula₁
      second_formula := hformula₂
      third_formula := hformula₃
      first_beta_norm := rfl
      second_beta_norm := rfl
      third_beta_norm := rfl
      first_phase := ?_
      second_phase := ?_
      third_phase := ?_ }
  · intro x hx
    exact normPhaseOfLowerFormula F D.firstField ht₁ hres₁ O.first_degree
      ha htraceDepth₁ tau₁ PsiF D.beta1 hformula₁ x hx
  · intro x hx
    exact normPhaseOfLowerFormula F D.secondField ht₂ hres₂ O.second_degree
      (by omega) htraceDepth₂ tau₂ PsiF D.beta2 hformula₂ x hx
  · intro x hx
    exact normPhaseOfLowerFormula F D.thirdField ht₃ hres₃ O.third_degree
      (by omega) htraceDepth₂ tau₃ PsiF D.beta3 hformula₃ x hx

end AlignedLowerCharacters

set_option maxHeartbeats 800000 in
/-- **Full lower-character formulas (`D:MX:lower`).**

For the three literal quadratic intermediate fields of an aligned maximal
dyadic extension, every supplied nontrivial actual norm character has the
paper's exact coefficient on the whole required unit layer.  The third-field
duality chart also forces the exact additive conductor used in the second
formula.  The result retains the chosen origin representatives as genuine
norms and gives the positive-sign trace-to-norm phase conversion on all three
source ideals. -/
theorem lowerCharacters
    {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {pi : ringOfIntegers F} {e a b : ℕ}
    {u0 w0 : (ringOfIntegers F)ˣ} {s R0 : K}
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (hres : residueDegree F K = 1)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (ha : 1 ≤ a) (hae : a ≤ e) (hb : b = 2 * e - 2 * a + 1)
    (D : AlignmentData pi e a b u0 w0 s R0)
    (O : OriginData D) :
    letI : ValuativeRel D.firstField :=
      Basic.intermediateFieldValuativeRel D.firstField
    letI : TopologicalSpace D.firstField :=
      Basic.intermediateFieldTopology D.firstField
    letI : ValuativeRel D.secondField :=
      Basic.intermediateFieldValuativeRel D.secondField
    letI : TopologicalSpace D.secondField :=
      Basic.intermediateFieldTopology D.secondField
    letI : ValuativeRel D.thirdField :=
      Basic.intermediateFieldValuativeRel D.thirdField
    letI : TopologicalSpace D.thirdField :=
      Basic.intermediateFieldTopology D.thirdField
    let E₁ := Basic.intermediateField_tower_compatible Nat.prime_two hG
      D.firstField O.first_degree
    let E₂ := Basic.intermediateField_tower_compatible Nat.prime_two hG
      D.secondField O.second_degree
    let E₃ := Basic.intermediateField_tower_compatible Nat.prime_two hG
      D.thirdField O.third_degree
    letI : IsNonarchimedeanLocalField D.firstField := E₁.1
    letI : Module.Free F D.firstField := E₁.2.1
    letI : Module.Finite F D.firstField := E₁.2.2.1
    letI : ValuativeExtension F D.firstField := E₁.2.2.2.2.2.2.1
    letI : CyclicPrimeExtension F D.firstField := E₁.2.2.2.2.2.2.2.2.2.2.2.1
    letI : IsNonarchimedeanLocalField D.secondField := E₂.1
    letI : Module.Free F D.secondField := E₂.2.1
    letI : Module.Finite F D.secondField := E₂.2.2.1
    letI : ValuativeExtension F D.secondField := E₂.2.2.2.2.2.2.1
    letI : CyclicPrimeExtension F D.secondField := E₂.2.2.2.2.2.2.2.2.2.2.2.1
    letI : IsNonarchimedeanLocalField D.thirdField := E₃.1
    letI : Module.Free F D.thirdField := E₃.2.1
    letI : Module.Finite F D.thirdField := E₃.2.2.1
    letI : ValuativeExtension F D.thirdField := E₃.2.2.2.2.2.2.1
    letI : CyclicPrimeExtension F D.thirdField := E₃.2.2.2.2.2.2.2.2.2.2.2.1
    ∀ (_ht₁ : PrimeCyclicExtension.IsLowerBreak F D.firstField (2 * a - 1))
      (_ht₂ : PrimeCyclicExtension.IsLowerBreak F D.secondField (2 * e))
      (_ht₃ : PrimeCyclicExtension.IsLowerBreak F D.thirdField (2 * e))
      (tau₁ : NormCharacter F D.firstField) (_htau₁ : tau₁ ≠ 1)
      (tau₂ : NormCharacter F D.secondField) (_htau₂ : tau₂ ≠ 1)
      (tau₃ : NormCharacter F D.thirdField) (_htau₃ : tau₃ ≠ 1)
      (PsiF : ContinuousAddChar F)
      (_hchart₃ : ∀ (z : F) (hz : z ∈ lattice F ((e + 1 : ℕ) : ℤ)),
        tau₃.1 (lowerOneSubUnit F (e + 1) (by omega) z hz) = PsiF z),
      LowerCharacterData F D.firstField D.secondField D.thirdField
        a e ha tau₁ tau₂ tau₃ PsiF D.beta1 D.beta2 D.beta3 D.h1 D.h2 D.h3 := by
  dsimp only
  letI : ValuativeRel D.firstField :=
    Basic.intermediateFieldValuativeRel D.firstField
  letI : TopologicalSpace D.firstField :=
    Basic.intermediateFieldTopology D.firstField
  letI : ValuativeRel D.secondField :=
    Basic.intermediateFieldValuativeRel D.secondField
  letI : TopologicalSpace D.secondField :=
    Basic.intermediateFieldTopology D.secondField
  letI : ValuativeRel D.thirdField :=
    Basic.intermediateFieldValuativeRel D.thirdField
  letI : TopologicalSpace D.thirdField :=
    Basic.intermediateFieldTopology D.thirdField
  let E₁ := Basic.intermediateField_tower_compatible Nat.prime_two hG
    D.firstField O.first_degree
  let E₂ := Basic.intermediateField_tower_compatible Nat.prime_two hG
    D.secondField O.second_degree
  let E₃ := Basic.intermediateField_tower_compatible Nat.prime_two hG
    D.thirdField O.third_degree
  letI : IsNonarchimedeanLocalField D.firstField := E₁.1
  letI : Module.Free F D.firstField := E₁.2.1
  letI : Module.Finite F D.firstField := E₁.2.2.1
  letI : ValuativeExtension F D.firstField := E₁.2.2.2.2.2.2.1
  letI : CyclicPrimeExtension F D.firstField := E₁.2.2.2.2.2.2.2.2.2.2.2.1
  letI : PrimeCyclicExtension F D.firstField :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F D.firstField
      E₁.2.2.2.2.2.2.2.2.2.2.2.1
  letI : IsNonarchimedeanLocalField D.secondField := E₂.1
  letI : Module.Free F D.secondField := E₂.2.1
  letI : Module.Finite F D.secondField := E₂.2.2.1
  letI : ValuativeExtension F D.secondField := E₂.2.2.2.2.2.2.1
  letI : CyclicPrimeExtension F D.secondField := E₂.2.2.2.2.2.2.2.2.2.2.2.1
  letI : PrimeCyclicExtension F D.secondField :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F D.secondField
      E₂.2.2.2.2.2.2.2.2.2.2.2.1
  letI : IsNonarchimedeanLocalField D.thirdField := E₃.1
  letI : Module.Free F D.thirdField := E₃.2.1
  letI : Module.Finite F D.thirdField := E₃.2.2.1
  letI : ValuativeExtension F D.thirdField := E₃.2.2.2.2.2.2.1
  letI : CyclicPrimeExtension F D.thirdField := E₃.2.2.2.2.2.2.2.2.2.2.2.1
  letI : PrimeCyclicExtension F D.thirdField :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F D.thirdField
      E₃.2.2.2.2.2.2.2.2.2.2.2.1
  intro ht₁ ht₂ ht₃ tau₁ htau₁ tau₂ htau₂ tau₃ htau₃ PsiF hchart₃
  classical

  have htwoNe : (2 : F) ≠ 0 := by
    intro hzero
    rw [hzero, ord_zero] at htwo
    exact WithTop.top_ne_coe htwo
  have hchar : ringChar F ≠ 2 := by
    intro hringChar
    letI : CharP F 2 := ringChar.of_eq hringChar
    exact htwoNe (CharP.cast_eq_zero F 2)

  have hres₁ := intermediate_residueDegree_eq_one D.firstField hres
  have hres₂ := intermediate_residueDegree_eq_one D.secondField hres
  have hres₃ := intermediate_residueDegree_eq_one D.thirdField hres
  obtain ⟨A, R2, hA, hR2, homega₁, homega₂, homega₃⟩ :=
    alignedNormCharacters D O hchar (by rw [hb]; omega)
      ht₁ ht₂ ht₃ hres₁ hres₂ hres₃ tau₁ htau₁ tau₂ htau₂ tau₃ htau₃
  obtain ⟨pi₃, hpi₃, hgen₃⟩ := monogenicUniformizer F D.thirdField hres₃
  have hPsi := additiveConductor_of_lowerChart F e (ha.trans hae) tau₃.1
    (ramifiedNormCharacter_conductor F D.thirdField ht₃ hres₃
      pi₃ hpi₃ hgen₃ tau₃ htau₃) PsiF hchart₃
  have hformula₁ := firstLowerFormula D O hchar htwo ha hae hb
    A R2 hA hR2 tau₁.1 tau₃.1 homega₁ homega₃ PsiF hchart₃
  have hproduct : ∀ B, tau₂.1 B = tau₁.1 B * tau₃.1 B := by
    rw [homega₁, homega₂, homega₃]
    exact quadraticNormCharacter_product F hchar A R2
  have hformula₂ := secondLowerFormula D O ha hae hb
    tau₁.1 tau₂.1 tau₃.1 hproduct PsiF hPsi hformula₁ hchart₃
  apply lowerCharacterData_of_formulas D O ha hae ht₁ ht₂ ht₃ hres₁ hres₂ hres₃
    tau₁ tau₂ tau₃ PsiF hformula₁ hformula₂
  intro z hz
  rw [O.beta3_table, one_mul]
  exact hchart₃ z hz

end

end LanglandsSecondMainLemma.Dyadic.Maximal
