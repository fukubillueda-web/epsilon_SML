import LanglandsFirstMainLemma.Delta.Elementary
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Dyadic.Maximal.Twist
import LanglandsSecondMainLemma.Stationary.NormalizationFreedom

/-!
# Dyadic / Maximal / Normalization

Paper Lemma 12.8 (`D:MX:freedom`). Changing the normalization by a unit of
`U_F^(2e)` preserves the whole lower-character formulas, their norm-phase
conversions, and the full stationary formulas of the already fixed cores.
The permitted change then makes any nonzero base coefficient an actual
third-field norm, while preserving its raw covector.
-/

namespace LanglandsSecondMainLemma.Dyadic.Maximal

open LanglandsFirstMainLemma

noncomputable section

private theorem normalization_unit_sub
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {d : ℕ} (hd : 0 < d) (u : unitFiltration F d) :
    ((u : Fˣ) : F) - 1 ∈ lattice F (d : ℤ) := by
  cases d with
  | zero => omega
  | succ n => exact (mem_unitFiltration_succ_iff_sub_mem_lattice F n _).1 u.property

/-- Scaling changes a phase by precisely the value on `(u-1)*x`. -/
private theorem normalization_scaled_value
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (psi : LocalAddCharData F) (alpha u : Fˣ) {T : ℤ}
    (htrivial : AddCharTrivialOnLattice F
      (scaleAddCharData F psi alpha).character T)
    (x : F) (hx : ((u : F) - 1) * x ∈ lattice F T) :
    (scaleAddCharData F psi (alpha * u)).character x =
      (scaleAddCharData F psi alpha).character x := by
  have h := htrivial _ hx
  simp only [scaleAddCharData_character_apply, Units.val_mul] at h ⊢
  rw [show (alpha : F) * (u : F) * x =
    (alpha : F) * x + (alpha : F) * (((u : F) - 1) * x) by ring,
    ContinuousAddChar.map_add_eq_mul, h, mul_one]

/-- The lower phase error has depth `2e + v(beta) + q`. -/
private theorem normalization_lower_value
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (psi : LocalAddCharData F) (alpha : Fˣ) {e : ℕ} (he : 0 < e)
    (htrivial : AddCharTrivialOnLattice F
      (scaleAddCharData F psi alpha).character (2 * (e : ℤ) + 1))
    {b q : ℤ} (hdepth : 2 * (e : ℤ) + 1 ≤ 2 * (e : ℤ) + b + q)
    (beta : F) (hbeta : beta ∈ lattice F b)
    (u : unitFiltration F (2 * e)) (z : F) (hz : z ∈ lattice F q) :
    (scaleAddCharData F psi (alpha * (u : Fˣ))).character (beta * z) =
      (scaleAddCharData F psi alpha).character (beta * z) := by
  apply normalization_scaled_value F psi alpha (u : Fˣ) htrivial
  have hu := normalization_unit_sub F (by omega : 0 < 2 * e) u
  have hmul := mul_mem_lattice F hu (mul_mem_lattice F hbeta hz)
  apply lattice_antitone F hdepth
  simpa only [Nat.cast_mul, Nat.cast_ofNat, add_assoc] using hmul

/-- The upper phase error has depth `4e + v(c) + d`; the actual
quadratic trace ideal sends it into the base additive kernel. -/
private theorem normalization_core_value
    (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
    [PrimeCyclicExtension F E]
    {t d e : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hdeg : Module.finrank F E = 2)
    (he : 0 < e) (hd : 0 < d) {cdepth : ℤ}
    (hdepth : 2 * (e : ℤ) + 1 ≤
      (4 * (e : ℤ) + cdepth + (d : ℤ) + (t + 1 : ℕ)) / 2)
    (psi : LocalAddCharData F) (alpha : Fˣ)
    (htrivial : AddCharTrivialOnLattice F
      (scaleAddCharData F psi alpha).character (2 * (e : ℤ) + 1))
    (c : E) (hc : c ∈ lattice E cdepth)
    (u : unitFiltration F (2 * e)) (v : unitFiltration E d) :
    corePhaseValue E
        (tracePullbackAddChar F E (scaleAddCharData F psi (alpha * (u : Fˣ))).character)
        c (v : Eˣ) =
      corePhaseValue E
        (tracePullbackAddChar F E (scaleAddCharData F psi alpha).character)
        c (v : Eˣ) := by
  have hram : ramificationIndex F E = 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F E
    rw [hres, mul_one, hdeg] at h
    exact h.symm
  let z : E := 1 - ((v : Eˣ) : E)
  have hz : z ∈ lattice E (d : ℤ) := by
    simpa only [neg_sub] using neg_mem_lattice E (normalization_unit_sub E hd v)
  have hu : algebraMap F E (((u : Fˣ) : F) - 1) ∈ lattice E (4 * (e : ℤ)) := by
    rw [mem_lattice, ord_algebraMap, hram]
    have h := (mem_lattice F).1 (normalization_unit_sub F (by omega : 0 < 2 * e) u)
    have hh := add_le_add h h
    simpa only [two_nsmul, ← WithTop.coe_add, Nat.cast_mul, Nat.cast_ofNat,
      show 2 * (e : ℤ) + 2 * (e : ℤ) = 4 * (e : ℤ) by ring] using hh
  have hx : algebraMap F E (((u : Fˣ) : F) - 1) * (c * z) ∈
      lattice E (4 * (e : ℤ) + cdepth + (d : ℤ)) := by
    simpa only [add_assoc] using mul_mem_lattice E hu (mul_mem_lattice E hc hz)
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have htrace : trace F E (algebraMap F E (((u : Fˣ) : F) - 1) * (c * z)) ∈
      lattice F ((4 * (e : ℤ) + cdepth + (d : ℤ) + (t + 1 : ℕ)) / 2) := by
    have hmap : trace F E (algebraMap F E (((u : Fˣ) : F) - 1) * (c * z)) ∈
        Submodule.map ((trace F E).restrictScalars (ringOfIntegers F))
          ((lattice E (4 * (e : ℤ) + cdepth + (d : ℤ))).restrictScalars
            (ringOfIntegers F)) := Submodule.mem_map.mpr ⟨_, hx, rfl⟩
    rw [cyclicPrime_trace_lattice_image_eq F E ht hres pi hpi hgen, hdeg] at hmap
    simpa only [Nat.reduceSub, one_mul, Nat.cast_ofNat] using hmap
  have htraceMul : trace F E (algebraMap F E (((u : Fˣ) : F) - 1) * (c * z)) =
      (((u : Fˣ) : F) - 1) * trace F E (c * z) := by
    simpa [Algebra.smul_def] using (trace F E).map_smul (((u : Fˣ) : F) - 1) (c * z)
  rw [htraceMul] at htrace
  exact normalization_scaled_value F psi alpha (u : Fˣ) htrivial _
    (lattice_antitone F hdepth htrace)

/-- FML represents every field element by a norm modulo the critical
unit layer. Norm-triviality therefore gives the required full character
image without asserting surjectivity of the critical norm map. -/
private theorem normalization_norm_character_image
    (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
    [PrimeCyclicExtension F E]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (tau : NormCharacter F E) :
    (unitFiltration F t).map tau.1.toMonoidHom = tau.1.toMonoidHom.range := by
  apply le_antisymm
  · rintro y ⟨u, _, rfl⟩
    exact ⟨u, rfl⟩
  · rintro y ⟨u, rfl⟩
    obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
    obtain ⟨x, hx⟩ := exists_norm_representative_mod_break F E ht hres pi hpi hgen u
    refine ⟨u / normUnits F E x, hx, ?_⟩
    change tau.1 (u / normUnits F E x) = tau.1 u
    rw [map_div, tau.eq_one_on_normRange F E _ ⟨x, rfl⟩, div_one]


/-- The complete formulas whose preservation is required in `D:MX:freedom`.
The lower part includes the actual norm representatives and all three
whole-ideal trace-to-norm phase conversions from `D:MX:lowerformula`.
The upper part is the full `D:MX:R` formula for the same three continuous
characters, on their full stationary unit groups. -/
def NormalizationFormulas
    (F L₁ L₂ L₃ : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field L₁] [ValuativeRel L₁] [TopologicalSpace L₁]
    [IsNonarchimedeanLocalField L₁] [Algebra F L₁]
    [Module.Finite F L₁] [ValuativeExtension F L₁]
    [Field L₂] [ValuativeRel L₂] [TopologicalSpace L₂]
    [IsNonarchimedeanLocalField L₂] [Algebra F L₂]
    [Module.Finite F L₂] [ValuativeExtension F L₂]
    [Field L₃] [ValuativeRel L₃] [TopologicalSpace L₃]
    [IsNonarchimedeanLocalField L₃] [Algebra F L₃]
    [Module.Finite F L₃] [ValuativeExtension F L₃]
    (a e : ℕ) (ha : 0 < a)
    (tau₁ : NormCharacter F L₁) (tau₂ : NormCharacter F L₂)
    (tau₃ : NormCharacter F L₃) (psi : LocalAddCharData F)
    (beta₁ beta₂ beta₃ : F) (h₁ : L₁) (h₂ : L₂) (h₃ : L₃)
    (c₁ : L₁) (c₂ : L₂) (c₃ : L₃)
    (chi₁ : ContinuousQuasiChar L₁) (chi₂ : ContinuousQuasiChar L₂)
    (chi₃ : ContinuousQuasiChar L₃) (alpha : Fˣ) : Prop :=
  LowerCharacterData F L₁ L₂ L₃ a e ha tau₁ tau₂ tau₃
      (scaleAddCharData F psi alpha).character beta₁ beta₂ beta₃ h₁ h₂ h₃ ∧
    (∀ v : unitFiltration L₁ (2 * e + 1),
      chi₁ (v : L₁ˣ) = corePhaseValue L₁
        (tracePullbackAddChar F L₁ (scaleAddCharData F psi alpha).character)
        c₁ (v : L₁ˣ)) ∧
    (∀ v : unitFiltration L₂ (e + a),
      chi₂ (v : L₂ˣ) = corePhaseValue L₂
        (tracePullbackAddChar F L₂ (scaleAddCharData F psi alpha).character)
        c₂ (v : L₂ˣ)) ∧
    (∀ v : unitFiltration L₃ (e + a),
      chi₃ (v : L₃ˣ) = corePhaseValue L₃
        (tracePullbackAddChar F L₃ (scaleAddCharData F psi alpha).character)
        c₃ (v : L₃ˣ))

/-- Total ramification passes to the actual intermediate field. Norm
transitivity and the valuation of one uniformizer give the assertion
without introducing a second valuation on that field. -/
private theorem normalization_lower_residueDegree
    {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]
    (E : IntermediateField F K)
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeExtension F E] [ValuativeExtension E K]
    (hres : residueDegree F K = 1) : residueDegree F E = 1 := by
  obtain ⟨x, hx⟩ := exists_ord_eq K 1
  have h := congrArg (ord F) (Basic.norm_tower (F := F) (L := E) x)
  rw [ord_norm, ord_norm, ord_norm, hres, hx] at h
  have hmul : residueDegree F E * residueDegree E K = 1 := by
    have hz : residueDegree F E • residueDegree E K • (1 : ℤ) = 1 • (1 : ℤ) := by
      exact_mod_cast h
    have hz' : (residueDegree F E : ℤ) * (residueDegree E K : ℤ) = 1 := by
      simpa [nsmul_eq_mul] using hz
    exact_mod_cast hz'
  exact (mul_eq_one.mp hmul).1

set_option maxHeartbeats 1200000 in
/-- **Preservation and an exact third-field norm (`D:MX:freedom`).**

For the genuine aligned three-field diagram, every change `alpha ↦ alpha*u`
with `u ∈ U_F^(2e)` preserves all the fixed formulas. An allowed change
makes `Astar/u` the norm of an actual element of the third field. The
normalization order, the norm valuation, and the raw covector `alpha*Astar`
are retained. The final identity is on every base-field element, so any
coefficient formula for any continuous base quasi-character transfers
with the same character and domain.

`NormalizationFormulas` takes the already constructed lower data and core
formulas from `lowerCharacters` and `twist`; preservation is proved here,
not assumed. The actual norm image at the critical depth is used without
assuming that the critical norm map is onto. -/
theorem normalization
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
      (psi : LocalAddCharData F) (alpha : Fˣ)
      (_halpha : ord F (alpha : F) =
        ((-psi.conductor - (2 * (e : ℤ) + 1) : ℤ) : WithTop ℤ))
      (chi₁ : ContinuousQuasiChar D.firstField)
      (chi₂ : ContinuousQuasiChar D.secondField)
      (chi₃ : ContinuousQuasiChar D.thirdField),
      let FixedFormulas := NormalizationFormulas F D.firstField D.secondField D.thirdField
        a e ha tau₁ tau₂ tau₃ psi D.beta1 D.beta2 D.beta3 D.h1 D.h2 D.h3
        D.a1 D.a2 D.a3 chi₁ chi₂ chi₃
      FixedFormulas alpha →
        (∀ u : unitFiltration F (2 * e),
          FixedFormulas (alpha * (u : Fˣ))) ∧
        ∀ Astar : Fˣ, ∃ (u : unitFiltration F (2 * e)) (X : D.thirdFieldˣ),
          Astar / (u : Fˣ) = normUnits F D.thirdField X ∧
          FixedFormulas (alpha * (u : Fˣ)) ∧
          ord F ((alpha * (u : Fˣ) : Fˣ) : F) = ord F (alpha : F) ∧
          ord D.thirdField (X : D.thirdField) =
            ord F ((Astar / (u : Fˣ) : Fˣ) : F) ∧
          (alpha * (u : Fˣ)) * (Astar / (u : Fˣ)) = alpha * Astar ∧
          (∀ x : F,
            (scaleAddCharData F psi (alpha * (u : Fˣ))).character
                (((Astar / (u : Fˣ) : Fˣ) : F) * x) =
              (scaleAddCharData F psi alpha).character ((Astar : F) * x)) := by
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
  letI : ValuativeExtension D.firstField K := E₁.2.2.2.2.2.2.2.1
  letI : ValuativeExtension D.secondField K := E₂.2.2.2.2.2.2.2.1
  letI : ValuativeExtension D.thirdField K := E₃.2.2.2.2.2.2.2.1
  intro ht₁ ht₂ ht₃ tau₁ htau₁ tau₂ htau₂ tau₃ htau₃ psi alpha halpha
    chi₁ chi₂ chi₃
  let FixedFormulas := NormalizationFormulas F D.firstField D.secondField D.thirdField
    a e ha tau₁ tau₂ tau₃ psi D.beta1 D.beta2 D.beta3 D.h1 D.h2 D.h3
    D.a1 D.a2 D.a3 chi₁ chi₂ chi₃
  change FixedFormulas alpha → _
  intro H
  have he : 0 < e := by omega
  have hres₁ := normalization_lower_residueDegree D.firstField hres
  have hres₂ := normalization_lower_residueDegree D.secondField hres
  have hres₃ := normalization_lower_residueDegree D.thirdField hres
  have htrivial : AddCharTrivialOnLattice F
      (scaleAddCharData F psi alpha).character (2 * (e : ℤ) + 1) := by
    intro x hx
    rw [scaleAddCharData_character_apply]
    apply psi.isConductor.trivial
    have halphaMem : (alpha : F) ∈ lattice F (-psi.conductor - (2 * (e : ℤ) + 1)) := by
      rw [mem_lattice, halpha]
    have hmul := mul_mem_lattice F halphaMem hx
    simpa only [sub_add_cancel] using hmul
  have hc₁ : D.a1 ∈ lattice D.firstField (1 - 2 * (a : ℤ)) := by
    rw [mem_lattice]
    exact le_of_eq (by simpa only [intermediateOrder] using O.a1_order.symm)
  have hc₂ : D.a2 ∈ lattice D.secondField (1 - 2 * (a : ℤ)) := by
    rw [mem_lattice]
    exact le_of_eq (by simpa only [intermediateOrder] using O.a2_order.symm)
  have hc₃ : D.a3 ∈ lattice D.thirdField (1 - 2 * (a : ℤ)) := by
    rw [mem_lattice]
    exact le_of_eq (by simpa only [intermediateOrder] using O.a3_order.symm)
  have hpreserved (u : unitFiltration F (2 * e)) :
      FixedFormulas (alpha * (u : Fˣ)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply lowerCharacters hG hres htwo ha hae hb D O
        ht₁ ht₂ ht₃ tau₁ htau₁ tau₂ htau₂ tau₃ htau₃
      intro z hz
      have hvalue := normalization_lower_value F psi alpha he htrivial
        (b := 0) (q := ((e + 1 : ℕ) : ℤ)) (by omega)
        1 (by simp) u z hz
      simpa only [one_mul] using
        (H.1.third_formula z hz).trans (by simpa only [O.beta3_table, one_mul] using hvalue.symm)
    · intro v
      exact (H.2.1 v).trans (normalization_core_value F D.firstField
        ht₁ hres₁ O.first_degree he (by omega) (by
          have hsub : ((2 * a - 1 : ℕ) : ℤ) = 2 * (a : ℤ) - 1 := by omega
          simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, hsub]
          omega)
        psi alpha htrivial D.a1 hc₁ u v).symm
    · intro v
      exact (H.2.2.1 v).trans (normalization_core_value F D.secondField
        ht₂ hres₂ O.second_degree he (by omega) (by
          push_cast
          omega)
        psi alpha htrivial D.a2 hc₂ u v).symm
    · intro v
      exact (H.2.2.2 v).trans (normalization_core_value F D.thirdField
        ht₃ hres₃ O.third_degree he (by omega) (by
          push_cast
          omega)
        psi alpha htrivial D.a3 hc₃ u v).symm
  refine ⟨hpreserved, ?_⟩
  intro Astar
  have himage := normalization_norm_character_image F D.thirdField ht₃ hres₃ tau₃
  have htauVal : tau₃.1 ≠ 1 := by
    intro h
    exact htau₃ (Subtype.ext h)
  obtain ⟨u, X, hnorm, _, hraw⟩ := Stationary.normalizationFreedom
    E₃.2.2.2.2.2.2.2.2.2.2.2.1 tau₃ htauVal (unitFiltration F (2 * e))
    FixedFormulas alpha Astar (fun u => iff_of_true (hpreserved u) H) himage
  refine ⟨u, X, hnorm, hpreserved u, ?_, ?_, hraw, ?_⟩
  · have hu : ord F ((u : Fˣ) : F) = 0 :=
      (mem_unitFiltration_zero F _).1
        (unitFiltration_antitone F (Nat.zero_le _) u.property)
    simp only [Units.val_mul, ord_mul, hu, add_zero]
  · have h := congrArg (fun y : Fˣ => ord F (y : F)) hnorm
    rw [coe_normUnits, ord_norm, hres₃, one_nsmul] at h
    exact h.symm
  · intro x
    simp only [scaleAddCharData_character_apply]
    have h := congrArg (fun y : Fˣ => (y : F)) hraw
    simp only [Units.val_mul] at h
    exact congrArg psi.character (by simpa only [Units.val_mul, mul_assoc] using congrArg (fun y : F => y * x) h)

end
end LanglandsSecondMainLemma.Dyadic.Maximal
