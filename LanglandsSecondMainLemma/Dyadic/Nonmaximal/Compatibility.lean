import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.LowerCharacters
import LanglandsSecondMainLemma.Algebra.BiquadraticE2

/-!
# Dyadic nonmaximal compatibility

Paper Lemma 13.5, `D:NM:compat`, with the full setup at
`D:NM:breaks`, `D:NM:upper`, `D:NM:origin`, `D:NM:lower`, and
`D:NM:Rcharts` (controlling source, lines 7405--7458, 7500--7624,
and 7700--7724).

The accepted origin and lower-character data have constructors from the
actual fields and characters. FML's finite stationary pairing and
principal-unit/lattice quotient equivalence construct the three chart
homomorphisms. Its trace-ideal formula proves domain membership and the
relative trace depths. The exact quadratic norm formula and the accepted
positive lower norm-phase relation remove the norm-of-trace term in the
biquadratic E₂ identity. No norm surjectivity or shallow commutator is used.

The input `V : Kˣ` is the paper's `1-v`; its hypothesis is exactly
`v ∈ 𝔭_K^(2r)`. Since `r ≥ a ≥ 1`, every such `1-v` is nonzero.
-/

namespace LanglandsSecondMainLemma.Dyadic.Nonmaximal

open LanglandsFirstMainLemma
open LanglandsSecondMainLemma.Characters

noncomputable section

/-- Construct the actual stationary chart through FML's multiplicative
principal-unit/lattice quotient equivalence. The negative coefficient
converts its displacement `u-1` to the paper's `1-u`. -/
private theorem exists_chart
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (Ψ : LocalAddCharData E) (c : Eˣ) (s m : ℕ)
    (hs : 0 < s) (hsm : s ≤ m) (hms : m ≤ 2 * s)
    (hc : Ψ.conductor + unitOrder E c = -(m : ℤ)) :
    ∃ R : unitFiltration E s →* ℂˣ,
      ∀ u, R u = Ψ.character ((c : E) * (1 - ((u : Eˣ) : E))) := by
  let ψ := scaleAddCharData E Ψ (-c)
  have hord : unitOrder E (-c) = unitOrder E c := by
    apply WithTop.coe_injective
    rw [← ord_coe_eq_unitOrder E (-c), ← ord_coe_eq_unitOrder E c]
    simp
  have hψ : ψ.conductor = -(m : ℤ) := by
    change Ψ.conductor + unitOrder E (-c) = _
    rw [hord, hc]
  have hΓ : ord E ((1 : Eˣ) : E) =
      (((m : ℤ) + ψ.conductor : ℤ) : WithTop ℤ) := by rw [hψ]; simp
  let hsmZ : (s : ℤ) ≤ (m : ℤ) := by exact_mod_cast hsm
  let C : lattice E ((m : ℤ) - m) := ⟨1, by simp⟩
  let χ := lamprechtPairing E ψ hsmZ 1 hΓ
    (latticeQuotientMk E (sub_le_sub_left hsmZ (m : ℤ)) C)
  let R := (AddChar.toMonoidHomEquiv χ).comp
    ((positiveUnitFiltrationQuotientMulEquivLattice E hs hsm hms).toMonoidHom.comp
      (unitFiltrationQuotientMk E hsm))
  refine ⟨R, ?_⟩
  intro u
  change χ (latticeQuotientMk E hsmZ (positiveUnitDisplacement E hs u)) = _
  rw [lamprechtPairing_mk_mk, coe_positiveUnitDisplacement,
    scaleAddCharData_character_apply]
  congr 1
  simp only [C, Units.val_neg, Units.val_one, div_one, one_mul]
  ring

/-- Field-coefficient form of the preceding constructor. -/
private theorem exists_chart_of_order
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (Ψ : LocalAddCharData E) (c : E) (n : ℤ)
    (hc : ord E c = (n : WithTop ℤ)) (s m : ℕ)
    (hs : 0 < s) (hsm : s ≤ m) (hms : m ≤ 2 * s)
    (hconductor : Ψ.conductor + n = -(m : ℤ)) :
    ∃ R : unitFiltration E s →* ℂˣ,
      ∀ u, R u = Ψ.character (c * (1 - ((u : Eˣ) : E))) := by
  have hc0 : c ≠ 0 := (ord_ne_top_iff E).mp (by rw [hc]; simp)
  let C : Eˣ := Units.mk0 c hc0
  have hC : unitOrder E C = n := by
    apply WithTop.coe_injective
    rw [← ord_coe_eq_unitOrder E C]
    exact hc
  exact exists_chart E Ψ C s m hs hsm hms (by rw [hC]; exact hconductor)

/-- On one quadratic edge, the norm endpoint has the required depth and
its prescribed chart value is the common second-symmetric-function phase.
The numerical inequalities are instantiated by the nonmaximal break ledger. -/
private theorem compatibility_edge
    (F K : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [Module.Finite F K] [IsGalois F K] [IsKleinFour Gal(K/F)]
    (L : IntermediateField F K)
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension F L] [ValuativeExtension L K]
    [Module.Finite F L] [Module.Finite L K]
    [Algebra.IsQuadraticExtension F L] [Algebra.IsQuadraticExtension L K]
    [PrimeCyclicExtension L K]
    (t : ℕ) (ht : PrimeCyclicExtension.IsLowerBreak L K t)
    (hres : residueDegree L K = 1)
    (s : ℕ) (hs : 0 < s) (q : ℤ) (j y h : ℤ)
    (htraceDepth : (s : ℤ) ≤ (j + (t + 1 : ℕ)) / 2)
    (hnormDepth : (s : ℤ) ≤ j)
    (hrelativeDepth : h + q ≤ (y + j + (t + 1 : ℕ)) / 2)
    (Ψ : ContinuousAddChar F) (Y : K)
    (hY : ord K Y = (y : WithTop ℤ))
    (hH : ord L (trace L K Y) = (h : WithTop ℤ))
    (hphase : ∀ w ∈ lattice L q,
      tracePullbackAddChar F L Ψ (algebraMap F L (norm F L (trace L K Y)) * w) =
        Ψ (norm F L (trace L K Y) * norm F L w))
    (V : Kˣ) (hV : 1 - (V : K) ∈ lattice K j) :
    normUnits L K V ∈ unitFiltration L s ∧
      tracePullbackAddChar F L Ψ
        (norm L K Y * (1 - (normUnits L K V : L))) =
        Ψ (-elementarySymmetric F K 2 (Y * (V : K)) +
          elementarySymmetric F K 2 Y) := by
  have htrace (b : ℤ) (u : K) (hu : u ∈ lattice K b) :
      trace L K u ∈ lattice L ((b + (t + 1 : ℕ)) / 2) := by
    obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer L K hres
    have hm : trace L K u ∈
        Submodule.map ((trace L K).restrictScalars (ringOfIntegers L))
          ((lattice K b).restrictScalars (ringOfIntegers L)) := ⟨u, hu, rfl⟩
    rw [cyclicPrime_trace_lattice_image_eq L K ht hres pi hpi hgen,
      Algebra.IsQuadraticExtension.finrank_eq_two L K] at hm
    simpa only [Nat.reduceSub, one_mul, Nat.cast_ofNat] using hm
  let v : K := 1 - (V : K)
  have hnormv : norm L K v ∈ lattice L (s : ℤ) := by
    apply lattice_antitone L hnormDepth
    rw [mem_lattice, ord_norm, hres, one_nsmul]
    exact hV
  have hnormV : (normUnits L K V : L) =
      1 - trace L K v + norm L K v := by
    rw [coe_normUnits, show (V : K) = 1 - v by dsimp [v]; ring]
    simpa using wildQuadratic_norm_sub L K
      (Algebra.IsQuadraticExtension.finrank_eq_two L K) 1 v
  have hdomain : normUnits L K V ∈ unitFiltration L s := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
    rw [mem_unitFiltration_succ_iff_sub_mem_lattice, hnormV]
    convert sub_mem_lattice L hnormv
      (lattice_antitone L htraceDepth (htrace j v hV)) using 1
    ring
  refine ⟨hdomain, ?_⟩
  let H : L := trace L K Y
  let w : L := trace L K (Y * v) / H
  have hH0 : H ≠ 0 := by
    intro hzero
    have htopp := hH
    rw [show trace L K Y = 0 from hzero, ord_zero] at htopp
    exact WithTop.top_ne_coe htopp
  have hw : w ∈ lattice L q := by
    rw [div_mem_lattice_iff L H _ h q hH]
    apply lattice_antitone L hrelativeDepth
    apply htrace
    exact mul_mem_lattice K (by rw [mem_lattice, hY]) hV
  have htraceYV : trace L K (Y * (V : K)) = H * (1 - w) := by
    have hdecomp : Y * (V : K) = Y - Y * v := by dsimp [v]; ring
    rw [hdecomp, map_sub]
    change H - trace L K (Y * v) = H * (1 - trace L K (Y * v) / H)
    field_simp [hH0]
  have hnormTrace : norm F L (trace L K (Y * (V : K))) =
      norm F L H * (1 - trace F L w + norm F L w) := by
    rw [htraceYV, map_mul]
    congr 1
    simpa using wildQuadratic_norm_sub F L
      (Algebra.IsQuadraticExtension.finrank_eq_two F L) 1 w
  have htraceMul : trace F L (algebraMap F L (norm F L H) * w) =
      norm F L H * trace F L w := by
    simpa [Algebra.smul_def] using (trace F L).map_smul (norm F L H) w
  have herr : Ψ (norm F L H * trace F L w - norm F L H * norm F L w) = 1 := by
    calc
      _ = Ψ (norm F L H * trace F L w) / Ψ (norm F L H * norm F L w) :=
        Ψ.toAddChar.map_sub_eq_div _ _
      _ = 1 := div_eq_one.mpr (by
        have hp := hphase w hw
        change Ψ (trace F L (algebraMap F L (norm F L H) * w)) =
          Ψ (norm F L H * norm F L w) at hp
        rwa [htraceMul] at hp)
  have he2 : -elementarySymmetric F K 2 (Y * (V : K)) +
      elementarySymmetric F K 2 Y =
      trace F L (norm L K Y * (1 - (normUnits L K V : L))) +
        (norm F L H * trace F L w - norm F L H * norm F L w) := by
    rw [Algebra.biquadraticE2 F K L (Y * (V : K)),
      Algebra.biquadraticE2 F K L Y, hnormTrace, map_mul, coe_normUnits,
      mul_sub, mul_one, map_sub]
    dsimp only [H]
    ring
  rw [tracePullbackAddChar_apply, he2, ContinuousAddChar.map_add_eq_mul, herr, mul_one]

/-- **Paper Lemma 13.5 (`D:NM:compat`).**

For the actual aligned origin and the normalized lower characters of
`lowerCharacters`, construct all three group characters prescribed in
`D:NM:Rcharts`. Every common top unit `V = 1-v`, with `v ∈ 𝔭_K^(2r)`,
has its three actual norm endpoints in the indicated chart domains.
All three values equal `Ψ_F(-E₂(YV)+E₂(Y))`.

The upper breaks are exactly `D:NM:upper`, expressed as different minus
one. The input records have proved constructors in `Origin` and
`LowerCharacters`; no common phase or norm representative is assumed. -/
theorem compatibility
    (F K : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [Module.Finite F K] [IsGalois F K] [IsKleinFour Gal(K/F)]
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
    [PrimeCyclicExtension L₁ K] [PrimeCyclicExtension L₂ K] [PrimeCyclicExtension L₃ K]
    (a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r)
    (ht₁ : PrimeCyclicExtension.IsLowerBreak L₁ K (4 * r - 2 * a - 1))
    (ht₂ : PrimeCyclicExtension.IsLowerBreak L₂ K (2 * a - 1))
    (ht₃ : PrimeCyclicExtension.IsLowerBreak L₃ K (2 * a - 1))
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
    ∃ (R₁ : unitFiltration L₁ (2 * r) →* ℂˣ)
      (R₂ : unitFiltration L₂ (a + r) →* ℂˣ)
      (R₃ : unitFiltration L₃ (a + r) →* ℂˣ),
      (∀ u, R₁ u = tracePullbackAddChar F L₁ Ψ
        (norm L₁ K O.Y * (1 - ((u : L₁ˣ) : L₁)))) ∧
      (∀ u, R₂ u = tracePullbackAddChar F L₂ Ψ
        (norm L₂ K O.Y * (1 - ((u : L₂ˣ) : L₂)))) ∧
      (∀ u, R₃ u = tracePullbackAddChar F L₃ Ψ
        (norm L₃ K O.Y * (1 - ((u : L₃ˣ) : L₃)))) ∧
      ∀ (V : Kˣ), 1 - (V : K) ∈ lattice K (2 * (r : ℤ)) →
        ∃ (h₁ : normUnits L₁ K V ∈ unitFiltration L₁ (2 * r))
          (h₂ : normUnits L₂ K V ∈ unitFiltration L₂ (a + r))
          (h₃ : normUnits L₃ K V ∈ unitFiltration L₃ (a + r)),
          R₁ ⟨normUnits L₁ K V, h₁⟩ =
            Ψ (-elementarySymmetric F K 2 (O.Y * (V : K)) +
              elementarySymmetric F K 2 O.Y) ∧
          R₂ ⟨normUnits L₂ K V, h₂⟩ =
            Ψ (-elementarySymmetric F K 2 (O.Y * (V : K)) +
              elementarySymmetric F K 2 O.Y) ∧
          R₃ ⟨normUnits L₃ K V, h₃⟩ =
            Ψ (-elementarySymmetric F K 2 (O.Y * (V : K)) +
              elementarySymmetric F K 2 O.Y) := by
  let Ψ := (scaleAddCharData F ψ α).character
  let Ψ₁ : LocalAddCharData L₁ :=
    ⟨tracePullbackAddChar F L₁ Ψ, -(4 * (r : ℤ) - 2 * (a : ℤ)), D.first_conductor⟩
  let Ψ₂ : LocalAddCharData L₂ :=
    ⟨tracePullbackAddChar F L₂ Ψ, -2 * (r : ℤ), D.second_conductor⟩
  let Ψ₃ : LocalAddCharData L₃ :=
    ⟨tracePullbackAddChar F L₃ Ψ, -2 * (r : ℤ), D.third_conductor⟩
  obtain ⟨R₁, hR₁⟩ := exists_chart_of_order L₁ Ψ₁ (norm L₁ K O.Y)
    (1 - 2 * (a : ℤ)) O.upperNorm₁_order (2 * r) (4 * r - 1)
    (by omega) (by omega) (by omega) (by dsimp [Ψ₁]; omega)
  obtain ⟨R₂, hR₂⟩ := exists_chart_of_order L₂ Ψ₂ (norm L₂ K O.Y)
    (1 - 2 * (a : ℤ)) O.upperNorm₂_order (a + r) (2 * a + 2 * r - 1)
    (by omega) (by omega) (by omega) (by dsimp [Ψ₂]; omega)
  obtain ⟨R₃, hR₃⟩ := exists_chart_of_order L₃ Ψ₃ (norm L₃ K O.Y)
    (1 - 2 * (a : ℤ)) O.upperNorm₃_order (a + r) (2 * a + 2 * r - 1)
    (by omega) (by omega) (by omega) (by dsimp [Ψ₃]; omega)
  refine ⟨R₁, R₂, R₃, hR₁, hR₂, hR₃, ?_⟩
  intro V hV
  have hphase₁ : ∀ w ∈ lattice L₁ (a : ℤ),
      tracePullbackAddChar F L₁ Ψ
        (algebraMap F L₁ (norm F L₁ (trace L₁ K O.Y)) * w) =
      Ψ (norm F L₁ (trace L₁ K O.Y) * norm F L₁ w) := by
    simpa only [coe_normUnits, Units.val_mk0] using D.first_phase
  have hphase₂ : ∀ w ∈ lattice L₂ (r : ℤ),
      tracePullbackAddChar F L₂ Ψ
        (algebraMap F L₂ (norm F L₂ (trace L₂ K O.Y)) * w) =
      Ψ (norm F L₂ (trace L₂ K O.Y) * norm F L₂ w) := by
    simpa only [coe_normUnits, Units.val_mk0] using D.second_phase
  have hphase₃ : ∀ w ∈ lattice L₃ (r : ℤ),
      tracePullbackAddChar F L₃ Ψ
        (algebraMap F L₃ (norm F L₃ (trace L₃ K O.Y)) * w) =
      Ψ (norm F L₃ (trace L₃ K O.Y) * norm F L₃ w) := by
    simpa only [coe_normUnits, Units.val_mk0] using D.third_phase
  obtain ⟨h₁, hv₁⟩ := compatibility_edge F K L₁ _ ht₁ hres₁
    (2 * r) (by omega) (a : ℤ) (2 * (r : ℤ)) (1 - 2 * (a : ℤ))
    (2 * ((r : ℤ) - a)) (by omega) (by omega) (by omega)
    Ψ O.Y O.Y_order (by simpa only [Nat.cast_sub har] using O.upperTrace₁_order)
    hphase₁ V hV
  obtain ⟨h₂, hv₂⟩ := compatibility_edge F K L₂ _ ht₂ hres₂
    (a + r) (by omega) (r : ℤ) (2 * (r : ℤ)) (1 - 2 * (a : ℤ)) 0
    (by omega) (by omega) (by omega) Ψ O.Y O.Y_order O.upperTrace₂_order hphase₂ V hV
  obtain ⟨h₃, hv₃⟩ := compatibility_edge F K L₃ _ ht₃ hres₃
    (a + r) (by omega) (r : ℤ) (2 * (r : ℤ)) (1 - 2 * (a : ℤ)) 0
    (by omega) (by omega) (by omega) Ψ O.Y O.Y_order O.upperTrace₃_order hphase₃ V hV
  exact ⟨h₁, h₂, h₃, (hR₁ _).trans hv₁, (hR₂ _).trans hv₂, (hR₃ _).trans hv₃⟩

end
end LanglandsSecondMainLemma.Dyadic.Nonmaximal
