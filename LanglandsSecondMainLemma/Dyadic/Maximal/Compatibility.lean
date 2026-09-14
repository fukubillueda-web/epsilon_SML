import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Dyadic.Maximal.LowerCharacters
import LanglandsSecondMainLemma.Algebra.BiquadraticE2

/-!
# Dyadic / Maximal / Compatibility

The full unit-subgroup compatibility lemma `D:MX:Rcompat`.
-/

namespace LanglandsSecondMainLemma.Dyadic.Maximal

open LanglandsFirstMainLemma

noncomputable section

/-- The value prescribed by the stationary chart `R(1-x) = Psi(c*x)`,
written directly as a function of the unit. -/
noncomputable def corePhaseValue
    (E : Type) [Field E] [TopologicalSpace E] [IsTopologicalRing E]
    (Psi : ContinuousAddChar E) (c : E) (u : Eˣ) : ℂˣ :=
  Psi (c * (1 - (u : E)))

private theorem one_sub_mem_lattice_of_mem_unitFiltration
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (d : ℕ) (hd : 0 < d) (u : unitFiltration E d) :
    1 - ((u : Eˣ) : E) ∈ lattice E (d : ℤ) := by
  cases d with
  | zero => omega
  | succ n =>
      have hsub := (mem_unitFiltration_succ_iff_sub_mem_lattice E n
        (u : Eˣ)).1 u.property
      have hneg := neg_mem_lattice E hsub
      convert hneg using 1
      ring

/-- The genuine group character defined by a stationary chart once the
quadratic error term is known to lie in the additive character's kernel. -/
noncomputable def coreUnitCharacter
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (d : ℕ) (hd : 0 < d) (Psi : ContinuousAddChar E) (c : E)
    (herror : ∀ (x : E), x ∈ lattice E (d : ℤ) →
      ∀ (y : E), y ∈ lattice E (d : ℤ) → Psi (c * (x * y)) = 1) :
    unitFiltration E d →* ℂˣ where
  toFun u := corePhaseValue E Psi c (u : Eˣ)
  map_one' := by simp [corePhaseValue]
  map_mul' u v := by
    let x : E := 1 - (((u : unitFiltration E d) : Eˣ) : E)
    let y : E := 1 - (((v : unitFiltration E d) : Eˣ) : E)
    have hx : x ∈ lattice E (d : ℤ) :=
      one_sub_mem_lattice_of_mem_unitFiltration E d hd u
    have hy : y ∈ lattice E (d : ℤ) :=
      one_sub_mem_lattice_of_mem_unitFiltration E d hd v
    have herr := herror x hx y hy
    change Psi (c * (1 - ((((u * v : unitFiltration E d) : Eˣ) : E)))) =
      Psi (c * (1 - (((u : unitFiltration E d) : Eˣ) : E))) *
        Psi (c * (1 - (((v : unitFiltration E d) : Eˣ) : E)))
    have harg : c * (1 -
        ((((u * v : unitFiltration E d) : Eˣ) : E))) =
        c * x + c * y - c * (x * y) := by
      change c * (1 -
        ((((u : unitFiltration E d) : Eˣ) : E) *
          (((v : unitFiltration E d) : Eˣ) : E))) = _
      dsimp only [x, y]
      ring
    rw [harg]
    change Psi (c * x + c * y - c * (x * y)) =
      Psi (c * x) * Psi (c * y)
    calc
      Psi (c * x + c * y - c * (x * y)) =
          Psi (c * x + c * y) / Psi (c * (x * y)) :=
        Psi.toAddChar.map_sub_eq_div _ _
      _ = (Psi (c * x) * Psi (c * y)) / Psi (c * (x * y)) := by
        rw [ContinuousAddChar.map_add_eq_mul]
      _ = Psi (c * x) * Psi (c * y) := by rw [herr, div_one]

@[simp]
theorem coreUnitCharacter_apply
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (d : ℕ) (hd : 0 < d) (Psi : ContinuousAddChar E) (c : E)
    (herror : ∀ (x : E), x ∈ lattice E (d : ℤ) →
      ∀ (y : E), y ∈ lattice E (d : ℤ) → Psi (c * (x * y)) = 1)
    (u : unitFiltration E d) :
    coreUnitCharacter E d hd Psi c herror u =
      corePhaseValue E Psi c (u : Eˣ) := rfl

private theorem quadraticNormOneSub
    (E M : Type) [Field E] [Field M] [Algebra E M]
    [Module.Free E M] [Module.Finite E M]
    (hdegree : Module.finrank E M = 2) (z : M) :
    norm E M (1 - z) = 1 - trace E M z + norm E M z := by
  have h := norm_one_add_eq_one_add_sum_elementarySymmetric E M (-z)
  rw [hdegree] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h
  rw [elementarySymmetric_one] at h
  have hfin : elementarySymmetric E M 2 (-z) = norm E M (-z) := by
    rw [← hdegree]
    exact elementarySymmetric_finrank E M (-z)
  rw [hfin] at h
  have hnormneg : norm E M (-z) = norm E M z := by
    rw [show -z = algebraMap E M (-1 : E) * z by simp, map_mul,
      LanglandsFirstMainLemma.norm_algebraMap, hdegree]
    norm_num
  rw [map_neg, hnormneg] at h
  simpa only [sub_eq_add_neg, add_assoc] using h

private theorem trace_mem_lattice_at_break
    (E M : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    [Algebra E M] [ValuativeExtension E M]
    [Module.Free E M] [Module.Finite E M] [PrimeCyclicExtension E M]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak E M t)
    (hres : residueDegree E M = 1) (d : ℤ)
    (x : M) (hx : x ∈ lattice M d) :
    trace E M x ∈ lattice E
      ((d + ((((Module.finrank E M - 1) * (t + 1) : ℕ)) : ℤ)) /
        (Module.finrank E M : ℤ)) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer E M hres
  have hmap : trace E M x ∈
      Submodule.map ((trace E M).restrictScalars (ringOfIntegers E))
        ((lattice M d).restrictScalars (ringOfIntegers E)) := by
    exact ⟨x, hx, rfl⟩
  rw [cyclicPrime_trace_lattice_image_eq E M ht hres pi hpi hgen] at hmap
  exact hmap

/-- Total ramification descends to both edges of each intermediate tower. -/
private theorem intermediate_residueDegrees_eq_one
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
    letI : ValuativeExtension L K :=
      Basic.intermediateField_upperValuativeExtension L
    residueDegree F L = 1 ∧ residueDegree L K = 1 := by
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
  apply mul_eq_one.mp
  calc
    residueDegree F L * residueDegree L K = residueDegree F K := by
      rw [residueDegree_eq_finrank_residueField,
        residueDegree_eq_finrank_residueField,
        residueDegree_eq_finrank_residueField]
      exact Module.finrank_mul_finrank
        (ResidueField F) (ResidueField L) (ResidueField K)
    _ = 1 := hres

/-- The field-independent algebra at the end of `D:MX:Rcompat`.  The
lower phase kills the norm-of-trace error, leaving the same `E₂` difference
for every quadratic intermediate field. -/
private theorem corePhase_eq_e2Difference
    (F K : Type) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [Field K] [Algebra F K] [Module.Free F K] [Module.Finite F K]
    [IsGalois F K] [IsKleinFour Gal(K/F)]
    (L : IntermediateField F K)
    [TopologicalSpace L] [IsTopologicalRing L]
    [Module.Finite F L] [Module.Finite L K]
    [IsScalarTower F L K] [IsGalois F L] [IsGalois L K]
    [IsModuleTopology F L]
    [Algebra.IsQuadraticExtension F L]
    [Algebra.IsQuadraticExtension L K]
    (PsiF : ContinuousAddChar F)
    (Y V W : K) (a h : L) (beta : F) (u : Lˣ) (w : L)
    (hW : W = Y * V)
    (ha : a = norm L K Y)
    (hbeta : beta = norm F L h)
    (hu : (u : L) = norm L K V)
    (htraceW : trace L K W = h * (1 - w))
    (he2Y : elementarySymmetric F K 2 Y = trace F L a + beta)
    (hlowerPhase : tracePullbackAddChar F L PsiF
        (algebraMap F L beta * w) = PsiF (beta * norm F L w)) :
    corePhaseValue L (tracePullbackAddChar F L PsiF) a u =
      PsiF (-elementarySymmetric F K 2 W + elementarySymmetric F K 2 Y) := by
  have hnormW : norm L K W = a * (u : L) := by
    calc
      norm L K W = norm L K (Y * V) := congrArg (norm L K) hW
      _ = norm L K Y * norm L K V := map_mul (norm L K) Y V
      _ = a * (u : L) := by rw [ha, hu]
  have hnormTraceW : norm F L (trace L K W) =
      beta * (1 - trace F L w + norm F L w) := by
    calc
      norm F L (trace L K W) = norm F L (h * (1 - w)) :=
        congrArg (norm F L) htraceW
      _ = norm F L h * norm F L (1 - w) := map_mul (norm F L) h (1 - w)
      _ = beta * norm F L (1 - w) := by rw [hbeta]
      _ = beta * (1 - trace F L w + norm F L w) := by
        rw [quadraticNormOneSub F L
          (Algebra.IsQuadraticExtension.finrank_eq_two F L) w]
  have htraceBeta : trace F L (algebraMap F L beta * w) =
      beta * trace F L w := by
    simpa [Algebra.smul_def] using (trace F L).map_smul beta w
  have hlowerPhase' : PsiF (beta * trace F L w) =
      PsiF (beta * norm F L w) := by
    simpa only [tracePullbackAddChar_apply, htraceBeta] using hlowerPhase
  have herrorPhase :
      PsiF (beta * trace F L w - beta * norm F L w) = 1 := by
    calc
      PsiF (beta * trace F L w - beta * norm F L w) =
          PsiF (beta * trace F L w) / PsiF (beta * norm F L w) :=
        PsiF.toAddChar.map_sub_eq_div _ _
      _ = 1 := div_eq_one.mpr hlowerPhase'
  have htraceDifference :
      trace F L (a * (1 - (u : L))) =
        trace F L a - trace F L (a * (u : L)) := by
    rw [show a * (1 - (u : L)) = a - a * (u : L) by ring,
      map_sub]
  have he2W := LanglandsSecondMainLemma.Algebra.biquadraticE2 F K L W
  have hargument :
      -elementarySymmetric F K 2 W + elementarySymmetric F K 2 Y =
        trace F L (a * (1 - (u : L))) +
          (beta * trace F L w - beta * norm F L w) := by
    rw [he2W, he2Y, hnormW, hnormTraceW, htraceDifference]
    ring
  rw [corePhaseValue, tracePullbackAddChar_apply, hargument,
    ContinuousAddChar.map_add_eq_mul, herrorPhase, mul_one]

section QuadraticDepth

variable (E M : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M]
  [Algebra E M] [ValuativeExtension E M]
  [Module.Free E M] [Module.Finite E M] [PrimeCyclicExtension E M]

/-- The quadratic trace bound, with the desired target depth kept integral. -/
private theorem quadratic_trace_mem_lattice
    (hdegree : Module.finrank E M = 2)
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak E M t)
    (hres : residueDegree E M = 1) {r q : ℤ}
    (hdepth : q ≤ (r + (t : ℤ) + 1) / 2)
    (x : M) (hx : x ∈ lattice M r) :
    trace E M x ∈ lattice E q := by
  apply lattice_antitone E hdepth
  have htrace := trace_mem_lattice_at_break E M ht hres r x hx
  simpa only [hdegree, Nat.reduceSub, one_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat, add_assoc] using htrace

/-- A normalized norm-character formula gives the additive triviality used
to kill all three stationary quadratic errors. -/
private theorem addCharTrivialOnLattice_of_normCharacter_formula
    {t q : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak E M t)
    (hres : residueDegree E M = 1)
    (tau : NormCharacter E M) (htau : tau ≠ 1)
    (Psi : ContinuousAddChar E) (hq : 0 < q) (hqt : q ≤ t + 1)
    (hformula : ∀ (x : E) (hx : x ∈ lattice E (q : ℤ)),
      tau.1 (lowerOneSubUnit E q hq x hx) = Psi x) :
    AddCharTrivialOnLattice E Psi ((t + 1 : ℕ) : ℤ) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer E M hres
  have hconductor :=
    ramifiedNormCharacter_conductor E M ht hres pi hpi hgen tau htau
  intro x hx
  have hxq : x ∈ lattice E (q : ℤ) :=
    lattice_antitone E (by exact_mod_cast hqt) hx
  rw [← hformula x hxq]
  apply hconductor.trivial
  rw [mem_unitFiltration_succ_iff_sub_mem_lattice E t, coe_lowerOneSubUnit]
  convert neg_mem_lattice E hx using 1
  ring

/-- The trace of the quadratic error lies in the base character's kernel,
so the stationary chart defines a group homomorphism. -/
private theorem exists_coreUnitCharacter_of_trace_bound
    (hdegree : Module.finrank E M = 2)
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak E M t)
    (hres : residueDegree E M = 1)
    (Psi : ContinuousAddChar E) {n r : ℤ}
    (hPsi : AddCharTrivialOnLattice E Psi n)
    (c : M) (hc : ord M c = (r : WithTop ℤ))
    (d : ℕ) (hd : 0 < d)
    (hdepth : n ≤ (r + (d : ℤ) + (d : ℤ) + (t : ℤ) + 1) / 2) :
    ∃ R : unitFiltration M d →* ℂˣ,
      ∀ u, R u = corePhaseValue M (tracePullbackAddChar E M Psi) c (u : Mˣ) := by
  have hcMem : c ∈ lattice M r := by rw [mem_lattice, hc]
  have herror (x : M) (hx : x ∈ lattice M (d : ℤ))
      (y : M) (hy : y ∈ lattice M (d : ℤ)) :
      tracePullbackAddChar E M Psi (c * (x * y)) = 1 := by
    rw [tracePullbackAddChar_apply]
    apply hPsi
    apply quadratic_trace_mem_lattice E M hdegree ht hres hdepth
    simpa only [mul_assoc] using mul_mem_lattice M (mul_mem_lattice M hcMem hx) hy
  exact ⟨coreUnitCharacter M d hd (tracePullbackAddChar E M Psi) c herror,
    fun _ => rfl⟩

/-- The exact quadratic norm identity transports a principal unit to the
required unit subgroup once both the trace and norm have enough depth. -/
private theorem normOneSub_mem_unitFiltration
    (hdegree : Module.finrank E M = 2)
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak E M t)
    (hres : residueDegree E M = 1)
    {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n)
    (hdepth : (d : ℤ) ≤ ((n : ℤ) + (t : ℤ) + 1) / 2)
    (z : M) (hz : z ∈ lattice M (n : ℤ)) :
    normUnits E M (lowerOneSubUnit M n hn z hz) ∈ unitFiltration E d := by
  have hnorm : norm E M z ∈ lattice E (n : ℤ) := by
    rw [mem_lattice, ord_norm, hres, one_nsmul]
    exact (mem_lattice M).1 hz
  have htrace := quadratic_trace_mem_lattice E M hdegree ht hres hdepth z hz
  have hdisp := sub_mem_lattice E
    (lattice_antitone E (by exact_mod_cast hdn) hnorm) htrace
  cases d with
  | zero => omega
  | succ d =>
      rw [mem_unitFiltration_succ_iff_sub_mem_lattice E d]
      convert hdisp using 1
      simp only [coe_normUnits, coe_lowerOneSubUnit]
      rw [quadraticNormOneSub E M hdegree z]
      ring

/-- The normalized trace `Tr(Yz)/h` belongs to the whole lower-phase
ideal.  Both the origin order and the denominator order remain integers. -/
private theorem trace_mul_div_mem_lattice
    (hdegree : Module.finrank E M = 2)
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak E M t)
    (hres : residueDegree E M = 1)
    (Y : M) (h : E) {r k n q : ℤ}
    (hY : ord M Y = (r : WithTop ℤ)) (hh : ord E h = (k : WithTop ℤ))
    (hdepth : k + q ≤ (r + n + (t : ℤ) + 1) / 2)
    (z : M) (hz : z ∈ lattice M n) :
    trace E M (Y * z) / h ∈ lattice E q := by
  apply (div_mem_lattice_iff E h (trace E M (Y * z)) k q hh).2
  apply quadratic_trace_mem_lattice E M hdegree ht hres hdepth
  exact mul_mem_lattice M (by rw [mem_lattice, hY]) hz

end QuadraticDepth

/-- Specialize the field-independent `E₂` calculation to the actual norm
endpoint and normalized trace of `Y(1-z)`. -/
private theorem corePhase_normOneSub_eq_e2Difference
    (F K : Type) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [Module.Free F K] [Module.Finite F K]
    [IsGalois F K] [IsKleinFour Gal(K/F)]
    (L : IntermediateField F K)
    [TopologicalSpace L] [IsTopologicalRing L]
    [Module.Finite F L] [Module.Finite L K]
    [IsScalarTower F L K] [IsGalois F L] [IsGalois L K]
    [IsModuleTopology F L]
    [Algebra.IsQuadraticExtension F L] [Algebra.IsQuadraticExtension L K]
    (Psi : ContinuousAddChar F) (Y : K) (c h : L) (beta : F)
    (hc : c = norm L K Y) (hh : h = trace L K Y) (hh0 : h ≠ 0)
    (hbeta : beta = norm F L h)
    (he2 : elementarySymmetric F K 2 Y = trace F L c + beta)
    {n : ℕ} (hn : 0 < n) (z : K) (hz : z ∈ lattice K (n : ℤ))
    (hphase : tracePullbackAddChar F L Psi
        (algebraMap F L beta * (trace L K (Y * z) / h)) =
      Psi (beta * norm F L (trace L K (Y * z) / h))) :
    corePhaseValue L (tracePullbackAddChar F L Psi) c
        (normUnits L K (lowerOneSubUnit K n hn z hz)) =
      Psi (-elementarySymmetric F K 2 (Y * (1 - z)) +
        elementarySymmetric F K 2 Y) := by
  apply corePhase_eq_e2Difference F K L Psi Y (1 - z) (Y * (1 - z))
    c h beta _ (trace L K (Y * z) / h) rfl hc hbeta
    (by simp only [coe_normUnits, coe_lowerOneSubUnit]) _ he2 hphase
  rw [show Y * (1 - z) = Y - Y * z by ring, map_sub, ← hh]
  field_simp [hh0]

/-- Recognize the actual Galois group as a Klein four group for the `E₂`
identity. -/
private theorem isKleinFour_of_galoisEquiv
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))) :
    IsKleinFour Gal(K/F) := by
  let iso := Classical.choice hG
  constructor
  · rw [Nat.card_congr iso.toEquiv, Nat.card_prod]
    norm_num
  · rw [Monoid.exponent_eq_of_mulEquiv iso, Monoid.exponent_prod]
    norm_num

/-- The degree and cyclicity facts used locally by the compatibility proof. -/
private structure QuadraticTowerData
    (F K : Type) [Field F] [Field K] [Algebra F K] [Module.Finite F K]
    (L : IntermediateField F K) : Prop where
  lowerDegree : Module.finrank F L = 2
  upperDegree : Module.finrank L K = 2
  primeCyclicLower : PrimeCyclicExtension F L
  primeCyclicUpper : PrimeCyclicExtension L K

/-- Extract the local package from the genuine compatible intermediate tower. -/
private theorem intermediateQuadraticTowerData
    {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (L : IntermediateField F K) (hL : Module.finrank F L = 2) :
    QuadraticTowerData F K L := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hLower, hUpper, hCyclicLower, hCyclicUpper⟩ :=
    Basic.intermediateField_tower_compatible Nat.prime_two hG L hL
  exact ⟨hLower, hUpper,
    PrimeCyclicExtension.ofCyclicPrimeExtension F L hCyclicLower,
    PrimeCyclicExtension.ofCyclicPrimeExtension L K hCyclicUpper⟩

set_option maxHeartbeats 800000 in
/-- **Compatibility before extension (`D:MX:Rcompat`).**

The three stationary formulas are genuine group homomorphisms on exactly
the paper's unit subgroups.  For every `z` of top-field depth `2e+1`, its
three actual norm endpoints lie in those domains, and all three character
values equal the same `E₂` phase. -/
theorem compatibility
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
    letI : Module.Free D.firstField K := E₁.2.2.2.1
    letI : Module.Finite D.firstField K := E₁.2.2.2.2.1
    letI : IsScalarTower F D.firstField K := E₁.2.2.2.2.2.1
    letI : ValuativeExtension F D.firstField := E₁.2.2.2.2.2.2.1
    letI : ValuativeExtension D.firstField K := E₁.2.2.2.2.2.2.2.1
    letI : CyclicPrimeExtension F D.firstField :=
      E₁.2.2.2.2.2.2.2.2.2.2.2.1
    letI : CyclicPrimeExtension D.firstField K :=
      E₁.2.2.2.2.2.2.2.2.2.2.2.2
    letI : IsNonarchimedeanLocalField D.secondField := E₂.1
    letI : Module.Free F D.secondField := E₂.2.1
    letI : Module.Finite F D.secondField := E₂.2.2.1
    letI : Module.Free D.secondField K := E₂.2.2.2.1
    letI : Module.Finite D.secondField K := E₂.2.2.2.2.1
    letI : IsScalarTower F D.secondField K := E₂.2.2.2.2.2.1
    letI : ValuativeExtension F D.secondField := E₂.2.2.2.2.2.2.1
    letI : ValuativeExtension D.secondField K := E₂.2.2.2.2.2.2.2.1
    letI : CyclicPrimeExtension F D.secondField :=
      E₂.2.2.2.2.2.2.2.2.2.2.2.1
    letI : CyclicPrimeExtension D.secondField K :=
      E₂.2.2.2.2.2.2.2.2.2.2.2.2
    letI : IsNonarchimedeanLocalField D.thirdField := E₃.1
    letI : Module.Free F D.thirdField := E₃.2.1
    letI : Module.Finite F D.thirdField := E₃.2.2.1
    letI : Module.Free D.thirdField K := E₃.2.2.2.1
    letI : Module.Finite D.thirdField K := E₃.2.2.2.2.1
    letI : IsScalarTower F D.thirdField K := E₃.2.2.2.2.2.1
    letI : ValuativeExtension F D.thirdField := E₃.2.2.2.2.2.2.1
    letI : ValuativeExtension D.thirdField K := E₃.2.2.2.2.2.2.2.1
    letI : CyclicPrimeExtension F D.thirdField :=
      E₃.2.2.2.2.2.2.2.2.2.2.2.1
    letI : CyclicPrimeExtension D.thirdField K :=
      E₃.2.2.2.2.2.2.2.2.2.2.2.2
    ∀ (_htLower₁ : PrimeCyclicExtension.IsLowerBreak F D.firstField
        (2 * a - 1))
      (_htLower₂ : PrimeCyclicExtension.IsLowerBreak F D.secondField (2 * e))
      (_htLower₃ : PrimeCyclicExtension.IsLowerBreak F D.thirdField (2 * e))
      (_ht₁ : PrimeCyclicExtension.IsLowerBreak D.firstField K
        (4 * e - 2 * a + 1))
      (_ht₂ : PrimeCyclicExtension.IsLowerBreak D.secondField K (2 * a - 1))
      (_ht₃ : PrimeCyclicExtension.IsLowerBreak D.thirdField K (2 * a - 1))
      (tau₁ : NormCharacter F D.firstField)
      (tau₂ : NormCharacter F D.secondField)
      (tau₃ : NormCharacter F D.thirdField)
      (_htau₃ : tau₃ ≠ 1)
      (PsiF : ContinuousAddChar F)
      (_H : LowerCharacterData F D.firstField D.secondField D.thirdField
        a e ha tau₁ tau₂ tau₃ PsiF
        D.beta1 D.beta2 D.beta3 D.h1 D.h2 D.h3),
      ∃ (R₁ : unitFiltration D.firstField (2 * e + 1) →* ℂˣ)
        (R₂ : unitFiltration D.secondField (e + a) →* ℂˣ)
        (R₃ : unitFiltration D.thirdField (e + a) →* ℂˣ),
        (∀ u, R₁ u = corePhaseValue D.firstField
          (tracePullbackAddChar F D.firstField PsiF) D.a1 (u : D.firstFieldˣ)) ∧
        (∀ u, R₂ u = corePhaseValue D.secondField
          (tracePullbackAddChar F D.secondField PsiF) D.a2 (u : D.secondFieldˣ)) ∧
        (∀ u, R₃ u = corePhaseValue D.thirdField
          (tracePullbackAddChar F D.thirdField PsiF) D.a3 (u : D.thirdFieldˣ)) ∧
        ∀ (z : K) (hz : z ∈ lattice K (((2 * e + 1 : ℕ) : ℤ))),
          let uK := lowerOneSubUnit K (2 * e + 1) (by omega) z hz
          let u₁ := normUnits D.firstField K uK
          let u₂ := normUnits D.secondField K uK
          let u₃ := normUnits D.thirdField K uK
          let common := PsiF
            (-elementarySymmetric F K 2 (D.origin * (1 - z)) +
              elementarySymmetric F K 2 D.origin)
          ∃ (hu₁ : u₁ ∈ unitFiltration D.firstField (2 * e + 1))
            (hu₂ : u₂ ∈ unitFiltration D.secondField (e + a))
            (hu₃ : u₃ ∈ unitFiltration D.thirdField (e + a)),
            R₁ ⟨u₁, hu₁⟩ = common ∧
              R₂ ⟨u₂, hu₂⟩ = common ∧ R₃ ⟨u₃, hu₃⟩ = common := by
  dsimp only
  letI (L : IntermediateField F K) : ValuativeRel L :=
    Basic.intermediateFieldValuativeRel L
  letI (L : IntermediateField F K) : TopologicalSpace L :=
    Basic.intermediateFieldTopology L
  letI (L : IntermediateField F K) : IsNonarchimedeanLocalField L :=
    Basic.intermediateField_localField L
  letI (L : IntermediateField F K) : ValuativeExtension F L :=
    Basic.intermediateField_lowerValuativeExtension L
  letI (L : IntermediateField F K) : ValuativeExtension L K :=
    Basic.intermediateField_upperValuativeExtension L
  let E₁ := intermediateQuadraticTowerData hG D.firstField O.first_degree
  let E₂ := intermediateQuadraticTowerData hG D.secondField O.second_degree
  let E₃ := intermediateQuadraticTowerData hG D.thirdField O.third_degree
  letI := E₁.primeCyclicLower
  letI := E₁.primeCyclicUpper
  letI := E₂.primeCyclicLower
  letI := E₂.primeCyclicUpper
  letI := E₃.primeCyclicLower
  letI := E₃.primeCyclicUpper
  letI : Algebra.IsQuadraticExtension F D.firstField := ⟨E₁.lowerDegree⟩
  letI : Algebra.IsQuadraticExtension D.firstField K := ⟨E₁.upperDegree⟩
  letI : Algebra.IsQuadraticExtension F D.secondField := ⟨E₂.lowerDegree⟩
  letI : Algebra.IsQuadraticExtension D.secondField K := ⟨E₂.upperDegree⟩
  letI : Algebra.IsQuadraticExtension F D.thirdField := ⟨E₃.lowerDegree⟩
  letI : Algebra.IsQuadraticExtension D.thirdField K := ⟨E₃.upperDegree⟩
  letI : IsKleinFour Gal(K/F) := isKleinFour_of_galoisEquiv hG
  intro htLower₁ htLower₂ htLower₃ ht₁ ht₂ ht₃
    tau₁ tau₂ tau₃ htau₃ PsiF H
  obtain ⟨hresF₁, hres₁⟩ := intermediate_residueDegrees_eq_one D.firstField hres
  obtain ⟨hresF₂, hres₂⟩ := intermediate_residueDegrees_eq_one D.secondField hres
  obtain ⟨hresF₃, hres₃⟩ := intermediate_residueDegrees_eq_one D.thirdField hres

  have hPsiTrivial : AddCharTrivialOnLattice F PsiF ((2 * e + 1 : ℕ) : ℤ) :=
    addCharTrivialOnLattice_of_normCharacter_formula F D.thirdField
      htLower₃ hresF₃ tau₃ htau₃ PsiF (q := e + 1) (by omega) (by omega)
      (fun x hx => by simpa only [O.beta3_table, one_mul] using H.third_formula x hx)
  obtain ⟨R₁, hR₁⟩ := exists_coreUnitCharacter_of_trace_bound F D.firstField
    E₁.lowerDegree htLower₁ hresF₁ PsiF hPsiTrivial D.a1 O.a1_order
    (2 * e + 1) (by omega) (by push_cast; omega)
  obtain ⟨R₂, hR₂⟩ := exists_coreUnitCharacter_of_trace_bound F D.secondField
    E₂.lowerDegree htLower₂ hresF₂ PsiF hPsiTrivial D.a2 O.a2_order
    (e + a) (by omega) (by push_cast; omega)
  obtain ⟨R₃, hR₃⟩ := exists_coreUnitCharacter_of_trace_bound F D.thirdField
    E₃.lowerDegree htLower₃ hresF₃ PsiF hPsiTrivial D.a3 O.a3_order
    (e + a) (by omega) (by push_cast; omega)
  refine ⟨R₁, R₂, R₃, hR₁, hR₂, hR₃, ?_⟩
  intro z hz

  have hu₁ := normOneSub_mem_unitFiltration D.firstField K E₁.upperDegree ht₁ hres₁
    (d := 2 * e + 1) (by omega) (by omega) (by omega) (by push_cast; omega) z hz
  have hu₂ := normOneSub_mem_unitFiltration D.secondField K E₂.upperDegree ht₂ hres₂
    (d := e + a) (by omega) (by omega) (by omega) (by push_cast; omega) z hz
  have hu₃ := normOneSub_mem_unitFiltration D.thirdField K E₃.upperDegree ht₃ hres₃
    (d := e + a) (by omega) (by omega) (by omega) (by push_cast; omega) z hz
  have hw₁deep : trace D.firstField K (D.origin * z) / D.h1 ∈
      lattice D.firstField ((e + 1 : ℕ) : ℤ) :=
    trace_mul_div_mem_lattice D.firstField K E₁.upperDegree ht₁ hres₁
      D.origin D.h1 O.origin_order (k := b) (by simpa [intermediateOrder] using O.h1_order)
      (by push_cast [hb, Nat.cast_sub (Nat.mul_le_mul_left 2 hae)]; omega) z hz
  have hw₂ : trace D.secondField K (D.origin * z) / D.h2 ∈
      lattice D.secondField ((e + 1 : ℕ) : ℤ) :=
    trace_mul_div_mem_lattice D.secondField K E₂.upperDegree ht₂ hres₂
      D.origin D.h2 O.origin_order (k := 0) O.h2_order (by push_cast; omega) z hz
  have hw₃ : trace D.thirdField K (D.origin * z) / D.h3 ∈
      lattice D.thirdField ((e + 1 : ℕ) : ℤ) :=
    trace_mul_div_mem_lattice D.thirdField K E₃.upperDegree ht₃ hres₃
      D.origin D.h3 O.origin_order (k := 0) O.h3_order (by push_cast; omega) z hz
  have hw₁ : trace D.firstField K (D.origin * z) / D.h1 ∈
      lattice D.firstField (a : ℤ) :=
    lattice_antitone D.firstField (by exact_mod_cast (show a ≤ e + 1 by omega)) hw₁deep
  refine ⟨hu₁, hu₂, hu₃, ?_, ?_, ?_⟩
  · rw [hR₁]
    exact corePhase_normOneSub_eq_e2Difference F K D.firstField PsiF
      D.origin D.a1 D.h1 D.beta1 rfl rfl O.h1_ne_zero H.first_beta_norm O.e2_first
      (by omega) z hz (H.first_phase _ hw₁)
  · rw [hR₂]
    exact corePhase_normOneSub_eq_e2Difference F K D.secondField PsiF
      D.origin D.a2 D.h2 D.beta2 rfl rfl O.h2_ne_zero H.second_beta_norm O.e2_second
      (by omega) z hz (H.second_phase _ hw₂)
  · rw [hR₃]
    exact corePhase_normOneSub_eq_e2Difference F K D.thirdField PsiF
      D.origin D.a3 D.h3 D.beta3 rfl rfl O.h3_ne_zero H.third_beta_norm O.e2_third
      (by omega) z hz (H.third_phase _ hw₃)

end

end LanglandsSecondMainLemma.Dyadic.Maximal
