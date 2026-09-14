import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.Delta.ResidueFormula
import LanglandsSecondMainLemma.Dyadic.UR.Twist
import LanglandsSecondMainLemma.Dyadic.UR.NormPhase

/-!
# The exact dyadic last-layer sign

Paper Lemma `D:UR:traceparity`, including `D:UR:traceparitynorm` and
`D:UR:paritysign`. Write `T = t + 1`, `A = N_{E/F}(x)`, and
`b = Tr_{E/F}(x)`, where `ord_E(x) = -h` and `1 ≤ h ≤ t`.

The trace estimate uses integer fractional-ideal depths. For the exact
odd-parity estimate we apply FML's nonnegative-depth quadratic trace
shell theorem to `x/A`, of order `h`, and scale back. The last-layer
character is identified from an actual quadratic norm, followed by
FML's uniqueness theorem for the Artin--Schreier annihilator.
-/

namespace LanglandsSecondMainLemma.Dyadic.UR

noncomputable section

open LanglandsFirstMainLemma

/-- The genuine norm identity `D:UR:traceparitynorm`, with no assumption
on the characteristic and no choice of norm representative. -/
private theorem traceParity_norm
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Module.Free F E] [Module.Finite F E]
    (hdegree : Module.finrank F E = 2)
    (x : E) (hA : norm F E x ≠ 0) (z : F) :
    norm F E (1 + algebraMap F E (trace F E x / norm F E x * z) * x) =
      1 + trace F E x ^ 2 / norm F E x * (z + z ^ 2) := by
  let a : F := trace F E x / norm F E x * z
  let y : E := algebraMap F E a * x
  have hexp := norm_one_add_eq_one_add_sum_elementarySymmetric F E y
  rw [hdegree] at hexp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd, elementarySymmetric_one] at hexp
  have hlast : elementarySymmetric F E 2 y = norm F E y := by
    rw [← hdegree]
    exact elementarySymmetric_finrank F E y
  rw [hlast] at hexp
  have htrace : trace F E y = a * trace F E x := by
    simpa [y, Algebra.smul_def] using
      (trace F E).map_smul a x
  have hnorm : norm F E y = a ^ 2 * norm F E x := by
    simp only [y, map_mul, LanglandsFirstMainLemma.norm_algebraMap, hdegree]
  change norm F E (1 + y) = _
  rw [hexp, htrace, hnorm]
  dsimp only [a]
  field_simp [hA]

section Valuations

variable (F E : Type*)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E]
  [Module.Free F E] [Module.Finite F E] [PrimeCyclicExtension F E]

/-- Trace has depth at least `⌊(T-h)/2⌋`, and exactly this depth when
`T-h` is odd. Normalization by the actual norm preserves negative depths. -/
private theorem traceParity_trace
    {t h : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hdegree : Module.finrank F E = 2)
    (x : E) (hx : ord E x = ((-(h : ℤ)) : WithTop ℤ)) :
    let B : ℤ := ((t + 1 : ℤ) - (h : ℤ)) / 2
    trace F E x ∈ lattice F B ∧
      (((t + 1 : ℤ) - (h : ℤ)) % 2 = 1 →
        ord F (trace F E x) = (B : WithTop ℤ)) := by
  let B : ℤ := ((t + 1 : ℤ) - (h : ℤ)) / 2
  change trace F E x ∈ lattice F B ∧
    (((t + 1 : ℤ) - (h : ℤ)) % 2 = 1 →
      ord F (trace F E x) = (B : WithTop ℤ))
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have hxmem : x ∈ lattice E (-(h : ℤ)) := by
    rw [mem_lattice, hx]
    norm_num
  have hb : trace F E x ∈ lattice F B := by
    have hmap : trace F E x ∈
        Submodule.map ((trace F E).restrictScalars (ringOfIntegers F))
          ((lattice E (-(h : ℤ))).restrictScalars (ringOfIntegers F)) :=
      Submodule.mem_map.mpr ⟨x, hxmem, rfl⟩
    rw [cyclicPrime_trace_lattice_image_eq F E ht hres pi hpi hgen,
      hdegree] at hmap
    simpa [B, sub_eq_add_neg, add_comm] using hmap
  refine ⟨hb, ?_⟩
  intro hodd
  have hram : ramificationIndex F E = 2 := by
    have hf := finrank_eq_ramificationIndex_mul_residueDegree F E
    rw [hdegree, hres, mul_one] at hf
    exact hf.symm
  have hD : differentExponent F E = t + 1 := by
    rw [cyclicPrime_differentExponent_eq F E ht hres pi hpi hgen, hdegree]
    omega
  have hAord : ord F (norm F E x) = ((-(h : ℤ)) : WithTop ℤ) := by
    rw [ord_norm, hres, one_nsmul, hx]
  have hA : norm F E x ≠ 0 := by
    intro hz
    rw [hz, ord_zero] at hAord
    exact WithTop.top_ne_coe hAord
  let y : E := algebraMap F E (norm F E x)⁻¹ * x
  have hy : ord E y = ((h : ℤ) : WithTop ℤ) := by
    dsimp only [y]
    rw [ord_mul, ord_algebraMap, hram, ord_inv, hAord, hx]
    norm_cast
    simp only [nsmul_eq_mul, neg_neg]
    omega
  have hymem : y ∈ lattice E (h : ℤ) := by
    rw [mem_lattice, hy]
  have hshift : (h : ℤ) + (differentExponent F E : ℤ) =
      2 * (B + (h : ℤ)) + 1 := by
    rw [hD]
    dsimp only [B]
    omega
  have hty : ord F (trace F E y) = ((B + (h : ℤ)) : WithTop ℤ) :=
    (quadratic_trace_shell_iff F E pi hpi hgen
      (by omega) hram hdegree hshift y hymem).2 hy
  have htrace : trace F E y = (norm F E x)⁻¹ * trace F E x := by
    simpa [y, Algebra.smul_def] using
      (trace F E).map_smul (norm F E x)⁻¹ x
  have hrecover : trace F E x = norm F E x * trace F E y := by
    rw [htrace, ← mul_assoc, mul_inv_cancel₀ hA, one_mul]
  rw [hrecover, ord_mul, hAord, hty]
  norm_cast
  omega

/-- The parity-dependent order of `b²/A`, together with the positive
depth of the coefficient in the genuine norm identity. The even case
allows `b = 0` and therefore infinite order. -/
private theorem traceParity_depths
    {t h : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hdegree : Module.finrank F E = 2)
    (x : E) (hx : ord E x = ((-(h : ℤ)) : WithTop ℤ)) :
    ((((t + 1 : ℤ) - (h : ℤ)) % 2 = 0) →
      trace F E x ^ 2 / norm F E x ∈ lattice F (t + 1 : ℤ)) ∧
    ((((t + 1 : ℤ) - (h : ℤ)) % 2 = 1) →
      ord F (trace F E x ^ 2 / norm F E x) = ((t : ℤ) : WithTop ℤ) ∧
      ord E (algebraMap F E (trace F E x / norm F E x) * x) =
        ((t : ℤ) : WithTop ℤ)) := by
  let B : ℤ := ((t + 1 : ℤ) - (h : ℤ)) / 2
  obtain ⟨hb, hbexact⟩ := traceParity_trace F E ht hres hdegree x hx
  have hAord : ord F (norm F E x) = ((-(h : ℤ)) : WithTop ℤ) := by
    rw [ord_norm, hres, one_nsmul, hx]
  constructor
  · intro heven
    apply (div_mem_lattice_iff F (norm F E x) (trace F E x ^ 2)
      (-(h : ℤ)) (t + 1 : ℤ) hAord).2
    have hdepth : B + B = -(h : ℤ) + (t + 1 : ℤ) := by
      dsimp only [B]
      omega
    rw [← hdepth]
    simpa only [pow_two] using mul_mem_lattice F hb hb
  · intro hodd
    have hbord : ord F (trace F E x) = (B : WithTop ℤ) := hbexact hodd
    have hdepth : 2 * B + (h : ℤ) = (t : ℤ) := by
      dsimp only [B]
      omega
    have hram : ramificationIndex F E = 2 := by
      have hf := finrank_eq_ramificationIndex_mul_residueDegree F E
      rw [hdegree, hres, mul_one] at hf
      exact hf.symm
    constructor
    · rw [ord_div, ord_pow, hbord, hAord]
      norm_cast
      simp only [nsmul_eq_mul]
      omega
    · rw [ord_mul, ord_algebraMap, hram, ord_div, hbord, hAord, hx]
      norm_cast
      simp only [nsmul_eq_mul]
      omega

omit [PrimeCyclicExtension F E] in
/-- Evaluate the chart only at the norm of the explicitly constructed
unit `1 + (b/A)xz`. It kills every integral Artin--Schreier value. -/
private theorem traceParity_artinSchreier
    {t : ℕ} (htpos : 0 < t) (hdegree : Module.finrank F E = 2)
    (tau : NormCharacter F E) (PsiF : ContinuousAddChar F)
    (hchart : ∀ (a : F) (ha : a ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
      tau.1 (principalUnitOf F (t / 2) (-a) (neg_mem_lattice F ha)) = PsiF a)
    (x : E) (hA : norm F E x ≠ 0)
    (hu : trace F E x ^ 2 / norm F E x ∈ lattice F (t : ℤ))
    (hw : algebraMap F E (trace F E x / norm F E x) * x ∈ lattice E (t : ℤ))
    (z : F) (hz : z ∈ lattice F 0) :
    PsiF (trace F E x ^ 2 / norm F E x * (z + z ^ 2)) = 1 := by
  let u : F := trace F E x ^ 2 / norm F E x
  let w : E := algebraMap F E (trace F E x / norm F E x * z) * x
  have hzE : algebraMap F E z ∈ lattice E 0 := by
    rw [mem_lattice, ord_algebraMap]
    rw [mem_lattice] at hz
    simpa using nsmul_le_nsmul_right hz (ramificationIndex F E)
  have hwmem : w ∈ lattice E (t : ℤ) := by
    have heq : w = (algebraMap F E (trace F E x / norm F E x) * x) *
        algebraMap F E z := by
      dsimp only [w]
      rw [map_mul]
      ring
    rw [heq]
    simpa only [add_zero] using mul_mem_lattice E hw hzE
  let v : Eˣ := principalUnitOf E (t - 1) w (by
    simpa only [Nat.sub_add_cancel htpos] using hwmem)
  have hAS : z + z ^ 2 ∈ lattice F 0 := by
    apply add_mem_lattice F hz
    simpa only [pow_two, zero_add] using mul_mem_lattice F hz hz
  let a : F := -(u * (z + z ^ 2))
  have ha : a ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ) := by
    apply lattice_antitone F (show ((t / 2 + 1 : ℕ) : ℤ) ≤ (t : ℤ) by omega)
    exact neg_mem_lattice F (by simpa only [add_zero] using mul_mem_lattice F hu hAS)
  have hnorm : normUnits F E v =
      principalUnitOf F (t / 2) (-a) (neg_mem_lattice F ha) := by
    apply Units.ext
    simp only [coe_normUnits, v, coe_principalUnitOf]
    rw [traceParity_norm F E hdegree x hA z]
    simp only [a, u, neg_neg]
  have hphaseNeg : PsiF a = 1 := by
    rw [← hchart a ha, ← hnorm]
    exact tau.eq_one_on_normRange F E _ ⟨v, rfl⟩
  have hadd := PsiF.toAddChar.map_add_eq_mul (u * (z + z ^ 2)) a
  have hsum : u * (z + z ^ 2) + a = 0 := add_neg_cancel _
  change PsiF.toAddChar a = 1 at hphaseNeg
  rw [hsum, PsiF.toAddChar.map_zero_eq_one, hphaseNeg, mul_one] at hadd
  exact hadd.symm

end Valuations

/-- FML's canonical residual character identifies the phase on every
integral lift, using exact whole-ideal conductor data for nontriviality. -/
private theorem traceParity_residual
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (hchar : residueCharacteristic F = 2)
    (t : ℕ) (PsiF : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F PsiF (-((t + 1 : ℕ) : ℤ)))
    (u : F) (hu : ord F u = ((t : ℤ) : WithTop ℤ))
    (hAS : ∀ (z : F) (_hz : z ∈ lattice F 0), PsiF (u * (z + z ^ 2)) = 1) :
    ∀ (z : F) (hz : z ∈ lattice F 0),
      (PsiF (u * z) : ℂ) =
        (@absoluteTraceChar (ResidueField F) _ (ringChar.of_eq hchar))
          (reduce F z hz) := by
  letI : CharP (ResidueField F) 2 := ringChar.of_eq hchar
  letI : Fintype (ResidueField F) := residueFieldFintype F
  have hu0 : u ≠ 0 := by
    intro hz
    rw [hz, ord_zero] at hu
    exact WithTop.top_ne_coe hu
  let psiData : LocalAddCharData F :=
    continuousAddChar_toData F PsiF (-((t + 1 : ℕ) : ℤ)) hPsi
  let gamma : Fˣ := (Units.mk0 u hu0)⁻¹
  have hgamma : ord F (gamma : F) =
      ((psiData.conductor + 1 : ℤ) : WithTop ℤ) := by
    simp only [gamma, Units.val_inv_eq_inv_val, Units.val_mk0, ord_inv,
      psiData, continuousAddChar_toData_conductor, hu]
    norm_cast
    omega
  let phi : FiniteAddChar (ResidueField F) := residualAddChar F psiData gamma hgamma
  have hlift (z : F) (hz : z ∈ lattice F 0) :
      phi (reduce F z hz) = (PsiF (u * z) : ℂ) := by
    rw [residualAddChar_integral_lift F psiData gamma hgamma z hz]
    have hdiv : z / (gamma : F) = u * z := by
      simp only [gamma, Units.val_inv_eq_inv_val, Units.val_mk0,
        div_inv_eq_mul, mul_comm]
    rw [hdiv]
    rfl
  have hphi : phi = absoluteTraceChar (ResidueField F) := by
    apply absoluteTraceChar_eq_of_artinSchreier_trivial (ResidueField F)
      (residualAddChar_ne_one F psiData gamma hgamma)
    intro a
    let zO : ringOfIntegers F := teichmuller F a
    have hz : (zO : F) ∈ lattice F 0 := (mem_lattice_zero_iff F).2 zO.property
    have hzAS : (zO : F) + (zO : F) ^ 2 ∈ lattice F 0 := by
      apply add_mem_lattice F hz
      simpa only [pow_two, zero_add] using mul_mem_lattice F hz hz
    have hred : reduce F ((zO : F) + (zO : F) ^ 2) hzAS = a + a ^ 2 := by
      change residueMap F (zO + zO ^ 2) = a + a ^ 2
      simp only [map_add, map_pow, zO, residueMap_teichmuller]
    rw [← hred, hlift]
    exact congrArg Units.val (hAS zO hz)
  intro z hz
  rw [← hlift z hz, hphi]

/-- **The exact last-layer sign**, paper Lemma `D:UR:traceparity` and
equation `D:UR:paritysign`.

The ramified quadratic edge, its actual norm character, and its full
half-conductor chart are the genuine input data of the paper. The chosen
additive character has largest trivial ideal `p_F^(t+1)`. The element
`x` is arbitrary of exact order `-h`, so this applies in particular to
every representative furnished in the positive critical-conductor setup;
no stationarity or exact-norm-choice hypothesis is needed here.

For `u = (Tr x)^2 / N x`, the even row gives `ord_F(u) ≥ T`, allowing
`u = 0`. The odd row gives `ord_F(u) = T-1` and the exact absolute-trace
character on all of `O_F`. The final clause evaluates the prescribed
trace-one element `c` from `D:UR:dchoice` and retains the outer sign.
There is no restriction on the characteristic of either local field. -/
theorem traceParity
    (F E : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Free F E] [Module.Finite F E] [PrimeCyclicExtension F E]
    (hchar : residueCharacteristic F = 2)
    {t h : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hdegree : Module.finrank F E = 2)
    (tau : NormCharacter F E) (_htau : tau ≠ 1)
    (PsiF : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F PsiF (-((t + 1 : ℕ) : ℤ)))
    (hchart : ∀ (a : F) (ha : a ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
      tau.1 (principalUnitOf F (t / 2) (-a) (neg_mem_lattice F ha)) = PsiF a)
    (hh : 1 ≤ h) (hht : h ≤ t)
    (x : E) (hx : ord E x = ((-(h : ℤ)) : WithTop ℤ))
    (c : ringOfIntegers F)
    (hc : (@absoluteTraceTwo (ResidueField F) _ (ringChar.of_eq hchar))
      (residueMap F c) = 1) :
    let u : F := trace F E x ^ 2 / norm F E x
    ((((t + 1 : ℤ) - (h : ℤ)) % 2 = 0) →
      ((t + 1 : ℤ) : WithTop ℤ) ≤ ord F u) ∧
    ((((t + 1 : ℤ) - (h : ℤ)) % 2 = 1) →
      ord F u = ((t : ℤ) : WithTop ℤ) ∧
      ∀ (z : F) (hz : z ∈ lattice F 0),
        (PsiF (u * z) : ℂ) =
          (@absoluteTraceChar (ResidueField F) _ (ringChar.of_eq hchar))
            (reduce F z hz)) ∧
    (-1 : ℂ) ^ (t + 1 + h) * (PsiF (-(c : F) * u) : ℂ) = 1 := by
  let u : F := trace F E x ^ 2 / norm F E x
  obtain ⟨heven, hodd⟩ := traceParity_depths F E ht hres hdegree x hx
  have htpos : 0 < t := by omega
  have hA : norm F E x ≠ 0 := by
    apply Algebra.norm_ne_zero_iff.mpr
    intro hz
    rw [hz, ord_zero] at hx
    exact WithTop.top_ne_coe hx
  have hoddPhase (heps : ((t + 1 : ℤ) - (h : ℤ)) % 2 = 1) :
      ord F u = ((t : ℤ) : WithTop ℤ) ∧
      ∀ (z : F) (hz : z ∈ lattice F 0),
        (PsiF (u * z) : ℂ) =
          (@absoluteTraceChar (ResidueField F) _ (ringChar.of_eq hchar))
            (reduce F z hz) := by
    obtain ⟨hu, hw⟩ := hodd heps
    refine ⟨hu, traceParity_residual F hchar t PsiF hPsi u hu ?_⟩
    intro z hz
    exact traceParity_artinSchreier F E htpos hdegree tau PsiF hchart x hA
      (by rw [mem_lattice, hu]) (by rw [mem_lattice, hw]) z hz
  refine ⟨fun heps => (mem_lattice F).1 (heven heps), hoddPhase, ?_⟩
  have hc0 : (c : F) ∈ lattice F 0 := (mem_lattice_zero_iff F).2 c.property
  by_cases heps : ((t + 1 : ℤ) - (h : ℤ)) % 2 = 0
  · have hphase : PsiF (-(c : F) * u) = 1 := by
      apply hPsi.trivial
      simpa only [neg_neg, Nat.cast_add, Nat.cast_one, zero_add] using
        mul_mem_lattice F (neg_mem_lattice F hc0) (heven heps)
    have hpar : (t + 1 + h) % 2 = 0 := by omega
    rw [hphase, Units.val_one, mul_one,
      pow_eq_pow_mod (t + 1 + h) (by norm_num : (-1 : ℂ) ^ 2 = 1), hpar, pow_zero]
  · have heps1 : ((t + 1 : ℤ) - (h : ℤ)) % 2 = 1 := by omega
    have hpar : (t + 1 + h) % 2 = 1 := by omega
    have hnegc := neg_mem_lattice F hc0
    have hphase := (hoddPhase heps1).2 (-(c : F)) hnegc
    have htrace : (@absoluteTraceTwo (ResidueField F) _ (ringChar.of_eq hchar))
        (reduce F (-(c : F)) hnegc) = 1 := by
      change (@absoluteTraceTwo (ResidueField F) _ (ringChar.of_eq hchar))
        (residueMap F (-c)) = 1
      rw [map_neg, map_neg, hc]
      decide
    rw [absoluteTraceChar_apply, htrace, ZMod.val_one, pow_one] at hphase
    rw [mul_comm (-(c : F)) u, hphase,
      pow_eq_pow_mod (t + 1 + h) (by norm_num : (-1 : ℂ) ^ 2 = 1), hpar]
    norm_num

end

end LanglandsSecondMainLemma.Dyadic.UR
