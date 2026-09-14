import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Basic.Characters

/-!
# Dyadic / UR / Norm Phase

Blueprint: blueprint/tasks/Dyadic/UR/NormPhase.md
Paper: D:UR:normphase

This proves the actual quadratic norm phase on the full half-conductor
ideal.  If the lower break is `t`, the paper writes `T = t + 1` and
`q = ⌈T / 2⌉`; for natural numbers this is `q = t / 2 + 1`.

The chart hypothesis is the paper's actual identity
`tau (1 - x) = PsiF x` for every `x ∈ p_F^q`.  The units `1 - x`
are constructed canonically with FML's `principalUnitOf`.

The upper character is the actual trace pullback of `PsiF`.  Thus the
conclusion is literally `PsiE z = PsiF (N z)`, with the positive norm
sign required in residue characteristic two.
-/

namespace LanglandsSecondMainLemma.Dyadic.UR

noncomputable section

open LanglandsFirstMainLemma

/-- The exact degree-two identity
`N(1-z) = 1 - Tr(z) + N(z)`.

FML supplies the norm expansion in elementary symmetric functions.  In
degree two its only nonconstant terms are trace and norm. -/
private theorem quadraticNormOneSub
    (F E : Type*)
    [Field F] [Field E] [Algebra F E]
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

/-- **Actual dyadic norm phase** (paper Lemma `D:UR:normphase`).

Let `E/F` be the ramified quadratic edge of positive lower break `t`.
The assumptions `residueDegree F E = 1`, `finrank F E = 2`, and `0 < t`
are the paper's ramified dyadic setup; FML's positive-break theorem in
particular forces the residue characteristic to be two.

Let `tau` be the nontrivial actual norm character and let `PsiF` be the
scaled additive character from the paper.  If the actual chart
`tau(1-x) = PsiF(x)` holds on all of
`p_F^(t / 2 + 1)`, then its trace pullback `PsiE` satisfies
`PsiE(z) = PsiF(N z)` on all of `p_E^(t / 2 + 1)`.

No surjectivity of the norm is used: `tau` is evaluated only at the norm
of the explicitly constructed unit `1-z`. -/
theorem normPhase
    (F E : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Free F E] [Module.Finite F E]
    [PrimeCyclicExtension F E]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (htpos : 0 < t) (hres : residueDegree F E = 1)
    (hdegree : Module.finrank F E = 2)
    (tau : NormCharacter F E) (_htau : tau ≠ 1)
    (PsiF : ContinuousAddChar F)
    (hchart : ∀ (x : F)
      (hx : x ∈ lattice F (((t / 2 + 1 : ℕ) : ℤ))),
      tau.1 (principalUnitOf F (t / 2) (-x) (neg_mem_lattice F hx)) = PsiF x)
    (z : E) (hz : z ∈ lattice E (((t / 2 + 1 : ℕ) : ℤ))) :
    tracePullbackAddChar F E PsiF z = PsiF (norm F E z) := by
  let q : ℕ := t / 2 + 1
  have hqcast : ((q : ℕ) : ℤ) = ((t / 2 + 1 : ℕ) : ℤ) := rfl
  have hq_le_T : q ≤ t + 1 := by
    dsimp only [q]
    omega

  -- The exact trace-ideal formula gives
  -- `Tr(p_E^q) = p_F^⌊(q+T)/2⌋ ⊆ p_F^q`.
  have htrace : trace F E z ∈ lattice F (q : ℤ) := by
    obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
    have hmap : trace F E z ∈
        Submodule.map ((trace F E).restrictScalars (ringOfIntegers F))
          ((lattice E (q : ℤ)).restrictScalars (ringOfIntegers F)) := by
      apply Submodule.mem_map.mpr
      refine ⟨z, ?_, rfl⟩
      change z ∈ lattice E (q : ℤ)
      simpa only [hqcast] using hz
    rw [cyclicPrime_trace_lattice_image_eq F E ht hres pi hpi hgen,
      hdegree] at hmap
    have hdepth : (q : ℤ) ≤
        ((q : ℤ) + (((2 - 1) * (t + 1) : ℕ) : ℤ)) / (2 : ℤ) := by
      norm_num
      omega
    exact lattice_antitone F hdepth hmap

  -- Total ramification (`residueDegree = 1`) makes normalized order of
  -- the norm equal to normalized order upstairs.
  have hnorm : norm F E z ∈ lattice F (q : ℤ) := by
    rw [mem_lattice] at hz ⊢
    rw [ord_norm, hres, one_nsmul]
    simpa only [hqcast] using hz

  let y : F := trace F E z - norm F E z
  have hy : y ∈ lattice F (q : ℤ) :=
    sub_mem_lattice F htrace hnorm

  -- Construct the actual units `1-z` and `1-y` from their positive-depth
  -- lattice elements.  Here `q = t / 2 + 1`, so `principalUnitOf` is
  -- invoked at predecessor depth `t / 2`.
  have hnegz : -z ∈ lattice E (q : ℤ) :=
    neg_mem_lattice E (by simpa only [hqcast] using hz)
  let uz : Eˣ := principalUnitOf E (t / 2) (-z) (by
    simpa only [q, Nat.cast_add, Nat.cast_one] using hnegz)
  have hyOrig : y ∈ lattice F (((t / 2 + 1 : ℕ) : ℤ)) := by
    simpa only [hqcast] using hy
  let uy : Fˣ := principalUnitOf F (t / 2) (-y) (neg_mem_lattice F hyOrig)
  have huy : (uy : F) = 1 - y := by
    simp only [uy, coe_principalUnitOf]
    ring

  -- This is the exact quadratic identity, lifted from fields to units.
  have hnormUnits : normUnits F E uz = uy := by
    apply Units.ext
    simp only [coe_normUnits, uz, coe_principalUnitOf, huy]
    rw [show (1 : E) + -z = 1 - z by ring]
    rw [quadraticNormOneSub F E hdegree z]
    dsimp only [y]
    ring

  have htauNorm : tau.1 (normUnits F E uz) = 1 :=
    tau.eq_one_on_normRange F E _ ⟨uz, rfl⟩
  have hphase : PsiF y = 1 := by
    rw [← hchart y hyOrig]
    change tau.1 uy = 1
    rw [← hnormUnits]
    exact htauNorm

  -- `PsiF(Tr z - N z) = 1` is exactly the desired equality of the two
  -- additive-character values.
  rw [tracePullbackAddChar_apply]
  apply div_eq_one.mp
  calc
    PsiF (trace F E z) / PsiF (norm F E z) =
        PsiF (trace F E z - norm F E z) :=
      (PsiF.toAddChar.map_sub_eq_div _ _).symm
    _ = PsiF y := rfl
    _ = 1 := hphase

end

end LanglandsSecondMainLemma.Dyadic.UR
