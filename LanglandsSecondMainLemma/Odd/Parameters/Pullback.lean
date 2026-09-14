import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Odd.Parameters.Preservation
import LanglandsSecondMainLemma.Odd.NormLog
import LanglandsSecondMainLemma.Odd.NormPhase

/-!
# Odd / Parameters / Pullback

Blueprint: blueprint/tasks/Odd/Parameters/Pullback.md
Paper: Proposition 8.18 (`O:P:pullback`), corrected source lines 3075--3120,
with the full-coefficient and norm-choice setup in lines 2989--3039.

The norm-filtration theorem puts the actual norm in the entire lower
logarithm chart. The norm-log error is killed at depth `r+1`, and the
whole-subgroup norm phase cancels its norm term using the exact equation
`N(w) = gamma/A`. The coefficient is `gamma - A*w`; the scalar `A` stays
outside the norm. All valuation and additive-conductor exponents are integers.
-/

namespace LanglandsSecondMainLemma.Odd.Parameters

noncomputable section

open LanglandsFirstMainLemma

open private lamprechtAddChar_eq_of_sub_mem from
  LanglandsFirstMainLemma.Lamprecht.Formula

/-- The full upper chart is exactly `ceil(n/p)`. Its norm lies in the full
lower chart: this is the inverse-Herbrand form of the endpoint estimates
in the proof of `O:P:pullback`. -/
private theorem pullback_depths {p t r : ℕ} (hp : 2 < p) (ht : 0 < t)
    (hr : t < r) :
    0 < (t + 1) ⌈/⌉ p ∧
    0 < (r + 1) ⌈/⌉ p ∧
    r - t + (t + 1) ⌈/⌉ p = (1 + t + p * (r - t)) ⌈/⌉ p ∧
    herbrandPsiNat t p ((r + 1) ⌈/⌉ p - 1) + 1 ≤
      r - t + (t + 1) ⌈/⌉ p := by
  have hp0 : 0 < p := by omega
  have hc : 0 < (t + 1) ⌈/⌉ p := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_pos (by omega) hp0
  have hk : 0 < (r + 1) ⌈/⌉ p := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_pos (by omega) hp0
  have hpc : t + 1 ≤ p * ((t + 1) ⌈/⌉ p) :=
    (ceilDiv_le_iff_le_mul hp0).1 le_rfl
  have hrel : t + (r - t) = r := Nat.add_sub_of_le hr.le
  have hkq : (r + 1) ⌈/⌉ p ≤ r - t + (t + 1) ⌈/⌉ p := by
    rw [ceilDiv_le_iff_le_mul hp0]
    nlinarith
  refine ⟨hc, hk, ?_, ?_⟩
  · simp only [Nat.ceilDiv_eq_add_pred_div]
    have he : 1 + t + p * (r - t) + p - 1 = t + p + p * (r - t) := by
      omega
    rw [he, Nat.add_mul_div_left _ _ hp0]
    rw [show t + 1 + p - 1 = t + p by omega]
    omega
  · by_cases hkt : (r + 1) ⌈/⌉ p - 1 ≤ t
    · rw [herbrandPsiNat_of_le_break t p hkt]
      omega
    · rw [herbrandPsiNat_of_break_le t p (by omega)]
      have hpk : p * ((r + 1) ⌈/⌉ p - 1) ≤ r := by
        have hlt : p * ((r + 1) ⌈/⌉ p - 1) < r + 1 := by
          exact lt_of_not_ge (fun H ↦ by
            have := (ceilDiv_le_iff_le_mul hp0).2 H
            omega)
        omega
      have hsub : ((r + 1) ⌈/⌉ p - 1 - t) + t =
          (r + 1) ⌈/⌉ p - 1 := Nat.sub_add_cancel (by omega)
      nlinarith

private theorem pullback_unit_displacement
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {q : ℕ} (hq : 0 < q)
    (u : unitFiltration E q) :
    1 - ((u : Eˣ) : E) ∈ lattice E (q : ℤ) := by
  have hu := (mem_unitFiltration_succ_iff_sub_mem_lattice E (q - 1)
    (u : Eˣ)).1 (by simpa only [Nat.sub_add_cancel hq] using u.property)
  simpa only [Nat.sub_add_cancel hq, neg_sub] using neg_mem_lattice E hu

section Extension

variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E]
  [Module.Free F E] [Module.Finite F E] [PrimeCyclicExtension F E]

/-- Containment of the norm in the full lower coefficient domain, including
the critical successor if that is where the lower depth falls. -/
private theorem pullback_norm_mem
    {p t r : ℕ} (hdegree : Module.finrank F E = p) (hodd : 2 < p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
    (hr : t < r) (hres : residueDegree F E = 1)
    (u : unitFiltration E (r - t + (t + 1) ⌈/⌉ p)) :
    normUnits F E (u : Eˣ) ∈ unitFiltration F ((r + 1) ⌈/⌉ p) := by
  obtain ⟨_, hk, _, hdepth⟩ := pullback_depths hodd htpos hr
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have hmaps := normMapsUnitFiltration_herbrand_succ F E ht hres pi hpi hgen
    ((r + 1) ⌈/⌉ p - 1)
  rw [hdegree, Nat.sub_add_cancel hk] at hmaps
  exact hmaps (u : Eˣ) (unitFiltration_antitone E hdepth u.property)

omit [Module.Free F E] [PrimeCyclicExtension F E] in
/-- Exact norm and coefficient orders. In particular `w` has negative
integer order `-(r-t)`; no fractional-ideal depth is truncated. -/
private theorem pullback_orders
    {p t r : ℕ} (hdegree : Module.finrank F E = p) (hodd : 2 < p)
    (hr : t < r) (hres : residueDegree F E = 1)
    (e : LocalAddCharData F) (gamma A : Fˣ) (w : Eˣ)
    (hgamma : ord F (gamma : F) =
      ((-e.conductor - (r : ℤ) - 1 : ℤ) : WithTop ℤ))
    (hA : ord F (A : F) =
      ((-e.conductor - (t : ℤ) - 1 : ℤ) : WithTop ℤ))
    (hw : normUnits F E w = gamma / A) :
    ord E (w : E) = ((-((r - t : ℕ) : ℤ) : ℤ) : WithTop ℤ) ∧
    ord E (algebraMap F E (gamma : F) - algebraMap F E (A : F) * (w : E)) =
      p • ord F (gamma : F) := by
  have hram : ramificationIndex F E = p := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F E
    rw [hres, mul_one, hdegree] at h
    exact h.symm
  have hwn : norm F E (w : E) = (gamma : F) / (A : F) :=
    by simpa only [coe_normUnits, Units.val_div_eq_div_val] using congrArg Units.val hw
  have hwOrder : ord E (w : E) = ((-((r - t : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
    calc
      ord E (w : E) = ord F (norm F E (w : E)) := by
        rw [ord_norm, hres, one_nsmul]
      _ = ord F (gamma : F) - ord F (A : F) := by rw [hwn, ord_div]
      _ = _ := by
        rw [hgamma, hA, ← WithTop.LinearOrderedAddCommGroup.coe_sub]
        congr 1
        omega
  have hlt : ord E (algebraMap F E (gamma : F)) <
      ord E (algebraMap F E (A : F) * (w : E)) := by
    rw [ord_mul, ord_algebraMap, ord_algebraMap, hram, hgamma, hA, hwOrder]
    simp only [← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_lt_coe,
      nsmul_eq_mul]
    have hpZ : (2 : ℤ) < p := by exact_mod_cast hodd
    have hrZ : (t : ℤ) < r := by exact_mod_cast hr
    rw [Nat.cast_sub hr.le]
    nlinarith
  refine ⟨hwOrder, ?_⟩
  rw [(ord E).map_sub_eq_of_lt_left hlt, ord_algebraMap, hram]

/-- **Full coefficient of a descending pullback, Paper 8.18
(`O:P:pullback`).** The exact norm witness is the one supplied by
`normChoice`, after preservation of the original full norm-character chart.
For every such witness the coefficient is literally `gamma - A*w`.

The conclusions include the full chart depth, the exact multiplicative
conductor, the trace additive conductor (with its different exponent), and
both forms of the coefficient order. The character `lambda` is an arbitrary
continuous quasi-character, and both field characteristics are permitted.
The formula is written on `U_E^q` with `u = 1-x`, equivalently on the
paper's entire ideal `x ∈ 𝔭_E^q`. -/
theorem pullback
    {p t r : ℕ} (hdegree : Module.finrank F E = p) (hodd : 2 < p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
    (hr : t < r) (hres : residueDegree F E = 1)
    (lambda : ContinuousQuasiChar F)
    (hlambda : IsMultiplicativeConductor F lambda (r + 1))
    (e : LocalAddCharData F) (gamma A : Fˣ)
    (hgamma : ord F (gamma : F) =
      ((-e.conductor - (r : ℤ) - 1 : ℤ) : WithTop ℤ))
    (hlambdaFormula : ∀ u : unitFiltration F ((r + 1) ⌈/⌉ p),
      lambda u = e.character ((gamma : F) *
        truncatedLog p (1 - ((u : Fˣ) : F))))
    (nu : NormCharacter F E) (hnu : nu ≠ 1)
    (hA : ord F (A : F) =
      ((-e.conductor - (t : ℤ) - 1 : ℤ) : WithTop ℤ))
    (hnuFormula : ∀ u : unitFiltration F ((t + 1) ⌈/⌉ p),
      nu.1 u = e.character ((A : F) *
        truncatedLog p (1 - ((u : Fˣ) : F))))
    (w : Eˣ) (hw : normUnits F E w = gamma / A) :
    let h := r - t
    let n := 1 + t + p * h
    let q := h + (t + 1) ⌈/⌉ p
    let dE : ℤ := (p : ℤ) * e.conductor + (((p - 1) * (t + 1) : ℕ) : ℤ)
    let C := algebraMap F E (gamma : F) - algebraMap F E (A : F) * (w : E)
    q = n ⌈/⌉ p ∧
    IsMultiplicativeConductor E lambda.compNorm n ∧
    IsAdditiveConductor E (tracePullbackAddChar F E e.character) dE ∧
    ord E C = p • ord F (gamma : F) ∧
    ord E C = ((-dE - (n : ℤ) : ℤ) : WithTop ℤ) ∧
    ∀ u : unitFiltration E q,
      lambda.compNorm (u : Eˣ) = tracePullbackAddChar F E e.character
        (C * truncatedLog p (1 - ((u : Eˣ) : E))) := by
  dsimp only
  obtain ⟨hc, _, hqeq, _⟩ := pullback_depths hodd htpos hr
  have hqpos : 0 < r - t + (t + 1) ⌈/⌉ p := by omega
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have hchar : residueCharacteristic F = Module.finrank F E :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak F E
      ht htpos pi hpi hgen
  have hcharE : residueCharacteristic E = p :=
    (residueCharacteristic_extension_eq F E).trans (hchar.trans hdegree)
  have hodd' : Module.finrank F E ≠ 2 := by omega
  have hcond := multiplicativeConductor_compNorm_aboveBreak F E ht hres pi hpi hgen
    hr hlambda
  rw [herbrandPsiNat_of_break_le _ _ hr.le, hdegree] at hcond
  have hadd := additiveConductor_compTrace_cyclicPrime F E ht hres pi hpi hgen
    e.isConductor
  rw [hdegree] at hadd
  obtain ⟨hwOrder, hC⟩ := pullback_orders F E hdegree hodd hr hres e gamma A w
    hgamma hA hw
  refine ⟨hqeq, ?_, hadd, hC, ?_, ?_⟩
  · convert hcond using 1; omega
  · rw [hC, hgamma, ← WithTop.coe_nsmul]
    congr 1
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      Nat.cast_sub hr.le, Nat.cast_sub (by omega : 1 ≤ p)]
    ring
  · intro u
    let x : E := 1 - ((u : Eˣ) : E)
    have hx : x ∈ lattice E ((r - t + (t + 1) ⌈/⌉ p : ℕ) : ℤ) :=
      pullback_unit_displacement E hqpos u
    have hxone : 1 - x = ((u : Eˣ) : E) := by dsimp only [x]; ring
    have hnorm := pullback_norm_mem F E hdegree hodd ht htpos hr hres u
    have hlog := normLog F E ht htpos hres hchar hodd' (r - t) x (by
      simpa only [hdegree] using hx)
    rw [hdegree, hxone] at hlog
    have herr := mul_mem_lattice F ((mem_lattice F).2 hgamma.ge) hlog
    have herrorDepth : -e.conductor - (r : ℤ) - 1 +
        ((t + 1 + (r - t) : ℕ) : ℤ) = -e.conductor := by omega
    rw [herrorDepth] at herr
    have hphaseLog : lambda.compNorm (u : Eˣ) =
        e.character ((gamma : F) *
          (trace F E (truncatedLog p x) + norm F E (truncatedLog p x))) := by
      change lambda (normUnits F E (u : Eˣ)) = _
      refine (hlambdaFormula ⟨_, hnorm⟩).trans ?_
      apply lamprechtAddChar_eq_of_sub_mem F e
      change (gamma : F) * truncatedLog p (1 - norm F E ((u : Eˣ) : E)) -
        (gamma : F) * (trace F E (truncatedLog p x) + norm F E (truncatedLog p x)) ∈
          lattice F (-e.conductor)
      convert herr using 1; ring
    have hPx : truncatedLog p x ∈ lattice E
        ((r - t + (t + 1) ⌈/⌉ p : ℕ) : ℤ) :=
      (truncatedLogOnLattice E p _ hcharE hqpos ⟨x, hx⟩).property
    have hwPx : (w : E) * truncatedLog p x ∈
        lattice E (((t + 1) ⌈/⌉ p : ℕ) : ℤ) := by
      have hm := mul_mem_lattice E ((mem_lattice E).2 hwOrder.ge) hPx
      convert hm using 1
      congr 1
      omega
    have hAint : unitOrder F A = -e.conductor - (t : ℤ) - 1 := by
      rw [ord_coe_eq_unitOrder] at hA
      exact WithTop.coe_injective hA
    have hPsi : IsAdditiveConductor F (scaleAddCharData F e A).character
        (-((t + 1 : ℕ) : ℤ)) := by
      have hcA := (scaleAddCharData F e A).isConductor
      simpa only [scaleAddCharData_conductor, hAint,
        show e.conductor + (-e.conductor - (t : ℤ) - 1) =
          -((t + 1 : ℕ) : ℤ) by push_cast; ring] using hcA
    have hchart : ∀ z : lattice F (((t + 1) ⌈/⌉ p : ℕ) : ℤ),
        nu.1 (positiveUnitOfLattice F hc (-z)) =
          (scaleAddCharData F e A).character (truncatedLog p (z : F)) := by
      intro z
      simpa using hnuFormula (positiveUnitOfLattice F hc (-z))
    have hconversion := (normPhase F E ht htpos hres hchar hodd'
      ((t + 1) ⌈/⌉ p) (by rw [hdegree]) hc nu hnu
      (scaleAddCharData F e A).character hPsi (by
        simpa only [hdegree] using hchart)
      ((w : E) * truncatedLog p x) hwPx).2
    have hwn : norm F E (w : E) = (gamma : F) / (A : F) := by
      simpa only [coe_normUnits, Units.val_div_eq_div_val] using congrArg Units.val hw
    have hcancel : (A : F) * (-norm F E ((w : E) * truncatedLog p x)) =
        -((gamma : F) * norm F E (truncatedLog p x)) := by
      rw [map_mul, hwn]
      field_simp
    have hphase : tracePullbackAddChar F E e.character
        (algebraMap F E (A : F) * ((w : E) * truncatedLog p x)) =
        e.character (-((gamma : F) * norm F E (truncatedLog p x))) := by
      rw [tracePullbackAddChar_apply, scaleAddCharData_character_apply,
        scaleAddCharData_character_apply, hcancel] at hconversion
      rw [tracePullbackAddChar_apply, ← Algebra.smul_def, map_smul, smul_eq_mul]
      exact hconversion
    have htrace : tracePullbackAddChar F E e.character
        (algebraMap F E (gamma : F) * truncatedLog p x) =
        e.character ((gamma : F) * trace F E (truncatedLog p x)) := by
      rw [tracePullbackAddChar_apply, ← Algebra.smul_def, map_smul, smul_eq_mul]
    rw [hphaseLog]
    change _ = tracePullbackAddChar F E e.character
      ((algebraMap F E (gamma : F) - algebraMap F E (A : F) * (w : E)) *
        truncatedLog p x)
    calc
      e.character ((gamma : F) *
          (trace F E (truncatedLog p x) + norm F E (truncatedLog p x))) =
          e.character ((gamma : F) * trace F E (truncatedLog p x) -
            (-((gamma : F) * norm F E (truncatedLog p x)))) := by congr 1; ring
      _ = e.character ((gamma : F) * trace F E (truncatedLog p x)) /
          e.character (-((gamma : F) * norm F E (truncatedLog p x))) :=
        e.character.toAddChar.map_sub_eq_div _ _
      _ = tracePullbackAddChar F E e.character
          (algebraMap F E (gamma : F) * truncatedLog p x) /
          tracePullbackAddChar F E e.character
            (algebraMap F E (A : F) * ((w : E) * truncatedLog p x)) := by
        rw [htrace, hphase]
      _ = tracePullbackAddChar F E e.character
          (algebraMap F E (gamma : F) * truncatedLog p x -
            algebraMap F E (A : F) * ((w : E) * truncatedLog p x)) :=
        ((tracePullbackAddChar F E e.character).toAddChar.map_sub_eq_div _ _).symm
      _ = _ := by congr 1; ring

/-- A constructor for the parameters in `pullback`: start with the original
full coefficient of the actual norm character, use `normChoice` to move it
within `U_F^t`, and retain its entire chart and coefficient class. No exact
norm representative is assumed. -/
theorem pullback_exists
    {p t r : ℕ} (hdegree : Module.finrank F E = p) (hodd : 2 < p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
    (hr : t < r) (hres : residueDegree F E = 1)
    (lambda : ContinuousQuasiChar F)
    (hlambda : IsMultiplicativeConductor F lambda (r + 1))
    (e : LocalAddCharData F) (gamma A : Fˣ)
    (hgamma : ord F (gamma : F) =
      ((-e.conductor - (r : ℤ) - 1 : ℤ) : WithTop ℤ))
    (hlambdaFormula : ∀ u : unitFiltration F ((r + 1) ⌈/⌉ p),
      lambda u = e.character ((gamma : F) *
        truncatedLog p (1 - ((u : Fˣ) : F))))
    (nu : NormCharacter F E) (hnu : nu ≠ 1)
    (hA : ord F (A : F) =
      ((-e.conductor - (t : ℤ) - 1 : ℤ) : WithTop ℤ))
    (hnuFormula : ∀ u : unitFiltration F ((t + 1) ⌈/⌉ p),
      nu.1 u = e.character ((A : F) *
        truncatedLog p (1 - ((u : Fˣ) : F)))) :
    let h := r - t
    let n := 1 + t + p * h
    let q := h + (t + 1) ⌈/⌉ p
    let dE : ℤ := (p : ℤ) * e.conductor + (((p - 1) * (t + 1) : ℕ) : ℤ)
    ∃ (A' : Fˣ) (w : Eˣ),
      A' / A ∈ unitFiltration F t ∧
      ord F (A' : F) = ((-e.conductor - (t : ℤ) - 1 : ℤ) : WithTop ℤ) ∧
      (A' : F) - (A : F) ∈
        lattice F (-e.conductor - (((t + 1) ⌈/⌉ p : ℕ) : ℤ)) ∧
      (∀ u : unitFiltration F ((t + 1) ⌈/⌉ p),
        nu.1 u = e.character ((A' : F) *
          truncatedLog p (1 - ((u : Fˣ) : F)))) ∧
      normUnits F E w = gamma / A' ∧
      let C := algebraMap F E (gamma : F) - algebraMap F E (A' : F) * (w : E)
      q = n ⌈/⌉ p ∧
      IsMultiplicativeConductor E lambda.compNorm n ∧
      IsAdditiveConductor E (tracePullbackAddChar F E e.character) dE ∧
      ord E C = p • ord F (gamma : F) ∧
      ord E C = ((-dE - (n : ℤ) : ℤ) : WithTop ℤ) ∧
      ∀ u : unitFiltration E q,
        lambda.compNorm (u : Eˣ) = tracePullbackAddChar F E e.character
          (C * truncatedLog p (1 - ((u : Eˣ) : E))) := by
  obtain ⟨A', hratio, hA', hclass, hformula, _, w, hw, _⟩ :=
    normChoice F E hdegree hodd ht htpos hres nu hnu e A gamma hA hnuFormula
  refine ⟨A', w, hratio, hA', hclass, hformula, hw, ?_⟩
  exact pullback F E hdegree hodd ht htpos hr hres lambda hlambda e gamma A'
    hgamma hlambdaFormula nu hnu hA' hformula w hw

end Extension

end

end LanglandsSecondMainLemma.Odd.Parameters
