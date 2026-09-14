import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.Delta.ResidueFormula
import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Dyadic.UR.NormPhase

/-!
# Dyadic / UR / Odd Conductor

Blueprint: `blueprint/tasks/Dyadic/UR/OddConductor.md`.
Paper: Lemma `D:UR:oddT` and formula `D:UR:critical4`.

For a ramified quadratic edge write `T = t + 1`.  When `T` is odd,
FML's exact quadratic trace-ideal theorem identifies the order of `2` as
`(T - 1) / 2`; in particular the lower field has characteristic zero.

The second assertion is the genuinely character-theoretic part of the
paper's argument.  The actual norm character has order two because the
square of a lower-field unit is the norm of that same unit upstairs.  The
identity

`(1 + 2z)^2 = 1 + 4(z + z^2)`

therefore makes the last-layer residue character trivial on the
Artin--Schreier image.  Exactness of the actual norm-character conductor
makes that residue character nontrivial, so FML's finite-field uniqueness
theorem identifies it with `x ↦ (-1)^Tr(x)`.
-/

namespace LanglandsSecondMainLemma.Dyadic.UR

noncomputable section

open LanglandsFirstMainLemma

/-- A character of the quadratic norm quotient kills every square.

This is the literal norm argument: `u^2` is the norm of the image of `u`
in the quadratic extension.  It does not use a cardinality computation for
the norm quotient. -/
private theorem normCharacter_sq_apply
    (F E : Type)
    [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [Field E] [TopologicalSpace E] [IsTopologicalRing E]
    [Algebra F E] [Module.Free F E] [Module.Finite F E]
    [IsModuleTopology F E]
    (hdegree : Module.finrank F E = 2)
    (tau : NormCharacter F E) (u : Fˣ) :
    tau.1 (u ^ 2) = 1 := by
  apply tau.eq_one_on_normRange F E
  refine ⟨Units.map (algebraMap F E) u, ?_⟩
  apply Units.ext
  change norm F E (algebraMap F E (u : F)) = ((u ^ 2 : Fˣ) : F)
  rw [LanglandsFirstMainLemma.norm_algebraMap, hdegree]
  rfl

/-- The odd different exponent determines the order of `2` by FML's exact
quadratic trace-ideal formula. -/
private theorem ord_two_of_odd_conductor
    (F E : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Free F E] [Module.Finite F E]
    [PrimeCyclicExtension F E]
    {t e : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1)
    (hdegree : Module.finrank F E = 2)
    (pi : ringOfIntegers E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers E)) = ⊤)
    (hT : t + 1 = 2 * e + 1) :
    ord F (2 : F) = ((e : ℤ) : WithTop ℤ) := by
  have hram : ramificationIndex F E = 2 := by
    have hfund := finrank_eq_ramificationIndex_mul_residueDegree F E
    rw [hdegree, hres, mul_one] at hfund
    exact hfund.symm
  have hdifferentNat : differentExponent F E = t + 1 := by
    rw [cyclicPrime_differentExponent_eq F E ht hres pi hpi hgen, hdegree]
    omega
  have hdifferentOdd : (differentExponent F E : ℤ) = 2 * (e : ℤ) + 1 := by
    rw [hdifferentNat]
    exact_mod_cast hT
  exact quadratic_ord_two F E pi hpi hgen hram hdegree hdifferentOdd

section

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Finite order of `2` rules out equal characteristic when the residue
characteristic is two. -/
private theorem charZero_of_ord_two
    (hchar : residueCharacteristic F = 2) {e : ℕ}
    (hordTwo : ord F (2 : F) = ((e : ℤ) : WithTop ℤ)) : CharZero F := by
  have htwoNe : (2 : F) ≠ 0 := (ord_ne_top_iff F).1 (by
    rw [hordTwo]
    exact WithTop.coe_ne_top)
  rcases CharP.exists' F with hzero | ⟨p, hp, hcharP⟩
  · exact hzero
  · letI : CharP F p := hcharP
    letI : CharP (ringOfIntegers F) p :=
      (SubringClass.subtype (ringOfIntegers F)).charP
        (fun x y hxy ↦ Subtype.ext hxy) p
    let hcharResidueP : CharP (ResidueField F) p :=
      CharP.of_ringHom_of_ne_zero (residueMap F) p hp.out.ne_zero
    have hpTwo : p = 2 :=
      CharP.eq (ResidueField F) hcharResidueP (ringChar.of_eq hchar)
    have hpzero : (p : F) = 0 := CharP.cast_eq_zero F p
    rw [hpTwo] at hpzero
    exact (htwoNe hpzero).elim

/-- The chart transfers exact multiplicative conductor `t + 1` to exact
additive conductor `-(t + 1)`, using the whole boundary and predecessor ideals. -/
private theorem additiveConductor_of_chart
    {t : ℕ} (htpos : 0 < t)
    (chi : ContinuousQuasiChar F) (PsiF : ContinuousAddChar F)
    (hchi : IsMultiplicativeConductor F chi (t + 1))
    (hchart : ∀ (x : F)
      (hx : x ∈ lattice F (((t / 2 + 1 : ℕ) : ℤ))),
      chi (principalUnitOf F (t / 2) (-x)
        (neg_mem_lattice F hx)) = PsiF x) :
    IsAdditiveConductor F PsiF (-((t + 1 : ℕ) : ℤ)) := by
  have hq_le_t : t / 2 + 1 ≤ t := by omega
  have hPsiTrivial :
      AddCharTrivialOnLattice F PsiF ((t + 1 : ℕ) : ℤ) := by
    intro x hx
    have hxq : x ∈ lattice F (((t / 2 + 1 : ℕ) : ℤ)) :=
      lattice_antitone F (by omega) hx
    rw [← hchart x hxq]
    apply hchi.trivial
    rw [mem_unitFiltration_succ_iff_sub_mem_lattice F t]
    simpa only [coe_principalUnitOf, add_sub_cancel_left] using neg_mem_lattice F hx
  have hPsiNontrivial : ¬ AddCharTrivialOnLattice F PsiF (t : ℤ) := by
    intro htriv
    apply hchi.not_trivialOnPredecessor
    intro u hu
    have hdisp : (u : F) - 1 ∈ lattice F (t : ℤ) := by
      rw [← Nat.sub_add_cancel htpos,
        mem_unitFiltration_succ_iff_sub_mem_lattice F (t - 1)] at hu
      simpa only [Nat.sub_add_cancel htpos] using hu
    let x : F := 1 - (u : F)
    have hxt : x ∈ lattice F (t : ℤ) := by
      simpa only [x, neg_sub] using neg_mem_lattice F hdisp
    have hxq : x ∈ lattice F (((t / 2 + 1 : ℕ) : ℤ)) :=
      lattice_antitone F (by exact_mod_cast hq_le_t) hxt
    have hunit :
        principalUnitOf F (t / 2) (-x) (neg_mem_lattice F hxq) = u := by
      apply Units.ext
      simp only [coe_principalUnitOf, x]
      ring
    calc
      chi u = chi (principalUnitOf F (t / 2) (-x)
          (neg_mem_lattice F hxq)) := congrArg chi hunit.symm
      _ = PsiF x := hchart x hxq
      _ = 1 := htriv x hxt
  apply IsAdditiveConductor.of_boundary
  · simpa only [neg_neg] using hPsiTrivial
  · simpa only [neg_neg, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      using hPsiNontrivial

/-- The identity `(1 + 2a)^2 = 1 + 4(a + a^2)` makes the chart character
trivial on every integral Artin--Schreier value when the unit character kills squares. -/
private theorem chart_four_mul_artinSchreier
    {t e : ℕ} (htpos : 0 < t) (htEven : t = 2 * e)
    (hordTwo : ord F (2 : F) = ((e : ℤ) : WithTop ℤ))
    (hordFour : ord F (4 : F) = ((t : ℕ) : ℤ))
    (chi : ContinuousQuasiChar F) (hchiSquare : ∀ u : Fˣ, chi (u ^ 2) = 1)
    (PsiF : ContinuousAddChar F)
    (hchart : ∀ (x : F)
      (hx : x ∈ lattice F (((t / 2 + 1 : ℕ) : ℤ))),
      chi (principalUnitOf F (t / 2) (-x)
        (neg_mem_lattice F hx)) = PsiF x)
    (a : F) (ha : a ∈ lattice F 0) :
    PsiF ((4 : F) * (a + a ^ 2)) = 1 := by
  have hepos : 0 < e := by omega
  have hq_le_t : t / 2 + 1 ≤ t := by omega
  have haSq : a ^ 2 ∈ lattice F 0 := by
    simpa only [pow_two, zero_add] using mul_mem_lattice F ha ha
  have hAS : a + a ^ 2 ∈ lattice F 0 := add_mem_lattice F ha haSq
  have htwoMem : (2 : F) ∈ lattice F (e : ℤ) := by
    rw [mem_lattice, hordTwo]
  have htwoA : (2 : F) * a ∈ lattice F (e : ℤ) := by
    simpa only [add_zero] using mul_mem_lattice F htwoMem ha
  let u : Fˣ := principalUnitOf F (e - 1) ((2 : F) * a) (by
    simpa only [Nat.sub_add_cancel hepos] using htwoA)
  let x : F := -((4 : F) * (a + a ^ 2))
  have hfourMem : (4 : F) ∈ lattice F (t : ℤ) := by
    rw [mem_lattice, hordFour]
  have hxt : x ∈ lattice F (t : ℤ) :=
    neg_mem_lattice F
      (by simpa only [add_zero] using mul_mem_lattice F hfourMem hAS)
  have hxq : x ∈ lattice F (((t / 2 + 1 : ℕ) : ℤ)) :=
    lattice_antitone F (by exact_mod_cast hq_le_t) hxt
  have hunitSquare :
      u ^ 2 = principalUnitOf F (t / 2) (-x) (neg_mem_lattice F hxq) := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, u, coe_principalUnitOf, x]
    ring
  have hphaseNeg : PsiF x = 1 := by
    rw [← hchart x hxq, ← hunitSquare]
    exact hchiSquare u
  change PsiF.toAddChar (-((4 : F) * (a + a ^ 2))) = 1 at hphaseNeg
  rw [AddChar.map_neg_eq_inv, inv_eq_one] at hphaseNeg
  exact hphaseNeg

/-- FML's nontrivial residual character is the absolute-trace character once
its integral lifts annihilate the Artin--Schreier image. -/
private theorem four_mul_eq_absoluteTrace_of_artinSchreier
    [CharP (ResidueField F) 2] {t : ℕ}
    (PsiF : ContinuousAddChar F)
    (hPsiConductor : IsAdditiveConductor F PsiF (-((t + 1 : ℕ) : ℤ)))
    (hordFour : ord F (4 : F) = ((t : ℕ) : ℤ))
    (hAS : ∀ a : F, a ∈ lattice F 0 → PsiF ((4 : F) * (a + a ^ 2)) = 1)
    (z : F) (hz : z ∈ lattice F 0) :
    (PsiF ((4 : F) * z) : ℂ) = absoluteTraceChar (ResidueField F) (reduce F z hz) := by
  letI : Fintype (ResidueField F) := residueFieldFintype F
  let psiData : LocalAddCharData F :=
    continuousAddChar_toData F PsiF (-((t + 1 : ℕ) : ℤ)) hPsiConductor
  have hfourNe : (4 : F) ≠ 0 := (ord_ne_top_iff F).1 (by
    rw [hordFour]
    exact WithTop.coe_ne_top)
  let four : Fˣ := Units.mk0 (4 : F) hfourNe
  let gamma : Fˣ := four⁻¹
  have hgamma :
      ord F (gamma : F) = ((psiData.conductor + 1 : ℤ) : WithTop ℤ) := by
    simp only [gamma, four, Units.val_inv_eq_inv_val, Units.val_mk0,
      ord_inv, psiData, continuousAddChar_toData_conductor]
    rw [hordFour]
    norm_cast
    omega
  let phi : FiniteAddChar (ResidueField F) := residualAddChar F psiData gamma hgamma
  have hphi_apply (a : F) (ha : a ∈ lattice F 0) :
      phi (reduce F a ha) = (PsiF ((4 : F) * a) : ℂ) := by
    simpa only [psiData, continuousAddChar_toData_character, gamma, four,
      Units.val_inv_eq_inv_val, Units.val_mk0, div_inv_eq_mul, mul_comm]
      using residualAddChar_integral_lift F psiData gamma hgamma a ha
  have hphiAS : ∀ c : ResidueField F, phi (c + c ^ 2) = 1 := by
    intro c
    let aO : ringOfIntegers F := teichmuller F c
    let a : F := (aO : F)
    have ha : a ∈ lattice F 0 := (mem_lattice_zero_iff F).2 aO.property
    have haSq : a ^ 2 ∈ lattice F 0 := by
      simpa only [pow_two, zero_add] using mul_mem_lattice F ha ha
    have haAS : a + a ^ 2 ∈ lattice F 0 := add_mem_lattice F ha haSq
    have hreduceAS : reduce F (a + a ^ 2) haAS = c + c ^ 2 := by
      change residueMap F (aO + aO ^ 2) = c + c ^ 2
      dsimp only [aO]
      rw [map_add, map_pow, residueMap_teichmuller]
    rw [← hreduceAS, hphi_apply, hAS a ha]
    rfl
  have hphi : phi = absoluteTraceChar (ResidueField F) :=
    absoluteTraceChar_eq_of_artinSchreier_trivial (ResidueField F)
      (residualAddChar_ne_one F psiData gamma hgamma) hphiAS
  rw [← hphi, hphi_apply]

end

/-- **The odd quadratic conductor** (paper Lemma `D:UR:oddT`).

Let `E/F` be the ramified quadratic edge of positive lower break `t`, and
put `T = t + 1`.  The character `tau` is an actual nontrivial norm
character.  The chart hypothesis is precisely the paper's chosen additive
duality chart on `p_F^(t/2+1)`:

`tau(1-x) = PsiF(x)`.

If `T` is odd, the conclusion says:

* `F` has characteristic zero;
* for `e = ord_F(2)`, one has `T = 2e + 1`;
* on every integral `z`, `PsiF(4z)` is the absolute-trace character of
  the reduction of `z`.

The reduction in the last clause is FML's canonical `reduce`, so the
formula is independent of representatives.  Exact additive-conductor data
for `PsiF` are derived inside the proof from the actual chart and the exact
conductor of `tau`; they are not an extra hypothesis. -/
theorem oddConductor
    (F E : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Free F E] [Module.Finite F E]
    [PrimeCyclicExtension F E]
    (hchar : residueCharacteristic F = 2)
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (htpos : 0 < t) (hres : residueDegree F E = 1)
    (hdegree : Module.finrank F E = 2)
    (pi : ringOfIntegers E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers E)) = ⊤)
    (tau : NormCharacter F E) (htau : tau ≠ 1)
    (PsiF : ContinuousAddChar F)
    (hchart : ∀ (x : F)
      (hx : x ∈ lattice F (((t / 2 + 1 : ℕ) : ℤ))),
      tau.1 (principalUnitOf F (t / 2) (-x)
        (neg_mem_lattice F hx)) = PsiF x)
    (hodd : Odd (t + 1)) :
    CharZero F ∧
      ∃ e : ℕ,
        ord F (2 : F) = ((e : ℤ) : WithTop ℤ) ∧
        t + 1 = 2 * e + 1 ∧
        ∀ (z : F) (hz : z ∈ lattice F 0),
          (PsiF ((4 : F) * z) : ℂ) =
            (@absoluteTraceChar (ResidueField F) _
              (ringChar.of_eq hchar)) (reduce F z hz) := by
  obtain ⟨e, hT⟩ := hodd
  have hordTwo : ord F (2 : F) = ((e : ℤ) : WithTop ℤ) :=
    ord_two_of_odd_conductor F E ht hres hdegree pi hpi hgen hT
  have hcharZero : CharZero F := charZero_of_ord_two F hchar hordTwo
  have htEven : t = 2 * e := by omega
  have hordFour : ord F (4 : F) = ((t : ℕ) : ℤ) := by
    rw [show (4 : F) = (2 : F) ^ 2 by norm_num, ord_pow, hordTwo, htEven,
      ← WithTop.coe_nsmul]
    norm_cast
  have hPsiConductor : IsAdditiveConductor F PsiF (-((t + 1 : ℕ) : ℤ)) :=
    additiveConductor_of_chart F htpos tau.1 PsiF
      (ramifiedNormCharacter_conductor F E ht hres pi hpi hgen tau htau) hchart
  letI : CharP (ResidueField F) 2 := ringChar.of_eq hchar
  refine ⟨hcharZero, e, hordTwo, hT, ?_⟩
  exact four_mul_eq_absoluteTrace_of_artinSchreier F PsiF hPsiConductor hordFour
    (chart_four_mul_artinSchreier F htpos htEven hordTwo hordFour tau.1
      (normCharacter_sq_apply F E hdegree tau) PsiF hchart)

end

end LanglandsSecondMainLemma.Dyadic.UR
