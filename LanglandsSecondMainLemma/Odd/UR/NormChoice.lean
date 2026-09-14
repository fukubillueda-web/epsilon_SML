import LanglandsFirstMainLemma.Ramification.NormRepresentatives
import LanglandsSecondMainLemma.Odd.UR.Twist

/-!
# Norm choices at the available relative precision

Paper: Lemma 6.8 (`O:I:chooseA`), with `O:I:lambdachart` and
`O:I:epsilon`, corrected source lines 1416--1451.

The common twist supplies its conductor bound and exact conductor when
`h > 0`. We first construct its full logarithm coefficient on
`𝔭_F^⌊(t+1+h)/2⌋`, including the zero class. FML's norm representatives
then replace this coefficient within its ambiguity when `h < t`.
At `h = t` the relative precision is only `t`: the retained error is
integral and is not discarded from the character formula.
-/

namespace LanglandsSecondMainLemma.Odd.UR

noncomputable section
open LanglandsFirstMainLemma

section Coefficient
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The half-depth is positive and supports the full odd logarithm chart. -/
theorem normChoice_depths {p t h : ℕ} (hp : 2 < p) (ht : 0 < t) :
    0 < (t + 1 + h) / 2 ∧
      (t + 1 + h) / 2 < t + 1 + h ∧
      t + 1 + h ≤ p * ((t + 1 + h) / 2) := by
  have hd : 0 < (t + 1 + h) / 2 := by omega
  have hp3 : 3 ≤ p := by omega
  have hmul := Nat.mul_le_mul_right ((t + 1 + h) / 2) hp3
  omega

/-- Construction of `A_*` in `O:I:lambdachart`. The coefficient is zero
when the restriction is trivial. At `h = 0` the nonzero coefficient is
integral; for `h > 0` it has exact order `-h`. -/
theorem normChoice_coefficient
    {p t h : ℕ} (hp : p.Prime) (hodd : 2 < p) (ht : 0 < t)
    (hchar : residueCharacteristic F = p)
    (lambda : ContinuousQuasiChar F) (Psi : LocalAddCharData F)
    (hPsi : Psi.conductor = -((t + 1 : ℕ) : ℤ))
    (hbound : multiplicativeConductorExponent F lambda ≤ t + 1 + h)
    (hhigh : 0 < h → IsMultiplicativeConductor F lambda (t + 1 + h)) :
    ∃ Astar : F,
      (∀ z : lattice F (((t + 1 + h) / 2 : ℕ) : ℤ),
        lambda (positiveUnitOfLattice F (normChoice_depths (h := h) hodd ht).1 (-z)) =
          Psi.character (Astar * truncatedLog p (z : F))) ∧
      (0 < h → ord F Astar = ((-(h : ℤ) : ℤ) : WithTop ℤ)) ∧
      (h = 0 → Astar ∈ lattice F 0) ∧
      (QuasiCharTrivialOnUnitFiltration F lambda ((t + 1 + h) / 2) → Astar = 0) := by
  let d := (t + 1 + h) / 2
  have hd := (normChoice_depths (h := h) hodd ht).1
  have hlog := (normChoice_depths (h := h) hodd ht).2.2
  let theta := canonicalLocalQuasiCharData F lambda
  have hn : theta.conductor ≤ t + 1 + h := hbound
  by_cases hsmall : theta.conductor ≤ d
  · have htriv := theta.isConductor.trivialOnUnitFiltration_iff.2 hsmall
    refine ⟨0, ?_, ?_, by simp, fun _ => rfl⟩
    · intro z
      simpa only [theta, canonicalLocalQuasiCharData, zero_mul,
        Psi.character.map_zero_eq_one] using
        htriv _ (positiveUnitOfLattice F hd (-z)).property
    · intro hh
      have heq := theta.isConductor.unique (hhigh hh)
      have := (normChoice_depths (h := h) hodd ht).2.1
      dsimp only [d] at hsmall
      omega
  · have hdn : d + 1 ≤ theta.conductor := by omega
    obtain ⟨A, hA, _⟩ := enhancedCoefficient_exists_unique_mod F theta Psi p d
      ((t + 1 : ℕ) : ℤ) hchar hp hd (by omega) (hn.trans hlog)
      (by rw [hPsi, neg_neg]) (by omega) hdn
    refine ⟨(A : F), hA.2, ?_, ?_, ?_⟩
    · intro hh
      have heq := theta.isConductor.unique (hhigh hh)
      have ho := hA.1
      rw [heq] at ho
      have he : ((t + 1 : ℕ) : ℤ) - ((t + 1 + h : ℕ) : ℤ) = -(h : ℤ) := by
        omega
      rwa [he] at ho
    · intro hh
      have hn' : (theta.conductor : ℤ) ≤ ((t + 1 : ℕ) : ℤ) := by
        exact_mod_cast (show theta.conductor ≤ t + 1 by omega)
      rw [mem_lattice, hA.1]
      exact_mod_cast (show (0 : ℤ) ≤ ((t + 1 : ℕ) : ℤ) - theta.conductor by omega)
    · intro htriv
      exact (hsmall (theta.isConductor.trivialOnUnitFiltration_iff.1 htriv)).elim

/-- A change in the whole coefficient ambiguity preserves every value of
the full logarithm chart. This does not use a single test value. -/
theorem normChoice_chart_congruent
    {p d : ℕ} (hchar : residueCharacteristic F = p) (hd : 0 < d)
    (Psi : LocalAddCharData F) {J : ℤ} (hJ : J = -Psi.conductor)
    {a b : F} (hab : a - b ∈ lattice F (J - (d : ℤ)))
    (z : lattice F (d : ℤ)) :
    Psi.character (a * truncatedLog p (z : F)) =
      Psi.character (b * truncatedLog p (z : F)) := by
  have hP : truncatedLog p (z : F) ∈ lattice F (d : ℤ) :=
    (truncatedLogOnLattice F p d hchar hd z).property
  have hprod : (a - b) * truncatedLog p (z : F) ∈ lattice F J := by
    simpa only [sub_add_cancel] using mul_mem_lattice F hab hP
  apply div_eq_one.mp
  calc
    _ = Psi.character ((a - b) * truncatedLog p (z : F)) := by
      rw [sub_mul]
      exact (Psi.character.toAddChar.map_sub_eq_div _ _).symm
    _ = 1 := Psi.isConductor.trivial _ (hJ ▸ hprod)

end Coefficient

section NormApproximation
variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

/-- FML supplies a norm at relative precision `t`, simultaneously retaining
both exact orders. For the enhanced class this suffices precisely below
`h = t`; at the endpoint its absolute error is only integral. -/
theorem normChoice_approximation
    {t h : ℕ} (htpos : 0 < t) (_hh : h ≤ t)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1)
    (Astar : F)
    (horder : 0 < h → ord F Astar = ((-(h : ℤ) : ℤ) : WithTop ℤ))
    (hintegral : h = 0 → Astar ∈ lattice F 0) :
    ∃ x : E,
      (h < t → Astar - norm F E x ∈
        lattice F (((t + 1 : ℕ) : ℤ) - ((t + 1 + h) / 2 : ℕ))) ∧
      (h = t → Astar - norm F E x ∈ lattice F 0) ∧
      (0 < h → ord E x = ((-(h : ℤ) : ℤ) : WithTop ℤ) ∧
        ord F (norm F E x) = ((-(h : ℤ) : ℤ) : WithTop ℤ)) ∧
      (h = 0 → x ∈ lattice E 0) ∧
      (Astar = 0 → x = 0) := by
  by_cases hz : Astar = 0
  · have hhzero : h = 0 := by
      by_contra hn
      have ho := horder (by omega)
      rw [hz, ord_zero] at ho
      exact WithTop.coe_ne_top ho.symm
    subst Astar
    refine ⟨0, ?_, ?_, ?_, by simp, fun _ => rfl⟩
    · intro _
      simp [LanglandsFirstMainLemma.norm, Algebra.norm_zero]
    · intro he
      omega
    · intro hpos
      omega
  · let a := unitOrder F (Units.mk0 Astar hz)
    have ha : ord F Astar = (a : WithTop ℤ) :=
      ord_coe_eq_unitOrder F (Units.mk0 Astar hz)
    have ha_high : 0 < h → a = -(h : ℤ) := by
      intro hpos
      exact WithTop.coe_inj.mp (ha.symm.trans (horder hpos))
    have ha_zero : h = 0 → 0 ≤ a := by
      intro he
      have ha0 := hintegral he
      rw [mem_lattice, ha] at ha0
      exact_mod_cast ha0
    obtain ⟨pi, hpi, hgen⟩ :=
      exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one F E hres
    obtain ⟨x, hx⟩ := normRepresentative_all_subcriticalPrecisions F E ht hres
      pi hpi hgen (Units.mk0 Astar hz) ha
    have hx := hx t le_rfl
    refine ⟨(x : E), ?_, ?_, ?_, ?_, fun he => (hz he).elim⟩
    · intro hlt
      apply lattice_antitone F _ hx.norm_congruent
      by_cases hhzero : h = 0
      · have := ha_zero hhzero
        have hd : 1 ≤ (t + 1 + h) / 2 := by omega
        omega
      · have := ha_high (by omega)
        omega
    · intro he
      have := ha_high (by omega)
      apply lattice_antitone F _ hx.norm_congruent
      omega
    · intro hpos
      rw [hx.source_order, hx.norm_order, ha_high hpos]
      exact ⟨rfl, rfl⟩
    · intro he
      rw [mem_lattice, hx.source_order]
      exact_mod_cast ha_zero he

/-- Lemma 6.8 (`O:I:chooseA`) for the actual common twist's conductor
hypotheses. The exact norm is `A = norm F E x`. Its coefficient in the
full character chart is `A + epsilon`; `epsilon = 0` below the boundary,
whereas the boundary retains the integral error. The zero coefficient
class is realized by `x = A = 0`.

Only the totally ramified edge is needed here. The conductor hypotheses
are supplied by `ActualTwist`, so no norm representative or chart is an
unproved input. Both field characteristics and nonunitary characters are
allowed. -/
theorem normChoice
    {p t h : ℕ} (hp : p.Prime) (hodd : 2 < p) (htpos : 0 < t) (hh : h ≤ t)
    (hchar : residueCharacteristic F = p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1)
    (lambda : ContinuousQuasiChar F) (Psi : LocalAddCharData F)
    (hPsi : Psi.conductor = -((t + 1 : ℕ) : ℤ))
    (hbound : multiplicativeConductorExponent F lambda ≤ t + 1 + h)
    (hhigh : 0 < h → IsMultiplicativeConductor F lambda (t + 1 + h)) :
    ∃ (x : E) (epsilon : F),
      epsilon ∈ lattice F 0 ∧
      (h < t → epsilon = 0) ∧
      (∀ z : lattice F (((t + 1 + h) / 2 : ℕ) : ℤ),
        lambda (positiveUnitOfLattice F (normChoice_depths hodd htpos).1 (-z)) =
          Psi.character ((norm F E x + epsilon) * truncatedLog p (z : F))) ∧
      (0 < h → ord E x = ((-(h : ℤ) : ℤ) : WithTop ℤ) ∧
        ord F (norm F E x) = ((-(h : ℤ) : ℤ) : WithTop ℤ)) ∧
      (h = 0 → x ∈ lattice E 0) ∧
      (QuasiCharTrivialOnUnitFiltration F lambda ((t + 1 + h) / 2) →
        x = 0 ∧ norm F E x = 0 ∧ epsilon = 0) := by
  obtain ⟨Astar, hchart, horder, hintegral, hzero⟩ :=
    normChoice_coefficient F hp hodd htpos hchar lambda Psi hPsi hbound hhigh
  obtain ⟨x, hsub, hboundary, hxorder, hxintegral, hxzero⟩ :=
    normChoice_approximation F E htpos hh ht hres Astar horder hintegral
  by_cases hlt : h < t
  · refine ⟨x, 0, by simp, fun _ => rfl, ?_, hxorder, hxintegral, ?_⟩
    · intro z
      rw [add_zero, hchart]
      exact normChoice_chart_congruent F hchar (normChoice_depths hodd htpos).1
        Psi (by rw [hPsi, neg_neg]) (hsub hlt) z
    · intro htriv
      have hx0 := hxzero (hzero htriv)
      simp [hx0, LanglandsFirstMainLemma.norm, Algebra.norm_zero]
  · have he : h = t := by omega
    refine ⟨x, Astar - norm F E x, hboundary he, fun hlt' => (hlt hlt').elim,
      ?_, hxorder, hxintegral, ?_⟩
    · intro z
      rw [add_sub_cancel, hchart]
    · intro htriv
      have hA0 := hzero htriv
      have hx0 := hxzero hA0
      simp [hA0, hx0, LanglandsFirstMainLemma.norm, Algebra.norm_zero]

end NormApproximation

section ActualPair
variable (F E U K : Type) [Field F] [Field E] [Field U] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F E] [Algebra F U] [Algebra F K] [Algebra E K] [Algebra U K]
  [ValuativeExtension F E] [ValuativeExtension F U] [ValuativeExtension F K]
  [ValuativeExtension U K] [ValuativeExtension E K]
  [Module.Finite F E] [Module.Finite F U] [Module.Finite E K]
  [Module.Finite U K] [Module.Finite F K] [IsGalois F U]
  [PrimeCyclicExtension F E]

/-- Apply Lemma 6.8 directly to the common twist constructed in
`O:I:actualtwist`. The coefficient and norm witness are constructed here;
only the ramification data and the paper's range `h ≤ t` are supplied. -/
theorem ActualTwist.normChoice
    {p t q : ℕ} (hp : p.Prime) (hodd : 2 < p) (htpos : 0 < t)
    (hchar : residueCharacteristic F = p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hres : residueDegree F E = 1)
    {hq : 0 < q} {tau : ContinuousQuasiChar F} (Psi : LocalAddCharData F)
    (hPsi : Psi.conductor = -((t + 1 : ℕ) : ℤ)) {c : F} {d : U}
    {M : CompatibleModels F E U K p (t + 1) q hq tau Psi.character c d}
    {thetaU : ContinuousQuasiChar U} {thetaE : ContinuousQuasiChar E}
    (D : ActualTwist F E U K M thetaU thetaE) (hh : D.h ≤ t) :
    ∃ (x : E) (epsilon : F),
      epsilon ∈ lattice F 0 ∧
      (D.h < t → epsilon = 0) ∧
      (∀ z : lattice F (((t + 1 + D.h) / 2 : ℕ) : ℤ),
        D.lambda (positiveUnitOfLattice F (normChoice_depths hodd htpos).1 (-z)) =
          Psi.character ((norm F E x + epsilon) * truncatedLog p (z : F))) ∧
      (0 < D.h → ord E x = ((-(D.h : ℤ) : ℤ) : WithTop ℤ) ∧
        ord F (norm F E x) = ((-(D.h : ℤ) : ℤ) : WithTop ℤ)) ∧
      (D.h = 0 → x ∈ lattice E 0) ∧
      (QuasiCharTrivialOnUnitFiltration F D.lambda ((t + 1 + D.h) / 2) →
        x = 0 ∧ norm F E x = 0 ∧ epsilon = 0) :=
  UR.normChoice F E hp hodd htpos hh hchar ht hres D.lambda Psi hPsi
    D.lambda_bound D.lambda_high

end ActualPair

end
end LanglandsSecondMainLemma.Odd.UR
