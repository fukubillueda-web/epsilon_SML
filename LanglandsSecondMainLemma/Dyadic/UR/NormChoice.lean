import LanglandsFirstMainLemma.Ramification.NormRepresentatives
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Dyadic.UR.Twist

/-!
# Norm coefficients for the unramified--ramified dyadic pair

Paper Lemma `D:UR:choosex` and equation `D:UR:lambdachart`.
Write `T = t + 1` and `s = (t + h) / 2 + 1 = ceil ((T + h) / 2)`.
The coefficient ambiguity is the integer-depth lattice `p_F^(T-s)`.
FML supplies an actual norm at relative precision at most `t`; multiplying
the error by the entire variable ideal proves preservation of the chart.
The zero class is represented by zero, including when the base twist has
conductor at most `s`.
-/

namespace LanglandsSecondMainLemma.Dyadic.UR

noncomputable section

open LanglandsFirstMainLemma

section NormRepresentative

variable (F E : Type) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

/-- The relative precision is `T-s-a` for a coefficient of order `a`.
It is at most the break, both at positive height and for integral classes.
No surjectivity beyond the subcritical norm theorem is used. -/
private theorem normChoice_representative
    {t h : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (_htpos : 0 < t) (hres : residueDegree F E = 1) (hh : h ≤ t)
    (Astar : F)
    (horder : 0 < h → ord F Astar = ((-(h : ℤ) : ℤ) : WithTop ℤ))
    (hintegral : h = 0 → Astar ∈ lattice F 0) :
    ∃ x : E,
      Astar - norm F E x ∈
        lattice F (((t + 1 : ℕ) : ℤ) - (((t + h) / 2 + 1 : ℕ) : ℤ)) ∧
      (0 < h → ord E x = ((-(h : ℤ) : ℤ) : WithTop ℤ)) ∧
      (h = 0 → x ∈ lattice E 0) ∧
      (Astar ∈ lattice F
        (((t + 1 : ℕ) : ℤ) - (((t + h) / 2 + 1 : ℕ) : ℤ)) → x = 0) := by
  let k : ℤ := ((t + 1 : ℕ) : ℤ) - (((t + h) / 2 + 1 : ℕ) : ℤ)
  have hk : 0 ≤ k := by dsimp [k]; omega
  by_cases hzero : Astar ∈ lattice F k
  · refine ⟨0, ?_, ?_, ?_, fun _ => rfl⟩
    · simpa only [LanglandsFirstMainLemma.norm, Algebra.norm_zero, sub_zero] using hzero
    · intro hpos
      have hbound := (mem_lattice F).1 hzero
      rw [horder hpos, WithTop.coe_le_coe] at hbound
      omega
    · intro _
      exact (lattice E 0).zero_mem
  · have hne : Astar ≠ 0 := by
      intro heq
      apply hzero
      rw [heq]
      exact (lattice F k).zero_mem
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).2 hne)
    have hak : a < k := by
      rw [mem_lattice, ← ha, WithTop.coe_le_coe] at hzero
      omega
    have haorder (hpos : 0 < h) : a = -(h : ℤ) :=
      WithTop.coe_injective (ha.trans (horder hpos))
    have haint (hz : h = 0) : 0 ≤ a := by
      have hmem := (mem_lattice F).1 (hintegral hz)
      rwa [← ha, WithTop.coe_le_coe] at hmem
    have hprecision : k - a ≤ t := by
      by_cases hz : h = 0
      · have := haint hz
        dsimp [k]
        omega
      · have := haorder (by omega)
        dsimp [k]
        omega
    obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
    obtain ⟨x, hx⟩ := normRepresentative_subcritical F E ht hres pi hpi hgen
      (s := (k - a).toNat) (by omega) (Units.mk0 Astar hne) ha.symm
    refine ⟨(x : E), ?_, ?_, ?_, fun hmem => (hzero hmem).elim⟩
    · have heq : a + ((k - a).toNat : ℤ) = k := by omega
      simpa only [Units.val_mk0, heq] using hx.norm_congruent
    · intro hpos
      rw [hx.source_order, haorder hpos]
    · intro hz
      rw [mem_lattice, hx.source_order, WithTop.coe_le_coe]
      exact haint hz

/-- Replace any coefficient in `D:UR:lambdachart` by an actual field norm.
The difference lies in the full stationary ambiguity, and the formula is
preserved at every element of the original ideal. Positive-height orders,
integrality at height zero, and the zero representative are all retained.
Only the ramified edge is needed for this construction. -/
theorem normChoice_of_coefficient
    {t h : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (htpos : 0 < t) (hres : residueDegree F E = 1) (hh : h ≤ t)
    (lambda : ContinuousQuasiChar F) (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (Astar : F)
    (horder : 0 < h → ord F Astar = ((-(h : ℤ) : ℤ) : WithTop ℤ))
    (hintegral : h = 0 → Astar ∈ lattice F 0)
    (hchart : ∀ (z : F) (hz : z ∈ lattice F (((t + h) / 2 + 1 : ℕ) : ℤ)),
      lambda (principalUnitOf F ((t + h) / 2) (-z) (neg_mem_lattice F hz)) =
        Psi (Astar * z)) :
    ∃ x : E,
      Astar - norm F E x ∈
        lattice F (((t + 1 : ℕ) : ℤ) - (((t + h) / 2 + 1 : ℕ) : ℤ)) ∧
      (∀ (z : F) (hz : z ∈ lattice F (((t + h) / 2 + 1 : ℕ) : ℤ)),
        lambda (principalUnitOf F ((t + h) / 2) (-z) (neg_mem_lattice F hz)) =
          Psi (norm F E x * z)) ∧
      (0 < h → ord E x = ((-(h : ℤ) : ℤ) : WithTop ℤ)) ∧
      (h = 0 → x ∈ lattice E 0) ∧
      (Astar ∈ lattice F
        (((t + 1 : ℕ) : ℤ) - (((t + h) / 2 + 1 : ℕ) : ℤ)) → x = 0) := by
  obtain ⟨x, hx, hxo, hxi, hxz⟩ :=
    normChoice_representative F E ht htpos hres hh Astar horder hintegral
  refine ⟨x, hx, ?_, hxo, hxi, hxz⟩
  intro z hz
  rw [hchart z hz]
  have herror : (Astar - norm F E x) * z ∈ lattice F ((t + 1 : ℕ) : ℤ) := by
    simpa only [sub_add_cancel] using mul_mem_lattice F hx hz
  have htrivial : Psi (Astar * z - norm F E x * z) = 1 := by
    apply hPsi.trivial
    simpa only [neg_neg, sub_mul] using herror
  change Psi.toAddChar (Astar * z - norm F E x * z) = 1 at htrivial
  rw [AddChar.map_sub_eq_div] at htrivial
  exact div_eq_one.mp htrivial

end NormRepresentative

section BaseCoefficient

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- FML finite duality constructs the coefficient, with the paper's
minus-sign convention and its exact order. -/
private theorem normChoice_coefficient_at_depth
    (lambda : ContinuousQuasiChar F) (Psi : LocalAddCharData F)
    {m s : ℕ} (hcond : IsMultiplicativeConductor F lambda m)
    (hs : IsLamprechtStationaryDepth m s) :
    ∃ Astar : F,
      ord F Astar = ((-Psi.conductor - (m : ℤ) : ℤ) : WithTop ℤ) ∧
      ∀ z ∈ lattice F (s : ℤ), ∀ B : Fˣ, (B : F) = 1 - z →
        lambda B = Psi.character (Astar * z) := by
  let chi : LocalQuasiCharData F := ⟨lambda, m, hcond⟩
  have hGamma : ord F ((1 : Fˣ) : F) =
      ((-Psi.conductor + Psi.conductor : ℤ) : WithTop ℤ) := by simp
  obtain ⟨c, hc⟩ := latticeQuotientMk_surjective F
    (sub_le_sub_left hs.int_le_conductor (-Psi.conductor))
    (stationaryNumeratorClass F chi Psi (-Psi.conductor) hs 1 hGamma)
  refine ⟨-(c : F), ?_, ?_⟩
  · rw [ord_neg]
    exact stationaryNumeratorClass_representative_ord
      F chi Psi (-Psi.conductor) hs 1 hGamma c hc
  · intro z hz B hB
    let v : lattice F (s : ℤ) := ⟨-z, neg_mem_lattice F hz⟩
    have hlin := stationaryNumeratorClass_linearization
      F chi Psi (-Psi.conductor) hs 1 hGamma c hc v
    have hunit : (positiveUnitOfLattice F hs.pos v : Fˣ) = B := by
      apply Units.ext
      simp only [coe_positiveUnitOfLattice, v, hB, sub_eq_add_neg]
    rw [hunit] at hlin
    change lambda B = Psi.character ((c : F) * (-z) / 1) at hlin
    simpa only [div_one, mul_neg, neg_mul] using hlin

/-- Construct `Astar` from exactly the base-conductor conclusions of
`twist`. If the chart is trivial, select the zero coefficient. -/
private theorem normChoice_baseCoefficient
    {t h : ℕ} (htpos : 0 < t)
    (lambda : ContinuousQuasiChar F) (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (hcondpos : 0 < h → IsMultiplicativeConductor F lambda (t + 1 + h))
    (hcondzero : h = 0 → multiplicativeConductorExponent F lambda ≤ t + 1) :
    ∃ Astar : F,
      (0 < h → ord F Astar = ((-(h : ℤ) : ℤ) : WithTop ℤ)) ∧
      (h = 0 → Astar ∈ lattice F 0) ∧
      (∀ (z : F) (hz : z ∈ lattice F (((t + h) / 2 + 1 : ℕ) : ℤ)),
        lambda (principalUnitOf F ((t + h) / 2) (-z) (neg_mem_lattice F hz)) =
          Psi (Astar * z)) ∧
      (QuasiCharTrivialOnUnitFiltration F lambda ((t + h) / 2 + 1) → Astar = 0) := by
  let m := multiplicativeConductorExponent F lambda
  have hm : IsMultiplicativeConductor F lambda m :=
    multiplicativeConductorExponent_isConductor F lambda
  have hmpos (hpos : 0 < h) : m = t + 1 + h := hm.unique (hcondpos hpos)
  have hmbound : m ≤ t + 1 + h := by
    by_cases hz : h = 0
    · have := hcondzero hz
      dsimp [m]
      omega
    · rw [hmpos (by omega)]
  by_cases hsmall : m ≤ (t + h) / 2 + 1
  · refine ⟨0, ?_, fun _ => (lattice F 0).zero_mem, ?_, fun _ => rfl⟩
    · intro hpos
      have := hmpos hpos
      omega
    · intro z hz
      rw [zero_mul]
      have hvalue := hm.trivial _ (unitFiltration_antitone F hsmall
        (principalUnitOf_mem F ((t + h) / 2) (-z) (neg_mem_lattice F hz)))
      simpa using hvalue
  · have hs : IsLamprechtStationaryDepth m ((t + h) / 2 + 1) :=
      ⟨by omega, by omega, by omega⟩
    let psi : LocalAddCharData F := ⟨Psi, -((t + 1 : ℕ) : ℤ), hPsi⟩
    obtain ⟨Astar, hA, hchart⟩ := normChoice_coefficient_at_depth F lambda psi hm hs
    have hA' : ord F Astar = ((((t + 1 : ℕ) : ℤ) - (m : ℤ) : ℤ) : WithTop ℤ) := by
      simpa only [psi, neg_neg] using hA
    refine ⟨Astar, ?_, ?_, ?_, ?_⟩
    · intro hpos
      rw [hA', hmpos hpos]
      congr 1
      omega
    · intro hz
      rw [mem_lattice, hA', WithTop.coe_le_coe]
      have := hcondzero hz
      dsimp [m]
      omega
    · intro z hz
      exact hchart z hz _ (by simp only [coe_principalUnitOf, sub_eq_add_neg])
    · intro htrivial
      exact (hsmall (hm.minimal _ htrivial)).elim

end BaseCoefficient

section Choice

variable (F E : Type) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

/-- **Paper Lemma `D:UR:choosex`.** From the actual base twist and its
conductor bounds, construct a field element whose exact norm is a
coefficient on the entire half-conductor ideal. Its order is `-h` when
`h > 0`, and it is integral at `h = 0`. The zero coefficient class is
represented by `x = 0`.

The input conductor bounds are the conclusions of `twist`. The initial
coefficient is constructed by FML stationary duality, and preservation
under the norm choice is proved by `normChoice_of_coefficient`. This
local construction needs only the ramified edge; neither a characteristic
assumption nor unitarity is used. -/
theorem normChoice
    {t h : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (htpos : 0 < t) (hres : residueDegree F E = 1) (hh : h ≤ t)
    (lambda : ContinuousQuasiChar F) (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (hcondpos : 0 < h → IsMultiplicativeConductor F lambda (t + 1 + h))
    (hcondzero : h = 0 → multiplicativeConductorExponent F lambda ≤ t + 1) :
    ∃ x : E,
      (∀ (z : F) (hz : z ∈ lattice F (((t + h) / 2 + 1 : ℕ) : ℤ)),
        lambda (principalUnitOf F ((t + h) / 2) (-z) (neg_mem_lattice F hz)) =
          Psi (norm F E x * z)) ∧
      (0 < h → ord E x = ((-(h : ℤ) : ℤ) : WithTop ℤ)) ∧
      (h = 0 → x ∈ lattice E 0) ∧
      (QuasiCharTrivialOnUnitFiltration F lambda ((t + h) / 2 + 1) → x = 0) := by
  obtain ⟨Astar, hAo, hAi, hchart, hAz⟩ :=
    normChoice_baseCoefficient F htpos lambda Psi hPsi hcondpos hcondzero
  obtain ⟨x, _, hxchart, hxo, hxi, hxz⟩ :=
    normChoice_of_coefficient F E ht htpos hres hh lambda Psi hPsi Astar hAo hAi hchart
  refine ⟨x, hxchart, hxo, hxi, ?_⟩
  intro hzero
  apply hxz
  rw [hAz hzero]
  exact (lattice F _).zero_mem

end Choice

end

end LanglandsSecondMainLemma.Dyadic.UR
