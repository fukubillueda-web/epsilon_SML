import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Dyadic.UR.Coefficients
import LanglandsSecondMainLemma.Stationary.CommonOrigin
import LanglandsSecondMainLemma.Dyadic.UR.OddConductor

/-!
# Dyadic / UR / Minimal Origin

Paper `D:UR:BCdefs`, `D:UR:ZU`, `D:UR:ZE`, `D:UR:Sidentity`, and the
elementary part of `D:UR:minimal`. All norms and traces below are actual
field operations. The same integral representative supplied by `normChoice`
is retained, including the possible value zero.
-/

namespace LanglandsSecondMainLemma.Dyadic.UR

noncomputable section
open LanglandsFirstMainLemma

section QuadraticAlgebra
variable (F L : Type*) [Field F] [Field L] [Algebra F L]
  [Module.Finite F L] [IsGalois F L]

/-- The two conjugates, used together for the exact trace and norm formulas. -/
private theorem minimal_conjugates (hdegree : Module.finrank F L = 2)
    (sigma : Gal(L/F)) (hsigma : sigma ≠ 1) (x : L) :
    algebraMap F L (trace F L x) = x + sigma x ∧
      algebraMap F L (norm F L x) = x * sigma x := by
  classical
  have hcard : Fintype.card Gal(L/F) = 2 := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, hdegree]
  have huniv : ({sigma, (1 : Gal(L/F))} : Finset Gal(L/F)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simpa using hsigma),
      Finset.card_singleton, hcard]
  rw [trace_eq_sum_automorphisms, Algebra.norm_eq_prod_automorphisms, ← huniv]
  simp [hsigma, add_comm, mul_comm]

/-- The quadratic equation of every element, with no division by two. -/
private theorem minimal_quadratic_relation (hdegree : Module.finrank F L = 2)
    (x : L) :
    x ^ 2 - algebraMap F L (trace F L x) * x + algebraMap F L (norm F L x) = 0 := by
  classical
  obtain ⟨sigma, hsigma⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, hdegree]; omega)
    (1 : Gal(L/F))
  obtain ⟨htrace, hnorm⟩ := minimal_conjugates F L hdegree sigma hsigma x
  rw [htrace, hnorm]
  ring

/-- The norm of a translated element; the translating scalar may be zero. -/
private theorem minimal_norm_add (hdegree : Module.finrank F L = 2)
    (x : L) (a : F) :
    norm F L (x + algebraMap F L a) = norm F L x + a * trace F L x + a ^ 2 := by
  classical
  obtain ⟨sigma, hsigma⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, hdegree]; omega)
    (1 : Gal(L/F))
  apply (algebraMap F L).injective
  rw [(minimal_conjugates F L hdegree sigma hsigma _).2]
  simp only [map_add, map_mul, map_pow, sigma.commutes]
  rw [(minimal_conjugates F L hdegree sigma hsigma x).1,
    (minimal_conjugates F L hdegree sigma hsigma x).2]
  ring

private theorem minimal_trace_square (hdegree : Module.finrank F L = 2) (x : L) :
    trace F L (x ^ 2) = trace F L x ^ 2 - 2 * norm F L x := by
  classical
  obtain ⟨sigma, hsigma⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, hdegree]; omega)
    (1 : Gal(L/F))
  apply (algebraMap F L).injective
  rw [(minimal_conjugates F L hdegree sigma hsigma _).1]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  rw [(minimal_conjugates F L hdegree sigma hsigma x).1,
    (minimal_conjugates F L hdegree sigma hsigma x).2]
  ring

/-- The exact lower norm in `D:UR:Wdefs`. -/
private theorem minimal_norm_one_double (hdegree : Module.finrank F L = 2) (x : L) :
    norm F L (2 * x + 1) = 1 + 2 * trace F L x + 4 * norm F L x := by
  have hn : norm F L (2 : L) = (4 : F) := by
    have h := LanglandsFirstMainLemma.norm_algebraMap F L (2 : F)
    simpa only [map_ofNat, hdegree, show (2 : F) ^ 2 = 4 by ring] using h
  have ht : trace F L (2 * x) = 2 * trace F L x := by
    simpa only [Algebra.smul_def, map_ofNat] using (trace F L).map_smul (2 : F) x
  have h := minimal_norm_add F L hdegree (2 * x) 1
  simp only [map_one, one_mul, one_pow, map_mul, hn, ht] at h
  rw [h]
  ring

end QuadraticAlgebra

section Lattices
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- A positive-depth perturbation preserves order zero. -/
private theorem minimal_order_zero {r : ℤ} (hr : 0 < r) {B Z : L}
    (hB : ord L B = 0) (herror : Z - B ∈ lattice L r) : ord L Z = 0 := by
  have hpos : (0 : WithTop ℤ) < ord L (Z - B) :=
    (WithTop.coe_lt_coe.mpr hr).trans_le ((mem_lattice L).mp herror)
  have hne : ord L (Z - B) ≠ ord L B := by rw [hB]; exact ne_of_gt hpos
  have heq := ord_add_eq_min L hne
  simpa only [sub_add_cancel, hB, min_eq_right hpos.le] using heq

/-- Changing a coefficient by the full annihilator ideal preserves its
entire stationary chart, not just one character value. -/
private theorem minimal_stationary
    (theta : LocalQuasiCharData L) (Psi : LocalAddCharData L)
    {t : ℕ} (ht : 0 < t) (hm : theta.conductor = t + 1)
    (hPsi : Psi.conductor = -((t + 1 : ℕ) : ℤ))
    (B : L) (Z : Lˣ) (hB : ord L B = 0)
    (hchart : ∀ (z : L) (hz : z ∈ lattice L ((t / 2 + 1 : ℕ) : ℤ)),
      theta.character (principalUnitOf L (t / 2) (-z) (neg_mem_lattice L hz)) =
        Psi.character (B * z))
    (herror : (Z : L) - B ∈ lattice L (((t + 1) / 2 : ℕ) : ℤ)) :
    Stationary.IsOrdinaryStationaryCoefficient L theta Psi Z (by omega) := by
  have hord : ord L (Z : L) = 0 := minimal_order_zero L (by omega) hB herror
  refine ⟨?_, ?_⟩
  · simpa [hm, hPsi] using hord
  · intro z
    have hdepth : theta.conductor / 2 + theta.conductor % 2 = t / 2 + 1 := by omega
    have hz : (z : L) ∈ lattice L ((t / 2 + 1 : ℕ) : ℤ) := by
      simpa only [hdepth] using z.property
    have hunit : positiveUnitOfLattice L (show 0 < theta.conductor / 2 +
        theta.conductor % 2 by omega) (-z) =
        principalUnitOf L (t / 2) (-(z : L)) (neg_mem_lattice L hz) := by
      apply Units.ext
      simp only [coe_positiveUnitOfLattice, Submodule.coe_neg, coe_principalUnitOf]
    rw [hunit, hchart _ hz]
    have htriv : Psi.character (((Z : L) - B) * (z : L)) = 1 := by
      apply Psi.isConductor.trivial
      rw [hPsi, neg_neg]
      exact lattice_antitone L (by omega) (mul_mem_lattice L herror hz)
    have heq : (Z : L) * (z : L) = B * (z : L) + ((Z : L) - B) * (z : L) := by ring
    rw [heq, ContinuousAddChar.map_add_eq_mul, htriv, mul_one]

end Lattices

section RamifiedEstimates
variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

/-- Integral traces and the trace of one give both bounds in the local ledger.
The order of two is allowed to be infinite. -/
private theorem minimal_integral_trace
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hdegree : Module.finrank F E = 2)
    (x : E) (hx : x ∈ lattice E 0) :
    trace F E x ∈ lattice F (((t + 1) / 2 : ℕ) : ℤ) ∧
      (2 : F) ∈ lattice F (((t + 1) / 2 : ℕ) : ℤ) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have htrace (y : E) (hy : y ∈ lattice E 0) :
      trace F E y ∈ lattice F (((t + 1) / 2 : ℕ) : ℤ) := by
    have hmap : trace F E y ∈
        Submodule.map ((trace F E).restrictScalars (ringOfIntegers F))
          ((lattice E 0).restrictScalars (ringOfIntegers F)) :=
      Submodule.mem_map.mpr ⟨y, hy, rfl⟩
    rw [cyclicPrime_trace_lattice_image_eq F E ht hres pi hpi hgen, hdegree] at hmap
    simpa using hmap
  refine ⟨htrace x hx, ?_⟩
  have hone := htrace 1 (by simp)
  rw [← map_one (algebraMap F E), trace_algebraMap, hdegree] at hone
  simpa using hone

private theorem minimal_ramified_additive
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hdegree : Module.finrank F E = 2)
    (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ))) :
    IsAdditiveConductor E (tracePullbackAddChar F E Psi) (-((t + 1 : ℕ) : ℤ)) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have h := additiveConductor_compTrace_cyclicPrime F E ht hres pi hpi hgen hPsi
  rw [hdegree] at h
  have heq : (2 : ℤ) * (-((t + 1 : ℕ) : ℤ)) +
      (((2 - 1) * (t + 1) : ℕ) : ℤ) = -((t + 1 : ℕ) : ℤ) := by
    norm_num
    omega
  exact heq ▸ h

end RamifiedEstimates

section Diamond
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  (U E : IntermediateField F K)
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeExtension F U] [ValuativeExtension U K]
  [ValuativeExtension F E] [ValuativeExtension E K]

/-- The actual height-zero origin, together with its canonical trace characters
and the full stationary assertions. `dyadicUR_minimal_origin` constructs this
record from the model and twist charts; its fields are not extra assumptions
on the primitive pair. -/
structure MinimalOriginData (c : F) (d : U) (x : E) (t : ℕ)
    (thetaU : LocalQuasiCharData U) (thetaE : LocalQuasiCharData E)
    (Psi : ContinuousAddChar F) where
  origin : Kˣ
  origin_eq : (origin : K) = (x : K) + (d : K)
  psiU : LocalAddCharData U
  psiE : LocalAddCharData E
  psiU_character : psiU.character = tracePullbackAddChar F U Psi
  psiE_character : psiE.character = tracePullbackAddChar F E Psi
  psiU_conductor : psiU.conductor = -((t + 1 : ℕ) : ℤ)
  psiE_conductor : psiE.conductor = -((t + 1 : ℕ) : ℤ)
  largeU : 1 < thetaU.conductor
  largeE : 1 < thetaE.conductor
  d_trace : trace F U d = 1
  d_norm : norm F U d = -c
  normU_eq : norm U K (origin : K) = algebraMap F U (norm F E x) +
    algebraMap F U (trace F E x) * d + d ^ 2
  normE_eq : norm E K (origin : K) = x ^ 2 + x - algebraMap F E c
  traceU_eq : trace U K (origin : K) = algebraMap F U (trace F E x) + 2 * d
  traceE_eq : trace E K (origin : K) = 2 * x + 1
  errorU : norm U K (origin : K) - (algebraMap F U (norm F E x) + d ^ 2) ∈
    lattice U (((t + 1) / 2 : ℕ) : ℤ)
  errorE : norm E K (origin : K) -
      (algebraMap F E (norm F E x) - x + algebraMap F E c) ∈
    lattice E (2 * (((t + 1) / 2 : ℕ) : ℤ))
  stationaryU : Stationary.IsOrdinaryStationaryCoefficient U thetaU psiU
    (normUnits U K origin) largeU
  stationaryE : Stationary.IsOrdinaryStationaryCoefficient E thetaE psiE
    (normUnits E K origin) largeE

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] [IsGalois F K]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeExtension F U] [ValuativeExtension U K]
  [ValuativeExtension F E] [ValuativeExtension E K] in
private theorem minimal_disjoint
    (hK : Module.finrank F K = 4) (hU : Module.finrank F U = 2)
    (hE : Module.finrank F E = 2) (hsup : U ⊔ E = ⊤) : U.LinearDisjoint E := by
  apply IntermediateField.LinearDisjoint.of_finrank_sup
  rw [hsup, IntermediateField.finrank_top', hK, hU, hE]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeExtension F U] [ValuativeExtension U K]
  [ValuativeExtension F E] [ValuativeExtension E K] in
/-- The four exact upper formulas follow by base change in the actual diamond. -/
private theorem minimal_upper_formulas
    (hK : Module.finrank F K = 4) (hU : Module.finrank F U = 2)
    (hE : Module.finrank F E = 2) (hsup : U ⊔ E = ⊤)
    (c : F) (d : U) (x : E)
    (hdtrace : trace F U d = 1) (hdnorm : norm F U d = -c) :
    let C : K := (x : K) + (d : K)
    norm U K C = algebraMap F U (norm F E x) +
        algebraMap F U (trace F E x) * d + d ^ 2 ∧
    norm E K C = x ^ 2 + x - algebraMap F E c ∧
    trace U K C = algebraMap F U (trace F E x) + 2 * d ∧
    trace E K C = 2 * x + 1 := by
  have hdisj := minimal_disjoint U E hK hU hE hsup
  have hsup' : E ⊔ U = ⊤ := sup_comm U E ▸ hsup
  have hUK : Module.finrank U K = 2 := (hdisj.finrank_left_eq_finrank hsup).trans hE
  have hEK : Module.finrank E K = 2 := (hdisj.symm.finrank_left_eq_finrank hsup').trans hU
  have hnx : norm U K (x : K) = algebraMap F U (norm F E x) :=
    hdisj.norm_algebraMap hsup x
  have htx : trace U K (x : K) = algebraMap F U (trace F E x) :=
    hdisj.trace_algebraMap hsup x
  have hnd : norm E K (d : K) = -algebraMap F E c := by
    rw [show norm E K (d : K) = algebraMap F E (norm F U d) from
      hdisj.symm.norm_algebraMap hsup' d, hdnorm, map_neg]
  have htd : trace E K (d : K) = 1 := by
    rw [show trace E K (d : K) = algebraMap F E (trace F U d) from
      hdisj.symm.trace_algebraMap hsup' d, hdtrace, map_one]
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hn := minimal_norm_add U K hUK (x : K) d
    simp only [IntermediateField.algebraMap_apply] at hn
    rw [hn, hnx, htx]
    ring
  · have hn := minimal_norm_add E K hEK (d : K) x
    simp only [IntermediateField.algebraMap_apply] at hn
    rw [add_comm (x : K), hn, hnd, htd]
    ring
  · rw [map_add, htx, show trace U K (d : K) = Module.finrank U K • d from
      trace_algebraMap U K d, hUK, two_smul]
    ring
  · rw [map_add, htd, show trace E K (x : K) = Module.finrank E K • x from
      trace_algebraMap E K x, hEK, two_smul]
    ring

variable [PrimeCyclicExtension F E]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] [ValuativeExtension U K] [ValuativeExtension E K] in
/-- The errors have the paper's respective depths `floor(T/2)` and
`2*floor(T/2)`. In particular, equality at the unramified ambiguity boundary
is retained in both parities. -/
private theorem minimal_errors
    (hunr : ramificationIndex F U = 1)
    (hE : Module.finrank F E = 2) {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hres : residueDegree F E = 1)
    (c : F) (hc : c ∈ lattice F 0) (d : U) (hd : d ∈ lattice U 0)
    (x : E) (hx : x ∈ lattice E 0) :
    algebraMap F U (trace F E x) * d ∈ lattice U (((t + 1) / 2 : ℕ) : ℤ) ∧
    (x ^ 2 + x - algebraMap F E c) -
        (algebraMap F E (norm F E x) - x + algebraMap F E c) ∈
      lattice E (2 * (((t + 1) / 2 : ℕ) : ℤ)) := by
  let r : ℤ := (((t + 1) / 2 : ℕ) : ℤ)
  have hram : ramificationIndex F E = 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa only [hE, hres, mul_one] using h.symm
  obtain ⟨hb, htwo⟩ := minimal_integral_trace F E ht hres hE x hx
  have hbU : algebraMap F U (trace F E x) ∈ lattice U r := by
    rwa [mem_lattice, ord_algebraMap, hunr, one_nsmul, ← mem_lattice]
  have hmap {a : F} {j : ℤ} (ha : a ∈ lattice F j) :
      algebraMap F E a ∈ lattice E (2 * j) := by
    rw [mem_lattice, ord_algebraMap, hram, two_nsmul]
    simpa only [two_mul, WithTop.coe_add] using
      add_le_add ((mem_lattice F).mp ha) ((mem_lattice F).mp ha)
  have hbE : algebraMap F E (trace F E x) ∈ lattice E (2 * r) := hmap hb
  have htwoE : (2 : E) ∈ lattice E (2 * r) := by simpa only [map_ofNat] using hmap htwo
  have hA : algebraMap F E (norm F E x) ∈ lattice E 0 := by
    apply lattice_antitone E (by omega) (hmap (j := 0) ?_)
    rwa [mem_lattice, ord_norm, hres, one_nsmul, ← mem_lattice]
  have hcE : algebraMap F E c ∈ lattice E 0 := by simpa only [mul_zero] using hmap hc
  have hmul {a z : E} (ha : a ∈ lattice E (2 * r)) (hz : z ∈ lattice E 0) :
      a * z ∈ lattice E (2 * r) := by simpa only [add_zero] using mul_mem_lattice E ha hz
  refine ⟨by simpa only [add_zero] using mul_mem_lattice U hbU hd, ?_⟩
  have heq : (x ^ 2 + x - algebraMap F E c) -
      (algebraMap F E (norm F E x) - x + algebraMap F E c) =
      algebraMap F E (trace F E x) * x - 2 * algebraMap F E (norm F E x) +
        2 * x - 2 * algebraMap F E c := by
    linear_combination minimal_quadratic_relation F E hE x
  rw [heq]
  exact sub_mem_lattice E
    (add_mem_lattice E (sub_mem_lattice E (hmul hbE hx) (hmul htwoE hA))
      (hmul htwoE hx)) (hmul htwoE hcE)

/-- **The minimal common origin** (`D:UR:minimal`, both parities).

The integral `x` and its full base chart are the height-zero conclusions of
`normChoice`. The model charts and the exact actual conductors are supplied
by `models` and `twist`. We apply `coefficients` to those genuine inputs,
then construct the unit `C = x+d` and prove that its literal upper norms are
ordinary stationary coefficients. No stationary common norm is assumed.
The hypothesis `U ⊔ E = ⊤` is the paper's `K = EU`; linear disjointness and
both upper degrees are proved from the actual degree-four diamond. -/
theorem dyadicUR_minimal_origin
    (hK : Module.finrank F K = 4)
    (hunr : ramificationIndex F U = 1)
    (hU : Module.finrank F U = 2) (hE : Module.finrank F E = 2)
    (hsup : U ⊔ E = ⊤)
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (htpos : 0 < t) (hres : residueDegree F E = 1)
    (tau : NormCharacter F E) (htau : tau ≠ 1)
    (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (htauchart : ∀ (z : F) (hz : z ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
      tau.1 (principalUnitOf F (t / 2) (-z) (neg_mem_lattice F hz)) = Psi z)
    (sigma : Gal(U/F)) (hsigma : sigma ≠ 1)
    (c : F) (hc : ord F c = 0) (d : U) (hd : ord U d = 0)
    (hdc : d ^ 2 - d = algebraMap F U c) (hconj : sigma d = 1 - d)
    (chiU : ContinuousQuasiChar U) (chiE : ContinuousQuasiChar E)
    (thetaU : LocalQuasiCharData U) (thetaE : LocalQuasiCharData E)
    (lambda : ContinuousQuasiChar F)
    (hmodelU : ∀ (z : U) (hz : z ∈ lattice U ((t / 2 + 1 : ℕ) : ℤ)),
      chiU (principalUnitOf U (t / 2) (-z) (neg_mem_lattice U hz)) =
        tracePullbackAddChar F U Psi (d ^ 2 * z))
    (hmodelE : ∀ (z : E) (hz : z ∈ lattice E ((t / 2 + 1 : ℕ) : ℤ)),
      chiE (principalUnitOf E (t / 2) (-z) (neg_mem_lattice E hz)) =
        tracePullbackAddChar F E Psi (algebraMap F E c * z))
    (htwistU : thetaU.character = chiU * normQuasiChar F U lambda)
    (htwistE : thetaE.character = chiE * normQuasiChar F E lambda)
    (hcondU : thetaU.conductor = t + 1) (hcondE : thetaE.conductor = t + 1)
    (x : E) (hx : x ∈ lattice E 0)
    (hxchart : ∀ (z : F) (hz : z ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
      lambda (principalUnitOf F (t / 2) (-z) (neg_mem_lattice F hz)) =
        Psi (norm F E x * z)) :
    Nonempty (MinimalOriginData U E c d x t thetaU thetaE Psi) := by
  letI : Algebra.IsQuadraticExtension F U := ⟨hU⟩
  have hcoeff := coefficients F U E hunr hU hE ht htpos hres (h := 0) (by omega)
    tau htau Psi hPsi htauchart c d chiU thetaU.character chiE thetaE.character lambda
    hmodelU hmodelE htwistU htwistE
    (by simpa only [hcondU, add_zero] using thetaU.isConductor)
    (by simpa only [hcondE, mul_zero, add_zero] using thetaE.isConductor)
    x (by simpa only [add_zero] using hxchart) (by omega) (fun _ => hx)
  simp only [Nat.cast_zero, neg_zero, mul_zero, add_zero] at hcoeff
  obtain ⟨hchartU, hchartE, hBU, hBE⟩ := hcoeff
  have hc0 : c ∈ lattice F 0 := by simp only [mem_lattice, hc, WithTop.coe_zero, le_refl]
  have hd0 : d ∈ lattice U 0 := by simp only [mem_lattice, hd, WithTop.coe_zero, le_refl]
  have hdtrace : trace F U d = 1 := by
    apply (algebraMap F U).injective
    rw [(minimal_conjugates F U hU sigma hsigma d).1, hconj, map_one]
    ring
  have hdnorm : norm F U d = -c := by
    apply (algebraMap F U).injective
    rw [(minimal_conjugates F U hU sigma hsigma d).2, hconj, map_neg, ← hdc]
    ring
  obtain ⟨hnU, hnE, htU, htE⟩ :=
    minimal_upper_formulas U E hK hU hE hsup c d x hdtrace hdnorm
  obtain ⟨herrU, herrE⟩ := minimal_errors U E hunr hE ht hres c hc0 d hd0 x hx
  let C0 : K := (x : K) + (d : K)
  have herrorU : norm U K C0 - (algebraMap F U (norm F E x) + d ^ 2) ∈
      lattice U (((t + 1) / 2 : ℕ) : ℤ) := by
    rw [hnU]
    convert herrU using 1
    ring
  have herrorE : norm E K C0 - (algebraMap F E (norm F E x) - x + algebraMap F E c) ∈
      lattice E (2 * (((t + 1) / 2 : ℕ) : ℤ)) := by rwa [hnE]
  have hZ : ord U (norm U K C0) = 0 := minimal_order_zero U (by omega) hBU herrorU
  have hC0 : C0 ≠ 0 := by
    intro hzero
    rw [hzero, show norm U K 0 = 0 from Algebra.norm_zero, ord_zero] at hZ
    exact WithTop.top_ne_coe hZ
  let C : Kˣ := Units.mk0 C0 hC0
  let PsiU : LocalAddCharData U := ⟨tracePullbackAddChar F U Psi, -((t + 1 : ℕ) : ℤ),
    (unramified_additiveConductor_compTrace F U hunr Psi _).mpr hPsi⟩
  let PsiE : LocalAddCharData E := ⟨tracePullbackAddChar F E Psi, -((t + 1 : ℕ) : ℤ),
    minimal_ramified_additive F E ht hres hE Psi hPsi⟩
  refine ⟨{
    origin := C
    origin_eq := rfl
    psiU := PsiU
    psiE := PsiE
    psiU_character := rfl
    psiE_character := rfl
    psiU_conductor := rfl
    psiE_conductor := rfl
    largeU := by omega
    largeE := by omega
    d_trace := hdtrace
    d_norm := hdnorm
    normU_eq := hnU
    normE_eq := hnE
    traceU_eq := htU
    traceE_eq := htE
    errorU := herrorU
    errorE := herrorE
    stationaryU := ?_
    stationaryE := ?_ }⟩
  · exact minimal_stationary U thetaU PsiU htpos hcondU rfl _ (normUnits U K C)
      hBU hchartU herrorU
  · exact minimal_stationary E thetaE PsiE htpos hcondE rfl _ (normUnits E K C)
      hBE hchartE (lattice_antitone E (by omega) herrorE)

/-- The lower trace norm and the elementary sign in odd conductor. Every
coefficient is an actual unit or actual norm, and both additive and
multiplicative conductor data are constructed by the theorem below. -/
structure MinimalOddElementaryData (x : E) (t : ℕ) (tau : NormCharacter F E)
    (Psi : ContinuousAddChar F) (C : Kˣ) where
  e : ℕ
  e_pos : 0 < e
  order_two : ord F (2 : F) = ((e : ℤ) : WithTop ℤ)
  conductor_eq : t + 1 = 2 * e + 1
  traceE_order : ord E (trace E K (C : K)) = 0
  traceE_ne_zero : trace E K (C : K) ≠ 0
  traceU_ne_zero : trace U K (C : K) ≠ 0
  tauData : LocalQuasiCharData F
  tau_character : tauData.character = tau.1
  tau_conductor : tauData.conductor = t + 1
  psiData : LocalAddCharData F
  psi_character : psiData.character = Psi
  psi_conductor : psiData.conductor = -((t + 1 : ℕ) : ℤ)
  large : 1 < tauData.conductor
  lower_eq : (Stationary.commonOriginLowerCoefficient E C traceE_ne_zero : F) =
    1 + 2 * trace F E x + 4 * norm F E x
  lower_error : (Stationary.commonOriginLowerCoefficient E C traceE_ne_zero : F) - 1 ∈
    lattice F (2 * (e : ℤ))
  stationary : Stationary.IsOrdinaryStationaryCoefficient F tauData psiData
    (Stationary.commonOriginLowerCoefficient E C traceE_ne_zero) large
  norm_character_value : tau.1 (Stationary.commonOriginLowerCoefficient E C traceE_ne_zero) = 1
  traceU_phase : (Psi (norm F U (trace U K (C : K))) : ℂ) = -1
  elementary_sign : (-1 : ℂ) ^ (t + 1) * (Psi (norm F U (trace U K (C : K))) : ℂ) = 1

/-- **The odd elementary sign**, `D:UR:Wdefs` and the prefactor in
`D:UR:oddratio`. We apply `oddConductor` to the actual norm character.
The residue condition on `c` is exactly the paper's absolute-trace-one
choice. The lower coefficient is the norm of the nonzero trace of the
already constructed origin. The value `Psi(W_U) = -1` is proved before
combining it with the retained factor `(-1)^T`. -/
theorem dyadicUR_minimal_elementary
    (hU : Module.finrank F U = 2) (hE : Module.finrank F E = 2)
    (hchar : residueCharacteristic F = 2)
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (htpos : 0 < t) (hres : residueDegree F E = 1)
    (tau : NormCharacter F E) (htau : tau ≠ 1)
    (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (htauchart : ∀ (z : F) (hz : z ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
      tau.1 (principalUnitOf F (t / 2) (-z) (neg_mem_lattice F hz)) = Psi z)
    (c : F) (hc : c ∈ lattice F 0)
    (hcTrace : (@absoluteTraceTwo (ResidueField F) _ (ringChar.of_eq hchar))
      (reduce F c hc) = 1)
    (d : U) (x : E) (hx : x ∈ lattice E 0)
    (thetaU : LocalQuasiCharData U) (thetaE : LocalQuasiCharData E)
    (O : MinimalOriginData U E c d x t thetaU thetaE Psi)
    (hodd : Odd (t + 1)) :
    CharZero F ∧ Nonempty (MinimalOddElementaryData U E x t tau Psi O.origin) := by
  letI : Algebra.IsQuadraticExtension F U := ⟨hU⟩
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  obtain ⟨hzero, e, htwo, hT, hphase⟩ :=
    oddConductor F E hchar ht htpos hres hE pi hpi hgen tau htau Psi htauchart hodd
  letI : CharZero F := hzero
  letI : CharP (ResidueField F) 2 := ringChar.of_eq hchar
  letI : Fintype (ResidueField F) := residueFieldFintype F
  have he : 0 < e := by omega
  have hr : (t + 1) / 2 = e := by omega
  obtain ⟨hb, _⟩ := minimal_integral_trace F E ht hres hE x hx
  rw [hr] at hb
  have htwoF : (2 : F) ∈ lattice F (e : ℤ) := by rw [mem_lattice, htwo]
  have hram : ramificationIndex F E = 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa only [hE, hres, mul_one] using h.symm
  have htwoE : (2 : E) ∈ lattice E (2 * (e : ℤ)) := by
    rw [mem_lattice, ← map_ofNat (algebraMap F E) 2, ord_algebraMap, hram, htwo]
    norm_cast
  have hPCerror : (2 * x + 1) - 1 ∈ lattice E (2 * (e : ℤ)) := by
    simpa only [add_sub_cancel_right, add_zero] using mul_mem_lattice E htwoE hx
  have hPCorder : ord E (trace E K (O.origin : K)) = 0 := by
    rw [O.traceE_eq]
    exact minimal_order_zero E (by omega) (ord_one E) hPCerror
  have hPCne : trace E K (O.origin : K) ≠ 0 :=
    (ord_ne_top_iff E).mp (by rw [hPCorder]; exact WithTop.coe_ne_top)
  let W : Fˣ := Stationary.commonOriginLowerCoefficient E O.origin hPCne
  have hW : (W : F) = 1 + 2 * trace F E x + 4 * norm F E x := by
    change norm F E (trace E K (O.origin : K)) = _
    rw [O.traceE_eq, minimal_norm_one_double F E hE]
  have hA : norm F E x ∈ lattice F 0 := by
    rwa [mem_lattice, ord_norm, hres, one_nsmul, ← mem_lattice]
  have hfour : (4 : F) ∈ lattice F (2 * (e : ℤ)) := by
    convert mul_mem_lattice F htwoF htwoF using 1 <;> ring
  have hWerror : (W : F) - 1 ∈ lattice F (2 * (e : ℤ)) := by
    rw [hW, show (1 + 2 * trace F E x + 4 * norm F E x) - 1 =
      2 * trace F E x + 4 * norm F E x by ring]
    exact add_mem_lattice F
      (by simpa only [two_mul] using mul_mem_lattice F htwoF hb)
      (by simpa only [add_zero] using mul_mem_lattice F hfour hA)
  let tauData : LocalQuasiCharData F := ⟨tau.1, t + 1,
    ramifiedNormCharacter_conductor F E ht hres pi hpi hgen tau htau⟩
  let psiData : LocalAddCharData F := ⟨Psi, -((t + 1 : ℕ) : ℤ), hPsi⟩
  have hstationary : Stationary.IsOrdinaryStationaryCoefficient F tauData psiData W
      (by dsimp [tauData]; omega) := by
    apply minimal_stationary F tauData psiData htpos rfl rfl 1 W (ord_one F)
    · simpa only [one_mul] using htauchart
    · exact lattice_antitone F (by rw [hr]; omega) hWerror
  have htauW : tau.1 W = 1 :=
    tau.eq_one_on_normRange F E W ⟨Units.mk0 (trace E K (O.origin : K)) hPCne, rfl⟩
  let a : F := trace F E x / 2
  have ha : a ∈ lattice F 0 :=
    (div_mem_lattice_iff F 2 (trace F E x) (e : ℤ) 0 htwo).mpr (by simpa using hb)
  let z : F := a ^ 2 + a - c
  have hz : z ∈ lattice F 0 := sub_mem_lattice F
    (add_mem_lattice F (by simpa only [pow_two, zero_add] using mul_mem_lattice F ha ha) ha) hc
  have h2a : (2 : F) * a = trace F E x := by dsimp only [a]; field_simp
  have hnorm : norm F U (d + algebraMap F U a) = z := by
    rw [minimal_norm_add F U hU, O.d_trace, O.d_norm]
    dsimp only [z]
    ring
  have hQ : trace U K (O.origin : K) =
      algebraMap F U (2 : F) * (d + algebraMap F U a) := by
    rw [O.traceU_eq, mul_add, ← map_mul, h2a, map_ofNat]
    ring
  have hWU : norm F U (trace U K (O.origin : K)) = 4 * z := by
    rw [hQ, map_mul, LanglandsFirstMainLemma.norm_algebraMap, hU, hnorm]
    ring
  have hreduce : reduce F z hz = (reduce F a ha) ^ 2 + reduce F a ha - reduce F c hc := by
    let aO : ringOfIntegers F := ⟨a, (mem_lattice_zero_iff F).mp ha⟩
    let cO : ringOfIntegers F := ⟨c, (mem_lattice_zero_iff F).mp hc⟩
    change residueMap F (aO ^ 2 + aO - cO) =
      (residueMap F aO) ^ 2 + residueMap F aO - residueMap F cO
    simp only [map_sub, map_add, map_pow]
  have htrace : absoluteTraceTwo (ResidueField F) (reduce F z hz) = 1 := by
    rw [hreduce, map_sub, map_add, absoluteTraceTwo_sq, hcTrace,
      CharTwo.add_self_eq_zero, zero_sub, CharTwo.neg_eq]
  have hWUphase : (Psi (norm F U (trace U K (O.origin : K))) : ℂ) = -1 := by
    rw [hWU, hphase z hz, absoluteTraceChar_apply, htrace, ZMod.val_one, pow_one]
  have hQne : trace U K (O.origin : K) ≠ 0 := by
    intro hQzero
    rw [hQzero, show norm F U 0 = 0 from Algebra.norm_zero,
      ContinuousAddChar.map_zero_eq_one, Units.val_one] at hWUphase
    norm_num at hWUphase
  refine ⟨hzero, ⟨{
    e := e
    e_pos := he
    order_two := htwo
    conductor_eq := hT
    traceE_order := hPCorder
    traceE_ne_zero := hPCne
    traceU_ne_zero := hQne
    tauData := tauData
    tau_character := rfl
    tau_conductor := rfl
    psiData := psiData
    psi_character := rfl
    psi_conductor := rfl
    large := by dsimp only [tauData]; omega
    lower_eq := hW
    lower_error := hWerror
    stationary := hstationary
    norm_character_value := htauW
    traceU_phase := hWUphase
    elementary_sign := ?_ }⟩⟩
  rw [hWUphase, hodd.neg_one_pow]
  norm_num

/-- The exact trace difference `D:UR:Sidentity`. This keeps `4c` and the
discriminant term in both field characteristics. -/
theorem MinimalOriginData.trace_difference
    {c : F} {d : U} {x : E} {t : ℕ}
    {thetaU : LocalQuasiCharData U} {thetaE : LocalQuasiCharData E}
    {Psi : ContinuousAddChar F}
    (O : MinimalOriginData U E c d x t thetaU thetaE Psi)
    (hU : Module.finrank F U = 2) (hE : Module.finrank F E = 2) :
    trace F U (norm U K (O.origin : K)) - trace F E (norm E K (O.origin : K)) =
      1 + 4 * c - (trace F E x ^ 2 - 4 * norm F E x) := by
  letI : Algebra.IsQuadraticExtension F U := ⟨hU⟩
  have hbd : trace F U (algebraMap F U (trace F E x) * d) = trace F E x := by
    rw [← Algebra.smul_def, map_smul, O.d_trace, smul_eq_mul, mul_one]
  rw [O.normU_eq, O.normE_eq]
  simp only [map_add, map_sub, hbd, minimal_trace_square F U hU,
    minimal_trace_square F E hE, trace_algebraMap, hU, hE, O.d_trace, O.d_norm,
    two_smul]
  ring

/-- The even elementary prefactor `D:UR:evenratio` equals one. The norm
phase is applied only after proving that the actual trace-zero element
`2x-Tr(x)` belongs to its allowed ideal. This proof includes characteristic
two, where the order of two is infinite. -/
theorem minimal_even_elementary
    (hU : Module.finrank F U = 2) (hE : Module.finrank F E = 2)
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (htpos : 0 < t) (hres : residueDegree F E = 1)
    (tau : NormCharacter F E) (htau : tau ≠ 1)
    (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (htauchart : ∀ (z : F) (hz : z ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
      tau.1 (principalUnitOf F (t / 2) (-z) (neg_mem_lattice F hz)) = Psi z)
    (c : F) (hc : c ∈ lattice F 0) (d : U) (x : E) (hx : x ∈ lattice E 0)
    (thetaU : LocalQuasiCharData U) (thetaE : LocalQuasiCharData E)
    (O : MinimalOriginData U E c d x t thetaU thetaE Psi)
    (heven : Even (t + 1)) :
    (-1 : ℂ) ^ (t + 1) * (Psi (1 -
      (trace F U (norm U K (O.origin : K)) - trace F E (norm E K (O.origin : K)))) : ℂ) = 1 := by
  let r : ℤ := (((t + 1) / 2 : ℕ) : ℤ)
  have hT : (t + 1 : ℤ) = 2 * r := by
    obtain ⟨k, hk⟩ := heven
    dsimp only [r]
    omega
  have hram : ramificationIndex F E = 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa only [hE, hres, mul_one] using h.symm
  obtain ⟨hb, htwo⟩ := minimal_integral_trace F E ht hres hE x hx
  have hmap {a : F} (ha : a ∈ lattice F r) :
      algebraMap F E a ∈ lattice E (2 * r) := by
    rw [mem_lattice, ord_algebraMap, hram, two_nsmul]
    simpa only [two_mul, WithTop.coe_add] using
      add_le_add ((mem_lattice F).mp ha) ((mem_lattice F).mp ha)
  have htwoE : (2 : E) ∈ lattice E (2 * r) := by simpa only [map_ofNat] using hmap htwo
  let y : E := 2 * x - algebraMap F E (trace F E x)
  let D : F := trace F E x ^ 2 - 4 * norm F E x
  have hy : y ∈ lattice E (2 * r) := sub_mem_lattice E
    (by simpa only [add_zero] using mul_mem_lattice E htwoE hx) (hmap hb)
  have hytrace : trace F E y = 0 := by
    have hdouble : trace F E (2 * x) = 2 * trace F E x := by
      simpa only [Algebra.smul_def, map_ofNat] using (trace F E).map_smul (2 : F) x
    dsimp only [y]
    rw [map_sub, hdouble, trace_algebraMap, hE, two_smul]
    ring
  have hysq : y ^ 2 = algebraMap F E D := by
    dsimp only [y, D]
    simp only [map_sub, map_pow, map_mul, map_ofNat]
    linear_combination 4 * minimal_quadratic_relation F E hE x
  have hynorm : norm F E y = -D := by
    have h := minimal_quadratic_relation F E hE y
    rw [hytrace, map_zero, zero_mul, sub_zero, hysq] at h
    apply (algebraMap F E).injective
    rw [map_neg]
    linear_combination h
  have hphase := normPhase F E ht htpos hres hE tau htau Psi htauchart y
    (lattice_antitone E (by dsimp only [r] at *; omega) hy)
  change Psi (trace F E y) = Psi (norm F E y) at hphase
  rw [hytrace, hynorm, ContinuousAddChar.map_zero_eq_one] at hphase
  have hD : Psi D = 1 := by
    have h := Psi.toAddChar.map_neg_eq_inv D
    change Psi (-D) = (Psi D)⁻¹ at h
    rw [← hphase] at h
    exact inv_eq_one.mp h.symm
  have hfour : (4 : F) * c ∈ lattice F ((t + 1 : ℕ) : ℤ) := by
    have h4 : (4 : F) ∈ lattice F (2 * r) := by
      simpa only [show (2 : F) * 2 = 4 by ring, ← two_mul] using
        mul_mem_lattice F (show (2 : F) ∈ lattice F r from htwo)
          (show (2 : F) ∈ lattice F r from htwo)
    exact lattice_antitone F (by omega) (mul_mem_lattice F h4 hc)
  have h4phase : Psi (4 * c) = 1 :=
    hPsi.trivial (4 * c) (by simpa only [neg_neg] using hfour)
  rw [heven.neg_one_pow, one_mul, O.trace_difference U E hU hE]
  have harg : 1 - (1 + 4 * c - (trace F E x ^ 2 - 4 * norm F E x)) = D - 4 * c := by
    dsimp only [D]
    ring
  rw [harg]
  have hsub := Psi.toAddChar.map_sub_eq_div D (4 * c)
  change Psi (D - 4 * c) = Psi D / Psi (4 * c) at hsub
  rw [hsub, hD, h4phase]
  simp

end Diamond

end

end LanglandsSecondMainLemma.Dyadic.UR
