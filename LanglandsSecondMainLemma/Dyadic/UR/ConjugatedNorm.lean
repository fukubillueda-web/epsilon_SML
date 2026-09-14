import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Dyadic.UR.Coefficients
import LanglandsSecondMainLemma.Characters.Conjugacy
import LanglandsSecondMainLemma.Stationary.NormalizedFactor

/-!
# Corrected common representatives at positive critical height

Paper Lemma `D:UR:correctedreps`, equations `D:UR:newrep`--`D:UR:newmult`.
The correction uses the actual conjugate of the selected exact norm
representative. All coefficient ambiguity ideals have integer exponents.
-/

namespace LanglandsSecondMainLemma.Dyadic.UR

noncomputable section
open LanglandsFirstMainLemma

section QuadraticAlgebra
variable (F L : Type*) [Field F] [Field L] [Algebra F L]
  [Module.Finite F L] [IsGalois F L]

/-- Trace and norm in the actual quadratic extension, with its specified
nonidentity automorphism. This also identifies `trace(x)-x` as the conjugate. -/
private theorem conjugatedNorm_trace_norm
    (hdegree : Module.finrank F L = 2) (sigma : Gal(L/F)) (hsigma : sigma ≠ 1)
    (x : L) :
    algebraMap F L (trace F L x) = x + sigma x ∧
      algebraMap F L (norm F L x) = x * sigma x := by
  classical
  obtain ⟨s, hs, hall⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/F))).mp
    ((IsGalois.card_aut_eq_finrank F L).trans hdegree)
  have huniv : (Finset.univ : Finset Gal(L/F)) = {1, sigma} := by
    ext rho
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hrho : rho = 1
    · exact Or.inl hrho
    · exact Or.inr ((hall rho hrho).trans (hall sigma hsigma).symm)
  constructor
  · rw [show trace F L x = Algebra.trace F L x from rfl,
      trace_eq_sum_automorphisms, huniv]
    simp [hsigma.symm]
  · rw [show norm F L x = Algebra.norm F x from rfl,
      Algebra.norm_eq_prod_automorphisms, huniv]
    simp [hsigma.symm]

/-- The exact quadratic norm expansion with an arbitrary base scalar. -/
private theorem conjugatedNorm_norm_add
    (hdegree : Module.finrank F L = 2) (a : F) (x : L) :
    norm F L (algebraMap F L a + x) =
      a ^ 2 + a * trace F L x + norm F L x := by
  obtain ⟨sigma, hsigma, _⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/F))).mp
    ((IsGalois.card_aut_eq_finrank F L).trans hdegree)
  obtain ⟨hb, hA⟩ := conjugatedNorm_trace_norm F L hdegree sigma hsigma x
  apply (algebraMap F L).injective
  rw [(conjugatedNorm_trace_norm F L hdegree sigma hsigma _).2]
  simp only [map_add, map_mul, map_pow, AlgEquiv.commutes, hb, hA]
  ring

/-- Exact ramified error; no replacement of the selected norm is involved. -/
theorem conjugatedNorm_error
    (hdegree : Module.finrank F L = 2) (sigma : Gal(L/F)) (hsigma : sigma ≠ 1)
    (x : L) (hx : x ≠ 0) (c : F) :
    (sigma x / x) * (x ^ 2 + x - algebraMap F L c) -
        (algebraMap F L (norm F L x) - x + algebraMap F L c) =
      algebraMap F L (trace F L x) * (1 - algebraMap F L c / x) := by
  obtain ⟨hb, hA⟩ := conjugatedNorm_trace_norm F L hdegree sigma hsigma x
  rw [hb, hA]
  field_simp
  ring

/-- The exact trace of the conjugating multiplier, valid in both characteristics. -/
theorem conjugatedNorm_trace_ratio
    (hdegree : Module.finrank F L = 2) (sigma : Gal(L/F)) (hsigma : sigma ≠ 1)
    (x : L) (hx : x ≠ 0) :
    trace F L (sigma x / x) = (trace F L x) ^ 2 / norm F L x - 2 := by
  obtain ⟨hb, hA⟩ := conjugatedNorm_trace_norm F L hdegree sigma hsigma x
  have hsx : sigma x ≠ 0 := (map_ne_zero sigma).mpr hx
  have hinv : sigma (sigma x) = x := by
    have h := congrArg sigma hb
    simp only [AlgEquiv.commutes, map_add] at h
    rw [hb] at h
    linear_combination -h
  apply (algebraMap F L).injective
  rw [(conjugatedNorm_trace_norm F L hdegree sigma hsigma _).1]
  simp only [map_div₀, map_pow, map_sub, map_ofNat, hinv, hb, hA]
  field_simp
  ring

/-- Trace of the corrected ramified coefficient, retaining the affine terms. -/
theorem conjugatedNorm_trace
    (hdegree : Module.finrank F L = 2) (sigma : Gal(L/F)) (hsigma : sigma ≠ 1)
    (x : L) (hx : x ≠ 0) (c : F) :
    trace F L ((sigma x / x) * (x ^ 2 + x - algebraMap F L c)) =
      2 * norm F L x + trace F L x + 2 * c -
        c * ((trace F L x) ^ 2 / norm F L x) := by
  have hform : (sigma x / x) * (x ^ 2 + x - algebraMap F L c) =
      algebraMap F L (norm F L x) + sigma x -
        algebraMap F L c * (sigma x / x) := by
    rw [(conjugatedNorm_trace_norm F L hdegree sigma hsigma x).2]
    field_simp
  rw [hform, map_sub, map_add, trace_algebraMap, hdegree,
    show trace F L (sigma x) = trace F L x from Algebra.trace_eq_of_algEquiv sigma x,
    ← Algebra.smul_def, map_smul, conjugatedNorm_trace_ratio F L hdegree sigma hsigma x hx]
  simp only [smul_eq_mul, two_nsmul]
  ring
end QuadraticAlgebra

section Stationarity
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- Whole-ideal coefficient ambiguity transports the full minus-sign chart. -/
private theorem conjugatedNorm_stationary
    (theta : LocalQuasiCharData L) (Psi : LocalAddCharData L)
    {J : ℤ} (hPsi : Psi.conductor = -J) (r : ℕ) (B : L) (Z : Lˣ)
    (hchart : ∀ (z : L) (hz : z ∈ lattice L ((r + 1 : ℕ) : ℤ)),
      theta.character (principalUnitOf L r (-z) (neg_mem_lattice L hz)) =
        Psi.character (B * z))
    (herr : (Z : L) - B ∈ lattice L (J - ((r + 1 : ℕ) : ℤ))) :
    Stationary.IsNormalizedStationaryCoefficientAtDepth L theta Psi Z (r + 1)
      (by omega) := by
  intro z
  have hu : positiveUnitOfLattice L (show 0 < r + 1 by omega) (-z) =
      principalUnitOf L r (-(z : L)) (neg_mem_lattice L z.property) := by
    apply Units.ext
    simp only [coe_positiveUnitOfLattice, Submodule.coe_neg, coe_principalUnitOf]
  rw [hu, hchart (z : L) z.property]
  have htriv : Psi.character (((Z : L) - B) * (z : L)) = 1 := by
    apply Psi.isConductor.trivial
    rw [hPsi, neg_neg]
    simpa only [sub_add_cancel] using mul_mem_lattice L herr z.property
  have heq : (Z : L) * (z : L) = B * (z : L) + ((Z : L) - B) * (z : L) := by ring
  rw [heq, ContinuousAddChar.map_add_eq_mul, htriv, mul_one]

/-- A deeper additive correction preserves an exact, possibly negative, order. -/
private theorem conjugatedNorm_order
    {B Z : L} {a j : ℤ} (hB : ord L B = (a : WithTop ℤ))
    (herr : Z - B ∈ lattice L j) (haj : a < j) :
    ord L Z = (a : WithTop ℤ) := by
  have hlt : ord L B < ord L (Z - B) := by
    rw [hB]
    exact (WithTop.coe_lt_coe.mpr haj).trans_le ((mem_lattice L).mp herr)
  have heq := ord_add_eq_min L (ne_of_lt hlt)
  rw [add_sub_cancel, min_eq_left hlt.le] at heq
  exact heq.trans hB
end Stationarity

section ErrorBounds
variable (F U E : Type*) [Field F] [Field U] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

omit [Module.Finite F U] in
/-- Both errors lie in the full ordinary coefficient ambiguity ideals.
The ramified estimate uses the improved error `b*(1-c/x)`. -/
theorem conjugatedNorm_error_bounds
    (hunr : ramificationIndex F U = 1) (hdegree : Module.finrank F E = 2)
    {t h : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hh : h ≤ t)
    (x : E) (hx : ord E x = ((-(h : ℤ) : ℤ) : WithTop ℤ))
    (c : F) (hc : c ∈ lattice F 0) (d : U) (hd : d ∈ lattice U 0) :
    algebraMap F U (trace F E x) * d ∈
        lattice U (((t + 1 : ℕ) : ℤ) - (((t + h) / 2 + 1 : ℕ) : ℤ)) ∧
    algebraMap F E (trace F E x) * (1 - algebraMap F E c / x) ∈
        lattice E (((t + 1 : ℕ) : ℤ) - ((t / 2 + h + 1 : ℕ) : ℤ)) := by
  let B : ℤ := (((t + 1 : ℕ) : ℤ) - (h : ℤ)) / 2
  have hram : ramificationIndex F E = 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa only [hdegree, hres, mul_one] using h.symm
  have hb : trace F E x ∈ lattice F B := by
    obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
    have hmem : trace F E x ∈
        Submodule.map ((trace F E).restrictScalars (ringOfIntegers F))
          ((lattice E (-(h : ℤ))).restrictScalars (ringOfIntegers F)) :=
      Submodule.mem_map.mpr ⟨x, (mem_lattice E).mpr (by rw [hx]), rfl⟩
    rw [cyclicPrime_trace_lattice_image_eq F E ht hres pi hpi hgen, hdegree] at hmem
    convert hmem using 1
    dsimp [B]
    congr 1
    norm_num
    omega
  have hbU : algebraMap F U (trace F E x) ∈ lattice U B := by
    rw [mem_lattice, ord_algebraMap, hunr, one_nsmul]
    exact (mem_lattice F).mp hb
  have hbE : algebraMap F E (trace F E x) ∈ lattice E (2 * B) := by
    rw [mem_lattice, ord_algebraMap, hram]
    have hv := add_le_add ((mem_lattice F).mp hb) ((mem_lattice F).mp hb)
    simpa only [two_nsmul, two_mul, WithTop.coe_add] using hv
  have hcE : algebraMap F E c ∈ lattice E 0 := by
    rw [mem_lattice, ord_algebraMap, hram]
    have hv := add_le_add ((mem_lattice F).mp hc) ((mem_lattice F).mp hc)
    simpa only [two_nsmul, WithTop.coe_zero, add_zero] using hv
  have hquot : algebraMap F E c / x ∈ lattice E (h : ℤ) := by
    apply (div_mem_lattice_iff E x _ (-(h : ℤ)) (h : ℤ) hx).mpr
    simpa only [neg_add_cancel] using hcE
  have hunit : 1 - algebraMap F E c / x ∈ lattice E 0 :=
    sub_mem_lattice E (by simp)
      (lattice_antitone E (by omega) hquot)
  constructor
  · exact lattice_antitone U (by dsimp [B]; omega)
      (mul_mem_lattice U hbU hd)
  · exact lattice_antitone E (by dsimp [B]; omega)
      (mul_mem_lattice E hbE hunit)
end ErrorBounds

section UnramifiedSign
variable (E K : Type*) [Field E] [Field K]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra E K] [ValuativeExtension E K] [Module.Finite E K]

/-- Evaluate the actual nontrivial norm character of an unramified quadratic
extension on a nonzero element of order `-h`. -/
theorem conjugatedNorm_unramified_sign
    (hunr : ramificationIndex E K = 1) (hdegree : Module.finrank E K = 2)
    (mu : NormCharacter E K) (hmu : mu ≠ 1)
    (x : Eˣ) (h : ℕ) (hx : ord E (x : E) = ((-(h : ℤ) : ℤ) : WithTop ℤ)) :
    (mu.1 x : ℂ) = (-1 : ℂ) ^ h := by
  let f := (mu.toQuotientCharacter E K).toMonoidHom
  have hcard : Nat.card (NormQuotient E K) = 2 :=
    (unramifiedNormQuotient_natCard E K hunr).trans hdegree
  letI : Fact (Nat.card (NormQuotient E K)).Prime := ⟨hcard ▸ Nat.prime_two⟩
  have hf : Function.Injective f := by
    rcases f.ker.eq_bot_or_eq_top_of_prime_card with hker | hker
    · exact (MonoidHom.ker_eq_bot_iff f).mp hker
    · exfalso
      apply hmu
      apply NormCharacter.ext
      apply ContinuousMonoidHom.ext
      intro y
      have hy : f (QuotientGroup.mk y) = 1 := by
        change QuotientGroup.mk y ∈ f.ker
        rw [hker]
        exact Subgroup.mem_top _
      exact hy
  have hiff : mu.1 x = 1 ↔ x ∈ (normUnits E K).range := by
    change f (QuotientGroup.mk x) = 1 ↔ _
    rw [← map_one f, hf.eq_iff, QuotientGroup.eq_one_iff]
  have hord : localUnitOrder E x = -(h : ℤ) := by
    apply WithTop.coe_injective
    rw [coe_localUnitOrder, hx]
  have hres : residueDegree E K = 2 := by
    have hv := finrank_eq_ramificationIndex_mul_residueDegree E K
    simpa only [hdegree, hunr, one_mul] using hv.symm
  rw [mem_unramified_norm_range_iff_order_dvd E K hunr, hres, hord] at hiff
  have hsquare : (mu.1 x : ℂ) ^ 2 = 1 := by
    have hn : normUnits E K (Units.map (algebraMap E K) x) = x ^ 2 := by
      apply Units.ext
      change norm E K (algebraMap E K (x : E)) = (x : E) ^ 2
      rw [LanglandsFirstMainLemma.norm_algebraMap, hdegree]
    have hm := mu.eq_one_on_normRange E K _ ⟨_, hn⟩
    simpa only [map_pow, Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (Units.val : ℂˣ → ℂ) hm
  by_cases heven : Even h
  · rw [heven.neg_one_pow]
    apply congrArg (Units.val : ℂˣ → ℂ) (hiff.mpr ?_)
    obtain ⟨k, hk⟩ := heven
    refine ⟨-(k : ℤ), ?_⟩
    rw [hk]
    push_cast
    ring
  · have hodd : Odd h := Nat.not_even_iff_odd.mp heven
    rw [hodd.neg_one_pow]
    apply (sq_eq_one_iff.mp hsquare).resolve_left
    intro heq
    have hdiv := hiff.mp (Units.ext heq)
    have hdiv' : (2 : ℤ) ∣ (h : ℤ) := dvd_neg.mp hdiv
    exact heven ((even_iff_two_dvd).mpr (Int.natCast_dvd_natCast.mp hdiv'))
end UnramifiedSign

section CommonNorms
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Module.Finite F K] [IsGalois F K]
  (U E : IntermediateField F K) [IsGalois F U]
  [IsGalois U K] [IsGalois E K]

/-- The uncorrected polynomials are the two actual norms of `x+d`.
Linear disjointness is used for the genuine base-change identities. -/
private theorem conjugatedNorm_common_norms
    (hU : Module.finrank F U = 2)
    (hUK : Module.finrank U K = 2) (hEK : Module.finrank E K = 2)
    (hdisjoint : U.LinearDisjoint E) (hsup : U ⊔ E = ⊤)
    (sigma : Gal(U/F)) (hsigma : sigma ≠ 1)
    (c : F) (d : U) (hdc : d ^ 2 - d = algebraMap F U c)
    (hconj : sigma d = 1 - d) (x : E) :
    norm U K (algebraMap E K x + algebraMap U K d) =
        algebraMap F U (norm F E x) + algebraMap F U (trace F E x) * d + d ^ 2 ∧
    norm E K (algebraMap E K x + algebraMap U K d) =
        x ^ 2 + x - algebraMap F E c ∧
    trace F U d = 1 ∧ trace F U (d ^ 2) = 1 + 2 * c := by
  obtain ⟨ht, hn⟩ := conjugatedNorm_trace_norm F U hU sigma hsigma d
  have htd : trace F U d = 1 := by
    apply (algebraMap F U).injective
    rw [ht, hconj, map_one]
    ring
  have hnd : norm F U d = -c := by
    apply (algebraMap F U).injective
    rw [hn, hconj, map_neg, ← hdc]
    ring
  have htd2 : trace F U (d ^ 2) = 1 + 2 * c := by
    have heq : d ^ 2 = d + algebraMap F U c := by rw [← hdc]; ring
    rw [heq, map_add, htd, trace_algebraMap, hU, two_nsmul]
    ring
  refine ⟨?_, ?_, htd, htd2⟩
  · rw [add_comm, conjugatedNorm_norm_add U K hUK,
      hdisjoint.trace_algebraMap hsup, hdisjoint.norm_algebraMap hsup]
    ring
  · rw [conjugatedNorm_norm_add E K hEK,
      hdisjoint.symm.trace_algebraMap (by rwa [sup_comm]),
      hdisjoint.symm.norm_algebraMap (by rwa [sup_comm]), htd, hnd, map_one, map_neg]
    ring
end CommonNorms

section ResultData
variable (F U E : Type*) [Field F] [Field U] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]

/-- The paper's two nonzero corrected representatives, their full ordinary
stationary charts, and all four exact identities. The conjugate in `valueE`
is written as `Tr(x)-x`, identified above with the actual nonidentity conjugate. -/
structure ConjugatedNormData
    (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
    (Psi : ContinuousAddChar F) (c : F) (d : U) (x : E) (t h : ℕ) where
  ZU : Uˣ
  ZE : Eˣ
  valueU : (ZU : U) = algebraMap F U (norm F E x) +
    algebraMap F U (trace F E x) * d + d ^ 2
  valueE : (ZE : E) = ((algebraMap F E (trace F E x) - x) / x) *
    (x ^ 2 + x - algebraMap F E c)
  orderU : ord U (ZU : U) = ((-(h : ℤ) : ℤ) : WithTop ℤ)
  orderE : ord E (ZE : E) = ((-2 * (h : ℤ) : ℤ) : WithTop ℤ)
  additiveConductorU : IsAdditiveConductor U (tracePullbackAddChar F U Psi)
    (-((t + 1 : ℕ) : ℤ))
  additiveConductorE : IsAdditiveConductor E (tracePullbackAddChar F E Psi)
    (-((t + 1 : ℕ) : ℤ))
  stationaryU : Stationary.IsNormalizedStationaryCoefficientAtDepth U
    (canonicalLocalQuasiCharData U thetaU)
    ⟨tracePullbackAddChar F U Psi, -((t + 1 : ℕ) : ℤ), additiveConductorU⟩ ZU
    ((t + h) / 2 + 1) (by omega)
  stationaryE : Stationary.IsNormalizedStationaryCoefficientAtDepth E
    (canonicalLocalQuasiCharData E thetaE)
    ⟨tracePullbackAddChar F E Psi, -((t + 1 : ℕ) : ℤ), additiveConductorE⟩ ZE
    (t / 2 + h + 1) (by omega)
  errorU : (ZU : U) - (algebraMap F U (norm F E x) + d ^ 2) =
    algebraMap F U (trace F E x) * d
  errorE : (ZE : E) - (algebraMap F E (norm F E x) - x + algebraMap F E c) =
    algebraMap F E (trace F E x) * (1 - algebraMap F E c / x)
  trace_difference : trace F U (ZU : U) - trace F E (ZE : E) =
    1 + c * ((trace F E x) ^ 2 / norm F E x)
  character_ratio : (thetaE ZE : ℂ) / (thetaU ZU : ℂ) = (-1 : ℂ) ^ h
end ResultData

section Construction
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  (U E : IntermediateField F K)
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeExtension F U] [ValuativeExtension F E]
  [ValuativeExtension U K] [ValuativeExtension E K]
  [IsGalois F U] [PrimeCyclicExtension F E] [IsGalois U K] [IsGalois E K]

omit [ValuativeExtension F K] in
/-- Apply the correction to any selected `x` with the actual coefficient
charts and orders supplied by `coefficients`. The conjugacy datum is supplied
by `Characters.conjugacy`; the genuine-input constructor below supplies it
and the two coefficient charts internally. -/
theorem conjugatedNorm_of_coefficients
    (hU : Module.finrank F U = 2) (hE : Module.finrank F E = 2)
    (hUK : Module.finrank U K = 2) (hEK : Module.finrank E K = 2)
    (hunr : ramificationIndex F U = 1) (hunrEK : ramificationIndex E K = 1)
    (hdisjoint : U.LinearDisjoint E) (hsup : U ⊔ E = ⊤)
    {t h : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) (hhpos : 0 < h) (hh : h ≤ t)
    (sigma : Gal(U/F)) (hsigma : sigma ≠ 1)
    (c : F) (hc : c ∈ lattice F 0) (d : U) (hd : d ∈ lattice U 0)
    (hdc : d ^ 2 - d = algebraMap F U c) (hconj : sigma d = 1 - d)
    (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
    (hcomp : normQuasiChar U K thetaU = normQuasiChar E K thetaE)
    (D : Characters.ConjugateTwistData F E K thetaE)
    (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (x : E) (hx : ord E x = ((-(h : ℤ) : ℤ) : WithTop ℤ))
    (hchartU : ∀ (z : U) (hz : z ∈ lattice U (((t + h) / 2 + 1 : ℕ) : ℤ)),
      thetaU (principalUnitOf U ((t + h) / 2) (-z) (neg_mem_lattice U hz)) =
        tracePullbackAddChar F U Psi ((algebraMap F U (norm F E x) + d ^ 2) * z))
    (hchartE : ∀ (z : E) (hz : z ∈ lattice E ((t / 2 + h + 1 : ℕ) : ℤ)),
      thetaE (principalUnitOf E (t / 2 + h) (-z) (neg_mem_lattice E hz)) =
        tracePullbackAddChar F E Psi
          ((algebraMap F E (norm F E x) - x + algebraMap F E c) * z))
    (hBU : ord U (algebraMap F U (norm F E x) + d ^ 2) =
      ((-(h : ℤ) : ℤ) : WithTop ℤ))
    (hBE : ord E (algebraMap F E (norm F E x) - x + algebraMap F E c) =
      ((-2 * (h : ℤ) : ℤ) : WithTop ℤ)) :
    Nonempty (ConjugatedNormData F U E thetaU thetaE Psi c d x t h) := by
  obtain ⟨s, hs, _⟩ := (Nat.card_eq_two_iff' (1 : Gal(E/F))).mp
    ((IsGalois.card_aut_eq_finrank F E).trans hE)
  have hx0 : x ≠ 0 := (ord_ne_top_iff E).mp (by rw [hx]; simp)
  let zU : U := algebraMap F U (norm F E x) + algebraMap F U (trace F E x) * d + d ^ 2
  let zE : E := (s x / x) * (x ^ 2 + x - algebraMap F E c)
  have herrU : zU - (algebraMap F U (norm F E x) + d ^ 2) =
      algebraMap F U (trace F E x) * d := by dsimp [zU]; ring
  have herrE := conjugatedNorm_error F E hE s hs x hx0 c
  obtain ⟨hmemU, hmemE⟩ := conjugatedNorm_error_bounds F U E hunr hE ht hres hh
    x hx c hc d hd
  rw [← herrU] at hmemU
  rw [← herrE] at hmemE
  have hoU : ord U zU = ((-(h : ℤ) : ℤ) : WithTop ℤ) :=
    conjugatedNorm_order U hBU hmemU (by push_cast; omega)
  have hoE : ord E zE = ((-2 * (h : ℤ) : ℤ) : WithTop ℤ) :=
    conjugatedNorm_order E hBE hmemE (by push_cast; omega)
  let ZU : Uˣ := Units.mk0 zU ((ord_ne_top_iff U).mp (by rw [hoU]; simp))
  let ZE : Eˣ := Units.mk0 zE ((ord_ne_top_iff E).mp (by rw [hoE]; exact WithTop.coe_ne_top))
  have hPsiU : IsAdditiveConductor U (tracePullbackAddChar F U Psi)
      (-((t + 1 : ℕ) : ℤ)) :=
    (unramified_additiveConductor_compTrace F U hunr Psi _).mpr hPsi
  have hPsiE : IsAdditiveConductor E (tracePullbackAddChar F E Psi)
      (-((t + 1 : ℕ) : ℤ)) := by
    obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
    have hp := additiveConductor_compTrace_cyclicPrime F E ht hres pi hpi hgen hPsi
    rw [hE] at hp
    have heq : (2 : ℤ) * (-((t + 1 : ℕ) : ℤ)) +
        (((2 - 1) * (t + 1) : ℕ) : ℤ) = -((t + 1 : ℕ) : ℤ) := by norm_num; omega
    exact heq ▸ hp
  obtain ⟨hNU, hNE, htd, htd2⟩ := conjugatedNorm_common_norms U E hU hUK hEK
    hdisjoint hsup sigma hsigma c d hdc hconj x
  have hC0 : algebraMap E K x + algebraMap U K d ≠ 0 := by
    intro heq
    have hzU0 : zU = 0 := by dsimp [zU]; rw [← hNU, heq]; simp
    exact Units.ne_zero ZU hzU0
  let C : Kˣ := Units.mk0 (algebraMap E K x + algebraMap U K d) hC0
  have hCU : normUnits U K C = ZU := Units.ext hNU
  let xu : Eˣ := Units.mk0 x hx0
  let rho : Eˣ := Units.map s.toMonoidHom xu / xu
  have hCE : ZE = rho * normUnits E K C := by
    apply Units.ext
    simp only [Units.val_mul, rho, Units.val_div_eq_div_val, Units.coe_map]
    change zE = (s x / x) * norm E K (algebraMap E K x + algebraMap U K d)
    rw [hNE]
  let mu := D.quotientEquiv s.symm
  have hmu : mu ≠ 1 := by
    intro heq
    have heq' : s.symm = 1 := D.quotientEquiv.injective (heq.trans D.quotientEquiv.map_one.symm)
    exact hs (inv_eq_one.mp heq')
  have hrho : thetaE rho = mu.1 xu := by
    rw [show mu.1 = Basic.conjugateQuasiChar F E s.symm thetaE / thetaE from D.quotient_eq _]
    change thetaE (Units.map s.toMonoidHom xu / xu) =
      thetaE (Units.map s.toMonoidHom xu) / thetaE xu
    exact map_div thetaE _ _
  have hsign : (thetaE rho : ℂ) = (-1 : ℂ) ^ h := by
    rw [hrho]
    exact conjugatedNorm_unramified_sign E K hunrEK hEK mu hmu xu h hx
  have hcommon : thetaE (normUnits E K C) = thetaU ZU := by
    have hv := DFunLike.congr_fun hcomp C
    change thetaU (normUnits U K C) = thetaE (normUnits E K C) at hv
    rw [hCU] at hv
    exact hv.symm
  refine ⟨{
    ZU := ZU, ZE := ZE, valueU := rfl, valueE := ?_, orderU := hoU, orderE := hoE
    additiveConductorU := hPsiU, additiveConductorE := hPsiE
    stationaryU := ?_, stationaryE := ?_, errorU := herrU, errorE := herrE
    trace_difference := ?_, character_ratio := ?_ }⟩
  · change zE = _
    rw [(conjugatedNorm_trace_norm F E hE s hs x).1, add_sub_cancel_left]
  · exact conjugatedNorm_stationary U _ _
      rfl
      ((t + h) / 2) _ ZU hchartU hmemU
  · exact conjugatedNorm_stationary E _ _
      rfl
      (t / 2 + h) _ ZE hchartE hmemE
  · change trace F U zU - trace F E zE = _
    have htU : trace F U zU = 2 * norm F E x + trace F E x + 1 + 2 * c := by
      dsimp [zU]
      rw [map_add, map_add, trace_algebraMap, hU, ← Algebra.smul_def, map_smul, htd, htd2]
      simp only [smul_eq_mul, mul_one, two_nsmul]
      ring
    rw [htU, conjugatedNorm_trace F E hE s hs x hx0 c]
    ring
  · rw [hCE, map_mul, Units.val_mul, hsign, hcommon]
    exact mul_div_cancel_right₀ _ (Units.ne_zero (thetaU ZU))
end Construction

section ActualPair
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

/-- **Corrected common representatives**, paper Lemma `D:UR:correctedreps`.

For the actual primitive compatible pair at `1 ≤ h ≤ t`, construct a base
twist, select its exact norm representative using `coefficients_exists`, and
correct the ramified norm by the actual conjugate ratio. The result includes
both normalized stationary coefficients and all four displayed identities.

The input `c,d,Psi` is exactly the geometric and additive setup of `models`
and `twist`. Neither coefficient chart, a commutator identity, an exact norm
preimage, nor the sign is an input. The ordinary charts, the nonzero units,
the upper unramified edge, and the conjugacy datum are all constructed.
The proof permits both field characteristics and arbitrary continuous
quasi-characters. `conjugatedNorm_of_coefficients` gives the same result for
every already-selected representative with the proved coefficient data. -/
theorem conjugatedNorm
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (U E : IntermediateField F K)
    (hU : Module.finrank F U = 2) (hE : Module.finrank F E = 2) :
    letI := Basic.intermediateFieldValuativeRel U
    letI := Basic.intermediateFieldTopology U
    letI := Basic.intermediateField_localField U
    letI := Basic.intermediateField_lowerValuativeExtension U
    letI := Basic.intermediateField_upperValuativeExtension U
    letI := Basic.intermediateFieldValuativeRel E
    letI := Basic.intermediateFieldTopology E
    letI := Basic.intermediateField_localField E
    letI := Basic.intermediateField_lowerValuativeExtension E
    letI := Basic.intermediateField_upperValuativeExtension E
    ∀ (_hunr : ramificationIndex F U = 1) (t h : ℕ)
      (_hhpos : 0 < h) (_hh : h ≤ t)
      (_ht : PrimeCyclicExtension.IsLowerBreak F E t) (_hres : residueDegree F E = 1)
      (tau : NormCharacter F E) (_htau : tau ≠ 1)
      (Psi : ContinuousAddChar F)
      (_hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
      (_htauchart : ∀ (z : F) (hz : z ∈ lattice F ((t / 2 + 1 : ℕ) : ℤ)),
        tau.1 (principalUnitOf F (t / 2) (-z) (neg_mem_lattice F hz)) = Psi z)
      (sigma : Gal(U/F)) (_hsigma : sigma ≠ 1)
      (c : F) (_hc : ord F c = 0) (d : U) (_hd : ord U d = 0)
      (_hdc : d ^ 2 - d = algebraMap F U c) (_hconj : sigma d = 1 - d)
      (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
      (_hcomp : normQuasiChar U K thetaU = normQuasiChar E K thetaE)
      (_hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F,
        normQuasiChar F K lambda = normQuasiChar U K thetaU)
      (_hcondU : IsMultiplicativeConductor U thetaU (t + 1 + h)),
      IsMultiplicativeConductor E thetaE (t + 1 + 2 * h) ∧
        ∃ x : E, ord E x = ((-(h : ℤ) : ℤ) : WithTop ℤ) ∧
          Nonempty (ConjugatedNormData F U E thetaU thetaE Psi c d x t h) := by
  letI := Basic.intermediateFieldValuativeRel U
  letI := Basic.intermediateFieldTopology U
  letI := Basic.intermediateField_localField U
  letI := Basic.intermediateField_lowerValuativeExtension U
  letI := Basic.intermediateField_upperValuativeExtension U
  letI := Basic.intermediateFieldValuativeRel E
  letI := Basic.intermediateFieldTopology E
  letI := Basic.intermediateField_localField E
  letI := Basic.intermediateField_lowerValuativeExtension E
  letI := Basic.intermediateField_upperValuativeExtension E
  intro hunr t h hhpos hh ht hres tau htau Psi hPsi htauchart sigma hsigma
    c hc d hd hdc hconj thetaU thetaE hcomp hprimitive hcondU
  have dataU := Basic.intermediateField_tower_compatible Nat.prime_two hG U hU
  have dataE := Basic.intermediateField_tower_compatible Nat.prime_two hG E hE
  have hUK := dataU.2.2.2.2.2.2.2.2.2.2.1
  have hEK := dataE.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F U dataU.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension U K dataU.2.2.2.2.2.2.2.2.2.2.2.2
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E dataE.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension E K dataE.2.2.2.2.2.2.2.2.2.2.2.2
  have htpos : 0 < t := by omega
  obtain ⟨chiU, chiE, lambda, nu, k, _, _, _, _, _, _, _, hmodelU, hmodelE,
      hrealU, hrealE, hcondU', hcondE, hlambda, hlambdazero⟩ :=
    twist hG U E hU hE hunr t ht htpos hres tau htau Psi hPsi htauchart
      sigma hsigma c hc d hd hdc hconj thetaU thetaE hcomp hprimitive
  have hk : k = h := by have heq := hcondU'.unique hcondU; omega
  subst k
  obtain ⟨x, _, hxorder, _, _, hchartU, hchartE, hBU, hBE⟩ :=
    coefficients_exists F U E hunr hU hE ht htpos hres hh tau htau Psi hPsi
      htauchart c d chiU thetaU (chiE * nu.1) thetaE lambda hmodelU hmodelE
      hrealU hrealE hcondU hcondE hlambda hlambdazero
  have hne : Ramification.intermediateNormRange U ≠ Ramification.intermediateNormRange E := by
    change (normUnits F U).range ≠ (normUnits F E).range
    intro heq
    obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
    have hct := ramifiedNormCharacter_conductor F E ht hres pi hpi hgen tau htau
    have hzero : QuasiCharTrivialOnUnitFiltration F tau.1 0 := by
      intro u hu
      apply tau.eq_one_on_normRange F E
      rw [← heq]
      obtain ⟨v, _, hv⟩ := (unramified_norm_unitFiltration F U hunr 0).2 u hu
      exact ⟨v, hv⟩
    have hb := hct.minimal 0 hzero
    omega
  obtain ⟨_, ⟨D⟩, _⟩ := Characters.conjugacy Nat.prime_two hG U E hU hE hne
    thetaU thetaE (normQuasiChar U K thetaU) rfl hcomp.symm hprimitive
  have hUE : U ≠ E := fun heq => hne (congrArg Ramification.intermediateNormRange heq)
  have hinf : U ⊓ E = ⊥ := by
    have hdiv : Module.finrank F ↥(U ⊓ E) ∣ 2 := by
      rw [← hU]
      exact IntermediateField.finrank_dvd_of_le_right inf_le_left
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hdim | hdim
    · exact IntermediateField.finrank_eq_one_iff.mp hdim
    · have hi : U ⊓ E = U :=
        IntermediateField.eq_of_le_of_finrank_eq inf_le_left (hdim.trans hU.symm)
      have hle : U ≤ E := by rw [← hi]; exact inf_le_right
      exact (hUE (IntermediateField.eq_of_le_of_finrank_eq hle (hU.trans hE.symm))).elim
  have hdisjoint : U.LinearDisjoint E := IntermediateField.LinearDisjoint.of_inf_eq_bot hinf
  have hsup : U ⊔ E = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [hdisjoint.finrank_sup, IntermediateField.finrank_top', hU, hE]
    exact dataU.2.2.2.2.2.2.2.2.1.symm
  have hunrEK : ramificationIndex E K = 1 := by
    have hram : ramificationIndex F E = 2 := by
      have hv := finrank_eq_ramificationIndex_mul_residueDegree F E
      simpa only [hE, hres, mul_one] using hv.symm
    obtain ⟨pi, hpi⟩ := exists_ord_eq F 1
    have hv : ord K (algebraMap U K (algebraMap F U pi)) =
        ord K (algebraMap E K (algebraMap F E pi)) := by
      rw [← IsScalarTower.algebraMap_apply F U K, ← IsScalarTower.algebraMap_apply F E K]
    rw [ord_algebraMap, ord_algebraMap, ord_algebraMap, ord_algebraMap,
      hunr, hram, hpi, one_nsmul] at hv
    have heq : (ramificationIndex U K : ℤ) = (ramificationIndex E K : ℤ) * 2 := by
      exact WithTop.coe_injective (by simpa only [← WithTop.coe_nsmul,
        nsmul_eq_mul, Nat.cast_ofNat, mul_one] using hv)
    have hdeg := finrank_eq_ramificationIndex_mul_residueDegree U K
    have hfpos := residueDegree_pos U K
    have hepos := ramificationIndex_pos E K
    have hbound : ramificationIndex U K ≤ 2 := by rw [hUK] at hdeg; nlinarith
    omega
  refine ⟨hcondE, x, hxorder hhpos, ?_⟩
  exact conjugatedNorm_of_coefficients U E hU hE hUK hEK hunr hunrEK hdisjoint hsup
    ht hres hhpos hh sigma hsigma c ((mem_lattice F).mpr (by rw [hc]; rfl))
    d ((mem_lattice U).mpr (by rw [hd]; rfl)) hdc hconj thetaU thetaE hcomp D
    Psi hPsi x (hxorder hhpos) hchartU hchartE hBU hBE
end ActualPair

end
end LanglandsSecondMainLemma.Dyadic.UR
