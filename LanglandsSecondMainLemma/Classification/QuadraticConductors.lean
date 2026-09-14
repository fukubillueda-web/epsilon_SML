import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Dyadic.UR.OddConductor
import LanglandsSecondMainLemma.Local.TraceIdeals

/-!
# Classification / Quadratic Conductors

Blueprint: `blueprint/tasks/Classification/QuadraticConductors.md`.
Paper: Lemma `U:quadratic-types`.

Let `F` be a mixed-characteristic dyadic local field and write
`e = ord_F(2)`. For an actual ramified quadratic edge of lower break `t`,
FML identifies the exact conductor of its nontrivial norm character with
the different exponent `t + 1`.

The trace-ideal formula applied to `1` bounds this exponent by `2e + 1`.
An even exponent is therefore `2a` with `1 ≤ a ≤ e`; the accepted
odd-conductor theorem proves that every odd exponent is exactly `2e + 1`.
That theorem also gives a canonical last-layer formula. Consequently two
maximal quadratic norm characters agree on `U_F^(2e)`, and their product
has conductor at most `2e`.

The additive characters and chart hypotheses below are the actual duality
charts chosen in the paper before Lemma `D:UR:oddT`; the proof never treats
the resulting last-layer formula as a hypothesis.
-/

namespace LanglandsSecondMainLemma.Classification

noncomputable section

open LanglandsFirstMainLemma

/-- The conductor classification for one actual ramified quadratic edge.

The trace of `1` belongs to the exact image of the integral trace lattice.
Since it equals `2`, this gives `floor ((t+1)/2) ≤ e`. -/
private theorem quadraticConductorShape
    (F E : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Free F E] [Module.Finite F E]
    [PrimeCyclicExtension F E]
    (hchar : residueCharacteristic F = 2)
    (e : ℕ) (he : ord F (2 : F) = ((e : ℤ) : WithTop ℤ))
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
        (neg_mem_lattice F hx)) = PsiF x) :
    IsMultiplicativeConductor F tau.1 (t + 1) ∧
      ((∃ a : ℕ, 1 ≤ a ∧ a ≤ e ∧ t + 1 = 2 * a) ∨
        t + 1 = 2 * e + 1) := by
  have hram : ramificationIndex F E = 2 := by
    have hfund := finrank_eq_ramificationIndex_mul_residueDegree F E
    rw [hdegree, hres, mul_one] at hfund
    exact hfund.symm
  have hdifferent : differentExponent F E = t + 1 := by
    rw [cyclicPrime_differentExponent_eq F E ht hres pi hpi hgen,
      hdegree]
    omega
  have htraceOne : trace F E (1 : E) = (2 : F) := by
    rw [← map_one (algebraMap F E), trace_algebraMap, hdegree]
    norm_num
  have htraceMem : trace F E (1 : E) ∈
      Submodule.map ((trace F E).restrictScalars (ringOfIntegers F))
        ((lattice E 0).restrictScalars (ringOfIntegers F)) := by
    exact Submodule.mem_map.mpr ⟨1, by simp, rfl⟩
  rw [LanglandsSecondMainLemma.Local.traceIdeal_eq_fml F E hres 0,
    hram, zero_add, htraceOne, mem_lattice, he] at htraceMem
  have hfloor : ((t + 1 : ℕ) : ℤ) / 2 ≤ (e : ℤ) := by
    rw [hdifferent] at htraceMem
    exact_mod_cast htraceMem
  have hupper : t + 1 ≤ 2 * e + 1 := by
    omega
  have hcond : IsMultiplicativeConductor F tau.1 (t + 1) :=
    ramifiedNormCharacter_conductor F E ht hres pi hpi hgen tau htau
  refine ⟨hcond, ?_⟩
  rcases Nat.even_or_odd (t + 1) with heven | hodd
  · left
    obtain ⟨a, ha⟩ := heven
    refine ⟨a, by omega, by omega, by omega⟩
  · right
    obtain ⟨_hcharZero, e', he', hmax, _hlast⟩ :=
      LanglandsSecondMainLemma.Dyadic.UR.oddConductor F E hchar ht htpos
        hres hdegree pi hpi hgen tau htau PsiF hchart hodd
    have heq : e' = e := by
      rw [he] at he'
      exact_mod_cast (WithTop.coe_eq_coe.mp he').symm
    simpa only [heq] using hmax

/-- At maximal conductor, the value of an actual quadratic norm character
in a last-layer coordinate `1 - 4z` is the canonical absolute-trace
character. In particular it is independent of the quadratic edge. -/
private theorem maximalQuadraticNormCharacter_value
    (F E : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Free F E] [Module.Finite F E]
    [PrimeCyclicExtension F E]
    (hchar : residueCharacteristic F = 2)
    (e : ℕ) (he : ord F (2 : F) = ((e : ℤ) : WithTop ℤ))
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
    (hmax : t + 1 = 2 * e + 1)
    (z : F) (hz : z ∈ lattice F 0)
    (u : Fˣ) (hu : (u : F) = 1 - (4 : F) * z) :
    (tau.1 u : ℂ) =
      ((@absoluteTraceChar (ResidueField F) _ (ringChar.of_eq hchar))
        (reduce F z hz) : ℂ) := by
  have hepos : 0 < e := by omega
  have htEven : t = 2 * e := by omega
  obtain ⟨_hcharZero, e', he', _hmax', hlast⟩ :=
    LanglandsSecondMainLemma.Dyadic.UR.oddConductor F E hchar ht htpos
      hres hdegree pi hpi hgen tau htau PsiF hchart ⟨e, hmax⟩
  have heq : e' = e := by
    rw [he] at he'
    exact_mod_cast (WithTop.coe_eq_coe.mp he').symm
  subst e'
  have hfour : ord F (4 : F) = (((2 * e : ℕ) : ℤ) : WithTop ℤ) := by
    rw [show (4 : F) = (2 : F) ^ 2 by norm_num, ord_pow, he]
    rw [← WithTop.coe_nsmul]
    norm_cast
  let x : F := (4 : F) * z
  have hx : x ∈ lattice F (((2 * e : ℕ) : ℤ)) := by
    have hfourMem : (4 : F) ∈ lattice F (((2 * e : ℕ) : ℤ)) := by
      rw [mem_lattice, hfour]
    simpa only [x, add_zero] using mul_mem_lattice F hfourMem hz
  have hxq : x ∈ lattice F (((t / 2 + 1 : ℕ) : ℤ)) := by
    apply lattice_antitone F
      (show ((t / 2 + 1 : ℕ) : ℤ) ≤ ((2 * e : ℕ) : ℤ) by
        exact_mod_cast (show t / 2 + 1 ≤ 2 * e by omega))
    simpa only [x] using hx
  have huPrincipal : principalUnitOf F (t / 2) (-x)
      (neg_mem_lattice F hxq) = u := by
    apply Units.ext
    simp only [coe_principalUnitOf, x, hu]
    ring
  calc
    (tau.1 u : ℂ) = (PsiF x : ℂ) := by
      exact congrArg Units.val (by rw [← hchart x hxq, huPrincipal])
    _ = (PsiF ((4 : F) * z) : ℂ) := by
      rfl
    _ = ((@absoluteTraceChar (ResidueField F) _
          (ringChar.of_eq hchar)) (reduce F z hz) : ℂ) := hlast z hz

/-- A character of a genuine quadratic norm quotient kills every square. -/
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

/-- **Quadratic conductors in mixed characteristic** (paper Lemma
`U:quadratic-types`).

Each supplied character is the nontrivial actual norm character of a
ramified quadratic edge over the same dyadic mixed-characteristic field.
Its conductor is `2a`, with `1 ≤ a ≤ e`, or `2e+1`. If both conductors
are maximal, the characters agree on the whole subgroup `U_F^(2e)`.
Their product is therefore trivial there, and FML's canonical exact
conductor exponent of that product is at most `2e`. -/
theorem quadraticConductors
    (F E₁ E₂ : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    [Field E₁] [ValuativeRel E₁] [TopologicalSpace E₁]
    [IsNonarchimedeanLocalField E₁]
    [Algebra F E₁] [ValuativeExtension F E₁]
    [Module.Free F E₁] [Module.Finite F E₁]
    [PrimeCyclicExtension F E₁]
    [Field E₂] [ValuativeRel E₂] [TopologicalSpace E₂]
    [IsNonarchimedeanLocalField E₂]
    [Algebra F E₂] [ValuativeExtension F E₂]
    [Module.Free F E₂] [Module.Finite F E₂]
    [PrimeCyclicExtension F E₂]
    (hchar : residueCharacteristic F = 2)
    (e : ℕ) (he : ord F (2 : F) = ((e : ℤ) : WithTop ℤ))
    {t₁ t₂ : ℕ}
    (ht₁ : PrimeCyclicExtension.IsLowerBreak F E₁ t₁)
    (ht₁pos : 0 < t₁) (hres₁ : residueDegree F E₁ = 1)
    (hdegree₁ : Module.finrank F E₁ = 2)
    (pi₁ : ringOfIntegers E₁)
    (hpi₁ : (ValuativeRel.valuation E₁).IsUniformizer (pi₁ : E₁))
    (hgen₁ : Algebra.adjoin (ringOfIntegers F)
      ({pi₁} : Set (ringOfIntegers E₁)) = ⊤)
    (tau₁ : NormCharacter F E₁) (htau₁ : tau₁ ≠ 1)
    (Psi₁ : ContinuousAddChar F)
    (hchart₁ : ∀ (x : F)
      (hx : x ∈ lattice F (((t₁ / 2 + 1 : ℕ) : ℤ))),
      tau₁.1 (principalUnitOf F (t₁ / 2) (-x)
        (neg_mem_lattice F hx)) = Psi₁ x)
    (ht₂ : PrimeCyclicExtension.IsLowerBreak F E₂ t₂)
    (ht₂pos : 0 < t₂) (hres₂ : residueDegree F E₂ = 1)
    (hdegree₂ : Module.finrank F E₂ = 2)
    (pi₂ : ringOfIntegers E₂)
    (hpi₂ : (ValuativeRel.valuation E₂).IsUniformizer (pi₂ : E₂))
    (hgen₂ : Algebra.adjoin (ringOfIntegers F)
      ({pi₂} : Set (ringOfIntegers E₂)) = ⊤)
    (tau₂ : NormCharacter F E₂) (htau₂ : tau₂ ≠ 1)
    (Psi₂ : ContinuousAddChar F)
    (hchart₂ : ∀ (x : F)
      (hx : x ∈ lattice F (((t₂ / 2 + 1 : ℕ) : ℤ))),
      tau₂.1 (principalUnitOf F (t₂ / 2) (-x)
        (neg_mem_lattice F hx)) = Psi₂ x) :
    (IsMultiplicativeConductor F tau₁.1 (t₁ + 1) ∧
      ((∃ a : ℕ, 1 ≤ a ∧ a ≤ e ∧ t₁ + 1 = 2 * a) ∨
        t₁ + 1 = 2 * e + 1)) ∧
    (IsMultiplicativeConductor F tau₂.1 (t₂ + 1) ∧
      ((∃ a : ℕ, 1 ≤ a ∧ a ≤ e ∧ t₂ + 1 = 2 * a) ∨
        t₂ + 1 = 2 * e + 1)) ∧
    ((t₁ + 1 = 2 * e + 1 ∧ t₂ + 1 = 2 * e + 1) →
      (∀ u : Fˣ, u ∈ unitFiltration F (2 * e) →
        tau₁.1 u = tau₂.1 u) ∧
      QuasiCharTrivialOnUnitFiltration F (tau₁.1 * tau₂.1) (2 * e) ∧
      multiplicativeConductorExponent F (tau₁.1 * tau₂.1) ≤ 2 * e) := by
  have hshape₁ := quadraticConductorShape F E₁ hchar e he ht₁ ht₁pos
    hres₁ hdegree₁ pi₁ hpi₁ hgen₁ tau₁ htau₁ Psi₁ hchart₁
  have hshape₂ := quadraticConductorShape F E₂ hchar e he ht₂ ht₂pos
    hres₂ hdegree₂ pi₂ hpi₂ hgen₂ tau₂ htau₂ Psi₂ hchart₂
  refine ⟨hshape₁, hshape₂, ?_⟩
  rintro ⟨hmax₁, hmax₂⟩
  have hepos : 0 < e := by omega
  have hfour : ord F (4 : F) = (((2 * e : ℕ) : ℤ) : WithTop ℤ) := by
    rw [show (4 : F) = (2 : F) ^ 2 by norm_num, ord_pow, he]
    rw [← WithTop.coe_nsmul]
    norm_cast
  have hagree : ∀ u : Fˣ, u ∈ unitFiltration F (2 * e) →
      tau₁.1 u = tau₂.1 u := by
    intro u hu
    have hpred : 2 * e - 1 + 1 = 2 * e := by omega
    have hdisp : (u : F) - 1 ∈ lattice F (((2 * e : ℕ) : ℤ)) := by
      have hdisp' := (mem_unitFiltration_succ_iff_sub_mem_lattice F
        (2 * e - 1) u).1 (by simpa only [hpred] using hu)
      rw [hpred] at hdisp'
      exact hdisp'
    let x : F := (1 : F) - (u : F)
    have hx : x ∈ lattice F (((2 * e : ℕ) : ℤ)) := by
      simpa only [x, neg_sub] using neg_mem_lattice F hdisp
    let z : F := x / 4
    have hz : z ∈ lattice F 0 :=
      (div_mem_lattice_iff F (4 : F) x ((2 * e : ℕ) : ℤ) 0 hfour).2
        (by simpa using hx)
    have huCoord : (u : F) = 1 - (4 : F) * z := by
      dsimp only [z, x]
      field_simp
      ring
    have hvalue₁ := maximalQuadraticNormCharacter_value F E₁ hchar e he
      ht₁ ht₁pos hres₁ hdegree₁ pi₁ hpi₁ hgen₁ tau₁ htau₁
      Psi₁ hchart₁ hmax₁ z hz u huCoord
    have hvalue₂ := maximalQuadraticNormCharacter_value F E₂ hchar e he
      ht₂ ht₂pos hres₂ hdegree₂ pi₂ hpi₂ hgen₂ tau₂ htau₂
      Psi₂ hchart₂ hmax₂ z hz u huCoord
    apply Units.ext
    exact hvalue₁.trans hvalue₂.symm
  have hprod : QuasiCharTrivialOnUnitFiltration F
      (tau₁.1 * tau₂.1) (2 * e) := by
    intro u hu
    have heq := hagree u hu
    calc
      (tau₁.1 * tau₂.1) u = tau₁.1 u * tau₂.1 u := rfl
      _ = tau₁.1 u * tau₁.1 u := by rw [← heq]
      _ = tau₁.1 (u ^ 2) := by rw [pow_two, map_mul]
      _ = 1 := normCharacter_sq_apply F E₁ hdegree₁ tau₁ u
  exact ⟨hagree, hprod,
    (quasiCharTrivialOnUnitFiltration_iff_conductorExponent_le F
      (tau₁.1 * tau₂.1) (2 * e)).1 hprod⟩

end

end LanglandsSecondMainLemma.Classification
