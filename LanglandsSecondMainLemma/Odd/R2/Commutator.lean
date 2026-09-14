import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Odd.Models.Realization
import LanglandsSecondMainLemma.Characters.Conjugacy

/-!
# Odd / R2 / Commutator

Blueprint: blueprint/tasks/Odd/R2/Commutator.md
Paper: Lemma 8.9, `O:R:comm-log`, lines 2782--2833.

The logarithmic error retains the extra ramification depth of the second
variable. Thus the full model is applied to the quotient of two shallow
units. Conjugation uses the inverse automorphism on the character argument
and the forward automorphism on the coefficient.
-/

namespace LanglandsSecondMainLemma.Odd.R2

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

open private truncatedLogIntegralMvPolynomial truncatedLogIntegralDefectPolynomial
  map_truncatedLogIntegralDefectPolynomial support_degree_truncatedLogIntegralDefectPolynomial
  pow_mem_lattice_nat from LanglandsSecondMainLemma.Odd.TruncatedLog

/-- The defect vanishes when its second variable is zero, over the ring of
integers itself. This supplies the additional ramification depth. -/
private theorem X_dvd_integralDefect
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (p : ℕ)
    (hchar : ringChar (ResidueField E) = p) :
    MvPolynomial.X (1 : Fin 2) ∣ truncatedLogIntegralDefectPolynomial E p hchar := by
  let z : MvPolynomial (Fin 2) (ringOfIntegers E) := MvPolynomial.X 0
  let w : MvPolynomial (Fin 2) (ringOfIntegers E) := MvPolynomial.X 1
  have hd : w ∣ (z + w - z * w) - z := ⟨1 - z, by ring⟩
  have hsub : w ∣ truncatedLogIntegralMvPolynomial E p hchar (z + w - z * w) -
      truncatedLogIntegralMvPolynomial E p hchar z := by
    dsimp only [truncatedLogIntegralMvPolynomial]
    rw [add_sub_add_comm, ← Finset.sum_sub_distrib]
    apply dvd_add hd
    apply Finset.dvd_sum
    intro j hj
    rw [← mul_sub]
    exact dvd_mul_of_dvd_right (hd.trans (sub_dvd_pow_sub_pow _ _ j)) _
  have hw : w ∣ truncatedLogIntegralMvPolynomial E p hchar w := by
    dsimp only [truncatedLogIntegralMvPolynomial]
    apply dvd_add dvd_rfl
    apply Finset.dvd_sum
    intro j hj
    exact dvd_mul_of_dvd_right (dvd_pow_self _ (by
      have := (Finset.mem_Ico.mp hj).1
      omega)) _
  exact dvd_sub hsub hw

/-- A monomial of the integral defect contains the second variable. -/
private theorem integralDefect_second_degree_pos
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (p : ℕ)
    (hchar : ringChar (ResidueField E) = p)
    (d : Fin 2 →₀ ℕ)
    (hd : d ∈ (truncatedLogIntegralDefectPolynomial E p hchar).support) :
    0 < d 1 := by
  obtain ⟨Q, hQ⟩ := X_dvd_integralDefect E p hchar
  by_contra h
  have hd1 : d 1 = 0 := by omega
  have hc := MvPolynomial.mem_support_iff.mp hd
  rw [hQ, MvPolynomial.coeff_X_mul'] at hc
  simp only [Finsupp.mem_support_iff, hd1, ne_eq, not_true_eq_false, ↓reduceIte] at hc

/-- The two-variable logarithmic defect at depths `q` and `q+t` has depth
`p*q+t`, including when the residue prime is zero in the field. -/
theorem truncatedLog_defect_mem_lattice_weighted
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (p q t : ℕ)
    (hchar : ringChar (ResidueField E) = p) (hp : p.Prime)
    {x y : E} (hx : x ∈ lattice E (q : ℤ)) (hy : y ∈ lattice E ((q + t : ℕ) : ℤ)) :
    truncatedLog p (x + y - x * y) - truncatedLog p x - truncatedLog p y ∈
      lattice E ((p * q + t : ℕ) : ℤ) := by
  let Q := truncatedLogIntegralDefectPolynomial E p hchar
  have heval : MvPolynomial.eval₂ (ValuativeRel.valuation E).integer.subtype ![x, y] Q ∈
      lattice E ((p * q + t : ℕ) : ℤ) := by
    rw [Q.as_sum, MvPolynomial.eval₂_sum]
    apply sum_mem_lattice E
    intro d hd
    rw [MvPolynomial.eval₂_monomial]
    have hc : ((Q.coeff d : ringOfIntegers E) : E) ∈ lattice E 0 :=
      (mem_lattice_zero_iff E).2 (Q.coeff d).property
    have hprod : d.prod (fun i e => (![x, y] : Fin 2 → E) i ^ e) =
        x ^ d 0 * y ^ d 1 := by
      rw [Finsupp.prod_fintype d _ (by simp), Fin.prod_univ_two]
      rfl
    rw [hprod]
    have hterm := mul_mem_lattice E hc
      (mul_mem_lattice E (pow_mem_lattice_nat E hx (d 0))
        (pow_mem_lattice_nat E hy (d 1)))
    apply lattice_antitone E _ hterm
    have hdeg := support_degree_truncatedLogIntegralDefectPolynomial E p hchar hp d hd
    have hpos := integralDefect_second_degree_pos E p hchar d hd
    have hsum : d.degree = d 0 + d 1 := by
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
    have hbound : p * q + t ≤ d 0 * q + d 1 * (q + t) := by
      have := Nat.mul_le_mul_right q hdeg
      have := Nat.mul_le_mul_right t hpos
      rw [hsum] at *
      nlinarith
    simp only [zero_add]
    exact_mod_cast hbound
  rw [← eval_truncatedLogDefectPolynomial E p x y,
    ← map_truncatedLogIntegralDefectPolynomial E p hchar, MvPolynomial.eval_map]
  exact heval

private theorem ord_one_sub_of_mem
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {q : ℕ} (hq : 0 < q)
    {x : E} (hx : x ∈ lattice E (q : ℤ)) : ord E (1 - x) = 0 := by
  let u := positiveUnitOfLattice E hq (-⟨x, hx⟩)
  have h := (mem_unitFiltration_zero E (u : Eˣ)).1
    (unitFiltration_antitone E (Nat.zero_le q) u.property)
  simpa only [u, coe_positiveUnitOfLattice, Submodule.coe_neg,
    sub_eq_add_neg] using h

/-- The rational error in `O:R:comm-log`; the denominator is the actual
unit `1-x`, and no model formula at the shallow argument is assumed. -/
theorem truncatedLog_quotient_error_mem
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (p q t : ℕ)
    (hchar : ringChar (ResidueField E) = p) (hp : p.Prime) (hq : 0 < q)
    {x d : E} (hx : x ∈ lattice E (q : ℤ))
    (hd : d ∈ lattice E ((q + t : ℕ) : ℤ)) :
    truncatedLog p (d / (1 - x)) - truncatedLog p (x + d) + truncatedLog p x ∈
      lattice E ((p * q + t : ℕ) : ℤ) := by
  have hden := ord_one_sub_of_mem E hq hx
  have hne : 1 - x ≠ 0 := (ord_ne_top_iff E).1 (by rw [hden]; exact WithTop.coe_ne_top)
  have hy : d / (1 - x) ∈ lattice E ((q + t : ℕ) : ℤ) :=
    (div_mem_lattice_iff E (1 - x) d 0 _ hden).2 (by simpa using hd)
  have heq : x + d / (1 - x) - x * (d / (1 - x)) = x + d := by
    field_simp
    ring
  have h := neg_mem_lattice E
    (truncatedLog_defect_mem_lattice_weighted E p q t hchar hp hx hy)
  rw [heq] at h
  convert h using 1
  ring

/-- The genuine lower ramification action increases every positive
integer depth by the break. The proof also treats the zero input. -/
theorem galois_sub_mem_lattice
    (F E : Type) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Finite F E] [PrimeCyclicExtension F E]
    {t q : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
    (hres : residueDegree F E = 1) (sigma : Gal(E/F))
    {x : E} (hx : x ∈ lattice E (q : ℤ)) :
    sigma x - x ∈ lattice E ((q + t : ℕ) : ℤ) := by
  by_cases hzero : x = 0
  · subst x
    simp
  let u := Units.mk0 x hzero
  have hs (z : E) : sigma.toMonoidHom z = sigma z := rfl
  have hr := Models.ramificationRatio_mem F E ht htpos hres sigma u
  have hr' : sigma x / x - 1 ∈ lattice E (t : ℤ) := by
    have h := (mem_unitFiltration_succ_iff_sub_mem_lattice E (t - 1)
      (Units.map sigma.toMonoidHom u / u)).1 (by
        simpa only [Nat.sub_add_cancel htpos] using hr)
    simpa only [Nat.sub_add_cancel htpos, Units.val_div_eq_div_val,
      Units.coe_map, u, Units.val_mk0, MonoidHom.coe_coe, hs] using h
  have heq : x * (sigma x / x - 1) = sigma x - x := by
    field_simp
  simpa only [heq, Nat.cast_add] using mul_mem_lattice E hx hr'

open private map_truncatedLog from LanglandsSecondMainLemma.Odd.NormLog
open private additivePhase_sub from LanglandsSecondMainLemma.Odd.Models.TwistFormula

/-- Apply a full logarithmic character model to the deeper quotient.
The scalar depth and the additive kernel depth are integers. -/
theorem commutator_on_model
    (F E : Type) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Finite F E] [PrimeCyclicExtension F E]
    {p t q r : ℕ} (hp : p.Prime) (hchar : residueCharacteristic E = p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
    (hres : residueDegree F E = 1) (hq : 0 < q) (hr : 0 < r) (hrq : r ≤ q + t)
    (v T : ℤ) (hdepth : T ≤ v + ((p * q + t : ℕ) : ℤ))
    (b : E) (hb : b ∈ lattice E v) (Psi : ContinuousAddChar F)
    (hPsi : AddCharTrivialOnLattice E (tracePullbackAddChar F E Psi) T)
    (chi : ContinuousQuasiChar E)
    (hmodel : ∀ u : unitFiltration E r,
      chi u = tracePullbackAddChar F E Psi
        (b * truncatedLog p (1 - ((u : Eˣ) : E))))
    (sigma : Gal(E/F)) (x : lattice E (q : ℤ)) :
    (Basic.conjugateQuasiChar F E sigma chi / chi)
        (positiveUnitOfLattice E hq (-x)) =
      tracePullbackAddChar F E Psi ((sigma b - b) * truncatedLog p (x : E)) := by
  let u := positiveUnitOfLattice E hq (-x)
  let d := sigma.symm (x : E) - (x : E)
  let y := d / (1 - (x : E))
  have hd : d ∈ lattice E ((q + t : ℕ) : ℤ) :=
    galois_sub_mem_lattice F E ht htpos hres sigma.symm x.property
  have hden := ord_one_sub_of_mem E hq x.property
  have hy : y ∈ lattice E ((q + t : ℕ) : ℤ) :=
    (div_mem_lattice_iff E (1 - (x : E)) d 0 _ hden).2 (by simpa using hd)
  have hne : 1 - (x : E) ≠ 0 :=
    (ord_ne_top_iff E).1 (by rw [hden]; exact WithTop.coe_ne_top)
  let w : Eˣ := Units.map sigma.symm.toMonoidHom (u : Eˣ) / (u : Eˣ)
  have hs (z : E) : sigma.symm.toMonoidHom z = sigma.symm z := rfl
  have hw : (w : E) = 1 - y := by
    simp only [w, Units.val_div_eq_div_val, Units.coe_map, hs, u,
      coe_positiveUnitOfLattice, Submodule.coe_neg, ← sub_eq_add_neg, map_sub, map_one]
    dsimp only [y, d]
    field_simp
    ring
  have hwr : w ∈ unitFiltration E r := by
    rw [← Nat.sub_add_cancel hr, mem_unitFiltration_succ_iff_sub_mem_lattice]
    simpa only [Nat.sub_add_cancel hr, hw, sub_sub_cancel_left] using
      neg_mem_lattice E (lattice_antitone E (by exact_mod_cast hrq) hy)
  have hmodelw := hmodel ⟨w, hwr⟩
  simp only [hw, sub_sub_cancel] at hmodelw
  have herr := truncatedLog_quotient_error_mem E p q t hchar hp hq x.property hd
  have harg : (x : E) + d = sigma.symm (x : E) := by dsimp only [d]; ring
  rw [harg] at herr
  have hephase : tracePullbackAddChar F E Psi (b * truncatedLog p y) =
      tracePullbackAddChar F E Psi
        (b * (truncatedLog p (sigma.symm (x : E)) - truncatedLog p (x : E))) := by
    apply div_eq_one.mp
    rw [← additivePhase_sub]
    apply hPsi
    have h := lattice_antitone E hdepth (mul_mem_lattice E hb herr)
    convert h using 1
    dsimp only [y]
    ring
  have htrace : trace F E (b * truncatedLog p (sigma.symm (x : E))) =
      trace F E (sigma b * truncatedLog p (x : E)) := by
    have hlog : sigma (truncatedLog p (sigma.symm (x : E))) =
        truncatedLog p (sigma (sigma.symm (x : E))) :=
      map_truncatedLog sigma.toRingHom p _
    calc
      _ = trace F E (sigma (b * truncatedLog p (sigma.symm (x : E)))) :=
        (Algebra.trace_eq_of_algEquiv sigma _).symm
      _ = _ := by rw [map_mul, hlog, sigma.apply_symm_apply]
  calc
    _ = chi w := (map_div chi _ _).symm
    _ = tracePullbackAddChar F E Psi (b * truncatedLog p y) := hmodelw
    _ = _ := by
      rw [hephase]
      simp only [tracePullbackAddChar_apply, mul_sub, sub_mul,
        map_sub (trace F E), htrace]

section Diamond

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]
  {p : ℕ} (hp : p.Prime)
  (hG : Nonempty
    (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
  (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
  (D : Total.OddTotalBreakData (F := F) (K := K) hp hG)

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

local notation "B₁" => D.B₁
local notation "B₂" => D.B₂

local instance : PrimeCyclicExtension F B₁ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₁
    (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.2.2.2.1
local instance : PrimeCyclicExtension B₁ K :=
  PrimeCyclicExtension.ofCyclicPrimeExtension B₁ K
    (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.2.2.2.2
local instance : PrimeCyclicExtension F B₂ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₂
    (Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.1

open private realization_tower_data from LanglandsSecondMainLemma.Odd.Models.Realization
open private additiveConductor_of_normCharacterChart from LanglandsSecondMainLemma.Odd.Models.Setup

include hp hG hres hchar D

omit [Module.Free F K] in
/-- The additive conductor at `B₁` is forced by the actual lower norm
character and its full logarithm chart. -/
private theorem commutator_additiveConductor
    (c : ℕ) (hc : c = (D.t₂ + 1) ⌈/⌉ p) (hcpos : 0 < c)
    (tau : NormCharacter F B₂) (htau : tau ≠ 1) (Psi : ContinuousAddChar F)
    (hchart : ∀ z : lattice F (c : ℤ),
      tau.1 (positiveUnitOfLattice F hcpos (-z)) = Psi (truncatedLog p (z : F))) :
    IsAdditiveConductor B₁ (tracePullbackAddChar F B₁ Psi)
      (-((D.tPrime + 1 : ℕ) : ℤ)) := by
  obtain ⟨_, hrF₁, _, _, _⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  obtain ⟨_, hrF₂, _, _, _⟩ := realization_tower_data hp hG hres B₂ D.degree_B₂
  have hPsiF := additiveConductor_of_normCharacterChart F B₂ hp D.odd_prime hchar
    D.degree_B₂ D.B₂_breaks.1 (D.t_pos.trans_le D.t_le_t₂) hrF₂
    hc hcpos tau htau Psi hchart
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F B₁ hrF₁
  have h := additiveConductor_compTrace_cyclicPrime F B₁
    D.B₁_breaks.1 hrF₁ pi hpi hgen hPsiF
  have hdegree : Module.finrank F B₁ = p := D.degree_B₁
  rw [hdegree] at h
  have heq : (p : ℤ) * (-((D.t₂ + 1 : ℕ) : ℤ)) +
      (((p - 1) * (D.t + 1) : ℕ) : ℤ) = -((D.tPrime + 1 : ℕ) : ℤ) := by
    norm_num [D.t₂_eq, D.tPrime_eq, Nat.cast_sub hp.one_le]
    ring
  exact heq ▸ h

omit hres hchar in
/-- The paper's two precision inequalities at the shallow depth
`q = delta + ceil((t+1)/p)`. All lattice depths will be cast to integers. -/
theorem commutator_depths :
    0 < D.delta + (D.t + 1) ⌈/⌉ p ∧
    Models.firstModelDepth D ≤ D.delta + (D.t + 1) ⌈/⌉ p + D.t ∧
    D.tPrime + 1 ≤ p * (D.delta + (D.t + 1) ⌈/⌉ p) := by
  have hc : D.t + 1 ≤ p * ((D.t + 1) ⌈/⌉ p) := le_smul_ceilDiv hp.pos
  have hcpos : 0 < (D.t + 1) ⌈/⌉ p := by
    by_contra h
    have hz : (D.t + 1) ⌈/⌉ p = 0 := by omega
    rw [hz, mul_zero] at hc
    omega
  refine ⟨by omega, ?_, ?_⟩
  · rw [Models.firstModelDepth, ceilDiv_le_iff_le_mul hp.pos,
      Models.firstModelConductor, D.tPrime_eq]
    have hpt : D.t ≤ p * D.t := Nat.le_mul_of_pos_left _ hp.pos
    nlinarith
  · rw [D.tPrime_eq]
    nlinarith

/-- Lemma 8.9 (`O:R:comm-log`) in the genuine totally ramified diamond.
The coefficient is the actual norm `b = N₁ Delta`; the additive phase is
fixed by the actual norm-character chart. The full model hypothesis is
`O:R:model`, constructed for the allowed conjugate by `Models.realization`.

The formula holds for every lower automorphism, hence for the restriction
of the upper automorphism carrying `Delta` to the root near `Delta+1`.
It does not identify the resulting norm character with an arbitrary
generator. The subsequent shift uses the signed coefficient
`s = -elementarySymmetric B₁ K (p-1) Delta` with this same norm and orientation. -/
theorem commutator
    (c : ℕ) (hc : c = (D.t₂ + 1) ⌈/⌉ p) (hcpos : 0 < c)
    (tau : NormCharacter F B₂) (htau : tau ≠ 1) (Psi : ContinuousAddChar F)
    (hchart : ∀ z : lattice F (c : ℤ),
      tau.1 (positiveUnitOfLattice F hcpos (-z)) = Psi (truncatedLog p (z : F)))
    (Delta : K) (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (chi : ContinuousQuasiChar B₁)
    (hmodel : ∀ u : unitFiltration B₁ (Models.firstModelDepth D),
      chi u = tracePullbackAddChar F B₁ Psi
        (norm B₁ K Delta * truncatedLog p (1 - ((u : B₁ˣ) : B₁))))
    (sigma : Gal(B₁/F))
    (x : lattice B₁ ((D.delta + (D.t + 1) ⌈/⌉ p : ℕ) : ℤ)) :
    (Basic.conjugateQuasiChar F B₁ sigma chi / chi)
        (positiveUnitOfLattice B₁ (commutator_depths hp hG D).1 (-x)) =
      tracePullbackAddChar F B₁ Psi
        ((sigma (norm B₁ K Delta) - norm B₁ K Delta) * truncatedLog p (x : B₁)) := by
  obtain ⟨_, hrF₁, hr₁K, _, _⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  have hPsi := commutator_additiveConductor hp hG hres hchar D
    c hc hcpos tau htau Psi hchart
  have hb : norm B₁ K Delta ∈ lattice B₁ (-(D.t : ℤ)) := by
    rw [mem_lattice, ord_norm, hr₁K, one_nsmul, hDelta]
  obtain ⟨hq, hrq, hdepth⟩ := commutator_depths hp hG D
  have hr : 0 < Models.firstModelDepth D := (Models.domains_original D hres).1
  apply commutator_on_model F B₁ hp
    ((residueCharacteristic_extension_eq F B₁).trans hchar)
    D.B₁_breaks.1 D.t_pos hrF₁ hq hr hrq
    (-(D.t : ℤ)) ((D.tPrime + 1 : ℕ) : ℤ) _
    (norm B₁ K Delta) hb Psi (by simpa using hPsi.trivial) chi hmodel sigma x
  push_cast
  have hdepthZ : (D.tPrime : ℤ) + 1 ≤
      (p : ℤ) * ((D.delta : ℤ) + ((D.t + 1) ⌈/⌉ p : ℕ)) := by exact_mod_cast hdepth
  linarith

open private twistNormRanges_ne from LanglandsSecondMainLemma.Odd.Models.TwistFormula

/-- Construct the actual upper norm character from a primitive compatible
pair. Its reciprocal orientation is fixed by `conjugateQuasiChar`, and a
nonidentity automorphism gives exact conductor `T'`. -/
theorem commutator_normCharacter
    (chi₁ : ContinuousQuasiChar B₁) (chi₂ : ContinuousQuasiChar B₂)
    (hcompat : normQuasiChar B₁ K chi₁ = normQuasiChar B₂ K chi₂)
    (hprimitive : ¬ ∃ chi : ContinuousQuasiChar F,
      normQuasiChar F K chi = normQuasiChar B₂ K chi₂)
    (sigma : Gal(B₁/F)) :
    ∃ mu : NormCharacter B₁ K,
      mu.1 = Basic.conjugateQuasiChar F B₁ sigma chi₁ / chi₁ ∧
      (sigma ≠ 1 → mu ≠ 1 ∧
        IsMultiplicativeConductor B₁ mu.1 (D.tPrime + 1)) := by
  obtain ⟨⟨C⟩, _⟩ := Characters.conjugacy hp hG B₁ B₂
    D.degree_B₁ D.degree_B₂ (twistNormRanges_ne hp hG hres hchar D)
    chi₁ chi₂ (normQuasiChar B₂ K chi₂) hcompat rfl hprimitive
  refine ⟨C.quotientEquiv sigma, C.quotient_eq sigma, ?_⟩
  intro hsigma
  have hmu : C.quotientEquiv sigma ≠ 1 := by
    intro h
    exact hsigma (C.quotientEquiv.injective (h.trans C.quotientEquiv.map_one.symm))
  obtain ⟨_, _, hr₁K, _, _⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer B₁ K hr₁K
  exact ⟨hmu, ramifiedNormCharacter_conductor B₁ K D.B₁_breaks.2
    hr₁K pi hpi hgen (C.quotientEquiv sigma) hmu⟩

/-- Supply the normalized commutator directly from the genuine prescribed
primitive pair. The exact coordinate and the allowed first conjugate are
constructed by `O:M:realize`; the phase is the same powered norm-character
phase, and the quotient is constructed by character-theoretic conjugacy.
Thus no logarithmic model or commutator identity is an extra assumption on
the prescribed pair. Both field characteristics and nonunitary characters
are retained. -/
theorem commutator_realization
    (phi₁ : ContinuousQuasiChar B₁) (phi₂ : ContinuousQuasiChar B₂)
    (hcompat : normQuasiChar B₁ K phi₁ = normQuasiChar B₂ K phi₂)
    (hprimitive : ¬ ∃ chi : ContinuousQuasiChar F,
      normQuasiChar F K chi = normQuasiChar B₂ K phi₂)
    (hphi : QuasiCharTrivialOnUnitFiltration B₂ phi₂ (Models.secondModelConductor D))
    (c : ℕ) (hc : c = (D.t₂ + 1) ⌈/⌉ p) (hcpos : 0 < c)
    (tau : NormCharacter F B₂) (htau : tau ≠ 1) (Psi : ContinuousAddChar F)
    (hchart : ∀ z : lattice F (c : ℤ),
      tau.1 (positiveUnitOfLattice F hcpos (-z)) = Psi (truncatedLog p (z : F))) :
    ∃ (j : ℕ) (Delta : K) (a : B₂) (chi : ContinuousQuasiChar B₁) (rho : Gal(B₁/F)),
      0 < j ∧ j < p ∧ tau ^ j ≠ 1 ∧
      Delta ^ p - Delta = algebraMap B₂ K a ∧
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ¬ p ∣ D.t ∧ Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ ∧
      norm B₂ K Delta = a ∧
      chi = Basic.conjugateQuasiChar F B₁ rho phi₁ ∧
      normQuasiChar B₁ K chi = normQuasiChar B₂ K phi₂ ∧
      IsMultiplicativeConductor B₁ chi (Models.firstModelConductor D) ∧
      (∀ (e : ContinuousAddChar F) (alpha : F),
        (∀ z : F, Psi z = e (alpha * z)) →
        ∀ z : F, (Psi ^ j) z = e (((j : F) * alpha) * z)) ∧
      (∀ (psi : ContinuousAddChar F), psi ≠ 1 →
        localConstant B₁ chi (tracePullbackAddChar F B₁ psi) =
          localConstant B₁ phi₁ (tracePullbackAddChar F B₁ psi)) ∧
      ∀ sigma : Gal(B₁/F), ∃ mu : NormCharacter B₁ K,
        mu.1 = Basic.conjugateQuasiChar F B₁ sigma chi / chi ∧
        (sigma ≠ 1 → mu ≠ 1 ∧ IsMultiplicativeConductor B₁ mu.1 (D.tPrime + 1)) ∧
        ∀ x : lattice B₁ ((D.delta + (D.t + 1) ⌈/⌉ p : ℕ) : ℤ),
          mu.1 (positiveUnitOfLattice B₁ (commutator_depths hp hG D).1 (-x)) =
            tracePullbackAddChar F B₁ (Psi ^ j)
              ((sigma (norm B₁ K Delta) - norm B₁ K Delta) * truncatedLog p (x : B₁)) := by
  obtain ⟨j, Delta, a, hjpos, hjp, htauj, hchartj, hphase, hroot, hDelta, _ha,
      hprime, hgen, hnorm, M, _hext₂, _hc₂, rho, hext₁, hpull, hc₁, hconstant⟩ :=
    Models.realization hp hG hres hchar D phi₁ phi₂ hcompat hprimitive hphi
      c hc hcpos tau htau Psi hchart
  let chi := Basic.conjugateQuasiChar F B₁ rho phi₁
  refine ⟨j, Delta, a, chi, rho, hjpos, hjp, htauj, hroot, hDelta,
    hprime, hgen, hnorm, rfl, hpull, hc₁, hphase, hconstant, ?_⟩
  intro sigma
  obtain ⟨mu, hmu, hcond⟩ := commutator_normCharacter hp hG hres hchar D
    chi phi₂ hpull hprimitive sigma
  refine ⟨mu, hmu, hcond, ?_⟩
  intro x
  rw [hmu]
  apply commutator hp hG hres hchar D c hc hcpos (tau ^ j) htauj (Psi ^ j)
    hchartj Delta hDelta chi _ sigma x
  intro u
  exact (DFunLike.congr_fun hext₁ u).trans (M.R₁_apply u)

end Diamond

end

end LanglandsSecondMainLemma.Odd.R2
