import LanglandsFirstMainLemma.Delta.Elementary
import LanglandsFirstMainLemma.Delta.LocalConstantRealization
import LanglandsSecondMainLemma.Odd.Models.TwistFormula
import LanglandsSecondMainLemma.Local.Newton
import LanglandsSecondMainLemma.Characters.Conjugacy

/-!
# Odd / Models / Realization

Blueprint: blueprint/tasks/Odd/Models/Realization.md
Paper: O:M:realize (Theorem 8.8, lines 2741--2774).

`realization` constructs a translated exact Artin--Schreier coordinate and
powered norm character. Its second full model is the actual second character;
its first full model is an allowed conjugate of the actual first character,
with the same norm pullback and canonical local constant. The phase coefficient
is exactly `alpha' = j * alpha` for the original additive character.

The root construction uses Newton lifting in mixed characteristic and an exact
translation in equal characteristic. The coefficient, twisted-estimate,
weighted translated-norm and monomial-phase adapters keep this same coordinate.
Whole-ideal duality, the cubic correction, and the complete lower norm weight
are retained. Unramified rigidity and descending induction prove compatibility;
extension and character-theoretic conjugacy then give the first full model.
-/

namespace LanglandsSecondMainLemma.Odd.Models

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

open private pow_mem_lattice_int natCast_mem_lattice_zero from
  LanglandsSecondMainLemma.Odd.Total.ASApproximation
open private lift_artinSchreier_root exact_coordinate_orders_and_generation from
  LanglandsSecondMainLemma.Odd.Total.ASCoordinate
open private norm_artinSchreierCoordinate from
  LanglandsSecondMainLemma.Odd.Models.Setup

/-- The binomial error for arbitrary integer-depth inputs. This bound is
valid in both field characteristics, including a zero residue prime in the
field. It is the coarser `v(p)-pt` bound sufficient for the Newton step in
`O:M:realize` (lines 2756--2761). -/
theorem realization_binomial_error_mem
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    {p : ℕ} (hp : p.Prime) {V q : ℤ}
    (hpV : (p : L) ∈ lattice L V) {x y : L}
    (hx : x ∈ lattice L q) (hy : y ∈ lattice L q) :
    (x + y) ^ p - x ^ p - y ^ p ∈ lattice L (V + (p : ℤ) * q) := by
  let s : L := ∑ i ∈ Finset.Ioo 0 p,
    x ^ i * y ^ (p - i) * ((Nat.choose p i / p : ℕ) : L)
  have hs : s ∈ lattice L ((p : ℤ) * q) := by
    apply sum_mem_lattice L
    intro i hi
    have hip : i ≤ p := (Finset.mem_Ioo.mp hi).2.le
    have hterm := mul_mem_lattice L
      (mul_mem_lattice L (pow_mem_lattice_int L hx i)
        (pow_mem_lattice_int L hy (p - i)))
      (natCast_mem_lattice_zero L (Nat.choose p i / p))
    convert hterm using 1
    rw [Nat.cast_sub hip]
    ring_nf
  have hformula := (Commute.all x y).add_pow_prime_pow_eq' hp 1
  norm_num only [pow_one] at hformula
  have heq : (x + y) ^ p - x ^ p - y ^ p = (p : L) * s := by
    rw [hformula]
    dsimp only [s]
    ring_nf
  rw [heq]
  exact mul_mem_lattice L hpV hs

/-- The root-construction part of `O:M:realize`. Only the lower bound on
`w` furnished by the approximate norm representative is used; there is no
equation prescribing its norm. The output coefficient is literally
`a + w^p - w`, and the exact root generates the given extension. -/
theorem realization_translate_root
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L] [Module.Finite E L]
    {p t : ℕ} (hp : p.Prime) (hodd : 2 < p) (ht : 0 < t)
    (hdegree : Module.finrank E L = p) (hres : residueDegree E L = 1)
    (hprime : ¬ p ∣ t)
    (hpval : (((p * t : ℕ) : ℤ) : WithTop ℤ) < ord L (p : L))
    (Delta : L) (a w : E)
    (hroot : Delta ^ p - Delta = algebraMap E L a)
    (hDelta : ord L Delta = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hw : w ∈ lattice E (-((t / p : ℕ) : ℤ))) :
    ∃ Delta' : L,
      Delta' ^ p - Delta' = algebraMap E L (a + w ^ p - w) ∧
      ord L Delta' = ((-(t : ℤ) : ℤ) : WithTop ℤ) ∧
      ord E (a + w ^ p - w) = ((-(t : ℤ) : ℤ) : WithTop ℤ) ∧
      Algebra.adjoin E ({Delta'} : Set L) = ⊤ ∧
      norm E L Delta' = a + w ^ p - w := by
  have hram : ramificationIndex E L = p := by
    simpa only [hres, hdegree, mul_one] using
      (finrank_eq_ramificationIndex_mul_residueDegree E L).symm
  have hquot : p * (t / p) < t := by
    have hrem : 0 < t % p := Nat.pos_of_ne_zero (fun h ↦ hprime (Nat.dvd_of_mod_eq_zero h))
    have := Nat.mod_add_div t p
    omega
  have hwmap : ((-(t : ℤ) : ℤ) : WithTop ℤ) < ord L (algebraMap E L w) := by
    rw [ord_algebraMap, hram]
    have hw' := nsmul_le_nsmul_right ((mem_lattice E).1 hw) p
    apply lt_of_lt_of_le _ hw'
    rw [← WithTop.coe_nsmul, WithTop.coe_lt_coe, nsmul_eq_mul]
    have hquotZ : (p : ℤ) * (t / p : ℕ) < t := by exact_mod_cast hquot
    nlinarith
  let d := Delta + algebraMap E L w
  have hd : ord L d = ((-(t : ℤ) : ℤ) : WithTop ℤ) := by
    dsimp only [d]
    rw [ord_add_eq_min L (by rw [hDelta]; exact ne_of_lt hwmap), hDelta,
      min_eq_left hwmap.le]
  have herrorEq : d ^ p - d - algebraMap E L (a + w ^ p - w) =
      (Delta + algebraMap E L w) ^ p - Delta ^ p - (algebraMap E L w) ^ p := by
    rw [map_sub, map_add, map_pow, ← hroot]
    dsimp only [d]
    ring
  have hexists : ∃ Delta' : L,
      Delta' ^ p - Delta' = algebraMap E L (a + w ^ p - w) ∧
      ord L Delta' = ((-(t : ℤ) : ℤ) : WithTop ℤ) := by
    by_cases hpzero : (p : L) = 0
    · refine ⟨d, ?_, hd⟩
      apply sub_eq_zero.mp
      rw [herrorEq]
      have hformula := (Commute.all Delta (algebraMap E L w)).add_pow_prime_pow_eq' hp 1
      simpa [hpzero] using congrArg
        (fun z : L ↦ z - Delta ^ p - (algebraMap E L w) ^ p) hformula
    · obtain ⟨V, hV⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff L).2 hpzero)
      have hVpt : ((p * t : ℕ) : ℤ) < V := by
        rw [← hV] at hpval
        exact WithTop.coe_lt_coe.mp hpval
      apply lift_artinSchreier_root L hp hV.symm hVpt hd
      rw [herrorEq]
      have hbin := realization_binomial_error_mem L hp
        ((mem_lattice L).2 (le_of_eq hV))
        ((mem_lattice L).2 hDelta.ge) ((mem_lattice L).2 hwmap.le)
      have hdepth : V + (p : ℤ) * -(t : ℤ) = V - ((p * t : ℕ) : ℤ) := by
        push_cast
        ring
      simpa only [hdepth] using (mem_lattice L).1 hbin
  obtain ⟨Delta', hroot', hDelta'⟩ := hexists
  obtain ⟨ha', hgen'⟩ := exact_coordinate_orders_and_generation E L hp ht
    hdegree hram Delta' (a + w ^ p - w) hDelta' hprime hroot'
  exact ⟨Delta', hroot', hDelta', ha', hgen',
    norm_artinSchreierCoordinate E L hp hodd hdegree Delta' (a + w ^ p - w) hroot' hgen'⟩

/-- Powering the additive phase by `j` is precisely the paper's coefficient
change `alpha' = j * alpha`, rather than a new independent additive phase. -/
theorem realization_power_coefficient
    {F : Type*} [Field F] [TopologicalSpace F]
    (Psi e : ContinuousAddChar F) (alpha : F)
    (hPsi : ∀ x : F, Psi x = e (alpha * x)) (j : ℕ) (x : F) :
    (Psi ^ j) x = e (((j : F) * alpha) * x) := by
  rw [ContinuousAddChar.pow_apply, hPsi]
  calc
    e (alpha * x) ^ j = e.toAddChar (j • (alpha * x)) :=
      (e.toAddChar.map_nsmul_eq_pow j (alpha * x)).symm
    _ = e (((j : F) * alpha) * x) := by
      change e (j • (alpha * x)) = e (((j : F) * alpha) * x)
      congr 1
      simp only [nsmul_eq_mul, mul_assoc]

/-- Combine the global twisting identity with `O:M:lambdaformula` on the
entire unit group, not just a set of representative values. This is the
second-model identity at lines 2762--2763. -/
theorem realization_second_formula
    (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
    {p q j : ℕ} (hq : 0 < q)
    (phi theta : ContinuousQuasiChar E) (lambda : ContinuousQuasiChar F)
    (Psi : ContinuousAddChar F) (a w : E)
    (hidentity : phi = theta ^ j * normQuasiChar F E lambda)
    (htheta : ∀ u : unitFiltration E q,
      theta u = tracePullbackAddChar F E Psi
        (a * truncatedLog p (1 - ((u : Eˣ) : E))))
    (hlambda : ∀ x : lattice E (q : ℤ),
      normQuasiChar F E lambda (positiveUnitOfLattice E hq (-x)) =
        tracePullbackAddChar F E (Psi ^ j)
          ((w ^ p - w) * truncatedLog p (x : E))) :
    ∀ u : unitFiltration E q,
      phi u = tracePullbackAddChar F E (Psi ^ j)
        ((a + w ^ p - w) * truncatedLog p (1 - ((u : Eˣ) : E))) := by
  intro u
  have hx : 1 - ((u : Eˣ) : E) ∈ lattice E (q : ℤ) := by
    have hu := (mem_unitFiltration_succ_iff_sub_mem_lattice E (q - 1) (u : Eˣ)).1
      (by simpa only [Nat.sub_add_cancel hq] using u.property)
    simpa only [Nat.sub_add_cancel hq, neg_sub] using neg_mem_lattice E hu
  let x : lattice E (q : ℤ) := ⟨1 - ((u : Eˣ) : E), hx⟩
  have hunit : positiveUnitOfLattice E hq (-x) = u := by
    apply Subtype.ext
    apply Units.ext
    simp [x]
  have hl := hlambda x
  rw [hunit] at hl
  calc
    phi u = theta u ^ j * normQuasiChar F E lambda u := by
      rw [hidentity, ContinuousMonoidHom.mul_apply, ContinuousMonoidHom.pow_apply]
    _ = tracePullbackAddChar F E (Psi ^ j) (a * truncatedLog p (x : E)) *
        tracePullbackAddChar F E (Psi ^ j) ((w ^ p - w) * truncatedLog p (x : E)) := by
      rw [htheta, hl]
      rfl
    _ = tracePullbackAddChar F E (Psi ^ j)
        ((a + w ^ p - w) * truncatedLog p (1 - ((u : Eˣ) : E))) := by
      rw [← ContinuousAddChar.map_add_eq_mul]
      congr 1
      dsimp only [x]
      ring

open private twistNormRanges_ne twistNormCharacter_pow_ne_one from
  LanglandsSecondMainLemma.Odd.Models.TwistFormula

open private norm_tower_residueDegrees from
  LanglandsSecondMainLemma.Odd.Models.PolynomialCoefficients

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

-- Use the existing canonical restrictions throughout this local section.
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
local instance : PrimeCyclicExtension B₂ K :=
  PrimeCyclicExtension.ofCyclicPrimeExtension B₂ K
    (Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.2

omit [Module.Free F K] in
include hp hG hres in
private theorem realization_tower_data (E : IntermediateField F K)
    (hE : Module.finrank F E = p) :
    Module.finrank E K = p ∧ residueDegree F E = 1 ∧ residueDegree E K = 1 ∧
      ramificationIndex F E = p ∧ ramificationIndex E K = p := by
  have hd : Module.finrank E K = p :=
    (Basic.intermediateField_tower_compatible hp hG E hE).2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hrF, hrK⟩ := norm_tower_residueDegrees E hres
  refine ⟨hd, hrF, hrK, ?_, ?_⟩
  · simpa only [hE, hrF, mul_one] using
      (finrank_eq_ramificationIndex_mul_residueDegree F E).symm
  · simpa only [hd, hrK, mul_one] using
      (finrank_eq_ramificationIndex_mul_residueDegree E K).symm

include hp hG hres hchar D

omit hchar in
private theorem realization_prime_mem (E : IntermediateField F K)
    (hE : Module.finrank F E = p) :
    (p : E) ∈ lattice E (((p : ℤ) - 1) * D.t₂) := by
  obtain ⟨_, _, _, _, hram⟩ := realization_tower_data hp hG hres E hE
  have hbound : algebraMap E K (p : E) ∈
      lattice K ((p * ((p - 1) * D.t₂) : ℕ) : ℤ) := by
    simpa only [map_natCast, mem_lattice, mul_assoc] using
      Total.oddTotal_primeValuationBound hp hG hres D
  have h := monomialPhase_ceil_depth E K hp.pos hram hbound
  have hceil : (p * ((p - 1) * D.t₂)) ⌈/⌉ p = (p - 1) * D.t₂ := smul_ceilDiv hp.pos _
  simpa only [hceil, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one] using h

/-- The last character-theoretic step of `O:M:realize` (lines 2766--2774).
Any actual first character with the same norm pullback is an allowed
conjugate, and its canonical local constant is unchanged. The commutator
equivalence is constructed from the actual primitive pair by `conjugacy`.
This lemma does not construct an extension of a prescribed first unit model. -/
theorem realization_conjugate_of_samePullback :
    ∀ (phi₁ : ContinuousQuasiChar B₁) (phi₂ : ContinuousQuasiChar B₂),
      normQuasiChar B₁ K phi₁ = normQuasiChar B₂ K phi₂ →
      (¬ ∃ chi : ContinuousQuasiChar F,
        normQuasiChar F K chi = normQuasiChar B₂ K phi₂) →
      ∀ theta₁ : ContinuousQuasiChar B₁,
        normQuasiChar B₁ K theta₁ = normQuasiChar B₂ K phi₂ →
        ∃ sigma : Gal(B₁/F),
          theta₁ = Basic.conjugateQuasiChar F B₁ sigma phi₁ ∧
          ∀ (psi : ContinuousAddChar F), psi ≠ 1 →
            localConstant B₁ theta₁ (tracePullbackAddChar F B₁ psi) =
              localConstant B₁ phi₁ (tracePullbackAddChar F B₁ psi) := by
  intro phi₁ phi₂ hcompat hprimitive theta₁ htheta
  obtain ⟨⟨C⟩, _⟩ := Characters.conjugacy hp hG B₁ B₂
    D.degree_B₁ D.degree_B₂ (twistNormRanges_ne hp hG hres hchar D)
    phi₁ phi₂ (normQuasiChar B₂ K phi₂) hcompat rfl hprimitive
  let mu : NormCharacter B₁ K := ⟨theta₁ / phi₁, by
    apply ContinuousMonoidHom.ext
    intro x
    change theta₁ (normUnits B₁ K x) / phi₁ (normUnits B₁ K x) = 1
    have hval := DFunLike.congr_fun (htheta.trans hcompat.symm) x
    change theta₁ (normUnits B₁ K x) = phi₁ (normUnits B₁ K x) at hval
    rw [hval, div_self']⟩
  obtain ⟨sigma, hsigma⟩ := C.quotientEquiv.surjective mu
  have heq : theta₁ = Basic.conjugateQuasiChar F B₁ sigma phi₁ := by
    rw [C.conjugate_eq_twist, hsigma]
    dsimp only [mu]
    simp [div_eq_mul_inv]
  refine ⟨sigma, heq, ?_⟩
  intro psi hpsi
  rw [heq]
  apply Basic.localConstant_conjugate F B₁ sigma phi₁ (tracePullbackAddChar F B₁ psi)
    (Basic.tracePullbackAddChar_ne_one F B₁ psi hpsi)
  intro x
  simp only [tracePullbackAddChar_apply, Algebra.trace_eq_of_algEquiv sigma x]

omit hchar in
/-- The prescribed first character has the exact first minimal conductor
once its compatible second character has the second minimal conductor.
This uses the two actual upper norm maps and FML's high-conductor formula;
it does not require a first unit-model formula or compatibility of new models.
The natural subtractions in the Herbrand formula are used only after proving
that the conductors are strictly above their respective upper breaks. -/
theorem realization_first_conductor :
    ∀ (phi₁ : ContinuousQuasiChar B₁) (phi₂ : ContinuousQuasiChar B₂),
      normQuasiChar B₁ K phi₁ = normQuasiChar B₂ K phi₂ →
      IsMultiplicativeConductor B₂ phi₂ (secondModelConductor D) →
      IsMultiplicativeConductor B₁ phi₁ (firstModelConductor D) := by
  let E₁ := Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁
  let E₂ := Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
  have hd₁ : Module.finrank B₁ K = p := E₁.2.2.2.2.2.2.2.2.2.2.1
  have hd₂ : Module.finrank B₂ K = p := E₂.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨_, hr₁⟩ := norm_tower_residueDegrees B₁ hres
  obtain ⟨_, hr₂⟩ := norm_tower_residueDegrees B₂ hres
  obtain ⟨pi₁, hpi₁, hgen₁⟩ := monogenicUniformizer B₁ K hr₁
  obtain ⟨pi₂, hpi₂, hgen₂⟩ := monogenicUniformizer B₂ K hr₂
  intro phi₁ phi₂ hcompat hc₂
  have ht₂pos : 0 < D.t₂ := D.t_pos.trans_le D.t_le_t₂
  have hhigh₂ : D.t + 1 < secondModelConductor D := by
    simp only [secondModelConductor]
    omega
  have hdepth₂ : herbrandPsiNat D.t p (secondModelConductor D - 1) + 1 =
      D.tPrime + p * D.t + 1 := by
    rw [herbrandPsiNat_of_break_le D.t p (by omega)]
    have hsub : secondModelConductor D - 1 - D.t = D.t₂ := by
      simp only [secondModelConductor]
      omega
    rw [hsub, D.tPrime_eq, D.t₂_eq]
    ring
  have hcommon := multiplicativeConductor_compNorm_high B₂ K D.B₂_breaks.2 hr₂
    pi₂ hpi₂ hgen₂ hhigh₂ hc₂
  rw [hd₂, hdepth₂] at hcommon
  obtain ⟨n, hn⟩ := exists_isMultiplicativeConductor B₁ phi₁
  have hhigh₁ : D.tPrime + 1 < n := by
    by_contra h
    have htriv := quasiCharTrivialOnUnitFiltration_mono B₁
      (by omega : n ≤ D.tPrime + 1) hn.trivial
    have hpull := (quasiCharTrivialOnUnitFiltration_compNorm_iff_break_succ
      B₁ K D.B₁_breaks.2 hr₁ pi₁ hpi₁ hgen₁ phi₁).2 htriv
    change QuasiCharTrivialOnUnitFiltration K (normQuasiChar B₁ K phi₁)
      (D.tPrime + 1) at hpull
    rw [hcompat] at hpull
    have := hcommon.minimal (D.tPrime + 1) hpull
    have := Nat.mul_pos hp.pos D.t_pos
    omega
  have hpull₁ := multiplicativeConductor_compNorm_high B₁ K D.B₁_breaks.2 hr₁
    pi₁ hpi₁ hgen₁ hhigh₁ hn
  change IsMultiplicativeConductor K (normQuasiChar B₁ K phi₁) _ at hpull₁
  rw [hcompat] at hpull₁
  have heq := hpull₁.unique hcommon
  rw [hd₁, herbrandPsiNat_of_break_le D.tPrime p (by omega)] at heq
  have hcancel : n - 1 - D.tPrime = D.t := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    omega
  have hnval : n = firstModelConductor D := by
    simp only [firstModelConductor]
    omega
  simpa only [hnval] using hn

open private additiveConductor_of_normCharacterChart from
  LanglandsSecondMainLemma.Odd.Models.Setup

set_option maxHeartbeats 1200000 in
/-- Compatibility for a prescribed coordinate and prescribed literal models,
reduced to its monomial trace--norm phases. This reuses the proved polynomial
coefficient bounds, unramified rigidity and descending induction, all of which
accept the actual coordinate. The auxiliary unramified extension and its norm
comparison are constructed here, in both field characteristics.

This applies to the translated generator in `O:M:realize`, lines 2764--2766.
`realization_monomialPhase_of_coordinate` supplies its monomial-phase premise. -/
theorem realization_compatibility_of_monomialPhase :
    ∀ (c : ℕ) (_hc : c = (D.t₂ + 1) ⌈/⌉ p) (hcpos : 0 < c)
      (tau : NormCharacter F B₂) (_htau : tau ≠ 1) (Psi : ContinuousAddChar F),
      (∀ z : lattice F (c : ℤ),
        tau.1 (positiveUnitOfLattice F hcpos (-z)) =
          Psi (truncatedLog p (z : F))) →
      ∀ (Delta : K) (a : B₂),
        ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) →
        ¬ p ∣ D.t → Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ →
        norm B₂ K Delta = a →
        ∀ M : OddMinimalCharacterModels B₁ B₂ p
            (firstModelDepth D) (firstModelConductor D)
            (secondModelDepth D) (secondModelConductor D)
            (tracePullbackAddChar F B₁ Psi) (tracePullbackAddChar F B₂ Psi)
            (norm B₁ K Delta) a,
          (∀ (x : B₂) (j : ℕ), j < p →
            algebraMap B₂ K x * Delta ^ j ∈ lattice K (firstModelDepth D : ℤ) →
            let z := algebraMap B₂ K x * Delta ^ j
            Psi ((trace F B₁ (norm B₁ K Delta * trace B₁ K z) -
              trace F B₂ (a * trace B₂ K z)) +
              Total.weightedNormTraceDefect F B₁ B₂ K Delta z) = 1) →
          ∀ u : Kˣ, u ∈ unitFiltration K (firstModelDepth D) →
            ∃ h₁ : normUnits B₁ K u ∈ unitFiltration B₁ (firstModelDepth D),
            ∃ h₂ : normUnits B₂ K u ∈ unitFiltration B₂ (secondModelDepth D),
              M.R₁ ⟨normUnits B₁ K u, h₁⟩ = M.R₂ ⟨normUnits B₂ K u, h₂⟩ := by
  let E₁ := Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁
  let E₂ := Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
  have hd₁ : Module.finrank B₁ K = p := E₁.2.2.2.2.2.2.2.2.2.2.1
  have hd₂ : Module.finrank B₂ K = p := E₂.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨_, hr₁⟩ := norm_tower_residueDegrees B₁ hres
  obtain ⟨hrF₂, hr₂⟩ := norm_tower_residueDegrees B₂ hres
  have hram : ramificationIndex B₂ K = p := by
    simpa only [hd₂, hr₂, mul_one] using
      (finrank_eq_ramificationIndex_mul_residueDegree B₂ K).symm
  obtain ⟨hq, hq₂, hqt, hq₂t, _, _, hpre, hmap⟩ := domains_original D hres
  have hN₁ : ∀ u : Kˣ, u ∈ unitFiltration K (firstModelDepth D) →
      normUnits B₁ K u ∈ unitFiltration B₁ (firstModelDepth D) := by
    intro u hu
    change u ∈ (unitFiltration B₁ (firstModelDepth D)).comap (normUnits B₁ K)
    rw [hpre]
    exact hu
  have hN₂ : ∀ u : Kˣ, u ∈ unitFiltration K (firstModelDepth D) →
      normUnits B₂ K u ∈ unitFiltration B₂ (secondModelDepth D) := by
    intro u hu
    exact hmap ⟨u, hu, rfl⟩
  intro c hc hcpos tau htau Psi hchart Delta a hDelta hprime hgen hnorm M hmono
  have ha : ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [← hnorm, ord_norm, hr₂, one_nsmul, hDelta]
  have hPsi := additiveConductor_of_normCharacterChart F B₂ hp D.odd_prime hchar
    D.degree_B₂ D.B₂_breaks.1 (D.t_pos.trans_le D.t_le_t₂) hrF₂
    hc hcpos tau htau Psi hchart
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hPsi₁, hPsi₂, _⟩ :=
    oddMinimalCharacters_onUnits hp hG hres hchar D c hc hcpos tau htau Psi hchart
  have hb : ord B₁ (norm B₁ K Delta) = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_norm, hr₁, one_nsmul, hDelta]
  have hm₁ : firstModelConductor D = D.t + (D.tPrime + 1) := by
    simp only [firstModelConductor]; omega
  have hm₂ : secondModelConductor D = D.t + (D.t₂ + 1) := by
    simp only [secondModelConductor]; omega
  let pb : PowerBasis B₂ K :=
    PowerBasis.ofAdjoinEqTop (IsAlgebraic.of_finite B₂ Delta).isIntegral hgen
  have hpbgen : pb.gen = Delta := PowerBasis.ofAdjoinEqTop_gen _ _
  have hpbdim : pb.dim = p := by rw [← pb.finrank]; exact hd₂
  have hdFK : Module.finrank F K = p ^ 2 := by
    have hdF₂ : Module.finrank F B₂ = p := D.degree_B₂
    simpa only [hdF₂, hd₂, pow_two] using
      (Module.finrank_mul_finrank F B₂ K).symm
  obtain ⟨F', fldF', algF', vF', topF', locF', valF',
      K', fldK', algFK', algKK', algF'K', vK', topK', locK', valKK', valF'K',
      towerK, towerF', finF', finF'K', finKK', _, _, hcop, huF', huK', _, hgen',
      hgalF', _, _, hlarge⟩ :=
    BaseChange.largeUnramifiedSquare_exists F K hp D.odd_prime hdFK hres
  letI := fldF'
  letI := algF'
  letI := vF'
  letI := topF'
  letI := locF'
  letI := valF'
  letI := fldK'
  letI := algFK'
  letI := algKK'
  letI := algF'K'
  letI := vK'
  letI := topK'
  letI := locK'
  letI := valKK'
  letI := valF'K'
  letI := towerK
  letI := towerF'
  letI := finF'
  letI := finF'K'
  letI := finKK'
  letI := hgalF'
  let B₁' := BaseChange.field B₁ F' K'
  let B₂' := BaseChange.field B₂ F' K'
  letI := Basic.intermediateFieldValuativeRel B₁'
  letI := Basic.intermediateFieldTopology B₁'
  letI := Basic.intermediateField_localField B₁'
  letI := Basic.intermediateField_lowerValuativeExtension B₁'
  letI := Basic.intermediateField_upperValuativeExtension B₁'
  letI := Basic.intermediateFieldValuativeRel B₂'
  letI := Basic.intermediateFieldTopology B₂'
  letI := Basic.intermediateField_localField B₂'
  letI := Basic.intermediateField_lowerValuativeExtension B₂'
  letI := Basic.intermediateField_upperValuativeExtension B₂'
  obtain ⟨_, _, _, _, _, _, hpre', hmap'⟩ := (domains F' K' D hres huF' hgen').2.1
  have hN₁' : ∀ u : K'ˣ, u ∈ unitFiltration K' (firstModelDepth D) →
      normUnits B₁' K' u ∈ unitFiltration B₁' (firstModelDepth D) := by
    intro u hu
    change u ∈ (unitFiltration B₁' (firstModelDepth D)).comap (normUnits B₁' K')
    rw [hpre']; exact hu
  have hN₂' : ∀ u : K'ˣ, u ∈ unitFiltration K' (firstModelDepth D) →
      normUnits B₂' K' u ∈ unitFiltration B₂' (secondModelDepth D) := by
    intro u hu
    exact hmap' ⟨u, hu, rfl⟩
  have htriv₁ : ∀ x ∈ lattice B₁ (-(D.t : ℤ) + (p * firstModelDepth D : ℕ)),
      tracePullbackAddChar F B₁ Psi x = 1 := by
    intro x hx
    apply hPsi₁.trivial x
    apply lattice_antitone B₁ _ hx
    have hceil := le_smul_ceilDiv (b := firstModelConductor D) hp.pos
    change firstModelConductor D ≤ p * firstModelDepth D at hceil
    rw [hm₁] at hceil
    simp only [neg_neg]
    omega
  have htriv₂ : ∀ x ∈ lattice B₂ (-(D.t : ℤ) + (p * secondModelDepth D : ℕ)),
      tracePullbackAddChar F B₂ Psi x = 1 := by
    intro x hx
    apply hPsi₂.trivial x
    apply lattice_antitone B₂ _ hx
    have hceil := le_smul_ceilDiv (b := secondModelConductor D) hp.pos
    change secondModelConductor D ≤ p * secondModelDepth D at hceil
    rw [hm₂] at hceil
    simp only [neg_neg]
    omega
  have hXi : modelDiscrepancy F B₁ B₂ K M hN₁ hN₂ = 1 := by
    apply modelDiscrepancy_eq_one_of_monomial_coefficients F B₁ B₂ K hp
      hd₁ hd₂ D.B₁_breaks.2 D.B₂_breaks.2 hr₁ hr₂ hq
      (by rw [hm₁]; omega) (by rw [hm₂]; omega)
      hram pb hpbdim (by simpa only [hpbgen] using hDelta) hprime M hN₁ hN₂
    · intro x j hj
      have hj' : algebraMap B₂ K x * Delta ^ (j : ℕ) ∈
          lattice K (firstModelDepth D : ℤ) := by simpa only [hpbgen] using hj
      have h := discrepancyPolynomial_coeff_phase hp hG hres hchar D Delta hDelta
        Psi hPsi (algebraMap B₂ K x * Delta ^ (j : ℕ)) hj'
      dsimp only at h
      rw [hnorm] at h
      have hm := hmono x (j : ℕ) j.isLt hj'
      simpa only [hpbgen] using h.trans hm
    · intro s hqs ih z
      have hs : 0 < s := hq.trans_le hqs
      let Ns₁ : ∀ u : Kˣ, u ∈ unitFiltration K s →
          normUnits B₁ K u ∈ unitFiltration B₁ (firstModelDepth D) :=
        fun u hu => hN₁ u (unitFiltration_antitone K hqs hu)
      let Ns₂ : ∀ u : Kˣ, u ∈ unitFiltration K s →
          normUnits B₂ K u ∈ unitFiltration B₂ (secondModelDepth D) :=
        fun u hu => hN₂ u (unitFiltration_antitone K hqs hu)
      let XiS := modelDiscrepancy F B₁ B₂ K M Ns₁ Ns₂
      have htrivS (u : unitFiltration K s) (hu : (u : Kˣ) ∈ unitFiltration K (s + 1)) :
          XiS u = 1 := ih ⟨u, unitFiltration_antitone K hqs u.property⟩ hu
      let z' : lattice K' (s : ℤ) := ⟨algebraMap K K' (z : K), by
        simpa only [mem_lattice, ord_algebraMap, huK', one_nsmul] using z.property⟩
      refine unitCharacter_norm_rigidity F K F' K' hchar huF' huK' hcop hlarge hs
        (by omega) XiS htrivS Psi _
        (discrepancyPolynomial_coeff_zero F B₁ B₂ K p (norm B₁ K Delta) a z)
        ((discrepancyPolynomial_degree F B₁ B₂ K hp.two_le hd₁ hd₂ (norm B₁ K Delta) a z).1.trans_lt
          (discrepancyPolynomial_degree F B₁ B₂ K hp.two_le hd₁ hd₂ (norm B₁ K Delta) a z).2)
        ?_ z' ?_
      · intro n x
        have hzq := lattice_antitone K (show (firstModelDepth D : ℤ) ≤ s by omega) z.property
        simpa only [hnorm] using (polynomialCoefficients hp hG hres hchar D
          Delta hDelta Psi hPsi z hzq).1 n x
      · intro x
        let us := positiveUnitOfLattice K' hs (-(integralScalarLattice F' K' z' x))
        let u : unitFiltration K' (firstModelDepth D) :=
          ⟨us, unitFiltration_antitone K' hqs us.property⟩
        have hu : ((u : K'ˣ) : K') =
            1 - algebraMap F' K' (x : F') * algebraMap K K' (z : K) := by
          simp only [u, us, coe_positiveUnitOfLattice, Submodule.coe_neg,
            integralScalarLattice_apply, z', sub_eq_add_neg]
        have h₁ := BaseChange.modelNormCharacter_norm_baseChange F' K' hp hG B₁
          D.degree_B₁ hres hchar huF' huK' hgen' hq Psi (norm B₁ K Delta) (-(D.t : ℤ))
          (by rw [mem_lattice, hb]) htriv₁ M.R₁ M.R₁_apply hN₁ hN₁' z x u hu
        have h₂ := BaseChange.modelNormCharacter_norm_baseChange F' K' hp hG B₂
          D.degree_B₂ hres hchar huF' huK' hgen' hq₂ Psi a (-(D.t : ℤ))
          (by rw [mem_lattice, ha]) htriv₂ M.R₂ M.R₂_apply hN₂ hN₂' z x u hu
        simp only [discrepancyPolynomial, Polynomial.eval₂_sub]
        change Psi.compTrace.toAddChar _ = _
        rw [AddChar.map_sub_eq_div]
        exact congrArg₂ (fun x y : ℂˣ => x / y) h₁.symm h₂.symm
  intro u hu
  refine ⟨hN₁ u hu, hN₂ u hu, ?_⟩
  apply div_eq_one.mp
  have h := DFunLike.congr_fun hXi (⟨u, hu⟩ : unitFiltration K (firstModelDepth D))
  simpa only [modelDiscrepancy_apply, MonoidHom.one_apply] using h

/-- The extension and conjugacy equivalence at `O:M:realize`, lines 2764--2774.
For a model whose second character is already the prescribed character,
compatibility on the entire original unit subgroup is equivalent to
realization by an allowed first conjugate, with the same actual norm
pullback, exact first conductor, and canonical local constant.

This isolates the extension and conjugacy steps. The final `realization`
constructs the translated models and proves their compatibility. -/
theorem realization_firstModel_iff_compatibility :
    ∀ (phi₁ : ContinuousQuasiChar B₁) (phi₂ : ContinuousQuasiChar B₂),
      normQuasiChar B₁ K phi₁ = normQuasiChar B₂ K phi₂ →
      (¬ ∃ chi : ContinuousQuasiChar F,
        normQuasiChar F K chi = normQuasiChar B₂ K phi₂) →
      ∀ (Psi₁ : ContinuousAddChar B₁) (Psi₂ : ContinuousAddChar B₂)
        (b : B₁) (a : B₂)
        (M : OddMinimalCharacterModels B₁ B₂ p
          (firstModelDepth D) (firstModelConductor D)
          (secondModelDepth D) (secondModelConductor D) Psi₁ Psi₂ b a),
        phi₂.toMonoidHom.comp (unitFiltration B₂ (secondModelDepth D)).subtype = M.R₂ →
        ((∀ u : Kˣ, u ∈ unitFiltration K (firstModelDepth D) →
          ∃ h₁ : normUnits B₁ K u ∈ unitFiltration B₁ (firstModelDepth D),
          ∃ h₂ : normUnits B₂ K u ∈ unitFiltration B₂ (secondModelDepth D),
            M.R₁ ⟨normUnits B₁ K u, h₁⟩ = M.R₂ ⟨normUnits B₂ K u, h₂⟩) ↔
        ∃ sigma : Gal(B₁/F),
          (Basic.conjugateQuasiChar F B₁ sigma phi₁).toMonoidHom.comp
            (unitFiltration B₁ (firstModelDepth D)).subtype = M.R₁ ∧
          normQuasiChar B₁ K (Basic.conjugateQuasiChar F B₁ sigma phi₁) =
            normQuasiChar B₂ K phi₂ ∧
          IsMultiplicativeConductor B₁ (Basic.conjugateQuasiChar F B₁ sigma phi₁)
            (firstModelConductor D) ∧
          ∀ psi : ContinuousAddChar F, psi ≠ 1 →
            localConstant B₁ (Basic.conjugateQuasiChar F B₁ sigma phi₁)
                (tracePullbackAddChar F B₁ psi) =
              localConstant B₁ phi₁ (tracePullbackAddChar F B₁ psi)) := by
  obtain ⟨_, hr₁⟩ := norm_tower_residueDegrees B₁ hres
  obtain ⟨hq₁, _, hq₁t, _, _, _, hpre, hmap⟩ := domains_original D hres
  intro phi₁ phi₂ hcompat hprimitive Psi₁ Psi₂ b a M hext₂
  constructor
  · intro hmodels
    obtain ⟨theta₁, hext₁, htheta⟩ := compatibleUnitModels_extend B₁ B₂ K
      D.B₁_breaks.2 (hq₁.trans_le hq₁t) hr₁ hq₁t M.R₁ M.R₂ hmodels phi₂ hext₂
    have hc₁ := unitModel_extension_conductor B₁ M.R₁ M.R₁_conductor
      (by simp only [firstModelConductor]; omega) theta₁ hext₁
    obtain ⟨sigma, hsigma, hconstant⟩ := realization_conjugate_of_samePullback
      hp hG hres hchar D phi₁ phi₂ hcompat hprimitive theta₁ htheta
    exact ⟨sigma, hsigma ▸ hext₁, hsigma ▸ htheta, hsigma ▸ hc₁, hsigma ▸ hconstant⟩
  · rintro ⟨sigma, hext₁, hpull, _, _⟩ u hu
    have h₁ : normUnits B₁ K u ∈ unitFiltration B₁ (firstModelDepth D) := by
      change u ∈ (unitFiltration B₁ (firstModelDepth D)).comap (normUnits B₁ K)
      rw [hpre]
      exact hu
    have h₂ : normUnits B₂ K u ∈ unitFiltration B₂ (secondModelDepth D) :=
      hmap ⟨u, hu, rfl⟩
    refine ⟨h₁, h₂, ?_⟩
    exact (DFunLike.congr_fun hext₁ ⟨normUnits B₁ K u, h₁⟩).symm.trans
      ((DFunLike.congr_fun hpull u).trans
        (DFunLike.congr_fun hext₂ ⟨normUnits B₂ K u, h₂⟩))

/-- The complete first-model conclusion of `O:M:realize` for the prescribed
second model, once the translated coordinate's monomial phases are proved.
This is an explicit reduction lemma: it constructs the full extension and
allowed conjugate, with the actual norm pullback and canonical local constant.
The final `realization` discharges the premise for its translated coordinate. -/
theorem realization_firstModel_of_monomialPhase :
    ∀ (phi₁ : ContinuousQuasiChar B₁) (phi₂ : ContinuousQuasiChar B₂),
      normQuasiChar B₁ K phi₁ = normQuasiChar B₂ K phi₂ →
      (¬ ∃ chi : ContinuousQuasiChar F,
        normQuasiChar F K chi = normQuasiChar B₂ K phi₂) →
      ∀ (c : ℕ) (_hc : c = (D.t₂ + 1) ⌈/⌉ p) (hcpos : 0 < c)
        (tau : NormCharacter F B₂) (_htau : tau ≠ 1) (Psi : ContinuousAddChar F),
        (∀ z : lattice F (c : ℤ),
          tau.1 (positiveUnitOfLattice F hcpos (-z)) =
            Psi (truncatedLog p (z : F))) →
        ∀ (Delta : K) (a : B₂),
          ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) →
          ¬ p ∣ D.t → Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ →
          norm B₂ K Delta = a →
          ∀ M : OddMinimalCharacterModels B₁ B₂ p
              (firstModelDepth D) (firstModelConductor D)
              (secondModelDepth D) (secondModelConductor D)
              (tracePullbackAddChar F B₁ Psi) (tracePullbackAddChar F B₂ Psi)
              (norm B₁ K Delta) a,
            phi₂.toMonoidHom.comp
              (unitFiltration B₂ (secondModelDepth D)).subtype = M.R₂ →
            (∀ (x : B₂) (k : ℕ), k < p →
              algebraMap B₂ K x * Delta ^ k ∈ lattice K (firstModelDepth D : ℤ) →
              let z := algebraMap B₂ K x * Delta ^ k
              Psi ((trace F B₁ (norm B₁ K Delta * trace B₁ K z) -
                trace F B₂ (a * trace B₂ K z)) +
                Total.weightedNormTraceDefect F B₁ B₂ K Delta z) = 1) →
        ∃ sigma : Gal(B₁/F),
          (Basic.conjugateQuasiChar F B₁ sigma phi₁).toMonoidHom.comp
            (unitFiltration B₁ (firstModelDepth D)).subtype = M.R₁ ∧
          normQuasiChar B₁ K (Basic.conjugateQuasiChar F B₁ sigma phi₁) =
            normQuasiChar B₂ K phi₂ ∧
          IsMultiplicativeConductor B₁ (Basic.conjugateQuasiChar F B₁ sigma phi₁)
            (firstModelConductor D) ∧
          ∀ psi : ContinuousAddChar F, psi ≠ 1 →
            localConstant B₁ (Basic.conjugateQuasiChar F B₁ sigma phi₁)
                (tracePullbackAddChar F B₁ psi) =
              localConstant B₁ phi₁ (tracePullbackAddChar F B₁ psi) := by
  intro phi₁ phi₂ hcompat hprimitive c hc hcpos tau htau Psi hchart
    Delta a hDelta hprime hgen hnorm M hext₂ hmono
  exact (realization_firstModel_iff_compatibility hp hG hres hchar D
    phi₁ phi₂ hcompat hprimitive _ _ _ _ M hext₂).mp
      (realization_compatibility_of_monomialPhase hp hG hres hchar D
        c hc hcpos tau htau Psi hchart Delta a hDelta hprime hgen hnorm M hmono)

open private truncatedLogUnitCharacter_exists from
  LanglandsSecondMainLemma.Odd.Models.Setup

set_option maxHeartbeats 1200000 in
/-- The proved second-model part of Paper 8.8. Starting with the actual
primitive pair, construct the powered norm character, the translated exact
generator, and both literal unit-model formulas. The prescribed second
character restricts to the second model on its entire domain.

The final `realization` proves compatibility for this same coordinate and
extends the first model to an allowed conjugate. -/
theorem realization_secondModels :
    ∀ (phi₁ : ContinuousQuasiChar B₁) (phi₂ : ContinuousQuasiChar B₂),
      normQuasiChar B₁ K phi₁ = normQuasiChar B₂ K phi₂ →
      (¬ ∃ chi : ContinuousQuasiChar F,
        normQuasiChar F K chi = normQuasiChar B₂ K phi₂) →
      QuasiCharTrivialOnUnitFiltration B₂ phi₂ (secondModelConductor D) →
      ∀ (c : ℕ) (_hc : c = (D.t₂ + 1) ⌈/⌉ p) (hcpos : 0 < c)
        (tau : NormCharacter F B₂) (_htau : tau ≠ 1) (Psi : ContinuousAddChar F),
        (∀ z : lattice F (c : ℤ),
          tau.1 (positiveUnitOfLattice F hcpos (-z)) =
            Psi (truncatedLog p (z : F))) →
        ∃ (j : ℕ) (Delta : K) (a : B₂),
          0 < j ∧ j < p ∧ tau ^ j ≠ 1 ∧
          (∀ z : lattice F (c : ℤ),
            (tau ^ j).1 (positiveUnitOfLattice F hcpos (-z)) =
              (Psi ^ j) (truncatedLog p (z : F))) ∧
          Delta ^ p - Delta = algebraMap B₂ K a ∧
          ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
          ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
          ¬ p ∣ D.t ∧ Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ ∧
          norm B₂ K Delta = a ∧
          ∃ M : OddMinimalCharacterModels B₁ B₂ p
              (firstModelDepth D) (firstModelConductor D)
              (secondModelDepth D) (secondModelConductor D)
              (tracePullbackAddChar F B₁ (Psi ^ j))
              (tracePullbackAddChar F B₂ (Psi ^ j)) (norm B₁ K Delta) a,
            phi₂.toMonoidHom.comp (unitFiltration B₂ (secondModelDepth D)).subtype = M.R₂ ∧
            IsMultiplicativeConductor B₂ phi₂ (secondModelConductor D) := by
  intro phi₁ phi₂ hcompat hprimitive hphi c hc hcpos tau htau Psi hchart
  let E₂ := Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
  have hd₂ : Module.finrank B₂ K = p := E₂.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨_, hr₁⟩ := norm_tower_residueDegrees B₁ hres
  obtain ⟨hrF₂, hr₂⟩ := norm_tower_residueDegrees B₂ hres
  obtain ⟨Delta, a, hroot, hDelta, _, hprime, _, _, M,
    theta₁, theta₂, _, hext₂, _, _, _,
    j, lambda, gamma, w, hjpos, hjp, hidentity, _, _, _, hw,
    _, _, _, _, _, hformula⟩ :=
    twistFormula hp hG hres hchar D phi₁ phi₂ hcompat hprimitive hphi
      c hc hcpos tau htau Psi hchart
  have htauj := twistNormCharacter_pow_ne_one F B₂ D.degree_B₂ D.B₂_breaks.1
    hrF₂ hjpos hjp tau htau
  have hchartj : ∀ z : lattice F (c : ℤ),
      (tau ^ j).1 (positiveUnitOfLattice F hcpos (-z)) =
        (Psi ^ j) (truncatedLog p (z : F)) := by
    intro z
    simpa only [NormCharacter.coe_pow, ContinuousMonoidHom.pow_apply,
      ContinuousAddChar.pow_apply] using congrArg (fun v : ℂˣ ↦ v ^ j) (hchart z)
  have hpval : (((p * D.t : ℕ) : ℤ) : WithTop ℤ) < ord K (p : K) := by
    have hupper : D.t < (p - 1) * D.t₂ := by
      have hdouble : 2 * D.t ≤ (p - 1) * D.t₂ :=
        Nat.mul_le_mul (by have := D.odd_prime; omega) D.t_le_t₂
      have := D.t_pos
      omega
    have hmul : p * D.t < p * (p - 1) * D.t₂ := by
      simpa only [Nat.mul_assoc] using Nat.mul_lt_mul_of_pos_left hupper hp.pos
    exact (WithTop.coe_lt_coe.mpr (by exact_mod_cast hmul)).trans_le
      (Total.oddTotal_primeValuationBound hp hG hres D)
  obtain ⟨Delta', hroot', hDelta', ha', hgen', hnorm'⟩ :=
    realization_translate_root B₂ K hp D.odd_prime D.t_pos hd₂ hr₂ hprime hpval
      Delta a w hroot hDelta hw
  let a' := a + w ^ p - w
  obtain ⟨hq₁, hq₂, hq₁t, hq₂t, _⟩ := domains_original D hres
  have hphiFormula := realization_second_formula F B₂ hq₂ phi₂ theta₂ lambda Psi a w
    hidentity (fun u ↦ (DFunLike.congr_fun hext₂ u).trans (M.R₂_apply u)) (hformula hq₂)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hPsi₁, hPsi₂, _⟩ :=
    oddMinimalCharacters_onUnits hp hG hres hchar D c hc hcpos (tau ^ j) htauj
      (Psi ^ j) hchartj
  have hb' : ord B₁ (norm B₁ K Delta') = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_norm, hr₁, one_nsmul, hDelta']
  have hm₁ : firstModelConductor D = D.t + (D.tPrime + 1) := by
    simp only [firstModelConductor]
    omega
  have hm₂ : secondModelConductor D = D.t + (D.t₂ + 1) := by
    simp only [secondModelConductor]
    omega
  obtain ⟨R₁, hR₁, hR₁cond⟩ := truncatedLogUnitCharacter_exists B₁ hp
    ((residueCharacteristic_extension_eq F B₁).trans hchar)
    D.t_pos (Nat.zero_lt_succ _) hm₁ hq₁
    (show firstModelDepth D ≤ firstModelConductor D - 1 by rw [hm₁]; omega)
    (show firstModelConductor D ≤ p * firstModelDepth D from
      le_smul_ceilDiv (b := firstModelConductor D) hp.pos)
    (norm B₁ K Delta') hb' (tracePullbackAddChar F B₁ (Psi ^ j)) hPsi₁
  obtain ⟨R₂, hR₂, hR₂cond⟩ := truncatedLogUnitCharacter_exists B₂ hp
    ((residueCharacteristic_extension_eq F B₂).trans hchar)
    D.t_pos (Nat.zero_lt_succ _) hm₂ hq₂
    (show secondModelDepth D ≤ secondModelConductor D - 1 by rw [hm₂]; omega)
    (show secondModelConductor D ≤ p * secondModelDepth D from
      le_smul_ceilDiv (b := secondModelConductor D) hp.pos)
    a' ha' (tracePullbackAddChar F B₂ (Psi ^ j)) hPsi₂
  let M' : OddMinimalCharacterModels B₁ B₂ p
      (firstModelDepth D) (firstModelConductor D)
      (secondModelDepth D) (secondModelConductor D)
      (tracePullbackAddChar F B₁ (Psi ^ j)) (tracePullbackAddChar F B₂ (Psi ^ j))
      (norm B₁ K Delta') a' := ⟨R₁, R₂, hR₁, hR₂, hR₁cond, hR₂cond⟩
  have hext' : phi₂.toMonoidHom.comp
      (unitFiltration B₂ (secondModelDepth D)).subtype = M'.R₂ := by
    apply MonoidHom.ext
    intro u
    exact (hphiFormula u).trans (hR₂ u).symm
  exact ⟨j, Delta', a', hjpos, hjp, htauj, hchartj, hroot', hDelta', ha', hprime,
    hgen', hnorm', M', hext', unitModel_extension_conductor B₂ M'.R₂ M'.R₂_conductor
      (by rw [hm₂]; have := D.t_pos; omega) phi₂ hext'⟩

open private coefficient_bounds_of_coordinate from
  LanglandsSecondMainLemma.Odd.Total.CoefficientExtraction

-- Keep the existing public freeness parameter, even though the induction no longer needs it.
open Total in
/-- The coefficient estimate `O:A:lem:coeff` for the prescribed exact root
used in `O:M:realize`. In particular this applies to the root returned by
`realization_secondModels`, without replacing it by the existential witness
of `Total.coefficientExtraction`.

The simultaneous induction uses the proved conjugates of this very root,
the original preliminary coefficient estimate, and the original Hensel-error
and root-of-unity averaging lemmas. Both field characteristics and zero
coefficients are covered by the extended valuations. -/
theorem realization_coefficientExtraction_of_coordinate :
    ∀ (Delta : K) (a : B₂),
      Delta ^ p - Delta = algebraMap B₂ K a →
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) →
      ¬ p ∣ D.t → Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ →
      ∀ (theta : B₁) (Y : Fin p → B₂),
        algebraMap B₁ K theta =
          ∑ i : Fin p, algebraMap B₂ K (Y i) * Delta ^ (i : ℕ) →
        ∀ i : Fin p,
          ord B₁ theta + ((((i : ℕ) * D.t : ℕ) : ℤ) : WithTop ℤ) ≤
            ord B₂ (Y i) := by
  intro Delta a hroot hDelta hprime hgen
  exact coefficient_bounds_of_coordinate hp hG hres hchar D hroot hDelta hprime hgen

open private affine_bound_withTop from
  LanglandsSecondMainLemma.Odd.Total.TwistedEstimates

open Total in
set_option maxHeartbeats 1200000 in
/-- The crossed trace and elementary-symmetric bounds `O:A:lem:twisted`
for the prescribed root in `O:M:realize`. The coefficient estimate is
constructed by `realization_coefficientExtraction_of_coordinate`; whole-ideal
trace duality and Newton identities then apply to this same root.

This includes the zero-th trace, arbitrary coefficients (including zero),
and the bound for the actual exceptional coefficient
`s = -elementarySymmetric B₁ K (p - 1) Delta`. -/
theorem realization_twistedEstimates_of_coordinate :
    ∀ (Delta : K) (a : B₂),
      Delta ^ p - Delta = algebraMap B₂ K a →
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) →
      ¬ p ∣ D.t → Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ →
      (∀ (Y : B₂) (i : ℕ), i < p →
        ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) + ord B₂ Y ≤
          ord B₁ (trace B₁ K (algebraMap B₂ K Y * Delta ^ i))) ∧
      (∀ (Y : B₂) (i : ℕ), 1 ≤ i → i < p →
        ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) + i • ord B₂ Y ≤
          ord B₁ (elementarySymmetric B₁ K i (algebraMap B₂ K Y * Delta))) ∧
      (∀ i : ℕ, 1 ≤ i → i < p →
        ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) ≤
          ord B₁ (elementarySymmetric B₁ K i Delta)) ∧
      ((((p : ℤ) - 1) * D.delta : ℤ) : WithTop ℤ) ≤
        ord B₁ (-elementarySymmetric B₁ K (p - 1) Delta) := by
  have hdegreeLower₁ : Module.finrank F B₁ = p := D.degree_B₁
  have hdegreeLower₂ : Module.finrank F B₂ = p := D.degree_B₂
  obtain ⟨_, hresF₁, _, _, _⟩ := realization_tower_data hp hG hres B₁ D.degree_B₁
  obtain ⟨hdegreeUpper₂, hresF₂, hres₂K, _, hram₂K⟩ :=
    realization_tower_data hp hG hres B₂ D.degree_B₂
  have hbreak₁ : PrimeCyclicExtension.IsLowerBreak F B₁ D.t := D.B₁_breaks.1
  have hbreak₂ : PrimeCyclicExtension.IsLowerBreak F B₂ D.t₂ := D.B₂_breaks.1
  intro Delta a hroot hDelta hprime hgen
  obtain ⟨ha, _⟩ := exact_coordinate_orders_and_generation B₂ K hp D.t_pos
    hdegreeUpper₂ hram₂K Delta a hDelta hprime hroot
  have hcoeff := realization_coefficientExtraction_of_coordinate hp hG hres hchar D
  have hcoeff := hcoeff Delta a hroot hDelta hprime hgen
  have hdiff₁ : Local.differentIdealExponent F B₁ =
      ((p : ℤ) - 1) * ((D.t : ℤ) + 1) := by
    rw [Local.differentIdealExponent_eq_fml F B₁ hresF₁]
    obtain ⟨pi, hpi, hgen⟩ :=
      exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one F B₁ hresF₁
    rw [differentExponent_eq F B₁ hbreak₁ pi hpi hgen, hdegreeLower₁]
    push_cast [Nat.cast_sub hp.one_le]
    rfl
  have hdiff₂ : Local.differentIdealExponent F B₂ =
      ((p : ℤ) - 1) * ((D.t₂ : ℤ) + 1) := by
    rw [Local.differentIdealExponent_eq_fml F B₂ hresF₂]
    obtain ⟨pi, hpi, hgen⟩ :=
      exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one F B₂ hresF₂
    rw [differentExponent_eq F B₂ hbreak₂ pi hpi hgen, hdegreeLower₂]
    push_cast [Nat.cast_sub hp.one_le]
    rfl
  have hpval : (p : B₂) ∈ lattice B₂ (((p : ℤ) - 1) * D.t) :=
    lattice_antitone B₂ (mul_le_mul_of_nonneg_left
      (by exact_mod_cast D.t_le_t₂) (by have := hp.one_lt; omega))
      (realization_prime_mem hp hG hres D B₂ D.degree_B₂)
  let pb : PowerBasis B₂ K :=
    PowerBasis.ofAdjoinEqTop (IsAlgebraic.of_finite B₂ Delta).isIntegral hgen
  have hpbgen : pb.gen = Delta := PowerBasis.ofAdjoinEqTop_gen _ _
  have hpbdim : pb.dim = p := by rw [← pb.finrank]; exact hdegreeUpper₂
  have hexp : ∀ theta : B₁, ∃ Z : Fin p → B₂,
      algebraMap B₁ K theta = ∑ r : Fin p, algebraMap B₂ K (Z r) * pb.gen ^ (r : ℕ) ∧
      ∀ r : Fin p, ord B₁ theta + (((r : ℕ) * (D.t : ℤ) : ℤ) : WithTop ℤ) ≤ ord B₂ (Z r) := by
    intro theta
    let Z : Fin p → B₂ := fun r => pb.basis.repr (algebraMap B₁ K theta) (Fin.cast hpbdim.symm r)
    have hzexp : algebraMap B₁ K theta =
        ∑ r : Fin p, algebraMap B₂ K (Z r) * pb.gen ^ (r : ℕ) := by
      let e : Fin p ≃ Fin pb.dim := (Fin.castOrderIso hpbdim.symm).toEquiv
      have hs := pb.basis.sum_repr (algebraMap B₁ K theta)
      rw [← e.sum_comp] at hs
      refine hs.symm.trans ?_
      apply Finset.sum_congr rfl
      intro r hr
      rw [pb.basis_eq_pow, Algebra.smul_def]
      rfl
    refine ⟨Z, hzexp, ?_⟩
    intro r
    have hz := hcoeff theta Z (by simpa [hpbgen] using hzexp) r
    simpa only [Nat.cast_mul] using hz
  have htr : ∀ (Y : B₂) (q : ℤ), Y ∈ lattice B₂ q → ∀ i : ℕ, i < p →
      trace B₁ K (algebraMap B₂ K Y * Delta ^ i) ∈
        lattice B₁ (((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t + q) := by
    intro Y q hY i hi
    have h := crossedTrace_of_coefficientExtraction F B₁ B₂ K pb D.odd_prime hpbdim
      a (by simpa [hpbgen] using hroot) D.t D.t₂ (by positivity)
      (by rw [mem_lattice, ha]) hdiff₁ hdiff₂ hpval hexp Y q hY i hi
    simpa only [hpbgen] using h
  have hC : 0 ≤ ((p : ℤ) - 1) * D.t₂ := by
    exact mul_nonneg (by have := hp.one_lt; omega) (Int.natCast_nonneg _)
  have hchar₁ : residueCharacteristic B₁ = p :=
    (residueCharacteristic_extension_eq F B₁).trans hchar
  have hsym : ∀ (Y : B₂) (q : ℤ), Y ∈ lattice B₂ q → ∀ i : ℕ, 1 ≤ i → i < p →
      ((((p : ℤ) - 1) * D.t₂ + (i : ℤ) * (q - D.t) : ℤ) : WithTop ℤ) ≤
        ord B₁ (elementarySymmetric B₁ K i (algebraMap B₂ K Y * Delta)) := by
    intro Y q hY i hi hip
    apply twistedSymmetric_of_powerTrace B₁ K _ _ _ hC _ i hi (by simpa [hchar₁] using hip)
    intro j hj hjp
    have hpow : Y ^ j ∈ lattice B₂ ((j : ℤ) * q) := by
      rw [mem_lattice, ord_pow]
      rw [mem_lattice] at hY
      simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using nsmul_le_nsmul_right hY j
    have h := htr (Y ^ j) ((j : ℤ) * q) hpow j (by simpa [hchar₁] using hjp)
    rw [mem_lattice] at h
    convert h using 1
    · congr 1; ring
    · rw [mul_pow, ← map_pow]
  have hsymOrd : ∀ (Y : B₂) (i : ℕ), 1 ≤ i → i < p →
      ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) + i • ord B₂ Y ≤
        ord B₁ (elementarySymmetric B₁ K i (algebraMap B₂ K Y * Delta)) := by
    intro Y i hi hip
    apply affine_bound_withTop _ _ _ i hi
    intro q hq
    convert hsym Y q hq i hi hip using 1
    congr 1
    ring
  have hei : ∀ i : ℕ, 1 ≤ i → i < p →
      ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) ≤
        ord B₁ (elementarySymmetric B₁ K i Delta) := by
    intro i hi hip
    simpa using hsymOrd 1 i hi hip
  refine ⟨?_, hsymOrd, hei, ?_⟩
  · intro Y i hip
    simpa only [one_nsmul] using affine_bound_withTop (ord B₂ Y)
      (ord B₁ (trace B₁ K (algebraMap B₂ K Y * Delta ^ i)))
      (((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t) 1 (by omega)
      (by intro q hq; simpa using htr Y q hq i hip)
  · have h := hei (p - 1) (by have := hp.one_lt; omega) (by have := hp.pos; omega)
    rw [ord_neg]
    convert h using 1
    congr 1
    rw [D.t₂_eq, Nat.cast_add, Nat.cast_sub hp.one_le]
    ring

open private TranslatedNormProof.coordinate_congruence from
  LanglandsSecondMainLemma.Odd.Total.TranslatedNorm

open Total in
/-- The weighted translated-root comparison `O:A:lem:translate` for a prescribed
exact coordinate. All conjugate corrections and twisted estimates are proved
for this coordinate. The weight is the actual lower norm, and the precision
retains the integer depth `R = p*v - (k-1)*t`, including zero coefficients. -/
theorem realization_translatedNorm_of_coordinate :
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (Delta : K) (a : B₂),
      Delta ^ p - Delta = algebraMap B₂ K a →
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) →
      ¬ p ∣ D.t → Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ →
      ∀ (x : B₂) (v : ℤ) (k : ℕ), x ∈ lattice B₂ v → 1 ≤ k → k ≤ p →
        let R := (p : ℤ) * v - ((k : ℤ) - 1) * D.t
        let X := algebraMap F B₁ (norm F B₂ x)
        1 ≤ R →
        X * algebraMap F B₁ (trace F B₁ (norm B₁ K Delta ^ k)) -
          X * (∑ j : ZMod p,
            norm B₁ K (Delta + algebraMap F K (primeTeichmuller F p hchar j : F)) ^ k) ∈
              lattice B₁ ((p : ℤ) * D.t₂ + R) := by
  dsimp only
  letI : Fact p.Prime := ⟨hp⟩
  intro Delta a hroot hDelta hprime hgen x v k hx _hk _hkp _hR
  obtain ⟨hdegree, _, _, _, hram⟩ :=
    realization_tower_data hp hG hres B₂ D.degree_B₂
  obtain ⟨ha, _⟩ := exact_coordinate_orders_and_generation B₂ K hp D.t_pos
    hdegree hram Delta a hDelta hprime hroot
  obtain ⟨htw, hsym, _, _⟩ := realization_twistedEstimates_of_coordinate
    hp hG hres hchar D Delta a hroot hDelta hprime hgen
  exact TranslatedNormProof.coordinate_congruence hp hG hres hchar D
    Delta a hroot hDelta ha hgen htw hsym x v k hx

open private MonomialCoordinate MonomialCoordinate.mk MonomialCoordinate.Delta
  MonomialCoordinate.a monomialPhase_coordinate_phase from
  LanglandsSecondMainLemma.Odd.Models.MonomialPhase

/-- Equip the prescribed root with the existing monomial-coordinate estimates.
The two equalities retain the actual generator and its coefficient when the
private phase argument unpacks the coordinate. -/
private theorem realization_monomialCoordinate_of_coordinate [Fact p.Prime]
    (Delta : K) (a : B₂)
    (hroot : Delta ^ p - Delta = algebraMap B₂ K a)
    (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ D.t) (hgen : Algebra.adjoin B₂ ({Delta} : Set K) = ⊤) :
    ∃ C : MonomialCoordinate D hchar,
      MonomialCoordinate.Delta C = Delta ∧ MonomialCoordinate.a C = a := by
  obtain ⟨hdegree, _, _, _, hram⟩ :=
    realization_tower_data hp hG hres B₂ D.degree_B₂
  obtain ⟨ha, _⟩ := exact_coordinate_orders_and_generation B₂ K hp D.t_pos
    hdegree hram Delta a hDelta hprime hroot
  obtain ⟨_, _, hei, hsord⟩ := realization_twistedEstimates_of_coordinate
    hp hG hres hchar D Delta a hroot hDelta hprime hgen
  exact ⟨MonomialCoordinate.mk (D := D) (hchar := hchar)
    (Delta := Delta) (a := a) (root := hroot) (ord_Delta := hDelta) (ord_a := ha)
    (prime_not_dvd := hprime) (adjoin_eq_top := hgen)
    (coefficient_bound := realization_coefficientExtraction_of_coordinate
      hp hG hres hchar D Delta a hroot hDelta hprime hgen)
    (symmetric_bound := hei) (scalar_bound := hsord)
    (translated_norm := realization_translatedNorm_of_coordinate
      hp hG hres hchar D Delta a hroot hDelta hprime hgen), rfl, rfl⟩

open Total in
/-- Paper `O:M:monophase` for every prescribed exact coordinate. The coefficient,
weighted norm, exceptional projection and whole-domain conversion estimates
are all constructed for this coordinate and the actual norm character. -/
theorem realization_monomialPhase_of_coordinate :
    ∀ (Delta : K) (a : B₂),
      Delta ^ p - Delta = algebraMap B₂ K a →
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) →
      ¬ p ∣ D.t → Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ →
      ∀ (c : ℕ) (_hc : c = (D.t₂ + 1) ⌈/⌉ p) (hcpos : 0 < c)
        (tau : NormCharacter F B₂) (_htau : tau ≠ 1) (Psi : ContinuousAddChar F),
        (∀ z : lattice F (c : ℤ),
          tau.1 (positiveUnitOfLattice F hcpos (-z)) =
            Psi (truncatedLog p (z : F))) →
        ∀ (x : B₂) (j : ℕ), j < p →
          algebraMap B₂ K x * Delta ^ j ∈ lattice K (firstModelDepth D : ℤ) →
          let z := algebraMap B₂ K x * Delta ^ j
          Psi ((trace F B₁ (norm B₁ K Delta * trace B₁ K z) -
            trace F B₂ (a * trace B₂ K z)) +
            weightedNormTraceDefect F B₁ B₂ K Delta z) = 1 := by
  intro Delta a hroot hDelta hprime hgen
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨C, hCDelta, hCa⟩ := realization_monomialCoordinate_of_coordinate
    hp hG hres hchar D Delta a hroot hDelta hprime hgen
  letI : IsGalois F (IntermediateField.fixedField D.H₁) := inferInstanceAs (IsGalois F B₁)
  letI : PrimeCyclicExtension F (IntermediateField.fixedField D.H₂) :=
    inferInstanceAs (PrimeCyclicExtension F B₂)
  simpa only [OddTotalBreakData.B₁, OddTotalBreakData.B₂, hCDelta, hCa] using
    monomialPhase_coordinate_phase D hres hchar C

/-- **Actual realization, Paper 8.8 (`O:M:realize`).** The given primitive
compatible pair at the minimal conductor bound yields a powered actual norm
character and an exact coordinate with both full unit models. The second
extension is literally `phi₂`; the first is the displayed Galois conjugate
of `phi₁`, with the same actual norm pullback and canonical local constant.
For any expression of the original phase as `e(alpha * x)`, the new phase
uses the coefficient `j * alpha`. No norm equation or model compatibility
is assumed. -/
theorem realization :
    ∀ (phi₁ : ContinuousQuasiChar B₁) (phi₂ : ContinuousQuasiChar B₂),
      normQuasiChar B₁ K phi₁ = normQuasiChar B₂ K phi₂ →
      (¬ ∃ chi : ContinuousQuasiChar F,
        normQuasiChar F K chi = normQuasiChar B₂ K phi₂) →
      QuasiCharTrivialOnUnitFiltration B₂ phi₂ (secondModelConductor D) →
      ∀ (c : ℕ) (_hc : c = (D.t₂ + 1) ⌈/⌉ p) (hcpos : 0 < c)
        (tau : NormCharacter F B₂) (_htau : tau ≠ 1) (Psi : ContinuousAddChar F),
        (∀ z : lattice F (c : ℤ),
          tau.1 (positiveUnitOfLattice F hcpos (-z)) =
            Psi (truncatedLog p (z : F))) →
        ∃ (j : ℕ) (Delta : K) (a : B₂),
          0 < j ∧ j < p ∧ tau ^ j ≠ 1 ∧
          (∀ z : lattice F (c : ℤ),
            (tau ^ j).1 (positiveUnitOfLattice F hcpos (-z)) =
              (Psi ^ j) (truncatedLog p (z : F))) ∧
          (∀ (e : ContinuousAddChar F) (alpha : F),
            (∀ x : F, Psi x = e (alpha * x)) →
            ∀ x : F, (Psi ^ j) x = e (((j : F) * alpha) * x)) ∧
          Delta ^ p - Delta = algebraMap B₂ K a ∧
          ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
          ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
          ¬ p ∣ D.t ∧ Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ ∧
          norm B₂ K Delta = a ∧
          ∃ M : OddMinimalCharacterModels B₁ B₂ p
              (firstModelDepth D) (firstModelConductor D)
              (secondModelDepth D) (secondModelConductor D)
              (tracePullbackAddChar F B₁ (Psi ^ j))
              (tracePullbackAddChar F B₂ (Psi ^ j)) (norm B₁ K Delta) a,
            phi₂.toMonoidHom.comp (unitFiltration B₂ (secondModelDepth D)).subtype = M.R₂ ∧
            IsMultiplicativeConductor B₂ phi₂ (secondModelConductor D) ∧
            ∃ sigma : Gal(B₁/F),
              (Basic.conjugateQuasiChar F B₁ sigma phi₁).toMonoidHom.comp
                (unitFiltration B₁ (firstModelDepth D)).subtype = M.R₁ ∧
              normQuasiChar B₁ K (Basic.conjugateQuasiChar F B₁ sigma phi₁) =
                normQuasiChar B₂ K phi₂ ∧
              IsMultiplicativeConductor B₁ (Basic.conjugateQuasiChar F B₁ sigma phi₁)
                (firstModelConductor D) ∧
              ∀ psi : ContinuousAddChar F, psi ≠ 1 →
                localConstant B₁ (Basic.conjugateQuasiChar F B₁ sigma phi₁)
                    (tracePullbackAddChar F B₁ psi) =
                  localConstant B₁ phi₁ (tracePullbackAddChar F B₁ psi) := by
  intro phi₁ phi₂ hcompat hprimitive hphi c hc hcpos tau htau Psi hchart
  obtain ⟨j, Delta, a, hjpos, hjp, htauj, hchartj, hroot, hDelta, ha, hprime,
      hgen, hnorm, M, hext₂, hc₂⟩ := realization_secondModels
    hp hG hres hchar D phi₁ phi₂ hcompat hprimitive hphi c hc hcpos tau htau Psi hchart
  have hmono := realization_monomialPhase_of_coordinate hp hG hres hchar D
    Delta a hroot hDelta hprime hgen c hc hcpos (tau ^ j) htauj (Psi ^ j) hchartj
  obtain ⟨sigma, hext₁, hpull, hc₁, hconstant⟩ := realization_firstModel_of_monomialPhase
    hp hG hres hchar D phi₁ phi₂ hcompat hprimitive c hc hcpos (tau ^ j) htauj
      (Psi ^ j) hchartj Delta a hDelta hprime hgen hnorm M hext₂ hmono
  refine ⟨j, Delta, a, hjpos, hjp, htauj, hchartj, ?_, hroot, hDelta, ha, hprime,
    hgen, hnorm, M, hext₂, hc₂, sigma, hext₁, hpull, hc₁, hconstant⟩
  intro e alpha he x
  exact realization_power_coefficient Psi e alpha he j x

end Diamond

end

end LanglandsSecondMainLemma.Odd.Models
