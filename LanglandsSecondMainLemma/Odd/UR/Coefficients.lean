import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Odd.UR.NormChoice
import LanglandsSecondMainLemma.Odd.NormLog
import LanglandsSecondMainLemma.Odd.NormPhase

/-!
# Full logarithm coefficients of the actual unramified–ramified pair

Paper: Proposition 6.9 (`O:I:actualcoeff`), corrected source lines
1453–1500, in the setup 1060–1128 and 1416–1451.

The exact norm witness comes from `ActualTwist.normChoice`. The
unramified coefficient keeps its integral endpoint error, while the
ramified calculation kills that error on the whole conductor ideal.
Both formulas hold on the full half-depth ideals, using the actual
continuous characters and the trace pullbacks of their normalized
additive character.
-/

namespace LanglandsSecondMainLemma.Odd.UR

noncomputable section
open LanglandsFirstMainLemma

/-- The half-depths used in `O:I:actualcoeff`, including the extra depth
at `h = t`. All divisions here are of nonnegative conductor exponents. -/
theorem coefficients_depths {p t h : ℕ} (hp : 2 < p) (ht : 0 < t) (hh : h ≤ t) :
    (t + 1) ⌈/⌉ p ≤ (t + 1 + h) / 2 ∧
    (t + 1 + h) / 2 ≤ t ∧
    (t + 1 + h) / 2 ≤ (t + 1 + p * h) / 2 ∧
    h + (t + 1) ⌈/⌉ p ≤ (t + 1 + p * h) / 2 ∧
    (h = t → t + 1 ≤ (t + 1 + p * h) / 2) := by
  have hp3 : 3 ≤ p := hp
  have hq : (t + 1) ⌈/⌉ p ≤ (t + 1) / 2 := by
    rw [ceilDiv_le_iff_le_mul (by omega : 0 < p)]
    have hm := Nat.mul_le_mul_right ((t + 1) / 2) hp3
    omega
  have hmul : 3 * h ≤ p * h := Nat.mul_le_mul_right h hp3
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  intro he
  subst h
  omega

private theorem coefficient_phase_congruent
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (Psi : ContinuousAddChar F) {J : ℤ}
    (hPsi : AddCharTrivialOnLattice F Psi J) {a b : F}
    (hab : a - b ∈ lattice F J) : Psi a = Psi b := by
  apply div_eq_one.mp
  exact (Psi.toAddChar.map_sub_eq_div _ _).symm.trans (hPsi _ hab)

section Unramified
variable (F U : Type*) [Field F] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U]
  [PrimeCyclicExtension F U]

/-- Pull back a full logarithm chart with a possibly nonintegral coefficient.
The norm-log congruence is used at depth `T + h` before multiplication
by the coefficient in `𝔭_F^(-h)`. -/
theorem coefficients_unramified_twist
    {p T h r : ℕ} (hdegree : Module.finrank F U = p)
    (hchar : residueCharacteristic F = p) (hunr : ramificationIndex F U = 1)
    (hr : 0 < r) (hdepth : T + h ≤ p * r)
    (lambda : ContinuousQuasiChar F) (Psi : ContinuousAddChar F)
    (hPsi : AddCharTrivialOnLattice F Psi (T : ℤ))
    (a : F) (ha : a ∈ lattice F (-(h : ℤ)))
    (hchart : ∀ z : lattice F (r : ℤ),
      lambda (positiveUnitOfLattice F hr (-z)) = Psi (a * truncatedLog p (z : F)))
    (z : lattice U (r : ℤ)) :
    normQuasiChar F U lambda (positiveUnitOfLattice U hr (-z)) =
      tracePullbackAddChar F U Psi (algebraMap F U a * truncatedLog p (z : U)) := by
  have hp : 0 < p := hdegree ▸ (PrimeCyclicExtension.degree_prime F U).pos
  let uz := positiveUnitOfLattice U hr (-z)
  let nu : unitFiltration F r := ⟨normUnits F U (uz : Uˣ),
    (unramified_norm_unitFiltration F U hunr r).1 _ uz.property⟩
  have hnu : ((nu : Fˣ) : F) = norm F U (1 - (z : U)) := by
    simp only [nu, uz, coe_normUnits, coe_positiveUnitOfLattice]
    change norm F U (1 + -(z : U)) = norm F U (1 - (z : U))
    rw [sub_eq_add_neg]
  have hz : (z : U) ∈ lattice U (((T + h) ⌈/⌉ Module.finrank F U : ℕ) : ℤ) := by
    apply lattice_antitone U _ z.property
    exact_mod_cast (show (T + h) ⌈/⌉ Module.finrank F U ≤ r by
      rw [hdegree, ceilDiv_le_iff_le_mul hp]
      exact hdepth)
  have hlog := unramifiedNormLog F U (T + h) (hchar.trans hdegree.symm) hunr (z : U) hz
  rw [hdegree] at hlog
  have herr : a * (truncatedLog p (1 - ((nu : Fˣ) : F)) -
      trace F U (truncatedLog p (z : U))) ∈ lattice F (T : ℤ) := by
    have he : -(h : ℤ) + ((T + h : ℕ) : ℤ) = (T : ℤ) := by omega
    simpa only [he, hnu] using mul_mem_lattice F ha hlog
  have htr : trace F U (algebraMap F U a * truncatedLog p (z : U)) =
      a * trace F U (truncatedLog p (z : U)) := by
    simpa [Algebra.smul_def] using map_smul (trace F U) a (truncatedLog p (z : U))
  change lambda (nu : Fˣ) = _
  rw [(one_sub_chart_iff_units F p r hr lambda Psi a).1 hchart nu,
    tracePullbackAddChar_apply, htr]
  apply coefficient_phase_congruent F Psi hPsi
  rwa [← mul_sub]

end Unramified

section Ramified
variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

/-- The actual ramified base twist has coefficient `N(x) - x` on the
entire half-depth ideal. The integral error retained by `normChoice` at
`h = t` is killed using the norm containment at `t + 1`. -/
theorem coefficients_ramified_twist
    {p t h q : ℕ} (hdegree : Module.finrank F E = p)
    (hodd : 2 < p) (htpos : 0 < t) (hh : h ≤ t)
    (hchar : residueCharacteristic F = p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hres : residueDegree F E = 1)
    (hq : q = (t + 1) ⌈/⌉ p) (hqpos : 0 < q)
    (tau : NormCharacter F E) (htaune : tau ≠ 1)
    (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (htau : ∀ z : lattice F (q : ℤ),
      tau.1 (positiveUnitOfLattice F hqpos (-z)) = Psi (truncatedLog p (z : F)))
    (lambda : ContinuousQuasiChar F) (x : E) (epsilon : F)
    (hx : x ∈ lattice E (-(h : ℤ)))
    (hepsilon : epsilon ∈ lattice F 0) (hepsilon_zero : h < t → epsilon = 0)
    (hchart : ∀ z : lattice F (((t + 1 + h) / 2 : ℕ) : ℤ),
      lambda (positiveUnitOfLattice F (normChoice_depths hodd htpos).1 (-z)) =
        Psi ((norm F E x + epsilon) * truncatedLog p (z : F)))
    (z : lattice E (((t + 1 + p * h) / 2 : ℕ) : ℤ)) :
    normQuasiChar F E lambda
        (positiveUnitOfLattice E (normChoice_depths hodd htpos).1 (-z)) =
      tracePullbackAddChar F E Psi
        ((algebraMap F E (norm F E x) - x) * truncatedLog p (z : E)) := by
  let r := (t + 1 + h) / 2
  let s := (t + 1 + p * h) / 2
  have hr : 0 < r := (normChoice_depths hodd htpos).1
  have hs : 0 < s := (normChoice_depths hodd htpos).1
  obtain ⟨_, hrt, hrs, hsq, hboundary⟩ := coefficients_depths hodd htpos hh
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  let uz := positiveUnitOfLattice E hs (-z)
  let nu : unitFiltration F r := ⟨normUnits F E (uz : Eˣ),
    normMapsUnitFiltration_belowBreak F E ht hrt hres pi hpi hgen _
      (unitFiltration_antitone E hrs uz.property)⟩
  have hnu : ((nu : Fˣ) : F) = norm F E (1 - (z : E)) := by
    simp only [nu, uz, coe_normUnits, coe_positiveUnitOfLattice]
    change norm F E (1 + -(z : E)) = norm F E (1 - (z : E))
    rw [sub_eq_add_neg]
  let y := 1 - ((nu : Fˣ) : F)
  let w := truncatedLog p (z : E)
  have hcharE : residueCharacteristic E = p :=
    (residueCharacteristic_extension_eq F E).trans hchar
  have hw : w ∈ lattice E (s : ℤ) :=
    (truncatedLogOnLattice E p s hcharE hs z).property
  have hxw : x * w ∈ lattice E (q : ℤ) :=
    lattice_antitone E (by rw [hq]; omega) (mul_mem_lattice E hx hw)
  have hchar' : residueCharacteristic F = Module.finrank F E := hchar.trans hdegree.symm
  have hodd' : Module.finrank F E ≠ 2 := by omega
  have hconv := (normPhase F E ht htpos hres hchar' hodd' q
    (by rw [hdegree]; exact hq) hqpos tau htaune Psi hPsi
    (by simpa only [hdegree] using htau) (x * w) hxw).1
  have hn : norm F E (x * w) = norm F E x * norm F E w :=
    map_mul (Algebra.norm F) x w
  rw [hn] at hconv
  have hzlog : (z : E) ∈ lattice E
      ((h + (t + 1) ⌈/⌉ Module.finrank F E : ℕ) : ℤ) := by
    apply lattice_antitone E _ z.property
    rw [hdegree]
    exact_mod_cast hsq
  have hlog := normLog F E ht htpos hres hchar' hodd' h (z : E) hzlog
  have hA : norm F E x ∈ lattice F (-(h : ℤ)) := by
    simpa only [mem_lattice, ord_norm, hres, one_nsmul] using hx
  have herr : norm F E x * (truncatedLog p y - trace F E w - norm F E w) ∈
      lattice F ((t + 1 : ℕ) : ℤ) := by
    have he : -(h : ℤ) + ((t + 1 + h : ℕ) : ℤ) = ((t + 1 : ℕ) : ℤ) := by omega
    simpa only [he, hdegree, ← hnu, y, w] using mul_mem_lattice F hA hlog
  have hPsiT : AddCharTrivialOnLattice F Psi ((t + 1 : ℕ) : ℤ) := by
    simpa only [neg_neg] using hPsi.trivial
  have herror : Psi (norm F E x * truncatedLog p y) =
      Psi (norm F E x * (trace F E w + norm F E w)) := by
    apply coefficient_phase_congruent F Psi hPsiT
    convert herr using 1
    ring
  have heps : Psi (epsilon * truncatedLog p y) = 1 := by
    by_cases hlt : h < t
    · simp [hepsilon_zero hlt]
    · have heq : h = t := by omega
      have hnuT : normUnits F E (uz : Eˣ) ∈ unitFiltration F (t + 1) :=
        normMapsUnitFiltration_break_succ F E ht hres pi hpi hgen _
          (unitFiltration_antitone E (hboundary heq) uz.property)
      let nuT : unitFiltration F (t + 1) := ⟨normUnits F E (uz : Eˣ), hnuT⟩
      have hy : y ∈ lattice F ((t + 1 : ℕ) : ℤ) := by
        have hv := (truncatedLogUnitArgument F (by omega) nuT).property
        rw [coe_truncatedLogUnitArgument] at hv
        exact hv
      have hPy : truncatedLog p y ∈ lattice F ((t + 1 : ℕ) : ℤ) :=
        (truncatedLogOnLattice F p (t + 1) hchar (by omega)
          (⟨y, hy⟩ : lattice F ((t + 1 : ℕ) : ℤ))).property
      apply hPsiT
      simpa only [zero_add] using mul_mem_lattice F hepsilon hPy
  have htr : trace F E (algebraMap F E (norm F E x) * w) =
      norm F E x * trace F E w := by
    simpa [Algebra.smul_def] using map_smul (trace F E) (norm F E x) w
  change lambda (nu : Fˣ) = _
  rw [(one_sub_chart_iff_units F p r hr lambda Psi (norm F E x + epsilon)).1 hchart nu]
  change Psi ((norm F E x + epsilon) * truncatedLog p y) = _
  rw [add_mul, Psi.map_add_eq_mul, heps, mul_one, herror, tracePullbackAddChar_apply,
    sub_mul, map_sub, htr]
  apply div_eq_one.mp
  calc
    _ = Psi (norm F E x * (trace F E w + norm F E w) -
        (norm F E x * trace F E w - trace F E (x * w))) :=
      (Psi.toAddChar.map_sub_eq_div _ _).symm
    _ = Psi (trace F E (x * w) + norm F E x * norm F E w) := by
      congr 1
      ring
    _ = 1 := hconv

end Ramified

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
  [Module.Finite U K] [Module.Finite F K]
  [PrimeCyclicExtension F E] [PrimeCyclicExtension F U]

/-- Proposition 6.9 (`O:I:actualcoeff`). Starting with the actual common
twist, construct its exact norm witness and retain the full logarithm
formulas at `d_U = ⌊(t+1+h)/2⌋` and `d_E = ⌊(t+1+ph)/2⌋`.

The coefficients are `B_U = N(x) + d^p + epsilon` and
`B_E = N(x) - x + c`, with the base-field embeddings displayed explicitly.
The boundary error is integral and is set to zero only when `h < t`.
The norm witness, its orders, and the zero-class convention are constructed
by `ActualTwist.normChoice`, not supplied as additional hypotheses.

The norm character's chart and the actual twist are the proved outputs of
`twist`; `Psi` is its normalized additive character. Equal and mixed
characteristic and nonunitary quasi-characters are allowed. -/
theorem coefficients
    {p t q : ℕ} (hp : p.Prime) (hodd : 2 < p) (htpos : 0 < t)
    (hFE : Module.finrank F E = p) (hFU : Module.finrank F U = p)
    (hchar : residueCharacteristic F = p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hres : residueDegree F E = 1)
    (hunr : ramificationIndex F U = 1)
    (hq : q = (t + 1) ⌈/⌉ p) {hqpos : 0 < q}
    (tau : NormCharacter F E) (htaune : tau ≠ 1)
    (Psi : LocalAddCharData F) (hPsi : Psi.conductor = -((t + 1 : ℕ) : ℤ))
    (htau : ∀ z : lattice F (q : ℤ),
      tau.1 (positiveUnitOfLattice F hqpos (-z)) =
        Psi.character (truncatedLog p (z : F)))
    {c : F} {d : U}
    {M : CompatibleModels F E U K p (t + 1) q hqpos tau.1 Psi.character c d}
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
        x = 0 ∧ norm F E x = 0 ∧ epsilon = 0) ∧
      (∀ z : lattice U (((t + 1 + D.h) / 2 : ℕ) : ℤ),
        thetaU (positiveUnitOfLattice U (normChoice_depths hodd htpos).1 (-z)) =
          tracePullbackAddChar F U Psi.character
            ((algebraMap F U (norm F E x) + d ^ p + algebraMap F U epsilon) *
              truncatedLog p (z : U))) ∧
      (∀ z : lattice E (((t + 1 + p * D.h) / 2 : ℕ) : ℤ),
        thetaE (positiveUnitOfLattice E (normChoice_depths hodd htpos).1 (-z)) =
          tracePullbackAddChar F E Psi.character
            ((algebraMap F E (norm F E x) - x + algebraMap F E c) *
              truncatedLog p (z : E))) := by
  obtain ⟨x, epsilon, hepsilon, hepsilon_zero, hchart, horder, hintegral, hzero⟩ :=
    D.normChoice F E U K hp hodd htpos hchar ht hres Psi hPsi hh
  have hx : x ∈ lattice E (-(D.h : ℤ)) := by
    by_cases hhzero : D.h = 0
    · simpa only [hhzero, Nat.cast_zero, neg_zero] using hintegral hhzero
    · rw [mem_lattice, (horder (by omega)).1]
  have hA : norm F E x ∈ lattice F (-(D.h : ℤ)) := by
    simpa only [mem_lattice, ord_norm, hres, one_nsmul] using hx
  have ha : norm F E x + epsilon ∈ lattice F (-(D.h : ℤ)) :=
    add_mem_lattice F hA (lattice_antitone F (by omega) hepsilon)
  have hPsiT : AddCharTrivialOnLattice F Psi.character ((t + 1 : ℕ) : ℤ) := by
    simpa only [hPsi, neg_neg] using Psi.isConductor.trivial
  obtain ⟨hqr, _, hrs, _, _⟩ := coefficients_depths hodd htpos hh
  have hqs : q ≤ (t + 1 + p * D.h) / 2 := hq.le.trans (hqr.trans hrs)
  rw [← hq] at hqr
  refine ⟨x, epsilon, hepsilon, hepsilon_zero, hchart, horder, hintegral, hzero, ?_, ?_⟩
  · intro z
    let zq : lattice U (q : ℤ) := ⟨(z : U), lattice_antitone U (by exact_mod_cast hqr) z.property⟩
    have hmodel : M.chiU (positiveUnitOfLattice U (normChoice_depths hodd htpos).1 (-z)) =
        tracePullbackAddChar F U Psi.character (d ^ p * truncatedLog p (z : U)) :=
      M.logU zq
    have htwist := coefficients_unramified_twist F U hFU hchar hunr
      (normChoice_depths hodd htpos).1 (normChoice_depths hodd htpos).2.2
      D.lambda Psi.character hPsiT (norm F E x + epsilon) ha hchart z
    rw [DFunLike.congr_fun D.twistU
      (positiveUnitOfLattice U (normChoice_depths hodd htpos).1 (-z) : Uˣ)]
    change M.chiU (positiveUnitOfLattice U (normChoice_depths hodd htpos).1 (-z)) *
      normQuasiChar F U D.lambda (positiveUnitOfLattice U (normChoice_depths hodd htpos).1 (-z)) = _
    rw [hmodel, htwist, ← ContinuousAddChar.map_add_eq_mul]
    congr 1
    rw [map_add]
    ring
  · intro z
    let zq : lattice E (q : ℤ) := ⟨(z : E), lattice_antitone E (by exact_mod_cast hqs) z.property⟩
    have hmodel : (M.chiE * D.rho.1)
        (positiveUnitOfLattice E (normChoice_depths hodd htpos).1 (-z)) =
        tracePullbackAddChar F E Psi.character
          (algebraMap F E c * truncatedLog p (z : E)) := D.adjusted_log zq
    have htwist := coefficients_ramified_twist F E hFE hodd htpos hh hchar ht hres
      hq hqpos tau htaune Psi.character (hPsi ▸ Psi.isConductor) htau
      D.lambda x epsilon hx hepsilon hepsilon_zero hchart z
    rw [DFunLike.congr_fun D.twistE
      (positiveUnitOfLattice E (normChoice_depths hodd htpos).1 (-z) : Eˣ)]
    change (M.chiE * D.rho.1)
      (positiveUnitOfLattice E (normChoice_depths hodd htpos).1 (-z)) *
      normQuasiChar F E D.lambda
        (positiveUnitOfLattice E (normChoice_depths hodd htpos).1 (-z)) = _
    rw [hmodel, htwist, ← ContinuousAddChar.map_add_eq_mul]
    congr 1
    ring

end ActualPair

end
end LanglandsSecondMainLemma.Odd.UR
