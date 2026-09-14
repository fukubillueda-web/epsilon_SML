import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsSecondMainLemma.Odd.UR.ScalarPhase

/-!
# Odd / UR / Cubic Identity

Paper Lemma 6.13, the algebraic identity `O:I:Lambdaexact`, and the two
boundary corrections `O:I:cubicU` and `O:I:cubicE` (source lines 1668–1730).
The ambient setup is in lines 1060–1128 and 1408–1430.

At residual characteristic three and `h = t`, the actual norm witness
from `scalarPhase` gives the literal characteristic-polynomial expansion,
both full affine corrections, and the local-constant ratio with phase
`Psi (-Lambda)`. The norm-character evaluation of this phase is owned by
`Odd/UR/CubicPhase`, corresponding to paper lines 1731–1751.
-/

namespace LanglandsSecondMainLemma.Odd.UR

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

section Algebra
variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra F E] [Module.Finite F E] [IsGalois F E]

/-- Newton traces of degrees two through four, as used in paper lines 1716–1720. -/
theorem cubic_powerTraces (hdegree : Module.finrank F E = 3) (x : E) :
    let a := trace F E x
    let b := elementarySymmetric F E 2 x
    let A := norm F E x
    trace F E (x ^ 2) = a ^ 2 - 2 * b ∧
    trace F E (x ^ 3) = a ^ 3 - 3 * a * b + 3 * A ∧
    trace F E (x ^ 4) = a ^ 4 - 4 * a ^ 2 * b + 2 * b ^ 2 + 4 * a * A := by
  have hn2 := elementarySymmetric_newton_identity F E x 2
  have hn3 := elementarySymmetric_newton_identity F E x 3
  have hn4 := elementarySymmetric_newton_identity F E x 4
  have he3 : elementarySymmetric F E 3 x = norm F E x := by
    rw [← hdegree, elementarySymmetric_finrank]
  have he4 : elementarySymmetric F E 4 x = 0 :=
    elementarySymmetric_of_finrank_lt F E (by omega) x
  have hd2 : Finset.HasAntidiagonal.antidiagonal 2 =
      ({(0, 2), (1, 1), (2, 0)} : Finset (ℕ × ℕ)) := by decide
  have hd3 : Finset.HasAntidiagonal.antidiagonal 3 =
      ({(0, 3), (1, 2), (2, 1), (3, 0)} : Finset (ℕ × ℕ)) := by decide
  have hd4 : Finset.HasAntidiagonal.antidiagonal 4 =
      ({(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hd2] at hn2
  rw [hd3] at hn3
  rw [hd4] at hn4
  norm_num [Finset.sum_filter,
    galoisPowerSum, he3, he4] at hn2 hn3 hn4
  dsimp
  constructor
  · linear_combination hn2
  constructor
  · linear_combination (trace F E x) * hn2 - hn3
  · linear_combination (trace F E x ^ 2 - elementarySymmetric F E 2 x) * hn2 -
      trace F E x * hn3 + hn4

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The characteristic polynomial, including the multiplicities when `x` is in `F`. -/
theorem cubic_characteristic (hdegree : Module.finrank F E = 3) (x : E) :
    (Algebra.lmul F E x).charpoly =
      Polynomial.X ^ 3 - Polynomial.C (trace F E x) * Polynomial.X ^ 2 +
        Polynomial.C (elementarySymmetric F E 2 x) * Polynomial.X -
          Polynomial.C (norm F E x) := by
  let f := (Algebra.lmul F E x).charpoly
  have hf : f.natDegree = 3 := (LinearMap.charpoly_natDegree _).trans hdegree
  have hc3 : f.coeff 3 = 1 := by
    rw [← hf]
    exact (LinearMap.charpoly_monic _).coeff_natDegree
  have he3 := elementarySymmetric_finrank F E x
  have he1 := elementarySymmetric_one F E x
  have he2 : elementarySymmetric F E 2 x = f.coeff 1 := by
    norm_num [elementarySymmetric, hdegree, f]
  rw [elementarySymmetric, if_pos le_rfl, hdegree] at he3
  rw [elementarySymmetric, hdegree] at he1
  norm_num at he3 he1
  change -f.coeff 0 = norm F E x at he3
  change -f.coeff 2 = trace F E x at he1
  have hc0 : f.coeff 0 = -norm F E x := by linear_combination -he3
  have hc2 : f.coeff 2 = -trace F E x := by linear_combination -he1
  rw [show (Algebra.lmul F E x).charpoly = f from rfl,
    f.as_sum_range_C_mul_X_pow]
  rw [hf]
  norm_num [Finset.sum_range_succ, hc0, he2, hc2, hc3]
  ring

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The exact ramified displacement, with the characteristic-polynomial signs. -/
theorem cubic_displacement (hdegree : Module.finrank F E = 3) (x : E) :
    x ^ 3 - algebraMap F E (norm F E x) =
      algebraMap F E (trace F E x) * x ^ 2 -
        algebraMap F E (elementarySymmetric F E 2 x) * x := by
  have h := Algebra.aeval_self_charpoly_lmul (R := F) x
  rw [cubic_characteristic F E hdegree x] at h
  simp only [map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C] at h
  linear_combination h

/-- Square the full ramified displacement before taking its trace. -/
theorem cubic_displacement_trace (hdegree : Module.finrank F E = 3) (x : E) :
    let a := trace F E x
    let b := elementarySymmetric F E 2 x
    let A := norm F E x
    trace F E ((x ^ 3 - algebraMap F E A) ^ 2) =
      a ^ 6 - 6 * a ^ 4 * b + 9 * a ^ 2 * b ^ 2 - 2 * b ^ 3 +
        4 * a ^ 3 * A - 6 * a * b * A := by
  dsimp
  rw [cubic_displacement F E hdegree x]
  have he : (algebraMap F E (trace F E x) * x ^ 2 -
        algebraMap F E (elementarySymmetric F E 2 x) * x) ^ 2 =
      algebraMap F E (trace F E x ^ 2) * x ^ 4 -
        algebraMap F E (2 * trace F E x * elementarySymmetric F E 2 x) * x ^ 3 +
          algebraMap F E (elementarySymmetric F E 2 x ^ 2) * x ^ 2 := by
    simp only [map_pow, map_mul, map_ofNat]
    ring
  rw [he, map_add, map_sub]
  simp_rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  obtain ⟨h2, h3, h4⟩ := cubic_powerTraces F E hdegree x
  rw [h2, h3, h4]
  ring

/-- The exact rational completion; no characteristic-three division is used. -/
theorem cubic_completion (hdegree : Module.finrank F E = 3)
    (htwo : (2 : F) ≠ 0) (x : E) (hA : norm F E x ≠ 0) :
    let a := trace F E x
    let b := elementarySymmetric F E 2 x
    let A := norm F E x
    (3 * A - trace F E (x ^ 3) + 3 * a) - b ^ 2 / A +
      trace F E ((x ^ 3 - algebraMap F E A) ^ 2) / (2 * A) =
    3 * a + a ^ 3 - (b ^ 2 + b ^ 3) / A + a ^ 2 * (a ^ 2 - 3 * b) ^ 2 / (2 * A) := by
  dsimp
  rw [(cubic_powerTraces F E hdegree x).2.1,
    cubic_displacement_trace F E hdegree x]
  field_simp
  ring

end Algebra

section Precision
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

private theorem cubic_phase_eq (Psi : ContinuousAddChar L) {J : ℤ}
    (hPsi : AddCharTrivialOnLattice L Psi J) {y z : L}
    (h : y - z ∈ lattice L J) : Psi y = Psi z := by
  apply div_eq_one.mp
  exact (Psi.toAddChar.map_sub_eq_div _ _).symm.trans (hPsi _ h)

private theorem cubic_numerator_precision {eta eta0 B : L} {r s k J : ℤ}
    (htwo : ord L (2 : L) = 0) (hB : ord L B = (k : WithTop ℤ))
    (heta : eta ∈ lattice L r) (heta0 : eta0 ∈ lattice L r)
    (hdiff : eta - eta0 ∈ lattice L s) (hdepth : J ≤ s + r - k) :
    eta ^ 2 / (2 * B) - eta0 ^ 2 / (2 * B) ∈ lattice L J := by
  rw [← sub_div, show eta ^ 2 - eta0 ^ 2 = (eta - eta0) * (eta + eta0) by ring]
  have hden : ord L (2 * B) = (k : WithTop ℤ) := by
    rw [ord_mul, htwo, hB, zero_add]
  apply (div_mem_lattice_iff L _ _ k J hden).2
  exact lattice_antitone L (by omega)
    (mul_mem_lattice L hdiff (add_mem_lattice L heta heta0))

private theorem cubic_denominator_precision {eta A B : L} {r s k J : ℤ}
    (htwo : ord L (2 : L) = 0) (hA : ord L A = (k : WithTop ℤ))
    (hB : ord L B = (k : WithTop ℤ))
    (heta : eta ∈ lattice L r) (hdiff : B - A ∈ lattice L s)
    (hdepth : J ≤ r + r + s - (k + k)) :
    eta ^ 2 / (2 * B) - eta ^ 2 / (2 * A) ∈ lattice L J := by
  have hA0 := (ord_ne_top_iff L).1 (hA ▸ WithTop.coe_ne_top)
  have hB0 := (ord_ne_top_iff L).1 (hB ▸ WithTop.coe_ne_top)
  have h20 : (2 : L) ≠ 0 := (ord_ne_top_iff L).1 (htwo ▸ (by simp))
  have he : eta ^ 2 / (2 * B) - eta ^ 2 / (2 * A) =
      eta ^ 2 * (A - B) / (2 * B * A) := by
    field_simp
  rw [he]
  have hden : ord L (2 * B * A) = ((k + k : ℤ) : WithTop ℤ) := by
    rw [ord_mul, ord_mul, htwo, hB, hA, zero_add, WithTop.coe_add]
  apply (div_mem_lattice_iff L _ _ (k + k) J hden).2
  have hnum : eta ^ 2 * (A - B) ∈ lattice L (r + r + s) :=
    mul_mem_lattice L (by simpa only [pow_two] using mul_mem_lattice L heta heta)
      (by simpa only [neg_sub] using neg_mem_lattice L hdiff)
  exact lattice_antitone L (by omega) hnum

end Precision

section UnramifiedCorrection
variable (F U : Type*) [Field F] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U] [IsGalois F U]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeExtension F U] [Module.Finite F U] [IsGalois F U] in
private theorem cubic_trace_div (z : U) (A : F) :
    trace F U (z / algebraMap F U A) = trace F U z / A := by
  rw [div_eq_mul_inv, ← map_inv₀, mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
  ring

/-- The unramified affine term retains the integral error in the norm choice
until its trace is proved to lie in the character kernel. -/
private theorem cubic_unramified_correction {t : ℕ} (htpos : 0 < t)
    (hdegree : Module.finrank F U = 3) (hunr : ramificationIndex F U = 1)
    (hchar : residueCharacteristic F = 3)
    (Psi : ContinuousAddChar F) (hPsi : IsAdditiveConductor F Psi (-((t : ℤ) + 1)))
    (c : F) (d : ringOfIntegers U)
    (hd : (d : U) ^ 3 - (d : U) = algebraMap F U c)
    (hgen : IntermediateField.adjoin F {(d : U)} = ⊤)
    (A b epsilon : F) (eta : U)
    (hA : ord F A = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hb : b ∈ lattice F 0) (hepsilon : epsilon ∈ lattice F 0)
    (hB : ord U (algebraMap F U A + (d : U) ^ 3 + algebraMap F U epsilon) =
      ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (heta : eta ∈ lattice U 0)
    (hdiff : eta - (algebraMap F U b * (d : U) - algebraMap F U epsilon) ∈ lattice U 1) :
    tracePullbackAddChar F U Psi
      (eta ^ 2 / (2 * (algebraMap F U A + (d : U) ^ 3 + algebraMap F U epsilon))) =
      Psi (b ^ 2 / A) := by
  let eta0 := algebraMap F U b * (d : U) - algebraMap F U epsilon
  let B := algebraMap F U A + (d : U) ^ 3 + algebraMap F U epsilon
  have hmap {z : F} (hz : z ∈ lattice F 0) : algebraMap F U z ∈ lattice U 0 := by
    simpa only [mem_lattice, ord_algebraMap, hunr, one_nsmul] using hz
  have hd0 : (d : U) ∈ lattice U 0 := (mem_lattice_zero_iff U).mpr d.property
  have hd3 : (d : U) ^ 3 ∈ lattice U 0 := (mem_lattice_zero_iff U).mpr (pow_mem d.property 3)
  have heta0 : eta0 ∈ lattice U 0 :=
    sub_mem_lattice U (by simpa using mul_mem_lattice U (hmap hb) hd0) (hmap hepsilon)
  have hBA : B - algebraMap F U A ∈ lattice U 0 := by
    have he : B - algebraMap F U A = (d : U) ^ 3 + algebraMap F U epsilon := by
      dsimp [B]
      ring
    rw [he]
    exact add_mem_lattice U hd3 (hmap hepsilon)
  have hAU : ord U (algebraMap F U A) = ((-(t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hunr, one_nsmul, hA]
  have htwoF : ord F (2 : F) = 0 :=
    ord_natCast_eq_zero_of_lt_residueCharacteristic F (j := 2) (by decide) (by omega)
  have htwoU : ord U (2 : U) = 0 := by
    rw [← map_ofNat (algebraMap F U) 2, ord_algebraMap, hunr, one_nsmul, htwoF]
  have hkernel : AddCharTrivialOnLattice U (tracePullbackAddChar F U Psi) ((t : ℤ) + 1) := by
    have hc := (unramified_additiveConductor_compTrace F U hunr Psi _).2 hPsi
    simpa only [neg_neg] using (show AddCharTrivialOnLattice U
      (tracePullbackAddChar F U Psi) (-(-((t : ℤ) + 1))) from hc.trivial)
  have hc1 := cubic_phase_eq U _ hkernel
    (cubic_numerator_precision U htwoU hB heta heta0 hdiff (by omega))
  have hc2 := cubic_phase_eq U _ hkernel
    (cubic_denominator_precision U htwoU hAU hB heta0 hBA (by omega))
  change tracePullbackAddChar F U Psi (eta ^ 2 / (2 * B)) = _
  rw [hc1, hc2, tracePullbackAddChar_apply]
  rw [show (2 : U) * algebraMap F U A = algebraMap F U (2 * A) by simp only [map_mul, map_ofNat]]
  rw [cubic_trace_div]
  obtain ⟨htr, _⟩ := scalarPhase_powerTraces F U (by decide : Odd 3) (by decide)
    hdegree c (d : U) hd hgen
  have ht1 : trace F U (d : U) = 0 := by simpa using htr 1 (by decide) (by decide)
  have ht2 : trace F U ((d : U) ^ 2) = 2 := by simpa using htr 2 (by decide) (by decide)
  have hexp : eta0 ^ 2 = algebraMap F U (b ^ 2) * (d : U) ^ 2 -
      algebraMap F U (2 * b * epsilon) * (d : U) + algebraMap F U (epsilon ^ 2) := by
    dsimp [eta0]
    simp only [map_pow, map_mul, map_ofNat]
    ring
  have heval : trace F U (eta0 ^ 2) = 2 * b ^ 2 + 3 * epsilon ^ 2 := by
    rw [hexp, map_add, map_sub, Algebra.trace_algebraMap, hdegree]
    simp_rw [← Algebra.smul_def, map_smul, smul_eq_mul]
    rw [ht1, ht2]
    simp only [nsmul_eq_mul]
    ring
  rw [heval]
  apply cubic_phase_eq F Psi (by simpa only [neg_neg] using hPsi.trivial)
  have h30 : (3 : F) ∈ lattice F 1 := by
    apply (residueMap_eq_zero_iff F (3 : ringOfIntegers F)).1
    change (3 : ResidueField F) = 0
    simpa only [hchar, Nat.cast_ofNat] using CharP.cast_eq_zero (ResidueField F) (residueCharacteristic F)
  have hnum : 3 * epsilon ^ 2 ∈ lattice F 1 := by
    simpa only [pow_two, add_zero] using
      mul_mem_lattice F h30 (mul_mem_lattice F hepsilon hepsilon)
  have h20 : (2 : F) ≠ 0 := (ord_ne_top_iff F).1 (htwoF ▸ (by simp))
  have hA0 : A ≠ 0 := (ord_ne_top_iff F).1 (hA ▸ WithTop.coe_ne_top)
  have he : (2 * b ^ 2 + 3 * epsilon ^ 2) / (2 * A) - b ^ 2 / A =
      3 * epsilon ^ 2 / (2 * A) := by field_simp; ring
  rw [he]
  apply (div_mem_lattice_iff F _ _ (-(t : ℤ)) ((t : ℤ) + 1)
    (by rw [ord_mul, htwoF, hA, zero_add])).2
  simpa only [neg_add_cancel_left] using hnum

end UnramifiedCorrection

section RamifiedCorrection
variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]
local instance : IsGalois F E := PrimeCyclicExtension.instIsGalois F E

/-- At the cubic boundary the discarded ramified argument has depth `3t`,
which lies in the actual trace character's kernel. -/
private theorem cubic_ramified_correction {t : ℕ} (htpos : 0 < t)
    (hdegree : Module.finrank F E = 3)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hres : residueDegree F E = 1)
    (hchar : residueCharacteristic F = 3)
    (Psi : ContinuousAddChar F) (hPsi : IsAdditiveConductor F Psi (-((t : ℤ) + 1)))
    (c : ringOfIntegers F) (A : F) (x eta : E)
    (hx : ord E x = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hA : ord F A = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hB : ord E (algebraMap F E A - x + algebraMap F E (c : F)) =
      ((-3 * (t : ℤ) : ℤ) : WithTop ℤ))
    (heta : eta ∈ lattice E (-(t : ℤ))) :
    tracePullbackAddChar F E Psi
      (eta ^ 2 / (2 * (algebraMap F E A - x + algebraMap F E (c : F)))) =
      Psi (trace F E (eta ^ 2) / (2 * A)) := by
  have hram : ramificationIndex F E = 3 := by
    have he := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa only [hdegree, hres, mul_one] using he.symm
  have hAE : ord E (algebraMap F E A) = ((-3 * (t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hram, hA, ← WithTop.coe_nsmul]
    congr 1
    simp
  have hc0 : algebraMap F E (c : F) ∈ lattice E 0 := by
    rw [mem_lattice, ord_algebraMap]
    simpa using nsmul_le_nsmul_right
      (show (0 : WithTop ℤ) ≤ ord F (c : F) from
        (mem_lattice (F := F)).1 ((mem_lattice_zero_iff F).mpr c.property))
      (ramificationIndex F E)
  have hdiff : (algebraMap F E A - x + algebraMap F E (c : F)) - algebraMap F E A ∈
      lattice E (-(t : ℤ)) := by
    have hz : -x + algebraMap F E (c : F) ∈ lattice E (-(t : ℤ)) :=
      add_mem_lattice E (neg_mem_lattice E (by rw [mem_lattice, hx]))
        (lattice_antitone E (by omega) hc0)
    convert hz using 1
    ring
  have htwo : ord E (2 : E) = 0 :=
    ord_natCast_eq_zero_of_lt_residueCharacteristic E (j := 2) (by decide)
      (by rw [residueCharacteristic_extension_eq F E, hchar]; decide)
  obtain ⟨pi, hpi, hg⟩ := monogenicUniformizer F E hres
  have hc := additiveConductor_compTrace_cyclicPrime F E ht hres pi hpi hg hPsi
  have hkernel : AddCharTrivialOnLattice E (tracePullbackAddChar F E Psi) ((t : ℤ) + 1) := by
    have heq : -((Module.finrank F E : ℤ) * -((t : ℤ) + 1) +
        (((Module.finrank F E - 1) * (t + 1) : ℕ) : ℤ)) = (t : ℤ) + 1 := by
      rw [hdegree]
      push_cast
      ring
    exact heq ▸ hc.trivial
  rw [cubic_phase_eq E _ hkernel
    (cubic_denominator_precision E htwo hAE hB heta hdiff (by omega))]
  rw [tracePullbackAddChar_apply,
    show (2 : E) * algebraMap F E A = algebraMap F E (2 * A) by simp only [map_mul, map_ofNat],
    cubic_trace_div]

end RamifiedCorrection

/-- The cubic boundary formulas for the literal common norms, with the two
original affine denominators retained on the left. The final assertion is
a reduction to `Psi (-Lambda)`, prior to norm-character cancellation. -/
def CubicIdentityAt
    (F E U K : Type*) [Field F] [Field E] [Field U] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
    [Algebra F E] [Algebra F U] [Algebra E K] [Algebra U K]
    [ValuativeExtension F E] [ValuativeExtension F U]
    [Module.Finite F E] [Module.Finite F U]
    (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
    (psiF Psi : ContinuousAddChar F) (t : ℕ) (c : F) (d : U) (x : E) (epsilon : F) : Prop :=
  let a := trace F E x
  let b := elementarySymmetric F E 2 x
  let A := norm F E x
  let C := algebraMap E K x + algebraMap U K d
  let BU := algebraMap F U A + d ^ 3 + algebraMap F U epsilon
  let BE := algebraMap F E A - x + algebraMap F E c
  let ZU := norm U K C
  let ZE := norm E K C
  let etaU := ZU - BU
  let etaE := ZE - BE
  let S := trace F U ZU - trace F E ZE
  let Lambda := S - b ^ 2 / A + trace F E (etaE ^ 2) / (2 * A)
  a ∈ lattice F (((t : ℤ) + 2) / 3) ∧
  b ∈ lattice F 0 ∧
  etaE = algebraMap F E a * x ^ 2 - algebraMap F E b * x ∧
  tracePullbackAddChar F U Psi (etaU ^ 2 / (2 * BU)) = Psi (b ^ 2 / A) ∧
  tracePullbackAddChar F E Psi (etaE ^ 2 / (2 * BE)) =
    Psi (trace F E (etaE ^ 2) / (2 * A)) ∧
  Lambda = 3 * a + a ^ 3 - (b ^ 2 + b ^ 3) / A +
    a ^ 2 * (a ^ 2 - 3 * b) ^ 2 / (2 * A) ∧
  ∃ g : ℂ, g ^ 4 = 1 ∧
    LanglandsFirstMainLemma.localConstant U thetaU (tracePullbackAddChar F U psiF) /
      LanglandsFirstMainLemma.localConstant E thetaE (tracePullbackAddChar F E psiF) =
        g * (Psi (-Lambda) : ℂ)

section AtScalarPhase
variable (F E U K : Type*) [Field F] [Field E] [Field U] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F E] [Algebra F U] [Algebra E K] [Algebra U K]
  [ValuativeExtension F E] [ValuativeExtension F U]
  [Module.Finite F E] [Module.Finite F U]
  [PrimeCyclicExtension F E] [IsGalois F U]
local instance : IsGalois F E := PrimeCyclicExtension.instIsGalois F E

private theorem cubicIdentity_at {t : ℕ} (htpos : 0 < t)
    (hFE : Module.finrank F E = 3) (hFU : Module.finrank F U = 3)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hres : residueDegree F E = 1)
    (hunr : ramificationIndex F U = 1) (hchar : residueCharacteristic F = 3)
    (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
    (psiF Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t : ℤ) + 1)))
    (c : ringOfIntegers F) (d : ringOfIntegers U) (x : E) (epsilon : F)
    (hd : (d : U) ^ 3 - (d : U) = algebraMap F U (c : F))
    (hgen : IntermediateField.adjoin F {(d : U)} = ⊤)
    (hepsilon : epsilon ∈ lattice F 0)
    (hx : ord E x = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hA : ord F (norm F E x) = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (R : NormDepthsAt F E U K thetaU thetaE Psi 3 t t (c : F) (d : U) x epsilon)
    (P : ScalarPhaseAt F E U K thetaU thetaE psiF Psi 3 (c : F) (d : U) x epsilon) :
    CubicIdentityAt F E U K thetaU thetaE psiF Psi t (c : F) (d : U) x epsilon := by
  let a := trace F E x
  let b := elementarySymmetric F E 2 x
  let A := norm F E x
  let C := algebraMap E K x + algebraMap U K (d : U)
  let BU := algebraMap F U A + (d : U) ^ 3 + algebraMap F U epsilon
  let BE := algebraMap F E A - x + algebraMap F E (c : F)
  let ZU := norm U K C
  let ZE := norm E K C
  let etaU := ZU - BU
  let etaE := ZE - BE
  let S := trace F U ZU - trace F E ZE
  rcases R with ⟨hC, hZU, hZE, hEtaU, hEtaE, RU, RE, _, _, hboundary⟩
  obtain ⟨hb, hresidue⟩ := hboundary rfl
  have hBU : ord U BU = ((-(t : ℤ) : ℤ) : WithTop ℤ) := by
    have he : (t : ℤ) + 1 - ((t + 1 + t : ℕ) : ℤ) = -(t : ℤ) := by
      push_cast
      ring
    simpa only [he] using RU.coefficient_order
  have hBE : ord E BE = ((-3 * (t : ℤ) : ℤ) : WithTop ℤ) := by
    have he : (t : ℤ) + 1 - ((t + 1 + 3 * t : ℕ) : ℤ) = -3 * (t : ℤ) := by
      push_cast
      ring
    simpa only [he] using RE.coefficient_order
  have hetaU : etaU ∈ lattice U 0 := by
    convert hEtaU using 1
    congr 1
    omega
  have hetaE : etaE ∈ lattice E (-(t : ℤ)) := by
    convert hEtaE using 1
    congr 1
    omega
  have hetaEeq : etaE = x ^ 3 - algebraMap F E A := by
    change ZE - BE = _
    change ZE = x ^ 3 - x + algebraMap F E (c : F) at hZE
    rw [hZE]
    dsimp [BE]
    ring
  have hcU := cubic_unramified_correction F U htpos hFU hunr hchar Psi hPsi
    (c : F) d hd hgen A b epsilon etaU hA hb hepsilon hBU hetaU hresidue
  have hcE := cubic_ramified_correction F E htpos hFE ht hres hchar Psi hPsi
    c A x etaE hx hA hBE hetaE
  obtain ⟨pi, hpi, hg⟩ := monogenicUniformizer F E hres
  have htrace := traceIdealLowerBound_of_integralGenerator F E ht hres pi hpi hg
  have ha : a ∈ lattice F (((t : ℤ) + 2) / 3) := by
    rw [mem_lattice]
    dsimp [a]
    have hv := htrace (-(t : ℤ)) x (by rw [hx])
    rw [hFE] at hv
    norm_num only [Nat.reduceSub, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_one] at hv
    convert hv using 1
    congr 2
    ring
  have htwoord : ord F (2 : F) = 0 :=
    ord_natCast_eq_zero_of_lt_residueCharacteristic F (j := 2) (by decide) (by omega)
  have htwo : (2 : F) ≠ 0 := (ord_ne_top_iff F).1 (htwoord ▸ (by simp))
  have hA0 : A ≠ 0 := (ord_ne_top_iff F).1 (hA ▸ WithTop.coe_ne_top)
  rcases P with ⟨⟨g, hg, hratio⟩, hS⟩
  change S = 3 * A - trace F E (x ^ 3) + 3 * a at hS
  change CubicIdentityAt F E U K thetaU thetaE psiF Psi t (c : F) (d : U) x epsilon
  refine ⟨ha, hb, hetaEeq.trans (cubic_displacement F E hFE x), hcU, hcE, ?_, g, hg, ?_⟩
  · change S - b ^ 2 / A + trace F E (etaE ^ 2) / (2 * A) = _
    rw [hetaEeq, hS]
    exact cubic_completion F E hFE htwo x hA0
  · change _ = g * (Psi (-(S - b ^ 2 / A + trace F E (etaE ^ 2) / (2 * A))) : ℂ)
    change _ = g * (Psi (-S) : ℂ) *
      (tracePullbackAddChar F U Psi (etaU ^ 2 / (2 * BU)) : ℂ) /
        (tracePullbackAddChar F E Psi (etaE ^ 2 / (2 * BE)) : ℂ) at hratio
    rw [hratio, hcU, hcE]
    have hp : Psi (-S) * Psi (b ^ 2 / A) / Psi (trace F E (etaE ^ 2) / (2 * A)) =
        Psi (-(S - b ^ 2 / A + trace F E (etaE ^ 2) / (2 * A))) := by
      rw [← Psi.map_add_eq_mul]
      exact (Psi.toAddChar.map_sub_eq_div _ _).symm.trans (congrArg Psi (by ring))
    have hpc := congrArg Units.val hp
    simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val] at hpc ⊢
    rw [← hpc]
    ring

end AtScalarPhase

section Assembly
variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  (E U : IntermediateField F K)

local instance : ValuativeRel E := Basic.intermediateFieldValuativeRel E
local instance : TopologicalSpace E := Basic.intermediateFieldTopology E
local instance : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E
local instance : ValuativeExtension F E := Basic.intermediateField_lowerValuativeExtension E
local instance : ValuativeExtension E K := Basic.intermediateField_upperValuativeExtension E
local instance : ValuativeRel U := Basic.intermediateFieldValuativeRel U
local instance : TopologicalSpace U := Basic.intermediateFieldTopology U
local instance : IsNonarchimedeanLocalField U := Basic.intermediateField_localField U
local instance : ValuativeExtension F U := Basic.intermediateField_lowerValuativeExtension U
local instance : ValuativeExtension U K := Basic.intermediateField_upperValuativeExtension U

variable (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))))
  (hFE : Module.finrank F E = 3) (hFU : Module.finrank F U = 3)

include hG hFE hFU

set_option maxHeartbeats 800000 in
/-- **Paper Lemma 6.13, algebraic part (`O:I:Lambdaexact`).**

At `p = 3` and `h = t`, extend the genuine norm witness constructed by
`scalarPhase` with the cubic characteristic-polynomial identity and both
affine corrections (`O:I:cubicU`, `O:I:cubicE`). `CubicIdentityAt` records
these equalities and the reduction of the canonical local-constant ratio
to `g * Psi (-Lambda)`, where `g ^ 4 = 1`.

The integral critical error `epsilon` is preserved through its proved
trace-kernel estimate. The final norm-character evaluation of `Lambda`
is the separate `Odd/UR/CubicPhase` task. There is no restriction on the
field characteristic or on divisibility of the positive break by three. -/
theorem cubicIdentity
    {t q : ℕ} (htpos : 0 < t)
    (hchar : residueCharacteristic F = 3) :
  letI : IsGalois F E :=
    (Basic.intermediateField_tower_compatible (by decide : Nat.Prime 3) hG E hFE).2.2.2.2.2.2.2.2.2.2.2.1.1
  letI : IsGalois F U :=
    (Basic.intermediateField_tower_compatible (by decide : Nat.Prime 3) hG U hFU).2.2.2.2.2.2.2.2.2.2.2.1.1
  ∀ (_ht : PrimeCyclicExtension.IsLowerBreak F E t) (_hres : residueDegree F E = 1)
    (_hunr : ramificationIndex F U = 1) (_hsup : E ⊔ U = ⊤)
    (_hne : Ramification.intermediateNormRange U ≠ Ramification.intermediateNormRange E)
    (_hq : q = (t + 1) ⌈/⌉ 3) {hqpos : 0 < q}
    (tau : NormCharacter F E) (_htaune : tau ≠ 1)
    (psiF : LocalAddCharData F) (alpha : Fˣ)
    (_hPsi : (scaleAddCharData F psiF alpha).conductor = -((t + 1 : ℕ) : ℤ))
    (_htau : ∀ z : lattice F (q : ℤ),
      tau.1 (positiveUnitOfLattice F hqpos (-z)) =
        (scaleAddCharData F psiF alpha).character (truncatedLog 3 (z : F)))
    (c : ringOfIntegers F) (d : ringOfIntegers U)
    (_hd : (d : U) ^ 3 - (d : U) = algebraMap F U (c : F))
    (_hgen : IntermediateField.adjoin F {(d : U)} = ⊤)
    {M : CompatibleModels F E U K 3 (t + 1) q hqpos tau.1
      (scaleAddCharData F psiF alpha).character (c : F) (d : U)}
    {thetaU : ContinuousQuasiChar U} {thetaE : ContinuousQuasiChar E}
    (_hcomp : normQuasiChar U K thetaU = normQuasiChar E K thetaE)
    (_hprimitive : ¬ ∃ chi : ContinuousQuasiChar F, normQuasiChar F K chi = normQuasiChar U K thetaU)
    (D : ActualTwist F E U K M thetaU thetaE) (_hboundary : D.h = t),
    ∃ (x : E) (epsilon : F),
      epsilon ∈ lattice F 0 ∧
      (D.h < t → epsilon = 0) ∧
      (∀ z : lattice F (((t + 1 + D.h) / 2 : ℕ) : ℤ),
        D.lambda (positiveUnitOfLattice F (normChoice_depths (by decide : 2 < 3) htpos).1 (-z)) =
          (scaleAddCharData F psiF alpha).character
            ((norm F E x + epsilon) * truncatedLog 3 (z : F))) ∧
      (0 < D.h → ord E x = ((-(D.h : ℤ) : ℤ) : WithTop ℤ) ∧
        ord F (norm F E x) = ((-(D.h : ℤ) : ℤ) : WithTop ℤ)) ∧
      (D.h = 0 → x ∈ lattice E 0) ∧
      (QuasiCharTrivialOnUnitFiltration F D.lambda ((t + 1 + D.h) / 2) →
        x = 0 ∧ norm F E x = 0 ∧ epsilon = 0) ∧
      NormDepthsAt F E U K thetaU thetaE (scaleAddCharData F psiF alpha).character
        3 t D.h (c : F) (d : U) x epsilon ∧
      ScalarPhaseAt F E U K thetaU thetaE psiF.character (scaleAddCharData F psiF alpha).character
        3 (c : F) (d : U) x epsilon ∧
      CubicIdentityAt F E U K thetaU thetaE psiF.character (scaleAddCharData F psiF alpha).character
        t (c : F) (d : U) x epsilon := by
  letI : PrimeCyclicExtension F E :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F E
      (Basic.intermediateField_tower_compatible (by decide : Nat.Prime 3) hG E hFE).2.2.2.2.2.2.2.2.2.2.2.1
  letI : PrimeCyclicExtension F U :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F U
      (Basic.intermediateField_tower_compatible (by decide : Nat.Prime 3) hG U hFU).2.2.2.2.2.2.2.2.2.2.2.1
  letI : PrimeCyclicExtension E K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension E K
      (Basic.intermediateField_tower_compatible (by decide : Nat.Prime 3) hG E hFE).2.2.2.2.2.2.2.2.2.2.2.2
  letI : PrimeCyclicExtension U K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension U K
      (Basic.intermediateField_tower_compatible (by decide : Nat.Prime 3) hG U hFU).2.2.2.2.2.2.2.2.2.2.2.2
  letI : IsGalois F E := PrimeCyclicExtension.instIsGalois F E
  letI : IsGalois F U := PrimeCyclicExtension.instIsGalois F U
  intro ht hres hunr hsup hne hq hqpos tau htaune psiF alpha hPsi htau c d hd hgen
    M thetaU thetaE hcomp hprimitive D hboundary
  obtain ⟨x, epsilon, hepsilon, hepsilon_zero, hchart, horder, hintegral, hzero, R, P⟩ :=
    scalarPhase F K E U (by decide : Nat.Prime 3) hG hFE hFU (by decide : 2 < 3)
      htpos hchar ht hres hunr hsup hne hq tau htaune psiF alpha hPsi htau c d hd hgen
      hcomp hprimitive D (by omega)
  refine ⟨x, epsilon, hepsilon, hepsilon_zero, hchart, horder, hintegral, hzero, R, P, ?_⟩
  obtain ⟨hx, hA⟩ := horder (by omega)
  rw [hboundary] at hx hA R
  have hc : IsAdditiveConductor F (scaleAddCharData F psiF alpha).character
      (-((t : ℤ) + 1)) := by
    simpa only [hPsi, Nat.cast_add, Nat.cast_one] using
      (scaleAddCharData F psiF alpha).isConductor
  exact cubicIdentity_at F E U K htpos hFE hFU ht hres hunr hchar thetaU thetaE
    psiF.character (scaleAddCharData F psiF alpha).character hc c d x epsilon hd hgen
    hepsilon hx hA R P

end Assembly

end

end LanglandsSecondMainLemma.Odd.UR
