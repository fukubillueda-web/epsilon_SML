import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Odd.TruncatedLog
import LanglandsSecondMainLemma.Stationary.NormalizedFactor

/-!
# Odd / Enhanced Stationary

Blueprint: blueprint/tasks/Odd/EnhancedStationary.md
Paper: O:I:enhanced

Complete the quadratic critical sum for a displaced coefficient, including the eta^2/(2B) correction and every domain bound. Work with arbitrary additive trivial-ideal exponent J. This is shared by UR and total ramification.

Normal planning range: 350–1100 lines; review splitting at 1200.
Never replace this task by a theorem of True, an axiom, or a statement
assuming the mathematical conclusion. Successful compilation of this
import-only scaffold does not complete the task.
-/

namespace LanglandsSecondMainLemma.Odd

noncomputable section

open LanglandsFirstMainLemma
open LanglandsSecondMainLemma.Stationary
open scoped BigOperators

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-! ## The enhanced coefficient class -/

/-- The restriction of `theta` to `U^d`, descended through its exact
conductor layer.  Unlike FML's ordinary stationary character, this character
is used one step below the ordinary stationary depth when the conductor is
odd. -/
private noncomputable def enhancedQuasiCharOnUnitQuotient
    (theta : LocalQuasiCharData E) (d : ℕ) (hdm : d ≤ theta.conductor) :
    UnitFiltrationQuotient E d theta.conductor hdm →* ℂˣ :=
  QuotientGroup.lift (unitFiltrationInside E hdm)
    (theta.character.toMonoidHom.comp (unitFiltration E d).subtype)
    (by
      intro u hu
      rw [MonoidHom.mem_ker]
      exact theta.isConductor.trivial _
        ((mem_unitFiltrationInside E hdm u).1 hu))

@[simp] private theorem enhancedQuasiCharOnUnitQuotient_mk
    (theta : LocalQuasiCharData E) (d : ℕ) (hdm : d ≤ theta.conductor)
    (u : unitFiltration E d) :
    enhancedQuasiCharOnUnitQuotient E theta d hdm
        (unitFiltrationQuotientMk E hdm u) = theta.character (u : Eˣ) :=
  rfl

/-- The additive character of `𝑙^d/𝑙^m` obtained by transporting
`theta|U^d` through the genuine truncated-logarithm chart. -/
private noncomputable def enhancedLinearizationCharacter
    (theta : LocalQuasiCharData E) (p d : ℕ)
    (hchar : ringChar (ResidueField E) = p) (hp : p.Prime)
    (hd : 1 ≤ d) (hdm : d ≤ theta.conductor)
    (hlog : theta.conductor ≤ p * d) :
    AddChar
      (LamprechtVariableQuotient E (theta.conductor : ℤ) (d : ℤ)
        (by exact_mod_cast hdm))
      ℂ :=
  (Units.coeHom ℂ).compAddChar
    (AddChar.toMonoidHomEquiv.symm
      ((enhancedQuasiCharOnUnitQuotient E theta d hdm).comp
        (truncatedLogQuotientMulEquiv E p d theta.conductor hchar hp hd hdm
          hlog).symm.toMonoidHom))

@[simp] private theorem enhancedLinearizationCharacter_mk
    (theta : LocalQuasiCharData E) (p d : ℕ)
    (hchar : ringChar (ResidueField E) = p) (hp : p.Prime)
    (hd : 1 ≤ d) (hdm : d ≤ theta.conductor)
    (hlog : theta.conductor ≤ p * d)
    (z : lattice E (d : ℤ)) :
    enhancedLinearizationCharacter E theta p d hchar hp hd hdm hlog
        (latticeQuotientMk E (by exact_mod_cast hdm)
          (truncatedLogOnLattice E p d hchar hd z)) =
      (theta.character (positiveUnitOfLattice E (by omega) (-z)) : ℂ) := by
  let e := truncatedLogQuotientMulEquiv E p d theta.conductor hchar hp hd hdm hlog
  have he := truncatedLogQuotientMulEquiv_one_sub E p d theta.conductor
    hchar hp hd hdm hlog z
  have he' :
      e.symm
          (Multiplicative.ofAdd
            (latticeQuotientMk E (by exact_mod_cast hdm)
              (truncatedLogOnLattice E p d hchar hd z))) =
        unitFiltrationQuotientMk E hdm
          (positiveUnitOfLattice E (by omega) (-z)) := by
    apply e.injective
    simpa [e] using he.symm
  change
    (((enhancedQuasiCharOnUnitQuotient E theta d hdm)
      (e.symm
        (Multiplicative.ofAdd
          (latticeQuotientMk E (by exact_mod_cast hdm)
            (truncatedLogOnLattice E p d hchar hd z))))) : ℂ) = _
  rw [he', enhancedQuasiCharOnUnitQuotient_mk]

/-- The enhanced coefficient quotient.  Its ambient quotient is literally
`𝑙^(J-m) / 𝑙^(J-d)`, so equality of these classes is exactly the
ambiguity asserted in `O:I:enhanced`. -/
private noncomputable def enhancedCoefficientClass
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (p d : ℕ) (J : ℤ)
    (hchar : ringChar (ResidueField E) = p) (hp : p.Prime)
    (hd : 1 ≤ d) (hdm : d ≤ theta.conductor)
    (hlog : theta.conductor ≤ p * d)
    (hJ : J = -Psi.conductor) :
    LamprechtCoefficientQuotient E J (theta.conductor : ℤ) (d : ℤ)
      (by exact_mod_cast hdm) :=
  (lamprechtPairingLeftEquiv E Psi (by exact_mod_cast hdm) 1 (by
      simp [hJ])).symm
    (enhancedLinearizationCharacter E theta p d hchar hp hd hdm hlog)

/-- A field unit is an enhanced coefficient when it has the exact order
`J-m` and realizes the full truncated-logarithm formula on `𝑙^d`.
The sign is the manuscript's `theta (1-z)` convention. -/
def IsEnhancedStationaryCoefficient
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (p d : ℕ) (hd : 0 < d) (J : ℤ) (B : Eˣ) : Prop :=
  ord E (B : E) =
      ((J - (theta.conductor : ℤ) : ℤ) : WithTop ℤ) ∧
    ∀ z : lattice E (d : ℤ),
      theta.character (positiveUnitOfLattice E hd (-z)) =
        Psi.character ((B : E) * truncatedLog p (z : E))

private theorem enhancedCoefficientClass_spec
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (p d : ℕ) (J : ℤ)
    (hchar : ringChar (ResidueField E) = p) (hp : p.Prime)
    (hd : 1 ≤ d) (hdm : d ≤ theta.conductor)
    (hlog : theta.conductor ≤ p * d)
    (hJ : J = -Psi.conductor)
    (B : lattice E (J - (theta.conductor : ℤ)))
    (hB : latticeQuotientMk E
        (sub_le_sub_left (by exact_mod_cast hdm) J) B =
      enhancedCoefficientClass E theta Psi p d J hchar hp hd hdm hlog hJ)
    (z : lattice E (d : ℤ)) :
    theta.character (positiveUnitOfLattice E (by omega) (-z)) =
      Psi.character ((B : E) * truncatedLog p (z : E)) := by
  apply Units.ext
  have hpair := congrArg
    (fun xi : AddChar
        (LamprechtVariableQuotient E (theta.conductor : ℤ) (d : ℤ)
          (by exact_mod_cast hdm)) ℂ =>
      xi (latticeQuotientMk E (by exact_mod_cast hdm)
        (truncatedLogOnLattice E p d hchar hd z)))
    (show lamprechtPairingLeft E Psi (by exact_mod_cast hdm) 1 (by
        simp [hJ])
        (enhancedCoefficientClass E theta Psi p d J hchar hp hd hdm hlog hJ) =
      enhancedLinearizationCharacter E theta p d hchar hp hd hdm hlog by
        exact (lamprechtPairingLeftEquiv E Psi (by exact_mod_cast hdm) 1 (by
          simp [hJ])).apply_symm_apply _)
  rw [← hB, lamprechtPairingLeft_apply, lamprechtPairing_mk_mk,
    enhancedLinearizationCharacter_mk] at hpair
  simpa [truncatedLogOnLattice] using hpair.symm

private theorem latticeQuotientMk_eq_enhancedCoefficientClass_iff
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (p d : ℕ) (J : ℤ)
    (hchar : ringChar (ResidueField E) = p) (hp : p.Prime)
    (hd : 1 ≤ d) (hdm : d ≤ theta.conductor)
    (hlog : theta.conductor ≤ p * d)
    (hJ : J = -Psi.conductor)
    (B : lattice E (J - (theta.conductor : ℤ))) :
    latticeQuotientMk E (sub_le_sub_left (by exact_mod_cast hdm) J) B =
        enhancedCoefficientClass E theta Psi p d J hchar hp hd hdm hlog hJ ↔
      ∀ z : lattice E (d : ℤ),
        theta.character (positiveUnitOfLattice E (by omega) (-z)) =
          Psi.character ((B : E) * truncatedLog p (z : E)) := by
  constructor
  · intro hB z
    exact enhancedCoefficientClass_spec E theta Psi p d J hchar hp hd hdm
      hlog hJ B hB z
  · intro hformula
    apply lamprechtPairingLeft_injective E Psi (by exact_mod_cast hdm) 1 (by
      simp [hJ])
    have hclasspair :
        lamprechtPairingLeft E Psi (by exact_mod_cast hdm) 1 (by simp [hJ])
            (enhancedCoefficientClass E theta Psi p d J hchar hp hd hdm hlog hJ) =
          enhancedLinearizationCharacter E theta p d hchar hp hd hdm hlog := by
      exact (lamprechtPairingLeftEquiv E Psi (by exact_mod_cast hdm) 1
        (by simp [hJ])).apply_symm_apply _
    rw [hclasspair]
    apply AddChar.ext
    intro q
    obtain ⟨x, rfl⟩ :=
      latticeQuotientMk_surjective E (by exact_mod_cast hdm) q
    obtain ⟨z, hz⟩ :=
      (truncatedLogOnLattice_bijective E p d hchar hp hd).2 x
    have hzval := congrArg Subtype.val hz
    rw [lamprechtPairingLeft_apply, lamprechtPairing_mk_mk]
    simp only [Units.val_one, div_one]
    change
      (Psi.character ((B : E) * (x : E)) : ℂ) =
        enhancedLinearizationCharacter E theta p d hchar hp hd hdm hlog
          (latticeQuotientMk E (by exact_mod_cast hdm) x)
    rw [← hz]
    rw [enhancedLinearizationCharacter_mk]
    exact congrArg Units.val (hformula z).symm

/-- Every representative of the enhanced coefficient class has exact order
`J-m`.  The proof uses nontriviality on the whole predecessor unit group,
not a single test value. -/
private theorem enhancedCoefficientClass_representative_ord
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (p d : ℕ) (J : ℤ)
    (hchar : ringChar (ResidueField E) = p) (hp : p.Prime)
    (hd : 1 ≤ d) (hdm : d ≤ theta.conductor)
    (hlog : theta.conductor ≤ p * d)
    (hJ : J = -Psi.conductor) (hlarge : 1 < theta.conductor)
    (hdpred : d + 1 ≤ theta.conductor)
    (B : lattice E (J - (theta.conductor : ℤ)))
    (hB : latticeQuotientMk E
        (sub_le_sub_left (by exact_mod_cast hdm) J) B =
      enhancedCoefficientClass E theta Psi p d J hchar hp hd hdm hlog hJ) :
    ord E (B : E) =
      ((J - (theta.conductor : ℤ) : ℤ) : WithTop ℤ) := by
  rw [← mem_lattice_and_not_mem_succ_iff E]
  refine ⟨B.property, ?_⟩
  intro hBdeep
  have htrivial : QuasiCharTrivialOnUnitFiltration E theta.character
      (theta.conductor - 1) := by
    intro u hu
    have hpredPos : 0 < theta.conductor - 1 := by omega
    let u0 : unitFiltration E (theta.conductor - 1) := ⟨u, hu⟩
    let z0 : lattice E ((theta.conductor - 1 : ℕ) : ℤ) :=
      truncatedLogUnitArgument E hpredPos u0
    have hdepth : d ≤ theta.conductor - 1 := by omega
    let z : lattice E (d : ℤ) :=
      ⟨(z0 : E), lattice_antitone E (by exact_mod_cast hdepth) z0.property⟩
    have hformula := enhancedCoefficientClass_spec E theta Psi p d J hchar hp
      hd hdm hlog hJ B hB z
    have hunit : (positiveUnitOfLattice E (by omega) (-z) : Eˣ) = u := by
      apply Units.ext
      simp [z, z0, u0, coe_truncatedLogUnitArgument]
    rw [hunit] at hformula
    rw [hformula]
    apply Psi.isConductor.trivial
    have hP : truncatedLog p (z : E) ∈
        lattice E ((theta.conductor - 1 : ℕ) : ℤ) := by
      have := (truncatedLogOnLattice E p (theta.conductor - 1) hchar
        (by omega) z0).property
      simpa [z, z0, truncatedLogOnLattice] using this
    have hprod := mul_mem_lattice E hBdeep hP
    have hdepthEq :
        (J - (theta.conductor : ℤ) + 1) +
            ((theta.conductor - 1 : ℕ) : ℤ) = J := by
      omega
    exact lattice_antitone E (by omega) hprod
  exact (theta.isConductor.not_trivialOnUnitFiltration_iff.2 (by omega)) htrivial

/-- Existence of the genuine enhanced coefficient, together with its exact
ambiguity modulo `𝑙^(J-d)`. -/
theorem enhancedCoefficient_exists_unique_mod
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (p d : ℕ) (J : ℤ)
    (hchar : ringChar (ResidueField E) = p) (hp : p.Prime)
    (hd : 1 ≤ d) (hdm : d ≤ theta.conductor)
    (hlog : theta.conductor ≤ p * d)
    (hJ : J = -Psi.conductor) (hlarge : 1 < theta.conductor)
    (hdpred : d + 1 ≤ theta.conductor) :
    ∃ B : Eˣ,
      IsEnhancedStationaryCoefficient E theta Psi p d (by omega) J B ∧
      ∀ B' : Eˣ,
        IsEnhancedStationaryCoefficient E theta Psi p d (by omega) J B' →
        (B : E) - (B' : E) ∈ lattice E (J - (d : ℤ)) := by
  obtain ⟨B, hB⟩ := latticeQuotientMk_surjective E
    (sub_le_sub_left (by exact_mod_cast hdm) J)
    (enhancedCoefficientClass E theta Psi p d J hchar hp hd hdm hlog hJ)
  have hBord := enhancedCoefficientClass_representative_ord E theta Psi p d J
    hchar hp hd hdm hlog hJ hlarge hdpred B hB
  have hBne : (B : E) ≠ 0 :=
    (ord_ne_top_iff E).1 (by rw [hBord]; simp)
  let Bu : Eˣ := Units.mk0 (B : E) hBne
  refine ⟨Bu, ⟨hBord, ?_⟩, ?_⟩
  · intro z
    simpa [Bu] using enhancedCoefficientClass_spec E theta Psi p d J hchar hp
      hd hdm hlog hJ B hB z
  · intro B' hB'
    let hdmZ : (d : ℤ) ≤ (theta.conductor : ℤ) := by exact_mod_cast hdm
    let hcoef : J - (theta.conductor : ℤ) ≤ J - (d : ℤ) :=
      sub_le_sub_left hdmZ J
    let B'lattice : lattice E (J - (theta.conductor : ℤ)) :=
      ⟨(B' : E), by rw [mem_lattice, hB'.1]⟩
    have hB'class : latticeQuotientMk E
        hcoef B'lattice =
        enhancedCoefficientClass E theta Psi p d J hchar hp hd hdm hlog hJ := by
      apply (latticeQuotientMk_eq_enhancedCoefficientClass_iff E theta Psi p d
        J hchar hp hd hdm hlog hJ B'lattice).2
      intro z
      simpa [B'lattice] using hB'.2 z
    have heq : latticeQuotientMk E
        hcoef B =
        latticeQuotientMk E
          hcoef B'lattice := by
      rw [hB, hB'class]
    have hdiff := (latticeQuotientMk_eq_mk_iff
      (m := J - (theta.conductor : ℤ)) (n := J - (d : ℤ)) E
      hcoef).1 heq
    simpa [Bu, B'lattice] using hdiff

/-! ## Truncated-logarithm precision -/

private theorem pow_mem_lattice
    {z : E} {r : ℕ} (hz : z ∈ lattice E (r : ℤ)) (j : ℕ) :
    z ^ j ∈ lattice E ((j * r : ℕ) : ℤ) := by
  rw [mem_lattice, ord_pow]
  rw [mem_lattice] at hz
  have h := nsmul_le_nsmul_right hz j
  calc
    ((((j * r : ℕ) : ℤ) : WithTop ℤ)) =
        j • (((r : ℤ) : WithTop ℤ)) := by
          rw [← WithTop.coe_nsmul]
          congr
    _ ≤ j • ord E z := h

private theorem inv_natCast_mem_lattice_zero
    (p j : ℕ) (hchar : ringChar (ResidueField E) = p)
    (hjpos : 0 < j) (hjlt : j < p) :
    (j : E)⁻¹ ∈ lattice E 0 := by
  rw [mem_lattice, ord_inv,
    ord_natCast_eq_zero_of_lt_residueCharacteristic E hjpos (by
      change j < ringChar (ResidueField E)
      rw [hchar]
      exact hjlt)]
  simp

/-- Beyond its linear term, `P` has depth at least `2r`. -/
private theorem truncatedLog_sub_linear_mem
    (p r : ℕ) (hchar : ringChar (ResidueField E) = p)
    {z : E} (hz : z ∈ lattice E (r : ℤ)) :
    truncatedLog p z - z ∈ lattice E ((2 * r : ℕ) : ℤ) := by
  rw [truncatedLog_apply]
  simp only [add_sub_cancel_left]
  apply sum_mem_lattice E
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  rw [div_eq_mul_inv]
  have hterm := mul_mem_lattice E (pow_mem_lattice E hz j)
    (inv_natCast_mem_lattice_zero E p j hchar (by omega) hj'.2)
  have hle : ((2 * r : ℕ) : ℤ) ≤ ((j * r : ℕ) : ℤ) := by
    exact_mod_cast Nat.mul_le_mul_right r hj'.1
  exact lattice_antitone E hle (by simpa using hterm)

/-- Beyond its quadratic term, `P` has depth at least `3r`. -/
private theorem truncatedLog_sub_quadratic_mem
    (p r : ℕ) (hchar : ringChar (ResidueField E) = p)
    (hpodd : p ≠ 2) {z : E} (hz : z ∈ lattice E (r : ℤ)) :
    truncatedLog p z - z - z ^ 2 / (2 : E) ∈
      lattice E ((3 * r : ℕ) : ℤ) := by
  have hp3 : 3 ≤ p := by
    have hp2 := (residueCharacteristic_prime E).two_le
    change 2 ≤ ringChar (ResidueField E) at hp2
    rw [hchar] at hp2
    omega
  have hsum :
      (∑ j ∈ Finset.Ico 2 p, z ^ j / (j : E)) =
        z ^ 2 / (2 : E) + ∑ j ∈ Finset.Ico 3 p, z ^ j / (j : E) := by
    rw [← Finset.insert_Ico_add_one_left_eq_Ico hp3]
    simp
  rw [truncatedLog_apply, hsum]
  ring_nf
  apply sum_mem_lattice E
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  have hterm := mul_mem_lattice E (pow_mem_lattice E hz j)
    (inv_natCast_mem_lattice_zero E p j hchar (by omega) hj'.2)
  have hterm' : z ^ j * (j : E)⁻¹ ∈ lattice E ((j * r : ℕ) : ℤ) := by
    simpa using hterm
  have hle : ((r * 3 : ℕ) : ℤ) ≤ ((j * r : ℕ) : ℤ) := by
    exact_mod_cast (show r * 3 ≤ j * r by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right r hj'.1)
  exact lattice_antitone E hle hterm'

/-! ## Ordinary displacement and the correction character -/

private theorem addChar_eq_of_sub_mem
    (Psi : LocalAddCharData E) (J : ℤ) (hJ : J = -Psi.conductor)
    {x y : E} (hxy : x - y ∈ lattice E J) :
    Psi.character x = Psi.character y := by
  have htriv : Psi.character (x - y) = 1 :=
    Psi.isConductor.trivial _ (by simpa [hJ] using hxy)
  have hmap := Psi.character.toAddChar.map_sub_eq_div x y
  apply Units.ext
  have hy : (Psi.character y : ℂ) ≠ 0 :=
    ContinuousAddChar.apply_ne_zero Psi.character y
  have hdiv : (Psi.character x : ℂ) / (Psi.character y : ℂ) = 1 := by
    simpa [htriv] using congrArg Units.val hmap.symm
  exact (div_eq_one_iff_eq hy).1 hdiv

private theorem enhanced_displacement_ord
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (p d epsilon : ℕ) (hd : 0 < d) (J : ℤ) (B : Eˣ)
    (_hepsilon : epsilon ≤ 1)
    (hm : theta.conductor = 2 * d + epsilon)
    (hB : IsEnhancedStationaryCoefficient E theta Psi p d hd J B)
    (eta : E) (heta : eta ∈ lattice E (J - (d + epsilon : ℕ))) :
    ord E ((B : E) + eta) =
      ((J - (theta.conductor : ℤ) : ℤ) : WithTop ℤ) := by
  have hetaOrd :
      (((J - (d + epsilon : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤ ord E eta :=
    heta
  have hlt : ord E (B : E) < ord E eta := by
    rw [hB.1]
    exact lt_of_lt_of_le (by
      norm_cast
      omega) hetaOrd
  simpa [hB.1] using (ord E).map_add_eq_of_lt_left hlt

private theorem enhanced_displacement_stationary
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (p d epsilon : ℕ) (hd : 0 < d) (J : ℤ) (B C : Eˣ)
    (hchar : ringChar (ResidueField E) = p)
    (hepsilon : epsilon ≤ 1)
    (hm : theta.conductor = 2 * d + epsilon)
    (hJ : J = -Psi.conductor)
    (hB : IsEnhancedStationaryCoefficient E theta Psi p d hd J B)
    (eta : E) (heta : eta ∈ lattice E (J - (d + epsilon : ℕ)))
    (hC : (C : E) = (B : E) + eta) :
    IsNormalizedStationaryCoefficientAtDepth E theta Psi C (d + epsilon)
      (by omega) := by
  intro z
  let zd : lattice E (d : ℤ) :=
    ⟨(z : E), lattice_antitone E (by norm_cast; omega) z.property⟩
  have hformula := hB.2 zd
  have hunit :
      (positiveUnitOfLattice E (by omega) (-zd) : Eˣ) =
        positiveUnitOfLattice E (by omega) (-z) := by
    apply Units.ext
    rfl
  rw [hunit] at hformula
  rw [hformula]
  apply addChar_eq_of_sub_mem E Psi J hJ
  have hPdiff := truncatedLog_sub_linear_mem E p (d + epsilon) hchar z.property
  have hBmem : (B : E) ∈ lattice E (J - (theta.conductor : ℤ)) := by
    rw [mem_lattice, hB.1]
  have hfirst := mul_mem_lattice E hBmem hPdiff
  have hfirstJ :
      (B : E) * (truncatedLog p (z : E) - (z : E)) ∈ lattice E J :=
    lattice_antitone E (by
      push_cast
      omega) hfirst
  have hetaz := mul_mem_lattice E heta z.property
  have hetazJ : eta * (z : E) ∈ lattice E J := by
    simpa only [show
      (J - (d + epsilon : ℕ)) + ((d + epsilon : ℕ) : ℤ) = J by
        push_cast
        omega] using hetaz
  have hdiff := sub_mem_lattice E hfirstJ hetazJ
  convert hdiff using 1
  rw [hC]
  ring

/-- The affine correction is trivial at the stronger enhanced ambiguity
depth `J-d`, in either parity. -/
theorem enhancedCorrection_eq_one
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (p d epsilon : ℕ) (hd : 0 < d) (J : ℤ) (B : Eˣ)
    (hchar : ringChar (ResidueField E) = p) (hpodd : p ≠ 2)
    (hepsilon : epsilon ≤ 1)
    (hm : theta.conductor = 2 * d + epsilon)
    (hJ : J = -Psi.conductor)
    (hB : IsEnhancedStationaryCoefficient E theta Psi p d hd J B)
    (eta : E) (heta : eta ∈ lattice E (J - (d : ℤ))) :
    Psi.character (eta ^ 2 / ((2 : E) * (B : E))) = 1 := by
  apply Psi.isConductor.trivial
  have hetaSq : eta ^ 2 ∈
      lattice E ((J - (d : ℤ)) + (J - (d : ℤ))) := by
    simpa only [pow_two] using mul_mem_lattice E heta heta
  have htwo : ord E (2 : E) = 0 := by
    apply ord_natCast_eq_zero_of_lt_residueCharacteristic E (j := 2) (by omega)
    change 2 < ringChar (ResidueField E)
    rw [hchar]
    have hp2 := (residueCharacteristic_prime E).two_le
    change 2 ≤ ringChar (ResidueField E) at hp2
    rw [hchar] at hp2
    omega
  have hden : ord E ((2 : E) * (B : E)) =
      ((J - (theta.conductor : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_mul, htwo, hB.1, zero_add]
  have hle :
      (J - (theta.conductor : ℤ)) + J ≤
        (J - (d : ℤ)) + (J - (d : ℤ)) := by
    omega
  have hquot := (div_mem_lattice_iff E ((2 : E) * (B : E)) (eta ^ 2)
    (J - (theta.conductor : ℤ)) J hden).2
      (lattice_antitone E hle hetaSq)
  simpa [hJ] using hquot

/-! ## The exact odd residual quadratic -/

/-- The enhanced `P`-identity gives the exact quadratic expansion at the
character precision. -/
private theorem enhanced_theta_one_add
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (p d epsilon : ℕ) (hd : 0 < d) (J : ℤ) (B : Eˣ)
    (hchar : ringChar (ResidueField E) = p) (hpodd : p ≠ 2)
    (hepsilon : epsilon ≤ 1)
    (hm : theta.conductor = 2 * d + epsilon)
    (hJ : J = -Psi.conductor)
    (hB : IsEnhancedStationaryCoefficient E theta Psi p d hd J B)
    (v : lattice E (d : ℤ)) :
    theta.character (positiveUnitOfLattice E hd v) =
      Psi.character (-(B : E) * (v : E) +
        (B : E) * (v : E) ^ 2 / (2 : E)) := by
  have hformula := hB.2 (-v)
  have hunit :
      (positiveUnitOfLattice E hd (-(-v)) : Eˣ) =
        positiveUnitOfLattice E hd v := by
    congr 1
    simp
  rw [hunit] at hformula
  rw [hformula]
  apply addChar_eq_of_sub_mem E Psi J hJ
  have hrem := truncatedLog_sub_quadratic_mem E p d hchar hpodd
    (neg_mem_lattice E v.property)
  have hBmem : (B : E) ∈ lattice E (J - (theta.conductor : ℤ)) := by
    rw [mem_lattice, hB.1]
  have hprod := mul_mem_lattice E hBmem hrem
  have hprodJ :
      (B : E) *
          (truncatedLog p (-(v : E)) - (-(v : E)) -
            (-(v : E)) ^ 2 / (2 : E)) ∈ lattice E J :=
    lattice_antitone E (by
      push_cast
      omega) hprod
  change
    (B : E) * truncatedLog p (-(v : E)) -
        (-(B : E) * (v : E) + (B : E) * (v : E) ^ 2 / (2 : E)) ∈
      lattice E J
  rw [show
    (B : E) * truncatedLog p (-(v : E)) -
        (-(B : E) * (v : E) + (B : E) * (v : E) ^ 2 / (2 : E)) =
      (B : E) *
        (truncatedLog p (-(v : E)) - (-(v : E)) -
          (-(v : E)) ^ 2 / (2 : E)) by ring]
  exact hprodJ

private theorem enhanced_residualGamma_ord
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (p d : ℕ) (hd : 0 < d) (J : ℤ) (B delta : Eˣ)
    (hm : theta.conductor = 2 * d + 1)
    (hJ : J = -Psi.conductor)
    (hB : IsEnhancedStationaryCoefficient E theta Psi p d hd J B)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ)) :
    ord E (((-B * delta ^ 2)⁻¹ : Eˣ) : E) =
      ((Psi.conductor + 1 : ℤ) : WithTop ℤ) := by
  simp only [Units.val_inv_eq_inv_val, Units.val_mul, Units.val_neg,
    Units.val_pow_eq_pow_val]
  rw [ord_inv, ord_mul, ord_neg, hB.1, ord_pow, hdelta]
  simp only [two_nsmul]
  norm_cast
  omega

private theorem enhanced_residualAddChar_apply
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (p d : ℕ) (hd : 0 < d) (J : ℤ) (B delta : Eˣ)
    (hm : theta.conductor = 2 * d + 1)
    (hJ : J = -Psi.conductor)
    (hB : IsEnhancedStationaryCoefficient E theta Psi p d hd J B)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (z : E) (hz : z ∈ lattice E 0) :
    residualAddChar E Psi ((-B * delta ^ 2)⁻¹)
        (enhanced_residualGamma_ord E theta Psi p d hd J B delta hm hJ hB hdelta)
        (reduce E z hz) =
      (Psi.character (-(B : E) * (delta : E) ^ 2 * z) : ℂ) := by
  rw [residualAddChar_integral_lift]
  congr 2
  simp only [Units.val_inv_eq_inv_val, Units.val_mul, Units.val_neg,
    Units.val_pow_eq_pow_val]
  field_simp [Units.ne_zero B, Units.ne_zero delta]

private theorem enhanced_residualShift_mem
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (p d : ℕ) (hd : 0 < d) (J : ℤ) (B delta : Eˣ)
    (hm : theta.conductor = 2 * d + 1)
    (hB : IsEnhancedStationaryCoefficient E theta Psi p d hd J B)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (eta : E) (heta : eta ∈ lattice E (J - (d + 1 : ℕ))) :
    eta / ((B : E) * (delta : E)) ∈ lattice E 0 := by
  have hden : ord E ((B : E) * (delta : E)) =
      ((J - (d + 1 : ℕ) : ℤ) : WithTop ℤ) := by
    rw [ord_mul, hB.1, hdelta]
    norm_cast
    omega
  exact (div_mem_lattice_iff E ((B : E) * (delta : E)) eta
    (J - (d + 1 : ℕ)) 0 hden).2 (by simpa using heta)

noncomputable def enhancedResidualShift
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (p d : ℕ) (hd : 0 < d) (J : ℤ) (B delta : Eˣ)
    (hm : theta.conductor = 2 * d + 1)
    (hB : IsEnhancedStationaryCoefficient E theta Psi p d hd J B)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (eta : E) (heta : eta ∈ lattice E (J - (d + 1 : ℕ))) :
    ResidueField E :=
  reduce E (eta / ((B : E) * (delta : E)))
    (enhanced_residualShift_mem E theta Psi p d hd J B delta hm hB hdelta
      eta heta)

noncomputable def enhancedResidualAddChar
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (p d : ℕ) (hd : 0 < d) (J : ℤ) (B delta : Eˣ)
    (hm : theta.conductor = 2 * d + 1)
    (hJ : J = -Psi.conductor)
    (hB : IsEnhancedStationaryCoefficient E theta Psi p d hd J B)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ)) :
    FiniteAddChar (ResidueField E) :=
  residualAddChar E Psi ((-B * delta ^ 2)⁻¹)
    (enhanced_residualGamma_ord E theta Psi p d hd J B delta hm hJ hB hdelta)

theorem enhancedResidualAddChar_ne_one
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (p d : ℕ) (hd : 0 < d) (J : ℤ) (B delta : Eˣ)
    (hm : theta.conductor = 2 * d + 1)
    (hJ : J = -Psi.conductor)
    (hB : IsEnhancedStationaryCoefficient E theta Psi p d hd J B)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ)) :
    enhancedResidualAddChar E theta Psi p d hd J B delta hm hJ hB hdelta ≠ 1 :=
  residualAddChar_ne_one E Psi ((-B * delta ^ 2)⁻¹)
    (enhanced_residualGamma_ord E theta Psi p d hd J B delta hm hJ hB hdelta)

private theorem enhanced_normalizedResidualFunction
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (alpha : Eˣ) (p d : ℕ) (hd : 0 < d) (J : ℤ) (B C : Eˣ)
    (hchar : ringChar (ResidueField E) = p) (hpodd : p ≠ 2)
    (hm : theta.conductor = 2 * d + 1) (hlarge : 1 < theta.conductor)
    (hJ : J = -(scaleAddCharData E psi alpha).conductor)
    (hB : IsEnhancedStationaryCoefficient E theta
      (scaleAddCharData E psi alpha) p d hd J B)
    (eta : E) (hC : (C : E) = (B : E) + eta)
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (x : ResidueField E) :
    normalizedResidualFunction E theta psi alpha C d hm hlarge delta hdelta x =
      ((scaleAddCharData E psi alpha).character
        (-eta * (delta : E) * (teichmuller E x : E) -
          (B : E) * (delta : E) ^ 2 * (teichmuller E x : E) ^ 2 / (2 : E)) : ℂ) := by
  let tx : E := (teichmuller E x : E)
  have htx : tx ∈ lattice E 0 :=
    (mem_lattice_zero_iff E).2 (teichmuller E x).property
  have hdeltaMem : (delta : E) ∈ lattice E (d : ℤ) := by
    rw [mem_lattice, hdelta]
  have hv : (delta : E) * tx ∈ lattice E (d : ℤ) := by
    simpa only [add_zero] using mul_mem_lattice E hdeltaMem htx
  let v : lattice E (d : ℤ) := ⟨(delta : E) * tx, hv⟩
  have htheta := enhanced_theta_one_add E theta (scaleAddCharData E psi alpha)
    p d 1 hd J B hchar hpodd (by omega) hm hJ hB v
  have hthetaC := congrArg Units.val htheta
  have hunit :
      (lamprechtHasseUnit E theta d hm hlarge delta hdelta tx htx : Eˣ) =
        positiveUnitOfLattice E hd v := by
    apply Units.ext
    rw [lamprechtHasseUnit_coe, coe_positiveUnitOfLattice]
  rw [normalizedResidualFunction]
  rw [hunit]
  change
    ((scaleAddCharData E psi alpha).character
        (-(C : E) * (delta : E) * (teichmuller E x : E)) : ℂ) *
        (theta.character (positiveUnitOfLattice E hd v) : ℂ)⁻¹ = _
  rw [hthetaC]
  have hcombine :
      ((scaleAddCharData E psi alpha).character
          (-(C : E) * (delta : E) * (teichmuller E x : E)) : ℂ) *
          ((scaleAddCharData E psi alpha).character
            (-(B : E) * (v : E) +
              (B : E) * (v : E) ^ 2 / (2 : E)) : ℂ)⁻¹ =
        ((scaleAddCharData E psi alpha).character
          (-(C : E) * (delta : E) * (teichmuller E x : E) -
            (-(B : E) * (v : E) +
              (B : E) * (v : E) ^ 2 / (2 : E))) : ℂ) := by
    have hmap := congrArg Units.val
      ((scaleAddCharData E psi alpha).character.toAddChar.map_sub_eq_div
        (-(C : E) * (delta : E) * (teichmuller E x : E))
        (-(B : E) * (v : E) +
          (B : E) * (v : E) ^ 2 / (2 : E)))
    push_cast at hmap
    exact hmap.symm
  rw [hcombine]
  congr 2
  dsimp only [v, tx]
  rw [hC]
  ring

private theorem enhanced_normalizedResidualFunction_eq_quadratic
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (alpha : Eˣ) (p d : ℕ) (hd : 0 < d) (J : ℤ) (B C : Eˣ)
    (hchar : ringChar (ResidueField E) = p) (hpodd : p ≠ 2)
    (hm : theta.conductor = 2 * d + 1) (hlarge : 1 < theta.conductor)
    (hJ : J = -(scaleAddCharData E psi alpha).conductor)
    (hB : IsEnhancedStationaryCoefficient E theta
      (scaleAddCharData E psi alpha) p d hd J B)
    (eta : E) (heta : eta ∈ lattice E (J - (d + 1 : ℕ)))
    (Ceq : (C : E) = (B : E) + eta)
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (x : ResidueField E) :
    normalizedResidualFunction E theta psi alpha C d hm hlarge delta hdelta x =
      enhancedResidualAddChar E theta (scaleAddCharData E psi alpha) p d hd J
        B delta hm hJ hB hdelta
        ((1 : ResidueField E) / 2 * x ^ 2 +
          enhancedResidualShift E theta (scaleAddCharData E psi alpha) p d hd J
            B delta hm hB hdelta eta heta * x) := by
  let Psi := scaleAddCharData E psi alpha
  let txR : ringOfIntegers E := teichmuller E x
  let b : E := eta / ((B : E) * (delta : E))
  have hb : b ∈ lattice E 0 :=
    enhanced_residualShift_mem E theta Psi p d hd J B delta hm hB hdelta eta heta
  have hp2 : 2 < p := by
    have hpprime : p.Prime := by
      rw [← hchar]
      exact residueCharacteristic_prime E
    have hpge := hpprime.two_le
    omega
  have hinv2 : (2 : E)⁻¹ ∈ lattice E 0 :=
    inv_natCast_mem_lattice_zero E p 2 hchar (by omega) hp2
  have htx : (txR : E) ∈ lattice E 0 :=
    (mem_lattice_zero_iff E).2 txR.property
  have htxSq : (txR : E) ^ 2 ∈ lattice E 0 := by
    simpa only [zero_add, pow_two] using mul_mem_lattice E htx htx
  have hquad : (txR : E) ^ 2 / (2 : E) ∈ lattice E 0 := by
    rw [div_eq_mul_inv]
    simpa only [zero_add] using mul_mem_lattice E htxSq hinv2
  have hlinear : b * (txR : E) ∈ lattice E 0 := by
    simpa only [zero_add] using mul_mem_lattice E hb htx
  let q : E := (txR : E) ^ 2 / (2 : E) + b * (txR : E)
  have hq : q ∈ lattice E 0 := add_mem_lattice E hquad hlinear
  have hreduce :
      reduce E q hq =
        (1 : ResidueField E) / 2 * x ^ 2 +
          enhancedResidualShift E theta Psi p d hd J B delta hm hB hdelta eta heta * x := by
    let inv2R : ringOfIntegers E :=
      ⟨(2 : E)⁻¹, (mem_lattice_zero_iff E).1 hinv2⟩
    let bR : ringOfIntegers E := ⟨b, (mem_lattice_zero_iff E).1 hb⟩
    let qR : ringOfIntegers E := txR ^ 2 * inv2R + bR * txR
    have hqR : (qR : E) = q := by
      dsimp only [qR, q, inv2R, bR]
      change (txR : E) ^ 2 * (2 : E)⁻¹ + b * (txR : E) =
        (txR : E) ^ 2 / (2 : E) + b * (txR : E)
      rw [div_eq_mul_inv]
    have hinv2res : residueMap E inv2R = (2 : ResidueField E)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      change residueMap E inv2R * residueMap E (2 : ringOfIntegers E) = 1
      rw [← map_mul]
      have htwo : (2 : E) ≠ 0 := by
        intro hzero
        have hord := ord_natCast_eq_zero_of_lt_residueCharacteristic E
          (j := 2) (by omega) (by
            change 2 < ringChar (ResidueField E)
            rw [hchar]
            exact hp2)
        have heq : (0 : WithTop ℤ) = ⊤ := by
          calc
            (0 : WithTop ℤ) = ord E (2 : E) := hord.symm
            _ = ord E 0 := congrArg (ord E) hzero
            _ = ⊤ := ord_zero E
        exact WithTop.coe_ne_top heq
      rw [show inv2R * (2 : ringOfIntegers E) = 1 by
        apply Subtype.ext
        exact inv_mul_cancel₀ htwo]
      exact map_one (residueMap E)
    change residueMap E ⟨q, (mem_lattice_zero_iff E).1 hq⟩ = _
    have hqSubtype :
        (⟨q, (mem_lattice_zero_iff E).1 hq⟩ : ringOfIntegers E) = qR :=
      Subtype.ext hqR.symm
    rw [hqSubtype]
    change residueMap E qR = _
    simp only [qR, map_add, map_mul, map_pow, hinv2res, one_div]
    rw [show residueMap E txR = x by
      exact residueMap_teichmuller E x]
    have hbmap : residueMap E bR =
        enhancedResidualShift E theta Psi p d hd J B delta hm hB hdelta eta heta := by
      rfl
    rw [hbmap]
    ring
  rw [enhanced_normalizedResidualFunction E theta psi alpha p d hd J B C
    hchar hpodd hm hlarge hJ hB eta Ceq delta hdelta x]
  rw [← hreduce]
  symm
  change residualAddChar E Psi ((-B * delta ^ 2)⁻¹) _ (reduce E q hq) = _
  rw [enhanced_residualAddChar_apply E theta Psi p d hd J B delta hm hJ hB
    hdelta q hq]
  congr 2
  dsimp only [q, b, txR, Psi]
  field_simp [Units.ne_zero B, Units.ne_zero delta]
  ring

/-- In odd conductor, the complete normalized residual factor is the genuine
finite-field quadratic phase whose affine coefficient is the reduction of
`eta / (B * delta)`. -/
theorem enhancedNormalizedResidualFactor_eq_quadraticPhase
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (alpha : Eˣ) (p d : ℕ) (hd : 0 < d) (J : ℤ) (B C : Eˣ)
    (hchar : ringChar (ResidueField E) = p) (hpodd : p ≠ 2)
    (hm : theta.conductor = 2 * d + 1) (hlarge : 1 < theta.conductor)
    (hJ : J = -(scaleAddCharData E psi alpha).conductor)
    (hB : IsEnhancedStationaryCoefficient E theta
      (scaleAddCharData E psi alpha) p d hd J B)
    (eta : E) (heta : eta ∈ lattice E (J - (d + 1 : ℕ)))
    (Ceq : (C : E) = (B : E) + eta)
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ)) :
    normalizedResidualFactor E theta psi alpha C d hm hlarge delta hdelta =
      @quadraticPhase (ResidueField E) _ (residueFieldFintype E)
        (enhancedResidualAddChar E theta (scaleAddCharData E psi alpha)
          p d hd J B delta hm hJ hB hdelta)
        1
        (enhancedResidualShift E theta (scaleAddCharData E psi alpha)
          p d hd J B delta hm hB hdelta eta heta) := by
  letI := residueFieldFintype E
  let Psi := scaleAddCharData E psi alpha
  let psi0 := enhancedResidualAddChar E theta Psi p d hd J B delta hm hJ hB hdelta
  let b0 := enhancedResidualShift E theta Psi p d hd J B delta hm hB hdelta eta heta
  have hcharOdd : ringChar (ResidueField E) ≠ 2 := by
    rw [hchar]
    exact hpodd
  have hpsi0 : psi0 ≠ 1 :=
    enhancedResidualAddChar_ne_one E theta Psi p d hd J B delta hm hJ hB hdelta
  have hsum :
      (∑ x : ResidueField E,
          normalizedResidualFunction E theta psi alpha C d hm hlarge delta hdelta x) =
        quadraticSum psi0 1 b0 := by
    rw [quadraticSum]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [enhanced_normalizedResidualFunction_eq_quadratic E theta psi alpha p d hd
      J B C hchar hpodd hm hlarge hJ hB eta heta Ceq delta hdelta x]
  have hne : quadraticSum psi0 1 b0 ≠ 0 :=
    quadraticSum_ne_zero hcharOdd hpsi0 one_ne_zero b0
  have hnorm : ‖quadraticSum psi0 1 b0‖ =
      Real.sqrt (Fintype.card (ResidueField E) : ℝ) :=
    quadraticSum_norm hcharOdd hpsi0 one_ne_zero b0
  rw [normalizedResidualFactor, hsum]
  change (Real.sqrt (residueCard E : ℝ) : ℂ)⁻¹ * quadraticSum psi0 1 b0 =
    phase (quadraticSum psi0 1 b0)
  rw [phase_of_ne_zero hne, hnorm]
  rw [show residueCard E = Fintype.card (ResidueField E) by rfl,
    div_eq_mul_inv, mul_comm]

/-- Completing the residual square produces exactly the manuscript's local
character value `Psi(eta^2 / (2 * B))`; in particular the denominator is the
original enhanced coefficient, not the displaced coefficient. -/
theorem enhancedResidualAffineCorrection
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (p d : ℕ) (hd : 0 < d) (J : ℤ) (B delta : Eˣ)
    (hchar : ringChar (ResidueField E) = p) (hpodd : p ≠ 2)
    (hm : theta.conductor = 2 * d + 1)
    (hJ : J = -Psi.conductor)
    (hB : IsEnhancedStationaryCoefficient E theta Psi p d hd J B)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (eta : E) (heta : eta ∈ lattice E (J - (d + 1 : ℕ))) :
    enhancedResidualAddChar E theta Psi p d hd J B delta hm hJ hB hdelta
        (-enhancedResidualShift E theta Psi p d hd J B delta hm hB hdelta
          eta heta ^ 2 / 2) =
      (Psi.character (eta ^ 2 / ((2 : E) * (B : E))) : ℂ) := by
  let b : E := eta / ((B : E) * (delta : E))
  have hb : b ∈ lattice E 0 :=
    enhanced_residualShift_mem E theta Psi p d hd J B delta hm hB hdelta eta heta
  have hp2 : 2 < p := by
    have hpprime : p.Prime := by
      rw [← hchar]
      exact residueCharacteristic_prime E
    have hpge := hpprime.two_le
    omega
  have hinv2 : (2 : E)⁻¹ ∈ lattice E 0 :=
    inv_natCast_mem_lattice_zero E p 2 hchar (by omega) hp2
  have hbSq : b ^ 2 ∈ lattice E 0 := by
    simpa only [zero_add, pow_two] using mul_mem_lattice E hb hb
  have hq : -b ^ 2 / (2 : E) ∈ lattice E 0 := by
    rw [div_eq_mul_inv]
    simpa only [zero_add] using
      mul_mem_lattice E (neg_mem_lattice E hbSq) hinv2
  have hreduce :
      reduce E (-b ^ 2 / (2 : E)) hq =
        -enhancedResidualShift E theta Psi p d hd J B delta hm hB hdelta
          eta heta ^ 2 / 2 := by
    let inv2R : ringOfIntegers E :=
      ⟨(2 : E)⁻¹, (mem_lattice_zero_iff E).1 hinv2⟩
    let bR : ringOfIntegers E := ⟨b, (mem_lattice_zero_iff E).1 hb⟩
    let qR : ringOfIntegers E := -(bR ^ 2 * inv2R)
    have hqR : (qR : E) = -b ^ 2 / (2 : E) := by
      dsimp only [qR, bR, inv2R]
      change -(b ^ 2 * (2 : E)⁻¹) = -b ^ 2 / (2 : E)
      rw [div_eq_mul_inv]
      ring
    have htwo : (2 : E) ≠ 0 := by
      intro hzero
      have hord := ord_natCast_eq_zero_of_lt_residueCharacteristic E
        (j := 2) (by omega) (by
          change 2 < ringChar (ResidueField E)
          rw [hchar]
          exact hp2)
      have heq : (0 : WithTop ℤ) = ⊤ := by
        calc
          (0 : WithTop ℤ) = ord E (2 : E) := hord.symm
          _ = ord E 0 := congrArg (ord E) hzero
          _ = ⊤ := ord_zero E
      exact WithTop.coe_ne_top heq
    have hinv2res : residueMap E inv2R = (2 : ResidueField E)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      change residueMap E inv2R * residueMap E (2 : ringOfIntegers E) = 1
      rw [← map_mul]
      rw [show inv2R * (2 : ringOfIntegers E) = 1 by
        apply Subtype.ext
        exact inv_mul_cancel₀ htwo]
      exact map_one (residueMap E)
    change residueMap E ⟨-b ^ 2 / (2 : E),
      (mem_lattice_zero_iff E).1 hq⟩ = _
    have hqSubtype :
        (⟨-b ^ 2 / (2 : E), (mem_lattice_zero_iff E).1 hq⟩ :
          ringOfIntegers E) = qR := Subtype.ext hqR.symm
    rw [hqSubtype]
    change residueMap E qR = _
    simp only [qR, map_neg, map_mul, map_pow, hinv2res]
    have hbmap : residueMap E bR =
        enhancedResidualShift E theta Psi p d hd J B delta hm hB hdelta eta heta := by
      rfl
    rw [hbmap]
    ring
  rw [← hreduce]
  change residualAddChar E Psi ((-B * delta ^ 2)⁻¹) _
      (reduce E (-b ^ 2 / (2 : E)) hq) = _
  rw [enhanced_residualAddChar_apply E theta Psi p d hd J B delta hm hJ hB
    hdelta (-b ^ 2 / (2 : E)) hq]
  congr 2
  dsimp only [b]
  field_simp [Units.ne_zero B, Units.ne_zero delta]

private theorem enhanced_basicQuadraticPhase_pow_four
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (p d : ℕ) (hd : 0 < d) (J : ℤ) (B delta : Eˣ)
    (hchar : ringChar (ResidueField E) = p) (hpodd : p ≠ 2)
    (hm : theta.conductor = 2 * d + 1)
    (hJ : J = -Psi.conductor)
    (hB : IsEnhancedStationaryCoefficient E theta Psi p d hd J B)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ)) :
    @quadraticPhase (ResidueField E) _ (residueFieldFintype E)
        (enhancedResidualAddChar E theta Psi p d hd J B delta hm hJ hB hdelta)
        1 0 ^ 4 = 1 := by
  letI := residueFieldFintype E
  let psi0 := enhancedResidualAddChar E theta Psi p d hd J B delta hm hJ hB hdelta
  have hcharOdd : ringChar (ResidueField E) ≠ 2 := by
    rw [hchar]
    exact hpodd
  have hpsi0 : psi0 ≠ 1 :=
    enhancedResidualAddChar_ne_one E theta Psi p d hd J B delta hm hJ hB hdelta
  have hsq : quadraticPhase psi0 1 0 ^ 2 =
      finiteQuadraticChar (ResidueField E) (-1) :=
    quadraticPhase_basic_sq hcharOdd hpsi0
  calc
    quadraticPhase psi0 1 0 ^ 4 = (quadraticPhase psi0 1 0 ^ 2) ^ 2 := by ring
    _ = finiteQuadraticChar (ResidueField E) (-1) ^ 2 := by rw [hsq]
    _ = 1 := finiteQuadraticChar_sq (ResidueField E) (neg_ne_zero.mpr one_ne_zero)

/-! ## Paper 6.5: enhanced stationary phase -/

/-- The enhanced stationary lemma `O:I:enhanced`, with the coefficient,
its exact ambiguity, every displaced ordinary stationary coefficient, and
the completed affine correction packaged in one theorem.

Here `epsilon = 0` and `epsilon = 1` are respectively the even- and
odd-conductor cases, so `d = floor(m/2)` and `d + epsilon = ceil(m/2)`.
The equation `J = -Psi.conductor` says precisely that `𝑙^J` is the largest
ideal on which `Psi(x) = psi(alpha*x)` is trivial. -/
theorem enhancedStationary
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (alpha : Eˣ) (p d epsilon : ℕ) (J : ℤ)
    (hchar : ringChar (ResidueField E) = p) (hpodd : p ≠ 2)
    (hepsilon : epsilon ≤ 1)
    (hm : theta.conductor = 2 * d + epsilon)
    (hlarge : 1 < theta.conductor)
    (hJ : J = -(scaleAddCharData E psi alpha).conductor) :
    ∃ B : Eˣ,
      IsEnhancedStationaryCoefficient E theta
          (scaleAddCharData E psi alpha) p d (by omega) J B ∧
      (∀ B' : Eˣ,
        IsEnhancedStationaryCoefficient E theta
            (scaleAddCharData E psi alpha) p d (by omega) J B' →
          (B : E) - (B' : E) ∈ lattice E (J - (d : ℤ))) ∧
      ∀ eta : E, eta ∈ lattice E (J - (d + epsilon : ℕ)) →
        ∃ C : Eˣ,
          (C : E) = (B : E) + eta ∧
          ord E (C : E) =
            ((J - (theta.conductor : ℤ) : ℤ) : WithTop ℤ) ∧
          IsNormalizedStationaryCoefficientAtDepth E theta
            (scaleAddCharData E psi alpha) C (d + epsilon)
            (lamprechtFormula_stationaryDepth E theta d epsilon
              hepsilon hm hlarge).pos ∧
          ∃ g : ℂ,
            g ^ 4 = 1 ∧
            LanglandsFirstMainLemma.localConstant E theta.character psi.character =
              (theta.character ((-alpha * C)⁻¹) : ℂ) *
                ((scaleAddCharData E psi alpha).character (-(C : E)) : ℂ) *
                ((scaleAddCharData E psi alpha).character
                  (eta ^ 2 / ((2 : E) * (B : E))) : ℂ) * g ∧
            (epsilon = 0 →
              g = 1 ∧
              ((scaleAddCharData E psi alpha).character
                (eta ^ 2 / ((2 : E) * (B : E))) : ℂ) = 1) ∧
            (eta ∈ lattice E (J - (d : ℤ)) →
              ((scaleAddCharData E psi alpha).character
                (eta ^ 2 / ((2 : E) * (B : E))) : ℂ) = 1) := by
  let Psi := scaleAddCharData E psi alpha
  have hp : p.Prime := by
    rw [← hchar]
    exact residueCharacteristic_prime E
  have hpge : 3 ≤ p := by
    have := hp.two_le
    omega
  have hd : 1 ≤ d := by omega
  have hdm : d ≤ theta.conductor := by omega
  have hlog : theta.conductor ≤ p * d := by
    rw [hm]
    nlinarith
  have hdpred : d + 1 ≤ theta.conductor := by omega
  obtain ⟨B, hB, hBunique⟩ := enhancedCoefficient_exists_unique_mod E theta Psi
    p d J hchar hp hd hdm hlog hJ hlarge hdpred
  refine ⟨B, hB, hBunique, ?_⟩
  intro eta heta
  have hCord := enhanced_displacement_ord E theta Psi p d epsilon (by omega) J B
    hepsilon hm hB eta heta
  have hCne : (B : E) + eta ≠ 0 :=
    (ord_ne_top_iff E).1 (by rw [hCord]; simp)
  let C : Eˣ := Units.mk0 ((B : E) + eta) hCne
  have hCeq : (C : E) = (B : E) + eta := rfl
  have hstationary :
      IsNormalizedStationaryCoefficientAtDepth E theta Psi C (d + epsilon)
        (lamprechtFormula_stationaryDepth E theta d epsilon
          hepsilon hm hlarge).pos :=
    enhanced_displacement_stationary E theta Psi p d epsilon (by omega) J B C
      hchar hepsilon hm hJ hB eta heta hCeq
  have hCord' : ord E (C : E) =
      ((-Psi.conductor - (theta.conductor : ℤ) : ℤ) : WithTop ℤ) := by
    simpa only [hCeq, hJ] using hCord
  have hnormalized := normalizedFactor E theta psi alpha C d epsilon hepsilon hm
    hlarge hCord' hstationary
  refine ⟨C, hCeq, by simpa only [hCeq] using hCord, hstationary, ?_⟩
  by_cases heven : epsilon = 0
  · have hetaDeep : eta ∈ lattice E (J - (d : ℤ)) := by
      simpa [heven] using heta
    have hcorrectionUnits := enhancedCorrection_eq_one E theta Psi p d epsilon
      (by omega) J B hchar hpodd hepsilon hm hJ hB eta hetaDeep
    have hcorrection := congrArg Units.val hcorrectionUnits
    refine ⟨1, by norm_num, ?_, ?_, ?_⟩
    · calc
        LanglandsFirstMainLemma.localConstant E theta.character psi.character =
            (theta.character ((-alpha * C)⁻¹) : ℂ) *
              (Psi.character (-(C : E)) : ℂ) := hnormalized.1 heven
        _ = (theta.character ((-alpha * C)⁻¹) : ℂ) *
              (Psi.character (-(C : E)) : ℂ) *
              (Psi.character (eta ^ 2 / ((2 : E) * (B : E))) : ℂ) * 1 := by
          rw [hcorrection]
          simp only [Units.val_one, mul_one]
    · intro _
      exact ⟨rfl, hcorrection⟩
    · intro _
      exact hcorrection
  · have hodd : epsilon = 1 := by omega
    letI := residueFieldFintype E
    obtain ⟨delta0, hdelta0⟩ := exists_ord_eq E (d : ℤ)
    have hdelta0ne : delta0 ≠ 0 :=
      (ord_ne_top_iff E).1 (by rw [hdelta0]; simp)
    let delta : Eˣ := Units.mk0 delta0 hdelta0ne
    have hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ) := hdelta0
    have hetaOdd : eta ∈ lattice E (J - (d + 1 : ℕ)) := by
      simpa only [hodd] using heta
    let psi0 := enhancedResidualAddChar E theta Psi p d (by omega) J B delta
      (by omega) hJ hB hdelta
    let b0 := enhancedResidualShift E theta Psi p d (by omega) J B delta
      (by omega) hB hdelta eta hetaOdd
    let g : ℂ := quadraticPhase psi0 1 0
    have hcharOdd : ringChar (ResidueField E) ≠ 2 := by
      rw [hchar]
      exact hpodd
    have hpsi0 : psi0 ≠ 1 :=
      enhancedResidualAddChar_ne_one E theta Psi p d (by omega) J B delta
        (by omega) hJ hB hdelta
    have hresidual :
        normalizedResidualFactor E theta psi alpha C d (by omega) hlarge delta
            hdelta =
          ((Psi.character (eta ^ 2 / ((2 : E) * (B : E))) : ℂ) * g) := by
      calc
        normalizedResidualFactor E theta psi alpha C d (by omega) hlarge delta
            hdelta = quadraticPhase psi0 1 b0 :=
          enhancedNormalizedResidualFactor_eq_quadraticPhase E theta psi alpha
            p d (by omega) J B C hchar hpodd (by omega) hlarge hJ hB eta
            hetaOdd hCeq delta hdelta
        _ = psi0 (-b0 ^ 2 / (2 * 1)) * quadraticPhase psi0 1 0 :=
          quadraticPhase_completeSquare hcharOdd hpsi0 one_ne_zero b0
        _ = (Psi.character (eta ^ 2 / ((2 : E) * (B : E))) : ℂ) * g := by
          have hc := enhancedResidualAffineCorrection E theta Psi p d (by omega)
            J B delta hchar hpodd (by omega) hJ hB hdelta eta hetaOdd
          simpa only [mul_one, g] using congrArg (fun z : ℂ ↦ z * g) hc
    have hg4 : g ^ 4 = 1 :=
      enhanced_basicQuadraticPhase_pow_four E theta Psi p d (by omega) J B delta
        hchar hpodd (by omega) hJ hB hdelta
    refine ⟨g, hg4, ?_, ?_, ?_⟩
    · rw [hnormalized.2 hodd delta hdelta, hresidual]
      ring
    · intro heven'
      omega
    · intro hetaDeep
      exact congrArg Units.val
        (enhancedCorrection_eq_one E theta Psi p d epsilon (by omega) J B hchar
          hpodd hepsilon hm hJ hB eta hetaDeep)

end

end LanglandsSecondMainLemma.Odd
