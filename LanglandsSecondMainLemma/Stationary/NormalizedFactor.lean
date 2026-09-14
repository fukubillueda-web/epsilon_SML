import LanglandsFirstMainLemma.Delta.Elementary
import LanglandsFirstMainLemma.Delta.LocalConstantRealization
import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Basic.LocalConstants

/-!
# Stationary / Normalized Factor

Blueprint: blueprint/tasks/Stationary/NormalizedFactor.md
Paper: U:stationary-factor

This module translates FML's positive-sign stationary numerator into the
manuscript's coefficient `Z`, whose convention is
`theta (1 - z) = Psi (Z * z)`.  The translated numerator is constructed as
`(-alpha * Z) * Gamma`; it is never assumed as an extra representative.

The odd residual factor below is the full affine critical function, normalized
as `|k_E|^(-1/2) * sum H_E`.  The final two theorems give the normalized
Lamprecht formula in both parities and the paper's terminal-coset invariance.
-/

namespace LanglandsSecondMainLemma.Stationary

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- The manuscript's minus-sign stationary convention at a positive depth.

The use of `positiveUnitOfLattice E hr (-z)` says literally `1 - z`, while
keeping the nonvanishing proof bundled in the unit filtration. -/
def IsNormalizedStationaryCoefficientAtDepth
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (Z : Eˣ) (r : ℕ) (hr : 0 < r) : Prop :=
  ∀ z : lattice E (r : ℤ),
    theta.character (positiveUnitOfLattice E hr (-z)) =
      Psi.character ((Z : E) * (z : E))

/-- The FML stationary numerator obtained from the manuscript coefficient.
Its value is `(-alpha * Z) * Gamma`, and the exact conductor equation proves
that it is a unit. -/
private def normalizedStationaryNumerator
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (alpha Z : Eˣ) (Gamma : AdmissibleGamma E theta psi)
    (hZ : ord E (Z : E) =
      ((-(scaleAddCharData E psi alpha).conductor - (theta.conductor : ℤ) : ℤ) :
        WithTop ℤ)) :
    lattice E ((theta.conductor : ℤ) - (theta.conductor : ℤ)) :=
  ⟨-(alpha : E) * (Z : E) * ((Gamma : Eˣ) : E), by
    rw [sub_self, mem_lattice, ord_mul, ord_mul, ord_neg,
      ord_coe_eq_unitOrder E alpha, hZ, Gamma.property,
      scaleAddCharData_conductor]
    norm_cast
    omega⟩

@[simp]
private theorem normalizedStationaryNumerator_coe
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (alpha Z : Eˣ) (Gamma : AdmissibleGamma E theta psi)
    (hZ : ord E (Z : E) =
      ((-(scaleAddCharData E psi alpha).conductor - (theta.conductor : ℤ) : ℤ) :
        WithTop ℤ)) :
    (normalizedStationaryNumerator E theta psi alpha Z Gamma hZ : E) =
      -(alpha : E) * (Z : E) * ((Gamma : Eˣ) : E) :=
  rfl

/-- The constructed numerator represents FML's stationary quotient class.
The proof applies the manuscript hypothesis to `-x`, which accounts for both
minus signs in the covector `-alpha * Z`. -/
private theorem normalizedStationaryNumerator_represents
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (alpha Z : Eˣ) (d epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (hm : theta.conductor = 2 * d + epsilon)
    (hlarge : 1 < theta.conductor)
    (Gamma : AdmissibleGamma E theta psi)
    (hZ : ord E (Z : E) =
      ((-(scaleAddCharData E psi alpha).conductor - (theta.conductor : ℤ) : ℤ) :
        WithTop ℤ))
    (hstationary : IsNormalizedStationaryCoefficientAtDepth E theta
      (scaleAddCharData E psi alpha) Z (d + epsilon)
      (lamprechtFormula_stationaryDepth E theta d epsilon
        hepsilon hm hlarge).pos) :
    latticeQuotientMk E
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth E theta d epsilon
            hepsilon hm hlarge).int_le_conductor
          (theta.conductor : ℤ))
        (normalizedStationaryNumerator E theta psi alpha Z Gamma hZ) =
      stationaryNumeratorClass E theta psi (theta.conductor : ℤ)
        (lamprechtFormula_stationaryDepth E theta d epsilon
          hepsilon hm hlarge) Gamma Gamma.property := by
  apply (latticeQuotientMk_eq_stationaryNumeratorClass_iff
    E theta psi (theta.conductor : ℤ)
      (lamprechtFormula_stationaryDepth E theta d epsilon
        hepsilon hm hlarge) Gamma Gamma.property _).2
  intro x
  have hs := hstationary (-x)
  have harg :
      ((normalizedStationaryNumerator E theta psi alpha Z Gamma hZ : E) *
          (x : E) / ((Gamma : Eˣ) : E)) =
        (alpha : E) * ((Z : E) *
          ((-x : lattice E ((d + epsilon : ℕ) : ℤ)) : E)) := by
    rw [normalizedStationaryNumerator_coe]
    simp only [Submodule.coe_neg]
    field_simp [AdmissibleGamma.coe_ne_zero Gamma]
  rw [harg, ← scaleAddCharData_character_apply]
  simpa only [neg_neg] using hs

/-- The complete normalized critical value on the depth-`d` lattice:
`Psi (-Z v) * theta (1 + v)⁻¹`. -/
def normalizedCriticalValue
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (Z : Eˣ) (d : ℕ) (hd : 0 < d) (v : lattice E (d : ℤ)) : ℂ :=
  (Psi.character (-(Z : E) * (v : E)) : ℂ) *
    (theta.character (positiveUnitOfLattice E hd v) : ℂ)⁻¹

/-- In even conductor the normalized critical value is identically one on
the full terminal lattice `𝓅_E^d`. -/
theorem normalizedCriticalValue_even
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (Z : Eˣ) (d : ℕ) (hm : theta.conductor = 2 * d)
    (hlarge : 1 < theta.conductor)
    (hstationary : IsNormalizedStationaryCoefficientAtDepth E theta Psi Z d
      (by omega)) (v : lattice E (d : ℤ)) :
    normalizedCriticalValue E theta Psi Z d (by omega) v = 1 := by
  have hs := hstationary (-v)
  have hsC := congrArg (Units.val : ℂˣ → ℂ) hs
  rw [normalizedCriticalValue]
  have hsC' :
      (theta.character (positiveUnitOfLattice E (by omega) v) : ℂ) =
        (Psi.character (-(Z : E) * (v : E)) : ℂ) := by
    simpa only [Submodule.coe_neg, neg_neg, mul_neg, neg_mul] using hsC
  rw [hsC']
  exact mul_inv_cancel₀
    (ContinuousAddChar.apply_ne_zero Psi.character (-(Z : E) * (v : E)))

/-- The normalized odd residual function
`H_E(x) = Psi (-Z * delta * x) * theta (1 + delta * x)⁻¹`.

Teichmüller representatives merely provide concrete lifts; terminal-coset
invariance below proves that the value depends only on the residue class. -/
def normalizedResidualFunction
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (alpha Z : Eˣ) (d : ℕ)
    (hm : theta.conductor = 2 * d + 1) (hlarge : 1 < theta.conductor)
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (x : ResidueField E) : ℂ :=
  ((scaleAddCharData E psi alpha).character
      (-(Z : E) * (delta : E) * (teichmuller E x : E)) : ℂ) *
    (theta.character
      (lamprechtHasseUnit E theta d hm hlarge delta hdelta
        (teichmuller E x : E)
        ((mem_lattice_zero_iff E).2 (teichmuller E x).property)) : ℂ)⁻¹

/-- The manuscript normalization `|k_E|^(-1/2) * sum H_E`. -/
noncomputable def normalizedResidualFactor
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (alpha Z : Eˣ) (d : ℕ)
    (hm : theta.conductor = 2 * d + 1) (hlarge : 1 < theta.conductor)
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ)) : ℂ := by
  letI := residueFieldFintype E
  exact (Real.sqrt (residueCard E : ℝ) : ℂ)⁻¹ *
    ∑ x : ResidueField E,
      normalizedResidualFunction E theta psi alpha Z d hm hlarge delta hdelta x

/-- The elementary part of FML's formula is exactly the manuscript's
normalized elementary factor. -/
private theorem normalizedElementaryFactor_eq
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (alpha Z : Eˣ) (d epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (hm : theta.conductor = 2 * d + epsilon)
    (hlarge : 1 < theta.conductor)
    (Gamma : AdmissibleGamma E theta psi)
    (hZ : ord E (Z : E) =
      ((-(scaleAddCharData E psi alpha).conductor - (theta.conductor : ℤ) : ℤ) :
        WithTop ℤ))
    (hstationary : IsNormalizedStationaryCoefficientAtDepth E theta
      (scaleAddCharData E psi alpha) Z (d + epsilon)
      (lamprechtFormula_stationaryDepth E theta d epsilon
        hepsilon hm hlarge).pos) :
    let c := normalizedStationaryNumerator E theta psi alpha Z Gamma hZ
    let hc := normalizedStationaryNumerator_represents E theta psi alpha Z
      d epsilon hepsilon hm hlarge Gamma hZ hstationary
    (theta.character (Gamma : Eˣ) : ℂ) *
        lamprechtElementaryFactor E theta psi Gamma
          (lamprechtStationaryRepresentativeUnit E theta psi
            (lamprechtFormula_stationaryDepth E theta d epsilon
              hepsilon hm hlarge) Gamma c hc) =
      (theta.character ((-alpha * Z)⁻¹) : ℂ) *
        ((scaleAddCharData E psi alpha).character (-(Z : E)) : ℂ) := by
  dsimp only
  let c := normalizedStationaryNumerator E theta psi alpha Z Gamma hZ
  let hc := normalizedStationaryNumerator_represents E theta psi alpha Z
    d epsilon hepsilon hm hlarge Gamma hZ hstationary
  let beta := lamprechtStationaryRepresentativeUnit E theta psi
    (lamprechtFormula_stationaryDepth E theta d epsilon
      hepsilon hm hlarge) Gamma c hc
  have hbeta : beta = (-alpha * Z) * (Gamma : Eˣ) := by
    apply Units.ext
    change (c : E) = (-((alpha : E)) * (Z : E)) * ((Gamma : Eˣ) : E)
    rfl
  have hpsi :
      (psi.character ((beta : E) / ((Gamma : Eˣ) : E)) : ℂ) =
        ((scaleAddCharData E psi alpha).character (-(Z : E)) : ℂ) := by
    rw [scaleAddCharData_character_apply]
    congr 2
    rw [hbeta]
    simp only [Units.val_mul, Units.val_neg]
    field_simp [AdmissibleGamma.coe_ne_zero Gamma]
  have htheta :
      (theta.character (Gamma : Eˣ) : ℂ) *
          (theta.character beta : ℂ)⁻¹ =
        (theta.character ((-alpha * Z)⁻¹) : ℂ) := by
    rw [hbeta, map_mul, map_inv]
    push_cast
    field_simp [ContinuousQuasiChar.apply_ne_zero theta.character]
  rw [lamprechtElementaryFactor, hpsi]
  change (theta.character (Gamma : Eˣ) : ℂ) *
      (((scaleAddCharData E psi alpha).character (-(Z : E)) : ℂ) *
        (theta.character beta : ℂ)⁻¹) = _
  calc
    (theta.character (Gamma : Eˣ) : ℂ) *
          (((scaleAddCharData E psi alpha).character (-(Z : E)) : ℂ) *
            (theta.character beta : ℂ)⁻¹) =
        ((theta.character (Gamma : Eˣ) : ℂ) *
          (theta.character beta : ℂ)⁻¹) *
          ((scaleAddCharData E psi alpha).character (-(Z : E)) : ℂ) := by
      ring
    _ = _ := by rw [htheta]

/-- The normalized residual function is FML's complete odd Hasse function,
after substituting the constructed stationary numerator. -/
private theorem normalizedResidualFunction_eq_lamprecht
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (alpha Z : Eˣ) (d : ℕ)
    (hm : theta.conductor = 2 * d + 1) (hlarge : 1 < theta.conductor)
    (Gamma : AdmissibleGamma E theta psi)
    (hZ : ord E (Z : E) =
      ((-(scaleAddCharData E psi alpha).conductor - (theta.conductor : ℤ) : ℤ) :
        WithTop ℤ))
    (hstationary : IsNormalizedStationaryCoefficientAtDepth E theta
      (scaleAddCharData E psi alpha) Z (d + 1)
      (lamprechtFormula_stationaryDepth E theta d 1
        (by omega) hm hlarge).pos)
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (x : ResidueField E) :
    let c := normalizedStationaryNumerator E theta psi alpha Z Gamma hZ
    let hc := normalizedStationaryNumerator_represents E theta psi alpha Z
      d 1 (by omega) hm hlarge Gamma hZ hstationary
    normalizedResidualFunction E theta psi alpha Z d hm hlarge delta hdelta x =
      lamprechtHasseFunction E theta psi d hm hlarge Gamma delta hdelta c hc x := by
  dsimp only [normalizedResidualFunction, lamprechtHasseFunction,
    lamprechtHasseValue]
  rw [scaleAddCharData_character_apply]
  congr 2
  rw [normalizedStationaryNumerator_coe]
  field_simp [AdmissibleGamma.coe_ne_zero Gamma]

/-- FML's phase normalization is the literal `|k_E|^(-1/2)` normalization,
because the complete odd Hasse sum has norm `sqrt |k_E|`. -/
private theorem normalizedResidualFactor_eq_lamprecht
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (alpha Z : Eˣ) (d : ℕ)
    (hm : theta.conductor = 2 * d + 1) (hlarge : 1 < theta.conductor)
    (Gamma : AdmissibleGamma E theta psi)
    (hZ : ord E (Z : E) =
      ((-(scaleAddCharData E psi alpha).conductor - (theta.conductor : ℤ) : ℤ) :
        WithTop ℤ))
    (hstationary : IsNormalizedStationaryCoefficientAtDepth E theta
      (scaleAddCharData E psi alpha) Z (d + 1)
      (lamprechtFormula_stationaryDepth E theta d 1
        (by omega) hm hlarge).pos)
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ)) :
    letI := residueFieldFintype E
    let c := normalizedStationaryNumerator E theta psi alpha Z Gamma hZ
    let hc := normalizedStationaryNumerator_represents E theta psi alpha Z
      d 1 (by omega) hm hlarge Gamma hZ hstationary
    normalizedResidualFactor E theta psi alpha Z d hm hlarge delta hdelta =
      (lamprechtHasseFunction E theta psi d hm hlarge Gamma delta hdelta c hc).sumPhase := by
  letI := residueFieldFintype E
  dsimp only
  let c := normalizedStationaryNumerator E theta psi alpha Z Gamma hZ
  let hc := normalizedStationaryNumerator_represents E theta psi alpha Z
    d 1 (by omega) hm hlarge Gamma hZ hstationary
  let phi := lamprechtHasseFunction E theta psi d hm hlarge Gamma delta hdelta c hc
  have hfun : ∀ x : ResidueField E,
      normalizedResidualFunction E theta psi alpha Z d hm hlarge delta hdelta x =
        phi x := by
    intro x
    exact normalizedResidualFunction_eq_lamprecht E theta psi alpha Z d hm
      hlarge Gamma hZ hstationary delta hdelta x
  have hsum :
      (∑ x : ResidueField E,
          normalizedResidualFunction E theta psi alpha Z d hm hlarge delta hdelta x) =
        phi.sum := by
    rw [HasseFunction.sum]
    exact Finset.sum_congr rfl (fun x _ ↦ hfun x)
  have hne : phi.sum ≠ 0 := by
    exact lamprechtOdd_hasseSum_ne_zero E theta psi d hm hlarge Gamma delta
      hdelta c hc
  have hnorm : ‖phi.sum‖ = Real.sqrt (residueCard E : ℝ) := by
    exact lamprechtOdd_hasseSum_norm E theta psi d hm hlarge Gamma delta
      hdelta c hc
  rw [normalizedResidualFactor, hsum]
  change (Real.sqrt (residueCard E : ℝ) : ℂ)⁻¹ * phi.sum = phase phi.sum
  rw [phase_of_ne_zero hne, hnorm]
  rw [div_eq_mul_inv, mul_comm]

/-- Lamprecht's formula in the manuscript's normalized coefficient and sign
convention (`U:normalized-factor` and `U:normalized-residual`).

The first component is the even-conductor formula.  The second is the odd
formula for every choice of an element of order `d`; its residual factor is
the full affine critical sum, normalized by `|k_E|^(-1/2)`.  Here
`-(scaleAddCharData E psi alpha).conductor` is exactly the manuscript's `J`,
the largest trivial-ideal exponent of `Psi(x) = psi(alpha*x)`. -/
theorem normalizedFactor
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (alpha Z : Eˣ) (d epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (hm : theta.conductor = 2 * d + epsilon)
    (hlarge : 1 < theta.conductor)
    (hZ : ord E (Z : E) =
      ((-(scaleAddCharData E psi alpha).conductor - (theta.conductor : ℤ) : ℤ) :
        WithTop ℤ))
    (hstationary : IsNormalizedStationaryCoefficientAtDepth E theta
      (scaleAddCharData E psi alpha) Z (d + epsilon)
      (lamprechtFormula_stationaryDepth E theta d epsilon
        hepsilon hm hlarge).pos) :
    (∀ _heven : epsilon = 0,
      LanglandsFirstMainLemma.localConstant E theta.character psi.character =
        (theta.character ((-alpha * Z)⁻¹) : ℂ) *
          ((scaleAddCharData E psi alpha).character (-(Z : E)) : ℂ)) ∧
    (∀ hodd : epsilon = 1, ∀ (delta : Eˣ)
      (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ)),
      LanglandsFirstMainLemma.localConstant E theta.character psi.character =
        (theta.character ((-alpha * Z)⁻¹) : ℂ) *
          ((scaleAddCharData E psi alpha).character (-(Z : E)) : ℂ) *
          normalizedResidualFactor E theta psi alpha Z d (by omega) hlarge
            delta hdelta) := by
  constructor
  · intro heven
    subst epsilon
    let Gamma : AdmissibleGamma E theta psi :=
      Classical.choice (AdmissibleGamma.exists_admissible (F := E))
    let c := normalizedStationaryNumerator E theta psi alpha Z Gamma hZ
    let hc := normalizedStationaryNumerator_represents E theta psi alpha Z
      d 0 (by omega) hm hlarge Gamma hZ hstationary
    calc
      LanglandsFirstMainLemma.localConstant E theta.character psi.character =
          deltaFinite theta psi Gamma :=
        LanglandsFirstMainLemma.localConstant_isDeltaFinite E theta psi Gamma
      _ = (theta.character (Gamma : Eˣ) : ℂ) *
          lamprechtElementaryFactor E theta psi Gamma
            (lamprechtStationaryRepresentativeUnit E theta psi
              (lamprechtFormula_stationaryDepth E theta d 0
                (by omega) (by simpa using hm) hlarge) Gamma c hc) := by
        exact lamprechtEven E theta psi d hm hlarge Gamma c hc
      _ = _ := normalizedElementaryFactor_eq E theta psi alpha Z d 0
        (by omega) hm hlarge Gamma hZ hstationary
  · intro hodd delta hdelta
    subst epsilon
    letI := residueFieldFintype E
    let Gamma : AdmissibleGamma E theta psi :=
      Classical.choice (AdmissibleGamma.exists_admissible (F := E))
    let c := normalizedStationaryNumerator E theta psi alpha Z Gamma hZ
    let hc := normalizedStationaryNumerator_represents E theta psi alpha Z
      d 1 (by omega) hm hlarge Gamma hZ hstationary
    let phi := lamprechtHasseFunction E theta psi d hm hlarge Gamma delta
      hdelta c hc
    have helem := normalizedElementaryFactor_eq E theta psi alpha Z d 1
      (by omega) hm hlarge Gamma hZ hstationary
    have hres := normalizedResidualFactor_eq_lamprecht E theta psi alpha Z d
      hm hlarge Gamma hZ hstationary delta hdelta
    calc
      LanglandsFirstMainLemma.localConstant E theta.character psi.character =
          deltaFinite theta psi Gamma :=
        LanglandsFirstMainLemma.localConstant_isDeltaFinite E theta psi Gamma
      _ = (theta.character (Gamma : Eˣ) : ℂ) *
          lamprechtElementaryFactor E theta psi Gamma
            (lamprechtStationaryRepresentativeUnit E theta psi
              (lamprechtFormula_stationaryDepth E theta d 1
                (by omega) hm hlarge) Gamma c hc) * phi.sumPhase := by
        exact lamprechtOdd E theta psi d hm hlarge Gamma delta hdelta c hc
      _ = _ := by
        rw [helem, hres]

/-- For odd conductor the full critical value is constant on every terminal
coset of `𝓅_E^(d+1)` in `𝓅_E^d`, as asserted in
`U:stationary-factor`.  The internally used element of order `d` and
admissible denominator are constructed from the genuine local-field data and
do not occur in the statement. -/
theorem normalizedCriticalValue_odd_eq_of_congruent
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (alpha Z : Eˣ) (d : ℕ)
    (hm : theta.conductor = 2 * d + 1) (hlarge : 1 < theta.conductor)
    (hZ : ord E (Z : E) =
      ((-(scaleAddCharData E psi alpha).conductor - (theta.conductor : ℤ) : ℤ) :
        WithTop ℤ))
    (hstationary : IsNormalizedStationaryCoefficientAtDepth E theta
      (scaleAddCharData E psi alpha) Z (d + 1)
      (lamprechtFormula_stationaryDepth E theta d 1
        (by omega) hm hlarge).pos)
    (v v' : lattice E (d : ℤ))
    (hvv' : CongruentAtDepth ((d + 1 : ℕ) : ℤ) (v : E) (v' : E)) :
    normalizedCriticalValue E theta (scaleAddCharData E psi alpha) Z d
        (by omega) v =
      normalizedCriticalValue E theta (scaleAddCharData E psi alpha) Z d
        (by omega) v' := by
  obtain ⟨deltaField, hdeltaField⟩ := exists_ord_eq E (d : ℤ)
  have hdeltaField_ne : deltaField ≠ 0 := by
    apply (ord_ne_top_iff E).1
    rw [hdeltaField]
    simp
  let delta : Eˣ := Units.mk0 deltaField hdeltaField_ne
  have hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ) := hdeltaField
  let Gamma : AdmissibleGamma E theta psi :=
    Classical.choice (AdmissibleGamma.exists_admissible (F := E))
  let c := normalizedStationaryNumerator E theta psi alpha Z Gamma hZ
  let hc := normalizedStationaryNumerator_represents E theta psi alpha Z
    d 1 (by omega) hm hlarge Gamma hZ hstationary
  let z : E := (v : E) / (delta : E)
  let z' : E := (v' : E) / (delta : E)
  have hz : z ∈ lattice E 0 := by
    apply (div_mem_lattice_iff E (delta : E) (v : E) (d : ℤ) 0 hdelta).2
    simpa only [add_zero] using v.property
  have hz' : z' ∈ lattice E 0 := by
    apply (div_mem_lattice_iff E (delta : E) (v' : E) (d : ℤ) 0 hdelta).2
    simpa only [add_zero] using v'.property
  have hvz : (delta : E) * z = (v : E) := by
    dsimp only [z]
    field_simp [Units.ne_zero delta]
  have hvz' : (delta : E) * z' = (v' : E) := by
    dsimp only [z']
    field_simp [Units.ne_zero delta]
  have hzz' : CongruentAtDepth 1 z z' := by
    apply (congruentAtDepth_iff_sub_mem_lattice E 1 z z').2
    have hvdiff := (congruentAtDepth_iff_sub_mem_lattice E
      ((d + 1 : ℕ) : ℤ) (v : E) (v' : E)).1 hvv'
    have hvdiff' : (v : E) - (v' : E) ∈ lattice E ((d : ℤ) + 1) := by
      rw [← show ((d + 1 : ℕ) : ℤ) = (d : ℤ) + 1 by omega]
      exact hvdiff
    have hquot := (div_mem_lattice_iff E (delta : E)
      ((v : E) - (v' : E)) (d : ℤ) 1 hdelta).2 hvdiff'
    have halg : z - z' = ((v : E) - (v' : E)) / (delta : E) := by
      dsimp only [z, z']
      ring
    rw [halg]
    exact hquot
  have hvalue (w : lattice E (d : ℤ)) (t : E)
      (ht : t ∈ lattice E 0) (hwt : (delta : E) * t = (w : E)) :
      normalizedCriticalValue E theta (scaleAddCharData E psi alpha) Z d
          (by omega) w =
        lamprechtHasseValue E theta psi d hm hlarge Gamma delta hdelta c t ht := by
    have hunit :
        (lamprechtHasseUnit E theta d hm hlarge delta hdelta t ht : Eˣ) =
          positiveUnitOfLattice E (by omega) w := by
      apply Units.ext
      rw [lamprechtHasseUnit_coe, coe_positiveUnitOfLattice, hwt]
    have harg :
        (alpha : E) * (-(Z : E) * (w : E)) =
          (c : E) * (delta : E) * t / ((Gamma : Eˣ) : E) := by
      dsimp only [c]
      rw [normalizedStationaryNumerator_coe, ← hwt]
      field_simp [AdmissibleGamma.coe_ne_zero Gamma]
    rw [normalizedCriticalValue, lamprechtHasseValue,
      scaleAddCharData_character_apply, harg, hunit]
  rw [hvalue v z hz hvz, hvalue v' z' hz' hvz']
  exact lamprechtHasseValue_eq_of_congruent E theta psi d hm hlarge Gamma
    delta hdelta c hc z z' hz hz' hzz'

end

end LanglandsSecondMainLemma.Stationary
