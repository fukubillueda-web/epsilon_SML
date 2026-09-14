import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Dyadic.Maximal.TwoOrigins

/-!
# Dyadic / Maximal / Higher Comparison

Blueprint: blueprint/tasks/Dyadic/Maximal/HigherComparison.md
Paper: D:MX:higher

The upper and lower odd functions retain their actual multiplicative values
and their affine terms. The lower origin is `Y`, while the upper origin is
`C = Y - X`. The common correction is retained before residual summation.
-/

namespace LanglandsSecondMainLemma.Dyadic.Maximal

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators ComplexConjugate

section ResidualSums

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- Complete critical values have modulus one on their positive-depth domain,
including for nonunitary quasi-characters. -/
theorem higherCriticalValue_norm
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (Z : Eˣ) (d : ℕ) (hd : 0 < d) (v : lattice E (d : ℤ)) :
    ‖Stationary.normalizedCriticalValue E theta Psi Z d hd v‖ = 1 := by
  rw [Stationary.normalizedCriticalValue, norm_mul, norm_inv,
    localAddChar_norm_eq_one]
  have hu : (positiveUnitOfLattice E hd v : Eˣ) ∈ unitGroup E :=
    unitFiltration_le_unitGroup E d (positiveUnitOfLattice E hd v).property
  rw [continuousQuasiChar_norm_eq_one_of_mem_unitGroup E theta.character _ hu]
  simp

/-- The full odd residual sum has modulus one. The admissible denominator
is constructed directly from the stationary coefficient, and FML's canonical
finite local constant supplies its magnitude. -/
theorem higherResidualFactor_norm
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (alpha Z : Eˣ) (d : ℕ)
    (hm : theta.conductor = 2 * d + 1) (hlarge : 1 < theta.conductor)
    (hZ : ord E (Z : E) =
      ((-(scaleAddCharData E psi alpha).conductor - (theta.conductor : ℤ) : ℤ) :
        WithTop ℤ))
    (hstationary : Stationary.IsNormalizedStationaryCoefficientAtDepth E theta
      (scaleAddCharData E psi alpha) Z (d + 1) (by omega))
    (delta : Eˣ) (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ)) :
    ‖Stationary.normalizedResidualFactor E theta psi alpha Z d hm hlarge delta hdelta‖ =
      1 := by
  let Gamma : AdmissibleGamma E theta psi := ⟨(-alpha * Z)⁻¹, by
    simp only [Units.val_inv_eq_inv_val, Units.val_mul, Units.val_neg,
      ord_inv, ord_mul, ord_neg]
    rw [ord_coe_eq_unitOrder E alpha, hZ, scaleAddCharData_conductor]
    norm_cast
    omega⟩
  have hformula := (Stationary.normalizedFactor E theta psi alpha Z d 1
    (by omega) hm hlarge hZ hstationary).2 rfl delta hdelta
  have hn := congrArg norm hformula
  rw [LanglandsFirstMainLemma.localConstant_isDeltaFinite E theta psi Gamma,
    deltaFinite, norm_mul, phase_norm, mul_one] at hn
  rw [norm_mul, norm_mul, localAddChar_norm_eq_one, mul_one] at hn
  have hne : ‖(theta.character ((-alpha * Z)⁻¹) : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (ContinuousQuasiChar.apply_ne_zero _ _)
  change ‖(theta.character ((-alpha * Z)⁻¹) : ℂ)‖ = _ at hn
  exact (mul_left_cancel₀ hne (by simpa using hn.symm))

end ResidualSums

/-- Reindex the literal functions under two bijections before multiplying
their normalized sums. Pointwise reciprocals become complex conjugates because
the function values have modulus one. -/
theorem higher_reciprocal_sums
    {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
    (f : A → ℂ) (g : B → ℂ) (p : I → A) (q : I → B)
    (hp : Function.Bijective p) (hq : Function.Bijective q)
    (hpoint : ∀ i, f (p i) * g (q i) = 1)
    (hg : ∀ y, ‖g y‖ = 1) :
    (∑ x, f x) = conj (∑ y, g y) := by
  have hfg (i : I) : f (p i) = conj (g (q i)) := by
    have hconj : conj (g (q i)) * g (q i) = 1 := by
      rw [mul_comm, Complex.mul_conj', hg]
      simp
    exact mul_right_cancel₀ (norm_ne_zero_iff.mp (by rw [hg]; norm_num))
      ((hpoint i).trans hconj.symm)
  rw [← hp.sum_comp f, ← hq.sum_comp g, map_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ hfg i)

/-- The final finite-sum step of `D:MX:higher`, retaining the real common
normalization explicitly. -/
theorem higher_reciprocal_normalized_sums
    {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
    (f : A → ℂ) (g : B → ℂ) (p : I → A) (q : I → B)
    (hp : Function.Bijective p) (hq : Function.Bijective q)
    (hpoint : ∀ i, f (p i) * g (q i) = 1)
    (hg : ∀ y, ‖g y‖ = 1) (r : ℝ)
    (hmag : ‖(r : ℂ) * ∑ y, g y‖ = 1) :
    ((r : ℂ) * ∑ x, f x) * ((r : ℂ) * ∑ y, g y) = 1 := by
  have hs := higher_reciprocal_sums f g p q hp hq hpoint hg
  have hconj : (r : ℂ) * ∑ x, f x = conj ((r : ℂ) * ∑ y, g y) := by
    rw [hs, map_mul, Complex.conj_ofReal]
  rw [hconj, mul_comm, Complex.mul_conj', hmag]
  simp

section GradedDivision

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- Division by the actual origin or trace, on successive lattice quotients.
All three depths in this construction are integers. -/
def higherGradedDivide (c : Eˣ) (r n : ℤ)
    (hc : ord E (c : E) = ((r - n : ℤ) : WithTop ℤ)) :
    LatticeGradedPiece E r → LatticeGradedPiece E n :=
  latticeQuotientLift E (show r ≤ r + 1 by omega)
    (fun x ↦ latticeQuotientMk E (show n ≤ n + 1 by omega)
      ⟨(x : E) / (c : E), (div_mem_lattice_iff E _ _ (r - n) n hc).2
        (by simp)⟩)
    (by
      intro x y hxy
      apply (latticeQuotientMk_eq_mk_iff E (show n ≤ n + 1 by omega)).2
      change (x : E) / (c : E) - (y : E) / (c : E) ∈ lattice E (n + 1)
      rw [← sub_div]
      apply (div_mem_lattice_iff E _ _ (r - n) (n + 1) hc).2
      have hh := (congruentAtDepth_iff_sub_mem_lattice E (r + 1) _ _).1 hxy
      convert hh using 1
      congr 1
      ring)

@[simp]
theorem higherGradedDivide_mk (c : Eˣ) (r n : ℤ)
    (hc : ord E (c : E) = ((r - n : ℤ) : WithTop ℤ))
    (x : lattice E r) :
    higherGradedDivide E c r n hc (latticeQuotientMk E (by omega) x) =
      latticeQuotientMk E (show n ≤ n + 1 by omega)
        ⟨(x : E) / (c : E), (div_mem_lattice_iff E _ _ (r - n) n hc).2
          (by simp)⟩ := rfl

/-- The division map is a proved bijection; no choice of an exact norm
representative is required for it. -/
theorem higherGradedDivide_bijective (c : Eˣ) (r n : ℤ)
    (hc : ord E (c : E) = ((r - n : ℤ) : WithTop ℤ)) :
    Function.Bijective (higherGradedDivide E c r n hc) := by
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective E (show r ≤ r + 1 by omega) x
    obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective E (show r ≤ r + 1 by omega) y
    rw [higherGradedDivide_mk, higherGradedDivide_mk] at hxy
    apply (latticeQuotientMk_eq_mk_iff E (show r ≤ r + 1 by omega)).2
    have hh := (latticeQuotientMk_eq_mk_iff E (show n ≤ n + 1 by omega)).1 hxy
    change (x : E) / (c : E) - (y : E) / (c : E) ∈ lattice E (n + 1) at hh
    rw [← sub_div] at hh
    have hd := (div_mem_lattice_iff E _ _ (r - n) (n + 1) hc).1 hh
    convert hd using 1
    congr 1
    ring
  · intro y
    obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective E (show n ≤ n + 1 by omega) y
    have hcy : (c : E) * (y : E) ∈ lattice E r := by
      have hh := mul_mem_lattice E ((mem_lattice E).2 hc.ge) y.property
      simpa using hh
    refine ⟨latticeQuotientMk E (show r ≤ r + 1 by omega) ⟨_, hcy⟩, ?_⟩
    rw [higherGradedDivide_mk]
    congr 1
    apply Subtype.ext
    exact mul_div_cancel_left₀ _ (Units.ne_zero c)

/-- Additivity holds on the actual quotient map, not merely on a
chosen permutation of its finite underlying set. -/
theorem higherGradedDivide_add (c : Eˣ) (r n : ℤ)
    (hc : ord E (c : E) = ((r - n : ℤ) : WithTop ℤ))
    (x y : LatticeGradedPiece E r) :
    higherGradedDivide E c r n hc (x + y) =
      higherGradedDivide E c r n hc x + higherGradedDivide E c r n hc y := by
  obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective E (show r ≤ r + 1 by omega) x
  obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective E (show r ≤ r + 1 by omega) y
  rw [← map_add, higherGradedDivide_mk, higherGradedDivide_mk,
    higherGradedDivide_mk, ← map_add]
  congr 1
  apply Subtype.ext
  exact add_div _ _ _

end GradedDivision

section GradedCriticalFunction

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
  (alpha Z : Eˣ) (d : ℕ)
  (hm : theta.conductor = 2 * d + 1) (hlarge : 1 < theta.conductor)
  (hZ : ord E (Z : E) =
    ((-(scaleAddCharData E psi alpha).conductor - (theta.conductor : ℤ) : ℤ) :
      WithTop ℤ))
  (hstationary : Stationary.IsNormalizedStationaryCoefficientAtDepth E theta
    (scaleAddCharData E psi alpha) Z (d + 1) (by omega))

/-- The actual affine critical function, descended to the terminal lattice
quotient by the proved stationary invariance theorem. -/
def higherCriticalFunction : LatticeGradedPiece E (d : ℤ) → ℂ :=
  latticeQuotientLift E (show (d : ℤ) ≤ (d : ℤ) + 1 by omega)
    (Stationary.normalizedCriticalValue E theta (scaleAddCharData E psi alpha) Z d
      (by omega))
    (fun x y hxy ↦ Stationary.normalizedCriticalValue_odd_eq_of_congruent E
      theta psi alpha Z d hm hlarge hZ hstationary x y (by simpa using hxy))

@[simp]
theorem higherCriticalFunction_mk (v : lattice E (d : ℤ)) :
    higherCriticalFunction E theta psi alpha Z d hm hlarge hZ hstationary
        (latticeQuotientMk E (by omega) v) =
      Stationary.normalizedCriticalValue E theta (scaleAddCharData E psi alpha)
        Z d (by omega) v := rfl

theorem higherCriticalFunction_norm (x : LatticeGradedPiece E (d : ℤ)) :
    ‖higherCriticalFunction E theta psi alpha Z d hm hlarge hZ hstationary x‖ = 1 := by
  obtain ⟨v, rfl⟩ := latticeQuotientMk_surjective E (show (d : ℤ) ≤ (d : ℤ) + 1 by omega) x
  exact higherCriticalValue_norm E theta _ Z d (by omega) v

/-- The same normalized sum, enumerated by actual terminal lattice classes. -/
def higherCriticalSum : ℂ := by
  letI := latticeQuotientFintype E (show (d : ℤ) ≤ (d : ℤ) + 1 by omega)
  exact (Real.sqrt (residueCard E : ℝ) : ℂ)⁻¹ *
    ∑ x, higherCriticalFunction E theta psi alpha Z d hm hlarge hZ hstationary x

/-- This quotient sum is exactly the normalized residual factor for every
admissible residual scale. No coefficient or terminal representative is changed. -/
theorem higherCriticalSum_eq_residual
    (delta : Eˣ) (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ)) :
    higherCriticalSum E theta psi alpha Z d hm hlarge hZ hstationary =
      Stationary.normalizedResidualFactor E theta psi alpha Z d hm hlarge delta hdelta := by
  letI := residueFieldFintype E
  letI := latticeQuotientFintype E (show (d : ℤ) ≤ (d : ℤ) + 1 by omega)
  obtain ⟨pi, hpi⟩ := exists_ord_eq E 1
  have hpi' := (ord_eq_one_iff_isUniformizer E pi).1 hpi
  have hdelta' : ord E (delta : E) = (((d : ℤ) - 0 : ℤ) : WithTop ℤ) := by
    simpa using hdelta
  let e : LatticeGradedPiece E (d : ℤ) ≃ ResidueField E :=
    (Equiv.ofBijective (higherGradedDivide E delta (d : ℤ) 0 hdelta')
      (higherGradedDivide_bijective E delta (d : ℤ) 0 hdelta')).trans
      (criticalNormLatticeGradedResidueAddEquiv E pi hpi' 0).toEquiv
  let v (x : ResidueField E) : lattice E (d : ℤ) :=
    ⟨(delta : E) * (teichmuller E x : E), by
      have hh := mul_mem_lattice E ((mem_lattice E).2 hdelta.ge)
        ((mem_lattice_zero_iff E).2 (teichmuller E x).property)
      simpa using hh⟩
  let t (x : ResidueField E) : LatticeGradedPiece E (d : ℤ) :=
    latticeQuotientMk E (by omega) (v x)
  have he (x : ResidueField E) : e (t x) = x := by
    change criticalNormLatticeGradedResidueAddEquiv E pi hpi' 0
      (higherGradedDivide E delta (d : ℤ) 0 hdelta'
        (latticeQuotientMk E (by omega) (v x))) = x
    rw [higherGradedDivide_mk, criticalNormLatticeGradedResidueAddEquiv_mk]
    change reduce E (((delta : E) * (teichmuller E x : E) / (delta : E)) / pi ^ 0) _ = x
    simp only [mul_div_cancel_left₀ _ (Units.ne_zero delta), pow_zero, div_one]
    exact residueMap_teichmuller E x
  have ht : Function.Bijective t := by
    have hte : t = e.symm := by
      funext x
      exact e.injective ((he x).trans (e.apply_symm_apply x).symm)
    rw [hte]
    exact e.symm.bijective
  have hv (x : ResidueField E) :
      higherCriticalFunction E theta psi alpha Z d hm hlarge hZ hstationary (t x) =
        Stationary.normalizedResidualFunction E theta psi alpha Z d hm hlarge delta hdelta x := by
    rw [show t x = latticeQuotientMk E (by omega) (v x) from rfl,
      higherCriticalFunction_mk]
    have hu : (positiveUnitOfLattice E (by omega) (v x) : Eˣ) =
        lamprechtHasseUnit E theta d hm hlarge delta hdelta (teichmuller E x : E)
          ((mem_lattice_zero_iff E).2 (teichmuller E x).property) := by
      apply Units.ext
      rw [coe_positiveUnitOfLattice, lamprechtHasseUnit_coe]
    simp only [Stationary.normalizedCriticalValue, Stationary.normalizedResidualFunction,
      hu, v, mul_assoc]
  rw [higherCriticalSum, Stationary.normalizedResidualFactor,
    ← ht.sum_comp (higherCriticalFunction E theta psi alpha Z d hm hlarge hZ hstationary)]
  congr 1
  exact Finset.sum_congr rfl (fun x _ ↦ hv x)

theorem higherCriticalSum_norm :
    ‖higherCriticalSum E theta psi alpha Z d hm hlarge hZ hstationary‖ = 1 := by
  obtain ⟨x, hx⟩ := exists_ord_eq E (d : ℤ)
  have hx0 : x ≠ 0 := (ord_ne_top_iff E).1 (by rw [hx]; exact WithTop.coe_ne_top)
  rw [higherCriticalSum_eq_residual E theta psi alpha Z d hm hlarge hZ hstationary
    (Units.mk0 x hx0) hx]
  exact higherResidualFactor_norm E theta psi alpha Z d hm hlarge hZ hstationary _ hx

theorem higherCompleteResidual_eq :
    Stationary.completeNormalizedResidualFactor E theta psi alpha Z hlarge =
      higherCriticalSum E theta psi alpha Z d hm hlarge hZ hstationary := by
  unfold Stationary.completeNormalizedResidualFactor
  split_ifs with heven
  · omega
  · have hd : theta.conductor / 2 = d := by omega
    simp only [hd]
    exact (higherCriticalSum_eq_residual E theta psi alpha Z d hm hlarge hZ hstationary _ _).symm

end GradedCriticalFunction

section GradedNorm

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- FML's additive displacement coordinate at any positive depth. -/
def higherUnitGradedEquiv (d : ℕ) (hd : 0 < d) :
    Additive (UnitGradedPiece E d) ≃+ LatticeGradedPiece E (d : ℤ) := by
  cases d with
  | zero => omega
  | succ n => exact positiveUnitGradedAddEquivLattice E n

@[simp]
theorem higherUnitGradedEquiv_mk (d : ℕ) (hd : 0 < d) (u : unitFiltration E d) :
    higherUnitGradedEquiv E d hd (Additive.ofMul (unitGradedMk E d u)) =
      latticeQuotientMk E (show (d : ℤ) ≤ (d : ℤ) + 1 by omega)
        (positiveUnitDisplacement E hd u) := by
  cases d with
  | zero => omega
  | succ n => rfl

@[simp]
theorem higherUnitGradedEquiv_symm_mk (d : ℕ) (hd : 0 < d) (v : lattice E (d : ℤ)) :
    (higherUnitGradedEquiv E d hd).symm (latticeQuotientMk E (by omega) v) =
      Additive.ofMul (unitGradedMk E d (positiveUnitOfLattice E hd v)) := by
  apply (higherUnitGradedEquiv E d hd).injective
  rw [AddEquiv.apply_symm_apply, higherUnitGradedEquiv_mk]
  congr 1
  apply Subtype.ext
  simp

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Algebra F E] [ValuativeExtension F E]
  [Module.Finite F E]

/-- The actual norm on positive terminal lattice classes, obtained from
FML's unit-quotient norm by its canonical displacement coordinates. -/
def higherGradedNorm (r n : ℕ) (hr : 0 < r) (hn : 0 < n)
    (hnum : NormMapsUnitFiltration F E r n)
    (hden : NormMapsUnitFiltration F E (r + 1) (n + 1)) :
    LatticeGradedPiece E (r : ℤ) → LatticeGradedPiece F (n : ℤ) :=
  fun x ↦ higherUnitGradedEquiv F n hn (Additive.ofMul
    (normUnitFiltrationQuotient F E (Nat.le_succ r) (Nat.le_succ n) hnum hden
      (Additive.toMul ((higherUnitGradedEquiv E r hr).symm x))))

@[simp]
theorem higherGradedNorm_mk (r n : ℕ) (hr : 0 < r) (hn : 0 < n)
    (hnum : NormMapsUnitFiltration F E r n)
    (hden : NormMapsUnitFiltration F E (r + 1) (n + 1))
    (v : lattice E (r : ℤ)) :
    higherGradedNorm E F r n hr hn hnum hden (latticeQuotientMk E (by omega) v) =
      latticeQuotientMk F (show (n : ℤ) ≤ (n : ℤ) + 1 by omega)
        (positiveUnitDisplacement F hn
          (normBelowBreakUnitFiltrationHom F E r n hnum (positiveUnitOfLattice E hr v))) := by
  rw [higherGradedNorm, higherUnitGradedEquiv_symm_mk]
  change higherUnitGradedEquiv F n hn (Additive.ofMul
    (normUnitFiltrationQuotient F E (Nat.le_succ r) (Nat.le_succ n) hnum hden
      (unitFiltrationQuotientMk E (Nat.le_succ r) (positiveUnitOfLattice E hr v)))) = _
  rw [normUnitFiltrationQuotient_mk]
  exact higherUnitGradedEquiv_mk F n hn _

theorem higherGradedNorm_bijective (r n : ℕ) (hr : 0 < r) (hn : 0 < n)
    (hnum : NormMapsUnitFiltration F E r n)
    (hden : NormMapsUnitFiltration F E (r + 1) (n + 1))
    (hbij : Function.Bijective
      (normUnitFiltrationQuotient F E (Nat.le_succ r) (Nat.le_succ n) hnum hden)) :
    Function.Bijective (higherGradedNorm E F r n hr hn hnum hden) :=
  (higherUnitGradedEquiv F n hn).bijective.comp
    (Additive.ofMul.bijective.comp (hbij.comp
      (Additive.toMul.bijective.comp (higherUnitGradedEquiv E r hr).symm.bijective)))

theorem higherGradedNorm_add (r n : ℕ) (hr : 0 < r) (hn : 0 < n)
    (hnum : NormMapsUnitFiltration F E r n)
    (hden : NormMapsUnitFiltration F E (r + 1) (n + 1))
    (x y : LatticeGradedPiece E (r : ℤ)) :
    higherGradedNorm E F r n hr hn hnum hden (x + y) =
      higherGradedNorm E F r n hr hn hnum hden x +
        higherGradedNorm E F r n hr hn hnum hden y := by
  simp only [higherGradedNorm, map_add, toMul_add, map_mul, ofMul_mul]

end GradedNorm

section ResidueBijections

variable (F L K : Type*) [Field F] [Field L] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F L] [ValuativeExtension F L] [Module.Finite F L]
  [Algebra L K] [ValuativeExtension L K] [Module.Finite L K]
  [PrimeCyclicExtension F L] [PrimeCyclicExtension L K]

/-- Construct both actual odd residue bijections of `D:MX:higher`.

The upper map is the above-break norm of `1 + V/C`. The lower map is
the below-break norm of `1 + Tr(V)/hy`, with `hy` the original trace.
The intermediate trace is FML's exact quadratic graded-trace isomorphism.
The representative equations identify the full norm increments, including
the terms which disappear only after passage to the terminal quotient. -/
theorem higherResidueBijections
    (e a b h : ℕ) (ha : 1 ≤ a) (hae : a ≤ e) (hah : a ≤ h)
    (hb : b = 2 * e - 2 * a + 1)
    (hdeg : Module.finrank L K = 2)
    (hres : residueDegree L K = 1) (hresF : residueDegree F L = 1)
    (ht : PrimeCyclicExtension.IsLowerBreak L K (2 * a - 1))
    (htF : PrimeCyclicExtension.IsLowerBreak F L (2 * e))
    (C : Kˣ) (hC : ord K (C : K) = ((-2 * (h : ℤ) : ℤ) : WithTop ℤ))
    (hy : Lˣ) (hhy : ord L (hy : L) = 0) :
    ∃ (p : LatticeGradedPiece K (b : ℤ) → LatticeGradedPiece L ((e + h : ℕ) : ℤ))
      (q : LatticeGradedPiece K (b : ℤ) → LatticeGradedPiece F (e : ℤ)),
      Function.Bijective p ∧ Function.Bijective q ∧
      (∀ x y, p (x + y) = p x + p y) ∧ (∀ x y, q (x + y) = q x + q y) ∧
      ∀ V : lattice K (b : ℤ),
        ∃ (v : lattice L ((e + h : ℕ) : ℤ)) (w : lattice F (e : ℤ)),
          (v : L) = norm L K (1 + (V : K) / (C : K)) - 1 ∧
          (w : F) = norm F L (1 + trace L K (V : K) / (hy : L)) - 1 ∧
          p (latticeQuotientMk K (by omega) V) = latticeQuotientMk L (by omega) v ∧
          q (latticeQuotientMk K (by omega) V) = latticeQuotientMk F (by omega) w := by
  obtain ⟨piK, hpiK, hgenK⟩ := monogenicUniformizer L K hres
  obtain ⟨piL, hpiL, hgenL⟩ := monogenicUniformizer F L hresF
  have he : 0 < e := by omega
  have hpos : 0 < b + 2 * h := by omega
  have hd : 0 < e + h := by omega
  have hhigh : 2 * a - 1 < e + h := by omega
  have hs : herbrandPsiNat (2 * a - 1) (Module.finrank L K) (e + h) = b + 2 * h := by
    rw [hdeg, herbrandPsiNat_of_break_le _ _ hhigh.le]
    omega
  have hnum : NormMapsUnitFiltration L K (b + 2 * h) (e + h) := by
    simpa only [hs] using normMapsUnitFiltration_herbrand L K ht hres piK hpiK hgenK (e + h)
  have hden : NormMapsUnitFiltration L K (b + 2 * h + 1) (e + h + 1) := by
    simpa only [hs] using normMapsUnitFiltration_herbrand_succ L K ht hres piK hpiK hgenK (e + h)
  have hnormbij : Function.Bijective
      (normUnitFiltrationQuotient L K (Nat.le_succ (b + 2 * h))
        (Nat.le_succ (e + h)) hnum hden) := by
    have transfer (r : ℕ)
        (hsr : herbrandPsiNat (2 * a - 1) (Module.finrank L K) (e + h) = r)
        (hnr : NormMapsUnitFiltration L K r (e + h))
        (hdr : NormMapsUnitFiltration L K (r + 1) (e + h + 1)) :
        Function.Bijective (normUnitFiltrationQuotient L K (Nat.le_succ r)
          (Nat.le_succ (e + h)) hnr hdr) := by
      subst r
      exact cyclicPrimeGradedNorm_bijective_aboveBreak L K ht hres piK hpiK hgenK hhigh
    exact transfer _ hs hnum hden
  have hnumF := normMapsUnitFiltration_belowBreak F L htF (show e ≤ 2 * e by omega)
    hresF piL hpiL hgenL
  have hdenF := normMapsUnitFiltration_belowBreak F L htF (show e + 1 ≤ 2 * e by omega)
    hresF piL hpiL hgenL
  have hnormbijF : Function.Bijective
      (normUnitFiltrationQuotient F L (Nat.le_succ e) (Nat.le_succ e) hnumF hdenF) :=
    gradedNorm_bijective_belowBreak F L htF (by omega) hresF piL hpiL hgenL
  have hram : ramificationIndex L K = 2 := by
    have hh := finrank_eq_ramificationIndex_mul_residueDegree L K
    rw [hdeg, hres, mul_one] at hh
    exact hh.symm
  have hodd : (b : ℤ) + ((2 * a - 1 + 1 : ℕ) : ℤ) = 2 * (e : ℤ) + 1 := by omega
  let T := wildQuadraticGradedTraceEquiv L K piK hpiK hgenK ht (by omega)
    hram hdeg (show 0 ≤ (b : ℤ) by omega) hodd
  have hD : differentExponent L K = 2 * a - 1 + 1 :=
    differentExponent_wildQuadratic_eq L K ht hdeg piK hpiK hgenK
  have htrace (V : lattice K (b : ℤ)) : trace L K (V : K) ∈ lattice L (e : ℤ) := by
    have hh := trace_mem_lattice_floor L K piK hpiK hgenK (b : ℤ) V.property
    rw [hram, hD] at hh
    convert hh using 1
    congr 1
    omega
  have hC' : ord K (C : K) =
      (((b : ℤ) - ((b + 2 * h : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
    convert hC using 1
    congr 1
    omega
  have hhy' : ord L (hy : L) = (((e : ℤ) - (e : ℤ) : ℤ) : WithTop ℤ) := by
    simpa using hhy
  let divC := higherGradedDivide K C (b : ℤ) ((b + 2 * h : ℕ) : ℤ) hC'
  let divH := higherGradedDivide L hy (e : ℤ) (e : ℤ) hhy'
  let N := higherGradedNorm K L (b + 2 * h) (e + h) hpos hd hnum hden
  let n := higherGradedNorm L F e e he he hnumF hdenF
  refine ⟨N ∘ divC, n ∘ divH ∘ T, ?_, ?_, ?_, ?_, ?_⟩
  · exact (higherGradedNorm_bijective K L _ _ hpos hd hnum hden hnormbij).comp
      (higherGradedDivide_bijective K C _ _ hC')
  · exact (higherGradedNorm_bijective L F e e he he hnumF hdenF hnormbijF).comp
      ((higherGradedDivide_bijective L hy _ _ hhy').comp T.bijective)
  · intro x y
    simp only [Function.comp_apply, divC, N, higherGradedDivide_add, higherGradedNorm_add]
  · intro x y
    simp only [Function.comp_apply, divH, n, map_add, higherGradedDivide_add, higherGradedNorm_add]
  · intro V
    let z : lattice K ((b + 2 * h : ℕ) : ℤ) := ⟨(V : K) / (C : K),
      (div_mem_lattice_iff K _ _ ((b : ℤ) - ((b + 2 * h : ℕ) : ℤ))
        ((b + 2 * h : ℕ) : ℤ) hC').2 (by simp)⟩
    let t : lattice L (e : ℤ) := ⟨trace L K (V : K), htrace V⟩
    let u : lattice L (e : ℤ) := ⟨(t : L) / (hy : L),
      (div_mem_lattice_iff L _ _ ((e : ℤ) - (e : ℤ)) (e : ℤ) hhy').2
        (by simp)⟩
    let v := positiveUnitDisplacement L hd
      (normBelowBreakUnitFiltrationHom L K (b + 2 * h) (e + h) hnum
        (positiveUnitOfLattice K hpos z))
    let w := positiveUnitDisplacement F he
      (normBelowBreakUnitFiltrationHom F L e e hnumF (positiveUnitOfLattice L he u))
    refine ⟨v, w, ?_, ?_, ?_, ?_⟩
    · simp only [v, coe_positiveUnitDisplacement, coe_normBelowBreakUnitFiltrationHom,
        coe_normUnits, coe_positiveUnitOfLattice, z]
    · simp only [w, coe_positiveUnitDisplacement, coe_normBelowBreakUnitFiltrationHom,
        coe_normUnits, coe_positiveUnitOfLattice, u, t]
    · simp only [Function.comp_apply, N, divC, higherGradedDivide_mk, higherGradedNorm_mk]
      rfl
    · have hT : T (latticeQuotientMk K (by omega) V) =
          latticeQuotientMk L (by omega) t := rfl
      simp only [Function.comp_apply, hT, divH, n, higherGradedDivide_mk, higherGradedNorm_mk]
      rfl

end ResidueBijections

/-- The first upper norm sends the entire perturbation ideal into its even
stationary ideal, on both sides of the upper ramification break. -/
theorem higherFirstNormMaps
    (L K : Type*) [Field L] [Field K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra L K] [ValuativeExtension L K] [Module.Finite L K]
    [PrimeCyclicExtension L K]
    (e a b h : ℕ) (ha : 1 ≤ a) (hae : a ≤ e) (hah : a ≤ h)
    (hb : b = 2 * e - 2 * a + 1)
    (hdeg : Module.finrank L K = 2) (hres : residueDegree L K = 1)
    (ht : PrimeCyclicExtension.IsLowerBreak L K (4 * e - 2 * a + 1)) :
    NormMapsUnitFiltration L K (b + 2 * h) (2 * e + 1 + h - a) := by
  obtain ⟨piK, hpiK, hgenK⟩ := monogenicUniformizer L K hres
  have hh := normMapsUnitFiltration_herbrand L K ht hres piK hpiK hgenK
    (2 * e + 1 + h - a)
  have hdepth : herbrandPsiNat (4 * e - 2 * a + 1) (Module.finrank L K)
      (2 * e + 1 + h - a) ≤ b + 2 * h := by
    rw [hdeg]
    by_cases hr : 2 * e + 1 + h - a ≤ 4 * e - 2 * a + 1
    · rw [herbrandPsiNat_of_le_break _ _ hr]
      omega
    · rw [herbrandPsiNat_of_break_le _ _ (by omega)]
      omega
  intro u hu
  exact hh u (unitFiltration_antitone K hdepth hu)

section FullFactor

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [Module.Finite F K] [IsGalois F K] [IsKleinFour Gal(K/F)]
  (L : IntermediateField F K)
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension F L] [ValuativeExtension L K]
  [Algebra.IsQuadraticExtension F L] [Algebra.IsQuadraticExtension L K]

/-- The full factor in `D:MX:higher-full`. The lower coefficient remains
the norm of the original trace at `Y`. The correction is the actual difference
of the trace norms, so this formula makes no depth assumption on it. -/
theorem higherFullFactor
    (theta : LocalQuasiCharData L) (omega : LocalQuasiCharData F)
    (omegaNorm : NormCharacter F L) (homegaChar : omega.character = omegaNorm.1)
    (Theta : ContinuousQuasiChar K) (hc : normQuasiChar L K theta.character = Theta)
    (psiF : LocalAddCharData F) (psiL : LocalAddCharData L)
    (hpsi : psiL.character = psiF.character.compTrace)
    (alpha : Fˣ) (C : Kˣ) (Y : K) (hy : trace L K Y ≠ 0)
    (htheta : 1 < theta.conductor) (homega : 1 < omega.conductor)
    (hZ : Stationary.IsOrdinaryStationaryCoefficient L theta
      (scaleAddCharData L psiL (Units.map (algebraMap F L).toMonoidHom alpha))
      (normUnits L K C) htheta)
    (hW : Stationary.IsOrdinaryStationaryCoefficient F omega
      (scaleAddCharData F psiF alpha)
      (normUnits F L (Units.mk0 (trace L K Y) hy)) homega) :
    LanglandsFirstMainLemma.localConstant L theta.character psiL.character *
        LanglandsFirstMainLemma.localConstant F omega.character psiF.character =
      ((Characters.restrictQuasiChar F L theta.character * omega.character)
        (-alpha⁻¹) : ℂ) * (Theta C : ℂ)⁻¹ *
        ((scaleAddCharData F psiF alpha).character
          (-elementarySymmetric F K 2 (C : K) +
            (norm F L (trace L K (C : K)) - norm F L (trace L K Y))) : ℂ) *
        (Stationary.completeNormalizedResidualFactor L theta psiL
          (Units.map (algebraMap F L).toMonoidHom alpha) (normUnits L K C) htheta *
        Stationary.completeNormalizedResidualFactor F omega psiF alpha
          (normUnits F L (Units.mk0 (trace L K Y) hy)) homega) := by
  let alphaL := Units.map (algebraMap F L).toMonoidHom alpha
  let Z := normUnits L K C
  let W := normUnits F L (Units.mk0 (trace L K Y) hy)
  have hthetaZ : theta.character Z = Theta C := DFunLike.congr_fun hc C
  have homegaW : omega.character W = 1 := by
    rw [homegaChar]
    exact omegaNorm.eq_one_on_normRange F L W ⟨Units.mk0 (trace L K Y) hy, rfl⟩
  have hunitL : (-alphaL * Z)⁻¹ =
      Units.map (algebraMap F L).toMonoidHom (-alpha⁻¹) * Z⁻¹ := by
    simp [alphaL, mul_comm]
  have hunitF : (-alpha * W)⁻¹ = -alpha⁻¹ * W⁻¹ := by simp [mul_comm]
  have hmult :
      (theta.character ((-alphaL * Z)⁻¹) : ℂ) *
          (omega.character ((-alpha * W)⁻¹) : ℂ) =
        ((Characters.restrictQuasiChar F L theta.character * omega.character)
          (-alpha⁻¹) : ℂ) * (Theta C : ℂ)⁻¹ := by
    change _ = (theta.character (Units.map (algebraMap F L).toMonoidHom (-alpha⁻¹)) *
      omega.character (-alpha⁻¹) : ℂˣ) * (Theta C : ℂ)⁻¹
    rw [hunitL, hunitF, map_mul, map_mul, map_inv, map_inv, hthetaZ, homegaW]
    push_cast
    ring
  have hadd :
      ((scaleAddCharData L psiL alphaL).character (-(Z : L)) : ℂ) *
          ((scaleAddCharData F psiF alpha).character (-(W : F)) : ℂ) =
        ((scaleAddCharData F psiF alpha).character
          (-elementarySymmetric F K 2 (C : K) +
            (norm F L (trace L K (C : K)) - norm F L (trace L K Y))) : ℂ) := by
    have htraceAlpha : trace F L ((alphaL : L) * -(Z : L)) =
        (alpha : F) * -trace F L (Z : L) := by
      change trace F L (algebraMap F L (alpha : F) * -(Z : L)) = _
      rw [← Algebra.smul_def, map_smul, map_neg, smul_eq_mul]
    rw [scaleAddCharData_character_apply, hpsi, ContinuousAddChar.compTrace_apply,
      htraceAlpha, ← scaleAddCharData_character_apply,
      ← Units.val_mul, ← ContinuousAddChar.map_add_eq_mul]
    congr 2
    rw [Algebra.biquadraticE2 F K L]
    change -trace F L (norm L K (C : K)) + -norm F L (trace L K Y) = _
    ring
  rw [Stationary.completeNormalizedFactor L theta psiL _ _ htheta hZ,
    Stationary.completeNormalizedFactor F omega psiF _ _ homega hW]
  calc
    _ = ((theta.character ((-alphaL * Z)⁻¹) : ℂ) *
          (omega.character ((-alpha * W)⁻¹) : ℂ)) *
        (((scaleAddCharData L psiL alphaL).character (-(Z : L)) : ℂ) *
          ((scaleAddCharData F psiF alpha).character (-(W : F)) : ℂ)) *
        (Stationary.completeNormalizedResidualFactor L theta psiL alphaL Z htheta *
          Stationary.completeNormalizedResidualFactor F omega psiF alpha W homega) := by ring
    _ = _ := by rw [hmult, hadd]

end FullFactor

section ActualResidualProduct

variable {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Algebra F K] [ValuativeExtension F K]
  [Module.Finite F K] [IsGalois F K]
  {pi : ringOfIntegers F} {e a b : ℕ} {u0 w0 : (ringOfIntegers F)ˣ} {s R0 : K}

local instance (L : IntermediateField F K) : ValuativeRel L :=
  Basic.intermediateFieldValuativeRel L
local instance (L : IntermediateField F K) : TopologicalSpace L :=
  Basic.intermediateFieldTopology L
local instance (L : IntermediateField F K) : IsNonarchimedeanLocalField L :=
  Basic.intermediateField_localField L
local instance (L : IntermediateField F K) : ValuativeExtension F L :=
  Basic.intermediateField_lowerValuativeExtension L
local instance (L : IntermediateField F K) : ValuativeExtension L K :=
  Basic.intermediateField_upperValuativeExtension L

open private higher_residue_degrees from LanglandsSecondMainLemma.Dyadic.Maximal.HigherCoefficients

private theorem higher_scaled_trace (L : IntermediateField F K)
    (psiF : LocalAddCharData F) (psiL : LocalAddCharData L)
    (hpsi : psiL.character = psiF.character.compTrace) (alpha : Fˣ) :
    (scaleAddCharData L psiL (Units.map (algebraMap F L).toMonoidHom alpha)).character =
      tracePullbackAddChar F L (scaleAddCharData F psiF alpha).character := by
  ext x
  simp only [scaleAddCharData_character_apply, hpsi, ContinuousAddChar.compTrace_apply,
    tracePullbackAddChar_apply]
  congr 2
  change trace F L (algebraMap F L (alpha : F) * x) = (alpha : F) * trace F L x
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-- The complete odd residual product is one for the constructed maximal-case
origins. Both bijections and the reciprocal pointwise identity are proved here;
the four stationary inputs are the whole-ideal data produced by
`higherCoefficients` and the preserved lower-character formulas. -/
theorem higherOddResidualProduct
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (hres : residueDegree F K = 1)
    (h : ℕ) (ha : 1 ≤ a) (hae : a ≤ e) (hah : a ≤ h)
    (hb : b = 2 * e - 2 * a + 1)
    (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)
    (ht₁ : actualLowerBreak hG D.firstField O.first_degree (2 * a - 1))
    (ht₂ : actualLowerBreak hG D.secondField O.second_degree (2 * e))
    (htK₁ : actualUpperBreak hG D.firstField O.first_degree (4 * e - 2 * a + 1))
    (htK₂ : actualUpperBreak hG D.secondField O.second_degree (2 * a - 1))
    (g1 : Gal(K/D.firstField)) (g2 : Gal(K/D.secondField)) (q3 : Gal(D.thirdField/F))
    (X : D.thirdField) (CE : CommonErrorData D g1 g2 q3 X (h : ℤ))
    (C : Kˣ) (hC : (C : K) = D.adjustedOrigin X)
    (hCord : ord K (C : K) = ((-2 * (h : ℤ) : ℤ) : WithTop ℤ))
    (theta₁ : LocalQuasiCharData D.firstField) (theta₂ : LocalQuasiCharData D.secondField)
    (omega₁ omega₂ : LocalQuasiCharData F)
    (tau₁ : NormCharacter F D.firstField) (tau₂ : NormCharacter F D.secondField)
    (hw₁ : omega₁.character = tau₁.1) (hw₂ : omega₂.character = tau₂.1)
    (Theta : ContinuousQuasiChar K)
    (hc₁ : normQuasiChar D.firstField K theta₁.character = Theta)
    (hc₂ : normQuasiChar D.secondField K theta₂.character = Theta)
    (psiF : LocalAddCharData F) (psi₁ : LocalAddCharData D.firstField)
    (psi₂ : LocalAddCharData D.secondField)
    (hpsi₁ : psi₁.character = psiF.character.compTrace)
    (hpsi₂ : psi₂.character = psiF.character.compTrace) (alpha : Fˣ)
    (hm₁ : theta₁.conductor = 2 * (2 * e + 1 + h - a))
    (hm₂ : theta₂.conductor = 2 * (e + h) + 1)
    (hmw₁ : omega₁.conductor = 2 * a) (hmw₂ : omega₂.conductor = 2 * e + 1)
    (hZ₁ : Stationary.IsOrdinaryStationaryCoefficient D.firstField theta₁
      (scaleAddCharData D.firstField psi₁ (Units.map (algebraMap F D.firstField).toMonoidHom alpha))
      (normUnits D.firstField K C) (by omega))
    (hZ₂ : Stationary.IsOrdinaryStationaryCoefficient D.secondField theta₂
      (scaleAddCharData D.secondField psi₂ (Units.map (algebraMap F D.secondField).toMonoidHom alpha))
      (normUnits D.secondField K C) (by omega))
    (hW₁ : Stationary.IsOrdinaryStationaryCoefficient F omega₁ (scaleAddCharData F psiF alpha)
      (normUnits F D.firstField (Units.mk0 D.h1 O.h1_ne_zero)) (by omega))
    (hW₂ : Stationary.IsOrdinaryStationaryCoefficient F omega₂ (scaleAddCharData F psiF alpha)
      (normUnits F D.secondField (Units.mk0 D.h2 O.h2_ne_zero)) (by omega)) :
    Stationary.completeNormalizedResidualFactor D.secondField theta₂ psi₂
        (Units.map (algebraMap F D.secondField).toMonoidHom alpha) (normUnits D.secondField K C)
        (by omega) *
      Stationary.completeNormalizedResidualFactor F omega₂ psiF alpha
        (normUnits F D.secondField (Units.mk0 D.h2 O.h2_ne_zero)) (by omega) = 1 := by
  have E₁ := Basic.intermediateField_tower_compatible Nat.prime_two hG D.firstField O.first_degree
  have E₂ := Basic.intermediateField_tower_compatible Nat.prime_two hG D.secondField O.second_degree
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F D.firstField E₁.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F D.secondField E₂.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension D.firstField K E₁.2.2.2.2.2.2.2.2.2.2.2.2
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension D.secondField K E₂.2.2.2.2.2.2.2.2.2.2.2.2
  have hr₁ := higher_residue_degrees D.firstField hres
  have hr₂ := higher_residue_degrees D.secondField hres
  have ht₁' : PrimeCyclicExtension.IsLowerBreak F D.firstField (2 * a - 1) := by
    simpa [actualLowerBreak] using ht₁
  have ht₂' : PrimeCyclicExtension.IsLowerBreak F D.secondField (2 * e) := by
    simpa [actualLowerBreak] using ht₂
  have htK₁' : PrimeCyclicExtension.IsLowerBreak D.firstField K (4 * e - 2 * a + 1) := by
    simpa [actualUpperBreak] using htK₁
  have htK₂' : PrimeCyclicExtension.IsLowerBreak D.secondField K (2 * a - 1) := by
    simpa [actualUpperBreak] using htK₂
  let alpha₁ := Units.map (algebraMap F D.firstField).toMonoidHom alpha
  let alpha₂ := Units.map (algebraMap F D.secondField).toMonoidHom alpha
  let W₁ := normUnits F D.firstField (Units.mk0 D.h1 O.h1_ne_zero)
  let W₂ := normUnits F D.secondField (Units.mk0 D.h2 O.h2_ne_zero)
  have hstat₁ : Stationary.IsNormalizedStationaryCoefficientAtDepth D.firstField theta₁
      (scaleAddCharData D.firstField psi₁ alpha₁) (normUnits D.firstField K C)
      (2 * e + 1 + h - a) (by omega) := by
    convert hZ₁.2 using 1
    omega
  have hstat₂ : Stationary.IsNormalizedStationaryCoefficientAtDepth D.secondField theta₂
      (scaleAddCharData D.secondField psi₂ alpha₂) (normUnits D.secondField K C)
      (e + h + 1) (by omega) := by
    convert hZ₂.2 using 1
    omega
  have hstatw₁ : Stationary.IsNormalizedStationaryCoefficientAtDepth F omega₁
      (scaleAddCharData F psiF alpha) W₁ a (by omega) := by
    convert hW₁.2 using 1
    omega
  have hstatw₂ : Stationary.IsNormalizedStationaryCoefficientAtDepth F omega₂
      (scaleAddCharData F psiF alpha) W₂ (e + 1) (by omega) := by
    convert hW₂.2 using 1
    omega
  obtain ⟨p, q, hp, hq, _hpadd, _hqadd, hcoords⟩ := higherResidueBijections F D.secondField K
    e a b h ha hae hah hb E₂.2.2.2.2.2.2.2.2.2.2.1 hr₂.2 hr₂.1 htK₂' ht₂'
    C hCord (Units.mk0 D.h2 O.h2_ne_zero) O.h2_order
  let f := higherCriticalFunction D.secondField theta₂ psi₂ alpha₂ (normUnits D.secondField K C)
    (e + h) hm₂ (by omega) hZ₂.1 hstat₂
  let g := higherCriticalFunction F omega₂ psiF alpha W₂ e hmw₂ (by omega) hW₂.1 hstatw₂
  have hpoint (x : LatticeGradedPiece K (b : ℤ)) : f (p x) * g (q x) = 1 := by
    obtain ⟨V, rfl⟩ := latticeQuotientMk_surjective K (show (b : ℤ) ≤ (b : ℤ) + 1 by omega) x
    obtain ⟨v₂, w₂, hv₂, hw₂', hpV, hqV⟩ := hcoords V
    obtain ⟨C', hC', hunit⟩ := twoOrigin_upper_perturbation C (V : K) h (by omega) hCord V.property
    obtain ⟨htr₁, _htr₂, _hyord₁, _hyord₂, hy₁', hy₂'⟩ :=
      twoOrigin_lower_perturbation hG D O ha hae hb hr₁.2 hr₂.2 htK₁ htK₂ (V : K) V.property
    have hu₁ := higherFirstNormMaps D.firstField K e a b h ha hae hah hb
      E₁.2.2.2.2.2.2.2.2.2.2.1 hr₁.2 htK₁' (C' / C) hunit
    let v₁ := positiveUnitDisplacement D.firstField (show 0 < 2 * e + 1 + h - a by omega)
      ⟨normUnits D.firstField K (C' / C), hu₁⟩
    have htdiv : trace D.firstField K (V : K) / D.h1 ∈ lattice D.firstField (a : ℤ) := by
      apply (div_mem_lattice_iff D.firstField D.h1 _ (b : ℤ) (a : ℤ) O.h1_order).2
      exact lattice_antitone D.firstField (by omega) htr₁
    let t₁ : lattice D.firstField (a : ℤ) := ⟨_, htdiv⟩
    have hut₁ : Units.mk0 (trace D.firstField K (D.origin + (V : K))) hy₁' /
        Units.mk0 D.h1 O.h1_ne_zero = positiveUnitOfLattice D.firstField (by omega) t₁ := by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_mk0, map_add, coe_positiveUnitOfLattice]
      change (D.h1 + trace D.firstField K (V : K)) / D.h1 = 1 + _
      dsimp only [t₁]
      field_simp [O.h1_ne_zero]
    obtain ⟨pi₁, hpi₁, hgen₁⟩ := monogenicUniformizer F D.firstField hr₁.1
    have hwunit := normMapsUnitFiltration_belowBreak F D.firstField ht₁'
      (show a ≤ 2 * a - 1 by omega) hr₁.1 pi₁ hpi₁ hgen₁
      (positiveUnitOfLattice D.firstField (by omega) t₁) (positiveUnitOfLattice D.firstField (by omega) t₁).property
    let w₁ := positiveUnitDisplacement F (show 0 < a by omega)
      ⟨normUnits F D.firstField (positiveUnitOfLattice D.firstField (by omega) t₁), hwunit⟩
    have hz₁ : 1 + (v₁ : D.firstField) =
        ((normUnits D.firstField K C' / normUnits D.firstField K C : D.firstFieldˣ) : D.firstField) := by
      simp [v₁, map_div]
    have hw₁' : 1 + (w₁ : F) =
        ((normUnits F D.firstField (Units.mk0 (trace D.firstField K (D.origin + (V : K))) hy₁') /
          W₁ : Fˣ) : F) := by
      simp only [w₁, coe_positiveUnitDisplacement, add_sub_cancel, W₁, ← map_div, hut₁]
    have hP₁ := twoOriginFunctionProduct_eq_criticalValues D.firstField theta₁ omega₁
      (scaleAddCharData F psiF alpha) (scaleAddCharData D.firstField psi₁ alpha₁)
      (higher_scaled_trace D.firstField psiF psi₁ hpsi₁ alpha) C C'
      D.origin (D.origin + (V : K)) O.h1_ne_zero hy₁' (2 * e + 1 + h - a) a
      (by omega) (by omega) v₁ w₁ hz₁ hw₁'
    change (twoOriginFunctionProduct D.firstField theta₁.character omega₁.character
      (scaleAddCharData F psiF alpha).character C C' D.origin (D.origin + (V : K))
      O.h1_ne_zero hy₁' : ℂ) =
      Stationary.normalizedCriticalValue D.firstField theta₁
        (scaleAddCharData D.firstField psi₁ alpha₁) (normUnits D.firstField K C)
        (2 * e + 1 + h - a) (by omega) v₁ *
      Stationary.normalizedCriticalValue F omega₁ (scaleAddCharData F psiF alpha) W₁ a
        (by omega) w₁ at hP₁
    rw [Stationary.normalizedCriticalValue_even D.firstField theta₁ _ _ _ hm₁
      (by omega) hstat₁, Stationary.normalizedCriticalValue_even F omega₁ _ _ _ hmw₁
      (by omega) hstatw₁, mul_one] at hP₁
    have hpEqual := (dyadicMaximal_twoOrigin_function hG D O g1 g2 q3 X (h : ℤ) CE
      theta₁.character theta₂.character tau₁ tau₂ Theta hc₁ hc₂
      (scaleAddCharData F psiF alpha).character C C' (V : K) hC hC' hy₁' hy₂').2.2
    have hnorm : ((C' / C : Kˣ) : K) = 1 + (V : K) / (C : K) := by
      rw [Units.val_div_eq_div_val, hC']
      field_simp
    have hz₂ : 1 + (v₂ : D.secondField) =
        ((normUnits D.secondField K C' / normUnits D.secondField K C : D.secondFieldˣ) : D.secondField) := by
      rw [hv₂, add_sub_cancel, ← map_div, coe_normUnits, hnorm]
    have hyquot : ((Units.mk0 (trace D.secondField K (D.origin + (V : K))) hy₂' /
        Units.mk0 D.h2 O.h2_ne_zero : D.secondFieldˣ) : D.secondField) =
        1 + trace D.secondField K (V : K) / D.h2 := by
      simp only [Units.val_div_eq_div_val, Units.val_mk0, map_add]
      change (D.h2 + trace D.secondField K (V : K)) / D.h2 = _
      field_simp [O.h2_ne_zero]
    have hw₂'' : 1 + (w₂ : F) =
        ((normUnits F D.secondField (Units.mk0 (trace D.secondField K (D.origin + (V : K))) hy₂') /
          W₂ : Fˣ) : F) := by
      rw [hw₂', add_sub_cancel]
      change _ = ((normUnits F D.secondField _ / normUnits F D.secondField _ : Fˣ) : F)
      rw [← map_div, coe_normUnits, hyquot]
      rfl
    have hP₂ := twoOriginFunctionProduct_eq_criticalValues D.secondField theta₂ omega₂
      (scaleAddCharData F psiF alpha) (scaleAddCharData D.secondField psi₂ alpha₂)
      (higher_scaled_trace D.secondField psiF psi₂ hpsi₂ alpha) C C'
      D.origin (D.origin + (V : K)) O.h2_ne_zero hy₂' (e + h) e
      (by omega) (by omega) v₂ w₂ hz₂ hw₂''
    rw [hw₁] at hP₁
    rw [hw₂] at hP₂
    rw [hpV, hqV]
    exact hP₂.symm.trans ((congrArg (Units.val : ℂˣ → ℂ) hpEqual).symm.trans hP₁)
  letI := latticeQuotientFintype K (show (b : ℤ) ≤ (b : ℤ) + 1 by omega)
  letI := latticeQuotientFintype D.secondField
    (show ((e + h : ℕ) : ℤ) ≤ ((e + h : ℕ) : ℤ) + 1 by omega)
  letI := latticeQuotientFintype F (show (e : ℤ) ≤ (e : ℤ) + 1 by omega)
  have hcard : residueCard D.secondField = residueCard F :=
    residueCard_eq_of_residueDegree_eq_one F D.secondField hr₂.1
  have hfinite := higher_reciprocal_normalized_sums f g p q hp hq hpoint
    (higherCriticalFunction_norm F omega₂ psiF alpha W₂ e hmw₂ (by omega) hW₂.1 hstatw₂)
    (Real.sqrt (residueCard F : ℝ))⁻¹ (by
      simpa only [higherCriticalSum, g, Complex.ofReal_inv] using
        higherCriticalSum_norm F omega₂ psiF alpha W₂ e hmw₂ (by omega) hW₂.1 hstatw₂)
  rw [higherCompleteResidual_eq D.secondField theta₂ psi₂ alpha₂ _ (e + h) hm₂
    (by omega) hZ₂.1 hstat₂, higherCompleteResidual_eq F omega₂ psiF alpha W₂ e hmw₂
    (by omega) hW₂.1 hstatw₂]
  simpa only [higherCriticalSum, hcard, Complex.ofReal_inv] using hfinite

private theorem higherOrdinaryFromChart
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (theta : LocalQuasiCharData E) (Psi : LocalAddCharData E)
    (Z : Eˣ) (r : ℕ) (hr : 0 < r) (hlarge : 1 < theta.conductor)
    (hhalf : theta.conductor / 2 + theta.conductor % 2 = r)
    (hord : ord E (Z : E) = ((-Psi.conductor - (theta.conductor : ℤ) : ℤ) : WithTop ℤ))
    (hchart : ∀ (z : E) (hz : z ∈ lattice E (r : ℤ)),
      theta.character (lowerOneSubUnit E r hr z hz) = Psi.character ((Z : E) * z)) :
    Stationary.IsOrdinaryStationaryCoefficient E theta Psi Z hlarge := by
  refine ⟨hord, ?_⟩
  suffices hs : Stationary.IsNormalizedStationaryCoefficientAtDepth E theta Psi Z r hr by
    simpa only [hhalf] using hs
  intro z
  have hu : (positiveUnitOfLattice E hr (-z) : Eˣ) = lowerOneSubUnit E r hr z z.property := by
    apply Units.ext
    simp only [coe_positiveUnitOfLattice, Submodule.coe_neg, coe_lowerOneSubUnit, sub_eq_add_neg]
  rw [hu]
  exact hchart z z.property

open private quadraticNormRanges_ne from LanglandsSecondMainLemma.Dyadic.Maximal.Twist

set_option maxHeartbeats 1600000 in
/-- **Exact higher comparison (`D:MX:higher`).**

For every higher continuous base twist, the two complete canonical local
constant expressions agree. The cores and their full lower/core formulas
are the data constructed in `models`, `lowerCharacters`, and `normalization`.
`higherCoefficients` constructs the normalization change and the exact
third-field norm internally. The common-error constructor then supplies the
two genuine origins. No residual identity, residue bijection, stationary
coefficient for the twisted characters, or phase cancellation is assumed.

There is no upper bound on `h`, and no unitarity restriction on any
quasi-character. The nontrivial lower quadratic characters are identified
with the complete lower norm-character products in the proof.
-/
theorem higherComparison
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (hres : residueDegree F K = 1)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (ha : 1 ≤ a) (hae : a ≤ e) (hb : b = 2 * e - 2 * a + 1)
    (D : AlignmentData pi e a b u0 w0 s R0) (O : OriginData D)
    (ht₁ : actualLowerBreak hG D.firstField O.first_degree (2 * a - 1))
    (ht₂ : actualLowerBreak hG D.secondField O.second_degree (2 * e))
    (ht₃ : actualLowerBreak hG D.thirdField O.third_degree (2 * e))
    (htK₁ : actualUpperBreak hG D.firstField O.first_degree (4 * e - 2 * a + 1))
    (htK₂ : actualUpperBreak hG D.secondField O.second_degree (2 * a - 1))
    (tau₁ : NormCharacter F D.firstField) (htau₁ : tau₁ ≠ 1)
    (tau₂ : NormCharacter F D.secondField) (htau₂ : tau₂ ≠ 1)
    (tau₃ : NormCharacter F D.thirdField) (htau₃ : tau₃ ≠ 1)
    (psi : LocalAddCharData F) (alpha : Fˣ)
    (halpha : ord F (alpha : F) =
      ((-psi.conductor - (2 * (e : ℤ) + 1) : ℤ) : WithTop ℤ))
    (chi₁ : ContinuousQuasiChar D.firstField) (chi₂ : ContinuousQuasiChar D.secondField)
    (chi₃ : ContinuousQuasiChar D.thirdField)
    (hc₁ : IsMultiplicativeConductor D.firstField chi₁ (4 * e + 1))
    (hc₂ : IsMultiplicativeConductor D.secondField chi₂ (2 * e + 2 * a))
    (H : NormalizationFormulas F D.firstField D.secondField D.thirdField
      a e ha tau₁ tau₂ tau₃ psi D.beta1 D.beta2 D.beta3 D.h1 D.h2 D.h3
      D.a1 D.a2 D.a3 chi₁ chi₂ chi₃ alpha)
    (lambda : ContinuousQuasiChar F) (h : ℕ) (hah : a ≤ h)
    (hn : multiplicativeConductorExponent F lambda = 2 * e + 1 + h)
    (g1 : Gal(K/D.firstField)) (hg1 : g1 ≠ 1) (hg1R : g1 D.R = -D.R)
    (g2 : Gal(K/D.secondField)) (hg2 : g2 ≠ 1) (hg2S : g2 D.S = -D.S)
    (q1 : Gal(D.firstField/F)) (hq1 : q1 ≠ 1) (hq1S : q1 D.firstGenerator = -D.firstGenerator)
    (q2 : Gal(D.secondField/F)) (hq2 : q2 ≠ 1) (hq2R : q2 D.secondGenerator = -D.secondGenerator)
    (q3 : Gal(D.thirdField/F)) (hq3 : q3 ≠ 1) (hq3SR : q3 D.thirdGenerator = -D.thirdGenerator)
    (Theta : ContinuousQuasiChar K)
    (hcomp₁ : normQuasiChar D.firstField K (chi₁ * normQuasiChar F D.firstField lambda) = Theta)
    (hcomp₂ : normQuasiChar D.secondField K (chi₂ * normQuasiChar F D.secondField lambda) = Theta)
    (hprimitive : ¬ ∃ eta : ContinuousQuasiChar F, normQuasiChar F K eta = Theta) :
    LanglandsFirstMainLemma.localConstant D.firstField (chi₁ * normQuasiChar F D.firstField lambda)
        (tracePullbackAddChar F D.firstField psi.character) *
      LanglandsFirstMainLemma.localConstant F tau₁.1 psi.character =
    LanglandsFirstMainLemma.localConstant D.secondField (chi₂ * normQuasiChar F D.secondField lambda)
        (tracePullbackAddChar F D.secondField psi.character) *
      LanglandsFirstMainLemma.localConstant F tau₂.1 psi.character := by
  obtain ⟨u, X, H', hau, hX, _hbase, hm₁, hm₂, hchart₁, hchart₂, hCord, hZord₁, hZord₂⟩ :=
    higherCoefficients hG hres htwo ha hae hb D O ht₁ ht₂ ht₃ htK₁ htK₂
      tau₁ htau₁ tau₂ htau₂ tau₃ htau₃ psi alpha halpha chi₁ chi₂ chi₃ hc₁ hc₂ H
      lambda h hah hn g1 hg1 hg1R g2 hg2 hg2S q1 hq1 hq1S q2 hq2 hq2R q3 hq3 hq3SR
  let alpha' := alpha * (u : Fˣ)
  have halpha' : ord F (alpha' : F) =
      ((-psi.conductor - (2 * (e : ℤ) + 1) : ℤ) : WithTop ℤ) := hau.trans halpha
  have CE := commonError hG hres htwo ha hae hb D O g1 hg1 hg1R g2 hg2 hg2S
    q1 hq1 hq1S q2 hq2 hq2R q3 hq3 hq3SR ht₃ htK₁ htK₂ (X : D.thirdField) (h : ℤ) hX
  have hC0 : D.adjustedOrigin X ≠ 0 := (ord_ne_top_iff K).1 (by
    rw [hCord]; exact WithTop.coe_ne_top)
  let C : Kˣ := Units.mk0 (D.adjustedOrigin X) hC0
  let theta₁ := canonicalLocalQuasiCharData D.firstField (chi₁ * normQuasiChar F D.firstField lambda)
  let theta₂ := canonicalLocalQuasiCharData D.secondField (chi₂ * normQuasiChar F D.secondField lambda)
  have hmt₁ : theta₁.conductor = 2 * (2 * e + 1 + h - a) := hm₁
  have hmt₂ : theta₂.conductor = 2 * (e + h) + 1 := by
    change multiplicativeConductorExponent D.secondField _ = _
    omega
  have E₁ := Basic.intermediateField_tower_compatible Nat.prime_two hG D.firstField O.first_degree
  have E₂ := Basic.intermediateField_tower_compatible Nat.prime_two hG D.secondField O.second_degree
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F D.firstField E₁.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F D.secondField E₂.2.2.2.2.2.2.2.2.2.2.2.1
  have hr₁ := higher_residue_degrees D.firstField hres
  have hr₂ := higher_residue_degrees D.secondField hres
  have ht₁' : PrimeCyclicExtension.IsLowerBreak F D.firstField (2 * a - 1) := by
    simpa [actualLowerBreak] using ht₁
  have ht₂' : PrimeCyclicExtension.IsLowerBreak F D.secondField (2 * e) := by
    simpa [actualLowerBreak] using ht₂
  obtain ⟨pi₁, hpi₁, hgen₁⟩ := monogenicUniformizer F D.firstField hr₁.1
  obtain ⟨pi₂, hpi₂, hgen₂⟩ := monogenicUniformizer F D.secondField hr₂.1
  let omega₁ : LocalQuasiCharData F := ⟨tau₁.1, 2 * a, by
    convert ramifiedNormCharacter_conductor F D.firstField ht₁' hr₁.1 pi₁ hpi₁ hgen₁ tau₁ htau₁
      using 1
    omega⟩
  let omega₂ : LocalQuasiCharData F := ⟨tau₂.1, 2 * e + 1,
    ramifiedNormCharacter_conductor F D.secondField ht₂' hr₂.1 pi₂ hpi₂ hgen₂ tau₂ htau₂⟩
  let psi₁ : LocalAddCharData D.firstField := ⟨psi.character.compTrace,
    2 * psi.conductor + 2 * (a : ℤ), by
      have hh := additiveConductor_compTrace_cyclicPrime F D.firstField ht₁' hr₁.1
        pi₁ hpi₁ hgen₁ psi.isConductor
      rw [O.first_degree] at hh
      convert hh using 1
      push_cast
      omega⟩
  let psi₂ : LocalAddCharData D.secondField := ⟨psi.character.compTrace,
    2 * psi.conductor + (2 * (e : ℤ) + 1), by
      have hh := additiveConductor_compTrace_cyclicPrime F D.secondField ht₂' hr₂.1
        pi₂ hpi₂ hgen₂ psi.isConductor
      rw [O.second_degree] at hh
      convert hh using 1
      push_cast
      omega⟩
  let alpha₁ := Units.map (algebraMap F D.firstField).toMonoidHom alpha'
  let alpha₂ := Units.map (algebraMap F D.secondField).toMonoidHom alpha'
  let W₁ := normUnits F D.firstField (Units.mk0 D.h1 O.h1_ne_zero)
  let W₂ := normUnits F D.secondField (Units.mk0 D.h2 O.h2_ne_zero)
  have hPsi : (scaleAddCharData F psi alpha').conductor = -(2 * (e : ℤ) + 1) := by
    have ho := ord_coe_eq_unitOrder F alpha'
    rw [halpha'] at ho
    have hu : unitOrder F alpha' = -psi.conductor - (2 * (e : ℤ) + 1) :=
      (WithTop.coe_eq_coe.mp ho).symm
    rw [scaleAddCharData_conductor, hu]
    omega
  have hPsi₁ : (scaleAddCharData D.firstField psi₁ alpha₁).conductor =
      -2 * (2 * (e : ℤ) + 1) + 2 * (a : ℤ) := by
    have hh := LocalAddCharData.conductor_compTrace_eq_cyclicPrime F D.firstField ht₁'
      hr₁.1 pi₁ hpi₁ hgen₁ (scaleAddCharData F psi alpha')
      (scaleAddCharData D.firstField psi₁ alpha₁) (higher_scaled_trace D.firstField psi psi₁ rfl alpha')
    rw [O.first_degree, hPsi] at hh
    convert hh using 1
    push_cast
    omega
  have hPsi₂ : (scaleAddCharData D.secondField psi₂ alpha₂).conductor = -(2 * (e : ℤ) + 1) := by
    have hh := LocalAddCharData.conductor_compTrace_eq_cyclicPrime F D.secondField ht₂'
      hr₂.1 pi₂ hpi₂ hgen₂ (scaleAddCharData F psi alpha')
      (scaleAddCharData D.secondField psi₂ alpha₂) (higher_scaled_trace D.secondField psi psi₂ rfl alpha')
    rw [O.second_degree, hPsi] at hh
    convert hh using 1
    push_cast
    omega
  have hZ₁ : Stationary.IsOrdinaryStationaryCoefficient D.firstField theta₁
      (scaleAddCharData D.firstField psi₁ alpha₁) (normUnits D.firstField K C) (by omega) := by
    apply higherOrdinaryFromChart D.firstField theta₁ _ _ (2 * e + 1 + h - a)
      (by omega) (by omega) (by omega)
    · change intermediateOrder D.firstField (norm D.firstField K (D.adjustedOrigin X)) = _
      rw [hZord₁, hPsi₁, hmt₁]
      congr 1
      omega
    · intro z hz
      rw [higher_scaled_trace D.firstField psi psi₁ rfl alpha']
      exact hchart₁ z hz
  have hZ₂ : Stationary.IsOrdinaryStationaryCoefficient D.secondField theta₂
      (scaleAddCharData D.secondField psi₂ alpha₂) (normUnits D.secondField K C) (by omega) := by
    apply higherOrdinaryFromChart D.secondField theta₂ _ _ (e + h + 1)
      (by omega) (by omega) (by omega)
    · change intermediateOrder D.secondField (norm D.secondField K (D.adjustedOrigin X)) = _
      rw [hZord₂, hPsi₂, hmt₂]
      congr 1
      omega
    · intro z hz
      rw [higher_scaled_trace D.secondField psi psi₂ rfl alpha']
      convert hchart₂ z (by
        convert hz using 1
        congr 1
        omega) using 1 <;> congr 1
  have hW₁ : Stationary.IsOrdinaryStationaryCoefficient F omega₁ (scaleAddCharData F psi alpha') W₁
      (by change 1 < 2 * a; omega) := by
    apply higherOrdinaryFromChart F omega₁ _ _ a (by omega) (by change 1 < 2 * a; omega)
      (by change (2 * a) / 2 + (2 * a) % 2 = a; omega)
    · change ord F D.beta1 = _
      rw [O.beta1_order, hPsi]
      change (b : WithTop ℤ) = ((2 * (e : ℤ) + 1 - (2 * a : ℕ) : ℤ) : WithTop ℤ)
      exact_mod_cast (show (b : ℤ) = 2 * (e : ℤ) + 1 - 2 * (a : ℤ) by omega)
    · exact H'.1.first_formula
  have hW₂ : Stationary.IsOrdinaryStationaryCoefficient F omega₂ (scaleAddCharData F psi alpha') W₂
      (by change 1 < 2 * e + 1; omega) := by
    apply higherOrdinaryFromChart F omega₂ _ _ (e + 1) (by omega)
      (by change 1 < 2 * e + 1; omega)
      (by change (2 * e + 1) / 2 + (2 * e + 1) % 2 = e + 1; omega)
    · change ord F D.beta2 = _
      rw [O.beta2_order, hPsi]
      change (0 : WithTop ℤ) = ((2 * (e : ℤ) + 1 - (2 * e + 1 : ℕ) : ℤ) : WithTop ℤ)
      norm_num
    · exact H'.1.second_formula
  have hodd := higherOddResidualProduct hG hres h ha hae hah hb D O ht₁ ht₂ htK₁ htK₂
    g1 g2 q3 X CE C rfl hCord theta₁ theta₂ omega₁ omega₂ tau₁ tau₂ rfl rfl Theta
    hcomp₁ hcomp₂ psi psi₁ psi₂ rfl rfl alpha' hmt₁ hmt₂ rfl rfl hZ₁ hZ₂ hW₁ hW₂
  have hne : Ramification.intermediateNormRange D.firstField ≠
      Ramification.intermediateNormRange D.secondField :=
    quadraticNormRanges_ne F D.firstField D.secondField ht₁' ht₂' hr₁.1 hr₂.1 O.first_degree (by omega)
  have hconj := Characters.conjugacy Nat.prime_two hG D.firstField D.secondField
    O.first_degree O.second_degree hne theta₁.character theta₂.character Theta hcomp₁ hcomp₂ hprimitive
  obtain ⟨nu₁, nu₂, hnu₁, hnu₂, hprod₁, hprod₂⟩ := hconj.2.2.2.2 rfl
  have hcard₁ : Nat.card (NormCharacter F D.firstField) = 2 :=
    (ramifiedNormCharacter_card F D.firstField ht₁' hr₁.1 pi₁ hpi₁ hgen₁).trans O.first_degree
  have hcard₂ : Nat.card (NormCharacter F D.secondField) = 2 :=
    (ramifiedNormCharacter_card F D.secondField ht₂' hr₂.1 pi₂ hpi₂ hgen₂).trans O.second_degree
  have hnueq₁ : nu₁ = tau₁ := ((Nat.card_eq_two_iff' (1 : NormCharacter F D.firstField)).mp hcard₁).unique hnu₁ htau₁
  have hnueq₂ : nu₂ = tau₂ := ((Nat.card_eq_two_iff' (1 : NormCharacter F D.secondField)).mp hcard₂).unique hnu₂ htau₂
  have hdet := hconj.2.2.1
  rw [hprod₁, hprod₂, hnueq₁, hnueq₂] at hdet
  letI : IsKleinFour Gal(K/F) := by
    let phi := Classical.choice hG
    constructor
    · rw [Nat.card_congr phi.toEquiv]; simp
    · rw [Monoid.exponent_eq_of_mulEquiv phi]; simp [Monoid.exponent_prod]
  letI : Algebra.IsQuadraticExtension F D.firstField := { finrank_eq_two' := O.first_degree }
  letI : Algebra.IsQuadraticExtension F D.secondField := { finrank_eq_two' := O.second_degree }
  letI : Algebra.IsQuadraticExtension D.firstField K := { finrank_eq_two' := E₁.2.2.2.2.2.2.2.2.2.2.1 }
  letI : Algebra.IsQuadraticExtension D.secondField K := { finrank_eq_two' := E₂.2.2.2.2.2.2.2.2.2.2.1 }
  have hf₁ := higherFullFactor D.firstField theta₁ omega₁ tau₁ rfl Theta hcomp₁ psi psi₁ rfl
    alpha' C D.origin O.h1_ne_zero (by omega) (by change 1 < 2 * a; omega) hZ₁ hW₁
  have hf₂ := higherFullFactor D.secondField theta₂ omega₂ tau₂ rfl Theta hcomp₂ psi psi₂ rfl
    alpha' C D.origin O.h2_ne_zero (by omega) (by change 1 < 2 * e + 1; omega) hZ₂ hW₂
  have hdelta₁ : norm F D.firstField (trace D.firstField K (C : K)) -
      norm F D.firstField (trace D.firstField K D.origin) = D.traceNormIncrement X := by
    change norm F D.firstField (trace D.firstField K (D.adjustedOrigin X)) - D.beta1 = _
    rw [CE.first_trace_norm]
    ring
  have hdelta₂ : norm F D.secondField (trace D.secondField K (C : K)) -
      norm F D.secondField (trace D.secondField K D.origin) = D.traceNormIncrement X := by
    change norm F D.secondField (trace D.secondField K (D.adjustedOrigin X)) - D.beta2 = _
    rw [CE.second_trace_norm]
    ring
  rw [hdelta₁, Stationary.completeNormalizedResidualFactor_even _ _ _ _ _ _ (by omega),
    Stationary.completeNormalizedResidualFactor_even _ _ _ _ _ _
      (by change (2 * a) % 2 = 0; omega), mul_one, mul_one] at hf₁
  rw [hdelta₂] at hf₂
  change _ = _ *
    (Stationary.completeNormalizedResidualFactor D.secondField theta₂ psi₂ alpha₂
      (normUnits D.secondField K C) (by omega) *
    Stationary.completeNormalizedResidualFactor F omega₂ psi alpha' W₂
      (by change 1 < 2 * e + 1; omega)) at hf₂
  rw [hodd, mul_one] at hf₂
  have hdet' : Characters.restrictQuasiChar F D.firstField theta₁.character * omega₁.character =
      Characters.restrictQuasiChar F D.secondField theta₂.character * omega₂.character := hdet
  rw [hdet'] at hf₁
  exact hf₁.trans hf₂.symm

end ActualResidualProduct

end

end LanglandsSecondMainLemma.Dyadic.Maximal
