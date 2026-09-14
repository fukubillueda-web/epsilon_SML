import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Models.PolynomialCoefficients
import LanglandsSecondMainLemma.Odd.Models.MonomialPhase
import LanglandsSecondMainLemma.Finite.PolynomialRigidity
import LanglandsSecondMainLemma.Odd.Total.TraceNorm
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.Finite.Extension

/-!
# Odd / Models / Compatibility

The exact discrepancy is a group character on the full certified norm domain.
Descending induction linearizes it on each successive unit lattice. A
constructed degree-four unramified extension supplies polynomial rigidity
for every residue field, in both field characteristics.

The induced intermediate fields and their Galois structures are constructed
inside the local compositum. Norm--log comparison identifies the norm
pullback of the original character with the coefficientwise transported
polynomial, retaining the original weights and residue-prime truncation.
Integral trace transfers coefficient order bounds and controls Teichmüller
carries. Prime-to-`p` descent is performed by `Finite.polynomialRigidity`.

Finally, valuation separation expands each lattice point in the original
Artin--Schreier power basis. The proved monomial phases kill the surviving
coefficients. `compatibility` constructs both minimal models and proves
`O:M:compat` on the complete unit domain, with no residue-degree restriction
or auxiliary character equality among its hypotheses.
-/

namespace LanglandsSecondMainLemma.Odd.Models

noncomputable section
open LanglandsFirstMainLemma
open scoped Polynomial

open private addChar_map_sum teichmuller_add_carry from
  LanglandsSecondMainLemma.Finite.PolynomialRigidity

section Linearization
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- Triviality on a deeper unit subgroup makes the actual character constant
on depth congruence classes. -/
theorem unitCharacter_eq_of_congruent {q M : ℕ}
    (Xi : unitFiltration L q →* ℂˣ)
    (htriv : ∀ u : unitFiltration L q,
      (u : Lˣ) ∈ unitFiltration L M → Xi u = 1)
    (u v : unitFiltration L q)
    (huv : ((u : Lˣ) : L) - ((v : Lˣ) : L) ∈ lattice L (M : ℤ)) :
    Xi u = Xi v := by
  apply div_eq_one.mp
  rw [← map_div]
  apply htriv
  exact (div_mem_unitFiltration_iff_congruentAtDepth L M (u : Lˣ) (v : Lˣ)
    (unitFiltration_le_unitGroup L q u.property)
    (unitFiltration_le_unitGroup L q v.property)).2 huv

/-- Additivity in the linear range is proved for the multiplicative character
itself, evaluated at `1-z`. The integer-depth multiplication error is retained. -/
theorem unitCharacter_add {q M : ℕ} (hq : 0 < q) (hlin : M ≤ 2 * q)
    (Xi : unitFiltration L q →* ℂˣ)
    (htriv : ∀ u : unitFiltration L q,
      (u : Lˣ) ∈ unitFiltration L M → Xi u = 1)
    (z w : lattice L (q : ℤ)) :
    Xi (positiveUnitOfLattice L hq (-(z + w))) =
      Xi (positiveUnitOfLattice L hq (-z)) *
        Xi (positiveUnitOfLattice L hq (-w)) := by
  rw [← map_mul]
  apply unitCharacter_eq_of_congruent L Xi htriv
  have hprod := mul_mem_lattice L z.property w.property
  have hdeep : (z : L) * (w : L) ∈ lattice L (M : ℤ) :=
    lattice_antitone L (by omega) hprod
  convert (lattice L (M : ℤ)).neg_mem hdeep using 1
  simp only [Subgroup.coe_mul, Units.val_mul, coe_positiveUnitOfLattice,
    Submodule.coe_neg, Submodule.coe_add]
  ring

/-- The additive character used in the descending induction is constructed
from the actual unit character and the already proved deeper triviality. -/
def unitCharacterLinearization {q M : ℕ} (hq : 0 < q) (hlin : M ≤ 2 * q)
    (Xi : unitFiltration L q →* ℂˣ)
    (htriv : ∀ u : unitFiltration L q,
      (u : Lˣ) ∈ unitFiltration L M → Xi u = 1) :
    AddChar (lattice L (q : ℤ)) ℂˣ where
  toFun z := Xi (positiveUnitOfLattice L hq (-z))
  map_zero_eq_one' := by
    have hzero : positiveUnitOfLattice L hq (-(0 : lattice L (q : ℤ))) = 1 := by
      apply Subtype.ext
      apply Units.ext
      simp
    rw [hzero, map_one]
  map_add_eq_mul' := unitCharacter_add L hq hlin Xi htriv

@[simp] theorem unitCharacterLinearization_apply {q M : ℕ}
    (hq : 0 < q) (hlin : M ≤ 2 * q) (Xi : unitFiltration L q →* ℂˣ)
    (htriv : ∀ u : unitFiltration L q,
      (u : Lˣ) ∈ unitFiltration L M → Xi u = 1)
    (z : lattice L (q : ℤ)) :
    unitCharacterLinearization L hq hlin Xi htriv z =
      Xi (positiveUnitOfLattice L hq (-z)) := rfl

/-- Linearization also respects every finite monomial expansion; no additivity
of the norm defect is presumed. -/
theorem unitCharacter_sum {q M : ℕ} (hq : 0 < q) (hlin : M ≤ 2 * q)
    (Xi : unitFiltration L q →* ℂˣ)
    (htriv : ∀ u : unitFiltration L q,
      (u : Lˣ) ∈ unitFiltration L M → Xi u = 1)
    {ι : Type*} (s : Finset ι) (z : ι → lattice L (q : ℤ)) :
    Xi (positiveUnitOfLattice L hq (-(∑ i ∈ s, z i))) =
      ∏ i ∈ s, Xi (positiveUnitOfLattice L hq (-z i)) := by
  exact addChar_map_sum (unitCharacterLinearization L hq hlin Xi htriv) s z

end Linearization

section NormCharacter
variable (E L : Type*) [Field E] [Field L]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra E L]

/-- Restrict the actual field norm to its proved principal-unit domain before
pulling back a character. -/
def modelNormCharacter {q r : ℕ} (R : unitFiltration E r →* ℂˣ)
    (hN : ∀ u : Lˣ, u ∈ unitFiltration L q →
      normUnits E L u ∈ unitFiltration E r) : unitFiltration L q →* ℂˣ where
  toFun u := R ⟨normUnits E L (u : Lˣ), hN u u.property⟩
  map_one' := by
    convert R.map_one using 1
    congr 1
    exact Subtype.ext (map_one (normUnits E L))
  map_mul' u v := by
    convert R.map_mul ⟨normUnits E L (u : Lˣ), hN u u.property⟩
      ⟨normUnits E L (v : Lˣ), hN v v.property⟩ using 1
    congr 1
    exact Subtype.ext (map_mul (normUnits E L) (u : Lˣ) (v : Lˣ))

@[simp] theorem modelNormCharacter_apply {q r : ℕ}
    (R : unitFiltration E r →* ℂˣ)
    (hN : ∀ u : Lˣ, u ∈ unitFiltration L q →
      normUnits E L u ∈ unitFiltration E r) (u : unitFiltration L q) :
    modelNormCharacter E L R hN u =
      R ⟨normUnits E L (u : Lˣ), hN u u.property⟩ := rfl
end NormCharacter

section ActualDiscrepancy
variable (F E₁ E₂ L : Type*) [Field F] [Field E₁] [Field E₂] [Field L]
  [ValuativeRel E₁] [TopologicalSpace E₁] [IsNonarchimedeanLocalField E₁]
  [ValuativeRel E₂] [TopologicalSpace E₂] [IsNonarchimedeanLocalField E₂]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra F E₁] [Algebra F E₂] [Algebra E₁ L] [Algebra E₂ L]
  [TopologicalSpace F] [IsTopologicalRing F]
  [IsModuleTopology F E₁] [IsModuleTopology F E₂]

/-- The character `Xi = R₁ N₁ / R₂ N₂` from the proof of `O:M:compat`.
Both factors are group homomorphisms on the full certified norm domain. -/
def modelDiscrepancy {p q q₁ m₁ q₂ m₂ : ℕ}
    {Psi : ContinuousAddChar F} {b : E₁} {a : E₂}
    (M : OddMinimalCharacterModels E₁ E₂ p q₁ m₁ q₂ m₂
      (tracePullbackAddChar F E₁ Psi) (tracePullbackAddChar F E₂ Psi) b a)
    (hN₁ : ∀ u : Lˣ, u ∈ unitFiltration L q →
      normUnits E₁ L u ∈ unitFiltration E₁ q₁)
    (hN₂ : ∀ u : Lˣ, u ∈ unitFiltration L q →
      normUnits E₂ L u ∈ unitFiltration E₂ q₂) :
    unitFiltration L q →* ℂˣ :=
  modelNormCharacter E₁ L M.R₁ hN₁ / modelNormCharacter E₂ L M.R₂ hN₂

@[simp] theorem modelDiscrepancy_apply {p q q₁ m₁ q₂ m₂ : ℕ}
    {Psi : ContinuousAddChar F} {b : E₁} {a : E₂}
    (M : OddMinimalCharacterModels E₁ E₂ p q₁ m₁ q₂ m₂
      (tracePullbackAddChar F E₁ Psi) (tracePullbackAddChar F E₂ Psi) b a)
    (hN₁ : ∀ u : Lˣ, u ∈ unitFiltration L q →
      normUnits E₁ L u ∈ unitFiltration E₁ q₁)
    (hN₂ : ∀ u : Lˣ, u ∈ unitFiltration L q →
      normUnits E₂ L u ∈ unitFiltration E₂ q₂) (u : unitFiltration L q) :
    modelDiscrepancy F E₁ E₂ L M hN₁ hN₂ u =
      M.R₁ ⟨normUnits E₁ L (u : Lˣ), hN₁ u u.property⟩ /
        M.R₂ ⟨normUnits E₂ L (u : Lˣ), hN₂ u u.property⟩ := rfl

variable [Module.Free E₁ L] [Module.Finite E₁ L] [IsGalois E₁ L]
  [Module.Free E₂ L] [Module.Finite E₂ L] [IsGalois E₂ L]
  [Algebra F L] [IsScalarTower F E₁ L] [IsScalarTower F E₂ L]

/-- The constructed discrepancy agrees with the exact polynomial, at every
lattice point in its domain. -/
theorem modelDiscrepancy_polynomial {p q q₁ m₁ q₂ m₂ : ℕ} (hq : 0 < q)
    {Psi : ContinuousAddChar F} {b : E₁} {a : E₂}
    (M : OddMinimalCharacterModels E₁ E₂ p q₁ m₁ q₂ m₂
      (tracePullbackAddChar F E₁ Psi) (tracePullbackAddChar F E₂ Psi) b a)
    (hN₁ : ∀ u : Lˣ, u ∈ unitFiltration L q →
      normUnits E₁ L u ∈ unitFiltration E₁ q₁)
    (hN₂ : ∀ u : Lˣ, u ∈ unitFiltration L q →
      normUnits E₂ L u ∈ unitFiltration E₂ q₂) (z : lattice L (q : ℤ)) :
    modelDiscrepancy F E₁ E₂ L M hN₁ hN₂ (positiveUnitOfLattice L hq (-z)) =
      Psi ((discrepancyPolynomial F E₁ E₂ L p b a z).eval 1) := by
  have h := discrepancyPolynomial_character F E₁ E₂ L p q₁ m₁ q₂ m₂
    Psi b a M (positiveUnitOfLattice L hq (-z))
    (hN₁ _ (positiveUnitOfLattice L hq (-z)).property)
    (hN₂ _ (positiveUnitOfLattice L hq (-z)).property)
  simpa only [modelDiscrepancy_apply, coe_positiveUnitOfLattice,
    Submodule.coe_neg, ← sub_eq_add_neg, sub_sub_cancel] using h.symm

end ActualDiscrepancy

section IntegralRigidity
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

omit [IsNonarchimedeanLocalField F] in
/-- The coefficient order bound gives the order of the exact polynomial
phase at every integral scalar, before any rigidity or descent argument. -/
theorem polynomialPhase_pow_eq_one {p : ℕ}
    (Psi : ContinuousAddChar F) (f : F[X])
    (hcoeff : ∀ n ∈ f.support, ∀ x : ringOfIntegers F,
      Psi (f.coeff n * (x : F)) ^ p = 1)
    (x : ringOfIntegers F) : Psi (f.eval (x : F)) ^ p = 1 := by
  classical
  change Psi.toAddChar (f.eval (x : F)) ^ p = 1
  rw [Polynomial.eval_eq_sum, Polynomial.sum, addChar_map_sum, ← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro n hn
  exact hcoeff n hn (x ^ n)

omit [IsNonarchimedeanLocalField F] in
/-- The coefficient order bound kills polynomial changes by `p` times an
integral scalar, including every Teichmüller carry. -/
theorem polynomialPhase_congr_mod_prime {p : ℕ}
    (Psi : ContinuousAddChar F) (f : F[X])
    (hcoeff : ∀ n ∈ f.support, ∀ x : ringOfIntegers F,
      Psi (f.coeff n * (x : F)) ^ p = 1)
    (x y : ringOfIntegers F) (hxy : (p : ringOfIntegers F) ∣ x - y) :
    Psi (f.eval (x : F)) = Psi (f.eval (y : F)) := by
  classical
  apply div_eq_one.mp
  change Psi.toAddChar (f.eval (x : F)) / Psi.toAddChar (f.eval (y : F)) = 1
  rw [← AddChar.map_sub_eq_div Psi.toAddChar]
  have heval : f.eval (x : F) - f.eval (y : F) =
      ∑ n ∈ f.support, f.coeff n * ((x : F) ^ n - (y : F) ^ n) := by
    simp only [Polynomial.eval_eq_sum, Polynomial.sum, mul_sub,
      Finset.sum_sub_distrib]
  rw [heval, addChar_map_sum]
  apply Finset.prod_eq_one
  intro n hn
  obtain ⟨v, hv⟩ := dvd_trans hxy (sub_dvd_pow_sub_pow x y n)
  have hv' : (x : F) ^ n - (y : F) ^ n = (p : F) * (v : F) := by
    exact_mod_cast hv
  rw [hv']
  have he : f.coeff n * ((p : F) * (v : F)) = p • (f.coeff n * (v : F)) := by
    rw [nsmul_eq_mul]
    ring
  rw [he, AddChar.map_nsmul_eq_pow]
  exact hcoeff n hn v

/-- Integral additivity gives the residue-field additivity required by
rigidity. The carry is handled by the proved coefficient order bound. -/
theorem polynomialPhase_teichmuller_add {p : ℕ}
    (hchar : residueCharacteristic F = p) (Psi : ContinuousAddChar F) (f : F[X])
    (hcoeff : ∀ n ∈ f.support, ∀ x : ringOfIntegers F,
      Psi (f.coeff n * (x : F)) ^ p = 1)
    (hadd : ∀ x y : ringOfIntegers F,
      Psi (f.eval ((x + y : ringOfIntegers F) : F)) =
        Psi (f.eval (x : F)) * Psi (f.eval (y : F)))
    (x y : ResidueField F) :
    Psi (f.eval (teichmuller F (x + y) : F)) =
      Psi (f.eval (teichmuller F x : F)) *
        Psi (f.eval (teichmuller F y : F)) := by
  obtain ⟨v, hv⟩ := teichmuller_add_carry F x y
  have hdiv : (p : ringOfIntegers F) ∣
      teichmuller F (x + y) - (teichmuller F x + teichmuller F y) := by
    refine ⟨v, ?_⟩
    apply Subtype.ext
    change (teichmuller F (x + y) : F) -
      ((teichmuller F x : F) + (teichmuller F y : F)) = (p : F) * (v : F)
    simpa only [sub_add_eq_sub_sub, hchar] using hv
  exact (polynomialPhase_congr_mod_prime F Psi f hcoeff _ _ hdiv).trans
    (hadd _ _)

end IntegralRigidity

namespace BaseChange
section NormTrace
variable (E L E' L' : Type*) [Field E] [Field L] [Field E'] [Field L']
  [Algebra E L] [Algebra E E'] [Algebra E L'] [Algebra L L'] [Algebra E' L']
  [IsScalarTower E L L'] [IsScalarTower E E' L']
  [Module.Finite E L] [IsGalois E L] [Module.Finite E' L']

/-- In a compositum square of unchanged degree, the norm and trace of
each specified downstairs element are preserved. In particular this
preserves the norm coefficients of the chosen coordinate itself. -/
theorem norm_trace_algebraMap
    (hgen : Algebra.adjoin E' (Set.range (algebraMap L L')) = ⊤)
    (hdegree : Module.finrank E' L' = Module.finrank E L) (x : L) :
    norm E' L' (algebraMap L L' x) = algebraMap E E' (norm E L x) ∧
      trace E' L' (algebraMap L L' x) = algebraMap E E' (trace E L x) := by
  classical
  letI := galois_square E L E' L' hgen
  let r := IntermediateField.restrictRestrictAlgEquivMapHom E L E' L'
  have hr : Function.Bijective r := by
    apply (Fintype.bijective_iff_injective_and_card r).2
    refine ⟨restriction_square_injective E L E' L' hgen, ?_⟩
    simpa only [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank] using hdegree
  have hcomm (σ : Gal(L'/E')) :
      σ (algebraMap L L' x) = algebraMap L L' (r σ x) := by
    simp only [r, IntermediateField.restrictRestrictAlgEquivMapHom,
      MonoidHom.comp_apply, AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply,
      AlgEquiv.restrictNormal_commutes, MulSemiringAction.toAlgAut_apply,
      MulSemiringAction.toAlgEquiv_apply, AlgEquiv.smul_def]
  constructor
  · apply (algebraMap E' L').injective
    rw [← IsScalarTower.algebraMap_apply E E' L',
      IsScalarTower.algebraMap_apply E L L', Algebra.norm_eq_prod_automorphisms,
      Algebra.norm_eq_prod_automorphisms, map_prod]
    exact Finset.prod_bijective r hr (by simp) (fun σ _ => hcomm σ)
  · apply (algebraMap E' L').injective
    rw [← IsScalarTower.algebraMap_apply E E' L',
      IsScalarTower.algebraMap_apply E L L', trace_eq_sum_automorphisms,
      trace_eq_sum_automorphisms, map_sum]
    exact Finset.sum_bijective r hr (by simp) (fun σ _ => hcomm σ)

/-- Coefficientwise weighted trace preserves the specified weight under
base change; it does not choose a new model coefficient upstairs. -/
theorem weightedTracePolynomial_algebraMap
    (hgen : Algebra.adjoin E' (Set.range (algebraMap L L')) = ⊤)
    (hdegree : Module.finrank E' L' = Module.finrank E L)
    (b : L) (f : L[X]) :
    weightedTracePolynomial E' L' (algebraMap L L' b) (f.map (algebraMap L L')) =
      (weightedTracePolynomial E L b f).map (algebraMap E E') := by
  ext n
  simp only [weightedTracePolynomial_coeff, Polynomial.coeff_map, ← map_mul]
  exact (norm_trace_algebraMap E L E' L' hgen hdegree (b * f.coeff n)).2

end NormTrace

open private localField_infinite from LanglandsSecondMainLemma.Odd.Total.TraceNorm

section NormPolynomial
variable (E L E' L' : Type*) [Field E] [Field L] [Field E'] [Field L']
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel E'] [TopologicalSpace E'] [IsNonarchimedeanLocalField E']
  [Algebra E L] [Algebra E E'] [Algebra E L'] [Algebra L L'] [Algebra E' L']
  [IsScalarTower E L L'] [IsScalarTower E E' L']
  [Module.Finite E L] [IsGalois E L] [Module.Finite E' L']

/-- The entire exact norm polynomial is transported coefficientwise.
Equality on the infinite embedded base field proves the polynomial identity,
so it also controls evaluation at scalars outside that embedded field. -/
theorem normArgumentPolynomial_algebraMap
    (hgen : Algebra.adjoin E' (Set.range (algebraMap L L')) = ⊤)
    (hdegree : Module.finrank E' L' = Module.finrank E L) (z : L) :
    normArgumentPolynomial E' L' (algebraMap L L' z) =
      (normArgumentPolynomial E L z).map (algebraMap E E') := by
  letI := galois_square E L E' L' hgen
  letI := localField_infinite E
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (algebraMap E E').injective).mono
  rintro _ ⟨s, rfl⟩
  change _ = _
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply,
    normArgumentPolynomial_eval, normArgumentPolynomial_eval]
  have harg :
      1 - algebraMap E' L' (algebraMap E E' s) * algebraMap L L' z =
        algebraMap L L' (1 - algebraMap E L s * z) := by
    simp only [map_sub, map_one, map_mul, ← IsScalarTower.algebraMap_apply]
  rw [harg, (norm_trace_algebraMap E L E' L' hgen hdegree _).1]
  simp only [map_sub, map_one]

/-- The original truncated logarithm, including every denominator, commutes
with the exact norm-polynomial transport. -/
theorem normLogPolynomial_algebraMap
    (hgen : Algebra.adjoin E' (Set.range (algebraMap L L')) = ⊤)
    (hdegree : Module.finrank E' L' = Module.finrank E L) (p : ℕ) (z : L) :
    normLogPolynomial E' L' p (algebraMap L L' z) =
      (normLogPolynomial E L p z).map (algebraMap E E') := by
  rw [normLogPolynomial, normLogPolynomial, Polynomial.map_comp,
    normArgumentPolynomial_algebraMap E L E' L' hgen hdegree]
  congr 1
  simp [truncatedLogPolynomial, Polynomial.map_sum]

end NormPolynomial

end BaseChange

section ScalarOrbit
variable (F L : Type*) [Field F] [Field L]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra F L] [ValuativeExtension F L]

/-- Integral base scalars act additively on every integer-depth lattice in
the actual extension field. -/
def integralScalarLattice {q : ℤ} (z : lattice L q) :
    ringOfIntegers F →+ lattice L q where
  toFun x := ⟨algebraMap F L (x : F) * (z : L), by
    have hx : (0 : WithTop ℤ) ≤ ord F (x : F) :=
      (mem_lattice F).1 ((mem_lattice_zero_iff F).2 x.property)
    have hx' : algebraMap F L (x : F) ∈ lattice L 0 := by
      rw [mem_lattice, ord_algebraMap]
      simpa only [nsmul_zero, WithTop.coe_zero] using
        nsmul_le_nsmul_right hx (ramificationIndex F L)
    simpa only [zero_add] using mul_mem_lattice L hx' z.property⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [map_add, add_mul]

@[simp] theorem integralScalarLattice_apply {q : ℤ} (z : lattice L q)
    (x : ringOfIntegers F) :
    (integralScalarLattice F L z x : L) = algebraMap F L (x : F) * (z : L) := rfl

end ScalarOrbit

section DiamondCoefficients
variable {F K : Type*} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]

/-- The surviving polynomial coefficients have exactly the phase of `g+h`
on the genuine diamond. The degree-`p` correction is killed using the whole
conductor lattice supplied by `polynomialCoefficients`. -/
theorem discrepancyPolynomial_coeff_phase {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (D : Total.OddTotalBreakData (F := F) (K := K) hp hG)
    (Delta : K) (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((D.t₂ + 1 : ℕ) : ℤ)))
    (z : K) (hz : z ∈ lattice K ((firstModelDepth D : ℕ) : ℤ)) :
    let B₁ := D.B₁
    let B₂ := D.B₂
    letI := Basic.intermediateFieldValuativeRel B₁
    letI := Basic.intermediateFieldTopology B₁
    letI := Basic.intermediateField_localField B₁
    letI := Basic.intermediateFieldValuativeRel B₂
    letI := Basic.intermediateFieldTopology B₂
    letI := Basic.intermediateField_localField B₂
    let f := discrepancyPolynomial F B₁ B₂ K p (norm B₁ K Delta) (norm B₂ K Delta) z
    Psi (f.coeff 1 + f.coeff p) =
      Psi ((trace F B₁ (norm B₁ K Delta * trace B₁ K z) -
        trace F B₂ (norm B₂ K Delta * trace B₂ K z)) +
        Total.weightedNormTraceDefect F B₁ B₂ K Delta z) := by
  let B₁ := D.B₁
  let B₂ := D.B₂
  letI := Basic.intermediateFieldValuativeRel B₁
  letI := Basic.intermediateFieldTopology B₁
  letI := Basic.intermediateField_localField B₁
  letI := Basic.intermediateFieldValuativeRel B₂
  letI := Basic.intermediateFieldTopology B₂
  letI := Basic.intermediateField_localField B₂
  let f := discrepancyPolynomial F B₁ B₂ K p (norm B₁ K Delta) (norm B₂ K Delta) z
  obtain ⟨_, hlinear, hprime⟩ := polynomialCoefficients hp hG hres hchar D
    Delta hDelta Psi hPsi z hz
  have htriv := hPsi.trivial
  rw [neg_neg] at htriv
  have hphase : Psi (f.coeff p) =
      Psi (Total.weightedNormTraceDefect F B₁ B₂ K Delta z) := by
    apply div_eq_one.mp
    change Psi.toAddChar (f.coeff p) /
      Psi.toAddChar (Total.weightedNormTraceDefect F B₁ B₂ K Delta z) = 1
    rw [← AddChar.map_sub_eq_div]
    exact htriv _ hprime
  change Psi (f.coeff 1 + f.coeff p) = _
  rw [ContinuousAddChar.map_add_eq_mul, hphase, hlinear,
    ← ContinuousAddChar.map_add_eq_mul]

end DiamondCoefficients

section DeepDiscrepancy
variable (F E₁ E₂ L : Type*) [Field F] [Field E₁] [Field E₂] [Field L]
  [ValuativeRel E₁] [TopologicalSpace E₁] [IsNonarchimedeanLocalField E₁]
  [ValuativeRel E₂] [TopologicalSpace E₂] [IsNonarchimedeanLocalField E₂]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra F E₁] [Algebra F E₂] [Algebra E₁ L] [Algebra E₂ L]
  [TopologicalSpace F] [IsTopologicalRing F]
  [IsModuleTopology F E₁] [IsModuleTopology F E₂]
  [Module.Free E₁ L] [Module.Finite E₁ L] [PrimeCyclicExtension E₁ L]
  [Module.Free E₂ L] [Module.Finite E₂ L] [PrimeCyclicExtension E₂ L]
  [ValuativeExtension E₁ L] [ValuativeExtension E₂ L]

/-- A finite starting depth for descending induction, obtained directly from
the exact model conductors and the proved norm filtration. This bound is
`p * max m₁ m₂`; it does not assert the paper's sharper initial depth `m₁`. -/
theorem modelDiscrepancy_trivial_deep {p q q₁ m₁ q₂ m₂ t₁ t₂ : ℕ}
    (hp : 0 < p) (hd₁ : Module.finrank E₁ L = p) (hd₂ : Module.finrank E₂ L = p)
    (ht₁ : PrimeCyclicExtension.IsLowerBreak E₁ L t₁)
    (ht₂ : PrimeCyclicExtension.IsLowerBreak E₂ L t₂)
    (hr₁ : residueDegree E₁ L = 1) (hr₂ : residueDegree E₂ L = 1)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    {Psi : ContinuousAddChar F} {b : E₁} {a : E₂}
    (M : OddMinimalCharacterModels E₁ E₂ p q₁ m₁ q₂ m₂
      (tracePullbackAddChar F E₁ Psi) (tracePullbackAddChar F E₂ Psi) b a)
    (hN₁ : ∀ u : Lˣ, u ∈ unitFiltration L q →
      normUnits E₁ L u ∈ unitFiltration E₁ q₁)
    (hN₂ : ∀ u : Lˣ, u ∈ unitFiltration L q →
      normUnits E₂ L u ∈ unitFiltration E₂ q₂)
    (u : unitFiltration L q)
    (hu : (u : Lˣ) ∈ unitFiltration L (p * max m₁ m₂)) :
    modelDiscrepancy F E₁ E₂ L M hN₁ hN₂ u = 1 := by
  have hn₁ : normUnits E₁ L (u : Lˣ) ∈ unitFiltration E₁ m₁ := by
    apply norm_maps_modelDepth E₁ L ht₁ hr₁ hm₁
      (show m₁ ≤ p * max m₁ m₂ by
        have := Nat.le_max_left m₁ m₂
        nlinarith) _ (u : Lˣ) hu
    rw [hd₁, Nat.le_div_iff_mul_le hp]
    have := Nat.le_max_left m₁ m₂
    nlinarith
  have hn₂ : normUnits E₂ L (u : Lˣ) ∈ unitFiltration E₂ m₂ := by
    apply norm_maps_modelDepth E₂ L ht₂ hr₂ hm₂
      (show m₂ ≤ p * max m₁ m₂ by
        have := Nat.le_max_right m₁ m₂
        nlinarith) _ (u : Lˣ) hu
    rw [hd₂, Nat.le_div_iff_mul_le hp]
    have := Nat.le_max_right m₁ m₂
    nlinarith
  have hR₁ : M.R₁ ⟨normUnits E₁ L (u : Lˣ), hN₁ u u.property⟩ = 1 := by
    have h := DFunLike.congr_fun M.R₁_conductor.trivial
      (⟨normUnits E₁ L (u : Lˣ), hn₁⟩ : unitFiltration E₁ m₁)
    simpa [Subgroup.inclusion, MonoidHom.mk'] using h
  have hR₂ : M.R₂ ⟨normUnits E₂ L (u : Lˣ), hN₂ u u.property⟩ = 1 := by
    have h := DFunLike.congr_fun M.R₂_conductor.trivial
      (⟨normUnits E₂ L (u : Lˣ), hn₂⟩ : unitFiltration E₂ m₂)
    simpa [Subgroup.inclusion, MonoidHom.mk'] using h
  rw [modelDiscrepancy_apply, hR₁, hR₂, div_one]

end DeepDiscrepancy

open private preliminary_coefficient_bound from
  LanglandsSecondMainLemma.Odd.Total.CoefficientExtraction
open private norm_basis_expansion from
  LanglandsSecondMainLemma.Odd.Total.NormCoefficients

/-- Valuation separation puts every term of the genuine power-basis
expansion in the same integer-depth lattice as its sum. The coordinate is
preserved throughout. -/
theorem powerBasis_lattice_expansion
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    {p t : ℕ} (hp : p.Prime) (hram : ramificationIndex E L = p)
    (pb : PowerBasis E L) (hdim : pb.dim = p)
    (hDelta : ord L pb.gen = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ t) (r : ℤ) (z : lattice L r) :
    ∃ x : Fin p → E,
      (z : L) = ∑ j : Fin p, algebraMap E L (x j) * pb.gen ^ (j : ℕ) ∧
      ∀ j : Fin p, algebraMap E L (x j) * pb.gen ^ (j : ℕ) ∈ lattice L r := by
  let x : Fin p → E := fun j => pb.basis.repr (z : L) (Fin.cast hdim.symm j)
  have hexp : (z : L) = ∑ j : Fin p, algebraMap E L (x j) * pb.gen ^ (j : ℕ) :=
    norm_basis_expansion pb hdim z
  refine ⟨x, hexp, ?_⟩
  intro j
  have hterm := preliminary_coefficient_bound E L hp hram hDelta hprime x j
  rw [← hexp] at hterm
  exact ((mem_lattice L).1 z.property).trans hterm

namespace BaseChange

open scoped NNReal in
/-- Every finite field extension has an actual local-field structure extending
the given base valuation. The spectral norm supplies the topology; finite
dimensionality supplies local compactness. -/
theorem finiteExtension_localField_exists
    (F L : Type*) [Field F] [Field L]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F L] [Module.Finite F L] :
    ∃ (_v : ValuativeRel L) (_top : TopologicalSpace L),
      IsNonarchimedeanLocalField L ∧ ValuativeExtension F L := by
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  letI : Valued F (ValuativeRel.ValueGroupWithZero F) := inferInstance
  letI : (Valued.v : Valuation F (ValuativeRel.ValueGroupWithZero F)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := F).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField F := Valued.toNontriviallyNormedField F _
  letI : CompleteSpace F := inferInstance
  letI : IsUltrametricDist F := inferInstance
  letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField F L
  letI : NormedAlgebra F L := spectralNorm.normedAlgebra F L
  letI : IsUltrametricDist L := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := F) (L := L))
  letI : Valued L ℝ≥0 := NormedField.toValued
  letI : ValuativeRel L := ValuativeRel.ofValuation (NormedField.valuation (K := L))
  letI : (NormedField.valuation (K := L)).Compatible :=
    Valuation.Compatible.ofValuation _
  letI : IsValuativeTopology L :=
    IsValuativeTopology.of_mem_nhds_iff_vle (NormedField.valuation (K := L))
      (fun {_ _} => Valued.mem_nhds)
  letI : ValuativeRel.IsNontrivial L :=
    (ValuativeRel.isNontrivial_iff_isNontrivial (NormedField.valuation (K := L))).2
      inferInstance
  letI : LocallyCompactSpace L :=
    LocallyCompactSpace.of_finiteDimensional_of_complete F L
  have hv : ValuativeExtension F L := ⟨by
    intro x y
    change ‖algebraMap F L x‖₊ ≤ ‖algebraMap F L y‖₊ ↔ x ≤ᵥ y
    rw [← NNReal.coe_le_coe]
    change spectralNorm F L (algebraMap F L x) ≤
      spectralNorm F L (algebraMap F L y) ↔ x ≤ᵥ y
    rw [spectralNorm_extends, spectralNorm_extends, Valued.toNormedField.norm_le_iff]
    exact (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F) x y).symm⟩
  refine ⟨inferInstance, inferInstance, ?_, hv⟩
  exact { toIsValuativeTopology := inferInstance
          toLocallyCompactSpace := inferInstance
          toIsNontrivial := inferInstance }

/-- A monic irreducible residue polynomial of any prescribed positive
degree lifts to the actual valuation ring, without changing its degree. -/
theorem irreducible_residue_lift_exists
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) [NeZero n] :
    ∃ P : (ringOfIntegers F)[X], P.Monic ∧ P.natDegree = n ∧
      Irreducible (P.map (residueMap F)) ∧
      Irreducible (P.map (algebraMap (ringOfIntegers F) F)) := by
  let p := residueCharacteristic F
  letI : Fact p.Prime := ⟨residueCharacteristic_prime F⟩
  let k' := FiniteField.Extension (ResidueField F) p n
  let pb := Field.powerBasisOfFiniteOfSeparable (ResidueField F) k'
  let g := minpoly (ResidueField F) pb.gen
  have hg : Irreducible g := minpoly.irreducible pb.isIntegral_gen
  obtain ⟨P, hmap, hdegree, hmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (residueMap_surjective F) g)
    (minpoly.monic pb.isIntegral_gen)
  have hirr : Irreducible (P.map (residueMap F)) := hmap.symm ▸ hg
  refine ⟨P, hmonic, ?_, hirr,
    hmonic.irreducible_iff_irreducible_map_fraction_map.mp
      (hmonic.irreducible_of_irreducible_map (residueMap F) P hirr)⟩
  rw [hdegree, pb.natDegree_minpoly, ← pb.finrank]
  exact FiniteField.finrank_extension (ResidueField F) p n

set_option synthInstance.maxHeartbeats 100000 in
/-- A root of a monic lift of an irreducible residue polynomial generates
an unramified extension when its field degree equals the polynomial degree.
The residue-degree lower bound is proved using the reduced root. -/
theorem unramified_of_irreducible_reduction
    (F L : Type*) [Field F] [Field L]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra F L] [ValuativeExtension F L] [Module.Finite F L]
    (P : (ringOfIntegers F)[X]) (hmonic : P.Monic)
    (hirr : Irreducible (P.map (residueMap F)))
    (x : L) (hx : Polynomial.aeval x P = 0)
    (hdegree : Module.finrank F L = P.natDegree) :
    ramificationIndex F L = 1 ∧ residueDegree F L = P.natDegree := by
  letI := ringOfIntegers_isIntegralClosure F L
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff
    (A := ringOfIntegers L) (R := ringOfIntegers F) (B := L)).1
    (show IsIntegral (ringOfIntegers F) x from ⟨P, hmonic, hx⟩)
  have hyroot : Polynomial.aeval y P = 0 := by
    apply (IsIntegralClosure.algebraMap_injective
      (ringOfIntegers L) (ringOfIntegers F) L)
    simpa only [map_zero, ← Polynomial.aeval_algebraMap_apply, hy] using hx
  have hredroot : Polynomial.aeval (residueMap L y) (P.map (residueMap F)) = 0 := by
    have h := congrArg (residueMap L) hyroot
    have hcomm : (algebraMap (ResidueField F) (ResidueField L)).comp (residueMap F) =
        (residueMap L).comp (algebraMap (ringOfIntegers F) (ringOfIntegers L)) := rfl
    simpa only [Polynomial.aeval_def, Polynomial.eval₂_map, hcomm,
      Polynomial.hom_eval₂, map_zero] using h
  have hmin : minpoly (ResidueField F) (residueMap L y) = P.map (residueMap F) :=
    (minpoly.eq_of_irreducible_of_monic hirr hredroot (hmonic.map _)).symm
  have hle : P.natDegree ≤ residueDegree F L := by
    rw [residueDegree_eq_finrank_residueField]
    have h := minpoly.natDegree_le (A := ResidueField F) (x := residueMap L y)
    simpa only [hmin, hmonic.natDegree_map] using h
  have hprod := finrank_eq_ramificationIndex_mul_residueDegree F L
  have he := ramificationIndex_pos F L
  have hf := residueDegree_pos F L
  rw [hdegree] at hprod
  have heq : ramificationIndex F L = 1 := by nlinarith
  exact ⟨heq, by simpa only [heq, one_mul] using hprod.symm⟩

/-- A simple residue root lifts to an exact integral root with the same
residue. This is the local Hensel step used to construct the automorphisms
of the unramified extension. -/
theorem lift_simple_residue_root
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (P : (ringOfIntegers L)[X]) (hP : P.Monic)
    (x : ResidueField L) (hx : (P.map (residueMap L)).eval x = 0)
    (hd : (P.map (residueMap L)).derivative.eval x ≠ 0) :
    ∃ y : ringOfIntegers L, P.eval y = 0 ∧ residueMap L y = x := by
  obtain ⟨x₀, rfl⟩ := residueMap_surjective L x
  letI : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  letI : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  have hx₀ : P.eval x₀ ∈ IsLocalRing.maximalIdeal (ringOfIntegers L) := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simpa only [Polynomial.eval_map_apply] using hx
  have hd₀ : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (ringOfIntegers L))
      (P.derivative.eval x₀)) := by
    change IsUnit (residueMap L (P.derivative.eval x₀))
    apply isUnit_iff_ne_zero.mpr
    simpa only [Polynomial.derivative_map, Polynomial.eval_map_apply] using hd
  obtain ⟨y, hy, hres⟩ := HenselianRing.is_henselian P hP x₀ hx₀ hd₀
  refine ⟨y, hy, ?_⟩
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (IsLocalRing.residue_eq_zero_iff _).2 hres

set_option synthInstance.maxHeartbeats 100000 in
/-- A monic lift of an irreducible residue polynomial splits in any local
field generated by one of its roots. The residue roots lift individually;
their distinct residues give the full number of field roots. -/
theorem galois_of_irreducible_reduction
    (F L : Type*) [Field F] [Field L]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra F L] [ValuativeExtension F L] [Module.Finite F L]
    (P : (ringOfIntegers F)[X]) (hP : P.Monic)
    (hirr : Irreducible (P.map (residueMap F)))
    (x : L) (hx : Polynomial.aeval x P = 0)
    (hgen : Algebra.adjoin F ({x} : Set L) = ⊤) : IsGalois F L := by
  classical
  let f := P.map (algebraMap (ringOfIntegers F) F)
  let g := P.map (residueMap F)
  let Q := P.map (algebraMap (ringOfIntegers F) (ringOfIntegers L))
  have hf : Irreducible f := hP.irreducible_iff_irreducible_map_fraction_map.mp
    (hP.irreducible_of_irreducible_map (residueMap F) P hirr)
  have hg : g.Separable := PerfectField.separable_of_irreducible hirr
  have hfsep : f.Separable := (Polynomial.separable_iff_derivative_ne_zero hf).2 (by
    intro hzero
    have hPzero : P.derivative = 0 := Polynomial.map_injective
      (algebraMap (ringOfIntegers F) F)
      (IsFractionRing.injective (ringOfIntegers F) F) (by
        simpa only [f, Polynomial.derivative_map, Polynomial.map_zero] using hzero)
    exact ((Polynomial.separable_iff_derivative_ne_zero hirr).1 hg)
      (by simp only [Polynomial.derivative_map, hPzero, Polynomial.map_zero]))
  letI := ringOfIntegers_isIntegralClosure F L
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff
    (A := ringOfIntegers L) (R := ringOfIntegers F) (B := L)).1
    (show IsIntegral (ringOfIntegers F) x from ⟨P, hP, hx⟩)
  have hcomm : Q.map (residueMap L) = g.map (algebraMap (ResidueField F) (ResidueField L)) := by
    simp only [Q, g, Polynomial.map_map]
    rfl
  have hyroot : Q.eval y = 0 := by
    dsimp only [Q]
    rw [Polynomial.eval_map]
    change Polynomial.aeval y P = 0
    apply (IsIntegralClosure.algebraMap_injective
      (ringOfIntegers L) (ringOfIntegers F) L)
    simpa only [map_zero, ← Polynomial.aeval_algebraMap_apply, hy] using hx
  have hredroot : Polynomial.aeval (residueMap L y) g = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, ← hcomm,
      Polynomial.eval_map_apply, hyroot, map_zero]
  have hmin := minpoly.eq_of_irreducible_of_monic hirr hredroot (hP.map _)
  have hsplit : (g.map (algebraMap (ResidueField F) (ResidueField L))).Splits := by
    change ((P.map (residueMap F)).map _).Splits
    rw [hmin]
    exact Normal.splits inferInstance _
  have hlift (r : g.rootSet (ResidueField L)) :
      ∃ z : ringOfIntegers L, Q.eval z = 0 ∧ residueMap L z = (r : ResidueField L) := by
    apply lift_simple_residue_root L Q (hP.map _)
    · rw [hcomm, Polynomial.eval_map]
      change Polynomial.aeval (r : ResidueField L) g = 0
      exact (Polynomial.mem_rootSet.mp r.property).2
    · rw [hcomm]
      rw [Polynomial.derivative_map, Polynomial.eval_map]
      exact hg.aeval_derivative_ne_zero (Polynomial.mem_rootSet.mp r.property).2
  choose z hz hzres using hlift
  let lift : g.rootSet (ResidueField L) → f.rootSet L := fun r => ⟨(z r : L), by
    apply Polynomial.mem_rootSet.mpr
    refine ⟨hf.ne_zero, ?_⟩
    have h := congrArg (algebraMap (ringOfIntegers L) L) (hz r)
    dsimp only [Q] at h
    rw [Polynomial.eval_map, map_zero] at h
    change algebraMap (ringOfIntegers L) L (Polynomial.aeval (z r) P) = 0 at h
    rw [← Polynomial.aeval_algebraMap_apply] at h
    rw [show algebraMap (ringOfIntegers L) L (z r) = (z r : L) from
      congrFun (Algebra.coe_algebraMap_ofSubsemiring (ringOfIntegers L)) (z r)] at h
    simpa only [f, Polynomial.aeval_def, Polynomial.eval₂_map,
      ← IsScalarTower.algebraMap_eq] using h⟩
  have hinj : Function.Injective lift := by
    intro r s h
    apply Subtype.ext
    rw [← hzres r, ← hzres s]
    have hval : (z r : L) = (z s : L) := congrArg (fun a : f.rootSet L => (a : L)) h
    exact congrArg (residueMap L) (Subtype.ext hval)
  have hcard := Fintype.card_le_of_injective lift hinj
  rw [Polynomial.card_rootSet_eq_natDegree hg hsplit, hP.natDegree_map] at hcard
  have hfsplit : (f.map (algebraMap F L)).Splits := by
    apply Polynomial.splits_iff_card_roots.mpr
    apply le_antisymm (Polynomial.card_roots' _)
    simpa only [Polynomial.rootSet_def, Finset.coe_sort_coe, Fintype.card_coe,
      Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hfsep.map),
      Polynomial.natDegree_map, f, hP.natDegree_map] using hcard
  letI : f.IsSplittingField F L := ⟨hfsplit, by
    apply top_unique
    rw [← hgen]
    apply Algebra.adjoin_mono
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    apply Polynomial.mem_rootSet.mpr
    exact ⟨hf.ne_zero, by simpa only [f, Polynomial.aeval_def, Polynomial.eval₂_map,
      ← IsScalarTower.algebraMap_eq] using hx⟩⟩
  exact IsGalois.of_separable_splitting_field hfsep

/-- Construct a finite unramified extension of any positive degree, in both
field characteristics, by lifting a residue-field minimal polynomial. -/
theorem finiteUnramifiedExtension_exists
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) [NeZero n] :
    ∃ (L : Type) (_field : Field L) (_algebra : Algebra F L)
      (_v : ValuativeRel L) (_top : TopologicalSpace L)
      (_local : IsNonarchimedeanLocalField L) (_val : ValuativeExtension F L),
      Module.Finite F L ∧ Module.finrank F L = n ∧
        ramificationIndex F L = 1 ∧ residueDegree F L = n ∧ IsGalois F L := by
  obtain ⟨P, hmonic, hdegree, hred, hirr⟩ := irreducible_residue_lift_exists F n
  let f := P.map (algebraMap (ringOfIntegers F) F)
  letI : Fact (Irreducible f) := ⟨hirr⟩
  let L := AdjoinRoot f
  letI : Module.Finite F L := (hmonic.map _).finite_adjoinRoot
  obtain ⟨v, top, hlocal, hval⟩ := finiteExtension_localField_exists F L
  have hd : Module.finrank F L = P.natDegree := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
    exact hmonic.natDegree_map _
  have hroot : Polynomial.aeval (AdjoinRoot.root f) P = 0 := by
    rw [← Polynomial.aeval_map_algebraMap F]
    exact (AdjoinRoot.aeval_eq f).trans AdjoinRoot.mk_self
  have hu := unramified_of_irreducible_reduction F L P hmonic hred
    (AdjoinRoot.root f) hroot hd
  have hgal := galois_of_irreducible_reduction F L P hmonic hred
    (AdjoinRoot.root f) hroot (AdjoinRoot.powerBasis hirr.ne_zero).adjoin_gen_eq_top
  exact ⟨L, inferInstance, inferInstance, v, top, hlocal, hval, inferInstance,
    hd.trans hdegree, hu.1, hu.2.trans hdegree, hgal⟩

/-- Residue cardinalities in an unramified extension of degree at least
three meet exactly the absolute-degree hypothesis of polynomial rigidity. -/
theorem large_residue_of_unramified_degree
    (F L : Type*) [Field F] [Field L]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra F L] [ValuativeExtension F L] [Module.Finite F L]
    (hunr : ramificationIndex F L = 1) (hdegree : 3 ≤ Module.finrank F L) :
    ∃ r : ℕ, 3 ≤ r ∧ residueCard L = residueCharacteristic L ^ r := by
  letI := Fintype.ofFinite (ResidueField F)
  letI := Fintype.ofFinite (ResidueField L)
  obtain ⟨r, _, hr⟩ := FiniteField.card (ResidueField F) (residueCharacteristic F)
  have hf : residueDegree F L = Module.finrank F L := by
    simpa only [hunr, one_mul] using
      (finrank_eq_ramificationIndex_mul_residueDegree F L).symm
  refine ⟨r * Module.finrank F L, by have := r.pos; nlinarith, ?_⟩
  rw [residueCharacteristic_extension_eq F L, pow_mul]
  rw [residueCard, Fintype.card_eq_nat_card]
  rw [Module.natCard_eq_pow_finrank (K := ResidueField F),
    ← residueDegree_eq_finrank_residueField, hf]
  congr 1
  simpa only [Nat.card_eq_fintype_card] using hr

/-- Degree four enlarges either small residue field and is prime to every
odd residue characteristic. The local field and its unramified structure
are constructed, rather than assumed. -/
theorem primeToOdd_large_unramified_exists
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {p : ℕ} (hp : p.Prime) (hpodd : 2 < p) :
    ∃ (L : Type) (_field : Field L) (_algebra : Algebra F L)
      (_v : ValuativeRel L) (_top : TopologicalSpace L)
      (_local : IsNonarchimedeanLocalField L) (_val : ValuativeExtension F L),
      Module.Finite F L ∧ Module.finrank F L = 4 ∧ ramificationIndex F L = 1 ∧
        Nat.Coprime (Module.finrank F L) p ∧ IsGalois F L ∧
        ∃ r : ℕ, 3 ≤ r ∧ residueCard L = residueCharacteristic L ^ r := by
  obtain ⟨L, fld, alg, v, top, loc, val, fin, hd, he, _, hgal⟩ :=
    finiteUnramifiedExtension_exists F 4
  refine ⟨L, fld, alg, v, top, loc, val, fin, hd, he, ?_, hgal,
    large_residue_of_unramified_degree F L he (by omega)⟩
  rw [hd, show 4 = 2 ^ 2 by norm_num]
  exact ((Nat.coprime_two_left.mpr (hp.odd_of_ne_two (by omega))).pow_left 2)

/-- Integrality over the original valuation ring detects the upper
valuation ring. This lets one extend all embeddings in a compositum with
the same topology, rather than choosing incompatible valuations. -/
theorem mem_integers_iff_integral
    (F L : Type*) [Field F] [Field L]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra F L] [ValuativeExtension F L] [Module.Finite F L] (x : L) :
    x ∈ ringOfIntegers L ↔ IsIntegral (ringOfIntegers F) x := by
  letI := ringOfIntegers_isIntegralClosure F L
  rw [IsIntegralClosure.isIntegral_iff (A := ringOfIntegers L)]
  exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.property⟩

/-- Every embedding over a common local base respects the given valuations
on finite extensions. The assertion follows from integral closure. -/
theorem valuativeExtension_of_common_base
    (F E L : Type*) [Field F] [Field E] [Field L]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra F E] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
    [ValuativeExtension F E] [ValuativeExtension F L]
    [Module.Finite F E] [Module.Finite F L] : ValuativeExtension E L := by
  let f := IsScalarTower.toAlgHom (ringOfIntegers F) E L
  have hmap : (ValuativeRel.valuation L).integer.comap (algebraMap E L) =
      (ValuativeRel.valuation E).integer := by
    ext x
    change algebraMap E L x ∈ ringOfIntegers L ↔ x ∈ ringOfIntegers E
    rw [mem_integers_iff_integral F L, mem_integers_iff_integral F E]
    exact isIntegral_algHom_iff f (algebraMap E L).injective
  letI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation L) :=
    Valuation.HasExtension.ofComapInteger hmap
  refine ⟨fun x y => ?_⟩
  rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation L),
    Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation E)]
  exact Valuation.HasExtension.val_map_le_iff _ _ x y

open scoped TensorProduct

/-- Coprime field degrees make the actual tensor product a field. This
constructs the ambient compositum without a separate existence hypothesis. -/
theorem tensorProduct_isField_of_coprime
    (F E L : Type*) [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L]
    (hcop : Nat.Coprime (Module.finrank F E) (Module.finrank F L)) :
    IsField (E ⊗[F] L) := by
  apply IntermediateField.LinearDisjoint.isField_of_forall F E L
  intro M _ _ f g
  apply IntermediateField.LinearDisjoint.of_finrank_coprime
  simpa only [← f.equivFieldRange.toLinearEquiv.finrank_eq,
    ← g.equivFieldRange.toLinearEquiv.finrank_eq] using hcop

set_option backward.isDefEq.respectTransparency false in
/-- A finite local compositum for extensions of coprime degrees. All three
valuation embeddings and both scalar towers are constructed on the same
tensor-product field. -/
theorem localCompositum_exists
    (F E L : Type) [Field F] [Field E] [Field L]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra F E] [Algebra F L] [ValuativeExtension F E] [ValuativeExtension F L]
    [Module.Finite F E] [Module.Finite F L]
    (hcop : Nat.Coprime (Module.finrank F E) (Module.finrank F L)) :
    ∃ (M : Type) (_field : Field M) (_algF : Algebra F M)
      (_algE : Algebra E M) (_algL : Algebra L M)
      (_v : ValuativeRel M) (_top : TopologicalSpace M)
      (_local : IsNonarchimedeanLocalField M),
      ValuativeExtension F M ∧ ValuativeExtension E M ∧ ValuativeExtension L M ∧
      IsScalarTower F E M ∧ IsScalarTower F L M ∧
      Module.Finite F M ∧ Module.Finite E M ∧ Module.Finite L M ∧
      Module.finrank E M = Module.finrank F L ∧
      Module.finrank L M = Module.finrank F E ∧
      Algebra.adjoin E (Set.range (algebraMap L M)) = ⊤ := by
  let M := E ⊗[F] L
  letI : Field M := (tensorProduct_isField_of_coprime F E L hcop).toField
  letI : Algebra L M := Algebra.TensorProduct.rightAlgebra
  letI : IsScalarTower F L M := Algebra.TensorProduct.right_isScalarTower
  have hfin : Module.Finite F M := inferInstance
  letI := hfin
  letI : Module.Finite L M := Module.Finite.of_restrictScalars_finite F L M
  obtain ⟨v, top, hlocal, hval⟩ := finiteExtension_localField_exists F M
  letI : ValuativeExtension E M := valuativeExtension_of_common_base F E M
  letI : ValuativeExtension L M := valuativeExtension_of_common_base F L M
  have hdE : Module.finrank E M = Module.finrank F L := Module.finrank_baseChange
  have hdL : Module.finrank L M = Module.finrank F E := by
    have h₁ := Module.finrank_mul_finrank F E M
    have h₂ := Module.finrank_mul_finrank F L M
    have hpos : 0 < Module.finrank F L := Module.finrank_pos
    rw [hdE] at h₁
    nlinarith
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance,
    v, top, hlocal, hval, inferInstance, inferInstance, inferInstance,
    inferInstance, hfin, inferInstance, inferInstance, hdE, hdL, ?_⟩
  change Algebra.adjoin E (Set.range (fun x : L => (1 : E) ⊗ₜ[F] x)) = ⊤
  simpa only [Set.image_univ] using
    (Algebra.TensorProduct.adjoin_one_tmul_image_eq_top
      (R := F) (A := E) (Set.univ : Set L) (by simp))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The actual degree-four unramified square needed in the small-residue
case of `O:M:compat`. Both horizontal degrees, total ramification upstairs,
the original Galois group, and the large residue field are retained. -/
theorem largeUnramifiedSquare_exists
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime) (hpodd : 2 < p)
    (hdegree : Module.finrank F K = p ^ 2) (hres : residueDegree F K = 1) :
    ∃ (F' : Type) (_fieldF' : Field F') (_algF' : Algebra F F')
      (_vF' : ValuativeRel F') (_topF' : TopologicalSpace F')
      (_localF' : IsNonarchimedeanLocalField F') (_valF' : ValuativeExtension F F')
      (K' : Type) (_fieldK' : Field K') (_algFK' : Algebra F K')
      (_algKK' : Algebra K K') (_algF'K' : Algebra F' K')
      (_vK' : ValuativeRel K') (_topK' : TopologicalSpace K')
      (_localK' : IsNonarchimedeanLocalField K')
      (_valKK' : ValuativeExtension K K') (_valF'K' : ValuativeExtension F' K'),
      IsScalarTower F K K' ∧ IsScalarTower F F' K' ∧
      Module.Finite F F' ∧ Module.Finite F' K' ∧ Module.Finite K K' ∧
      Module.finrank F F' = 4 ∧ Module.finrank K K' = 4 ∧
      Nat.Coprime (Module.finrank F F') p ∧
      ramificationIndex F F' = 1 ∧ ramificationIndex K K' = 1 ∧
      residueDegree F' K' = 1 ∧
      Algebra.adjoin F' (Set.range (algebraMap K K')) = ⊤ ∧
      IsGalois F F' ∧ IsGalois F' K' ∧ Nonempty (Gal(K'/F') ≃* Gal(K/F)) ∧
      ∃ r : ℕ, 3 ≤ r ∧ residueCard F' = residueCharacteristic F' ^ r := by
  obtain ⟨F', fldF', algF', vF', topF', locF', valF', finF', hdF', huF', hcop, hgalF', hlarge⟩ :=
    primeToOdd_large_unramified_exists F hp hpodd
  have hcopK : Nat.Coprime (Module.finrank F F') (Module.finrank F K) := by
    rw [hdegree]
    exact hcop.pow_right 2
  obtain ⟨K', fldK', algFK', algF'K', algKK', vK', topK', locK',
      valFK', valF'K', valKK', towerF', towerK, finFK', finF'K', finKK',
      hdF'K', hdKK', hgen⟩ := localCompositum_exists F F' K hcopK
  have hinv := unramified_compositum_invariants F K F' K' hgen hres huF'
  letI : IsGalois F' K' := galois_square F K F' K' hgen
  let r := IntermediateField.restrictRestrictAlgEquivMapHom F K F' K'
  have hr : Function.Bijective r := by
    apply (Fintype.bijective_iff_injective_and_card r).2
    refine ⟨restriction_square_injective F K F' K' hgen, ?_⟩
    simpa only [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank] using hdF'K'
  exact ⟨F', fldF', algF', vF', topF', locF', valF',
    K', fldK', algFK', algKK', algF'K', vK', topK', locK', valKK', valF'K',
    towerK, towerF', finF', finF'K', finKK', hdF', hdKK'.trans hdF', hcop,
    huF', hinv.2.1, hinv.2.2, hgen, hgalF', inferInstance,
    ⟨MulEquiv.ofBijective r hr⟩, hlarge⟩

open private map_truncatedLog from LanglandsSecondMainLemma.Odd.NormLog

/-- The exact truncated logarithm of a finite product differs from the sum
by the original depth `p * q`, independently of the number of factors. -/
theorem truncatedLog_prod_sub_sum_mem
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {p q : ℕ} (hp : p.Prime)
    (hchar : residueCharacteristic E = p) (hq : 0 < q)
    {ι : Type*} (s : Finset ι) (u : ι → unitFiltration E q) :
    truncatedLog p (1 - (((∏ i ∈ s, u i : unitFiltration E q) : Eˣ) : E)) -
      ∑ i ∈ s, truncatedLog p (1 - (((u i) : Eˣ) : E)) ∈
        lattice E ((p * q : ℕ) : ℤ) := by
  classical
  have harg (v : unitFiltration E q) :
      1 - ((v : Eˣ) : E) ∈ lattice E (q : ℤ) := by
    simpa only [Submodule.coe_neg, coe_positiveUnitDisplacement, neg_sub] using
      (-positiveUnitDisplacement E hq v).property
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, OneMemClass.coe_one, Units.val_one, sub_self,
      Finset.sum_empty, sub_zero, mem_lattice]
    rw [ord_truncatedLog E p hchar (by simp), ord_zero]
    exact le_top
  | @insert i s hi ih =>
    have h := truncatedLog_defect_mem_lattice E p q hchar hp
      (harg (u i)) (harg (∏ j ∈ s, u j))
    have he (x y : E) : (1 - x) + (1 - y) - (1 - x) * (1 - y) = 1 - x * y := by
      ring
    rw [he] at h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    convert (lattice E ((p * q : ℕ) : ℤ)).add_mem h ih using 1
    simp only [Subgroup.coe_mul, Units.val_mul]
    ring

/-- Norm--log comparison along an unramified Galois extension of arbitrary
degree. The logarithm is truncated at the residue prime, not the extension
degree, so this applies to the prime-to-`p` extensions used for rigidity. -/
theorem unramifiedNormLog_of_isGalois
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L] [Module.Finite E L] [IsGalois E L]
    {p q : ℕ} (hp : p.Prime) (hchar : residueCharacteristic E = p)
    (hunr : ramificationIndex E L = 1) (hq : 0 < q)
    (z : L) (hz : z ∈ lattice L (q : ℤ)) :
    truncatedLog p (1 - norm E L (1 - z)) - trace E L (truncatedLog p z) ∈
      lattice E ((p * q : ℕ) : ℤ) := by
  let u (σ : Gal(L/E)) : unitFiltration L q :=
    positiveUnitOfLattice L hq (-⟨σ z,
      by simpa only [mem_lattice, ord_galoisConjugate] using hz⟩)
  have h := truncatedLog_prod_sub_sum_mem L hp
    ((residueCharacteristic_extension_eq E L).trans hchar) hq Finset.univ u
  have hu (σ : Gal(L/E)) : ((u σ : Lˣ) : L) = 1 - σ z := by
    simp only [u, coe_positiveUnitOfLattice, Submodule.coe_neg, sub_eq_add_neg]
  have hnorm : (((∏ σ : Gal(L/E), u σ : unitFiltration L q) : Lˣ) : L) =
      algebraMap E L (norm E L (1 - z)) := by
    simp only [SubmonoidClass.coe_finsetProd, Units.coe_prod, hu,
      Algebra.norm_eq_prod_automorphisms, map_sub, map_one]
  rw [hnorm] at h
  have htrace : ∑ σ : Gal(L/E), truncatedLog p (1 - (((u σ) : Lˣ) : L)) =
      algebraMap E L (trace E L (truncatedLog p z)) := by
    simp only [hu, sub_sub_cancel, trace_eq_sum_automorphisms]
    exact Finset.sum_congr rfl fun σ _ => (map_truncatedLog σ.toRingHom p z).symm
  rw [htrace, ← map_one (algebraMap E L), ← map_sub, ← map_truncatedLog,
    ← map_sub, mem_lattice, ord_algebraMap, hunr, one_nsmul] at h
  simpa only [map_one, mem_lattice] using h

/-- On the full original unit domain, pulling a model back by an unramified
norm gives exactly the trace-pulled model with the original coefficient.
The loss from that coefficient is an integer lattice exponent. -/
theorem modelNormCharacter_unramified_formula
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L] [Module.Finite E L] [IsGalois E L]
    {p q : ℕ} (hp : p.Prime) (hchar : residueCharacteristic E = p)
    (hunr : ramificationIndex E L = 1) (hq : 0 < q)
    (Psi : ContinuousAddChar E) (b : E) (v : ℤ) (hb : b ∈ lattice E v)
    (htriv : ∀ x ∈ lattice E (v + (p * q : ℕ)), Psi x = 1)
    (R : unitFiltration E q →* ℂˣ)
    (hR : ∀ u : unitFiltration E q,
      R u = Psi (b * truncatedLog p (1 - ((u : Eˣ) : E))))
    (u : unitFiltration L q) :
    modelNormCharacter E L R (fun _ hu => unramified_norm_mem_unitFiltration E L hunr q hu) u =
      Psi.compTrace (algebraMap E L b * truncatedLog p (1 - ((u : Lˣ) : L))) := by
  have hz : 1 - ((u : Lˣ) : L) ∈ lattice L (q : ℤ) := by
    simpa only [Submodule.coe_neg, coe_positiveUnitDisplacement, neg_sub] using
      (-positiveUnitDisplacement L hq u).property
  have hlog := unramifiedNormLog_of_isGalois E L hp hchar hunr hq _ hz
  simp only [sub_sub_cancel] at hlog
  have hphase := htriv _ (mul_mem_lattice E hb hlog)
  change Psi.toAddChar _ = 1 at hphase
  rw [mul_sub, AddChar.map_sub_eq_div] at hphase
  calc
    modelNormCharacter E L R (fun _ hu => unramified_norm_mem_unitFiltration E L hunr q hu) u =
        Psi (b * truncatedLog p (1 - norm E L ((u : Lˣ) : L))) := hR _
    _ = Psi (b * trace E L (truncatedLog p (1 - ((u : Lˣ) : L)))) :=
      div_eq_one.mp hphase
    _ = Psi.compTrace (algebraMap E L b * truncatedLog p (1 - ((u : Lˣ) : L))) := by
      rw [ContinuousAddChar.compTrace_apply]
      congr 1
      symm
      simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self_apply]
        using (trace E L).map_smul b (truncatedLog p (1 - ((u : Lˣ) : L)))

/-- The same compositum is generated in either order. This supplies the
Galois structure on the unramified sides of the induced squares. -/
theorem compositum_generation_symm
    (E L M : Type*) [Field E] [Field L] [Field M]
    [Algebra E M] [Algebra L M]
    (hgen : Algebra.adjoin E (Set.range (algebraMap L M)) = ⊤) :
    Algebra.adjoin L (Set.range (algebraMap E M)) = ⊤ := by
  let C := Algebra.adjoin L (Set.range (algebraMap E M))
  apply top_unique
  intro x htop
  clear htop
  have hx : x ∈ Algebra.adjoin E (Set.range (algebraMap L M)) := by
    rw [hgen]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    exact C.algebraMap_mem y
  | algebraMap x => exact Algebra.subset_adjoin (Set.mem_range_self x)
  | add x y _ _ hx hy => exact C.add_mem hx hy
  | mul x y _ _ hx hy => exact C.mul_mem hx hy

section UnramifiedPolynomial
variable (F E K F' E' K' : Type*)
  [Field F] [Field E] [Field K] [Field F'] [Field E'] [Field K']
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel F'] [TopologicalSpace F'] [IsNonarchimedeanLocalField F']
  [ValuativeRel E'] [TopologicalSpace E'] [IsNonarchimedeanLocalField E']
  [Algebra F E] [Algebra F F'] [Algebra F E'] [Algebra E E'] [Algebra F' E']
  [Algebra E K] [Algebra E K'] [Algebra K K'] [Algebra E' K'] [Algebra F' K']
  [IsScalarTower F E E'] [IsScalarTower F F' E']
  [IsScalarTower E K K'] [IsScalarTower E E' K'] [IsScalarTower F' E' K']
  [ValuativeExtension E E']
  [Module.Finite F E] [Module.Finite F F'] [Module.Finite F' E']
  [Module.Finite E E'] [Module.Finite E K] [Module.Finite E' K']
  [IsGalois F E] [IsGalois E K] [IsGalois E E']
  [IsModuleTopology F E] [IsModuleTopology E E'] [IsModuleTopology F F']

omit [ValuativeRel F'] [IsNonarchimedeanLocalField F'] [IsModuleTopology E E'] in
/-- The norm pullback of one original model is the trace phase of its
coefficientwise transported polynomial. Both original weights and the
residue-prime logarithm are preserved. -/
theorem modelNormCharacter_unramified_polynomial
    {p r : ℕ} (hp : p.Prime) (hchar : residueCharacteristic E = p)
    (hunr : ramificationIndex E E' = 1) (hr : 0 < r)
    (hgF : Algebra.adjoin F' (Set.range (algebraMap E E')) = ⊤)
    (hdF : Module.finrank F' E' = Module.finrank F E)
    (hgE : Algebra.adjoin E' (Set.range (algebraMap K K')) = ⊤)
    (hdE : Module.finrank E' K' = Module.finrank E K)
    (Psi : ContinuousAddChar F) (b : E) (v : ℤ) (hb : b ∈ lattice E v)
    (htriv : ∀ x ∈ lattice E (v + (p * r : ℕ)), tracePullbackAddChar F E Psi x = 1)
    (R : unitFiltration E r →* ℂˣ)
    (hR : ∀ u : unitFiltration E r,
      R u = tracePullbackAddChar F E Psi
        (b * truncatedLog p (1 - ((u : Eˣ) : E))))
    (z : K) (s : F') (u : K'ˣ)
    (hu : (u : K') = 1 - algebraMap F' K' s * algebraMap K K' z)
    (hNu : normUnits E' K' u ∈ unitFiltration E' r) :
    modelNormCharacter E E' R
        (fun _ h => unramified_norm_mem_unitFiltration E E' hunr r h)
        ⟨normUnits E' K' u, hNu⟩ =
      Psi.compTrace
        ((weightedTracePolynomial F E b (normLogPolynomial E K p z)).eval₂
          (algebraMap F F') s) := by
  letI : IsGalois E' K' := galois_square E K E' K' hgE
  rw [modelNormCharacter_unramified_formula E E' hp hchar hunr hr
    (tracePullbackAddChar F E Psi) b v hb htriv R hR]
  have hpoly := weightedTracePolynomial_algebraMap F E F' E' hgF hdF b
    (normLogPolynomial E K p z)
  rw [← normLogPolynomial_algebraMap E K E' K' hgE hdE] at hpoly
  rw [← Polynomial.eval_map, ← hpoly, weightedTracePolynomial_eval,
    normLogPolynomial_eval, ← IsScalarTower.algebraMap_apply F' E' K']
  simp only [ContinuousAddChar.compTrace_apply, tracePullbackAddChar_apply,
    coe_normUnits, hu, trace_trans]

end UnramifiedPolynomial

open private norm_tower_residueDegrees from
  LanglandsSecondMainLemma.Odd.Models.PolynomialCoefficients

set_option backward.isDefEq.respectTransparency false in
/-- Construct the induced intermediate field and both Galois structures,
then identify the original model's norm pullback on the whole scalar orbit.
The norm domain upstairs is the one proved by `domains`. -/
theorem modelNormCharacter_norm_baseChange
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
    (F' K' : Type) [Field F'] [Field K']
    [ValuativeRel F'] [TopologicalSpace F'] [IsNonarchimedeanLocalField F']
    [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
    [Algebra F F'] [Algebra F K'] [Algebra K K'] [Algebra F' K']
    [IsScalarTower F K K'] [IsScalarTower F F' K']
    [ValuativeExtension F F'] [ValuativeExtension K K'] [ValuativeExtension F' K']
    [Module.Finite F F'] [Module.Finite F' K'] [Module.Finite K K'] [IsGalois F F']
    {p q r : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (B : IntermediateField F K) (hB : Module.finrank F B = p)
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (hunr : ramificationIndex F F' = 1) (hunrK : ramificationIndex K K' = 1)
    (hgen : Algebra.adjoin F' (Set.range (algebraMap K K')) = ⊤) (hr : 0 < r) :
    letI := Basic.intermediateFieldValuativeRel B
    letI := Basic.intermediateFieldTopology B
    letI := Basic.intermediateField_localField B
    letI := Basic.intermediateField_lowerValuativeExtension B
    let B' := field B F' K'
    letI := Basic.intermediateFieldValuativeRel B'
    letI := Basic.intermediateFieldTopology B'
    letI := Basic.intermediateField_localField B'
    ∀ (Psi : ContinuousAddChar F) (b : B) (v : ℤ) (_hb : b ∈ lattice B v)
      (_htriv : ∀ x ∈ lattice B (v + (p * r : ℕ)), tracePullbackAddChar F B Psi x = 1)
      (R : unitFiltration B r →* ℂˣ)
      (_hR : ∀ u : unitFiltration B r,
        R u = tracePullbackAddChar F B Psi
          (b * truncatedLog p (1 - ((u : Bˣ) : B))))
      (hN : ∀ u : Kˣ, u ∈ unitFiltration K q → normUnits B K u ∈ unitFiltration B r)
      (_hN' : ∀ u : K'ˣ, u ∈ unitFiltration K' q → normUnits B' K' u ∈ unitFiltration B' r)
      (z : K) (s : F') (u : unitFiltration K' q),
      ((u : K'ˣ) : K') = 1 - algebraMap F' K' s * algebraMap K K' z →
      modelNormCharacter B K R hN
        ⟨normUnits K K' (u : K'ˣ), unramified_norm_mem_unitFiltration K K' hunrK q u.property⟩ =
        Psi.compTrace
          ((weightedTracePolynomial F B b (normLogPolynomial B K p z)).eval₂
            (algebraMap F F') s) := by
  dsimp only
  letI := Basic.intermediateFieldValuativeRel B
  letI := Basic.intermediateFieldTopology B
  letI := Basic.intermediateField_localField B
  letI := Basic.intermediateField_lowerValuativeExtension B
  letI := Basic.intermediateField_upperValuativeExtension B
  let data := Basic.intermediateField_tower_compatible hp hG B hB
  letI : PrimeCyclicExtension F B :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F B data.2.2.2.2.2.2.2.2.2.2.2.1
  letI : ValuativeExtension B K' := ⟨fun x y => by
    rw [IsScalarTower.algebraMap_apply B K K', IsScalarTower.algebraMap_apply B K K',
      ValuativeExtension.vle_iff_vle, ValuativeExtension.vle_iff_vle]⟩
  let B' := field B F' K'
  letI := Basic.intermediateFieldValuativeRel B'
  letI := Basic.intermediateFieldTopology B'
  letI := Basic.intermediateField_localField B'
  letI := Basic.intermediateField_lowerValuativeExtension B'
  letI := Basic.intermediateField_upperValuativeExtension B'
  letI := fieldValuativeExtension B F' K'
  letI : Module.Finite F B' := Module.Finite.trans (R := F) F' B'
  letI : Module.Finite B B' := Module.Finite.of_restrictScalars_finite F B B'
  obtain ⟨hrF, hrK⟩ := norm_tower_residueDegrees B hres
  have hgF := field_generation B F' K'
  have hgB := upper_generation B F' K' (Set.range (algebraMap K K')) hgen
  have hlower := unramified_compositum_invariants F B F' B' hgF hrF hunr
  have hupper := unramified_compositum_invariants B K B' K' hgB hrK hlower.2.1
  letI : IsGalois B B' := galois_square F F' B B'
    (compositum_generation_symm F' B B' hgF)
  intro Psi b v hb htriv R hR hN hN' z s u hu
  have hn : normUnits B B' (normUnits B' K' (u : K'ˣ)) =
      normUnits B K (normUnits K K' (u : K'ˣ)) := by
    apply Units.ext
    exact (norm_trans B B' K' _).trans (norm_trans B K K' _).symm
  calc
    modelNormCharacter B K R hN _ = modelNormCharacter B B' R
        (fun _ h => unramified_norm_mem_unitFiltration B B' hlower.2.1 r h)
        ⟨normUnits B' K' (u : K'ˣ), hN' u u.property⟩ := by
      change R _ = R _
      congr 1
      exact Subtype.ext hn.symm
    _ = _ := modelNormCharacter_unramified_polynomial F B K F' B' K'
      hp ((residueCharacteristic_extension_eq F B).trans hchar) hlower.2.1 hr
      hgF hlower.1 hgB hupper.1 Psi b v hb htriv R hR z s u hu (hN' u u.property)

end BaseChange

/-- Rigidity applied to the norm pullback of the original unit character.
Deeper triviality proves additivity upstairs; integral trace transfers the
coefficient order bounds, including the Teichmüller carries. -/
theorem unitCharacter_norm_rigidity
    (F K F' K' : Type*) [Field F] [Field K] [Field F'] [Field K']
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel F'] [TopologicalSpace F'] [IsNonarchimedeanLocalField F']
    [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
    [Algebra F F'] [Algebra K K'] [Algebra F' K']
    [ValuativeExtension F F'] [ValuativeExtension K K'] [ValuativeExtension F' K']
    [Module.Finite F F'] [Module.Finite K K']
    {p q T : ℕ} (hchar : residueCharacteristic F = p)
    (hunr : ramificationIndex F F' = 1) (hunrK : ramificationIndex K K' = 1)
    (hdegree : Nat.Coprime (Module.finrank F F') p)
    (habsolute : ∃ r : ℕ, 3 ≤ r ∧ residueCard F' = residueCharacteristic F' ^ r)
    (hq : 0 < q) (hlin : T ≤ 2 * q) (Xi : unitFiltration K q →* ℂˣ)
    (htriv : ∀ u : unitFiltration K q, (u : Kˣ) ∈ unitFiltration K T → Xi u = 1)
    (Psi : ContinuousAddChar F) (f : F[X]) (hf0 : f.coeff 0 = 0)
    (hdeg : f.natDegree < p ^ 2)
    (hcoeff : ∀ n : ℕ, ∀ x : ringOfIntegers F, Psi (f.coeff n * (x : F)) ^ p = 1)
    (z : lattice K' (q : ℤ))
    (hformula : ∀ x : ringOfIntegers F',
      Psi.compTrace (f.eval₂ (algebraMap F F') (x : F')) =
        modelNormCharacter K K' Xi
          (fun _ hu => unramified_norm_mem_unitFiltration K K' hunrK q hu)
          (positiveUnitOfLattice K' hq (-(integralScalarLattice F' K' z x)))) :
    Psi (f.eval 1) = Psi (f.coeff 1 + f.coeff p) := by
  let Xi' := modelNormCharacter K K' Xi
    (fun _ hu => unramified_norm_mem_unitFiltration K K' hunrK q hu)
  have htriv' (u : unitFiltration K' q) (hu : (u : K'ˣ) ∈ unitFiltration K' T) :
      Xi' u = 1 :=
    htriv _ (unramified_norm_mem_unitFiltration K K' hunrK T hu)
  have hcoeff' (n : ℕ) (x : ringOfIntegers F') :
      Psi.compTrace ((f.map (algebraMap F F')).coeff n * (x : F')) ^ p = 1 := by
    let y : ringOfIntegers F := ⟨trace F F' (x : F'),
      (mem_lattice_zero_iff F).1
        (trace_mem_lattice F F' hunr 0 ((mem_lattice_zero_iff F').2 x.property))⟩
    rw [Polynomial.coeff_map, ContinuousAddChar.compTrace_apply]
    have ht := (trace F F').map_smul (f.coeff n) (x : F')
    simp only [Algebra.smul_def, Algebra.algebraMap_self_apply] at ht
    rw [ht]
    exact hcoeff n y
  apply Finite.polynomialRigidity (M' := F') hchar Psi f hf0 hdeg
    (fun n _ x => hcoeff n x) hunr hdegree habsolute
  have hadd (x y : ringOfIntegers F') :
      Psi.compTrace ((f.map (algebraMap F F')).eval ((x + y : ringOfIntegers F') : F')) =
        Psi.compTrace ((f.map (algebraMap F F')).eval (x : F')) *
          Psi.compTrace ((f.map (algebraMap F F')).eval (y : F')) := by
    simp only [Polynomial.eval_map, hformula, map_add]
    exact unitCharacter_add K' hq hlin Xi' htriv' _ _
  simpa only [Polynomial.eval_map] using
    polynomialPhase_teichmuller_add F'
      ((residueCharacteristic_extension_eq F F').trans hchar)
      Psi.compTrace (f.map (algebraMap F F')) (fun n _ x => hcoeff' n x) hadd

section Induction
variable (F E₁ E₂ L : Type*) [Field F] [Field E₁] [Field E₂] [Field L]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E₁] [TopologicalSpace E₁] [IsNonarchimedeanLocalField E₁]
  [ValuativeRel E₂] [TopologicalSpace E₂] [IsNonarchimedeanLocalField E₂]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra F E₁] [Algebra F E₂] [Algebra E₁ L] [Algebra E₂ L]
  [IsModuleTopology F E₁] [IsModuleTopology F E₂]
  [Module.Free E₁ L] [Module.Finite E₁ L] [PrimeCyclicExtension E₁ L]
  [Module.Free E₂ L] [Module.Finite E₂ L] [PrimeCyclicExtension E₂ L]
  [ValuativeExtension E₁ L] [ValuativeExtension E₂ L]
  [Algebra F L]
  [IsScalarTower F E₁ L] [IsScalarTower F E₂ L]

/-- Descending induction for the actual discrepancy. The rigidity step and
monomial phases are discharged from the genuine diamond in `compatibility`.
Only the already proved deeper triviality enters each induction step. -/
theorem modelDiscrepancy_eq_one_of_monomial_coefficients
    {p q q₁ m₁ q₂ m₂ t₁ t₂ t : ℕ}
    (hp : p.Prime)
    (hd₁ : Module.finrank E₁ L = p) (hd₂ : Module.finrank E₂ L = p)
    (ht₁ : PrimeCyclicExtension.IsLowerBreak E₁ L t₁)
    (ht₂ : PrimeCyclicExtension.IsLowerBreak E₂ L t₂)
    (hr₁ : residueDegree E₁ L = 1) (hr₂ : residueDegree E₂ L = 1)
    (hq : 0 < q) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hram : ramificationIndex E₂ L = p)
    (pb : PowerBasis E₂ L) (hdim : pb.dim = p)
    (hDelta : ord L pb.gen = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ t)
    {Psi : ContinuousAddChar F} {b : E₁} {a : E₂}
    (M : OddMinimalCharacterModels E₁ E₂ p q₁ m₁ q₂ m₂
      (tracePullbackAddChar F E₁ Psi) (tracePullbackAddChar F E₂ Psi) b a)
    (hN₁ : ∀ u : Lˣ, u ∈ unitFiltration L q →
      normUnits E₁ L u ∈ unitFiltration E₁ q₁)
    (hN₂ : ∀ u : Lˣ, u ∈ unitFiltration L q →
      normUnits E₂ L u ∈ unitFiltration E₂ q₂)
    (hmono : ∀ (x : E₂) (j : Fin p),
      algebraMap E₂ L x * pb.gen ^ (j : ℕ) ∈ lattice L (q : ℤ) →
      let f := discrepancyPolynomial F E₁ E₂ L p b a
        (algebraMap E₂ L x * pb.gen ^ (j : ℕ))
      Psi (f.coeff 1 + f.coeff p) = 1)
    (hrigidity : ∀ (s : ℕ), q ≤ s →
      (∀ u : unitFiltration L q, (u : Lˣ) ∈ unitFiltration L (s + 1) →
        modelDiscrepancy F E₁ E₂ L M hN₁ hN₂ u = 1) →
      ∀ z : lattice L (s : ℤ),
        let f := discrepancyPolynomial F E₁ E₂ L p b a z
        Psi (f.eval 1) = Psi (f.coeff 1 + f.coeff p)) :
    modelDiscrepancy F E₁ E₂ L M hN₁ hN₂ = 1 := by
  classical
  let Xi := modelDiscrepancy F E₁ E₂ L M hN₁ hN₂
  let P : ℕ → Prop := fun s =>
    ∀ u : unitFiltration L q, (u : Lˣ) ∈ unitFiltration L s → Xi u = 1
  let B := max q (p * max m₁ m₂)
  have hbase : P B := by
    intro u hu
    exact modelDiscrepancy_trivial_deep F E₁ E₂ L hp.pos hd₁ hd₂ ht₁ ht₂
      hr₁ hr₂ hm₁ hm₂ M hN₁ hN₂ u
      (unitFiltration_antitone L (Nat.le_max_right _ _) hu)
  have hstep (s : ℕ) (_hsB : s < B) (hqs : q ≤ s) (ih : P (s + 1)) : P s := by
    have hs : 0 < s := hq.trans_le hqs
    have hlin : s + 1 ≤ 2 * s := by omega
    let Ns₁ : ∀ u : Lˣ, u ∈ unitFiltration L s →
        normUnits E₁ L u ∈ unitFiltration E₁ q₁ :=
      fun u hu => hN₁ u (unitFiltration_antitone L hqs hu)
    let Ns₂ : ∀ u : Lˣ, u ∈ unitFiltration L s →
        normUnits E₂ L u ∈ unitFiltration E₂ q₂ :=
      fun u hu => hN₂ u (unitFiltration_antitone L hqs hu)
    let XiS := modelDiscrepancy F E₁ E₂ L M Ns₁ Ns₂
    have hrestrict (v : unitFiltration L s) :
        XiS v = Xi ⟨(v : Lˣ), unitFiltration_antitone L hqs v.property⟩ := rfl
    have htrivS : ∀ v : unitFiltration L s,
        (v : Lˣ) ∈ unitFiltration L (s + 1) → XiS v = 1 := by
      intro v hv
      exact (hrestrict v).trans (ih _ hv)
    intro u hu
    let us : unitFiltration L s := ⟨(u : Lˣ), hu⟩
    let z : lattice L (s : ℤ) := -positiveUnitDisplacement L hs us
    obtain ⟨Y, hY, hYm⟩ := powerBasis_lattice_expansion E₂ L hp hram pb hdim
      hDelta hprime (s : ℤ) z
    let terms : Fin p → lattice L (s : ℤ) :=
      fun j => ⟨algebraMap E₂ L (Y j) * pb.gen ^ (j : ℕ), hYm j⟩
    have hsumz : z = ∑ j : Fin p, terms j := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum] using hY
    have hterm (j : Fin p) :
        XiS (positiveUnitOfLattice L hs (-(terms j))) = 1 := by
      have hjq : (terms j : L) ∈ lattice L (q : ℤ) :=
        lattice_antitone L (by exact_mod_cast hqs) (terms j).property
      have h := (modelDiscrepancy_polynomial F E₁ E₂ L hs M Ns₁ Ns₂ (terms j)).trans
        (hrigidity s hqs ih (terms j))
      exact h.trans (hmono (Y j) j hjq)
    have hsum := unitCharacter_sum L hs hlin XiS htrivS Finset.univ terms
    rw [← hsumz] at hsum
    have hv : XiS (positiveUnitOfLattice L hs (-z)) = 1 :=
      hsum.trans (Finset.prod_eq_one fun j _ => hterm j)
    have hunit : positiveUnitOfLattice L hs (-z) = us := by
      apply Subtype.ext
      apply Units.ext
      simp only [coe_positiveUnitOfLattice, z, Submodule.coe_neg,
        coe_positiveUnitDisplacement]
      ring
    rw [hunit] at hv
    exact (hrestrict us).symm.trans hv
  have hlast : P q := Nat.decreasingInduction' (P := P) (n := B) (m := q)
    hstep (Nat.le_max_left _ _) hbase
  apply MonoidHom.ext
  intro u
  exact hlast u u.property

end Induction

open private additiveConductor_of_normCharacterChart truncatedLogUnitCharacter_exists from
  LanglandsSecondMainLemma.Odd.Models.Setup
open private norm_tower_residueDegrees from
  LanglandsSecondMainLemma.Odd.Models.PolynomialCoefficients

section Compatibility

/-- The conductor kills the whole logarithm-error lattice after the coefficient loses depth `t`. -/
private theorem additiveConductor_trivial_logError
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {p q t T : ℕ}
    (chi : ContinuousAddChar E) (hchi : IsAdditiveConductor E chi (-(T : ℤ)))
    (hbound : t + T ≤ p * q) :
    ∀ x ∈ lattice E (-(t : ℤ) + (p * q : ℕ)), chi x = 1 := by
  intro x hx
  exact hchi.trivial x (lattice_antitone E (by push_cast; omega) hx)

-- Use the canonical intermediate-field structures throughout the assembly.
attribute [local instance] Basic.intermediateFieldValuativeRel
  Basic.intermediateFieldTopology Basic.intermediateField_localField
  Basic.intermediateField_lowerValuativeExtension Basic.intermediateField_upperValuativeExtension

section
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]
  {p : ℕ} {hp : p.Prime}
  {hG : Nonempty
    (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))}
  (D : Total.OddTotalBreakData (F := F) (K := K) hp hG)

local notation "B₁" => D.B₁
local notation "B₂" => D.B₂

/-- Construct both minimal models with the specified coefficients and exact conductors. -/
private theorem minimalModels_of_conductors
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (Delta : K) (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (a : B₂) (ha : ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (Psi : ContinuousAddChar F)
    (hPsi₁ : IsAdditiveConductor B₁ (tracePullbackAddChar F B₁ Psi) (-(D.tPrime + 1 : ℕ) : ℤ))
    (hPsi₂ : IsAdditiveConductor B₂ (tracePullbackAddChar F B₂ Psi) (-(D.t₂ + 1 : ℕ) : ℤ)) :
    Nonempty (OddMinimalCharacterModels B₁ B₂ p
      (firstModelDepth D) (firstModelConductor D) (secondModelDepth D) (secondModelConductor D)
      (tracePullbackAddChar F B₁ Psi) (tracePullbackAddChar F B₂ Psi) (norm B₁ K Delta) a) := by
  obtain ⟨hq, hq₂, hqt, hq₂t, _⟩ := domains_original D hres
  obtain ⟨_, hr₁⟩ := norm_tower_residueDegrees B₁ hres
  have hb : ord B₁ (norm B₁ K Delta) = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_norm, hr₁, one_nsmul, hDelta]
  have hm₁ : firstModelConductor D = D.t + (D.tPrime + 1) := by
    simp only [firstModelConductor]; omega
  have hm₂ : secondModelConductor D = D.t + (D.t₂ + 1) := by
    simp only [secondModelConductor]; omega
  obtain ⟨R₁, hR₁, hR₁cond⟩ := truncatedLogUnitCharacter_exists B₁ hp
    ((residueCharacteristic_extension_eq F B₁).trans hchar)
    D.t_pos (Nat.zero_lt_succ _) hm₁ hq
    (show firstModelDepth D ≤ firstModelConductor D - 1 by rw [hm₁]; omega)
    (show firstModelConductor D ≤ p * firstModelDepth D by
      exact le_smul_ceilDiv (b := firstModelConductor D) hp.pos)
    (norm B₁ K Delta) hb (tracePullbackAddChar F B₁ Psi) hPsi₁
  obtain ⟨R₂, hR₂, hR₂cond⟩ := truncatedLogUnitCharacter_exists B₂ hp
    ((residueCharacteristic_extension_eq F B₂).trans hchar)
    D.t_pos (Nat.zero_lt_succ _) hm₂ hq₂
    (show secondModelDepth D ≤ secondModelConductor D - 1 by rw [hm₂]; omega)
    (show secondModelConductor D ≤ p * secondModelDepth D by
      exact le_smul_ceilDiv (b := secondModelConductor D) hp.pos)
    a ha (tracePullbackAddChar F B₂ Psi) hPsi₂
  exact ⟨⟨R₁, R₂, hR₁, hR₂, hR₁cond, hR₂cond⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- At each induction depth, the constructed unramified square reduces the exact
polynomial phase to its surviving coefficients. Deeper triviality is the induction hypothesis. -/
private theorem modelDiscrepancy_rigidity
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (Delta : K) (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (a : B₂) (ha : ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hnorm : norm B₂ K Delta = a) (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-(D.t₂ + 1 : ℕ) : ℤ))
    (hPsi₁ : IsAdditiveConductor B₁ (tracePullbackAddChar F B₁ Psi) (-(D.tPrime + 1 : ℕ) : ℤ))
    (hPsi₂ : IsAdditiveConductor B₂ (tracePullbackAddChar F B₂ Psi) (-(D.t₂ + 1 : ℕ) : ℤ))
    (M : OddMinimalCharacterModels B₁ B₂ p
      (firstModelDepth D) (firstModelConductor D) (secondModelDepth D) (secondModelConductor D)
      (tracePullbackAddChar F B₁ Psi) (tracePullbackAddChar F B₂ Psi) (norm B₁ K Delta) a)
    (hN₁ : ∀ u : Kˣ, u ∈ unitFiltration K (firstModelDepth D) →
      normUnits B₁ K u ∈ unitFiltration B₁ (firstModelDepth D))
    (hN₂ : ∀ u : Kˣ, u ∈ unitFiltration K (firstModelDepth D) →
      normUnits B₂ K u ∈ unitFiltration B₂ (secondModelDepth D))
    (s : ℕ) (hqs : firstModelDepth D ≤ s)
    (ih : ∀ u : unitFiltration K (firstModelDepth D),
      (u : Kˣ) ∈ unitFiltration K (s + 1) → modelDiscrepancy F B₁ B₂ K M hN₁ hN₂ u = 1)
    (z : lattice K (s : ℤ)) :
    let f := discrepancyPolynomial F B₁ B₂ K p (norm B₁ K Delta) a z
    Psi (f.eval 1) = Psi (f.coeff 1 + f.coeff p) := by
  classical
  obtain ⟨_, _, _, _, _, _, _, _, hdFK, _, hd₁, _⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hd₂, _⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
  obtain ⟨hq, hq₂, _⟩ := domains_original D hres
  have hb : ord B₁ (norm B₁ K Delta) = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_norm, (norm_tower_residueDegrees B₁ hres).2, one_nsmul, hDelta]
  obtain ⟨F', fldF', algF', vF', topF', locF', valF',
      K', fldK', algFK', algKK', algF'K', vK', topK', locK', valKK', valF'K',
      towerK, towerF', finF', finF'K', finKK', _, _, hcop, huF', huK', _, hgen',
      hgalF', _, _, hlarge⟩ :=
    BaseChange.largeUnramifiedSquare_exists F K hp D.odd_prime
      (by simpa only [pow_two] using hdFK) hres
  let B₁' := BaseChange.field B₁ F' K'
  let B₂' := BaseChange.field B₂ F' K'
  obtain ⟨_, _, _, _, _, _, hpre', hmap'⟩ := (domains F' K' D hres huF' hgen').2.1
  have hN₁' : ∀ u : K'ˣ, u ∈ unitFiltration K' (firstModelDepth D) →
      normUnits B₁' K' u ∈ unitFiltration B₁' (firstModelDepth D) :=
    fun u hu => show u ∈ (unitFiltration B₁' (firstModelDepth D)).comap (normUnits B₁' K') from
      hpre'.symm ▸ hu
  have hN₂' : ∀ u : K'ˣ, u ∈ unitFiltration K' (firstModelDepth D) →
      normUnits B₂' K' u ∈ unitFiltration B₂' (secondModelDepth D) :=
    fun u hu => hmap' ⟨u, hu, rfl⟩
  have htriv₁ := additiveConductor_trivial_logError (tracePullbackAddChar F B₁ Psi) hPsi₁
    (show D.t + (D.tPrime + 1) ≤ p * firstModelDepth D by
      have hceil : firstModelConductor D ≤ p * firstModelDepth D := le_smul_ceilDiv hp.pos
      simpa only [firstModelConductor, Nat.add_left_comm, Nat.add_comm] using hceil)
  have htriv₂ := additiveConductor_trivial_logError (tracePullbackAddChar F B₂ Psi) hPsi₂
    (show D.t + (D.t₂ + 1) ≤ p * secondModelDepth D by
      have hceil : secondModelConductor D ≤ p * secondModelDepth D := le_smul_ceilDiv hp.pos
      simpa only [secondModelConductor, Nat.add_left_comm, Nat.add_comm] using hceil)
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
    (by
      obtain ⟨hdegree, hlt⟩ :=
        discrepancyPolynomial_degree F B₁ B₂ K hp.two_le hd₁ hd₂ (norm B₁ K Delta) a z
      exact hdegree.trans_lt hlt)
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

end

set_option backward.isDefEq.respectTransparency false in
/-- Paper `O:M:compat`: construct the minimal models and prove compatibility
on the full unit domain for every odd residue prime, in both field
characteristics. Unramified norm pullback supplies rigidity without an
absolute residue-degree restriction or an assumed character comparison. -/
theorem compatibility
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (D : Total.OddTotalBreakData (F := F) (K := K) hp hG) :
    let B₁ := D.B₁
    let B₂ := D.B₂
    letI := Basic.intermediateFieldValuativeRel B₁
    letI := Basic.intermediateFieldTopology B₁
    letI := Basic.intermediateField_localField B₁
    letI := Basic.intermediateField_lowerValuativeExtension B₁
    letI := Basic.intermediateFieldValuativeRel B₂
    letI := Basic.intermediateFieldTopology B₂
    letI := Basic.intermediateField_localField B₂
    letI := Basic.intermediateField_lowerValuativeExtension B₂
    ∃ (Delta : K) (a : B₂),
      Delta ^ p - Delta = algebraMap B₂ K a ∧
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ¬ p ∣ D.t ∧ Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ ∧
      norm B₂ K Delta = a ∧
      ∀ (c : ℕ) (_hc : c = (D.t₂ + 1) ⌈/⌉ p) (hcpos : 0 < c)
        (tau : NormCharacter F B₂) (_htau : tau ≠ 1)
        (Psi : ContinuousAddChar F),
        (∀ z : lattice F (c : ℤ),
          tau.1 (positiveUnitOfLattice F hcpos (-z)) =
            Psi (truncatedLog p (z : F))) →
        ∃ M : OddMinimalCharacterModels B₁ B₂ p
            (firstModelDepth D) (firstModelConductor D)
            (secondModelDepth D) (secondModelConductor D)
            (tracePullbackAddChar F B₁ Psi) (tracePullbackAddChar F B₂ Psi)
            (norm B₁ K Delta) a,
          ∀ (u : Kˣ), u ∈ unitFiltration K (firstModelDepth D) →
            ∃ h₁ : normUnits B₁ K u ∈ unitFiltration B₁ (firstModelDepth D),
            ∃ h₂ : normUnits B₂ K u ∈ unitFiltration B₂ (secondModelDepth D),
              M.R₁ ⟨normUnits B₁ K u, h₁⟩ = M.R₂ ⟨normUnits B₂ K u, h₂⟩ := by
  dsimp only
  let B₁ := D.B₁
  let B₂ := D.B₂
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hd₁, _, hcyc₁⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hd₂, hcycF₂, hcyc₂⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
  letI : PrimeCyclicExtension B₁ K := PrimeCyclicExtension.ofCyclicPrimeExtension B₁ K
    hcyc₁
  letI : PrimeCyclicExtension F B₂ := PrimeCyclicExtension.ofCyclicPrimeExtension F B₂
    hcycF₂
  letI : PrimeCyclicExtension B₂ K := PrimeCyclicExtension.ofCyclicPrimeExtension B₂ K
    hcyc₂
  obtain ⟨_, hr₁⟩ := norm_tower_residueDegrees B₁ hres
  obtain ⟨hrF₂, hr₂⟩ := norm_tower_residueDegrees B₂ hres
  have hram : ramificationIndex B₂ K = p := by
    simpa only [hd₂, hr₂, mul_one] using
      (finrank_eq_ramificationIndex_mul_residueDegree B₂ K).symm
  obtain ⟨hq, _, _, _, _, _, hpre, hmap⟩ := domains_original D hres
  have hN₁ : ∀ u : Kˣ, u ∈ unitFiltration K (firstModelDepth D) →
      normUnits B₁ K u ∈ unitFiltration B₁ (firstModelDepth D) :=
    fun u hu => show u ∈ (unitFiltration B₁ (firstModelDepth D)).comap (normUnits B₁ K) from
      hpre.symm ▸ hu
  have hN₂ : ∀ u : Kˣ, u ∈ unitFiltration K (firstModelDepth D) →
      normUnits B₂ K u ∈ unitFiltration B₂ (secondModelDepth D) :=
    fun u hu => hmap ⟨u, hu, rfl⟩
  obtain ⟨Delta, a, hroot, hDelta, ha, hprime, hgen, hnorm, hmono⟩ :=
    monomialPhase hp hG hres hchar D
  refine ⟨Delta, a, hroot, hDelta, ha, hprime, hgen, hnorm, ?_⟩
  intro c hc hcpos tau htau Psi hchart
  have hPsi := additiveConductor_of_normCharacterChart F B₂ hp D.odd_prime hchar
    D.degree_B₂ D.B₂_breaks.1 (D.t_pos.trans_le D.t_le_t₂) hrF₂
    hc hcpos tau htau Psi hchart
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hPsi₁, hPsi₂, _⟩ :=
    oddMinimalCharacters_onUnits hp hG hres hchar D c hc hcpos tau htau Psi hchart
  obtain ⟨M⟩ := minimalModels_of_conductors D hres hchar Delta hDelta a ha Psi hPsi₁ hPsi₂
  let pb : PowerBasis B₂ K :=
    PowerBasis.ofAdjoinEqTop (IsAlgebraic.of_finite B₂ Delta).isIntegral hgen
  have hpbgen : pb.gen = Delta := PowerBasis.ofAdjoinEqTop_gen _ _
  have hpbdim : pb.dim = p := by rw [← pb.finrank]; exact hd₂
  have hXi : modelDiscrepancy F B₁ B₂ K M hN₁ hN₂ = 1 := by
    apply modelDiscrepancy_eq_one_of_monomial_coefficients F B₁ B₂ K hp
      hd₁ hd₂ D.B₁_breaks.2 D.B₂_breaks.2 hr₁ hr₂ hq
      (by simp only [firstModelConductor]; omega) (by simp only [secondModelConductor]; omega)
      hram pb hpbdim (by simpa only [hpbgen] using hDelta) hprime M hN₁ hN₂
    · intro x j hj
      have hj' : algebraMap B₂ K x * Delta ^ (j : ℕ) ∈
          lattice K (firstModelDepth D : ℤ) := by simpa only [hpbgen] using hj
      have h := discrepancyPolynomial_coeff_phase hp hG hres hchar D Delta hDelta
        Psi hPsi (algebraMap B₂ K x * Delta ^ (j : ℕ)) hj'
      dsimp only at h
      rw [hnorm] at h
      have hm := hmono c hc hcpos tau htau Psi hchart x (j : ℕ) j.isLt hj'
      simpa only [hpbgen] using h.trans hm
    · exact modelDiscrepancy_rigidity D hres hchar Delta hDelta a ha hnorm Psi
        hPsi hPsi₁ hPsi₂ M hN₁ hN₂
  refine ⟨M, ?_⟩
  intro u hu
  refine ⟨hN₁ u hu, hN₂ u hu, ?_⟩
  apply div_eq_one.mp
  have h := DFunLike.congr_fun hXi (⟨u, hu⟩ : unitFiltration K (firstModelDepth D))
  simpa only [modelDiscrepancy_apply, MonoidHom.one_apply] using h

end Compatibility

end
end LanglandsSecondMainLemma.Odd.Models
