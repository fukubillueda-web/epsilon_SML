import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.LocalField.Lattices
import LanglandsFirstMainLemma.LocalField.MonogenicUniformizer
import LanglandsFirstMainLemma.LocalField.Valuation
import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Ramification.DiamondBreaks
import LanglandsSecondMainLemma.Basic.Characters
import LanglandsSecondMainLemma.Odd.EnhancedStationary

/-!
# Odd / UR / Setup

This file constructs the data at the start of the odd, unramified--ramified
branch.  The unramified lower field is the inertia fixed field `U`; a supplied
order-`p` line distinct from inertia has fixed field `E`.  The exported setup
contains the common positive lower break, `T = t + 1`, `q0 = ceil(T / p)`, a
nontrivial actual norm character for `E/F` of conductor `T`, its normalized
logarithm coefficient for every nontrivial continuous additive character,
and integral Artin--Schreier data `d ^ p - d = c` generating `U/F`.

The logarithm coefficient `alpha` is nonzero, has order `-n(psiF)-T`, and
realizes the full `tauF(1-z) = psiF(alpha * P(z))` chart on the integer
lattice of depth `q0`.  It is constructed from the actual `tauF` using the
accepted logarithm quotient isomorphism and finite additive duality, via
`enhancedCoefficient_exists_unique_mod`; no chart is assumed.

The separate Artin--Schreier coefficient `c` is normalized by absolute residue trace one.  Its exact
lifted equation is proved with Hensel--Newton, in both equal and mixed
characteristic; it is not imposed as an extra hypothesis.  The four norm and
trace abbreviations below keep the paper's lower and upper field domains
visible.

Paper: corrected setup in lines 1060--1128, `O:I:tauchart` in lines
1204--1222, and the Artin--Schreier construction in lines 1298--1316 of `references/epsilon_SML.tex`.
-/

namespace LanglandsSecondMainLemma.Odd.UR

noncomputable section

open LanglandsFirstMainLemma
open Polynomial

/-! ## The two lower fields and the four norm/trace domains -/

/-- The unramified lower field `U`, defined as the inertia fixed field. -/
noncomputable abbrev UnramifiedField
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Finite F K] [IsGalois F K] : IntermediateField F K :=
  IntermediateField.fixedField
    (Ramification.inertiaSubgroup (F := F) (K := K))

/-- The ramified lower field `E` attached to the supplied Galois line `H`. -/
noncomputable abbrev RamifiedField
    (F K : Type) [Field F] [Field K] [Algebra F K]
    (H : Subgroup Gal(K/F)) : IntermediateField F K :=
  IntermediateField.fixedField H

/-- The paper's `n_E : E → F`. -/
noncomputable abbrev lowerRamifiedNorm
    (F K : Type) [Field F] [Field K] [Algebra F K]
    (H : Subgroup Gal(K/F)) : RamifiedField F K H →* F :=
  norm F (RamifiedField F K H)

/-- The lower trace `Tr_{E/F} : E → F`. -/
noncomputable abbrev lowerRamifiedTrace
    (F K : Type) [Field F] [Field K] [Algebra F K]
    (H : Subgroup Gal(K/F)) : RamifiedField F K H →ₗ[F] F :=
  trace F (RamifiedField F K H)

/-- The paper's `N_E : K → E`; this edge is unramified. -/
noncomputable abbrev upperUnramifiedNorm
    (F K : Type) [Field F] [Field K] [Algebra F K]
    (H : Subgroup Gal(K/F)) : K →* RamifiedField F K H :=
  norm (RamifiedField F K H) K

/-- The upper trace `Tr_{K/E} : K → E`; this edge is unramified. -/
noncomputable abbrev upperUnramifiedTrace
    (F K : Type) [Field F] [Field K] [Algebra F K]
    (H : Subgroup Gal(K/F)) : K →ₗ[RamifiedField F K H] RamifiedField F K H :=
  trace (RamifiedField F K H) K

/-- The paper's `n_U : U → F`. -/
noncomputable abbrev lowerUnramifiedNorm
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Finite F K] [IsGalois F K] : UnramifiedField F K →* F :=
  norm F (UnramifiedField F K)

/-- The lower trace `Tr_{U/F} : U → F`. -/
noncomputable abbrev lowerUnramifiedTrace
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Finite F K] [IsGalois F K] : UnramifiedField F K →ₗ[F] F :=
  trace F (UnramifiedField F K)

/-- The paper's `N_U : K → U`; this edge is totally ramified. -/
noncomputable abbrev upperRamifiedNorm
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Finite F K] [IsGalois F K] : K →* UnramifiedField F K :=
  norm (UnramifiedField F K) K

/-- The upper trace `Tr_{K/U} : K → U`; this edge is totally ramified. -/
noncomputable abbrev upperRamifiedTrace
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Finite F K] [IsGalois F K] :
    K →ₗ[UnramifiedField F K] UnramifiedField F K :=
  trace (UnramifiedField F K) K

/-! ## Actual character and Artin--Schreier data -/

/-- The valuation ring of the actual inertia fixed field `U`. -/
noncomputable abbrev UnramifiedIntegers
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Finite F K] [IsGalois F K] :=
  let U := UnramifiedField F K
  letI : ValuativeRel U := Basic.intermediateFieldValuativeRel U
  ringOfIntegers U

/-- The actual FML norm-character type for the ramified edge `E/F`.

Thus its elements are continuous group homomorphisms on `Fˣ` which are
trivial on every value of `lowerRamifiedNorm F K H`. -/
noncomputable abbrev RamifiedNormCharacter
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (H : Subgroup Gal(K/F)) :=
  let E := RamifiedField F K H
  letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E
  letI : TopologicalSpace E := Basic.intermediateFieldTopology E
  letI : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E
  letI : ValuativeExtension F E :=
    Basic.intermediateField_lowerValuativeExtension E
  letI : Module.Free F E := Module.Free.of_divisionRing F E
  letI : Module.Finite F E := inferInstance
  NormCharacter F E

/-- Conductor predicate for a character on the actual ramified lower edge. -/
def HasRamifiedConductor
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (H : Subgroup Gal(K/F)) (tau : RamifiedNormCharacter F K H)
    (T : ℕ) : Prop := by
  let E := RamifiedField F K H
  letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E
  letI : TopologicalSpace E := Basic.intermediateFieldTopology E
  letI : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E
  letI : ValuativeExtension F E :=
    Basic.intermediateField_lowerValuativeExtension E
  letI : Module.Free F E := Module.Free.of_divisionRing F E
  letI : Module.Finite F E := inferInstance
  exact IsMultiplicativeConductor F tau.1 T

/-- The coefficient `c` has absolute residue trace one. -/
def IsNormalizedArtinSchreierCoefficient
    (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (p : ℕ) (hchar : residueCharacteristic F = p)
    (c : ringOfIntegers F) : Prop := by
  letI : CharP (ResidueField F) p := by
    rw [← hchar]
    infer_instance
  letI : Algebra (ZMod p) (ResidueField F) :=
    ZMod.algebra (ResidueField F) p
  exact Algebra.trace (ZMod p) (ResidueField F) (residueMap F c) = 1

/-- Exact integral Artin--Schreier data for the unramified lower field.

Besides the lifted equation, the residue equation and the generation
statement are retained so later arguments do not have to infer either from a
chosen representative. -/
def IsUnramifiedArtinSchreierGenerator
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Finite F K] [IsGalois F K]
    (p : ℕ) (hchar : residueCharacteristic F = p)
    (c : ringOfIntegers F) (d : UnramifiedIntegers F K) : Prop := by
  let U := UnramifiedField F K
  letI : ValuativeRel U := Basic.intermediateFieldValuativeRel U
  letI : TopologicalSpace U := Basic.intermediateFieldTopology U
  letI : IsNonarchimedeanLocalField U := Basic.intermediateField_localField U
  letI : ValuativeExtension F U :=
    Basic.intermediateField_lowerValuativeExtension U
  exact IsNormalizedArtinSchreierCoefficient F p hchar c ∧
    residueMap U d ^ p - residueMap U d =
      extensionResidueMap F U (residueMap F c) ∧
    (d : U) ^ p - (d : U) = algebraMap F U (c : F) ∧
    IntermediateField.adjoin F {(d : U)} = ⊤

/-! ## The normalized coefficient of the actual norm character -/

-- The logarithm quotient must see the predecessor of the exact conductor.
-- These bounds also cover `t = 1` and require no condition on `p ∣ t`.
private theorem normCharacterChart_depths {p t : ℕ}
    (hp : p.Prime) (ht : 0 < t) :
    0 < (t + 1) ⌈/⌉ p ∧ (t + 1) ⌈/⌉ p ≤ t ∧
      t + 1 ≤ p * ((t + 1) ⌈/⌉ p) := by
  have hcover : t + 1 ≤ p * ((t + 1) ⌈/⌉ p) := le_smul_ceilDiv hp.pos
  refine ⟨?_, ?_, hcover⟩
  · by_contra h
    have hz : (t + 1) ⌈/⌉ p = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, mul_zero] at hcover
    omega
  · rw [ceilDiv_le_iff_le_mul hp.pos]
    calc
      t + 1 ≤ 2 * t := by omega
      _ ≤ p * t := Nat.mul_le_mul_right t hp.two_le


private theorem normalizedNormCharacterCoefficient_exists
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {p t : ℕ} (hp : p.Prime) (ht : 0 < t)
    (hchar : residueCharacteristic F = p)
    (tau : ContinuousQuasiChar F)
    (htau : IsMultiplicativeConductor F tau (t + 1))
    (psiF : ContinuousAddChar F) (hpsiF : psiF ≠ 1) :
    ∃ alpha : Fˣ,
      ord F (alpha : F) =
        ((-(canonicalLocalAddCharData F psiF hpsiF).conductor -
          ((t + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) ∧
      ∀ z : lattice F (((t + 1) ⌈/⌉ p : ℕ) : ℤ),
        tau (positiveUnitOfLattice F (normCharacterChart_depths hp ht).1 (-z)) =
          psiF ((alpha : F) * truncatedLog p (z : F)) := by
  let theta : LocalQuasiCharData F := ⟨tau, t + 1, htau⟩
  let psi := canonicalLocalAddCharData F psiF hpsiF
  obtain ⟨hqpos, hqt, hcover⟩ := normCharacterChart_depths hp ht
  obtain ⟨alpha, halpha, _⟩ := enhancedCoefficient_exists_unique_mod F theta psi
    p ((t + 1) ⌈/⌉ p) (-psi.conductor) hchar hp hqpos
    (Nat.le_succ_of_le hqt) hcover rfl (by change 1 < t + 1; omega)
    (Nat.add_le_add_right hqt 1)
  exact ⟨alpha, halpha⟩


/-- Proof-bearing initial data for the odd unramified--ramified branch.

The normalized coefficient is constructed for every nontrivial continuous
additive character.  Its type `Fˣ` retains nonzeroness, and both its order
and its full chart are assertions about the actual `tauF` below. -/
structure OddURSetup
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hI : Nat.card (Ramification.inertiaSubgroup (F := F) (K := K)) = p)
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p)
    (hne : H ≠ Ramification.inertiaSubgroup)
    (hchar : residueCharacteristic F = p) where
  odd_prime : 2 < p
  t : ℕ
  t_pos : 0 < t
  T : ℕ
  T_eq : T = t + 1
  q0 : ℕ
  q0_eq : q0 = T ⌈/⌉ p
  q0_pos : 0 < q0
  breaks : Ramification.UnramifiedBaseChangeBreakPair hp hG hI H hH t
  tauF : RamifiedNormCharacter F K H
  tauF_ne_one : tauF ≠ 1
  tauF_conductor : HasRamifiedConductor F K H tauF T
  normalizedCoefficient : ∀ (psiF : ContinuousAddChar F) (hpsiF : psiF ≠ 1),
    ∃ alpha : Fˣ,
      ord F (alpha : F) =
        ((-(canonicalLocalAddCharData F psiF hpsiF).conductor -
          (T : ℤ) : ℤ) : WithTop ℤ) ∧
      ∀ z : lattice F (q0 : ℤ),
        tauF.1 (positiveUnitOfLattice F q0_pos (-z)) =
          psiF ((alpha : F) * truncatedLog p (z : F))
  c : ringOfIntegers F
  d : UnramifiedIntegers F K
  artinSchreier : IsUnramifiedArtinSchreierGenerator F K p hchar c d

/-! ## Construction of the unramified generator -/

private theorem exists_unramifiedArtinSchreierGenerator
    {F U : Type*} [Field F] [Field U]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
    [Algebra F U] [ValuativeExtension F U]
    [Module.Free F U] [Module.Finite F U]
    {p : ℕ} (hp : p.Prime) (hchar : residueCharacteristic F = p)
    (hunr : ramificationIndex F U = 1)
    (hres : residueDegree F U = p) :
    ∃ (c : ringOfIntegers F) (d : ringOfIntegers U),
      IsNormalizedArtinSchreierCoefficient F p hchar c ∧
      residueMap U d ^ p - residueMap U d =
        extensionResidueMap F U (residueMap F c) ∧
      (d : U) ^ p - (d : U) = algebraMap F U (c : F) ∧
      IntermediateField.adjoin F {(d : U)} = ⊤ := by
  let k := ResidueField F
  let kappa := ResidueField U
  letI : Fact p.Prime := ⟨hp⟩
  letI : CharP k p := by
    rw [← hchar]
    infer_instance
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI : CharP kappa p :=
    (RingHom.charP_iff (algebraMap k kappa)
      (algebraMap k kappa).injective p).mp inferInstance
  letI : Algebra (ZMod p) kappa :=
    ((algebraMap k kappa).comp (algebraMap (ZMod p) k)).toAlgebra
  letI : IsScalarTower (ZMod p) k kappa := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Free k kappa := Module.Free.of_divisionRing k kappa
  have hdegResidue : Module.finrank k kappa = p := by
    simpa only [k, kappa] using
      (residueDegree_eq_finrank_residueField F U).symm.trans hres
  obtain ⟨cbar, hcbar⟩ :=
    (Algebra.trace_surjective (ZMod p) k) (1 : ZMod p)
  have htraceKappa :
      Algebra.trace (ZMod p) kappa (algebraMap k kappa cbar) = 0 := by
    rw [← Algebra.trace_trace (R := ZMod p) (S := k)
        (x := algebraMap k kappa cbar),
      Algebra.trace_algebraMap, hdegResidue]
    simp
  have hmem : algebraMap k kappa cbar ∈
      ((Algebra.trace (ZMod p) kappa).ker : Set kappa) := htraceKappa
  rw [← finiteField_frobeniusSub_range_eq_traceKer kappa p
    (ringChar.eq kappa p)] at hmem
  obtain ⟨dbar, hdbar⟩ := hmem
  have hdbar_not_base : dbar ∉ (⊥ : IntermediateField k kappa) := by
    rw [IntermediateField.mem_bot]
    rintro ⟨x, hx⟩
    have has : x ^ p - x = cbar := by
      apply (algebraMap k kappa).injective
      simpa only [map_sub, map_pow, hx] using hdbar
    have htracezero : Algebra.trace (ZMod p) k (x ^ p - x) = 0 := by
      have hxmem : x ^ p - x ∈
          ((Algebra.trace (ZMod p) k).ker : Set k) := by
        rw [← finiteField_frobeniusSub_range_eq_traceKer k p (ringChar.eq k p)]
        exact ⟨x, rfl⟩
      exact hxmem
    rw [has, hcbar] at htracezero
    exact one_ne_zero htracezero
  obtain ⟨c, hc⟩ := residueMap_surjective F cbar
  let d0 : ringOfIntegers U := teichmuller U dbar
  let cU : ringOfIntegers U :=
    algebraMap (ringOfIntegers F) (ringOfIntegers U) c
  let P : (ringOfIntegers U)[X] := X ^ p - X - C cU
  have hPred : residueMap U (P.eval d0) = 0 := by
    dsimp only [P]
    rw [Polynomial.eval_sub, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    dsimp only [d0]
    rw [map_sub, map_sub, map_pow, residueMap_teichmuller]
    rw [show residueMap U
        (algebraMap (ringOfIntegers F) (ringOfIntegers U) c) =
          extensionResidueMap F U (residueMap F c) from rfl,
      hc, ← hdbar]
    ring
  have hPpos : (0 : WithTop ℤ) < ord U ((P.eval d0 : ringOfIntegers U) : U) := by
    apply (ord_pos_iff_mem_maximalIdeal U (P.eval d0)).2
    exact (IsLocalRing.residue_eq_zero_iff (P.eval d0)).1 hPred
  have hderivred : residueMap U (P.derivative.eval d0) = -1 := by
    rw [← Polynomial.eval_map_apply, ← Polynomial.derivative_map]
    simp only [P, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_C, sub_zero]
    rw [Polynomial.derivative_X_pow]
    simp
  have hderivord :
      ord U ((P.derivative.eval d0 : ringOfIntegers U) : U) =
        (0 : WithTop ℤ) := by
    apply le_antisymm
    · apply le_of_not_gt
      intro hpos
      have hmem' :=
        (ord_pos_iff_mem_maximalIdeal U (P.derivative.eval d0)).1 hpos
      have hz := (IsLocalRing.residue_eq_zero_iff _).2 hmem'
      change residueMap U (P.derivative.eval d0) = 0 at hz
      rw [hderivred] at hz
      exact (neg_ne_zero.mpr one_ne_zero) hz
    · exact (ord_nonneg_iff_mem_integer U _).2
        (P.derivative.eval d0).property
  obtain ⟨d, hdroot, hdnear, _⟩ :=
    Local.newton P d0 0 hderivord (by simpa using hPpos)
  have hdred : residueMap U d = dbar := by
    rw [← residueMap_teichmuller U dbar, residueMap_eq_residueMap_iff]
    change (((d - d0 : ringOfIntegers U) : U)) ∈ lattice U 1
    rw [mem_lattice_one_iff_mem_maximalIdeal U (d - d0)]
    exact (ord_pos_iff_mem_maximalIdeal U (d - d0)).1 (by simpa using hdnear)
  have heq : (d : U) ^ p - (d : U) = algebraMap F U (c : F) := by
    have h := congrArg (algebraMap (ringOfIntegers U) U) hdroot
    simp only [map_zero, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, map_sub, map_pow, P, cU] at h
    rw [show algebraMap (ringOfIntegers U) U
        (algebraMap (ringOfIntegers F) (ringOfIntegers U) c) =
      algebraMap F U (c : F) from rfl] at h
    rw [show algebraMap (ringOfIntegers U) U d = (d : U) from rfl] at h
    exact sub_eq_zero.mp (by simpa using h)
  have hdegree : Module.finrank F U = p := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F U
    rw [hunr, hres, one_mul] at h
    exact h
  have hd_not_base : (d : U) ∉ (⊥ : IntermediateField F U) := by
    rw [IntermediateField.mem_bot]
    rintro ⟨x, hx⟩
    have hxint : x ∈ lattice F 0 := by
      have hxord : (0 : WithTop ℤ) ≤ ord U (algebraMap F U x) := by
        rw [hx]
        exact (ord_nonneg_iff_mem_integer U (d : U)).2 d.property
      rw [ord_algebraMap, hunr, one_nsmul] at hxord
      exact (mem_lattice F).2 hxord
    let x0 : ringOfIntegers F :=
      ⟨x, (mem_lattice_zero_iff F).1 hxint⟩
    apply hdbar_not_base
    rw [IntermediateField.mem_bot]
    refine ⟨residueMap F x0, ?_⟩
    rw [← hdred]
    change extensionResidueMap F U (residueMap F x0) = residueMap U d
    rw [show d = algebraMap (ringOfIntegers F) (ringOfIntegers U) x0 by
      apply Subtype.ext
      exact hx.symm]
    rfl
  have hd_primitive : IntermediateField.adjoin F {(d : U)} = ⊤ := by
    letI : IsSimpleOrder (IntermediateField F U) :=
      IntermediateField.isSimpleOrder_of_finrank_prime F U (hdegree.symm ▸ hp)
    rcases IsSimpleOrder.eq_bot_or_eq_top
      (IntermediateField.adjoin F {(d : U)}) with h | h
    · exact False.elim (hd_not_base
        (IntermediateField.adjoin_simple_eq_bot_iff.mp h))
    · exact h
  refine ⟨c, d, ?_, by simpa [hdred, hc] using hdbar, heq, hd_primitive⟩
  simpa [IsNormalizedArtinSchreierCoefficient, hc] using hcbar

private theorem fixedField_finrank
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p) :
    Module.finrank F (IntermediateField.fixedField H) = p := by
  have htower := Module.finrank_mul_finrank F (IntermediateField.fixedField H) K
  rw [IntermediateField.finrank_fixedField_eq_card H, hH,
    ← IsGalois.card_aut_eq_finrank F K,
    Nat.card_congr (Classical.choice hG).toEquiv, Nat.card_prod] at htower
  have hcard : Nat.card (Multiplicative (ZMod p)) = p :=
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod p)
  rw [hcard] at htower
  exact Nat.mul_right_cancel hp.pos htower

/-! ## Public constructor -/

/-- Construct all initial odd unramified--ramified data from the genuine
local-field diamond and a ramified order-`p` line.

In particular, the theorem proves rather than assumes the common break, its
positivity, the nontrivial norm character and its exact conductor, its full
normalized logarithm chart for every nontrivial additive character, and the
exact integral Artin--Schreier generator. -/
theorem oddURSetup_exists
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime) (hodd : 2 < p)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hchar : residueCharacteristic F = p)
    (hI : Nat.card (Ramification.inertiaSubgroup (F := F) (K := K)) = p)
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p)
    (hne : H ≠ Ramification.inertiaSubgroup) :
    Nonempty (OddURSetup hp hG hI H hH hne hchar) := by
  let U := UnramifiedField F K
  let E := RamifiedField F K H
  have hdegU : Module.finrank F U = p := fixedField_finrank hp hG _ hI
  have hdegE : Module.finrank F E = p := fixedField_finrank hp hG H hH
  obtain ⟨hLocalU, hFreeFU, hFiniteFU, hFreeUK, hFiniteUK, hScalarU,
      hValFU, hValUK, _htotalU, _hdegFU, _hdegUK, hcycFU, hcycUK⟩ :=
    Basic.intermediateField_tower_compatible hp hG U hdegU
  obtain ⟨hLocalE, hFreeFE, hFiniteFE, hFreeEK, hFiniteEK, hScalarE,
      hValFE, hValEK, _htotalE, _hdegFE, _hdegEK, hcycFE, hcycEK⟩ :=
    Basic.intermediateField_tower_compatible hp hG E hdegE
  letI : ValuativeRel U := Basic.intermediateFieldValuativeRel U
  letI : TopologicalSpace U := Basic.intermediateFieldTopology U
  letI : IsNonarchimedeanLocalField U := hLocalU
  letI : Module.Free F U := hFreeFU
  letI : Module.Finite F U := hFiniteFU
  letI : Module.Free U K := hFreeUK
  letI : Module.Finite U K := hFiniteUK
  letI : IsScalarTower F U K := hScalarU
  letI : ValuativeExtension F U := hValFU
  letI : ValuativeExtension U K := hValUK
  letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E
  letI : TopologicalSpace E := Basic.intermediateFieldTopology E
  letI : IsNonarchimedeanLocalField E := hLocalE
  letI : Module.Free F E := hFreeFE
  letI : Module.Finite F E := hFiniteFE
  letI : Module.Free E K := hFreeEK
  letI : Module.Finite E K := hFiniteEK
  letI : IsScalarTower F E K := hScalarE
  letI : ValuativeExtension F E := hValFE
  letI : ValuativeExtension E K := hValEK
  letI : PrimeCyclicExtension F U :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F U hcycFU
  letI : PrimeCyclicExtension U K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension U K hcycUK
  letI : PrimeCyclicExtension F E :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F E hcycFE
  letI : PrimeCyclicExtension E K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension E K hcycEK
  let P := (Ramification.diamondBreaks hp hG hchar).2 hI
  obtain ⟨t, ht⟩ := P.ramified_lower H hH hne
  have ht' : residueDegree F E = 1 ∧ ramificationIndex E K = 1 ∧
      PrimeCyclicExtension.IsLowerBreak F E t ∧
      PrimeCyclicExtension.IsLowerBreak U K t := by
    simpa only [Ramification.UnramifiedBaseChangeBreakPair, U, E,
      UnramifiedField, RamifiedField] using ht
  have hFU : ramificationIndex F U = 1 ∧ residueDegree F U = p := by
    simpa only [U, UnramifiedField] using P.unramified_lower
  have hramFE : ramificationIndex F E = p := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F E
    rw [hdegE, ht'.1, mul_one] at h
    exact h.symm
  obtain ⟨piE, hpiE, hgenE⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one
      F E ht'.1
  have htpos : 0 < t := by
    by_contra hnot
    have htzero : t = 0 := Nat.eq_zero_of_not_pos hnot
    have hbreak0 : PrimeCyclicExtension.IsLowerBreak F E 0 := by
      simpa only [htzero] using ht'.2.2.1
    have htame := isTamelyRamified_of_isLowerBreak_zero F E ht'.1
      piE hpiE hgenE hbreak0
    apply htame
    rw [hchar, hramFE]
  letI : Finite (NormCharacter F E) :=
    ramifiedNormCharacter_finite F E ht'.2.2.1 ht'.1 piE hpiE hgenE
  letI : Nontrivial (NormCharacter F E) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [ramifiedNormCharacter_card F E ht'.2.2.1 ht'.1
        piE hpiE hgenE, hdegE]
      exact hp.one_lt)
  obtain ⟨tauF, htauF⟩ := exists_ne (1 : NormCharacter F E)
  have htauConductor : IsMultiplicativeConductor F tauF.1 (t + 1) :=
    ramifiedNormCharacter_conductor F E ht'.2.2.1 ht'.1
      piE hpiE hgenE tauF htauF
  obtain ⟨c, d, hnormc, hdres, hdeq, hdgen⟩ :=
    exists_unramifiedArtinSchreierGenerator hp hchar hFU.1 hFU.2
  refine ⟨{
    odd_prime := hodd
    t := t
    t_pos := htpos
    T := t + 1
    T_eq := rfl
    q0 := (t + 1) ⌈/⌉ p
    q0_eq := rfl
    q0_pos := (normCharacterChart_depths hp htpos).1
    breaks := ht
    tauF := ?_
    tauF_ne_one := ?_
    tauF_conductor := ?_
    normalizedCoefficient := ?_
    c := c
    d := ?_
    artinSchreier := ?_ }⟩
  · exact tauF
  · exact htauF
  · exact htauConductor
  · intro psiF hpsiF
    exact normalizedNormCharacterCoefficient_exists F hp htpos hchar
      tauF.1 htauConductor psiF hpsiF
  · exact d
  · exact ⟨hnormc, hdres, hdeq, hdgen⟩

end

end LanglandsSecondMainLemma.Odd.UR
