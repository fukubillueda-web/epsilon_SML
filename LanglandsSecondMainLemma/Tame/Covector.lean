import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Basic.NormTrace
import LanglandsSecondMainLemma.Local.TraceIdeals

/-!
# Tame / Covector

Blueprint: `blueprint/tasks/Tame/Covector.md`.
Paper: Lemma 5.2 (`U:tame-covector`).

Let `m > 1` be the conductor of a base-field quasi-character `lambda`,
and let `g` linearize `lambda` on the literal half-depth lattice
`p_F^(ceil(m/2))`.  For an unramified degree-`ell` edge the pullback has
the same conductor.  For a totally ramified tame edge its conductor is
`M = 1 + ell * (m - 1)`.  This file proves directly from the norm
expansion that the same element `g` gives the stationary linearization at
both full half-depth lattices.

The ramified estimate includes the terminal norm coefficient and does not
divide by the residue characteristic.  Consequently the proof also covers
`ell = 2` and `m = 2`.
-/

namespace LanglandsSecondMainLemma.Tame

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

/-- A nonarchimedean local field is infinite.  We use this only to identify
the elementary symmetric coefficients with symmetric polynomials in all
Galois conjugates. -/
private theorem localField_infinite
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : Infinite F := by
  let f : ℤ → F := fun n ↦ (exists_ord_eq F n).choose
  have hf : Function.Injective f := by
    intro a b hab
    have ha : ord F (f a) = (a : WithTop ℤ) := (exists_ord_eq F a).choose_spec
    have hb : ord F (f b) = (b : WithTop ℤ) := (exists_ord_eq F b).choose_spec
    exact WithTop.coe_injective (ha.symm.trans ((congrArg (ord F) hab).trans hb))
  exact Infinite.of_injective f hf

/-- Over an unramified extension, the `j`-th elementary symmetric
coefficient of an element of depth `a` has depth at least `j*a`.

This is the conjugate-monomial argument used on the unramified side of the
paper.  The ramification-index-one hypothesis is used when the bound is
descended from the upper field. -/
private theorem unramified_elementarySymmetric_bound
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (hunramified : ramificationIndex F K = 1)
    (a : ℤ) {x : K} (hx : (a : WithTop ℤ) ≤ ord K x)
    (j : ℕ) (_hj : j ≤ Module.finrank F K) :
    (((j : ℤ) * a : ℤ) : WithTop ℤ) ≤
      ord F (elementarySymmetric F K j x) := by
  classical
  letI : Infinite F := localField_infinite F
  have hprod (t : Finset Gal(K/F)) :
      t.card • (a : WithTop ℤ) ≤ ord K (∏ sigma ∈ t, sigma x) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert sigma t hsigma ih =>
        have hsx : (a : WithTop ℤ) ≤ ord K (sigma x) := by
          simpa using hx
        simpa [Finset.card_insert_of_notMem, hsigma, succ_nsmul, add_comm] using
          add_le_add hsx ih
  have hup : (((j : ℤ) * a : ℤ) : WithTop ℤ) ≤
      ord K (algebraMap F K (elementarySymmetric F K j x)) := by
    rw [algebraMap_elementarySymmetric_eq_esymm_galois,
      galoisConjugates, Finset.esymm_map_val]
    apply ord_sum K
    intro t ht
    have htcard : t.card = j := (Finset.mem_powersetCard.mp ht).2
    have htbound := hprod t
    rw [htcard] at htbound
    calc
      (((j : ℤ) * a : ℤ) : WithTop ℤ) = j • (a : WithTop ℤ) := by
        rw [← WithTop.coe_nsmul]
        congr
      _ ≤ ord K (∏ sigma ∈ t, sigma x) := htbound
  rw [ord_algebraMap, hunramified, one_nsmul] at hup
  exact hup

/-- At the unramified half depth, every term of degree at least two in
`N(1+x)` lies in the conductor lattice. -/
private theorem unramified_normError_mem
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (hunramified : ramificationIndex F K = 1)
    (m r : ℕ) (hm : m ≤ 2 * r)
    (x : K) (hx : ((r : ℕ) : WithTop ℤ) ≤ ord K x) :
    norm F K (1 + x) - 1 - trace F K x ∈ lattice F (m : ℤ) := by
  have hdegreePos : 0 < Module.finrank F K := Module.finrank_pos
  rw [norm_one_add_eq_one_add_sum_elementarySymmetric, add_sub_cancel_left]
  rw [show Module.finrank F K = (Module.finrank F K - 1) + 1 by omega]
  rw [Finset.sum_range_succ']
  rw [elementarySymmetric_one, add_sub_cancel_right, mem_lattice]
  apply ord_sum F
  intro j hj
  simp only [Finset.mem_range] at hj
  have hjtwo : 2 ≤ j + 1 + 1 := by omega
  have hjle : j + 1 + 1 ≤ Module.finrank F K := by omega
  have hsymm := unramified_elementarySymmetric_bound F K hunramified
    (r : ℤ) hx (j + 1 + 1) hjle
  apply (WithTop.coe_le_coe.mpr ?_).trans hsymm
  push_cast
  nlinarith

/-- At the ramified tame half depth
`s = ceil((1 + ell*(m-1))/2)`, every nontrace norm coefficient has
base-field depth at least `m`. -/
private theorem ramified_normError_mem
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (ell m s : ℕ) (hell : 0 < ell) (hm : 1 < m)
    (hdegree : Module.finrank F K = ell)
    (htotallyRamified : residueDegree F K = 1)
    (hs : s = (1 + ell * (m - 1)) ⌈/⌉ 2)
    (x : K) (hx : ((s : ℕ) : WithTop ℤ) ≤ ord K x) :
    norm F K (1 + x) - 1 - trace F K x ∈ lattice F (m : ℤ) := by
  have hramification : ramificationIndex F K = ell := by
    have hfactor := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hdegree, htotallyRamified, mul_one] at hfactor
    exact hfactor.symm
  have hMle : 1 + ell * (m - 1) ≤ 2 * s := by
    rw [hs]
    have hceil :=
      le_smul_ceilDiv (b := 1 + ell * (m - 1)) (a := 2) (by omega)
    change 1 + ell * (m - 1) ≤ 2 * ((1 + ell * (m - 1)) ⌈/⌉ 2) at hceil
    exact hceil
  rw [norm_one_add_eq_one_add_sum_elementarySymmetric, add_sub_cancel_left]
  rw [hdegree]
  rw [show ell = (ell - 1) + 1 by omega]
  rw [Finset.sum_range_succ']
  rw [elementarySymmetric_one, add_sub_cancel_right, mem_lattice]
  apply ord_sum F
  intro j hj
  simp only [Finset.mem_range] at hj
  have hjtwo : 2 ≤ j + 1 + 1 := by omega
  have hjle : j + 1 + 1 ≤ ell := by omega
  have hsymm := totallyRamified_elementarySymmetric_bound F K ell (s : ℤ)
    hell hdegree hramification hx (j + 1 + 1) hjle
  apply (WithTop.coe_le_coe.mpr ?_).trans hsymm
  unfold integerCeilingDiv
  rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hell)]
  push_cast
  have hmSub : m - 1 + 1 = m := by omega
  have hjbound : 2 * s ≤ (j + 1 + 1) * s :=
    Nat.mul_le_mul_right s hjtwo
  have hstrict : ell * (m - 1) < (j + 1 + 1) * s := by
    nlinarith
  rw [← hmSub]
  push_cast
  nlinarith

/-- If the norm differs from `1 + trace` only by a conductor-depth error,
then a base stationary linearization pulls back with the same coefficient.
The right-hand side uses the literal image of the same `g : Fˣ`. -/
private theorem covector_of_normError
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (m r s : ℕ) (hm : 1 < m) (hr : 0 < r) (hs : 0 < s)
    (lambda : ContinuousQuasiChar F)
    (hlambda : IsMultiplicativeConductor F lambda m)
    (psi : ContinuousAddChar F) (g : Fˣ)
    (hbase : ∀ z : lattice F (r : ℤ),
      lambda (positiveUnitOfLattice F hr z) =
        psi ((g : F) * (z : F)))
    (htrace : ∀ x : K, x ∈ lattice K (s : ℤ) →
      trace F K x ∈ lattice F (r : ℤ))
    (hnormError : ∀ x : K, x ∈ lattice K (s : ℤ) →
      norm F K (1 + x) - 1 - trace F K x ∈ lattice F (m : ℤ)) :
    ∀ x : lattice K (s : ℤ),
      normQuasiChar F K lambda (positiveUnitOfLattice K hs x) =
        tracePullbackAddChar F K psi
          (algebraMap F K (g : F) * (x : K)) := by
  intro x
  let tx : lattice F (r : ℤ) := ⟨trace F K (x : K), htrace x x.property⟩
  let ux : Kˣ := positiveUnitOfLattice K hs x
  let ut : Fˣ := positiveUnitOfLattice F hr tx
  let error : F := norm F K (1 + (x : K)) - 1 - trace F K (x : K)
  let ratio : Fˣ := normUnits F K ux / ut

  have hutGroup : ut ∈ unitGroup F :=
    unitFiltration_le_unitGroup F r (positiveUnitOfLattice F hr tx).property
  have hutOrd : ord F (ut : F) = 0 :=
    (mem_unitGroup_iff_ord_eq_zero F ut).1 hutGroup
  have hratioCoe : (ratio : F) - 1 = error / (ut : F) := by
    simp only [ratio, error, Units.val_div_eq_div_val, coe_normUnits, ux, ut,
      coe_positiveUnitOfLattice, tx]
    have hden : 1 + trace F K (x : K) ≠ 0 := by
      rw [← show (ut : F) = 1 + trace F K (x : K) by
        simp only [ut, coe_positiveUnitOfLattice, tx]]
      exact Units.ne_zero ut
    field_simp [hden]
    ring
  have herror : error ∈ lattice F (m : ℤ) :=
    hnormError x x.property
  have hratioDisp : (ratio : F) - 1 ∈ lattice F (m : ℤ) := by
    rw [hratioCoe]
    exact (div_mem_lattice_iff F (ut : F) error 0 (m : ℤ) hutOrd).2
      (by simpa using herror)
  have hmSucc : m - 1 + 1 = m := by omega
  have hratio : ratio ∈ unitFiltration F m := by
    rw [← hmSucc, mem_unitFiltration_succ_iff_sub_mem_lattice]
    simpa only [hmSucc] using hratioDisp
  have hratioOne : lambda ratio = 1 := hlambda.trivial ratio hratio
  have hnormFactor : normUnits F K ux = ratio * ut := by
    simp [ratio]

  rw [normQuasiChar_apply]
  change lambda (normUnits F K ux) = _
  rw [hnormFactor, map_mul, hratioOne, one_mul]
  rw [hbase tx, tracePullbackAddChar_apply]
  congr 1
  rw [show algebraMap F K (g : F) * (x : K) = (g : F) • (x : K) by
    simp [Algebra.smul_def], map_smul]
  rfl

/-- **The full tame stationary covector** (Paper Lemma 5.2,
`U:tame-covector`).

Let `U/F` be the unramified cyclic edge of prime degree `ell`, and let
`E/F` be a totally ramified cyclic edge of the same degree, with residue
characteristic different from `ell`.  If `lambda` has exact conductor
`m > 1` and the actual element `g : Fˣ` gives its stationary formula on
`p_F^(ceil(m/2))`, then the literal image of this same `g` gives the
stationary formula

* on `p_U^(ceil(m/2))` for the unramified norm pullback, and
* on `p_E^(ceil((1 + ell*(m-1))/2))` for the ramified norm pullback.

The conclusions are pointwise identities for the genuine field norm and
trace pullbacks, so no auxiliary stationary model or representative is
introduced. -/
theorem covector
    (F U E : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field U] [ValuativeRel U] [TopologicalSpace U]
    [IsNonarchimedeanLocalField U]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F U] [ValuativeExtension F U]
    [Module.Free F U] [Module.Finite F U] [PrimeCyclicExtension F U]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Free F E] [Module.Finite F E] [PrimeCyclicExtension F E]
    (ell m : ℕ) (hell : ell.Prime) (hm : 1 < m)
    (_htame : residueCharacteristic F ≠ ell)
    (hdegreeU : Module.finrank F U = ell)
    (hunramified : ramificationIndex F U = 1)
    (hdegreeE : Module.finrank F E = ell)
    (htotallyRamified : residueDegree F E = 1)
    (lambda : ContinuousQuasiChar F)
    (hlambda : IsMultiplicativeConductor F lambda m)
    (psi : ContinuousAddChar F) (_hpsi : psi ≠ 1) (g : Fˣ)
    (hbase : ∀ z : lattice F ((m ⌈/⌉ 2 : ℕ) : ℤ),
      lambda (positiveUnitOfLattice F (by
        rw [Nat.ceilDiv_eq_add_pred_div]
        omega) z) =
        psi ((g : F) * (z : F))) :
    (∀ x : lattice U ((m ⌈/⌉ 2 : ℕ) : ℤ),
      normQuasiChar F U lambda
          (positiveUnitOfLattice U (by
            rw [Nat.ceilDiv_eq_add_pred_div]
            omega) x) =
        tracePullbackAddChar F U psi
          (algebraMap F U (g : F) * (x : U))) ∧
    (∀ x : lattice E
        (((1 + ell * (m - 1)) ⌈/⌉ 2 : ℕ) : ℤ),
      normQuasiChar F E lambda
          (positiveUnitOfLattice E (by
            rw [Nat.ceilDiv_eq_add_pred_div]
            omega) x) =
        tracePullbackAddChar F E psi
          (algebraMap F E (g : F) * (x : E))) := by
  let r : ℕ := m ⌈/⌉ 2
  let M : ℕ := 1 + ell * (m - 1)
  let s : ℕ := M ⌈/⌉ 2
  have hr : 0 < r := by
    dsimp only [r]
    rw [Nat.ceilDiv_eq_add_pred_div]
    omega
  have hs : 0 < s := by
    dsimp only [s, M]
    rw [Nat.ceilDiv_eq_add_pred_div]
    omega
  have hmHalf : m ≤ 2 * r := by
    dsimp only [r]
    have hceil := le_smul_ceilDiv (b := m) (a := 2) (by omega)
    change m ≤ 2 * (m ⌈/⌉ 2) at hceil
    exact hceil

  constructor
  · apply covector_of_normError F U m r r hm hr hr lambda hlambda psi g
    · simpa only [r] using hbase
    · intro x hx
      have hbound := unramified_elementarySymmetric_bound F U hunramified
        (r : ℤ) hx 1 (by rw [hdegreeU]; exact hell.one_le)
      rw [mem_lattice]
      norm_num [elementarySymmetric_one] at hbound ⊢
      exact hbound
    · intro x hx
      exact unramified_normError_mem F U hunramified m r hmHalf x hx
  · apply covector_of_normError F E m r s hm hr hs lambda hlambda psi g
    · simpa only [r] using hbase
    · intro x hx
      have hramification : ramificationIndex F E = ell := by
        have hfactor := finrank_eq_ramificationIndex_mul_residueDegree F E
        rw [hdegreeE, htotallyRamified, mul_one] at hfactor
        exact hfactor.symm
      have hbound := totallyRamified_elementarySymmetric_bound F E ell (s : ℤ)
        hell.pos hdegreeE hramification hx 1 (by exact hell.one_le)
      rw [elementarySymmetric_one] at hbound
      apply (WithTop.coe_le_coe.mpr ?_).trans hbound
      unfold integerCeilingDiv
      rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hell.pos)]
      push_cast
      have hMle : M ≤ 2 * s := by
        dsimp only [s]
        have hceil := le_smul_ceilDiv (b := M) (a := 2) (by omega)
        change M ≤ 2 * (M ⌈/⌉ 2) at hceil
        exact hceil
      have hMleZ :
          (1 : ℤ) + (ell : ℤ) * ((m : ℤ) - 1) ≤ 2 * (s : ℤ) := by
        have hcast : ((M : ℕ) : ℤ) ≤ ((2 * s : ℕ) : ℤ) := by
          exact_mod_cast hMle
        dsimp only [M] at hcast
        push_cast [Nat.cast_sub (by omega : 1 ≤ m)] at hcast
        exact hcast
      rcases Nat.even_or_odd m with heven | hodd
      · obtain ⟨b, hb⟩ := heven
        have hmEq : m = 2 * b := by omega
        have hrEq : r = b := by
          dsimp only [r]
          rw [Nat.ceilDiv_eq_add_pred_div, hmEq]
          omega
        rw [hrEq]
        have hmEqZ : (m : ℤ) = 2 * (b : ℤ) := by exact_mod_cast hmEq
        have hellTwoZ : (2 : ℤ) ≤ ell := by exact_mod_cast hell.two_le
        nlinarith [hMleZ]
      · obtain ⟨b, hb⟩ := hodd
        have hmEq : m = 2 * b + 1 := by omega
        have hrEq : r = b + 1 := by
          dsimp only [r]
          rw [Nat.ceilDiv_eq_add_pred_div, hmEq]
          omega
        rw [hrEq]
        have hmEqZ : (m : ℤ) = 2 * (b : ℤ) + 1 := by exact_mod_cast hmEq
        push_cast
        nlinarith [hMleZ]
    · intro x hx
      exact ramified_normError_mem F E ell m s hell.pos hm hdegreeE
        htotallyRamified (by rfl) x hx

end

end LanglandsSecondMainLemma.Tame
