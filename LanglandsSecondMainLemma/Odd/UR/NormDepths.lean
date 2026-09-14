import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.UR.Coefficients
import LanglandsSecondMainLemma.Odd.EnhancedStationary

/-!
# Depths of the two actual norms in the unramified--ramified case

Paper Lemma 6.10 (`O:I:normdepths`), with `O:I:commonC`, `O:I:ZU`,
`O:I:ZE`, `O:I:normpower` and `O:I:etaUresidue` (source lines 1492--1574).
The setup is lines 1060--1128 and 1416--1451. The exact norm witness and
full character charts are supplied by the accepted coefficient theorem.
All lattice exponents are integers; zero inputs retain infinite valuation.
The last coefficient error is retained at `h = t`.
-/

open LanglandsFirstMainLemma
namespace LanglandsSecondMainLemma.Odd.UR

noncomputable section
open scoped BigOperators

private theorem half_bound {p r : ℤ} (hp : 3 ≤ p) (hr : 2 ≤ r) :
    (r + 1) / 2 ≤ ((p - 1) * r) / p := by
  apply (Int.le_ediv_iff_mul_le (by omega : 0 < p)).2
  have hhalf : 1 ≤ (r + 1) / 2 := by omega
  have htwice : 2 * ((r + 1) / 2) ≤ r + 1 := by omega
  have htriple : 3 * ((r + 1) / 2) ≤ 2 * r := by omega
  nlinarith

/-- The two error bounds imply ordinary precision, and enhanced precision
away from the last depth. All potentially negative exponents are integers. -/
private theorem normDepths_arithmetic {p t h : ℤ}
    (hp : 3 ≤ p) (ht : 1 ≤ t) (hh0 : 0 ≤ h) (hht : h ≤ t) :
    (t + 1 - (t + 2 + h) / 2 ≤ ((p - 1) * (t + 1 - h)) / p) ∧
    (t + 1 - (t + 2 + p * h) / 2 ≤ (p - 1) * t - p * h) ∧
    (h < t →
      t + 1 - (t + 1 + h) / 2 ≤ ((p - 1) * (t + 1 - h)) / p ∧
      t + 1 - (t + 1 + p * h) / 2 ≤ (p - 1) * t - p * h) ∧
    (5 ≤ p → t + 1 - (t + 1 + p * h) / 2 ≤ (p - 1) * t - p * h) := by
  have hU : h < t → t + 1 - (t + 1 + h) / 2 ≤
      ((p - 1) * (t + 1 - h)) / p := by
    intro hlt
    have hb := half_bound hp (by omega : 2 ≤ t + 1 - h)
    omega
  have hE : 0 ≤ (2 * p - 3) * t - p * h := by
    nlinarith
  have hU0 : 0 ≤ ((p - 1) * (t + 1 - h)) / p :=
    Int.ediv_nonneg (by nlinarith) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases hlt : h < t
    · have := hU hlt; omega
    · have : h = t := by omega
      subst h
      omega
  · have : t + 1 + p * h ≤ 2 * ((t + 2 + p * h) / 2) := by omega
    nlinarith
  · intro hlt
    refine ⟨hU hlt, ?_⟩
    have : 1 ≤ (2 * p - 3) * t - p * h := by nlinarith
    have : t + p * h ≤ 2 * ((t + 1 + p * h) / 2) := by omega
    nlinarith
  · intro hp5
    have : 1 ≤ (2 * p - 3) * t - p * h := by nlinarith
    have : t + p * h ≤ 2 * ((t + 1 + p * h) / 2) := by omega
    nlinarith
private theorem local_infinite (F : Type*) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] : Infinite F := by
  let f : ℤ → F := fun n => (exists_ord_eq F n).choose
  apply Infinite.of_injective f
  intro m n he
  have hm := (exists_ord_eq F m).choose_spec
  have hn := (exists_ord_eq F n).choose_spec
  exact WithTop.coe_injective (hm.symm.trans ((congrArg (ord F) he).trans hn))

/-- Vieta's identity with an arbitrary evaluation point, retaining repeated
conjugates when the element lies in the base field. -/
private theorem normDepths_vieta (F E L : Type*) [Field F] [Field E] [CommRing L]
    [Algebra F E] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
    [Module.Finite F E] [IsGalois F E] [Infinite F] (x : E) (y : L) :
    (∏ sigma : Gal(E/F), (y + algebraMap E L (sigma x))) =
      ∑ i ∈ Finset.range (Module.finrank F E + 1),
        algebraMap F L (elementarySymmetric F E i x) * y ^ (Module.finrank F E - i) := by
  have hv := congrArg (Polynomial.eval₂ (algebraMap E L) y)
    (Multiset.prod_X_add_C_eq_sum_esymm (galoisConjugates F E x))
  rw [galoisConjugates_card] at hv
  simp_rw [← algebraMap_elementarySymmetric_eq_esymm_galois] at hv
  simpa only [galoisConjugates, Multiset.map_map, ← Finset.prod_eq_multiset_prod,
    Function.comp_def, galoisConjugate, Polynomial.eval₂_finsetProd,
    Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    ← IsScalarTower.algebraMap_apply] using hv

section RamifiedBounds
variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

/-- The paper's symmetric estimate, with its trace hypothesis constructed
from the actual different and lower break. -/
private theorem normDepths_symmetric {p t h : ℕ}
    (hdegree : Module.finrank F E = p) (htpos : 0 < t)
    (hchar : residueCharacteristic F = p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hres : residueDegree F E = 1)
    {x : E} (hx : x ∈ lattice E (-(h : ℤ)))
    {i : ℕ} (hi : 1 ≤ i) (hip : i < p) :
    elementarySymmetric F E i x ∈
      lattice F (((p - 1 : ℕ) * (t + 1) - (i : ℤ) * h) / p) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have htrace := traceIdealLowerBound_of_integralGenerator F E ht hres pi hpi hgen
  have hram : ramificationIndex F E = Module.finrank F E := by
    have he := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa only [hres, mul_one] using he.symm
  have hb := (wild_symmetric_bound F E t ht htpos (hchar.trans hdegree.symm)
    hram htrace (-(h : ℤ)) hx).1 hi (hdegree ▸ hip)
  simpa only [mem_lattice, hdegree, wildDifferentContribution, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, mul_neg, neg_add_eq_sub] using hb
end RamifiedBounds
private theorem pow_lattice (L : Type*) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    {x : L} {a : ℤ} (hx : x ∈ lattice L a) (i : ℕ) :
    x ^ i ∈ lattice L ((i : ℤ) * a) := by
  rw [mem_lattice] at hx
  rw [mem_lattice, ord_pow]
  simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using nsmul_le_nsmul_right hx i

private theorem map_lattice (F L : Type*) [Field F] [Field L]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra F L] [ValuativeExtension F L] {x : F} {a : ℤ}
    (hx : x ∈ lattice F a) :
    algebraMap F L x ∈ lattice L ((ramificationIndex F L : ℤ) * a) := by
  rw [mem_lattice] at hx
  rw [mem_lattice, ord_algebraMap]
  simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using
    nsmul_le_nsmul_right hx (ramificationIndex F L)

private theorem sum_endpoints {R : Type*} [AddCommMonoid R] {p : ℕ}
    (hp : 0 < p) (f : ℕ → R) :
    ∑ i ∈ Finset.range (p + 1), f i =
      f 0 + ∑ i ∈ Finset.Ico 1 p, f i + f p := by
  rw [Finset.sum_range_succ, ← Finset.sum_range_add_sum_Ico f (show 1 ≤ p from hp)]
  simp

section PowerError
variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeExtension F E] in
/-- The exact signed power--norm identity (`O:I:normpower`). -/
private theorem normDepths_power_identity {p : ℕ} (hp : Odd p)
    (hdegree : Module.finrank F E = p) (x : E) :
    x ^ p - algebraMap F E (norm F E x) =
      ∑ i ∈ Finset.Ico 1 p,
        algebraMap F E (elementarySymmetric F E i x) * (-x) ^ (p - i) := by
  letI : Infinite F := local_infinite F
  have hv := normDepths_vieta F E E x (-x)
  have hz : (∏ sigma : Gal(E/F), (-x + algebraMap E E (sigma x))) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ (1 : Gal(E/F)))
    simp
  rw [hz, hdegree, sum_endpoints hp.pos] at hv
  simp only [elementarySymmetric_zero, map_one, one_mul, Nat.sub_zero,
    Nat.sub_self, pow_zero, mul_one,
    ← hdegree, elementarySymmetric_finrank] at hv
  rw [hdegree, hp.neg_pow] at hv
  linear_combination hv

/-- The power--norm error at every allowed integer depth, including zero
and inputs whose valuation is infinity. -/
private theorem normDepths_power_bound {p t h : ℕ} (hp : Odd p)
    (hdegree : Module.finrank F E = p) (htpos : 0 < t)
    (hchar : residueCharacteristic F = p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hres : residueDegree F E = 1)
    {x : E} (hx : x ∈ lattice E (-(h : ℤ))) :
    x ^ p - algebraMap F E (norm F E x) ∈
      lattice E (((p : ℤ) - 1) * t - p * h) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hram : ramificationIndex F E = p := by
    have he := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa only [hdegree, hres, mul_one] using he.symm
  rw [normDepths_power_identity F E hp hdegree]
  apply sum_mem_lattice E
  intro i hi
  obtain ⟨hi, hip⟩ := Finset.mem_Ico.mp hi
  have hb := normDepths_symmetric F E hdegree htpos hchar ht hres hx hi hip
  have hmap := map_lattice F E hb
  rw [hram] at hmap
  have hpow := pow_lattice E (neg_mem_lattice E hx) (p - i)
  apply lattice_antitone E _ (mul_mem_lattice E hmap hpow)
  have hpi : (p - i : ℕ) = (p : ℤ) - i := by omega
  have hp1 : (p - 1 : ℕ) = (p : ℤ) - 1 := by omega
  rw [hpi, hp1]
  have hfloor : (p : ℤ) - 1 + p *
      ((((p : ℤ) - 1) * (t + 1) - i * h) / p) ≥
        ((p : ℤ) - 1) * (t + 1) - i * h := by
    have hb := Int.emod_lt_of_pos (((p : ℤ) - 1) * (t + 1) - i * h) hp0
    have he := Int.emod_add_mul_ediv (((p : ℤ) - 1) * (t + 1) - i * h) p
    omega
  nlinarith
end PowerError
section NormExpansion
variable (F K : Type*) [Field F] [Field K] [Algebra F K] [Module.Finite F K]
  (E U : IntermediateField F K) [IsGalois F E] [IsGalois U K] [Infinite F]

/-- Restriction reindexes the actual conjugates in a degree-preserving
compositum; it does not choose formal norm representatives. -/
private def normDepths_restrictEquiv
    (hsup : E ⊔ U = ⊤) (hdegree : Module.finrank F E = Module.finrank U K) :
    Gal(K/U) ≃ Gal(E/F) :=
  Equiv.ofBijective (IntermediateField.restrictRestrictAlgEquivMapHom F E U K)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨
      IntermediateField.restrictRestrictAlgEquivMapHom_injective E U hsup,
      by simp only [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, hdegree]⟩)

/-- Both sides of the paper's norm expansion are actual field elements.
This is used on each side of the diamond. -/
private theorem normDepths_norm_expansion
    (hsup : E ⊔ U = ⊤) (hdegree : Module.finrank F E = Module.finrank U K)
    (x : E) (d : U) :
    norm U K ((x : K) + (d : K)) =
      ∑ i ∈ Finset.range (Module.finrank F E + 1),
        algebraMap F U (elementarySymmetric F E i x) * d ^ (Module.finrank F E - i) := by
  let e := normDepths_restrictEquiv F K E U hsup hdegree
  apply (algebraMap U K).injective
  simp only [map_sum, map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
  calc
    algebraMap U K (norm U K ((x : K) + (d : K))) =
        ∏ sigma : Gal(K/U), ((d : K) + sigma (x : K)) := by
      rw [Algebra.norm_eq_prod_automorphisms]
      apply Finset.prod_congr rfl
      intro sigma _
      change sigma ((x : K) + algebraMap U K d) = _
      rw [map_add, sigma.commutes]
      exact add_comm _ _
    _ = ∏ sigma : Gal(E/F), ((d : K) + algebraMap E K (sigma x)) := by
      apply Fintype.prod_equiv e
      intro sigma
      congr 1
      exact (IntermediateField.restrictRestrictAlgEquivMapHom_apply E U sigma x).symm
    _ = _ := normDepths_vieta F E K x (d : K)
end NormExpansion

/-- The exact Artin--Schreier equation and generation identify the
characteristic polynomial, also in mixed characteristic. -/
private theorem normDepths_artinSchreier_charpoly
    (F U : Type*) [Field F] [Field U] [Algebra F U] [Module.Finite F U]
    {p : ℕ} (hp : 2 < p) (hdegree : Module.finrank F U = p)
    (c : F) (d : U) (hd : d ^ p - d = algebraMap F U c)
    (hgen : IntermediateField.adjoin F {d} = ⊤) :
    (Algebra.lmul F U d).charpoly = Polynomial.X ^ p - Polynomial.X - Polynomial.C c := by
  let f : Polynomial F := Polynomial.X ^ p - Polynomial.X - Polynomial.C c
  have hfdeg : f.natDegree = p := by
    dsimp [f]
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt,
      Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · simp; omega
    · rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simp; omega)]
      simp; omega
  have hfmonic : f.Monic := by
    apply Polynomial.Monic.sub_of_left
    · apply Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow p)
      simp; omega
    · rw [Polynomial.degree_sub_eq_left_of_degree_lt (by simp; omega)]
      exact lt_of_le_of_lt Polynomial.degree_C_le (by simp; omega)
  have hroot : Polynomial.aeval d f = 0 := by
    simpa [f, sub_eq_zero] using hd
  have hint : IsIntegral F d := Algebra.IsIntegral.isIntegral d
  have hmin : (minpoly F d).natDegree = p := by
    rw [← IntermediateField.adjoin.finrank hint, hgen, IntermediateField.finrank_top', hdegree]
  have hfeq : f = minpoly F d :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hfmonic
      (minpoly.dvd F d hroot) (by rw [hfdeg, hmin])
  have hceq : (Algebra.lmul F U d).charpoly = minpoly F d :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
      (LinearMap.charpoly_monic _) (minpoly.dvd F d (Algebra.aeval_self_charpoly_lmul d))
      (by rw [LinearMap.charpoly_natDegree, hdegree, hmin])
  exact hceq.trans hfeq.symm
section SymmetricSum
variable (F E U : Type*) [Field F] [Field E] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F E] [Algebra F U] [ValuativeExtension F E] [ValuativeExtension F U]
  [Module.Finite F E] [PrimeCyclicExtension F E]

/-- The nonterminal unramified norm terms, before the endpoint error. -/
private def normDepths_symmetricSum (p : ℕ) (x : E) (d : U) : U :=
  ∑ i ∈ Finset.Ico 1 p,
    algebraMap F U (elementarySymmetric F E i x) * d ^ (p - i)

/-- The uniform bound in `O:I:errorsbounds`; the same formula covers integral
`x`, including `x = 0`, without taking a finite valuation. -/
private theorem normDepths_sum_bound {p t h : ℕ} (hp : 2 < p)
    (hdegree : Module.finrank F E = p) (htpos : 0 < t)
    (hchar : residueCharacteristic F = p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hres : residueDegree F E = 1)
    (hunr : ramificationIndex F U = 1)
    {x : E} (hx : x ∈ lattice E (-(h : ℤ))) {d : U} (hd : d ∈ lattice U 0) :
    normDepths_symmetricSum F E U p x d ∈
      lattice U ((((p : ℤ) - 1) * (t + 1 - h)) / p) := by
  apply sum_mem_lattice U
  intro i hi
  obtain ⟨hi, hip⟩ := Finset.mem_Ico.mp hi
  have hbound := normDepths_symmetric F E hdegree htpos hchar ht hres hx hi hip
  have hcoeff : elementarySymmetric F E i x ∈
      lattice F ((((p : ℤ) - 1) * (t + 1 - h)) / p) := by
    apply lattice_antitone F _ hbound
    apply Int.ediv_le_ediv (by omega : (0 : ℤ) < p)
    have hp1 : (p - 1 : ℕ) = (p : ℤ) - 1 := by omega
    rw [hp1]
    have hiZ : (i : ℤ) ≤ p - 1 := by omega
    nlinarith
  have hm := map_lattice F U hcoeff
  simp only [hunr, Nat.cast_one, one_mul] at hm
  simpa only [mul_zero, add_zero] using mul_mem_lattice U hm (pow_lattice U hd (p - i))

/-- At `h = t` the last coefficient is integral, and deleting its term
leaves a full maximal-ideal error (`O:I:etaUresidue`). -/
private theorem normDepths_boundary_residue {p t : ℕ} (hp : 2 < p)
    (hdegree : Module.finrank F E = p) (htpos : 0 < t)
    (hchar : residueCharacteristic F = p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hres : residueDegree F E = 1)
    (hunr : ramificationIndex F U = 1)
    {x : E} (hx : x ∈ lattice E (-(t : ℤ))) {d : U} (hd : d ∈ lattice U 0) :
    elementarySymmetric F E (p - 1) x ∈ lattice F 0 ∧
    normDepths_symmetricSum F E U p x d -
      algebraMap F U (elementarySymmetric F E (p - 1) x) * d ∈ lattice U 1 := by
  have hp1 : (p - 1 : ℕ) = (p : ℤ) - 1 := by omega
  have hb := normDepths_symmetric F E hdegree htpos hchar ht hres hx
    (by omega : 1 ≤ p - 1) (by omega : p - 1 < p)
  constructor
  · apply lattice_antitone F _ hb
    apply Int.ediv_nonneg _ (by omega)
    rw [hp1]
    nlinarith
  · have hsum : normDepths_symmetricSum F E U p x d =
        (∑ i ∈ Finset.Ico 1 (p - 1),
          algebraMap F U (elementarySymmetric F E i x) * d ^ (p - i)) +
        algebraMap F U (elementarySymmetric F E (p - 1) x) * d := by
      unfold normDepths_symmetricSum
      rw [show p = (p - 1) + 1 by omega, Finset.sum_Ico_succ_top (by omega)]
      simp only [show p - 1 + 1 = p by omega, show p - (p - 1) = 1 by omega, pow_one]
    rw [hsum, add_sub_cancel_right]
    apply sum_mem_lattice U
    intro i hi
    obtain ⟨hi, hip⟩ := Finset.mem_Ico.mp hi
    have he := normDepths_symmetric F E hdegree htpos hchar ht hres hx hi (by omega)
    have he1 : elementarySymmetric F E i x ∈ lattice F 1 := by
      apply lattice_antitone F _ he
      apply (Int.le_ediv_iff_mul_le (by omega : (0 : ℤ) < p)).2
      rw [hp1]
      have hiZ : (i : ℤ) ≤ p - 2 := by omega
      nlinarith
    have heU := map_lattice F U he1
    simp only [hunr, Nat.cast_one, one_mul] at heU
    simpa only [mul_zero, add_zero] using mul_mem_lattice U heU (pow_lattice U hd (p - i))
end SymmetricSum
section ArtinSchreierNorm
variable (F U : Type*) [Field F] [Field U] [Algebra F U] [Module.Finite F U]
  {p : ℕ} (hp : Odd p) (hodd : 2 < p) (hdegree : Module.finrank F U = p)
  (c : F) (d : U) (hd : d ^ p - d = algebraMap F U c)
  (hgen : IntermediateField.adjoin F {d} = ⊤)

include hp hodd hdegree hd hgen

private theorem artinSchreier_symmetric {i : ℕ} (hi : 1 ≤ i) (hip : i < p) :
    elementarySymmetric F U i d = if i = p - 1 then -1 else 0 := by
  rw [elementarySymmetric, hdegree, if_pos (by omega),
    normDepths_artinSchreier_charpoly F U hodd hdegree c d hd hgen]
  have hpi0 : p - i ≠ 0 := by omega
  have hpip : p - i ≠ p := by omega
  by_cases he : i = p - 1
  · subst i
    have hev : Even (p - 1) := by obtain ⟨k, hk⟩ := hp; exact ⟨k, by omega⟩
    simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      show p - (p - 1) = 1 by omega, hev.neg_one_pow, show (1 : ℕ) ≠ p by omega]
  · have hpi1 : p - i ≠ 1 := by omega
    simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_C, hpi0, hpip, Ne.symm hpi1, he]

private theorem artinSchreier_norm : norm F U d = c := by
  rw [← elementarySymmetric_finrank, elementarySymmetric, if_pos le_rfl,
    hdegree, Nat.sub_self, normDepths_artinSchreier_charpoly F U hodd hdegree c d hd hgen]
  simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_C, show (0 : ℕ) ≠ p by omega, hp.neg_one_pow]
end ArtinSchreierNorm

/-- The second actual norm is the exact lifted Artin--Schreier polynomial
(`O:I:ZE`), without reducing the field characteristic. -/
private theorem normDepths_norm_E
    (F K : Type*) [Field F] [Field K] [Algebra F K] [Module.Finite F K]
    (E U : IntermediateField F K) [IsGalois F U] [IsGalois E K] [Infinite F]
    {p : ℕ} (hp : Odd p) (hodd : 2 < p)
    (hFU : Module.finrank F U = p) (hEK : Module.finrank E K = p)
    (hsup : E ⊔ U = ⊤) (c : F) (d : U)
    (hd : d ^ p - d = algebraMap F U c)
    (hgen : IntermediateField.adjoin F {d} = ⊤) (x : E) :
    norm E K ((x : K) + (d : K)) = x ^ p - x + algebraMap F E c := by
  have hnorm := normDepths_norm_expansion F K U E (by simpa [sup_comm] using hsup)
    (hFU.trans hEK.symm) d x
  rw [hFU, sum_endpoints hp.pos] at hnorm
  have hsum :
      (∑ i ∈ Finset.Ico 1 p,
        algebraMap F E (elementarySymmetric F U i d) * x ^ (p - i)) = -x := by
    rw [Finset.sum_eq_single (p - 1)]
    · rw [artinSchreier_symmetric F U hp hodd hFU c d hd hgen (by omega) (by omega)]
      simp [show p - (p - 1) = 1 by omega]
    · intro i hi hne
      rw [artinSchreier_symmetric F U hp hodd hFU c d hd hgen
        (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2, if_neg hne]
      simp
    · intro hnot
      exact (hnot (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)).elim
  rw [hsum, elementarySymmetric_zero, map_one, one_mul, Nat.sub_zero,
    Nat.sub_self, pow_zero, mul_one, ← hFU, elementarySymmetric_finrank,
    artinSchreier_norm F U hp hodd hFU c d hd hgen, hFU] at hnorm
  simpa only [add_comm (d : K) (x : K), sub_eq_add_neg] using hnorm
section Representatives
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- The complete stationary meaning of a replacement coefficient. Its
nonzero order, ordinary linearization, enhanced logarithm chart and affine
character value are all stated for the actual continuous characters. -/
structure NormDepthRepresentative (theta : ContinuousQuasiChar L)
    (Psi : ContinuousAddChar L) (p m : ℕ) (J : ℤ) (B Z : L) : Prop where
  large : 1 < m
  coefficient_order : ord L B = ((J - (m : ℤ) : ℤ) : WithTop ℤ)
  numerator_order : ord L Z = ((J - (m : ℤ) : ℤ) : WithTop ℤ)
  displacement : Z - B ∈ lattice L (J - (((m + 1) / 2 : ℕ) : ℤ))
  coefficient_chart : ∀ z : lattice L (((m / 2 : ℕ) : ℤ)),
    theta (positiveUnitOfLattice L (by omega) (-z)) =
      Psi (B * truncatedLog p (z : L))
  ordinary : ∀ z : lattice L ((((m + 1) / 2 : ℕ) : ℤ)),
    theta (positiveUnitOfLattice L (by omega) (-z)) = Psi (Z * (z : L))
  enhanced : Z - B ∈ lattice L (J - ((m / 2 : ℕ) : ℤ)) →
    (∀ z : lattice L (((m / 2 : ℕ) : ℤ)),
      theta (positiveUnitOfLattice L (by omega) (-z)) =
        Psi (Z * truncatedLog p (z : L))) ∧
    Psi ((Z - B) ^ 2 / ((2 : L) * B)) = 1

private theorem phase_eq (Psi : ContinuousAddChar L) {J : ℤ}
    (hPsi : AddCharTrivialOnLattice L Psi J) {a b : L}
    (hab : a - b ∈ lattice L J) : Psi a = Psi b := by
  apply div_eq_one.mp
  exact (Psi.toAddChar.map_sub_eq_div _ _).symm.trans (hPsi _ hab)

private theorem log_linear_precision {p r : ℕ}
    (hchar : residueCharacteristic L = p) {z : L} (hz : z ∈ lattice L (r : ℤ)) :
    truncatedLog p z - z ∈ lattice L (2 * (r : ℤ)) := by
  rw [truncatedLog_apply, add_sub_cancel_left]
  apply sum_mem_lattice L
  intro j hj
  obtain ⟨hj, hjp⟩ := Finset.mem_Ico.mp hj
  have hi : (j : L)⁻¹ ∈ lattice L 0 := by
    rw [mem_lattice, ord_inv,
      ord_natCast_eq_zero_of_lt_residueCharacteristic L (by omega) (hchar.symm ▸ hjp)]
    simp
  have hp := mul_mem_lattice L (pow_lattice L hz j) hi
  rw [div_eq_mul_inv]
  apply lattice_antitone L _ hp
  have hjZ : (2 : ℤ) ≤ j := by omega
  nlinarith

/-- Nontriviality on the whole predecessor unit group forces the exact
order of a coefficient of the full logarithm chart. -/
private theorem chart_order
    (theta : ContinuousQuasiChar L) (Psi : ContinuousAddChar L)
    {p m : ℕ} {J : ℤ} (hchar : residueCharacteristic L = p)
    (hm : 1 < m) (hcond : IsMultiplicativeConductor L theta m)
    (hPsi : AddCharTrivialOnLattice L Psi J)
    {B : L} (hB : B ∈ lattice L (J - (m : ℤ)))
    (hchart : ∀ z : lattice L ((m / 2 : ℕ) : ℤ),
      theta (positiveUnitOfLattice L (by omega) (-z)) = Psi (B * truncatedLog p (z : L))) :
    ord L B = ((J - (m : ℤ) : ℤ) : WithTop ℤ) := by
  rw [← mem_lattice_and_not_mem_succ_iff L]
  refine ⟨hB, ?_⟩
  intro hdeep
  apply (hcond.not_trivialOnUnitFiltration_iff.2 (by omega : m - 1 < m))
  intro u hu
  let z0 := truncatedLogUnitArgument L (by omega : 0 < m - 1)
    (⟨u, hu⟩ : unitFiltration L (m - 1))
  let z : lattice L ((m / 2 : ℕ) : ℤ) :=
    ⟨(z0 : L), lattice_antitone L (by omega) z0.property⟩
  have hz : (positiveUnitOfLattice L (by omega) (-z) : Lˣ) = u := by
    apply Units.ext
    change 1 + -(z : L) = (u : L)
    dsimp only [z, z0]
    rw [coe_truncatedLogUnitArgument]
    ring
  rw [← hz, hchart]
  apply hPsi
  have hlog : truncatedLog p (z : L) ∈ lattice L ((m - 1 : ℕ) : ℤ) :=
    (truncatedLogOnLattice L p (m - 1) hchar (by omega) z0).property
  exact lattice_antitone L (by omega) (mul_mem_lattice L hdeep hlog)

private theorem representative_of_depth
    (theta : ContinuousQuasiChar L) (Psi : ContinuousAddChar L)
    {p m : ℕ} {J : ℤ} (hchar : residueCharacteristic L = p) (hp : 2 < p)
    (hm : 1 < m) (hcond : IsMultiplicativeConductor L theta m)
    (hPsi : IsAdditiveConductor L Psi (-J))
    {B Z : L} (hB : B ∈ lattice L (J - (m : ℤ)))
    (hchart : ∀ z : lattice L ((m / 2 : ℕ) : ℤ),
      theta (positiveUnitOfLattice L (by omega) (-z)) = Psi (B * truncatedLog p (z : L)))
    (heta : Z - B ∈ lattice L (J - (((m + 1) / 2 : ℕ) : ℤ))) :
    NormDepthRepresentative L theta Psi p m J B Z := by
  have htriv : AddCharTrivialOnLattice L Psi J := by simpa using hPsi.trivial
  have hord := chart_order L theta Psi hchar hm hcond htriv hB hchart
  have hlt : ord L B < ord L (Z - B) := by
    rw [hord]
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) heta
  have hZord : ord L Z = ((J - (m : ℤ) : ℤ) : WithTop ℤ) := by
    simpa only [add_sub_cancel, hord] using (ord L).map_add_eq_of_lt_left hlt
  refine ⟨hm, hord, hZord, heta, hchart, ?_, ?_⟩
  · intro z
    let z0 : lattice L ((m / 2 : ℕ) : ℤ) :=
      ⟨(z : L), lattice_antitone L (by omega) z.property⟩
    rw [show theta (positiveUnitOfLattice L (by omega) (-z)) =
      Psi (B * truncatedLog p (z : L)) from hchart z0]
    apply phase_eq L Psi htriv
    have hlog := log_linear_precision L hchar z.property
    have hfirst := mul_mem_lattice L hB hlog
    have hsecond := mul_mem_lattice L heta z.property
    have hdiff : B * (truncatedLog p (z : L) - (z : L)) -
        (Z - B) * (z : L) ∈ lattice L J := sub_mem_lattice L
      (lattice_antitone L (by omega) hfirst) (lattice_antitone L (by omega) hsecond)
    convert hdiff using 1
    ring
  · intro hdeep
    constructor
    · intro z
      rw [hchart]
      apply phase_eq L Psi htriv
      have hlog : truncatedLog p (z : L) ∈ lattice L ((m / 2 : ℕ) : ℤ) :=
        (truncatedLogOnLattice L p (m / 2) hchar (by omega) z).property
      have hprod := mul_mem_lattice L hdeep hlog
      have hneg : -((Z - B) * truncatedLog p (z : L)) ∈ lattice L J :=
        neg_mem_lattice L (lattice_antitone L (by omega) hprod)
      convert hneg using 1
      ring
    · let thetaD : LocalQuasiCharData L := ⟨theta, m, hcond⟩
      let psiD : LocalAddCharData L := ⟨Psi, -J, hPsi⟩
      let Bu : Lˣ := Units.mk0 B ((ord_ne_top_iff L).1 (by rw [hord]; simp))
      have hBfull : IsEnhancedStationaryCoefficient L thetaD psiD p (m / 2)
          (by omega) J Bu := ⟨hord, hchart⟩
      exact enhancedCorrection_eq_one L thetaD psiD p (m / 2) (m % 2)
        (by omega) J Bu hchar (by omega) (by omega) (by dsimp [thetaD]; omega)
        (by simp [psiD]) hBfull (Z - B) hdeep

end Representatives

/-- The source-facing conclusion for the literal common element and its
two field norms. The representative assertions include exact orders and
whole-ideal character formulas; the endpoint residue retains `epsilon`. -/
def NormDepthsAt
    (F E U K : Type*) [Field F] [Field E] [Field U] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
    [Algebra F E] [Algebra F U] [Algebra E K] [Algebra U K]
    [ValuativeExtension F E] [ValuativeExtension F U]
    [Module.Finite F E] [Module.Finite F U]
    (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
    (Psi : ContinuousAddChar F) (p t h : ℕ) (c : F) (d : U) (x : E) (epsilon : F) : Prop :=
  let C := algebraMap E K x + algebraMap U K d
  let A := norm F E x
  let BU := algebraMap F U A + d ^ p + algebraMap F U epsilon
  let BE := algebraMap F E A - x + algebraMap F E c
  let ZU := norm U K C
  let ZE := norm E K C
  let PsiU := tracePullbackAddChar F U Psi
  let PsiE := tracePullbackAddChar F E Psi
  C ≠ 0 ∧
  ZU = d ^ p +
    (∑ i ∈ Finset.Ico 1 p, algebraMap F U (elementarySymmetric F E i x) * d ^ (p - i)) +
      algebraMap F U A ∧
  ZE = x ^ p - x + algebraMap F E c ∧
  ZU - BU ∈ lattice U ((((p : ℤ) - 1) * (t + 1 - h)) / p) ∧
  ZE - BE ∈ lattice E (((p : ℤ) - 1) * t - p * h) ∧
  NormDepthRepresentative U thetaU PsiU p (t + 1 + h) (t + 1) BU ZU ∧
  NormDepthRepresentative E thetaE PsiE p (t + 1 + p * h) (t + 1) BE ZE ∧
  (h < t →
    ZU - BU ∈ lattice U ((t : ℤ) + 1 - (((t + 1 + h) / 2 : ℕ) : ℤ)) ∧
    ZE - BE ∈ lattice E ((t : ℤ) + 1 - (((t + 1 + p * h) / 2 : ℕ) : ℤ)) ∧
    PsiU ((ZU - BU) ^ 2 / ((2 : U) * BU)) = 1 ∧
    PsiE ((ZE - BE) ^ 2 / ((2 : E) * BE)) = 1) ∧
  (3 < p → ZE - BE ∈ lattice E ((t : ℤ) + 1 - (((t + 1 + p * h) / 2 : ℕ) : ℤ))) ∧
  (h = t →
    elementarySymmetric F E (p - 1) x ∈ lattice F 0 ∧
    (ZU - BU) -
      (algebraMap F U (elementarySymmetric F E (p - 1) x) * d - algebraMap F U epsilon) ∈
        lattice U 1)

section Assembly
variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]
  (E U : IntermediateField F K)
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeExtension F E] [ValuativeExtension F U]
  [ValuativeExtension E K] [ValuativeExtension U K]
  [PrimeCyclicExtension F E] [PrimeCyclicExtension F U]
  [PrimeCyclicExtension E K] [PrimeCyclicExtension U K]

local instance : IsGalois F E := PrimeCyclicExtension.instIsGalois F E
local instance : IsGalois F U := PrimeCyclicExtension.instIsGalois F U
local instance : IsGalois E K := PrimeCyclicExtension.instIsGalois E K
local instance : IsGalois U K := PrimeCyclicExtension.instIsGalois U K

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] [ValuativeExtension E K] [ValuativeExtension U K] in
set_option maxHeartbeats 600000 in
private theorem normDepths_at
    {p t h : ℕ} (hp : p.Prime) (hodd : 2 < p) (htpos : 0 < t) (hh : h ≤ t)
    (hFE : Module.finrank F E = p) (hFU : Module.finrank F U = p)
    (hEK : Module.finrank E K = p) (hUK : Module.finrank U K = p)
    (hchar : residueCharacteristic F = p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hres : residueDegree F E = 1)
    (hunr : ramificationIndex F U = 1) (hsup : E ⊔ U = ⊤)
    (c : ringOfIntegers F) (d : ringOfIntegers U)
    (hd : (d : U) ^ p - (d : U) = algebraMap F U (c : F))
    (hgen : IntermediateField.adjoin F {(d : U)} = ⊤)
    (thetaU : ContinuousQuasiChar U) (thetaE : ContinuousQuasiChar E)
    (hcondU : IsMultiplicativeConductor U thetaU (t + 1 + h))
    (hcondE : IsMultiplicativeConductor E thetaE (t + 1 + p * h))
    (Psi : LocalAddCharData F) (hPsi : Psi.conductor = -((t + 1 : ℕ) : ℤ))
    (x : E) (epsilon : F) (hx : x ∈ lattice E (-(h : ℤ)))
    (hepsilon : epsilon ∈ lattice F 0) (hepsilon_zero : h < t → epsilon = 0)
    (hchartU : ∀ z : lattice U (((t + 1 + h) / 2 : ℕ) : ℤ),
      thetaU (positiveUnitOfLattice U (normChoice_depths hodd htpos).1 (-z)) =
        tracePullbackAddChar F U Psi.character
          ((algebraMap F U (norm F E x) + (d : U) ^ p + algebraMap F U epsilon) *
            truncatedLog p (z : U)))
    (hchartE : ∀ z : lattice E (((t + 1 + p * h) / 2 : ℕ) : ℤ),
      thetaE (positiveUnitOfLattice E (normChoice_depths hodd htpos).1 (-z)) =
        tracePullbackAddChar F E Psi.character
          ((algebraMap F E (norm F E x) - x + algebraMap F E (c : F)) *
            truncatedLog p (z : E))) :
    NormDepthsAt F E U K thetaU thetaE Psi.character p t h (c : F) (d : U) x epsilon := by
  letI : Infinite F := local_infinite F
  let C : K := (x : K) + ((d : U) : K)
  let A := norm F E x
  let BU := algebraMap F U A + (d : U) ^ p + algebraMap F U epsilon
  let BE := algebraMap F E A - x + algebraMap F E (c : F)
  let ZU := norm U K C
  let ZE := norm E K C
  let q : ℤ := (((p : ℤ) - 1) * (t + 1 - h)) / p
  have hpo : Odd p := hp.odd_of_ne_two (by omega)
  have hdmem : (d : U) ∈ lattice U 0 := (mem_lattice_zero_iff U).2 d.property
  have hZU : ZU = (d : U) ^ p + normDepths_symmetricSum F E U p x d + algebraMap F U A := by
    have he := normDepths_norm_expansion F K E U hsup (hFE.trans hUK.symm) x (d : U)
    rw [hFE, sum_endpoints hp.pos] at he
    rw [elementarySymmetric_zero, map_one, one_mul, Nat.sub_zero,
      Nat.sub_self, pow_zero, mul_one] at he
    have hend : elementarySymmetric F E p x = norm F E x := by
      rw [← hFE, elementarySymmetric_finrank]
    rw [hend] at he
    exact he
  have hZE : ZE = x ^ p - x + algebraMap F E (c : F) :=
    normDepths_norm_E F K E U hpo hodd hFU hEK hsup (c : F) (d : U) hd hgen x
  have hetaU : ZU - BU = normDepths_symmetricSum F E U p x d - algebraMap F U epsilon := by
    dsimp only [BU]
    rw [hZU]
    ring
  have hetaE : ZE - BE = x ^ p - algebraMap F E A := by
    dsimp only [BE]
    rw [hZE]
    ring
  have hepsq : algebraMap F U epsilon ∈ lattice U q := by
    by_cases hlt : h < t
    · simp [hepsilon_zero hlt]
    · have heq : h = t := by omega
      have hq : q = 0 := by
        dsimp [q]
        rw [heq]
        simp only [add_sub_cancel_left, mul_one]
        exact Int.ediv_eq_zero_of_lt (by omega) (by omega)
      rw [hq]
      simpa only [hunr, Nat.cast_one, one_mul] using map_lattice F U hepsilon
  have hUbound : ZU - BU ∈ lattice U q := by
    rw [hetaU]
    exact sub_mem_lattice U
      (normDepths_sum_bound F E U hodd hFE htpos hchar ht hres hunr hx hdmem) hepsq
  have hEbound : ZE - BE ∈ lattice E (((p : ℤ) - 1) * t - p * h) := by
    rw [hetaE]
    exact normDepths_power_bound F E hpo hFE htpos hchar ht hres hx
  obtain ⟨hUord, hEord, henh, hEenh⟩ := normDepths_arithmetic
    (by omega : (3 : ℤ) ≤ p) (by omega : (1 : ℤ) ≤ t)
    (by omega : (0 : ℤ) ≤ h) (by omega : (h : ℤ) ≤ t)
  have hUordinary : ZU - BU ∈ lattice U
      ((t : ℤ) + 1 - (((t + 1 + h + 1) / 2 : ℕ) : ℤ)) := by
    apply lattice_antitone U _ hUbound
    simpa only [Int.natCast_ediv, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      add_assoc, add_left_comm, add_comm, show (1 : ℤ) + 1 = 2 by norm_num, q] using hUord
  have hEordinary : ZE - BE ∈ lattice E
      ((t : ℤ) + 1 - (((t + 1 + p * h + 1) / 2 : ℕ) : ℤ)) := by
    apply lattice_antitone E _ hEbound
    simpa only [Int.natCast_ediv, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat, add_assoc, add_left_comm, add_comm, show (1 : ℤ) + 1 = 2 by norm_num] using hEord
  have henhanced : h < t →
      ZU - BU ∈ lattice U ((t : ℤ) + 1 - (((t + 1 + h) / 2 : ℕ) : ℤ)) ∧
      ZE - BE ∈ lattice E ((t : ℤ) + 1 - (((t + 1 + p * h) / 2 : ℕ) : ℤ)) := by
    intro hlt
    obtain ⟨hu, he⟩ := henh (by omega : (h : ℤ) < t)
    constructor
    · apply lattice_antitone U _ hUbound
      simpa only [Int.natCast_ediv, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hu
    · apply lattice_antitone E _ hEbound
      simpa only [Int.natCast_ediv, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using he
  have hram : ramificationIndex F E = p := by
    have he := finrank_eq_ramificationIndex_mul_residueDegree F E
    simpa only [hFE, hres, mul_one] using he.symm
  have hA : A ∈ lattice F (-(h : ℤ)) := by
    simpa only [A, mem_lattice, ord_norm, hres, one_nsmul] using hx
  have hBU : BU ∈ lattice U ((t : ℤ) + 1 - ((t + 1 + h : ℕ) : ℤ)) := by
    have hAU := map_lattice F U hA
    simp only [hunr, Nat.cast_one, one_mul] at hAU
    have hdU : (d : U) ^ p ∈ lattice U 0 := by simpa using pow_lattice U hdmem p
    have hepsU : algebraMap F U epsilon ∈ lattice U 0 := by
      simpa only [mul_zero] using map_lattice F U hepsilon
    exact add_mem_lattice U (add_mem_lattice U
      (lattice_antitone U (by omega) hAU) (lattice_antitone U (by omega) hdU))
      (lattice_antitone U (by omega) hepsU)
  have hBE : BE ∈ lattice E ((t : ℤ) + 1 - ((t + 1 + p * h : ℕ) : ℤ)) := by
    have hAE := map_lattice F E hA
    rw [hram] at hAE
    have hcE := map_lattice F E ((mem_lattice_zero_iff F).2 c.property)
    have hpZ : (1 : ℤ) ≤ p := by omega
    apply add_mem_lattice E
    · apply sub_mem_lattice E
      · apply lattice_antitone E _ hAE
        push_cast
        ring_nf
        exact le_rfl
      · apply lattice_antitone E _ hx
        push_cast
        nlinarith
    · apply lattice_antitone E _ hcE
      push_cast
      nlinarith
  have hPsiF : IsAdditiveConductor F Psi.character (-((t + 1 : ℕ) : ℤ)) := hPsi ▸ Psi.isConductor
  have hPsiU : IsAdditiveConductor U (tracePullbackAddChar F U Psi.character)
      (-((t : ℤ) + 1)) :=
    (unramified_additiveConductor_compTrace F U hunr Psi.character _).2 hPsiF
  have hPsiE : IsAdditiveConductor E (tracePullbackAddChar F E Psi.character)
      (-((t : ℤ) + 1)) := by
    obtain ⟨pi, hpi, hg⟩ := monogenicUniformizer F E hres
    have he := additiveConductor_compTrace_cyclicPrime F E ht hres pi hpi hg hPsiF
    change IsAdditiveConductor E Psi.character.compTrace _
    convert he using 1
    rw [hFE]
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    push_cast
    ring
  have hcharU : residueCharacteristic U = p := (residueCharacteristic_extension_eq F U).trans hchar
  have hcharE : residueCharacteristic E = p := (residueCharacteristic_extension_eq F E).trans hchar
  have hrepU := representative_of_depth U thetaU (tracePullbackAddChar F U Psi.character)
    hcharU hodd (by omega) hcondU hPsiU hBU hchartU hUordinary
  have hrepE := representative_of_depth E thetaE (tracePullbackAddChar F E Psi.character)
    hcharE hodd (by omega) hcondE hPsiE hBE hchartE hEordinary
  have hCne : C ≠ 0 := by
    intro hzero
    have hz := hrepU.numerator_order
    change ord U (norm U K C) = _ at hz
    rw [hzero, Algebra.norm_zero, ord_zero] at hz
    exact WithTop.top_ne_coe hz
  refine ⟨hCne, hZU, hZE, hUbound, hEbound, hrepU, hrepE, ?_, ?_, ?_⟩
  · intro hlt
    obtain ⟨hu, he⟩ := henhanced hlt
    exact ⟨hu, he, (hrepU.enhanced hu).2, (hrepE.enhanced he).2⟩
  · intro hp3
    apply lattice_antitone E _ hEbound
    have hp5 : (5 : ℤ) ≤ p := by
      have hpo' := hpo
      obtain ⟨k, hk⟩ := hpo'
      omega
    simpa only [Int.natCast_ediv, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using hEenh hp5
  · intro heq
    obtain ⟨hb, hr⟩ := normDepths_boundary_residue F E U hodd hFE htpos hchar ht hres hunr
      (by simpa only [heq] using hx) hdmem
    refine ⟨hb, ?_⟩
    change (ZU - BU) -
      (algebraMap F U (elementarySymmetric F E (p - 1) x) * (d : U) -
        algebraMap F U epsilon) ∈ lattice U 1
    rw [hetaU]
    convert hr using 1
    ring

/-- Lemma 6.10 (`O:I:normdepths`) for the actual character pair.

The exact norm witness and the full character charts are constructed by
`coefficients`. `E` and `U` are the actual intermediate fields, with `K = EU`.
The conclusion retains the endpoint coefficient error and the zero-class
convention, and supplies ordinary/enhanced representatives for both literal
norms of `x + d`, together with the complete affine correction values. -/
theorem normDepths
    {p t q : ℕ} (hp : p.Prime) (hodd : 2 < p) (htpos : 0 < t)
    (hFE : Module.finrank F E = p) (hFU : Module.finrank F U = p)
    (hEK : Module.finrank E K = p) (hUK : Module.finrank U K = p)
    (hchar : residueCharacteristic F = p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (hres : residueDegree F E = 1)
    (hunr : ramificationIndex F U = 1) (hsup : E ⊔ U = ⊤)
    (hq : q = (t + 1) ⌈/⌉ p) {hqpos : 0 < q}
    (tau : NormCharacter F E) (htaune : tau ≠ 1)
    (Psi : LocalAddCharData F) (hPsi : Psi.conductor = -((t + 1 : ℕ) : ℤ))
    (htau : ∀ z : lattice F (q : ℤ),
      tau.1 (positiveUnitOfLattice F hqpos (-z)) = Psi.character (truncatedLog p (z : F)))
    (c : ringOfIntegers F) (d : ringOfIntegers U)
    (hd : (d : U) ^ p - (d : U) = algebraMap F U (c : F))
    (hgen : IntermediateField.adjoin F {(d : U)} = ⊤)
    {M : CompatibleModels F E U K p (t + 1) q hqpos tau.1 Psi.character (c : F) (d : U)}
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
      NormDepthsAt F E U K thetaU thetaE Psi.character p t D.h (c : F) (d : U) x epsilon := by
  obtain ⟨x, epsilon, hepsilon, hepsilon_zero, hchart, horder, hintegral, hzero, hU, hE⟩ :=
    coefficients F E U K hp hodd htpos hFE hFU hchar ht hres hunr hq tau htaune Psi hPsi htau D hh
  have hx : x ∈ lattice E (-(D.h : ℤ)) := by
    by_cases hhzero : D.h = 0
    · simpa only [hhzero, Nat.cast_zero, neg_zero] using hintegral hhzero
    · rw [mem_lattice, (horder (by omega)).1]
  refine ⟨x, epsilon, hepsilon, hepsilon_zero, hchart, horder, hintegral, hzero, ?_⟩
  exact normDepths_at F K E U hp hodd htpos hh hFE hFU hEK hUK hchar ht hres hunr hsup
    c d hd hgen thetaU thetaE D.conductorU D.conductorE Psi hPsi x epsilon hx hepsilon
    hepsilon_zero hU hE

end Assembly
end
end LanglandsSecondMainLemma.Odd.UR
