import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.R2.Trace

/-!
# Odd / R2 / Reciprocal

Blueprint: blueprint/tasks/Odd/R2/Reciprocal.md
Paper: Lemma 8.12 (`O:R:reciprocal`), lines 2902--2919,
with the normalization at lines 2782--2810.

Characteristic-polynomial reciprocity gives the exact trace of `Delta⁻¹`.
The exact Artin--Schreier polynomial supplies its coefficient `-1` on the
second upper edge. Trace transitivity identifies the two additive phases;
norm transitivity then identifies the two lower norms. The actual second
lower norm character supplies the conversion on the whole required ideal.
-/

namespace LanglandsSecondMainLemma.Odd.R2

noncomputable section
open LanglandsFirstMainLemma Polynomial
set_option backward.isDefEq.respectTransparency false

/-- Exact reciprocal trace in odd degree. Matrix inversion reverses the
characteristic polynomial, so its coefficient of degree one gives the
trace of the reciprocal. The element is explicitly nonzero. -/
private theorem reciprocal_trace_inv
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    [Module.Finite E L] {p : ℕ} (hp : Odd p) (hp1 : 1 < p)
    (hdegree : Module.finrank E L = p) (x : L) (hx : x ≠ 0) :
    LanglandsFirstMainLemma.trace E L x⁻¹ =
      elementarySymmetric E L (p - 1) x / norm E L x := by
  classical
  let b := Module.Free.chooseBasis E L
  let M := Algebra.leftMulMatrix b x
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex E L) = p :=
    (Module.finrank_eq_card_basis b).symm.trans hdegree
  haveI : Nonempty (Module.Free.ChooseBasisIndex E L) :=
    Fintype.card_pos_iff.mp (by rw [hcard]; omega)
  have hM : IsUnit M := (isUnit_iff_ne_zero.mpr hx).map (Algebra.leftMulMatrix b)
  have hinv : M⁻¹ = Algebra.leftMulMatrix b x⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [← map_mul, inv_mul_cancel₀ hx, map_one]
  have heven : Even (p - 1) := by
    obtain ⟨k, hk⟩ := hp
    exact ⟨k, by omega⟩
  have hpoly : M.charpoly = (Algebra.lmul E L x).charpoly := by
    exact LinearMap.charpoly_toMatrix _ b
  rw [trace_apply, Algebra.trace_eq_matrix_trace b, ← hinv,
    Matrix.trace_eq_neg_charpoly_coeff, Matrix.charpoly_inv M hM,
    ← Matrix.reverse_charpoly, hcard]
  have hsign : ((-1 : E[X]) ^ p) = C (-1 : E) := by rw [hp.neg_one_pow]; simp
  rw [hsign, ← C_mul, coeff_C_mul, coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
    hcard, revAt_le (by omega), Nat.sub_sub_self (by omega : 1 ≤ p),
    Ring.inverse_eq_inv, hpoly]
  rw [elementarySymmetric, hdegree, if_pos (by omega : p - 1 ≤ p),
    heven.neg_one_pow, one_mul, Nat.sub_sub_self (by omega : 1 ≤ p)]
  rw [norm_apply, Algebra.norm_eq_matrix_det b]
  dsimp only [M]
  ring

/-- The coefficient of degree one is literally `-1`, in either characteristic. -/
private theorem reciprocal_artinSchreier_coefficient
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    [Module.Finite E L] {p : ℕ} (hp : Odd p) (hp2 : 2 < p)
    (hdegree : Module.finrank E L = p) (x : L) (a : E)
    (hroot : x ^ p - x = algebraMap E L a)
    (hgen : Algebra.adjoin E ({x} : Set L) = ⊤) :
    elementarySymmetric E L (p - 1) x = -1 := by
  let pb := PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral (R := E) x) hgen
  have hdim : pb.dim = p := pb.finrank.symm.trans hdegree
  have hpoly : (Algebra.lmul E L x).charpoly = X ^ p - X - C a := by
    calc
      _ = (Algebra.leftMulMatrix pb.basis pb.gen).charpoly := by
        rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix,
          PowerBasis.ofAdjoinEqTop_gen]
      _ = minpoly E pb.gen := charpoly_leftMulMatrix pb
      _ = X ^ p - X - C a := Total.artinSchreier_minpoly pb hp2 hdim a hroot
  have heven : Even (p - 1) := by
    obtain ⟨k, hk⟩ := hp
    exact ⟨k, by omega⟩
  rw [elementarySymmetric, hdegree, if_pos (by omega : p - 1 ≤ p),
    heven.neg_one_pow, one_mul, Nat.sub_sub_self (by omega : 1 ≤ p), hpoly]
  simp [show 1 ≠ p by omega]

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

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

local notation "B₁" => D.B₁
local notation "B₂" => D.B₂

local instance : PrimeCyclicExtension F B₂ :=
  PrimeCyclicExtension.ofCyclicPrimeExtension F B₂
    (Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂).2.2.2.2.2.2.2.2.2.2.2.1

open private realization_tower_data from LanglandsSecondMainLemma.Odd.Models.Realization
open private norm_artinSchreierCoordinate additiveConductor_of_normCharacterChart from
  LanglandsSecondMainLemma.Odd.Models.Setup

include hp hG hres hchar D

/-- **Paper Lemma 8.12 (`O:R:reciprocal`).** In the one-break case,
for every `Y` in the actual valuation ring of the base field,
`Psi₁(sY/b) = Psi₂(Y/a) = Psi(-n₁(Y/b))`.

Here `b` is the actual upper norm and `s` is the signed elementary
symmetric coefficient. The proof identifies `a` with the other upper
norm and returns nonvanishing of both denominators. The normalized
character is the supplied nontrivial `tau₂`, on its full logarithm chart;
its exact additive conductor is deduced from that chart. The coordinate
hypotheses are those supplied by the accepted realization constructor,
with its exact root and generation properties, in either characteristic. -/
theorem reciprocal
    (hdelta : D.delta = 0)
    (q : ℕ) (hq : q = (D.t₂ + 1) ⌈/⌉ p) (hqpos : 0 < q)
    (tau₂ : NormCharacter F B₂) (htau₂ : tau₂ ≠ 1)
    (Psi : ContinuousAddChar F)
    (hchart₂ : ∀ z : lattice F (q : ℤ),
      tau₂.1 (positiveUnitOfLattice F hqpos (-z)) = Psi (truncatedLog p (z : F)))
    (Delta : K) (a : B₂)
    (hroot : Delta ^ p - Delta = algebraMap B₂ K a)
    (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hgen : Algebra.adjoin B₂ ({Delta} : Set K) = ⊤) :
    let b := norm B₁ K Delta
    let s := -elementarySymmetric B₁ K (p - 1) Delta
    a ≠ 0 ∧ b ≠ 0 ∧ ∀ Y : ringOfIntegers F,
      tracePullbackAddChar F B₁ Psi (s * algebraMap F B₁ (Y : F) / b) =
        tracePullbackAddChar F B₂ Psi (algebraMap F B₂ (Y : F) / a) ∧
      tracePullbackAddChar F B₂ Psi (algebraMap F B₂ (Y : F) / a) =
        Psi (-norm F B₁ (algebraMap F B₁ (Y : F) / b)) := by
  classical
  obtain ⟨hdegree₁, _, hres₁K, _, _⟩ :=
    realization_tower_data hp hG hres B₁ D.degree_B₁
  obtain ⟨hdegree₂, hres₂, hres₂K, hram₂, _⟩ :=
    realization_tower_data hp hG hres B₂ D.degree_B₂
  have hdegreeF₁ : Module.finrank F B₁ = p := D.degree_B₁
  have hdegreeF₂ : Module.finrank F B₂ = p := D.degree_B₂
  have hpOdd := hp.odd_of_ne_two (by have := D.odd_prime; omega)
  have hDeltaNe : Delta ≠ 0 := (ord_ne_top_iff K).1 (by
    rw [hDelta]; exact WithTop.coe_ne_top)
  have hnorma : norm B₂ K Delta = a :=
    norm_artinSchreierCoordinate B₂ K hp D.odd_prime hdegree₂ Delta a hroot hgen
  have haord : ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) := by
    rw [← hnorma, ord_norm, hres₂K, one_nsmul, hDelta]
  have ha : a ≠ 0 := (ord_ne_top_iff B₂).1 (by
    rw [haord]; exact WithTop.coe_ne_top)
  have hb : norm B₁ K Delta ≠ 0 := (ord_ne_top_iff B₁).1 (by
    rw [ord_norm, hres₁K, one_nsmul, hDelta]; exact WithTop.coe_ne_top)
  refine ⟨ha, hb, ?_⟩
  intro Y
  have htrace₁ := reciprocal_trace_inv B₁ K hpOdd hp.one_lt hdegree₁ Delta hDeltaNe
  have htrace₂ : LanglandsFirstMainLemma.trace B₂ K Delta⁻¹ = -1 / a := by
    rw [reciprocal_trace_inv B₂ K hpOdd hp.one_lt hdegree₂ Delta hDeltaNe,
      reciprocal_artinSchreier_coefficient B₂ K hpOdd D.odd_prime hdegree₂
        Delta a hroot hgen, hnorma]
  -- Both upper traces are taken on the same actual element of `K`.
  have hscalar (E : IntermediateField F K) :
      LanglandsFirstMainLemma.trace E K (algebraMap F K (Y : F) / Delta) =
        algebraMap F E (Y : F) * LanglandsFirstMainLemma.trace E K Delta⁻¹ := by
    rw [IsScalarTower.algebraMap_apply F E K, div_eq_mul_inv,
      ← Algebra.smul_def, map_smul, smul_eq_mul]
  have hfirst :
      LanglandsFirstMainLemma.trace F B₁
          (-elementarySymmetric B₁ K (p - 1) Delta * algebraMap F B₁ (Y : F) /
            norm B₁ K Delta) =
        LanglandsFirstMainLemma.trace F B₂ (algebraMap F B₂ (Y : F) / a) := by
    calc
      _ = -LanglandsFirstMainLemma.trace F B₁
          (LanglandsFirstMainLemma.trace B₁ K (algebraMap F K (Y : F) / Delta)) := by
        rw [hscalar, htrace₁, ← map_neg]
        congr 1
        ring
      _ = -LanglandsFirstMainLemma.trace F K (algebraMap F K (Y : F) / Delta) := by
        rw [trace_trans]
      _ = -LanglandsFirstMainLemma.trace F B₂
          (LanglandsFirstMainLemma.trace B₂ K (algebraMap F K (Y : F) / Delta)) := by
        rw [trace_trans]
      _ = _ := by
        rw [hscalar, htrace₂, ← map_neg]
        congr 1
        ring
  constructor
  · simpa only [tracePullbackAddChar_apply] using congrArg Psi hfirst
  -- The one-break hypothesis puts every integral numerator in the full
  -- norm-phase domain, including the zero numerator.
  have ht₂ : D.t₂ = D.t := by rw [D.t₂_eq, hdelta, add_zero]
  have hqt : q ≤ D.t := by
    rw [hq, ht₂, ceilDiv_le_iff_le_mul hp.pos]
    have hmul := Nat.mul_le_mul_right D.t hp.two_le
    have := D.t_pos
    omega
  have hY : algebraMap F B₂ (Y : F) ∈ lattice B₂ 0 := by
    rw [mem_lattice, ord_algebraMap, hram₂]
    have h := (mem_lattice F).1 ((mem_lattice_zero_iff F).2 Y.property)
    simpa using nsmul_le_nsmul_right h p
  have hquot : algebraMap F B₂ (Y : F) / a ∈ lattice B₂ (q : ℤ) := by
    apply (div_mem_lattice_iff B₂ a _ (-(D.t : ℤ)) (q : ℤ) haord).2
    exact lattice_antitone B₂ (by omega) hY
  have hPsi := additiveConductor_of_normCharacterChart F B₂ hp D.odd_prime hchar
    D.degree_B₂ D.B₂_breaks.1 (D.t_pos.trans_le D.t_le_t₂) hres₂
    hq hqpos tau₂ htau₂ Psi hchart₂
  have hphase := (normPhase F B₂ D.B₂_breaks.1 (D.t_pos.trans_le D.t_le_t₂)
    hres₂ (hchar.trans hdegreeF₂.symm) (by rw [hdegreeF₂]; have := D.odd_prime; omega)
    q (by simpa only [hdegreeF₂] using hq) hqpos tau₂ htau₂ Psi hPsi
    (by simpa only [hdegreeF₂] using hchart₂) _ hquot).2
  -- The lower norms coincide exactly, with the same degree `p` on both edges.
  have hnorms : norm F B₂ (algebraMap F B₂ (Y : F) / a) =
      norm F B₁ (algebraMap F B₁ (Y : F) / norm B₁ K Delta) := by
    simp only [div_eq_mul_inv, map_mul, LanglandsFirstMainLemma.norm_algebraMap,
      hdegreeF₁, hdegreeF₂, Algebra.norm_inv, ← hnorma, norm_trans]
  exact hphase.trans (congrArg (fun z => Psi (-z)) hnorms)

end Diamond

end
end LanglandsSecondMainLemma.Odd.R2
