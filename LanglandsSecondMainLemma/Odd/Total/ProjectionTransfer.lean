import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Total.CoefficientExtraction
import LanglandsSecondMainLemma.Odd.Total.TwistedEstimates
import Mathlib.FieldTheory.LinearDisjoint

/-!
# Odd / Total / Projection Transfer

Paper `O:A:lem:H17`, with `K₀ = 1 + p*t₂`. All lattices have integer
indices, and the two norms in the conclusion have their actual domains.
-/

namespace LanglandsSecondMainLemma.Odd.Total

open LanglandsFirstMainLemma
open scoped BigOperators

noncomputable section

/-- A norm perturbation, with the terminal coefficient kept as the actual
norm of the perturbation. This uses multiplicativity even when the first
factor does not belong to the base field. -/
theorem norm_add_sub_mem_of_symmetric
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra E L] [Module.Free E L] [Module.Finite E L]
    {u v : L} (hu : u ≠ 0) (k : ℤ)
    (hcoeff : ∀ j : ℕ, 1 ≤ j → j < Module.finrank E L →
      norm E L u * elementarySymmetric E L j (v / u) ∈ lattice E k)
    (hend : norm E L v ∈ lattice E k) :
    norm E L (u + v) - norm E L u ∈ lattice E k := by
  have hfactor : u + v = u * (1 + v / u) := by field_simp
  rw [hfactor, map_mul, norm_one_add_eq_one_add_sum_elementarySymmetric,
    mul_add, mul_one, add_sub_cancel_left, Finset.mul_sum]
  apply sum_mem_lattice E
  intro j hj
  have hjlt := Finset.mem_range.mp hj
  by_cases hjend : j + 1 = Module.finrank E L
  · rw [hjend, elementarySymmetric_finrank]
    have heq : norm E L u * norm E L (v / u) = norm E L v := by
      rw [← map_mul]
      congr 1
      field_simp
    simpa only [heq] using hend
  · exact hcoeff (j + 1) (by omega) (by omega)

/-- The integer floor comparison in the higher-degree part of H17.
The positive remainder `(p-3)*t+p-1` is retained. -/
theorem projectionTransfer_floor_bound
    {p t t₂ t' : ℕ} (hp : 3 ≤ p) (_ht : 0 < t)
    (_ht₂ : t ≤ t₂) (hbreak : (t' : ℤ) = t + p * ((t₂ : ℤ) - t))
    {h : ℤ} (hh : 1 + t₂ + ((p : ℤ) - 3) * t ≤ h)
    {j : ℕ} (hj : 1 ≤ j) :
    1 + (p : ℤ) * t₂ + (((p : ℤ) - 3) * t + p - 1) / p ≤
      h + (2 * j * ((p : ℤ) - 1) * t +
        ((p : ℤ) - 1) * ((t' : ℤ) + 1)) / p := by
  have hpZ : (0 : ℤ) < p := by omega
  have hnum :
      (1 + (p : ℤ) * t₂ - h) * p + (((p : ℤ) - 3) * t + p - 1) ≤
        2 * j * ((p : ℤ) - 1) * t + ((p : ℤ) - 1) * ((t' : ℤ) + 1) := by
    rw [hbreak]
    have hprod := mul_nonneg (show (0 : ℤ) ≤ j - 1 by omega)
      (mul_nonneg (show (0 : ℤ) ≤ p - 1 by omega) (Int.natCast_nonneg t))
    have hhprod := mul_le_mul_of_nonneg_right hh hpZ.le
    nlinarith
  have hdiv := Int.ediv_le_ediv hpZ hnum
  rw [Int.add_ediv_of_dvd_left (dvd_mul_left _ _), Int.mul_ediv_cancel _ hpZ.ne'] at hdiv
  omega

/-- Strong symmetric bounds directly from the exact trace ideal on an
actual totally ramified prime cyclic edge. -/
theorem cyclic_symmetric_mem
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    [Module.Free E L] [Module.Finite E L] [PrimeCyclicExtension E L]
    {p t : ℕ} (hp : p.Prime) (ht : 0 < t)
    (hdegree : Module.finrank E L = p) (hres : residueDegree E L = 1)
    (hchar : residueCharacteristic E = p)
    (hbreak : PrimeCyclicExtension.IsLowerBreak E L t)
    {q : ℤ} {z : L} (hz : z ∈ lattice L q)
    {j : ℕ} (hj : 1 ≤ j) (hjp : j < p) :
    elementarySymmetric E L j z ∈
      lattice E (((j : ℤ) * q + ((p : ℤ) - 1) * ((t : ℤ) + 1)) / p) := by
  have hram : ramificationIndex E L = p := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree E L
    simpa [hres, hdegree] using h.symm
  obtain ⟨pi, hpi, hgen⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one E L hres
  have hdiff : differentExponent E L = ((p : ℤ) - 1) * ((t : ℤ) + 1) := by
    rw [differentExponent_eq E L hbreak pi hpi hgen, hdegree]
    push_cast [Nat.cast_sub hp.one_le]
    rfl
  have htrace : TraceIdealLowerBound E L p (((p - 1) * (t + 1) : ℕ) : ℤ) := by
    intro a x hx
    have himage : trace E L x ∈ Submodule.map
        ((trace E L).restrictScalars (ringOfIntegers E))
        ((lattice L a).restrictScalars (ringOfIntegers E)) :=
      Submodule.mem_map.mpr ⟨x, (mem_lattice L).2 hx, rfl⟩
    rw [Local.traceIdeal_eq_fml E L hres a, hram, hdiff] at himage
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hp.one_le] using
      (mem_lattice E).1 himage
  have h := wild_elementarySymmetric_bound E L p (t + 1) q hp (by omega)
    hchar hdegree htrace ((mem_lattice L).1 hz) hj hjp
  simpa only [mem_lattice, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_sub hp.one_le] using h

/-- The final, integral, lower-edge comparison in H17. No surjectivity of
a critical norm map is asserted or used. -/
theorem cyclic_norm_sub_mem_of_integral
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    [Module.Free E L] [Module.Finite E L] [PrimeCyclicExtension E L]
    {p t : ℕ} (hp : p.Prime) (ht : 0 < t)
    (hdegree : Module.finrank E L = p) (hres : residueDegree E L = 1)
    (hchar : residueCharacteristic E = p)
    (hbreak : PrimeCyclicExtension.IsLowerBreak E L t)
    {y z : L} (hy : y ∈ lattice L 0) (hz : z - y ∈ lattice L ((t : ℤ) + 1)) :
    norm E L z - norm E L y ∈ lattice E ((t : ℤ) + 1) := by
  have hn (x : L) (hx : x ∈ lattice L ((t : ℤ) + 1)) :
      norm E L x ∈ lattice E ((t : ℤ) + 1) := by
    simpa only [mem_lattice, ord_norm, hres, one_nsmul] using hx
  by_cases hyzero : y = 0
  · subst y
    simpa only [sub_zero, norm_apply, Algebra.norm_zero] using hn z (by simpa using hz)
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff L).2 hyzero)
  have ha0 : 0 ≤ a := by simpa only [mem_lattice, ← ha, WithTop.coe_le_coe] using hy
  by_cases hadeep : (t : ℤ) + 1 ≤ a
  · have hydeep : y ∈ lattice L ((t : ℤ) + 1) := by
      simpa only [mem_lattice, ← ha, WithTop.coe_le_coe] using hadeep
    have hzdeep : z ∈ lattice L ((t : ℤ) + 1) := by
      simpa using (lattice L _).add_mem hz hydeep
    exact (lattice E _).sub_mem (hn z hzdeep) (hn y hydeep)
  have haT : a < (t : ℤ) + 1 := lt_of_not_ge hadeep
  have hratio : (z - y) / y ∈ lattice L ((t : ℤ) + 1 - a) := by
    rw [div_eq_mul_inv]
    have hyinv : y⁻¹ ∈ lattice L (-a) := by
      simp [mem_lattice, ← ha]
    simpa only [sub_eq_add_neg] using mul_mem_lattice L hz hyinv
  have hnormy : ord E (norm E L y) = (a : WithTop ℤ) := by
    rw [ord_norm, hres, one_nsmul, ← ha]
  have hresult := norm_add_sub_mem_of_symmetric E L hyzero ((t : ℤ) + 1)
    (v := z - y) (fun j hj hjp => ?_) (hn (z - y) hz)
  · simpa only [add_sub_cancel] using hresult
  have hs := cyclic_symmetric_mem E L hp ht hdegree hres hchar hbreak hratio hj
    (by simpa only [hdegree] using hjp)
  have hfloor : (t : ℤ) + 1 ≤ a +
      ((j : ℤ) * ((t : ℤ) + 1 - a) + ((p : ℤ) - 1) * ((t : ℤ) + 1)) / p := by
    have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
    have hprod := mul_nonneg (show (0 : ℤ) ≤ j - 1 by omega) (sub_nonneg.mpr haT.le)
    have hp1 : (0 : ℤ) ≤ p - 1 := by have := hp.one_le; omega
    have hpa := mul_nonneg hp1 ha0
    have h : ((t : ℤ) + 1 - a) * p ≤
        (j : ℤ) * ((t : ℤ) + 1 - a) + ((p : ℤ) - 1) * ((t : ℤ) + 1) := by
      nlinarith
    have := (Int.le_ediv_iff_mul_le hpZ).2 h
    omega
  rw [mem_lattice, ord_mul, hnormy]
  exact (WithTop.coe_le_coe.mpr hfloor).trans (by
    simpa only [WithTop.coe_add, add_comm] using
      add_le_add_left ((mem_lattice E).1 hs) (a : WithTop ℤ))

/-- H17's higher-degree tail estimate on the upper edge. The relative
error and absolute error are separate inputs; both are used. -/
theorem projectionTransfer_tail
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    [Module.Free E L] [Module.Finite E L] [PrimeCyclicExtension E L]
    {p t t₂ t' : ℕ} (hp : p.Prime) (hodd : 2 < p) (ht : 0 < t)
    (ht₂ : t ≤ t₂) (hbreaks : (t' : ℤ) = t + p * ((t₂ : ℤ) - t))
    (hdegree : Module.finrank E L = p) (hres : residueDegree E L = 1)
    (hchar : residueCharacteristic E = p)
    (hbreak : PrimeCyclicExtension.IsLowerBreak E L t')
    {z U : L} {h : ℤ} (hz : ord L z = (h : WithTop ℤ))
    (hh : 1 + t₂ + ((p : ℤ) - 3) * t ≤ h)
    (hU : U ∈ lattice L (1 + (p : ℤ) * t₂))
    (hrel : U / z ∈ lattice L (2 * ((p : ℤ) - 1) * t)) :
    norm E L z - norm E L (z - U) ∈ lattice E (1 + (p : ℤ) * t₂) := by
  have hz0 : z ≠ 0 := (ord_ne_top_iff L).1 (by rw [hz]; simp)
  have ht' : 0 < t' := by
    have hdiff : (0 : ℤ) ≤ (t₂ : ℤ) - t := by omega
    have hmul := mul_nonneg (Int.natCast_nonneg p) hdiff
    omega
  have hresult : norm E L (z + -U) - norm E L z ∈
      lattice E (1 + (p : ℤ) * t₂) := by
    apply norm_add_sub_mem_of_symmetric E L hz0
    · intro j hj hjp
      have hneg : -U / z ∈ lattice L (2 * ((p : ℤ) - 1) * t) := by
        simpa only [neg_div] using (lattice L _).neg_mem hrel
      have hs := cyclic_symmetric_mem E L hp ht' hdegree hres hchar hbreak hneg hj
        (by simpa only [hdegree] using hjp)
      have hf := projectionTransfer_floor_bound (by omega) ht ht₂ hbreaks hh hj
      have hrem : (0 : ℤ) ≤ (((p : ℤ) - 3) * t + p - 1) / p := by
        apply Int.ediv_nonneg
        · have := mul_nonneg (show (0 : ℤ) ≤ p - 3 by omega) (Int.natCast_nonneg t)
          omega
        · omega
      have hdepth : 1 + (p : ℤ) * t₂ ≤ h +
          ((j : ℤ) * (2 * ((p : ℤ) - 1) * t) +
            ((p : ℤ) - 1) * ((t' : ℤ) + 1)) / p := by
        have heq : 2 * (j : ℤ) * ((p : ℤ) - 1) * t =
            (j : ℤ) * (2 * ((p : ℤ) - 1) * t) := by ring
        rw [heq] at hf
        omega
      rw [mem_lattice, ord_mul, ord_norm, hres, one_nsmul, hz]
      exact (WithTop.coe_le_coe.mpr hdepth).trans (by
        simpa only [WithTop.coe_add] using
          add_le_add_right ((mem_lattice E).1 hs) (h : WithTop ℤ))
    · simpa only [mem_lattice, ord_norm, hres, one_nsmul, ord_neg] using hU
  simpa only [← sub_eq_add_neg, neg_sub] using (lattice E _).neg_mem hresult

/-- Distinct prime-degree subfields in a degree-square Galois extension
have the literal crossed norm restriction used in H17. -/
theorem primeDiamond_norm_restrict
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Module.Finite F K]
    (B₁ B₂ : IntermediateField F K) [IsGalois F B₁]
    {p : ℕ} (hp : p.Prime)
    (hdegree : Module.finrank F K = p * p)
    (h₁ : Module.finrank F B₁ = p) (h₂ : Module.finrank F B₂ = p)
    (hne : B₁ ≠ B₂) (y : B₂) :
    Algebra.norm B₁ (algebraMap B₂ K y) = algebraMap F B₁ (Algebra.norm F y) := by
  have hinf : B₁ ⊓ B₂ = ⊥ := by
    have hdvd := IntermediateField.finrank_dvd_of_le_right
      (show B₁ ⊓ B₂ ≤ B₁ from inf_le_left)
    rw [h₁] at hdvd
    rcases (Nat.dvd_prime hp).1 hdvd with hone | heq
    · exact IntermediateField.finrank_eq_one_iff.mp hone
    · have heq₁ : B₁ ⊓ B₂ = B₁ :=
        IntermediateField.eq_of_le_of_finrank_eq inf_le_left (heq.trans h₁.symm)
      have heq₂ : B₁ ⊓ B₂ = B₂ :=
        IntermediateField.eq_of_le_of_finrank_eq inf_le_right (heq.trans h₂.symm)
      exact (hne (heq₁.symm.trans heq₂)).elim
  have hdis := IntermediateField.LinearDisjoint.of_inf_eq_bot hinf
  have hsup : B₁ ⊔ B₂ = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [hdis.finrank_sup, h₁, h₂]
    simpa using hdegree.symm
  exact hdis.norm_algebraMap hsup y

/-- A power-coordinate expansion has no cancellation between different
indices: their finite orders are incongruent modulo the ramification degree.
Consequently a whole sum in a fractional lattice has every term there. -/
theorem coordinate_terms_mem
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    {p t : ℕ} (hp : p.Prime) (hram : ramificationIndex E L = p)
    {Delta : L} (hDelta : ord L Delta = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ t) (Y : Fin p → E) {k : ℤ}
    (h : (∑ i : Fin p, algebraMap E L (Y i) * Delta ^ (i : ℕ)) ∈ lattice L k) :
    ∀ i : Fin p, algebraMap E L (Y i) * Delta ^ (i : ℕ) ∈ lattice L k := by
  classical
  let f : Fin p → L := fun i => algebraMap E L (Y i) * Delta ^ (i : ℕ)
  have hsep (i j : Fin p) (hi : f i ≠ 0) (hj : f j ≠ 0)
      (heq : ord L (f i) = ord L (f j)) : i = j := by
    have hYi : Y i ≠ 0 := by intro he; simp [f, he] at hi
    have hYj : Y j ≠ 0 := by intro he; simp [f, he] at hj
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff E).2 hYi)
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff E).2 hYj)
    simp only [f, ord_mul, ord_algebraMap, hram, ord_pow, hDelta,
      ← ha, ← hb, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_eq_coe,
      nsmul_eq_mul] at heq
    have hdvd : (p : ℤ) ∣ ((i : ℤ) - (j : ℤ)) * t := by
      refine ⟨a - b, ?_⟩
      nlinarith [heq]
    have hij : p ∣ ((i : ℤ) - (j : ℤ)).natAbs :=
      (Int.Prime.dvd_mul hp hdvd).resolve_right (by simpa using hprime)
    have habs : ((i : ℤ) - (j : ℤ)).natAbs < p :=
      Int.natAbs_coe_sub_coe_lt_of_lt i.isLt j.isLt
    have hz := Int.natAbs_eq_zero.mp (Nat.eq_zero_of_dvd_of_lt hij habs)
    exact Fin.ext (by omega)
  letI : Nonempty (Fin p) := ⟨⟨0, hp.pos⟩⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ (fun i => ord L (f i))
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin p)).Nonempty)
  intro i
  by_cases hf : f i = 0
  · simpa only [← show f i = algebraMap E L (Y i) * Delta ^ (i : ℕ) from rfl, hf]
      using (lattice L k).zero_mem
  have hj0 : f j ≠ 0 := by
    intro hjzero
    have hx := hj i (Finset.mem_univ i)
    simp only [hjzero, ord_zero, top_le_iff, ord_eq_top_iff] at hx
    exact hf hx
  have hsum : ord L (∑ r, f r) = ord L (f j) := by
    apply Valuation.map_sum_eq_of_lt (ord L) (Finset.mem_univ j)
    intro r hr
    have hrj : r ≠ j := by simpa using hr
    change ord L (f j) < ord L (f r)
    apply lt_of_le_of_ne (hj r (Finset.mem_univ r))
    intro heq
    by_cases hr0 : f r = 0
    · rw [hr0, ord_zero] at heq
      exact hj0 ((ord_eq_top_iff L).1 heq)
    · exact hrj (hsep j r hj0 hr0 heq).symm
  rw [mem_lattice] at h ⊢
  exact (h.trans_eq hsum).trans (hj i (Finset.mem_univ i))

private theorem map_lattice
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    {p : ℕ} (hram : ramificationIndex E L = p) {x : E} {q : ℤ}
    (hx : x ∈ lattice E q) : algebraMap E L x ∈ lattice L ((p : ℤ) * q) := by
  rw [mem_lattice, ord_algebraMap, hram]
  simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using
    nsmul_le_nsmul_right ((mem_lattice E).1 hx) p

private theorem div_lattice
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    {u v : L} {a b : ℤ} (hu : u ∈ lattice L a)
    (hv : ord L v = (b : WithTop ℤ)) : u / v ∈ lattice L (a - b) := by
  have hi : v⁻¹ ∈ lattice L (-b) := by simp [mem_lattice, hv]
  simpa only [div_eq_mul_inv, sub_eq_add_neg] using mul_mem_lattice L hu hi

/-- The linear part of H17, using the crossed symmetric bound and the
literal upper norm. -/
theorem projectionTransfer_linear
    (E₁ E₂ L : Type*) [Field E₁] [Field E₂] [Field L]
    [ValuativeRel E₁] [TopologicalSpace E₁] [IsNonarchimedeanLocalField E₁]
    [ValuativeRel E₂] [TopologicalSpace E₂] [IsNonarchimedeanLocalField E₂]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E₁ L] [ValuativeExtension E₁ L]
    [Algebra E₂ L] [ValuativeExtension E₂ L]
    [Module.Free E₁ L] [Module.Finite E₁ L]
    {p t t₂ : ℕ} (_hp : 0 < p)
    (hdegree : Module.finrank E₁ L = p) (hres : residueDegree E₁ L = 1)
    {Delta : L}
    (hsym : ∀ (Y : E₂) (j : ℕ), 1 ≤ j → j < p →
      ((((p : ℤ) - 1) * t₂ - (j : ℤ) * t : ℤ) : WithTop ℤ) + j • ord E₂ Y ≤
        ord E₁ (elementarySymmetric E₁ L j (algebraMap E₂ L Y * Delta)))
    {y₀ y₁ : E₂} {h : ℤ}
    (hy₀ : ord L (algebraMap E₂ L y₀) = (h : WithTop ℤ))
    (hh : 1 + t₂ ≤ h)
    (hratio : y₁ / y₀ ∈ lattice E₂ (t : ℤ))
    (hy₁ : algebraMap E₂ L y₁ * Delta ∈ lattice L (1 + (p : ℤ) * t₂)) :
    norm E₁ L (algebraMap E₂ L y₀ + algebraMap E₂ L y₁ * Delta) -
      norm E₁ L (algebraMap E₂ L y₀) ∈ lattice E₁ (1 + (p : ℤ) * t₂) := by
  have hzero : algebraMap E₂ L y₀ ≠ 0 :=
    (ord_ne_top_iff L).1 (by rw [hy₀]; simp)
  apply norm_add_sub_mem_of_symmetric E₁ L hzero
  · intro j hj hjp
    have hs := hsym (y₁ / y₀) j hj (by simpa only [hdegree] using hjp)
    have hq := nsmul_le_nsmul_right ((mem_lattice E₂).1 hratio) j
    have hbound : ((((p : ℤ) - 1) * t₂ : ℤ) : WithTop ℤ) ≤
        ord E₁ (elementarySymmetric E₁ L j (algebraMap E₂ L (y₁ / y₀) * Delta)) := by
      have hb := (add_le_add_right hq
        (((((p : ℤ) - 1) * t₂ - (j : ℤ) * t : ℤ) : WithTop ℤ))).trans hs
      convert hb using 1
      rw [← WithTop.coe_nsmul, ← WithTop.coe_add]
      congr 1
      simp only [nsmul_eq_mul]
      ring
    have harg : (algebraMap E₂ L y₁ * Delta) / algebraMap E₂ L y₀ =
        algebraMap E₂ L (y₁ / y₀) * Delta := by rw [map_div₀]; ring
    rw [harg, mem_lattice, ord_mul, ord_norm, hres, one_nsmul, hy₀]
    have hdepth : 1 + (p : ℤ) * t₂ ≤ h + ((p : ℤ) - 1) * t₂ := by nlinarith
    exact (WithTop.coe_le_coe.mpr hdepth).trans (by
      simpa only [WithTop.coe_add] using add_le_add_right hbound (h : WithTop ℤ))
  · simpa only [mem_lattice, ord_norm, hres, one_nsmul] using hy₁

/-- Projection of the scalar expansion onto its constant coefficient,
with both absolute and relative bounds for every nonconstant term. -/
theorem projectionTransfer_coefficients
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    {p t t₂ : ℕ} (hp : p.Prime) (ht : 0 < t)
    (hram : ramificationIndex E L = p)
    {Delta : L} (hDelta : ord L Delta = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ t) (Y : Fin p → E) (q : ℤ) {z : L} {y : E}
    (hexp : z = ∑ i : Fin p, algebraMap E L (Y i) * Delta ^ (i : ℕ))
    (hz : ord L z = (((p : ℤ) * q : ℤ) : WithTop ℤ))
    (hcoeff : ∀ i : Fin p, Y i ∈ lattice E (q + (i : ℕ) * (t : ℤ)))
    (hclose : z - algebraMap E L y ∈ lattice L (1 + (p : ℤ) * t₂)) :
    ord E (Y ⟨0, hp.pos⟩) = (q : WithTop ℤ) ∧
    Y ⟨0, hp.pos⟩ - y ∈ lattice E ((t₂ : ℤ) + 1) ∧
    (∀ i : Fin p, 1 ≤ (i : ℕ) →
      algebraMap E L (Y i) * Delta ^ (i : ℕ) ∈ lattice L (1 + (p : ℤ) * t₂)) ∧
    (∀ i : Fin p,
      algebraMap E L (Y i) * Delta ^ (i : ℕ) ∈
        lattice L ((p : ℤ) * q + ((p : ℤ) - 1) * (i : ℕ) * t)) := by
  classical
  let i₀ : Fin p := ⟨0, hp.pos⟩
  let f : Fin p → L := fun i => algebraMap E L (Y i) * Delta ^ (i : ℕ)
  have hterm (i : Fin p) : f i ∈
      lattice L ((p : ℤ) * q + ((p : ℤ) - 1) * (i : ℕ) * t) := by
    have hd : Delta ^ (i : ℕ) ∈ lattice L (-((i : ℕ) * (t : ℤ))) := by
      simp only [mem_lattice, ord_pow, hDelta, ← WithTop.coe_nsmul,
        nsmul_eq_mul, mul_neg, le_refl]
    convert mul_mem_lattice L (map_lattice E L hram (hcoeff i)) hd using 1
    congr 1
    ring
  have hrest : (((p : ℤ) * q : ℤ) : WithTop ℤ) <
      ord L (∑ i ∈ Finset.univ \ {i₀}, f i) := by
    apply (ord L).map_lt_sum (WithTop.coe_ne_top)
    intro i hi
    have hi0 : i ≠ i₀ := by simpa using hi
    have hi1 : (1 : ℤ) ≤ (i : ℕ) := by
      have : (i : ℕ) ≠ 0 := fun he => hi0 (Fin.ext he)
      omega
    have hpos : (0 : ℤ) < ((p : ℤ) - 1) * (i : ℕ) * t := by
      apply mul_pos
      · exact mul_pos (by have := hp.one_lt; omega) (by omega)
      · omega
    exact (WithTop.coe_lt_coe.mpr (by omega)).trans_le ((mem_lattice L).1 (hterm i))
  have hconst : ord L (algebraMap E L (Y i₀)) = (((p : ℤ) * q : ℤ) : WithTop ℤ) := by
    have heq : algebraMap E L (Y i₀) = z - ∑ i ∈ Finset.univ \ {i₀}, f i := by
      rw [hexp, Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i₀)]
      simp [f, i₀]
    rw [heq, sub_eq_add_neg, ord_add_eq_min L (by simpa [hz] using ne_of_lt hrest),
      ord_neg, hz, min_eq_left hrest.le]
  have hY0 : ord E (Y i₀) = (q : WithTop ℤ) := by
    have hY0ne : Y i₀ ≠ 0 := by
      intro he
      rw [he, map_zero, ord_zero] at hconst
      exact WithTop.coe_ne_top hconst.symm
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff E).2 hY0ne)
    rw [ord_algebraMap, hram, ← ha, ← WithTop.coe_nsmul, WithTop.coe_eq_coe] at hconst
    simp only [nsmul_eq_mul] at hconst
    have haq : a = q := mul_left_cancel₀ (by exact_mod_cast hp.ne_zero) hconst
    simpa [haq] using ha.symm
  let Z : Fin p → E := Function.update Y i₀ (Y i₀ - y)
  have hZexp : (∑ i : Fin p, algebraMap E L (Z i) * Delta ^ (i : ℕ)) =
      z - algebraMap E L y := by
    have hfun : (fun i : Fin p => algebraMap E L (Z i) * Delta ^ (i : ℕ)) =
        Function.update f i₀ (algebraMap E L (Y i₀ - y)) := by
      funext i
      by_cases hi : i = i₀
      · subst i; simp [Z, i₀]
      · simp [Z, hi, f]
    rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ i₀), hexp,
      Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i₀)]
    simp only [map_sub, f, i₀, pow_zero, mul_one]
    ring
  have hZ := coordinate_terms_mem E L hp hram hDelta hprime Z
    (hZexp.symm ▸ hclose)
  have hclose0 : Y i₀ - y ∈ lattice E ((t₂ : ℤ) + 1) := by
    have h0 := hZ i₀
    simp only [Z, Function.update_self, i₀, pow_zero, mul_one, mem_lattice,
      ord_algebraMap, hram] at h0
    by_cases he : Y i₀ - y = 0
    · simp [he]
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff E).2 he)
    change ((1 + (p : ℤ) * t₂ : ℤ) : WithTop ℤ) ≤ p • ord E (Y i₀ - y) at h0
    rw [← ha, ← WithTop.coe_nsmul, WithTop.coe_le_coe] at h0
    simp only [nsmul_eq_mul] at h0
    have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
    have hlt : (t₂ : ℤ) < a := by nlinarith
    rw [mem_lattice, ← ha, WithTop.coe_le_coe]
    omega
  refine ⟨hY0, hclose0, ?_, hterm⟩
  intro i hi
  have hi0 : i ≠ i₀ := by intro he; subst i; simp [i₀] at hi
  simpa only [Z, Function.update_of_ne hi0] using hZ i

private theorem residueDegree_projectionTower
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (L : IntermediateField F K) :
    letI := Basic.intermediateFieldValuativeRel L
    letI := Basic.intermediateFieldTopology L
    letI := Basic.intermediateField_localField L
    letI := Basic.intermediateField_lowerValuativeExtension L
    letI := Basic.intermediateField_upperValuativeExtension L
    residueDegree F L * residueDegree L K = residueDegree F K := by
  letI := Basic.intermediateFieldValuativeRel L
  letI := Basic.intermediateFieldTopology L
  letI := Basic.intermediateField_localField L
  letI := Basic.intermediateField_lowerValuativeExtension L
  letI := Basic.intermediateField_upperValuativeExtension L
  letI : IsScalarTower (ringOfIntegers F) (ringOfIntegers L) (ringOfIntegers K) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap F K (x : F) = algebraMap L K (algebraMap F L (x : F))
      rw [← IsScalarTower.algebraMap_apply F L K])
  letI : IsLocalHom (algebraMap (ringOfIntegers F) (ringOfIntegers L)) := inferInstance
  letI : IsLocalHom (algebraMap (ringOfIntegers L) (ringOfIntegers K)) := inferInstance
  rw [residueDegree_eq_finrank_residueField, residueDegree_eq_finrank_residueField,
    residueDegree_eq_finrank_residueField]
  exact Module.finrank_mul_finrank (ResidueField F) (ResidueField L) (ResidueField K)

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K]
variable [Module.Free F K] [Module.Finite F K] [IsGalois F K]

set_option maxHeartbeats 800000 in
/-- Paper H17, with the stated scalar product, both numerical hypotheses,
and the literal upper and lower field norms. The Artin--Schreier coordinate
and all coefficient estimates are constructed from the genuine diamond. -/
theorem projectionTransfer {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (D : OddTotalBreakData (F := F) (K := K) hp hG) :
    let B₁ := D.B₁
    let B₂ := D.B₂
    letI := Basic.intermediateFieldValuativeRel B₁
    letI := Basic.intermediateFieldTopology B₁
    letI := Basic.intermediateField_localField B₁
    letI := Basic.intermediateFieldValuativeRel B₂
    letI := Basic.intermediateFieldTopology B₂
    letI := Basic.intermediateField_localField B₂
    ∀ (x : B₂) (w : B₁) (y : B₂),
      algebraMap B₂ K x * algebraMap B₁ K w - algebraMap B₂ K y ∈
        lattice K (1 + (p : ℤ) * D.t₂) →
      ((1 + D.t₂ + ((p : ℤ) - 3) * D.t : ℤ) : WithTop ℤ) ≤
        ord K (algebraMap B₂ K x * algebraMap B₁ K w) →
      norm B₁ K (algebraMap B₂ K x * algebraMap B₁ K w) -
        algebraMap F B₁ (norm F B₂ y) ∈ lattice B₁ (1 + (p : ℤ) * D.t₂) := by
  classical
  dsimp only [OddTotalBreakData.B₁, OddTotalBreakData.B₂]
  let B₁ := IntermediateField.fixedField D.H₁
  let B₂ := IntermediateField.fixedField D.H₂
  letI := Basic.intermediateFieldValuativeRel B₁
  letI := Basic.intermediateFieldTopology B₁
  letI := Basic.intermediateFieldValuativeRel B₂
  letI := Basic.intermediateFieldTopology B₂
  obtain ⟨hLocal₁, hFreeF₁, hFiniteF₁, hFree₁K, hFinite₁K, hScalar₁,
      hValF₁, hVal₁K, htotal₁, hdegreeLower₁, hdegreeUpper₁,
      hcycF₁, hcyc₁K⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁
  letI := hLocal₁
  letI := hFreeF₁
  letI := hFiniteF₁
  letI := hFree₁K
  letI := hFinite₁K
  letI := hScalar₁
  letI := hValF₁
  letI := hVal₁K
  letI : IsGalois F B₁ := hcycF₁.1
  letI : IsGalois B₁ K := hcyc₁K.1
  letI : PrimeCyclicExtension F B₁ :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F B₁ hcycF₁
  obtain ⟨hLocal₂, hFreeF₂, hFiniteF₂, hFree₂K, hFinite₂K, hScalar₂,
      hValF₂, hVal₂K, _htotal₂, hdegreeLower₂, hdegreeUpper₂,
      hcycF₂, hcyc₂K⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
  letI := hLocal₂
  letI := hFreeF₂
  letI := hFiniteF₂
  letI := hFree₂K
  letI := hFinite₂K
  letI := hScalar₂
  letI := hValF₂
  letI := hVal₂K
  letI : IsGalois F B₂ := hcycF₂.1
  letI : IsGalois B₂ K := hcyc₂K.1
  letI : PrimeCyclicExtension F B₂ :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F B₂ hcycF₂
  letI : PrimeCyclicExtension B₁ K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension B₁ K hcyc₁K
  have hresmul₁ := residueDegree_projectionTower B₁
  have hresmul₂ := residueDegree_projectionTower B₂
  rw [hres] at hresmul₁ hresmul₂
  have hresF₁ : residueDegree F B₁ = 1 := (mul_eq_one.mp hresmul₁).1
  have hres₁K : residueDegree B₁ K = 1 := (mul_eq_one.mp hresmul₁).2
  have hresF₂ : residueDegree F B₂ = 1 := (mul_eq_one.mp hresmul₂).1
  have hres₂K : residueDegree B₂ K = 1 := (mul_eq_one.mp hresmul₂).2
  have hramF₁ : ramificationIndex F B₁ = p := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F B₁
    simpa only [hresF₁, hdegreeLower₁, mul_one] using h.symm
  have hram₁K : ramificationIndex B₁ K = p := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree B₁ K
    simpa only [hres₁K, hdegreeUpper₁, mul_one] using h.symm
  have hram₂K : ramificationIndex B₂ K = p := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree B₂ K
    simpa only [hres₂K, hdegreeUpper₂, mul_one] using h.symm
  have hbreak₂ : PrimeCyclicExtension.IsLowerBreak F B₂ D.t₂ := by
    simpa only [B₂, Ramification.IntermediateBreakPair] using D.B₂_breaks.1
  have hbreak₁K : PrimeCyclicExtension.IsLowerBreak B₁ K D.tPrime := by
    simpa only [B₁, Ramification.IntermediateBreakPair] using D.B₁_breaks.2
  have hchar₁ : residueCharacteristic B₁ = p :=
    (residueCharacteristic_extension_eq F B₁).trans hchar
  have hcross (c : B₂) : norm B₁ K (algebraMap B₂ K c) =
      algebraMap F B₁ (norm F B₂ c) :=
    primeDiamond_norm_restrict B₁ B₂ hp htotal₁ hdegreeLower₁ hdegreeLower₂
      D.B₁_ne_B₂ c
  intro x w y hclose hnum
  let z := algebraMap B₂ K x * algebraMap B₁ K w
  change z - algebraMap B₂ K y ∈ lattice K (1 + (p : ℤ) * D.t₂) at hclose
  change _ ≤ ord K z at hnum
  change norm B₁ K z - algebraMap F B₁ (norm F B₂ y) ∈
    lattice B₁ (1 + (p : ℤ) * D.t₂)
  by_cases hz0 : z = 0
  · rw [hz0, zero_sub] at hclose
    rw [hz0, norm_apply, Algebra.norm_zero, zero_sub, ← hcross]
    simpa only [mem_lattice, ord_neg, ord_norm, hres₁K, one_nsmul] using hclose
  have hx0 : x ≠ 0 := by intro hx; simp [z, hx] at hz0
  have hw0 : w ≠ 0 := by intro hw; simp [z, hw] at hz0
  obtain ⟨vx, hvx⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff B₂).2 hx0)
  obtain ⟨vw, hvw⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff B₁).2 hw0)
  let q : ℤ := vx + vw
  have hz : ord K z = (((p : ℤ) * q : ℤ) : WithTop ℤ) := by
    simp only [z, ord_mul, ord_algebraMap, hram₁K, hram₂K,
      ← hvx, ← hvw, ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul]
    congr 1
    dsimp only [q]
    ring
  have hh : 1 + D.t₂ + ((p : ℤ) - 3) * D.t ≤ (p : ℤ) * q := by
    simpa only [hz, WithTop.coe_le_coe] using hnum
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hp3 : (0 : ℤ) ≤ p - 3 := by have := D.odd_prime; omega
  have hq0 : 0 ≤ q := by
    have := mul_nonneg hp3 (Int.natCast_nonneg D.t)
    nlinarith
  have hdata := twistedEstimates hp hG hres hchar D
  dsimp only [OddTotalBreakData.B₁, OddTotalBreakData.B₂] at hdata
  obtain ⟨Delta, a, hroot, hDelta, ha, hprime, hgen, hcoeff, htrace, hsym, hei, hs⟩ := hdata
  let pb : PowerBasis B₂ K :=
    PowerBasis.ofAdjoinEqTop (IsAlgebraic.of_finite B₂ Delta).isIntegral hgen
  have hpbgen : pb.gen = Delta := PowerBasis.ofAdjoinEqTop_gen _ _
  have hpbdim : pb.dim = p := by rw [← pb.finrank]; exact hdegreeUpper₂
  let W : Fin p → B₂ := fun i =>
    pb.basis.repr (algebraMap B₁ K w) (Fin.cast hpbdim.symm i)
  have hexpw : algebraMap B₁ K w =
      ∑ i : Fin p, algebraMap B₂ K (W i) * Delta ^ (i : ℕ) := by
    let e : Fin p ≃ Fin pb.dim := (Fin.castOrderIso hpbdim.symm).toEquiv
    have hs := pb.basis.sum_repr (algebraMap B₁ K w)
    rw [← e.sum_comp] at hs
    refine hs.symm.trans ?_
    apply Finset.sum_congr rfl
    intro i hi
    rw [pb.basis_eq_pow, Algebra.smul_def, hpbgen]
    rfl
  let Y : Fin p → B₂ := fun i => x * W i
  have hexp : z = ∑ i : Fin p, algebraMap B₂ K (Y i) * Delta ^ (i : ℕ) := by
    dsimp only [z, Y]
    rw [hexpw, Finset.mul_sum]
    simp only [map_mul, mul_assoc]
  have hY : ∀ i : Fin p, Y i ∈ lattice B₂ (q + (i : ℕ) * (D.t : ℤ)) := by
    intro i
    have hc := hcoeff w W hexpw i
    rw [← hvw] at hc
    have hWi : W i ∈ lattice B₂ (vw + (i : ℕ) * (D.t : ℤ)) := by
      simpa only [mem_lattice, WithTop.coe_add, Nat.cast_mul] using hc
    have hxi : x ∈ lattice B₂ vx := by rw [mem_lattice, ← hvx]
    convert mul_mem_lattice B₂ hxi hWi using 1
    congr 1
    dsimp only [q]
    ring
  obtain ⟨hY0, hY0y, htermAbs, htermRel⟩ :=
    projectionTransfer_coefficients B₂ K hp D.t_pos hram₂K hDelta hprime Y q
      hexp hz hY hclose
  let i₀ : Fin p := ⟨0, hp.pos⟩
  let i₁ : Fin p := ⟨1, hp.one_lt⟩
  let y₀ := Y i₀
  let y₁ := Y i₁
  have hconst : ord K (algebraMap B₂ K y₀) = (((p : ℤ) * q : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hram₂K, hY0]
    simp only [← WithTop.coe_nsmul, nsmul_eq_mul]
  have hratio : y₁ / y₀ ∈ lattice B₂ (D.t : ℤ) := by
    have h := div_lattice B₂ (hY i₁) hY0
    simpa only [i₁, Nat.cast_one, one_mul, add_sub_cancel_left] using h
  have hlinear := projectionTransfer_linear B₁ B₂ K hp.pos hdegreeUpper₁ hres₁K
    hsym hconst (by
      have := mul_nonneg hp3 (Int.natCast_nonneg D.t)
      omega) hratio (by simpa only [i₁, pow_one] using htermAbs i₁ (by simp [i₁]))
  let U : K := Finset.sum
    ((Finset.univ : Finset (Fin p)).filter (fun (i : Fin p) => 2 ≤ i.val))
    (fun (i : Fin p) => algebraMap B₂ K (Y i) * Delta ^ i.val)
  have hUabs : U ∈ lattice K (1 + (p : ℤ) * D.t₂) := by
    apply sum_mem_lattice K
    intro i hi
    exact htermAbs i (by have := (Finset.mem_filter.mp hi).2; omega)
  have hUrel : U ∈ lattice K ((p : ℤ) * q + 2 * ((p : ℤ) - 1) * D.t) := by
    apply sum_mem_lattice K
    intro i hi
    have hi2 : (2 : ℤ) ≤ (i : ℕ) := by
      exact_mod_cast (Finset.mem_filter.mp hi).2
    apply lattice_antitone K _ (htermRel i)
    have hmul := mul_nonneg (sub_nonneg.mpr hi2)
      (mul_nonneg (show (0 : ℤ) ≤ p - 1 by omega) (Int.natCast_nonneg D.t))
    nlinarith
  have hUdiv : U / z ∈ lattice K (2 * ((p : ℤ) - 1) * D.t) := by
    simpa only [add_sub_cancel_left] using div_lattice K hUrel hz
  have hbreaks : (D.tPrime : ℤ) = D.t + p * ((D.t₂ : ℤ) - D.t) := by
    rw [D.tPrime_eq, D.t₂_eq]
    push_cast
    ring
  have htail := projectionTransfer_tail B₁ K hp D.odd_prime D.t_pos D.t_le_t₂
    hbreaks hdegreeUpper₁ hres₁K hchar₁ hbreak₁K hz hh hUabs hUdiv
  have hsplit : z = algebraMap B₂ K y₀ + algebraMap B₂ K y₁ * Delta + U := by
    rw [hexp]
    let f : Fin p → K := fun i => algebraMap B₂ K (Y i) * Delta ^ (i : ℕ)
    change (∑ i, f i) = _
    calc
      (∑ i, f i) = ∑ i : Fin p,
          ((if i = i₀ then f i else 0) + (if i = i₁ then f i else 0) +
            (if 2 ≤ (i : ℕ) then f i else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hi0 : i = i₀
        · subst i; simp [i₀, i₁, Fin.ext_iff]
        by_cases hi1 : i = i₁
        · subst i; simp [i₀, i₁, Fin.ext_iff]
        have hi2 : 2 ≤ (i : ℕ) := by
          have h0 : (i : ℕ) ≠ 0 := fun he => hi0 (Fin.ext he)
          have h1 : (i : ℕ) ≠ 1 := fun he => hi1 (Fin.ext he)
          omega
        simp only [hi0, hi1, hi2, if_false, if_true, zero_add]
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
          if_true, U, Finset.sum_filter, f, i₀, i₁, pow_zero, pow_one, mul_one, y₀, y₁]
  have htail' : norm B₁ K z -
      norm B₁ K (algebraMap B₂ K y₀ + algebraMap B₂ K y₁ * Delta) ∈
      lattice B₁ (1 + (p : ℤ) * D.t₂) := by
    have heq : z - U = algebraMap B₂ K y₀ + algebraMap B₂ K y₁ * Delta := by
      rw [hsplit, add_sub_cancel_right]
    simpa only [heq] using htail
  have hy₀int : y₀ ∈ lattice B₂ 0 := by
    change Y ⟨0, hp.pos⟩ ∈ lattice B₂ 0
    simpa only [mem_lattice, hY0, WithTop.coe_le_coe] using hq0
  have hyint : y ∈ lattice B₂ 0 := by
    have hdiff0 : y₀ - y ∈ lattice B₂ 0 :=
      lattice_antitone B₂ (by omega) hY0y
    simpa only [sub_sub_cancel] using (lattice B₂ 0).sub_mem hy₀int hdiff0
  have hlower := cyclic_norm_sub_mem_of_integral F B₂ hp
    (D.t_pos.trans_le D.t_le_t₂) hdegreeLower₂ hresF₂ hchar hbreak₂ hyint hY0y
  have hlowerMap : algebraMap F B₁ (norm F B₂ y₀ - norm F B₂ y) ∈
      lattice B₁ (1 + (p : ℤ) * D.t₂) := by
    apply lattice_antitone B₁ _ (map_lattice F B₁ hramF₁ hlower)
    have := hp.one_le
    nlinarith
  have hlower' : norm B₁ K (algebraMap B₂ K y₀) -
      algebraMap F B₁ (norm F B₂ y) ∈ lattice B₁ (1 + (p : ℤ) * D.t₂) := by
    simpa only [map_sub, hcross] using hlowerMap
  have hsum := (lattice B₁ (1 + (p : ℤ) * D.t₂)).add_mem
    ((lattice B₁ _).add_mem htail' hlinear) hlower'
  convert hsum using 1
  ring

end

end LanglandsSecondMainLemma.Odd.Total
