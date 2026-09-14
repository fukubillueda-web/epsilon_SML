import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Total.ASCoordinate
import LanglandsSecondMainLemma.Odd.Total.ConjugateRoots

/-!
# Odd / Total / Coefficient Extraction

Paper Lemma `O:A:lem:coeff`.  The exact Artin--Schreier coordinate supplied
by `ConjugateRoots` has pairwise valuation-separated powers.  This gives a
preliminary bound for every coefficient.  Restricting each actual translated
root automorphism to `B₁`, and using the lower break `t`, improves the bound
one coefficient at a time.  In mixed characteristic the Hensel correction is
retained; the prime-valuation estimate makes every one of its power-basis
coefficients deep enough for the induction.
-/

namespace LanglandsSecondMainLemma.Odd.Total

open LanglandsFirstMainLemma
open scoped BigOperators

noncomputable section

/-- Multiplicativity of residue degrees in the canonical valuation tower
through an actual intermediate field. -/
private theorem residueDegree_mul_local
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (L : IntermediateField F K) :
    letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
    letI : TopologicalSpace L := Basic.intermediateFieldTopology L
    letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
    letI : ValuativeExtension F L := Basic.intermediateField_lowerValuativeExtension L
    letI : ValuativeExtension L K := Basic.intermediateField_upperValuativeExtension L
    residueDegree F L * residueDegree L K = residueDegree F K := by
  letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
  letI : TopologicalSpace L := Basic.intermediateFieldTopology L
  letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
  letI : ValuativeExtension F L := Basic.intermediateField_lowerValuativeExtension L
  letI : ValuativeExtension L K := Basic.intermediateField_upperValuativeExtension L
  letI : IsScalarTower
      (ringOfIntegers F) (ringOfIntegers L) (ringOfIntegers K) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap F K (x : F) = algebraMap L K (algebraMap F L (x : F))
      rw [← IsScalarTower.algebraMap_apply F L K])
  letI : IsLocalHom
      (algebraMap (ringOfIntegers F) (ringOfIntegers L)) := inferInstance
  letI : IsLocalHom
      (algebraMap (ringOfIntegers L) (ringOfIntegers K)) := inferInstance
  simp only [residueDegree_eq_finrank_residueField]
  exact Module.finrank_mul_finrank
    (ResidueField F) (ResidueField L) (ResidueField K)

private theorem pow_mem_lattice_int
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    {x : L} {q : ℤ} (hx : x ∈ lattice L q) (n : ℕ) :
    x ^ n ∈ lattice L ((n : ℤ) * q) := by
  rw [mem_lattice] at hx ⊢
  rw [ord_pow]
  have h := nsmul_le_nsmul_right hx n
  simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using h

/-- A depth congruence between order-zero elements is preserved by every
integer power. -/
private theorem congruent_zpow_of_ord_zero
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    {r : L} (hr : ord L r = 0) {d : ℤ}
    (h : CongruentAtDepth d r 1) (n : ℤ) :
    CongruentAtDepth d (r ^ n) 1 := by
  have hnat : ∀ m : ℕ, CongruentAtDepth d (r ^ m) 1 := by
    intro m
    induction m with
    | zero => simpa using CongruentAtDepth.refl (F := L) (n := d) 1
    | succ m ih =>
        rw [pow_succ]
        simpa only [one_mul] using
          CongruentAtDepth.mul (F := L) (n := d)
            (by rw [ord_pow, hr]; simp) (by simp) ih h
  cases n with
  | ofNat m => simpa using hnat m
  | negSucc m =>
      rw [zpow_negSucc]
      have hmord : ord L (r ^ (m + 1)) = 0 := by rw [ord_pow, hr]; simp
      simpa using (hnat (m + 1)).inv hmord (by simp)

/-- An automorphism in the lower group at `t` moves an arbitrary fractional
element by order at least its own order plus `t`.  The definition of the
lower group only mentions integral elements; the proof passes to a DVR
uniformizer and an order-zero unit. -/
private theorem galois_sub_order_ge
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    [Module.Finite E L] [IsGalois E L]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak E L t)
    (sigma : Gal(L/E)) (x : L) :
    ord L x + ((t : ℤ) : WithTop ℤ) ≤ ord L (sigma x - x) := by
  by_cases hx : x = 0
  · subst x
    simp
  obtain ⟨pi, hpi⟩ :=
    IsDiscreteValuationRing.exists_irreducible (ringOfIntegers L)
  obtain ⟨n, u, hxu⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hpi hx
  let piL : L := (pi : L)
  let uL : L := (u : ringOfIntegers L)
  have hpiord : ord L piL = 1 := by
    apply ord_uniformizer L
    apply Valuation.isUniformizer_of_maximalIdeal_eq_span
    exact (IsDiscreteValuationRing.irreducible_iff_uniformizer pi).mp hpi
  have huord : ord L uL = 0 := by
    have huval : (ValuativeRel.valuation L) uL = 1 :=
      Valuation.Integers.one_of_isUnit
        (Valuation.integer.integers (ValuativeRel.valuation L)) u.isUnit
    apply le_antisymm
    · rw [← ord_one L, ord_le_ord_iff]
      rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation L)]
      simp [huval]
    · rw [← ord_one L, ord_le_ord_iff]
      rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation L)]
      simp [huval]
  have hsigmaMem : sigma ∈ lowerRamificationGroup E L (t : ℤ) := by
    rw [ht.1]
    exact Subgroup.mem_top sigma
  let piO : ringOfIntegers L := pi
  let uO : ringOfIntegers L := (u : ringOfIntegers L)
  have hpiCong : CongruentAtDepth ((t : ℤ) + 1)
      (sigma piL) piL := by
    exact (mem_lowerRamificationGroup E L sigma (t : ℤ)).1 hsigmaMem piO
  have huCong : CongruentAtDepth ((t : ℤ) + 1)
      (sigma uL) uL := by
    exact (mem_lowerRamificationGroup E L sigma (t : ℤ)).1 hsigmaMem uO
  let r : L := sigma piL / piL
  have hrord : ord L r = 0 := by
    dsimp only [r]
    rw [ord_div, ord_galoisConjugate, hpiord]
    simp
  have hrCong : CongruentAtDepth (t : ℤ) r 1 := by
    have hpine : piL ≠ 0 :=
      (ord_ne_top_iff L).1 (by rw [hpiord]; simp)
    rw [CongruentAtDepth, show r - 1 = (sigma piL - piL) / piL by
      dsimp only [r]
      exact div_sub_one hpine]
    rw [ord_div, hpiord]
    have hpiCong' := hpiCong
    rw [CongruentAtDepth] at hpiCong'
    by_cases hdiff : sigma piL - piL = 0
    · simp [hdiff]
    obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp
      ((ord_ne_top_iff L).2 hdiff)
    rw [← hz] at hpiCong' ⊢
    have hzint : (t : ℤ) ≤ z - 1 := by
      change ((((t : ℤ) + 1 : ℤ) : WithTop ℤ)) ≤ (z : WithTop ℤ) at hpiCong'
      have := WithTop.coe_le_coe.mp hpiCong'
      omega
    simpa using WithTop.coe_le_coe.mpr hzint
  have hrPowCong : CongruentAtDepth (t : ℤ) (r ^ n) 1 :=
    congruent_zpow_of_ord_zero L hrord hrCong n
  have huCong' : CongruentAtDepth (t : ℤ) (sigma uL) uL :=
    huCong.mono (by omega)
  have hprod : CongruentAtDepth (t : ℤ)
      (sigma uL * r ^ n) uL := by
    simpa only [mul_one] using
      huCong'.mul (by simpa only [ord_galoisConjugate] using huord.ge)
        (by simp) hrPowCong
  have hpiZpow : ord L (piL ^ n) = (n : WithTop ℤ) := by
    rw [ord_zpow, hpiord]
    cases n with
    | ofNat m => simp
    | negSucc m =>
        rw [negSucc_zsmul]
        norm_num [Int.negSucc_eq]
  have hxform : x = uL * piL ^ n := by
    simpa only [uL, piL, Units.smul_def, Algebra.smul_def,
      Algebra.coe_algebraMap_ofSubsemiring] using hxu
  have hsigmaPi : sigma piL = r * piL := by
    dsimp only [r]
    field_simp [show piL ≠ 0 by
      exact (ord_ne_top_iff L).1 (by rw [hpiord]; simp)]
  have hxord : ord L x = (n : WithTop ℤ) := by
    rw [hxform, ord_mul, huord, hpiZpow, zero_add]
  have hdiffEq : sigma x - x =
      (sigma uL * r ^ n - uL) * piL ^ n := by
    rw [hxform, map_mul, map_zpow₀, hsigmaPi, mul_zpow]
    ring
  rw [hxord, hdiffEq, ord_mul, hpiZpow, add_comm]
  rw [CongruentAtDepth] at hprod
  simpa only [WithTop.coe_add, add_comm] using
    add_le_add_right hprod (n : WithTop ℤ)

/-- Difference of two powers, with an integer-lattice bound that is valid
for negative `q`. -/
private theorem pow_sub_pow_mem_lattice
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    {x y : L} {q r : ℤ}
    (hx : x ∈ lattice L q) (hy : y ∈ lattice L q)
    (hxy : x - y ∈ lattice L r) (n : ℕ) :
    x ^ n - y ^ n ∈ lattice L (r + ((n - 1 : ℕ) : ℤ) * q) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hsum : (∑ k ∈ Finset.range n,
      x ^ k * y ^ (n - 1 - k)) ∈
      lattice L (((n - 1 : ℕ) : ℤ) * q) := by
    apply sum_mem_lattice L
    intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    have hxk := pow_mem_lattice_int L hx k
    have hyk := pow_mem_lattice_int L hy (n - 1 - k)
    have hmul := mul_mem_lattice L hxk hyk
    have hkn : k + (n - 1 - k) = n - 1 := by omega
    convert hmul using 1
    rw [← add_mul, ← Nat.cast_add, hkn]
  have hmul := mul_mem_lattice L hsum hxy
  rw [geom_sum₂_mul] at hmul
  convert hmul using 1; ring_nf

/-- If the orders of the nonzero summands are pairwise distinct, every
summand has order at least the order of the sum. -/
private theorem ord_sum_le_each_of_pairwise
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f : ι → L)
    (hsep : ∀ i j, i ≠ j → f i ≠ 0 → f j ≠ 0 →
      ord L (f i) ≠ ord L (f j)) (i : ι) :
    ord L (∑ j, f j) ≤ ord L (f i) := by
  by_cases hi : f i = 0
  · simp [hi]
  obtain ⟨j, _hj, hjmin⟩ := Finset.exists_min_image Finset.univ
    (fun j ↦ ord L (f j)) (Finset.univ_nonempty : Finset.univ.Nonempty)
  have hjzero : f j ≠ 0 := by
    intro hj
    have htop : ord L (f j) = ⊤ := by simp [hj]
    have := hjmin i (Finset.mem_univ i)
    rw [htop] at this
    have hitop : ord L (f i) = ⊤ := top_unique this
    exact hi ((ord_eq_top_iff L).1 hitop)
  have hjnotTop : ord L (f j) ≠ ⊤ := (ord_ne_top_iff L).2 hjzero
  have hjlt : ∀ k ∈ Finset.univ \ {j}, ord L (f j) < ord L (f k) := by
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton,
      true_and] at hk
    have hkj : j ≠ k := fun h => hk h.symm
    by_cases hkzero : f k = 0
    · rw [hkzero, ord_zero]
      exact lt_top_iff_ne_top.mpr hjnotTop
    exact lt_of_le_of_ne (hjmin k (Finset.mem_univ k))
      (hsep j k hkj hjzero hkzero)
  have hrest : ord L (f j) < ord L (∑ k ∈ Finset.univ \ {j}, f k) :=
    (ord L).map_lt_sum hjnotTop hjlt
  have hsum : ord L (∑ k, f k) = ord L (f j) := by
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ j)]
    exact (ord_add_eq_min L (ne_of_lt hrest)).trans (min_eq_left hrest.le)
  rw [hsum]
  exact hjmin i (Finset.mem_univ i)

/-- Preliminary coefficient bound from the incongruent orders
`p v(Y_i) - i t`. -/
private theorem preliminary_coefficient_bound
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    {p t : ℕ} (hp : p.Prime) (hram : ramificationIndex E L = p)
    {Delta : L} (hDelta : ord L Delta = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ t) (Y : Fin p → E) (i : Fin p) :
    ord L (∑ j : Fin p,
      algebraMap E L (Y j) * Delta ^ (j : ℕ)) ≤
      ord L (algebraMap E L (Y i) * Delta ^ (i : ℕ)) := by
  letI : Nonempty (Fin p) := ⟨⟨0, hp.pos⟩⟩
  let f : Fin p → L := fun j ↦
    algebraMap E L (Y j) * Delta ^ (j : ℕ)
  apply ord_sum_le_each_of_pairwise L f
  intro a b hab ha hb hord
  have hYa : Y a ≠ 0 := by
    intro h
    apply ha
    simp [f, h]
  have hYb : Y b ≠ 0 := by
    intro h
    apply hb
    simp [f, h]
  obtain ⟨va, hva⟩ := WithTop.ne_top_iff_exists.mp
    ((ord_ne_top_iff E).2 hYa)
  obtain ⟨vb, hvb⟩ := WithTop.ne_top_iff_exists.mp
    ((ord_ne_top_iff E).2 hYb)
  have hord' :
      ((p : ℤ) * va - (a : ℕ) * t : ℤ) =
        (p : ℤ) * vb - (b : ℕ) * t := by
    dsimp only [f] at hord
    rw [ord_mul, ord_mul, ord_algebraMap, ord_algebraMap,
      hram, ord_pow, ord_pow, hDelta, ← hva, ← hvb,
      ← WithTop.coe_nsmul, ← WithTop.coe_nsmul,
      ← WithTop.coe_nsmul, ← WithTop.coe_nsmul,
      ← WithTop.coe_add, ← WithTop.coe_add] at hord
    have hordZ := WithTop.coe_eq_coe.mp hord
    simp only [nsmul_eq_mul] at hordZ
    linear_combination hordZ
  have hdvd : (p : ℤ) ∣
      (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) * (t : ℤ) := by
    refine ⟨va - vb, ?_⟩
    linear_combination -hord'
  rcases Int.Prime.dvd_mul hp hdvd with hd | ht
  · have habslt :
        ((((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)).natAbs) < p := by
      exact Int.natAbs_coe_sub_coe_lt_of_lt a.isLt b.isLt
    have habszero :
        ((((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)).natAbs) = 0 :=
      Nat.eq_zero_of_dvd_of_lt hd habslt
    apply hab
    apply Fin.ext
    have hz := Int.natAbs_eq_zero.mp habszero
    omega
  · exact hprime (by simpa using ht)

private theorem ord_eq_zero_of_pow_eq_one
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    {x : L} {n : ℕ} (hn : 0 < n) (hx : x ^ n = 1) :
    ord L x = 0 := by
  have hxne : x ≠ 0 := by
    intro h
    subst x
    simp [Nat.ne_of_gt hn] at hx
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
    ((ord_ne_top_iff L).2 hxne)
  have hval := congrArg (ord L) hx
  rw [ord_pow, ord_one, ← hm, ← WithTop.coe_nsmul] at hval
  have hmzero : n • m = 0 := WithTop.coe_eq_zero.mp hval
  simp only [nsmul_eq_mul] at hmzero
  have : m = 0 :=
    (mul_eq_zero.mp hmzero).resolve_left
      (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hn))
  rw [← hm, this]
  rfl

/-- Multiplication by a positive natural reflects order on `WithTop ℤ`. -/
private theorem nsmul_le_nsmul_iff_right_withTop
    {n : ℕ} (hn : n ≠ 0) {a b : WithTop ℤ} :
    n • a ≤ n • b ↔ a ≤ b := by
  constructor
  · intro h
    by_cases hb : b = ⊤
    · simp [hb]
    obtain ⟨b', rfl⟩ := WithTop.ne_top_iff_exists.mp hb
    by_cases ha : a = ⊤
    · subst a
      have hntop : n • (⊤ : WithTop ℤ) = ⊤ := by
        rw [show n = (n - 1) + 1 by omega, add_nsmul]
        simp
      rw [hntop, ← WithTop.coe_nsmul] at h
      exact False.elim (WithTop.coe_ne_top (top_unique h))
    obtain ⟨a', rfl⟩ := WithTop.ne_top_iff_exists.mp ha
    rw [← WithTop.coe_nsmul, ← WithTop.coe_nsmul] at h
    exact WithTop.coe_le_coe.mpr
      ((nsmul_le_nsmul_iff_right hn).mp (WithTop.coe_le_coe.mp h))
  · exact fun h ↦ nsmul_le_nsmul_right h n

/-- The prime subfield of the residue field, followed by Teichmuller lift,
supplies the full group of `(p-1)`-st roots used in coefficient extraction. -/
private theorem exists_primitive_root_prime_subfield
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    {p : ℕ} (hp : p.Prime) (hchar : residueCharacteristic L = p) :
    ∃ zeta : L,
      IsPrimitiveRoot zeta (p - 1) ∧ ord L zeta = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : CharP (ResidueField L) p := ringChar.of_eq hchar
  letI : Algebra (ZMod p) (ResidueField L) := ZMod.algebra _ p
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have horder : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg,
      Nat.card_eq_fintype_card, Fintype.card_units, ZMod.card]
  have hprimUnits : IsPrimitiveRoot g (p - 1) := by
    rw [← horder]
    exact IsPrimitiveRoot.orderOf g
  have hprimZMod : IsPrimitiveRoot (g : ZMod p) (p - 1) :=
    IsPrimitiveRoot.coe_units_iff.mpr hprimUnits
  have hprimRes : IsPrimitiveRoot
      (algebraMap (ZMod p) (ResidueField L) (g : ZMod p)) (p - 1) :=
    IsPrimitiveRoot.map_of_injective
      (f := algebraMap (ZMod p) (ResidueField L)) hprimZMod
      (algebraMap (ZMod p) (ResidueField L)).injective
  have hprimInt : IsPrimitiveRoot
      (teichmuller L
        (algebraMap (ZMod p) (ResidueField L) (g : ZMod p))) (p - 1) :=
    IsPrimitiveRoot.map_of_injective (f := teichmuller L) hprimRes
      (teichmuller_injective L)
  let incl : ringOfIntegers L →+* L :=
    (ValuativeRel.valuation L).integer.subtype
  let zeta : L :=
    incl
      (teichmuller L
        (algebraMap (ZMod p) (ResidueField L) (g : ZMod p)))
  have hprim : IsPrimitiveRoot zeta (p - 1) :=
    IsPrimitiveRoot.map_of_injective
      (f := incl) hprimInt (by
        intro x y hxy
        change (x : L) = (y : L) at hxy
        exact Subtype.ext hxy)
  exact ⟨zeta, hprim,
    ord_eq_zero_of_pow_eq_one L (Nat.sub_pos_of_lt hp.one_lt)
      hprim.pow_eq_one⟩

/-- Exact power sums for the powers of a primitive `n`-th root, in the
range needed below. -/
private theorem primitive_root_power_sum_below
    {L : Type*} [Field L] {n k : ℕ} {zeta : L}
    (hzeta : IsPrimitiveRoot zeta n) (hk : k < n) :
    ∑ r : Fin n, (zeta ^ (r : ℕ)) ^ k =
      if k = 0 then (n : L) else 0 := by
  rw [show (∑ r : Fin n, (zeta ^ (r : ℕ)) ^ k) =
      ∑ r ∈ Finset.range n, (zeta ^ r) ^ k by
    simpa using Fin.sum_univ_eq_sum_range
      (fun r : ℕ ↦ (zeta ^ r) ^ k) n]
  by_cases hkzero : k = 0
  · subst k
    simp
  rw [if_neg hkzero]
  have hne : zeta ^ k ≠ 1 := by
    intro h
    have hdiv := hzeta.dvd_of_pow_eq_one k h
    exact hkzero (Nat.eq_zero_of_dvd_of_lt hdiv hk)
  have hpow : (zeta ^ k) ^ n = 1 := by
    rw [← pow_mul, mul_comm k n, pow_mul, hzeta.pow_eq_one, one_pow]
  have hgeom : (∑ r ∈ Finset.range n, (zeta ^ k) ^ r) *
      (zeta ^ k - 1) = 0 := by
    rw [geom_sum_mul, hpow, sub_self]
  have hsum : ∑ r ∈ Finset.range n, (zeta ^ k) ^ r = 0 :=
    (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne)
  simpa only [← pow_mul, mul_comm k] using hsum

/-- Reindex the coordinate expansion of a power basis whose dimension is
identified with `p`. -/
private theorem powerBasis_sum_coeff
    {E L : Type*} [Field E] [Field L] [Algebra E L]
    {p : ℕ} (pb : PowerBasis E L) (hdim : pb.dim = p) (x : L) :
    (∑ i : Fin p,
      algebraMap E L
          (pb.basis.repr x (Fin.cast hdim.symm i)) *
        pb.gen ^ (i : ℕ)) = x := by
  let e : Fin p ≃ Fin pb.dim := (Fin.castOrderIso hdim.symm).toEquiv
  calc
    (∑ i : Fin p,
        algebraMap E L
            (pb.basis.repr x (Fin.cast hdim.symm i)) *
          pb.gen ^ (i : ℕ)) =
        ∑ j : Fin pb.dim,
          algebraMap E L (pb.basis.repr x j) * pb.gen ^ (j : ℕ) := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro i hi
      rfl
    _ = ∑ j : Fin pb.dim, (pb.basis.repr x j) • pb.basis j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [PowerBasis.coe_basis]
      exact (Algebra.smul_def _ _).symm
    _ = x := pb.basis.sum_repr x

/-- Coordinates of an explicitly supplied power-basis expansion. -/
private theorem powerBasis_coeff_sum
    {E L : Type*} [Field E] [Field L] [Algebra E L]
    {p : ℕ} (pb : PowerBasis E L) (hdim : pb.dim = p)
    (Y : Fin p → E) (i : Fin p) :
    pb.basis.repr
        (∑ j : Fin p, algebraMap E L (Y j) * pb.gen ^ (j : ℕ))
        (Fin.cast hdim.symm i) = Y i := by
  let e : Fin p ≃ Fin pb.dim := (Fin.castOrderIso hdim.symm).toEquiv
  let Y' : Fin pb.dim → E := fun j ↦ Y (e.symm j)
  have hsum :
      (∑ j : Fin p, algebraMap E L (Y j) * pb.gen ^ (j : ℕ)) =
        ∑ j : Fin pb.dim, Y' j • pb.basis j := by
    rw [← e.sum_comp]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [Y']
    rw [PowerBasis.coe_basis]
    simp only [e, Equiv.symm_apply_apply, Algebra.smul_def]
    congr 2
  rw [hsum, ← pb.basis.equivFun_symm_apply]
  change pb.basis.equivFun (pb.basis.equivFun.symm Y')
      (Fin.cast hdim.symm i) = Y i
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- A binomial expansion whose coefficients are padded to the full power
basis dimension. -/
private theorem powerBasis_coeff_add_pow
    {E L : Type*} [Field E] [Field L] [Algebra E L]
    {p : ℕ} (pb : PowerBasis E L) (hdim : pb.dim = p)
    (xi : E) (n k : Fin p) :
    pb.basis.repr
        ((pb.gen + algebraMap E L xi) ^ (n : ℕ))
        (Fin.cast hdim.symm k) =
      if (k : ℕ) ≤ (n : ℕ) then
        ((n : ℕ).choose (k : ℕ) : E) * xi ^ ((n : ℕ) - (k : ℕ))
      else 0 := by
  let A : Fin p → E := fun j ↦
    if (j : ℕ) ≤ (n : ℕ) then
      ((n : ℕ).choose (j : ℕ) : E) * xi ^ ((n : ℕ) - (j : ℕ))
    else 0
  let B : ℕ → L := fun j ↦
    if hj : j < p then algebraMap E L (A ⟨j, hj⟩) * pb.gen ^ j else 0
  have hexp : (pb.gen + algebraMap E L xi) ^ (n : ℕ) =
      ∑ j : Fin p, algebraMap E L (A j) * pb.gen ^ (j : ℕ) := by
    rw [add_pow]
    symm
    rw [show (∑ j : Fin p, algebraMap E L (A j) * pb.gen ^ (j : ℕ)) =
        ∑ j : Fin p, B j by
      apply Finset.sum_congr rfl
      intro j hj
      simp [B]]
    rw [Fin.sum_univ_eq_sum_range]
    symm
    calc
      (∑ m ∈ Finset.range ((n : ℕ) + 1),
          pb.gen ^ m * algebraMap E L xi ^ ((n : ℕ) - m) *
            ((n : ℕ).choose m : L)) =
          ∑ m ∈ Finset.range ((n : ℕ) + 1), B m := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjn : j ≤ (n : ℕ) := by
          simp only [Finset.mem_range] at hj
          omega
        have hjp : j < p := lt_of_le_of_lt hjn n.isLt
        simp only [B, A, hjp, dif_pos, if_pos hjn, map_mul, map_natCast,
          map_pow]
        ring
      _ = ∑ i ∈ Finset.range p, B i := by
        apply Finset.sum_subset
        · intro j hj
          simp only [Finset.mem_range] at hj ⊢
          omega
        · intro j hjp hjnot
          have hjn : (n : ℕ) < j := by
            simp only [Finset.mem_range, not_lt] at hjnot
            omega
          have hjp' : j < p := Finset.mem_range.mp hjp
          have hnotle : ¬ (⟨j, hjp'⟩ : Fin p) ≤ n := by
            intro hle
            exact (Nat.not_le.mpr hjn) hle
          simp [B, A, hjp', hnotle]
  rw [hexp, powerBasis_coeff_sum pb hdim A k]

/-- The `k`-th coordinate of a translated power minus the original power. -/
private theorem powerBasis_coeff_translated_sub
    {E L : Type*} [Field E] [Field L] [Algebra E L]
    {p : ℕ} (pb : PowerBasis E L) (hdim : pb.dim = p)
    (xi : E) (n k : Fin p) :
    pb.basis.repr
        ((pb.gen + algebraMap E L xi) ^ (n : ℕ) - pb.gen ^ (n : ℕ))
        (Fin.cast hdim.symm k) =
      if (k : ℕ) < (n : ℕ) then
        ((n : ℕ).choose (k : ℕ) : E) * xi ^ ((n : ℕ) - (k : ℕ))
      else 0 := by
  rw [map_sub]
  change pb.basis.repr ((pb.gen + algebraMap E L xi) ^ (n : ℕ))
      (Fin.cast hdim.symm k) -
    pb.basis.repr (pb.gen ^ (n : ℕ)) (Fin.cast hdim.symm k) = _
  rw [powerBasis_coeff_add_pow pb hdim xi n k]
  have hself : pb.basis.repr (pb.gen ^ (n : ℕ))
      (Fin.cast hdim.symm k) = if k = n then 1 else 0 := by
    rw [show pb.gen ^ (n : ℕ) = pb.basis (Fin.cast hdim.symm n) by
      rw [PowerBasis.coe_basis]
      rfl]
    rw [Module.Basis.repr_self]
    by_cases h : k = n
    · subst k
      simp
    · simp only [Finsupp.single_apply]
      have hcast : Fin.cast hdim.symm n ≠ Fin.cast hdim.symm k :=
        fun hcast ↦ h (Fin.cast_injective hdim.symm hcast).symm
      simp [hcast, h]
  rw [hself]
  by_cases hkn : (k : ℕ) < (n : ℕ)
  · have hle : (k : ℕ) ≤ (n : ℕ) := Nat.le_of_lt hkn
    have hne : k ≠ n := by intro h; subst k; omega
    simp [hkn, hle, hne]
  · rw [if_neg hkn]
    by_cases hEq : k = n
    · subst k
      simp
    · have hnk : (n : ℕ) < (k : ℕ) := by omega
      have hnle : ¬ (k : ℕ) ≤ (n : ℕ) := Nat.not_le.mpr hnk
      simp [hEq, hnle]

/-- The explicit `k`-th coefficient of the exact translation part. -/
private theorem powerBasis_coeff_translation_sum
    {E L : Type*} [Field E] [Field L] [Algebra E L]
    {p : ℕ} (pb : PowerBasis E L) (hdim : pb.dim = p)
    (xi : E) (Y : Fin p → E) (k : Fin p) :
    pb.basis.repr
        (∑ i : Fin p, algebraMap E L (Y i) *
          ((pb.gen + algebraMap E L xi) ^ (i : ℕ) - pb.gen ^ (i : ℕ)))
        (Fin.cast hdim.symm k) =
      ∑ i : Fin p, if (k : ℕ) < (i : ℕ) then
        ((i : ℕ).choose (k : ℕ) : E) *
          xi ^ ((i : ℕ) - (k : ℕ)) * Y i
      else 0 := by
  rw [map_sum]
  rw [Finset.sum_apply']
  apply Finset.sum_congr rfl
  intro i hi
  rw [show algebraMap E L (Y i) *
      ((pb.gen + algebraMap E L xi) ^ (i : ℕ) - pb.gen ^ (i : ℕ)) =
      Y i • ((pb.gen + algebraMap E L xi) ^ (i : ℕ) - pb.gen ^ (i : ℕ)) by
    rw [Algebra.smul_def]]
  rw [pb.basis.repr.map_smul, Finsupp.smul_apply]
  change Y i * pb.basis.repr
      ((pb.gen + algebraMap E L xi) ^ (i : ℕ) - pb.gen ^ (i : ℕ))
        (Fin.cast hdim.symm k) = _
  rw [powerBasis_coeff_translated_sub pb hdim xi i k]
  split_ifs <;> ring

/-- The Hensel correction contributes no shallow coefficient.  The bound is
stated in the upper field's normalization; this avoids dividing a
`WithTop ℤ` inequality by the ramification index. -/
private theorem hensel_error_coefficient_bound
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    {p t t₂ : ℕ} (hp : p.Prime) (hodd : 2 < p)
    (hram : ramificationIndex E L = p)
    (pb : PowerBasis E L) (hdim : pb.dim = p)
    (hgen : ord L pb.gen = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ t) (ht : t ≤ t₂)
    {q V : ℤ} {theta : L} (htheta : ord L theta = (q : WithTop ℤ))
    (Y : Fin p → E)
    (hexp : (∑ i : Fin p, algebraMap E L (Y i) * pb.gen ^ (i : ℕ)) = theta)
    (xi : E) (hxi : ord L (algebraMap E L xi) = 0)
    (eta : L)
    (heta : ((V - ((p - 1) * t : ℕ) : ℤ) : WithTop ℤ) ≤ ord L eta)
    (hV : (((p * (p - 1) * t₂ : ℕ) : ℤ) : WithTop ℤ) ≤
      (V : WithTop ℤ))
    (j : ℕ) (hjpos : 0 < j) (hjlt : j < p) :
    let k : Fin p := ⟨j - 1, by omega⟩
    let err : L := ∑ i : Fin p, algebraMap E L (Y i) *
      ((pb.gen + algebraMap E L xi + eta) ^ (i : ℕ) -
        (pb.gen + algebraMap E L xi) ^ (i : ℕ))
    ((q + ((p * j * t : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤
      p • ord E (pb.basis.repr err (Fin.cast hdim.symm k)) := by
  let k : Fin p := ⟨j - 1, by omega⟩
  let center : L := pb.gen + algebraMap E L xi
  let err : L := ∑ i : Fin p, algebraMap E L (Y i) *
    ((center + eta) ^ (i : ℕ) - center ^ (i : ℕ))
  have hcenter : ord L center = ((-(t : ℤ) : ℤ) : WithTop ℤ) := by
    have htpos : (0 : ℤ) < (t : ℤ) := by
      have htposNat : 0 < t := Nat.pos_of_ne_zero (fun ht0 ↦ by
        apply hprime
        rw [ht0]
        exact dvd_zero p)
      exact_mod_cast htposNat
    have hne : ord L pb.gen ≠ ord L (algebraMap E L xi) := by
      rw [hgen, hxi]
      exact ne_of_lt (WithTop.coe_lt_coe.mpr (neg_neg_of_pos htpos))
    dsimp only [center]
    rw [ord_add_eq_min L hne, hgen, hxi]
    exact min_eq_left (WithTop.coe_le_coe.mpr (neg_nonpos.mpr htpos.le))
  have hVint : ((p * (p - 1) * t₂ : ℕ) : ℤ) ≤ V :=
    WithTop.coe_le_coe.mp hV
  have hVjNat : (p - 1) * (j + 1) * t ≤ p * (p - 1) * t₂ := by
    have hjone : j + 1 ≤ p := by omega
    calc
      (p - 1) * (j + 1) * t ≤ (p - 1) * p * t := by
        exact Nat.mul_le_mul_right t (Nat.mul_le_mul_left (p - 1) hjone)
      _ ≤ (p - 1) * p * t₂ := Nat.mul_le_mul_left ((p - 1) * p) ht
      _ = p * (p - 1) * t₂ := by ring
  have hVj : (((p - 1) * (j + 1) * t : ℕ) : ℤ) ≤ V := by
    have hcast : (((p - 1) * (j + 1) * t : ℕ) : ℤ) ≤
        ((p * (p - 1) * t₂ : ℕ) : ℤ) := by
      exact_mod_cast hVjNat
    exact hcast.trans hVint
  have hetaBase : ((-(t : ℤ) : ℤ) : WithTop ℤ) ≤ ord L eta := by
    apply le_trans (b := ((V - ((p - 1) * t : ℕ) : ℤ) : WithTop ℤ))
    · apply WithTop.coe_le_coe.mpr
      have hsmallNat : (p - 2) * t ≤ (p - 1) * (j + 1) * t := by
        apply Nat.mul_le_mul_right t
        calc
          p - 2 ≤ p - 1 := by omega
          _ = (p - 1) * 1 := by ring
          _ ≤ (p - 1) * (j + 1) := by
            exact Nat.mul_le_mul_left (p - 1) (by omega)
      have hsmall : (((p - 2) * t : ℕ) : ℤ) ≤ V := by
        have hcast : (((p - 2) * t : ℕ) : ℤ) ≤
            (((p - 1) * (j + 1) * t : ℕ) : ℤ) := by
          exact_mod_cast hsmallNat
        exact hcast.trans hVj
      have hsubNat : (p - 2) * t + t = (p - 1) * t := by
        have hpSub : p - 1 = (p - 2) + 1 := by omega
        rw [hpSub, Nat.add_mul]
        simp
      have hsubInt : (((p - 2) * t : ℕ) : ℤ) + (t : ℤ) =
          (((p - 1) * t : ℕ) : ℤ) := by exact_mod_cast hsubNat
      omega
    · exact heta
  have hcenterMem : center ∈ lattice L (-(t : ℤ)) :=
    (mem_lattice L).2 hcenter.ge
  have hcenterEtaMem : center + eta ∈ lattice L (-(t : ℤ)) :=
    add_mem_lattice L hcenterMem ((mem_lattice L).2 hetaBase)
  have hterm : ∀ i : Fin p,
      algebraMap E L (Y i) *
          ((center + eta) ^ (i : ℕ) - center ^ (i : ℕ)) ∈
        lattice L (q + V - ((p - 2) * t : ℕ)) := by
    intro i
    by_cases hi0 : (i : ℕ) = 0
    · have hi : i = ⟨0, hp.pos⟩ := Fin.ext hi0
      subst i
      simp
    have hipos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi0
    have hpre := preliminary_coefficient_bound E L hp hram hgen hprime Y i
    rw [hexp] at hpre
    by_cases hYiZero : Y i = 0
    · simp [hYiZero]
    have hYi : Y i ≠ 0 := hYiZero
    obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp
      ((ord_ne_top_iff E).2 hYi)
    have hYiInt : q + (((i : ℕ) * t : ℕ) : ℤ) ≤ (p : ℤ) * z := by
      rw [ord_mul, ord_algebraMap, hram, ord_pow, hgen, htheta,
        ← hz, ← WithTop.coe_nsmul, ← WithTop.coe_nsmul,
        ← WithTop.coe_add] at hpre
      have hpreInt := WithTop.coe_le_coe.mp hpre
      simp only [nsmul_eq_mul] at hpreInt
      push_cast at hpreInt ⊢
      ring_nf at hpreInt ⊢
      omega
    have hYiMem : algebraMap E L (Y i) ∈
        lattice L (q + (((i : ℕ) * t : ℕ) : ℤ)) := by
      rw [mem_lattice, ord_algebraMap, hram, ← hz,
        ← WithTop.coe_nsmul]
      apply WithTop.coe_le_coe.mpr
      simpa only [nsmul_eq_mul] using hYiInt
    have hdiffMem := pow_sub_pow_mem_lattice L hcenterEtaMem hcenterMem
      (by
        rw [show center + eta - center = eta by ring]
        exact (mem_lattice L).2 heta) (i : ℕ)
    have hmul := mul_mem_lattice L hYiMem hdiffMem
    have hisub : (i : ℕ) - 1 + 1 = (i : ℕ) := Nat.sub_add_cancel hipos
    have hiSubZ : (((i : ℕ) - 1 : ℕ) : ℤ) = ((i : ℕ) : ℤ) - 1 := by
      have hcast := congrArg (fun n : ℕ ↦ (n : ℤ)) hisub
      push_cast at hcast
      omega
    have hpOneZ : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
      omega
    have hpTwoZ : ((p - 2 : ℕ) : ℤ) = (p : ℤ) - 2 := by
      omega
    have hdepth :
        q + (((i : ℕ) * t : ℕ) : ℤ) +
            (V - (((p - 1) * t : ℕ) : ℤ) +
              (((i : ℕ) - 1 : ℕ) : ℤ) * -(t : ℤ)) =
          q + V - (((p - 2) * t : ℕ) : ℤ) := by
      push_cast
      rw [hiSubZ, hpOneZ, hpTwoZ]
      ring
    rw [hdepth] at hmul
    exact hmul
  have herrMem : err ∈ lattice L (q + V - ((p - 2) * t : ℕ)) := by
    apply sum_mem_lattice L
    intro i hi
    exact hterm i
  let Z : E := pb.basis.repr err (Fin.cast hdim.symm k)
  have hpreZ := preliminary_coefficient_bound E L hp hram hgen hprime
    (fun i : Fin p ↦ pb.basis.repr err (Fin.cast hdim.symm i)) k
  rw [powerBasis_sum_coeff pb hdim err] at hpreZ
  have herrLower :
      ((q + V - ((p - 2) * t : ℕ) : ℤ) : WithTop ℤ) ≤ ord L err :=
    (mem_lattice L).1 herrMem
  change ((q + ((p * j * t : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤ p • ord E Z
  by_cases hZ : Z = 0
  · rw [hZ, ord_zero]
    have hptop : p • (⊤ : WithTop ℤ) = ⊤ := by
      rw [show p = (p - 1) + 1 by omega, add_nsmul]
      simp
    rw [hptop]
    exact le_top
  obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp
    ((ord_ne_top_iff E).2 hZ)
  have hbound := herrLower.trans hpreZ
  have hboundInt : q + V - (((p - 2) * t : ℕ) : ℤ) ≤
      (p : ℤ) * z + ((j - 1 : ℕ) : ℤ) * -(t : ℤ) := by
    change ord L err ≤
      ord L (algebraMap E L Z * pb.gen ^ (k : ℕ)) at hpreZ
    rw [ord_mul, ord_algebraMap, hram, ord_pow, hgen, ← hz,
      ← WithTop.coe_nsmul, ← WithTop.coe_nsmul,
      ← WithTop.coe_add] at hbound
    have hbound' := WithTop.coe_le_coe.mp hbound
    simp only [nsmul_eq_mul, k] at hbound'
    push_cast at hbound' ⊢
    exact hbound'
  rw [← hz, ← WithTop.coe_nsmul]
  apply WithTop.coe_le_coe.mpr
  simp only [nsmul_eq_mul]
  have harithNat : p * j * t + (p - 2) * t =
      (p - 1) * (j + 1) * t + (j - 1) * t := by
    have hpOne : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
    have hpTwo : p - 2 + 2 = p := Nat.sub_add_cancel hodd.le
    have hjOne : j - 1 + 1 = j := Nat.sub_add_cancel hjpos
    have hpmOne : p - 1 = (p - 2) + 1 := by omega
    have hjpOne : j + 1 = (j - 1) + 2 := by omega
    rw [hpmOne, hjpOne]
    nth_rewrite 1 [← hpTwo]
    nth_rewrite 1 [← hjOne]
    ring
  have harithZ : ((p * j * t : ℕ) : ℤ) + (((p - 2) * t : ℕ) : ℤ) =
      (((p - 1) * (j + 1) * t : ℕ) : ℤ) +
        (((j - 1) * t : ℕ) : ℤ) := by
    exact_mod_cast harithNat
  have hjSubMulZ : ((j - 1 : ℕ) : ℤ) * (t : ℤ) =
      (((j - 1) * t : ℕ) : ℤ) := by
    push_cast
    ring
  have hnegZ : ((j - 1 : ℕ) : ℤ) * -(t : ℤ) =
      -(((j - 1) * t : ℕ) : ℤ) := by
    rw [← hjSubMulZ]
    ring
  rw [hnegZ] at hboundInt
  omega

/-- Averaging the `(j-1)`-st translated coefficient against `xi⁻¹`
kills every higher coefficient and leaves `(p-1)jY_j`. -/
private theorem weighted_translation_coeff_sum
    {E : Type*} [Field E] {p : ℕ} (hp : p.Prime)
    {zeta : E} (hzeta : IsPrimitiveRoot zeta (p - 1))
    (Y : Fin p → E) (j : ℕ) (hjpos : 0 < j) (hjlt : j < p) :
    let k : Fin p := ⟨j - 1, by omega⟩
    ∑ r : Fin (p - 1), (zeta ^ (r : ℕ))⁻¹ *
        (∑ i : Fin p, if (k : ℕ) < (i : ℕ) then
          ((i : ℕ).choose (k : ℕ) : E) *
            (zeta ^ (r : ℕ)) ^ ((i : ℕ) - (k : ℕ)) * Y i
        else 0) =
      ((p - 1 : ℕ) : E) * (j : E) * Y ⟨j, hjlt⟩ := by
  let k : Fin p := ⟨j - 1, by omega⟩
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hother : ∀ i ∈ (Finset.univ : Finset (Fin p)),
      i ≠ ⟨j, hjlt⟩ →
      (∑ r : Fin (p - 1), (zeta ^ (r : ℕ))⁻¹ *
        if (k : ℕ) < (i : ℕ) then
          ((i : ℕ).choose (k : ℕ) : E) *
            (zeta ^ (r : ℕ)) ^ ((i : ℕ) - (k : ℕ)) * Y i
        else 0) = 0 := by
    intro i hi hij
    by_cases hik : (k : ℕ) < (i : ℕ)
    · simp_rw [if_pos hik]
      rw [show (∑ r : Fin (p - 1), (zeta ^ (r : ℕ))⁻¹ *
          (((i : ℕ).choose (k : ℕ) : E) *
            (zeta ^ (r : ℕ)) ^ ((i : ℕ) - (k : ℕ)) * Y i)) =
          ((i : ℕ).choose (k : ℕ) : E) * Y i *
            ∑ r : Fin (p - 1), (zeta ^ (r : ℕ))⁻¹ *
              (zeta ^ (r : ℕ)) ^ ((i : ℕ) - (k : ℕ)) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring]
      have hzeta0 : zeta ≠ 0 := hzeta.ne_zero (by omega)
      change j - 1 < (i : ℕ) at hik
      have hji : j < (i : ℕ) := by
        have hne : (i : ℕ) ≠ j := by
          intro h
          apply hij
          apply Fin.ext
          simpa using h
        omega
      have hpow (r : Fin (p - 1)) :
          (zeta ^ (r : ℕ))⁻¹ *
              (zeta ^ (r : ℕ)) ^ ((i : ℕ) - (k : ℕ)) =
            (zeta ^ (r : ℕ)) ^ ((i : ℕ) - j) := by
        have hexp : (i : ℕ) - (k : ℕ) = ((i : ℕ) - j) + 1 := by
          change (i : ℕ) - (j - 1) = ((i : ℕ) - j) + 1
          omega
        rw [hexp, pow_succ]
        field_simp
      simp_rw [hpow]
      have hbelow : (i : ℕ) - j < p - 1 := by omega
      rw [primitive_root_power_sum_below hzeta hbelow, if_neg (by omega)]
      simp
    · simp_rw [if_neg hik]
      simp
  rw [Finset.sum_eq_single ⟨j, hjlt⟩ hother (by simp)]
  have hik : (k : ℕ) < j := by
    dsimp only [k]
    omega
  change (∑ r : Fin (p - 1), (zeta ^ (r : ℕ))⁻¹ *
      if j - 1 < j then
        ((j : ℕ).choose (j - 1) : E) *
          (zeta ^ (r : ℕ)) ^ (j - (j - 1)) * Y ⟨j, hjlt⟩
      else 0) = ((p - 1 : ℕ) : E) * (j : E) * Y ⟨j, hjlt⟩
  have hjsub : j - 1 < j := by omega
  simp_rw [if_pos hjsub]
  rw [show (∑ r : Fin (p - 1), (zeta ^ (r : ℕ))⁻¹ *
      (((j : ℕ).choose (j - 1) : E) *
        (zeta ^ (r : ℕ)) ^ (j - (j - 1)) * Y ⟨j, hjlt⟩)) =
      ((j : ℕ).choose (j - 1) : E) * Y ⟨j, hjlt⟩ *
        ∑ r : Fin (p - 1), (zeta ^ (r : ℕ))⁻¹ *
          (zeta ^ (r : ℕ)) ^ (j - (j - 1)) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring]
  have hzeta0 : zeta ≠ 0 := hzeta.ne_zero (by omega)
  have hpow (r : Fin (p - 1)) :
      (zeta ^ (r : ℕ))⁻¹ *
          (zeta ^ (r : ℕ)) ^ (j - (j - 1)) = 1 := by
    have hexp : j - (j - 1) = 1 := by omega
    rw [hexp, pow_one, inv_mul_cancel₀]
    exact pow_ne_zero _ hzeta0
  simp_rw [hpow]
  rw [← Nat.choose_symm (show j - 1 ≤ j by omega),
    show j - (j - 1) = 1 by omega, Nat.choose_one_right]
  simp
  rw [Nat.cast_sub hp.one_le]
  norm_num
  ring

/-- The coefficient of the exact translation by `xi`, before the Hensel correction. -/
private def translationCoefficient
    {E : Type*} [Field E] {p : ℕ} (xi : E) (Y : Fin p → E) (k : Fin p) : E :=
  ∑ i : Fin p, if (k : ℕ) < (i : ℕ) then
    ((i : ℕ).choose (k : ℕ) : E) * xi ^ ((i : ℕ) - (k : ℕ)) * Y i
  else 0

/-- The change in the expansion caused by the Hensel correction `eta`. -/
private def translationError
    {E L : Type*} [Field E] [Field L] [Algebra E L]
    {p : ℕ} (Delta : L) (xi : E) (eta : L) (Y : Fin p → E) : L :=
  ∑ i : Fin p, algebraMap E L (Y i) *
    ((Delta + algebraMap E L xi + eta) ^ (i : ℕ) -
      (Delta + algebraMap E L xi) ^ (i : ℕ))

/-- Split the coordinate of a conjugate difference into its exact translation
and Hensel error. -/
private theorem powerBasis_coeff_conjugate_sub
    {E L : Type*} [Field E] [Field L] [Algebra E L]
    {p : ℕ} (pb : PowerBasis E L) (hdim : pb.dim = p)
    (sigma : Gal(L/E)) (xi : E) (eta : L)
    (hsigma : sigma pb.gen = pb.gen + algebraMap E L xi + eta)
    (Y : Fin p → E) (k : Fin p) :
    pb.basis.repr
        (sigma (∑ i : Fin p, algebraMap E L (Y i) * pb.gen ^ (i : ℕ)) -
          ∑ i : Fin p, algebraMap E L (Y i) * pb.gen ^ (i : ℕ))
        (Fin.cast hdim.symm k) =
      translationCoefficient xi Y k +
        pb.basis.repr (translationError pb.gen xi eta Y) (Fin.cast hdim.symm k) := by
  have hsplit :
      sigma (∑ i : Fin p, algebraMap E L (Y i) * pb.gen ^ (i : ℕ)) -
          ∑ i : Fin p, algebraMap E L (Y i) * pb.gen ^ (i : ℕ) =
        (∑ i : Fin p, algebraMap E L (Y i) *
          ((pb.gen + algebraMap E L xi) ^ (i : ℕ) - pb.gen ^ (i : ℕ))) +
          translationError pb.gen xi eta Y := by
    simp only [translationError, map_sum, map_mul, map_pow, sigma.commutes, hsigma]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsplit, map_add, Finsupp.add_apply, powerBasis_coeff_translation_sum pb hdim]
  rfl

/-- Average the translated coefficients and cancel the unit multiplier `(p-1)j`.
The depth may be infinite, so this also applies to a zero original element. -/
private theorem coefficient_bound_of_translation_bounds
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {p : ℕ} (hp : p.Prime) (hchar : residueCharacteristic E = p)
    {zeta : E} (hzeta : IsPrimitiveRoot zeta (p - 1)) (hzetaOrd : ord E zeta = 0)
    (Y : Fin p → E) (j : ℕ) (hjpos : 0 < j) (hjlt : j < p)
    {d : WithTop ℤ}
    (hC : ∀ r : Fin (p - 1),
      d ≤ ord E (translationCoefficient (zeta ^ (r : ℕ)) Y ⟨j - 1, by omega⟩)) :
    d ≤ ord E (Y ⟨j, hjlt⟩) := by
  have hsum : d ≤ ord E
      (∑ r : Fin (p - 1), (zeta ^ (r : ℕ))⁻¹ *
        translationCoefficient (zeta ^ (r : ℕ)) Y ⟨j - 1, by omega⟩) := by
    apply ord_sum E
    intro r _
    simpa only [ord_mul, ord_inv, ord_pow, hzetaOrd, nsmul_zero, neg_zero,
      zero_add] using hC r
  rw [show (∑ r : Fin (p - 1), (zeta ^ (r : ℕ))⁻¹ *
      translationCoefficient (zeta ^ (r : ℕ)) Y ⟨j - 1, by omega⟩) =
        ((p - 1 : ℕ) : E) * (j : E) * Y ⟨j, hjlt⟩ from
      weighted_translation_coeff_sum hp hzeta Y j hjpos hjlt] at hsum
  simpa only [ord_mul,
    ord_natCast_eq_zero_of_lt_residueCharacteristic E (j := p - 1)
      (by omega) (by rw [hchar]; omega),
    ord_natCast_eq_zero_of_lt_residueCharacteristic E (j := j) hjpos
      (by rw [hchar]; exact hjlt), zero_add] using hsum

/-- Express the Hensel error bound in the two lower fields' normalizations.
Both upper ramification indices are `p`. -/
private theorem translationError_coefficient_bound
    {E M L : Type*} [Field E] [Field M] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L] [Algebra M L] [ValuativeExtension M L]
    {p t t₂ : ℕ} (hp : p.Prime) (hodd : 2 < p)
    (hramE : ramificationIndex E L = p) (hramM : ramificationIndex M L = p)
    (pb : PowerBasis E L) (hdim : pb.dim = p)
    (hgen : ord L pb.gen = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ t) (ht : t ≤ t₂)
    {theta : M} (htheta : theta ≠ 0) (Y : Fin p → E)
    (hexp : algebraMap M L theta =
      ∑ i : Fin p, algebraMap E L (Y i) * pb.gen ^ (i : ℕ))
    (xi : E) (hxi : ord E xi = 0) (eta : L)
    (heta : eta = 0 ∨ ∃ V : ℤ,
      (((p * (p - 1) * t₂ : ℕ) : ℤ) : WithTop ℤ) ≤ (V : WithTop ℤ) ∧
      ((V - ((p - 1) * t : ℕ) : ℤ) : WithTop ℤ) ≤ ord L eta)
    (j : ℕ) (hjpos : 0 < j) (hjlt : j < p) :
    ord M theta + (((j * t : ℕ) : ℤ) : WithTop ℤ) ≤
      ord E (pb.basis.repr (translationError pb.gen xi eta Y)
        (Fin.cast hdim.symm ⟨j - 1, by omega⟩)) := by
  rcases heta with rfl | ⟨V, hV, heta⟩
  · simp [translationError]
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff M).2 htheta)
  have hxiL : ord L (algebraMap E L xi) = 0 := by
    rw [ord_algebraMap, hxi, nsmul_zero]
  have hthetaL : ord L (algebraMap M L theta) =
      (((p : ℤ) * q : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hramM, ← hq, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have herr := hensel_error_coefficient_bound E L hp hodd hramE pb hdim
    hgen hprime ht hthetaL Y hexp.symm xi hxiL eta heta hV j hjpos hjlt
  apply (nsmul_le_nsmul_iff_right_withTop hp.ne_zero).mp
  have hscale : p • (ord M theta + (((j * t : ℕ) : ℤ) : WithTop ℤ)) =
      (((p : ℤ) * q + ((p * j * t : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
    rw [← hq, ← WithTop.coe_add, ← WithTop.coe_nsmul]
    congr 1
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring
  rw [hscale]
  exact herr

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K]
variable [Module.Free F K] [Module.Finite F K] [IsGalois F K]

section IntermediateFields

omit [Module.Free F K]

variable (B₁ B₂ : IntermediateField F K)

private local instance (B : IntermediateField F K) : ValuativeRel B :=
  Basic.intermediateFieldValuativeRel B
private local instance (B : IntermediateField F K) : TopologicalSpace B :=
  Basic.intermediateFieldTopology B
private local instance (B : IntermediateField F K) : IsNonarchimedeanLocalField B :=
  Basic.intermediateField_localField B
private local instance (B : IntermediateField F K) : ValuativeExtension F B :=
  Basic.intermediateField_lowerValuativeExtension B
private local instance (B : IntermediateField F K) : ValuativeExtension B K :=
  Basic.intermediateField_upperValuativeExtension B

/-- A degree-`p` intermediate field in the total diamond has upper degree and
ramification index `p`, and is Galois over the base. -/
private theorem intermediateField_extraction_data
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1) (B : IntermediateField F K)
    (hdegree : Module.finrank F B = p) :
    IsGalois F B ∧ Module.finrank B K = p ∧ ramificationIndex B K = p := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hupper, hcyc, _⟩ :=
    Basic.intermediateField_tower_compatible hp hG B hdegree
  have hresB : residueDegree B K = 1 := by
    have hmul := residueDegree_mul_local (F := F) (K := K) B
    rw [hres] at hmul
    exact (mul_eq_one.mp hmul).2
  refine ⟨hcyc.1, hupper, ?_⟩
  have hfund := finrank_eq_ramificationIndex_mul_residueDegree B K
  rwa [hresB, mul_one, hupper, eq_comm] at hfund

section CoefficientInduction

omit [IsGalois F K]

variable [IsGalois F B₁]
variable {p t : ℕ} (pb : PowerBasis B₂ K) (hdim : pb.dim = p)

/-- The induction hypothesis and the lower break bound control the preceding
coefficient of every actual conjugate difference. -/
private theorem conjugate_difference_coefficient_bound
    (hbreak : PrimeCyclicExtension.IsLowerBreak F B₁ t)
    (j : ℕ) (hjpos : 0 < j) (hjlt : j < p)
    (hprev : ∀ (theta : B₁) (Y : Fin p → B₂),
      algebraMap B₁ K theta =
          ∑ i : Fin p, algebraMap B₂ K (Y i) * pb.gen ^ (i : ℕ) →
      ord B₁ theta + ((((j - 1) * t : ℕ) : ℤ) : WithTop ℤ) ≤
        ord B₂ (Y ⟨j - 1, by omega⟩))
    (tau : Gal(B₁/F)) (theta : B₁) :
    ord B₁ theta + (((j * t : ℕ) : ℤ) : WithTop ℤ) ≤
      ord B₂ (pb.basis.repr (algebraMap B₁ K (tau theta - theta))
        (Fin.cast hdim.symm ⟨j - 1, by omega⟩)) := by
  have hind := hprev (tau theta - theta)
    (fun i ↦ pb.basis.repr (algebraMap B₁ K (tau theta - theta))
      (Fin.cast hdim.symm i)) (powerBasis_sum_coeff pb hdim _).symm
  have hmove := add_le_add_right (galois_sub_order_ge F B₁ hbreak tau theta)
    (((((j - 1) * t : ℕ) : ℤ)) : WithTop ℤ)
  have hjmul : j * t = t + (j - 1) * t := by
    conv_lhs => rw [← Nat.sub_add_cancel hjpos]
    ring
  have hdepth : (((j * t : ℕ) : ℤ) : WithTop ℤ) =
      ((t : ℤ) : WithTop ℤ) + (((((j - 1) * t : ℕ) : ℤ)) : WithTop ℤ) := by
    rw [hjmul, Nat.cast_add, WithTop.coe_add]
  apply le_trans (b := ord B₁ (tau theta - theta) +
    (((((j - 1) * t : ℕ) : ℤ)) : WithTop ℤ))
  · simpa only [hdepth, add_assoc, add_comm, add_left_comm] using hmove
  · exact hind

/-- Subtract the controlled Hensel error from the conjugate-difference
coefficient to bound the exact translated coefficient. -/
private theorem translationCoefficient_bound
    (hbreak : PrimeCyclicExtension.IsLowerBreak F B₁ t)
    (j : ℕ) (hjpos : 0 < j) (hjlt : j < p)
    (hprev : ∀ (theta : B₁) (Y : Fin p → B₂),
      algebraMap B₁ K theta =
          ∑ i : Fin p, algebraMap B₂ K (Y i) * pb.gen ^ (i : ℕ) →
      ord B₁ theta + ((((j - 1) * t : ℕ) : ℤ) : WithTop ℤ) ≤
        ord B₂ (Y ⟨j - 1, by omega⟩))
    (theta : B₁) (Y : Fin p → B₂)
    (hexp : algebraMap B₁ K theta =
      ∑ i : Fin p, algebraMap B₂ K (Y i) * pb.gen ^ (i : ℕ))
    (sigma : Gal(K/B₂)) (xi : B₂) (eta : K)
    (hsigma : sigma pb.gen = pb.gen + algebraMap B₂ K xi + eta)
    (herr : ord B₁ theta + (((j * t : ℕ) : ℤ) : WithTop ℤ) ≤
      ord B₂ (pb.basis.repr (translationError pb.gen xi eta Y)
        (Fin.cast hdim.symm ⟨j - 1, by omega⟩))) :
    ord B₁ theta + (((j * t : ℕ) : ℤ) : WithTop ℤ) ≤
      ord B₂ (translationCoefficient xi Y ⟨j - 1, by omega⟩) := by
  let tau := IntermediateField.restrictRestrictAlgEquivMapHom F B₁ B₂ K sigma
  have hcoord := powerBasis_coeff_conjugate_sub pb hdim sigma xi eta hsigma Y
    ⟨j - 1, by omega⟩
  have htau : algebraMap B₁ K (tau theta - theta) =
      sigma (algebraMap B₁ K theta) - algebraMap B₁ K theta := by
    rw [map_sub]
    congr 1
    exact IntermediateField.restrictRestrictAlgEquivMapHom_apply B₁ B₂ sigma theta
  rw [← hexp, ← htau] at hcoord
  have hbound := conjugate_difference_coefficient_bound B₁ B₂ pb hdim
    hbreak j hjpos hjlt hprev tau theta
  rw [eq_comm, ← eq_sub_iff_add_eq] at hcoord
  rw [hcoord]
  exact (le_min hbound herr).trans (ord_sub B₂ _ _)

/-- Induct simultaneously over all elements of `B₁`.  At each positive index,
translate, apply the preceding coefficient bound, and average over roots of unity. -/
private theorem powerBasis_coefficient_bounds
    (hdim : pb.dim = p)
    (hp : p.Prime) (hodd : 2 < p)
    (hram₁ : ramificationIndex B₁ K = p) (hram₂ : ramificationIndex B₂ K = p)
    (hbreak : PrimeCyclicExtension.IsLowerBreak F B₁ t)
    (hchar : residueCharacteristic B₂ = p)
    (hgen : ord K pb.gen = ((-(t : ℤ) : ℤ) : WithTop ℤ)) (hprime : ¬ p ∣ t)
    {t₂ : ℕ} (ht : t ≤ t₂)
    (hconj : ∀ xi : B₂, xi ^ (p - 1) = 1 →
      ∃ (sigma : Gal(K/B₂)) (eta : K),
        sigma pb.gen = pb.gen + algebraMap B₂ K xi + eta ∧
        (eta = 0 ∨ ∃ V : ℤ,
          (((p * (p - 1) * t₂ : ℕ) : ℤ) : WithTop ℤ) ≤ (V : WithTop ℤ) ∧
          ((V - ((p - 1) * t : ℕ) : ℤ) : WithTop ℤ) ≤ ord K eta)) :
    ∀ (theta : B₁) (Y : Fin p → B₂),
      algebraMap B₁ K theta =
          ∑ i : Fin p, algebraMap B₂ K (Y i) * pb.gen ^ (i : ℕ) →
      ∀ i : Fin p,
        ord B₁ theta + ((((i : ℕ) * t : ℕ) : ℤ) : WithTop ℤ) ≤ ord B₂ (Y i) := by
  obtain ⟨zeta, hzeta, hzetaOrd⟩ := exists_primitive_root_prime_subfield B₂ hp hchar
  suffices hclaim : ∀ (j : ℕ) (hj : j < p) (theta : B₁) (Y : Fin p → B₂),
      algebraMap B₁ K theta =
          ∑ i : Fin p, algebraMap B₂ K (Y i) * pb.gen ^ (i : ℕ) →
      ord B₁ theta + (((j * t : ℕ) : ℤ) : WithTop ℤ) ≤ ord B₂ (Y ⟨j, hj⟩) by
    intro theta Y hexp i
    exact hclaim i i.isLt theta Y hexp
  intro j
  induction j with
  | zero =>
      intro hj theta Y hexp
      have hpre := preliminary_coefficient_bound B₂ K hp hram₂ hgen hprime Y ⟨0, hj⟩
      rw [← hexp, ord_mul, ord_algebraMap, hram₁, ord_algebraMap, hram₂,
        pow_zero, ord_one, add_zero] at hpre
      simpa only [zero_mul, Nat.cast_zero, WithTop.coe_zero, add_zero] using
        (nsmul_le_nsmul_iff_right_withTop hp.ne_zero).mp hpre
  | succ j ih =>
      intro hj theta Y hexp
      by_cases htheta : theta = 0
      · have hY := congrArg (fun x : K ↦ pb.basis.repr x (Fin.cast hdim.symm ⟨j + 1, hj⟩))
          hexp
        rw [htheta, map_zero, map_zero, Finsupp.zero_apply,
          powerBasis_coeff_sum pb hdim] at hY
        simp [htheta, ← hY]
      have hprev := ih (show j < p by omega)
      apply coefficient_bound_of_translation_bounds hp hchar hzeta hzetaOrd Y
        (j + 1) (by omega) hj
      intro r
      let xi := zeta ^ (r : ℕ)
      have hxiRoot : xi ^ (p - 1) = 1 := by
        dsimp only [xi]
        rw [← pow_mul, mul_comm, pow_mul, hzeta.pow_eq_one, one_pow]
      have hxiOrd : ord B₂ xi = 0 := by simp only [xi, ord_pow, hzetaOrd, nsmul_zero]
      obtain ⟨sigma, eta, hsigma, heta⟩ := hconj xi hxiRoot
      have herr := translationError_coefficient_bound hp hodd hram₂ hram₁ pb hdim
        hgen hprime ht htheta Y hexp xi hxiOrd eta heta (j + 1) (by omega) hj
      exact translationCoefficient_bound B₁ B₂ pb hdim hbreak (j + 1) (by omega) hj
        hprev theta Y hexp sigma xi eta hsigma herr

end CoefficientInduction

/-- Apply the power-basis argument to the actual coordinate and its proved conjugates. -/
private theorem coefficient_bounds_of_coordinate
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (D : OddTotalBreakData (F := F) (K := K) hp hG)
    {Delta : K} {a : D.B₂}
    (hroot : Delta ^ p - Delta = algebraMap D.B₂ K a)
    (hDelta : ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ D.t) (hgen : Algebra.adjoin D.B₂ ({Delta} : Set K) = ⊤) :
    ∀ (theta : D.B₁) (Y : Fin p → D.B₂),
      algebraMap D.B₁ K theta =
          ∑ i : Fin p, algebraMap D.B₂ K (Y i) * Delta ^ (i : ℕ) →
      ∀ i : Fin p,
        ord D.B₁ theta + ((((i : ℕ) * D.t : ℕ) : ℤ) : WithTop ℤ) ≤
          ord D.B₂ (Y i) := by
  obtain ⟨hGalois₁, _, hram₁⟩ :=
    intermediateField_extraction_data hp hG hres D.B₁ D.degree_B₁
  obtain ⟨_, hdegree₂, hram₂⟩ :=
    intermediateField_extraction_data hp hG hres D.B₂ D.degree_B₂
  letI : IsGalois F D.B₁ := hGalois₁
  let pb : PowerBasis D.B₂ K :=
    PowerBasis.ofAdjoinEqTop (IsAlgebraic.of_finite D.B₂ Delta).isIntegral hgen
  have hpbgen : pb.gen = Delta := PowerBasis.ofAdjoinEqTop_gen _ hgen
  have hpbdim : pb.dim = p := pb.finrank.symm.trans hdegree₂
  have hbreak : PrimeCyclicExtension.IsLowerBreak F D.B₁ D.t := D.B₁_breaks.1
  have hchar₂ : residueCharacteristic D.B₂ = p :=
    (residueCharacteristic_extension_eq F D.B₂).trans hchar
  rw [← hpbgen] at hDelta ⊢
  apply powerBasis_coefficient_bounds D.B₁ D.B₂ pb hpbdim hp D.odd_prime
    hram₁ hram₂ hbreak hchar₂ hDelta hprime D.t_le_t₂
  intro xi hxi
  obtain ⟨sigma, eta, hsigma, _, _, heta⟩ :=
    oddAS_actualConjugates_of_coordinate hp hG hres hchar D Delta a hroot
      (by rwa [hpbgen] at hDelta) hgen xi hxi
  refine ⟨sigma, eta, by simpa only [hpbgen] using hsigma, ?_⟩
  rcases heta with ⟨_, rfl⟩ | ⟨_, V, hVord, _, heta⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨V, ?_, heta⟩
    simpa only [hVord] using oddTotal_primeValuationBound hp hG hres D

end IntermediateFields

/-- Paper Lemma `O:A:lem:coeff`: for the actual Artin--Schreier coordinate
chosen from the odd totally ramified diamond, every `B₂` coefficient gains
`i t` over the order of the element in `B₁`.

The existential packet retains the root equation and generation properties
of the coordinate, so later nodes can use the same `Delta` and `a`. -/
theorem coefficientExtraction {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = p)
    (D : OddTotalBreakData (F := F) (K := K) hp hG) :
    let B₁ := D.B₁
    let B₂ := D.B₂
    letI : ValuativeRel B₁ := Basic.intermediateFieldValuativeRel B₁
    letI : TopologicalSpace B₁ := Basic.intermediateFieldTopology B₁
    letI : IsNonarchimedeanLocalField B₁ := Basic.intermediateField_localField B₁
    letI : ValuativeRel B₂ := Basic.intermediateFieldValuativeRel B₂
    letI : TopologicalSpace B₂ := Basic.intermediateFieldTopology B₂
    letI : IsNonarchimedeanLocalField B₂ := Basic.intermediateField_localField B₂
    ∃ (Delta : K) (a : B₂),
      Delta ^ p - Delta = algebraMap B₂ K a ∧
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ¬ p ∣ D.t ∧
      Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ ∧
      ∀ (theta : B₁) (Y : Fin p → B₂),
        algebraMap B₁ K theta =
            ∑ i : Fin p, algebraMap B₂ K (Y i) * Delta ^ (i : ℕ) →
        ∀ i : Fin p,
          ord B₁ theta + ((((i : ℕ) * D.t : ℕ) : ℤ) : WithTop ℤ) ≤
            ord B₂ (Y i) := by
  letI : ValuativeRel D.B₁ := Basic.intermediateFieldValuativeRel D.B₁
  letI : TopologicalSpace D.B₁ := Basic.intermediateFieldTopology D.B₁
  letI : IsNonarchimedeanLocalField D.B₁ := Basic.intermediateField_localField D.B₁
  letI : ValuativeRel D.B₂ := Basic.intermediateFieldValuativeRel D.B₂
  letI : TopologicalSpace D.B₂ := Basic.intermediateFieldTopology D.B₂
  letI : IsNonarchimedeanLocalField D.B₂ := Basic.intermediateField_localField D.B₂
  obtain ⟨Delta, a, hroot, hDelta, ha, hprime, hgen⟩ := aSCoordinate hp hG hres hchar D
  exact ⟨Delta, a, hroot, hDelta, ha, hprime, hgen,
    coefficient_bounds_of_coordinate hp hG hres hchar D hroot hDelta hprime hgen⟩

end

end LanglandsSecondMainLemma.Odd.Total
