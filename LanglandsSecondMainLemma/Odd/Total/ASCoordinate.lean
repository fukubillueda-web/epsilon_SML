import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.LocalField.Lattices
import LanglandsFirstMainLemma.LocalField.MonogenicUniformizer
import LanglandsFirstMainLemma.LocalField.Valuation
import LanglandsSecondMainLemma.Odd.Total.ASApproximation
import LanglandsSecondMainLemma.Local.Newton

/-!
# Odd / Total / ASCoordinate

The approximate generator constructed in `ASApproximation` is already exact
in equal characteristic.  In mixed characteristic we apply the quantitative
Newton theorem to the translated polynomial

`(X + d)^p - (X + d) - a`.

The prime-valuation bound makes all its coefficients integral, its constant
coefficient is in the maximal ideal, and its linear coefficient is a unit.
The resulting correction has positive order, so it does not change the order
of `d`.  Finally, the prime-to-`p` order excludes the base field and hence the
coordinate generates the prime-degree upper extension.
-/

namespace LanglandsSecondMainLemma.Odd.Total

open Polynomial
open LanglandsFirstMainLemma

noncomputable section

private theorem natCast_ord_nonneg
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (n : ℕ) :
    0 ≤ ord L (n : L) := by
  exact (ord_nonneg_iff_mem_integer L _).2
    (show (n : L) ∈ ringOfIntegers L by
      exact (n : ringOfIntegers L).property)

/-- Multiplicativity of residue degrees for the canonical valuation on an
actual intermediate field. -/
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
  rw [residueDegree_eq_finrank_residueField,
    residueDegree_eq_finrank_residueField,
    residueDegree_eq_finrank_residueField]
  exact Module.finrank_mul_finrank
    (ResidueField F) (ResidueField L) (ResidueField K)

/-- The mixed-characteristic Hensel step in the fractional coordinate `d`.
Only the two inequalities actually supplied by the preceding construction are
used: `v(p)=V>pt` and `v(d^p-d-A)≥V-pt`. -/
private theorem lift_artinSchreier_root
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    {p t : ℕ} (hp : p.Prime)
    {V : ℤ} (hV : ord L (p : L) = (V : WithTop ℤ))
    (hVpt : (((p * t : ℕ) : ℤ)) < V)
    {d A : L}
    (hd : ord L d = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (herror : ((V - (p * t : ℕ) : ℤ) : WithTop ℤ) ≤
      ord L (d ^ p - d - A)) :
    ∃ Δ : L,
      Δ ^ p - Δ = A ∧
      ord L Δ = ((-(t : ℤ) : ℤ) : WithTop ℤ) := by
  let H : L[X] := (X + C d) ^ p - (X + C d) - C A
  have hrespos : (0 : WithTop ℤ) < ord L (d ^ p - d - A) :=
    (WithTop.coe_lt_coe.mpr (sub_pos.mpr hVpt)).trans_le herror
  have hHzero : H.coeff 0 = d ^ p - d - A := by
    simp [H, Polynomial.coeff_X_add_C_pow]
  have hHone : H.coeff 1 = d ^ (p - 1) * (p : L) - 1 := by
    simp [H, Polynomial.coeff_X_add_C_pow]
  have hlinearTermOrd :
      ord L (d ^ (p - 1) * (p : L)) =
        ((V - (((p - 1) * t : ℕ) : ℤ)) : WithTop ℤ) := by
    rw [ord_mul, ord_pow, hd, hV, ← WithTop.coe_nsmul, ← WithTop.coe_add]
    congr 1
    push_cast
    ring
  have hlinearTermPos : (0 : WithTop ℤ) <
      ord L (d ^ (p - 1) * (p : L)) := by
    rw [hlinearTermOrd]
    apply WithTop.coe_lt_coe.mpr
    have hmul : (p - 1) * t ≤ p * t :=
      Nat.mul_le_mul_right t (Nat.sub_le p 1)
    have hmulZ : ((((p - 1) * t : ℕ) : ℤ)) ≤ ((p * t : ℕ) : ℤ) := by
      exact_mod_cast hmul
    omega
  have hHoneOrd : ord L (H.coeff 1) = 0 := by
    have hne : ord L (d ^ (p - 1) * (p : L)) ≠ ord L (-1) := by
      simpa using ne_of_gt hlinearTermPos
    rw [hHone, sub_eq_add_neg, ord_add_eq_min L hne, ord_neg, ord_one,
      min_eq_right hlinearTermPos.le]
  have hHcoeff : ∀ n : ℕ, 0 ≤ ord L (H.coeff n) := by
    intro n
    by_cases hn0 : n = 0
    · subst n
      rw [hHzero]
      exact hrespos.le
    by_cases hn1 : n = 1
    · subst n
      rw [hHoneOrd]
    by_cases hnp : n < p
    · have hcoeff : H.coeff n = d ^ (p - n) * (p.choose n : L) := by
        simp [H, Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X,
          Polynomial.coeff_C, hn0, Ne.symm hn1]
      obtain ⟨q, hq⟩ := hp.dvd_choose_self hn0 hnp
      have hchoose : (p.choose n : L) = (p : L) * (q : L) := by
        rw [hq]
        norm_num
      have hbaseOrd : ord L (d ^ (p - n) * (p : L)) =
          ((V - (((p - n) * t : ℕ) : ℤ)) : WithTop ℤ) := by
        rw [ord_mul, ord_pow, hd, hV, ← WithTop.coe_nsmul, ← WithTop.coe_add]
        congr 1
        push_cast
        ring
      rw [hcoeff, hchoose, ← mul_assoc, ord_mul, hbaseOrd]
      apply add_nonneg
      · apply WithTop.coe_nonneg.mpr
        have hsuble : p - n ≤ p := Nat.sub_le p n
        have hmul : (p - n) * t ≤ p * t := Nat.mul_le_mul_right t hsuble
        have hmulZ : ((((p - n) * t : ℕ) : ℤ)) ≤ ((p * t : ℕ) : ℤ) := by
          exact_mod_cast hmul
        omega
      · exact natCast_ord_nonneg L q
    by_cases hnpEq : n = p
    · subst n
      simp [H, Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X,
        Polynomial.coeff_C, hp.ne_zero, hp.ne_one.symm]
    · have hpn : p < n := by omega
      simp [H, Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X,
        Polynomial.coeff_C, hn0, Ne.symm hn1,
        Nat.choose_eq_zero_of_lt hpn]
  let i : ringOfIntegers L →+* L :=
    (ValuativeRel.valuation L).integer.subtype
  have hHrange : H ∈ (Polynomial.mapRingHom i).range := by
    rw [Polynomial.mem_map_range]
    intro n
    exact ⟨⟨H.coeff n, (ord_nonneg_iff_mem_integer L _).1 (hHcoeff n)⟩, rfl⟩
  obtain ⟨h, hh⟩ := hHrange
  have hhcoeff (n : ℕ) : i (h.coeff n) = H.coeff n := by
    calc
      i (h.coeff n) = (h.map i).coeff n := by rw [Polynomial.coeff_map]
      _ = H.coeff n := congrArg (fun f : L[X] ↦ f.coeff n) hh
  have hderiv :
      ord L ((h.derivative.eval 0 : ringOfIntegers L) : L) =
        (0 : WithTop ℤ) := by
    have heval : h.derivative.eval 0 = h.coeff 1 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
      simp
    rw [heval]
    change ord L (i (h.coeff 1)) = (0 : WithTop ℤ)
    rw [hhcoeff, hHoneOrd]
  have hres : ((2 * (0 : ℤ) : ℤ) : WithTop ℤ) <
      ord L ((h.eval 0 : ringOfIntegers L) : L) := by
    have heval : i (h.eval 0) = H.coeff 0 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, hhcoeff]
    change (0 : WithTop ℤ) < ord L (i (h.eval 0))
    rw [heval, hHzero]
    exact hrespos
  obtain ⟨z, hz, hzpos, _hzbound, _hzunique⟩ :=
    Local.newton h 0 0 hderiv hres
  have hHroot : H.eval (z : L) = 0 := by
    calc
      H.eval (z : L) = (Polynomial.mapRingHom i h).eval (i z) := by
        simpa [i] using
          congrArg (fun f : L[X] ↦ f.eval (z : L)) hh.symm
      _ = i (h.eval z) := Polynomial.eval_map_apply i z
      _ = 0 := by rw [hz, map_zero]
  let Δ : L := d + z
  have hroot : Δ ^ p - Δ = A := by
    have hHroot' : (d + (z : L)) ^ p - (d + (z : L)) - A = 0 := by
      simpa [H, add_comm] using hHroot
    dsimp only [Δ]
    linear_combination hHroot'
  have hzpos' : (0 : WithTop ℤ) < ord L (z : L) := by
    simpa using hzpos
  have hdlt : ord L d < ord L (z : L) := by
    rw [hd]
    exact (WithTop.coe_le_coe.mpr
      (neg_nonpos.mpr (Int.natCast_nonneg t))).trans_lt hzpos'
  have hΔord : ord L Δ = ((-(t : ℤ) : ℤ) : WithTop ℤ) := by
    dsimp only [Δ]
    rw [ord_add_eq_min L (ne_of_lt hdlt), min_eq_left hdlt.le, hd]
  exact ⟨Δ, hroot, hΔord⟩

/-- An exact prime-to-`p` Artin--Schreier coordinate has the paper's lower
order and generates the prime-degree extension. -/
private theorem exact_coordinate_orders_and_generation
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    [Module.Finite E L]
    {p t : ℕ} (hp : p.Prime) (ht : 0 < t)
    (hdegree : Module.finrank E L = p)
    (hram : ramificationIndex E L = p)
    (Δ : L) (a : E)
    (hΔ : ord L Δ = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hprime : ¬ p ∣ t)
    (hroot : Δ ^ p - Δ = algebraMap E L a) :
    ord E a = ((-(t : ℤ) : ℤ) : WithTop ℤ) ∧
      Algebra.adjoin E ({Δ} : Set L) = ⊤ := by
  have hpow : ord L (Δ ^ p) =
      ((-((p * t : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_pow, hΔ, ← WithTop.coe_nsmul]
    congr 1
    push_cast
    ring
  have hpowlt : ord L (Δ ^ p) < ord L Δ := by
    rw [hpow, hΔ]
    apply WithTop.coe_lt_coe.mpr
    have hpone : 1 < p := hp.one_lt
    exact_mod_cast (show -(p * t : ℤ) < -(t : ℤ) by nlinarith)
  have hrootOrd : ord L (Δ ^ p - Δ) =
      ((-((p * t : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
    rw [sub_eq_add_neg, ord_add_eq_min L (by
      rw [ord_neg]
      exact ne_of_lt hpowlt), ord_neg, min_eq_left hpowlt.le, hpow]
  have ha : a ≠ 0 := by
    intro ha
    subst a
    rw [map_zero] at hroot
    have := congrArg (ord L) hroot
    rw [hrootOrd, ord_zero] at this
    exact WithTop.coe_ne_top this
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
    ((ord_ne_top_iff E).2 ha)
  have hbaseOrd :
      ramificationIndex E L • ord E a =
        ((-((p * t : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
    rw [← ord_algebraMap, ← hroot, hrootOrd]
  have hmEq : (p : ℕ) • m = -((p * t : ℕ) : ℤ) := by
    rw [hram, ← hm, ← WithTop.coe_nsmul] at hbaseOrd
    exact WithTop.coe_eq_coe.mp hbaseOrd
  have hmFinal : m = -(t : ℤ) := by
    simp only [nsmul_eq_mul] at hmEq
    push_cast at hmEq
    have hpz : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
    nlinarith
  constructor
  · rw [← hm, hmFinal]
  · have hnotbase : Δ ∉ (⊥ : Subalgebra E L) := by
      intro hmem
      obtain ⟨b, hb⟩ := Algebra.mem_bot.mp hmem
      have hbne : b ≠ 0 := by
        intro hbzero
        subst b
        rw [map_zero] at hb
        have := congrArg (ord L) hb
        rw [ord_zero, hΔ] at this
        exact WithTop.coe_ne_top this.symm
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp
        ((ord_ne_top_iff E).2 hbne)
      have hord := congrArg (ord L) hb
      rw [ord_algebraMap, hram, ← hn, hΔ, ← WithTop.coe_nsmul] at hord
      have hordZ := WithTop.coe_eq_coe.mp hord
      apply hprime
      rw [← Int.natCast_dvd_natCast, ← Int.dvd_neg]
      refine ⟨n, ?_⟩
      simpa [nsmul_eq_mul] using hordZ.symm
    have hprimeDegree : (Module.finrank E L).Prime := by
      rw [hdegree]
      exact hp
    have hsimple := Subalgebra.isSimpleOrder_of_finrank_prime E L hprimeDegree
    rcases hsimple.eq_bot_or_eq_top (Algebra.adjoin E ({Δ} : Set L)) with hbot | htop
    · exfalso
      apply hnotbase
      rw [← hbot]
      exact Algebra.subset_adjoin (Set.mem_singleton Δ)
    · exact htop

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K]
variable [Module.Free F K] [Module.Finite F K] [IsGalois F K]

/-- **Paper Proposition 7.2 (`O:A:prop:AS`).**  The upper cyclic extension
admits an exact Artin--Schreier coordinate of order `-t`; its coefficient has
order `-t` in the lower field, the break is prime to `p`, and the coordinate
generates the whole upper extension. -/
theorem aSCoordinate {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = p)
    (D : OddTotalBreakData (F := F) (K := K) hp hG) :
    let B₂ := D.B₂
    letI : ValuativeRel B₂ := Basic.intermediateFieldValuativeRel B₂
    letI : TopologicalSpace B₂ := Basic.intermediateFieldTopology B₂
    letI : IsNonarchimedeanLocalField B₂ := Basic.intermediateField_localField B₂
    ∃ (Δ : K) (a : B₂),
      Δ ^ p - Δ = algebraMap B₂ K a ∧
      ord K Δ = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ¬ p ∣ D.t ∧
      Algebra.adjoin B₂ ({Δ} : Set K) = ⊤ := by
  dsimp only [OddTotalBreakData.B₂]
  let B₂ := IntermediateField.fixedField D.H₂
  letI : ValuativeRel B₂ := Basic.intermediateFieldValuativeRel B₂
  letI : TopologicalSpace B₂ := Basic.intermediateFieldTopology B₂
  obtain ⟨hLocal, hFreeFB₂, hFiniteFB₂, hFreeB₂K, hFiniteB₂K, hScalar,
      hValFB₂, hValB₂K, _htotal, _hdegreeLower, hdegreeUpper,
      _hcycFB₂, _hcycB₂K⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
  letI : IsNonarchimedeanLocalField B₂ := hLocal
  letI : Module.Free F B₂ := hFreeFB₂
  letI : Module.Finite F B₂ := hFiniteFB₂
  letI : Module.Free B₂ K := hFreeB₂K
  letI : Module.Finite B₂ K := hFiniteB₂K
  letI : IsScalarTower F B₂ K := hScalar
  letI : ValuativeExtension F B₂ := hValFB₂
  letI : ValuativeExtension B₂ K := hValB₂K
  have hresB₂K : residueDegree B₂ K = 1 := by
    have hmul := residueDegree_mul_local (F := F) (K := K) B₂
    rw [hres] at hmul
    exact (mul_eq_one.mp hmul).2
  have hramB₂K : ramificationIndex B₂ K = p := by
    have hdegree := finrank_eq_ramificationIndex_mul_residueDegree B₂ K
    rw [hresB₂K, mul_one, hdegreeUpper] at hdegree
    exact hdegree.symm
  obtain ⟨d, a, hd, hprime, hexact | hmixed⟩ :=
    oddAS_approximate_generator hp hG hres hchar D
  · obtain ⟨_hpzero, hroot⟩ := hexact
    obtain ⟨ha, hgen⟩ := exact_coordinate_orders_and_generation
      B₂ K hp D.t_pos hdegreeUpper hramB₂K d a hd hprime hroot
    exact ⟨d, a, hroot, hd, ha, hprime, hgen⟩
  · obtain ⟨_hpne, V, hV, herror⟩ := hmixed
    have hprimeBound := oddTotal_primeValuationBound hp hG hres D
    rw [hV] at hprimeBound
    have hVbound : (((p * (p - 1) * D.t₂ : ℕ) : ℤ)) ≤ V :=
      WithTop.coe_le_coe.mp hprimeBound
    have hVpt : (((p * D.t : ℕ) : ℤ)) < V := by
      have hnat : p * D.t < p * (p - 1) * D.t₂ := by
        have hp2 : 2 ≤ p - 1 := Nat.le_sub_one_of_lt D.odd_prime
        have hdouble : 2 * D.t ≤ (p - 1) * D.t₂ := by
          exact (Nat.mul_le_mul hp2 D.t_le_t₂)
        have ht : 0 < D.t := D.t_pos
        have hstrict : D.t < 2 * D.t := by omega
        have hupper : D.t < (p - 1) * D.t₂ := hstrict.trans_le hdouble
        simpa [Nat.mul_assoc] using Nat.mul_lt_mul_of_pos_left hupper hp.pos
      exact (show (((p * D.t : ℕ) : ℤ)) <
          ((p * (p - 1) * D.t₂ : ℕ) : ℤ) by
            exact_mod_cast hnat).trans_le hVbound
    obtain ⟨Δ, hroot, hΔ⟩ := lift_artinSchreier_root K hp
      hV hVpt hd herror
    obtain ⟨ha, hgen⟩ := exact_coordinate_orders_and_generation
      B₂ K hp D.t_pos hdegreeUpper hramB₂K Δ a hΔ hprime hroot
    exact ⟨Δ, a, hroot, hΔ, ha, hprime, hgen⟩

end

end LanglandsSecondMainLemma.Odd.Total
