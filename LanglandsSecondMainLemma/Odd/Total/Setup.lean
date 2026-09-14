import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.LocalField.Lattices
import LanglandsFirstMainLemma.LocalField.MonogenicUniformizer
import LanglandsFirstMainLemma.LocalField.Valuation
import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Ramification.DiamondBreaks
import LanglandsSecondMainLemma.Local.TraceIdeals

/-!
# Odd / Total / Setup

This is the setup at the start of the paper's section on Artin--Schreier
coordinates and trace--norm estimates.  From the totally ramified branch of
the genuine `C_p × C_p` diamond, we select two distinct subgroup lines.  Their
fixed fields are the paper's actual fields `B₁` and `B₂`.  The distinguished
line has breaks `(t,t')`; the other has breaks `(t₂,t)`, with

`t₂ = t + δ` and `t' = t + pδ`.

The valuation bound is then obtained from the exact trace ideal of `B₂/F`:
the trace of `1` is `p`, and normalization from `F` to the total field
multiplies its order by `p²`.  The statement uses `WithTop ℤ`, so it also
covers equal characteristic, where the order of `p = 0` is infinite.

No divisibility condition on `t` is imposed here; it is a conclusion of the
later Artin--Schreier coordinate construction.
-/

namespace LanglandsSecondMainLemma.Odd.Total

open LanglandsFirstMainLemma

noncomputable section

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K]
variable [Module.Free F K] [Module.Finite F K] [IsGalois F K]

/-- The two coordinate axes give distinct order-`p` lines in any group
identified with `C_p × C_p`. -/
private theorem two_lines {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (e : G ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))) :
    ∃ H J : Subgroup G, Nat.card H = p ∧ Nat.card J = p ∧ H ≠ J := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact (1 < p) := ⟨hp.one_lt⟩
  let M := Multiplicative (ZMod p)
  let X : Subgroup (M × M) := (⊤ : Subgroup M).prod ⊥
  let Y : Subgroup (M × M) := (⊥ : Subgroup M).prod ⊤
  let H := X.comap e.toMonoidHom
  let J := Y.comap e.toMonoidHom
  have hcardM : Nat.card M = p :=
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod p)
  have hcardX : Nat.card X = p := by
    rw [Nat.card_congr (Subgroup.prodEquiv (⊤ : Subgroup M) ⊥).toEquiv,
      Nat.card_prod, Subgroup.card_top, Subgroup.card_bot, hcardM]
    simp
  have hcardY : Nat.card Y = p := by
    rw [Nat.card_congr (Subgroup.prodEquiv (⊥ : Subgroup M) ⊤).toEquiv,
      Nat.card_prod, Subgroup.card_top, Subgroup.card_bot, hcardM]
    simp
  have hXY : X ≠ Y := by
    let a : M := Multiplicative.ofAdd (1 : ZMod p)
    have ha : a ≠ 1 := by
      intro h
      have h' := congrArg Multiplicative.toAdd h
      simp [a] at h'
    intro h
    have hx : (a, 1) ∈ X :=
      ⟨Subgroup.mem_top a, Subgroup.mem_bot.mpr rfl⟩
    rw [h] at hx
    exact ha (Subgroup.mem_bot.mp hx.1)
  have hcardH : Nat.card H = p := by
    change Nat.card (X.comap e.toMonoidHom) = p
    rw [Subgroup.comap_equiv_eq_map_symm']
    exact (Nat.card_congr (e.symm.subgroupMap X).toEquiv).symm.trans hcardX
  have hcardJ : Nat.card J = p := by
    change Nat.card (Y.comap e.toMonoidHom) = p
    rw [Subgroup.comap_equiv_eq_map_symm']
    exact (Nat.card_congr (e.symm.subgroupMap Y).toEquiv).symm.trans hcardY
  have hHJ : H ≠ J := by
    intro h
    apply hXY
    exact Subgroup.comap_injective e.surjective h
  exact ⟨H, J, hcardH, hcardJ, hHJ⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K] [IsGalois F K] in
/-- Cardinality of the actual prime-square Galois group. -/
private theorem galoisCard_eq_prime_sq {p : ℕ}
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))) :
    Nat.card Gal(K/F) = p ^ 2 := by
  let e := Classical.choice hG
  rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  have hp : Nat.card (Multiplicative (ZMod p)) = p :=
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod p)
  rw [hp, pow_two]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] [Module.Free F K] in
/-- The fixed field of an order-`p` line has lower degree `p`. -/
private theorem fixedField_line_finrank {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p) :
    Module.finrank F (IntermediateField.fixedField H) = p := by
  let L := IntermediateField.fixedField H
  have htower := Module.finrank_mul_finrank F L K
  rw [IntermediateField.finrank_fixedField_eq_card H, hH,
    ← IsGalois.card_aut_eq_finrank F K, galoisCard_eq_prime_sq hG] at htower
  exact Nat.mul_right_cancel hp.pos (by simpa [pow_two] using htower)

/-- Residue degrees multiply through an actual intermediate field equipped
with the accepted restricted valuation. -/
private theorem residueDegree_mul (L : IntermediateField F K) :
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

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K] [IsGalois F K] in
/-- There is an order-`p` line distinct from any specified line. -/
private theorem exists_line_ne {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (H₀ : Subgroup Gal(K/F)) :
    ∃ H : Subgroup Gal(K/F), Nat.card H = p ∧ H ≠ H₀ := by
  let e := Classical.choice hG
  obtain ⟨X, Y, hX, hY, hXY⟩ := two_lines hp e
  by_cases h : X ≠ H₀
  · exact ⟨X, hX, h⟩
  · refine ⟨Y, hY, ?_⟩
    intro hY₀
    apply hXY
    exact (not_ne_iff.mp h).trans hY₀.symm

/-- The two actual lower fields and all four cyclic breaks in the totally
ramified odd prime-square diamond.

`H₁` is the distinguished line from the diamond-break theorem and `H₂` is
a genuinely different line.  Thus `B₁ = K ^ H₁` has lower/upper breaks
`(t,tPrime)`, whereas `B₂ = K ^ H₂` has breaks `(t₂,t)`. -/
structure OddTotalBreakData {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))) where
  odd_prime : 2 < p
  H₁ : Subgroup Gal(K/F)
  H₂ : Subgroup Gal(K/F)
  card_H₁ : Nat.card H₁ = p
  card_H₂ : Nat.card H₂ = p
  lines_ne : H₁ ≠ H₂
  t : ℕ
  t₂ : ℕ
  tPrime : ℕ
  delta : ℕ
  t_pos : 0 < t
  t_le_t₂ : t ≤ t₂
  t₂_eq : t₂ = t + delta
  tPrime_eq : tPrime = t + p * delta
  B₁_breaks : Ramification.IntermediateBreakPair hp hG H₁ card_H₁ t tPrime
  B₂_breaks : Ramification.IntermediateBreakPair hp hG H₂ card_H₂ t₂ t
  degree_B₁ : Module.finrank F (IntermediateField.fixedField H₁) = p
  degree_B₂ : Module.finrank F (IntermediateField.fixedField H₂) = p

/-- The paper's actual first lower field `B₁`. -/
def OddTotalBreakData.B₁ {p : ℕ} {hp : p.Prime} {hG}
    (D : OddTotalBreakData (F := F) (K := K) hp hG) : IntermediateField F K :=
  IntermediateField.fixedField D.H₁

/-- The paper's actual second lower field `B₂`. -/
def OddTotalBreakData.B₂ {p : ℕ} {hp : p.Prime} {hG}
    (D : OddTotalBreakData (F := F) (K := K) hp hG) : IntermediateField F K :=
  IntermediateField.fixedField D.H₂

/-- The two selected intermediate fields are genuinely distinct. -/
theorem OddTotalBreakData.B₁_ne_B₂ {p : ℕ} {hp : p.Prime} {hG}
    (D : OddTotalBreakData (F := F) (K := K) hp hG) : D.B₁ ≠ D.B₂ := by
  intro h
  apply D.lines_ne
  rw [← IntermediateField.fixingSubgroup_fixedField D.H₁,
    ← IntermediateField.fixingSubgroup_fixedField D.H₂]
  exact congrArg IntermediateField.fixingSubgroup h

/-- Select the two actual intermediate fields and record the paper's break
relations `t₂ = t + δ` and `t' = t + pδ`.

This is the totally ramified branch of Paper Lemma D.3 specialized to an
odd prime.  It deliberately records no assertion that `p ∤ t`. -/
theorem oddTotalBreakData_exists {p : ℕ} (hp : p.Prime) (hodd : 2 < p)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = p) :
    Nonempty (OddTotalBreakData (F := F) (K := K) hp hG) := by
  let P := Classical.choice ((Ramification.diamondBreaks hp hG hchar).1 hres)
  obtain ⟨H₂, hH₂, hne⟩ := exists_line_ne hp hG P.H₀
  obtain ⟨t₂, hB₂, _hdiv, ht₂, htPrime⟩ := P.other_breaks H₂ hH₂ hne
  have hle : P.t ≤ t₂ :=
    (Nat.le_add_right P.t ((P.b - P.t) / p)).trans_eq ht₂.symm
  exact ⟨
    { odd_prime := hodd
      H₁ := P.H₀
      H₂ := H₂
      card_H₁ := P.card_H₀
      card_H₂ := hH₂
      lines_ne := hne.symm
      t := P.t
      t₂ := t₂
      tPrime := P.b
      delta := t₂ - P.t
      t_pos := P.t_pos
      t_le_t₂ := hle
      t₂_eq := (Nat.add_sub_of_le hle).symm
      tPrime_eq := htPrime
      B₁_breaks := P.distinguished_breaks
      B₂_breaks := hB₂
      degree_B₁ := fixedField_line_finrank hp hG P.H₀ P.card_H₀
      degree_B₂ := fixedField_line_finrank hp hG H₂ hH₂ }⟩

/-- The exact trace-lattice formula supplies FML's lower-bound interface. -/
private theorem traceIdealLowerBound_of_exact
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    [Module.Free E L] [Module.Finite E L] [IsGalois E L]
    (p : ℕ) (D : ℤ)
    (hdegree : Module.finrank E L = p)
    (hres : residueDegree E L = 1)
    (hdiff : differentExponent E L = D) :
    TraceIdealLowerBound E L p D := by
  have hram : ramificationIndex E L = p := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree E L
    rw [hres, mul_one, hdegree] at h
    exact h.symm
  intro q z hz
  have hz' : z ∈ lattice L q := (mem_lattice L).2 hz
  have htrace : trace E L z ∈ Submodule.map
      ((trace E L).restrictScalars (ringOfIntegers E))
      ((lattice L q).restrictScalars (ringOfIntegers E)) :=
    Submodule.mem_map.mpr ⟨z, hz', rfl⟩
  rw [Local.traceIdeal_eq_fml E L hres q, hdiff, hram] at htrace
  exact (mem_lattice E).1 htrace

/-- Elementary floor estimate used after applying the trace formula to `1`. -/
private theorem break_floor_bound (p t : ℕ) (hp : 0 < p) :
    p * (p - 1) * t ≤ p * p * (((p - 1) * (t + 1)) / p) := by
  let d := (p - 1) * (t + 1)
  have hmod : d % p < p := Nat.mod_lt d hp
  have hdecomp : p * (d / p) + d % p = d := Nat.div_add_mod d p
  have hd : d = (p - 1) * t + (p - 1) := by
    simp only [d]
    ring
  have hinner : (p - 1) * t ≤ p * (d / p) := by omega
  simpa only [d, mul_assoc] using Nat.mul_le_mul_left p hinner

/-- The trace of `1` on `B₂/F` gives the paper's prime valuation bound

`p(p-1)t₂ ≤ v_K(p)`.

All orders are normalized in their own fields.  The last passage from `F`
to `K` therefore uses the proved total ramification index `e(K/F)=p²`.
Because the codomain is `WithTop ℤ`, the same declaration covers both
mixed and equal characteristic. -/
theorem oddTotal_primeValuationBound {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1)
    (D : OddTotalBreakData (F := F) (K := K) hp hG) :
    (((p * (p - 1) * D.t₂ : ℕ) : ℤ) : WithTop ℤ) ≤ ord K (p : K) := by
  let B₂ := IntermediateField.fixedField D.H₂
  letI : ValuativeRel B₂ := Basic.intermediateFieldValuativeRel B₂
  letI : TopologicalSpace B₂ := Basic.intermediateFieldTopology B₂
  obtain ⟨hLocal, hFreeFB₂, hFiniteFB₂, hFreeB₂K, hFiniteB₂K, hScalar,
      hValFB₂, hValB₂K, htotal, _hdegree, _hdegreeUpper, hcycFB₂, _hcycB₂K⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
  letI : IsNonarchimedeanLocalField B₂ := hLocal
  letI : Module.Free F B₂ := hFreeFB₂
  letI : Module.Finite F B₂ := hFiniteFB₂
  letI : Module.Free B₂ K := hFreeB₂K
  letI : Module.Finite B₂ K := hFiniteB₂K
  letI : IsScalarTower F B₂ K := hScalar
  letI : ValuativeExtension F B₂ := hValFB₂
  letI : ValuativeExtension B₂ K := hValB₂K
  letI : PrimeCyclicExtension F B₂ :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F B₂ hcycFB₂
  have hbreak : PrimeCyclicExtension.IsLowerBreak F B₂ D.t₂ := by
    simpa only [B₂, Ramification.IntermediateBreakPair] using D.B₂_breaks.1
  have hresFB₂ : residueDegree F B₂ = 1 := by
    have hmul := residueDegree_mul (F := F) (K := K) B₂
    rw [hres] at hmul
    exact (mul_eq_one.mp hmul).1
  obtain ⟨pi, hpi, hgen⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one F B₂ hresFB₂
  have hdiff : differentExponent F B₂ = (p - 1) * (D.t₂ + 1) := by
    rw [differentExponent_eq F B₂ hbreak pi hpi hgen]
    simpa only [B₂] using
      congrArg (fun n : ℕ ↦ (n - 1) * (D.t₂ + 1)) D.degree_B₂
  have htrace : TraceIdealLowerBound F B₂ p
      (((p - 1) * (D.t₂ + 1) : ℕ) : ℤ) :=
    traceIdealLowerBound_of_exact F B₂ p _ D.degree_B₂ hresFB₂
      (by exact_mod_cast hdiff)
  have hbase := degree_natCast_ord_bound F B₂ p
    (((p - 1) * (D.t₂ + 1) : ℕ) : ℤ) hp.pos D.degree_B₂ htrace
  have hramFK : ramificationIndex F K = p * p := by
    have hdegree := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one, htotal] at hdegree
    exact hdegree.symm
  have hscaled := nsmul_le_nsmul_right hbase (p * p)
  rw [show (p : K) = algebraMap F K (p : F) by simp,
    ord_algebraMap, hramFK]
  calc
    (((p * (p - 1) * D.t₂ : ℕ) : ℤ) : WithTop ℤ) ≤
        (((p * p * (((p - 1) * (D.t₂ + 1)) / p) : ℕ) : ℤ) : WithTop ℤ) := by
      exact_mod_cast break_floor_bound p D.t₂ hp.pos
    _ = (p * p) •
        (((((p - 1) * (D.t₂ + 1) : ℕ) : ℤ) / (p : ℤ) : ℤ) : WithTop ℤ) := by
      rw [← WithTop.coe_nsmul]
      norm_num [nsmul_eq_mul]
    _ ≤ (p * p) • ord F (p : F) := hscaled

end

end LanglandsSecondMainLemma.Odd.Total
