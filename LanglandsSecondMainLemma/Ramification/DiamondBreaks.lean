import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Ramification.Inertia
import LanglandsSecondMainLemma.Local.Different
import LanglandsSecondMainLemma.Local.TraceIdeals
import Mathlib.GroupTheory.Sylow

/-!
# Ramification / Diamond Breaks

This file proves Paper Lemma D.3.  It first treats the lower filtration as an actual
decreasing family of subgroups of `Gal(K/F)`.  In the totally ramified wild
`C_p × C_p` case the tame quotient is trivial, so `G₁ = G`; elementary subgroup
cardinality then shows that the filtration has one or two breaks and at most one
intermediate line.  The numerical lower-edge breaks are recovered from Hilbert's
different sum and transitivity of the genuine different ideal.  The final part proves
the stated unramified-base-change comparison directly with uniformizers.

No Herbrand quotient theorem is used.
-/

namespace LanglandsSecondMainLemma.Ramification

open LanglandsFirstMainLemma
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K]
variable [Module.Free F K] [Module.Finite F K] [IsGalois F K]

/-- Residue degrees multiply in the canonical valuation-compatible tower through an
actual intermediate field. -/
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
  [ValuativeExtension F K] [Module.Free F K] [IsGalois F K] in
/-- Every proper nontrivial subgroup of `C_p × C_p` is a line. -/
private theorem card_eq_prime_of_ne_bot_ne_top {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (H : Subgroup Gal(K/F)) (hbot : H ≠ ⊥) (htop : H ≠ ⊤) :
    Nat.card H = p := by
  have hdiv : Nat.card H ∣ p ^ 2 := by
    rw [← galoisCard_eq_prime_sq hG]
    exact Subgroup.card_subgroup_dvd_card H
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow hp).mp hdiv
  have hk0 : k ≠ 0 := by
    intro hk0
    apply hbot
    rw [← Subgroup.card_eq_one, hcard, hk0, pow_zero]
  have hk2 : k ≠ 2 := by
    intro hk2
    apply htop
    apply Subgroup.eq_of_le_of_card_ge le_top
    rw [Subgroup.card_top, hcard, hk2, galoisCard_eq_prime_sq hG]
  have : k = 1 := by omega
  calc
    Nat.card H = p ^ k := hcard
    _ = p := by rw [this, pow_one]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] [Module.Free F K] [IsGalois F K] in
/-- Two distinct lines in `C_p × C_p` meet trivially. -/
private theorem inf_eq_bot_of_distinct_lines {p : ℕ} (hp : p.Prime)
    (H J : Subgroup Gal(K/F)) (hH : Nat.card H = p)
    (hJ : Nat.card J = p) (hne : H ≠ J) : H ⊓ J = ⊥ := by
  letI : Fact (Nat.card H).Prime := ⟨hH.symm ▸ hp⟩
  rcases (J.comap H.subtype).eq_bot_or_eq_top_of_prime_card with hbot | htop
  · apply le_antisymm _ bot_le
    intro x hx
    have hx' : (⟨x, hx.1⟩ : H) ∈ J.comap H.subtype := hx.2
    rw [hbot, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  · exfalso
    apply hne
    apply Subgroup.eq_of_le_of_card_ge
    · intro x hx
      have hx' : (⟨x, hx⟩ : H) ∈ J.comap H.subtype := by
        rw [htop]
        trivial
      exact hx'
    · rw [hH, hJ]

/-- Residue degree one makes the actual residue action trivial, hence `G₀`
is the full Galois group. -/
private theorem lowerRamificationGroup_zero_eq_top_of_residueDegree_one
    (hres : residueDegree F K = 1) :
    lowerRamificationGroup F K 0 = ⊤ := by
  letI : Module.Finite (ResidueField F) (ResidueField K) :=
    Module.Finite.of_finite
  letI : IsGalois (ResidueField F) (ResidueField K) := inferInstance
  let e := residueActionQuotientEquiv (F := F) (K := K)
  have hcard :
      Nat.card (Gal(K/F) ⧸ inertiaSubgroup (F := F) (K := K)) = 1 := by
    rw [Nat.card_congr e.toEquiv, IsGalois.card_aut_eq_finrank,
      ← residueDegree_eq_finrank_residueField, hres]
  have hindex : (inertiaSubgroup (F := F) (K := K)).index = 1 := by
    rw [(inertiaSubgroup (F := F) (K := K)).index_eq_card]
    exact hcard
  rw [← inertiaSubgroup_eq_lowerRamificationGroup_zero]
  exact Subgroup.index_eq_one.mp hindex

/-- In the totally ramified prime-square case with residue characteristic
`p`, the tame quotient has order both prime to `p` and dividing `p²`, hence
is trivial.  Thus wild inertia is the whole Galois group. -/
private theorem lowerRamificationGroup_one_eq_top {p : ℕ} (_hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = p) :
    lowerRamificationGroup F K 1 = ⊤ := by
  have hzero : lowerRamificationGroup F K 0 = ⊤ :=
    lowerRamificationGroup_zero_eq_top_of_residueDegree_one hres
  have hdiv : Nat.card (LowerRamificationGraded F K 0) ∣ p ^ 2 := by
    have h := Subgroup.card_quotient_dvd_card
      (lowerRamificationGroupInside F K (show (0 : ℤ) ≤ 1 by omega))
    change Nat.card (lowerRamificationGroup F K 0 ⧸
      lowerRamificationGroupInside F K (show (0 : ℤ) ≤ 1 by omega)) ∣ p ^ 2
    simpa only [hzero, Subgroup.card_top, galoisCard_eq_prime_sq hG] using h
  have hcop : Nat.Coprime (Nat.card (LowerRamificationGraded F K 0)) p := by
    simpa only [hchar] using
      (tameInertia_cyclic (F := F) (K := K)).2
  have hcard : Nat.card (LowerRamificationGraded F K 0) = 1 :=
    (hcop.pow_right 2).eq_one_of_dvd hdiv
  have hinside :
      lowerRamificationGroupInside F K (show (0 : ℤ) ≤ 1 by omega) = ⊤ := by
    apply Subgroup.index_eq_one.mp
    rw [← lowerRamificationQuotient_natCard F K]
    exact hcard
  apply eq_top_iff.mpr
  intro σ _hσ
  let σ0 : lowerRamificationGroup F K 0 := ⟨σ, hzero.symm ▸ trivial⟩
  have hmem : σ0 ∈ (lowerRamificationGroupInside F K
      (show (0 : ℤ) ≤ 1 by omega)) := by
    rw [hinside]
    trivial
  exact (mem_lowerRamificationGroupInside F K
    (show (0 : ℤ) ≤ 1 by omega) σ0).1 hmem

private structure GroupDiamondProfile (p : ℕ) where
  H₀ : Subgroup Gal(K/F)
  card_H₀ : Nat.card H₀ = p
  t : ℕ
  b : ℕ
  t_pos : 0 < t
  t_le_b : t ≤ b
  filtration : ∀ i : ℕ,
    lowerRamificationGroup F K (i : ℤ) =
      if i ≤ t then ⊤ else if i ≤ b then H₀ else ⊥

/-- Elementary construction of the one-line filtration profile.  The first
index is the least index at which the filtration is not full; in the
two-break case the second is the least index at which its unique line is
trivial. -/
private theorem groupDiamondProfile_exists {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = p) :
    Nonempty (GroupDiamondProfile (F := F) (K := K) p) := by
  classical
  have hzero : lowerRamificationGroup F K 0 = ⊤ :=
    lowerRamificationGroup_zero_eq_top_of_residueDegree_one hres
  have hone : lowerRamificationGroup F K 1 = ⊤ :=
    lowerRamificationGroup_one_eq_top hp hG hres hchar
  have htopnebot : (⊤ : Subgroup Gal(K/F)) ≠ ⊥ := by
    intro h
    have hcard : p ^ 2 = 1 := by
      rw [← galoisCard_eq_prime_sq hG, ← Subgroup.card_top,
        h, Subgroup.card_bot]
    nlinarith [hp.two_le]
  let P : ℕ → Prop := fun n => lowerRamificationGroup F K (n : ℤ) ≠ ⊤
  have hP : ∃ n : ℕ, P n := by
    obtain ⟨j, hj0, hj⟩ := exists_nonnegative_lowerRamificationGroup_eq_bot F K
    refine ⟨j.toNat, ?_⟩
    simpa only [P, Int.toNat_of_nonneg hj0, hj, ne_eq] using htopnebot.symm
  let n : ℕ := Nat.find hP
  have hnP : P n := Nat.find_spec hP
  have hn_two : 2 ≤ n := by
    by_contra hn
    have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with hn0 | hn1
    · exact hnP (by simpa only [hn0, Nat.cast_zero] using hzero)
    · exact hnP (by simpa only [hn1, Nat.cast_one] using hone)
  let t : ℕ := n - 1
  have ht_pos : 0 < t := by simp only [t]; omega
  have ht_succ : t + 1 = n := by simp only [t]; omega
  have ht_full : lowerRamificationGroup F K (t : ℤ) = ⊤ := by
    by_contra ht
    exact Nat.find_min hP (show t < n by simp only [t]; omega) ht
  let Q : Subgroup Gal(K/F) := lowerRamificationGroup F K (n : ℤ)
  have hQtop : Q ≠ ⊤ := hnP
  by_cases hQbot : Q = ⊥
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨H₀, hH₀⟩ := Sylow.exists_subgroup_card_pow_prime p
      (G := Gal(K/F)) (n := 1) (by
        rw [galoisCard_eq_prime_sq hG]
        exact pow_dvd_pow p (by omega))
    have hH₀p : Nat.card H₀ = p := by simpa using hH₀
    refine ⟨⟨H₀, hH₀p, t, t, ht_pos, le_rfl, ?_⟩⟩
    intro i
    split_ifs with hit
    · by_contra hi
      have hin : i < n := by rw [← ht_succ]; omega
      exact Nat.find_min hP hin hi
    · have hni : n ≤ i := by rw [← ht_succ]; omega
      apply le_antisymm _ bot_le
      rw [← hQbot]
      exact lowerRamificationGroup_antitone F K (by exact_mod_cast hni)
  · have hQcard : Nat.card Q = p :=
      card_eq_prime_of_ne_bot_ne_top hp hG Q hQbot hQtop
    let R : ℕ → Prop := fun m => lowerRamificationGroup F K (m : ℤ) = ⊥
    have hR : ∃ m : ℕ, R m := by
      obtain ⟨j, hj0, hj⟩ := exists_nonnegative_lowerRamificationGroup_eq_bot F K
      exact ⟨j.toNat, by simpa only [R, Int.toNat_of_nonneg hj0] using hj⟩
    let m : ℕ := Nat.find hR
    have hm_bot : lowerRamificationGroup F K (m : ℤ) = ⊥ := Nat.find_spec hR
    have hnm : n < m := by
      by_contra hmn
      have hle : m ≤ n := by omega
      have hQle : Q ≤ lowerRamificationGroup F K (m : ℤ) :=
        lowerRamificationGroup_antitone F K (by exact_mod_cast hle)
      rw [hm_bot] at hQle
      exact hQbot (le_bot_iff.mp hQle)
    let b : ℕ := m - 1
    have hb_succ : b + 1 = m := by simp only [b]; omega
    have htb : t ≤ b := by simp only [t, b]; omega
    refine ⟨⟨Q, hQcard, t, b, ht_pos, htb, ?_⟩⟩
    intro i
    split_ifs with hit hib
    · by_contra hi
      have hin : i < n := by rw [← ht_succ]; omega
      exact Nat.find_min hP hin hi
    · have hni : n ≤ i := by rw [← ht_succ]; omega
      have him : i < m := by rw [← hb_succ]; omega
      apply Subgroup.eq_of_le_of_card_ge
      · exact lowerRamificationGroup_antitone F K (by exact_mod_cast hni)
      · have hnebot : lowerRamificationGroup F K (i : ℤ) ≠ ⊥ := by
          intro hi
          exact Nat.find_min hR him hi
        have hdiv : Nat.card (lowerRamificationGroup F K (i : ℤ)) ∣ p := by
          rw [← hQcard]
          exact Subgroup.card_dvd_of_le
            (lowerRamificationGroup_antitone F K (by exact_mod_cast hni))
        have hcard_ne_one :
            Nat.card (lowerRamificationGroup F K (i : ℤ)) ≠ 1 := by
          intro hcard
          exact hnebot (Subgroup.card_eq_one.mp hcard)
        have hcard := ((Nat.dvd_prime hp).mp hdiv).resolve_left hcard_ne_one
        rw [hQcard, hcard]
    · have hmi : m ≤ i := by rw [← hb_succ]; omega
      exact lowerRamificationGroup_eq_bot_of_ge F K hm_bot (by exact_mod_cast hmi)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] [Module.Free F K] in
/-- The fixed field of a line has lower degree `p`. -/
private theorem finrank_fixedField_line {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p) :
    Module.finrank F (IntermediateField.fixedField H) = p := by
  let L := IntermediateField.fixedField H
  have htower := Module.finrank_mul_finrank F L K
  rw [IntermediateField.finrank_fixedField_eq_card H, hH,
    ← IsGalois.card_aut_eq_finrank F K, galoisCard_eq_prime_sq hG] at htower
  exact Nat.mul_right_cancel hp.pos (by simpa [pow_two] using htower)

omit [Module.Free F K] in
/-- Stable Galois proof for the lower edge cut out by a line. -/
private theorem fixedField_line_isGalois {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p) :
    IsGalois F (IntermediateField.fixedField H) := by
  let L := IntermediateField.fixedField H
  letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
  letI : TopologicalSpace L := Basic.intermediateFieldTopology L
  obtain ⟨hLocal, hFreeFL, hFiniteFL, hFreeLK, hFiniteLK, hScalar,
      hValFL, hValLK, _htotal, _hdegFL, _hdegLK, hcycFL, hcycLK⟩ :=
    Basic.intermediateField_tower_compatible hp hG L
      (finrank_fixedField_line hp hG H hH)
  exact hcycFL.1

/-- A line subgroup cuts out two genuine cyclic degree-`p` edges.  This
definition installs only the canonical intermediate-field structures. -/
def IntermediateBreakPair {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p)
    (lowerBreak upperBreak : ℕ) : Prop := by
  let L := IntermediateField.fixedField H
  letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
  letI : TopologicalSpace L := Basic.intermediateFieldTopology L
  letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
  letI : ValuativeExtension F L := Basic.intermediateField_lowerValuativeExtension L
  letI : ValuativeExtension L K := Basic.intermediateField_upperValuativeExtension L
  letI : IsGalois F L := fixedField_line_isGalois hp hG H hH
  exact PrimeCyclicExtension.IsLowerBreak F L lowerBreak ∧
    PrimeCyclicExtension.IsLowerBreak L K upperBreak

/-- Upper-edge half of `IntermediateBreakPair`, used while the lower break
is still being recovered from the different ledger. -/
private def IntermediateUpperBreak {p : ℕ} (_hp : p.Prime)
    (_hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (H : Subgroup Gal(K/F)) (_hH : Nat.card H = p) (upperBreak : ℕ) : Prop := by
  let L := IntermediateField.fixedField H
  letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
  letI : TopologicalSpace L := Basic.intermediateFieldTopology L
  letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
  letI : ValuativeExtension L K := Basic.intermediateField_upperValuativeExtension L
  exact PrimeCyclicExtension.IsLowerBreak L K upperBreak

/-- Exact different calculation along a line tower.  The upper break is
obtained from the top filtration; the lower break is constructed from
`G₀ = G` and then related to it by different transitivity. -/
private theorem exists_lowerBreak_and_different_relation {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1)
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p) (r : ℕ)
    (hupper : IntermediateUpperBreak hp hG H hH r) :
    ∃ s : ℕ, IntermediateBreakPair hp hG H hH s r ∧
      differentExponent F K =
        (p - 1) * (r + 1) + p * ((p - 1) * (s + 1)) := by
  let L := IntermediateField.fixedField H
  letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
  letI : TopologicalSpace L := Basic.intermediateFieldTopology L
  have hdegFL : Module.finrank F L = p := finrank_fixedField_line hp hG H hH
  obtain ⟨hLocal, hFreeFL, hFiniteFL, hFreeLK, hFiniteLK, hScalar,
      hValFL, hValLK, _htotal, _hdegFL, hdegLK, hcycFL, hcycLK⟩ :=
    Basic.intermediateField_tower_compatible hp hG L hdegFL
  letI : IsNonarchimedeanLocalField L := hLocal
  letI : Module.Free F L := hFreeFL
  letI : Module.Finite F L := hFiniteFL
  letI : Module.Free L K := hFreeLK
  letI : Module.Finite L K := hFiniteLK
  letI : IsScalarTower F L K := hScalar
  letI : ValuativeExtension F L := hValFL
  letI : ValuativeExtension L K := hValLK
  letI : IsGalois F L := fixedField_line_isGalois hp hG H hH
  letI : PrimeCyclicExtension F L :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F L hcycFL
  letI : PrimeCyclicExtension L K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension L K hcycLK
  have hresmul := residueDegree_mul (F := F) (K := K) L
  rw [hres] at hresmul
  have hresFL : residueDegree F L = 1 := (mul_eq_one.mp hresmul).1
  have hresLK : residueDegree L K = 1 := (mul_eq_one.mp hresmul).2
  have hzeroFL : lowerRamificationGroup F L 0 = ⊤ :=
    lowerRamificationGroup_zero_eq_top_of_residueDegree_one hresFL
  let s := PrimeCyclicExtension.lowerBreakIndex F L hzeroFL
  have hs : PrimeCyclicExtension.IsLowerBreak F L s :=
    PrimeCyclicExtension.lowerBreakIndex_isLowerBreak F L hzeroFL
  have hr : PrimeCyclicExtension.IsLowerBreak L K r := by
    simpa only [IntermediateUpperBreak] using hupper
  obtain ⟨piFL, hpiFL, hgenFL⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one F L hresFL
  obtain ⟨piLK, hpiLK, hgenLK⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one L K hresLK
  have hdFL : differentExponent F L = (p - 1) * (s + 1) := by
    rw [differentExponent_eq F L hs piFL hpiFL hgenFL, hdegFL]
  have hdLK : differentExponent L K = (p - 1) * (r + 1) := by
    rw [differentExponent_eq L K hr piLK hpiLK hgenLK, hdegLK]
  have heLK : ramificationIndex L K = p := by
    have hdegree := finrank_eq_ramificationIndex_mul_residueDegree L K
    rw [hresLK, mul_one, hdegLK] at hdegree
    exact hdegree.symm
  have htower := Local.differentExponent_tower F L K hresFL hresLK hres
  rw [hdFL, hdLK, heLK] at htower
  refine ⟨s, ?_, htower⟩
  simpa only [IntermediateBreakPair] using And.intro hs hr

omit [Module.Free F K] in
/-- Convert the two boundary intersections supplied by the top filtration
into the actual upper-edge break over a fixed field. -/
private theorem upperBreak_fixedField_of_comap {r : ℕ}
    (H : Subgroup Gal(K/F))
    (hr : (lowerRamificationGroup F K (r : ℤ)).comap H.subtype = ⊤)
    (hr1 : (lowerRamificationGroup F K ((r : ℤ) + 1)).comap H.subtype = ⊥) :
    let L := IntermediateField.fixedField H
    letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
    letI : TopologicalSpace L := Basic.intermediateFieldTopology L
    letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
    letI : ValuativeExtension L K := Basic.intermediateField_upperValuativeExtension L
    PrimeCyclicExtension.IsLowerBreak L K r := by
  let L := IntermediateField.fixedField H
  letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
  letI : TopologicalSpace L := Basic.intermediateFieldTopology L
  letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
  letI : ValuativeExtension L K := Basic.intermediateField_upperValuativeExtension L
  let e := IntermediateField.subgroupEquivAlgEquiv H
  constructor
  · apply (Subgroup.comap_injective (f := e.toMonoidHom) e.surjective)
    rw [lowerRamificationGroup_fixedField H (r : ℤ), hr, Subgroup.comap_top]
  · apply (Subgroup.comap_injective (f := e.toMonoidHom) e.surjective)
    rw [lowerRamificationGroup_fixedField H ((r : ℤ) + 1), hr1]
    exact ((MonoidHom.comap_bot e.toMonoidHom).trans
      (e.toMonoidHom.ker_eq_bot e.injective)).symm

omit [Module.Free F K] [IsGalois F K] in
/-- A nonidentity automorphism in the distinguished line contributes
`b+1` to Hilbert's different sum; every other automorphism contributes
`t+1`. -/
private theorem lowerDifferentSummand_eq_of_profile {p : ℕ}
    (P : GroupDiamondProfile (F := F) (K := K) p)
    (σ : Gal(K/F)) (hσ : σ ≠ 1) :
    lowerDifferentSummand F K σ =
      if σ ∈ P.H₀ then P.b + 1 else P.t + 1 := by
  by_cases hline : σ ∈ P.H₀
  · rw [if_pos hline]
    have hnot : σ ∉ lowerRamificationGroup F K ((P.b + 1 : ℕ) : ℤ) := by
      rw [P.filtration (P.b + 1)]
      rw [if_neg (not_le_of_gt
        (lt_of_le_of_lt P.t_le_b (Nat.lt_succ_self P.b))),
        if_neg (Nat.not_succ_le_self P.b)]
      simpa only [Subgroup.mem_bot] using hσ
    have hle : lowerDifferentSummand F K σ ≤ P.b + 1 := by
      by_contra h
      exact hnot (lowerDifferentSummand_mem_of_lt F K hσ (by omega))
    have hge : P.b + 1 ≤ lowerDifferentSummand F K σ := by
      by_contra h
      have hd : lowerDifferentSummand F K σ ≤ P.b := by omega
      apply lowerDifferentSummand_not_mem F K hσ
      rw [P.filtration (lowerDifferentSummand F K σ)]
      split_ifs with hdt
      · trivial
      · exact hline
    omega
  · rw [if_neg hline]
    have hnot : σ ∉ lowerRamificationGroup F K ((P.t + 1 : ℕ) : ℤ) := by
      rw [P.filtration (P.t + 1)]
      split_ifs with hfirst hsecond
      · omega
      · exact hline
      · simpa only [Subgroup.mem_bot] using hσ
    have hle : lowerDifferentSummand F K σ ≤ P.t + 1 := by
      by_contra h
      exact hnot (lowerDifferentSummand_mem_of_lt F K hσ (by omega))
    have hge : P.t + 1 ≤ lowerDifferentSummand F K σ := by
      by_contra h
      have hd : lowerDifferentSummand F K σ ≤ P.t := by omega
      apply lowerDifferentSummand_not_mem F K hσ
      rw [P.filtration (lowerDifferentSummand F K σ), if_pos hd]
      trivial
    omega

omit [Module.Free F K] [IsGalois F K] in
/-- Hilbert's different sum evaluated from the two-break profile. -/
private theorem differentExponent_eq_of_profile {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (P : GroupDiamondProfile (F := F) (K := K) p) :
    differentExponent F K =
      (p ^ 2 - 1) * (P.t + 1) + (p - 1) * (P.b - P.t) := by
  classical
  let A := (nonidentityGaloisAutomorphisms F K).filter fun σ => σ ∈ P.H₀
  let B := (nonidentityGaloisAutomorphisms F K).filter fun σ => σ ∉ P.H₀
  have hsplit : nonidentityGaloisAutomorphisms F K = A ∪ B := by
    ext σ
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    tauto
  have hdisjoint : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro σ hσA hσB
    simp only [A, Finset.mem_filter] at hσA
    simp only [B, Finset.mem_filter] at hσB
    exact hσB.2 hσA.2
  have hAcard : A.card = p - 1 := by
    let Hfin := (Finset.univ : Finset Gal(K/F)).filter fun σ => σ ∈ P.H₀
    have hHcard : Hfin.card = Nat.card P.H₀ := by
      letI : Fintype P.H₀ := Fintype.ofFinite P.H₀
      simp only [Hfin]
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hA : A = Hfin.erase 1 := by
      ext σ
      simp [A, Hfin, nonidentityGaloisAutomorphisms]
    rw [hA, Finset.card_erase_of_mem, hHcard, P.card_H₀]
    simp [Hfin]
  have hBcard : B.card = p ^ 2 - p := by
    have hcardAll : (nonidentityGaloisAutomorphisms F K).card = p ^ 2 - 1 := by
      rw [nonidentityGaloisAutomorphisms,
        Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ,
        ← Nat.card_eq_fintype_card, galoisCard_eq_prime_sq hG]
    have hcardUnion := Finset.card_union_of_disjoint hdisjoint
    rw [← hsplit, hcardAll, hAcard] at hcardUnion
    have hp_le : p ≤ p ^ 2 := by nlinarith [hp.two_le]
    have hsquare_pos : 1 ≤ p ^ 2 := by nlinarith [hp.two_le]
    have htarget : p ^ 2 - 1 = (p - 1) + (p ^ 2 - p) := by
      apply Nat.cast_injective (R := ℤ)
      simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one,
        Nat.cast_sub hsquare_pos, Nat.cast_sub hp.one_le, Nat.cast_sub hp_le]
      ring
    rw [htarget] at hcardUnion
    exact Nat.add_left_cancel hcardUnion.symm
  unfold differentExponent
  rw [hsplit, Finset.sum_union hdisjoint]
  have hsumA :
      ∑ σ ∈ A, lowerDifferentSummand F K σ = A.card * (P.b + 1) := by
    calc
      _ = ∑ _σ ∈ A, (P.b + 1) := by
        refine Finset.sum_congr rfl (fun σ hσ => ?_)
        rw [lowerDifferentSummand_eq_of_profile P σ]
        · rw [if_pos (Finset.mem_filter.mp hσ).2]
        · exact (mem_nonidentityGaloisAutomorphisms F K).mp
            ((Finset.mem_filter.mp hσ).1)
      _ = A.card * (P.b + 1) := by simp
  have hsumB :
      ∑ σ ∈ B, lowerDifferentSummand F K σ = B.card * (P.t + 1) := by
    calc
      _ = ∑ _σ ∈ B, (P.t + 1) := by
        refine Finset.sum_congr rfl (fun σ hσ => ?_)
        rw [lowerDifferentSummand_eq_of_profile P σ]
        · rw [if_neg (Finset.mem_filter.mp hσ).2]
        · exact (mem_nonidentityGaloisAutomorphisms F K).mp
            ((Finset.mem_filter.mp hσ).1)
      _ = B.card * (P.t + 1) := by simp
  rw [hsumA, hsumB, hAcard, hBcard]
  apply Nat.cast_injective (R := ℤ)
  have hp_le : p ≤ p ^ 2 := by nlinarith [hp.two_le]
  have hsquare_pos : 1 ≤ p ^ 2 := by nlinarith [hp.two_le]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_pow,
    Nat.cast_sub hp.one_le, Nat.cast_sub hp_le,
    Nat.cast_sub hsquare_pos, Nat.cast_sub P.t_le_b]
  ring

/-- The full output in the totally ramified branch of Paper D.3.  `H₀`
is the distinguished line and `fixedField H₀` is the paper's `L₀`.
The profile is stated for every integral lower index, not just at the two
boundary values. -/
structure TotallyRamifiedDiamondBreaks {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))) where
  H₀ : Subgroup Gal(K/F)
  card_H₀ : Nat.card H₀ = p
  t : ℕ
  b : ℕ
  t_pos : 0 < t
  t_le_b : t ≤ b
  filtration : ∀ i : ℕ,
    lowerRamificationGroup F K (i : ℤ) =
      if i ≤ t then ⊤ else if i ≤ b then H₀ else ⊥
  distinguished_breaks :
    IntermediateBreakPair hp hG H₀ card_H₀ t b
  top_different :
    differentExponent F K =
      (p ^ 2 - 1) * (t + 1) + (p - 1) * (b - t)
  other_breaks : ∀ (H : Subgroup Gal(K/F)) (hH : Nat.card H = p), H ≠ H₀ →
    ∃ s : ℕ, IntermediateBreakPair hp hG H hH s t ∧
      p ∣ b - t ∧ s = t + (b - t) / p ∧ b = t + p * (s - t)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K] [IsGalois F K] in
private theorem comap_subtype_eq_bot_of_inf_eq_bot
    (H J : Subgroup Gal(K/F)) (h : H ⊓ J = ⊥) :
    J.comap H.subtype = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  have hx' : (x : Gal(K/F)) ∈ H ⊓ J := ⟨x.prop, hx⟩
  rw [h, Subgroup.mem_bot] at hx'
  exact hx'

private theorem distinguished_break_arithmetic {p t b s : ℕ} (hp : 2 ≤ p)
    (htb : t ≤ b)
    (heq : (p ^ 2 - 1) * (t + 1) + (p - 1) * (b - t) =
      (p - 1) * (b + 1) + p * ((p - 1) * (s + 1))) :
    s = t := by
  have heqZ := congrArg (fun n : ℕ => (n : ℤ)) heq
  have hp1 : 1 ≤ p := by omega
  have hp21 : 1 ≤ p ^ 2 := by nlinarith
  push_cast [Nat.cast_sub hp21, Nat.cast_sub hp1, Nat.cast_sub htb] at heqZ
  have hfacZ : ((p : ℤ) * (p - 1)) * t =
      ((p : ℤ) * (p - 1)) * s := by
    linear_combination heqZ
  have hpZ : (2 : ℤ) ≤ p := by exact_mod_cast hp
  have hcoef : (0 : ℤ) < p * (p - 1) := by nlinarith
  have hts : (t : ℤ) = s :=
    mul_left_cancel₀ (ne_of_gt hcoef) hfacZ
  exact_mod_cast hts.symm

private theorem other_break_linear_arithmetic {p t b s : ℕ} (hp : 2 ≤ p)
    (htb : t ≤ b)
    (heq : (p ^ 2 - 1) * (t + 1) + (p - 1) * (b - t) =
      (p - 1) * (t + 1) + p * ((p - 1) * (s + 1))) :
    p * s = b + (p - 1) * t := by
  have heqZ := congrArg (fun n : ℕ => (n : ℤ)) heq
  have hp1 : 1 ≤ p := by omega
  have hp21 : 1 ≤ p ^ 2 := by nlinarith
  push_cast [Nat.cast_sub hp21, Nat.cast_sub hp1, Nat.cast_sub htb] at heqZ
  have hfacZ : ((p : ℤ) - 1) * (p * s) =
      ((p : ℤ) - 1) * (b + (p - 1) * t) := by
    linear_combination -heqZ
  have hpZ : (2 : ℤ) ≤ p := by exact_mod_cast hp
  have hcoef : (0 : ℤ) < p - 1 := by omega
  have hz : (p : ℤ) * s = b + (p - 1) * t :=
    mul_left_cancel₀ (ne_of_gt hcoef) hfacZ
  exact_mod_cast hz

private theorem lower_break_le_of_linear {p t b s : ℕ} (hp : 0 < p)
    (htb : t ≤ b) (hlinear : p * s = b + (p - 1) * t) :
    t ≤ s := by
  have hpt : p * t = t + (p - 1) * t := by
    calc
      p * t = (1 + (p - 1)) * t := by
        rw [Nat.add_sub_of_le hp]
      _ = t + (p - 1) * t := by ring
  have hm : p * t ≤ p * s := by
    rw [hpt, hlinear]
    exact Nat.add_le_add_right htb _
  exact Nat.le_of_mul_le_mul_left hm hp

private theorem other_break_relation_arithmetic {p t b s : ℕ} (hp : 0 < p)
    (hst : t ≤ s) (hlinear : p * s = b + (p - 1) * t) :
    b = t + p * (s - t) := by
  have hz := congrArg (fun n : ℕ => (n : ℤ)) hlinear
  have hp1 : 1 ≤ p := hp
  push_cast [Nat.cast_sub hp1] at hz
  have hgoal : (b : ℤ) = t + p * ((s : ℤ) - t) := by
    linear_combination -hz
  exact_mod_cast hgoal

/-- Totally ramified branch of Paper D.3. -/
private noncomputable def totallyRamifiedDiamondBreaks {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = p) :
    TotallyRamifiedDiamondBreaks (F := F) (K := K) hp hG := by
  let P := Classical.choice (groupDiamondProfile_exists hp hG hres hchar)
  have hdtop := differentExponent_eq_of_profile hp hG P
  have hupper₀ : IntermediateUpperBreak hp hG P.H₀ P.card_H₀ P.b := by
    have hb :
        (lowerRamificationGroup F K (P.b : ℤ)).comap P.H₀.subtype = ⊤ := by
      rw [P.filtration P.b]
      by_cases hbt : P.b ≤ P.t
      · rw [if_pos hbt, Subgroup.comap_top]
      · rw [if_neg hbt, if_pos le_rfl]
        ext x
        simp
    have hb1 :
        (lowerRamificationGroup F K ((P.b : ℤ) + 1)).comap P.H₀.subtype = ⊥ := by
      have htble := P.t_le_b
      rw [show (P.b : ℤ) + 1 = ((P.b + 1 : ℕ) : ℤ) by omega,
        P.filtration (P.b + 1), if_neg (by omega), if_neg (by omega)]
      exact (MonoidHom.comap_bot P.H₀.subtype).trans
        (P.H₀.subtype.ker_eq_bot P.H₀.subtype_injective)
    simpa only [IntermediateUpperBreak] using
      (upperBreak_fixedField_of_comap P.H₀ hb hb1)
  let hs₀exists := exists_lowerBreak_and_different_relation hp hG hres
    P.H₀ P.card_H₀ P.b hupper₀
  let s₀ := Classical.choose hs₀exists
  have hs₀data := Classical.choose_spec hs₀exists
  have hs₀pair := hs₀data.1
  have hs₀tower := hs₀data.2
  change differentExponent F K =
    (p - 1) * (P.b + 1) + p * ((p - 1) * (s₀ + 1)) at hs₀tower
  have hs₀ : s₀ = P.t := by
    have heq := hdtop.symm.trans hs₀tower
    exact distinguished_break_arithmetic hp.two_le P.t_le_b heq
  have hdistinguished :
      IntermediateBreakPair hp hG P.H₀ P.card_H₀ P.t P.b := by
    rw [← hs₀]
    exact hs₀pair
  refine
    { H₀ := P.H₀
      card_H₀ := P.card_H₀
      t := P.t
      b := P.b
      t_pos := P.t_pos
      t_le_b := P.t_le_b
      filtration := P.filtration
      distinguished_breaks := hdistinguished
      top_different := hdtop
      other_breaks := ?_ }
  intro H hH hne
  have hinter : H ⊓ P.H₀ = ⊥ :=
    inf_eq_bot_of_distinct_lines hp H P.H₀ hH P.card_H₀ hne
  have hcomap : P.H₀.comap H.subtype = ⊥ :=
    comap_subtype_eq_bot_of_inf_eq_bot H P.H₀ hinter
  have hupper : IntermediateUpperBreak hp hG H hH P.t := by
    have ht :
        (lowerRamificationGroup F K (P.t : ℤ)).comap H.subtype = ⊤ := by
      rw [P.filtration P.t, if_pos le_rfl, Subgroup.comap_top]
    have ht1 :
        (lowerRamificationGroup F K ((P.t : ℤ) + 1)).comap H.subtype = ⊥ := by
      rw [show (P.t : ℤ) + 1 = ((P.t + 1 : ℕ) : ℤ) by omega,
        P.filtration (P.t + 1), if_neg (by omega)]
      by_cases htb : P.t + 1 ≤ P.b
      · rw [if_pos htb, hcomap]
      · rw [if_neg htb]
        exact (MonoidHom.comap_bot H.subtype).trans
          (H.subtype.ker_eq_bot H.subtype_injective)
    simpa only [IntermediateUpperBreak] using
      (upperBreak_fixedField_of_comap H ht ht1)
  let hsexists :=
    exists_lowerBreak_and_different_relation hp hG hres H hH P.t hupper
  let s := Classical.choose hsexists
  have hsdata := Classical.choose_spec hsexists
  have hspair := hsdata.1
  have hstower := hsdata.2
  change differentExponent F K =
    (p - 1) * (P.t + 1) + p * ((p - 1) * (s + 1)) at hstower
  have hlinear : p * s = P.b + (p - 1) * P.t := by
    have heq := hdtop.symm.trans hstower
    exact other_break_linear_arithmetic hp.two_le P.t_le_b heq
  have hst : P.t ≤ s :=
    lower_break_le_of_linear hp.pos P.t_le_b hlinear
  have hrel : P.b = P.t + p * (s - P.t) :=
    other_break_relation_arithmetic hp.pos hst hlinear
  have hrelsub : P.b - P.t = p * (s - P.t) := by omega
  have hdvd : p ∣ P.b - P.t := ⟨s - P.t, by simpa [mul_comm] using hrelsub⟩
  have hformula : s = P.t + (P.b - P.t) / p := by
    rw [hrelsub]
    simp [hp.ne_zero]
    exact (Nat.add_sub_of_le hst).symm
  exact ⟨s, hspair, hdvd, hformula, hrel⟩

/-- The genuine pair of equal lower breaks in the inertia-line case of
Paper D.3.  Here `fixedField H` is a ramified lower field and the inertia
fixed field is the unramified lower field. -/
def UnramifiedBaseChangeBreakPair {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hI : Nat.card (inertiaSubgroup (F := F) (K := K)) = p)
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p) (t : ℕ) : Prop := by
  let I := inertiaSubgroup (F := F) (K := K)
  let U := IntermediateField.fixedField I
  let E := IntermediateField.fixedField H
  letI : ValuativeRel U := Basic.intermediateFieldValuativeRel U
  letI : TopologicalSpace U := Basic.intermediateFieldTopology U
  letI : IsNonarchimedeanLocalField U := Basic.intermediateField_localField U
  letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E
  letI : TopologicalSpace E := Basic.intermediateFieldTopology E
  letI : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E
  letI : ValuativeExtension F U := Basic.intermediateField_lowerValuativeExtension U
  letI : ValuativeExtension U K := Basic.intermediateField_upperValuativeExtension U
  letI : ValuativeExtension F E := Basic.intermediateField_lowerValuativeExtension E
  letI : ValuativeExtension E K := Basic.intermediateField_upperValuativeExtension E
  letI : IsGalois F U := fixedField_line_isGalois hp hG I hI
  letI : IsGalois F E := fixedField_line_isGalois hp hG H hH
  exact residueDegree F E = 1 ∧ ramificationIndex E K = 1 ∧
    PrimeCyclicExtension.IsLowerBreak F E t ∧
      PrimeCyclicExtension.IsLowerBreak U K t

/-- The full output when inertia is a line.  Its fixed field is the unique
unramified degree-`p` lower field, and every other line cuts out a totally
ramified lower field whose break is unchanged after base change to that
unramified field. -/
structure InertiaLineDiamondBreaks {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hI : Nat.card (inertiaSubgroup (F := F) (K := K)) = p) where
  unramified_lower :
    let U := IntermediateField.fixedField
      (inertiaSubgroup (F := F) (K := K))
    letI : ValuativeRel U := Basic.intermediateFieldValuativeRel U
    letI : TopologicalSpace U := Basic.intermediateFieldTopology U
    letI : IsNonarchimedeanLocalField U := Basic.intermediateField_localField U
    letI : ValuativeExtension F U :=
      Basic.intermediateField_lowerValuativeExtension U
    ramificationIndex F U = 1 ∧ residueDegree F U = p
  ramified_lower : ∀ (H : Subgroup Gal(K/F)) (hH : Nat.card H = p),
    H ≠ inertiaSubgroup (F := F) (K := K) →
      ∃ t : ℕ, UnramifiedBaseChangeBreakPair hp hG hI H hH t

private theorem inertiaLine_other_break {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hI : Nat.card (inertiaSubgroup (F := F) (K := K)) = p)
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p)
    (hne : H ≠ inertiaSubgroup (F := F) (K := K)) :
    ∃ t : ℕ, UnramifiedBaseChangeBreakPair hp hG hI H hH t := by
  let I := inertiaSubgroup (F := F) (K := K)
  let U := IntermediateField.fixedField I
  let E := IntermediateField.fixedField H
  letI : ValuativeRel U := Basic.intermediateFieldValuativeRel U
  letI : TopologicalSpace U := Basic.intermediateFieldTopology U
  letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E
  letI : TopologicalSpace E := Basic.intermediateFieldTopology E
  have hdegFU : Module.finrank F U = p :=
    finrank_fixedField_line hp hG I hI
  obtain ⟨hLocalU, hFreeFU, hFiniteFU, hFreeUK, hFiniteUK, hScalarU,
      hValFU, hValUK, _htotalU, _hdegFU, hdegUK, hcycFU, hcycUK⟩ :=
    Basic.intermediateField_tower_compatible hp hG U hdegFU
  have hdegFE : Module.finrank F E = p :=
    finrank_fixedField_line hp hG H hH
  obtain ⟨hLocalE, hFreeFE, hFiniteFE, hFreeEK, hFiniteEK, hScalarE,
      hValFE, hValEK, _htotalE, _hdegFE, hdegEK, hcycFE, hcycEK⟩ :=
    Basic.intermediateField_tower_compatible hp hG E hdegFE
  letI : IsNonarchimedeanLocalField U := hLocalU
  letI : Module.Free F U := hFreeFU
  letI : Module.Finite F U := hFiniteFU
  letI : Module.Free U K := hFreeUK
  letI : Module.Finite U K := hFiniteUK
  letI : IsScalarTower F U K := hScalarU
  letI : ValuativeExtension F U := hValFU
  letI : ValuativeExtension U K := hValUK
  letI : IsGalois F U := fixedField_line_isGalois hp hG I hI
  letI : PrimeCyclicExtension F U :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F U hcycFU
  letI : PrimeCyclicExtension U K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension U K hcycUK
  letI : IsNonarchimedeanLocalField E := hLocalE
  letI : Module.Free F E := hFreeFE
  letI : Module.Finite F E := hFiniteFE
  letI : Module.Free E K := hFreeEK
  letI : Module.Finite E K := hFiniteEK
  letI : IsScalarTower F E K := hScalarE
  letI : ValuativeExtension F E := hValFE
  letI : ValuativeExtension E K := hValEK
  letI : IsGalois F E := fixedField_line_isGalois hp hG H hH
  letI : PrimeCyclicExtension F E :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F E hcycFE
  letI : PrimeCyclicExtension E K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension E K hcycEK
  have hUdata := inertiaFixedField_unramified (F := F) (K := K)
  change IsGalois F U ∧ ramificationIndex F U = 1 ∧
    residueDegree F U = residueDegree F K at hUdata
  have hunrFU : ramificationIndex F U = 1 := hUdata.2.1
  have hresFU : residueDegree F U = p := by
    have hdegree := finrank_eq_ramificationIndex_mul_residueDegree F U
    rw [hdegFU, hunrFU, one_mul] at hdegree
    exact hdegree.symm
  have hresFK : residueDegree F K = p := hUdata.2.2.symm.trans hresFU
  have hresUK : residueDegree U K = 1 := by
    have hmul := residueDegree_mul (F := F) (K := K) U
    rw [hresFU, hresFK] at hmul
    exact Nat.mul_left_cancel hp.pos (by simpa using hmul)
  have hinter : H ⊓ I = ⊥ :=
    inf_eq_bot_of_distinct_lines hp H I hH hI hne
  have hcomapI : I.comap H.subtype = ⊥ :=
    comap_subtype_eq_bot_of_inf_eq_bot H I hinter
  have hzeroEK : lowerRamificationGroup E K 0 = ⊥ := by
    let eH := IntermediateField.subgroupEquivAlgEquiv H
    apply (Subgroup.comap_injective (f := eH.toMonoidHom) eH.surjective)
    rw [lowerRamificationGroup_fixedField H 0,
      ← inertiaSubgroup_eq_lowerRamificationGroup_zero, hcomapI]
    exact ((MonoidHom.comap_bot eH.toMonoidHom).trans
      (eH.toMonoidHom.ker_eq_bot eH.injective)).symm
  have hunrEK : ramificationIndex E K = 1 := by
    rcases unramified_or_totallyRamified E K with hunr | hres
    · exact hunr
    · have htop : lowerRamificationGroup E K 0 = ⊤ :=
        lowerRamificationGroup_zero_eq_top_of_residueDegree_one hres
      exact (PrimeCyclicExtension.galoisSubgroup_top_ne_bot E K
        (htop.symm.trans hzeroEK)).elim
  have hresEK : residueDegree E K = p := by
    have hdegree := finrank_eq_ramificationIndex_mul_residueDegree E K
    rw [hdegEK, hunrEK, one_mul] at hdegree
    exact hdegree.symm
  have hresFE : residueDegree F E = 1 := by
    have hmul := residueDegree_mul (F := F) (K := K) E
    rw [hresEK, hresFK] at hmul
    exact Nat.mul_right_cancel hp.pos (by simpa using hmul)
  have hzeroUK : lowerRamificationGroup U K 0 = ⊤ :=
    lowerRamificationGroup_zero_eq_top_of_residueDegree_one hresUK
  let t := PrimeCyclicExtension.lowerBreakIndex U K hzeroUK
  have htUK : PrimeCyclicExtension.IsLowerBreak U K t :=
    PrimeCyclicExtension.lowerBreakIndex_isLowerBreak U K hzeroUK
  have hzeroFE : lowerRamificationGroup F E 0 = ⊤ :=
    lowerRamificationGroup_zero_eq_top_of_residueDegree_one hresFE
  let s := PrimeCyclicExtension.lowerBreakIndex F E hzeroFE
  have hsFE : PrimeCyclicExtension.IsLowerBreak F E s :=
    PrimeCyclicExtension.lowerBreakIndex_isLowerBreak F E hzeroFE
  obtain ⟨piE, hpiE, hgenFE⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one
      F E hresFE
  let piK : ringOfIntegers K :=
    algebraMap (ringOfIntegers E) (ringOfIntegers K) piE
  have hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K) := by
    change (ValuativeRel.valuation K).IsUniformizer
      (algebraMap E K (piE : E))
    rw [← ord_eq_one_iff_isUniformizer K, ord_algebraMap, hunrEK,
      one_nsmul, ord_uniformizer E hpiE]
  have hgenUK : Algebra.adjoin (ringOfIntegers U)
      ({piK} : Set (ringOfIntegers K)) = ⊤ :=
    algebra_adjoin_uniformizer_eq_top_of_residueDegree_eq_one
      U K hresUK piK hpiK
  let tauU : Gal(K/U) := PrimeCyclicExtension.generator U K
  let eI := IntermediateField.subgroupEquivAlgEquiv I
  let tauI : I := eI.symm tauU
  let tauG : Gal(K/F) := tauI.1
  let tauE : Gal(E/F) := tauG.restrictNormal E
  have htauApply (x : K) : tauU x = tauG x := by
    have hx := congrArg (fun phi : Gal(K/U) ↦ phi x)
      (eI.apply_symm_apply tauU)
    exact hx.symm
  have htauE : tauE ≠ 1 := by
    intro htau
    have htauH : tauG ∈ H := by
      rw [← IntermediateField.fixingSubgroup_fixedField H]
      apply (IntermediateField.mem_fixingSubgroup_iff E tauG).2
      exact (AlgEquiv.restrictNormal_eq_one_iff E tauG).1 htau
    have htauInter : tauG ∈ H ⊓ I := ⟨htauH, tauI.prop⟩
    rw [hinter, Subgroup.mem_bot] at htauInter
    have htauIone : tauI = 1 := Subtype.ext htauInter
    apply PrimeCyclicExtension.generator_ne_one U K
    calc
      tauU = eI tauI := (eI.apply_symm_apply tauU).symm
      _ = eI 1 := congrArg eI htauIone
      _ = 1 := map_one eI
  have hordUK := ord_galois_uniformizer_sub_eq_of_isLowerBreak
    U K htUK piK hpiK hgenUK
      (PrimeCyclicExtension.generator_ne_one U K)
  have hordFE := ord_galois_uniformizer_sub_eq_of_isLowerBreak
    F E hsFE piE hpiE hgenFE htauE
  have hdiff : tauU (piK : K) - (piK : K) =
      algebraMap E K (tauE (piE : E) - (piE : E)) := by
    change tauU (algebraMap E K (piE : E)) - algebraMap E K (piE : E) =
      algebraMap E K (tauE (piE : E) - (piE : E))
    calc
      tauU (algebraMap E K (piE : E)) - algebraMap E K (piE : E) =
          tauG (algebraMap E K (piE : E)) - algebraMap E K (piE : E) := by
            rw [htauApply]
      _ = algebraMap E K (tauE (piE : E)) - algebraMap E K (piE : E) := by
            rw [AlgEquiv.restrictNormal_commutes]
      _ = algebraMap E K (tauE (piE : E) - (piE : E)) := by rw [map_sub]
  have hordMap : ord K (algebraMap E K
      (tauE (piE : E) - (piE : E))) =
      ord E (tauE (piE : E) - (piE : E)) := by
    rw [ord_algebraMap, hunrEK, one_nsmul]
  have horders : ((((t + 1 : ℕ) : ℤ) : WithTop ℤ)) =
      ((((s + 1 : ℕ) : ℤ) : WithTop ℤ)) := by
    calc
      ((((t + 1 : ℕ) : ℤ) : WithTop ℤ)) =
          ord K (tauU (piK : K) - (piK : K)) := hordUK.symm
      _ = ord K (algebraMap E K
          (tauE (piE : E) - (piE : E))) := by rw [hdiff]
      _ = ord E (tauE (piE : E) - (piE : E)) := hordMap
      _ = ((((s + 1 : ℕ) : ℤ) : WithTop ℤ)) := hordFE
  have hst : s = t := by
    have : s + 1 = t + 1 := by exact_mod_cast horders.symm
    omega
  rw [hst] at hsFE
  refine ⟨t, ?_⟩
  simpa only [UnramifiedBaseChangeBreakPair] using
    And.intro hresFE (And.intro hunrEK (And.intro hsFE htUK))

omit [Module.Free F K] in
private theorem inertiaLine_unramified_lower {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hI : Nat.card (inertiaSubgroup (F := F) (K := K)) = p) :
    let U := IntermediateField.fixedField
      (inertiaSubgroup (F := F) (K := K))
    letI : ValuativeRel U := Basic.intermediateFieldValuativeRel U
    letI : TopologicalSpace U := Basic.intermediateFieldTopology U
    letI : IsNonarchimedeanLocalField U := Basic.intermediateField_localField U
    letI : ValuativeExtension F U :=
      Basic.intermediateField_lowerValuativeExtension U
    ramificationIndex F U = 1 ∧ residueDegree F U = p := by
  let I := inertiaSubgroup (F := F) (K := K)
  let U := IntermediateField.fixedField I
  letI : ValuativeRel U := Basic.intermediateFieldValuativeRel U
  letI : TopologicalSpace U := Basic.intermediateFieldTopology U
  have hdegFU : Module.finrank F U = p :=
    finrank_fixedField_line hp hG I hI
  obtain ⟨hLocalU, hFreeFU, hFiniteFU, _hFreeUK, _hFiniteUK, _hScalarU,
      hValFU, _hValUK, _htotalU, _hdegFU, _hdegUK, _hcycFU, _hcycUK⟩ :=
    Basic.intermediateField_tower_compatible hp hG U hdegFU
  letI : IsNonarchimedeanLocalField U := hLocalU
  letI : Module.Free F U := hFreeFU
  letI : Module.Finite F U := hFiniteFU
  letI : ValuativeExtension F U := hValFU
  have hUdata := inertiaFixedField_unramified (F := F) (K := K)
  change IsGalois F U ∧ ramificationIndex F U = 1 ∧
    residueDegree F U = residueDegree F K at hUdata
  have hresFU : residueDegree F U = p := by
    have hdegree := finrank_eq_ramificationIndex_mul_residueDegree F U
    rw [hdegFU, hUdata.2.1, one_mul] at hdegree
    exact hdegree.symm
  exact ⟨hUdata.2.1, hresFU⟩

private theorem inertiaLineDiamondBreaks {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hI : Nat.card (inertiaSubgroup (F := F) (K := K)) = p) :
    InertiaLineDiamondBreaks hp hG hI where
  unramified_lower := inertiaLine_unramified_lower hp hG hI
  ramified_lower H hH hne := inertiaLine_other_break hp hG hI H hH hne

/-- **Paper Lemma D.3 (diamond breaks).**  In the totally ramified
prime-square case this gives the complete two-step filtration and the
break ledger on every degree-`p` edge.  If inertia has order `p`, its
fixed field is the unique unramified lower field, while every other lower
field is totally ramified and has the same break as its unramified base
change. -/
theorem diamondBreaks {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hchar : residueCharacteristic F = p) :
    (residueDegree F K = 1 →
      Nonempty (TotallyRamifiedDiamondBreaks hp hG)) ∧
    (∀ hI : Nat.card (inertiaSubgroup (F := F) (K := K)) = p,
      InertiaLineDiamondBreaks hp hG hI) := by
  constructor
  · intro hres
    exact ⟨totallyRamifiedDiamondBreaks hp hG hres hchar⟩
  · intro hI
    exact inertiaLineDiamondBreaks hp hG hI

end

end LanglandsSecondMainLemma.Ramification
