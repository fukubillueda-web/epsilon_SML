import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Ramification.DiamondBreaks
import LanglandsSecondMainLemma.Odd.Total.ASCoordinate

/-!
# Classification / Odd Selection

Paper Lemma 14.1 (`U:odd-selection`).  In a totally ramified odd
prime-square diamond, `diamondBreaks` supplies a distinguished subgroup
line and the break ledger for every other line.  To prove that its first
break is prime to `p`, we construct an `OddTotalBreakData` using that same
distinguished line and apply the exact Artin--Schreier coordinate theorem.

The result retains `OddTotalBreakData`, which contains the two actual fixed
fields used by the odd total-ramification argument, and separately records
the universal statement for every other degree-`p` lower field.
-/

namespace LanglandsSecondMainLemma.Classification

open LanglandsFirstMainLemma

noncomputable section

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K]
variable [Module.Free F K] [Module.Finite F K] [IsGalois F K]

/-- The fixed field of an order-`p` subgroup line has degree `p` over the
base field.  This is the degree assertion needed when rebuilding the
coordinate data with the particular distinguished line supplied by the
universal diamond-break ledger. -/
private theorem fixedField_line_degree
    {F K : Type*} [Field F] [Field K]
    [Algebra F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p) :
    Module.finrank F (IntermediateField.fixedField H) = p := by
  have hcardM : Nat.card (Multiplicative (ZMod p)) = p :=
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod p)
  have hcardG : Nat.card Gal(K/F) = p ^ 2 := by
    let e := Classical.choice hG
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, hcardM, pow_two]
  have htower := Module.finrank_mul_finrank F
    (IntermediateField.fixedField H) K
  rw [IntermediateField.finrank_fixedField_eq_card H, hH,
    ← IsGalois.card_aut_eq_finrank F K, hcardG] at htower
  exact Nat.mul_right_cancel hp.pos (by simpa [pow_two] using htower)

/-- **Selection of fields in wild odd degree** (paper Lemma 14.1,
`U:odd-selection`).

The selected data have an actual degree-`p` field `D.B₁`, lower break
`D.t`, and upper break `D.tPrime`.  For every distinct order-`p` line `H`,
its fixed field has lower break `t₂ = D.t + delta`, the upper extension
has break `D.t`, and `D.tPrime = D.t + p * delta`.  The natural-number
parameter `delta` records its nonnegativity.  Finally, `D.t` is prime to
`p`, as proved by the exact coordinate construction without assuming this
selection theorem. -/
theorem oddSelection {p : ℕ} (hp : p.Prime) (hodd : 2 < p)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = p) :
    ∃ D : Odd.Total.OddTotalBreakData (F := F) (K := K) hp hG,
      ¬ p ∣ D.t ∧
      ∀ (H : Subgroup Gal(K/F)) (hH : Nat.card H = p), H ≠ D.H₁ →
        ∃ t₂ delta : ℕ,
          D.t ≤ t₂ ∧
          t₂ = D.t + delta ∧
          Ramification.IntermediateBreakPair hp hG H hH t₂ D.t ∧
          D.tPrime = D.t + p * delta := by
  let P := Classical.choice
    ((Ramification.diamondBreaks hp hG hchar).1 hres)

  -- Any already constructed pair of distinct lines supplies a line other
  -- than `P.H₀`; no choice of coordinates in the abstract group is needed.
  let D₀ := Classical.choice
    (Odd.Total.oddTotalBreakData_exists hp hodd hG hres hchar)
  obtain ⟨H₂, hH₂, hH₂ne⟩ :
      ∃ H₂ : Subgroup Gal(K/F), Nat.card H₂ = p ∧ H₂ ≠ P.H₀ := by
    by_cases h : D₀.H₁ ≠ P.H₀
    · exact ⟨D₀.H₁, D₀.card_H₁, h⟩
    · refine ⟨D₀.H₂, D₀.card_H₂, ?_⟩
      intro h₂
      apply D₀.lines_ne
      exact (not_ne_iff.mp h).trans h₂.symm

  obtain ⟨t₂, hB₂, _hdiv, ht₂, htPrime⟩ :=
    P.other_breaks H₂ hH₂ hH₂ne
  have hle : P.t ≤ t₂ :=
    (Nat.le_add_right P.t ((P.b - P.t) / p)).trans_eq ht₂.symm
  let D : Odd.Total.OddTotalBreakData (F := F) (K := K) hp hG :=
    { odd_prime := hodd
      H₁ := P.H₀
      H₂ := H₂
      card_H₁ := P.card_H₀
      card_H₂ := hH₂
      lines_ne := hH₂ne.symm
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
      degree_B₁ := fixedField_line_degree hp hG P.H₀ P.card_H₀
      degree_B₂ := fixedField_line_degree hp hG H₂ hH₂ }

  -- Proposition 7.2 returns the required prime-to-`p` assertion for this
  -- exact break data; all of its stronger coordinate conclusions can be
  -- discarded here.
  obtain ⟨_delta, _a, _hroot, _hDelta, _ha, hprime, _hgen⟩ :=
    Odd.Total.aSCoordinate hp hG hres hchar D
  refine ⟨D, hprime, ?_⟩
  intro H hH hne
  have hneP : H ≠ P.H₀ := by
    simpa only [D] using hne
  obtain ⟨s, hpair, _hdvd, hs, hb⟩ := P.other_breaks H hH hneP
  have hts : P.t ≤ s :=
    (Nat.le_add_right P.t ((P.b - P.t) / p)).trans_eq hs.symm
  refine ⟨s, s - P.t, ?_, ?_, ?_, ?_⟩
  · simpa only [D] using hts
  · simpa only [D] using (Nat.add_sub_of_le hts).symm
  · simpa only [D] using hpair
  · simpa only [D] using hb

end

end LanglandsSecondMainLemma.Classification
