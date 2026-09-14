import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.NormRepresentatives
import LanglandsSecondMainLemma.Odd.Models.Realization

/-!
# Odd / Parameters / Norm Choice

Blueprint: blueprint/tasks/Odd/Parameters/NormChoice.md
Paper: Lemma 8.15 (`O:P:choose`), corrected source lines 3008--3039.

`normChoice` changes the coefficient of the actual norm character by a
depth-`t` unit, preserves its exact order and its full logarithm chart, and
constructs the requested exact norm and its source valuation.

FML's norm representative modulo the critical unit layer supplies the
correction directly. Thus the norm step does not require reconstructing
the order-`p` character quotient. The coefficient estimate is precisely
`-d_F-t-1+t+c ≥ -d_F`, on the whole prescribed ideal. No preservation of
the two minimal models is asserted here.
-/

namespace LanglandsSecondMainLemma.Odd.Parameters

noncomputable section

open LanglandsFirstMainLemma

open private lamprechtAddChar_eq_of_sub_mem from
  LanglandsFirstMainLemma.Lamprecht.Formula

section Coefficient

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The coefficient change in `O:P:choose` preserves the phase on the
entire positive ideal, with its integer conductor exponent. -/
theorem normChoice_coefficient_mul
    {p t c : ℕ} (hchar : residueCharacteristic F = p)
    (ht : 0 < t) (hc : 0 < c)
    (Psi : LocalAddCharData F) (A : Fˣ)
    (hA : ord F (A : F) =
      ((-Psi.conductor - (t : ℤ) - 1 : ℤ) : WithTop ℤ))
    (h : unitFiltration F t) :
    ord F ((A * (h : Fˣ) : Fˣ) : F) =
        ((-Psi.conductor - (t : ℤ) - 1 : ℤ) : WithTop ℤ) ∧
      ((A * (h : Fˣ) : Fˣ) : F) - (A : F) ∈
        lattice F (-Psi.conductor - (c : ℤ)) ∧
      ∀ z : lattice F (c : ℤ),
        Psi.character (((A * (h : Fˣ) : Fˣ) : F) * truncatedLog p (z : F)) =
          Psi.character ((A : F) * truncatedLog p (z : F)) := by
  have hhord : ord F ((h : Fˣ) : F) = 0 :=
    (mem_unitGroup_iff_ord_eq_zero F _).1
      (unitFiltration_le_unitGroup F t h.property)
  have hh : ((h : Fˣ) : F) - 1 ∈ lattice F (t : ℤ) := by
    have hh := (mem_unitFiltration_succ_iff_sub_mem_lattice F (t - 1)
      (h : Fˣ)).1 (by simpa only [Nat.sub_add_cancel ht] using h.property)
    simpa only [Nat.sub_add_cancel ht] using hh
  have hdiff : ((A * (h : Fˣ) : Fˣ) : F) - (A : F) ∈
      lattice F (-Psi.conductor - 1) := by
    have hmul := mul_mem_lattice F ((mem_lattice F).2 hA.ge) hh
    have he : -Psi.conductor - (t : ℤ) - 1 + t = -Psi.conductor - 1 := by omega
    rw [he] at hmul
    simpa only [Units.val_mul, mul_sub, mul_one] using hmul
  refine ⟨by rw [Units.val_mul, ord_mul, hhord, add_zero, hA],
    lattice_antitone F (by omega) hdiff, ?_⟩
  intro z
  apply lamprechtAddChar_eq_of_sub_mem F Psi
  rw [← sub_mul]
  have hP := (truncatedLogOnLattice F p c hchar hc z).property
  exact lattice_antitone F (by omega) (mul_mem_lattice F hdiff hP)

end Coefficient

section NormChoice

variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

/-- Paper `O:P:choose`. The full formula is written on `U_F^c` as
`nu(u) = e_F(A P(1-u))`, equivalently on every `z ∈ 𝔭_F^c` with `u=1-z`.
The additive character has largest trivial ideal `𝔭_F^(-Psi.conductor)`.
The result includes the whole coefficient ambiguity and the exact norm
witness with its valuation. Both field characteristics are allowed.

The nontriviality hypothesis is retained from the paper; FML's stronger
norm representative theorem makes the construction independent of it. -/
theorem normChoice
    {p t : ℕ} (hdegree : Module.finrank F E = p) (hodd : 2 < p)
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
    (hres : residueDegree F E = 1)
    (nu : NormCharacter F E) (_hnu : nu ≠ 1)
    (Psi : LocalAddCharData F) (A gamma : Fˣ)
    (hA : ord F (A : F) =
      ((-Psi.conductor - (t : ℤ) - 1 : ℤ) : WithTop ℤ))
    (hformula : ∀ u : unitFiltration F ((t + 1) ⌈/⌉ p),
      nu.1 u = Psi.character ((A : F) *
        truncatedLog p (1 - ((u : Fˣ) : F)))) :
    ∃ A' : Fˣ,
      A' / A ∈ unitFiltration F t ∧
      ord F (A' : F) = ((-Psi.conductor - (t : ℤ) - 1 : ℤ) : WithTop ℤ) ∧
      (A' : F) - (A : F) ∈
        lattice F (-Psi.conductor - (((t + 1) ⌈/⌉ p : ℕ) : ℤ)) ∧
      (∀ u : unitFiltration F ((t + 1) ⌈/⌉ p),
        nu.1 u = Psi.character ((A' : F) *
          truncatedLog p (1 - ((u : Fˣ) : F)))) ∧
      gamma / A' ∈ (normUnits F E).range ∧
      ∃ w : Eˣ, normUnits F E w = gamma / A' ∧
        ord E (w : E) = ord F ((gamma / A' : Fˣ) : F) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have hchar : residueCharacteristic F = p :=
    (residueCharacteristic_eq_degree_of_positive_isLowerBreak F E
      ht htpos pi hpi hgen).trans hdegree
  have hc : 0 < (t + 1) ⌈/⌉ p := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_pos (by omega) (by omega)
  obtain ⟨w, hw⟩ := exists_norm_representative_mod_break F E
    ht hres pi hpi hgen (gamma / A)
  let h : unitFiltration F t := ⟨(gamma / A) / normUnits F E w, hw⟩
  let A' : Fˣ := A * (h : Fˣ)
  have hnorm : normUnits F E w = gamma / A' := by
    dsimp only [A', h]
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  obtain ⟨horder, hclass, hphase⟩ := normChoice_coefficient_mul F
    hchar htpos hc Psi A hA h
  refine ⟨A', ?_, horder, hclass, ?_, ⟨w, hnorm⟩, w, hnorm, ?_⟩
  · simpa only [A', mul_div_cancel_left] using h.property
  · intro u
    have hz : 1 - ((u : Fˣ) : F) ∈
        lattice F (((t + 1) ⌈/⌉ p : ℕ) : ℤ) := by
      have hu := (mem_unitFiltration_succ_iff_sub_mem_lattice F
        (((t + 1) ⌈/⌉ p) - 1) (u : Fˣ)).1
        (by simpa only [Nat.sub_add_cancel hc] using u.property)
      simpa only [Nat.sub_add_cancel hc, neg_sub] using neg_mem_lattice F hu
    exact (hformula u).trans (hphase ⟨_, hz⟩).symm
  · rw [← hnorm, coe_normUnits, ord_norm, hres, one_nsmul]

end NormChoice

end

end LanglandsSecondMainLemma.Odd.Parameters
