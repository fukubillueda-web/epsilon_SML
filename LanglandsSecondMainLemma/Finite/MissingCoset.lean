import Mathlib

/-!
# Cancellation of a missing coset

This is the finite counting argument in Lemma `U:missing-coset` of the paper.
The quadratic refinements take values in `ℂˣ`; their finite sums are taken in
`ℂ` after coercion. A bicharacter is represented by
`AddChar V (AddChar V ℂˣ)`. The hypothesis `hpolar` is the cleared-denominator
form of

`B x y = H (x + y) / (H x * H y)`.

The last hypothesis says explicitly that the character `B w` induced on the
index-two quotient is its nontrivial character: it is one on the image of `p`
and minus one on the missing coset.
-/

namespace LanglandsSecondMainLemma.Finite

noncomputable section

open scoped BigOperators

/-- Cancellation of the missing norm coset (paper Lemma `U:missing-coset`).

Translation by `w` negates the summand off the image of `p`, while preserving
that complement. On the image, every fiber of `p` has the same cardinality as
its two-element kernel. -/
theorem missingCoset
    {V Z : Type*} [AddCommGroup V] [Fintype V]
    [AddCommGroup Z] [Fintype Z]
    (H : V → ℂˣ) (B : AddChar V (AddChar V ℂˣ))
    (Q : Z → ℂˣ) (p : Z →+ V) (w : V)
    (_hH_zero : H 0 = 1)
    (hpolar : ∀ x y, H (x + y) = B x y * H x * H y)
    (hker : Nat.card p.ker = 2)
    (_hindex : p.range.index = 2)
    (hQ : ∀ z, H (p z) = Q z)
    (hw_mem : w ∈ p.range) (hw : H w = 1)
    (hdetect : ∀ x, (x ∈ p.range → B w x = 1) ∧
      (x ∉ p.range → B w x = -1)) :
    (∑ x, (H x : ℂ)) = ((1 : ℂ) / 2) * ∑ z, (Q z : ℂ) := by
  classical
  let C := {x : V // x ∉ p.range}
  let shift : C ≃ C :=
    { toFun := fun x ↦ ⟨w + x, fun h ↦ x.property (by
          simpa using p.range.sub_mem h hw_mem)⟩
      invFun := fun x ↦ ⟨-w + x, fun h ↦ x.property (by
          simpa [add_assoc] using p.range.add_mem hw_mem h)⟩
      left_inv := fun x ↦ by ext; simp
      right_inv := fun x ↦ by ext; simp }

  have hshift (x : C) : (H (shift x) : ℂ) = -(H x : ℂ) := by
    have hu : H (w + x) = -H x := by
      calc
        H (w + x) = B w x * H w * H x := hpolar w x
        _ = -H x := by rw [(hdetect x).2 x.property, hw]; simp
    exact congrArg Units.val hu

  have hcomplement : (∑ x : C, (H x : ℂ)) = 0 := by
    have hneg : (∑ x : C, -(H x : ℂ)) = ∑ x : C, (H x : ℂ) := by
      calc
        (∑ x : C, -(H x : ℂ)) = ∑ x : C, (H (shift x) : ℂ) :=
          Fintype.sum_congr _ _ fun x ↦ (hshift x).symm
        _ = ∑ x : C, (H x : ℂ) := shift.sum_comp fun x ↦ (H x : ℂ)
    have : -(∑ x : C, (H x : ℂ)) = ∑ x : C, (H x : ℂ) := by
      simpa using hneg
    exact neg_eq_self.mp this

  have himage : (∑ x, (H x : ℂ)) = ∑ x : p.range, (H x : ℂ) := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun x : V ↦ x ∈ p.range) (fun x ↦ (H x : ℂ))
    rw [hcomplement, add_zero] at hsplit
    convert hsplit.symm using 1
    apply Finset.sum_congr
    · ext x
      simp
    · intro x hx
      rfl

  have hfiber_card (x : p.range) : Fintype.card {z : Z // p z = x} = 2 := by
    obtain ⟨x, ⟨a, rfl⟩⟩ := x
    let e : {z : Z // p z = p a} ≃ p.ker :=
      { toFun := fun z ↦ ⟨-a + z, by
            change p (-a + z) = 0
            rw [map_add, map_neg, z.property]
            simp⟩
        invFun := fun z ↦ ⟨a + z, by
            rw [map_add, show p z = 0 from z.property]
            simp⟩
        left_inv := fun z ↦ by ext; simp
        right_inv := fun z ↦ by ext; simp }
    calc
      Fintype.card {z : Z // p z = p a} = Nat.card {z : Z // p z = p a} :=
        Nat.card_eq_fintype_card.symm
      _ = Nat.card p.ker := Nat.card_congr e
      _ = 2 := hker

  have hfibers :
      (∑ z, (H (p z) : ℂ)) = 2 * ∑ x : p.range, (H x : ℂ) := by
    let e := Equiv.sigmaSubtypeFiberEquiv p (fun x ↦ x ∈ p.range)
      (fun z ↦ ⟨z, rfl⟩)
    calc
      (∑ z, (H (p z) : ℂ)) = ∑ y : (x : p.range) × {z : Z // p z = x},
          (H (p (e y)) : ℂ) := (e.sum_comp fun z ↦ (H (p z) : ℂ)).symm
      _ = ∑ x : p.range, ∑ _z : {z : Z // p z = x}, (H x : ℂ) := by
        rw [Fintype.sum_sigma]
        apply Fintype.sum_congr
        intro x
        apply Fintype.sum_congr
        intro z
        congr 2
        exact z.property
      _ = ∑ x : p.range, 2 * (H x : ℂ) := by
        apply Fintype.sum_congr
        intro x
        simp [hfiber_card x, two_mul]
      _ = 2 * ∑ x : p.range, (H x : ℂ) := by rw [Finset.mul_sum]

  have hQsum : (∑ z, (Q z : ℂ)) = 2 * ∑ x : p.range, (H x : ℂ) := by
    rw [← hfibers]
    apply Fintype.sum_congr
    intro z
    exact congrArg Units.val (hQ z).symm

  rw [himage, hQsum]
  ring

end

end LanglandsSecondMainLemma.Finite
