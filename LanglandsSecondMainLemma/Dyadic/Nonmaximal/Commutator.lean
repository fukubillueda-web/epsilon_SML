import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.LowerCharacters

/-!
# Dyadic / Nonmaximal / Commutator

Paper Lemma 13.4, `D:NM:commmodel`, with the aligned origin
`D:NM:origin` and the whole-ideal lower formula `D:NM:lowerformula`.
The rational comparison retains the full trivial ideal of exponent `2r`.
-/

namespace LanglandsSecondMainLemma.Dyadic.Nonmaximal

open LanglandsFirstMainLemma
open LanglandsSecondMainLemma.Characters

noncomputable section

section Depths

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private theorem mul_depth {m n t : ℤ} {u v : F}
    (hu : u ∈ lattice F m) (hv : v ∈ lattice F n) (h : t ≤ m + n) :
    u * v ∈ lattice F t :=
  lattice_antitone F h (mul_mem_lattice F hu hv)

private theorem ord_one_add {u : F} (hu : u ∈ lattice F 1) :
    ord F (1 + u) = 0 := by
  have hpos : (0 : WithTop ℤ) < ord F u :=
    lt_of_lt_of_le (by norm_num) hu
  rw [ord_add_eq_min F (by simpa using ne_of_lt hpos), ord_one,
    min_eq_left hpos.le]

private theorem div_depth {n : ℤ} {u v : F}
    (hu : u ∈ lattice F n) (hv : ord F v = 0) : u / v ∈ lattice F n := by
  exact (div_mem_lattice_iff F v u 0 n hv).2 (by simpa only [zero_add] using hu)

private theorem denominator_change {n : ℤ} {A V H : F}
    (hA : A ∈ lattice F n) (hV : ord F V = 0) (hH : ord F H = 0)
    (hVH : V - H ∈ lattice F n) : A / V - A / H ∈ lattice F (2 * n) := by
  have hV0 : V ≠ 0 := (ord_ne_top_iff F).mp (by rw [hV]; simp)
  have hH0 : H ≠ 0 := (ord_ne_top_iff F).mp (by rw [hH]; simp)
  have heq : A / V - A / H = -(A * (V - H)) / (V * H) := by
    field_simp
    ring
  rw [heq]
  apply div_depth F
  · exact neg_mem_lattice F (mul_depth F hA hVH (by omega))
  · rw [ord_mul, hV, hH, add_zero]

/-- The complete modulus comparison in `D:NM:commmodel`. Both denominators
are units, the lower-chart displacement has depth `r`, and the difference
of the two actual rational phases has depth `2r`, including `e = r = a`. -/
theorem commutator_rational_difference
    (e a r : ℤ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (f g d w : F)
    (hf : ord F f = ((1 - 2 * a : ℤ) : WithTop ℤ))
    (hg : ord F g = ((1 - 2 * r : ℤ) : WithTop ℤ))
    (hd : ord F d = ((r - a : ℤ) : WithTop ℤ))
    (hE : f + d ^ 2 * g ∈ lattice F (1 - a))
    (hw : w ∈ lattice F r) :
    let V := 1 - w - f * w ^ 2
    let Q := 1 - d * w - d ^ 2 * g * w ^ 2
    let B := -(1 + 4 * f) * ((f - d ^ 2 * g) * w ^ 2 + (1 + d) * w)
    let N := (1 + 2 * d - 4 * d ^ 2 * g) * (Q - V)
    ord F V = 0 ∧ ord F Q = 0 ∧ (Q - V) / Q ∈ lattice F r ∧
      B / V - N / Q ∈ lattice F (2 * r) := by
  let E := f + d ^ 2 * g
  let c := f - d ^ 2 * g
  let k := 1 + d
  let U := 1 + 4 * f
  let β := 1 + 2 * d - 4 * d ^ 2 * g
  let V := 1 - w - f * w ^ 2
  let Q := 1 - d * w - d ^ 2 * g * w ^ 2
  let H := 1 + d ^ 2 * g * w ^ 2
  let B := -U * (c * w ^ 2 + k * w)
  let N := β * (Q - V)
  change ord F V = 0 ∧ ord F Q = 0 ∧ (Q - V) / Q ∈ lattice F r ∧
    B / V - N / Q ∈ lattice F (2 * r)
  have h1 : (1 : F) ∈ lattice F 0 := by simp
  have h2 : (2 : F) ∈ lattice F e := by rw [mem_lattice, htwo]
  have h4 : (4 : F) ∈ lattice F (2 * e) := by
    convert mul_depth F h2 h2 (by omega : 2 * e ≤ e + e) using 1
    norm_num
  have h8 : (8 : F) ∈ lattice F (3 * e) := by
    convert mul_depth F h2 h4 (by omega : 3 * e ≤ e + 2 * e) using 1
    norm_num
  have hf' : f ∈ lattice F (1 - 2 * a) := by rw [mem_lattice, hf]
  have hg' : g ∈ lattice F (1 - 2 * r) := by rw [mem_lattice, hg]
  have hd' : d ∈ lattice F (r - a) := by rw [mem_lattice, hd]
  have hd0 := lattice_antitone F (by omega : 0 ≤ r - a) hd'
  have hd2 : d ^ 2 ∈ lattice F (2 * (r - a)) := by
    simpa only [pow_two] using mul_depth F hd' hd' (by omega :
      2 * (r - a) ≤ (r - a) + (r - a))
  have hdg := mul_depth F hd2 hg' (by omega :
    1 - 2 * a ≤ 2 * (r - a) + (1 - 2 * r))
  have hw2 : w ^ 2 ∈ lattice F (2 * r) := by
    simpa only [pow_two] using mul_depth F hw hw (by omega : 2 * r ≤ r + r)
  have hfw := mul_depth F hf' hw2 (by omega : 1 ≤ (1 - 2 * a) + 2 * r)
  have hdgw := mul_depth F hdg hw2 (by omega : 1 ≤ (1 - 2 * a) + 2 * r)
  have hdw := mul_depth F hd0 hw (by omega : r ≤ 0 + r)
  have hw1 := lattice_antitone F (by omega : 1 ≤ r) hw
  have hV : ord F V = 0 := by
    convert ord_one_add F (neg_mem_lattice F (add_mem_lattice F hw1 hfw)) using 1
    congr 1
    dsimp [V]
    ring
  have hQ : ord F Q = 0 := by
    convert ord_one_add F (neg_mem_lattice F (add_mem_lattice F
      (lattice_antitone F (by omega : 1 ≤ r) hdw) hdgw)) using 1
    congr 1
    dsimp [Q]
    ring
  have hH : ord F H = 0 := ord_one_add F hdgw
  have hc : c ∈ lattice F (1 - a) := by
    have ht := mul_depth F h2 hdg (by omega : 1 - a ≤ e + (1 - 2 * a))
    convert sub_mem_lattice F hE ht using 1
    dsimp [c]
    ring
  have hk : k ∈ lattice F 0 := add_mem_lattice F h1 hd0
  have hU : U ∈ lattice F 0 := add_mem_lattice F h1
    (mul_depth F h4 hf' (by omega : 0 ≤ 2 * e + (1 - 2 * a)))
  have hβ : β ∈ lattice F 0 := sub_mem_lattice F
    (add_mem_lattice F h1 (mul_depth F h2 hd0 (by omega : 0 ≤ e + 0)))
    (by simpa only [mul_assoc] using
      mul_depth F h4 hdg (by omega : 0 ≤ 2 * e + (1 - 2 * a)))
  have hcw := mul_depth F hc hw2 (by omega : r ≤ (1 - a) + 2 * r)
  have hQV : Q - V ∈ lattice F r := by
    convert add_mem_lattice F (mul_depth F (sub_mem_lattice F h1 hd0) hw
      (by omega : r ≤ 0 + r)) hcw using 1
    dsimp [Q, V, c]
    ring
  have hB : B ∈ lattice F r := mul_depth F (neg_mem_lattice F hU)
    (add_mem_lattice F hcw (mul_depth F hk hw (by omega : r ≤ 0 + r)))
    (by omega : r ≤ 0 + r)
  have hN : N ∈ lattice F r := mul_depth F hβ hQV (by omega : r ≤ 0 + r)
  have hVH : V - H ∈ lattice F r := by
    convert neg_mem_lattice F (add_mem_lattice F hw
      (mul_depth F hE hw2 (by omega : r ≤ (1 - a) + 2 * r))) using 1
    dsimp [V, H]
    ring
  have hQH : Q - H ∈ lattice F r := by
    have ht := mul_depth F h2 hdgw (by omega : r ≤ e + 1)
    convert neg_mem_lattice F (add_mem_lattice F hdw ht) using 1
    dsimp [Q, H]
    ring
  have hfirst : U + β ∈ lattice F e := by
    convert add_mem_lattice F (mul_depth F h2 hk (by omega : e ≤ e + 0))
      (mul_depth F h4 hc (by omega : e ≤ 2 * e + (1 - a))) using 1
    dsimp [U, β, k, c]
    ring
  have hsecond : U * k + β * (1 - d) ∈ lattice F e := by
    have hpoly : 1 + d - d ^ 2 ∈ lattice F 0 := sub_mem_lattice F hk
      (lattice_antitone F (by omega : 0 ≤ 2 * (r - a)) hd2)
    have ht₁ := mul_depth F h2 hpoly (by omega : e ≤ e + 0)
    have ht₂ := mul_depth F (mul_depth F h4 hE (le_refl _)) hk
      (by omega : e ≤ (2 * e + (1 - a)) + 0)
    have ht₃ := mul_depth F h8 hdg (by omega : e ≤ 3 * e + (1 - 2 * a))
    convert sub_mem_lattice F (add_mem_lattice F ht₁ ht₂) ht₃ using 1
    dsimp [U, β, k]
    ring
  have hBN : B - N ∈ lattice F (2 * r) := by
    have ht₁ := mul_depth F (mul_depth F hfirst hc (le_refl _)) hw2
      (by omega : 2 * r ≤ (e + (1 - a)) + 2 * r)
    have ht₂ := mul_depth F hsecond hw (by omega : 2 * r ≤ e + r)
    convert neg_mem_lattice F (add_mem_lattice F ht₁ ht₂) using 1
    dsimp [B, N, Q, V, c, k, U, β]
    ring
  refine ⟨hV, hQ, div_depth F hQV hQ, ?_⟩
  have hmid : B / H - N / H ∈ lattice F (2 * r) := by
    rw [← sub_div]
    exact div_depth F hBN hH
  convert sub_mem_lattice F
    (add_mem_lattice F (denominator_change F hB hV hH hVH) hmid)
    (denominator_change F hN hQ hH hQH) using 1
  ring

end Depths

section QuadraticAlgebra

variable (F L : Type*) [Field F] [Field L] [Algebra F L]

private theorem quadratic_coordinates (x : L) (f : F)
    (hx : x ^ 2 + x = algebraMap F L f)
    (hxgen : Algebra.adjoin F ({x} : Set L) = ⊤) (v : L) :
    ∃ P Q : F, v = algebraMap F L P + algebraMap F L Q * x := by
  have hv : v ∈ Algebra.adjoin F ({x} : Set L) := hxgen ▸ trivial
  induction hv using Algebra.adjoin_induction with
  | mem u hu =>
      rcases Set.mem_singleton_iff.mp hu with rfl
      exact ⟨0, 1, by simp⟩
  | algebraMap P => exact ⟨P, 0, by simp⟩
  | add u v _ _ hu hv =>
      obtain ⟨P, Q, rfl⟩ := hu
      obtain ⟨R, S, rfl⟩ := hv
      exact ⟨P + R, Q + S, by simp only [map_add]; ring⟩
  | mul u v _ _ hu hv =>
      obtain ⟨P, Q, rfl⟩ := hu
      obtain ⟨R, S, rfl⟩ := hv
      refine ⟨P * R + Q * S * f, P * S + Q * R - Q * S, ?_⟩
      simp only [map_add, map_sub, map_mul]
      linear_combination algebraMap F L Q * algebraMap F L S * hx

private theorem involution_generator (x : L) (f : F)
    (hx : x ^ 2 + x = algebraMap F L f)
    (hxgen : Algebra.adjoin F ({x} : Set L) = ⊤)
    (σ : Gal(L/F)) (hσ : σ ≠ 1) : σ x = -1 - x := by
  have hne : σ x ≠ x := by
    intro h
    apply hσ
    apply AlgEquiv.ext
    have heq : σ.toAlgHom = (1 : Gal(L/F)).toAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top hxgen
      intro u hu
      simpa [Set.mem_singleton_iff.mp hu] using h
    intro v
    exact DFunLike.congr_fun heq v
  have hroot : (σ x) ^ 2 + σ x = algebraMap F L f := by
    simpa using congrArg σ hx
  have hprod : (σ x - x) * (σ x + 1 + x) = 0 := by
    linear_combination hroot - hx
  have h := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)
  linear_combination h

variable [Module.Finite F L] [Algebra.IsQuadraticExtension F L] [IsGalois F L]

private theorem quadratic_trace_norm (σ : Gal(L/F)) (hσ : σ ≠ 1) (v : L) :
    algebraMap F L (trace F L v) = v + σ v ∧
      algebraMap F L (norm F L v) = v * σ v := by
  classical
  have hcard : Fintype.card Gal(L/F) = 2 := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank,
      Algebra.IsQuadraticExtension.finrank_eq_two F L]
  have huniv : ({σ, (1 : Gal(L/F))} : Finset Gal(L/F)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simpa using hσ), Finset.card_singleton, hcard]
  rw [trace_eq_sum_automorphisms, Algebra.norm_eq_prod_automorphisms, ← huniv]
  simp [hσ, add_comm, mul_comm]

private theorem quadratic_norm_affine (x : L) (f : F)
    (hx : x ^ 2 + x = algebraMap F L f)
    (hxgen : Algebra.adjoin F ({x} : Set L) = ⊤) (P Q : F) :
    norm F L (algebraMap F L P + algebraMap F L Q * x) =
      P ^ 2 - P * Q - f * Q ^ 2 := by
  classical
  have hcard : 1 < Fintype.card Gal(L/F) := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank,
      Algebra.IsQuadraticExtension.finrank_eq_two F L]
    decide
  obtain ⟨σ, hσ⟩ := Fintype.exists_ne_of_one_lt_card hcard (1 : Gal(L/F))
  apply (algebraMap F L).injective
  rw [(quadratic_trace_norm F L σ hσ _).2]
  simp only [map_add, map_mul, AlgEquiv.commutes,
    involution_generator F L x f hx hxgen σ hσ, map_sub, map_pow]
  linear_combination -(algebraMap F L Q) ^ 2 * hx

/-- Exact quadratic trace underlying `D:NM:comm-trace`. -/
private theorem quadratic_commutator_trace (x : L) (f c k w : F)
    (hx : x ^ 2 + x = algebraMap F L f)
    (hxgen : Algebra.adjoin F ({x} : Set L) = ⊤)
    (hV : 1 - w - f * w ^ 2 ≠ 0) :
    trace F L ((algebraMap F L c - algebraMap F L k * x) *
      (algebraMap F L w * (1 + 2 * x) / (1 + algebraMap F L w * x))) =
      -(1 + 4 * f) * (c * w ^ 2 + k * w) / (1 - w - f * w ^ 2) := by
  classical
  have hcard : 1 < Fintype.card Gal(L/F) := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank,
      Algebra.IsQuadraticExtension.finrank_eq_two F L]
    decide
  obtain ⟨σ, hσ⟩ := Fintype.exists_ne_of_one_lt_card hcard (1 : Gal(L/F))
  have hxσ := involution_generator F L x f hx hxgen σ hσ
  have hprod : (1 + algebraMap F L w * x) *
      (1 - algebraMap F L w - algebraMap F L w * x) =
      algebraMap F L (1 - w - f * w ^ 2) := by
    simp only [map_sub, map_one, map_mul, map_pow]
    linear_combination -(algebraMap F L w) ^ 2 * hx
  have hprod0 : (1 + algebraMap F L w * x) *
      (1 - algebraMap F L w - algebraMap F L w * x) ≠ 0 := by
    rw [hprod]
    exact (map_ne_zero (algebraMap F L)).mpr hV
  have hleft := (mul_ne_zero_iff.mp hprod0).1
  have hright := (mul_ne_zero_iff.mp hprod0).2
  apply (algebraMap F L).injective
  rw [(quadratic_trace_norm F L σ hσ _).1]
  simp only [map_mul, map_sub, map_add, map_div₀, map_one, map_ofNat,
    AlgEquiv.commutes, hxσ]
  have hden : 1 + algebraMap F L w * (-1 - x) =
      1 - algebraMap F L w - algebraMap F L w * x := by ring
  simp only [map_sub, map_one, map_mul, map_pow] at hprod
  simp only [map_neg, map_add, map_mul, map_one, map_ofNat, map_pow]
  rw [hden, ← hprod]
  rw [← mul_div_assoc, ← mul_div_assoc, div_add_div _ _ hleft hright]
  congr 1
  linear_combination
    (-4 * algebraMap F L w * (algebraMap F L c * algebraMap F L w +
      algebraMap F L k)) * hx

end QuadraticAlgebra

section ShallowCoordinates

variable (F L : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra F L] [ValuativeExtension F L]

/-- Every shallow quotient has a normalized coordinate, without an extra
valuation-parity hypothesis or an assumed choice of norm representative. -/
private theorem shallow_coordinates
    (e a r : ℤ) (_ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (hram : ramificationIndex F L = 2)
    (x : L) (f : F) (hx : x ^ 2 + x = algebraMap F L f)
    (hxgen : Algebra.adjoin F ({x} : Set L) = ⊤)
    (hxord : ord L x = ((1 - 2 * a : ℤ) : WithTop ℤ))
    (σ : Gal(L/F)) (hσ : σ ≠ 1) (v : Lˣ)
    (hv : 1 - σ (v : L) / (v : L) ∈ lattice L (2 * r)) :
    ∃ P : Fˣ, ∃ w ∈ lattice F r,
      (v : L) = algebraMap F L (P : F) * (1 + algebraMap F L w * x) := by
  have htwoL : ord L (2 : L) = ((2 * e : ℤ) : WithTop ℤ) := by
    rw [← map_ofNat (algebraMap F L) 2, ord_algebraMap, hram, htwo,
      ← WithTop.coe_nsmul]
    congr 1
  have hu : ord L (1 + 2 * x) = 0 := by
    apply ord_one_add L
    rw [mem_lattice, ord_mul, htwoL, hxord, ← WithTop.coe_add]
    exact_mod_cast (show (1 : ℤ) ≤ 2 * e + (1 - 2 * a) by omega)
  obtain ⟨P, Q, hcoord⟩ := quadratic_coordinates F L x f hx hxgen (v : L)
  by_cases hQ : Q = 0
  · have hP : P ≠ 0 := by
      intro hP
      simp [hQ, hP] at hcoord
    refine ⟨Units.mk0 P hP, 0, (lattice F r).zero_mem, ?_⟩
    simpa [hQ] using hcoord
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).2 hQ)
  have hqL : ord L (algebraMap F L Q) = ((2 * q : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hram, ← hq, ← WithTop.coe_nsmul]
    congr 1
  let n := unitOrder L v
  have hn : ord L (v : L) = (n : WithTop ℤ) := ord_coe_eq_unitOrder L v
  have hdisp : 1 - σ (v : L) / (v : L) =
      algebraMap F L Q * (1 + 2 * x) / (v : L) := by
    apply (eq_div_iff (Units.ne_zero v)).mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ (Units.ne_zero v)]
    rw [hcoord]
    simp only [map_add, map_mul, AlgEquiv.commutes,
      involution_generator F L x f hx hxgen σ hσ]
    ring
  have hbound : 2 * r ≤ 2 * q - n := by
    rw [hdisp, mem_lattice, ord_div, ord_mul, hqL, hu, hn, add_zero,
      ← WithTop.LinearOrderedAddCommGroup.coe_sub] at hv
    exact WithTop.coe_le_coe.mp hv
  have hQx : ord L (algebraMap F L Q * x) =
      ((2 * q + 1 - 2 * a : ℤ) : WithTop ℤ) := by
    rw [ord_mul, hqL, hxord, ← WithTop.coe_add]
    congr 1
    omega
  have hlt : ord L (v : L) < ord L (algebraMap F L Q * x) := by
    rw [hn, hQx]
    exact_mod_cast (show n < 2 * q + 1 - 2 * a by omega)
  have hPord : ord L (algebraMap F L P) = (n : WithTop ℤ) := by
    have heq : algebraMap F L P = (v : L) + -(algebraMap F L Q * x) := by
      rw [hcoord]
      ring
    rw [heq, ord_add_eq_min L (by simpa only [ord_neg] using ne_of_lt hlt),
      ord_neg, min_eq_left hlt.le, hn]
  have hP : P ≠ 0 := by
    intro h
    simp [h] at hPord
  let p := unitOrder F (Units.mk0 P hP)
  have hp : ord F P = (p : WithTop ℤ) := ord_coe_eq_unitOrder F (Units.mk0 P hP)
  have hnp : 2 * p = n := by
    rw [ord_algebraMap, hram, hp, ← WithTop.coe_nsmul] at hPord
    exact_mod_cast hPord
  refine ⟨Units.mk0 P hP, Q / P, ?_, ?_⟩
  · rw [mem_lattice, ord_div, ← hq, hp,
      ← WithTop.LinearOrderedAddCommGroup.coe_sub]
    exact_mod_cast (show r ≤ q - p by omega)
  · simp only [Units.val_mk0, map_div₀]
    rw [hcoord]
    field_simp [(map_ne_zero (algebraMap F L)).mpr hP]

end ShallowCoordinates

section Evaluation

variable (F L M : Type*)
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra F L] [ValuativeExtension F L] [Module.Finite F L]
  [Algebra F M] [ValuativeExtension F M] [Module.Finite F M]
  [Algebra.IsQuadraticExtension F L] [IsGalois F L]
  [Algebra.IsQuadraticExtension F M] [IsGalois F M]

private theorem commutator_evaluation
    (e a r : ℤ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (hram : ramificationIndex F L = 2)
    (x : L) (y : M) (f g d : F)
    (hx : x ^ 2 + x = algebraMap F L f)
    (hy : y ^ 2 + y = algebraMap F M g)
    (hxgen : Algebra.adjoin F ({x} : Set L) = ⊤)
    (hygen : Algebra.adjoin F ({y} : Set M) = ⊤)
    (hxord : ord L x = ((1 - 2 * a : ℤ) : WithTop ℤ))
    (hf : ord F f = ((1 - 2 * a : ℤ) : WithTop ℤ))
    (hg : ord F g = ((1 - 2 * r : ℤ) : WithTop ℤ))
    (hd : ord F d = ((r - a : ℤ) : WithTop ℤ))
    (hE : f + d ^ 2 * g ∈ lattice F (1 - a))
    (ω : NormCharacter F M) (Ψ : ContinuousAddChar F)
    (hΨ : IsAdditiveConductor F Ψ (-2 * r))
    (hlower : ∀ u ∈ lattice F r, ∀ B : Fˣ, (B : F) = 1 - u →
      ω.1 B = Ψ ((1 + 2 * d - 4 * d ^ 2 * g) * u))
    (σ : Gal(L/F)) (hσ : σ ≠ 1) (v : Lˣ)
    (hv : 1 - σ (v : L) / (v : L) ∈ lattice L (2 * r)) :
    Ψ (trace F L ((algebraMap F L (f - d ^ 2 * g) -
      algebraMap F L (1 + d) * x) * (1 - σ (v : L) / (v : L)))) =
      ω.1 (normUnits F L v) := by
  obtain ⟨P, w, hw, hcoord⟩ := shallow_coordinates F L e a r ha har hre htwo
    hram x f hx hxgen hxord σ hσ v hv
  let V := 1 - w - f * w ^ 2
  let Q := 1 - d * w - d ^ 2 * g * w ^ 2
  let B := -(1 + 4 * f) * ((f - d ^ 2 * g) * w ^ 2 + (1 + d) * w)
  let N := (1 + 2 * d - 4 * d ^ 2 * g) * (Q - V)
  obtain ⟨hV, hQ, hu, hdiff⟩ :=
    commutator_rational_difference F e a r ha har hre htwo f g d w hf hg hd hE hw
  change ord F V = 0 at hV
  change ord F Q = 0 at hQ
  change (Q - V) / Q ∈ lattice F r at hu
  change B / V - N / Q ∈ lattice F (2 * r) at hdiff
  have hV0 : V ≠ 0 := (ord_ne_top_iff F).mp (by rw [hV]; simp)
  have hQ0 : Q ≠ 0 := (ord_ne_top_iff F).mp (by rw [hQ]; simp)
  let Vunit := Units.mk0 V hV0
  let Qunit := Units.mk0 Q hQ0
  have hnormV : norm F L (1 + algebraMap F L w * x) = V := by
    simpa only [map_one, one_pow, one_mul] using
      quadratic_norm_affine F L x f hx hxgen 1 w
  have hnormQ : norm F M (1 + algebraMap F M (d * w) * y) = Q := by
    convert quadratic_norm_affine F M y g hy hygen 1 (d * w) using 1
    · simp only [map_one]
    · dsimp [Q]
      ring
  have hQarg : 1 + algebraMap F M (d * w) * y ≠ 0 := by
    intro h
    rw [h] at hnormQ
    exact hQ0 (by simpa using hnormQ.symm)
  let Z := Units.mk0 (1 + algebraMap F M (d * w) * y) hQarg
  have hQnorm : normUnits F M Z = Qunit := Units.ext hnormQ
  have hQchar : ω.1 Qunit = 1 := by
    rw [← hQnorm]
    exact ω.eq_one_on_normRange F M _ ⟨Z, rfl⟩
  have hVchar : ω.1 Vunit = Ψ (N / Q) := by
    have heq : ((Vunit / Qunit : Fˣ) : F) = 1 - (Q - V) / Q := by
      simp only [Units.val_div_eq_div_val, Units.val_mk0, Vunit, Qunit]
      field_simp
      ring
    have hh := hlower ((Q - V) / Q) hu (Vunit / Qunit) heq
    simpa only [map_div, hQchar, div_one, N, mul_div_assoc] using hh
  let C : Mˣ := Units.map (algebraMap F M).toMonoidHom P
  have hnormv : normUnits F L v = normUnits F M C * Vunit := by
    apply Units.ext
    change norm F L (v : L) = norm F M (algebraMap F M (P : F)) * V
    rw [hcoord, map_mul, LanglandsFirstMainLemma.norm_algebraMap,
      LanglandsFirstMainLemma.norm_algebraMap,
      Algebra.IsQuadraticExtension.finrank_eq_two F L,
      Algebra.IsQuadraticExtension.finrank_eq_two F M, hnormV]
  have hcharv : ω.1 (normUnits F L v) = Ψ (N / Q) := by
    rw [hnormv, map_mul, ω.eq_one_on_normRange F M _ ⟨C, rfl⟩, one_mul, hVchar]
  have hleft : 1 + algebraMap F L w * x ≠ 0 := by
    intro h
    rw [h] at hnormV
    exact hV0 (by simpa using hnormV.symm)
  have hquot : 1 - σ (v : L) / (v : L) =
      algebraMap F L w * (1 + 2 * x) / (1 + algebraMap F L w * x) := by
    rw [hcoord]
    simp only [map_mul, map_add, map_one, AlgEquiv.commutes,
      involution_generator F L x f hx hxgen σ hσ]
    rw [mul_div_mul_left _ _ (map_ne_zero (algebraMap F L) |>.mpr (Units.ne_zero P))]
    field_simp
    ring
  rw [hquot, quadratic_commutator_trace F L x f (f - d ^ 2 * g) (1 + d) w
    hx hxgen hV0, hcharv]
  apply div_eq_one.mp
  exact (Ψ.toAddChar.map_sub_eq_div (B / V) (N / Q)).symm.trans
    (hΨ.trivial _ (by simpa only [neg_mul, neg_neg] using hdiff))

end Evaluation

section ShallowCharacter

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

private theorem shallow_displacement (r : ℕ) (hr : 1 ≤ r)
    (u : Lˣ) (hu : u ∈ unitFiltration L (2 * r)) :
    1 - (u : L) ∈ lattice L (2 * (r : ℤ)) := by
  have hn : 2 * r - 1 + 1 = 2 * r := by omega
  have hh := (mem_unitFiltration_succ_iff_sub_mem_lattice L (2 * r - 1) u).mp
    (by simpa only [hn] using hu)
  have hh' : (u : L) - 1 ∈ lattice L (2 * (r : ℤ)) := by
    simpa only [hn, Nat.cast_mul, Nat.cast_ofNat] using hh
  simpa only [neg_sub] using neg_mem_lattice L hh'

/-- The actual continuous group character `R₁` of `D:NM:Rcharts` on
`U^(2r)`. Multiplicativity follows from the full product-error depth;
it is part of the construction, not additional data. -/
def firstShallowCharacter (a r : ℕ) (hr : 1 ≤ r)
    (Ψ : ContinuousAddChar L)
    (hΨ : IsAdditiveConductor L Ψ (-(4 * (r : ℤ) - 2 * (a : ℤ))))
    (A : L) (hA : ord L A = ((1 - 2 * (a : ℤ) : ℤ) : WithTop ℤ)) :
    ContinuousMonoidHom (unitFiltration L (2 * r)) ℂˣ := by
  let R : unitFiltration L (2 * r) →* ℂˣ :=
    { toFun := fun u => Ψ (A * (1 - ((u : Lˣ) : L)))
      map_one' := by simp
      map_mul' := by
        intro u v
        change Ψ (A * (1 - (((u : Lˣ) : L) * ((v : Lˣ) : L)))) =
          Ψ (A * (1 - ((u : Lˣ) : L))) * Ψ (A * (1 - ((v : Lˣ) : L)))
        rw [← Ψ.map_add_eq_mul]
        apply div_eq_one.mp
        apply (Ψ.toAddChar.map_sub_eq_div _ _).symm.trans
        apply hΨ.trivial
        have he := mul_depth L (show A ∈ lattice L (1 - 2 * (a : ℤ)) by
          rw [mem_lattice, hA])
          (mul_mem_lattice L (shallow_displacement L r hr u u.property)
            (shallow_displacement L r hr v v.property))
          (by omega : 4 * (r : ℤ) - 2 * (a : ℤ) ≤
            (1 - 2 * (a : ℤ)) + (2 * (r : ℤ) + 2 * (r : ℤ)))
        simp only [neg_neg]
        convert neg_mem_lattice L he using 1
        ring }
  refine ⟨R, ?_⟩
  exact Ψ.continuous.comp (continuous_const.mul
    (continuous_const.sub (Units.continuous_val.comp continuous_subtype_val)))

@[simp]
theorem firstShallowCharacter_apply (a r : ℕ) (hr : 1 ≤ r)
    (Ψ : ContinuousAddChar L)
    (hΨ : IsAdditiveConductor L Ψ (-(4 * (r : ℤ) - 2 * (a : ℤ))))
    (A : L) (hA : ord L A = ((1 - 2 * (a : ℤ) : ℤ) : WithTop ℤ))
    (u : unitFiltration L (2 * r)) :
    firstShallowCharacter L a r hr Ψ hΨ A hA u =
      Ψ (A * (1 - ((u : Lˣ) : L))) := rfl

end ShallowCharacter

section ActualFields

variable (F K : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [Module.Finite F K]
  (L₁ L₂ L₃ : IntermediateField F K)
  [ValuativeRel L₁] [TopologicalSpace L₁] [IsNonarchimedeanLocalField L₁]
  [ValuativeRel L₂] [TopologicalSpace L₂] [IsNonarchimedeanLocalField L₂]
  [ValuativeRel L₃] [TopologicalSpace L₃] [IsNonarchimedeanLocalField L₃]
  [ValuativeExtension F L₁] [ValuativeExtension L₁ K]
  [ValuativeExtension F L₂] [ValuativeExtension L₂ K]
  [ValuativeExtension F L₃] [ValuativeExtension L₃ K]
  [Module.Finite F L₁] [Module.Finite L₁ K]
  [Module.Finite F L₂] [Module.Finite L₂ K]
  [Module.Finite F L₃] [Module.Finite L₃ K]
  [Algebra.IsQuadraticExtension F L₁] [PrimeCyclicExtension F L₁]
  [Algebra.IsQuadraticExtension F L₂] [PrimeCyclicExtension F L₂]
  [Algebra.IsQuadraticExtension F L₃]

/-- **The shallow commutator is evaluated, not assumed** (Paper Lemma 13.4,
`D:NM:commmodel`).

The origin `O` is constructed by `dyadicNonmaximal_origin_data` and the
lower data `D` by `lowerCharacters`. The coefficient of the continuous
group character on the left is the actual upper norm `N₁Y`. The right
side is the actual lower norm pullback `ν₁ = ω₂ ∘ n₁`.

Every `v : L₁ˣ` whose conjugate quotient lies in `U^(2r)` is covered.
No coordinate normalization, norm representative, commutator identity,
or additional character formula is a hypothesis. All ideal calculations
use integer exponents and include `e = r = a`. -/
theorem commutator
    (e a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (hres₁ : residueDegree F L₁ = 1)
    (x : L₁) (y : L₂) (z : L₃) (f g d : F)
    (O : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂) (ω₃ : NormCharacter F L₃)
    (ψ : LocalAddCharData F) (α : Fˣ)
    (D : LowerCharacterData F L₁ L₂ L₃ a r ω₁ ω₂ ω₃ ψ α
      (normUnits F L₁ (Units.mk0 (trace L₁ K O.Y) O.upperTraces_ne_zero.1))
      (normUnits F L₂ (Units.mk0 (trace L₂ K O.Y) O.upperTraces_ne_zero.2.1))
      (normUnits F L₃ (Units.mk0 (trace L₃ K O.Y) O.upperTraces_ne_zero.2.2)))
    (σ : Gal(L₁/F)) (hσ : σ ≠ 1) (v : L₁ˣ)
    (hv : Units.map σ.toMonoidHom v / v ∈ unitFiltration L₁ (2 * r)) :
    firstShallowCharacter L₁ a r (ha.trans har)
      (tracePullbackAddChar F L₁ (scaleAddCharData F ψ α).character)
      D.first_conductor (norm L₁ K O.Y) O.upperNorm₁_order
      ⟨Units.map σ.toMonoidHom v / v, hv⟩ = ω₂.1 (normUnits F L₁ v) := by
  let Ψ := (scaleAddCharData F ψ α).character
  have hΨ : IsAdditiveConductor F Ψ (-2 * (r : ℤ)) := by
    rw [← D.base_conductor]
    exact (scaleAddCharData F ψ α).isConductor
  have hlower : ∀ u ∈ lattice F (r : ℤ), ∀ B : Fˣ, (B : F) = 1 - u →
      ω₂.1 B = Ψ ((1 + 2 * d - 4 * d ^ 2 * g) * u) := by
    intro u hu B hB
    simpa only [coe_normUnits, Units.val_mk0, O.lowerNormTrace₂] using
      D.second_formula u hu B hB
  have hram : ramificationIndex F L₁ = 2 := by
    have hh := finrank_eq_ramificationIndex_mul_residueDegree F L₁
    rw [Algebra.IsQuadraticExtension.finrank_eq_two F L₁, hres₁, mul_one] at hh
    exact hh.symm
  have hdisp : 1 - σ (v : L₁) / (v : L₁) ∈ lattice L₁ (2 * (r : ℤ)) := by
    simpa using shallow_displacement L₁ r (ha.trans har) _ hv
  have hE : f + d ^ 2 * g ∈ lattice F (1 - (a : ℤ)) :=
    O.E_eq ▸ O.E_lattice
  have heval := commutator_evaluation F L₁ L₂ (e : ℤ) (a : ℤ) (r : ℤ)
    (by exact_mod_cast ha) (by exact_mod_cast har) (by exact_mod_cast hre)
    (by exact_mod_cast htwo) hram x y f g d O.x_polynomial O.y_polynomial
    O.x_generates O.y_generates O.x_order O.f_order O.g_order O.d_order hE
    ω₂ Ψ hΨ hlower σ hσ v hdisp
  rw [firstShallowCharacter_apply, tracePullbackAddChar_apply]
  simp only [Units.val_div_eq_div_val, Units.coe_map]
  change Ψ (trace F L₁ (norm L₁ K O.Y * (1 - σ (v : L₁) / (v : L₁)))) = _
  have hA : norm L₁ K O.Y = algebraMap F L₁ (f - d ^ 2 * g) -
      algebraMap F L₁ (1 + d) * x := by
    rw [O.upperNorm₁, O.E_eq, O.k₀_eq]
    simp only [map_add, map_sub, map_mul, map_pow]
    ring
  rw [hA]
  exact heval

end ActualFields

end

end LanglandsSecondMainLemma.Dyadic.Nonmaximal
