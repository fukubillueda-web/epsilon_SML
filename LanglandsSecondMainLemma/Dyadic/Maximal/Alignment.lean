import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.LocalField.Lattices
import LanglandsFirstMainLemma.LocalField.MonogenicUniformizer
import LanglandsFirstMainLemma.LocalField.Valuation
import LanglandsSecondMainLemma.Dyadic.Mixed.UnitSymbol
import LanglandsSecondMainLemma.Local.Newton

/-!
# Dyadic / Maximal / Alignment

This file proves Paper Lemma 12.3 (`D:MX:align`).  It constructs the
alternating square corrections in the truncated dyadic valuation ring,
then applies them to the two actual Kummer generators in a common ambient
field.  The result records the unchanged intermediate fields, both exact
orders, and membership of the quotient in FML's full unit filtration.

Blueprint: `blueprint/tasks/Dyadic/Maximal/Alignment.md`.
Paper: lines 6820--6851 and 6894--6934 of `references/epsilon_SML.tex`.
-/
namespace LanglandsSecondMainLemma.Dyadic.Maximal

open LanglandsFirstMainLemma

noncomputable section

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private theorem nat_nsmul_one_withTop (n : ℕ) :
    n • (1 : WithTop ℤ) = ((n : ℤ) : WithTop ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul, ih]
      norm_num

private theorem residueFrobenius_two_surjective
    (hchar : residueCharacteristic F = 2) :
    Function.Surjective (fun x : ResidueField F => x ^ 2) := by
  letI : CharP (ResidueField F) 2 := ringChar.of_eq hchar
  intro y
  obtain ⟨x, hx⟩ :=
    Finite.surjective_of_injective (frobenius_inj (ResidueField F) 2) y
  refine ⟨x, ?_⟩
  simpa only [frobenius_def] using hx

private theorem exists_integral_square_correction
    (hchar : residueCharacteristic F = 2)
    (A x : ringOfIntegers F) (hA : IsUnit A) :
    ∃ z : ringOfIntegers F,
      (x : F) - (A : F) * (z : F) ^ 2 ∈ lattice F 1 := by
  have hAbar : residueMap F A ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit A).2 hA
  obtain ⟨zbar, hzbar⟩ := residueFrobenius_two_surjective F hchar
    ((residueMap F A)⁻¹ * residueMap F x)
  change zbar ^ 2 = _ at hzbar
  let z : ringOfIntegers F := teichmuller F zbar
  refine ⟨z, ?_⟩
  let d : ringOfIntegers F := x - A * z ^ 2
  have hd : residueMap F d = 0 := by
    simp only [d, map_sub, map_mul, map_pow]
    rw [show residueMap F z = zbar by
      simpa only [z] using residueMap_teichmuller F zbar]
    rw [hzbar]
    field_simp
    ring
  simpa [d] using (residueMap_eq_zero_iff F d).1 hd

private theorem exists_integral_unit_square_correction
    (hchar : residueCharacteristic F = 2)
    (A x : ringOfIntegers F) (hA : IsUnit A) (hx : IsUnit x) :
    ∃ z : ringOfIntegers F, IsUnit z ∧
      (x : F) - (A : F) * (z : F) ^ 2 ∈ lattice F 1 := by
  have hAbar : residueMap F A ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit A).2 hA
  have hxbar : residueMap F x ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit x).2 hx
  obtain ⟨zbar, hzbar⟩ := residueFrobenius_two_surjective F hchar
    ((residueMap F A)⁻¹ * residueMap F x)
  change zbar ^ 2 = _ at hzbar
  have hzbar0 : zbar ≠ 0 := by
    intro hz
    subst zbar
    change (0 : ResidueField F) ^ 2 = _ at hzbar
    rw [zero_pow (by norm_num)] at hzbar
    exact (mul_ne_zero (inv_ne_zero hAbar) hxbar) hzbar.symm
  let z : ringOfIntegers F := teichmuller F zbar
  have hzunit : IsUnit z :=
    (IsLocalRing.residue_ne_zero_iff_isUnit z).1 (by simpa [z])
  refine ⟨z, hzunit, ?_⟩
  let d : ringOfIntegers F := x - A * z ^ 2
  have hd : residueMap F d = 0 := by
    simp only [d, map_sub, map_mul, map_pow]
    rw [show residueMap F z = zbar by
      simpa only [z] using residueMap_teichmuller F zbar]
    rw [hzbar]
    field_simp
    ring
  simpa [d] using (residueMap_eq_zero_iff F d).1 hd

private theorem truncatedAlignmentSolution
    (hchar : residueCharacteristic F = 2)
    (pi : ringOfIntegers F)
    (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F))
    (e a : ℕ) (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (ha : 1 ≤ a) (hae : a ≤ e)
    (u0 w0 c : ringOfIntegers F)
    (hu0 : IsUnit u0) (hw0 : IsUnit w0) (hc : IsUnit c) :
    ∃ v w : ringOfIntegers F, IsUnit v ∧
      (u0 : F) - (w0 : F) * (v : F) ^ 2 -
          (pi : F) * (c : F) * (w : F) ^ 2 ∈
        lattice F (a : ℤ) := by
  let P : ℕ → Prop := fun n =>
    ∃ v w : ringOfIntegers F, IsUnit v ∧
      (u0 : F) - (w0 : F) * (v : F) ^ 2 -
          (pi : F) * (c : F) * (w : F) ^ 2 ∈
        lattice F (n : ℤ)
  have hbase : P 1 := by
    obtain ⟨v, hvunit, hv⟩ :=
      exists_integral_unit_square_correction F hchar w0 u0 hw0 hu0
    refine ⟨v, 0, hvunit, ?_⟩
    simpa using hv
  have hP : ∀ n, 1 ≤ n → n ≤ a → P n := by
    intro n hn hna
    induction n with
    | zero => omega
    | succ n ih =>
        by_cases hn0 : n = 0
        · subst n
          simpa using hbase
        · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
          have hna' : n ≤ a := (Nat.le_succ n).trans hna
          obtain ⟨v, w, hvunit, herror⟩ := ih hnpos hna'
          have hnlt : n < a := by omega
          have hscaled := herror
          rw [lattice_eq_uniformizer_zpow_smul F hpi (n : ℤ)] at hscaled
          rw [Submodule.mem_smul_pointwise_iff_exists] at hscaled
          obtain ⟨x, hx, hxeq⟩ := hscaled
          let xO : ringOfIntegers F :=
            ⟨x, (mem_lattice_zero_iff F).1 hx⟩
          have hxeq' :
              (u0 : F) - (w0 : F) * (v : F) ^ 2 -
                  (pi : F) * (c : F) * (w : F) ^ 2 =
                (pi : F) ^ n * (xO : F) := by
            simpa [xO, smul_eq_mul] using hxeq.symm
          by_cases heven : Even n
          · obtain ⟨j, hj⟩ := heven
            have hnj : n = 2 * j := by omega
            obtain ⟨z, hz⟩ :=
              exists_integral_square_correction F hchar w0 xO hw0
            let corr : ringOfIntegers F := pi ^ j * z
            let v' : ringOfIntegers F := v + corr
            have hcorrOne : (corr : F) ∈ lattice F 1 := by
              rw [mem_lattice]
              simp only [corr, Subring.coe_mul, Subring.coe_pow, ord_mul,
                ord_pow, ord_uniformizer F hpi]
              have hz0 : (0 : WithTop ℤ) ≤ ord F (z : F) :=
                (ord_nonneg_iff_mem_integer F _).2 z.property
              have hjpos : 1 ≤ j := by omega
              rw [nat_nsmul_one_withTop]
              have hjcast : ((1 : ℤ) : WithTop ℤ) ≤
                  ((j : ℤ) : WithTop ℤ) :=
                WithTop.coe_le_coe.mpr (by exact_mod_cast hjpos)
              simpa only [nsmul_eq_mul, mul_one] using
                hjcast.trans (le_add_of_nonneg_right hz0)
            have hv'unit : IsUnit v' := by
              apply (IsLocalRing.residue_ne_zero_iff_isUnit v').1
              have hvbar : residueMap F v ≠ 0 :=
                (IsLocalRing.residue_ne_zero_iff_isUnit v).2 hvunit
              have hcorrbar : residueMap F corr = 0 :=
                (residueMap_eq_zero_iff F corr).2 hcorrOne
              simpa [v', hcorrbar] using hvbar
            refine ⟨v', w, hv'unit, ?_⟩
            have hmain :
                (pi : F) ^ n * ((xO : F) - (w0 : F) * (z : F) ^ 2) ∈
                  lattice F ((n + 1 : ℕ) : ℤ) := by
              have hp : (pi : F) ^ n ∈ lattice F (n : ℤ) := by
                rw [mem_lattice, ord_pow, ord_uniformizer F hpi]
                simp
              simpa only [Int.natCast_add, Int.natCast_one] using
                mul_mem_lattice F hp hz
            have hcross :
                (2 : F) * (w0 : F) * (v : F) *
                    ((pi : F) ^ j * (z : F)) ∈
                  lattice F ((n + 1 : ℕ) : ℤ) := by
              rw [mem_lattice]
              simp only [ord_mul, ord_pow, ord_uniformizer F hpi, htwo]
              have hw00 : (0 : WithTop ℤ) ≤ ord F (w0 : F) :=
                (ord_nonneg_iff_mem_integer F _).2 w0.property
              have hv0 : (0 : WithTop ℤ) ≤ ord F (v : F) :=
                (ord_nonneg_iff_mem_integer F _).2 v.property
              have hz0 : (0 : WithTop ℤ) ≤ ord F (z : F) :=
                (ord_nonneg_iff_mem_integer F _).2 z.property
              rw [nat_nsmul_one_withTop]
              have hbaseOrder :
                  (((n + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
                    (e : WithTop ℤ) + ((j : ℤ) : WithTop ℤ) := by
                exact_mod_cast (show n + 1 ≤ e + j by omega)
              have hrest : ((j : ℤ) : WithTop ℤ) ≤
                  ord F (w0 : F) + ord F (v : F) +
                    (((j : ℤ) : WithTop ℤ) + ord F (z : F)) := by
                have := add_le_add (add_le_add hw00 hv0)
                  (add_le_add (le_refl (((j : ℤ) : WithTop ℤ))) hz0)
                simpa only [zero_add, add_zero] using this
              exact hbaseOrder.trans (by
                have := add_le_add_left hrest (e : WithTop ℤ)
                simpa only [add_assoc, add_comm, add_left_comm] using this)
            change
              (u0 : F) - (w0 : F) * (v' : F) ^ 2 -
                  (pi : F) * (c : F) * (w : F) ^ 2 ∈ _
            rw [show
                (u0 : F) - (w0 : F) * (v' : F) ^ 2 -
                    (pi : F) * (c : F) * (w : F) ^ 2 =
                  (pi : F) ^ n * ((xO : F) - (w0 : F) * (z : F) ^ 2) -
                    (2 : F) * (w0 : F) * (v : F) *
                      ((pi : F) ^ j * (z : F)) by
              calc
                _ = ((u0 : F) - (w0 : F) * (v : F) ^ 2 -
                      (pi : F) * (c : F) * (w : F) ^ 2) -
                    (w0 : F) * ((pi : F) ^ j * (z : F)) ^ 2 -
                    (2 : F) * (w0 : F) * (v : F) *
                      ((pi : F) ^ j * (z : F)) := by
                    simp only [v', corr, Subring.coe_add, Subring.coe_mul,
                      Subring.coe_pow]
                    ring
                _ = _ := by rw [hxeq', hnj]; ring]
            exact sub_mem_lattice F hmain hcross
          · have hodd : Odd n := Nat.not_even_iff_odd.mp heven
            obtain ⟨j, hj⟩ := hodd
            have hnj : n = 2 * j + 1 := by omega
            obtain ⟨z, hz⟩ :=
              exists_integral_square_correction F hchar c xO hc
            let corr : ringOfIntegers F := pi ^ j * z
            let w' : ringOfIntegers F := w + corr
            refine ⟨v, w', hvunit, ?_⟩
            have hmain :
                (pi : F) ^ n * ((xO : F) - (c : F) * (z : F) ^ 2) ∈
                  lattice F ((n + 1 : ℕ) : ℤ) := by
              have hp : (pi : F) ^ n ∈ lattice F (n : ℤ) := by
                rw [mem_lattice, ord_pow, ord_uniformizer F hpi]
                simp
              simpa only [Int.natCast_add, Int.natCast_one] using
                mul_mem_lattice F hp hz
            have hcross :
                (2 : F) * (pi : F) * (c : F) * (w : F) *
                    ((pi : F) ^ j * (z : F)) ∈
                  lattice F ((n + 1 : ℕ) : ℤ) := by
              rw [mem_lattice]
              simp only [ord_mul, ord_pow, ord_uniformizer F hpi, htwo]
              have hc0 : (0 : WithTop ℤ) ≤ ord F (c : F) :=
                (ord_nonneg_iff_mem_integer F _).2 c.property
              have hw0 : (0 : WithTop ℤ) ≤ ord F (w : F) :=
                (ord_nonneg_iff_mem_integer F _).2 w.property
              have hz0 : (0 : WithTop ℤ) ≤ ord F (z : F) :=
                (ord_nonneg_iff_mem_integer F _).2 z.property
              rw [nat_nsmul_one_withTop]
              have hbaseOrder :
                  (((n + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
                    (e : WithTop ℤ) + 1 +
                      ((j : ℤ) : WithTop ℤ) := by
                exact_mod_cast (show n + 1 ≤ e + 1 + j by omega)
              have hrest : ((j : ℤ) : WithTop ℤ) ≤
                  ord F (c : F) + ord F (w : F) +
                    (((j : ℤ) : WithTop ℤ) + ord F (z : F)) := by
                have := add_le_add (add_le_add hc0 hw0)
                  (add_le_add (le_refl (((j : ℤ) : WithTop ℤ))) hz0)
                simpa only [zero_add, add_zero] using this
              exact hbaseOrder.trans (by
                have := add_le_add_left hrest
                  ((e : WithTop ℤ) + 1)
                simpa only [add_assoc, add_comm, add_left_comm] using this)
            change
              (u0 : F) - (w0 : F) * (v : F) ^ 2 -
                  (pi : F) * (c : F) * (w' : F) ^ 2 ∈ _
            rw [show
                (u0 : F) - (w0 : F) * (v : F) ^ 2 -
                    (pi : F) * (c : F) * (w' : F) ^ 2 =
                  (pi : F) ^ n * ((xO : F) - (c : F) * (z : F) ^ 2) -
                    (2 : F) * (pi : F) * (c : F) * (w : F) *
                      ((pi : F) ^ j * (z : F)) by
              calc
                _ = ((u0 : F) - (w0 : F) * (v : F) ^ 2 -
                      (pi : F) * (c : F) * (w : F) ^ 2) -
                    (pi : F) * (c : F) *
                      ((pi : F) ^ j * (z : F)) ^ 2 -
                    (2 : F) * (pi : F) * (c : F) * (w : F) *
                      ((pi : F) ^ j * (z : F)) := by
                    simp only [w', corr, Subring.coe_add, Subring.coe_mul,
                      Subring.coe_pow]
                    ring
                _ = _ := by rw [hxeq', hnj]; ring]
            exact sub_mem_lattice F hmain hcross
  exact hP a ha le_rfl

private theorem ord_coe_integral_unit_eq_zero
    (u : ringOfIntegers F) (hu : IsUnit u) :
    ord F (u : F) = 0 := by
  let U : (ringOfIntegers F)ˣ := hu.unit
  have hU : (U : ringOfIntegers F) = u := hu.unit_spec
  have hu0 : (0 : WithTop ℤ) ≤ ord F (u : F) :=
    (ord_nonneg_iff_mem_integer F _).2 u.property
  have huval : (ValuativeRel.valuation F) (u : F) = 1 := by
    rw [← hU]
    exact Valuation.Integers.one_of_isUnit
      (Valuation.integer.integers (ValuativeRel.valuation F)) U.isUnit
  apply le_antisymm
  · rw [← ord_one F, ord_le_ord_iff]
    rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F)]
    simp [huval]
  · exact hu0

omit [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] in
private theorem adjoin_mul_algebraMap_eq
    {K : Type*} [Field K] [Algebra F K]
    (x : K) (c : F) (hc : c ≠ 0) :
    IntermediateField.adjoin F {x * algebraMap F K c} =
      IntermediateField.adjoin F {x} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    exact (IntermediateField.adjoin F {x}).mul_mem
      (IntermediateField.mem_adjoin_simple_self F x)
      ((IntermediateField.adjoin F {x}).algebraMap_mem c)
  · rw [IntermediateField.adjoin_le_iff]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    have hmap : algebraMap F K c ≠ 0 := by
      intro h
      apply hc
      apply (algebraMap F K).injective
      simpa using h
    let T : IntermediateField F K := IntermediateField.adjoin F
      {x * algebraMap F K c}
    have hm : (x * algebraMap F K c) * algebraMap F K c⁻¹ ∈ T := T.mul_mem
      (by
        change x * algebraMap F K c ∈
          IntermediateField.adjoin F {x * algebraMap F K c}
        exact IntermediateField.mem_adjoin_simple_self F
          (x * algebraMap F K c))
      (T.algebraMap_mem c⁻¹)
    have heq : (x * algebraMap F K c) * algebraMap F K c⁻¹ = x := by
      rw [map_inv₀, mul_assoc, mul_inv_cancel₀ hmap, mul_one]
    change x ∈ T
    exact heq ▸ hm

/-- The aligned replacements of the two Kummer generators.  The fields
`adjoin_S` and `adjoin_R` record that these are replacements inside the
same two actual quadratic subfields, rather than merely new square-class
parameters.  The final field is the literal `U_F^a` assertion. -/
structure AlignmentData
    {F K : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [Algebra F K]
    (pi : ringOfIntegers F) (e a b : ℕ)
    (u0 w0 : (ringOfIntegers F)ˣ) (s R0 : K) where
  w : ringOfIntegers F
  v : (ringOfIntegers F)ˣ
  delta : F
  S : K
  R : K
  epsilon : F
  rSquare : F
  ratio : Fˣ
  delta_eq : delta = (pi : F) ^ (e - a + 1) * (w : F)
  S_eq : S = s * algebraMap F K (1 + delta)
  R_eq : R = R0 * algebraMap F K (v : F)
  epsilon_eq : epsilon =
    (1 + (pi : F) ^ b * (u0 : F)) * (1 + delta) ^ 2 - 1
  rSquare_eq : rSquare = (pi : F) ^ b * (w0 : F) * (v : F) ^ 2
  S_sq : S ^ 2 = algebraMap F K (1 + epsilon)
  R_sq : R ^ 2 = algebraMap F K rSquare
  adjoin_S : IntermediateField.adjoin F {S} =
    IntermediateField.adjoin F {s}
  adjoin_R : IntermediateField.adjoin F {R} =
    IntermediateField.adjoin F {R0}
  epsilon_order : ord F epsilon = (b : WithTop ℤ)
  rSquare_order : ord F rSquare = (b : WithTop ℤ)
  ratio_coe : (ratio : F) = epsilon / rSquare
  ratio_mem : ratio ∈ unitFiltration F a

/-- **Paper Lemma 12.3 (`D:MX:align`)**.  Starting from the two genuine
Kummer generators

`s² = 1 + pi^b*u0` and `R0² = pi^b*w0`,

where `u0,w0` are base units and `b = 2e - 2a + 1`, this constructs the
paper's replacements `S = s(1+delta)` and `R = R0*v`.  Both generated
intermediate fields are unchanged.  For `epsilon = S² - 1` (viewed in the
base field), both `epsilon` and `R²` have order `b`, and their quotient is
in the full FML unit-filtration layer `U_F^a`.

The hypotheses `residueCharacteristic F = 2` and `ord_F(2)=e` are the
local-field content of `F/Q₂`; the natural-number exponents are protected
from truncation by `1 ≤ a ≤ e` and the displayed equality defining `b`. -/
theorem alignment
    {F K : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [Algebra F K]
    (hchar : residueCharacteristic F = 2)
    (pi : ringOfIntegers F)
    (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F))
    (e a b : ℕ) (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (ha : 1 ≤ a) (hae : a ≤ e)
    (hb : b = 2 * e - 2 * a + 1)
    (u0 w0 : (ringOfIntegers F)ˣ) (s R0 : K)
    (hs : s ^ 2 = algebraMap F K
      (1 + (pi : F) ^ b * (u0 : F)))
    (hR0 : R0 ^ 2 = algebraMap F K
      ((pi : F) ^ b * (w0 : F))) :
    Nonempty (AlignmentData pi e a b u0 w0 s R0) := by
  have hbpos : 1 ≤ b := by omega
  have hdeltaExp : 1 ≤ e - a + 1 := by omega
  let c : ringOfIntegers F :=
    1 + pi ^ b * (u0 : ringOfIntegers F)
  have hpiPowOne : ((pi : F) ^ b) ∈ lattice F 1 := by
    rw [mem_lattice, ord_pow, ord_uniformizer F hpi]
    rw [nat_nsmul_one_withTop]
    exact WithTop.coe_le_coe.mpr (by exact_mod_cast hbpos)
  have hpiPowResidue : residueMap F (pi ^ b) = 0 :=
    (residueMap_eq_zero_iff F (pi ^ b)).2 (by
      simpa only [Subring.coe_pow] using hpiPowOne)
  have hcunit : IsUnit c := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit c).1
    simp [c, hpiPowResidue]
  obtain ⟨v0, w, hv0unit, halign⟩ :=
    truncatedAlignmentSolution F hchar pi hpi e a htwo ha hae
      (u0 : ringOfIntegers F) (w0 : ringOfIntegers F) (-c)
      u0.isUnit w0.isUnit hcunit.neg
  let v : (ringOfIntegers F)ˣ := hv0unit.unit
  have hvcoe : (v : ringOfIntegers F) = v0 := hv0unit.unit_spec
  let delta : F := (pi : F) ^ (e - a + 1) * (w : F)
  let S : K := s * algebraMap F K (1 + delta)
  let R : K := R0 * algebraMap F K (v : F)
  let epsilon : F :=
    (1 + (pi : F) ^ b * (u0 : F)) * (1 + delta) ^ 2 - 1
  let rSquare : F := (pi : F) ^ b * (w0 : F) * (v : F) ^ 2
  have hdeltaOne : delta ∈ lattice F 1 := by
    rw [mem_lattice]
    simp only [delta, ord_mul, ord_pow, ord_uniformizer F hpi]
    rw [nat_nsmul_one_withTop]
    have hw0 : (0 : WithTop ℤ) ≤ ord F (w : F) :=
      (ord_nonneg_iff_mem_integer F _).2 w.property
    exact (WithTop.coe_le_coe.mpr
      (by exact_mod_cast hdeltaExp)).trans (le_add_of_nonneg_right hw0)
  let deltaO : ringOfIntegers F :=
    ⟨delta, (mem_lattice_zero_iff F).1
      (lattice_antitone F (by omega : (0 : ℤ) ≤ 1) hdeltaOne)⟩
  have hdeltaResidue : residueMap F deltaO = 0 :=
    (residueMap_eq_zero_iff F deltaO).2 (by
      simpa only [deltaO] using hdeltaOne)
  have honeDeltaUnit : IsUnit (1 + deltaO) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit (1 + deltaO)).1
    simp [hdeltaResidue]
  have honeDelta0 : 1 + delta ≠ 0 := by
    intro hzero
    have : (1 + deltaO : ringOfIntegers F) = 0 := by
      apply Subtype.ext
      change 1 + delta = 0
      exact hzero
    exact honeDeltaUnit.ne_zero this
  have hvc0 : (v : F) ≠ 0 := by exact_mod_cast Units.ne_zero v
  have hvOrder : ord F (v : F) = 0 := by
    simpa only [hvcoe] using ord_coe_integral_unit_eq_zero F v0 hv0unit
  have hw0Order : ord F (w0 : F) = 0 :=
    ord_coe_integral_unit_eq_zero F (w0 : ringOfIntegers F) w0.isUnit
  have hrOrder : ord F rSquare = (b : WithTop ℤ) := by
    simp only [rSquare, ord_mul, ord_pow, ord_uniformizer F hpi,
      hw0Order, hvOrder]
    rw [nat_nsmul_one_withTop]
    simp
  have hdeltaSq : delta ^ 2 =
      (pi : F) ^ b * (pi : F) * (w : F) ^ 2 := by
    calc
      delta ^ 2 = ((pi : F) ^ (e - a + 1)) ^ 2 * (w : F) ^ 2 := by
        simp only [delta, mul_pow]
      _ = (pi : F) ^ ((e - a + 1) * 2) * (w : F) ^ 2 := by
        rw [pow_mul]
      _ = (pi : F) ^ (b + 1) * (w : F) ^ 2 := by
        rw [show (e - a + 1) * 2 = b + 1 by omega]
      _ = (pi : F) ^ b * (pi : F) * (w : F) ^ 2 := by
        rw [pow_succ]
  have hcore :
      (u0 : F) - (w0 : F) * (v : F) ^ 2 +
          (pi : F) * (c : F) * (w : F) ^ 2 ∈ lattice F (a : ℤ) := by
    simpa only [hvcoe, Subring.coe_neg, neg_mul, mul_neg, sub_neg_eq_add] using
      halign
  have hqCore :
      (pi : F) ^ b *
          ((u0 : F) - (w0 : F) * (v : F) ^ 2 +
            (pi : F) * (c : F) * (w : F) ^ 2) ∈
        lattice F ((b + a : ℕ) : ℤ) := by
    have hq : (pi : F) ^ b ∈ lattice F (b : ℤ) := by
      rw [mem_lattice, ord_pow, ord_uniformizer F hpi,
        nat_nsmul_one_withTop]
    simpa only [Nat.cast_add] using mul_mem_lattice F hq hcore
  have hcross :
      (2 : F) * (c : F) * delta ∈
        lattice F ((b + a : ℕ) : ℤ) := by
    rw [mem_lattice]
    simp only [ord_mul, delta, ord_pow, ord_uniformizer F hpi, htwo]
    rw [nat_nsmul_one_withTop]
    have hc0 : (0 : WithTop ℤ) ≤ ord F (c : F) :=
      (ord_nonneg_iff_mem_integer F _).2 c.property
    have hw0 : (0 : WithTop ℤ) ≤ ord F (w : F) :=
      (ord_nonneg_iff_mem_integer F _).2 w.property
    have hbase : (((b + a : ℕ) : ℤ) : WithTop ℤ) ≤
        (e : WithTop ℤ) +
          (((e - a + 1 : ℕ) : ℤ) : WithTop ℤ) := by
      exact_mod_cast (show b + a ≤ e + (e - a + 1) by omega)
    exact hbase.trans (by
      have := add_le_add (add_le_add
        (le_refl (e : WithTop ℤ)) hc0)
        (add_le_add
          (le_refl (((e - a + 1 : ℕ) : ℤ) : WithTop ℤ)) hw0)
      simpa only [add_zero] using this)
  have hnumEq : epsilon - rSquare =
      (pi : F) ^ b *
          ((u0 : F) - (w0 : F) * (v : F) ^ 2 +
            (pi : F) * (c : F) * (w : F) ^ 2) +
        (2 : F) * (c : F) * delta := by
    simp only [epsilon, rSquare]
    have hcEq : (c : F) = 1 + (pi : F) ^ b * (u0 : F) := by
      simp [c]
    calc
      _ = (pi : F) ^ b *
            ((u0 : F) - (w0 : F) * (v : F) ^ 2) +
          (2 : F) * (c : F) * delta + (c : F) * delta ^ 2 := by
            rw [hcEq]
            ring
      _ = _ := by rw [hdeltaSq]; ring
  have hnum : epsilon - rSquare ∈
      lattice F ((b + a : ℕ) : ℤ) := by
    rw [hnumEq]
    exact add_mem_lattice F hqCore hcross
  have herrorGt : ord F rSquare < ord F (epsilon - rSquare) := by
    rw [hrOrder]
    exact (WithTop.coe_lt_coe.mpr
      (by exact_mod_cast (show b < b + a by omega))).trans_le hnum
  have hepsilonOrder : ord F epsilon = (b : WithTop ℤ) := by
    calc
      ord F epsilon = ord F (rSquare + (epsilon - rSquare)) := by
        congr 1
        ring
      _ = min (ord F rSquare) (ord F (epsilon - rSquare)) :=
        ord_add_eq_min F (ne_of_lt herrorGt)
      _ = (b : WithTop ℤ) := by rw [min_eq_left herrorGt.le, hrOrder]
  have hr0 : rSquare ≠ 0 :=
    (ord_ne_top_iff F).1 (by rw [hrOrder]; exact WithTop.coe_ne_top)
  have hepsilon0 : epsilon ≠ 0 :=
    (ord_ne_top_iff F).1 (by rw [hepsilonOrder]; exact WithTop.coe_ne_top)
  let ratio : Fˣ := Units.mk0 (epsilon / rSquare)
    (div_ne_zero hepsilon0 hr0)
  have hratioLattice : (ratio : F) - 1 ∈ lattice F (a : ℤ) := by
    have hdiv := (div_mem_lattice_iff F rSquare (epsilon - rSquare)
      (b : ℤ) (a : ℤ) (by simpa using hrOrder)).2 (by
        simpa only [Int.natCast_add] using hnum)
    rw [show (ratio : F) - 1 = (epsilon - rSquare) / rSquare by
      simp only [ratio, Units.val_mk0, sub_div]
      rw [div_self hr0]]
    exact hdiv
  have hratioMem : ratio ∈ unitFiltration F a := by
    obtain ⟨a0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    rw [mem_unitFiltration_succ_iff_sub_mem_lattice]
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
      hratioLattice
  have hSsq : S ^ 2 = algebraMap F K (1 + epsilon) := by
    simp only [S, mul_pow]
    rw [hs]
    rw [← map_pow, ← map_mul]
    apply congrArg (algebraMap F K)
    simp only [epsilon]
    ring
  have hRsq : R ^ 2 = algebraMap F K rSquare := by
    simp only [R, mul_pow, hR0]
    rw [← map_pow, ← map_mul]
  refine ⟨{
    w := w
    v := v
    delta := delta
    S := S
    R := R
    epsilon := epsilon
    rSquare := rSquare
    ratio := ratio
    delta_eq := rfl
    S_eq := rfl
    R_eq := rfl
    epsilon_eq := rfl
    rSquare_eq := rfl
    S_sq := hSsq
    R_sq := hRsq
    adjoin_S := adjoin_mul_algebraMap_eq F s (1 + delta) honeDelta0
    adjoin_R := adjoin_mul_algebraMap_eq F R0 (v : F) hvc0
    epsilon_order := hepsilonOrder
    rSquare_order := hrOrder
    ratio_coe := rfl
    ratio_mem := hratioMem
  }⟩

end

end LanglandsSecondMainLemma.Dyadic.Maximal
