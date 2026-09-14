import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.EqualChar.Cartier
import LanglandsSecondMainLemma.Residues.TraceCompatibility
import LanglandsSecondMainLemma.Residues.LogNorm

/-!
# The Artin--Schreier norm character

Paper Lemma 11.2 (`D:EQ:ASsymbol`), in the corrected manuscript.

The residue exponent is invariant under Artin--Schreier translations by Cartier.
A finite descent removes negative even leading powers; the accepted local Newton
lemma solves the integral trace-zero case. This proves nontriviality for every
nonzero Artin--Schreier class, including the unramified constant class.

The actual trace--residue and logarithmic norm identities prove norm triviality.
FML's single quadratic norm index identifies the resulting continuous group
character uniquely. Whole unit layers and the exact last-layer value give the
conductor `t + 1` for a positive odd largest pole `t`.
-/

open scoped LaurentSeries PowerSeries
open HahnSeries LanglandsFirstMainLemma
namespace LanglandsSecondMainLemma.EqualChar
noncomputable section

-- Reuse the proved formal product rule, without duplicating its coefficient proof.
open private laurentDerivative_mul laurentDerivative_coeff from
  LanglandsSecondMainLemma.Residues.LogNorm

local instance (k : Type*) [Field k] [CharP k 2] : CharP (k⸨X⸩) 2 :=
  CharP.of_ringHom_of_ne_zero (HahnSeries.C : k →+* k⸨X⸩) 2 (by norm_num)

section Laurent
variable {k : Type*} [Field k] [Finite k] [CharP k 2]
local instance : Algebra (ZMod 2) k := ZMod.algebra k 2

/-- The differential `du/u`, represented in the basis `dX`. -/
def logarithmicDerivative (u : k⸨X⸩) : k⸨X⸩ :=
  u⁻¹ * LaurentSeries.derivative k u

/-- The exponent of the characteristic-two Artin--Schreier residue symbol. -/
def residueExponent (f u : k⸨X⸩) : ZMod 2 :=
  Algebra.trace (ZMod 2) k (Residues.residue (f * logarithmicDerivative u))

omit [Finite k] in
@[simp] theorem residueExponent_add (f g u : k⸨X⸩) :
    residueExponent (f + g) u = residueExponent f u + residueExponent g u := by
  simp [residueExponent, add_mul, Residues.residue]

/-- Cartier makes Artin--Schreier coboundaries invisible to the residue symbol. -/
theorem residueExponent_artinSchreier (w u : k⸨X⸩) (hu : u ≠ 0) :
    residueExponent (w ^ 2 + w) u = 0 := by
  have h := cartier_residueTrace (w ^ 2 * logarithmicDerivative u)
  rw [cartier_square_mul, show cartier (logarithmicDerivative u) =
    logarithmicDerivative u from cartier_dlog u hu] at h
  rw [residueExponent_add]
  change residueExponent (w ^ 2) u + residueExponent w u = 0
  change residueExponent w u = residueExponent (w ^ 2) u at h
  rw [← h]
  exact CharTwo.add_self_eq_zero _

/-- The symbol depends only on the Artin--Schreier class of its first argument. -/
theorem residueExponent_add_artinSchreier (f w u : k⸨X⸩) (hu : u ≠ 0) :
    residueExponent (f + (w ^ 2 + w)) u = residueExponent f u := by
  rw [residueExponent_add, residueExponent_artinSchreier w u hu, add_zero]

omit [Finite k] [CharP k 2] in
private theorem logarithmicDerivative_mul (u v : k⸨X⸩) (hu : u ≠ 0) (hv : v ≠ 0) :
    logarithmicDerivative (u * v) = logarithmicDerivative u + logarithmicDerivative v := by
  simp only [logarithmicDerivative, laurentDerivative_mul]
  field_simp
  ring

omit [Finite k] in
/-- Multiplicativity of the exponent, with its additive target. -/
theorem residueExponent_mul (f u v : k⸨X⸩) (hu : u ≠ 0) (hv : v ≠ 0) :
    residueExponent f (u * v) = residueExponent f u + residueExponent f v := by
  simp [residueExponent, logarithmicDerivative_mul u v hu hv, mul_add, Residues.residue]

/-- The paper's exact sign `(-1)^(tr Res(f du/u))`, as a group homomorphism. -/
def residueSymbol (f : k⸨X⸩) : (k⸨X⸩)ˣ →* ℂˣ where
  toFun u := Units.mk0 (binaryAddChar (residueExponent f u)) (by
    rw [binaryAddChar_apply]
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  map_one' := by
    apply Units.ext
    simp [residueExponent, logarithmicDerivative, LaurentSeries.derivative_apply,
      Residues.residue, LaurentSeries.hasseDeriv_single, ← HahnSeries.single_zero_one]
  map_mul' u v := by
    apply Units.ext
    change binaryAddChar (residueExponent f ((u : k⸨X⸩) * (v : k⸨X⸩))) =
      binaryAddChar (residueExponent f u) * binaryAddChar (residueExponent f v)
    rw [residueExponent_mul f u v u.ne_zero v.ne_zero, AddChar.map_add_eq_mul]

omit [Finite k] in
@[simp] theorem residueSymbol_apply (f : k⸨X⸩) (u : (k⸨X⸩)ˣ) :
    (residueSymbol f u : ℂ) = (-1 : ℂ) ^ (residueExponent f u).val := rfl

omit [Finite k] [CharP k 2] in
private theorem logarithmicDerivative_order (u : k⸨X⸩) (n : ℤ)
    (hn : 0 < n) (hu : (n : WithTop ℤ) ≤ (u - 1).orderTop) :
    ((n - 1 : ℤ) : WithTop ℤ) ≤ (logarithmicDerivative u).orderTop := by
  have huord : u.orderTop = 0 := by
    have h := HahnSeries.orderTop_add_eq_left (x := (1 : k⸨X⸩))
      (y := u - 1) (by simpa using (WithTop.coe_lt_coe.mpr hn).trans_le hu)
    simpa using h
  have hu0 : u ≠ 0 := by
    intro hz
    simp [hz] at huord
  have hi : u⁻¹.orderTop = 0 := by
    have h := HahnSeries.orderTop_mul (x := u) (y := u⁻¹)
    rw [mul_inv_cancel₀ hu0, HahnSeries.orderTop_one, huord, zero_add] at h
    exact h.symm
  have hd : ((n - 1 : ℤ) : WithTop ℤ) ≤
      (LaurentSeries.derivative k (u - 1)).orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro j hj
    rw [laurentDerivative_coeff]
    have hj' : ((j + 1 : ℤ) : WithTop ℤ) < (u - 1).orderTop := by
      apply lt_of_lt_of_le _ hu
      exact WithTop.coe_lt_coe.mpr (by have hj0 := WithTop.coe_lt_coe.mp hj; omega)
    rw [HahnSeries.coeff_eq_zero_of_lt_orderTop hj', mul_zero]
  have hd1 : LaurentSeries.derivative k (1 : k⸨X⸩) = 0 := by
    simp [LaurentSeries.derivative_apply, ← HahnSeries.single_zero_one]
  simpa only [logarithmicDerivative, HahnSeries.orderTop_mul, hi, zero_add,
    map_sub, hd1, sub_zero] using hd

omit [Finite k] in
/-- The residue symbol vanishes on the whole sufficiently deep unit ideal. -/
theorem residueExponent_deepUnit (f u : k⸨X⸩) (t : ℕ)
    (hf : ((-(t : ℤ) : ℤ) : WithTop ℤ) ≤ f.orderTop)
    (hu : ((t + 1 : ℕ) : WithTop ℤ) ≤ (u - 1).orderTop) :
    residueExponent f u = 0 := by
  have hd := logarithmicDerivative_order u (t + 1) (by omega) (by exact_mod_cast hu)
  simp only [add_sub_cancel_right] at hd
  have hbound : (0 : WithTop ℤ) ≤ (f * logarithmicDerivative u).orderTop := by
    rw [HahnSeries.orderTop_mul]
    have h := add_le_add hf hd
    simpa only [← WithTop.LinearOrderedAddCommGroup.coe_neg,
      ← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero] using h
  have hz : Residues.residue (f * logarithmicDerivative u) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      ((WithTop.coe_lt_coe.mpr (by omega : (-1 : ℤ) < 0)).trans_le hbound)
  simp [residueExponent, hz]

omit [Finite k] [CharP k 2] in
private theorem single_order_bound (n : ℤ) (c : k) :
    (n : WithTop ℤ) ≤ (single n c).orderTop := HahnSeries.orderTop_single_le

omit [Finite k] in
/-- Exact last-layer value at `1 + c X^t`; the pole bound is on the whole
Laurent series, and `t` is positive and odd. -/
theorem residueExponent_lastLayer (f : k⸨X⸩) (t : ℕ) (ht : 0 < t)
    (hodd : Odd t) (hf : ((-(t : ℤ) : ℤ) : WithTop ℤ) ≤ f.orderTop) (c : k) :
    residueExponent f (1 + single (t : ℤ) c) =
      Algebra.trace (ZMod 2) k (f.coeff (-(t : ℤ)) * c) := by
  let u : k⸨X⸩ := 1 + single (t : ℤ) c
  have hu : ((t : ℤ) : WithTop ℤ) ≤ (u - 1).orderTop := by
    simp only [u, add_sub_cancel_left]
    exact single_order_bound _ _
  have hu0 : u ≠ 0 := by
    intro hzero
    have h0 := hu
    rw [hzero] at h0
    have : t = 0 := by simpa using h0
    omega
  have hd := logarithmicDerivative_order u t (by omega) hu
  have hvanish : Residues.residue
      (f * single (t : ℤ) c * logarithmicDerivative u) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    have hb := add_le_add (add_le_add hf (single_order_bound (t : ℤ) c)) hd
    simp only [← HahnSeries.orderTop_mul, ← WithTop.coe_add] at hb
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hb
  have hcast : (t : k) = 1 := by
    obtain ⟨n, hn⟩ := hodd
    rw [hn]
    push_cast
    rw [CharTwo.two_eq_zero]
    simp
  have hdu : LaurentSeries.derivative k u = single (t - 1 : ℤ) c := by
    simp [u, LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_single,
      ← HahnSeries.single_zero_one, hcast]
  have heq : f * logarithmicDerivative u +
      f * single (t : ℤ) c * logarithmicDerivative u =
      f * single (t - 1 : ℤ) c := by
    calc
      _ = f * (u * logarithmicDerivative u) := by dsimp [u]; ring
      _ = _ := by rw [logarithmicDerivative, ← mul_assoc u,
        mul_inv_cancel₀ hu0, one_mul, hdu]
  have hr := congrArg Residues.residue heq
  simp only [Residues.residue, HahnSeries.coeff_add, HahnSeries.coeff_mul_single] at hr
  change (f * logarithmicDerivative u).coeff (-1) +
      Residues.residue (f * single (t : ℤ) c * logarithmicDerivative u) = _ at hr
  rw [hvanish, add_zero] at hr
  change Algebra.trace (ZMod 2) k (Residues.residue (f * logarithmicDerivative u)) = _
  rw [show Residues.residue (f * logarithmicDerivative u) =
    f.coeff (-(t : ℤ)) * c by simpa only [Residues.residue,
      show (-1 : ℤ) - (t - 1) = -(t : ℤ) by omega] using hr]

/-- Every series whose largest pole is odd is detected by the residue symbol. -/
theorem residueExponent_nontrivial_of_oddPole (f : k⸨X⸩) (t : ℕ) (ht : 0 < t)
    (hodd : Odd t) (hf : f.orderTop = ((-(t : ℤ) : ℤ) : WithTop ℤ)) :
    ∃ u : (k⸨X⸩)ˣ, residueExponent f u = 1 := by
  letI := Fintype.ofFinite k
  have hcoeff : f.coeff (-(t : ℤ)) ≠ 0 := HahnSeries.coeff_orderTop_ne hf
  obtain ⟨c, hc⟩ := exists_absoluteTraceTwo_mul_eq_one k hcoeff
  have hu : (1 + single (t : ℤ) c : k⸨X⸩) ≠ 0 := by
    intro hzero
    have h := congrArg (fun x : k⸨X⸩ ↦ x.coeff 0) hzero
    simp [HahnSeries.coeff_single_of_ne (show (0 : ℤ) ≠ t by omega)] at h
  exact ⟨Units.mk0 _ hu, (residueExponent_lastLayer f t ht hodd hf.ge c).trans hc⟩

omit [Finite k] in
/-- A nonzero constant Artin--Schreier class is detected at the uniformizer. -/
theorem residueExponent_uniformizer (f : k⸨X⸩) :
    residueExponent f (single (1 : ℤ) 1) = Algebra.trace (ZMod 2) k (f.coeff 0) := by
  simp [residueExponent, logarithmicDerivative, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_single, Residues.residue,
    HahnSeries.coeff_mul_single]

omit [Finite k] [CharP k 2] in
private theorem next_order_bound {g : k⸨X⸩} {a : ℤ}
    (h : (a : WithTop ℤ) < g.orderTop) :
    ((a + 1 : ℤ) : WithTop ℤ) ≤ g.orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro j hj
  have hja : j ≤ a := by have := WithTop.coe_lt_coe.mp hj; omega
  exact HahnSeries.coeff_eq_zero_of_lt_orderTop
    ((WithTop.coe_le_coe.mpr hja).trans_lt h)

/-- A finite sequence of Artin--Schreier translations either removes every
pole or leaves a largest pole of positive odd order. This constructor uses a
natural number only to count the finite descent, and keeps all orders integer. -/
theorem exists_oddPole_or_integral_translate (f : k⸨X⸩) :
    ∃ w : k⸨X⸩, 0 ≤ (f + (w ^ 2 + w)).orderTop ∨
      ∃ t : ℕ, 0 < t ∧ Odd t ∧
        (f + (w ^ 2 + w)).orderTop = ((-(t : ℤ) : ℤ) : WithTop ℤ) := by
  have aux (n : ℕ) : ∀ f : k⸨X⸩, ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ f.orderTop →
      ∃ w : k⸨X⸩, 0 ≤ (f + (w ^ 2 + w)).orderTop ∨
        ∃ t : ℕ, 0 < t ∧ Odd t ∧
          (f + (w ^ 2 + w)).orderTop = ((-(t : ℤ) : ℤ) : WithTop ℤ) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hf
      by_cases hn : n = 0
      · exact ⟨0, Or.inl (by simpa [hn] using hf)⟩
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      by_cases heq : f.orderTop = ((-(n : ℤ) : ℤ) : WithTop ℤ)
      · by_cases hodd : Odd n
        · exact ⟨0, Or.inr ⟨n, hnpos, hodd, by simpa using heq⟩⟩
        obtain ⟨q, hq⟩ := (Nat.even_or_odd n).resolve_right hodd
        have hqpos : 0 < q := by omega
        let c : k := (frobeniusEquiv k 2).symm (f.coeff (-(n : ℤ)))
        have hc : c ^ 2 = f.coeff (-(n : ℤ)) :=
          (frobeniusEquiv k 2).apply_symm_apply _
        let v : k⸨X⸩ := single (-(q : ℤ)) c
        have hvsq : v ^ 2 = single (-(n : ℤ)) (f.coeff (-(n : ℤ))) := by
          dsimp [v]
          rw [pow_two, HahnSeries.single_mul_single, ← pow_two, hc]
          rw [show -(q : ℤ) + -(q : ℤ) = -(n : ℤ) by omega]
        have hv : ((-(n : ℤ) : ℤ) : WithTop ℤ) < v.orderTop :=
          (WithTop.coe_lt_coe.mpr (by omega)).trans_le (single_order_bound _ _)
        have hfv : ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ (f + v ^ 2).orderTop := by
          apply le_trans (le_min hf _) HahnSeries.min_orderTop_le_orderTop_add
          rw [hvsq]
          exact single_order_bound _ _
        have hz : (f + v ^ 2).coeff (-(n : ℤ)) = 0 := by
          rw [HahnSeries.coeff_add, hvsq, HahnSeries.coeff_single_same]
          exact CharTwo.add_self_eq_zero _
        have hstrict : ((-(n : ℤ) : ℤ) : WithTop ℤ) < (f + (v ^ 2 + v)).orderTop := by
          rw [← add_assoc]
          exact lt_of_lt_of_le
            (lt_min (lt_of_le_of_ne hfv
              (HahnSeries.orderTop_ne_of_coeff_eq_zero hz).symm) hv)
            HahnSeries.min_orderTop_le_orderTop_add
        have hnext : ((-((n - 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤
            (f + (v ^ 2 + v)).orderTop := by
          have hindex : -((n - 1 : ℕ) : ℤ) = -(n : ℤ) + 1 := by omega
          rw [hindex]
          exact next_order_bound hstrict
        obtain ⟨w, hw⟩ := ih (n - 1) (by omega) (f + (v ^ 2 + v)) hnext
        refine ⟨v + w, ?_⟩
        have hcombine : f + ((v + w) ^ 2 + (v + w)) =
            (f + (v ^ 2 + v)) + (w ^ 2 + w) := by
          rw [CharTwo.add_sq]
          abel
        rwa [hcombine]
      · have hstrict : ((-(n : ℤ) : ℤ) : WithTop ℤ) < f.orderTop :=
          lt_of_le_of_ne hf (Ne.symm heq)
        apply ih (n - 1) (by omega) f
        have hindex : -((n - 1 : ℕ) : ℤ) = -(n : ℤ) + 1 := by omega
        rw [hindex]
        exact next_order_bound hstrict
  apply aux f.order.natAbs f
  by_cases hf : f = 0
  · simp [hf]
  · rw [← HahnSeries.order_eq_orderTop_of_ne_zero hf]
    exact WithTop.coe_le_coe.mpr (by
      have := Int.le_natAbs (a := -f.order)
      simp only [Int.natAbs_neg] at this
      omega)

end Laurent

private theorem not_artinSchreier_of_generator
    (F E : Type*) [Field F] [Field E] [Algebra F E] [CharP F 2] (f : F) (z : E)
    (hz : z ^ 2 + z = algebraMap F E f)
    (hgen : z ∉ Set.range (algebraMap F E)) : ¬ ∃ w : F, w ^ 2 + w = f := by
  letI : CharP E 2 := charP_of_injective_algebraMap (algebraMap F E).injective 2
  rintro ⟨w, hw⟩
  let a := z + algebraMap F E w
  have ha : a ^ 2 + a = 0 := by
    dsimp [a]
    rw [CharTwo.add_sq]
    calc
      _ = (z ^ 2 + z) + ((algebraMap F E w) ^ 2 + algebraMap F E w) := by abel
      _ = 0 := by rw [hz, ← map_pow, ← map_add, hw, CharTwo.add_self_eq_zero]
  have hsq : a * a = a := by
    have h := CharTwo.add_eq_zero.mp ha
    simpa only [pow_two] using h
  rcases eq_zero_or_one_of_sq_eq_self (by simpa only [pow_two] using hsq) with ha0 | ha1
  · apply hgen
    refine ⟨w, ?_⟩
    exact (CharTwo.add_eq_zero.mp ha0).symm
  · apply hgen
    refine ⟨w + 1, ?_⟩
    rw [map_add, map_one]
    have h : z + algebraMap F E w = 1 := ha1
    calc
      algebraMap F E w + 1 = algebraMap F E w + (z + algebraMap F E w) := by rw [h]
      _ = z := by rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]


section ActualNorm
variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E]
  [Module.Finite F E] [Algebra.IsSeparable F E] [CharP F 2]

private theorem residueField_charTwo (K : Type*) [Field K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [CharP K 2] : CharP (ResidueField K) 2 := by
  letI : CharP (ringOfIntegers K) 2 :=
    (SubringClass.subtype (ringOfIntegers K)).charP
      (fun x y hxy ↦ Subtype.ext hxy) 2
  exact CharP.of_ringHom_of_ne_zero (residueMap K) 2 (by norm_num)

local instance (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharP K 2] : CharP (ResidueField K) 2 :=
  residueField_charTwo K
local instance (k : Type*) [Field k] [CharP k 2] : Algebra (ZMod 2) k :=
  ZMod.algebra k 2

/-- A local field of characteristic two has equal characteristic. -/
theorem equalCharacteristicTwo : ringChar F = ringChar (ResidueField F) :=
  (ringChar.eq F 2).trans (ringChar.eq (ResidueField F) 2).symm

private theorem integral_traceZero_is_artinSchreier
    (P : Residues.EqualCharacteristicPresentation F)
    (g : (ResidueField F)⸨X⸩) (hg : 0 ≤ g.orderTop)
    (htrace : Algebra.trace (ZMod 2) (ResidueField F) (g.coeff 0) = 0) :
    ∃ w : (ResidueField F)⸨X⸩, w ^ 2 + w = g := by
  letI : Fintype (ResidueField F) := residueFieldFintype F
  letI : CharP (ringOfIntegers F) 2 :=
    (SubringClass.subtype (ringOfIntegers F)).charP
      (fun x y hxy ↦ Subtype.ext hxy) 2
  obtain ⟨c, hc⟩ := (absoluteTraceTwo_eq_zero_iff (ResidueField F) (g.coeff 0)).mp htrace
  let a := g - HahnSeries.C (g.coeff 0)
  have ha : 0 < a.orderTop := by
    apply lt_of_le_of_ne
    · exact le_trans (le_min hg (by simpa [HahnSeries.C_apply] using
        (single_order_bound (0 : ℤ) (g.coeff 0))))
        HahnSeries.min_orderTop_le_orderTop_sub
    · exact (HahnSeries.orderTop_ne_of_coeff_eq_zero
        (by simp [a])).symm
  let A : ringOfIntegers F := ⟨P.laurentEquiv a,
    (ord_nonneg_iff_mem_integer F _).mp (by rw [P.laurentEquiv_order]; exact ha.le)⟩
  let p : Polynomial (ringOfIntegers F) :=
    Polynomial.X ^ 2 + Polynomial.X - Polynomial.C A
  have hpderiv : ord F ((p.derivative.eval 0 : ringOfIntegers F) : F) =
      (0 : WithTop ℤ) := by
    simp [p, Polynomial.derivative_pow]
  have hpres : ((2 * (0 : ℤ) : ℤ) : WithTop ℤ) <
      ord F ((p.eval 0 : ringOfIntegers F) : F) := by
    simpa [p, A, P.laurentEquiv_order] using ha
  obtain ⟨b, hb, _⟩ := Local.newton p 0 0 hpderiv hpres
  have hb' : (b : F) ^ 2 + (b : F) = P.laurentEquiv a := by
    have hb0 : b ^ 2 + b - A = 0 := by simpa [p, Polynomial.IsRoot] using hb
    exact congrArg (fun x : ringOfIntegers F ↦ (x : F)) (sub_eq_zero.mp hb0)
  refine ⟨P.laurentEquiv.symm (b : F) + HahnSeries.C c, ?_⟩
  have hbc : (P.laurentEquiv.symm (b : F)) ^ 2 +
      P.laurentEquiv.symm (b : F) = a := by
    simpa only [map_add, map_pow, RingEquiv.symm_apply_apply] using
      congrArg P.laurentEquiv.symm hb'
  rw [CharTwo.add_sq]
  calc
    _ = ((P.laurentEquiv.symm (b : F)) ^ 2 + P.laurentEquiv.symm (b : F)) +
        (HahnSeries.C c ^ 2 + HahnSeries.C c) := by abel
    _ = a + HahnSeries.C (c ^ 2 + c) := by rw [hbc, map_add, map_pow]
    _ = g := by
      rw [show c ^ 2 + c = g.coeff 0 by simpa [add_comm] using hc.symm]
      exact sub_add_cancel _ _

/-- Every nonzero Artin--Schreier class of the actual local field is detected.
The integral branch is solved by the accepted local Newton theorem, while
negative even poles are removed by the finite Laurent descent above. -/
theorem residueExponent_nontrivial
    (P : Residues.EqualCharacteristicPresentation F) (f : F)
    (hf : ¬ ∃ w : F, w ^ 2 + w = f) :
    ∃ u : ((ResidueField F)⸨X⸩)ˣ,
      residueExponent (P.laurentEquiv.symm f) u = 1 := by
  let f' := P.laurentEquiv.symm f
  obtain ⟨w, hint | ⟨t, ht, hodd, hpole⟩⟩ := exists_oddPole_or_integral_translate f'
  · let g := f' + (w ^ 2 + w)
    have htrace : Algebra.trace (ZMod 2) (ResidueField F) (g.coeff 0) ≠ 0 := by
      intro hz
      obtain ⟨b, hb⟩ := integral_traceZero_is_artinSchreier F P g hint hz
      apply hf
      refine ⟨P.laurentEquiv (b + w), ?_⟩
      apply P.laurentEquiv.symm.injective
      simp only [← map_pow, ← map_add, RingEquiv.symm_apply_apply]
      have heq : (b + w) ^ 2 + (b + w) = f' := by
        rw [CharTwo.add_sq]
        calc
          _ = (b ^ 2 + b) + (w ^ 2 + w) := by abel
          _ = f' := by rw [hb]; dsimp [g]; rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      exact heq
    let u : ((ResidueField F)⸨X⸩)ˣ := Units.mk0 (single 1 1)
      (by simp)
    refine ⟨u, ?_⟩
    have hval : residueExponent g (u : (ResidueField F)⸨X⸩) = 1 := by
      rw [show (u : (ResidueField F)⸨X⸩) = single 1 1 from rfl,
        residueExponent_uniformizer]
      apply (ZMod.val_injective 2)
      have hlt := ZMod.val_lt (Algebra.trace (ZMod 2) (ResidueField F) (g.coeff 0))
      have hne : (Algebra.trace (ZMod 2) (ResidueField F) (g.coeff 0)).val ≠ 0 := by
        simpa using htrace
      rw [ZMod.val_one]
      omega
    rwa [residueExponent_add_artinSchreier f' w u u.ne_zero] at hval
  · obtain ⟨u, hu⟩ := residueExponent_nontrivial_of_oddPole _ t ht hodd hpole
    exact ⟨u, by rwa [residueExponent_add_artinSchreier f' w u u.ne_zero] at hu⟩

/-- Norm triviality in the actual finite separable local extension. The chosen
Laurent coordinates are constructed by the accepted presentation theorem. -/
theorem residueExponent_norm (f : F) (z : E)
    (hz : z ^ 2 + z = algebraMap F E f) (v : Eˣ) :
    let P := Classical.choice (Residues.exists_equalCharacteristicExtensionPresentation
      F E (equalCharacteristicTwo F))
    residueExponent (P.base.laurentEquiv.symm f)
      (P.base.laurentEquiv.symm (Algebra.norm F (v : E))) = 0 := by
  letI : CharP E 2 := charP_of_injective_algebraMap (algebraMap F E).injective 2
  letI : Module.Free (ResidueField F) (ResidueField E) :=
    Module.Free.of_divisionRing _ _
  let hc := equalCharacteristicTwo F
  let P := Classical.choice (Residues.exists_equalCharacteristicExtensionPresentation F E hc)
  let q := logarithmicDerivative (P.extension.laurentEquiv.symm (v : E))
  have hscalar : Residues.differentialTrace F E hc
      (P.extension.laurentEquiv.symm (algebraMap F E f) * q) =
      P.base.laurentEquiv.symm f * Residues.differentialTrace F E hc q := by
    dsimp only [Residues.differentialTrace]
    rw [mul_div_assoc, map_mul, RingEquiv.apply_symm_apply,
      ← Algebra.smul_def, map_smul, Algebra.smul_def, map_mul,
      Algebra.algebraMap_self_apply]
  have hnorm : logarithmicDerivative (P.base.laurentEquiv.symm
      (Algebra.norm F (v : E))) = Residues.differentialTrace F E hc q := by
    simpa only [q, logarithmicDerivative, div_eq_mul_inv, mul_comm] using
      Residues.logNorm F E hc v
  change Algebra.trace (ZMod 2) (ResidueField F)
    (Residues.residue (P.base.laurentEquiv.symm f *
      logarithmicDerivative (P.base.laurentEquiv.symm (Algebra.norm F (v : E))))) = 0
  rw [hnorm, ← hscalar, ← Residues.traceCompatibility]
  rw [Algebra.trace_trace (R := ZMod 2) (S := ResidueField F) (T := ResidueField E)]
  rw [← hz, map_add, map_pow]
  exact residueExponent_artinSchreier (P.extension.laurentEquiv.symm z)
    (P.extension.laurentEquiv.symm (v : E))
    ((map_ne_zero P.extension.laurentEquiv.symm).mpr v.ne_zero)

/-- Transport of the residue sign along actual Laurent coordinates. -/
def actualResidueSymbol (P : Residues.EqualCharacteristicPresentation F) (f : F) :
    Fˣ →* ℂˣ :=
  (residueSymbol (P.laurentEquiv.symm f)).comp
    (Units.mapEquiv P.laurentEquiv.symm.toMulEquiv).toMonoidHom

@[simp] theorem actualResidueSymbol_apply (P : Residues.EqualCharacteristicPresentation F)
    (f : F) (u : Fˣ) :
    (actualResidueSymbol F P f u : ℂ) =
      (-1 : ℂ) ^ (residueExponent (P.laurentEquiv.symm f)
        (P.laurentEquiv.symm (u : F))).val := rfl


private theorem actualResidueSymbol_norm (f : F) (z : E)
    (hz : z ^ 2 + z = algebraMap F E f) (v : Eˣ) :
    let P := Classical.choice (Residues.exists_equalCharacteristicExtensionPresentation
      F E (equalCharacteristicTwo F))
    actualResidueSymbol F P.base f (normUnits F E v) = 1 := by
  let P := Classical.choice (Residues.exists_equalCharacteristicExtensionPresentation
    F E (equalCharacteristicTwo F))
  apply Units.ext
  change (-1 : ℂ) ^ (residueExponent (P.base.laurentEquiv.symm f)
    (P.base.laurentEquiv.symm (Algebra.norm F (v : E)))).val = 1
  rw [residueExponent_norm F E f z hz v]
  rfl

private theorem actualResidueSymbol_ne_one
    (P : Residues.EqualCharacteristicPresentation F) (f : F)
    (hf : ¬ ∃ w : F, w ^ 2 + w = f) : actualResidueSymbol F P f ≠ 1 := by
  obtain ⟨u, hu⟩ := residueExponent_nontrivial F P f hf
  intro heq
  have hv := DFunLike.congr_fun heq (Units.mapEquiv P.laurentEquiv.toMulEquiv u)
  have hval := congrArg (fun a : ℂˣ ↦ (a : ℂ)) hv
  rw [actualResidueSymbol_apply] at hval
  simp only [Units.coe_mapEquiv, MonoidHom.one_apply, Units.val_one] at hval
  change (-1 : ℂ) ^ (residueExponent (P.laurentEquiv.symm f)
    (P.laurentEquiv.symm (P.laurentEquiv (u : (ResidueField F)⸨X⸩)))).val = 1 at hval
  rw [RingEquiv.symm_apply_apply, hu, ZMod.val_one] at hval
  norm_num at hval

end ActualNorm

section QuadraticNorm
variable (F E : Type) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E]
  [Module.Finite F E] [IsGalois F E] [CharP F 2]

local instance : CharP (ResidueField F) 2 := residueField_charTwo F
local instance : Algebra (ZMod 2) (ResidueField F) := ZMod.algebra _ _

omit [CharP F 2] in
private theorem quadraticNormRange (hdegree : Module.finrank F E = 2) :
    IsOpen ((normUnits F E).range : Set Fˣ) ∧
      Nat.card (NormCharacter F E) = 2 := by
  letI : IsCyclic (E ≃ₐ[F] E) :=
    isCyclic_of_prime_card ((IsGalois.card_aut_eq_finrank F E).trans hdegree)
  letI : PrimeCyclicExtension F E :=
    ⟨inferInstance, inferInstance, by simpa only [hdegree] using Nat.prime_two⟩
  by_cases hunr : ramificationIndex F E = 1
  · exact ⟨unramifiedNormRange_isOpen F E hunr,
      (unramifiedNormCharacter_card F E hunr).trans hdegree⟩
  · let P := primeCyclicPreparation F E hunr
    exact ⟨ramifiedNormRange_isOpen F E P.ht P.hres P.piK P.hpiK P.hgen,
      (ramifiedNormCharacter_card F E P.ht P.hres P.piK P.hpiK P.hgen).trans hdegree⟩

/-- The residue formula constructs an actual continuous character trivial on norms.
Continuity follows by descent to the discrete quotient by the open norm group. -/
def constructedNormCharacter (hdegree : Module.finrank F E = 2)
    (f : F) (z : E) (hz : z ^ 2 + z = algebraMap F E f) : NormCharacter F E := by
  let P := Classical.choice (Residues.exists_equalCharacteristicExtensionPresentation
    F E (equalCharacteristicTwo F))
  let ρ : NormQuotient F E →* ℂˣ :=
    QuotientGroup.lift (normUnits F E).range (actualResidueSymbol F P.base f) (by
      rintro u ⟨v, rfl⟩
      exact actualResidueSymbol_norm F E f z hz v)
  let ρc := (normQuotientCharacterEquivMonoidHom F E
    (quadraticNormRange F E hdegree).1).symm ρ
  exact ρc.toNormCharacter F E

@[simp] theorem constructedNormCharacter_apply (hdegree : Module.finrank F E = 2)
    (f : F) (z : E) (hz : z ^ 2 + z = algebraMap F E f) (u : Fˣ) :
    let P := Classical.choice (Residues.exists_equalCharacteristicExtensionPresentation
      F E (equalCharacteristicTwo F))
    ((constructedNormCharacter F E hdegree f z hz).1 u : ℂ) =
      (-1 : ℂ) ^ (residueExponent (P.base.laurentEquiv.symm f)
        (P.base.laurentEquiv.symm (u : F))).val := rfl

private theorem constructedNormCharacter_nontrivial (hdegree : Module.finrank F E = 2)
    (f : F) (z : E) (hz : z ^ 2 + z = algebraMap F E f)
    (hgen : z ∉ Set.range (algebraMap F E)) :
    constructedNormCharacter F E hdegree f z hz ≠ 1 := by
  intro heq
  have hne := actualResidueSymbol_ne_one F
    (Classical.choice (Residues.exists_equalCharacteristicExtensionPresentation
      F E (equalCharacteristicTwo F))).base f (not_artinSchreier_of_generator F E f z hz hgen)
  apply hne
  ext u
  exact congrArg (fun μ : NormCharacter F E ↦ (μ.1 u : ℂ)) heq

omit [CharP F 2] in
private theorem quadraticNormCharacter_unique (hdegree : Module.finrank F E = 2)
    (μ ω : NormCharacter F E) (hμ : μ ≠ 1) (hω : ω ≠ 1) : μ = ω := by
  obtain ⟨ν, _hν, huniq⟩ :=
    (Nat.card_eq_two_iff' (1 : NormCharacter F E)).mp (quadraticNormRange F E hdegree).2
  exact (huniq μ hμ).trans (huniq ω hω).symm

/-- The exact conductor of the constructed character for a positive odd
largest pole. In particular this applies to every reduced ramified class. -/
theorem constructedNormCharacter_conductor (hdegree : Module.finrank F E = 2)
    (f : F) (z : E) (hz : z ^ 2 + z = algebraMap F E f)
    (t : ℕ) (ht : 0 < t) (hodd : Odd t)
    (hpole :
      ((Classical.choice (Residues.exists_equalCharacteristicExtensionPresentation
        F E (equalCharacteristicTwo F))).base.laurentEquiv.symm f).orderTop =
        ((-(t : ℤ) : ℤ) : WithTop ℤ)) :
    IsMultiplicativeConductor F (constructedNormCharacter F E hdegree f z hz).1 (t + 1) := by
  let P := Classical.choice (Residues.exists_equalCharacteristicExtensionPresentation
    F E (equalCharacteristicTwo F))
  let ω := constructedNormCharacter F E hdegree f z hz
  have hformula (u : Fˣ) : (ω.1 u : ℂ) =
      (-1 : ℂ) ^ (residueExponent (P.base.laurentEquiv.symm f)
        (P.base.laurentEquiv.symm (u : F))).val := rfl
  constructor
  · intro u hu
    apply Units.ext
    rw [hformula]
    have hdeep : ((t + 1 : ℕ) : WithTop ℤ) ≤
        (P.base.laurentEquiv.symm (u : F) - 1).orderTop := by
      have h := (mem_unitFiltration_succ_iff_ord F t u).mp hu
      have heq := P.base.laurentEquiv_order
        (P.base.laurentEquiv.symm (u : F) - 1)
      simp only [map_sub, map_one, RingEquiv.apply_symm_apply] at heq
      rw [← heq]
      exact_mod_cast h
    rw [residueExponent_deepUnit _ _ t hpole.ge hdeep]
    rfl
  · intro r hr
    by_contra hrt
    have hle : r ≤ t := by omega
    letI : Fintype (ResidueField F) := residueFieldFintype F
    obtain ⟨c, hc⟩ := exists_absoluteTraceTwo_mul_eq_one (ResidueField F)
      (HahnSeries.coeff_orderTop_ne hpole)
    let v : ((ResidueField F)⸨X⸩)ˣ := Units.mk0 (1 + single (t : ℤ) c) (by
      intro hz
      have h := congrArg (fun x : (ResidueField F)⸨X⸩ ↦ x.coeff 0) hz
      simp [HahnSeries.coeff_single_of_ne (show (0 : ℤ) ≠ t by omega)] at h)
    let u := Units.mapEquiv P.base.laurentEquiv.toMulEquiv v
    have hu : u ∈ unitFiltration F t := by
      have hpos : t = (t - 1) + 1 := by omega
      rw [hpos, mem_unitFiltration_succ_iff_ord]
      have heq : (u : F) - 1 = P.base.laurentEquiv (single (t : ℤ) c) := by
        change P.base.laurentEquiv (1 + single (t : ℤ) c) - 1 = _
        rw [map_add, map_one, add_sub_cancel_left]
      rw [heq, P.base.laurentEquiv_order]
      simpa only [← hpos] using (single_order_bound (t : ℤ) c)
    have hval : (ω.1 u : ℂ) = -1 := by
      rw [hformula]
      change (-1 : ℂ) ^ (residueExponent (P.base.laurentEquiv.symm f)
        (P.base.laurentEquiv.symm (P.base.laurentEquiv (1 + single (t : ℤ) c)))).val = -1
      rw [RingEquiv.symm_apply_apply, residueExponent_lastLayer _ t ht hodd hpole.ge c, hc,
        ZMod.val_one, pow_one]
    have hone : ω.1 u = 1 := hr u (unitFiltration_antitone F hle hu)
    rw [hone] at hval
    norm_num at hval

/-- **Paper Lemma 11.2 (`D:EQ:ASsymbol`).** The Artin--Schreier residue formula
is the unique nontrivial continuous norm character of the actual quadratic
local extension. A reduced class with positive largest pole `t` has conductor
`t+1`; the stronger condition used here only requires that largest pole to be
odd, and allows arbitrary terms above it.

All Laurent coordinates are constructed from the genuine local extension.
The hypotheses say that `z` is a nontrivial Artin--Schreier generator; no norm
character, residue model, or stationary data is assumed. -/
theorem normCharacter (hdegree : Module.finrank F E = 2)
    (f : F) (z : E) (hz : z ^ 2 + z = algebraMap F E f)
    (hgen : z ∉ Set.range (algebraMap F E)) :
    let P := Classical.choice (Residues.exists_equalCharacteristicExtensionPresentation
      F E (equalCharacteristicTwo F))
    ∃ ω : NormCharacter F E,
      ω ≠ 1 ∧
      (∀ μ : NormCharacter F E, μ ≠ 1 → μ = ω) ∧
      (∀ u : Fˣ, (ω.1 u : ℂ) =
        (-1 : ℂ) ^ (residueExponent (P.base.laurentEquiv.symm f)
          (P.base.laurentEquiv.symm (u : F))).val) ∧
      (∀ t : ℕ, 0 < t → Odd t →
        (P.base.laurentEquiv.symm f).orderTop = ((-(t : ℤ) : ℤ) : WithTop ℤ) →
        IsMultiplicativeConductor F ω.1 (t + 1)) := by
  let ω := constructedNormCharacter F E hdegree f z hz
  have hω : ω ≠ 1 := constructedNormCharacter_nontrivial F E hdegree f z hz hgen
  refine ⟨ω, hω, ?_, ?_, ?_⟩
  · intro μ hμ
    exact quadraticNormCharacter_unique F E hdegree μ ω hμ hω
  · intro u
    exact constructedNormCharacter_apply F E hdegree f z hz u
  · intro t ht hodd hpole
    exact constructedNormCharacter_conductor F E hdegree f z hz t ht hodd hpole

end QuadraticNorm

end
end LanglandsSecondMainLemma.EqualChar
