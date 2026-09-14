import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsFirstMainLemma.Ramification.NormBelowBreak
import LanglandsSecondMainLemma.Dyadic.Equal.MinimalFunctions
import LanglandsSecondMainLemma.Finite.MissingCoset

/-!
# The one-break minimal row

Paper Proposition 11.10, `D:EQ:min-one`, with the ambient setup of
`D:EQ:canonicalpsi` and the constructed origin of `D:EQ:min-origin`.

The scalar lemmas derive `eta = c⁻¹` and `u² = c*d*e` from the whole lower
critical norm image. The field lemmas prove this calibration for the actual
lower character and construct the full upper Hasse function and its polar.
The comparison works directly on the actual critical graded norm maps:
`gⱼ(C)/C` has norm one on side `j` and nonzero image on side `i`. The full
common-function identity determines both its value and the polar character
on the entire norm image. Only then is the shared missing-coset lemma used.

`equalBreaks` constructs all intermediate data from the primitive compatible
minimal family. Its conclusion uses FML's canonical `localConstant` and the
complete lower norm-character product at the paper's canonical additive
character. No unitarity or stationary-model assumption is imposed.
-/

namespace LanglandsSecondMainLemma.Dyadic.Equal.OneBreakResidue
open LanglandsFirstMainLemma
open scoped BigOperators
noncomputable section
variable (k : Type*) [Field k] [Fintype k] [CharP k 2]
local instance : Algebra (ZMod 2) k := ZMod.algebra k 2

def traceSign : AddChar k ℂˣ where
  toFun x := Units.mk0 (absoluteTraceChar k x) (by
    rw [absoluteTraceChar_apply]
    exact pow_ne_zero _ (by norm_num))
  map_zero_eq_one' := by apply Units.ext; exact AddChar.map_zero_eq_one _
  map_add_eq_mul' x y := by apply Units.ext; exact AddChar.map_add_eq_mul _ x y

omit [Fintype k] in
@[simp] theorem traceSign_coe (x : k) :
    (traceSign k x : ℂ) = absoluteTraceChar k x := rfl

omit [Fintype k] in
theorem traceSign_eq_one_iff (x : k) :
    traceSign k x = 1 ↔ absoluteTraceTwo k x = 0 := by
  have hx : absoluteTraceTwo k x = 0 ∨ absoluteTraceTwo k x = 1 := by
    have htwo : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    exact htwo _
  rcases hx with hx | hx <;>
    norm_num [Units.ext_iff, traceSign_coe, absoluteTraceChar_apply, hx, ZMod.val_one]

omit [Fintype k] in
theorem traceSign_eq_neg_one {x : k} (hx : absoluteTraceTwo k x ≠ 0) :
    traceSign k x = -1 := by
  have hx' : absoluteTraceTwo k x = 1 :=
    (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) _ |>.resolve_left hx
  apply Units.ext
  norm_num [traceSign_coe, absoluteTraceChar_apply, hx', ZMod.val_one]

/-- `D:EQ:onecalibration`, from triviality on every lower critical norm. -/
theorem lower_calibration {c eta : k} (hc : c ≠ 0)
    (hnorm : ∀ z : k, absoluteTraceTwo k (c ^ 2 * (z ^ 2 + eta * z)) = 0) :
    eta = c⁻¹ := by
  have hann (z : k) : absoluteTraceTwo k ((c + c ^ 2 * eta) * z) = 0 := by
    calc
      _ = absoluteTraceTwo k (c * z) + absoluteTraceTwo k (c ^ 2 * eta * z) := by
        rw [add_mul, map_add]
      _ = absoluteTraceTwo k ((c * z) ^ 2) +
          absoluteTraceTwo k (c ^ 2 * eta * z) := by rw [absoluteTraceTwo_sq]
      _ = absoluteTraceTwo k (c ^ 2 * (z ^ 2 + eta * z)) := by
        rw [← map_add]
        congr 1
        ring
      _ = 0 := hnorm z
  have hsum : c + c ^ 2 * eta = 0 := by
    by_contra h
    obtain ⟨z, hz⟩ := exists_absoluteTraceTwo_mul_eq_one k h
    exact one_ne_zero (hz.symm.trans (hann z))
  have hfactor : c * (1 + c * eta) = 0 := by linear_combination hsum
  have hone : c * eta = 1 := by
    have h := (mul_eq_zero.mp hfactor).resolve_left hc
    simpa only [CharTwo.neg_eq] using (add_eq_zero_iff_eq_neg.mp h).symm
  apply (mul_left_cancel₀ hc)
  simpa only [mul_inv_cancel₀ hc] using hone

/-- The lower critical coefficient determines the leading unit, not only its valuation. -/
theorem leading_calibration {c kap u : k} (hc : c ≠ 0) (hu : u ≠ 0)
    (hnorm : ∀ z : k,
      absoluteTraceTwo k (c ^ 2 * (z ^ 2 + (kap / u ^ 2) * z)) = 0) :
    kap / u ^ 2 = c⁻¹ ∧ u ^ 2 = c * kap := by
  have h := lower_calibration k hc hnorm
  refine ⟨h, ?_⟩
  have he : kap = c⁻¹ * u ^ 2 := (div_eq_iff (pow_ne_zero _ hu)).mp h
  rw [he, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- The actual shape of a positive-break quadratic norm polynomial. -/
def normPolynomial (lambda : k) : k →+ k where
  toFun z := z ^ 2 + lambda * z
  map_zero' := by simp
  map_add' x y := by simp [add_sq, CharTwo.two_eq_zero, mul_add, add_assoc, add_left_comm]

omit [Fintype k] in
@[simp] theorem normPolynomial_apply (lambda z : k) :
    normPolynomial k lambda z = z ^ 2 + lambda * z := rfl

omit [Fintype k] in
theorem normPolynomial_eq_zero (lambda z : k) :
    normPolynomial k lambda z = 0 ↔ z = 0 ∨ z = lambda := by
  rw [normPolynomial_apply, show z ^ 2 + lambda * z = z * (z + lambda) by ring,
    mul_eq_zero, add_eq_zero_iff_eq_neg, CharTwo.neg_eq]

omit [Fintype k] in
theorem normPolynomial_kernel_card {lambda : k} (hlambda : lambda ≠ 0) :
    Nat.card (normPolynomial k lambda).ker = 2 := by
  classical
  have hs : ((normPolynomial k lambda).ker : Set k) = {0, lambda} := by
    ext z
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, normPolynomial_eq_zero,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  calc
    _ = Nat.card ↥({0, lambda} : Set k) := Nat.card_congr (Equiv.setCongr hs)
    _ = 2 := by simp [Nat.card_eq_fintype_card, Ne.symm hlambda]

theorem normPolynomial_range_index {lambda : k} (hlambda : lambda ≠ 0) :
    (normPolynomial k lambda).range.index = 2 := by
  rw [AddSubgroup.index_range]
  exact normPolynomial_kernel_card k hlambda

/-- FML's scaled Frobenius theorem, with the trace hyperplane written explicitly. -/
theorem normPolynomial_mem_range {lambda : k} (hlambda : lambda ≠ 0) (x : k) :
    x ∈ (normPolynomial k lambda).range ↔
      absoluteTraceTwo k (x / lambda ^ 2) = 0 := by
  have hrange := finiteField_scaledFrobeniusSub_range_eq_scaledTraceKer
    k 2 (ringChar.eq k 2) lambda hlambda
  have hrange' : Set.range (normPolynomial k lambda) =
      Set.range (fun y : (absoluteTraceTwo k).ker ↦ lambda ^ 2 * (y : k)) := by
    change Set.range (fun z : k ↦ z ^ 2 + lambda * z) = _
    simpa only [Nat.reduceSub, pow_one, CharTwo.sub_eq_add] using hrange
  change x ∈ Set.range (normPolynomial k lambda) ↔ _
  rw [hrange']
  constructor
  · rintro ⟨y, rfl⟩
    simpa only [mul_div_cancel_left₀ _ (pow_ne_zero _ hlambda)] using
      (show absoluteTraceTwo k (y : k) = 0 from y.property)
  · intro hx
    exact ⟨⟨x / lambda ^ 2, hx⟩, mul_div_cancel₀ x (pow_ne_zero _ hlambda)⟩

/-- The trace bicharacter of `D:EQ:onepolar`, with values in complex units. -/
def polar (kap : k) : AddChar k (AddChar k ℂˣ) where
  toFun x := (traceSign k).mulShift (kap * x)
  map_zero_eq_one' := by ext y; simp
  map_add_eq_mul' x y := by
    ext z
    simp only [AddChar.mulShift_apply, AddChar.mul_apply, mul_add, add_mul,
      AddChar.map_add_eq_mul]

omit [Fintype k] in
@[simp] theorem polar_apply (kap x y : k) :
    polar k kap x y = traceSign k (kap * x * y) := rfl

omit [Fintype k] in
/-- The translation is the other critical kernel vector's actual image.
Its full function value is obtained from the common function, including
its affine term. No value at this vector is assumed. -/
theorem translation {c d e u : k} (hu : u ≠ 0) (hcde : c + d = e)
    (H J Q : k → ℂˣ) (hJzero : J 0 = 1)
    (hH : ∀ z, H (normPolynomial k (c / u) z) = Q z)
    (hJ : ∀ z, J (normPolynomial k (d / u) z) = Q z) :
    normPolynomial k (c / u) (d / u) = d * e / u ^ 2 ∧
      d * e / u ^ 2 ∈ (normPolynomial k (c / u)).range ∧
      H (d * e / u ^ 2) = 1 := by
  have hp : normPolynomial k (c / u) (d / u) = d * e / u ^ 2 := by
    rw [normPolynomial_apply, ← hcde]
    field_simp
    ring
  refine ⟨hp, ⟨d / u, hp⟩, ?_⟩
  calc
    H (d * e / u ^ 2) = H (normPolynomial k (c / u) (d / u)) := congrArg H hp.symm
    _ = Q (d / u) := hH _
    _ = J (normPolynomial k (d / u) (d / u)) := (hJ _).symm
    _ = J 0 := by rw [(normPolynomial_eq_zero k _ _).2 (Or.inr rfl)]
    _ = 1 := hJzero

/-- The entire finite argument of `D:EQ:min-one` on one residue line.
The lower trace identity first calibrates the coefficients. The second
function then supplies a translation with value one, after which the
shared missing-coset lemma applies. -/
theorem sum_eq_half_common {c d e u : k}
    (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hu : u ≠ 0)
    (hcde : c + d = e)
    (hnorm : ∀ z : k,
      absoluteTraceTwo k (c ^ 2 * (z ^ 2 + (d * e / u ^ 2) * z)) = 0)
    (H J Q : k → ℂˣ) (hHzero : H 0 = 1) (hJzero : J 0 = 1)
    (hpolar : ∀ x y, H (x + y) = traceSign k (d * e * x * y) * H x * H y)
    (hH : ∀ z, H (normPolynomial k (c / u) z) = Q z)
    (hJ : ∀ z, J (normPolynomial k (d / u) z) = Q z) :
    (∑ x, (H x : ℂ)) = ((1 : ℂ) / 2) * ∑ z, (Q z : ℂ) := by
  have hcal := leading_calibration k hc hu hnorm
  obtain ⟨hp, hwmem, hw⟩ := translation k hu hcde H J Q hJzero hH hJ
  have hw0 : d * e / u ^ 2 ≠ 0 := div_ne_zero (mul_ne_zero hd he) (pow_ne_zero _ hu)
  have hlambda : c / u ≠ 0 := div_ne_zero hc hu
  have hcoeff (x : k) : d * e * (d * e / u ^ 2) * x = x / (c / u) ^ 2 := by
    rw [div_pow, div_div_eq_mul_div, hcal.2]
    field_simp
  apply Finite.missingCoset H (polar k (d * e)) Q (normPolynomial k (c / u))
    (d * e / u ^ 2) hHzero hpolar (normPolynomial_kernel_card k hlambda)
    (normPolynomial_range_index k hlambda) hH hwmem hw
  intro x
  rw [polar_apply, hcoeff]
  exact ⟨fun hx ↦ (traceSign_eq_one_iff k _).2 ((normPolynomial_mem_range k hlambda x).1 hx),
    fun hx ↦ traceSign_eq_neg_one k (fun ht ↦ hx ((normPolynomial_mem_range k hlambda x).2 ht))⟩

/-- A nontrivial character trivial on an index-two subgroup detects the
missing coset with its actual value `-1`. -/
theorem indexTwo_character {V : Type*} [AddCommGroup V]
    (S : AddSubgroup V) (hindex : S.index = 2)
    (chi : AddChar V ℂˣ) (hchi : chi ≠ 1)
    (hS : ∀ x ∈ S, chi x = 1) (x : V) :
    (x ∈ S → chi x = 1) ∧ (x ∉ S → chi x = -1) := by
  obtain ⟨a, ha, hcover⟩ := AddSubgroup.index_eq_two_iff_exists_notMem_and.mp hindex
  have hca : chi a ≠ 1 := by
    intro hca
    apply hchi
    apply DFunLike.ext
    intro b
    change chi b = 1
    rcases hcover b with hb | hb
    · have h := hS (b + a) hb
      simpa only [AddChar.map_add_eq_mul, hca, mul_one, AddChar.one_apply] using h
    · exact hS b hb
  have hsq : (chi a : ℂ) ^ 2 = 1 := by
    have h := congrArg (fun u : ℂˣ ↦ (u : ℂ)) (hS (a + a) ((hcover a).resolve_right ha))
    simpa only [AddChar.map_add_eq_mul, Units.val_mul, Units.val_one, pow_two] using h
  have ham : chi a = -1 := by
    apply Units.ext
    exact (sq_eq_one_iff.mp hsq).resolve_left (fun h ↦ hca (Units.ext h))
  refine ⟨hS x, fun hx ↦ ?_⟩
  have hh := hS (x + a) ((hcover x).resolve_right hx)
  rw [AddChar.map_add_eq_mul, ham] at hh
  have hval := congrArg (fun u : ℂˣ ↦ (u : ℂ)) hh
  apply Units.ext
  change (chi x : ℂ) = -1
  apply neg_eq_iff_eq_neg.mp
  simpa only [Units.val_mul, Units.val_neg, Units.val_one, mul_neg, mul_one] using hval

/-- The same missing-coset argument in intrinsic Hasse coordinates. The
translation is supplied by a common source class killed by the other norm
map. Its value and the polar annihilation on the image are derived from
the full common-function identity. -/
theorem hasse_sum_eq_half_common
    {k k' Z : Type*} [Field k] [Field k'] [Fintype k]
    [AddCommGroup Z] [Fintype Z]
    (psi : FiniteAddChar k) (hpsi : psi ≠ 1) (H : HasseFunction k psi)
    (J : k' → ℂ) (hJzero : J 0 = 1)
    (p : Z →+ k) (q : Z →+ k')
    (hker : Nat.card p.ker = 2) (hindex : p.range.index = 2)
    (hcommon : ∀ z, H (p z) = J (q z))
    (a : Z) (ha : q a = 0) (hpa : p a ≠ 0) :
    (∑ x, H x) = ((1 : ℂ) / 2) * ∑ z, H (p z) := by
  let Hunit : k → ℂˣ := fun x ↦ Units.mk0 (H x) (H.ne_zero x)
  let chi : AddChar k ℂˣ := {
    toFun := fun x ↦ Units.mk0 (psi x) (AddChar.val_isUnit psi x).ne_zero
    map_zero_eq_one' := by apply Units.ext; exact AddChar.map_zero_eq_one _
    map_add_eq_mul' := by intro x y; apply Units.ext; exact AddChar.map_add_eq_mul _ x y }
  let B : AddChar k (AddChar k ℂˣ) := {
    toFun := fun x ↦ chi.mulShift x
    map_zero_eq_one' := by ext y; simp
    map_add_eq_mul' := by intro x y; ext z; simp [add_mul, AddChar.map_add_eq_mul] }
  have hw : H (p a) = 1 := by rw [hcommon, ha, hJzero]
  have hpolar : ∀ x y, Hunit (x + y) = B x y * Hunit x * Hunit y := by
    intro x y
    apply Units.ext
    change H (x + y) = psi (x * y) * H x * H y
    rw [H.map_add]
    ring
  have hann : ∀ x ∈ p.range, B (p a) x = 1 := by
    rintro x ⟨z, rfl⟩
    have hshift : H (p a + p z) = H (p z) := by
      rw [← map_add, hcommon, map_add, ha, zero_add, ← hcommon]
    apply Units.ext
    change psi (p a * p z) = 1
    apply mul_left_cancel₀ (H.ne_zero (p z))
    calc
      H (p z) * psi (p a * p z) = H (p a + p z) := by rw [H.map_add, hw, one_mul]
      _ = H (p z) := hshift
      _ = H (p z) * 1 := (mul_one _).symm
  have hnontrivial : B (p a) ≠ 1 := by
    intro h
    apply hpsi
    apply DFunLike.ext
    intro x
    change psi x = 1
    have hh := congrArg (fun u : ℂˣ ↦ (u : ℂ)) (DFunLike.congr_fun h (x / p a))
    change psi (p a * (x / p a)) = 1 at hh
    simpa only [mul_div_cancel₀ _ hpa] using hh
  have he := Finite.missingCoset Hunit B (fun z ↦ Hunit (p z)) p (p a)
    (Units.ext H.map_zero) hpolar hker hindex (fun _ ↦ rfl)
    ⟨a, rfl⟩ (Units.ext hw)
    (indexTwo_character p.range hindex (B (p a)) hnontrivial hann)
  exact he

end
end LanglandsSecondMainLemma.Dyadic.Equal.OneBreakResidue

namespace LanglandsSecondMainLemma.Dyadic.Equal
open LanglandsFirstMainLemma
open scoped BigOperators
noncomputable section
open private scale_one from LanglandsSecondMainLemma.Dyadic.Equal.MinimalFunctions
open private phase_eq_of_sub_mem from LanglandsSecondMainLemma.Dyadic.Equal.MinimalOrigin
open private residueField_charTwo from LanglandsSecondMainLemma.EqualChar.NormCharacter

section LastLayer
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharP F 2]
local instance : CharP (ResidueField F) 2 := residueField_charTwo F
local instance : Fintype (ResidueField F) := residueFieldFintype F
local instance : Algebra (ZMod 2) (ResidueField F) := ZMod.algebra _ 2

/-- Evaluate the canonical additive character on a last-layer monomial. -/
theorem originAddChar_lastMonomial
    (P : Residues.EqualCharacteristicPresentation F) (t : ℕ) (z : ResidueField F) :
    originAddChar F P ((t : ℤ) + 1)
      ((P.uniformizer : F) ^ t * (teichmuller F z : F)) =
      OneBreakResidue.traceSign (ResidueField F) z := by
  have hsingle : P.laurentEquiv (HahnSeries.single (t : ℤ) z) =
      (P.uniformizer : F) ^ t * (teichmuller F z : F) := by
    have he : (HahnSeries.single (t : ℤ) z : LaurentSeries (ResidueField F)) =
        (HahnSeries.single 1 1) ^ t * HahnSeries.C z := by
      simp [HahnSeries.single_pow, HahnSeries.C_apply, HahnSeries.single_mul_single]
    rw [he, map_mul, map_pow, P.laurentEquiv_X, P.laurentEquiv_C,
      P.coefficient_eq_teichmuller]
  rw [← hsingle]
  apply Units.ext
  rw [originAddChar_apply, RingEquiv.symm_apply_apply, OneBreakResidue.traceSign_coe]
  simp only [scaledResiduePhase, HahnSeries.single_mul_single, one_mul,
    show -((t : ℤ) + 1) + t = -1 by omega,
    Residues.residue, HahnSeries.coeff_single_same]
  rfl

/-- The canonical last-layer character is the exact absolute-trace sign
of the normalized residue. The assertion holds for every element of the
whole ideal, including zero and elements in the next ideal. -/
theorem originAddChar_lastLayer
    (P : Residues.EqualCharacteristicPresentation F) (t : ℕ)
    (x : lattice F (t : ℤ)) :
    originAddChar F P ((t : ℤ) + 1) (x : F) =
      OneBreakResidue.traceSign (ResidueField F)
        (reduce F ((x : F) / (P.uniformizer : F) ^ t) (by
          apply (div_mem_lattice_iff F _ _ (t : ℤ) 0 (by
            rw [ord_pow, ord_uniformizer F P.uniformizer_isUniformizer]
            norm_num)).2
          simpa only [add_zero] using x.property)) := by
  have hp : ord F ((P.uniformizer : F) ^ t) = ((t : ℤ) : WithTop ℤ) := by
    rw [ord_pow, ord_uniformizer F P.uniformizer_isUniformizer]
    norm_num
  have hp0 : (P.uniformizer : F) ^ t ≠ 0 :=
    pow_ne_zero _ P.uniformizer_isUniformizer.ne_zero
  have hy : (x : F) / (P.uniformizer : F) ^ t ∈ lattice F 0 := by
    apply (div_mem_lattice_iff F _ _ (t : ℤ) 0 hp).2
    simpa only [add_zero] using x.property
  let z := reduce F ((x : F) / (P.uniformizer : F) ^ t) hy
  have hdiff : (x : F) / (P.uniformizer : F) ^ t - (teichmuller F z : F) ∈
      lattice F 1 := by
    apply (residueMap_eq_residueMap_iff F
      ⟨_, (mem_lattice_zero_iff F).1 hy⟩ (teichmuller F z)).1
    rw [residueMap_teichmuller]
    rfl
  have hmem : (x : F) - (P.uniformizer : F) ^ t * (teichmuller F z : F) ∈
      lattice F ((t : ℤ) + 1) := by
    have hh := mul_mem_lattice F hp.ge hdiff
    have he : (P.uniformizer : F) ^ t *
        ((x : F) / (P.uniformizer : F) ^ t - (teichmuller F z : F)) =
        (x : F) - (P.uniformizer : F) ^ t * (teichmuller F z : F) := by
      rw [mul_sub, mul_div_cancel₀ _ hp0]
    rwa [he] at hh
  exact (phase_eq_of_sub_mem (originAddChar F P ((t : ℤ) + 1))
    (originAddChar_conductor F P _) hmem).trans (originAddChar_lastMonomial F P t z)

end LastLayer

section LowerCriticalNorm
variable (F E : Type) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E] [CharP F 2]
local instance : CharP (ResidueField F) 2 := residueField_charTwo F
local instance : Fintype (ResidueField F) := residueFieldFintype F
local instance : Algebra (ZMod 2) (ResidueField F) := ZMod.algebra _ 2

/-- Extract the residue trace identity from an actual lower norm character.
Its whole stationary chart is evaluated on an actual norm unit. The
uniformizer is the retained norm uniformizer, as in `D:EQ:compatiblepi`.
No critical norm surjectivity is used. -/
theorem lowerCriticalNorm_trace
    (hdegree : Module.finrank F E = 2) {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
    (hres : residueDegree F E = 1) (pi : ringOfIntegers E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers E)) = ⊤)
    (P : Residues.EqualCharacteristicPresentation F)
    (hP : (P.uniformizer : F) = Algebra.norm F (pi : E))
    (W : ringOfIntegers F) (omega : NormCharacter F E) {r : ℤ} (hr : r ≤ t)
    (hchart : ∀ v : Fˣ, 1 - (v : F) ∈ lattice F r →
      omega.1 v = originAddChar F P ((t : ℤ) + 1) ((W : F) * (1 - (v : F))))
    (z : ResidueField F) :
    absoluteTraceTwo (ResidueField F)
      (residueMap F W * (z ^ 2 +
        criticalNormRamificationLambda F E ht hres pi hpi * z)) = 0 := by
  let U := criticalNormSourceUnit F E htpos pi hpi z
  let V := normUnits F E (U : Eˣ)
  have hV : V ∈ unitFiltration F t :=
    normMapsUnitFiltration_atBreak F E ht hres pi hpi hgen U U.property
  have hinc : (V : F) - 1 ∈ lattice F (t : ℤ) := by
    have hv' : V ∈ unitFiltration F (t - 1 + 1) := by
      simpa only [Nat.sub_add_cancel htpos] using hV
    simpa only [Nat.sub_add_cancel htpos] using
      (mem_unitFiltration_succ_iff_sub_mem_lattice F (t - 1) V).1 hv'
  have hnorm : omega.1 V = 1 := omega.eq_one_on_normRange F E V ⟨U, rfl⟩
  have hphase : originAddChar F P ((t : ℤ) + 1) ((W : F) * ((V : F) - 1)) = 1 := by
    have hh := hchart V (by
      simpa only [CharTwo.sub_eq_add, add_comm] using lattice_antitone F hr hinc)
    simpa only [CharTwo.sub_eq_add, add_comm] using hh.symm.trans hnorm
  have hx : (W : F) * ((V : F) - 1) ∈ lattice F (t : ℤ) := by
    simpa only [zero_add] using
      mul_mem_lattice F ((mem_lattice_zero_iff F).2 W.property) hinc
  have hp : ord F ((P.uniformizer : F) ^ t) = ((t : ℤ) : WithTop ℤ) := by
    rw [ord_pow, ord_uniformizer F P.uniformizer_isUniformizer]
    norm_num
  have hy : ((V : F) - 1) / (P.uniformizer : F) ^ t ∈ lattice F 0 := by
    apply (div_mem_lattice_iff F _ _ (t : ℤ) 0 hp).2
    simpa only [add_zero] using hinc
  have hraw : reduce F (((V : F) - 1) / (P.uniformizer : F) ^ t) hy =
      criticalNormPolynomialValue F E ht htpos hres pi hpi hgen z := by
    rw [criticalNormPolynomialValue_raw]
    simp only [V, U, coe_normUnits, coe_criticalNormSourceUnit, hP,
      criticalNormLowerUniformizer]
  have hmul : reduce F (((W : F) * ((V : F) - 1)) / (P.uniformizer : F) ^ t)
      ((div_mem_lattice_iff F _ _ (t : ℤ) 0 hp).2 (by simpa only [add_zero] using hx)) =
      residueMap F W * criticalNormPolynomialValue F E ht htpos hres pi hpi hgen z := by
    rw [← hraw]
    change residueMap F ⟨_, _⟩ = residueMap F W * residueMap F ⟨_, _⟩
    rw [← map_mul]
    congr 1
    ext
    exact mul_div_assoc _ _ _
  have hlast := originAddChar_lastLayer F P t ⟨_, hx⟩
  change originAddChar F P ((t : ℤ) + 1) ((W : F) * ((V : F) - 1)) = _ at hlast
  rw [hphase, hmul, criticalNormPolynomialValue_exact_of_positiveBreak, hdegree] at hlast
  simp only [Nat.reduceSub, pow_one, CharTwo.sub_eq_add] at hlast
  exact (OneBreakResidue.traceSign_eq_one_iff (ResidueField F) _).1 hlast.symm

/-- Construct the nonzero coefficient whose square is the residue of the
actual lower stationary coefficient, and calibrate the critical norm map
against it. This is the lower-character step of `D:EQ:onecalibration`. -/
theorem lowerCriticalNorm_calibration
    (hdegree : Module.finrank F E = 2) {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
    (hres : residueDegree F E = 1) (pi : ringOfIntegers E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers E)) = ⊤)
    (P : Residues.EqualCharacteristicPresentation F)
    (hP : (P.uniformizer : F) = Algebra.norm F (pi : E))
    (W : ringOfIntegers F) (hW : ord F (W : F) = 0)
    (omega : NormCharacter F E) {r : ℤ} (hr : r ≤ t)
    (hchart : ∀ v : Fˣ, 1 - (v : F) ∈ lattice F r →
      omega.1 v = originAddChar F P ((t : ℤ) + 1) ((W : F) * (1 - (v : F)))) :
    ∃ c : ResidueField F, c ≠ 0 ∧ c ^ 2 = residueMap F W ∧
      criticalNormRamificationLambda F E ht hres pi hpi = c⁻¹ := by
  obtain ⟨c, hc, _⟩ := existsUnique_squareRoot (ResidueField F) (residueMap F W)
  have hb : residueMap F W ≠ 0 := by
    intro hb
    have hh : (1 : WithTop ℤ) ≤ ord F (W : F) := (residueMap_eq_zero_iff F W).1 hb
    rw [hW] at hh
    exact (not_le_of_gt (show (0 : WithTop ℤ) < 1 by decide)) hh
  have hc0 : c ≠ 0 := by rintro rfl; exact hb (by simpa using hc.symm)
  refine ⟨c, hc0, hc, OneBreakResidue.lower_calibration (ResidueField F) hc0 ?_⟩
  intro z
  rw [hc]
  exact lowerCriticalNorm_trace F E hdegree ht htpos hres pi hpi hgen P hP W omega hr hchart z

end LowerCriticalNorm

section GradedNorm
variable (D E : Type) [Field D] [Field E]
  [ValuativeRel D] [TopologicalSpace D] [IsNonarchimedeanLocalField D]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra D E] [ValuativeExtension D E] [Module.Finite D E]
  [PrimeCyclicExtension D E]
local instance (t : ℕ) : AddCommGroup (Additive (UnitGradedPiece E t)) := inferInstance

/-- The actual critical norm map with the target in normalized residue
coordinates and the common source left as the actual unit graded group. -/
def criticalNormToResidue {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak D E t) (htpos : 0 < t)
    (hres : residueDegree D E = 1) (pi : ringOfIntegers E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E))
    (hgen : Algebra.adjoin (ringOfIntegers D) ({pi} : Set (ringOfIntegers E)) = ⊤) :
    Additive (UnitGradedPiece E t) →+ ResidueField D :=
  (criticalNormPositiveUnitGradedResidueAddEquiv D htpos
    (criticalNormLowerUniformizer D E pi)
    (criticalNormLowerUniformizer_isUniformizer D E hres pi hpi)).toAddMonoidHom.comp
    (criticalGradedNorm D E ht hres pi hpi hgen).toAdditive

/-- Zero in the residue target means membership in the actual next norm
layer; it is not a surjectivity assertion. -/
theorem criticalNormToResidue_zero_iff {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak D E t) (htpos : 0 < t)
    (hres : residueDegree D E = 1) (pi : ringOfIntegers E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E))
    (hgen : Algebra.adjoin (ringOfIntegers D) ({pi} : Set (ringOfIntegers E)) = ⊤)
    (U : unitFiltration E t) :
    criticalNormToResidue D E ht htpos hres pi hpi hgen
        (Additive.ofMul (unitGradedMk E t U)) = 0 ↔
      normUnits D E (U : Eˣ) ∈ unitFiltration D (t + 1) := by
  unfold criticalNormToResidue
  change (criticalNormPositiveUnitGradedResidueAddEquiv D htpos
    (criticalNormLowerUniformizer D E pi)
    (criticalNormLowerUniformizer_isUniformizer D E hres pi hpi))
      (Additive.ofMul (criticalGradedNorm D E ht hres pi hpi hgen (unitGradedMk E t U))) = 0 ↔ _
  rw [AddEquiv.map_eq_zero_iff]
  change criticalGradedNorm D E ht hres pi hpi hgen (unitGradedMk E t U) = 1 ↔ _
  rw [criticalGradedNorm_mk, unitGradedMk_eq_one_iff]
  rfl

/-- FML supplies the exact two-element kernel and index-two image for
this coordinate of the actual quadratic critical norm map. -/
theorem criticalNormToResidue_card (hdegree : Module.finrank D E = 2) {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak D E t) (htpos : 0 < t)
    (hres : residueDegree D E = 1) (pi : ringOfIntegers E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E))
    (hgen : Algebra.adjoin (ringOfIntegers D) ({pi} : Set (ringOfIntegers E)) = ⊤) :
    Nat.card (criticalNormToResidue D E ht htpos hres pi hpi hgen).ker = 2 ∧
      (criticalNormToResidue D E ht htpos hres pi hpi hgen).range.index = 2 := by
  let f := criticalGradedNorm D E ht hres pi hpi hgen
  let e := criticalNormPositiveUnitGradedResidueAddEquiv D htpos
    (criticalNormLowerUniformizer D E pi)
    (criticalNormLowerUniformizer_isUniformizer D E hres pi hpi)
  let p := criticalNormToResidue D E ht htpos hres pi hpi hgen
  have hk : p.ker = f.toAdditive.ker :=
    AddMonoidHom.ker_comp_of_injective f.toAdditive e.toAddMonoidHom e.injective
  have hcard : Nat.card p.ker = 2 := by
    rw [hk]
    calc
      Nat.card f.toAdditive.ker = Nat.card f.ker := Nat.card_congr {
        toFun := fun x ↦ ⟨x.1.toMul, x.2⟩
        invFun := fun x ↦ ⟨Additive.ofMul x.1, x.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
      _ = 2 := (criticalGradedNorm_kernel_card D E ht hres pi hpi hgen).trans hdegree
  refine ⟨hcard, ?_⟩
  have hsource : Nat.card (Additive (UnitGradedPiece E t)) = Nat.card (ResidueField D) := by
    change Nat.card (UnitGradedPiece E t) = _
    exact (unitGradedPiece_card_eq_of_residueDegree_eq_one D E t hres).trans
      (Nat.card_congr e.toEquiv)
  have hrange := p.range.card_mul_index
  have hkernel := p.ker.card_mul_index
  rw [AddSubgroup.index_ker, hcard] at hkernel
  rw [← hsource, ← hkernel] at hrange
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos : 0 < Nat.card p.range)
    (by simpa only [Nat.mul_comm] using hrange)

end GradedNorm

/-- Extend the quadratic exact trace shell to the negative odd break order.
All exponents remain integers: a base-field scaling makes the source depth
nonnegative before applying FML's shell theorem. -/
private theorem trace_order_neg_break
    (D E : Type) [Field D] [Field E]
    [ValuativeRel D] [TopologicalSpace D] [IsNonarchimedeanLocalField D]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra D E] [ValuativeExtension D E] [Module.Finite D E] [IsGalois D E]
    (hdegree : Module.finrank D E = 2) (hres : residueDegree D E = 1)
    (t : ℕ) (hdiff : differentExponent D E = t + 1)
    (x : E) (hx : ord E x = ((-(t : ℤ) : ℤ) : WithTop ℤ)) :
    ord D (Algebra.trace D E x) = 0 := by
  have hram : ramificationIndex D E = 2 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree D E
    rw [hdegree, hres, mul_one] at h
    exact h.symm
  obtain ⟨b, hb⟩ := exists_ord_eq D (t : ℤ)
  have hb0 : b ≠ 0 := (ord_ne_top_iff D).1 (by rw [hb]; exact WithTop.coe_ne_top)
  let y := algebraMap D E b * x
  have hy : ord E y = ((t : ℤ) : WithTop ℤ) := by
    rw [ord_mul, ord_algebraMap, hram, hb, hx, ← WithTop.coe_nsmul, ← WithTop.coe_add]
    congr 1
    simp only [nsmul_eq_mul]
    ring
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer D E hres
  have ht := (quadratic_trace_shell_iff D E pi hpi hgen (by positivity)
    hram hdegree (show (t : ℤ) + differentExponent D E = 2 * (t : ℤ) + 1 by
      rw [hdiff]; push_cast; ring) y hy.ge).2 hy
  have he : Algebra.trace D E y = b * Algebra.trace D E x := by
    change Algebra.trace D E (algebraMap D E b * x) = _
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have he' : Algebra.trace D E x = Algebra.trace D E y / b := by
    rw [he, mul_div_cancel_left₀ _ hb0]
  rw [he', ord_div, ht, hb, ← WithTop.LinearOrderedAddCommGroup.coe_sub, sub_self]
  rfl

/-- Identify the complete odd residual factor with a sum of the full
function in any actual terminal coordinate. The equality of coordinate
choices follows from the two proved Lamprecht formulas. -/
theorem completeResidualFactor_eq_sum
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E) (Z : Eˣ)
    (d : ℕ) (hm : theta.conductor = 2 * d + 1) (hlarge : 1 < theta.conductor)
    (hZ : ord E (Z : E) = ((-psi.conductor - (theta.conductor : ℤ) : ℤ) : WithTop ℤ))
    (hs : Stationary.IsNormalizedStationaryCoefficientAtDepth E theta psi Z (d + 1) (by omega))
    (delta : Eˣ) (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (H : ResidueField E → ℂ)
    (hH : ∀ v : lattice E (d : ℤ),
      H (reduce E ((v : E) / (delta : E)) (by
        apply (div_mem_lattice_iff E _ _ (d : ℤ) 0 hdelta).2
        simpa only [add_zero] using v.property)) =
      Stationary.normalizedCriticalValue E theta psi Z d (by omega) v) :
    letI := residueFieldFintype E
    Stationary.completeNormalizedResidualFactor E theta psi 1 Z hlarge =
      (Real.sqrt (residueCard E : ℝ) : ℂ)⁻¹ * ∑ x, H x := by
  letI := residueFieldFintype E
  have hZ' : ord E (Z : E) =
      ((-(scaleAddCharData E psi 1).conductor - (theta.conductor : ℤ) : ℤ) : WithTop ℤ) := by
    simpa only [scale_one] using hZ
  have hs' : Stationary.IsNormalizedStationaryCoefficientAtDepth E theta
      (scaleAddCharData E psi 1) Z (d + 1) (by omega) := by
    simpa only [scale_one] using hs
  have hord : Stationary.IsOrdinaryStationaryCoefficient E theta (scaleAddCharData E psi 1) Z
      hlarge := by
    refine ⟨hZ', ?_⟩
    have he : theta.conductor / 2 + theta.conductor % 2 = d + 1 := by omega
    simpa only [he] using hs'
  have hcomplete := Stationary.completeNormalizedFactor E theta psi 1 Z hlarge hord
  have hnormal := (Stationary.normalizedFactor E theta psi 1 Z d 1 (by omega)
    hm hlarge hZ' hs').2 rfl delta hdelta
  have hfactor : Stationary.completeNormalizedResidualFactor E theta psi 1 Z hlarge =
      Stationary.normalizedResidualFactor E theta psi 1 Z d hm hlarge delta hdelta := by
    exact mul_left_cancel₀ (mul_ne_zero
      (ContinuousQuasiChar.apply_ne_zero theta.character _)
      (ContinuousAddChar.apply_ne_zero (scaleAddCharData E psi 1).character _))
      (hcomplete.symm.trans hnormal)
  rw [hfactor, Stationary.normalizedResidualFactor]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  let v : lattice E (d : ℤ) := ⟨(delta : E) * (teichmuller E x : E), by
    simpa only [add_zero] using mul_mem_lattice E hdelta.ge
      ((mem_lattice_zero_iff E).2 (teichmuller E x).property)⟩
  have hv : reduce E ((v : E) / (delta : E))
      ((div_mem_lattice_iff E _ _ (d : ℤ) 0 hdelta).2
        (by simpa only [add_zero] using v.property)) = x := by
    change residueMap E ⟨_, _⟩ = x
    rw [show (⟨(v : E) / (delta : E), _⟩ : ringOfIntegers E) = teichmuller E x by
      ext; exact mul_div_cancel_left₀ _ (Units.ne_zero delta)]
    exact residueMap_teichmuller E x
  have hunit : (lamprechtHasseUnit E theta d hm hlarge delta hdelta
      (teichmuller E x : E) ((mem_lattice_zero_iff E).2 (teichmuller E x).property) : Eˣ) =
      positiveUnitOfLattice E (by omega : 0 < d) v := by
    apply Units.ext
    rfl
  have hh := hH v
  rw [hv] at hh
  rw [hh]
  dsimp only [Stationary.normalizedResidualFunction, Stationary.normalizedCriticalValue]
  rw [hunit, scale_one]
  congr 2
  congr 1
  change -(Z : E) * (delta : E) * (teichmuller E x : E) =
    -(Z : E) * ((delta : E) * (teichmuller E x : E))
  ring

section Scaling
variable (F E : Type) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E] [Algebra.IsSeparable F E]

private theorem canonicalLocalConstant_scale (chi : ContinuousQuasiChar E)
    (psi : LocalAddCharData E) (alpha : Eˣ) :
    localConstant E chi (scaleAddCharData E psi alpha).character =
      (chi alpha : ℂ) * localConstant E chi psi.character := by
  let chiD := canonicalLocalQuasiCharData E chi
  let gamma : AdmissibleGamma E chiD psi := Classical.choice (AdmissibleGamma.exists_admissible)
  calc
    _ = deltaFinite chiD (scaleAddCharData E psi alpha)
        (scaleAdmissibleGamma E alpha gamma) :=
      (localConstant_isDeltaFinite E) chiD (scaleAddCharData E psi alpha)
        (scaleAdmissibleGamma E alpha gamma)
    _ = (chi alpha : ℂ) * deltaFinite chiD psi gamma :=
      deltaFinite_scale_at_scaleAdmissibleGamma E chiD psi alpha gamma
    _ = _ := congrArg ((chi alpha : ℂ) * ·)
      ((localConstant_isDeltaFinite E) chiD psi gamma).symm

private theorem canonicalLocalConstant_one (psi : LocalAddCharData F) :
    localConstant F 1 psi.character = 1 := by
  let gamma : AdmissibleGamma F (trivialQuasiCharData F) psi :=
    Classical.choice (AdmissibleGamma.exists_admissible)
  exact ((localConstant_isDeltaFinite F) (trivialQuasiCharData F) psi gamma).trans
    (delta_trivial_character F psi gamma)

/-- Additive scaling for the actual upper factor and its lower correction. -/
theorem quadraticPair_scale (theta : ContinuousQuasiChar E) (omega : ContinuousQuasiChar F)
    (psi : LocalAddCharData F) (alpha : Fˣ) :
    localConstant E theta (tracePullbackAddChar F E (scaleAddCharData F psi alpha).character) *
        localConstant F omega (scaleAddCharData F psi alpha).character =
      ((Characters.restrictQuasiChar F E theta * omega) alpha : ℂ) *
        (localConstant E theta (tracePullbackAddChar F E psi.character) *
          localConstant F omega psi.character) := by
  let psiE := canonicalLocalAddCharData E (tracePullbackAddChar F E psi.character)
    (Basic.tracePullbackAddChar_ne_one F E psi.character psi.character_ne_one)
  have htrace : tracePullbackAddChar F E (scaleAddCharData F psi alpha).character =
      (scaleAddCharData E psiE (Units.map (algebraMap F E) alpha)).character := by
    ext x
    change (psi.character ((alpha : F) * Algebra.trace F E x) : ℂ) =
      (psi.character (Algebra.trace F E (algebraMap F E (alpha : F) * x)) : ℂ)
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [htrace, canonicalLocalConstant_scale, canonicalLocalConstant_scale]
  change (theta (Units.map (algebraMap F E) alpha) : ℂ) * _ * ((omega alpha : ℂ) * _) =
    ((theta (Units.map (algebraMap F E) alpha) * omega alpha : ℂˣ) : ℂ) * _
  dsimp only [psiE, canonicalLocalAddCharData]
  push_cast
  ring
end Scaling

section CanonicalCharacter
variable (F : Type) [Field F]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharP F 2]

def originCanonicalPsi (P : Residues.EqualCharacteristicPresentation F) : LocalAddCharData F :=
  ⟨originAddChar F P 0, 0, by simpa only [neg_zero] using originAddChar_conductor F P 0⟩

/-- The scale is the actual Laurent monomial, hence no chosen scalar or
additive-character normalization is assumed. -/
def originCanonicalScale (P : Residues.EqualCharacteristicPresentation F) (T : ℤ) : Fˣ :=
  Units.mk0 (P.laurentEquiv (HahnSeries.single (-T) 1))
    (by simpa only [map_ne_zero] using
      (HahnSeries.single_ne_zero (a := -T) (one_ne_zero : (1 : ResidueField F) ≠ 0)))

theorem originCanonicalPsi_scale (P : Residues.EqualCharacteristicPresentation F) (T : ℤ) :
    (scaleAddCharData F (originCanonicalPsi F P) (originCanonicalScale F P T)).character =
      originAddChar F P T := by
  ext x
  simp only [scaleAddCharData_character_apply, originCanonicalPsi, originAddChar_apply,
    originCanonicalScale, Units.val_mk0, map_mul, RingEquiv.symm_apply_apply,
    scaledResiduePhase, neg_zero, HahnSeries.single_zero_one, one_mul]
end CanonicalCharacter

section MinimalFamily
open private originLine_norm_trace from LanglandsSecondMainLemma.Dyadic.Equal.Origin
open private edge_ramification from LanglandsSecondMainLemma.Dyadic.Equal.Compatibility
open private trace_eq_self_add_nontrivial from LanglandsSecondMainLemma.Algebra.BiquadraticE2
open private terminal_ledger scale_one from LanglandsSecondMainLemma.Dyadic.Equal.MinimalFunctions
open private model_ledger from LanglandsSecondMainLemma.Dyadic.Equal.Models
open private normalizedStationaryNumerator normalizedStationaryNumerator_coe
  normalizedStationaryNumerator_represents from LanglandsSecondMainLemma.Stationary.NormalizedFactor
open private originLine_degrees origin_residueDegrees from
  LanglandsSecondMainLemma.Dyadic.Equal.Origin
open private lowerCyclic from LanglandsSecondMainLemma.Dyadic.Equal.Twist

variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]
  [CharP F 2] [CharP K 2] [IsKleinFour Gal(K/F)]

local instance (L : IntermediateField F K) : ValuativeRel L :=
  Basic.intermediateFieldValuativeRel L
local instance (L : IntermediateField F K) : TopologicalSpace L :=
  Basic.intermediateFieldTopology L
local instance (L : IntermediateField F K) : IsNonarchimedeanLocalField L :=
  Basic.intermediateField_localField L
local instance (L : IntermediateField F K) : ValuativeExtension F L :=
  Basic.intermediateField_lowerValuativeExtension L
local instance (L : IntermediateField F K) : ValuativeExtension L K :=
  Basic.intermediateField_upperValuativeExtension L
local instance (L : IntermediateField F K) : IsGalois F L := by
  letI : IsMulCommutative Gal(K/F) := IsKleinFour.isMulCommutative
  letI : L.fixingSubgroup.Normal := inferInstance
  have h := IsGalois.of_fixedField_normal_subgroup L.fixingSubgroup
  rwa [IsGalois.fixedField_fixingSubgroup L] at h
local instance : CharP (ResidueField F) 2 := residueField_charTwo F
local instance : Fintype (ResidueField F) := residueFieldFintype F

namespace SimultaneousASGenerators
variable {P : Residues.EqualCharacteristicPresentation F}
  (A : SimultaneousASGenerators F K P)

omit [IsGalois F K] [CharP F 2] [CharP K 2] in
/-- In the one-break row every retained lower break is the common break. -/
theorem oneBreak_eq (heq : A.t 0 = A.t 1) (i : Fin 3) : A.t i = A.t 1 := by
  fin_cases i
  · exact heq
  · rfl
  · exact A.third_break

/-- The actual lower coefficient `nᵢ Sᵢ C` is a unit in the one-break row.
This uses the exact upper trace shell and the lower norm valuation. -/
theorem minimalLowerCoefficient_order (hres : residueDegree F K = 1)
    (heq : A.t 0 = A.t 1) (C : K)
    (hC : ord K C = ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ)) (i : Fin 3) :
    ord F (Algebra.norm F (Algebra.trace (A.field i) K C)) = 0 := by
  change ord F (norm F (A.field i) (Algebra.trace (A.field i) K C)) = 0
  rw [ord_norm, (origin_residueDegrees F K hres (A.field i)).1, one_nsmul,
    A.minimalOrigin_trace_order hres C hC i, A.oneBreak_eq heq i]
  simp

/-- The residue of the actual lower stationary coefficient. -/
def minimalLowerCoefficientResidue (hres : residueDegree F K = 1)
    (heq : A.t 0 = A.t 1) (C : K)
    (hC : ord K C = ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ)) (i : Fin 3) : ResidueField F :=
  reduce F (Algebra.norm F (Algebra.trace (A.field i) K C))
    (by rw [mem_lattice, A.minimalLowerCoefficient_order hres heq C hC i]; rfl)

/-- Calibrate the critical polynomial of the actual lower edge from the
constructed minimal origin. Every nontrivial actual lower norm character
supplies the required chart; the coefficient is its literal trace norm.
The norm-uniformizer equality retains the paper's compatible choices. -/
theorem minimalLowerCriticalCalibration (hres : residueDegree F K = 1)
    (heq : A.t 0 = A.t 1)
    (theta : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (C : Kˣ) (hC : A.IsMinimalFunctionOrigin theta C) (i : Fin 3)
    (omega : NormCharacter F (A.field i)) (homega : omega ≠ 1)
    (pi : ringOfIntegers (A.field i))
    (hpi : (ValuativeRel.valuation (A.field i)).IsUniformizer (pi : A.field i))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers (A.field i))) = ⊤)
    (hP : (P.uniformizer : F) = Algebra.norm F (pi : A.field i)) :
    letI := lowerCyclic A i
    ∃ c : ResidueField F, c ≠ 0 ∧
      c ^ 2 = A.minimalLowerCoefficientResidue hres heq (C : K) hC.order i ∧
      criticalNormRamificationLambda F (A.field i) (A.edge i).2.2.2.2.2.2.2.1
        (origin_residueDegrees F K hres (A.field i)).1 pi hpi = c⁻¹ := by
  letI := lowerCyclic A i
  let W : ringOfIntegers F := ⟨Algebra.norm F (Algebra.trace (A.field i) K (C : K)),
    (mem_lattice_zero_iff F).1 (by
      rw [mem_lattice, A.minimalLowerCoefficient_order hres heq (C : K) hC.order i]
      rfl)⟩
  apply lowerCriticalNorm_calibration F (A.field i)
    (originLine_degrees F K (A.g i) (A.nontrivial i)).1
    (A.edge i).2.2.2.2.2.2.2.1 (A.edge i).2.2.2.1
    (origin_residueDegrees F K hres (A.field i)).1 pi hpi hgen P hP W
    (A.minimalLowerCoefficient_order hres heq (C : K) hC.order i) omega
    (r := A.lowerDepth i)
  · dsimp only [lowerDepth]
    have ht := (A.edge i).2.2.2.1
    omega
  · intro v hv
    have hh := hC.lower i (Or.inr heq) omega homega v hv
    simpa only [minimalBasePsi, A.oneBreak_eq heq i, W] using hh

/-- The complete upper stationary input to FML is derived from the constructed
minimal origin, including the exact order of its actual norm. -/
theorem minimalUpperStationary (hres : residueDegree F K = 1)
    (theta : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (C : Kˣ) (hC : A.IsMinimalFunctionOrigin theta C)
    (i : Fin 3) (hi : i ≠ 2 ∨ A.t 0 = A.t 1) :
    (canonicalLocalQuasiCharData (A.field i) (theta i)).conductor =
        2 * A.minimalTerminalDepth i + 1 ∧
      1 < (canonicalLocalQuasiCharData (A.field i) (theta i)).conductor ∧
      ord (A.field i) (normUnits (A.field i) K C : A.field i) =
        ((-(A.minimalUpperPsi hres i).conductor -
          ((canonicalLocalQuasiCharData (A.field i) (theta i)).conductor : ℤ) : ℤ) : WithTop ℤ) ∧
      Stationary.IsNormalizedStationaryCoefficientAtDepth (A.field i)
        (canonicalLocalQuasiCharData (A.field i) (theta i)) (A.minimalUpperPsi hres i)
        (normUnits (A.field i) K C) (A.minimalTerminalDepth i + 1) (by omega) := by
  have hm : (canonicalLocalQuasiCharData (A.field i) (theta i)).conductor =
      2 * A.minimalTerminalDepth i + 1 :=
    (hC.conductor i).trans (terminal_ledger A i).2.2.1
  refine ⟨hm, by have := (terminal_ledger A i).1; omega, ?_, ?_⟩
  · change ord (A.field i) (norm (A.field i) K (C : K)) =
      ((-(-A.additiveModulus i) -
        (multiplicativeConductorExponent (A.field i) (theta i) : ℤ) : ℤ) : WithTop ℤ)
    rw [ord_norm, (origin_residueDegrees F K hres (A.field i)).2, one_nsmul, hC.order,
      hC.conductor i, (model_ledger A i).2.2.2.1]
    congr 1
    ring
  · intro z
    have hz : 1 - ((positiveUnitOfLattice (A.field i) (by omega) (-z) : (A.field i)ˣ) :
        A.field i) = (z : A.field i) := by
      simp only [coe_positiveUnitOfLattice, Submodule.coe_neg]
      ring
    exact (hC.upper i hi _ (by
      rw [hz]
      simpa only [(terminal_ledger A i).2.1] using z.property)).trans (by rw [hz]; rfl)

/-- Construct the full residual Hasse function and its nontrivial polar
character. Both are evaluated on every integral lift, and the polar value
retains the actual upper norm coefficient. Thus this supplies functions,
not only an abstract quadratic form. -/
theorem minimalHasseFunction_exists (hres : residueDegree F K = 1)
    (theta : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (C : Kˣ) (hC : A.IsMinimalFunctionOrigin theta C)
    (i : Fin 3) (hi : i ≠ 2 ∨ A.t 0 = A.t 1)
    (delta : (A.field i)ˣ)
    (hdelta : ord (A.field i) (delta : A.field i) =
      ((A.minimalTerminalDepth i : ℤ) : WithTop ℤ)) :
    ∃ psi0 : FiniteAddChar (ResidueField (A.field i)), psi0 ≠ 1 ∧
      ∃ H : HasseFunction (ResidueField (A.field i)) psi0,
        (∀ v : lattice (A.field i) (A.minimalTerminalDepth i : ℤ),
          H (reduce (A.field i) ((v : A.field i) / (delta : A.field i)) (by
            apply (div_mem_lattice_iff (A.field i) _ _
              (A.minimalTerminalDepth i : ℤ) 0 hdelta).2
            simpa only [add_zero] using v.property)) =
            A.minimalFullFunction hres (theta i) C v) ∧
        (∀ z : lattice (A.field i) 0,
          psi0 (reduce (A.field i) (z : A.field i) z.property) =
            ((A.minimalUpperPsi hres i).character
              (Algebra.norm (A.field i) (C : K) * (delta : A.field i) ^ 2 *
                (z : A.field i)) : ℂ)) := by
  let L := A.field i
  let chi := canonicalLocalQuasiCharData L (theta i)
  let psi := A.minimalUpperPsi hres i
  let Z := normUnits L K C
  let d := A.minimalTerminalDepth i
  obtain ⟨hm, hlarge, hZ, hs⟩ := A.minimalUpperStationary hres theta C hC i hi
  have hZ' : ord L (Z : L) =
      ((-(scaleAddCharData L psi 1).conductor - (chi.conductor : ℤ) : ℤ) : WithTop ℤ) := by
    simpa only [scale_one] using hZ
  have hs' : Stationary.IsNormalizedStationaryCoefficientAtDepth L chi
      (scaleAddCharData L psi 1) Z (d + 1) (by omega) := by
    simpa only [scale_one] using hs
  let Gamma : AdmissibleGamma L chi psi := Classical.choice (AdmissibleGamma.exists_admissible)
  let c := normalizedStationaryNumerator L chi psi 1 Z Gamma hZ'
  have hc := normalizedStationaryNumerator_represents L chi psi 1 Z d 1
    (by omega) hm hlarge Gamma hZ' hs'
  let psi0 := lamprechtResidualAddChar L chi psi d hm hlarge Gamma delta hdelta
  let H := lamprechtHasseFunction L chi psi d hm hlarge Gamma delta hdelta c hc
  refine ⟨psi0, lamprechtResidualAddChar_ne_one L chi psi d hm hlarge Gamma delta hdelta c hc,
    H, ?_, ?_⟩
  · intro v
    let z : L := (v : L) / (delta : L)
    have hz : z ∈ lattice L 0 := by
      apply (div_mem_lattice_iff L _ _ (d : ℤ) 0 hdelta).2
      simpa only [add_zero] using v.property
    have hzv : (delta : L) * z = (v : L) := mul_div_cancel₀ _ (Units.ne_zero delta)
    have harg : (c : L) * (delta : L) * z / ((Gamma : Lˣ) : L) = -(Z : L) * (v : L) := by
      dsimp only [c]
      rw [normalizedStationaryNumerator_coe, Units.val_one]
      dsimp only [z]
      field_simp
    have hunit : (lamprechtHasseUnit L chi d hm hlarge delta hdelta z hz : Lˣ) =
        positiveUnitOfLattice L (terminal_ledger A i).1 v := by
      apply Units.ext
      change 1 + (delta : L) * z = 1 + (v : L)
      rw [hzv]
    change H (reduce L z hz) = _
    rw [show H = lamprechtHasseFunction L chi psi d hm hlarge Gamma delta hdelta c hc from rfl,
      lamprechtHasseFunction_integral_lift, lamprechtHasseValue, harg, hunit]
    rfl
  · intro z
    change lamprechtResidualAddChar L chi psi d hm hlarge Gamma delta hdelta
      (reduce L (z : L) z.property) = _
    rw [lamprechtResidualAddChar_integral_lift L chi psi d hm hlarge Gamma delta hdelta c hc]
    congr 2
    dsimp only [c]
    rw [normalizedStationaryNumerator_coe, Units.val_one, CharTwo.neg_eq, one_mul]
    change (Z : L) * ((Gamma : Lˣ) : L) * (delta : L) ^ 2 * (z : L) /
      ((Gamma : Lˣ) : L) = (Z : L) * (delta : L) ^ 2 * (z : L)
    field_simp

/-- An explicit common source unit: the quotient of a conjugate numerator
by the retained numerator. -/
def minimalConjugateQuotient (C : Kˣ) (j : Fin 3) : Kˣ :=
  Units.map (A.g j).toMonoidHom C / C

omit [IsGalois F K] [CharP F 2] [CharP K 2] in
/-- The source translation is an exact norm-one unit on side `j`. -/
theorem minimalConjugateQuotient_norm (C : Kˣ) (j : Fin 3) :
    normUnits (A.field j) K (A.minimalConjugateQuotient C j) = 1 := by
  let sigma : Gal(K/A.field j) :=
    { (A.g j).toRingEquiv with commutes' := fun x ↦
        (IntermediateField.mem_fixedField_iff _ _).mp x.property (A.g j) (Or.inr rfl) }
  have hn : normUnits (A.field j) K (Units.map (A.g j).toMonoidHom C) =
      normUnits (A.field j) K C := by
    apply Units.ext
    exact Algebra.norm_eq_of_algEquiv sigma (C : K)
  simp only [minimalConjugateQuotient, map_div, hn, div_self']

/-- The exact source depth of the conjugate quotient is the common break. -/
theorem minimalConjugateQuotient_order (hres : residueDegree F K = 1)
    (heq : A.t 0 = A.t 1) (C : Kˣ)
    (hC : ord K (C : K) = ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ)) (j : Fin 3) :
    ord K ((A.minimalConjugateQuotient C j : K) - 1) =
      ((A.t 1 : ℤ) : WithTop ℤ) := by
  have ht : ord (A.field j) (Algebra.trace (A.field j) K (C : K)) = 0 := by
    rw [A.minimalOrigin_trace_order hres (C : K) hC j, A.oneBreak_eq heq j]
    simp
  have he : (A.minimalConjugateQuotient C j : K) - 1 =
      algebraMap (A.field j) K (Algebra.trace (A.field j) K (C : K)) / (C : K) := by
    rw [(originLine_norm_trace F K (A.g j) (A.nontrivial j) (C : K)).2]
    simp only [minimalConjugateQuotient, Units.val_div_eq_div_val, Units.coe_map]
    change (A.g j (C : K)) / (C : K) - 1 = _
    rw [div_sub_one (Units.ne_zero C)]
    simp only [CharTwo.sub_eq_add, add_comm]
  rw [he, ord_div, ord_algebraMap, ht, nsmul_zero, hC, heq]
  norm_cast
  omega

/-- On a different side the translated norm is the lower conjugate quotient
of the actual upper norm. Its increment is exactly `Tr(aᵢ)/aᵢ`. -/
theorem minimalConjugateQuotient_norm_increment (C : Kˣ) (i j : Fin 3)
    (hji : A.g j ∉ originLine (A.g i)) :
    (normUnits (A.field i) K (A.minimalConjugateQuotient C j) : A.field i) - 1 =
      algebraMap F (A.field i) (Algebra.trace F (A.field i)
        (Algebra.norm (A.field i) (C : K))) / Algebra.norm (A.field i) (C : K) := by
  let L := A.field i
  let sigma : Gal(L/F) := AlgEquiv.restrictNormalHom L (A.g j)
  have hsigma : sigma ≠ 1 := by
    intro h
    have hh : A.g j ∈ (AlgEquiv.restrictNormalHom L).ker := h
    rw [IntermediateField.restrictNormalHom_ker, IntermediateField.fixingSubgroup_fixedField] at hh
    exact hji hh
  have hn : normUnits L K (Units.map (A.g j).toMonoidHom C) =
      Units.map sigma.toMonoidHom (normUnits L K C) := by
    apply Units.ext
    simp only [Units.coe_map]
    change Algebra.norm L (A.g j (C : K)) = sigma (Algebra.norm L (C : K))
    apply (algebraMap L K).injective
    rw [show algebraMap L K (sigma (Algebra.norm L (C : K))) =
      A.g j (algebraMap L K (Algebra.norm L (C : K))) from
        AlgEquiv.restrictNormal_commutes (A.g j) L _]
    rw [(originLine_norm_trace F K (A.g i) (A.nontrivial i) (A.g j (C : K))).1,
      (originLine_norm_trace F K (A.g i) (A.nontrivial i) (C : K)).1, map_mul]
    congr 1
    letI : IsMulCommutative Gal(K/F) := IsKleinFour.isMulCommutative
    exact DFunLike.congr_fun (mul_comm' (A.g i) (A.g j)) (C : K)

  have hcard : Fintype.card Gal(L/F) = 2 := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
    exact (originLine_degrees F K (A.g i) (A.nontrivial i)).1
  have ht := trace_eq_self_add_nontrivial sigma hsigma hcard (Algebra.norm L (C : K))
  rw [minimalConjugateQuotient, map_div, hn]
  simp only [Units.val_div_eq_div_val, Units.coe_map]
  change sigma (Algebra.norm L (C : K)) / Algebra.norm L (C : K) - 1 = _
  rw [div_sub_one (by exact Units.ne_zero (normUnits L K C)), ht]
  simp only [CharTwo.sub_eq_add, add_comm]
  rfl

/-- The translation is nonzero on the target's terminal graded line.
Its exact order follows from the actual lower trace shell, including the
negative order of the retained upper norm. -/
theorem minimalConjugateQuotient_norm_order (hres : residueDegree F K = 1)
    (heq : A.t 0 = A.t 1) (C : Kˣ)
    (hC : ord K (C : K) = ((-(A.t 0 : ℤ) : ℤ) : WithTop ℤ))
    (i j : Fin 3) (hji : A.g j ∉ originLine (A.g i)) :
    ord (A.field i) ((normUnits (A.field i) K (A.minimalConjugateQuotient C j) :
      A.field i) - 1) = ((A.t 1 : ℤ) : WithTop ℤ) := by
  let L := A.field i
  have hn : ord L (Algebra.norm L (C : K)) = ((-(A.t i : ℤ) : ℤ) : WithTop ℤ) := by
    change ord L (norm L K (C : K)) = _
    rw [ord_norm, (origin_residueDegrees F K hres L).2, one_nsmul, hC, heq, A.oneBreak_eq heq i]
  have ht := trace_order_neg_break F L (originLine_degrees F K (A.g i) (A.nontrivial i)).1
    (origin_residueDegrees F K hres L).1 (A.t i) (A.edge i).2.2.2.2.2.2.2.2
    (Algebra.norm L (C : K)) hn
  rw [A.minimalConjugateQuotient_norm_increment C i j hji, ord_div, ord_algebraMap, ht,
    nsmul_zero, hn, A.oneBreak_eq heq i]
  norm_cast
  omega

local instance (t : ℕ) : AddCommGroup (Additive (UnitGradedPiece K t)) := inferInstance
local instance (i : Fin 3) : Fintype (ResidueField (A.field i)) := residueFieldFintype _

omit [IsGalois F K] [CharP F 2] [CharP K 2] in
/-- The one-break terminal row is the critical norm row on all three sides. -/
theorem oneBreak_terminalDepth (heq : A.t 0 = A.t 1) (i : Fin 3) :
    A.minimalTerminalDepth i = A.t 1 := by
  obtain ⟨n, hn⟩ := (A.edge 1).2.2.2.2.1
  dsimp only [minimalTerminalDepth, stationaryDepth]
  split_ifs <;> omega

omit [CharP F 2] [CharP K 2] in
private theorem upperCyclic (i : Fin 3) : PrimeCyclicExtension (A.field i) K := by
  have hd := (originLine_degrees F K (A.g i) (A.nontrivial i)).2
  letI : IsCyclic Gal(K/A.field i) := isCyclic_of_prime_card
    ((IsGalois.card_aut_eq_finrank (A.field i) K).trans hd)
  exact ⟨inferInstance, inferInstance, by rw [hd]; exact Nat.prime_two⟩

/-- All data needed for the finite comparison, including its relation to
the full actual function and the complete normalized residual factor.
`minimalCriticalLine` constructs this record from the genuine origin. -/
structure MinimalCriticalLine (hres : residueDegree F K = 1) (heq : A.t 0 = A.t 1)
    (Theta : ContinuousQuasiChar K) (theta : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (C : Kˣ) (hC : A.IsMinimalFunctionOrigin theta C) (i : Fin 3) where
  psi0 : FiniteAddChar (ResidueField (A.field i))
  psi0_ne_one : psi0 ≠ 1
  hasse : HasseFunction (ResidueField (A.field i)) psi0
  normMap : Additive (UnitGradedPiece K (A.t 1)) →+ ResidueField (A.field i)
  kernel_card : Nat.card normMap.ker = 2
  range_index : normMap.range.index = 2
  norm_zero : ∀ U : unitFiltration K (A.t 1),
    normMap (Additive.ofMul (unitGradedMk K (A.t 1) U)) = 0 ↔
      normUnits (A.field i) K (U : Kˣ) ∈ unitFiltration (A.field i) (A.t 1 + 1)
  common : ∀ U : unitFiltration K (A.t 1),
    hasse (normMap (Additive.ofMul (unitGradedMk K (A.t 1) U))) =
      A.minimalCommonValue Theta C (U : Kˣ)
  residual : Stationary.completeNormalizedResidualFactor (A.field i)
      (canonicalLocalQuasiCharData (A.field i) (theta i)) (A.minimalUpperPsi hres i) 1
      (normUnits (A.field i) K C)
      (A.minimalUpperStationary hres theta C hC i (Or.inr heq)).2.1 =
    (Real.sqrt (residueCard (A.field i) : ℝ) : ℂ)⁻¹ * ∑ x, hasse x

/-- Construct the actual critical norm map and full Hasse function.
FML supplies its kernel, index, and residue coordinate; the accepted full
common-function identity supplies its values on every norm class. -/
def minimalCriticalLine (hres : residueDegree F K = 1) (heq : A.t 0 = A.t 1)
    (Theta : ContinuousQuasiChar K) (theta : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hcompatible : ∀ i, normQuasiChar (A.field i) K (theta i) = Theta)
    (C : Kˣ) (hC : A.IsMinimalFunctionOrigin theta C) (i : Fin 3) :
    A.MinimalCriticalLine hres heq Theta theta C hC i := by
  classical
  apply Classical.choice
  letI := upperCyclic A i
  let L := A.field i
  have hd := A.oneBreak_terminalDepth heq i
  have htpos : 0 < A.t 1 := (A.edge 1).2.2.2.1
  have ht : PrimeCyclicExtension.IsLowerBreak L K (A.t 1) := by
    simpa only [heq, Nat.sub_self, mul_zero, add_zero, ite_self] using A.upper_break i
  have hresL := (origin_residueDegrees F K hres L).2
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer L K hresL
  let Pi := criticalNormLowerUniformizer L K pi
  have hPi := criticalNormLowerUniformizer_isUniformizer L K hresL pi hpi
  let delta : Lˣ := Units.mk0 (Pi ^ A.t 1) (pow_ne_zero _ hPi.ne_zero)
  have hdelta : ord L (delta : L) = ((A.minimalTerminalDepth i : ℤ) : WithTop ℤ) := by
    change ord L (Pi ^ A.t 1) = _
    rw [ord_pow, ord_uniformizer L hPi, hd]
    norm_num
  obtain ⟨psi0, hpsi0, H, hH, _⟩ := A.minimalHasseFunction_exists hres theta C hC i
    (Or.inr heq) delta hdelta
  let p := criticalNormToResidue L K ht htpos hresL pi hpi hgen
  obtain ⟨hk, hindex⟩ := criticalNormToResidue_card L K
    (originLine_degrees F K (A.g i) (A.nontrivial i)).2 ht htpos hresL pi hpi hgen
  refine ⟨{ psi0 := psi0
            psi0_ne_one := hpsi0
            hasse := H
            normMap := p
            kernel_card := hk
            range_index := hindex
            norm_zero := criticalNormToResidue_zero_iff L K ht htpos hresL pi hpi hgen
            common := ?_
            residual := ?_ }⟩
  · intro U
    have hU : ((U : Kˣ) : K) - 1 ∈ lattice K (A.t 1 : ℤ) := by
      have hu' : (U : Kˣ) ∈ unitFiltration K (A.t 1 - 1 + 1) := by
        simpa only [Nat.sub_add_cancel htpos] using U.property
      simpa only [Nat.sub_add_cancel htpos] using
        (mem_unitFiltration_succ_iff_sub_mem_lattice K (A.t 1 - 1) U).1 hu'
    let v := A.minimalNormCoordinate hres (U : Kˣ) hU i
    have hcoord : p (Additive.ofMul (unitGradedMk K (A.t 1) U)) =
        reduce L ((v : L) / (delta : L)) (by
          apply (div_mem_lattice_iff L _ _ (A.minimalTerminalDepth i : ℤ) 0 hdelta).2
          simpa only [add_zero] using v.property) := by
      change (criticalNormPositiveUnitGradedResidueAddEquiv L htpos Pi hPi)
        (Additive.ofMul (criticalGradedNorm L K ht hresL pi hpi hgen
          (unitGradedMk K (A.t 1) U))) = _
      rw [criticalGradedNorm_mk, criticalNormPositiveUnitGradedResidueAddEquiv_mk]
      rfl
    rw [hcoord, hH v]
    exact A.minimalFullFunction_norm hres Theta theta hcompatible C hC i (Or.inr heq) U hU
  · obtain ⟨hm, hlarge, hZ, hs⟩ := A.minimalUpperStationary hres theta C hC i (Or.inr heq)
    exact completeResidualFactor_eq_sum L (canonicalLocalQuasiCharData L (theta i))
      (A.minimalUpperPsi hres i) (normUnits L K C) (A.minimalTerminalDepth i)
      hm hlarge hZ hs delta hdelta H hH

/-- The three norm maps are compared on the same actual source graded group. -/
theorem minimalCriticalLine_common (hres : residueDegree F K = 1)
    (heq : A.t 0 = A.t 1) (Theta : ContinuousQuasiChar K)
    (theta : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hcompatible : ∀ i, normQuasiChar (A.field i) K (theta i) = Theta)
    (C : Kˣ) (hC : A.IsMinimalFunctionOrigin theta C) (i j : Fin 3)
    (z : Additive (UnitGradedPiece K (A.t 1))) :
    let D := A.minimalCriticalLine hres heq Theta theta hcompatible C hC
    (D i).hasse ((D i).normMap z) = (D j).hasse ((D j).normMap z) := by
  dsimp only
  obtain ⟨U, hU⟩ := unitGradedMk_surjective K (A.t 1) (Additive.toMul z)
  have hz : Additive.ofMul (unitGradedMk K (A.t 1) U) = z := hU
  rw [← hz, (A.minimalCriticalLine hres heq Theta theta hcompatible C hC i).common,
    (A.minimalCriticalLine hres heq Theta theta hcompatible C hC j).common]

omit [IsGalois F K] [CharP F 2] [CharP K 2] in
private theorem exists_other_side (i : Fin 3) : ∃ j, A.g j ∉ originLine (A.g i) := by
  by_cases h : A.g 0 = A.g i
  · refine ⟨1, ?_⟩
    rintro (h1 | h1)
    · exact A.nontrivial 1 h1
    · exact A.distinct (h.trans h1.symm)
  · refine ⟨0, ?_⟩
    rintro (h0 | h0)
    · exact A.nontrivial 0 h0
    · exact h h0

/-- The actual conjugate quotient supplies the missing-coset translation.
Its full value is one, its polar annihilates the entire norm image, and its
nonzero image makes that polar nontrivial. -/
theorem minimalCriticalLine_sum (hres : residueDegree F K = 1)
    (heq : A.t 0 = A.t 1) (Theta : ContinuousQuasiChar K)
    (theta : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hcompatible : ∀ i, normQuasiChar (A.field i) K (theta i) = Theta)
    (C : Kˣ) (hC : A.IsMinimalFunctionOrigin theta C) (i : Fin 3) :
    letI : Fintype (Additive (UnitGradedPiece K (A.t 1))) := Fintype.ofFinite _
    let D := A.minimalCriticalLine hres heq Theta theta hcompatible C hC
    ∑ x, (D i).hasse x = (1 / 2 : ℂ) * ∑ z, (D i).hasse ((D i).normMap z) := by
  classical
  letI : Fintype (Additive (UnitGradedPiece K (A.t 1))) := Fintype.ofFinite _
  let D := A.minimalCriticalLine hres heq Theta theta hcompatible C hC
  obtain ⟨j, hji⟩ := A.exists_other_side i
  let U := A.minimalConjugateQuotient C j
  have htpos : 0 < A.t 1 := (A.edge 1).2.2.2.1
  have hUmem : U ∈ unitFiltration K (A.t 1) := by
    rw [← Nat.sub_add_cancel htpos]
    apply (mem_unitFiltration_succ_iff_sub_mem_lattice K _ U).2
    rw [Nat.sub_add_cancel htpos]
    exact (A.minimalConjugateQuotient_order hres heq C hC.order j).ge
  let u : unitFiltration K (A.t 1) := ⟨U, hUmem⟩
  let a := Additive.ofMul (unitGradedMk K (A.t 1) u)
  have ha : (D j).normMap a = 0 := by
    apply ((D j).norm_zero u).2
    rw [show (u : Kˣ) = U from rfl, A.minimalConjugateQuotient_norm]
    exact (unitFiltration (A.field j) (A.t 1 + 1)).one_mem
  have hpa : (D i).normMap a ≠ 0 := by
    intro hzero
    have hnext := (mem_unitFiltration_succ_iff_sub_mem_lattice (A.field i) (A.t 1)
      (normUnits (A.field i) K U)).1 (((D i).norm_zero u).1 hzero)
    change (((A.t 1 + 1 : ℕ) : ℤ) : WithTop ℤ) ≤ _ at hnext
    rw [A.minimalConjugateQuotient_norm_order hres heq C hC.order i j hji] at hnext
    norm_cast at hnext
    omega
  exact OneBreakResidue.hasse_sum_eq_half_common (D i).psi0 (D i).psi0_ne_one
    (D i).hasse (D j).hasse (D j).hasse.map_zero (D i).normMap (D j).normMap
    (D i).kernel_card (D i).range_index
    (A.minimalCriticalLine_common hres heq Theta theta hcompatible C hC i j) a ha hpa

/-- Equality of the complete upper residual factors in the one-break row. -/
theorem minimalResidualFactors_eq (hres : residueDegree F K = 1)
    (heq : A.t 0 = A.t 1) (Theta : ContinuousQuasiChar K)
    (theta : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hcompatible : ∀ i, normQuasiChar (A.field i) K (theta i) = Theta)
    (C : Kˣ) (hC : A.IsMinimalFunctionOrigin theta C) (i j : Fin 3) :
    Stationary.completeNormalizedResidualFactor (A.field i)
        (canonicalLocalQuasiCharData (A.field i) (theta i)) (A.minimalUpperPsi hres i) 1
        (normUnits (A.field i) K C)
        (A.minimalUpperStationary hres theta C hC i (Or.inr heq)).2.1 =
      Stationary.completeNormalizedResidualFactor (A.field j)
        (canonicalLocalQuasiCharData (A.field j) (theta j)) (A.minimalUpperPsi hres j) 1
        (normUnits (A.field j) K C)
        (A.minimalUpperStationary hres theta C hC j (Or.inr heq)).2.1 := by
  classical
  letI : Fintype (Additive (UnitGradedPiece K (A.t 1))) := Fintype.ofFinite _
  let D := A.minimalCriticalLine hres heq Theta theta hcompatible C hC
  rw [(D i).residual, (D j).residual,
    A.minimalCriticalLine_sum hres heq Theta theta hcompatible C hC i,
    A.minimalCriticalLine_sum hres heq Theta theta hcompatible C hC j,
    residueCard_eq_of_residueDegree_eq_one F (A.field i)
      (origin_residueDegrees F K hres (A.field i)).1,
    residueCard_eq_of_residueDegree_eq_one F (A.field j)
      (origin_residueDegrees F K hres (A.field j)).1]
  congr 2
  exact Finset.sum_congr rfl fun z _ ↦
    A.minimalCriticalLine_common hres heq Theta theta hcompatible C hC i j z

open private commonOrigin_edge from LanglandsSecondMainLemma.Stationary.CommonOrigin
open private scale_one from LanglandsSecondMainLemma.Dyadic.Equal.MinimalFunctions

/-- The actual lower norm character has the even conductor of this row. -/
theorem minimalLowerConductor (hres : residueDegree F K = 1)
    (heq : A.t 0 = A.t 1) (i : Fin 3) (omega : NormCharacter F (A.field i))
    (homega : omega ≠ 1) :
    (canonicalLocalQuasiCharData F omega.1).conductor = A.t 1 + 1 := by
  letI := lowerCyclic A i
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F (A.field i)
    (origin_residueDegrees F K hres (A.field i)).1
  exact (multiplicativeConductorExponent_eq_of_isConductor F _
    (ramifiedNormCharacter_conductor F (A.field i) (A.edge i).2.2.2.2.2.2.2.1
      (origin_residueDegrees F K hres (A.field i)).1 pi hpi hgen omega homega)).trans
    (by rw [A.oneBreak_eq heq i])

/-- Multiplication of the actual upper and lower Lamprecht factors, with
the full lower stationary chart and its even residual factor. -/
theorem minimalLocalConstants_factor (hres : residueDegree F K = 1)
    (heq : A.t 0 = A.t 1) (Theta : ContinuousQuasiChar K)
    (theta : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hcompatible : ∀ i, normQuasiChar (A.field i) K (theta i) = Theta)
    (C : Kˣ) (hC : A.IsMinimalFunctionOrigin theta C) (i : Fin 3)
    (omega : NormCharacter F (A.field i)) (homega : omega ≠ 1) :
    localConstant (A.field i) (theta i) (A.minimalUpperPsi hres i).character *
        localConstant F omega.1 A.minimalBasePsi.character =
      (Theta C : ℂ)⁻¹ * (A.minimalBasePsi.character
        (-elementarySymmetric F K 2 (C : K)) : ℂ) *
      Stationary.completeNormalizedResidualFactor (A.field i)
        (canonicalLocalQuasiCharData (A.field i) (theta i)) (A.minimalUpperPsi hres i) 1
        (normUnits (A.field i) K C)
        (A.minimalUpperStationary hres theta C hC i (Or.inr heq)).2.1 := by
  let L := A.field i
  have hdegree := originLine_degrees F K (A.g i) (A.nontrivial i)
  letI : Algebra.IsQuadraticExtension F L := ⟨hdegree.1⟩
  letI : Algebra.IsQuadraticExtension L K := ⟨hdegree.2⟩
  let chi := canonicalLocalQuasiCharData L (theta i)
  let om := canonicalLocalQuasiCharData F omega.1
  have hom : om.conductor = A.t 1 + 1 := A.minimalLowerConductor hres heq i omega homega
  have htpos : 0 < A.t 1 := (A.edge 1).2.2.2.1
  obtain ⟨n, hn⟩ := (A.edge 1).2.2.2.2.1
  have heven : om.conductor % 2 = 0 := by omega
  have homlarge : 1 < om.conductor := by omega
  have htrace : trace L K (C : K) ≠ 0 := (ord_ne_top_iff L).mp (by
    rw [A.minimalOrigin_trace_order hres (C : K) hC.order i]
    exact WithTop.coe_ne_top)
  obtain ⟨hm, hlarge, hZ, hs⟩ := A.minimalUpperStationary hres theta C hC i (Or.inr heq)
  have hZord : Stationary.IsOrdinaryStationaryCoefficient L chi
      (scaleAddCharData L (A.minimalUpperPsi hres i)
        (Units.map (algebraMap F L).toMonoidHom 1)) (normUnits L K C) hlarge := by
    rw [map_one, scale_one]
    refine ⟨hZ, ?_⟩
    have hm' : chi.conductor = 2 * A.minimalTerminalDepth i + 1 := hm
    have hd : chi.conductor / 2 + chi.conductor % 2 = A.minimalTerminalDepth i + 1 := by omega
    simpa only [hd] using hs
  have hWord : Stationary.IsOrdinaryStationaryCoefficient F om
      (scaleAddCharData F A.minimalBasePsi 1)
      (Stationary.commonOriginLowerCoefficient L C htrace) homlarge := by
    rw [scale_one]
    refine ⟨?_, ?_⟩
    · change ord F (Algebra.norm F (Algebra.trace L K (C : K))) = _
      rw [A.minimalLowerCoefficient_order hres heq C hC.order i, hom]
      dsimp only [minimalBasePsi]
      norm_num
    · intro v
      let u := positiveUnitOfLattice F
        (show 0 < om.conductor / 2 + om.conductor % 2 by omega) (-v)
      have hu : 1 - ((u : Fˣ) : F) = (v : F) := by
        change 1 - (1 + -(v : F)) = (v : F)
        ring
      have hdepth : ((om.conductor / 2 + om.conductor % 2 : ℕ) : ℤ) = A.lowerDepth i := by
        dsimp only [lowerDepth]
        rw [A.oneBreak_eq heq i]
        omega
      have hv : 1 - ((u : Fˣ) : F) ∈ lattice F (A.lowerDepth i) := by
        rw [hu, ← hdepth]
        exact v.property
      have hh := hC.lower i (Or.inr heq) omega homega u hv
      rw [hu] at hh
      exact hh
  have hfactor := commonOrigin_edge L chi om omega rfl Theta (hcompatible i)
    A.minimalBasePsi (A.minimalUpperPsi hres i) rfl 1 C htrace hlarge homlarge hZord hWord
  have hneg : -(1 : Fˣ)⁻¹ = 1 := by apply Units.ext; simp [CharTwo.neg_eq]
  rw [hneg, map_one, Units.val_one, one_mul, scale_one,
    Stationary.commonOriginResidualProduct, map_one,
    Stationary.completeNormalizedResidualFactor_even F om _ _ _ homlarge heven,
    mul_one] at hfactor
  exact hfactor

open private primeNormCharacter_card normCharacterProduct_two from
  LanglandsSecondMainLemma.Characters.Conjugacy

local instance (i : Fin 3) : PrimeCyclicExtension F (A.field i) := lowerCyclic A i
local instance (i : Fin 3) : Finite (NormCharacter F (A.field i)) :=
  primeCyclicNormCharacter_finite F (A.field i)
local instance (i : Fin 3) : Fintype (NormCharacter F (A.field i)) := Fintype.ofFinite _

/-- The paper's induction expression, with FML's canonical constants and
the complete product over all continuous lower norm characters. -/
def oneBreakExpression (theta : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (psi : ContinuousAddChar F) (i : Fin 3) : ℂ :=
  localConstant (A.field i) (theta i) (tracePullbackAddChar F (A.field i) psi) *
    ∏ omega : NormCharacter F (A.field i), localConstant F omega.1 psi

/-- In degree two the complete lower product is the nontrivial lower factor;
the identity character occurs in the product and its constant is proved one. -/
theorem oneBreakExpression_eq (theta : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (psi : LocalAddCharData F) (i : Fin 3)
    (omega : NormCharacter F (A.field i)) (homega : omega ≠ 1) :
    A.oneBreakExpression theta psi.character i =
      localConstant (A.field i) (theta i) (tracePullbackAddChar F (A.field i) psi.character) *
        localConstant F omega.1 psi.character := by
  classical
  have hcard : Nat.card (NormCharacter F (A.field i)) = 2 :=
    (primeNormCharacter_card F (A.field i)).trans
      (originLine_degrees F K (A.g i) (A.nontrivial i)).1
  have huniv : (Finset.univ : Finset (NormCharacter F (A.field i))) = {1, omega} := by
    apply Finset.eq_of_subset_of_card_le
    · intro x _
      by_cases hx : x = 1
      · simp [hx]
      · have hxo : x = omega := (Nat.card_eq_two_iff' (1 : NormCharacter F (A.field i))).mp
          hcard |>.unique hx homega
        simp [hxo]
    · simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard] using
        (Finset.card_le_two (a := (1 : NormCharacter F (A.field i))) (b := omega))
  dsimp only [oneBreakExpression]
  rw [huniv]
  have hone : (1 : NormCharacter F (A.field i)) ∉ ({omega} : Finset _) := by
    simpa only [Finset.mem_singleton] using homega.symm
  rw [Finset.prod_insert hone, Finset.prod_singleton]
  change _ * (localConstant F 1 psi.character * _) = _
  rw [canonicalLocalConstant_one F psi, one_mul]

/-- Comparison first at the exact scaled residue character used by the
constructed minimal origin. -/
theorem minimalExpressions_eq (hres : residueDegree F K = 1) (heq : A.t 0 = A.t 1)
    (Theta : ContinuousQuasiChar K) (theta : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hcompatible : ∀ i, normQuasiChar (A.field i) K (theta i) = Theta)
    (C : Kˣ) (hC : A.IsMinimalFunctionOrigin theta C) (i j : Fin 3) :
    A.oneBreakExpression theta A.minimalBasePsi.character i =
      A.oneBreakExpression theta A.minimalBasePsi.character j := by
  have hcard (i : Fin 3) : Nat.card (NormCharacter F (A.field i)) = 2 :=
    (primeNormCharacter_card F (A.field i)).trans
      (originLine_degrees F K (A.g i) (A.nontrivial i)).1
  obtain ⟨oi, hoi, _⟩ := (Nat.card_eq_two_iff' (1 : NormCharacter F (A.field i))).mp (hcard i)
  obtain ⟨oj, hoj, _⟩ := (Nat.card_eq_two_iff' (1 : NormCharacter F (A.field j))).mp (hcard j)
  rw [A.oneBreakExpression_eq theta A.minimalBasePsi i oi hoi,
    A.oneBreakExpression_eq theta A.minimalBasePsi j oj hoj]
  change localConstant (A.field i) (theta i) (A.minimalUpperPsi hres i).character * _ =
    localConstant (A.field j) (theta j) (A.minimalUpperPsi hres j).character * _
  rw [A.minimalLocalConstants_factor hres heq Theta theta hcompatible C hC i oi hoi,
    A.minimalLocalConstants_factor hres heq Theta theta hcompatible C hC j oj hoj,
    A.minimalResidualFactors_eq hres heq Theta theta hcompatible C hC i j]

end SimultaneousASGenerators
open private origin_group_equiv from LanglandsSecondMainLemma.Dyadic.Equal.Origin
open private field_injective from LanglandsSecondMainLemma.Dyadic.Equal.Models

/-- **Paper Proposition 11.10 (`D:EQ:min-one`).** Every primitive compatible
minimal family in the totally ramified equal-characteristic-two one-break
row has the same complete induction expression on all three fields.

The additive character is `D:EQ:canonicalpsi`, as fixed in the ambient
setup for this proposition. The lower product contains every continuous
norm character, including the trivial character. Quasi-character values
on uniformizers are unrestricted.

The origin, all stationary charts, the full Hasse functions, the actual
critical norm maps and their translations are constructed. The proof uses
the actual conjugate quotient `gⱼ(C)/C` to identify the polar annihilator
of the entire critical norm image before applying `missingCoset`. This is
the coordinate-free form of the paper's calibration and translation. -/
theorem equalBreaks (hres : residueDegree F K = 1)
    (P : Residues.EqualCharacteristicPresentation F) (A : SimultaneousASGenerators F K P)
    (heq : A.t 0 = A.t 1)
    (Theta : ContinuousQuasiChar K) (theta : (i : Fin 3) → ContinuousQuasiChar (A.field i))
    (hcompatible : ∀ i, normQuasiChar (A.field i) K (theta i) = Theta)
    (hprimitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = Theta)
    (hminimal : multiplicativeConductorExponent (A.field 0) (theta 0) = A.minimalConductor 0)
    (i j : Fin 3) :
    A.oneBreakExpression theta (originAddChar F P 0) i =
      A.oneBreakExpression theta (originAddChar F P 0) j := by
  obtain ⟨C, hC⟩ := A.minimalFunctionOrigin_exists hres Theta theta hcompatible hprimitive hminimal
  by_cases hij : i = j
  · subst j; rfl
  obtain ⟨_, _, _, _, hranges, _⟩ := Characters.quadraticProduct F
    (origin_group_equiv F K) A.field
    (fun k ↦ (originLine_degrees F K (A.g k) (A.nontrivial k)).1) (field_injective A)
  have hne : Ramification.intermediateNormRange (A.field i) ≠
      Ramification.intermediateNormRange (A.field j) := fun h ↦ hij (hranges h)
  obtain ⟨_, _, hD, _, hquadratic⟩ := Characters.conjugacy Nat.prime_two (origin_group_equiv F K)
    (A.field i) (A.field j)
    (originLine_degrees F K (A.g i) (A.nontrivial i)).1
    (originLine_degrees F K (A.g j) (A.nontrivial j)).1 hne
    (theta i) (theta j) Theta (hcompatible i) (hcompatible j) hprimitive
  obtain ⟨oi, oj, hoi, hoj, hprodI, hprodJ⟩ := hquadratic rfl
  rw [hprodI, hprodJ] at hD
  let psi := originCanonicalPsi F P
  let alpha := originCanonicalScale F P ((A.t 1 : ℤ) + 1)
  have hscale : (scaleAddCharData F psi alpha).character = A.minimalBasePsi.character :=
    originCanonicalPsi_scale F P ((A.t 1 : ℤ) + 1)
  have hscaled := A.minimalExpressions_eq hres heq Theta theta hcompatible C hC i j
  rw [A.oneBreakExpression_eq theta A.minimalBasePsi i oi hoi,
    A.oneBreakExpression_eq theta A.minimalBasePsi j oj hoj, ← hscale,
    quadraticPair_scale F (A.field i) (theta i) oi.1 psi alpha,
    quadraticPair_scale F (A.field j) (theta j) oj.1 psi alpha, hD] at hscaled
  change A.oneBreakExpression theta psi.character i = A.oneBreakExpression theta psi.character j
  rw [A.oneBreakExpression_eq theta psi i oi hoi, A.oneBreakExpression_eq theta psi j oj hoj]
  exact mul_left_cancel₀ (Units.ne_zero
    ((Characters.restrictQuasiChar F (A.field j) (theta j) * oj.1) alpha)) hscaled

end MinimalFamily

end
end LanglandsSecondMainLemma.Dyadic.Equal
