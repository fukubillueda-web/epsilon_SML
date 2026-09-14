import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.SymbolRelation

/-!
# Dyadic / Nonmaximal / Covector Ratio

The whole-ideal covector calculation and the exact polynomial error in
`D:NM:ratio-covectors` and `D:NM:lower-error`. All lattice exponents are
integers, including the possibly negative numerator depth `1-a`.

Controlling source: `references/epsilon_SML.tex`, lines 7592--7620,
with the aligned origin and lower stationary setup at 7405--7555.
-/

namespace LanglandsSecondMainLemma.Dyadic.Nonmaximal

open LanglandsFirstMainLemma
open LanglandsSecondMainLemma.Characters
open LanglandsSecondMainLemma.Dyadic.Mixed

noncomputable section

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The exact expansion in `D:NM:lower-error`, with the norm coefficients
from `D:NM:betatable`. This is an identity in the original field. -/
theorem dyadicNonmaximal_lowerError_identity (f g d : F) :
    f * (1 - 4 * g) * (1 + 2 * d - 4 * d ^ 2 * g) -
        g * (1 + 4 * f) * (d ^ 2 + 2 * d - 4 * f) =
      (f + d ^ 2 * g) * (1 + 2 * d + 16 * f * g) -
        8 * f * g * d * (d + 2) - 2 * g * d * (d ^ 2 + d + 1) := by
  ring

private theorem order_one_add_of_positive {v : F}
    (hv : v ∈ lattice F 1) : ord F (1 + v) = 0 := by
  have hpos : (0 : WithTop ℤ) < ord F v :=
    (by norm_num : (0 : WithTop ℤ) < (1 : WithTop ℤ)).trans_le hv
  rw [ord_add_eq_min F (by simpa only [ord_one] using ne_of_lt hpos),
    ord_one, min_eq_left hpos.le]

/-- Every summand of the displayed error has depth at least `1-a`.
The exact middle-term order retains the contribution of `d+2`; the last
factor is used only as an integral element and may be zero. -/
theorem dyadicNonmaximal_lowerError_depths
    (e a r : ℤ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (f g d : F)
    (hf : ord F f = ((1 - 2 * a : ℤ) : WithTop ℤ))
    (hg : ord F g = ((1 - 2 * r : ℤ) : WithTop ℤ))
    (hd : ord F d = ((r - a : ℤ) : WithTop ℤ))
    (hE : f + d ^ 2 * g ∈ lattice F (1 - a)) :
    (f + d ^ 2 * g) * (1 + 2 * d + 16 * f * g) ∈ lattice F (1 - a) ∧
      8 * f * g * d * (d + 2) ∈ lattice F (1 - a) ∧
      2 * g * d * (d ^ 2 + d + 1) ∈ lattice F (1 - a) := by
  have hdint : d ∈ lattice F 0 := by
    rw [mem_lattice, hd]
    exact_mod_cast (show 0 ≤ r - a by omega)
  have htwoD : 2 * d ∈ lattice F 0 := by
    rw [mem_lattice, ord_mul, htwo, hd]
    exact_mod_cast (show 0 ≤ e + (r - a) by omega)
  have hsixteen : ord F (16 : F) = ((4 * e : ℤ) : WithTop ℤ) := by
    rw [show (16 : F) = 2 ^ 4 by norm_num, ord_pow, htwo]
    exact_mod_cast (show 4 • e = 4 * e by simp)
  have hsixteenfg : 16 * f * g ∈ lattice F 0 := by
    rw [mem_lattice, ord_mul, ord_mul, hsixteen, hf, hg]
    exact_mod_cast (show 0 ≤ 4 * e + (1 - 2 * a) + (1 - 2 * r) by omega)
  have hone : (1 : F) ∈ lattice F 0 := by simp
  have hfirst := mul_mem_lattice F hE
    (add_mem_lattice F (add_mem_lattice F hone htwoD) hsixteenfg)
  have hde : r - a < e := by omega
  have hdplus : ord F (d + 2) = ((r - a : ℤ) : WithTop ℤ) := by
    rw [ord_add_eq_min F (by rw [hd, htwo]; exact_mod_cast ne_of_lt hde), hd, htwo]
    exact min_eq_left (WithTop.coe_le_coe.mpr hde.le)
  have height : ord F (8 : F) = ((3 * e : ℤ) : WithTop ℤ) := by
    rw [show (8 : F) = 2 ^ 3 by norm_num, ord_pow, htwo]
    exact_mod_cast (show 3 • e = 3 * e by simp)
  have hmiddle : 8 * f * g * d * (d + 2) ∈ lattice F (1 - a) := by
    rw [mem_lattice, ord_mul, ord_mul, ord_mul, ord_mul,
      height, hf, hg, hd, hdplus]
    exact_mod_cast (show 1 - a ≤
      3 * e + (1 - 2 * a) + (1 - 2 * r) + (r - a) + (r - a) by omega)
  have hlastFactor : d ^ 2 + d + 1 ∈ lattice F 0 := by
    have hdsq : d ^ 2 ∈ lattice F 0 := by
      simpa only [pow_two, add_zero] using mul_mem_lattice F hdint hdint
    exact add_mem_lattice F (add_mem_lattice F hdsq hdint) hone
  have hlastLeading : 2 * g * d ∈ lattice F (1 - a) := by
    rw [mem_lattice, ord_mul, ord_mul, htwo, hg, hd]
    exact_mod_cast (show 1 - a ≤ e + (1 - 2 * r) + (r - a) by omega)
  exact ⟨by simpa only [add_zero] using hfirst, hmiddle,
    by simpa only [add_zero] using mul_mem_lattice F hlastLeading hlastFactor⟩

/-- The polynomial error before division, at its full fractional depth. -/
theorem dyadicNonmaximal_lowerError_mem
    (e a r : ℤ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (f g d : F)
    (hf : ord F f = ((1 - 2 * a : ℤ) : WithTop ℤ))
    (hg : ord F g = ((1 - 2 * r : ℤ) : WithTop ℤ))
    (hd : ord F d = ((r - a : ℤ) : WithTop ℤ))
    (hE : f + d ^ 2 * g ∈ lattice F (1 - a)) :
    f * (1 - 4 * g) * (1 + 2 * d - 4 * d ^ 2 * g) -
        g * (1 + 4 * f) * (d ^ 2 + 2 * d - 4 * f) ∈ lattice F (1 - a) := by
  obtain ⟨hfirst, hmiddle, hlast⟩ :=
    dyadicNonmaximal_lowerError_depths F e a r ha har hre htwo f g d hf hg hd hE
  rw [dyadicNonmaximal_lowerError_identity]
  exact sub_mem_lattice F (sub_mem_lattice F hfirst hmiddle) hlast

/-- The two unit factors in the denominator of the ratio calculation. -/
theorem dyadicNonmaximal_ratio_unit_orders
    (e a r : ℤ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (f g d : F)
    (hf : ord F f = ((1 - 2 * a : ℤ) : WithTop ℤ))
    (hg : ord F g = ((1 - 2 * r : ℤ) : WithTop ℤ))
    (hd : ord F d = ((r - a : ℤ) : WithTop ℤ)) :
    ord F (1 + 4 * f) = 0 ∧ ord F (1 + 2 * d - 4 * d ^ 2 * g) = 0 := by
  have hfour : ord F (4 : F) = ((2 * e : ℤ) : WithTop ℤ) := by
    rw [show (4 : F) = 2 * 2 by norm_num, ord_mul, htwo]
    exact_mod_cast (show e + e = 2 * e by ring)
  have hfourf : 4 * f ∈ lattice F 1 := by
    rw [mem_lattice, ord_mul, hfour, hf]
    exact_mod_cast (show 1 ≤ 2 * e + (1 - 2 * a) by omega)
  have htwoD : 2 * d ∈ lattice F 1 := by
    rw [mem_lattice, ord_mul, htwo, hd]
    exact_mod_cast (show 1 ≤ e + (r - a) by omega)
  have hfourDg : 4 * d ^ 2 * g ∈ lattice F 1 := by
    rw [mem_lattice, ord_mul, ord_mul, ord_pow, hfour, hd, hg]
    exact_mod_cast (show 1 ≤ 2 * e + 2 • (r - a) + (1 - 2 * r) by
      simp only [two_nsmul]; omega)
  refine ⟨order_one_add_of_positive F hfourf, ?_⟩
  rw [show 1 + 2 * d - 4 * d ^ 2 * g = 1 + (2 * d - 4 * d ^ 2 * g) by ring]
  exact order_one_add_of_positive F (sub_mem_lattice F htwoD hfourDg)

/-- The polynomial ratio estimate `R - β₁/β₂ ∈ 𝔭_F^(2r-a)`.
Its denominator has exact order `1-2r`; it is never replaced by a unit
denominator or by a truncated natural-number depth. -/
theorem dyadicNonmaximal_normRatio
    (e a r : ℤ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (f g d : F)
    (hf : ord F f = ((1 - 2 * a : ℤ) : WithTop ℤ))
    (hg : ord F g = ((1 - 2 * r : ℤ) : WithTop ℤ))
    (hd : ord F d = ((r - a : ℤ) : WithTop ℤ))
    (hE : f + d ^ 2 * g ∈ lattice F (1 - a)) :
    f * (1 - 4 * g) / (g * (1 + 4 * f)) -
        (d ^ 2 + 2 * d - 4 * f) / (1 + 2 * d - 4 * d ^ 2 * g) ∈
      lattice F (2 * r - a) := by
  obtain ⟨hU, hβ₂⟩ :=
    dyadicNonmaximal_ratio_unit_orders F e a r ha har hre htwo f g d hf hg hd
  have hg0 : g ≠ 0 := (ord_ne_top_iff F).mp (by rw [hg]; exact WithTop.coe_ne_top)
  have hU0 : 1 + 4 * f ≠ 0 := (ord_ne_top_iff F).mp (by rw [hU]; norm_num)
  have hβ₂0 : 1 + 2 * d - 4 * d ^ 2 * g ≠ 0 :=
    (ord_ne_top_iff F).mp (by rw [hβ₂]; norm_num)
  have hden : ord F (g * (1 + 4 * f) * (1 + 2 * d - 4 * d ^ 2 * g)) =
      ((1 - 2 * r : ℤ) : WithTop ℤ) := by
    rw [ord_mul, ord_mul, hg, hU, hβ₂, add_zero, add_zero]
  rw [show f * (1 - 4 * g) / (g * (1 + 4 * f)) -
      (d ^ 2 + 2 * d - 4 * f) / (1 + 2 * d - 4 * d ^ 2 * g) =
      (f * (1 - 4 * g) * (1 + 2 * d - 4 * d ^ 2 * g) -
        g * (1 + 4 * f) * (d ^ 2 + 2 * d - 4 * f)) /
      (g * (1 + 4 * f) * (1 + 2 * d - 4 * d ^ 2 * g)) by
    rw [div_sub_div _ _ (mul_ne_zero hg0 hU0) hβ₂0]]
  rw [div_mem_lattice_iff F _ _ (1 - 2 * r) (2 * r - a) hden]
  convert dyadicNonmaximal_lowerError_mem F e a r ha har hre htwo f g d hf hg hd hE using 1
  congr 1
  omega

/-- Choose a full lower covector directly from FML's stationary numerator
class. The sign is the paper's `χ(1-u) = ψ(bu)`, and the exact order and
the entire half-conductor ideal are retained. -/
theorem dyadicNonmaximal_evenCovector_exists
    (χ : ContinuousQuasiChar F) (ψ : LocalAddCharData F)
    (q : ℕ) (hq : 1 ≤ q) (hχ : IsMultiplicativeConductor F χ (2 * q)) :
    ∃ b : Fˣ,
      ord F (b : F) = ((-ψ.conductor - 2 * (q : ℤ) : ℤ) : WithTop ℤ) ∧
      ∀ u ∈ lattice F (q : ℤ), ∀ B : Fˣ, (B : F) = 1 - u →
        χ B = ψ.character ((b : F) * u) := by
  let χD := continuousQuasiChar_toData F χ (2 * q) hχ
  have hqD : IsLamprechtStationaryDepth χD.conductor q := by
    change IsLamprechtStationaryDepth (2 * q) q
    exact ⟨by omega, le_rfl, by omega⟩
  have hΓ : ord F ((1 : Fˣ) : F) =
      (((-ψ.conductor) + ψ.conductor : ℤ) : WithTop ℤ) := by simp
  obtain ⟨c, hc⟩ := latticeQuotientMk_surjective F
    (sub_le_sub_left hqD.int_le_conductor (-ψ.conductor))
    (stationaryNumeratorClass F χD ψ (-ψ.conductor) hqD 1 hΓ)
  have hcOrd := stationaryNumeratorClass_representative_ord
    F χD ψ (-ψ.conductor) hqD 1 hΓ c hc
  have hbOrd : ord F (-(c : F)) =
      ((-ψ.conductor - 2 * (q : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_neg, hcOrd]
    simp only [χD, continuousQuasiChar_toData, Nat.cast_mul, Nat.cast_ofNat]
  have hb0 : -(c : F) ≠ 0 :=
    (ord_ne_top_iff F).mp (by rw [hbOrd]; exact WithTop.coe_ne_top)
  refine ⟨Units.mk0 (-(c : F)) hb0, hbOrd, ?_⟩
  intro u hu B hB
  let v : lattice F (q : ℤ) := ⟨-u, neg_mem_lattice F hu⟩
  have hlin := stationaryNumeratorClass_linearization
    F χD ψ (-ψ.conductor) hqD 1 hΓ c hc v
  have hunit : (positiveUnitOfLattice F hqD.pos v : Fˣ) = B := by
    apply Units.ext
    simp only [coe_positiveUnitOfLattice, v, hB, sub_eq_add_neg]
  rw [hunit] at hlin
  change χ B = ψ.character ((c : F) * (-u) / 1) at hlin
  simpa only [div_one, mul_neg, neg_mul, Units.val_mk0] using hlin

/-- Whole-ideal duality for the coefficient furnished by the symbol
relation. Multiplication of the variable by the unit `1+4f` is implemented
by division on the whole ideal before applying FML's annihilator theorem. -/
theorem dyadicNonmaximal_covector_duality
    (ψ : LocalAddCharData F) (a : ℤ) (f g b₁ b₂ : F)
    (hg : g ≠ 0) (hU : ord F (1 + 4 * f) = 0)
    (hphase : ∀ u ∈ lattice F a,
      ψ.character (b₁ * u) =
        ψ.character (b₂ * ((f / g) * u)) *
          ψ.character ((b₁ + b₂) * (-(4 * f * u)))) :
    b₁ - b₂ * (f * (1 - 4 * g) / (g * (1 + 4 * f))) ∈
      lattice F (-ψ.conductor - a) := by
  have hU0 : 1 + 4 * f ≠ 0 := (ord_ne_top_iff F).mp (by rw [hU]; norm_num)
  have hΓ : ord F (1 : F) =
      (((-ψ.conductor) + ψ.conductor : ℤ) : WithTop ℤ) := by simp
  apply (lamprechtAnnihilatorLeft F ψ hΓ).mp
  intro v hv
  have hu : v / (1 + 4 * f) ∈ lattice F a := by
    rw [div_mem_lattice_iff F _ _ 0 a hU, zero_add]
    exact hv
  have h := hphase (v / (1 + 4 * f)) hu
  rw [← ContinuousAddChar.map_add_eq_mul] at h
  have htriv : ψ.character
      (b₁ * (v / (1 + 4 * f)) -
        (b₂ * ((f / g) * (v / (1 + 4 * f))) +
          (b₁ + b₂) * (-(4 * f * (v / (1 + 4 * f)))))) = 1 := by
    calc
      _ = ψ.character (b₁ * (v / (1 + 4 * f))) /
          ψ.character (b₂ * ((f / g) * (v / (1 + 4 * f))) +
            (b₁ + b₂) * (-(4 * f * (v / (1 + 4 * f))))) :=
        ψ.character.toAddChar.map_sub_eq_div _ _
      _ = 1 := by rw [h, div_self']
  convert htriv using 1
  congr 1
  have hU0' : 1 + f * 4 ≠ 0 := by simpa only [mul_comm] using hU0
  field_simp [hg, hU0, hU0']
  ring

section ActualFields

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
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
  [Algebra.IsQuadraticExtension F L₁]
  [Algebra.IsQuadraticExtension F L₂]
  [Algebra.IsQuadraticExtension F L₃]

/-- The ratio estimates for any chosen full lower covectors. The input
`hproduct` is the lower-character product relation in the paper's setup.
The three characters are actual continuous norm characters of the named
fields; the symbol identity is supplied by the accepted origin theorem.
Both the duality error and the final quotient error keep their full depths. -/
theorem dyadicNonmaximal_covectorRatio_of_covectors
    (hchar : ringChar F ≠ 2)
    (e a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (x : L₁) (y : L₂) (z : L₃) (f g d : F)
    (O : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂) (ω₃ : NormCharacter F L₃)
    (hω₁ : ω₁ ≠ 1) (hω₂ : ω₂ ≠ 1) (hω₃ : ω₃ ≠ 1)
    (hproduct : ω₃.1 = ω₁.1 * ω₂.1)
    (ψ : LocalAddCharData F) (b₁ b₂ : Fˣ)
    (hb₂ord : ord F (b₂ : F) =
      ((-ψ.conductor - 2 * (r : ℤ) : ℤ) : WithTop ℤ))
    (hb₁ : ∀ u ∈ lattice F (a : ℤ), ∀ B : Fˣ, (B : F) = 1 - u →
      ω₁.1 B = ψ.character ((b₁ : F) * u))
    (hb₂ : ∀ u ∈ lattice F (r : ℤ), ∀ B : Fˣ, (B : F) = 1 - u →
      ω₂.1 B = ψ.character ((b₂ : F) * u)) :
    let β₁ := norm F L₁ (trace L₁ K O.Y)
    let β₂ := norm F L₂ (trace L₂ K O.Y)
    let R := f * (1 - 4 * g) / (g * (1 + 4 * f))
    (b₁ : F) - (b₂ : F) * R ∈ lattice F (-ψ.conductor - (a : ℤ)) ∧
      R - β₁ / β₂ ∈ lattice F (2 * (r : ℤ) - a) ∧
      (b₁ : F) / (b₂ : F) - β₁ / β₂ ∈ lattice F (2 * (r : ℤ) - a) ∧
      (b₁ : F) - ((b₂ : F) / β₂) * β₁ ∈
        lattice F (-ψ.conductor - (a : ℤ)) := by
  dsimp only
  have haZ : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have harZ : (a : ℤ) ≤ r := by exact_mod_cast har
  have hreZ : (r : ℤ) ≤ e := by exact_mod_cast hre
  have hE : f + d ^ 2 * g ∈ lattice F (1 - (a : ℤ)) := by
    rw [← O.E_eq]
    exact O.E_lattice
  obtain ⟨hU, _⟩ := dyadicNonmaximal_ratio_unit_orders F e a r haZ harZ hreZ
    htwo f g d O.f_order O.g_order O.d_order
  have hg0 : g ≠ 0 := (ord_ne_top_iff F).mp (by
    rw [O.g_order]
    exact WithTop.coe_ne_top)
  have hsymbols := dyadicNonmaximal_symbolRelation F L₁ L₂ L₃ hchar e a r
    ha har hre htwo x y z f g d O ω₁ ω₂ ω₃ hω₁ hω₂ hω₃
  have hphase : ∀ u ∈ lattice F (a : ℤ),
      ψ.character ((b₁ : F) * u) =
        ψ.character ((b₂ : F) * ((f / g) * u)) *
          ψ.character (((b₁ : F) + (b₂ : F)) * (-(4 * f * u))) := by
    intro u hu
    obtain ⟨B₁, B₂, C, hB₁, hB₂, hC, hB₂depth, hCdepth, hrel⟩ := hsymbols u hu
    have hw : (f / g) * u ∈ lattice F (r : ℤ) := by
      have heq : -((B₂ : F) - 1) = (f / g) * u := by rw [hB₂]; ring
      rw [← heq]
      exact neg_mem_lattice F hB₂depth
    have hv : -(4 * f * u) ∈ lattice F (r : ℤ) := by
      have heq : -((C : F) - 1) = -(4 * f * u) := by rw [hC]; ring
      rw [← heq]
      exact neg_mem_lattice F hCdepth
    have hCa : -(4 * f * u) ∈ lattice F (a : ℤ) := lattice_antitone F harZ hv
    have hCsub : (C : F) = 1 - (-(4 * f * u)) := by rw [hC]; ring
    have hthird : ω₃.1 C =
        ψ.character (((b₁ : F) + (b₂ : F)) * (-(4 * f * u))) := by
      rw [hproduct, ContinuousQuasiChar.mul_apply,
        hb₁ _ hCa C hCsub, hb₂ _ hv C hCsub,
        ← ContinuousAddChar.map_add_eq_mul, ← add_mul]
    rw [hb₁ u hu B₁ hB₁, hb₂ _ hw B₂ hB₂, hthird] at hrel
    exact hrel
  have hdual := dyadicNonmaximal_covector_duality F ψ a f g b₁ b₂ hg0 hU hphase
  have hratio : f * (1 - 4 * g) / (g * (1 + 4 * f)) -
      norm F L₁ (trace L₁ K O.Y) / norm F L₂ (trace L₂ K O.Y) ∈
        lattice F (2 * (r : ℤ) - a) := by
    rw [O.lowerNormTrace₁, O.lowerNormTrace₂]
    exact dyadicNonmaximal_normRatio F e a r haZ harZ hreZ htwo f g d
      O.f_order O.g_order O.d_order hE
  have hquot : (b₁ : F) / (b₂ : F) - f * (1 - 4 * g) / (g * (1 + 4 * f)) ∈
      lattice F (2 * (r : ℤ) - a) := by
    rw [show (b₁ : F) / (b₂ : F) - f * (1 - 4 * g) / (g * (1 + 4 * f)) =
      ((b₁ : F) - (b₂ : F) * (f * (1 - 4 * g) / (g * (1 + 4 * f)))) / (b₂ : F) by
      rw [sub_div, mul_div_cancel_left₀ _ b₂.ne_zero]]
    rw [div_mem_lattice_iff F _ _ (-ψ.conductor - 2 * (r : ℤ))
      (2 * (r : ℤ) - a) hb₂ord]
    convert hdual using 1
    congr 1
    omega
  have hfinal : (b₁ : F) / (b₂ : F) -
      norm F L₁ (trace L₁ K O.Y) / norm F L₂ (trace L₂ K O.Y) ∈
        lattice F (2 * (r : ℤ) - a) := by
    convert add_mem_lattice F hquot hratio using 1
    ring
  refine ⟨hdual, hratio, hfinal, ?_⟩
  have hb₂mem : (b₂ : F) ∈ lattice F (-ψ.conductor - 2 * (r : ℤ)) := by
    rw [mem_lattice, hb₂ord]
  have hscaled := mul_mem_lattice F hb₂mem hfinal
  have hscalar : (b₂ : F) * ((b₁ : F) / (b₂ : F) -
      norm F L₁ (trace L₁ K O.Y) / norm F L₂ (trace L₂ K O.Y)) =
      (b₁ : F) - ((b₂ : F) / norm F L₂ (trace L₂ K O.Y)) *
        norm F L₁ (trace L₁ K O.Y) := by
    rw [mul_sub, mul_div_cancel₀ _ b₂.ne_zero]
    ring
  rw [hscalar] at hscaled
  convert hscaled using 1
  congr 1
  omega

/-- **The lower covector ratio**, `D:NM:ratio-covectors` and
`D:NM:lower-error`. The covectors are constructed for the supplied actual
lower characters with conductors `2a` and `2r`, from the released FML
stationary class. Their ordinary charts hold on the whole ideals.

The usual lower-character product relation is kept explicit, as in the
paper's sentence declaring `ω₃` to be the product character. The origin
data comes with the accepted constructors from the aligned actual fields.
In particular the two beta coefficients below are actual lower norms of
the upper traces, rather than freely chosen polynomial coefficients. -/
theorem dyadicNonmaximal_covectorRatio
    (hchar : ringChar F ≠ 2)
    (e a r : ℕ) (ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (x : L₁) (y : L₂) (z : L₃) (f g d : F)
    (O : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (ω₁ : NormCharacter F L₁) (ω₂ : NormCharacter F L₂) (ω₃ : NormCharacter F L₃)
    (hω₁ : ω₁ ≠ 1) (hω₂ : ω₂ ≠ 1) (hω₃ : ω₃ ≠ 1)
    (hproduct : ω₃.1 = ω₁.1 * ω₂.1)
    (hconductor₁ : IsMultiplicativeConductor F ω₁.1 (2 * a))
    (hconductor₂ : IsMultiplicativeConductor F ω₂.1 (2 * r))
    (ψ : LocalAddCharData F) :
    let β₁ := norm F L₁ (trace L₁ K O.Y)
    let β₂ := norm F L₂ (trace L₂ K O.Y)
    let R := f * (1 - 4 * g) / (g * (1 + 4 * f))
    ∃ b₁ b₂ : Fˣ,
      ord F (b₁ : F) = ((-ψ.conductor - 2 * (a : ℤ) : ℤ) : WithTop ℤ) ∧
      ord F (b₂ : F) = ((-ψ.conductor - 2 * (r : ℤ) : ℤ) : WithTop ℤ) ∧
      (∀ u ∈ lattice F (a : ℤ), ∀ B : Fˣ, (B : F) = 1 - u →
        ω₁.1 B = ψ.character ((b₁ : F) * u)) ∧
      (∀ u ∈ lattice F (r : ℤ), ∀ B : Fˣ, (B : F) = 1 - u →
        ω₂.1 B = ψ.character ((b₂ : F) * u)) ∧
      (b₁ : F) - (b₂ : F) * R ∈ lattice F (-ψ.conductor - (a : ℤ)) ∧
      R - β₁ / β₂ ∈ lattice F (2 * (r : ℤ) - a) ∧
      (b₁ : F) / (b₂ : F) - β₁ / β₂ ∈ lattice F (2 * (r : ℤ) - a) ∧
      (b₁ : F) - ((b₂ : F) / β₂) * β₁ ∈
        lattice F (-ψ.conductor - (a : ℤ)) := by
  obtain ⟨b₁, hb₁ord, hb₁⟩ :=
    dyadicNonmaximal_evenCovector_exists F ω₁.1 ψ a ha hconductor₁
  obtain ⟨b₂, hb₂ord, hb₂⟩ :=
    dyadicNonmaximal_evenCovector_exists F ω₂.1 ψ r (ha.trans har) hconductor₂
  refine ⟨b₁, b₂, hb₁ord, hb₂ord, hb₁, hb₂, ?_⟩
  exact dyadicNonmaximal_covectorRatio_of_covectors F L₁ L₂ L₃ hchar e a r
    ha har hre htwo x y z f g d O ω₁ ω₂ ω₃ hω₁ hω₂ hω₃ hproduct
    ψ b₁ b₂ hb₂ord hb₁ hb₂

end ActualFields

end

end LanglandsSecondMainLemma.Dyadic.Nonmaximal
