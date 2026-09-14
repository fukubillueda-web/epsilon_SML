import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsSecondMainLemma.Odd.EnhancedStationary

/-!
# Odd / Parameters / Lamprecht

Blueprint: blueprint/tasks/Odd/Parameters/Lamprecht.md
Paper: O:P:lamprecht

Specialize the enhanced stationary result with zero displacement and the stated full P domain. Reuse its homogeneous quadratic argument rather than repeat it.

Normal planning range: 80–400 lines; review splitting at 1200.
Never replace this task by a theorem of True, an axiom, or a statement
assuming the mathematical conclusion. Successful compilation of this
import-only scaffold does not complete the task.
-/

namespace LanglandsSecondMainLemma.Odd.Parameters

noncomputable section

open LanglandsFirstMainLemma
open LanglandsSecondMainLemma.Stationary
open scoped BigOperators

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-! ## Restriction of the full truncated-logarithm coefficient -/

/-- A coefficient satisfying the full `P`-identity at the exact depth
`ceil(conductor / p)` also satisfies it at the half-conductor depth used by
the enhanced stationary lemma. -/
private theorem fullCoefficient_at_half
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (p q d epsilon : ℕ)
    (hchar : ringChar (ResidueField E) = p) (hpodd : p ≠ 2)
    (hepsilon : epsilon ≤ 1)
    (hm : theta.conductor = 2 * d + epsilon)
    (hlarge : 1 < theta.conductor)
    (hq : q = theta.conductor ⌈/⌉ p) (hqpos : 0 < q)
    (C : Eˣ)
    (hC : IsEnhancedStationaryCoefficient E theta psi p q hqpos
      (-psi.conductor) C) :
    IsEnhancedStationaryCoefficient E theta psi p d (by omega)
      (-psi.conductor) C := by
  have hp : p.Prime := by
    rw [← hchar]
    exact residueCharacteristic_prime E
  have hpge : 3 ≤ p := by
    have := hp.two_le
    omega
  have hlog : theta.conductor ≤ p * d := by
    rw [hm]
    nlinarith
  have hqd : q ≤ d := by
    rw [hq]
    exact (ceilDiv_le_iff_le_mul hp.pos).2 hlog
  refine ⟨hC.1, ?_⟩
  intro z
  let zq : lattice E (q : ℤ) :=
    ⟨(z : E), lattice_antitone E (by exact_mod_cast hqd) z.property⟩
  have hformula := hC.2 zq
  have hunit :
      (positiveUnitOfLattice E hqpos (-zq) : Eˣ) =
        (positiveUnitOfLattice E (by omega) (-z) : Eˣ) := by
    apply Units.ext
    rfl
  rw [hunit] at hformula
  exact hformula

/-! ## The full odd Gauss term -/

/-- The homogeneous quadratic phase in `enhancedStationary`, written as the
literal full odd-conductor Lamprecht sum. -/
private theorem basicQuadraticPhase_eq_fullGauss
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (p d : ℕ) (hd : 0 < d) (C delta : Eˣ)
    (hchar : ringChar (ResidueField E) = p) (hpodd : p ≠ 2)
    (hm : theta.conductor = 2 * d + 1)
    (hC : IsEnhancedStationaryCoefficient E theta
      (scaleAddCharData E psi (1 : Eˣ)) p d hd (-psi.conductor) C)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ)) :
    @quadraticPhase (ResidueField E) _ (residueFieldFintype E)
        (enhancedResidualAddChar E theta (scaleAddCharData E psi (1 : Eˣ))
          p d hd (-psi.conductor) C delta hm (by
            simp [unitOrder]) hC hdelta)
        1 0 =
      (Real.sqrt (residueCard E : ℝ) : ℂ)⁻¹ *
        ∑ x ∈ @Finset.univ (ResidueField E) (residueFieldFintype E),
          (psi.character
            (-(C : E) * (delta : E) ^ 2 *
              (teichmuller E x : E) ^ 2 / (2 : E)) : ℂ) := by
  letI := residueFieldFintype E
  let Psi := scaleAddCharData E psi (1 : Eˣ)
  have hJ : -psi.conductor = -Psi.conductor := by
    simp [Psi, unitOrder]
  let psi0 := enhancedResidualAddChar E theta Psi p d hd (-psi.conductor)
    C delta hm hJ hC hdelta
  have hp : p.Prime := by
    rw [← hchar]
    exact residueCharacteristic_prime E
  have hp2 : 2 < p := by
    have := hp.two_le
    omega
  have hcharOdd : ringChar (ResidueField E) ≠ 2 := by
    rw [hchar]
    exact hpodd
  have hpsi0 : psi0 ≠ 1 :=
    enhancedResidualAddChar_ne_one E theta Psi p d hd (-psi.conductor)
      C delta hm hJ hC hdelta
  have hinv2 : (2 : E)⁻¹ ∈ lattice E 0 := by
    have htwoOrd : ord E (2 : E) = 0 :=
      ord_natCast_eq_zero_of_lt_residueCharacteristic E (j := 2)
        (by omega) (by simpa [hchar] using hp2)
    rw [mem_lattice, ord_inv, htwoOrd]
    simp
  have hterm (x : ResidueField E) :
      (teichmuller E x : E) ^ 2 / (2 : E) ∈ lattice E 0 := by
    have htx : (teichmuller E x : E) ∈ lattice E 0 :=
      (mem_lattice_zero_iff E).2 (teichmuller E x).property
    have htx2 : (teichmuller E x : E) ^ 2 ∈ lattice E 0 := by
      simpa only [zero_add, pow_two] using mul_mem_lattice E htx htx
    rw [div_eq_mul_inv]
    simpa only [zero_add] using mul_mem_lattice E htx2 hinv2
  have hreduce (x : ResidueField E) :
      reduce E ((teichmuller E x : E) ^ 2 / (2 : E)) (hterm x) =
        (1 : ResidueField E) / 2 * x ^ 2 := by
    let inv2R : ringOfIntegers E :=
      ⟨(2 : E)⁻¹, (mem_lattice_zero_iff E).1 hinv2⟩
    let tx : ringOfIntegers E := teichmuller E x
    let qR : ringOfIntegers E := tx ^ 2 * inv2R
    have htwo : (2 : E) ≠ 0 := by
      intro hzero
      have hord := ord_natCast_eq_zero_of_lt_residueCharacteristic E
        (j := 2) (by omega) (by simpa [hchar] using hp2)
      have : (0 : WithTop ℤ) = ⊤ := by
        calc
          (0 : WithTop ℤ) = ord E (2 : E) := hord.symm
          _ = ord E 0 := congrArg (ord E) hzero
          _ = ⊤ := ord_zero E
      exact WithTop.coe_ne_top this
    have hinv2res : residueMap E inv2R = (2 : ResidueField E)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      change residueMap E inv2R * residueMap E (2 : ringOfIntegers E) = 1
      rw [← map_mul]
      rw [show inv2R * (2 : ringOfIntegers E) = 1 by
        apply Subtype.ext
        exact inv_mul_cancel₀ htwo]
      exact map_one (residueMap E)
    have hqR : (qR : E) = (teichmuller E x : E) ^ 2 / (2 : E) := by
      change (teichmuller E x : E) ^ 2 * (2 : E)⁻¹ = _
      rw [div_eq_mul_inv]
    change residueMap E
      (⟨(teichmuller E x : E) ^ 2 / (2 : E),
        (mem_lattice_zero_iff E).1 (hterm x)⟩ : ringOfIntegers E) = _
    have hqSubtype :
        (⟨(teichmuller E x : E) ^ 2 / (2 : E),
          (mem_lattice_zero_iff E).1 (hterm x)⟩ : ringOfIntegers E) = qR :=
      Subtype.ext hqR.symm
    rw [hqSubtype]
    change residueMap E qR = _
    simp only [qR, map_mul, map_pow, hinv2res, one_div]
    rw [show residueMap E tx = x by exact residueMap_teichmuller E x]
    ring
  have hvalue (x : ResidueField E) :
      psi0 ((1 : ResidueField E) / 2 * x ^ 2) =
        (psi.character
          (-(C : E) * (delta : E) ^ 2 *
            (teichmuller E x : E) ^ 2 / (2 : E)) : ℂ) := by
    rw [← hreduce x]
    change residualAddChar E Psi ((-C * delta ^ 2)⁻¹) _
      (reduce E ((teichmuller E x : E) ^ 2 / (2 : E)) (hterm x)) = _
    rw [residualAddChar_integral_lift]
    simp only [Psi, scaleAddCharData_character_apply, Units.val_one, one_mul]
    congr 2
    simp only [Units.val_inv_eq_inv_val, Units.val_mul, Units.val_neg,
      Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero C, Units.ne_zero delta]
  have hsum :
      quadraticSum psi0 1 0 =
        ∑ x : ResidueField E,
          (psi.character
            (-(C : E) * (delta : E) ^ 2 *
              (teichmuller E x : E) ^ 2 / (2 : E)) : ℂ) := by
    rw [quadraticSum]
    apply Finset.sum_congr rfl
    intro x _hx
    simpa only [one_div, one_mul, zero_mul, add_zero] using hvalue x
  have hne : quadraticSum psi0 1 0 ≠ 0 :=
    quadraticSum_ne_zero hcharOdd hpsi0 one_ne_zero 0
  have hnorm : ‖quadraticSum psi0 1 0‖ =
      Real.sqrt (Fintype.card (ResidueField E) : ℝ) :=
    quadraticSum_norm hcharOdd hpsi0 one_ne_zero 0
  change quadraticPhase psi0 1 0 = _
  rw [quadraticPhase, phase_of_ne_zero hne, hnorm, hsum]
  rw [show residueCard E = Fintype.card (ResidueField E) by rfl,
    div_eq_mul_inv, mul_comm]

/-! ## Paper 8.19: the complete Lamprecht formula -/

/-- The complete formula `O:P:lamprecht` from a coefficient satisfying the
full truncated-logarithm identity on `p_E^(ceil(n / p))`.

The conclusion retains the homogeneous odd-conductor sum for every choice of
`delta` of valuation `d`; in even conductor the same factor is exactly one. -/
theorem lamprecht
    (theta : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (p q d epsilon : ℕ)
    (hchar : ringChar (ResidueField E) = p) (hpodd : p ≠ 2)
    (hepsilon : epsilon ≤ 1)
    (hm : theta.conductor = 2 * d + epsilon)
    (hlarge : 1 < theta.conductor)
    (hq : q = theta.conductor ⌈/⌉ p) (hqpos : 0 < q)
    (C : Eˣ)
    (hC : IsEnhancedStationaryCoefficient E theta psi p q hqpos
      (-psi.conductor) C) :
    ∃ g : ℂ,
      g ^ 4 = 1 ∧
      LanglandsFirstMainLemma.localConstant E theta.character psi.character =
        (theta.character ((-C)⁻¹) : ℂ) *
          (psi.character (-(C : E)) : ℂ) * g ∧
      (epsilon = 0 → g = 1) ∧
      (epsilon = 1 → ∀ (delta : Eˣ),
        ord E (delta : E) = ((d : ℤ) : WithTop ℤ) →
        g = (Real.sqrt (residueCard E : ℝ) : ℂ)⁻¹ *
          ∑ x ∈ @Finset.univ (ResidueField E) (residueFieldFintype E),
            (psi.character
              (-(C : E) * (delta : E) ^ 2 *
                (teichmuller E x : E) ^ 2 / (2 : E)) : ℂ)) := by
  have hd : 0 < d := by omega
  have hChalf := fullCoefficient_at_half E theta psi p q d epsilon hchar
    hpodd hepsilon hm hlarge hq hqpos C hC
  have hJ : -psi.conductor =
      -(scaleAddCharData E psi (1 : Eˣ)).conductor := by
    simp [unitOrder]
  have hCscale : IsEnhancedStationaryCoefficient E theta
      (scaleAddCharData E psi (1 : Eˣ)) p d hd (-psi.conductor) C := by
    refine ⟨hChalf.1, ?_⟩
    intro z
    simpa only [scaleAddCharData_character_apply, Units.val_one, one_mul]
      using hChalf.2 z
  obtain ⟨B, hB, hBunique, hstationaryAll⟩ :=
    enhancedStationary E theta psi (1 : Eˣ) p d epsilon (-psi.conductor)
      hchar hpodd hepsilon hm hlarge hJ
  have hetaDeep : (C : E) - (B : E) ∈
      lattice E (-psi.conductor - (d : ℤ)) := by
    simpa only [neg_sub] using
      neg_mem_lattice E (hBunique C hCscale)
  have heta : (C : E) - (B : E) ∈
      lattice E (-psi.conductor - (d + epsilon : ℕ)) :=
    lattice_antitone E (by push_cast; omega) hetaDeep
  obtain ⟨C', hC'eq, hC'ord, hstationary, g, hg4, hformula,
      hgeven, hgdeep⟩ := hstationaryAll ((C : E) - (B : E)) heta
  have hC'C : C' = C := by
    apply Units.ext
    rw [hC'eq]
    ring
  subst C'
  have hcorrection := hgdeep hetaDeep
  have hformula0 :
      LanglandsFirstMainLemma.localConstant E theta.character psi.character =
        (theta.character ((-C)⁻¹) : ℂ) *
          (psi.character (-(C : E)) : ℂ) * g := by
    rw [hcorrection] at hformula
    have hneg : -(1 : Eˣ) * C = -C := by simp
    rw [hneg] at hformula
    simpa only [scaleAddCharData_character_apply, Units.val_one, one_mul,
      mul_one] using hformula
  refine ⟨g, hg4, hformula0, ?_, ?_⟩
  · intro heven
    exact (hgeven heven).1
  · intro hodd delta hdelta
    have hmOdd : theta.conductor = 2 * d + 1 := by
      simpa only [hodd] using hm
    have hCord : ord E (C : E) =
        ((-(scaleAddCharData E psi (1 : Eˣ)).conductor -
          (theta.conductor : ℤ) : ℤ) : WithTop ℤ) := by
      have hone : unitOrder E (1 : Eˣ) = 0 := by
        simp [unitOrder]
      simpa only [scaleAddCharData_conductor, hone, add_zero] using hC.1
    have hnormalized :=
      (normalizedFactor E theta psi (1 : Eˣ) C d epsilon hepsilon hm
        hlarge hCord hstationary).2 hodd delta hdelta
    have hzero : (0 : E) ∈ lattice E (-psi.conductor - (d + 1 : ℕ)) :=
      (lattice E _).zero_mem
    have hresidual :
        normalizedResidualFactor E theta psi (1 : Eˣ) C d hmOdd hlarge
            delta hdelta =
          @quadraticPhase (ResidueField E) _ (residueFieldFintype E)
            (enhancedResidualAddChar E theta
              (scaleAddCharData E psi (1 : Eˣ)) p d hd (-psi.conductor)
              C delta hmOdd hJ hCscale hdelta) 1 0 := by
      have hres :=
        enhancedNormalizedResidualFactor_eq_quadraticPhase E theta psi
          (1 : Eˣ) p d hd (-psi.conductor) C C hchar hpodd hmOdd hlarge
          hJ hCscale 0 hzero (by simp) delta hdelta
      have hshiftzero :
          enhancedResidualShift E theta
            (scaleAddCharData E psi (1 : Eˣ)) p d hd (-psi.conductor)
              C delta hmOdd hCscale hdelta 0 hzero = 0 := by
        unfold enhancedResidualShift
        simp only [zero_div]
        change residueMap E (0 : ringOfIntegers E) = 0
        exact map_zero (residueMap E)
      rw [hshiftzero] at hres
      exact hres
    have hgauss := basicQuadraticPhase_eq_fullGauss E theta psi p d hd C delta
      hchar hpodd hmOdd hCscale hdelta
    have hnormalizedGauss :
        LanglandsFirstMainLemma.localConstant E theta.character psi.character =
          (theta.character ((-C)⁻¹) : ℂ) *
            (psi.character (-(C : E)) : ℂ) *
              ((Real.sqrt (residueCard E : ℝ) : ℂ)⁻¹ *
                ∑ x ∈ @Finset.univ (ResidueField E)
                    (residueFieldFintype E),
                  (psi.character
                    (-(C : E) * (delta : E) ^ 2 *
                      (teichmuller E x : E) ^ 2 / (2 : E)) : ℂ)) := by
      rw [hresidual, hgauss] at hnormalized
      have hneg : -(1 : Eˣ) * C = -C := by simp
      rw [hneg] at hnormalized
      simpa only [scaleAddCharData_character_apply, Units.val_one, one_mul]
        using hnormalized
    have hcommon :
        (theta.character ((-C)⁻¹) : ℂ) *
          (psi.character (-(C : E)) : ℂ) ≠ 0 :=
      mul_ne_zero (ContinuousQuasiChar.apply_ne_zero _ _)
        (ContinuousAddChar.apply_ne_zero _ _)
    apply mul_left_cancel₀ hcommon
    exact hformula0.symm.trans hnormalizedGauss

end

end LanglandsSecondMainLemma.Odd.Parameters
