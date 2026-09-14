import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Odd.Models.Compatibility
import LanglandsSecondMainLemma.Local.NormDescent
import LanglandsSecondMainLemma.Ramification.LeadingTerm

/-!
# Odd / Models / Global Extension

Paper `O:M:global`: extend the actual unit models and correct the first
descent by a character trivial on the upper norm image. Exact conductors
are detected on the original unit subgroups.
-/

namespace LanglandsSecondMainLemma.Odd.Models

noncomputable section

open LanglandsFirstMainLemma

set_option backward.isDefEq.respectTransparency false

section UnitExtensions
variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- The unit model has a continuous extension, with arbitrary nonunitary
values allowed away from its open domain. -/
theorem unitModel_extension_exists {q m : ℕ} (hq : 0 < q)
    (R : unitFiltration E q →* ℂˣ) (hR : IsUnitFiltrationConductor E R m) :
    ∃ theta : ContinuousQuasiChar E,
      theta.toMonoidHom.comp (unitFiltration E q).subtype = R :=
  Local.characterExtension E (unitFiltration E q) m
    (hq.trans_le hR.domain_le) (unitFiltration_antitone E hR.domain_le) R hR.trivial

/-- Every extension preserves the conductor already visible strictly
beyond the model's initial domain. -/
theorem unitModel_extension_conductor {q m : ℕ}
    (R : unitFiltration E q →* ℂˣ) (hR : IsUnitFiltrationConductor E R m)
    (hqm : q < m) (theta : ContinuousQuasiChar E)
    (hext : theta.toMonoidHom.comp (unitFiltration E q).subtype = R) :
    IsMultiplicativeConductor E theta m := by
  have heval (u : unitFiltration E q) : theta u = R u :=
    DFunLike.congr_fun hext u
  constructor
  · intro u hu
    exact (heval ⟨u, unitFiltration_antitone E hR.domain_le hu⟩).trans
      (DFunLike.congr_fun hR.trivial ⟨u, hu⟩)
  · intro r hr
    have h := hR.minimal (max q r) (le_max_left _ _) (by
      apply MonoidHom.ext
      intro u
      exact (heval ⟨u, unitFiltration_antitone E (le_max_left q r) u.property⟩).symm.trans
        (hr u (unitFiltration_antitone E (le_max_right q r) u.property)))
    omega

end UnitExtensions

open private continuous_of_trivialOnUnitFiltration from
  LanglandsSecondMainLemma.Local.CharacterExtension

section NormCorrection
variable (E L : Type) [Field E] [Field L]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra E L] [ValuativeExtension E L]
  [Module.Free E L] [Module.Finite E L] [PrimeCyclicExtension E L]

/-- A character on `U^q` trivial on its intersection with the honest norm
image extends to an upper norm character. Below the break, the norm image
and `U^q` generate the whole multiplicative group. -/
theorem unitModel_normCharacter_extension {t q : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak E L t)
    (hres : residueDegree E L = 1) (hqt : q ≤ t)
    (R : unitFiltration E q →* ℂˣ)
    (hR : ∀ u : unitFiltration E q, (u : Eˣ) ∈ (normUnits E L).range → R u = 1) :
    ∃ mu : NormCharacter E L,
      mu.1.toMonoidHom.comp (unitFiltration E q).subtype = R := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer E L hres
  let NF := cyclicPrimeNormFiltration E L ht hres pi hpi hgen
  let N := (normUnits E L).range
  let H := unitFiltration E q
  let Q : Eˣ →* Eˣ ⧸ N := QuotientGroup.mk' N
  let QH : H →* Eˣ ⧸ N := Q.comp H.subtype
  have hsup : N ⊔ H = ⊤ := by
    apply eq_top_iff.mpr
    rw [← NF.field_image_sup]
    exact sup_le_sup le_rfl (unitFiltration_antitone E hqt)
  have hsurj : Function.Surjective QH := by
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    have hu : u ∈ N ⊔ H := by rw [hsup]; trivial
    obtain ⟨n, hn, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hu
    refine ⟨⟨h, hh⟩, ?_⟩
    change Q h = Q (n * h)
    rw [map_mul, show Q n = 1 from (QuotientGroup.eq_one_iff n).2 hn]
    exact (one_mul (Q h)).symm
  have hker : QH.ker ≤ R.ker := by
    intro u hu
    apply hR u
    exact (QuotientGroup.eq_one_iff (u : Eˣ)).1 (MonoidHom.mem_ker.mp hu)
  let rho : Eˣ ⧸ N →* ℂˣ := QH.liftOfSurjective hsurj ⟨R, hker⟩
  have hrho : rho.comp QH = R := MonoidHom.liftOfRightInverse_comp ..
  let f : Eˣ →* ℂˣ := rho.comp Q
  have hfN (u : Eˣ) (hu : u ∈ N) : f u = 1 := by
    change rho (Q u) = 1
    rw [show Q u = 1 from (QuotientGroup.eq_one_iff u).2 hu, map_one]
  have hfU : ∀ u ∈ unitFiltration E (t + 1), f u = 1 := by
    intro u hu
    apply hfN
    rw [← NF.critical_successor_image] at hu
    obtain ⟨z, _, rfl⟩ := hu
    exact ⟨z, rfl⟩
  let mu : ContinuousQuasiChar E :=
    ⟨f, continuous_of_trivialOnUnitFiltration E f (t + 1) hfU⟩
  have hmu : normQuasiChar E L mu = 1 := by
    apply ContinuousMonoidHom.ext
    intro z
    exact hfN (normUnits E L z) ⟨z, rfl⟩
  exact ⟨⟨mu, hmu⟩, hrho⟩

end NormCorrection

section RamificationRatios
variable (E L : Type) [Field E] [Field L]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra E L] [ValuativeExtension E L]
  [Module.Free E L] [Module.Finite E L] [PrimeCyclicExtension E L]

/-- The ramification ratio lies in `U^t` for every nonzero element,
including elements with negative valuation. -/
theorem ramificationRatio_mem {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak E L t) (htpos : 0 < t)
    (hres : residueDegree E L = 1) (sigma : Gal(L/E)) (x : Lˣ) :
    Units.map sigma.toMonoidHom x / x ∈ unitFiltration L t := by
  by_cases hs : sigma = 1
  · subst sigma
    have hmap : Units.map (1 : Gal(L/E)).toMonoidHom x = x := by
      apply Units.ext
      rfl
    rw [hmap, div_self']
    exact (unitFiltration L t).one_mem
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer E L hres
  have hshell : sigma ∈ lowerRamificationGroup E L (t : ℤ) ∧
      sigma ∉ lowerRamificationGroup E L ((t : ℤ) + 1) := by
    simpa only [ht.1, ht.2, Subgroup.mem_top, Subgroup.mem_bot, true_and] using hs
  let s : lowerRamificationGroup E L (t : ℤ) := ⟨sigma, hshell.1⟩
  let c : L := lowerRamificationNormalizedDisplacement E L s pi hpi
  have hc : ord L c = 0 :=
    ord_lowerRamificationNormalizedDisplacement_eq_zero E L s pi hpi hgen hshell.2
  have hformula : sigma (pi : L) = (pi : L) * (1 + c * (pi : L) ^ t) := by
    dsimp only [c]
    rw [coe_lowerRamificationNormalizedDisplacement]
    rw [show (t : ℤ) + 1 = ((t + 1 : ℕ) : ℤ) by omega, zpow_natCast, pow_succ]
    change sigma (pi : L) = (pi : L) *
      (1 + (sigma (pi : L) - (pi : L)) / ((pi : L) ^ t * (pi : L)) * (pi : L) ^ t)
    field_simp [hpi.ne_zero]
    ring
  let s0 : lowerRamificationGroup E L 0 :=
    ⟨sigma, lowerRamificationGroup_antitone E L (by omega) hshell.1⟩
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff L).2 x.ne_zero)
  have hl := Ramification.leadingTerm_lowerBound s0 pi c hpi htpos hc hformula
    x.ne_zero hm.symm
  have hdiff : sigma (x : L) / (x : L) - 1 ∈ lattice L (t : ℤ) := by
    rw [show sigma (x : L) / (x : L) - 1 =
      (sigma (x : L) - (x : L)) / (x : L) by field_simp]
    apply (div_mem_lattice_iff L (x : L) _ m (t : ℤ) hm.symm).2
    exact hl
  have ht : t - 1 + 1 = t := Nat.sub_add_cancel htpos
  rw [← ht, mem_unitFiltration_succ_iff_sub_mem_lattice]
  have hval : ((Units.map sigma.toMonoidHom x : Lˣ) : L) = sigma (x : L) := rfl
  rw [Units.val_div_eq_div_val, hval]
  simpa only [ht] using hdiff

end RamificationRatios

section ConductorObstruction
variable (E L : Type) [Field E] [Field L]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra E L] [ValuativeExtension E L]
  [Module.Free E L] [Module.Finite E L] [PrimeCyclicExtension E L]

/-- Two descents of the same norm pullback have the same exact conductor
when one conductor is strictly above the upper norm-character conductor. -/
theorem sameNormPullback_conductor {t m : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak E L t)
    (hres : residueDegree E L = 1) (hm : t + 1 < m)
    (theta eta : ContinuousQuasiChar E)
    (hcond : IsMultiplicativeConductor E theta m)
    (heq : normQuasiChar E L theta = normQuasiChar E L eta) :
    IsMultiplicativeConductor E eta m := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer E L hres
  let NF := cyclicPrimeNormFiltration E L ht hres pi hpi hgen
  have hvalues (u : Eˣ) (hu : u ∈ unitFiltration E (t + 1)) :
      theta u = eta u := by
    rw [← NF.critical_successor_image] at hu
    obtain ⟨z, _, rfl⟩ := hu
    exact DFunLike.congr_fun heq z
  constructor
  · intro u hu
    exact (hvalues u (unitFiltration_antitone E hm.le hu)).symm.trans (hcond.trivial u hu)
  · intro r hr
    have htriv : QuasiCharTrivialOnUnitFiltration E theta (max (t + 1) r) := by
      intro u hu
      exact (hvalues u (unitFiltration_antitone E (le_max_left _ _) hu)).trans
        (hr u (unitFiltration_antitone E (le_max_right _ _) hu))
    have := hcond.minimal _ htriv
    omega

/-- Above the lower break, the excess of a norm-pullback conductor over
the break is divisible by the actual extension degree. -/
theorem normPullback_conductor_excess_dvd {s m : ℕ}
    (hs : PrimeCyclicExtension.IsLowerBreak E L s)
    (hres : residueDegree E L = 1) (hm : s + 1 < m)
    (chi : ContinuousQuasiChar E)
    (hcond : IsMultiplicativeConductor L (normQuasiChar E L chi) m) :
    Module.finrank E L ∣ m - (s + 1) := by
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer E L hres
  obtain ⟨n, hn⟩ := exists_isMultiplicativeConductor E chi
  have hhigh : s + 1 < n := by
    by_contra h
    have htriv := quasiCharTrivialOnUnitFiltration_mono E (by omega : n ≤ s + 1) hn.trivial
    have hpull := (quasiCharTrivialOnUnitFiltration_compNorm_iff_break_succ
      E L hs hres pi hpi hgen chi).2 htriv
    have := hcond.minimal (s + 1) hpull
    omega
  have hpull := multiplicativeConductor_compNorm_high E L hs hres pi hpi hgen hhigh hn
  have heq := hcond.unique hpull
  rw [herbrandPsiNat_of_break_le s (Module.finrank E L) (by omega)] at heq
  refine ⟨n - 1 - s, ?_⟩
  omega

end ConductorObstruction

section CompatibleExtension
variable (E₁ E₂ L : Type) [Field E₁] [Field E₂] [Field L]
  [ValuativeRel E₁] [TopologicalSpace E₁] [IsNonarchimedeanLocalField E₁]
  [ValuativeRel E₂] [TopologicalSpace E₂] [IsNonarchimedeanLocalField E₂]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra E₁ L] [Algebra E₂ L]
  [ValuativeExtension E₁ L] [ValuativeExtension E₂ L]
  [Module.Free E₁ L] [Module.Finite E₁ L] [PrimeCyclicExtension E₁ L]
  [Module.Free E₂ L] [Module.Finite E₂ L]

/-- Descent followed by the upper norm-character correction. The second
full character is universally quantified and is never replaced. -/
theorem compatibleUnitModels_extend {t q₁ q₂ : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak E₁ L t) (htpos : 0 < t)
    (hres : residueDegree E₁ L = 1) (hqt : q₁ ≤ t)
    (R₁ : unitFiltration E₁ q₁ →* ℂˣ) (R₂ : unitFiltration E₂ q₂ →* ℂˣ)
    (hcompat : ∀ u : Lˣ, u ∈ unitFiltration L q₁ →
      ∃ h₁ : normUnits E₁ L u ∈ unitFiltration E₁ q₁,
      ∃ h₂ : normUnits E₂ L u ∈ unitFiltration E₂ q₂,
        R₁ ⟨normUnits E₁ L u, h₁⟩ = R₂ ⟨normUnits E₂ L u, h₂⟩)
    (theta₂ : ContinuousQuasiChar E₂)
    (hext₂ : theta₂.toMonoidHom.comp (unitFiltration E₂ q₂).subtype = R₂) :
    ∃ theta₁ : ContinuousQuasiChar E₁,
      theta₁.toMonoidHom.comp (unitFiltration E₁ q₁).subtype = R₁ ∧
      normQuasiChar E₁ L theta₁ = normQuasiChar E₂ L theta₂ := by
  let Theta := normQuasiChar E₂ L theta₂
  have hinv (sigma : Gal(L/E₁)) (x : Lˣ) :
      Theta (Units.map sigma.toMonoidHom x) = Theta x := by
    let u := Units.map sigma.toMonoidHom x / x
    have hu : u ∈ unitFiltration L q₁ :=
      unitFiltration_antitone L hqt (ramificationRatio_mem E₁ L ht htpos hres sigma x)
    obtain ⟨h₁, h₂, hc⟩ := hcompat u hu
    have hn : normUnits E₁ L u = 1 := by
      change normUnits E₁ L (Units.map sigma.toMonoidHom x / x) = 1
      rw [map_div]
      have hn' : normUnits E₁ L (Units.map sigma.toMonoidHom x) = normUnits E₁ L x := by
        apply Units.ext
        exact Basic.norm_conjugate sigma (x : L)
      rw [hn', div_self']
    have hR : R₁ ⟨normUnits E₁ L u, h₁⟩ = 1 := by
      rw [show (⟨normUnits E₁ L u, h₁⟩ : unitFiltration E₁ q₁) = 1 from Subtype.ext hn,
        map_one]
    have hval : Theta u = 1 :=
      (DFunLike.congr_fun hext₂ ⟨normUnits E₂ L u, h₂⟩).trans (hc.symm.trans hR)
    exact div_eq_one.mp ((map_div Theta _ _).symm.trans hval)
  obtain ⟨theta₁', hdesc⟩ := Local.invariantCharacter_descends E₁ L Theta hinv
  let H := unitFiltration E₁ q₁
  let discrepancy : H →* ℂˣ := theta₁'.toMonoidHom.comp H.subtype / R₁
  have hoverlap (u : H) (hu : (u : E₁ˣ) ∈ (normUnits E₁ L).range) :
      discrepancy u = 1 := by
    obtain ⟨z, hz⟩ := hu
    have hzq : z ∈ unitFiltration L q₁ := by
      rw [← norm_preimage_unitFiltration E₁ L ht hres hqt]
      change normUnits E₁ L z ∈ H
      rw [hz]
      exact u.property
    obtain ⟨h₁, h₂, hc⟩ := hcompat z hzq
    have hu' : (⟨normUnits E₁ L z, h₁⟩ : H) = u := Subtype.ext hz
    have heval : theta₁' (u : E₁ˣ) = R₁ u := by
      rw [← hz]
      exact (DFunLike.congr_fun hdesc z).trans
        ((DFunLike.congr_fun hext₂ ⟨normUnits E₂ L z, h₂⟩).trans
          (hc.symm.trans (congrArg R₁ hu')))
    change theta₁' (u : E₁ˣ) / R₁ u = 1
    rw [heval, div_self']
  obtain ⟨mu, hmu⟩ := unitModel_normCharacter_extension E₁ L ht hres hqt discrepancy hoverlap
  refine ⟨theta₁' / mu.1, ?_, ?_⟩
  · apply MonoidHom.ext
    intro u
    have h := DFunLike.congr_fun hmu u
    change mu.1 (u : E₁ˣ) = theta₁' (u : E₁ˣ) / R₁ u at h
    change theta₁' (u : E₁ˣ) / mu.1 (u : E₁ˣ) = R₁ u
    rw [h, div_div_cancel]
  · apply ContinuousMonoidHom.ext
    intro z
    have h := DFunLike.congr_fun mu.property z
    change mu.1 (normUnits E₁ L z) = 1 at h
    change theta₁' (normUnits E₁ L z) / mu.1 (normUnits E₁ L z) = Theta z
    rw [h, div_one]
    exact DFunLike.congr_fun hdesc z

end CompatibleExtension

section PrimitivePullback
variable (F E L : Type) [Field F] [Field E] [Field L]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
  [ValuativeExtension F E] [ValuativeExtension E L] [ValuativeExtension F L]
  [Module.Free F E] [Module.Finite F E] [PrimeCyclicExtension F E]
  [Module.Free E L] [Module.Finite E L] [PrimeCyclicExtension E L]
  [Module.Free F L] [Module.Finite F L]

/-- Primitivity follows from the exact local conductor formula: descent
from `F` would force the nonzero excess `t` to be divisible by the degree.
No commutator identity or phase cancellation is assumed. -/
theorem modelPullback_not_baseNorm {t s : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak E L t)
    (hs : PrimeCyclicExtension.IsLowerBreak F E s)
    (htpos : 0 < t) (hts : t ≤ s)
    (hresUpper : residueDegree E L = 1) (hresLower : residueDegree F E = 1)
    (hprime : ¬ Module.finrank F E ∣ t)
    (theta : ContinuousQuasiChar E)
    (hcond : IsMultiplicativeConductor E theta (1 + t + s)) :
    ¬ ∃ chi : ContinuousQuasiChar F,
      normQuasiChar F L chi = normQuasiChar E L theta := by
  rintro ⟨chi, hchi⟩
  have htower : normQuasiChar E L (normQuasiChar F E chi) = normQuasiChar F L chi := by
    apply ContinuousMonoidHom.ext
    intro x
    change chi (normUnits F E (normUnits E L x)) = chi (normUnits F L x)
    congr 1
    apply Units.ext
    exact Basic.norm_tower (F := F) (L := E) (K := L) (x : L)
  have hc := sameNormPullback_conductor E L ht hresUpper (by omega)
    theta (normQuasiChar F E chi) hcond (hchi.symm.trans htower.symm)
  have hd := normPullback_conductor_excess_dvd F E hs hresLower (by omega) chi hc
  apply hprime
  simpa only [show 1 + t + s - (s + 1) = t by omega] using hd

end PrimitivePullback

open private card_eq_prime_of_ne_bot_ne_top from
  LanglandsSecondMainLemma.Ramification.DiamondBreaks
open private actualGaloisGroup_isMulCommutative from
  LanglandsSecondMainLemma.Basic.Fields

section FullInvariance
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]

/-- The two genuinely distinct order-prime lines generate the actual
Galois group. -/
theorem modelLines_sup_eq_top {p : ℕ} {hp : p.Prime} {hG}
    (D : Total.OddTotalBreakData (F := F) (K := K) hp hG) : D.H₁ ⊔ D.H₂ = ⊤ := by
  by_contra htop
  have hbot : D.H₁ ⊔ D.H₂ ≠ ⊥ := by
    intro h
    have h₁ : D.H₁ = ⊥ := le_bot_iff.mp (h ▸ le_sup_left)
    have : p = 1 := by simpa only [h₁, Subgroup.card_bot] using D.card_H₁.symm
    exact hp.ne_one this
  have hc := card_eq_prime_of_ne_bot_ne_top hp hG (D.H₁ ⊔ D.H₂) hbot htop
  have h₁ : D.H₁ = D.H₁ ⊔ D.H₂ :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hc, D.card_H₁])
  have h₂ : D.H₂ = D.H₁ ⊔ D.H₂ :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hc, D.card_H₂])
  exact D.lines_ne (h₁.trans h₂.symm)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeExtension F K] [Module.Free F K] [IsGalois F K] in
private theorem normUnits_fixedField_conjugate
    (H : Subgroup Gal(K/F)) (sigma : H) (x : Kˣ) :
    normUnits (IntermediateField.fixedField H) K
        (Units.map (sigma : Gal(K/F)).toMonoidHom x) =
      normUnits (IntermediateField.fixedField H) K x := by
  let s := IntermediateField.subgroupEquivAlgEquiv H sigma
  apply Units.ext
  exact Basic.norm_conjugate s (x : K)

/-- Compatibility on the two upper edges implies invariance on the
whole actual Galois group. -/
theorem compatibleModels_fullInvariant {p : ℕ} {hp : p.Prime} {hG}
    (D : Total.OddTotalBreakData (F := F) (K := K) hp hG) :
    let B₁ := D.B₁
    let B₂ := D.B₂
    letI := Basic.intermediateFieldValuativeRel B₁
    letI := Basic.intermediateFieldTopology B₁
    letI := Basic.intermediateField_localField B₁
    letI := Basic.intermediateField_upperValuativeExtension B₁
    letI := Basic.intermediateFieldValuativeRel B₂
    letI := Basic.intermediateFieldTopology B₂
    letI := Basic.intermediateField_localField B₂
    letI := Basic.intermediateField_upperValuativeExtension B₂
    ∀ (theta₁ : ContinuousQuasiChar B₁) (theta₂ : ContinuousQuasiChar B₂),
      normQuasiChar B₁ K theta₁ = normQuasiChar B₂ K theta₂ →
      ∀ (sigma : Gal(K/F)) (x : Kˣ),
        normQuasiChar B₂ K theta₂ (Units.map sigma.toMonoidHom x) =
          normQuasiChar B₂ K theta₂ x := by
  dsimp only
  let B₁ := D.B₁
  let B₂ := D.B₂
  letI := Basic.intermediateFieldValuativeRel B₁
  letI := Basic.intermediateFieldTopology B₁
  letI := Basic.intermediateField_localField B₁
  letI := Basic.intermediateField_upperValuativeExtension B₁
  letI := Basic.intermediateFieldValuativeRel B₂
  letI := Basic.intermediateFieldTopology B₂
  letI := Basic.intermediateField_localField B₂
  letI := Basic.intermediateField_upperValuativeExtension B₂
  intro theta₁ theta₂ heq sigma x
  letI : IsMulCommutative Gal(K/F) := actualGaloisGroup_isMulCommutative (Classical.choice hG)
  have hsig : sigma ∈ D.H₁ ⊔ D.H₂ := by rw [modelLines_sup_eq_top D]; trivial
  obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hsig
  have h₁ (u : Kˣ) : normQuasiChar B₂ K theta₂ (Units.map s₁.toMonoidHom u) =
      normQuasiChar B₂ K theta₂ u := by
    rw [← heq]
    exact congrArg theta₁ (normUnits_fixedField_conjugate D.H₁ ⟨s₁, hs₁⟩ u)
  have h₂ (u : Kˣ) : normQuasiChar B₂ K theta₂ (Units.map s₂.toMonoidHom u) =
      normQuasiChar B₂ K theta₂ u :=
    congrArg theta₂ (normUnits_fixedField_conjugate D.H₂ ⟨s₂, hs₂⟩ u)
  have hmap : Units.map (s₁ * s₂).toMonoidHom x =
      Units.map s₁.toMonoidHom (Units.map s₂.toMonoidHom x) := by
    apply Units.ext
    rfl
  rw [hmap, h₁, h₂]

end FullInvariance

open private norm_tower_residueDegrees from
  LanglandsSecondMainLemma.Odd.Models.PolynomialCoefficients

/-- Paper `O:M:global`. Construct the actual minimal models and continuous
full characters. Every extension of the second model admits a compatible
extension of the first. Their exact conductors persist under every upper
norm-character twist, and the common pullback is invariant and primitive.

The models, their compatibility, and the Artin--Schreier data are conclusions
of the accepted construction. The only character input is the paper's
nontrivial lower norm character and its truncated-logarithm chart. -/
theorem globalExtension
    {F K : Type} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (D : Total.OddTotalBreakData (F := F) (K := K) hp hG) :
    let B₁ := D.B₁
    let B₂ := D.B₂
    letI := Basic.intermediateFieldValuativeRel B₁
    letI := Basic.intermediateFieldTopology B₁
    letI := Basic.intermediateField_localField B₁
    letI := Basic.intermediateField_lowerValuativeExtension B₁
    letI := Basic.intermediateField_upperValuativeExtension B₁
    letI := Basic.intermediateFieldValuativeRel B₂
    letI := Basic.intermediateFieldTopology B₂
    letI := Basic.intermediateField_localField B₂
    letI := Basic.intermediateField_lowerValuativeExtension B₂
    letI := Basic.intermediateField_upperValuativeExtension B₂
    ∃ (Delta : K) (a : B₂),
      Delta ^ p - Delta = algebraMap B₂ K a ∧
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ¬ p ∣ D.t ∧ Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ ∧
      norm B₂ K Delta = a ∧
      ∀ (c : ℕ) (_hc : c = (D.t₂ + 1) ⌈/⌉ p) (hcpos : 0 < c)
        (tau : NormCharacter F B₂) (_htau : tau ≠ 1)
        (Psi : ContinuousAddChar F),
        (∀ z : lattice F (c : ℤ),
          tau.1 (positiveUnitOfLattice F hcpos (-z)) =
            Psi (truncatedLog p (z : F))) →
        ∃ M : OddMinimalCharacterModels B₁ B₂ p
            (firstModelDepth D) (firstModelConductor D)
            (secondModelDepth D) (secondModelConductor D)
            (tracePullbackAddChar F B₁ Psi) (tracePullbackAddChar F B₂ Psi)
            (norm B₁ K Delta) a,
          (∃ theta₂ : ContinuousQuasiChar B₂,
            theta₂.toMonoidHom.comp (unitFiltration B₂ (secondModelDepth D)).subtype = M.R₂) ∧
          ∀ theta₂ : ContinuousQuasiChar B₂,
            theta₂.toMonoidHom.comp (unitFiltration B₂ (secondModelDepth D)).subtype = M.R₂ →
            ∃ theta₁ : ContinuousQuasiChar B₁,
              theta₁.toMonoidHom.comp (unitFiltration B₁ (firstModelDepth D)).subtype = M.R₁ ∧
              normQuasiChar B₁ K theta₁ = normQuasiChar B₂ K theta₂ ∧
              IsMultiplicativeConductor B₁ theta₁ (firstModelConductor D) ∧
              IsMultiplicativeConductor B₂ theta₂ (secondModelConductor D) ∧
              (∀ (sigma : Gal(K/F)) (x : Kˣ),
                normQuasiChar B₂ K theta₂ (Units.map sigma.toMonoidHom x) =
                  normQuasiChar B₂ K theta₂ x) ∧
              (¬ ∃ chi : ContinuousQuasiChar F,
                normQuasiChar F K chi = normQuasiChar B₂ K theta₂) ∧
              (∀ mu : NormCharacter B₁ K,
                IsMultiplicativeConductor B₁ (mu.1 * theta₁) (firstModelConductor D)) ∧
              (∀ mu : NormCharacter B₂ K,
                IsMultiplicativeConductor B₂ (mu.1 * theta₂) (secondModelConductor D)) := by
  dsimp only
  let B₁ := D.B₁
  let B₂ := D.B₂
  letI := Basic.intermediateFieldValuativeRel B₁
  letI := Basic.intermediateFieldTopology B₁
  letI := Basic.intermediateField_localField B₁
  letI := Basic.intermediateField_lowerValuativeExtension B₁
  letI := Basic.intermediateField_upperValuativeExtension B₁
  letI := Basic.intermediateFieldValuativeRel B₂
  letI := Basic.intermediateFieldTopology B₂
  letI := Basic.intermediateField_localField B₂
  letI := Basic.intermediateField_lowerValuativeExtension B₂
  letI := Basic.intermediateField_upperValuativeExtension B₂
  let E₁ := Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁
  let E₂ := Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
  letI : PrimeCyclicExtension B₁ K := PrimeCyclicExtension.ofCyclicPrimeExtension B₁ K
    E₁.2.2.2.2.2.2.2.2.2.2.2.2
  letI : PrimeCyclicExtension F B₂ := PrimeCyclicExtension.ofCyclicPrimeExtension F B₂
    E₂.2.2.2.2.2.2.2.2.2.2.2.1
  letI : PrimeCyclicExtension B₂ K := PrimeCyclicExtension.ofCyclicPrimeExtension B₂ K
    E₂.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨_, hr₁⟩ := norm_tower_residueDegrees B₁ hres
  obtain ⟨hrF₂, hr₂⟩ := norm_tower_residueDegrees B₂ hres
  obtain ⟨hq₁, hq₂, hq₁t, hq₂t, _, _, _, _⟩ := domains_original D hres
  have htPrime : 0 < D.tPrime := hq₁.trans_le hq₁t
  have hq₁m : firstModelDepth D < firstModelConductor D := by
    simp only [firstModelConductor]
    omega
  have hq₂m : secondModelDepth D < secondModelConductor D := by
    simp only [secondModelConductor]
    omega
  have hm₁ : D.tPrime + 1 < firstModelConductor D := by
    have := D.t_pos
    simp only [firstModelConductor]
    omega
  have hm₂ : D.t + 1 < secondModelConductor D := by
    have := D.t_pos
    have := D.t_le_t₂
    simp only [secondModelConductor]
    omega
  obtain ⟨Delta, a, hroot, hDelta, ha, hprime, hgen, hnorm, hmodels⟩ :=
    compatibility hp hG hres hchar D
  refine ⟨Delta, a, hroot, hDelta, ha, hprime, hgen, hnorm, ?_⟩
  intro c hc hcpos tau htau Psi hchart
  obtain ⟨M, hcompat⟩ := hmodels c hc hcpos tau htau Psi hchart
  refine ⟨M, unitModel_extension_exists B₂ hq₂ M.R₂ M.R₂_conductor, ?_⟩
  intro theta₂ hext₂
  obtain ⟨theta₁, hext₁, heq⟩ := compatibleUnitModels_extend B₁ B₂ K
    D.B₁_breaks.2 htPrime hr₁ hq₁t M.R₁ M.R₂ hcompat theta₂ hext₂
  have hc₁ := unitModel_extension_conductor B₁ M.R₁ M.R₁_conductor hq₁m theta₁ hext₁
  have hc₂ := unitModel_extension_conductor B₂ M.R₂ M.R₂_conductor hq₂m theta₂ hext₂
  refine ⟨theta₁, hext₁, heq, hc₁, hc₂, compatibleModels_fullInvariant D theta₁ theta₂ heq,
    ?_, ?_, ?_⟩
  · exact modelPullback_not_baseNorm F B₂ K D.B₂_breaks.2 D.B₂_breaks.1
      D.t_pos D.t_le_t₂ hr₂ hrF₂
      (by simpa only [show Module.finrank F B₂ = p from D.degree_B₂] using hprime) theta₂ hc₂
  · intro mu
    exact sameNormPullback_conductor B₁ K D.B₁_breaks.2 hr₁ hm₁ theta₁ (mu.1 * theta₁)
      hc₁ (normCharacter_mul_compNorm B₁ K mu theta₁).symm
  · intro mu
    exact sameNormPullback_conductor B₂ K D.B₂_breaks.2 hr₂ hm₂ theta₂ (mu.1 * theta₂)
      hc₂ (normCharacter_mul_compNorm B₂ K mu theta₂).symm

end

end LanglandsSecondMainLemma.Odd.Models
