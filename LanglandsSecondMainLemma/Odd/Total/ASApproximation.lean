import LanglandsSecondMainLemma.Odd.Total.Setup
import LanglandsSecondMainLemma.Local.Hilbert90
import LanglandsSecondMainLemma.Ramification.LeadingTerm

/-!
# Odd / Total / Artin--Schreier approximation

This file formalizes the pre-Hensel part of Paper Proposition 7.2.  It
constructs a best additive representative for the upper cyclic extension,
proves its exact order and prime-to-`p` break, and obtains the mixed-
characteristic error estimate at depth `V - p t`.
-/

namespace LanglandsSecondMainLemma.Odd.Total

open LanglandsFirstMainLemma

noncomputable section

private theorem improve_of_ramification_dvd_order
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L] [Module.Finite E L]
    (p : ℕ) (hram : ramificationIndex E L = p)
    (hres : residueDegree E L = 1)
    (x : L) (m : ℤ) (hx : ord L x = (m : WithTop ℤ))
    (hm : (p : ℤ) ∣ m) :
    ∃ a : E, (m : WithTop ℤ) < ord L (x - algebraMap E L a) := by
  obtain ⟨n, rfl⟩ := hm
  obtain ⟨pi, hpi⟩ := exists_ord_eq E 1
  have hpiU : (ValuativeRel.valuation E).IsUniformizer pi :=
    (ord_eq_one_iff_isUniformizer E pi).mp hpi
  have hpine : pi ≠ 0 := (ord_ne_top_iff E).mp (by rw [hpi]; simp)
  let q : L := algebraMap E L (pi ^ n)
  have hqne : q ≠ 0 := by
    dsimp only [q]
    exact (map_ne_zero (algebraMap E L)).mpr (zpow_ne_zero n hpine)
  have hqord : ord L q = (((p : ℤ) * n : ℤ) : WithTop ℤ) := by
    dsimp only [q]
    rw [ord_algebraMap, hram, ord_uniformizer_zpow E hpiU n]
    rw [← WithTop.coe_nsmul]
    congr 1
  let u : L := x / q
  have huord : ord L u = 0 := by
    dsimp only [u]
    rw [ord_div, hx, hqord]
    exact LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top
      (show ((((p : ℤ) * n : ℤ) : WithTop ℤ)) ≠ ⊤ from WithTop.coe_ne_top)
  have humem : u ∈ ringOfIntegers L :=
    (ord_nonneg_iff_mem_integer L u).mp (by rw [huord])
  let uO : ringOfIntegers L := ⟨u, humem⟩
  obtain ⟨aO, haO⟩ :=
    exists_ringOfIntegers_sub_mem_maximalIdeal_of_residueDegree_eq_one E L hres uO
  have hpositive : (0 : WithTop ℤ) <
      ord L (u - algebraMap E L (aO : E)) := by
    have hcoerce : ((uO - algebraMap (ringOfIntegers E) (ringOfIntegers L) aO :
        ringOfIntegers L) : L) = u - algebraMap E L (aO : E) := rfl
    rw [← hcoerce]
    exact (ord_pos_iff_mem_maximalIdeal L _).mpr haO
  let a : E := (aO : E) * pi ^ n
  refine ⟨a, ?_⟩
  have hfactor : x - algebraMap E L a =
      (u - algebraMap E L (aO : E)) * q := by
    dsimp only [a, q, u]
    rw [map_mul, map_zpow₀]
    rw [sub_mul]
    rw [div_mul_cancel₀ x
      (zpow_ne_zero n ((map_ne_zero (algebraMap E L)).mpr hpine))]
  rw [hfactor, ord_mul, hqord]
  have hfinite : ((((p : ℤ) * n : ℤ) : WithTop ℤ)) ≠ ⊤ := WithTop.coe_ne_top
  have := WithTop.add_lt_add_right hfinite hpositive
  simpa [add_comm] using this

/-- The integer-valued order and an a priori upper bound replace the
topological closest-point argument in the paper. -/
private theorem exists_best_additive_approximation
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L] [Module.Finite E L]
    (p : ℕ) (hram : ramificationIndex E L = p)
    (hres : residueDegree E L = 1)
    (x : L) (M : ℤ)
    (hnonbase : ∀ a : E, x - algebraMap E L a ≠ 0)
    (hupper : ∀ a : E,
      ord L (x - algebraMap E L a) ≤ (M : WithTop ℤ)) :
    ∃ (a : E) (m : ℤ),
      ord L (x - algebraMap E L a) = (m : WithTop ℤ) ∧
      (∀ b : E, ord L (x - algebraMap E L b) ≤ (m : WithTop ℤ)) ∧
      ¬ (p : ℤ) ∣ m := by
  classical
  let P : ℕ → Prop := fun n ↦ ∃ a : E,
    ord L (x - algebraMap E L a) = ((M - (n : ℕ) : ℤ) : WithTop ℤ)
  have hP : ∃ n, P n := by
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
      ((ord_ne_top_iff L).mpr (hnonbase 0))
    have hmord : ord L (x - algebraMap E L 0) = (m : WithTop ℤ) := hm.symm
    have hmle : m ≤ M := by
      have := hupper 0
      rw [hmord] at this
      exact WithTop.coe_le_coe.mp this
    let n : ℕ := (M - m).toNat
    have hn : (n : ℤ) = M - m := Int.toNat_of_nonneg (by omega)
    refine ⟨n, 0, ?_⟩
    simpa only [map_zero, sub_zero, hn, sub_sub_cancel] using hmord
  let n : ℕ := Nat.find hP
  obtain ⟨a, ha⟩ := Nat.find_spec hP
  let m : ℤ := M - (n : ℕ)
  have hmax : ∀ b : E,
      ord L (x - algebraMap E L b) ≤ (m : WithTop ℤ) := by
    intro b
    obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp
      ((ord_ne_top_iff L).mpr (hnonbase b))
    have hzord : ord L (x - algebraMap E L b) = (z : WithTop ℤ) := hz.symm
    have hzle : z ≤ M := by
      have := hupper b
      rw [hzord] at this
      exact WithTop.coe_le_coe.mp this
    by_contra hle
    have hlt : m < z := by
      have hlt' : (m : WithTop ℤ) < ord L (x - algebraMap E L b) :=
        lt_of_not_ge hle
      rw [hzord] at hlt'
      exact WithTop.coe_lt_coe.mp hlt'
    let nz : ℕ := (M - z).toNat
    have hnz : (nz : ℤ) = M - z := Int.toNat_of_nonneg (by omega)
    have hnzlt : nz < n := by
      exact_mod_cast (show (nz : ℤ) < (n : ℤ) by
        dsimp only [m] at hlt
        rw [hnz]
        omega)
    apply Nat.find_min hP hnzlt
    refine ⟨b, ?_⟩
    simpa only [hnz, sub_sub_cancel] using hzord
  refine ⟨a, m, ?_, hmax, ?_⟩
  · simpa only [m] using ha
  · intro hmdiv
    obtain ⟨b, hb⟩ := improve_of_ramification_dvd_order
      E L p hram hres (x - algebraMap E L a) m (by simpa [m] using ha) hmdiv
    have hrewrite :
        (x - algebraMap E L a) - algebraMap E L b =
          x - algebraMap E L (a + b) := by
      rw [map_add]
      ring
    rw [hrewrite] at hb
    exact (not_lt_of_ge (hmax (a + b))) hb

private theorem natCast_mem_lattice_zero
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (n : ℕ) :
    (n : L) ∈ lattice L 0 := by
  rw [mem_lattice]
  exact (ord_nonneg_iff_mem_integer L (n : L)).mpr
    (show (n : L) ∈ ringOfIntegers L by
      simp)

private theorem pow_mem_lattice_int
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    {x : L} {q : ℤ} (hx : x ∈ lattice L q) (n : ℕ) :
    x ^ n ∈ lattice L ((n : ℤ) * q) := by
  rw [mem_lattice] at hx ⊢
  rw [ord_pow]
  have h := nsmul_le_nsmul_right hx n
  simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using h

/-- The mixed-characteristic binomial correction for translation by one.
The output depth is the paper's `κ = V - (p-1)t`. -/
private theorem translate_one_power_error_mem
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    {p : ℕ} (hp : p.Prime) {V : ℤ} (hV : ord L (p : L) = (V : WithTop ℤ))
    {d : L} {t : ℕ}
    (hd : ord L d = ((-(t : ℤ) : ℤ) : WithTop ℤ)) :
    (d + 1) ^ p - d ^ p - 1 ∈ lattice L (V - ((p - 1) * t : ℕ)) := by
  let s : L := ∑ k ∈ Finset.Ioo 0 p,
    d ^ k * (1 : L) ^ (p - k) * ((Nat.choose p k / p : ℕ) : L)
  have hs : s ∈ lattice L (-(((p - 1) * t : ℕ) : ℤ)) := by
    apply sum_mem_lattice L
    intro k hk
    have hk' := Finset.mem_Ioo.mp hk
    have hdpow : d ^ k ∈ lattice L (-((k * t : ℕ) : ℤ)) := by
      have hdmem : d ∈ lattice L (-(t : ℤ)) := by rw [mem_lattice, hd]
      have := pow_mem_lattice_int L hdmem k
      convert this using 1
      push_cast
      ring
    have hpromote : d ^ k ∈ lattice L (-(((p - 1) * t : ℕ) : ℤ)) :=
      lattice_antitone L (by
        have hnat : k * t ≤ (p - 1) * t :=
          Nat.mul_le_mul_right t (by omega)
        have hint : ((k * t : ℕ) : ℤ) ≤ (((p - 1) * t : ℕ) : ℤ) := by
          exact_mod_cast hnat
        omega) hdpow
    have hcoeff : ((Nat.choose p k / p : ℕ) : L) ∈ lattice L 0 :=
      natCast_mem_lattice_zero L _
    simpa using mul_mem_lattice L hpromote hcoeff
  have hpcast : (p : L) ∈ lattice L V := by rw [mem_lattice, hV]
  have hprod : (p : L) * s ∈
      lattice L (V + -(((p - 1) * t : ℕ) : ℤ)) :=
    mul_mem_lattice L hpcast hs
  have hformula := (Commute.all d (1 : L)).add_pow_prime_pow_eq' hp 1
  norm_num [pow_one] at hformula
  have hid : (d + 1) ^ p - d ^ p - 1 = (p : L) * s := by
    rw [hformula]
    dsimp only [s]
    norm_num
    ring
  rw [hid]
  convert hprod using 1
  push_cast
  ring

/-- Perturbing the translated generator by an element of depth `κ` changes
its Artin--Schreier expression only in depth `κ`. -/
private theorem translate_small_power_error_mem
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    {p : ℕ} (hp : p.Prime) {V kappa : ℤ}
    (hV : ord L (p : L) = (V : WithTop ℤ))
    {x eta : L} {t : ℕ}
    (hkappa : kappa = V - ((p - 1) * t : ℕ))
    (hkappapos : 0 < kappa)
    (hx : ord L x = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (heta : eta ∈ lattice L kappa) :
    (x + eta) ^ p - x ^ p - eta ∈ lattice L kappa := by
  let s : L := ∑ k ∈ Finset.Ioo 0 p,
    x ^ k * eta ^ (p - k) * ((Nat.choose p k / p : ℕ) : L)
  have hs : s ∈ lattice L (-(((p - 1) * t : ℕ) : ℤ) + kappa) := by
    apply sum_mem_lattice L
    intro k hk
    have hk' := Finset.mem_Ioo.mp hk
    have hxmem : x ∈ lattice L (-(t : ℤ)) := by rw [mem_lattice, hx]
    have hxpow : x ^ k ∈ lattice L (-((k * t : ℕ) : ℤ)) := by
      have := pow_mem_lattice_int L hxmem k
      convert this using 1
      push_cast
      ring
    have hetapow : eta ^ (p - k) ∈ lattice L (((p - k : ℕ) : ℤ) * kappa) :=
      pow_mem_lattice_int L heta (p - k)
    have hmul := mul_mem_lattice L hxpow hetapow
    have hdepth : -(((p - 1) * t : ℕ) : ℤ) + kappa ≤
        -((k * t : ℕ) : ℤ) + ((p - k : ℕ) : ℤ) * kappa := by
      have hk_le : k * t ≤ (p - 1) * t :=
        Nat.mul_le_mul_right t (by omega)
      have hpk : 1 ≤ p - k := by omega
      have hk_cast : ((k * t : ℕ) : ℤ) ≤ (((p - 1) * t : ℕ) : ℤ) := by
        exact_mod_cast hk_le
      have hpk_cast : (1 : ℤ) ≤ (p - k : ℕ) := by exact_mod_cast hpk
      nlinarith
    have hpromote : x ^ k * eta ^ (p - k) ∈
        lattice L (-(((p - 1) * t : ℕ) : ℤ) + kappa) :=
      lattice_antitone L hdepth hmul
    have hcoeff : ((Nat.choose p k / p : ℕ) : L) ∈ lattice L 0 :=
      natCast_mem_lattice_zero L _
    simpa using mul_mem_lattice L hpromote hcoeff
  have hpcast : (p : L) ∈ lattice L V := by rw [mem_lattice, hV]
  have hps : (p : L) * s ∈
      lattice L (V + (-(((p - 1) * t : ℕ) : ℤ) + kappa)) :=
    mul_mem_lattice L hpcast hs
  have hps' : (p : L) * s ∈ lattice L kappa :=
    lattice_antitone L (by rw [hkappa]; omega) hps
  have hetap : eta ^ p ∈ lattice L ((p : ℤ) * kappa) :=
    pow_mem_lattice_int L heta p
  have hetap' : eta ^ p ∈ lattice L kappa :=
    lattice_antitone L (by
      have hpge : 1 ≤ p := hp.one_le
      nlinarith) hetap
  have htotal : eta ^ p + (p : L) * s - eta ∈ lattice L kappa := by
    exact (lattice L kappa).sub_mem ((lattice L kappa).add_mem hetap' hps') heta
  have hformula := (Commute.all x eta).add_pow_prime_pow_eq' hp 1
  norm_num [pow_one] at hformula
  have hid : (x + eta) ^ p - x ^ p - eta = eta ^ p + (p : L) * s - eta := by
    rw [hformula]
    dsimp only [s]
    ring
  rwa [hid]

private theorem residueDegree_mul_local
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (L : IntermediateField F K) :
    letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
    letI : TopologicalSpace L := Basic.intermediateFieldTopology L
    letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
    letI : ValuativeExtension F L := Basic.intermediateField_lowerValuativeExtension L
    letI : ValuativeExtension L K := Basic.intermediateField_upperValuativeExtension L
    residueDegree F L * residueDegree L K = residueDegree F K := by
  letI : ValuativeRel L := Basic.intermediateFieldValuativeRel L
  letI : TopologicalSpace L := Basic.intermediateFieldTopology L
  letI : IsNonarchimedeanLocalField L := Basic.intermediateField_localField L
  letI : ValuativeExtension F L := Basic.intermediateField_lowerValuativeExtension L
  letI : ValuativeExtension L K := Basic.intermediateField_upperValuativeExtension L
  letI : IsScalarTower
      (ringOfIntegers F) (ringOfIntegers L) (ringOfIntegers K) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap F K (x : F) = algebraMap L K (algebraMap F L (x : F))
      rw [← IsScalarTower.algebraMap_apply F L K])
  letI : IsLocalHom
      (algebraMap (ringOfIntegers F) (ringOfIntegers L)) := inferInstance
  letI : IsLocalHom
      (algebraMap (ringOfIntegers L) (ringOfIntegers K)) := inferInstance
  rw [residueDegree_eq_finrank_residueField,
    residueDegree_eq_finrank_residueField,
    residueDegree_eq_finrank_residueField]
  exact Module.finrank_mul_finrank
    (ResidueField F) (ResidueField L) (ResidueField K)

private theorem mem_range_algebraMap_of_generator_fixed
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    [FiniteDimensional E L] [IsGalois E L]
    (sigma : Gal(L/E)) (hsigma : ∀ tau : Gal(L/E), tau ∈ Subgroup.zpowers sigma)
    (x : L) (hx : sigma x = x) :
    x ∈ Set.range (algebraMap E L) := by
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  intro tau
  have hsigmaStabilizes : sigma ∈ MulAction.stabilizer Gal(L/E) x := by
    rw [MulAction.mem_stabilizer_iff]
    simpa [AlgEquiv.smul_def] using hx
  have htauStabilizes := (Subgroup.zpowers_le.mpr hsigmaStabilizes) (hsigma tau)
  rw [MulAction.mem_stabilizer_iff] at htauStabilizes
  simpa [AlgEquiv.smul_def] using htauStabilizes

/-- Universe-polymorphic additive half of `Local.hilbert90`.

The imported theorem currently quantifies its fields in `Type`, while the public
SML statement is universe-polymorphic.  This is the same dimension argument,
stated only for the additive half needed here. -/
private theorem additive_hilbert90
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    [FiniteDimensional E L] [IsGalois E L]
    (sigma : Gal(L/E))
    (hsigma : ∀ tau : Gal(L/E), tau ∈ Subgroup.zpowers sigma) :
    (trace E L).ker = (Local.additiveCoboundary sigma).range := by
  have hRange_le_ker :
      (Local.additiveCoboundary sigma).range ≤ (trace E L).ker := by
    rintro x ⟨y, rfl⟩
    change trace E L (sigma y - y) = 0
    rw [map_sub, Algebra.trace_eq_of_algEquiv sigma, sub_self]
  have hCoboundaryKer :
      (Local.additiveCoboundary sigma).ker =
        LinearMap.range (Algebra.linearMap E L) := by
    ext x
    constructor
    · intro hx
      have hxSigma : sigma x = x := by
        simpa only [LinearMap.mem_ker, Local.additiveCoboundary_apply,
          sub_eq_zero] using hx
      have hxRange : x ∈ Set.range (algebraMap E L) := by
        rw [IsGalois.mem_range_algebraMap_iff_fixed]
        intro tau
        have hsigmaStabilizes : sigma ∈ MulAction.stabilizer Gal(L/E) x := by
          rw [MulAction.mem_stabilizer_iff]
          simpa [AlgEquiv.smul_def] using hxSigma
        have htauStabilizes :=
          (Subgroup.zpowers_le.mpr hsigmaStabilizes) (hsigma tau)
        rw [MulAction.mem_stabilizer_iff] at htauStabilizes
        simpa [AlgEquiv.smul_def] using htauStabilizes
      obtain ⟨a, ha⟩ := hxRange
      exact ⟨a, by simpa using ha⟩
    · intro hx
      rw [LinearMap.mem_range] at hx
      obtain ⟨a, rfl⟩ := hx
      rw [LinearMap.mem_ker, Local.additiveCoboundary_apply, sub_eq_zero]
      exact sigma.commutes a
  have hCoboundaryKerFinrank :
      Module.finrank E (Local.additiveCoboundary sigma).ker = 1 := by
    rw [hCoboundaryKer, LinearMap.finrank_range_of_inj]
    · simp
    · exact (algebraMap E L).injective
  have hTraceRange : LinearMap.range (trace E L) = ⊤ :=
    LinearMap.range_eq_top.mpr (Algebra.trace_surjective E L)
  have hCoboundaryRank :=
    LinearMap.finrank_range_add_finrank_ker (Local.additiveCoboundary sigma)
  have hTraceRank := LinearMap.finrank_range_add_finrank_ker (trace E L)
  rw [hCoboundaryKerFinrank] at hCoboundaryRank
  rw [hTraceRange] at hTraceRank
  simp only [finrank_top, Module.finrank_self] at hTraceRank
  apply (Submodule.eq_of_le_of_finrank_eq hRange_le_ker ?_).symm
  omega

private theorem exists_generator_leading_data
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    [Module.Free E L] [Module.Finite E L] [PrimeCyclicExtension E L]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak E L t)
    (htpos : 0 < t) (hres : residueDegree E L = 1) :
    ∃ (sigma : lowerRamificationGroup E L 0) (pi c : L),
      (∀ tau : Gal(L/E), tau ∈ Subgroup.zpowers (sigma : Gal(L/E))) ∧
      (ValuativeRel.valuation L).IsUniformizer pi ∧ ord L c = 0 ∧
      (sigma : Gal(L/E)) pi = pi * (1 + c * pi ^ t) := by
  let generator := PrimeCyclicExtension.generator E L
  have hshell := PrimeCyclicExtension.generator_mem_break_and_not_mem_succ E L ht
  let sigmaT : lowerRamificationGroup E L (t : ℤ) := ⟨generator, hshell.1⟩
  have hsigma0 : generator ∈ lowerRamificationGroup E L 0 := by
    exact lowerRamificationGroup_antitone E L (by exact_mod_cast htpos.le) hshell.1
  let sigma : lowerRamificationGroup E L 0 := ⟨generator, hsigma0⟩
  obtain ⟨piO, hpi, hgen⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one E L hres
  let c : L := lowerRamificationNormalizedDisplacement E L sigmaT (piO : L) hpi
  have hc : ord L c = 0 := by
    dsimp only [c]
    exact ord_lowerRamificationNormalizedDisplacement_eq_zero
      E L sigmaT piO hpi hgen hshell.2
  refine ⟨sigma, piO, c, ?_, hpi, hc, ?_⟩
  · intro tau
    simpa only [sigma, generator] using
      PrimeCyclicExtension.generator_mem_zpowers E L tau
  · dsimp only [sigma, generator, c]
    rw [coe_lowerRamificationNormalizedDisplacement]
    have hpow : (piO : L) ^ ((t : ℤ) + 1) = (piO : L) * (piO : L) ^ t := by
      rw [zpow_add₀ hpi.ne_zero]
      simp [zpow_natCast]
      exact mul_comm _ _
    rw [hpow]
    field_simp [hpi.ne_zero]
    ring

private theorem best_coboundary_generator
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    [Module.Finite E L] [IsGalois E L]
    {p t : ℕ} (hchar : residueCharacteristic L = p)
    (hram : ramificationIndex E L = p) (hres : residueDegree E L = 1)
    (sigma : lowerRamificationGroup E L 0) (pi c : L)
    (hpi : (ValuativeRel.valuation L).IsUniformizer pi)
    (htpos : 0 < t) (hc : ord L c = 0)
    (hsigmapi : (sigma : Gal(L/E)) pi = pi * (1 + c * pi ^ t))
    (d0 q : L) (hdiff : (sigma : Gal(L/E)) d0 - d0 = q)
    (hqord : ord L q = 0) :
    ∃ d : L, ord L d = ((-(t : ℤ) : ℤ) : WithTop ℤ) ∧
      ¬ p ∣ t ∧ (sigma : Gal(L/E)) d - d = q := by
  have hqne : q ≠ 0 := (ord_ne_top_iff L).mp (by rw [hqord]; simp)
  have hnonbase : ∀ a : E, d0 - algebraMap E L a ≠ 0 := by
    intro a ha
    have hzero : (sigma : Gal(L/E)) d0 - d0 = 0 := by
      have hfixed : (sigma : Gal(L/E)) d0 = d0 := by
        have := congrArg (sigma : Gal(L/E)) ha
        simp only [map_sub, map_zero, (sigma : Gal(L/E)).commutes] at this
        have halg : d0 = algebraMap E L a := sub_eq_zero.mp ha
        rw [halg]
        exact (sigma : Gal(L/E)).commutes a
      exact sub_eq_zero.mpr hfixed
    rw [hdiff] at hzero
    exact hqne hzero
  have hupper : ∀ a : E,
      ord L (d0 - algebraMap E L a) ≤
        ((-(t : ℤ) : ℤ) : WithTop ℤ) := by
    intro a
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
      ((ord_ne_top_iff L).mpr (hnonbase a))
    have hmord : ord L (d0 - algebraMap E L a) = (m : WithTop ℤ) := hm.symm
    have hlower := Ramification.leadingTerm_lowerBound
      sigma pi c hpi htpos hc hsigmapi (hnonbase a) hmord
    have hsame : (sigma : Gal(L/E)) (d0 - algebraMap E L a) -
        (d0 - algebraMap E L a) = q := by
      rw [map_sub, (sigma : Gal(L/E)).commutes]
      calc
        (sigma : Gal(L/E)) d0 - algebraMap E L a -
            (d0 - algebraMap E L a) = (sigma : Gal(L/E)) d0 - d0 := by ring
        _ = q := hdiff
    rw [hsame, hqord] at hlower
    rw [hmord]
    exact WithTop.coe_le_coe.mpr (by
      have hlower' : m + (t : ℕ) ≤ 0 := by exact_mod_cast hlower
      omega)
  obtain ⟨b, m, hmord, _hmax, hmprime⟩ :=
    exists_best_additive_approximation E L p hram hres d0 (-(t : ℤ))
      hnonbase hupper
  let d : L := d0 - algebraMap E L b
  have hdifference : (sigma : Gal(L/E)) d - d = q := by
    dsimp only [d]
    rw [map_sub, (sigma : Gal(L/E)).commutes]
    calc
      (sigma : Gal(L/E)) d0 - algebraMap E L b -
          (d0 - algebraMap E L b) = (sigma : Gal(L/E)) d0 - d0 := by ring
      _ = q := hdiff
  have hmres : ¬ (residueCharacteristic L : ℤ) ∣ m := by
    rw [hchar]
    exact hmprime
  have hexact := Ramification.leadingTerm sigma pi c hpi htpos hc hsigmapi
    (hnonbase b) hmord hmres
  rw [hdifference, hqord] at hexact
  have hmt : m = -(t : ℤ) := by
    have : m + (t : ℕ) = 0 := by exact_mod_cast hexact.symm
    omega
  have hnotdvd : ¬ p ∣ t := by
    intro hpt
    apply hmprime
    rw [hmt]
    exact Int.dvd_neg.mpr (by exact_mod_cast hpt)
  exact ⟨d, by simpa only [d, hmt] using hmord, hnotdvd, hdifference⟩

private theorem exists_fixed_approximation_of_displacement
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    [Module.Finite E L] [IsGalois E L]
    {p t : ℕ} (hchar : residueCharacteristic L = p)
    (hram : ramificationIndex E L = p) (hres : residueDegree E L = 1)
    (sigma : lowerRamificationGroup E L 0)
    (hsigma : ∀ tau : Gal(L/E), tau ∈ Subgroup.zpowers (sigma : Gal(L/E)))
    (pi c : L) (hpi : (ValuativeRel.valuation L).IsUniformizer pi)
    (htpos : 0 < t) (hc : ord L c = 0)
    (hsigmapi : (sigma : Gal(L/E)) pi = pi * (1 + c * pi ^ t))
    (x : L) (kappa : ℤ)
    (hmove : (kappa : WithTop ℤ) ≤
      ord L ((sigma : Gal(L/E)) x - x)) :
    ∃ a : E, ((kappa - (t : ℕ) : ℤ) : WithTop ℤ) ≤
      ord L (x - algebraMap E L a) := by
  classical
  by_cases hxbase : x ∈ Set.range (algebraMap E L)
  · obtain ⟨a, rfl⟩ := hxbase
    refine ⟨a, ?_⟩
    rw [sub_self, ord_zero]
    exact le_top
  · have hnonbase : ∀ a : E, x - algebraMap E L a ≠ 0 := by
      intro a ha
      apply hxbase
      exact ⟨a, (sub_eq_zero.mp ha).symm⟩
    have hmovenonzero : (sigma : Gal(L/E)) x - x ≠ 0 := by
      intro hzero
      apply hxbase
      apply mem_range_algebraMap_of_generator_fixed E L
        (sigma : Gal(L/E)) hsigma x
      exact sub_eq_zero.mp hzero
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp
      ((ord_ne_top_iff L).mpr hmovenonzero)
    have hsmove : ord L ((sigma : Gal(L/E)) x - x) = (s : WithTop ℤ) := hs.symm
    have hupper : ∀ a : E, ord L (x - algebraMap E L a) ≤
        ((s - (t : ℕ) : ℤ) : WithTop ℤ) := by
      intro a
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
        ((ord_ne_top_iff L).mpr (hnonbase a))
      have hmord : ord L (x - algebraMap E L a) = (m : WithTop ℤ) := hm.symm
      have hlower := Ramification.leadingTerm_lowerBound sigma pi c hpi htpos hc
        hsigmapi (hnonbase a) hmord
      have hsame : (sigma : Gal(L/E)) (x - algebraMap E L a) -
          (x - algebraMap E L a) = (sigma : Gal(L/E)) x - x := by
        rw [map_sub, (sigma : Gal(L/E)).commutes]
        ring
      rw [hsame, hsmove] at hlower
      rw [hmord]
      exact WithTop.coe_le_coe.mpr (by
        have : m + (t : ℕ) ≤ s := by exact_mod_cast hlower
        omega)
    obtain ⟨a, m, hmord, _hmax, hmprime⟩ :=
      exists_best_additive_approximation E L p hram hres x
        (s - (t : ℕ)) hnonbase hupper
    have hmres : ¬ (residueCharacteristic L : ℤ) ∣ m := by
      rw [hchar]
      exact hmprime
    have hexact := Ramification.leadingTerm sigma pi c hpi htpos hc hsigmapi
      (hnonbase a) hmord hmres
    have hsame : (sigma : Gal(L/E)) (x - algebraMap E L a) -
        (x - algebraMap E L a) = (sigma : Gal(L/E)) x - x := by
      rw [map_sub, (sigma : Gal(L/E)).commutes]
      ring
    rw [hsame, hsmove] at hexact
    refine ⟨a, ?_⟩
    rw [hmord]
    apply WithTop.coe_le_coe.mpr
    have hks : kappa ≤ s := by
      rw [hsmove] at hmove
      exact WithTop.coe_le_coe.mp hmove
    have hms : m + (t : ℕ) = s := WithTop.coe_eq_coe.mp hexact.symm
    omega

private theorem artinSchreier_displacement_mem
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L]
    {p : ℕ} (hp : p.Prime) {V kappa : ℤ}
    (hV : ord L (p : L) = (V : WithTop ℤ))
    {t : ℕ} (htpos : 0 < t)
    (hkappa : kappa = V - ((p - 1) * t : ℕ))
    (hkappapos : 0 < kappa)
    (sigma : Gal(L/E)) (d eta : L)
    (hd : ord L d = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (heta : eta ∈ lattice L kappa)
    (hdifference : sigma d - d = 1 + eta) :
    sigma (d ^ p - d) - (d ^ p - d) ∈ lattice L kappa := by
  have hdplus : ord L (d + 1) = ((-(t : ℤ) : ℤ) : WithTop ℤ) := by
    have hne : ord L d ≠ ord L (1 : L) := by
      rw [hd, ord_one]
      intro h
      have h' := WithTop.coe_eq_coe.mp h
      omega
    rw [ord_add_eq_min L hne, hd, ord_one]
    apply min_eq_left
    exact WithTop.coe_le_coe.mpr (by omega)
  have hone := translate_one_power_error_mem L hp hV hd
  have hetaError := translate_small_power_error_mem L hp hV hkappa hkappapos
    hdplus heta
  have hdecomp : sigma (d ^ p - d) - (d ^ p - d) =
      ((d + 1 + eta) ^ p - (d + 1) ^ p - eta) +
        ((d + 1) ^ p - d ^ p - 1) := by
    rw [map_sub, map_pow]
    have hsigma : sigma d = d + 1 + eta := by
      rw [sub_eq_iff_eq_add] at hdifference
      simpa only [add_assoc, add_comm, add_left_comm] using hdifference
    rw [hsigma]
    ring
  rw [hdecomp]
  exact (lattice L kappa).add_mem hetaError
    (by simpa only [hkappa] using hone)

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K]
variable [Module.Free F K] [Module.Finite F K] [IsGalois F K]

/-- Approximate Artin--Schreier generator from Paper Proposition 7.2.

The equal-characteristic alternative is already exact.  In mixed
characteristic, `V` is the actual normalized order of `p` in the top field,
and the displayed lower bound is precisely `V - p t`, the depth required by
the subsequent Hensel argument. -/
theorem oddAS_approximate_generator {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = p)
    (D : OddTotalBreakData (F := F) (K := K) hp hG) :
    let B₂ := D.B₂
    ∃ (d : K) (a : B₂),
      ord K d = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ¬ p ∣ D.t ∧
      (((p : K) = 0 ∧ d ^ p - d = algebraMap B₂ K a) ∨
        ((p : K) ≠ 0 ∧ ∃ V : ℤ,
          ord K (p : K) = (V : WithTop ℤ) ∧
          ((V - (p * D.t : ℕ) : ℤ) : WithTop ℤ) ≤
            ord K (d ^ p - d - algebraMap B₂ K a))) := by
  dsimp only [OddTotalBreakData.B₂]
  let B₂ := IntermediateField.fixedField D.H₂
  letI : ValuativeRel B₂ := Basic.intermediateFieldValuativeRel B₂
  letI : TopologicalSpace B₂ := Basic.intermediateFieldTopology B₂
  obtain ⟨hLocal, hFreeFB₂, hFiniteFB₂, hFreeB₂K, hFiniteB₂K, hScalar,
      hValFB₂, hValB₂K, _htotal, _hdegreeLower, hdegreeUpper,
      _hcycFB₂, hcycB₂K⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
  letI : IsNonarchimedeanLocalField B₂ := hLocal
  letI : Module.Free F B₂ := hFreeFB₂
  letI : Module.Finite F B₂ := hFiniteFB₂
  letI : Module.Free B₂ K := hFreeB₂K
  letI : Module.Finite B₂ K := hFiniteB₂K
  letI : IsScalarTower F B₂ K := hScalar
  letI : ValuativeExtension F B₂ := hValFB₂
  letI : ValuativeExtension B₂ K := hValB₂K
  letI : IsGalois B₂ K := hcycB₂K.1
  letI : PrimeCyclicExtension B₂ K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension B₂ K hcycB₂K
  have hresB₂K : residueDegree B₂ K = 1 := by
    have hmul := residueDegree_mul_local (F := F) (K := K) B₂
    rw [hres] at hmul
    exact (mul_eq_one.mp hmul).2
  have hramB₂K : ramificationIndex B₂ K = p := by
    have hdegree := finrank_eq_ramificationIndex_mul_residueDegree B₂ K
    rw [hresB₂K, mul_one, hdegreeUpper] at hdegree
    exact hdegree.symm
  have hbreak : PrimeCyclicExtension.IsLowerBreak B₂ K D.t := by
    simpa only [B₂, Ramification.IntermediateBreakPair] using D.B₂_breaks.2
  have hcharK : residueCharacteristic K = p :=
    (residueCharacteristic_extension_eq F K).trans hchar
  obtain ⟨sigma, pi, c, hsigma, hpi, hc, hsigmapi⟩ :=
    exists_generator_leading_data B₂ K hbreak D.t_pos hresB₂K
  by_cases hpzero : (p : K) = 0
  · have hpzeroB₂ : (p : B₂) = 0 := by
      apply (algebraMap B₂ K).injective
      simpa using hpzero
    have htraceOne : trace B₂ K (1 : K) = 0 := by
      rw [← map_one (algebraMap B₂ K), trace_algebraMap, hdegreeUpper]
      simpa [nsmul_eq_mul] using hpzeroB₂
    have honeker : (1 : K) ∈ (trace B₂ K).ker := by
      rw [LinearMap.mem_ker, htraceOne]
    have hhilbert := additive_hilbert90 B₂ K (sigma : Gal(K/B₂)) hsigma
    rw [hhilbert] at honeker
    obtain ⟨d0, hd0⟩ := honeker
    have hdifference0 : (sigma : Gal(K/B₂)) d0 - d0 = 1 := by
      simpa only [Local.additiveCoboundary_apply] using hd0
    obtain ⟨d, hd, hpt, hdifference⟩ := best_coboundary_generator
      B₂ K hcharK hramB₂K hresB₂K sigma pi c hpi D.t_pos hc hsigmapi
      d0 1 hdifference0 (by simp)
    letI : Fact p.Prime := ⟨hp⟩
    letI : CharP K p := (CharP.charP_iff_prime_eq_zero hp).mpr hpzero
    have hfixed : (sigma : Gal(K/B₂)) (d ^ p - d) = d ^ p - d := by
      rw [map_sub, map_pow]
      have hsigmaD : (sigma : Gal(K/B₂)) d = d + 1 := by
        rw [← hdifference]
        ring
      rw [hsigmaD, add_pow_char]
      ring
    obtain ⟨a, ha⟩ := mem_range_algebraMap_of_generator_fixed
      B₂ K (sigma : Gal(K/B₂)) hsigma (d ^ p - d) hfixed
    refine ⟨d, a, hd, hpt, Or.inl ⟨hpzero, ?_⟩⟩
    exact ha.symm
  · have hpneB₂ : (p : B₂) ≠ 0 := by
      intro hpzeroB₂
      apply hpzero
      simpa using congrArg (algebraMap B₂ K) hpzeroB₂
    obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp
      ((ord_ne_top_iff B₂).mpr hpneB₂)
    have heord : ord B₂ (p : B₂) = (e : WithTop ℤ) := he.symm
    let V : ℤ := (p : ℤ) * e
    have hV : ord K (p : K) = (V : WithTop ℤ) := by
      rw [show (p : K) = algebraMap B₂ K (p : B₂) by simp,
        ord_algebraMap, hramB₂K, heord]
      rw [← WithTop.coe_nsmul]
      congr 1
    have hprimeBound := oddTotal_primeValuationBound hp hG hres D
    rw [hV] at hprimeBound
    have hprimeBoundZ :
        (((p * (p - 1) * D.t₂ : ℕ) : ℤ)) ≤ V :=
      WithTop.coe_le_coe.mp hprimeBound
    have hpZpos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
    have hpOneZ : (1 : ℤ) < (p : ℤ) := by exact_mod_cast hp.one_lt
    have hcastP : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
      omega
    have heLower : (((p - 1) * D.t₂ : ℕ) : ℤ) ≤ e := by
      have hscaled :
          (p : ℤ) * (((p - 1) * D.t₂ : ℕ) : ℤ) ≤ (p : ℤ) * e := by
        calc
          (p : ℤ) * (((p - 1) * D.t₂ : ℕ) : ℤ) =
              ((p * (p - 1) * D.t₂ : ℕ) : ℤ) := by norm_num [mul_assoc]
          _ ≤ V := hprimeBoundZ
          _ = (p : ℤ) * e := rfl
      nlinarith
    have heLowerT : (((p - 1) * D.t : ℕ) : ℤ) ≤ e := by
      apply le_trans ?_ heLower
      have hnat := Nat.mul_le_mul_left (p - 1) D.t_le_t₂
      exact_mod_cast hnat
    let kappa : ℤ := V - (((p - 1) * D.t : ℕ) : ℤ)
    have hkappapos : 0 < kappa := by
      have hApos : (0 : ℤ) < (((p - 1) * D.t : ℕ) : ℤ) := by
        have hnat : 0 < (p - 1) * D.t :=
          Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) D.t_pos
        exact_mod_cast hnat
      have hpe :
          (p : ℤ) * (((p - 1) * D.t : ℕ) : ℤ) ≤ (p : ℤ) * e :=
        mul_le_mul_of_nonneg_left heLowerT hpZpos.le
      have hAlt : (((p - 1) * D.t : ℕ) : ℤ) <
          (p : ℤ) * (((p - 1) * D.t : ℕ) : ℤ) := by
        nlinarith
      have hApe : (((p - 1) * D.t : ℕ) : ℤ) < (p : ℤ) * e :=
        lt_of_lt_of_le hAlt hpe
      dsimp only [kappa, V]
      exact sub_pos.mpr hApe
    obtain ⟨piO, hpiO, hgen⟩ :=
      exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one
        B₂ K hresB₂K
    have htraceImage := cyclicPrime_trace_lattice_image_eq
      B₂ K hbreak hresB₂K piO hpiO hgen kappa
    rw [hdegreeUpper] at htraceImage
    have htraceDepth :
        (kappa + (((p - 1) * (D.t + 1) : ℕ) : ℤ)) / (p : ℤ) = e := by
      dsimp only [kappa, V]
      push_cast
      rw [hcastP]
      rw [show
        (p : ℤ) * e - ((p : ℤ) - 1) * (D.t : ℤ) +
            ((p : ℤ) - 1) * ((D.t : ℤ) + 1) =
          (p : ℤ) * e + ((p : ℤ) - 1) by ring]
      rw [Int.mul_add_ediv_left e ((p : ℤ) - 1)
        (by exact_mod_cast hp.ne_zero)]
      rw [Int.ediv_eq_zero_of_lt]
      · ring
      · omega
      · omega
    rw [htraceDepth] at htraceImage
    have hpLattice : -(p : B₂) ∈ lattice B₂ e := by
      rw [mem_lattice, ord_neg, heord]
    have hpImage : -(p : B₂) ∈
        Submodule.map ((trace B₂ K).restrictScalars (ringOfIntegers B₂))
          ((lattice K kappa).restrictScalars (ringOfIntegers B₂)) := by
      rw [htraceImage]
      exact hpLattice
    obtain ⟨eta, heta, htraceEta⟩ := Submodule.mem_map.mp hpImage
    have htraceEta' : trace B₂ K eta = -(p : B₂) := by
      exact htraceEta
    have htraceOne : trace B₂ K (1 : K) = (p : B₂) := by
      rw [← map_one (algebraMap B₂ K), trace_algebraMap, hdegreeUpper]
      simp [nsmul_eq_mul]
    have hqker : (1 + eta : K) ∈ (trace B₂ K).ker := by
      rw [LinearMap.mem_ker, map_add, htraceOne, htraceEta']
      ring
    have hhilbert := additive_hilbert90 B₂ K (sigma : Gal(K/B₂)) hsigma
    rw [hhilbert] at hqker
    obtain ⟨d0, hd0⟩ := hqker
    have hdifference0 : (sigma : Gal(K/B₂)) d0 - d0 = 1 + eta := by
      simpa only [Local.additiveCoboundary_apply] using hd0
    have hetaOrder : (kappa : WithTop ℤ) ≤ ord K eta := by
      exact (mem_lattice K).mp heta
    have hetaPositive : (0 : WithTop ℤ) < ord K eta := by
      exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hkappapos) hetaOrder
    have hqord : ord K (1 + eta) = 0 := by
      rw [ord_add_eq_min K (by simpa only [ord_one] using ne_of_lt hetaPositive),
        ord_one]
      exact min_eq_left hetaPositive.le
    obtain ⟨d, hd, hpt, hdifference⟩ := best_coboundary_generator
      B₂ K hcharK hramB₂K hresB₂K sigma pi c hpi D.t_pos hc hsigmapi
      d0 (1 + eta) hdifference0 hqord
    have hmoveMem := artinSchreier_displacement_mem B₂ K hp hV D.t_pos
      (show kappa = V - (((p - 1) * D.t : ℕ) : ℤ) by rfl)
      hkappapos (sigma : Gal(K/B₂)) d eta hd heta hdifference
    have hmove : (kappa : WithTop ℤ) ≤
        ord K ((sigma : Gal(K/B₂)) (d ^ p - d) - (d ^ p - d)) :=
      (mem_lattice K).mp hmoveMem
    obtain ⟨a, ha⟩ := exists_fixed_approximation_of_displacement
      B₂ K hcharK hramB₂K hresB₂K sigma hsigma pi c hpi D.t_pos hc
      hsigmapi (d ^ p - d) kappa hmove
    have hfinalDepth : kappa - (D.t : ℕ) =
        V - ((p * D.t : ℕ) : ℤ) := by
      dsimp only [kappa]
      push_cast
      rw [hcastP]
      ring
    refine ⟨d, a, hd, hpt, Or.inr ⟨hpzero, V, hV, ?_⟩⟩
    rwa [← hfinalDepth]

end

end LanglandsSecondMainLemma.Odd.Total
