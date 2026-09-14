import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Ramification.Inertia

/-!
# Ramification / Leading Term

This file proves Paper Lemma C.3 for a genuine finite Galois extension of nonarchimedean
local fields.  The weak lower bound is retained separately because conductor arguments often
need it without the prime-to-`p` hypothesis.  The exact result uses the positive unit graded
line, so integer powers—and in particular negative valuations—are handled uniformly.
-/


namespace LanglandsSecondMainLemma.Ramification

open LanglandsFirstMainLemma

noncomputable section

variable {K : Type*} [Field K]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Every integer power of a positive-depth principal unit stays at that depth. -/
private theorem one_add_zpow_sub_one_mem_lattice
    {t : K} {u : ℕ} (hu : 1 ≤ u) (ht : t ∈ lattice K (u : ℤ)) (m : ℤ) :
    (1 + t) ^ m - 1 ∈ lattice K (u : ℤ) := by
  have hun : u - 1 + 1 = u := Nat.sub_add_cancel hu
  have ht' : t ∈ lattice K ((u - 1 + 1 : ℕ) : ℤ) := by
    simpa only [hun] using ht
  let q0 : Kˣ := principalUnitOf K (u - 1) t ht'
  have hq0coe : (q0 : K) = 1 + t := by
    dsimp only [q0]
    rw [coe_principalUnitOf]
  have hqmem : q0 ∈ unitFiltration K u := by
    dsimp only [q0]
    simpa only [hun] using principalUnitOf_mem K (u - 1) t ht'
  let q : unitFiltration K u := ⟨q0, hqmem⟩
  let qm : unitFiltration K u := q ^ m
  have hqmcoe : ((qm : Kˣ) : K) = (1 + t) ^ m := by
    calc
      ((qm : Kˣ) : K) = ((q0 ^ m : Kˣ) : K) := rfl
      _ = (q0 : K) ^ m := (Units.coeHom K).map_zpow q0 m
      _ = (1 + t) ^ m := by rw [hq0coe]
  have hqmp : (qm : Kˣ) ∈ unitFiltration K (u - 1 + 1) := by
    simpa only [hun] using qm.prop
  have hdiff :=
    (mem_unitFiltration_succ_iff_sub_mem_lattice K (u - 1) (qm : Kˣ)).1 hqmp
  simpa only [hun, hqmcoe] using hdiff

private theorem principalUnit_zpow_sub_one_ord
    {pi c : K} (hpi : (ValuativeRel.valuation K).IsUniformizer pi)
    {u : ℕ} (hu : 1 ≤ u) (hc : ord K c = 0) (m : ℤ)
    (hm : ¬ (residueCharacteristic K : ℤ) ∣ m) :
    ord K ((1 + c * pi ^ u) ^ m - 1) = ((u : ℤ) : WithTop ℤ) := by
  let t : K := c * pi ^ u
  have htord : ord K t = ((u : ℤ) : WithTop ℤ) := by
    dsimp only [t]
    rw [ord_mul, hc, ord_pow, ord_uniformizer K hpi, zero_add]
    norm_num
  have ht : t ∈ lattice K (u : ℤ) := by
    rw [mem_lattice, htord]
  have hun : u - 1 + 1 = u := Nat.sub_add_cancel hu
  have ht' : t ∈ lattice K ((u - 1 + 1 : ℕ) : ℤ) := by
    simpa only [hun] using ht
  let q0 : Kˣ := principalUnitOf K (u - 1) t ht'
  have hq0coe : (q0 : K) = 1 + t := by
    dsimp only [q0]
    rw [coe_principalUnitOf]
  have hqmem : q0 ∈ unitFiltration K u := by
    dsimp only [q0]
    simpa only [hun] using principalUnitOf_mem K (u - 1) t ht'
  let q : unitFiltration K u := ⟨q0, hqmem⟩
  let qm : unitFiltration K u := q ^ m
  have hqmcoe : ((qm : Kˣ) : K) = (1 + t) ^ m := by
    calc
      ((qm : Kˣ) : K) = ((q0 ^ m : Kˣ) : K) := rfl
      _ = (q0 : K) ^ m := (Units.coeHom K).map_zpow q0 m
      _ = (1 + t) ^ m := by rw [hq0coe]
  have hcint : c ∈ lattice K 0 := by
    rw [mem_lattice, hc]
    simp
  have hcred : reduce K c hcint ≠ 0 := by
    intro hzero
    change residueMap K
      ⟨c, (mem_lattice_zero_iff K).1 hcint⟩ = 0 at hzero
    rw [residueMap_eq_zero_iff] at hzero
    change c ∈ lattice K 1 at hzero
    rw [mem_lattice, hc] at hzero
    exact (not_le_of_gt (show (0 : WithTop ℤ) < 1 by norm_num)) hzero
  have hmcast : (m : ResidueField K) ≠ 0 := by
    rw [ne_eq, CharP.intCast_eq_zero_iff
      (ResidueField K) (residueCharacteristic K)]
    exact hm
  let e := criticalNormPositiveUnitGradedResidueAddEquiv K
    (show 0 < u by omega) pi hpi
  have heq : e (Additive.ofMul (unitGradedMk K u q)) =
      reduce K c hcint := by
    dsimp only [e]
    rw [criticalNormPositiveUnitGradedResidueAddEquiv_mk]
    apply congrArg (fun z : ringOfIntegers K => residueMap K z)
    apply Subtype.ext
    change (((q0 : K) - 1) / pi ^ u) = c
    rw [hq0coe]
    dsimp only [t]
    field_simp [pow_ne_zero _ hpi.ne_zero]
    ring
  have hclass : unitGradedMk K u qm ≠ 1 := by
    intro hone
    have himage : e (Additive.ofMul (unitGradedMk K u qm)) = 0 := by
      rw [hone]
      simp
    have himage' : e (Additive.ofMul (unitGradedMk K u qm)) =
        (m : ResidueField K) * reduce K c hcint := by
      calc
        e (Additive.ofMul (unitGradedMk K u qm)) =
            e (m • Additive.ofMul (unitGradedMk K u q)) := by
          simp only [qm, map_zpow, ofMul_zpow]
        _ = m • e (Additive.ofMul (unitGradedMk K u q)) := by
          exact map_zsmul e m _
        _ = (m : ResidueField K) * reduce K c hcint := by
          rw [heq, zsmul_eq_mul]
    rw [himage'] at himage
    exact mul_ne_zero hmcast hcred himage
  have hqmnot : (qm : Kˣ) ∉ unitFiltration K (u + 1) := by
    intro hdeep
    exact hclass ((unitGradedMk_eq_one_iff K u qm).2 hdeep)
  have hun2 : u - 1 + 2 = u + 1 := by omega
  have hqmnumerator : (qm : Kˣ) ∈ unitFiltration K (u - 1 + 1) := by
    rw [hun]
    exact qm.prop
  have hqmdenominator : (qm : Kˣ) ∉ unitFiltration K (u - 1 + 2) := by
    rw [hun2]
    exact hqmnot
  have hshell :=
    (mem_unitFiltration_and_not_mem_succ_iff K (u - 1) (qm : Kˣ)).1
      ⟨hqmnumerator, hqmdenominator⟩
  rw [hun] at hshell
  rw [← hqmcoe]
  exact hshell

variable {F : Type*} [Field F]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]
variable [IsGalois F K]

/-- On inertia, every upstairs uniformizer detects membership in every lower ramification
group.  The base ring for monogenicity is the actual inertia fixed field. -/
private theorem mem_lowerRamificationGroup_iff_uniformizer
    (sigma : lowerRamificationGroup F K 0) (i : ℤ)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K)) :
    (sigma : Gal(K/F)) ∈ lowerRamificationGroup F K i ↔
      CongruentAtDepth (i + 1) ((sigma : Gal(K/F)) (pi : K)) (pi : K) := by
  constructor
  · intro hsigma
    exact (mem_lowerRamificationGroup F K (sigma : Gal(K/F)) i).1 hsigma pi
  · intro hpicon
    let E := inertiaFixedField (F := F) (K := K)
    letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E
    letI : TopologicalSpace E := Basic.intermediateFieldTopology E
    letI : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E
    letI : ValuativeExtension E K := Basic.intermediateField_upperValuativeExtension E
    have hres : residueDegree E K = 1 :=
      inertiaFixedField_residueDegree (F := F) (K := K)
    have hgen : Algebra.adjoin (ringOfIntegers E)
        ({pi} : Set (ringOfIntegers K)) = ⊤ :=
      algebra_adjoin_uniformizer_eq_top_of_residueDegree_eq_one E K hres pi hpi
    rw [mem_lowerRamificationGroup]
    intro x
    have hx : x ∈ Algebra.adjoin (ringOfIntegers E)
        ({pi} : Set (ringOfIntegers K)) := by
      rw [hgen]
      trivial
    exact Algebra.adjoin_induction (p := fun (z : ringOfIntegers K) _ =>
        CongruentAtDepth (i + 1) ((sigma : Gal(K/F)) (z : K)) (z : K))
      (fun z hz => by
        rw [Set.mem_singleton_iff.mp hz]
        exact hpicon)
      (fun r => by
        have hsigmaI : (sigma : Gal(K/F)) ∈
            inertiaSubgroup (F := F) (K := K) := by
          rw [inertiaSubgroup_eq_lowerRamificationGroup_zero]
          exact sigma.prop
        have hrmem : ((r : E) : K) ∈
            IntermediateField.fixedField
              (inertiaSubgroup (F := F) (K := K)) := by
          rw [← inertiaFixedField_eq_fixedField (F := F) (K := K)]
          exact r.val.property
        have hrfix : (sigma : Gal(K/F)) ((r : E) : K) = ((r : E) : K) :=
          (IntermediateField.mem_fixedField_iff
              (inertiaSubgroup (F := F) (K := K)) ((r : E) : K)).mp hrmem
            (sigma : Gal(K/F)) hsigmaI
        have heq :
            (sigma : Gal(K/F))
                (((algebraMap (ringOfIntegers E) (ringOfIntegers K) r) :
                  ringOfIntegers K) : K) =
              (((algebraMap (ringOfIntegers E) (ringOfIntegers K) r) :
                ringOfIntegers K) : K) := by
          simpa using hrfix
        rw [heq]
        exact CongruentAtDepth.refl _)
      (fun a b _ _ ha hb => by
        simpa only [map_add, Subring.coe_add] using ha.add hb)
      (fun a b _ _ ha hb => by
        have hsigmaa : (0 : WithTop ℤ) ≤
            ord K ((sigma : Gal(K/F)) (a : K)) :=
          (ord_nonneg_iff_mem_integer K _).2
            ((galoisConjugate_mem_ringOfIntegers_iff F K
              (sigma : Gal(K/F)) (a : K)).2 a.prop)
        have hb0 : (0 : WithTop ℤ) ≤ ord K (b : K) :=
          (ord_nonneg_iff_mem_integer K _).2 b.prop
        simpa only [map_mul, Subring.coe_mul] using ha.mul hsigmaa hb0 hb)
      hx

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem mul_zpow_of_ne_zero
    {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (m : ℤ) :
    (a * b) ^ m = a ^ m * b ^ m := by
  let aU : Kˣ := Units.mk0 a ha
  let bU : Kˣ := Units.mk0 b hb
  calc
    (a * b) ^ m = (((aU * bU : Kˣ) : K)) ^ m := rfl
    _ = (((aU * bU) ^ m : Kˣ) : K) :=
      ((Units.coeHom K).map_zpow (aU * bU) m).symm
    _ = ((aU ^ m * bU ^ m : Kˣ) : K) := by rw [mul_zpow]
    _ = ((aU ^ m : Kˣ) : K) * ((bU ^ m : Kˣ) : K) := rfl
    _ = a ^ m * b ^ m := by
      apply congrArg₂ (· * ·)
      · exact (Units.coeHom K).map_zpow aU m
      · exact (Units.coeHom K).map_zpow bU m

/-- Once the uniformizer moves first in degree `u + 1`, inertia moves every integral element
in degree at least `u + 1`. -/
private theorem inertia_congruentAtDepth_succ_of_uniformizer
    (sigma : lowerRamificationGroup F K 0) (pi c : K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer pi)
    {u : ℕ} (hc : ord K c = 0)
    (hsigmapi : (sigma : Gal(K/F)) pi = pi * (1 + c * pi ^ u))
    (x : ringOfIntegers K) :
    CongruentAtDepth ((u : ℤ) + 1)
      ((sigma : Gal(K/F)) (x : K)) (x : K) := by
  let t : K := c * pi ^ u
  have htord : ord K t = ((u : ℤ) : WithTop ℤ) := by
    dsimp only [t]
    rw [ord_mul, hc, ord_pow, ord_uniformizer K hpi, zero_add]
    norm_num
  have hpiint : pi ∈ lattice K 0 := by
    rw [mem_lattice, ord_uniformizer K hpi]
    norm_num
  let piO : ringOfIntegers K :=
    ⟨pi, (mem_lattice_zero_iff K).1 hpiint⟩
  have hpicon : CongruentAtDepth ((u : ℤ) + 1)
      ((sigma : Gal(K/F)) pi) pi := by
    rw [CongruentAtDepth, hsigmapi]
    change (((u : ℤ) + 1 : ℤ) : WithTop ℤ) ≤
      ord K (pi * (1 + t) - pi)
    rw [show pi * (1 + t) - pi = pi * t by ring, ord_mul,
      ord_uniformizer K hpi, htord]
    norm_num [add_comm]
  have hsigmadeep : (sigma : Gal(K/F)) ∈
      lowerRamificationGroup F K (u : ℤ) := by
    apply (mem_lowerRamificationGroup_iff_uniformizer
      (F := F) (K := K) sigma (u : ℤ) piO hpi).2
    simpa only [piO] using hpicon
  exact (mem_lowerRamificationGroup F K (sigma : Gal(K/F)) (u : ℤ)).1
    hsigmadeep x

/-- An inertia automorphism whose uniformizer displacement starts in degree `u` moves every
nonzero element of order `m` by an element of order at least `m + u`. -/
theorem leadingTerm_lowerBound
    (sigma : lowerRamificationGroup F K 0) (pi c : K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer pi)
    {u : ℕ} (hu : 1 ≤ u) (hc : ord K c = 0)
    (hsigmapi : (sigma : Gal(K/F)) pi = pi * (1 + c * pi ^ u))
    {x : K} {m : ℤ} (_hx : x ≠ 0)
    (hxord : ord K x = (m : WithTop ℤ)) :
    ((m + (u : ℕ) : ℤ) : WithTop ℤ) ≤
      ord K ((sigma : Gal(K/F)) x - x) := by
  let t : K := c * pi ^ u
  let q : K := 1 + t
  have htord : ord K t = ((u : ℤ) : WithTop ℤ) := by
    dsimp only [t]
    rw [ord_mul, hc, ord_pow, ord_uniformizer K hpi, zero_add]
    norm_num
  have ht : t ∈ lattice K (u : ℤ) := by
    rw [mem_lattice, htord]
  have htpos : (0 : WithTop ℤ) < ord K t := by
    rw [htord]
    exact WithTop.coe_lt_coe.mpr (by omega)
  have hqord : ord K q = 0 := by
    dsimp only [q]
    rw [ord_add_eq_min K (by simpa only [ord_one] using ne_of_lt htpos), ord_one]
    exact min_eq_left htpos.le
  have hqne : q ≠ 0 := by
    intro hzero
    rw [hzero, ord_zero] at hqord
    exact WithTop.top_ne_coe hqord
  have hqmord : ord K (q ^ m) = 0 := by
    rw [ord_zpow, hqord]
    simp
  have hpimord : ord K (pi ^ m) = (m : WithTop ℤ) :=
    ord_uniformizer_zpow K hpi m
  have hmulz : (pi * q) ^ m = pi ^ m * q ^ m :=
    mul_zpow_of_ne_zero hpi.ne_zero hqne m
  let a : K := x / pi ^ m
  have haord : ord K a = 0 := by
    dsimp only [a]
    rw [ord_div, hxord, hpimord]
    simp
  have haint : a ∈ lattice K 0 := by
    rw [mem_lattice, haord]
    simp
  let aO : ringOfIntegers K :=
    ⟨a, (mem_lattice_zero_iff K).1 haint⟩
  have hacon : CongruentAtDepth ((u : ℤ) + 1)
      ((sigma : Gal(K/F)) a) a := by
    simpa only [aO] using
      inertia_congruentAtDepth_succ_of_uniformizer
        (F := F) (K := K) sigma pi c hpi hc hsigmapi aO
  have hadiff : (((u : ℤ) + 1 : ℤ) : WithTop ℤ) ≤
      ord K ((sigma : Gal(K/F)) a - a) := hacon
  have hpowdiff : ((u : ℤ) : WithTop ℤ) ≤ ord K (q ^ m - 1) := by
    have hmem := one_add_zpow_sub_one_mem_lattice hu ht m
    rw [mem_lattice] at hmem
    simpa only [q] using hmem
  have hxfactor : a * pi ^ m = x := by
    dsimp only [a]
    exact div_mul_cancel₀ x (zpow_ne_zero m hpi.ne_zero)
  let d1 : K := ((sigma : Gal(K/F)) a - a) * pi ^ m * q ^ m
  let d2 : K := a * pi ^ m * (q ^ m - 1)
  have hd1 : ((m + (u : ℕ) : ℤ) : WithTop ℤ) ≤ ord K d1 := by
    dsimp only [d1]
    rw [ord_mul, ord_mul, hpimord, hqmord, add_zero]
    have hadiff' : ((u : ℤ) : WithTop ℤ) ≤
        ord K ((sigma : Gal(K/F)) a - a) :=
      (WithTop.coe_le_coe.mpr (show (u : ℤ) ≤ (u : ℤ) + 1 by omega)).trans hadiff
    have h := add_le_add_right hadiff' (m : WithTop ℤ)
    simpa only [WithTop.coe_add, add_comm] using h
  have hd2 : ((m + (u : ℕ) : ℤ) : WithTop ℤ) ≤ ord K d2 := by
    dsimp only [d2]
    rw [ord_mul, ord_mul, haord, zero_add, hpimord]
    have h := add_le_add_left hpowdiff (m : WithTop ℤ)
    simpa only [WithTop.coe_add, add_comm] using h
  have hdecomp : (sigma : Gal(K/F)) x - x = d1 + d2 := by
    dsimp only [d1, d2]
    rw [← hxfactor, map_mul, map_zpow₀, hsigmapi]
    change (sigma : Gal(K/F)) a * (pi * q) ^ m - a * pi ^ m = _
    rw [hmulz]
    ring
  rw [hdecomp]
  simpa only [min_self] using (min_le_min hd1 hd2).trans (ord_add K d1 d2)

/-- The first wild ramification term.  If the normalized order `m` is prime to the
residue characteristic, the lower bound is exact, including for negative `m`. -/
theorem leadingTerm
    (sigma : lowerRamificationGroup F K 0) (pi c : K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer pi)
    {u : ℕ} (hu : 1 ≤ u) (hc : ord K c = 0)
    (hsigmapi : (sigma : Gal(K/F)) pi = pi * (1 + c * pi ^ u))
    {x : K} {m : ℤ} (_hx : x ≠ 0)
    (hxord : ord K x = (m : WithTop ℤ))
    (hm : ¬ (residueCharacteristic K : ℤ) ∣ m) :
    ord K ((sigma : Gal(K/F)) x - x) =
      ((m + (u : ℕ) : ℤ) : WithTop ℤ) := by
  let t : K := c * pi ^ u
  let q : K := 1 + t
  have htord : ord K t = ((u : ℤ) : WithTop ℤ) := by
    dsimp only [t]
    rw [ord_mul, hc, ord_pow, ord_uniformizer K hpi, zero_add]
    norm_num
  have ht : t ∈ lattice K (u : ℤ) := by
    rw [mem_lattice, htord]
  have htpos : (0 : WithTop ℤ) < ord K t := by
    rw [htord]
    exact WithTop.coe_lt_coe.mpr (by omega)
  have hqord : ord K q = 0 := by
    dsimp only [q]
    rw [ord_add_eq_min K (by simpa only [ord_one] using ne_of_lt htpos), ord_one]
    exact min_eq_left htpos.le
  have hqne : q ≠ 0 := by
    intro hzero
    rw [hzero, ord_zero] at hqord
    exact WithTop.top_ne_coe hqord
  have hqmord : ord K (q ^ m) = 0 := by
    rw [ord_zpow, hqord]
    simp
  have hpimord : ord K (pi ^ m) = (m : WithTop ℤ) :=
    ord_uniformizer_zpow K hpi m
  have hmulz : (pi * q) ^ m = pi ^ m * q ^ m :=
    mul_zpow_of_ne_zero hpi.ne_zero hqne m
  let a : K := x / pi ^ m
  have haord : ord K a = 0 := by
    dsimp only [a]
    rw [ord_div, hxord, hpimord]
    simp
  have haint : a ∈ lattice K 0 := by
    rw [mem_lattice, haord]
    simp
  let aO : ringOfIntegers K :=
    ⟨a, (mem_lattice_zero_iff K).1 haint⟩
  have hacon : CongruentAtDepth ((u : ℤ) + 1)
      ((sigma : Gal(K/F)) a) a := by
    simpa only [aO] using
      inertia_congruentAtDepth_succ_of_uniformizer
        (F := F) (K := K) sigma pi c hpi hc hsigmapi aO
  have hadiff : (((u : ℤ) + 1 : ℤ) : WithTop ℤ) ≤
      ord K ((sigma : Gal(K/F)) a - a) := hacon
  have hpowexact : ord K (q ^ m - 1) = ((u : ℤ) : WithTop ℤ) := by
    simpa only [q, t] using
      principalUnit_zpow_sub_one_ord hpi hu hc m hm
  have hxfactor : a * pi ^ m = x := by
    dsimp only [a]
    exact div_mul_cancel₀ x (zpow_ne_zero m hpi.ne_zero)
  let d1 : K := ((sigma : Gal(K/F)) a - a) * pi ^ m * q ^ m
  let d2 : K := a * pi ^ m * (q ^ m - 1)
  have hd1 : (((m + (u : ℕ) : ℤ) + 1 : ℤ) : WithTop ℤ) ≤ ord K d1 := by
    dsimp only [d1]
    rw [ord_mul, ord_mul, hpimord, hqmord, add_zero]
    have h := add_le_add_right hadiff (m : WithTop ℤ)
    simpa only [WithTop.coe_add, add_assoc, add_comm, add_left_comm] using h
  have hd2 : ord K d2 = ((m + (u : ℕ) : ℤ) : WithTop ℤ) := by
    dsimp only [d2]
    rw [ord_mul, ord_mul, haord, zero_add, hpimord, hpowexact]
    simp only [WithTop.coe_add]
  have hd2lt1 : ord K d2 < ord K d1 := by
    rw [hd2]
    exact (WithTop.coe_lt_coe.mpr
      (show m + (u : ℕ) < (m + (u : ℕ) : ℤ) + 1 by omega)).trans_le hd1
  have hdecomp : (sigma : Gal(K/F)) x - x = d1 + d2 := by
    dsimp only [d1, d2]
    rw [← hxfactor, map_mul, map_zpow₀, hsigmapi]
    change (sigma : Gal(K/F)) a * (pi * q) ^ m - a * pi ^ m = _
    rw [hmulz]
    ring
  rw [hdecomp, ord_add_eq_min K (ne_of_gt hd2lt1), min_eq_right hd2lt1.le, hd2]

end

end LanglandsSecondMainLemma.Ramification
