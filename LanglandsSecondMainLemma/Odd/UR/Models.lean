import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Odd.UR.Setup
import LanglandsSecondMainLemma.Odd.NormPhase
import LanglandsSecondMainLemma.Local.NormDescent
import LanglandsSecondMainLemma.Characters.CrossedNorm

/-!
# Odd / UR / Models

Paper: Proposition `O:I:canonical`, corrected source lines 1318--1385,
with the ambient setup in lines 1060--1128 and 1298--1316.

The theorem `models` constructs the two actual continuous characters from
`OddURSetup`. It proves their exact conductors, their full logarithm charts,
the global Frobenius commutator, and invariance and primitivity of their
common norm pullback. The additive normalization is constructed for every
nontrivial continuous additive character of the base field.

Integral trace-one descent replaces the paper's truncated Teichmüller
expansion in the overlap argument; it works for every multiplicative input,
including the valuation factor. The Artin--Schreier precision is proved by
finite-field trace and quantitative Hensel uniqueness. The ramified chart
uses the literal norm `N(d) = d^p`, the norm-log error on its full ideal,
and the proved norm-phase identity. The final chart descends through the
surjective unramified norm on the entire stated principal-unit subgroup.

Both equal and mixed characteristic are retained. All depths that can be
negative are integer lattice exponents, and all characters are continuous
group homomorphisms. No auxiliary model or commutator is a hypothesis of
`models`; the intermediate construction has a proved setup adapter.
-/

namespace LanglandsSecondMainLemma.Odd.UR
noncomputable section
open LanglandsFirstMainLemma

section LogCharacter
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- The actual logarithm character on the whole positive unit subgroup. -/
def logarithmCharacter (p q T : ℕ)
    (hchar : residueCharacteristic L = p) (hp : p.Prime)
    (hq : 0 < q) (hT : T ≤ p * q)
    (Psi : ContinuousAddChar L) (hPsi : AddCharTrivialOnLattice L Psi (T : ℤ))
    (a : ringOfIntegers L) : unitFiltration L q →* ℂˣ where
  toFun u := Psi ((a : L) * truncatedLog p (1 - ((u : Lˣ) : L)))
  map_one' := by
    have hzero : truncatedLog p (0 : L) = 0 := by
      rw [truncatedLog_apply, zero_add]
      apply Finset.sum_eq_zero
      intro j hj
      simp [ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) (Finset.mem_Ico.mp hj).1)]
    change Psi ((a : L) * truncatedLog p (1 - 1)) = 1
    rw [sub_self, hzero, mul_zero, Psi.map_zero_eq_one]
  map_mul' u v := by
    let z : L := 1 - ((u : Lˣ) : L)
    let w : L := 1 - ((v : Lˣ) : L)
    have hz : z ∈ lattice L (q : ℤ) :=
      by simpa [z] using (truncatedLogUnitArgument L hq u).property
    have hw : w ∈ lattice L (q : ℤ) :=
      by simpa [w] using (truncatedLogUnitArgument L hq v).property
    have he := lattice_antitone L (show (T : ℤ) ≤ ((p * q : ℕ) : ℤ) by exact_mod_cast hT)
      (truncatedLog_defect_mem_lattice L p q hchar hp hz hw)
    have hae : (a : L) *
        (truncatedLog p (z + w - z * w) - truncatedLog p z - truncatedLog p w)
        ∈ lattice L (T : ℤ) := by
      simpa using mul_mem_lattice L ((mem_lattice_zero_iff L).2 a.property) he
    have heval := hPsi _ hae
    have heq : 1 - (((u * v : unitFiltration L q) : Lˣ) : L) = z + w - z * w := by
      simp only [Subgroup.coe_mul, Units.val_mul, z, w]
      ring
    change Psi ((a : L) * truncatedLog p (1 - (((u * v : unitFiltration L q) : Lˣ) : L))) = _
    rw [heq]
    have hequal : Psi ((a : L) * truncatedLog p (z + w - z * w)) =
        Psi ((a : L) * truncatedLog p z + (a : L) * truncatedLog p w) := by
      apply div_eq_one.mp
      calc
        _ = Psi ((a : L) * truncatedLog p (z + w - z * w) -
            ((a : L) * truncatedLog p z + (a : L) * truncatedLog p w)) :=
          (Psi.toAddChar.map_sub_eq_div _ _).symm
        _ = 1 := by
          convert heval using 1
          congr 1
          ring
    exact hequal.trans (Psi.map_add_eq_mul _ _)

@[simp] theorem logarithmCharacter_one_sub (p q T : ℕ)
    (hchar : residueCharacteristic L = p) (hp : p.Prime)
    (hq : 0 < q) (hT : T ≤ p * q)
    (Psi : ContinuousAddChar L) (hPsi : AddCharTrivialOnLattice L Psi (T : ℤ))
    (a : ringOfIntegers L) (z : lattice L (q : ℤ)) :
    logarithmCharacter L p q T hchar hp hq hT Psi hPsi a
        (positiveUnitOfLattice L hq (-z)) = Psi ((a : L) * truncatedLog p (z : L)) := by
  simp [logarithmCharacter]

/-- Triviality is on the entire conductor layer, not at a test point. -/
theorem logarithmCharacter_trivial (p q T : ℕ)
    (hchar : residueCharacteristic L = p) (hp : p.Prime)
    (hq : 0 < q) (hqT : q ≤ T) (hT : T ≤ p * q)
    (Psi : ContinuousAddChar L) (hPsi : AddCharTrivialOnLattice L Psi (T : ℤ))
    (a : ringOfIntegers L) (u : unitFiltration L q)
    (hu : (u : Lˣ) ∈ unitFiltration L T) :
    logarithmCharacter L p q T hchar hp hq hT Psi hPsi a u = 1 := by
  have hTpos : 0 < T := lt_of_lt_of_le hq hqT
  let z := truncatedLogUnitArgument L hTpos ⟨(u : Lˣ), hu⟩
  have hP : truncatedLog p (1 - ((u : Lˣ) : L)) ∈ lattice L (T : ℤ) := by
    simpa [z, truncatedLogOnLattice] using
      (truncatedLogOnLattice L p T hchar hTpos z).property
  apply hPsi
  simpa using mul_mem_lattice L ((mem_lattice_zero_iff L).2 a.property) hP

/-- Any extension of a unit-coefficient logarithm chart has exact conductor `T`.
The proof uses the full preceding additive lattice and the bijectivity of `P`. -/
theorem logarithmCharacter_conductor (p q T : ℕ)
    (hchar : residueCharacteristic L = p) (hp : p.Prime)
    (hq : 0 < q) (hqT : q < T) (hT : T ≤ p * q)
    (Psi : ContinuousAddChar L) (hPsi : IsAdditiveConductor L Psi (-(T : ℤ)))
    (a : ringOfIntegers L) (ha : ord L (a : L) = 0)
    (chi : ContinuousQuasiChar L)
    (hchi : chi.toMonoidHom.comp (unitFiltration L q).subtype =
      logarithmCharacter L p q T hchar hp hq hT Psi (by simpa using hPsi.trivial) a) :
    IsMultiplicativeConductor L chi T := by
  have hpred : 0 < T - 1 := by omega
  have hqpred : q ≤ T - 1 := by omega
  have hsucc : T - 1 + 1 = T := by omega
  rw [← hsucc]
  apply IsMultiplicativeConductor.of_succ_boundary
  · rw [hsucc]
    intro u hu
    let uq : unitFiltration L q := ⟨u, unitFiltration_antitone L (by omega) hu⟩
    have heval := DFunLike.congr_fun hchi uq
    exact heval.trans (logarithmCharacter_trivial L p q T hchar hp hq (by omega)
      hT Psi (by simpa using hPsi.trivial) a uq hu)
  · intro hprev
    obtain ⟨w, hw, _, hwne⟩ := hPsi.exists_ne_one_on_predecessor
    have haw : (a : L)⁻¹ * w ∈ lattice L ((T - 1 : ℕ) : ℤ) := by
      rw [mem_lattice, ord_mul, ord_inv, ha, neg_zero, zero_add]
      have hw' := (mem_lattice L).1 hw
      simpa only [neg_neg, Nat.cast_sub (by omega : 1 ≤ T), Nat.cast_one] using hw'
    obtain ⟨z, hz⟩ := (truncatedLogOnLattice_bijective L p (T - 1) hchar hp hpred).2
      ⟨(a : L)⁻¹ * w, haw⟩
    have hPz : truncatedLog p (z : L) = (a : L)⁻¹ * w := congrArg Subtype.val hz
    let zq : lattice L (q : ℤ) :=
      ⟨(z : L), lattice_antitone L (by exact_mod_cast hqpred) z.property⟩
    have hu : (positiveUnitOfLattice L hq (-zq) : Lˣ) ∈ unitFiltration L (T - 1) := by
      have heq : (positiveUnitOfLattice L hq (-zq) : Lˣ) =
          (positiveUnitOfLattice L hpred (-z) : Lˣ) := by
        apply Units.ext
        simp [zq]
      rw [heq]
      exact (positiveUnitOfLattice L hpred (-z)).property
    have heval := DFunLike.congr_fun hchi (positiveUnitOfLattice L hq (-zq))
    rw [MonoidHom.comp_apply, logarithmCharacter_one_sub] at heval
    have ha0 : (a : L) ≠ 0 := (ord_ne_top_iff L).1 (by simp [ha])
    change chi (positiveUnitOfLattice L hq (-zq)) =
      Psi ((a : L) * truncatedLog p (zq : L)) at heval
    have heval' : chi (positiveUnitOfLattice L hq (-zq)) = Psi w := by
      simpa only [zq, hPz, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul] using heval
    exact hwne (heval'.symm.trans (hprev _ hu))

/-- A full logarithm chart extends to an actual continuous character with its
exact conductor. No commutator constraint is asserted by this preliminary step. -/
theorem logarithmCharacter_extension (p q T : ℕ)
    (hchar : residueCharacteristic L = p) (hp : p.Prime)
    (hq : 0 < q) (hqT : q < T) (hT : T ≤ p * q)
    (Psi : ContinuousAddChar L) (hPsi : IsAdditiveConductor L Psi (-(T : ℤ)))
    (a : ringOfIntegers L) (ha : ord L (a : L) = 0) :
    ∃ chi : ContinuousQuasiChar L, IsMultiplicativeConductor L chi T ∧
      ∀ z : lattice L (q : ℤ),
        chi (positiveUnitOfLattice L hq (-z)) = Psi ((a : L) * truncatedLog p (z : L)) := by
  let hPsiT : AddCharTrivialOnLattice L Psi (T : ℤ) := by simpa using hPsi.trivial
  let f := logarithmCharacter L p q T hchar hp hq hT Psi hPsiT a
  have htriv : f.comp (Subgroup.inclusion (unitFiltration_antitone L (le_of_lt hqT))) = 1 := by
    apply MonoidHom.ext
    intro u
    change f ((Subgroup.inclusion (unitFiltration_antitone L (le_of_lt hqT))) u) = 1
    exact logarithmCharacter_trivial L p q T hchar hp hq (le_of_lt hqT)
      hT Psi hPsiT a (Subgroup.inclusion (unitFiltration_antitone L (le_of_lt hqT)) u) u.property
  obtain ⟨chi, hchi⟩ := Local.characterExtension L (unitFiltration L q) T
    (by omega) (unitFiltration_antitone L (le_of_lt hqT)) f htriv
  refine ⟨chi, logarithmCharacter_conductor L p q T hchar hp hq hqT hT
    Psi hPsi a ha chi hchi, ?_⟩
  intro z
  exact (DFunLike.congr_fun hchi (positiveUnitOfLattice L hq (-z))).trans
    (logarithmCharacter_one_sub L p q T hchar hp hq hT Psi hPsiT a z)

/-- Equivalent forms of a full chart, on `1-z` and on all principal units. -/
theorem one_sub_chart_iff_units (p q : ℕ) (hq : 0 < q)
    (chi : ContinuousQuasiChar L) (Psi : ContinuousAddChar L) (a : L) :
    (∀ z : lattice L (q : ℤ), chi (positiveUnitOfLattice L hq (-z)) =
      Psi (a * truncatedLog p (z : L))) ↔
    (∀ u : unitFiltration L q, chi (u : Lˣ) =
      Psi (a * truncatedLog p (1 - ((u : Lˣ) : L)))) := by
  constructor
  · intro h u
    let z := truncatedLogUnitArgument L hq u
    have heq : (positiveUnitOfLattice L hq (-z) : Lˣ) = (u : Lˣ) := by
      apply Units.ext
      simp [z]
    simpa only [heq, z, coe_truncatedLogUnitArgument] using h z
  · intro h z
    simpa using h (positiveUnitOfLattice L hq (-z))

end LogCharacter

section CommutatorExtension
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- Extend a subgroup character while retaining an exact commutator prescription.
The hypothesis is precisely the overlap identity; the generated character and
its multiplicativity are constructed by descent from `Lˣ × H`. -/
theorem extendWithCommutator (H : Subgroup Lˣ) (chiH : H →* ℂˣ)
    (delta : Lˣ →* Lˣ) (tau : Lˣ →* ℂˣ)
    (hoverlap : ∀ (x : Lˣ) (hx : delta x ∈ H), chiH ⟨delta x, hx⟩ = tau x)
    (T : ℕ) (hT : 0 < T) (hTH : unitFiltration L T ≤ H)
    (htriv : ∀ u : H, (u : Lˣ) ∈ unitFiltration L T → chiH u = 1) :
    ∃ chi : ContinuousQuasiChar L,
      chi.toMonoidHom.comp H.subtype = chiH ∧
      ∀ x : Lˣ, chi (delta x) = tau x := by
  let f : Lˣ × H →* Lˣ :=
    (delta.comp (MonoidHom.fst Lˣ H)) * (H.subtype.comp (MonoidHom.snd Lˣ H))
  let g : Lˣ × H →* ℂˣ :=
    (tau.comp (MonoidHom.fst Lˣ H)) * (chiH.comp (MonoidHom.snd Lˣ H))
  have hker : f.rangeRestrict.ker ≤ g.ker := by
    intro x hx
    have hf : delta x.1 * (x.2 : Lˣ) = 1 := congrArg Subtype.val hx
    have hd : delta x.1 = ((x.2 : Lˣ))⁻¹ := (mul_eq_one_iff_eq_inv).1 hf
    have hmem : delta x.1 ∈ H := hd ▸ H.inv_mem x.2.property
    have hval := hoverlap x.1 hmem
    have hsub : (⟨delta x.1, hmem⟩ : H) = x.2⁻¹ := Subtype.ext hd
    rw [hsub, map_inv] at hval
    change tau x.1 * chiH x.2 = 1
    rw [← hval, inv_mul_cancel]
  let prescribed : f.range →* ℂˣ :=
    f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨g, hker⟩
  have hprescribed (x : Lˣ × H) : prescribed (f.rangeRestrict x) = g x :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hHF : H ≤ f.range := by
    intro h hh
    exact ⟨(1, ⟨h, hh⟩), by simp [f]⟩
  have hTF : unitFiltration L T ≤ f.range := hTH.trans hHF
  have hrestriction (h : H) : prescribed ⟨(h : Lˣ), hHF h.property⟩ = chiH h := by
    have hf : (⟨(h : Lˣ), hHF h.property⟩ : f.range) = f.rangeRestrict (1, h) := by
      apply Subtype.ext
      simp [f]
    rw [hf, hprescribed]
    simp [g]
  have hzero : prescribed.comp (Subgroup.inclusion hTF) = 1 := by
    apply MonoidHom.ext
    intro u
    change prescribed ⟨(u : Lˣ), hTF u.property⟩ = 1
    exact (hrestriction ⟨(u : Lˣ), hTH u.property⟩).trans (htriv _ u.property)
  obtain ⟨chi, hchi⟩ := Local.characterExtension L f.range T hT hTF prescribed hzero
  refine ⟨chi, ?_, ?_⟩
  · apply MonoidHom.ext
    intro h
    exact (DFunLike.congr_fun hchi ⟨(h : Lˣ), hHF h.property⟩).trans (hrestriction h)
  · intro x
    have hf : f (x, 1) = delta x := by simp [f]
    have heval := DFunLike.congr_fun hchi (f.rangeRestrict (x, 1))
    change chi (f (x, 1)) = prescribed (f.rangeRestrict (x, 1)) at heval
    rw [hf, hprescribed] at heval
    simpa [g] using heval

end CommutatorExtension

section UnramifiedOverlap
variable (F U : Type*) [Field F] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F U] [ValuativeExtension F U]
  [Module.Finite F U] [IsGalois F U]

/-- In an unramified extension, every Galois-fixed class modulo an integer
lattice comes from the base field. An integral trace-one element proves the
statement without choosing a truncated expansion. -/
theorem unramified_invariant_lattice_class
    (hunr : ramificationIndex F U = 1) (q : ℤ) (x : U)
    (hfixed : ∀ sigma : Gal(U/F), sigma x - x ∈ lattice U q) :
    ∃ f : F, x - algebraMap F U f ∈ lattice U q := by
  obtain ⟨a, ha, htrace⟩ := trace_lattice_surjective F U hunr 0 1 (by simp)
  refine ⟨trace F U (a * x), ?_⟩
  have hsum : (∑ sigma : Gal(U/F), sigma a) = 1 := by
    rw [← trace_eq_sum_automorphisms, htrace, map_one]
  have herr : algebraMap F U (trace F U (a * x)) - x =
      ∑ sigma : Gal(U/F), sigma a * (sigma x - x) := by
    rw [trace_eq_sum_automorphisms]
    simp_rw [map_mul, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  suffices hm : algebraMap F U (trace F U (a * x)) - x ∈ lattice U q by
    simpa only [neg_sub] using neg_mem_lattice U hm
  rw [herr]
  apply (lattice U q).sum_mem
  intro sigma _
  have hsa : sigma a ∈ lattice U 0 := by
    simpa only [mem_lattice, ord_galoisConjugate] using ha
  simpa only [zero_add] using mul_mem_lattice U hsa (hfixed sigma)

/-- A fixed class for a cyclic generator is fixed for the whole group. -/
theorem lattice_class_fixed_of_generator
    (sigma : Gal(U/F)) (hgen : ∀ tau : Gal(U/F), tau ∈ Subgroup.zpowers sigma)
    (q : ℤ) (x : U) (hx : sigma x - x ∈ lattice U q) :
    ∀ tau : Gal(U/F), tau x - x ∈ lattice U q := by
  have hmap (tau : Gal(U/F)) {y : U} (hy : y ∈ lattice U q) :
      tau y ∈ lattice U q := by
    simpa only [mem_lattice, ord_galoisConjugate] using hy
  let S : Subgroup Gal(U/F) :=
    { carrier := {tau | tau x - x ∈ lattice U q}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        have h := add_mem_lattice U (hmap a hb) ha
        change (a * b) x - x ∈ lattice U q
        simpa only [AlgEquiv.mul_apply, map_sub, sub_add_sub_cancel] using h
      inv_mem' := by
        intro a ha
        have h := neg_mem_lattice U (hmap a⁻¹ ha)
        change a⁻¹ x - x ∈ lattice U q
        simpa only [map_sub, AlgEquiv.coe_inv, AlgEquiv.symm_apply_apply, neg_sub] using h }
  intro tau
  exact (Subgroup.zpowers_le.mpr (show sigma ∈ S from hx)) (hgen tau)


/-- Exact multiplicative descent of a class fixed modulo `U^q`.  This is the
paper's assertion `v = f h` on the overlap of the commutator image and `U^q`;
it holds for every nonzero element, including the valuation factor. -/
theorem unramified_fixed_unit_class
    (hunr : ramificationIndex F U = 1)
    (sigma : Gal(U/F)) (hgen : ∀ tau : Gal(U/F), tau ∈ Subgroup.zpowers sigma)
    (q : ℕ) (hq : 0 < q) (x : Uˣ)
    (hx : Units.map sigma.toMonoidHom x / x ∈ unitFiltration U q) :
    ∃ (f : Fˣ) (h : unitFiltration U q),
      x = Units.map (algebraMap F U) f * (h : Uˣ) := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff U).2 x.ne_zero)
  have hxord : ord U (x : U) = (n : WithTop ℤ) := hn.symm
  have hdisp : sigma (x : U) / (x : U) - 1 ∈ lattice U (q : ℤ) := by
    simpa using (positiveUnitDisplacement U hq ⟨_, hx⟩).property
  have hdiff : sigma (x : U) - (x : U) ∈ lattice U (n + (q : ℤ)) := by
    have hprod := mul_mem_lattice U (show (x : U) ∈ lattice U n by rw [mem_lattice, hxord]) hdisp
    convert hprod using 1
    field_simp
  obtain ⟨f, hf⟩ := unramified_invariant_lattice_class F U hunr (n + (q : ℤ)) (x : U)
    (lattice_class_fixed_of_generator F U sigma hgen _ _ hdiff)
  have hquot : (x : U)⁻¹ * (algebraMap F U f - (x : U)) ∈ lattice U (q : ℤ) := by
    have hinv : (x : U)⁻¹ ∈ lattice U (-n) := by
      rw [mem_lattice, ord_inv, hxord]
      simp
    have hprod := mul_mem_lattice U hinv (neg_mem_lattice U hf)
    simpa only [neg_sub, neg_add_cancel_left] using hprod
  let u : unitFiltration U q := positiveUnitOfLattice U hq ⟨_, hquot⟩
  have hu : (((u : unitFiltration U q) : Uˣ) : U) = algebraMap F U f / (x : U) := by
    simp only [u, coe_positiveUnitOfLattice]
    field_simp
    ring
  have hf0 : f ≠ 0 := by
    intro hf0
    have : (((u : unitFiltration U q) : Uˣ) : U) = 0 := by simp [hu, hf0]
    exact (u : Uˣ).ne_zero this
  refine ⟨Units.mk0 f hf0, u⁻¹, ?_⟩
  apply Units.ext
  simp only [Units.val_mul, Units.coe_map, Units.val_mk0, Subgroup.coe_inv, Units.val_inv_eq_inv_val, hu]
  have hfU : algebraMap F U f ≠ 0 := by
    intro hzero
    apply hf0
    apply (algebraMap F U).injective
    simpa using hzero
  field_simp [hfU]
  rfl


/-- The unit coboundary for an actual field automorphism. To match the paper's
convention `chi^phi(y) = chi(phi⁻¹ y)`, use `sigma = phi⁻¹`. -/
def unitCommutator (sigma : Gal(U/F)) : Uˣ →* Uˣ :=
  Units.map sigma.toMonoidHom / MonoidHom.id Uˣ

@[simp] theorem unitCommutator_apply (sigma : Gal(U/F)) (x : Uˣ) :
    unitCommutator F U sigma x = Units.map sigma.toMonoidHom x / x := rfl

/-- Galois automorphisms preserve each full positive unit layer. -/
theorem galoisUnit_mem_filtration (sigma : Gal(U/F)) (q : ℕ) (hq : 0 < q)
    (u : unitFiltration U q) :
    Units.map sigma.toMonoidHom (u : Uˣ) ∈ unitFiltration U q := by
  let z := positiveUnitDisplacement U hq u
  have hz : sigma (z : U) ∈ lattice U (q : ℤ) := by
    simpa only [mem_lattice, ord_galoisConjugate] using z.property
  have heq : Units.map sigma.toMonoidHom (u : Uˣ) =
      (positiveUnitOfLattice U hq ⟨sigma (z : U), hz⟩ : Uˣ) := by
    apply Units.ext
    simp [z, map_sub]
  rw [heq]
  exact (positiveUnitOfLattice U hq ⟨sigma (z : U), hz⟩).property

/-- The same actual coboundary, restricted to a positive unit subgroup. -/
def principalUnitCommutator (sigma : Gal(U/F)) (q : ℕ) (hq : 0 < q) :
    unitFiltration U q →* unitFiltration U q :=
  ((unitCommutator F U sigma).restrict (unitFiltration U q)).codRestrict
    (unitFiltration U q) fun u =>
      (unitFiltration U q).div_mem (galoisUnit_mem_filtration F U sigma q hq u) u.property

/-- The paper's global overlap verification. A local commutator identity,
together with triviality of `tau` on the base field, forces the prescribed
value on every element of the full commutator image that belongs to `U^q`. -/
theorem unramified_commutator_overlap
    (hunr : ramificationIndex F U = 1)
    (sigma : Gal(U/F)) (hgen : ∀ tau : Gal(U/F), tau ∈ Subgroup.zpowers sigma)
    (q : ℕ) (hq : 0 < q) (chiH : unitFiltration U q →* ℂˣ)
    (tau : Uˣ →* ℂˣ)
    (htau : ∀ f : Fˣ, tau (Units.map (algebraMap F U) f) = 1)
    (hcomm : ∀ h : unitFiltration U q,
      chiH (principalUnitCommutator F U sigma q hq h) = tau (h : Uˣ))
    (x : Uˣ) (hx : unitCommutator F U sigma x ∈ unitFiltration U q) :
    chiH ⟨unitCommutator F U sigma x, hx⟩ = tau x := by
  obtain ⟨f, h, hxh⟩ := unramified_fixed_unit_class F U hunr sigma hgen q hq x hx
  have hbase : unitCommutator F U sigma (Units.map (algebraMap F U) f) = 1 := by
    apply Units.ext
    simp [unitCommutator, Units.coe_map, AlgEquiv.commutes]
  have hdelta : unitCommutator F U sigma x = unitCommutator F U sigma (h : Uˣ) := by
    rw [hxh, map_mul, hbase, one_mul]
  have heq : (⟨unitCommutator F U sigma x, hx⟩ : unitFiltration U q) =
      principalUnitCommutator F U sigma q hq h := Subtype.ext hdelta
  rw [heq, hcomm, hxh, map_mul, htau, one_mul]

/-- A verified local commutator extends globally over an actual unramified
cyclic edge. The overlap is proved here, and no surjectivity of a ramified
norm is used. -/
theorem unramified_commutator_extension
    (hunr : ramificationIndex F U = 1)
    (sigma : Gal(U/F)) (hgen : ∀ tau : Gal(U/F), tau ∈ Subgroup.zpowers sigma)
    (q T : ℕ) (hq : 0 < q) (hqT : q ≤ T)
    (chiH : unitFiltration U q →* ℂˣ) (tau : Uˣ →* ℂˣ)
    (htau : ∀ f : Fˣ, tau (Units.map (algebraMap F U) f) = 1)
    (hcomm : ∀ h : unitFiltration U q,
      chiH (principalUnitCommutator F U sigma q hq h) = tau (h : Uˣ))
    (htriv : ∀ u : unitFiltration U q,
      (u : Uˣ) ∈ unitFiltration U T → chiH u = 1) :
    ∃ chi : ContinuousQuasiChar U,
      chi.toMonoidHom.comp (unitFiltration U q).subtype = chiH ∧
      ∀ x : Uˣ, chi (Units.map sigma.toMonoidHom x) / chi x = tau x := by
  obtain ⟨chi, hchi, hglobal⟩ := extendWithCommutator U (unitFiltration U q)
    chiH (unitCommutator F U sigma) tau
    (unramified_commutator_overlap F U hunr sigma hgen q hq chiH tau htau hcomm)
    T (lt_of_lt_of_le hq hqT) (unitFiltration_antitone U hqT) htriv
  refine ⟨chi, hchi, ?_⟩
  intro x
  simpa only [unitCommutator_apply, map_div] using hglobal x


/-- Naturality of the literal truncated logarithm under an actual field map. -/
private theorem map_log {L M : Type*} [Field L] [Field M]
    (f : L →+* M) (p : ℕ) (z : L) :
    f (truncatedLog p z) = truncatedLog p (f z) := by
  simp only [truncatedLog_apply, map_add, map_sum, map_div₀, map_pow, map_natCast]

/-- The local commutator follows from the whole coefficient congruence modulo
`𝔭^(T-q)`, with the inverse-action convention retained explicitly. -/
theorem logarithmCharacter_commutator
    (sigma : Gal(U/F)) (p q T : ℕ)
    (hchar : residueCharacteristic U = p) (hp : p.Prime)
    (hq : 0 < q) (hT : T ≤ p * q)
    (PsiF : ContinuousAddChar F)
    (hPsi : AddCharTrivialOnLattice U (tracePullbackAddChar F U PsiF) (T : ℤ))
    (a : ringOfIntegers U)
    (ha : sigma.symm (a : U) - (a : U) - 1 ∈ lattice U ((T : ℤ) - (q : ℤ)))
    (tau : Uˣ →* ℂˣ)
    (htau : ∀ u : unitFiltration U q,
      tau (u : Uˣ) = tracePullbackAddChar F U PsiF
        (truncatedLog p (1 - ((u : Uˣ) : U))))
    (u : unitFiltration U q) :
    logarithmCharacter U p q T hchar hp hq hT (tracePullbackAddChar F U PsiF) hPsi a
        (principalUnitCommutator F U sigma q hq u) = tau (u : Uˣ) := by
  let Psi := tracePullbackAddChar F U PsiF
  let chiH := logarithmCharacter U p q T hchar hp hq hT Psi hPsi a
  let su : unitFiltration U q :=
    ⟨Units.map sigma.toMonoidHom (u : Uˣ), galoisUnit_mem_filtration F U sigma q hq u⟩
  let z := truncatedLogUnitArgument U hq u
  have hcomm : principalUnitCommutator F U sigma q hq u = su / u := rfl
  have hP : truncatedLog p (z : U) ∈ lattice U (q : ℤ) :=
    (truncatedLogOnLattice U p q hchar hq z).property
  have herr : (sigma.symm (a : U) - (a : U) - 1) * truncatedLog p (z : U)
      ∈ lattice U (T : ℤ) := by
    simpa only [sub_add_cancel] using mul_mem_lattice U ha hP
  have htransport : chiH su = Psi (sigma.symm (a : U) * truncatedLog p (z : U)) := by
    have hinv (w : U) : Psi (sigma w) = Psi w := by
      simp only [Psi, tracePullbackAddChar_apply, trace_galoisConjugate]
    change Psi ((a : U) * truncatedLog p (1 - sigma ((u : Uˣ) : U))) = _
    rw [show 1 - sigma ((u : Uˣ) : U) = sigma (z : U) by simp [z]]
    have hlog : sigma (truncatedLog p (z : U)) = truncatedLog p (sigma (z : U)) :=
      map_log sigma.toRingHom p (z : U)
    rw [← hlog]
    have heq : (a : U) * sigma (truncatedLog p (z : U)) =
        sigma (sigma.symm (a : U) * truncatedLog p (z : U)) := by simp
    rw [heq, hinv]
  have hphase : Psi ((sigma.symm (a : U) - (a : U)) * truncatedLog p (z : U)) =
      Psi (truncatedLog p (z : U)) := by
    apply div_eq_one.mp
    calc
      _ = Psi ((sigma.symm (a : U) - (a : U)) * truncatedLog p (z : U) -
          truncatedLog p (z : U)) := (Psi.toAddChar.map_sub_eq_div _ _).symm
      _ = Psi ((sigma.symm (a : U) - (a : U) - 1) * truncatedLog p (z : U)) := by
        congr 1
        ring
      _ = 1 := hPsi _ herr
  change chiH (principalUnitCommutator F U sigma q hq u) = _
  rw [hcomm, map_div, htransport]
  have hchi : chiH u = Psi ((a : U) * truncatedLog p (z : U)) := by
    simp only [chiH, logarithmCharacter, z, coe_truncatedLogUnitArgument, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [hchi]
  calc
    _ = Psi (sigma.symm (a : U) * truncatedLog p (z : U) -
        (a : U) * truncatedLog p (z : U)) := (Psi.toAddChar.map_sub_eq_div _ _).symm
    _ = Psi ((sigma.symm (a : U) - (a : U)) * truncatedLog p (z : U)) := by
      rw [sub_mul]
    _ = Psi (truncatedLog p (z : U)) := hphase
    _ = tau (u : Uˣ) := by simpa [z, Psi] using (htau u).symm

/-- Combining the coefficient calculation, overlap descent, and character
extension constructs an actual character with the full chart, exact
conductor, and exact global conjugate quotient. -/
theorem logarithmModel_with_commutator
    (hunr : ramificationIndex F U = 1)
    (sigma : Gal(U/F)) (hgen : ∀ tau : Gal(U/F), tau ∈ Subgroup.zpowers sigma)
    (p q T : ℕ) (hchar : residueCharacteristic U = p) (hp : p.Prime)
    (hq : 0 < q) (hqT : q < T) (hT : T ≤ p * q)
    (PsiF : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor U (tracePullbackAddChar F U PsiF) (-(T : ℤ)))
    (a : ringOfIntegers U) (haunit : ord U (a : U) = 0)
    (ha : sigma.symm (a : U) - (a : U) - 1 ∈ lattice U ((T : ℤ) - (q : ℤ)))
    (tau : Uˣ →* ℂˣ)
    (htaubase : ∀ f : Fˣ, tau (Units.map (algebraMap F U) f) = 1)
    (htau : ∀ u : unitFiltration U q,
      tau (u : Uˣ) = tracePullbackAddChar F U PsiF
        (truncatedLog p (1 - ((u : Uˣ) : U)))) :
    ∃ chi : ContinuousQuasiChar U, IsMultiplicativeConductor U chi T ∧
      (∀ z : lattice U (q : ℤ),
        chi (positiveUnitOfLattice U hq (-z)) =
          tracePullbackAddChar F U PsiF ((a : U) * truncatedLog p (z : U))) ∧
      ∀ x : Uˣ, chi (Units.map sigma.toMonoidHom x) / chi x = tau x := by
  let Psi := tracePullbackAddChar F U PsiF
  let hPsiT : AddCharTrivialOnLattice U Psi (T : ℤ) := by simpa using hPsi.trivial
  let chiH := logarithmCharacter U p q T hchar hp hq hT Psi hPsiT a
  obtain ⟨chi, hchi, hcomm⟩ := unramified_commutator_extension F U hunr sigma hgen q T hq
    (le_of_lt hqT) chiH tau htaubase
    (logarithmCharacter_commutator F U sigma p q T hchar hp hq hT PsiF hPsiT a ha tau htau)
    (logarithmCharacter_trivial U p q T hchar hp hq (le_of_lt hqT) hT Psi hPsiT a)
  refine ⟨chi, logarithmCharacter_conductor U p q T hchar hp hq hqT hT
    Psi hPsi a haunit chi hchi, ?_, hcomm⟩
  intro z
  exact (DFunLike.congr_fun hchi (positiveUnitOfLattice U hq (-z))).trans
    (logarithmCharacter_one_sub U p q T hchar hp hq hT Psi hPsiT a z)


end UnramifiedOverlap

section ArtinSchreierPrecision

private theorem artinSchreier_finiteField_frobenius
    (k l : Type*) [Field k] [Field l] [Finite k] [Algebra k l]
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP l p] [Algebra (ZMod p) k]
    (c : k) (d : l) (hd : d ^ p - d = algebraMap k l c) :
    d ^ Nat.card k - d =
      algebraMap k l (algebraMap (ZMod p) k (Algebra.trace (ZMod p) k c)) := by
  have hsum (n : ℕ) : d ^ (p ^ n) - d =
      ∑ i ∈ Finset.range n, (algebraMap k l c) ^ (p ^ i) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', pow_mul, sub_eq_iff_eq_add.mp hd, add_pow_char_pow,
        Finset.sum_range_succ, ← ih]
      ring
  rw [FiniteField.algebraMap_trace_eq_sum_pow]
  simp only [map_sum, map_pow, Nat.card_zmod]
  rw [← hsum, FiniteField.pow_finrank_eq_natCard]

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- Quantitative Hensel uniqueness upgrades a residue translation of two
Artin--Schreier roots to the full `p`-precision available in mixed
characteristic. The same proof includes the equal-characteristic case. -/
theorem artinSchreier_translation_precision
    (p : ℕ) (hp : p.Prime) (hchar : residueCharacteristic L = p)
    (j : ℤ) (hj : 0 < j) (hpdepth : (p : L) ∈ lattice L j)
    (c d e : ringOfIntegers L)
    (hd : d ^ p - d = c) (he : e ^ p - e = c)
    (hres : residueMap L e = residueMap L d + 1) :
    (e : L) - (d : L) - 1 ∈ lattice L j := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : CharP (ResidueField L) p := by rw [← hchar]; infer_instance
  let P : Polynomial (ringOfIntegers L) := Polynomial.X ^ p - Polynomial.X - Polynomial.C c
  let a : ringOfIntegers L := d + 1
  have hderivred : residueMap L (P.derivative.eval a) = -1 := by
    rw [← Polynomial.eval_map_apply, ← Polynomial.derivative_map]
    simp only [P, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_C, sub_zero]
    rw [Polynomial.derivative_X_pow]
    simp
  have hderivord : ord L ((P.derivative.eval a : ringOfIntegers L) : L) = 0 := by
    apply le_antisymm
    · apply le_of_not_gt
      intro hpos
      have hz := (IsLocalRing.residue_eq_zero_iff _).2
        ((ord_pos_iff_mem_maximalIdeal L _).1 hpos)
      change residueMap L (P.derivative.eval a) = 0 at hz
      rw [hderivred] at hz
      exact (neg_ne_zero.mpr one_ne_zero) hz
    · exact (ord_nonneg_iff_mem_integer L _).2 (P.derivative.eval a).property
  have hPeval : ((P.eval a : ringOfIntegers L) : L) ∈ lattice L j := by
    obtain ⟨r, hr⟩ := (Commute.all d (1 : ringOfIntegers L)).exists_add_pow_prime_eq hp
    have hval : P.eval a = (p : ringOfIntegers L) * (d * r) := by
      simp only [P, a, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C, hr, one_pow, mul_one]
      rw [← hd]
      ring
    rw [hval]
    have hprod := mul_mem_lattice L hpdepth ((mem_lattice_zero_iff L).2 (d * r).property)
    simpa only [add_zero, Subring.coe_mul, Subring.coe_natCast] using hprod
  have hPpos : (0 : WithTop ℤ) < ord L ((P.eval a : ringOfIntegers L) : L) :=
    lt_of_lt_of_le (by exact_mod_cast hj) ((mem_lattice L).1 hPeval)
  obtain ⟨b, hb, _, hbound, huniq⟩ := Local.newton P a 0 hderivord (by simpa using hPpos)
  have heroot : P.IsRoot e := by
    simp only [Polynomial.IsRoot, P, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, he, sub_self]
  have henear : (0 : WithTop ℤ) < ord L ((e : L) - (a : L)) := by
    apply (ord_pos_iff_mem_maximalIdeal L (e - a)).2
    apply (IsLocalRing.residue_eq_zero_iff _).1
    change residueMap L (e - a) = 0
    simp [a, hres]
  have heb : e = b := huniq e heroot henear
  have hmem : (e : L) - (a : L) ∈ lattice L j := by
    rw [mem_lattice, heb]
    exact ((mem_lattice L).1 hPeval).trans (by simpa using hbound)
  simpa only [a, Subring.coe_add, Subring.coe_one, sub_add_eq_sub_sub] using hmem


end ArtinSchreierPrecision

section FrobeniusCoefficient
variable (F U : Type*) [Field F] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U] [IsGalois F U]

/-- The arithmetic Frobenius lift translates the chosen Artin--Schreier
coefficient to the full ideal precision. The normalized absolute trace one
condition determines the sign of this translation. -/
theorem artinSchreier_frobenius_coefficient
    {p : ℕ} (hp : p.Prime) (hchar : residueCharacteristic F = p)
    (hdegree : Module.finrank F U = p)
    (j : ℤ) (hj : 0 < j) (hpdepth : (p : U) ∈ lattice U j)
    (c : ringOfIntegers F) (d : ringOfIntegers U)
    (hc : IsNormalizedArtinSchreierCoefficient F p hchar c)
    (hd : (d : U) ^ p - (d : U) = algebraMap F U (c : F)) :
    ∃ phi : Gal(U/F),
      (∀ x : ResidueField U, Ramification.residueAction phi x =
        x ^ Nat.card (ResidueField F)) ∧
      (∀ sigma : Gal(U/F), sigma ∈ Subgroup.zpowers phi) ∧
      phi ((d : U) ^ p) - (d : U) ^ p - 1 ∈ lattice U j := by
  let k := ResidueField F
  let l := ResidueField U
  letI : Fintype k := Fintype.ofFinite k
  letI : Finite l := inferInstanceAs (Finite (ResidueField U))
  letI : Module.Finite k l := Module.Finite.of_finite
  letI : Fact p.Prime := ⟨hp⟩
  letI : CharP k p := by rw [← hchar]; infer_instance
  letI : CharP l p :=
    (RingHom.charP_iff (algebraMap k l) (algebraMap k l).injective p).mp inferInstance
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  let cU : ringOfIntegers U := algebraMap (ringOfIntegers F) (ringOfIntegers U) c
  have hdint : d ^ p - d = cU := by
    apply Subtype.ext
    exact hd
  have hdres : residueMap U d ^ p - residueMap U d = algebraMap k l (residueMap F c) := by
    calc
      _ = residueMap U cU := by
        simpa only [map_sub, map_pow] using congrArg (residueMap U) hdint
      _ = algebraMap k l (residueMap F c) := rfl
  have hshift : residueMap U d ^ Nat.card k - residueMap U d = 1 := by
    have h := artinSchreier_finiteField_frobenius k l p (residueMap F c) (residueMap U d) hdres
    have htrace : Algebra.trace (ZMod p) k (residueMap F c) = 1 := hc
    simpa only [htrace, map_one] using h
  obtain ⟨phi, hphi⟩ := Ramification.residueAction_surjective (F := F) (K := U)
    (FiniteField.frobeniusAlgEquivOfAlgebraic k l)
  let e : ringOfIntegers U := galoisIntegerEquiv F U phi d
  have heres : residueMap U e = residueMap U d + 1 := by
    rw [← Ramification.residueAction_apply_residue, hphi]
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Fintype.card_eq_nat_card]
    exact (sub_eq_iff_eq_add.mp hshift).trans (add_comm _ _)
  have hphi_ne : phi ≠ 1 := by
    intro hzero
    have heq : e = d := by apply Subtype.ext; simp [e, hzero]
    rw [heq] at heres
    exact one_ne_zero (add_left_cancel (heres.symm.trans (add_zero _).symm))
  have hgen : ∀ sigma : Gal(U/F), sigma ∈ Subgroup.zpowers phi := by
    intro sigma
    exact mem_zpowers_of_prime_card
      ((IsGalois.card_aut_eq_finrank F U).trans hdegree) hphi_ne
  have heint : e ^ p - e = cU := by
    apply Subtype.ext
    change phi (d : U) ^ p - phi (d : U) = algebraMap F U (c : F)
    rw [← map_pow, ← map_sub, hd, AlgEquiv.commutes]
  have hcharU : residueCharacteristic U = p := (residueCharacteristic_extension_eq F U).trans hchar
  have hprec := artinSchreier_translation_precision U p hp hcharU j hj hpdepth cU d e hdint heint heres
  refine ⟨phi, ?_, hgen, ?_⟩
  · intro x
    rw [hphi, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Fintype.card_eq_nat_card]
  have hcoeff : phi ((d : U) ^ p) - (d : U) ^ p - 1 = (e : U) - (d : U) - 1 := by
    have he : (e : U) ^ p - (e : U) = (cU : U) := congrArg Subtype.val heint
    have hd' : (d : U) ^ p - (d : U) = (cU : U) := congrArg Subtype.val hdint
    rw [map_pow]
    change (e : U) ^ p - (d : U) ^ p - 1 = (e : U) - (d : U) - 1
    linear_combination he - hd'
  rwa [hcoeff]


end FrobeniusCoefficient

section NormCharacterChart
variable (F U : Type*) [Field F] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F U] [ValuativeExtension F U] [Module.Finite F U] [PrimeCyclicExtension F U]

/-- The full unramified norm-log phase identity, including an arbitrary
integral coefficient. It is used in both directions when descending a chart. -/
theorem unramified_logarithm_norm
    (hunr : ramificationIndex F U = 1)
    (T q : ℕ) (hq : q = T ⌈/⌉ Module.finrank F U) (hqpos : 0 < q)
    (hchar : residueCharacteristic F = Module.finrank F U)
    (Psi : ContinuousAddChar F) (hPsi : AddCharTrivialOnLattice F Psi (T : ℤ))
    (a : ringOfIntegers F) (u : unitFiltration U q) :
    Psi ((a : F) * truncatedLog (Module.finrank F U)
      (1 - (normUnits F U (u : Uˣ) : F))) =
    tracePullbackAddChar F U Psi
      (algebraMap F U (a : F) * truncatedLog (Module.finrank F U) (1 - ((u : Uˣ) : U))) := by
  let z := truncatedLogUnitArgument U hqpos u
  have hlog := unramifiedNormLog F U T hchar hunr (z : U) (by simpa only [← hq] using z.property)
  have hval : norm F U (1 - (z : U)) = (normUnits F U (u : Uˣ) : F) := by simp [z]
  have herr := mul_mem_lattice F ((mem_lattice_zero_iff F).2 a.property) hlog
  have herror : Psi ((a : F) * (truncatedLog (Module.finrank F U)
      (1 - (normUnits F U (u : Uˣ) : F)) - trace F U (truncatedLog (Module.finrank F U) (z : U)))) = 1 := by
    apply hPsi
    simpa only [zero_add, hval] using herr
  have htr : trace F U (algebraMap F U (a : F) * truncatedLog (Module.finrank F U) (z : U)) =
      (a : F) * trace F U (truncatedLog (Module.finrank F U) (z : U)) := by
    simpa [Algebra.smul_def] using map_smul (trace F U) (a : F) (truncatedLog (Module.finrank F U) (z : U))
  have hz : 1 - ((u : Uˣ) : U) = (z : U) := (coe_truncatedLogUnitArgument U hqpos u).symm
  rw [hz, tracePullbackAddChar_apply, htr]
  apply div_eq_one.mp
  calc
    _ = Psi ((a : F) * truncatedLog (Module.finrank F U) (1 - (normUnits F U (u : Uˣ) : F)) -
        (a : F) * trace F U (truncatedLog (Module.finrank F U) (z : U))) := (Psi.toAddChar.map_sub_eq_div _ _).symm
    _ = 1 := by rw [← mul_sub]; exact herror

/-- The norm pullback of the full logarithm chart along an unramified edge.
The norm-log error is killed on the entire conductor lattice. -/
theorem unramified_norm_character_chart
    (hunr : ramificationIndex F U = 1)
    (T q : ℕ) (hq : q = T ⌈/⌉ Module.finrank F U) (hqpos : 0 < q)
    (hchar : residueCharacteristic F = Module.finrank F U)
    (tau : ContinuousQuasiChar F) (Psi : ContinuousAddChar F)
    (hPsi : AddCharTrivialOnLattice F Psi (T : ℤ))
    (hchart : ∀ u : unitFiltration F q,
      tau (u : Fˣ) = Psi (truncatedLog (Module.finrank F U) (1 - ((u : Fˣ) : F))))
    (u : unitFiltration U q) :
    normQuasiChar F U tau (u : Uˣ) = tracePullbackAddChar F U Psi
      (truncatedLog (Module.finrank F U) (1 - ((u : Uˣ) : U))) := by
  let nu : unitFiltration F q :=
    ⟨normUnits F U (u : Uˣ), (unramified_norm_unitFiltration F U hunr q).1 _ u.property⟩
  change tau (nu : Fˣ) = _
  rw [hchart]
  simpa only [Subring.coe_one, one_mul, map_one] using
    unramified_logarithm_norm F U hunr T q hq hqpos hchar Psi hPsi 1 u

/-- A full chart descends through an unramified norm on its entire stated
unit subgroup, by the exact surjectivity of that positive norm filtration. -/
theorem unramified_descent_chart
    (hunr : ramificationIndex F U = 1)
    (T q : ℕ) (hq : q = T ⌈/⌉ Module.finrank F U) (hqpos : 0 < q)
    (hchar : residueCharacteristic F = Module.finrank F U)
    (Psi : ContinuousAddChar F) (hPsi : AddCharTrivialOnLattice F Psi (T : ℤ))
    (a : ringOfIntegers F) (chi : ContinuousQuasiChar F)
    (hup : ∀ u : unitFiltration U q,
      normQuasiChar F U chi (u : Uˣ) = tracePullbackAddChar F U Psi
        (algebraMap F U (a : F) * truncatedLog (Module.finrank F U) (1 - ((u : Uˣ) : U))))
    (u : unitFiltration F q) :
    chi (u : Fˣ) = Psi ((a : F) * truncatedLog (Module.finrank F U) (1 - ((u : Fˣ) : F))) := by
  obtain ⟨v, hv, hnv⟩ := (unramified_norm_unitFiltration F U hunr q).2 (u : Fˣ) u.property
  have h := (hup ⟨v, hv⟩).trans
    (unramified_logarithm_norm F U hunr T q hq hqpos hchar Psi hPsi a ⟨v, hv⟩).symm
  change chi (normUnits F U v) = Psi ((a : F) * truncatedLog (Module.finrank F U)
    (1 - (normUnits F U v : F))) at h
  simpa only [hnv] using h

end NormCharacterChart

section RamifiedPrecision
variable (F E : Type*) [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E] [PrimeCyclicExtension F E]

/-- The residue-prime precision used in the Frobenius calculation follows
from the actual ramified trace ideal by applying it to `1`. -/
theorem residuePrime_mem_modelPrecision
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t)
    (hres : residueDegree F E = 1) :
    (Module.finrank F E : F) ∈ lattice F
      (((t + 1 : ℕ) : ℤ) - (((t + 1) ⌈/⌉ Module.finrank F E : ℕ) : ℤ)) := by
  let p := Module.finrank F E
  let T := t + 1
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F E hres
  have htrace := traceIdealLowerBound_of_integralGenerator F E ht hres pi hpi hgen
    0 1 (by simp)
  have hceil : ((T ⌈/⌉ p : ℕ) : ℤ) = integerCeilingDiv (T : ℤ) p := by
    rw [Nat.ceilDiv_eq_add_pred_div, integerCeilingDiv, Int.natCast_div]
    congr 1
    rw [Nat.cast_sub (by have := PrimeCyclicExtension.degree_prime F E |>.pos; omega), Nat.cast_add]
    simp
  have hdepth : wildBaseDepth p T = (T : ℤ) - ((T ⌈/⌉ p : ℕ) : ℤ) := by
    rw [wildBaseDepth_eq_sub_integerCeilingDiv p T (PrimeCyclicExtension.degree_prime F E).pos, hceil]
  have htone : trace F E (1 : E) = (p : F) := by
    simpa [p] using Algebra.trace_algebraMap (R := F) (S := E) (1 : F)
  have hbase : (wildBaseDepth p T : WithTop ℤ) ≤ ord F (p : F) := by
    simpa only [zero_add, htone, p, T, wildBaseDepth] using htrace
  rw [mem_lattice]
  simpa only [hdepth, p, T] using hbase


end RamifiedPrecision

private theorem ord_zero_of_residue_ne_zero
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (x : ringOfIntegers L)
    (hx : residueMap L x ≠ 0) : ord L (x : L) = 0 := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hpos
    exact hx ((IsLocalRing.residue_eq_zero_iff x).2
      ((ord_pos_iff_mem_maximalIdeal L x).1 hpos))
  · exact (ord_nonneg_iff_mem_integer L _).2 x.property

section UnramifiedModel
variable (F E U : Type*) [Field F] [Field E] [Field U]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [Algebra F E] [Algebra F U] [ValuativeExtension F E] [ValuativeExtension F U]
  [Module.Finite F E] [Module.Finite F U]
  [PrimeCyclicExtension F E] [PrimeCyclicExtension F U]

/-- Equal lower degrees make the crossed norm character trivial on every
base-field element: its value is the actual ramified norm of that element. -/
theorem normCharacter_unramifiedPullback_on_base
    (hdegree : Module.finrank F U = Module.finrank F E)
    (tau : NormCharacter F E) (f : Fˣ) :
    normQuasiChar F U tau.1 (Units.map (algebraMap F U) f) = 1 := by
  have hn : normUnits F U (Units.map (algebraMap F U) f) =
      normUnits F E (Units.map (algebraMap F E) f) := by
    apply Units.ext
    change Algebra.norm F (algebraMap F U (f : F)) = Algebra.norm F (algebraMap F E (f : F))
    rw [Algebra.norm_algebraMap, Algebra.norm_algebraMap, hdegree]
  change tau.1 (normUnits F U (Units.map (algebraMap F U) f)) = 1
  rw [hn]
  exact tau.eq_one_on_normRange F E _ ⟨Units.map (algebraMap F E) f, rfl⟩

omit [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E] [PrimeCyclicExtension F E] in
/-- Absolute trace one forces both Artin--Schreier coefficients to be units. -/
theorem normalizedArtinSchreier_unit_coefficients
    {p : ℕ} (hp : p.Prime) (hchar : residueCharacteristic F = p)
    (c : ringOfIntegers F) (d : ringOfIntegers U)
    (hc : IsNormalizedArtinSchreierCoefficient F p hchar c)
    (hd : (d : U) ^ p - (d : U) = algebraMap F U (c : F)) :
    ord F (c : F) = 0 ∧ ord U (d : U) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : CharP (ResidueField F) p := by rw [← hchar]; infer_instance
  letI : Algebra (ZMod p) (ResidueField F) := ZMod.algebra _ p
  have htrace : Algebra.trace (ZMod p) (ResidueField F) (residueMap F c) = 1 := hc
  have hcne : residueMap F c ≠ 0 := by
    intro hz
    rw [hz, map_zero] at htrace
    exact zero_ne_one htrace
  have hdres : residueMap U d ^ p - residueMap U d =
      extensionResidueMap F U (residueMap F c) := by
    have hdint : d ^ p - d = algebraMap (ringOfIntegers F) (ringOfIntegers U) c :=
      Subtype.ext hd
    calc
      _ = residueMap U (algebraMap (ringOfIntegers F) (ringOfIntegers U) c) := by
        simpa only [map_pow, map_sub] using congrArg (residueMap U) hdint
      _ = extensionResidueMap F U (residueMap F c) := rfl
  have hdne : residueMap U d ≠ 0 := by
    intro hz
    rw [hz, zero_pow hp.ne_zero, sub_zero] at hdres
    apply hcne
    apply (extensionResidueMap F U).injective
    simpa using hdres.symm
  exact ⟨ord_zero_of_residue_ne_zero F c hcne, ord_zero_of_residue_ne_zero U d hdne⟩

/-- Construct the actual unramified-field model in `O:I:canonical` from the
ramified norm character and the exact normalized Artin--Schreier data. The
global quotient is retained, as is the full coefficient `d^p`. -/
theorem unramifiedModel_exists
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F E t) (htpos : 0 < t)
    (hres : residueDegree F E = 1) (hunr : ramificationIndex F U = 1)
    (hdegree : Module.finrank F U = Module.finrank F E)
    (hchar : residueCharacteristic F = Module.finrank F E)
    (tau : NormCharacter F E) (PsiF : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F PsiF (-((t + 1 : ℕ) : ℤ)))
    (hchart : ∀ z : lattice F (((t + 1) ⌈/⌉ Module.finrank F E : ℕ) : ℤ),
      ∀ hz : 0 < (t + 1) ⌈/⌉ Module.finrank F E,
        tau.1 (positiveUnitOfLattice F hz (-z)) =
          PsiF (truncatedLog (Module.finrank F E) (z : F)))
    (c : ringOfIntegers F) (d : ringOfIntegers U)
    (hc : IsNormalizedArtinSchreierCoefficient F (Module.finrank F E) hchar c)
    (hd : (d : U) ^ Module.finrank F E - (d : U) = algebraMap F U (c : F)) :
    ∃ (phi : Gal(U/F)) (chi : ContinuousQuasiChar U),
      (∀ x : ResidueField U, Ramification.residueAction phi x = x ^ Nat.card (ResidueField F)) ∧
      (∀ sigma : Gal(U/F), sigma ∈ Subgroup.zpowers phi) ∧
      IsMultiplicativeConductor U chi (t + 1) ∧
      (∀ z : lattice U (((t + 1) ⌈/⌉ Module.finrank F E : ℕ) : ℤ),
        ∀ hz : 0 < (t + 1) ⌈/⌉ Module.finrank F E,
          chi (positiveUnitOfLattice U hz (-z)) =
            tracePullbackAddChar F U PsiF
              ((d : U) ^ Module.finrank F E * truncatedLog (Module.finrank F E) (z : U))) ∧
      ∀ x : Uˣ, chi (Units.map phi.symm.toMonoidHom x) / chi x = normQuasiChar F U tau.1 x := by
  let p := Module.finrank F E
  let T := t + 1
  let q := T ⌈/⌉ p
  have hp : p.Prime := PrimeCyclicExtension.degree_prime F E
  have hcover : T ≤ p * q := le_smul_ceilDiv hp.pos
  have hqpos : 0 < q := by
    by_contra h
    have : q = 0 := Nat.eq_zero_of_not_pos h
    rw [this, mul_zero] at hcover
    omega
  have hqt : q ≤ t := by
    rw [show q = (t + 1) ⌈/⌉ p from rfl, ceilDiv_le_iff_le_mul hp.pos]
    calc
      t + 1 ≤ 2 * t := by omega
      _ ≤ p * t := Nat.mul_le_mul_right t hp.two_le
  have hj : 0 < (T : ℤ) - (q : ℤ) := by omega
  have hpF := residuePrime_mem_modelPrecision F E ht hres
  have hpU : (p : U) ∈ lattice U ((T : ℤ) - (q : ℤ)) := by
    rw [mem_lattice, ← map_natCast (algebraMap F U), ord_algebraMap, hunr, one_nsmul]
    exact (mem_lattice F).1 hpF
  obtain ⟨phi, hphi, hgen, hcoeff⟩ := artinSchreier_frobenius_coefficient F U hp hchar
    hdegree _ hj hpU c d hc hd
  let a : ringOfIntegers U := d ^ p
  have haunit : ord U (a : U) = 0 := by
    rw [show (a : U) = (d : U) ^ p from rfl, ord_pow,
      (normalizedArtinSchreier_unit_coefficients F U hp hchar c d hc hd).2, nsmul_zero]
  have hcharU : residueCharacteristic U = p := (residueCharacteristic_extension_eq F U).trans hchar
  have hPsiU : IsAdditiveConductor U (tracePullbackAddChar F U PsiF) (-(T : ℤ)) :=
    (unramified_additiveConductor_compTrace F U hunr PsiF (-(T : ℤ))).2 hPsi
  have htauchart (u : unitFiltration U q) : normQuasiChar F U tau.1 (u : Uˣ) =
      tracePullbackAddChar F U PsiF (truncatedLog p (1 - ((u : Uˣ) : U))) := by
    have h := unramified_norm_character_chart F U hunr T q (by simp only [hdegree]; rfl)
      hqpos (hchar.trans hdegree.symm) tau.1 PsiF (by simpa only [neg_neg] using hPsi.trivial) ?_ u
    · simpa only [hdegree] using h
    intro v
    let z := truncatedLogUnitArgument F hqpos v
    have hcv := hchart z hqpos
    have hu : (positiveUnitOfLattice F hqpos (-z) : Fˣ) = (v : Fˣ) := by
      apply Units.ext
      simp [z]
    rw [hu] at hcv
    simpa only [z, coe_truncatedLogUnitArgument, hdegree] using hcv
  have hgeninv : ∀ sigma : Gal(U/F), sigma ∈ Subgroup.zpowers phi.symm := by
    change ∀ sigma : Gal(U/F), sigma ∈ Subgroup.zpowers phi⁻¹
    simpa only [Subgroup.zpowers_inv] using hgen
  obtain ⟨chi, hcond, hlog, hcomm⟩ := logarithmModel_with_commutator F U hunr phi.symm hgeninv
    p q T hcharU hp hqpos (by omega) hcover PsiF hPsiU a haunit
    (by change phi ((d : U) ^ p) - (d : U) ^ p - 1 ∈ _; exact hcoeff)
    (normQuasiChar F U tau.1).toMonoidHom
    (normCharacter_unramifiedPullback_on_base F E U hdegree tau) htauchart
  exact ⟨phi, chi, hphi, hgen, hcond, fun z _ => hlog z, hcomm⟩


end UnramifiedModel

section CommonPullback
variable (F U K : Type*) [Field F] [Field U] [Field K]
  [Algebra F U] [Algebra F K] [Algebra U K] [IsScalarTower F U K]

/-- Naturality of the actual upper norm under an automorphism of the tower. -/
theorem normUnits_restrictNormal [Normal F U] (sigma : Gal(K/F)) (x : Kˣ) :
    normUnits U K (Units.map sigma.toMonoidHom x) =
      Units.map (sigma.restrictNormal U).toMonoidHom (normUnits U K x) := by
  apply Units.ext
  let e := sigma.restrictNormal U
  have he : (algebraMap U K).comp e.toRingHom =
      sigma.toRingHom.comp (algebraMap U K) := by
    ext u
    exact sigma.restrictNormal_commutes U u
  have h := Algebra.norm_eq_of_equiv_equiv e.toRingEquiv sigma.toRingEquiv he (x : K)
  have heq : e (norm U K (x : K)) = norm U K (sigma (x : K)) := by
    exact (e.eq_symm_apply).mp h
  exact heq.symm

end CommonPullback

section KernelInvariance
variable (F U : Type*) [Field F] [Field U] [Algebra F U]

/-- A cyclic conjugate quotient that is invariant itself makes the original
character invariant on its full kernel. This is applied to the actual upper
norm character, so every upper norm belongs to that kernel. -/
theorem invariant_on_kernel_of_commutator
    (sigma : Gal(U/F)) (hgen : ∀ tau : Gal(U/F), tau ∈ Subgroup.zpowers sigma)
    (chi tau : Uˣ →* ℂˣ)
    (htau : ∀ (g : Gal(U/F)) (x : Uˣ), tau (Units.map g.toMonoidHom x) = tau x)
    (hcomm : ∀ x : Uˣ, chi (Units.map sigma.toMonoidHom x) / chi x = tau x) :
    ∀ (g : Gal(U/F)) (x : Uˣ), tau x = 1 → chi (Units.map g.toMonoidHom x) = chi x := by
  have hmul (a b : Gal(U/F)) (x : Uˣ) : Units.map (a * b).toMonoidHom x =
      Units.map a.toMonoidHom (Units.map b.toMonoidHom x) := by apply Units.ext; rfl
  have hinv (a : Gal(U/F)) (x : Uˣ) :
      Units.map a.toMonoidHom (Units.map (a⁻¹).toMonoidHom x) = x := by
    apply Units.ext
    exact a.apply_symm_apply (x : U)
  let S : Subgroup Gal(U/F) :=
    { carrier := {g | ∀ x : Uˣ, tau x = 1 → chi (Units.map g.toMonoidHom x) = chi x}
      one_mem' := by intro x _; rfl
      mul_mem' := by
        intro a b ha hb x hx
        rw [hmul, ha _ ((htau b x).trans hx), hb x hx]
      inv_mem' := by
        intro a ha x hx
        have h := ha (Units.map (a⁻¹).toMonoidHom x) ((htau a⁻¹ x).trans hx)
        rw [hinv] at h
        exact h.symm }
  have hs : sigma ∈ S := by
    intro x hx
    exact div_eq_one.mp ((hcomm x).trans hx)
  intro g
  exact (Subgroup.zpowers_le.mpr hs) (hgen g)

end KernelInvariance

section PullbackInvariance
variable (F U K : Type*) [Field F] [Field U] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F U] [Algebra F K] [Algebra U K] [IsScalarTower F U K]
  [ValuativeExtension F U] [ValuativeExtension U K]
  [Module.Finite F U] [Module.Finite U K] [Normal F U]

/-- The global commutator gives full invariance of the actual common norm
pullback under the entire top-field Galois group. -/
theorem model_normPullback_invariant
    (sigma : Gal(U/F)) (hgen : ∀ tau : Gal(U/F), tau ∈ Subgroup.zpowers sigma)
    (chi : ContinuousQuasiChar U) (tauF : ContinuousQuasiChar F)
    (hnorm : normQuasiChar U K (normQuasiChar F U tauF) = 1)
    (hcomm : ∀ x : Uˣ, chi (Units.map sigma.toMonoidHom x) / chi x = normQuasiChar F U tauF x) :
    ∀ (g : Gal(K/F)) (x : Kˣ),
      normQuasiChar U K chi (Units.map g.toMonoidHom x) = normQuasiChar U K chi x := by
  have htau (g : Gal(U/F)) (x : Uˣ) :
      normQuasiChar F U tauF (Units.map g.toMonoidHom x) = normQuasiChar F U tauF x := by
    change tauF (normUnits F U (Units.map g.toMonoidHom x)) = tauF (normUnits F U x)
    congr 1
    apply Units.ext
    exact norm_galoisConjugate F U g (x : U)
  intro g x
  change chi (normUnits U K (Units.map g.toMonoidHom x)) = chi (normUnits U K x)
  rw [normUnits_restrictNormal F U K]
  exact invariant_on_kernel_of_commutator F U sigma hgen chi.toMonoidHom
    (normQuasiChar F U tauF).toMonoidHom htau hcomm (g.restrictNormal U)
    (normUnits U K x) (DFunLike.congr_fun hnorm x)


end PullbackInvariance

section RamifiedPullbackChart
variable (U K : Type*) [Field U] [Field K]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra U K] [ValuativeExtension U K] [Module.Finite U K] [PrimeCyclicExtension U K]

/-- The actual ramified norm-phase conversion changes `d^p P(z)` into
`(d^p-d) P(z)`. The proof uses `N(d)=d^p` exactly and kills the full
norm-log error at depth `T`. -/
theorem ramified_model_pullback_chart
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak U K t) (htpos : 0 < t)
    (hres : residueDegree U K = 1)
    (hchar : residueCharacteristic U = Module.finrank U K) (hodd : Module.finrank U K ≠ 2)
    (q : ℕ) (hq : q = (t + 1) ⌈/⌉ Module.finrank U K) (hqpos : 0 < q)
    (tau : NormCharacter U K) (htaune : tau ≠ 1) (Psi : ContinuousAddChar U)
    (hPsi : IsAdditiveConductor U Psi (-((t + 1 : ℕ) : ℤ)))
    (htau : ∀ z : lattice U (q : ℤ),
      tau.1 (positiveUnitOfLattice U hqpos (-z)) = Psi (truncatedLog (Module.finrank U K) (z : U)))
    (d : ringOfIntegers U) (chi : ContinuousQuasiChar U)
    (hchi : ∀ u : unitFiltration U q, chi (u : Uˣ) =
      Psi ((d : U) ^ Module.finrank U K * truncatedLog (Module.finrank U K) (1 - ((u : Uˣ) : U))))
    (z : lattice K (q : ℤ)) :
    normQuasiChar U K chi (positiveUnitOfLattice K hqpos (-z)) =
      tracePullbackAddChar U K Psi
        (algebraMap U K ((d : U) ^ Module.finrank U K - (d : U)) *
          truncatedLog (Module.finrank U K) (z : K)) := by
  let p := Module.finrank U K
  have hp := PrimeCyclicExtension.degree_prime U K
  have hqt : q ≤ t := by
    rw [hq, ceilDiv_le_iff_le_mul hp.pos]
    calc
      t + 1 ≤ 2 * t := by omega
      _ ≤ p * t := Nat.mul_le_mul_right t hp.two_le
  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer U K hres
  let uz := positiveUnitOfLattice K hqpos (-z)
  let nu : unitFiltration U q := ⟨normUnits U K (uz : Kˣ),
    normMapsUnitFiltration_belowBreak U K ht hqt hres pi hpi hgen _ uz.property⟩
  let w := truncatedLog p (z : K)
  have hw : w ∈ lattice K (q : ℤ) := (truncatedLogOnLattice K p q
    ((residueCharacteristic_extension_eq U K).trans hchar) hqpos z).property
  have hdK : algebraMap U K (d : U) ∈ lattice K 0 :=
    (mem_lattice_zero_iff K).2
      (algebraMap (ringOfIntegers U) (ringOfIntegers K) d).property
  have hdw : algebraMap U K (d : U) * w ∈ lattice K (q : ℤ) := by
    simpa only [zero_add] using mul_mem_lattice K hdK hw
  have hconv := (normPhase U K ht htpos hres hchar hodd q hq hqpos tau htaune
    Psi hPsi htau _ hdw).1
  have htr (a : U) : trace U K (algebraMap U K a * w) = a * trace U K w := by
    simpa [Algebra.smul_def] using map_smul (trace U K) a w
  have hn : norm U K (algebraMap U K (d : U) * w) = (d : U) ^ p * norm U K w := by
    change Algebra.norm U (algebraMap U K (d : U) * w) = _
    rw [map_mul, Algebra.norm_algebraMap]
  rw [htr, hn] at hconv
  have hlog := normLog U K ht htpos hres hchar hodd 0 (z : K) (by simpa only [zero_add, ← hq] using z.property)
  have hnu : ((nu : Uˣ) : U) = norm U K (1 - (z : K)) := by simp [nu, uz, sub_eq_add_neg]
  have herr : (d : U) ^ p * (truncatedLog p (1 - ((nu : Uˣ) : U)) -
      trace U K w - norm U K w) ∈ lattice U ((t + 1 : ℕ) : ℤ) := by
    have hd0 : (d : U) ^ p ∈ lattice U 0 := (mem_lattice_zero_iff U).2 (d ^ p).property
    have hprod := mul_mem_lattice U hd0 hlog
    simpa only [zero_add, Nat.add_zero, hnu, w, p] using hprod
  have hPsiT : AddCharTrivialOnLattice U Psi ((t + 1 : ℕ) : ℤ) := by simpa only [neg_neg] using hPsi.trivial
  have hequal : Psi ((d : U) ^ p * truncatedLog p (1 - ((nu : Uˣ) : U))) =
      Psi ((d : U) ^ p * (trace U K w + norm U K w)) := by
    apply div_eq_one.mp
    calc
      _ = Psi ((d : U) ^ p * truncatedLog p (1 - ((nu : Uˣ) : U)) -
          (d : U) ^ p * (trace U K w + norm U K w)) := (Psi.toAddChar.map_sub_eq_div _ _).symm
      _ = 1 := by
        convert hPsiT _ herr using 1
        congr 1
        ring
  change chi (nu : Uˣ) = _
  rw [hchi, hequal, tracePullbackAddChar_apply]
  change Psi ((d : U) ^ p * (trace U K w + norm U K w)) =
    Psi (trace U K (algebraMap U K ((d : U) ^ p - (d : U)) * w))
  rw [htr]
  apply div_eq_one.mp
  calc
    _ = Psi ((d : U) ^ p * (trace U K w + norm U K w) -
        ((d : U) ^ p - (d : U)) * trace U K w) := (Psi.toAddChar.map_sub_eq_div _ _).symm
    _ = Psi ((d : U) * trace U K w + (d : U) ^ p * norm U K w) := by
      congr 1
      ring
    _ = 1 := hconv


end RamifiedPullbackChart

section Primitivity
variable (F E U K : Type) [Field F] [Field E] [Field U] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F E] [Algebra F U] [Algebra F K] [Algebra E K] [Algebra U K]
  [IsScalarTower F E K] [IsScalarTower F U K]
  [ValuativeExtension F E] [ValuativeExtension F U] [ValuativeExtension F K]
  [ValuativeExtension U K]
  [Module.Finite F E] [Module.Finite F U] [Module.Finite E K] [Module.Finite U K] [Module.Finite F K]
  [PrimeCyclicExtension F E] [PrimeCyclicExtension F U] [PrimeCyclicExtension U K]

/-- The exact nontrivial commutator rules out descent of the common pullback
from `F`; the possible upper norm-character discrepancy is resolved by the
proved crossed-norm equivalence. -/
theorem model_normPullback_primitive
    {p : ℕ} (hp : p.Prime) (hFE : Module.finrank F E = p)
    (hFU : Module.finrank F U = p) (hUK : Module.finrank U K = p)
    (hne : (normUnits F U).range ≠ (normUnits F E).range)
    (tau : NormCharacter F E) (htaune : tau ≠ 1)
    (chi : ContinuousQuasiChar U) (sigma : Gal(U/F))
    (hcomm : ∀ x : Uˣ, chi (Units.map sigma.toMonoidHom x) / chi x = normQuasiChar F U tau.1 x) :
    ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = normQuasiChar U K chi := by
  rintro ⟨lambda, hlambda⟩
  let e := Characters.crossedNormEquivOfTowers F U E K hp hFU hFE hUK hne
  let mu : NormCharacter U K := ⟨chi / normQuasiChar F U lambda, by
    apply ContinuousMonoidHom.ext
    intro x
    change chi (normUnits U K x) / lambda (normUnits F U (normUnits U K x)) = 1
    have hn : normUnits F U (normUnits U K x) = normUnits F K x := by
      apply Units.ext
      exact Basic.norm_tower (F := F) (L := U) (K := K) (x : K)
    rw [hn]
    exact div_eq_one.mpr (DFunLike.congr_fun hlambda x).symm⟩
  obtain ⟨omega, homega⟩ := e.surjective mu
  have hquot (x : Uˣ) : chi x / lambda (normUnits F U x) = omega.1 (normUnits F U x) := by
    have h := DFunLike.congr_fun (congrArg Subtype.val homega) x
    exact h.symm
  have hchi (x : Uˣ) : chi x = omega.1 (normUnits F U x) * lambda (normUnits F U x) :=
    (div_eq_iff_eq_mul).mp (hquot x)
  have hnormsigma (x : Uˣ) : normUnits F U (Units.map sigma.toMonoidHom x) = normUnits F U x := by
    apply Units.ext
    exact norm_galoisConjugate F U sigma (x : U)
  have htauzero : normQuasiChar F U tau.1 = 1 := by
    apply ContinuousMonoidHom.ext
    intro x
    have hinv : chi (Units.map sigma.toMonoidHom x) = chi x := by
      rw [hchi, hchi, hnormsigma]
    have h := hcomm x
    rw [hinv] at h
    exact ((div_self' (chi x)).symm.trans h).symm
  apply htaune
  apply e.injective
  apply NormCharacter.ext
  change normQuasiChar F U tau.1 = normQuasiChar F U (1 : NormCharacter F E).1
  exact htauzero


end Primitivity

section PairConstruction
variable (F E U K : Type) [Field F] [Field E] [Field U] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F E] [Algebra F U] [Algebra F K] [Algebra E K] [Algebra U K]
  [IsScalarTower F E K] [IsScalarTower F U K]
  [ValuativeExtension F E] [ValuativeExtension F U] [ValuativeExtension F K]
  [ValuativeExtension U K] [ValuativeExtension E K]
  [Module.Finite F E] [Module.Finite F U] [Module.Finite E K] [Module.Finite U K] [Module.Finite F K]

/-- The actual characters and all assertions of `O:I:canonical`. The
constructor below proves these fields from the normalized initial data. -/
structure CompatibleModels [IsGalois F U] (p T q : ℕ) (hq : 0 < q)
    (tau : ContinuousQuasiChar F) (Psi : ContinuousAddChar F) (c : F) (d : U) where
  phi : Gal(U/F)
  frobenius : ∀ x : ResidueField U, Ramification.residueAction phi x = x ^ Nat.card (ResidueField F)
  chiU : ContinuousQuasiChar U
  chiE : ContinuousQuasiChar E
  conductorU : IsMultiplicativeConductor U chiU T
  conductorE : IsMultiplicativeConductor E chiE T
  commutator : ∀ x : Uˣ, chiU (Units.map phi.symm.toMonoidHom x) / chiU x = normQuasiChar F U tau x
  logU : ∀ z : lattice U (q : ℤ), chiU (positiveUnitOfLattice U hq (-z)) =
    tracePullbackAddChar F U Psi (d ^ p * truncatedLog p (z : U))
  logE : ∀ z : lattice E (q : ℤ), chiE (positiveUnitOfLattice E hq (-z)) =
    tracePullbackAddChar F E Psi (algebraMap F E c * truncatedLog p (z : E))
  compatible : normQuasiChar U K chiU = normQuasiChar E K chiE
  invariant : ∀ (g : Gal(K/F)) (x : Kˣ), normQuasiChar U K chiU (Units.map g.toMonoidHom x) = normQuasiChar U K chiU x
  primitive : ¬ ∃ lambda : ContinuousQuasiChar F, normQuasiChar F K lambda = normQuasiChar U K chiU

variable [PrimeCyclicExtension F E] [PrimeCyclicExtension F U]
  [PrimeCyclicExtension E K] [PrimeCyclicExtension U K]

/-- Full pair construction from the actual normalized local-field data of
the setup. Both descent and the ramified conductor are proved, along with
invariance and primitivity of the common pullback. -/
theorem compatibleModels_of_normalized_data
    {p t : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (htpos : 0 < t)
    (hFE : Module.finrank F E = p) (hFU : Module.finrank F U = p)
    (hUK : Module.finrank U K = p) (hEK : Module.finrank E K = p)
    (htFE : PrimeCyclicExtension.IsLowerBreak F E t) (htUK : PrimeCyclicExtension.IsLowerBreak U K t)
    (hresFE : residueDegree F E = 1) (hresUK : residueDegree U K = 1)
    (hunrFU : ramificationIndex F U = 1) (hunrEK : ramificationIndex E K = 1)
    (hchar : residueCharacteristic F = p)
    (hne : (normUnits F U).range ≠ (normUnits F E).range)
    (hq : 0 < (t + 1) ⌈/⌉ p)
    (tau : NormCharacter F E) (htaune : tau ≠ 1) (Psi : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F Psi (-((t + 1 : ℕ) : ℤ)))
    (htau : ∀ u : unitFiltration F ((t + 1) ⌈/⌉ p),
      tau.1 (u : Fˣ) = Psi (truncatedLog p (1 - ((u : Fˣ) : F))))
    (c : ringOfIntegers F) (d : ringOfIntegers U)
    (hc : IsNormalizedArtinSchreierCoefficient F p hchar c)
    (hd : (d : U) ^ p - (d : U) = algebraMap F U (c : F)) :
    Nonempty (CompatibleModels F E U K p (t + 1) ((t + 1) ⌈/⌉ p) hq tau.1 Psi (c : F) (d : U)) := by
  subst p
  let p := Module.finrank F E
  have hFE : Module.finrank F E = p := rfl
  let q := (t + 1) ⌈/⌉ p
  have hqt : q ≤ t := by
    rw [show q = (t + 1) ⌈/⌉ p from rfl, ceilDiv_le_iff_le_mul hp.pos]
    calc
      t + 1 ≤ 2 * t := by omega
      _ ≤ p * t := Nat.mul_le_mul_right t hp.two_le
  have hcover : t + 1 ≤ p * q := le_smul_ceilDiv hp.pos
  have htauz : ∀ z : lattice F (q : ℤ), tau.1 (positiveUnitOfLattice F hq (-z)) = Psi (truncatedLog p (z : F)) := by
    intro z
    simpa using htau (positiveUnitOfLattice F hq (-z))
  obtain ⟨phi, chiU, hphi, hgen, hcondU, hlogU, hcomm⟩ := unramifiedModel_exists F E U
    htFE htpos hresFE hunrFU (hFU.trans hFE.symm) (hchar.trans hFE.symm) tau Psi hPsi
    (fun z _ => htauz z) c d
    (by simpa only [hFE] using hc) (by simpa only [hFE] using hd)
  have hlogU' : ∀ z : lattice U (q : ℤ), chiU (positiveUnitOfLattice U hq (-z)) =
      tracePullbackAddChar F U Psi ((d : U) ^ p * truncatedLog p (z : U)) := by
    exact fun z => hlogU z hq
  have hunitU := (one_sub_chart_iff_units U p q hq chiU (tracePullbackAddChar F U Psi) ((d : U) ^ p)).1 hlogU'
  have hgeninv : ∀ g : Gal(U/F), g ∈ Subgroup.zpowers phi.symm := by
    change ∀ g : Gal(U/F), g ∈ Subgroup.zpowers phi⁻¹
    simpa only [Subgroup.zpowers_inv] using hgen
  let tauU := Characters.crossedNormHom F U E K tau
  have htauUne : tauU ≠ 1 := by
    intro hzero
    apply htaune
    apply (Characters.crossedNormEquivOfTowers F U E K hp hFU hFE hUK hne).injective
    exact hzero
  have hinv := model_normPullback_invariant F U K phi.symm hgeninv chiU tau.1 tauU.property hcomm
  obtain ⟨chiE, hcompat⟩ := Local.invariantCharacter_descends E K (normQuasiChar U K chiU)
    (fun g x => hinv (g.restrictScalars F) x)
  let PsiU := tracePullbackAddChar F U Psi
  let PsiE := tracePullbackAddChar F E Psi
  have hPsiU : IsAdditiveConductor U PsiU (-((t + 1 : ℕ) : ℤ)) :=
    (unramified_additiveConductor_compTrace F U hunrFU Psi _).2 hPsi
  have htauUunit (u : unitFiltration U q) : tauU.1 (u : Uˣ) = PsiU (truncatedLog p (1 - ((u : Uˣ) : U))) := by
    have h := unramified_norm_character_chart F U hunrFU (t + 1) q (by simp only [hFU]; rfl)
      hq (hchar.trans hFU.symm) tau.1 Psi (by simpa only [neg_neg] using hPsi.trivial)
      (by simpa only [hFU] using htau) u
    change normQuasiChar F U tau.1 (u : Uˣ) = tracePullbackAddChar F U Psi _
    simpa only [hFU] using h
  have htauUz (z : lattice U (q : ℤ)) : tauU.1 (positiveUnitOfLattice U hq (-z)) = PsiU (truncatedLog p (z : U)) := by
    simpa using htauUunit (positiveUnitOfLattice U hq (-z))
  obtain ⟨pi, hpi, hgenpi⟩ := monogenicUniformizer F E hresFE
  have hPsiE : IsAdditiveConductor E PsiE (-((t + 1 : ℕ) : ℤ)) := by
    have h := additiveConductor_compTrace_cyclicPrime F E htFE hresFE pi hpi hgenpi hPsi
    have hind : (Module.finrank F E : ℤ) * (-((t + 1 : ℕ) : ℤ)) +
        (((Module.finrank F E - 1) * (t + 1) : ℕ) : ℤ) = -((t + 1 : ℕ) : ℤ) := by
      rw [Nat.cast_mul, Nat.cast_sub hp.one_le]
      push_cast
      ring
    rw [hind] at h
    exact h
  let cE : ringOfIntegers E := algebraMap (ringOfIntegers F) (ringOfIntegers E) c
  have hmapC : algebraMap U K ((d : U) ^ p - (d : U)) = algebraMap E K (cE : E) := by
    rw [hd]
    exact (IsScalarTower.algebraMap_apply F U K (c : F)).symm.trans
      (IsScalarTower.algebraMap_apply F E K (c : F))
  have htraces (x : K) : tracePullbackAddChar U K PsiU x = tracePullbackAddChar E K PsiE x := by
    change Psi (Algebra.trace F U (Algebra.trace U K x)) = Psi (Algebra.trace F E (Algebra.trace E K x))
    rw [Basic.trace_tower, Basic.trace_tower]
  have hlogK (z : lattice K (q : ℤ)) : normQuasiChar U K chiU (positiveUnitOfLattice K hq (-z)) =
      tracePullbackAddChar E K PsiE (algebraMap E K (cE : E) * truncatedLog p (z : K)) := by
    have h := ramified_model_pullback_chart U K htUK htpos hresUK
      (((residueCharacteristic_extension_eq F U).trans hchar).trans hUK.symm)
      (by simpa only [hUK] using hodd) q (by simp only [hUK]; rfl) hq tauU htauUne PsiU hPsiU
      (by simpa only [hUK] using htauUz) d chiU (by simpa only [hUK] using hunitU) z
    simpa only [hUK, hFE, hmapC, htraces] using h
  have hunitK := (one_sub_chart_iff_units K p q hq (normQuasiChar U K chiU)
    (tracePullbackAddChar E K PsiE) (algebraMap E K (cE : E))).1 hlogK
  have hunitE (u : unitFiltration E q) : chiE (u : Eˣ) = PsiE ((cE : E) * truncatedLog p (1 - ((u : Eˣ) : E))) := by
    have h := unramified_descent_chart E K hunrEK (t + 1) q (by simp only [hEK]; rfl) hq
      (((residueCharacteristic_extension_eq F E).trans hchar).trans hEK.symm) PsiE
      (by simpa only [neg_neg] using hPsiE.trivial) cE chiE
      (by rw [hcompat]; simpa only [hEK] using hunitK) u
    simpa only [hEK] using h
  have hcunit := (normalizedArtinSchreier_unit_coefficients F U hp hchar c d hc hd).1
  have hcEunit : ord E (cE : E) = 0 := by
    change ord E (algebraMap F E (c : F)) = 0
    rw [ord_algebraMap, hcunit, nsmul_zero]
  have hcondE := logarithmCharacter_conductor E p q (t + 1)
    ((residueCharacteristic_extension_eq F E).trans hchar) hp hq (by omega) hcover PsiE hPsiE
    cE hcEunit chiE (by
      apply MonoidHom.ext
      intro u
      exact hunitE u)
  refine ⟨⟨phi, hphi, chiU, chiE, hcondU, hcondE, hcomm, hlogU', ?_,
    hcompat.symm, hinv, ?_⟩⟩
  · exact (one_sub_chart_iff_units E p q hq chiE PsiE (cE : E)).2 hunitE
  · exact model_normPullback_primitive F E U K hp hFE hFU hUK hne tau htaune chiU phi.symm hcomm

end PairConstruction

section SetupAdapter
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] [Module.Free F K] in
private theorem modelFixedField_degree {p : ℕ} (hp : p.Prime)
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p) :
    Module.finrank F (IntermediateField.fixedField H) = p := by
  have h := Module.finrank_mul_finrank F (IntermediateField.fixedField H) K
  rw [IntermediateField.finrank_fixedField_eq_card H, hH,
    ← IsGalois.card_aut_eq_finrank F K, Nat.card_congr (Classical.choice hG).toEquiv,
    Nat.card_prod] at h
  have hc : Nat.card (Multiplicative (ZMod p)) = p :=
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod p)
  rw [hc] at h
  exact Nat.mul_right_cancel hp.pos h

omit [Module.Free F K] in
private theorem modelFixedField_primeCyclic {p : ℕ} (hp : p.Prime)
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p) :
    PrimeCyclicExtension F (IntermediateField.fixedField H) ∧
      PrimeCyclicExtension (IntermediateField.fixedField H) K := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hFL, hLK⟩ :=
    Basic.intermediateField_tower_compatible hp hG (IntermediateField.fixedField H)
      (modelFixedField_degree hp hG H hH)
  exact ⟨PrimeCyclicExtension.ofCyclicPrimeExtension F _ hFL,
    PrimeCyclicExtension.ofCyclicPrimeExtension _ K hLK⟩

/-- **Paper `O:I:canonical`.** The global compatible models for the genuine
odd unramified--ramified setup, for every nontrivial continuous additive
character. The normalizing scalar, its order, and its whole-ideal chart are
constructed from the setup. No stationary model or commutator is assumed.

`CompatibleModels` records the arithmetic Frobenius, both actual continuous
characters of conductor `T`, the full `d^p P` and `c P` charts on depth `q0`,
and the invariant primitive common norm pullback. The convention is
`chi^phi(x) = chi(phi⁻¹ x)`, exactly as in the paper. -/
theorem models {p : ℕ} (hp : p.Prime)
    (hG : Nonempty (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hI : Nat.card (Ramification.inertiaSubgroup (F := F) (K := K)) = p)
    (H : Subgroup Gal(K/F)) (hH : Nat.card H = p)
    (hne : H ≠ Ramification.inertiaSubgroup) (hchar : residueCharacteristic F = p)
    (s : OddURSetup hp hG hI H hH hne hchar)
    (psiF : ContinuousAddChar F) (hpsiF : psiF ≠ 1) :
    let U := UnramifiedField F K
    let E := RamifiedField F K H
    letI : ValuativeRel U := Basic.intermediateFieldValuativeRel U
    letI : TopologicalSpace U := Basic.intermediateFieldTopology U
    letI : IsNonarchimedeanLocalField U := Basic.intermediateField_localField U
    letI : ValuativeExtension F U := Basic.intermediateField_lowerValuativeExtension U
    letI : ValuativeExtension U K := Basic.intermediateField_upperValuativeExtension U
    letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E
    letI : TopologicalSpace E := Basic.intermediateFieldTopology E
    letI : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E
    letI : ValuativeExtension F E := Basic.intermediateField_lowerValuativeExtension E
    letI : ValuativeExtension E K := Basic.intermediateField_upperValuativeExtension E
    letI : PrimeCyclicExtension F U := (modelFixedField_primeCyclic hp hG _ hI).1
    ∃ alpha : Fˣ,
      ord F (alpha : F) = ((-(canonicalLocalAddCharData F psiF hpsiF).conductor -
        (s.T : ℤ) : ℤ) : WithTop ℤ) ∧
      let Psi := scaleAddCharData F (canonicalLocalAddCharData F psiF hpsiF) alpha
      Psi.conductor = -(s.T : ℤ) ∧
      (∀ z : lattice F (s.q0 : ℤ), s.tauF.1 (positiveUnitOfLattice F s.q0_pos (-z)) =
        Psi.character (truncatedLog p (z : F))) ∧
      Nonempty (CompatibleModels F E U K p s.T s.q0 s.q0_pos
        s.tauF.1 Psi.character (s.c : F) (s.d : U)) := by
  let U := UnramifiedField F K
  let E := RamifiedField F K H
  letI : ValuativeRel U := Basic.intermediateFieldValuativeRel U
  letI : TopologicalSpace U := Basic.intermediateFieldTopology U
  letI : IsNonarchimedeanLocalField U := Basic.intermediateField_localField U
  letI : ValuativeExtension F U := Basic.intermediateField_lowerValuativeExtension U
  letI : ValuativeExtension U K := Basic.intermediateField_upperValuativeExtension U
  letI : ValuativeRel E := Basic.intermediateFieldValuativeRel E
  letI : TopologicalSpace E := Basic.intermediateFieldTopology E
  letI : IsNonarchimedeanLocalField E := Basic.intermediateField_localField E
  letI : ValuativeExtension F E := Basic.intermediateField_lowerValuativeExtension E
  letI : ValuativeExtension E K := Basic.intermediateField_upperValuativeExtension E
  letI : PrimeCyclicExtension F U := (modelFixedField_primeCyclic hp hG _ hI).1
  letI : PrimeCyclicExtension U K := (modelFixedField_primeCyclic hp hG _ hI).2
  letI : PrimeCyclicExtension F E := (modelFixedField_primeCyclic hp hG H hH).1
  letI : PrimeCyclicExtension E K := (modelFixedField_primeCyclic hp hG H hH).2
  have hFU : Module.finrank F U = p := modelFixedField_degree hp hG _ hI
  have hFE : Module.finrank F E = p := modelFixedField_degree hp hG H hH
  have hUK : Module.finrank U K = p := by
    change Module.finrank (IntermediateField.fixedField _) K = p
    rw [IntermediateField.finrank_fixedField_eq_card, hI]
  have hEK : Module.finrank E K = p := by
    change Module.finrank (IntermediateField.fixedField H) K = p
    rw [IntermediateField.finrank_fixedField_eq_card, hH]
  have hb : residueDegree F E = 1 ∧ ramificationIndex E K = 1 ∧
      PrimeCyclicExtension.IsLowerBreak F E s.t ∧
      PrimeCyclicExtension.IsLowerBreak U K s.t := by
    simpa only [Ramification.UnramifiedBaseChangeBreakPair, U, E,
      UnramifiedField, RamifiedField] using s.breaks
  have hunr : ramificationIndex F U = 1 :=
    ((Ramification.diamondBreaks hp hG hchar).2 hI).unramified_lower.1
  have hresUK : residueDegree U K = 1 := by
    obtain ⟨L, hL, hLres⟩ := Ramification.exists_inertiaUniformizer (F := F) (K := K)
    subst L
    exact hLres.1
  have hsep : (normUnits F U).range ≠ (normUnits F E).range :=
    (Ramification.normSeparation hp hG).unramified_lower hI H hH hne
  obtain ⟨alpha, halpha, hchart⟩ := s.normalizedCoefficient psiF hpsiF
  let Psi := scaleAddCharData F (canonicalLocalAddCharData F psiF hpsiF) alpha
  have horder : unitOrder F alpha = -(canonicalLocalAddCharData F psiF hpsiF).conductor - (s.T : ℤ) :=
    WithTop.coe_inj.mp ((ord_coe_eq_unitOrder F alpha).symm.trans halpha)
  have hn : Psi.conductor = -(s.T : ℤ) := by
    dsimp only [Psi]
    rw [scaleAddCharData_conductor, horder]
    ring
  have htau : ∀ z : lattice F (s.q0 : ℤ),
      s.tauF.1 (positiveUnitOfLattice F s.q0_pos (-z)) = Psi.character (truncatedLog p (z : F)) := by
    intro z
    exact hchart z
  refine ⟨alpha, halpha, hn, htau, ?_⟩
  have hqeq : s.q0 = (s.t + 1) ⌈/⌉ p := by rw [s.q0_eq, s.T_eq]
  have hq : 0 < (s.t + 1) ⌈/⌉ p := hqeq ▸ s.q0_pos
  have htauunits := (one_sub_chart_iff_units F p s.q0 s.q0_pos s.tauF.1 Psi.character 1).1
    (by simpa only [one_mul] using htau)
  have hPsi : IsAdditiveConductor F Psi.character (-((s.t + 1 : ℕ) : ℤ)) := by
    simpa only [hn, s.T_eq] using Psi.isConductor
  have hpair := compatibleModels_of_normalized_data F E U K hp (by have := s.odd_prime; omega)
    s.t_pos hFE hFU hUK hEK hb.2.2.1 hb.2.2.2 hb.1 hresUK hunr hb.2.1 hchar hsep hq
    s.tauF s.tauF_ne_one Psi.character hPsi (by
      rw [← hqeq]
      simpa only [one_mul] using htauunits)
    s.c s.d s.artinSchreier.1 s.artinSchreier.2.2.1
  simpa only [s.T_eq, hqeq] using hpair

end SetupAdapter

end
end LanglandsSecondMainLemma.Odd.UR
