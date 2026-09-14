import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsSecondMainLemma.Odd.Conductors.Lower
import LanglandsSecondMainLemma.Local.Hilbert90

/-!
# Deep norm-kernel descent

Paper Lemma 9.33 (`O:G:deep`), with the setup at lines 4962–4982.
We construct a best base-field approximation to a Hilbert 90 representative.
Its approximation order is prime to the ramification index: otherwise a
residue lift improves it. The exact ramification leading term then puts the
normalized representative in the trivial layer of the conjugate quotient.

The maximum is finite because the nonzero Galois displacement bounds every
approximation order. This is a finite version of the paper's closed-subfield
argument, and works with arbitrary integer orders in both characteristics.
-/

namespace LanglandsSecondMainLemma.Odd.Conductors

open LanglandsFirstMainLemma

noncomputable section

section Approximation
variable {F E : Type} [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]

/-- The common residue field improves an approximation at any integer
multiple of the ramification index, including negative multiples. -/
private theorem improve_at_ramification_multiple
    (hres : residueDegree F E = 1) (k : ℤ) {z : E}
    (hz : z ∈ lattice E ((ramificationIndex F E : ℤ) * k)) :
    ∃ b : F, z - algebraMap F E b ∈
      lattice E ((ramificationIndex F E : ℤ) * k + 1) := by
  obtain ⟨a, ha⟩ := exists_ord_eq F k
  have ha0 : a ≠ 0 := (ord_ne_top_iff F).1 (by rw [ha]; simp)
  have haE0 : algebraMap F E a ≠ 0 := by
    simpa using (algebraMap F E).injective.ne ha0
  have haE : ord E (algebraMap F E a) =
      (((ramificationIndex F E : ℤ) * k : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, ha, ← WithTop.coe_nsmul]
    rfl
  have hz0 : z / algebraMap F E a ∈ lattice E 0 := by
    apply (div_mem_lattice_iff E _ _ _ 0 haE).2
    simpa using hz
  let zO : ringOfIntegers E :=
    ⟨z / algebraMap F E a, (mem_lattice_zero_iff E).1 hz0⟩
  obtain ⟨b, hb⟩ :=
    exists_ringOfIntegers_sub_mem_maximalIdeal_of_residueDegree_eq_one F E hres zO
  have hdiff : z / algebraMap F E a - algebraMap F E (b : F) ∈ lattice E 1 := by
    exact (mem_lattice_one_iff_mem_maximalIdeal E
      (zO - algebraMap (ringOfIntegers F) (ringOfIntegers E) b)).2 hb
  refine ⟨a * (b : F), ?_⟩
  have hprod := mul_mem_lattice E (show algebraMap F E a ∈
      lattice E ((ramificationIndex F E : ℤ) * k) by rw [mem_lattice, haE]) hdiff
  convert hprod using 1
  rw [map_mul]
  field_simp

/-- A moved element has a best base-field approximation, whose integer
order is not divisible by the ramification index. -/
private theorem best_approximation
    (hres : residueDegree F E = 1) (σ : Gal(E/F)) {y : E} (hy : σ y ≠ y) :
    ∃ (a : F) (q : ℤ), ord E (y - algebraMap F E a) = (q : WithTop ℤ) ∧
      ¬ (ramificationIndex F E : ℤ) ∣ q := by
  have hy0 : y ≠ 0 := by intro h; apply hy; simp [h]
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp
    ((ord_ne_top_iff E).2 (sub_ne_zero.mpr hy))
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff E).2 hy0)
  let P : ℤ → Prop := fun q => ∃ a : F, (q : WithTop ℤ) ≤ ord E (y - algebraMap F E a)
  have hbound : ∀ q, P q → q ≤ d := by
    rintro q ⟨a, ha⟩
    have hdiff : σ (y - algebraMap F E a) - (y - algebraMap F E a) = σ y - y := by
      rw [map_sub, σ.commutes]
      ring
    have h := ord_sub E (σ (y - algebraMap F E a)) (y - algebraMap F E a)
    rw [ord_galoisConjugate, min_self, hdiff, ← hd] at h
    exact WithTop.coe_le_coe.mp (ha.trans h)
  have hnonempty : ∃ q, P q := ⟨m, 0, by simp [← hm]⟩
  obtain ⟨q, ⟨a, ha⟩, hmax⟩ := Int.exists_greatest_of_bdd ⟨d, hbound⟩ hnonempty
  have hno : ¬ P (q + 1) := fun h => (by have := hmax _ h; omega)
  have hq : ord E (y - algebraMap F E a) = (q : WithTop ℤ) :=
    (withTopInt_le_and_not_succ_le_iff_eq q _).1 ⟨ha, fun h => hno ⟨a, h⟩⟩
  refine ⟨a, q, hq, ?_⟩
  rintro ⟨k, hk⟩
  obtain ⟨b, hb⟩ := improve_at_ramification_multiple hres k
    (show y - algebraMap F E a ∈ lattice E ((ramificationIndex F E : ℤ) * k) by
      rw [← hk, mem_lattice, hq])
  apply hno
  refine ⟨a + b, ?_⟩
  rw [mem_lattice, ← hk] at hb
  simpa only [map_add, sub_add_eq_sub_sub] using hb

end Approximation

section Edge
variable {F E : Type} [Field F] [Field E]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
  [PrimeCyclicExtension F E]

/-- A lower-break profile has full inertia, hence residue degree one.
This uses the actual residue-action quotient and avoids choosing a second
valuation or repeating the residue-degree tower calculation. -/
private theorem residueDegree_one_of_isLowerBreak
    {s : ℕ} (hs : PrimeCyclicExtension.IsLowerBreak F E s) :
    residueDegree F E = 1 := by
  have hzero : lowerRamificationGroup F E 0 = ⊤ :=
    PrimeCyclicExtension.lowerRamificationGroup_eq_top_of_le_break F E hs
      (Int.natCast_nonneg s)
  have hI : Ramification.inertiaSubgroup (F := F) (K := E) = ⊤ :=
    Ramification.inertiaSubgroup_eq_lowerRamificationGroup_zero.trans hzero
  have hcard := Nat.card_congr
    (Ramification.residueActionQuotientEquiv (F := F) (K := E)).toEquiv
  rw [hI] at hcard
  rw [residueDegree_eq_finrank_residueField, ← IsGalois.card_aut_eq_finrank]
  exact hcard.symm.trans (Subgroup.index_top (G := Gal(E/F)))

/-- The accepted leading-term theorem, with its uniformizer coefficient
constructed from the actual lower break. -/
private theorem exact_displacement
    {s : ℕ} (hs : PrimeCyclicExtension.IsLowerBreak F E s) (hspos : 0 < s)
    (hres : residueDegree F E = 1) (σ : Gal(E/F)) (hσ : σ ≠ 1)
    {z : E} {q : ℤ} (hz : ord E z = (q : WithTop ℤ))
    (hq : ¬ (ramificationIndex F E : ℤ) ∣ q) :
    ord E (σ z - z) = ((q + s : ℤ) : WithTop ℤ) := by
  obtain ⟨π, hπ, hgen⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one F E hres
  have hdiff := ord_galois_uniformizer_sub_eq_of_isLowerBreak F E hs π hπ hgen hσ
  let c : E := (σ (π : E) - (π : E)) / (π : E) ^ (s + 1)
  have hc : ord E c = 0 := by
    dsimp only [c]
    rw [ord_div, hdiff, ord_pow, ord_uniformizer E hπ]
    simp
  have hπeq : σ (π : E) = (π : E) * (1 + c * (π : E) ^ s) := by
    dsimp only [c]
    field_simp [hπ.ne_zero]
    ring
  have hσzero : σ ∈ lowerRamificationGroup F E 0 := by
    apply lowerRamificationGroup_mono F E (Int.natCast_nonneg s)
    rw [hs.1]
    trivial
  have hchar : residueCharacteristic E = ramificationIndex F E := by
    rw [residueCharacteristic_extension_eq F E,
      residueCharacteristic_eq_degree_of_positive_isLowerBreak F E hs hspos π hπ hgen,
      finrank_eq_ramificationIndex_mul_residueDegree F E, hres, mul_one]
  exact Ramification.leadingTerm ⟨σ, hσzero⟩ (π : E) c hπ hspos hc hπeq
    ((ord_ne_top_iff E).1 (by rw [hz]; simp)) hz (by rwa [hchar])

/-- Deep norm-one units have deep Hilbert 90 representatives. The
representative is obtained by dividing by a best base-field approximation;
no surjectivity of a critical norm map is asserted. -/
private theorem deep_hilbert90
    {s u : ℕ} (hs : PrimeCyclicExtension.IsLowerBreak F E s) (hspos : 0 < s)
    (hres : residueDegree F E = 1) (x : Eˣ)
    (hx : x ∈ unitFiltration E (1 + s + u)) (hnorm : normUnits F E x = 1) :
    ∃ y : Eˣ, y ∈ unitFiltration E (u + 1) ∧
      Local.multiplicativeCoboundary (PrimeCyclicExtension.generator F E) y = x := by
  by_cases hxone : x = 1
  · exact ⟨1, (unitFiltration E (u + 1)).one_mem, by simp [hxone]⟩
  let σ := PrimeCyclicExtension.generator F E
  have hxker : x ∈ (normUnits F E).ker := hnorm
  rw [(Local.hilbert90 σ (PrimeCyclicExtension.generator_mem_zpowers F E)).1] at hxker
  obtain ⟨y, hy⟩ := hxker
  have hymoved : σ (y : E) ≠ (y : E) := by
    intro h
    apply hxone
    rw [← hy, Local.multiplicativeCoboundary_apply, div_eq_one]
    exact Units.ext h.symm
  obtain ⟨a, q, hq, hqprime⟩ := best_approximation hres σ hymoved
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
    ((ord_ne_top_iff E).2 y.ne_zero)
  have hdisp : ord E (σ (y : E) - (y : E)) = ((q + s : ℤ) : WithTop ℤ) := by
    have h := exact_displacement hs hspos hres σ
      (PrimeCyclicExtension.generator_ne_one F E) hq hqprime
    simpa only [map_sub, σ.commutes, sub_sub_sub_cancel_right] using h
  have hxord : ord E ((x : E) - 1) = ((q + s - m : ℤ) : WithTop ℤ) := by
    have heq : (x : E) - 1 = ((y : E) - σ (y : E)) / σ (y : E) := by
      rw [← hy, Local.multiplicativeCoboundary_apply, Units.val_div_eq_div_val]
      change (y : E) / σ (y : E) - 1 = _
      field_simp
    rw [heq, ord_div, ord_sub_swap E, hdisp, ord_galoisConjugate, ← hm]
    rfl
  have hdepth : (u : ℤ) + 1 ≤ q - m := by
    have h := (mem_unitFiltration_succ_iff_sub_mem_lattice E (s + u) x).1
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hx)
    rw [mem_lattice, hxord, WithTop.coe_le_coe] at h
    push_cast at h
    omega
  have hmq : m < q := by omega
  have haord : ord E (algebraMap F E a) = (m : WithTop ℤ) := by
    have heq : algebraMap F E a = (y : E) + -( (y : E) - algebraMap F E a) := by ring
    rw [heq, ord_add_eq_min E (by rw [ord_neg, hq, ← hm]; exact_mod_cast ne_of_lt hmq),
      ord_neg, hq, ← hm, min_eq_left (WithTop.coe_le_coe.mpr hmq.le)]
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero, ord_zero] at haord
    exact WithTop.top_ne_coe haord
  let aU : Fˣ := Units.mk0 a ha0
  let y' : Eˣ := y / Units.map (algebraMap F E).toMonoidHom aU
  refine ⟨y', ?_, ?_⟩
  · apply (mem_unitFiltration_succ_iff_sub_mem_lattice E u y').2
    have heq : (y' : E) - 1 = ((y : E) - algebraMap F E a) / algebraMap F E a := by
      dsimp only [y']
      rw [Units.val_div_eq_div_val]
      change (y : E) / algebraMap F E a - 1 = _
      have haE0 : algebraMap F E a ≠ 0 := by
        simpa using (algebraMap F E).injective.ne ha0
      field_simp [haE0]
    rw [heq, mem_lattice, ord_div, hq, haord]
    exact WithTop.coe_le_coe.mpr (by simpa using hdepth)
  · have hbase : Local.multiplicativeCoboundary σ
        (Units.map (algebraMap F E).toMonoidHom aU) = 1 := by
      rw [Local.multiplicativeCoboundary_apply, div_eq_one]
      apply Units.ext
      exact (σ.commutes a).symm
    change Local.multiplicativeCoboundary σ (y / _) = x
    rw [map_div, hbase, div_one, hy]

end Edge

section Tower
variable {F E K : Type} [Field F] [Field E] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F E] [Algebra E K]
  [ValuativeExtension F E] [ValuativeExtension E K]
  [Module.Finite F E] [Module.Finite E K]
  [PrimeCyclicExtension F E] [PrimeCyclicExtension E K]

/-- Apply the constructed deep representative to the actual conjugate
quotient. Its conductor is supplied by FML for the upper norm character. -/
private theorem descent_of_conjugateTwistData
    {θ : ContinuousQuasiChar E} (D : Characters.ConjugateTwistData F E K θ)
    {s u : ℕ} (hs : PrimeCyclicExtension.IsLowerBreak F E s) (hspos : 0 < s)
    (hu : PrimeCyclicExtension.IsLowerBreak E K u)
    (x : Eˣ) (hx : x ∈ unitFiltration E (1 + s + u))
    (hnorm : normUnits F E x = 1) : θ x = 1 := by
  have hresFE := residueDegree_one_of_isLowerBreak hs
  have hresEK := residueDegree_one_of_isLowerBreak hu
  obtain ⟨y, hy, hxy⟩ := deep_hilbert90 hs hspos hresFE x hx hnorm
  let σ := PrimeCyclicExtension.generator F E
  let μ := D.quotientEquiv σ.symm
  have hμ : μ ≠ 1 := by
    intro h
    have hσ : σ.symm = 1 :=
      D.quotientEquiv.injective (h.trans D.quotientEquiv.map_one.symm)
    exact PrimeCyclicExtension.generator_ne_one F E
      (inv_eq_one.mp (show σ⁻¹ = 1 from hσ))
  obtain ⟨π, hπ, hgen⟩ :=
    exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one E K hresEK
  have hcond := ramifiedNormCharacter_conductor E K hu hresEK π hπ hgen μ hμ
  have hvalue := hcond.trivial y hy
  have hquot := DFunLike.congr_fun (D.quotient_eq σ.symm) y
  change μ.1 y = θ (Units.map σ.toMonoidHom y) / θ y at hquot
  rw [hvalue] at hquot
  have hθ : θ (Units.map σ.toMonoidHom y) = θ y := div_eq_one.mp hquot.symm
  rw [← hxy, Local.multiplicativeCoboundary_apply, map_div, hθ]
  simp

end Tower

section Pair
variable {F K : Type} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] [IsGalois F K]

/-- **Paper Lemma 9.33 (`O:G:deep`).** An endpoint of the actual primitive
compatible pair is trivial on the norm-one units of depth `1 + s + u`.

Here `E/F` is the chosen lower edge and `K/E` its upper edge, with the
paper's breaks `s` and `u`. Both valuations are the canonical intermediate
field valuations; `normUnits F E` is the actual lower field norm. The
upper conjugate-quotient character and its conductor are constructed from
compatibility and non-descent, rather than supplied as hypotheses.

The proof of the local vanishing is valid even without the oddness and
prime-to-`p` upper-break restrictions, which are retained here to match the
paper's ambient odd-prime statement. No restriction on field characteristic
or on the absolute values of the continuous quasi-characters is imposed. -/
theorem descent {p : ℕ} (hp : p.Prime) (_hodd : 2 < p)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (E E' : IntermediateField F K)
    (hE : Module.finrank F E = p) (hE' : Module.finrank F E' = p)
    (hne : Ramification.intermediateNormRange E ≠
      Ramification.intermediateNormRange E') :
    letI := Basic.intermediateFieldValuativeRel E
    letI := Basic.intermediateFieldTopology E
    letI := Basic.intermediateField_localField E
    letI := Basic.intermediateField_lowerValuativeExtension E
    letI := Basic.intermediateField_upperValuativeExtension E
    letI := Basic.intermediateFieldValuativeRel E'
    letI := Basic.intermediateFieldTopology E'
    letI := Basic.intermediateField_localField E'
    letI := Basic.intermediateField_lowerValuativeExtension E'
    letI := Basic.intermediateField_upperValuativeExtension E'
    ∀ (s u : ℕ), PrimeCyclicExtension.IsLowerBreak F E s → 0 < s →
      PrimeCyclicExtension.IsLowerBreak E K u → (¬ p ∣ u) →
      ∀ (θ : ContinuousQuasiChar E) (θ' : ContinuousQuasiChar E')
        (Θ : ContinuousQuasiChar K),
        normQuasiChar E K θ = Θ → normQuasiChar E' K θ' = Θ →
        (¬ ∃ χ : ContinuousQuasiChar F, normQuasiChar F K χ = Θ) →
        ∀ x : Eˣ, x ∈ unitFiltration E (1 + s + u) →
          normUnits F E x = 1 → θ x = 1 := by
  letI := Basic.intermediateFieldValuativeRel E
  letI := Basic.intermediateFieldTopology E
  letI := Basic.intermediateField_localField E
  letI := Basic.intermediateField_lowerValuativeExtension E
  letI := Basic.intermediateField_upperValuativeExtension E
  letI := Basic.intermediateFieldValuativeRel E'
  letI := Basic.intermediateFieldTopology E'
  letI := Basic.intermediateField_localField E'
  letI := Basic.intermediateField_lowerValuativeExtension E'
  letI := Basic.intermediateField_upperValuativeExtension E'
  intro s u hs hspos hu _huprime θ θ' Θ hc hc' hprimitive x hx hnorm
  have hdata := Basic.intermediateField_tower_compatible hp hG E hE
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension F E
    hdata.2.2.2.2.2.2.2.2.2.2.2.1
  letI := PrimeCyclicExtension.ofCyclicPrimeExtension E K
    hdata.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨D⟩, _⟩ := Characters.conjugacy hp hG E E' hE hE' hne
    θ θ' Θ hc hc' hprimitive
  exact descent_of_conjugateTwistData D hs hspos hu x hx hnorm

end Pair

end

end LanglandsSecondMainLemma.Odd.Conductors
