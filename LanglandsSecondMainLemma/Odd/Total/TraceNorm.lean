import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Total.TwistedEstimates

/-!
# Odd / Total / Trace Norm

Paper `O:A:thm:H14` (Theorem 7.5). The exact coefficient expansion of the
iterated norms is split into a trace, a norm, and free prime-degree orbits.
The latter are sums of actual field traces, so the accepted fractional
trace-ideal theorem applies. In the exceptional cubic equal-break case,
whole-lattice duality proves injectivity on the last trace quotient and
improves the first coefficient by one depth.

The polynomial calculations use `1 + Z*Delta`, equivalently substituting
`-Z` into the paper's polynomials. Every norm, trace and coordinate remains
in its actual field. All fractional ideal depths are integers, and the
valuations include infinity. `traceNorm` retains any supplied exact
coordinate with the accepted bounds; `exists_traceNorm_coordinate` supplies
such a coordinate directly from `twistedEstimates`.
-/

namespace LanglandsSecondMainLemma.Odd.Total

open LanglandsFirstMainLemma
open scoped BigOperators

noncomputable section

section LastTraceQuotient

variable (F E : Type*) [Field F] [Field E]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
variable [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]

/-- Residue degree one supplies a base approximation at every integral
multiple of the ramification index, including negative multiples. -/
private theorem baseApproximation_at_multiple
    (hres : residueDegree F E = 1) (s : ℤ) {y : E}
    (hy : y ∈ lattice E ((ramificationIndex F E : ℤ) * s)) :
    ∃ b : F, b ∈ lattice F s ∧
      y - algebraMap F E b ∈ lattice E ((ramificationIndex F E : ℤ) * s + 1) := by
  obtain ⟨u, hu⟩ := exists_ord_eq F s
  have hu0 : u ≠ 0 := (ord_ne_top_iff F).1 (by rw [hu]; simp)
  have huE : ord E (algebraMap F E u) =
      (((ramificationIndex F E : ℤ) * s : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hu, ← WithTop.coe_nsmul]
    rfl
  let z : E := y / algebraMap F E u
  have hz : z ∈ lattice E 0 := by
    apply (div_mem_lattice_iff E (algebraMap F E u) y
      ((ramificationIndex F E : ℤ) * s) 0 huE).2
    simpa using hy
  let zO : ringOfIntegers E := ⟨z, (mem_lattice_zero_iff E).1 hz⟩
  obtain ⟨v, hv⟩ :=
    exists_ringOfIntegers_sub_mem_maximalIdeal_of_residueDegree_eq_one F E hres zO
  have hdiff : z - algebraMap F E (v : F) ∈ lattice E 1 := by
    have := (mem_lattice_one_iff_mem_maximalIdeal E _).2 hv
    change z - ((algebraMap (ringOfIntegers F) (ringOfIntegers E) v :
      ringOfIntegers E) : E) ∈ lattice E 1 at this
    simpa only [Valuation.HasExtension.val_algebraMap] using this
  refine ⟨u * (v : F), ?_, ?_⟩
  · have huLat : u ∈ lattice F s := by rw [mem_lattice, hu]
    have hvLat : (v : F) ∈ lattice F 0 := (mem_lattice_zero_iff F).2 v.property
    simpa using mul_mem_lattice F huLat hvLat
  · have huLat : algebraMap F E u ∈
        lattice E ((ramificationIndex F E : ℤ) * s) := by rw [mem_lattice, huE]
    have h := mul_mem_lattice E huLat hdiff
    convert h using 1
    dsimp only [z]
    rw [map_mul]
    have huE0 : algebraMap F E u ≠ 0 := by
      simpa using (algebraMap F E).injective.ne hu0
    field_simp [huE0]

variable [Module.Free F E] [Algebra.IsSeparable F E]

/-- Injectivity on the last nonzero trace quotient. This is the kernel step
used in `O:A:thm:H14`, proved from exact fractional trace ideals and residue
degree one. The equality `r + D = e(q+1)-1` identifies the last quotient;
it does not assume injectivity or a special representative. -/
theorem lastTraceQuotient_kernel
    (hres : residueDegree F E = 1) (r q : ℤ)
    (hlast : r + Local.differentIdealExponent F E =
      (ramificationIndex F E : ℤ) * (q + 1) - 1)
    {x : E} (hx : x ∈ lattice E r)
    (htrace : trace F E x ∈ lattice F (q + 1)) :
    x ∈ lattice E (r + 1) := by
  apply (mem_lattice_iff_integral_tracePairing F E x (r + 1)).2
  intro y hy
  have hm : (ramificationIndex F E : ℤ) * (-(q + 1)) =
      -Local.differentIdealExponent F E - (r + 1) := by nlinarith [hlast]
  obtain ⟨b, hb, hyb⟩ := baseApproximation_at_multiple F E hres (-(q + 1))
    (by rw [hm]; exact hy)
  have hbase : trace F E (algebraMap F E b * x) ∈ lattice F 0 := by
    rw [← Algebra.smul_def, map_smul]
    simpa only [smul_eq_mul, neg_add_cancel] using mul_mem_lattice F hb htrace
  have herr : (y - algebraMap F E b) * x ∈
      lattice E (-Local.differentIdealExponent F E) := by
    have h := mul_mem_lattice E hyb hx
    convert h using 1
    congr 1
    rw [hm]
    ring
  have herrTrace : trace F E ((y - algebraMap F E b) * x) ∈ lattice F 0 := by
    have himage : trace F E ((y - algebraMap F E b) * x) ∈
        Submodule.map ((trace F E).restrictScalars (ringOfIntegers F))
          ((lattice E (-Local.differentIdealExponent F E)).restrictScalars
            (ringOfIntegers F)) := Submodule.mem_map.mpr ⟨_, herr, rfl⟩
    rw [Local.traceIdeal_eq F E] at himage
    simpa using himage
  have hsum := (lattice F 0).add_mem hbase herrTrace
  rw [← map_add, ← add_mul, add_sub_cancel] at hsum
  exact hsum

/-- In the cubic equal-break case, zero trace improves depth `t` to `t+1`.
This is precisely the exceptional last-quotient argument of the paper. -/
theorem cubic_trace_zero_depth
    (hres : residueDegree F E = 1) (hram : ramificationIndex F E = 3)
    (t : ℤ) (hdiff : Local.differentIdealExponent F E = 2 * (t + 1))
    {x : E} (hx : x ∈ lattice E t) (htrace : trace F E x = 0) :
    x ∈ lattice E (t + 1) := by
  apply lastTraceQuotient_kernel F E hres t t _ hx
  · simp [htrace]
  · rw [hdiff, hram]
    push_cast
    ring

end LastTraceQuotient

/-- A finite equivariant sum on a free Galois set is an actual sum of field
traces, with one term per orbit. No division by the group order is used. -/
theorem freeGaloisSum_eq_sum_trace
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Module.Finite F E] [IsGalois F E]
    (X : Type*) [Fintype X] [MulAction Gal(E/F) X]
    (hfree : ∀ x : X, MulAction.stabilizer Gal(E/F) x = ⊥)
    (f : X → E) (heqv : ∀ (g : Gal(E/F)) (x : X), f (g • x) = g (f x)) :
    letI := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(E/F) X)
    ∃ s : F, algebraMap F E s = ∑ x, f x ∧
      s = ∑ o : MulAction.orbitRel.Quotient Gal(E/F) X, trace F E (f o.out) := by
  classical
  letI := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(E/F) X)
  let e := MulAction.selfEquivOrbitsQuotientProd hfree
  have hinv (o : MulAction.orbitRel.Quotient Gal(E/F) X) (g : Gal(E/F)) :
      e.symm (o, g) = g • o.out := by
    rfl
  refine ⟨_, ?_, rfl⟩
  rw [map_sum]
  simp_rw [trace_eq_sum_automorphisms]
  simpa only [Fintype.sum_prod_type, hinv, heqv] using (e.symm.sum_comp f)

attribute [local instance] Classical.propDecidable

private theorem prod_monomial
    {I R : Type*} [CommSemiring R] (s : Finset I) (n : I → ℕ) (a : I → R) :
    (∏ i ∈ s, Polynomial.monomial (n i) (a i)) =
      Polynomial.monomial (∑ i ∈ s, n i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp [Finset.prod_insert hi, Finset.sum_insert hi, ih,
      Polynomial.monomial_mul_monomial]

/-- Exact coefficient expansion of a product of truncated polynomials.
The natural index is a polynomial degree, not a fractional-ideal depth. -/
theorem coefficient_product_selections
    {I R : Type*} [Fintype I] [CommSemiring R]
    (p n : ℕ) (a : I → Fin (p + 1) → R) :
    (∏ g, ∑ i : Fin (p + 1), Polynomial.monomial (i : ℕ) (a g i)).coeff n =
      ∑ w : I → Fin (p + 1),
        if (∑ g, (w g : ℕ)) = n then ∏ g, a g (w g) else 0 := by
  classical
  rw [Fintype.prod_sum]
  simp_rw [prod_monomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]

/-- Nonconstant selections of total weight `p` using only the intermediate
coefficients. This is exactly the trace part of the paper's coefficient
comparison; the all-`e₁` selection and the single-`b` selections are separate. -/
abbrev TraceNormSelection (G : Type*) [Fintype G] (p : ℕ) :=
  {w : G → Fin (p + 1) // (∑ g, (w g : ℕ)) = p ∧
    (∃ g, (w g : ℕ) ≠ 1) ∧ ∀ g, (w g : ℕ) < p}

@[reducible] private def selectionAction (G : Type*) [Group G] [Fintype G] (p : ℕ) :
    MulAction G (TraceNormSelection G p) where
  smul g w := ⟨fun h => w.val (g⁻¹ * h), by
    constructor
    · exact (Equiv.sum_comp (Equiv.mulLeft g⁻¹)
        (fun h => (w.val h : ℕ))).trans w.property.1
    constructor
    · obtain ⟨h, hh⟩ := w.property.2.1
      exact ⟨g * h, by simpa using hh⟩
    · intro h
      exact w.property.2.2 _⟩
  one_smul w := by
    apply Subtype.ext
    funext h
    change w.val (1⁻¹ * h) = w.val h
    simp
  mul_smul g h w := by
    apply Subtype.ext
    funext k
    change w.val ((g * h)⁻¹ * k) = w.val (h⁻¹ * (g⁻¹ * k))
    simp [mul_assoc]

/-- All the intermediate nonconstant selections have full Galois orbits
in prime degree. This uses the actual prime-order group, without dividing
by `p` in the field. -/
theorem traceNormSelection_stabilizer
    (G : Type*) [Group G] [Fintype G] {p : ℕ} (hp : p.Prime)
    (hcard : Fintype.card G = p) :
    letI := selectionAction G p
    ∀ w : TraceNormSelection G p, MulAction.stabilizer G w = ⊥ := by
  letI := selectionAction G p
  letI : Fact (Nat.card G).Prime := ⟨by simpa [Nat.card_eq_fintype_card, hcard] using hp⟩
  intro w
  rcases (MulAction.stabilizer G w).eq_bot_or_eq_top_of_prime_card with h | h
  · exact h
  · have hconst (g : G) : (w.val g : ℕ) = (w.val 1 : ℕ) := by
      have hmem : g⁻¹ ∈ MulAction.stabilizer G w := by rw [h]; trivial
      have heq : g⁻¹ • w = w := hmem
      have hval := congrArg (fun u : TraceNormSelection G p => (u.val 1 : ℕ)) heq
      change (w.val ((g⁻¹)⁻¹ * 1) : ℕ) = (w.val 1 : ℕ) at hval
      simpa using hval
    have hsum := w.property.1
    simp_rw [hconst] at hsum
    simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul] at hsum
    have hone : (w.val 1 : ℕ) = 1 := by
      have : p * (w.val 1 : ℕ) = p * 1 := by simpa using hsum
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
    obtain ⟨g, hg⟩ := w.property.2.1
    exact False.elim (hg ((hconst g).trans hone))

/-- A weight-`p` selection with every entry below `p` has at least two
positive entries. -/
theorem traceNormSelection_support_card
    (G : Type*) [Fintype G] {p : ℕ} (hp : 0 < p)
    (w : TraceNormSelection G p) :
    2 ≤ (Finset.univ.filter (fun g => 0 < (w.val g : ℕ))).card := by
  classical
  let S := Finset.univ.filter (fun g => 0 < (w.val g : ℕ))
  have hsum : (∑ g ∈ S, (w.val g : ℕ)) = p := by
    rw [show (∑ g ∈ S, (w.val g : ℕ)) = ∑ g, (w.val g : ℕ) by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro g hg hnot
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt,
        Nat.le_zero] at hnot
      exact hnot]
    exact w.property.1
  obtain ⟨g, hg, hgpos⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show (∑ g ∈ S, (w.val g : ℕ)) ≠ 0 by rw [hsum]; omega)
  by_contra h
  change ¬ 2 ≤ S.card at h
  have hcard : S.card ≤ 1 := by omega
  have hsingle : S = {g} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hg, fun h hh => (Finset.card_le_one.mp hcard h hh g hg)⟩
  rw [hsingle, Finset.sum_singleton] at hsum
  have := w.property.2.2 g
  omega

/-- The product attached to a selection uses the actual conjugates of the
coefficients. Left translation of the selection acts on the product by the
same field automorphism. -/
theorem traceNormSelection_product_equivariant
    (F E : Type*) [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    (p : ℕ) (c : Fin (p + 1) → E) :
    letI := selectionAction Gal(E/F) p
    ∀ (g : Gal(E/F)) (w : TraceNormSelection Gal(E/F) p),
      (∏ h : Gal(E/F), h (c ((g • w).val h))) =
        g (∏ h : Gal(E/F), h (c (w.val h))) := by
  classical
  letI := selectionAction Gal(E/F) p
  intro g w
  change (∏ h : Gal(E/F), h (c (w.val (g⁻¹ * h)))) = _
  rw [map_prod]
  have h := Equiv.prod_comp (Equiv.mulLeft g)
    (fun h : Gal(E/F) => h (c (w.val (g⁻¹ * h))))
  change (∏ k : Gal(E/F), (g * k) (c (w.val (g⁻¹ * (g * k))))) = _ at h
  simpa only [inv_mul_cancel_left, AlgEquiv.mul_apply] using h.symm

private theorem product_mem_lattice
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {I : Type*} (s : Finset I) (f : I → E) (d : I → ℤ)
    (h : ∀ i ∈ s, f i ∈ lattice E (d i)) :
    (∏ i ∈ s, f i) ∈ lattice E (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mul_mem_lattice E (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

/-- The paper's lower bound on a nonconstant coefficient selection before
taking its trace. Negative coefficient depths are retained. -/
theorem traceNormSelection_product_mem
    (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
    {p : ℕ} (hp : 0 < p) (C t : ℤ) (hC : 0 ≤ C)
    (c : Fin (p + 1) → E) (hc0 : c 0 = 1)
    (hc : ∀ i : Fin (p + 1), 1 ≤ (i : ℕ) → (i : ℕ) < p →
      c i ∈ lattice E (C - (i : ℕ) * t))
    (w : TraceNormSelection Gal(E/F) p) :
    (∏ g : Gal(E/F), g (c (w.val g))) ∈ lattice E (2 * C - (p : ℤ) * t) := by
  classical
  let S := Finset.univ.filter (fun g => 0 < (w.val g : ℕ))
  have hcard : 2 ≤ S.card := traceNormSelection_support_card _ hp w
  have hsum : (∑ g ∈ S, (w.val g : ℕ)) = p := by
    calc
      _ = ∑ g, (w.val g : ℕ) := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro g hg hnot
        simpa [S, Nat.le_zero] using hnot
      _ = p := w.property.1
  have hprod : (∏ g ∈ S, g (c (w.val g))) = ∏ g : Gal(E/F), g (c (w.val g)) := by
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro g hg hnot
    have hz : w.val g = 0 := by
      apply Fin.ext
      simpa [S, Nat.le_zero] using hnot
    simp [hz, hc0]
  have hbound := product_mem_lattice E S
    (fun g => g (c (w.val g))) (fun g => C - (w.val g : ℕ) * t) (by
      intro g hg
      rw [mem_lattice, ord_galoisConjugate]
      exact hc (w.val g) (by
        have hgpos : 0 < (w.val g : ℕ) := (Finset.mem_filter.mp hg).2
        omega) (w.property.2.2 g))
  have hdepth : (∑ g ∈ S, (C - (w.val g : ℕ) * t : ℤ)) =
      (S.card : ℤ) * C - (p : ℤ) * t := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul]
    norm_cast
    rw [hsum]
  rw [hdepth, hprod] at hbound
  apply lattice_antitone E _ hbound
  have hcardZ : (2 : ℤ) ≤ S.card := by exact_mod_cast hcard
  nlinarith

/-- The exact three parts of the degree-`p` coefficient: the trace of the
last coefficient, the norm of the first, and the nonconstant selections.
This is an identity in the actual upper field in all characteristics. -/
theorem coefficient_product_trace_norm_selections
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Module.Finite F E] [IsGalois F E]
    {p : ℕ} (hp : 1 < p) (hcard : Fintype.card Gal(E/F) = p)
    (c : Fin (p + 1) → E) (hc0 : c 0 = 1) :
    (∏ g : Gal(E/F), ∑ i : Fin (p + 1),
      Polynomial.monomial (i : ℕ) (g (c i))).coeff p =
      algebraMap F E (trace F E (c ⟨p, by omega⟩)) +
      algebraMap F E (norm F E (c ⟨1, by omega⟩)) +
      ∑ w : TraceNormSelection Gal(E/F) p, ∏ g : Gal(E/F), g (c (w.val g)) := by
  classical
  let G := Gal(E/F)
  let W := {w : G → Fin (p + 1) // (∑ g, (w g : ℕ)) = p}
  let single (g : G) : W := ⟨fun h => if h = g then ⟨p, by omega⟩ else 0, by simp [apply_ite]⟩
  let allOne : W := ⟨fun _ => ⟨1, by omega⟩, by simp [G, hcard]⟩
  let index := G ⊕ (Unit ⊕ TraceNormSelection G p)
  let chooseSelection : index → W := Sum.elim single
    (Sum.elim (fun _ => allOne) (fun w => ⟨w.val, w.property.1⟩))
  have hinj : Function.Injective chooseSelection := by
    intro u v huv
    have hv := congrArg (fun w : W => w.val) huv
    rcases u with g | (u | u) <;> rcases v with h | (v | v)
    · have hgh : g = h := by
        by_contra hne
        have := congrFun hv g
        have := congrArg Fin.val this
        simp [chooseSelection, single, hne] at this
        omega
      exact congrArg Sum.inl hgh
    · have := congrArg (fun w : W => (w.val g : ℕ)) huv
      simp [chooseSelection, single, allOne] at this
      omega
    · have heq := congrArg (fun w : W => (w.val g : ℕ)) huv
      have := v.property.2.2 g
      simp [chooseSelection, single] at heq
      omega
    · have := congrArg (fun w : W => (w.val h : ℕ)) huv
      simp [chooseSelection, single, allOne] at this
      omega
    · have : u = v := Subsingleton.elim _ _
      subst v
      rfl
    · obtain ⟨g, hg⟩ := v.property.2.1
      have heq := congrArg (fun w : W => (w.val g : ℕ)) huv
      exact False.elim (hg (by simpa [chooseSelection, allOne] using heq.symm))
    · have heq := congrArg (fun w : W => (w.val h : ℕ)) huv
      have := u.property.2.2 h
      simp [chooseSelection, single] at heq
      omega
    · obtain ⟨g, hg⟩ := u.property.2.1
      have heq := congrArg (fun w : W => (w.val g : ℕ)) huv
      exact False.elim (hg (by simpa [chooseSelection, allOne] using heq))
    · exact congrArg (fun w => Sum.inr (Sum.inr w)) (Subtype.ext hv)
  have hsurj : Function.Surjective chooseSelection := by
    rintro ⟨w, hw⟩
    by_cases htop : ∃ g, (w g : ℕ) = p
    · obtain ⟨g, hg⟩ := htop
      refine ⟨Sum.inl g, ?_⟩
      apply Subtype.ext
      funext h
      apply Fin.ext
      simp only [chooseSelection, Sum.elim_inl, single, apply_ite, Fin.val_zero]
      by_cases hne : h = g
      · simp [hne, hg]
      · have herase : ∑ k ∈ Finset.univ.erase g, (w k : ℕ) = 0 := by
          have hsum := Finset.sum_erase_add Finset.univ (fun k => (w k : ℕ))
            (Finset.mem_univ g)
          rw [hw, hg] at hsum
          omega
        have hhmem : h ∈ Finset.univ.erase g := by simp [hne]
        have hle := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ.erase g) =>
          Nat.zero_le (w k : ℕ)) hhmem
        rw [herase] at hle
        simp [hne, Nat.eq_zero_of_le_zero hle]
    · by_cases hone : ∀ g, (w g : ℕ) = 1
      · refine ⟨Sum.inr (Sum.inl ()), ?_⟩
        apply Subtype.ext
        funext g
        apply Fin.ext
        exact (hone g).symm
      · have hsmall : ∀ g, (w g : ℕ) < p := by
          intro g
          have hbound := (w g).isLt
          have hne : (w g : ℕ) ≠ p := by intro h; exact htop ⟨g, h⟩
          omega
        exact ⟨Sum.inr (Sum.inr ⟨w, hw, not_forall.mp hone, hsmall⟩), rfl⟩
  let e : index ≃ W := Equiv.ofBijective chooseSelection ⟨hinj, hsurj⟩
  let term (w : G → Fin (p + 1)) : E := ∏ g : G, g (c (w g))
  have hterm_single (g : G) : term (single g).val = g (c ⟨p, by omega⟩) := by
    dsimp only [term, single]
    rw [Finset.prod_eq_single g]
    · simp
    · intro h hh hne
      simp [hne, hc0]
    · simp
  have hterm_one : term allOne.val = algebraMap F E (norm F E (c ⟨1, by omega⟩)) := by
    exact (Algebra.norm_eq_prod_automorphisms F (c ⟨1, by omega⟩)).symm
  have hsplit := e.sum_comp (fun w : W => term w.val)
  change (∑ j : index, term (chooseSelection j).val) = ∑ w : W, term w.val at hsplit
  simp only [index, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, chooseSelection,
    Fintype.sum_unique, hterm_single, hterm_one] at hsplit
  have hcoeff :
      (∑ w : G → Fin (p + 1), if (∑ g, (w g : ℕ)) = p then term w else 0) =
        ∑ w : W, term w.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by intro w; simp) term
  rw [coefficient_product_selections]
  change (∑ w : G → Fin (p + 1), if (∑ g, (w g : ℕ)) = p then term w else 0) = _
  rw [hcoeff, ← hsplit, trace_eq_sum_automorphisms]
  simp only [term, add_assoc]
  congr 2


/-- The trace-ideal estimate applied after grouping a free Galois sum. -/
theorem freeGaloisSum_mem
    (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Free F E] [Module.Finite F E] [IsGalois F E]
    (X : Type*) [Fintype X] [MulAction Gal(E/F) X]
    (hfree : ∀ x : X, MulAction.stabilizer Gal(E/F) x = ⊥)
    (f : X → E) (heqv : ∀ (g : Gal(E/F)) (x : X), f (g • x) = g (f x))
    (m : ℤ) (hf : ∀ x, f x ∈ lattice E m) :
    ∃ s : F, s ∈ lattice F ((m + Local.differentIdealExponent F E) /
        (ramificationIndex F E : ℤ)) ∧ algebraMap F E s = ∑ x, f x := by
  classical
  letI := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(E/F) X)
  obtain ⟨s, hs, rfl⟩ := freeGaloisSum_eq_sum_trace F E X hfree f heqv
  refine ⟨_, ?_, hs⟩
  apply sum_mem_lattice F
  intro o ho
  have himage : trace F E (f o.out) ∈
      Submodule.map ((trace F E).restrictScalars (ringOfIntegers F))
        ((lattice E m).restrictScalars (ringOfIntegers F)) :=
    Submodule.mem_map.mpr ⟨_, hf o.out, rfl⟩
  rwa [Local.traceIdeal_eq F E] at himage

/-- The coefficient comparison on one lower edge. Both the norm term and
the trace-selection terms are controlled, separately and without division
by the residue characteristic. -/
theorem coefficient_product_congr_trace
    (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E]
    [Module.Free F E] [Module.Finite F E] [IsGalois F E]
    {p : ℕ} (hp : p.Prime) (hcard : Fintype.card Gal(E/F) = p)
    (hres : residueDegree F E = 1)
    (c : Fin (p + 1) → E) (hc0 : c 0 = 1) (m q : ℤ)
    (hc1 : c ⟨1, by have := hp.pos; omega⟩ ∈ lattice E q)
    (hprod : ∀ w : TraceNormSelection Gal(E/F) p,
      (∏ g : Gal(E/F), g (c (w.val g))) ∈ lattice E m)
    (hdepth : q ≤ (m + Local.differentIdealExponent F E) /
      (ramificationIndex F E : ℤ)) :
    ∃ r : F, r ∈ lattice F q ∧
      (∏ g : Gal(E/F), ∑ i : Fin (p + 1),
        Polynomial.monomial (i : ℕ) (g (c i))).coeff p =
        algebraMap F E (trace F E (c ⟨p, by omega⟩) + r) := by
  classical
  letI := selectionAction Gal(E/F) p
  obtain ⟨s, hs, heq⟩ := freeGaloisSum_mem F E (TraceNormSelection Gal(E/F) p)
    (traceNormSelection_stabilizer _ hp hcard)
    (fun w => ∏ g : Gal(E/F), g (c (w.val g)))
    (traceNormSelection_product_equivariant F E p c) m hprod
  have hnorm : norm F E (c ⟨1, by have := hp.pos; omega⟩) ∈ lattice F q := by
    rw [mem_lattice, ord_norm, hres, one_nsmul]
    exact hc1
  refine ⟨norm F E (c ⟨1, by have := hp.pos; omega⟩) + s,
    (lattice F q).add_mem hnorm (lattice_antitone F hdepth hs), ?_⟩
  rw [coefficient_product_trace_norm_selections F E hp.one_lt hcard c hc0, ← heq]
  simp only [map_add, add_assoc]

/-- Arithmetic for the generic case of `O:A:thm:H14`. This condition covers
`p ≥ 5` and also `p = 3` with strictly unequal breaks. -/
theorem traceNorm_generic_depth
    {p : ℕ} (hp : 2 < p) {t t₂ : ℤ} (ht : 1 ≤ t) (htt : t ≤ t₂)
    (hgeneric : 5 ≤ p ∨ t < t₂) :
    1 + t₂ ≤ ((p : ℤ) - 1) * t₂ - t ∧
      1 + t₂ ≤ (2 * ((p : ℤ) - 1) * t₂ - (p : ℤ) * t +
        ((p : ℤ) - 1) * (t + 1)) / (p : ℤ) := by
  have hpZ : (3 : ℤ) ≤ p := by omega
  have hineq : 0 ≤ ((p : ℤ) - 2) * t₂ - t - 1 := by
    rcases hgeneric with hp5 | htt'
    · have hpZ5 : (5 : ℤ) ≤ p := by omega
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ p - 5 by omega) (show 0 ≤ t₂ by omega)]
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ p - 3 by omega) (show 0 ≤ t₂ by omega)]
  constructor
  · nlinarith
  · apply (Int.le_ediv_iff_mul_le (show (0 : ℤ) < p by omega)).2
    nlinarith

/-- Each nonconstant intermediate selection has an entry strictly between
zero and `p-1`. In degree three this is the indispensable `e₁` factor. -/
theorem traceNormSelection_small_entry
    (G : Type*) [Fintype G] {p : ℕ} (hp : 2 < p)
    (w : TraceNormSelection G p) :
    ∃ g, 1 ≤ (w.val g : ℕ) ∧ (w.val g : ℕ) < p - 1 := by
  classical
  let S := Finset.univ.filter (fun g => 0 < (w.val g : ℕ))
  have hcard : 2 ≤ S.card := traceNormSelection_support_card G (by omega) w
  by_contra h
  have hlarge (g : G) (hg : g ∈ S) : p - 1 ≤ (w.val g : ℕ) := by
    have hgpos : 0 < (w.val g : ℕ) := (Finset.mem_filter.mp hg).2
    have : ¬ (1 ≤ (w.val g : ℕ) ∧ (w.val g : ℕ) < p - 1) :=
      fun hh => h ⟨g, hh⟩
    omega
  have hsum : 2 * (p - 1) ≤ p := calc
    2 * (p - 1) ≤ S.card * (p - 1) := Nat.mul_le_mul_right _ hcard
    _ = ∑ _g ∈ S, (p - 1) := by simp
    _ ≤ ∑ g ∈ S, (w.val g : ℕ) := Finset.sum_le_sum hlarge
    _ ≤ ∑ g, (w.val g : ℕ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (by intro g hg hnot; exact Nat.zero_le _)
    _ = p := w.property.1
  omega

/-- The sparse Artin--Schreier polynomial has no extra degree-`p`
coefficient after the lower norm. -/
theorem coefficient_product_sparse
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Module.Finite F E] [IsGalois F E]
    {p : ℕ} (hp : 2 < p) (hcard : Fintype.card Gal(E/F) = p)
    (c : Fin (p + 1) → E) (hc0 : c 0 = 1)
    (hc : ∀ i : Fin (p + 1), 1 ≤ (i : ℕ) → (i : ℕ) < p - 1 → c i = 0) :
    (∏ g : Gal(E/F), ∑ i : Fin (p + 1),
      Polynomial.monomial (i : ℕ) (g (c i))).coeff p =
      algebraMap F E (trace F E (c ⟨p, by omega⟩)) := by
  classical
  rw [coefficient_product_trace_norm_selections F E (by omega) hcard c hc0,
    hc ⟨1, by omega⟩ (by simp) (by simp; omega)]
  have hsum : (∑ w : TraceNormSelection Gal(E/F) p,
      ∏ g : Gal(E/F), g (c (w.val g))) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    obtain ⟨g, hgpos, hgsmall⟩ := traceNormSelection_small_entry _ hp w
    apply Finset.prod_eq_zero (Finset.mem_univ g)
    rw [hc (w.val g) hgpos hgsmall, map_zero]
  simp only [hsum, norm_apply, Algebra.norm_zero, map_zero, add_zero]

/-- The remaining cubic selections acquire the extra depth from their
actual `e₁` factor; no generic strict inequality between breaks is used. -/
theorem cubic_selection_product_mem
    (F E : Type*) [Field F] [Field E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [Module.Finite F E]
    (t : ℤ) (ht : 0 ≤ t) (c : Fin 4 → E) (hc0 : c 0 = 1)
    (hc1 : c 1 ∈ lattice E (t + 1)) (hc2 : c 2 ∈ lattice E 0)
    (w : TraceNormSelection Gal(E/F) 3) :
    (∏ g : Gal(E/F), g (c (w.val g))) ∈ lattice E (t + 1) := by
  classical
  obtain ⟨g, hgpos, hgsmall⟩ := traceNormSelection_small_entry _ (by omega : 2 < 3) w
  have hgval : w.val g = 1 := by apply Fin.ext; simp only [Fin.val_one]; omega
  have hcoeff (h : Gal(E/F)) : c (w.val h) ∈ lattice E 0 := by
    have hsmall := w.property.2.2 h
    have hcases : w.val h = 0 ∨ w.val h = 1 ∨ w.val h = 2 := by
      have hval : (w.val h : ℕ) = 0 ∨ (w.val h : ℕ) = 1 ∨ (w.val h : ℕ) = 2 := by omega
      rcases hval with h0 | h1 | h2
      · exact Or.inl (Fin.ext h0)
      · exact Or.inr (Or.inl (Fin.ext h1))
      · exact Or.inr (Or.inr (Fin.ext h2))
    rcases hcases with h0 | h1 | h2
    · simp [h0, hc0]
    · rw [h1]; exact lattice_antitone E (by omega) hc1
    · rw [h2]; exact hc2
  have hprod := product_mem_lattice E Finset.univ
    (fun h : Gal(E/F) => h (c (w.val h)))
    (fun h => if h = g then t + 1 else 0) (by
      intro h hh
      rw [mem_lattice, ord_galoisConjugate]
      by_cases heq : h = g
      · simpa only [heq, hgval, if_true] using (mem_lattice E).mp hc1
      · simpa only [if_neg heq] using (mem_lattice E).mp (hcoeff h))
  simpa using hprod

open Polynomial

/-- Homogeneity of the actual elementary symmetric coefficient. -/
theorem elementarySymmetric_base_mul
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    [Module.Free E L] [Module.Finite E L] [IsGalois E L] [Infinite E]
    (z : E) (x : L) (i : ℕ) :
    elementarySymmetric E L i (algebraMap E L z * x) =
      z ^ i * elementarySymmetric E L i x := by
  apply (algebraMap E L).injective
  rw [map_mul, map_pow, algebraMap_elementarySymmetric_eq_esymm_galois,
    algebraMap_elementarySymmetric_eq_esymm_galois]
  have h := Multiset.pow_smul_esymm (algebraMap E L z) i (galoisConjugates E L x)
  simpa [galoisConjugates, galoisConjugate, Multiset.map_map,
    Function.comp_def, smul_eq_mul, map_mul] using h.symm

/-- Generating polynomial for the actual norm of `1 + Z*x`. -/
def normGeneratingPolynomial
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    [Module.Free E L] [Module.Finite E L] (p : ℕ) (x : L) : E[X] :=
  ∑ i : Fin (p + 1), Polynomial.monomial (i : ℕ) (elementarySymmetric E L i x)

theorem normGeneratingPolynomial_eval
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    [Module.Free E L] [Module.Finite E L] [IsGalois E L] [Infinite E]
    (p : ℕ) (hdegree : Module.finrank E L = p) (x : L) (z : E) :
    (normGeneratingPolynomial E L p x).eval z = norm E L (1 + algebraMap E L z * x) := by
  rw [normGeneratingPolynomial, Polynomial.eval_finsetSum,
    norm_one_add_eq_sum_elementarySymmetric, hdegree]
  simp_rw [Polynomial.eval_monomial, elementarySymmetric_base_mul]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

theorem polynomialNorm_eval
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Module.Free F E] [Module.Finite F E] [IsGalois F E]
    (Q : E[X]) (z : F) :
    (∏ g : Gal(E/F), Q.map g.toRingHom).eval (algebraMap F E z) =
      algebraMap F E (norm F E (Q.eval (algebraMap F E z))) := by
  rw [Polynomial.eval_prod, norm_apply, Algebra.norm_eq_prod_automorphisms]
  apply Finset.prod_congr rfl
  intro g hg
  have h := Polynomial.eval_map_apply g.toRingHom (algebraMap F E z) (p := Q)
  change (Q.map g.toRingHom).eval (g (algebraMap F E z)) =
    g (Q.eval (algebraMap F E z)) at h
  rwa [g.commutes] at h

/-- Transitivity identifies the two iterated norm polynomials, before any
coefficient is discarded. The element is the same actual representative
in both towers. -/
theorem iteratedNormPolynomial_eq
    (F E₁ E₂ L : Type*) [Field F] [Field E₁] [Field E₂] [Field L]
    [Algebra F E₁] [Algebra F E₂] [Algebra F L]
    [Algebra E₁ L] [Algebra E₂ L]
    [IsScalarTower F E₁ L] [IsScalarTower F E₂ L]
    [Module.Free F E₁] [Module.Finite F E₁] [IsGalois F E₁]
    [Module.Free F E₂] [Module.Finite F E₂] [IsGalois F E₂]
    [Module.Free E₁ L] [Module.Finite E₁ L] [IsGalois E₁ L]
    [Module.Free E₂ L] [Module.Finite E₂ L] [IsGalois E₂ L]
    [Infinite F] [Infinite E₁] [Infinite E₂]
    (p : ℕ) (hdegree₁ : Module.finrank E₁ L = p)
    (hdegree₂ : Module.finrank E₂ L = p) (x : L) :
    (∏ g : Gal(E₁/F), (normGeneratingPolynomial E₁ L p x).map g.toRingHom).map
        (algebraMap E₁ L) =
      (∏ g : Gal(E₂/F), (normGeneratingPolynomial E₂ L p x).map g.toRingHom).map
        (algebraMap E₂ L) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (algebraMap F L).injective).mono
  rintro y ⟨z, rfl⟩
  change Polynomial.eval (algebraMap F L z) _ = Polynomial.eval (algebraMap F L z) _
  have h₁ : algebraMap F L z = algebraMap E₁ L (algebraMap F E₁ z) :=
    IsScalarTower.algebraMap_apply F E₁ L z
  have h₂ : algebraMap F L z = algebraMap E₂ L (algebraMap F E₂ z) :=
    IsScalarTower.algebraMap_apply F E₂ L z
  conv_lhs =>
    rw [h₁, Polynomial.eval_map_apply, polynomialNorm_eval,
      normGeneratingPolynomial_eval E₁ L p hdegree₁]
  conv_rhs =>
    rw [h₂, Polynomial.eval_map_apply, polynomialNorm_eval,
      normGeneratingPolynomial_eval E₂ L p hdegree₂]
  simp only [← IsScalarTower.algebraMap_apply, norm_trans]

/-- Minimal polynomial of the exact Artin--Schreier power-basis generator. -/
theorem artinSchreier_minpoly
    {E L : Type*} [Field E] [Field L] [Algebra E L]
    (pb : PowerBasis E L) {p : ℕ} (hp : 2 < p) (hdim : pb.dim = p)
    (a : E) (hroot : pb.gen ^ p - pb.gen = algebraMap E L a) :
    minpoly E pb.gen = X ^ p - X - C a := by
  let P : E[X] := X ^ p - (X + C a)
  have hlow : (X + C a : E[X]).degree < p := by
    apply (degree_add_le _ _).trans_lt
    apply max_lt
    · simpa only [degree_X] using (show (1 : WithBot ℕ) < p by exact_mod_cast (show 1 < p by omega))
    · exact degree_C_le.trans_lt (by exact_mod_cast (show 0 < p by omega))
  have hlow' : (X + C a : E[X]).degree < (X ^ p : E[X]).degree := by
    simpa only [degree_X_pow] using hlow
  have hmonic : P.Monic := (monic_X_pow p).sub_of_left hlow'
  have hdegree : P.natDegree = p := by
    apply natDegree_eq_of_degree_eq_some
    dsimp only [P]
    rw [degree_sub_eq_left_of_degree_lt hlow', degree_X_pow]
  have heval : Polynomial.aeval pb.gen P = 0 := by
    simp only [P, map_sub, map_add, map_pow, aeval_X, aeval_C]
    linear_combination hroot
  have heq : P = minpoly E pb.gen := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic pb.isIntegral_gen) hmonic
    · exact minpoly.dvd E pb.gen heval
    · rw [hdegree, pb.natDegree_minpoly, hdim]
  rw [← heq]
  dsimp [P]
  ring

/-- The actual upper norm is the exact coefficient `a`, in both field
characteristics. -/
theorem artinSchreier_norm
    {E L : Type*} [Field E] [Field L] [Algebra E L]
    [Module.Free E L] [Module.Finite E L]
    (pb : PowerBasis E L) {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hdim : pb.dim = p)
    (a : E) (hroot : pb.gen ^ p - pb.gen = algebraMap E L a) :
    norm E L pb.gen = a := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  rw [norm_apply, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,
    artinSchreier_minpoly pb hp2 hdim a hroot, hdim, hodd.neg_one_pow]
  simp [Polynomial.coeff_X_pow, Ne.symm hp.ne_zero]

/-- The low intermediate coefficients of the exact upper polynomial
vanish. Newton's identity divides only by integers strictly below `p`. -/
theorem artinSchreier_elementarySymmetric_low
    {E L : Type*} [Field E] [Field L] [Algebra E L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Module.Free E L] [Module.Finite E L] [IsGalois E L]
    (pb : PowerBasis E L) {p : ℕ} (hp : 2 < p) (hdim : pb.dim = p)
    (hchar : residueCharacteristic E = p)
    (a : E) (hroot : pb.gen ^ p - pb.gen = algebraMap E L a)
    (i : ℕ) (hi : 1 ≤ i) (hip : i < p - 1) :
    elementarySymmetric E L i pb.gen = 0 := by
  have hiunit := ord_natCast_eq_zero_of_lt_residueCharacteristic E hi
    (show i < residueCharacteristic E by rw [hchar]; omega)
  have hinz : (i : E) ≠ 0 := by intro hz; simp [hz] at hiunit
  have hnewton := elementarySymmetric_newton_identity E L pb.gen i
  have hsum : (∑ b ∈ Finset.HasAntidiagonal.antidiagonal i with b.1 < i,
      (-1 : E) ^ b.1 * elementarySymmetric E L b.1 pb.gen *
        galoisPowerSum E L b.2 pb.gen) = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    have hmem := (Finset.mem_filter.mp hb)
    have hsum : b.1 + b.2 = i := by simpa using hmem.1
    have hmoment := artinSchreier_powerTrace_below pb hp hdim a hroot b.2
      (by omega) (by omega)
    have hzero : galoisPowerSum E L b.2 pb.gen = 0 := by
      simpa only [galoisPowerSum, trace_apply, if_neg (show b.2 ≠ p - 1 by omega)] using hmoment
    rw [hzero, mul_zero]
  rw [hsum, mul_zero] at hnewton
  exact (mul_eq_zero.mp hnewton).resolve_left hinz


/-- `O:A:thm:H14` on two actual finite Galois towers, retaining the given
power-basis generator and its exact Artin--Schreier coefficient. The only
coordinate estimate supplied here is the accepted intermediate symmetric
bound; the norm comparison and the cubic improvement are proved below. -/
theorem traceNorm_of_powerBasis
    (F E₁ E₂ L : Type*) [Field F] [Field E₁] [Field E₂] [Field L]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E₁] [TopologicalSpace E₁] [IsNonarchimedeanLocalField E₁]
    [ValuativeRel E₂] [TopologicalSpace E₂] [IsNonarchimedeanLocalField E₂]
    [Algebra F E₁] [Algebra F E₂] [Algebra F L]
    [ValuativeExtension F E₁] [ValuativeExtension F E₂]
    [Algebra E₁ L] [Algebra E₂ L]
    [IsScalarTower F E₁ L] [IsScalarTower F E₂ L]
    [Module.Free F E₁] [Module.Finite F E₁] [IsGalois F E₁]
    [Module.Free F E₂] [Module.Finite F E₂] [IsGalois F E₂]
    [Module.Free E₁ L] [Module.Finite E₁ L] [IsGalois E₁ L]
    [Module.Free E₂ L] [Module.Finite E₂ L] [IsGalois E₂ L]
    [Module.Free F L] [Module.Finite F L]
    [Infinite F] [Infinite E₁] [Infinite E₂]
    {p : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (hcard₁ : Fintype.card Gal(E₁/F) = p) (hcard₂ : Fintype.card Gal(E₂/F) = p)
    (hdegree₁ : Module.finrank E₁ L = p)
    (hres₁ : residueDegree F E₁ = 1) (hram₁ : ramificationIndex F E₁ = p)
    (hchar₂ : residueCharacteristic E₂ = p)
    (t t₂ : ℤ) (ht : 1 ≤ t) (htt : t ≤ t₂)
    (hdiff₁ : Local.differentIdealExponent F E₁ = ((p : ℤ) - 1) * (t + 1))
    (pb : PowerBasis E₂ L) (hdim : pb.dim = p)
    (a : E₂) (hroot : pb.gen ^ p - pb.gen = algebraMap E₂ L a)
    (hei : ∀ i : ℕ, 1 ≤ i → i < p →
      elementarySymmetric E₁ L i pb.gen ∈ lattice E₁ (((p : ℤ) - 1) * t₂ - (i : ℤ) * t)) :
    trace F E₁ (norm E₁ L pb.gen) - trace F E₂ a ∈ lattice F (1 + t₂) := by
  classical
  let c₁ : Fin (p + 1) → E₁ := fun i => elementarySymmetric E₁ L i pb.gen
  let c₂ : Fin (p + 1) → E₂ := fun i => elementarySymmetric E₂ L i pb.gen
  have hc₁zero : c₁ 0 = 1 := elementarySymmetric_zero _ _ _
  have hc₂zero : c₂ 0 = 1 := elementarySymmetric_zero _ _ _
  have hdegree₂ : Module.finrank E₂ L = p := pb.finrank.trans hdim
  have htrace₁ : trace F E₁ (c₁ ⟨1, by omega⟩) = 0 := by
    have hmoment := artinSchreier_powerTrace_below pb hp2 hdim a hroot 1 (by omega) (by omega)
    have htr₂ : trace E₂ L pb.gen = 0 := by simpa [show 1 ≠ p - 1 by omega] using hmoment
    change trace F E₁ (elementarySymmetric E₁ L 1 pb.gen) = 0
    rw [elementarySymmetric_one, trace_trans, ← trace_trans F E₂ L, htr₂, map_zero]
  have hleft : ∃ r : F, r ∈ lattice F (1 + t₂) ∧
      (∏ g : Gal(E₁/F), ∑ i : Fin (p + 1),
        Polynomial.monomial (i : ℕ) (g (c₁ i))).coeff p =
        algebraMap F E₁ (trace F E₁ (c₁ ⟨p, by omega⟩) + r) := by
    by_cases hgeneric : 5 ≤ p ∨ t < t₂
    · obtain ⟨hfirst, hother⟩ := traceNorm_generic_depth hp2 ht htt hgeneric
      apply coefficient_product_congr_trace F E₁ hp hcard₁ hres₁ c₁ hc₁zero
        (2 * ((p : ℤ) - 1) * t₂ - (p : ℤ) * t) (1 + t₂)
      · exact lattice_antitone E₁ hfirst (by
          simpa only [c₁, Nat.cast_one, one_mul] using hei 1 (by omega) (by omega))
      · intro w
        convert traceNormSelection_product_mem F E₁ hp.pos
          (((p : ℤ) - 1) * t₂) t (mul_nonneg (by omega) (by omega)) c₁ hc₁zero
          (fun i hi hip => hei i hi hip) w using 1
        congr 1
        ring
      · simpa only [hdiff₁, hram₁] using hother
    · have hp4 : p ≠ 4 := by
        intro h
        have hprime4 : Nat.Prime 4 := h ▸ hp
        norm_num at hprime4
      have hp3 : p = 3 := by omega
      have htt' : t₂ = t := by omega
      subst hp3
      subst t₂
      have he1 : c₁ 1 ∈ lattice E₁ (t + 1) :=
        cubic_trace_zero_depth F E₁ hres₁ hram₁ t (by simpa using hdiff₁)
          (by
            convert hei 1 (by omega) (by omega) using 1 <;> norm_num [c₁]
            ring) htrace₁
      apply coefficient_product_congr_trace F E₁ hp hcard₁ hres₁ c₁ hc₁zero
        (t + 1) (1 + t)
      · convert he1 using 1 <;> norm_num [c₁, add_comm]
      · intro w
        exact cubic_selection_product_mem F E₁ t (by omega) c₁ hc₁zero he1
          (by simpa [c₁] using hei 2 (by omega) (by omega)) w
      · rw [hdiff₁, hram₁]
        norm_num
        omega
  obtain ⟨r, hr, hleft⟩ := hleft
  have hright := coefficient_product_sparse F E₂ hp2 hcard₂ c₂ hc₂zero
    (fun i hi hip => artinSchreier_elementarySymmetric_low pb hp2 hdim hchar₂ a hroot i hi hip)
  have hpoly := iteratedNormPolynomial_eq F E₁ E₂ L p hdegree₁ hdegree₂ pb.gen
  have hcoeff := congrArg (fun Q : L[X] => Q.coeff p) hpoly
  simp only [Polynomial.coeff_map, normGeneratingPolynomial, Polynomial.map_sum,
    Polynomial.map_monomial] at hcoeff
  change algebraMap E₁ L
    ((∏ g : Gal(E₁/F), ∑ i : Fin (p + 1), Polynomial.monomial (i : ℕ) (g (c₁ i))).coeff p) =
      algebraMap E₂ L
        ((∏ g : Gal(E₂/F), ∑ i : Fin (p + 1), Polynomial.monomial (i : ℕ) (g (c₂ i))).coeff p) at hcoeff
  rw [hleft, hright, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at hcoeff
  have heq := (algebraMap F L).injective hcoeff
  have hlast₁ : c₁ ⟨p, by omega⟩ = norm E₁ L pb.gen := by
    dsimp only [c₁]
    rw [← hdegree₁, elementarySymmetric_finrank]
  have hlast₂ : c₂ ⟨p, by omega⟩ = a := by
    dsimp only [c₂]
    rw [← hdegree₂, elementarySymmetric_finrank]
    exact artinSchreier_norm pb hp hp2 hdim a hroot
  rw [hlast₁, hlast₂] at heq
  have hsub : trace F E₁ (norm E₁ L pb.gen) - trace F E₂ a = -r := by
    linear_combination heq
  rw [hsub]
  exact (lattice F (1 + t₂)).neg_mem hr

private theorem localField_infinite
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] : Infinite E := by
  let f : ℤ → E := fun n => (exists_ord_eq E n).choose
  apply Infinite.of_injective f
  intro m n h
  have hm := (exists_ord_eq E m).choose_spec
  have hn := (exists_ord_eq E n).choose_spec
  exact WithTop.coe_injective (hm.symm.trans ((congrArg (ord E) h).trans hn))

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K]
variable [Module.Free F K] [Module.Finite F K] [IsGalois F K]

private theorem intermediate_residueDegree_lower_one
    (hres : residueDegree F K = 1) (E : IntermediateField F K) :
    letI := Basic.intermediateFieldValuativeRel E
    letI := Basic.intermediateFieldTopology E
    letI := Basic.intermediateField_localField E
    letI := Basic.intermediateField_lowerValuativeExtension E
    letI := Basic.intermediateField_upperValuativeExtension E
    residueDegree F E = 1 := by
  letI := Basic.intermediateFieldValuativeRel E
  letI := Basic.intermediateFieldTopology E
  letI := Basic.intermediateField_localField E
  letI := Basic.intermediateField_lowerValuativeExtension E
  letI := Basic.intermediateField_upperValuativeExtension E
  letI : IsScalarTower (ringOfIntegers F) (ringOfIntegers E) (ringOfIntegers K) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap F K (x : F) = algebraMap E K (algebraMap F E (x : F))
      rw [← IsScalarTower.algebraMap_apply F E K])
  letI : IsLocalHom (algebraMap (ringOfIntegers F) (ringOfIntegers E)) := inferInstance
  letI : IsLocalHom (algebraMap (ringOfIntegers E) (ringOfIntegers K)) := inferInstance
  have hmul : residueDegree F E * residueDegree E K = residueDegree F K := by
    rw [residueDegree_eq_finrank_residueField, residueDegree_eq_finrank_residueField,
      residueDegree_eq_finrank_residueField]
    exact Module.finrank_mul_finrank (ResidueField F) (ResidueField E) (ResidueField K)
  rw [hres] at hmul
  exact (mul_eq_one.mp hmul).1

/-- **Paper Theorem 7.5 (`O:A:thm:H14`).** For the actual odd totally ramified
Galois diamond and the exact coordinate supplied by `twistedEstimates`,
`T₁(N₁ Δ) - T₂(a)` belongs to the integer-depth lattice `𝔭_F^(1+t₂)`.

The coordinate is universally quantified: applying this theorem preserves
its exact representative. Its root, generation and symmetric-bound inputs
are all supplied by the accepted `twistedEstimates` constructor. In particular,
no trace--norm congruence or exceptional-case improvement is assumed. -/
theorem traceNorm {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (D : OddTotalBreakData (F := F) (K := K) hp hG) :
    let B₁ := D.B₁
    let B₂ := D.B₂
    letI := Basic.intermediateFieldValuativeRel B₁
    letI := Basic.intermediateFieldTopology B₁
    letI := Basic.intermediateField_localField B₁
    letI := Basic.intermediateFieldValuativeRel B₂
    letI := Basic.intermediateFieldTopology B₂
    letI := Basic.intermediateField_localField B₂
    ∀ (Delta : K) (a : B₂),
      Delta ^ p - Delta = algebraMap B₂ K a →
      Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ →
      (∀ i : ℕ, 1 ≤ i → i < p →
        ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) ≤
          ord B₁ (elementarySymmetric B₁ K i Delta)) →
      trace F B₁ (norm B₁ K Delta) - trace F B₂ a ∈ lattice F (1 + (D.t₂ : ℤ)) := by
  dsimp only [OddTotalBreakData.B₁, OddTotalBreakData.B₂]
  let B₁ := IntermediateField.fixedField D.H₁
  let B₂ := IntermediateField.fixedField D.H₂
  letI := Basic.intermediateFieldValuativeRel B₁
  letI := Basic.intermediateFieldTopology B₁
  letI := Basic.intermediateFieldValuativeRel B₂
  letI := Basic.intermediateFieldTopology B₂
  obtain ⟨hLocal₁, hFreeF₁, hFiniteF₁, hFree₁K, hFinite₁K, hScalar₁,
      hValF₁, hVal₁K, _htotal₁, hdegreeLower₁, hdegreeUpper₁, hcycF₁, hcyc₁K⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁
  letI := hLocal₁
  letI := hFreeF₁
  letI := hFiniteF₁
  letI := hFree₁K
  letI := hFinite₁K
  letI := hScalar₁
  letI := hValF₁
  letI := hVal₁K
  letI : IsGalois F B₁ := hcycF₁.1
  letI : IsGalois B₁ K := hcyc₁K.1
  letI : PrimeCyclicExtension F B₁ := PrimeCyclicExtension.ofCyclicPrimeExtension F B₁ hcycF₁
  obtain ⟨hLocal₂, hFreeF₂, hFiniteF₂, hFree₂K, hFinite₂K, hScalar₂,
      hValF₂, hVal₂K, _htotal₂, hdegreeLower₂, hdegreeUpper₂, hcycF₂, hcyc₂K⟩ :=
    Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂
  letI := hLocal₂
  letI := hFreeF₂
  letI := hFiniteF₂
  letI := hFree₂K
  letI := hFinite₂K
  letI := hScalar₂
  letI := hValF₂
  letI := hVal₂K
  letI : IsGalois F B₂ := hcycF₂.1
  letI : IsGalois B₂ K := hcyc₂K.1
  letI : Infinite F := localField_infinite F
  letI : Infinite B₁ := localField_infinite B₁
  letI : Infinite B₂ := localField_infinite B₂
  have hresF₁ : residueDegree F B₁ = 1 := intermediate_residueDegree_lower_one hres B₁
  have hramF₁ : ramificationIndex F B₁ = p := by
    have hfund := finrank_eq_ramificationIndex_mul_residueDegree F B₁
    rw [hresF₁, mul_one, hdegreeLower₁] at hfund
    exact hfund.symm
  have hcard₁ : Fintype.card Gal(B₁/F) = p := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hdegreeLower₁]
  have hcard₂ : Fintype.card Gal(B₂/F) = p := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hdegreeLower₂]
  have hchar₂ : residueCharacteristic B₂ = p :=
    (residueCharacteristic_extension_eq F B₂).trans hchar
  have hbreak₁ : PrimeCyclicExtension.IsLowerBreak F B₁ D.t := by
    simpa only [B₁, Ramification.IntermediateBreakPair] using D.B₁_breaks.1
  have hdiff₁ : Local.differentIdealExponent F B₁ = ((p : ℤ) - 1) * ((D.t : ℤ) + 1) := by
    rw [Local.differentIdealExponent_eq_fml F B₁ hresF₁]
    obtain ⟨pi, hpi, hgen⟩ :=
      exists_uniformizer_and_algebra_adjoin_eq_top_of_residueDegree_eq_one F B₁ hresF₁
    rw [differentExponent_eq F B₁ hbreak₁ pi hpi hgen, hdegreeLower₁]
    push_cast [Nat.cast_sub hp.one_le]
    rfl
  intro Delta a hroot hgen hei
  let pb : PowerBasis B₂ K :=
    PowerBasis.ofAdjoinEqTop (IsAlgebraic.of_finite B₂ Delta).isIntegral hgen
  have hpbgen : pb.gen = Delta := PowerBasis.ofAdjoinEqTop_gen _ _
  have hpbdim : pb.dim = p := by rw [← pb.finrank]; exact hdegreeUpper₂
  have h := traceNorm_of_powerBasis F B₁ B₂ K hp D.odd_prime hcard₁ hcard₂ hdegreeUpper₁
    hresF₁ hramF₁ hchar₂ D.t D.t₂ (by exact_mod_cast Nat.succ_le_of_lt D.t_pos) (by exact_mod_cast D.t_le_t₂)
    hdiff₁ pb hpbdim a (by simpa only [hpbgen] using hroot)
    (by intro i hi hip; simpa only [hpbgen, mem_lattice] using hei i hi hip)
  simpa only [hpbgen] using h

/-- A coordinate satisfying the trace--norm congruence is constructed from
the genuine odd totally ramified diamond. The exact root, its two orders,
its generating property and its coefficient bounds are retained. -/
theorem exists_traceNorm_coordinate {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (D : OddTotalBreakData (F := F) (K := K) hp hG) :
    let B₁ := D.B₁
    let B₂ := D.B₂
    letI := Basic.intermediateFieldValuativeRel B₁
    letI := Basic.intermediateFieldTopology B₁
    letI := Basic.intermediateField_localField B₁
    letI := Basic.intermediateFieldValuativeRel B₂
    letI := Basic.intermediateFieldTopology B₂
    letI := Basic.intermediateField_localField B₂
    ∃ (Delta : K) (a : B₂),
      Delta ^ p - Delta = algebraMap B₂ K a ∧
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ¬ p ∣ D.t ∧ Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ ∧
      (∀ i : ℕ, 1 ≤ i → i < p →
        ((((p : ℤ) - 1) * D.t₂ - (i : ℤ) * D.t : ℤ) : WithTop ℤ) ≤
          ord B₁ (elementarySymmetric B₁ K i Delta)) ∧
      trace F B₁ (norm B₁ K Delta) - trace F B₂ a ∈ lattice F (1 + (D.t₂ : ℤ)) := by
  letI := Basic.intermediateFieldValuativeRel D.B₁
  letI := Basic.intermediateFieldTopology D.B₁
  letI := Basic.intermediateField_localField D.B₁
  letI := Basic.intermediateFieldValuativeRel D.B₂
  letI := Basic.intermediateFieldTopology D.B₂
  letI := Basic.intermediateField_localField D.B₂
  obtain ⟨Delta, a, hroot, hDelta, ha, hprime, hgen, _hcoeff, _htrace, _hsym, hei, _hs⟩ :=
    twistedEstimates hp hG hres hchar D
  exact ⟨Delta, a, hroot, hDelta, ha, hprime, hgen, hei,
    traceNorm hp hG hres hchar D Delta a hroot hgen hei⟩

end
end LanglandsSecondMainLemma.Odd.Total
