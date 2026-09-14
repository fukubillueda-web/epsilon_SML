import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Total.ProjectionTransfer
import LanglandsSecondMainLemma.Odd.Parameters.FourFactors

/-!
# Odd / Transition / Projection

Paper Lemma 9.24 (`O:T:projection`), with the stationary setup at
`O:T:coefficient` and the two bounds in `O:T:projectdepth`.

The projection is the zeroth coordinate of the actual Artin--Schreier
power basis. Coefficient extraction constructs this basis from the odd
totally ramified diamond. The first depth hypothesis puts every
nonconstant term in the required lattice; the second, together with that
proved congruence, supplies both inputs to `Total.projectionTransfer`.

All ideal exponents are integers and orders take values in `WithTop ℤ`.
The norm congruence uses the upper norm to `B₁` and the lower norm to `F`,
embedded in `B₁`. No character or stationary-phase identity is needed for
this field-theoretic step.
-/

namespace LanglandsSecondMainLemma.Odd.Transition

noncomputable section

open LanglandsFirstMainLemma
open scoped BigOperators

section PowerCoordinates

variable {E L : Type*} [Field E] [Field L] [Algebra E L]

/-- The literal constant coefficient in the expansion in powers of
`pb.gen`. Its codomain is the coefficient field. -/
def constantProjection (pb : PowerBasis E L) : L →ₗ[E] E :=
  pb.basis.coord ⟨0, pb.dim_pos⟩

@[simp]
theorem constantProjection_apply (pb : PowerBasis E L) (z : L) :
    constantProjection pb z = pb.basis.repr z ⟨0, pb.dim_pos⟩ := rfl

/-- Constants are fixed by constant projection. -/
@[simp]
theorem constantProjection_algebraMap (pb : PowerBasis E L) (x : E) :
    constantProjection pb (algebraMap E L x) = x := by
  have hzero : pb.basis ⟨0, pb.dim_pos⟩ = 1 := by
    rw [pb.basis_eq_pow, pow_zero]
  rw [show algebraMap E L x = x • pb.basis ⟨0, pb.dim_pos⟩ by
    rw [hzero, Algebra.smul_def, mul_one]]
  rw [map_smul]
  change x * pb.basis.repr (pb.basis ⟨0, pb.dim_pos⟩) ⟨0, pb.dim_pos⟩ = x
  rw [Module.Basis.repr_self_apply, if_pos rfl, mul_one]

private theorem powerBasis_expansion (pb : PowerBasis E L)
    {p : ℕ} (hdim : pb.dim = p) (z : L) :
    z = ∑ i : Fin p,
      algebraMap E L (pb.basis.repr z (Fin.cast hdim.symm i)) *
        pb.gen ^ (i : ℕ) := by
  let e : Fin p ≃ Fin pb.dim := (Fin.castOrderIso hdim.symm).toEquiv
  have hs := pb.basis.sum_repr z
  rw [← e.sum_comp] at hs
  refine hs.symm.trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  rw [pb.basis_eq_pow, Algebra.smul_def]
  rfl

end PowerCoordinates

open private map_lattice residueDegree_projectionTower from
  LanglandsSecondMainLemma.Odd.Total.ProjectionTransfer

/-- The coefficient bound `v₂(Yᵢ) ≥ q+i*t` places the nonconstant
tail in depth `p*q+(p-1)*t`. This is the first congruence argument of
`O:T:projection`, before inserting the numerical bound on `p*q`. -/
private theorem constant_tail_mem
    (E L : Type*) [Field E] [Field L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra E L] [ValuativeExtension E L]
    {p t : ℕ} (hp : 0 < p) (ht : 0 ≤ (t : ℤ))
    (hram : ramificationIndex E L = p)
    {Delta : L} (hDelta : ord L Delta = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (Y : Fin p → E) (q : ℤ) {z : L}
    (hexp : z = ∑ i : Fin p, algebraMap E L (Y i) * Delta ^ (i : ℕ))
    (hcoeff : ∀ i : Fin p, Y i ∈ lattice E (q + (i : ℕ) * (t : ℤ))) :
    z - algebraMap E L (Y ⟨0, hp⟩) ∈
      lattice L ((p : ℤ) * q + ((p : ℤ) - 1) * t) := by
  classical
  let i₀ : Fin p := ⟨0, hp⟩
  have htail : z - algebraMap E L (Y i₀) =
      ∑ i ∈ Finset.univ \ {i₀}, algebraMap E L (Y i) * Delta ^ (i : ℕ) := by
    rw [hexp, Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i₀)]
    simp [i₀]
  rw [htail]
  apply sum_mem_lattice L
  intro i hi
  have hi0 : i ≠ i₀ := by simpa using hi
  have hi1 : (1 : ℤ) ≤ (i : ℕ) := by
    have : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
    omega
  have hd : Delta ^ (i : ℕ) ∈ lattice L (-((i : ℕ) * (t : ℤ))) := by
    simp only [mem_lattice, ord_pow, hDelta, ← WithTop.coe_nsmul,
      nsmul_eq_mul, mul_neg, le_refl]
  have hterm := mul_mem_lattice L (map_lattice E L hram (hcoeff i)) hd
  apply lattice_antitone L _ hterm
  have hnonneg := mul_nonneg (show (0 : ℤ) ≤ p - 1 by omega) ht
  have hgain := mul_le_mul_of_nonneg_right hi1 hnonneg
  nlinarith

section Diamond

variable {F K : Type*} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]

attribute [local instance] Basic.intermediateFieldValuativeRel Basic.intermediateFieldTopology
  Basic.intermediateField_localField Basic.intermediateField_lowerValuativeExtension
  Basic.intermediateField_upperValuativeExtension

/-- **Constant projection and its norm, Paper Lemma 9.24.**

The power basis, its Artin--Schreier equation and its coefficient estimate
are constructed from the genuine diamond. The output retains the same
basis for all scalar products `x*w`, so `constantProjection pb` is a
single linear projection into `B₂`, not a separately chosen congruent
representative for each input. Both hypotheses of `O:T:projectdepth`
remain explicit. The order equality also covers zero, whose order is
infinite. -/
theorem projection {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1) (hchar : residueCharacteristic F = p)
    (D : Total.OddTotalBreakData (F := F) (K := K) hp hG) :
    ∃ (pb : PowerBasis D.B₂ K) (a : D.B₂),
      pb.dim = p ∧
      pb.gen ^ p - pb.gen = algebraMap D.B₂ K a ∧
      ord K pb.gen = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ord D.B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ¬ p ∣ D.t ∧
      (∀ (w : D.B₁) (i : Fin pb.dim),
        ord D.B₁ w + ((((i : ℕ) * D.t : ℕ) : ℤ) : WithTop ℤ) ≤
          ord D.B₂ (pb.basis.repr (algebraMap D.B₁ K w) i)) ∧
      ∀ (x : D.B₂) (w : D.B₁),
        let z := algebraMap D.B₂ K x * algebraMap D.B₁ K w
        let y := constantProjection pb z
        (((1 + D.tPrime : ℤ) : WithTop ℤ) ≤ ord K z) →
        (((1 + D.t₂ + ((p : ℤ) - 3) * D.t : ℤ) : WithTop ℤ) ≤ ord K z) →
        z - algebraMap D.B₂ K y ∈ lattice K (1 + (p : ℤ) * D.t₂) ∧
        norm D.B₁ K z - algebraMap F D.B₁ (norm F D.B₂ y) ∈
          lattice D.B₁ (1 + (p : ℤ) * D.t₂) ∧
        ord K (algebraMap D.B₂ K y) = ord K z := by
  classical
  let B₁ := D.B₁
  let B₂ := D.B₂
  have hresmul₁ := residueDegree_projectionTower B₁
  have hresmul₂ := residueDegree_projectionTower B₂
  rw [hres] at hresmul₁ hresmul₂
  have hr₁ : residueDegree B₁ K = 1 := (mul_eq_one.mp hresmul₁).2
  have hr₂ : residueDegree B₂ K = 1 := (mul_eq_one.mp hresmul₂).2
  have hd₁ : Module.finrank B₁ K = p :=
    (Basic.intermediateField_tower_compatible hp hG B₁ D.degree_B₁).2.2.2.2.2.2.2.2.2.2.1
  have hd₂ : Module.finrank B₂ K = p :=
    (Basic.intermediateField_tower_compatible hp hG B₂ D.degree_B₂).2.2.2.2.2.2.2.2.2.2.1
  have he₁ : ramificationIndex B₁ K = p := by
    simpa only [hd₁, hr₁, mul_one] using
      (finrank_eq_ramificationIndex_mul_residueDegree B₁ K).symm
  have he₂ : ramificationIndex B₂ K = p := by
    simpa only [hd₂, hr₂, mul_one] using
      (finrank_eq_ramificationIndex_mul_residueDegree B₂ K).symm
  obtain ⟨Delta, a, hroot, hDelta, ha, hprime, hgen, hcoeff⟩ :=
    Total.coefficientExtraction hp hG hres hchar D
  let pb : PowerBasis B₂ K :=
    PowerBasis.ofAdjoinEqTop (IsAlgebraic.of_finite B₂ Delta).isIntegral hgen
  have hpbgen : pb.gen = Delta := PowerBasis.ofAdjoinEqTop_gen _ _
  have hpbdim : pb.dim = p := by rw [← pb.finrank]; exact hd₂
  have hcoeffpb (w : B₁) (i : Fin pb.dim) :
      ord B₁ w + ((((i : ℕ) * D.t : ℕ) : ℤ) : WithTop ℤ) ≤
        ord B₂ (pb.basis.repr (algebraMap B₁ K w) i) := by
    have hexp := powerBasis_expansion pb hpbdim (algebraMap B₁ K w)
    rw [hpbgen] at hexp
    simpa using
      hcoeff w _ hexp (Fin.cast hpbdim i)
  refine ⟨pb, a, hpbdim, by simpa only [hpbgen] using hroot,
    by simpa only [hpbgen] using hDelta, ha, hprime, hcoeffpb, ?_⟩
  intro x w
  dsimp only
  let z := algebraMap B₂ K x * algebraMap B₁ K w
  let y := constantProjection pb z
  change (((1 + D.tPrime : ℤ) : WithTop ℤ) ≤ ord K z) →
    (((1 + D.t₂ + ((p : ℤ) - 3) * D.t : ℤ) : WithTop ℤ) ≤ ord K z) →
    z - algebraMap B₂ K y ∈ lattice K (1 + (p : ℤ) * D.t₂) ∧
    norm B₁ K z - algebraMap F B₁ (norm F B₂ y) ∈
      lattice B₁ (1 + (p : ℤ) * D.t₂) ∧
    ord K (algebraMap B₂ K y) = ord K z
  intro hfirst hsecond
  have hnorm (hclose : z - algebraMap B₂ K y ∈ lattice K (1 + (p : ℤ) * D.t₂)) :=
    Total.projectionTransfer hp hG hres hchar D x w y hclose hsecond
  by_cases hz0 : z = 0
  · have hy0 : y = 0 := by simp [y, hz0]
    have hclose : z - algebraMap B₂ K y ∈ lattice K (1 + (p : ℤ) * D.t₂) := by
      simp [hz0, hy0]
    exact ⟨hclose, hnorm hclose, by simp [hz0, hy0]⟩
  have hx0 : x ≠ 0 := by intro hx; simp [z, hx] at hz0
  have hw0 : w ≠ 0 := by intro hw; simp [z, hw] at hz0
  obtain ⟨vx, hvx⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff B₂).2 hx0)
  obtain ⟨vw, hvw⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff B₁).2 hw0)
  let q : ℤ := vx + vw
  have hz : ord K z = (((p : ℤ) * q : ℤ) : WithTop ℤ) := by
    simp only [z, ord_mul, ord_algebraMap, he₁, he₂,
      ← hvx, ← hvw, ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul]
    congr 1
    dsimp only [q]
    ring
  let W : Fin p → B₂ := fun i =>
    pb.basis.repr (algebraMap B₁ K w) (Fin.cast hpbdim.symm i)
  let Y : Fin p → B₂ := fun i => x * W i
  have hexpw : algebraMap B₁ K w =
      ∑ i : Fin p, algebraMap B₂ K (W i) * Delta ^ (i : ℕ) := by
    simpa only [hpbgen] using powerBasis_expansion pb hpbdim (algebraMap B₁ K w)
  have hexp : z = ∑ i : Fin p, algebraMap B₂ K (Y i) * Delta ^ (i : ℕ) := by
    dsimp only [z, Y]
    rw [hexpw, Finset.mul_sum]
    simp only [map_mul, mul_assoc]
  have hY : ∀ i : Fin p, Y i ∈ lattice B₂ (q + (i : ℕ) * (D.t : ℤ)) := by
    intro i
    have hc := hcoeff w W hexpw i
    rw [← hvw] at hc
    have hWi : W i ∈ lattice B₂ (vw + (i : ℕ) * (D.t : ℤ)) := by
      simpa only [mem_lattice, WithTop.coe_add, Nat.cast_mul] using hc
    have hxi : x ∈ lattice B₂ vx := by rw [mem_lattice, ← hvx]
    convert mul_mem_lattice B₂ hxi hWi using 1
    congr 1
    dsimp only [q]
    ring
  have hy : Y ⟨0, hp.pos⟩ = y := by
    change x * pb.basis.repr (algebraMap B₁ K w) (Fin.cast hpbdim.symm ⟨0, hp.pos⟩) =
      constantProjection pb (algebraMap B₂ K x * algebraMap B₁ K w)
    rw [← Algebra.smul_def, map_smul]
    rfl
  have htail := constant_tail_mem B₂ K hp.pos (Int.natCast_nonneg D.t)
    he₂ hDelta Y q hexp hY
  have hfirstZ : 1 + (D.tPrime : ℤ) ≤ (p : ℤ) * q := by
    simpa only [hz, WithTop.coe_le_coe] using hfirst
  have hK : 1 + (p : ℤ) * D.t₂ = 1 + D.tPrime + ((p : ℤ) - 1) * D.t := by
    rw [D.t₂_eq, D.tPrime_eq]
    push_cast
    ring
  have hclose : z - algebraMap B₂ K y ∈ lattice K (1 + (p : ℤ) * D.t₂) := by
    rw [hy] at htail
    exact lattice_antitone K (by rw [hK]; omega) htail
  have hconst := (Total.projectionTransfer_coefficients B₂ K hp D.t_pos he₂
    hDelta hprime Y q hexp hz hY hclose).1
  rw [hy] at hconst
  refine ⟨hclose, hnorm hclose, ?_⟩
  rw [ord_algebraMap, he₂, hconst, hz]
  simp only [← WithTop.coe_nsmul, nsmul_eq_mul]

end Diamond

end

end LanglandsSecondMainLemma.Odd.Transition
