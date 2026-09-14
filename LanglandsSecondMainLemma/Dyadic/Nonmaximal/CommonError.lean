import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Dyadic.Nonmaximal.Origin

/-!
# Dyadic nonmaximal common error

The exact identities `D:NM:commonC`, `D:NM:common-error`, and
`D:NM:common-Delta`, and all four bounds of `D:NM:bounds` (Lemma 13.9).
The input origin has the proved constructor in `Nonmaximal.Origin`.
All norms, traces, and valuations are those of the actual intermediate fields.
The identities include zero, and all depth indices are integers.
-/

namespace LanglandsSecondMainLemma.Dyadic.Nonmaximal

open LanglandsFirstMainLemma

noncomputable section

private theorem trace_eq_self_add_nontrivial
    {E M : Type*} [Field E] [Field M] [Algebra E M]
    [FiniteDimensional E M] [IsGalois E M]
    (sigma : Gal(M/E)) (hsigma : sigma ≠ 1)
    (hcard : Fintype.card Gal(M/E) = 2) (u : M) :
    algebraMap E M (trace E M u) = u + sigma u := by
  classical
  rw [trace_eq_sum_automorphisms]
  have huniv : ({sigma, (1 : Gal(M/E))} : Finset Gal(M/E)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simpa using hsigma),
      Finset.card_singleton, hcard]
  rw [← huniv]
  simp [hsigma, add_comm]

private theorem norm_eq_self_mul_nontrivial
    {E M : Type*} [Field E] [Field M] [Algebra E M]
    [FiniteDimensional E M] [IsGalois E M]
    (sigma : Gal(M/E)) (hsigma : sigma ≠ 1)
    (hcard : Fintype.card Gal(M/E) = 2) (u : M) :
    algebraMap E M (norm E M u) = u * sigma u := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms]
  have huniv : ({sigma, (1 : Gal(M/E))} : Finset Gal(M/E)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simpa using hsigma),
      Finset.card_singleton, hcard]
  rw [← huniv]
  simp [hsigma, mul_comm]

/-- A nonidentity automorphism of a quadratic simple extension exchanges
the two roots of `X² + X - c`. -/
private theorem nontrivial_map_artinSchreier_root
    {E M : Type*} [Field E] [Field M] [Algebra E M]
    (u : M) (c : E)
    (hu : u ^ 2 + u = algebraMap E M c)
    (hgen : Algebra.adjoin E ({u} : Set M) = ⊤)
    (sigma : Gal(M/E)) (hsigma : sigma ≠ 1) :
    sigma u = -1 - u := by
  have hsigmaRoot : (sigma u) ^ 2 + sigma u = algebraMap E M c := by
    calc
      (sigma u) ^ 2 + sigma u = sigma (u ^ 2 + u) := by simp
      _ = sigma (algebraMap E M c) := congrArg sigma hu
      _ = algebraMap E M c := sigma.commutes c
  have hroot : sigma u = u ∨ sigma u + u + 1 = 0 := by
    have hp : (sigma u - u) * (sigma u + u + 1) = 0 := by
      calc
        (sigma u - u) * (sigma u + u + 1) =
          ((sigma u) ^ 2 + sigma u) - (u ^ 2 + u) := by ring
        _ = 0 := by rw [hsigmaRoot, hu, sub_self]
    rcases mul_eq_zero.mp hp with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr h
  rcases hroot with hsame | hother
  · exfalso
    apply hsigma
    apply AlgEquiv.ext
    have heq : sigma.toAlgHom = (1 : Gal(M/E)).toAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top hgen
      intro v hv
      rw [Set.mem_singleton_iff.mp hv]
      simpa using hsame
    intro v
    exact DFunLike.congr_fun heq v
  · linear_combination hother


/-- Coordinates in a genuine quadratic power basis. -/
private theorem quadratic_coordinates
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    [Module.Finite F L] [Algebra.IsQuadraticExtension F L]
    (z : L) (hz : Algebra.adjoin F ({z} : Set L) = ⊤) (X : L) :
    ∃ P Q : F, X = algebraMap F L P + algebraMap F L Q * z := by
  let pb := PowerBasis.ofAdjoinEqTop' (Algebra.IsIntegral.isIntegral z) hz
  have hdim : pb.dim = 2 := by
    rw [← PowerBasis.finrank pb, Algebra.IsQuadraticExtension.finrank_eq_two F L]
  let B : Module.Basis (Fin 2) F L := pb.basis.reindex (finCongr hdim)
  have hB0 : B 0 = 1 := by simp [B]
  have hB1 : B 1 = z := by
    simp only [B, Module.Basis.reindex_apply]
    rw [pb.basis_eq_pow]
    have hindex : (((finCongr hdim).symm (1 : Fin 2)) : ℕ) = 1 := rfl
    rw [hindex, pow_one]
    exact PowerBasis.ofAdjoinEqTop'_gen _ _
  refine ⟨B.repr X 0, B.repr X 1, ?_⟩
  have hs := B.sum_repr X
  rw [Fin.sum_univ_two, hB0, hB1] at hs
  simpa only [Algebra.smul_def, mul_one] using hs.symm

/-- Odd generator order prevents cancellation between the two coordinates.
The result uses floor division on integers, including negative depths. -/
private theorem quadratic_coordinate_bounds
    (F L : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L]
    (hram : ramificationIndex F L = 2) (z : L) (r h : ℤ)
    (hz : ord L z = ((1 - 2 * r : ℤ) : WithTop ℤ))
    (P Q : F) (hX : algebraMap F L P + algebraMap F L Q * z ∈ lattice L (-h)) :
    P ∈ lattice F (-(h / 2)) ∧ Q ∈ lattice F (r - (h + 1) / 2) := by
  have hPmap : ord L (algebraMap F L P) = 2 • ord F P := by
    rw [ord_algebraMap, hram]
  have hQmap : ord L (algebraMap F L Q * z) =
      2 • ord F Q + ((1 - 2 * r : ℤ) : WithTop ℤ) := by
    rw [ord_mul, ord_algebraMap, hram, hz]
  have hboth : ((-h : ℤ) : WithTop ℤ) ≤ ord L (algebraMap F L P) ∧
      ((-h : ℤ) : WithTop ℤ) ≤ ord L (algebraMap F L Q * z) := by
    by_cases hP : P = 0
    · simpa [hP] using hX
    by_cases hQ : Q = 0
    · simpa [hQ] using hX
    obtain ⟨p, hp⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).mpr hP)
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).mpr hQ)
    have hne : ord L (algebraMap F L P) ≠ ord L (algebraMap F L Q * z) := by
      rw [hPmap, hQmap, ← hp, ← hq]
      intro heq
      have hi : 2 * p = 2 * q + (1 - 2 * r) := by exact_mod_cast heq
      omega
    rw [mem_lattice, ord_add_eq_min L hne] at hX
    exact le_min_iff.mp hX
  constructor
  · by_cases hP : P = 0
    · simp [hP]
    obtain ⟨p, hp⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).mpr hP)
    have hbound := hboth.1
    rw [hPmap, ← hp] at hbound
    have hi : -h ≤ 2 * p := by exact_mod_cast hbound
    rw [mem_lattice, ← hp]
    exact WithTop.coe_le_coe.mpr (by omega)
  · by_cases hQ : Q = 0
    · simp [hQ]
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).mpr hQ)
    have hbound := hboth.2
    rw [hQmap, ← hq] at hbound
    have hi : -h ≤ 2 * q + (1 - 2 * r) := by exact_mod_cast hbound
    rw [mem_lattice, ← hq]
    exact WithTop.coe_le_coe.mpr (by omega)

private theorem quadratic_card
    (F L : Type*) [Field F] [Field L] [Algebra F L]
    [Module.Finite F L] [IsGalois F L] [Algebra.IsQuadraticExtension F L] :
    Fintype.card Gal(L/F) = 2 := by
  rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank,
    Algebra.IsQuadraticExtension.finrank_eq_two F L]

/-- Exact norm of an affine coordinate for `z² + z = c`. -/
private theorem quadratic_norm_affine
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    [Module.Finite F L] [IsGalois F L] [Algebra.IsQuadraticExtension F L]
    (z : L) (c : F) (hz : z ^ 2 + z = algebraMap F L c)
    (hgen : Algebra.adjoin F ({z} : Set L) = ⊤) (P Q : F) :
    norm F L (algebraMap F L P + algebraMap F L Q * z) =
      P ^ 2 - P * Q - c * Q ^ 2 := by
  classical
  obtain ⟨sigma, hsigma⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [quadratic_card F L]; omega) (1 : Gal(L/F))
  have hsz := nontrivial_map_artinSchreier_root z c hz hgen sigma hsigma
  apply (algebraMap F L).injective
  rw [norm_eq_self_mul_nontrivial sigma hsigma (quadratic_card F L)]
  simp only [map_add, map_mul, sigma.commutes, hsz, map_sub, map_pow]
  linear_combination -(algebraMap F L Q) ^ 2 * hz

private theorem quadratic_norm_sub_base
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    [Module.Finite F L] [IsGalois F L] [Algebra.IsQuadraticExtension F L]
    (u : L) (c : F) :
    norm F L (u - algebraMap F L c) = norm F L u + c ^ 2 - c * trace F L u := by
  classical
  obtain ⟨sigma, hsigma⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [quadratic_card F L]; omega) (1 : Gal(L/F))
  apply (algebraMap F L).injective
  simp only [map_sub, map_add, map_mul, map_pow]
  rw [norm_eq_self_mul_nontrivial sigma hsigma (quadratic_card F L),
    norm_eq_self_mul_nontrivial sigma hsigma (quadratic_card F L),
    trace_eq_self_add_nontrivial sigma hsigma (quadratic_card F L)]
  simp only [map_sub, sigma.commutes]
  ring

private theorem quadratic_map_mem_lattice
    (F L : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L]
    (hram : ramificationIndex F L = 2) {n : ℤ} {v : F}
    (hv : v ∈ lattice F n) : algebraMap F L v ∈ lattice L (2 * n) := by
  rw [mem_lattice, ord_algebraMap, hram]
  have hm := nsmul_le_nsmul_right ((mem_lattice F).mp hv) 2
  rw [← WithTop.coe_nsmul] at hm
  simpa only [nsmul_eq_mul, Nat.cast_ofNat] using hm

variable {F K : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [Module.Finite F K]
  {L₁ L₂ L₃ : IntermediateField F K}
  [ValuativeRel L₁] [TopologicalSpace L₁] [IsNonarchimedeanLocalField L₁]
  [ValuativeRel L₂] [TopologicalSpace L₂] [IsNonarchimedeanLocalField L₂]
  [ValuativeRel L₃] [TopologicalSpace L₃] [IsNonarchimedeanLocalField L₃]
  [ValuativeExtension F L₁] [ValuativeExtension L₁ K]
  [ValuativeExtension F L₂] [ValuativeExtension L₂ K]
  [ValuativeExtension F L₃] [ValuativeExtension L₃ K]
  [Module.Finite F L₁] [Module.Finite L₁ K]
  [Module.Finite F L₂] [Module.Finite L₂ K]
  [Module.Finite F L₃] [Module.Finite L₃ K]
  {a r : ℕ} {x : L₁} {y : L₂} {z : L₃} {f g d : F}

namespace DyadicNonmaximalOriginData

/-- `C = Y - X`, with the third-field element embedded in `K`. -/
def adjustedOrigin (D : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (X : L₃) : K := D.Y - (X : K)

/-- `A = n₃ X`. -/
def adjustmentNorm (_D : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (X : L₃) : F := norm F L₃ X

/-- `p_X = tr₃ X`. -/
def adjustmentTrace (_D : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (X : L₃) : F := trace F L₃ X

/-- The actual first crossed trace `Q₁ = S₁(Y g₁ X)`. -/
def firstCrossedTrace (D : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (g₁ : Gal(K/L₁)) (X : L₃) : L₁ := trace L₁ K (D.Y * g₁ (X : K))

/-- The actual second crossed trace `Q₂ = S₂(Y g₂ X)`. -/
def secondCrossedTrace (D : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (g₂ : Gal(K/L₂)) (X : L₃) : L₂ := trace L₂ K (D.Y * g₂ (X : K))

/-- Define the error intrinsically in `F`; the theorem identifies both
lower norm errors with the paper's conjugate product. -/
def commonErrorTerm (D : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (g₁ : Gal(K/L₁)) (X : L₃) : F :=
  norm F L₁ (D.firstCrossedTrace g₁ X) -
    norm F L₁ (trace L₁ K D.Y) * D.adjustmentNorm X

/-- The full trace-norm increment, including its affine term. -/
def traceNormIncrement (D : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (X : L₃) : F := D.adjustmentTrace X ^ 2 + 2 * D.k₀ * D.adjustmentTrace X

end DyadicNonmaximalOriginData

/-- Exact adjustment identities. No trace or character argument is divided by. -/
structure CommonErrorIdentities
    (D : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (g₁ : Gal(K/L₁)) (g₂ : Gal(K/L₂)) (q₃ : Gal(L₃/F)) (X : L₃) : Prop where
  first_norm : norm L₁ K (D.adjustedOrigin X) = norm L₁ K D.Y +
    algebraMap F L₁ (D.adjustmentNorm X) - D.firstCrossedTrace g₁ X
  second_norm : norm L₂ K (D.adjustedOrigin X) = norm L₂ K D.Y +
    algebraMap F L₂ (D.adjustmentNorm X) - D.secondCrossedTrace g₂ X
  first_trace : trace L₁ K (D.adjustedOrigin X) = trace L₁ K D.Y -
    algebraMap F L₁ (D.adjustmentTrace X)
  second_trace : trace L₂ K (D.adjustedOrigin X) = trace L₂ K D.Y -
    algebraMap F L₂ (D.adjustmentTrace X)
  first_weighted_norm : norm F L₁ (D.firstCrossedTrace g₁ X) =
    norm F L₁ (trace L₁ K D.Y) * D.adjustmentNorm X + D.commonErrorTerm g₁ X
  second_weighted_norm : norm F L₂ (D.secondCrossedTrace g₂ X) =
    norm F L₂ (trace L₂ K D.Y) * D.adjustmentNorm X + D.commonErrorTerm g₁ X
  error_product : algebraMap F L₃ (D.commonErrorTerm g₁ X) =
    (q₃ X - X) * (norm L₃ K D.Y * q₃ X - q₃ (norm L₃ K D.Y) * X)
  first_trace_norm : norm F L₁ (trace L₁ K (D.adjustedOrigin X)) =
    norm F L₁ (trace L₁ K D.Y) + D.traceNormIncrement X
  second_trace_norm : norm F L₂ (trace L₂ K (D.adjustedOrigin X)) =
    norm F L₂ (trace L₂ K D.Y) + D.traceNormIncrement X

/-- Lemma 13.9, with `ceil(h/2)` expressed as integer `(h+1)/2`. -/
structure CommonErrorBounds
    (D : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (g₁ : Gal(K/L₁)) (g₂ : Gal(K/L₂)) (X : L₃) (h : ℤ) : Prop where
  trace_bound : (((r : ℤ) - (h + 1) / 2 : ℤ) : WithTop ℤ) ≤ ord F (D.adjustmentTrace X)
  error_bound : (((2 * (r : ℤ) - a - h : ℤ)) : WithTop ℤ) ≤ ord F (D.commonErrorTerm g₁ X)
  first_crossed_bound : (((2 * ((r : ℤ) - a) - h : ℤ)) : WithTop ℤ) ≤
    ord L₁ (D.firstCrossedTrace g₁ X)
  second_crossed_bound : ((-h : ℤ) : WithTop ℤ) ≤ ord L₂ (D.secondCrossedTrace g₂ X)

variable [IsGalois F L₁] [IsGalois L₁ K]
  [IsGalois F L₂] [IsGalois L₂ K] [IsGalois F L₃]
  [Algebra.IsQuadraticExtension F L₁] [Algebra.IsQuadraticExtension L₁ K]
  [Algebra.IsQuadraticExtension F L₂] [Algebra.IsQuadraticExtension L₂ K]
  [Algebra.IsQuadraticExtension F L₃]

set_option maxHeartbeats 800000 in
/-- Prove the exact two-field identities and retain their coordinates for the estimates. -/
private theorem commonError_coordinates
    (D : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (g₁ : Gal(K/L₁)) (hg₁ : g₁ ≠ 1) (g₂ : Gal(K/L₂)) (hg₂ : g₂ ≠ 1)
    (q₃ : Gal(L₃/F)) (hq₃ : q₃ ≠ 1) (X : L₃) :
    ∃ P Q : F,
      X = algebraMap F L₃ P + algebraMap F L₃ Q * z ∧
      D.adjustmentTrace X = 2 * P - Q ∧
      D.firstCrossedTrace g₁ X =
        algebraMap F L₁ (-d * P - 2 * d * g * Q) +
          algebraMap F L₁ (2 * P - (D.k₀ + 4 * d * g) * Q) * x ∧
      D.secondCrossedTrace g₂ X =
        algebraMap F L₂ (-P - 2 * f * Q) +
          algebraMap F L₂ (2 * d * P - (D.k₀ + 4 * f) * Q) * y ∧
      D.commonErrorTerm g₁ X = Q * (d * P - D.E * Q) * (1 + 4 * (f + g + 4 * f * g)) ∧
      CommonErrorIdentities D g₁ g₂ q₃ X := by
  obtain ⟨P, Q, hcoord⟩ := quadratic_coordinates z D.z_generates X
  have hxK : (x : K) ^ 2 + (x : K) = algebraMap F K f := by
    exact (congrArg (algebraMap L₁ K) D.x_polynomial).trans
      (IsScalarTower.algebraMap_apply F L₁ K f).symm
  have hyK : (y : K) ^ 2 + (y : K) = algebraMap F K g := by
    exact (congrArg (algebraMap L₂ K) D.y_polynomial).trans
      (IsScalarTower.algebraMap_apply F L₂ K g).symm
  have hg₁x : g₁ (x : K) = (x : K) := g₁.commutes x
  have hg₂y : g₂ (y : K) = (y : K) := g₂.commutes y
  have hg₁y : g₁ (y : K) = -1 - (y : K) :=
    nontrivial_map_artinSchreier_root (y : K) (algebraMap F L₁ g)
      (hyK.trans (IsScalarTower.algebraMap_apply F L₁ K g)) D.y_generates_over₁ g₁ hg₁
  have hg₂x : g₂ (x : K) = -1 - (x : K) :=
    nontrivial_map_artinSchreier_root (x : K) (algebraMap F L₂ f)
      (hxK.trans (IsScalarTower.algebraMap_apply F L₂ K f)) D.x_generates_over₂ g₂ hg₂
  have hq₃z : q₃ z = -1 - z :=
    nontrivial_map_artinSchreier_root z _ D.z_polynomial D.z_generates q₃ hq₃
  have hg₁F (v : F) : g₁ (algebraMap F K v) = algebraMap F K v := by
    rw [IsScalarTower.algebraMap_apply F L₁ K]
    exact g₁.commutes _
  have hg₂F (v : F) : g₂ (algebraMap F K v) = algebraMap F K v := by
    rw [IsScalarTower.algebraMap_apply F L₂ K]
    exact g₂.commutes _
  have hg₁z : g₁ (z : K) = -1 - (z : K) := by
    rw [D.z_eq]
    simp only [map_add, map_mul, map_ofNat, hg₁x, hg₁y]
    ring
  have hg₂z : g₂ (z : K) = -1 - (z : K) := by
    rw [D.z_eq]
    simp only [map_add, map_mul, map_ofNat, hg₂x, hg₂y]
    ring
  have hg₁Y : g₁ D.Y = (x : K) - algebraMap F K d - algebraMap F K d * (y : K) := by
    rw [D.Y_eq]
    simp only [map_add, map_mul, hg₁x, hg₁y, hg₁F]
    ring
  have hg₂Y : g₂ D.Y = -1 - (x : K) + algebraMap F K d * (y : K) := by
    rw [D.Y_eq]
    simp only [map_add, map_mul, hg₂x, hg₂y, hg₂F]
  have hq₃X : q₃ X = algebraMap F L₃ (P - Q) - algebraMap F L₃ Q * z := by
    rw [hcoord]
    simp only [map_add, map_mul, q₃.commutes, hq₃z, map_sub]
    ring
  have hcoordK : (X : K) = algebraMap F K P + algebraMap F K Q * (z : K) := by
    exact congrArg (algebraMap L₃ K) hcoord
  have hqcoordK : ((q₃ X : L₃) : K) =
      algebraMap F K (P - Q) - algebraMap F K Q * (z : K) := by
    exact congrArg (algebraMap L₃ K) hq₃X
  have hg₁X : g₁ (X : K) = (q₃ X : K) := by
    rw [hcoordK, hqcoordK]
    simp only [map_add, map_mul, hg₁F, hg₁z, map_sub]
    ring
  have hg₂X : g₂ (X : K) = (q₃ X : K) := by
    rw [hcoordK, hqcoordK]
    simp only [map_add, map_mul, hg₂F, hg₂z, map_sub]
    ring
  have hg₁X' : g₁ (q₃ X : K) = (X : K) := by
    rw [hqcoordK, hcoordK]
    simp only [map_sub, map_mul, hg₁F, hg₁z]
    ring
  have hg₂X' : g₂ (q₃ X : K) = (X : K) := by
    rw [hqcoordK, hcoordK]
    simp only [map_sub, map_mul, hg₂F, hg₂z]
    ring
  have hA : D.adjustmentNorm X = P ^ 2 - P * Q - (f + g + 4 * f * g) * Q ^ 2 := by
    rw [DyadicNonmaximalOriginData.adjustmentNorm, hcoord]
    exact quadratic_norm_affine z _ D.z_polynomial D.z_generates P Q
  have hp : D.adjustmentTrace X = 2 * P - Q := by
    apply (algebraMap F L₃).injective
    rw [DyadicNonmaximalOriginData.adjustmentTrace,
      trace_eq_self_add_nontrivial q₃ hq₃ (quadratic_card F L₃), hq₃X, hcoord]
    simp only [map_sub, map_mul, map_ofNat]
    ring
  have hAmap : algebraMap F K (D.adjustmentNorm X) = (X : K) * (q₃ X : K) := by
    rw [IsScalarTower.algebraMap_apply F L₃ K, DyadicNonmaximalOriginData.adjustmentNorm,
      norm_eq_self_mul_nontrivial q₃ hq₃ (quadratic_card F L₃)]
    rfl
  have hpmap : algebraMap F K (D.adjustmentTrace X) = (X : K) + (q₃ X : K) := by
    rw [IsScalarTower.algebraMap_apply F L₃ K, DyadicNonmaximalOriginData.adjustmentTrace,
      trace_eq_self_add_nontrivial q₃ hq₃ (quadratic_card F L₃)]
    rfl
  have hQ₁map : algebraMap L₁ K (D.firstCrossedTrace g₁ X) =
      D.Y * (q₃ X : K) + g₁ D.Y * (X : K) := by
    rw [DyadicNonmaximalOriginData.firstCrossedTrace,
      trace_eq_self_add_nontrivial g₁ hg₁ (quadratic_card L₁ K), hg₁X, map_mul, hg₁X']
  have hQ₂map : algebraMap L₂ K (D.secondCrossedTrace g₂ X) =
      D.Y * (q₃ X : K) + g₂ D.Y * (X : K) := by
    rw [DyadicNonmaximalOriginData.secondCrossedTrace,
      trace_eq_self_add_nontrivial g₂ hg₂ (quadratic_card L₂ K), hg₂X, map_mul, hg₂X']
  have hQ₁ : D.firstCrossedTrace g₁ X =
      algebraMap F L₁ (-d * P - 2 * d * g * Q) +
        algebraMap F L₁ (2 * P - (D.k₀ + 4 * d * g) * Q) * x := by
    apply (algebraMap L₁ K).injective
    rw [hQ₁map, hcoordK, hqcoordK, hg₁Y, D.Y_eq, D.z_eq, D.k₀_eq]
    simp only [map_add, map_sub, map_mul, map_neg, map_ofNat, map_one,
      ← IsScalarTower.algebraMap_apply F L₁ K]
    rw [show algebraMap L₁ K x = (x : K) from rfl]
    linear_combination -2 * algebraMap F K d * algebraMap F K Q *
      (1 + 2 * (x : K)) * hyK
  have hQ₂ : D.secondCrossedTrace g₂ X =
      algebraMap F L₂ (-P - 2 * f * Q) +
        algebraMap F L₂ (2 * d * P - (D.k₀ + 4 * f) * Q) * y := by
    apply (algebraMap L₂ K).injective
    rw [hQ₂map, hcoordK, hqcoordK, hg₂Y, D.Y_eq, D.z_eq, D.k₀_eq]
    simp only [map_add, map_sub, map_mul, map_neg, map_ofNat, map_one,
      ← IsScalarTower.algebraMap_apply F L₂ K]
    rw [show algebraMap L₂ K y = (y : K) from rfl]
    linear_combination -2 * algebraMap F K Q * (1 + 2 * (y : K)) * hxK
  have herror : D.commonErrorTerm g₁ X =
      Q * (d * P - D.E * Q) * (1 + 4 * (f + g + 4 * f * g)) := by
    rw [DyadicNonmaximalOriginData.commonErrorTerm, hQ₁,
      quadratic_norm_affine x f D.x_polynomial D.x_generates,
      D.lowerNormTrace₁, hA, D.k₀_eq, D.E_eq]
    ring
  have hweighted₂ : norm F L₂ (D.secondCrossedTrace g₂ X) =
      norm F L₂ (trace L₂ K D.Y) * D.adjustmentNorm X + D.commonErrorTerm g₁ X := by
    rw [hQ₂, quadratic_norm_affine y g D.y_polynomial D.y_generates,
      D.lowerNormTrace₂, hA, herror, D.k₀_eq, D.E_eq]
    ring
  have hproduct : algebraMap F L₃ (D.commonErrorTerm g₁ X) =
      (q₃ X - X) * (norm L₃ K D.Y * q₃ X - q₃ (norm L₃ K D.Y) * X) := by
    rw [herror, D.upperNorm₃, hq₃X, hcoord]
    simp only [map_sub, map_neg, map_add, map_mul, map_one, map_ofNat,
      q₃.commutes, hq₃z]
    have hzsq : z ^ 2 = algebraMap F L₃ (f + g + 4 * f * g) - z := by
      linear_combination D.z_polynomial
    ring_nf
    rw [hzsq]
    simp only [map_add, map_mul, map_ofNat]
    ring
  have hn₁ : norm L₁ K (D.adjustedOrigin X) = norm L₁ K D.Y +
      algebraMap F L₁ (D.adjustmentNorm X) - D.firstCrossedTrace g₁ X := by
    apply (algebraMap L₁ K).injective
    rw [DyadicNonmaximalOriginData.adjustedOrigin,
      norm_eq_self_mul_nontrivial g₁ hg₁ (quadratic_card L₁ K), map_sub, hg₁X]
    simp only [map_sub, map_add]
    rw [norm_eq_self_mul_nontrivial g₁ hg₁ (quadratic_card L₁ K),
      ← IsScalarTower.algebraMap_apply F L₁ K, hAmap, hQ₁map]
    ring
  have hn₂ : norm L₂ K (D.adjustedOrigin X) = norm L₂ K D.Y +
      algebraMap F L₂ (D.adjustmentNorm X) - D.secondCrossedTrace g₂ X := by
    apply (algebraMap L₂ K).injective
    rw [DyadicNonmaximalOriginData.adjustedOrigin,
      norm_eq_self_mul_nontrivial g₂ hg₂ (quadratic_card L₂ K), map_sub, hg₂X]
    simp only [map_sub, map_add]
    rw [norm_eq_self_mul_nontrivial g₂ hg₂ (quadratic_card L₂ K),
      ← IsScalarTower.algebraMap_apply F L₂ K, hAmap, hQ₂map]
    ring
  have ht₁ : trace L₁ K (D.adjustedOrigin X) = trace L₁ K D.Y -
      algebraMap F L₁ (D.adjustmentTrace X) := by
    apply (algebraMap L₁ K).injective
    rw [DyadicNonmaximalOriginData.adjustedOrigin,
      trace_eq_self_add_nontrivial g₁ hg₁ (quadratic_card L₁ K), map_sub, hg₁X]
    simp only [map_sub]
    rw [trace_eq_self_add_nontrivial g₁ hg₁ (quadratic_card L₁ K),
      ← IsScalarTower.algebraMap_apply F L₁ K, hpmap]
    ring
  have ht₂ : trace L₂ K (D.adjustedOrigin X) = trace L₂ K D.Y -
      algebraMap F L₂ (D.adjustmentTrace X) := by
    apply (algebraMap L₂ K).injective
    rw [DyadicNonmaximalOriginData.adjustedOrigin,
      trace_eq_self_add_nontrivial g₂ hg₂ (quadratic_card L₂ K), map_sub, hg₂X]
    simp only [map_sub]
    rw [trace_eq_self_add_nontrivial g₂ hg₂ (quadratic_card L₂ K),
      ← IsScalarTower.algebraMap_apply F L₂ K, hpmap]
    ring
  refine ⟨P, Q, hcoord, hp, hQ₁, hQ₂, herror, ?_⟩
  refine { first_norm := hn₁
           second_norm := hn₂
           first_trace := ht₁
           second_trace := ht₂
           first_weighted_norm := ?_
           second_weighted_norm := hweighted₂
           error_product := hproduct
           first_trace_norm := ?_
           second_trace_norm := ?_ }
  · rw [DyadicNonmaximalOriginData.commonErrorTerm]
    ring
  · rw [ht₁, quadratic_norm_sub_base, Algebra.trace_trace, D.totalTrace,
      DyadicNonmaximalOriginData.traceNormIncrement]
    ring
  · rw [ht₂, quadratic_norm_sub_base, Algebra.trace_trace, D.totalTrace,
      DyadicNonmaximalOriginData.traceNormIncrement]
    ring

set_option maxHeartbeats 800000 in
/-- **Common error and all four bounds (Paper 13.9).**

The input is the constructed nonmaximal origin in the actual quadratic
intermediate fields. Conjugation rules and both norm-error equalities are
proved from those coordinates, not supplied as hypotheses. The full
trace-norm increment includes `2 k₀ p_X` even when an upper trace vanishes.

The bounds are proved on the entire integer lattice `v(X) ≥ -h`, which
includes the stated case `v(X) = -h`, negative `h`, arbitrarily high `h`,
and `X = 0`. No character evaluation or norm representative is assumed.
-/
theorem commonError
    (D : DyadicNonmaximalOriginData F K L₁ L₂ L₃ a r x y z f g d)
    (e : ℕ) (_ha : 1 ≤ a) (har : a ≤ r) (hre : r ≤ e)
    (htwo : ord F (2 : F) = (e : WithTop ℤ))
    (hres₁ : residueDegree F L₁ = 1) (hres₂ : residueDegree F L₂ = 1)
    (hres₃ : residueDegree F L₃ = 1)
    (g₁ : Gal(K/L₁)) (hg₁ : g₁ ≠ 1) (g₂ : Gal(K/L₂)) (hg₂ : g₂ ≠ 1)
    (q₃ : Gal(L₃/F)) (hq₃ : q₃ ≠ 1) (X : L₃) :
    CommonErrorIdentities D g₁ g₂ q₃ X ∧
      ∀ h : ℤ, X ∈ lattice L₃ (-h) → CommonErrorBounds D g₁ g₂ X h := by
  obtain ⟨P, Q, hcoord, hp, hQ₁, hQ₂, herror, hidentities⟩ :=
    commonError_coordinates D g₁ hg₁ g₂ hg₂ q₃ hq₃ X
  refine ⟨hidentities, ?_⟩
  intro h hX
  have hram₁ : ramificationIndex F L₁ = 2 := by
    have hd := finrank_eq_ramificationIndex_mul_residueDegree F L₁
    rw [Algebra.IsQuadraticExtension.finrank_eq_two F L₁, hres₁, mul_one] at hd
    exact hd.symm
  have hram₂ : ramificationIndex F L₂ = 2 := by
    have hd := finrank_eq_ramificationIndex_mul_residueDegree F L₂
    rw [Algebra.IsQuadraticExtension.finrank_eq_two F L₂, hres₂, mul_one] at hd
    exact hd.symm
  have hram₃ : ramificationIndex F L₃ = 2 := by
    have hd := finrank_eq_ramificationIndex_mul_residueDegree F L₃
    rw [Algebra.IsQuadraticExtension.finrank_eq_two F L₃, hres₃, mul_one] at hd
    exact hd.symm
  obtain ⟨hP, hQ⟩ := quadratic_coordinate_bounds F L₃ hram₃ z (r : ℤ) h
    D.z_order P Q (hcoord ▸ hX)
  let pDepth : ℤ := -(h / 2)
  let qDepth : ℤ := (r : ℤ) - (h + 1) / 2
  change P ∈ lattice F pDepth at hP
  change Q ∈ lattice F qDepth at hQ
  have htwoLat : (2 : F) ∈ lattice F (e : ℤ) := by
    rw [mem_lattice, htwo]
    norm_num
  have hfourLat : (4 : F) ∈ lattice F (2 * (e : ℤ)) := by
    simpa only [show (2 : F) * 2 = 4 by norm_num, ← two_mul] using
      mul_mem_lattice F htwoLat htwoLat
  have hf : f ∈ lattice F (1 - 2 * (a : ℤ)) := by rw [mem_lattice, D.f_order]
  have hg : g ∈ lattice F (1 - 2 * (r : ℤ)) := by rw [mem_lattice, D.g_order]
  have hd : d ∈ lattice F ((r : ℤ) - a) := by rw [mem_lattice, D.d_order]
  have hk : D.k₀ ∈ lattice F 0 := by rw [mem_lattice, D.k₀_order]; norm_num
  have hx : x ∈ lattice L₁ (1 - 2 * (a : ℤ)) := by rw [mem_lattice, D.x_order]
  have hy : y ∈ lattice L₂ (1 - 2 * (r : ℤ)) := by rw [mem_lattice, D.y_order]

  -- The discriminant factor of the exact error is a unit.
  have hc : f + g + 4 * f * g ∈ lattice F (1 - 2 * (r : ℤ)) := by
    refine add_mem_lattice F (add_mem_lattice F ?_ hg) ?_
    · exact lattice_antitone F (by omega) hf
    · exact lattice_antitone F (by omega)
        (mul_mem_lattice F (mul_mem_lattice F hfourLat hf) hg)
  have hfourc : 4 * (f + g + 4 * f * g) ∈ lattice F 1 :=
    lattice_antitone F (by omega) (mul_mem_lattice F hfourLat hc)
  have hunit : ord F (1 + 4 * (f + g + 4 * f * g)) = 0 := by
    have hpos : (0 : WithTop ℤ) < ord F (4 * (f + g + 4 * f * g)) :=
      lt_of_lt_of_le (by norm_num) ((mem_lattice F).mp hfourc)
    rw [ord_add_eq_min F (by rw [ord_one]; exact ne_of_lt hpos), ord_one,
      min_eq_left hpos.le]
  have hunitLat : 1 + 4 * (f + g + 4 * f * g) ∈ lattice F 0 := by
    rw [mem_lattice, hunit]
    norm_num

  have hpLat : D.adjustmentTrace X ∈ lattice F qDepth := by
    rw [hp]
    exact sub_mem_lattice F
      (lattice_antitone F (by dsimp [pDepth, qDepth]; omega)
        (mul_mem_lattice F htwoLat hP)) hQ
  let target : ℤ := 2 * (r : ℤ) - a - h
  have hfirstError : Q * (d * P) ∈ lattice F target :=
    lattice_antitone F (by dsimp [target, pDepth, qDepth]; omega)
      (mul_mem_lattice F hQ (mul_mem_lattice F hd hP))
  have hsecondError : Q * (D.E * Q) ∈ lattice F target :=
    lattice_antitone F (by dsimp [target, qDepth]; omega)
      (mul_mem_lattice F hQ (mul_mem_lattice F D.E_lattice hQ))
  have herrorLat : D.commonErrorTerm g₁ X ∈ lattice F target := by
    rw [herror, mul_sub]
    simpa only [add_zero] using mul_mem_lattice F
      (sub_mem_lattice F hfirstError hsecondError) hunitLat

  -- Keep the full affine crossed traces and bound each summand. These
  -- coordinate estimates give the same depths as the upper trace formula.
  have hk₁ : D.k₀ + 4 * d * g ∈ lattice F 0 :=
    add_mem_lattice F hk (lattice_antitone F (by omega)
      (mul_mem_lattice F (mul_mem_lattice F hfourLat hd) hg))
  have hk₂ : D.k₀ + 4 * f ∈ lattice F 0 :=
    add_mem_lattice F hk (lattice_antitone F (by omega) (mul_mem_lattice F hfourLat hf))
  let target₁ : ℤ := 2 * ((r : ℤ) - a) - h
  have hconstant₁ : algebraMap F L₁ (-d * P - 2 * d * g * Q) ∈ lattice L₁ target₁ := by
    rw [map_sub, show -d * P = -(d * P) by ring, map_neg]
    refine sub_mem_lattice L₁ (neg_mem_lattice L₁ ?_) ?_
    · exact lattice_antitone L₁ (by dsimp [target₁, pDepth]; omega)
        (quadratic_map_mem_lattice F L₁ hram₁ (mul_mem_lattice F hd hP))
    · exact lattice_antitone L₁ (by dsimp [target₁, qDepth]; omega)
        (quadratic_map_mem_lattice F L₁ hram₁
          (mul_mem_lattice F (mul_mem_lattice F (mul_mem_lattice F htwoLat hd) hg) hQ))
  have hlinear₁ : algebraMap F L₁ (2 * P - (D.k₀ + 4 * d * g) * Q) * x ∈
      lattice L₁ target₁ := by
    rw [map_sub, sub_mul]
    refine sub_mem_lattice L₁ ?_ ?_
    · exact lattice_antitone L₁ (by dsimp [target₁, pDepth]; omega)
        (mul_mem_lattice L₁
          (quadratic_map_mem_lattice F L₁ hram₁ (mul_mem_lattice F htwoLat hP)) hx)
    · exact lattice_antitone L₁ (by dsimp [target₁, qDepth]; omega)
        (mul_mem_lattice L₁
          (quadratic_map_mem_lattice F L₁ hram₁ (mul_mem_lattice F hk₁ hQ)) hx)
  have hcross₁ : D.firstCrossedTrace g₁ X ∈ lattice L₁ target₁ := by
    rw [hQ₁]
    exact add_mem_lattice L₁ hconstant₁ hlinear₁
  have hconstant₂ : algebraMap F L₂ (-P - 2 * f * Q) ∈ lattice L₂ (-h) := by
    rw [map_sub, map_neg]
    refine sub_mem_lattice L₂ (neg_mem_lattice L₂ ?_) ?_
    · exact lattice_antitone L₂ (by dsimp [pDepth]; omega)
        (quadratic_map_mem_lattice F L₂ hram₂ hP)
    · exact lattice_antitone L₂ (by dsimp [qDepth]; omega)
        (quadratic_map_mem_lattice F L₂ hram₂
          (mul_mem_lattice F (mul_mem_lattice F htwoLat hf) hQ))
  have hlinear₂ : algebraMap F L₂ (2 * d * P - (D.k₀ + 4 * f) * Q) * y ∈
      lattice L₂ (-h) := by
    rw [map_sub, sub_mul]
    refine sub_mem_lattice L₂ ?_ ?_
    · exact lattice_antitone L₂ (by dsimp [pDepth]; omega)
        (mul_mem_lattice L₂ (quadratic_map_mem_lattice F L₂ hram₂
          (mul_mem_lattice F (mul_mem_lattice F htwoLat hd) hP)) hy)
    · exact lattice_antitone L₂ (by dsimp [qDepth]; omega)
        (mul_mem_lattice L₂
          (quadratic_map_mem_lattice F L₂ hram₂ (mul_mem_lattice F hk₂ hQ)) hy)
  have hcross₂ : D.secondCrossedTrace g₂ X ∈ lattice L₂ (-h) := by
    rw [hQ₂]
    exact add_mem_lattice L₂ hconstant₂ hlinear₂
  exact { trace_bound := hpLat
          error_bound := herrorLat
          first_crossed_bound := hcross₁
          second_crossed_bound := hcross₂ }

end

end LanglandsSecondMainLemma.Dyadic.Nonmaximal
