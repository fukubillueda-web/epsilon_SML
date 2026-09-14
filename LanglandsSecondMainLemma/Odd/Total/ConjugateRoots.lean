import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsSecondMainLemma.Odd.Total.ASCoordinate
import LanglandsSecondMainLemma.Local.Newton

/-!
# Odd / Total / Actual conjugate roots

For every nonzero Teichmuller representative `xi`, this module constructs a
genuine conjugate of the exact Artin--Schreier coordinate in the form
`Delta + xi + eta`.  It records the exact binomial residual and the
quantitative Hensel bound `V - (p - 1) * t`; in equal characteristic the
correction `eta` is exactly zero.
-/

namespace LanglandsSecondMainLemma.Odd.Total

open Polynomial
open LanglandsFirstMainLemma

noncomputable section

private theorem natCast_ord_nonneg
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (n : ℕ) :
    0 ≤ ord L (n : L) := by
  exact (ord_nonneg_iff_mem_integer L _).2
    (show (n : L) ∈ ringOfIntegers L by
      exact (n : ringOfIntegers L).property)

private theorem pow_mem_lattice_int
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    {x : L} {q : ℤ} (hx : x ∈ lattice L q) (n : ℕ) :
    x ^ n ∈ lattice L ((n : ℤ) * q) := by
  rw [mem_lattice] at hx ⊢
  rw [ord_pow]
  have h := nsmul_le_nsmul_right hx n
  simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using h

private theorem ord_eq_zero_of_pow_eq_one
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    {x : L} {n : ℕ} (hn : 0 < n) (hx : x ^ n = 1) :
    ord L x = 0 := by
  have hxne : x ≠ 0 := by
    intro h
    subst x
    simp [Nat.ne_of_gt hn] at hx
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
    ((ord_ne_top_iff L).2 hxne)
  have hval := congrArg (ord L) hx
  rw [ord_pow, ord_one, ← hm, ← WithTop.coe_nsmul] at hval
  have hmzero : n • m = 0 := WithTop.coe_eq_zero.mp hval
  simp only [nsmul_eq_mul] at hmzero
  have : m = 0 :=
    (mul_eq_zero.mp hmzero).resolve_left
      (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hn))
  rw [← hm, this]
  rfl

private theorem shifted_artinSchreier_error
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    {p t : ℕ} (hp : p.Prime) {V : ℤ}
    (hV : ord L (p : L) = (V : WithTop ℤ))
    {Delta xi A : L}
    (hDelta : ord L Delta = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (hxi : xi ^ (p - 1) = 1)
    (hroot : Delta ^ p - Delta = A) :
    let error := (Delta + xi) ^ p - (Delta + xi) - A
    let correction := ∑ k ∈ Finset.Ioo 0 p,
      Delta ^ k * xi ^ (p - k) * ((Nat.choose p k / p : ℕ) : L)
    error = (p : L) * correction ∧
      error ∈ lattice L (V - ((p - 1) * t : ℕ)) := by
  dsimp only
  let correction := ∑ k ∈ Finset.Ioo 0 p,
    Delta ^ k * xi ^ (p - k) * ((Nat.choose p k / p : ℕ) : L)
  have hxiord : ord L xi = 0 :=
    ord_eq_zero_of_pow_eq_one L (Nat.sub_pos_of_lt hp.one_lt) hxi
  have hcorr : correction ∈ lattice L (-(((p - 1) * t : ℕ) : ℤ)) := by
    apply sum_mem_lattice L
    intro k hk
    have hk' := Finset.mem_Ioo.mp hk
    have hDeltaMem : Delta ∈ lattice L (-(t : ℤ)) := by
      rw [mem_lattice, hDelta]
    have hDeltaPow : Delta ^ k ∈ lattice L (-((k * t : ℕ) : ℤ)) := by
      have h := pow_mem_lattice_int L hDeltaMem k
      convert h using 1
      push_cast
      ring
    have hDeltaPromote : Delta ^ k ∈
        lattice L (-(((p - 1) * t : ℕ) : ℤ)) :=
      lattice_antitone L (by
        have hnat : k * t ≤ (p - 1) * t :=
          Nat.mul_le_mul_right t (by omega)
        exact_mod_cast (Int.neg_le_neg (by exact_mod_cast hnat))) hDeltaPow
    have hxiPow : xi ^ (p - k) ∈ lattice L 0 := by
      rw [mem_lattice, ord_pow, hxiord]
      simp
    have hcoeff : ((Nat.choose p k / p : ℕ) : L) ∈ lattice L 0 := by
      rw [mem_lattice]
      exact natCast_ord_nonneg L _
    have hmul := mul_mem_lattice L
      (mul_mem_lattice L hDeltaPromote hxiPow) hcoeff
    simpa using hmul
  have hpcast : (p : L) ∈ lattice L V := by
    rw [mem_lattice, hV]
  have hbound : (p : L) * correction ∈
      lattice L (V - ((p - 1) * t : ℕ)) := by
    have hmul := mul_mem_lattice L hpcast hcorr
    convert hmul using 1
    push_cast
    ring
  have hxiP : xi ^ p = xi := by
    calc
      xi ^ p = xi ^ (p - 1 + 1) := by rw [Nat.sub_add_cancel hp.one_le]
      _ = xi ^ (p - 1) * xi := pow_succ _ _
      _ = xi := by rw [hxi, one_mul]
  have hformula := (Commute.all Delta xi).add_pow_prime_pow_eq' hp 1
  norm_num at hformula
  have heval : (Delta + xi) ^ p - (Delta + xi) - A =
      (p : L) * correction := by
    rw [hformula]
    dsimp only [correction]
    rw [hxiP]
    linear_combination hroot
  exact ⟨heval, heval ▸ hbound⟩

private theorem lift_shifted_artinSchreier_root
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    {p t : ℕ} (hp : p.Prime) {V : ℤ}
    (hV : ord L (p : L) = (V : WithTop ℤ))
    (hkappa : 0 < V - ((p - 1) * t : ℕ))
    {center A : L}
    (hcenter : ord L center = ((-(t : ℤ) : ℤ) : WithTop ℤ))
    (herror : ((V - ((p - 1) * t : ℕ) : ℤ) : WithTop ℤ) ≤
      ord L (center ^ p - center - A)) :
    ∃ eta : L,
      (center + eta) ^ p - (center + eta) = A ∧
      ((V - ((p - 1) * t : ℕ) : ℤ) : WithTop ℤ) ≤ ord L eta := by
  let H : L[X] := (X + C center) ^ p - (X + C center) - C A
  have hrespos : (0 : WithTop ℤ) < ord L (center ^ p - center - A) :=
    (WithTop.coe_lt_coe.mpr hkappa).trans_le herror
  have hHzero : H.coeff 0 = center ^ p - center - A := by
    simp [H, Polynomial.coeff_X_add_C_pow]
  have hHone : H.coeff 1 = center ^ (p - 1) * (p : L) - 1 := by
    simp [H, Polynomial.coeff_X_add_C_pow]
  have hlinearTermOrd :
      ord L (center ^ (p - 1) * (p : L)) =
        ((V - (((p - 1) * t : ℕ) : ℤ)) : WithTop ℤ) := by
    rw [ord_mul, ord_pow, hcenter, hV, ← WithTop.coe_nsmul, ← WithTop.coe_add]
    congr 1
    push_cast
    ring
  have hlinearTermPos : (0 : WithTop ℤ) <
      ord L (center ^ (p - 1) * (p : L)) := by
    rw [hlinearTermOrd]
    exact WithTop.coe_lt_coe.mpr hkappa
  have hHoneOrd : ord L (H.coeff 1) = 0 := by
    have hne : ord L (center ^ (p - 1) * (p : L)) ≠ ord L (-1) := by
      simpa using ne_of_gt hlinearTermPos
    rw [hHone, sub_eq_add_neg, ord_add_eq_min L hne, ord_neg, ord_one,
      min_eq_right hlinearTermPos.le]
  have hHcoeff : ∀ n : ℕ, 0 ≤ ord L (H.coeff n) := by
    intro n
    by_cases hn0 : n = 0
    · subst n
      rw [hHzero]
      exact hrespos.le
    by_cases hn1 : n = 1
    · subst n
      rw [hHoneOrd]
    by_cases hnp : n < p
    · have hcoeff : H.coeff n = center ^ (p - n) * (p.choose n : L) := by
        simp [H, Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X,
          Polynomial.coeff_C, hn0, Ne.symm hn1]
      obtain ⟨q, hq⟩ := hp.dvd_choose_self hn0 hnp
      have hchoose : (p.choose n : L) = (p : L) * (q : L) := by
        rw [hq]
        norm_num
      have hbaseOrd : ord L (center ^ (p - n) * (p : L)) =
          ((V - (((p - n) * t : ℕ) : ℤ)) : WithTop ℤ) := by
        rw [ord_mul, ord_pow, hcenter, hV, ← WithTop.coe_nsmul,
          ← WithTop.coe_add]
        congr 1
        push_cast
        ring
      rw [hcoeff, hchoose, ← mul_assoc, ord_mul, hbaseOrd]
      apply add_nonneg
      · apply WithTop.coe_nonneg.mpr
        have hsuble : p - n ≤ p - 1 := by omega
        have hmul : (p - n) * t ≤ (p - 1) * t :=
          Nat.mul_le_mul_right t hsuble
        have hmulZ : ((((p - n) * t : ℕ) : ℤ)) ≤
            (((p - 1) * t : ℕ) : ℤ) := by exact_mod_cast hmul
        omega
      · exact natCast_ord_nonneg L q
    by_cases hnpEq : n = p
    · subst n
      simp [H, Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X,
        Polynomial.coeff_C, hp.ne_zero, hp.ne_one.symm]
    · have hpn : p < n := by omega
      simp [H, Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X,
        Polynomial.coeff_C, hn0, Ne.symm hn1, Nat.choose_eq_zero_of_lt hpn]
  let i : ringOfIntegers L →+* L :=
    (ValuativeRel.valuation L).integer.subtype
  have hHrange : H ∈ (Polynomial.mapRingHom i).range := by
    rw [Polynomial.mem_map_range]
    intro n
    exact ⟨⟨H.coeff n, (ord_nonneg_iff_mem_integer L _).1 (hHcoeff n)⟩, rfl⟩
  obtain ⟨h, hh⟩ := hHrange
  have hhcoeff (n : ℕ) : i (h.coeff n) = H.coeff n := by
    calc
      i (h.coeff n) = (h.map i).coeff n := by rw [Polynomial.coeff_map]
      _ = H.coeff n := congrArg (fun f : L[X] ↦ f.coeff n) hh
  have hderiv : ord L ((h.derivative.eval 0 : ringOfIntegers L) : L) =
      (0 : WithTop ℤ) := by
    have heval : h.derivative.eval 0 = h.coeff 1 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
      simp
    rw [heval]
    change ord L (i (h.coeff 1)) = (0 : WithTop ℤ)
    rw [hhcoeff, hHoneOrd]
  have hres : ((2 * (0 : ℤ) : ℤ) : WithTop ℤ) <
      ord L ((h.eval 0 : ringOfIntegers L) : L) := by
    have heval : i (h.eval 0) = H.coeff 0 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, hhcoeff]
    change (0 : WithTop ℤ) < ord L (i (h.eval 0))
    rw [heval, hHzero]
    exact hrespos
  obtain ⟨z, hz, _hzpos, hzbound, _hzunique⟩ :=
    Local.newton h 0 0 hderiv hres
  have hHroot : H.eval (z : L) = 0 := by
    calc
      H.eval (z : L) = (Polynomial.mapRingHom i h).eval (i z) := by
        simpa [i] using congrArg (fun f : L[X] ↦ f.eval (z : L)) hh.symm
      _ = i (h.eval z) := Polynomial.eval_map_apply i z
      _ = 0 := by rw [hz, map_zero]
  have hroot : (center + (z : L)) ^ p - (center + (z : L)) = A := by
    have hHroot' : ((z : L) + center) ^ p - ((z : L) + center) - A = 0 := by
      simpa [H] using hHroot
    rw [add_comm]
    linear_combination hHroot'
  have hquant : ((V - ((p - 1) * t : ℕ) : ℤ) : WithTop ℤ) ≤
      ord L (z : L) := by
    apply herror.trans
    have heval : i (h.eval 0) = H.coeff 0 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, hhcoeff]
    have hzbound' : ord L (i (h.eval 0)) ≤ ord L ((z : L) - (0 : L)) := by
      change ord L ((h.eval 0 : ringOfIntegers L) : L) ≤
        ord L ((z : L) - (0 : L))
      simpa using hzbound
    rw [heval, hHzero, sub_zero] at hzbound'
    exact hzbound'
  exact ⟨z, hroot, hquant⟩

private theorem artinSchreier_root_is_conjugate
    (E L : Type*) [Field E] [Field L] [Algebra E L]
    [Module.Finite E L] [IsGalois E L]
    {p : ℕ} (hp : p.Prime)
    (hdegree : Module.finrank E L = p)
    (Delta : L) (A : E)
    (hgen : Algebra.adjoin E ({Delta} : Set L) = ⊤)
    {x : L}
    (hDeltaRoot : Delta ^ p - Delta = algebraMap E L A)
    (hxRoot : x ^ p - x = algebraMap E L A) :
    ∃ sigma : Gal(L/E), sigma Delta = x := by
  let P : E[X] := X ^ p - X - C A
  have hlow : (X + C A : E[X]).degree < (X ^ p : E[X]).degree := by
    rw [degree_X_pow]
    apply (degree_add_le _ _).trans_lt
    rw [max_lt_iff]
    constructor
    · simpa using (show (1 : WithBot ℕ) < (p : ℕ) by exact_mod_cast hp.one_lt)
    · exact degree_C_le.trans_lt
        (show (0 : WithBot ℕ) < (p : ℕ) by exact_mod_cast hp.pos)
  have hPform : P = X ^ p - (X + C A) := by
    dsimp only [P]
    ring
  have hPmonic : P.Monic := by
    rw [hPform]
    exact (monic_X_pow p).sub_of_left hlow
  have hPnat : P.natDegree = p := by
    apply natDegree_eq_of_degree_eq_some
    rw [hPform, degree_sub_eq_left_of_degree_lt hlow, degree_X_pow]
  have hDeltaEval : Polynomial.aeval Delta P = 0 := by
    simp only [P, map_sub, map_pow, aeval_X, aeval_C]
    linear_combination hDeltaRoot
  let pb : PowerBasis E L :=
    PowerBasis.ofAdjoinEqTop (IsAlgebraic.of_finite E Delta).isIntegral hgen
  have hpbdim : pb.dim = p := by
    rw [← PowerBasis.finrank pb]
    exact hdegree
  have hminDegree : (minpoly E Delta).natDegree = p := by
    rw [show (minpoly E Delta).natDegree = pb.dim by
      simpa only [pb, PowerBasis.ofAdjoinEqTop_gen] using
        PowerBasis.natDegree_minpoly pb]
    exact hpbdim
  have hminEq : P = minpoly E Delta := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic (IsAlgebraic.of_finite E Delta).isIntegral) hPmonic
    · exact minpoly.dvd E Delta hDeltaEval
    · rw [hPnat, hminDegree]
  have hxEval : Polynomial.aeval x (minpoly E Delta) = 0 := by
    rw [← hminEq]
    simp only [P, map_sub, map_pow, aeval_X, aeval_C]
    linear_combination hxRoot
  exact minpoly.exists_algEquiv_of_root'
    (IsAlgebraic.of_finite E Delta) hxEval

variable {F K : Type*} [Field F] [Field K]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Algebra F K] [ValuativeExtension F K]
variable [Module.Free F K] [Module.Finite F K] [IsGalois F K]

/-- For every nonzero Teichmuller representative in the lower field, an
exact Artin--Schreier coordinate has an actual Galois conjugate of the form
`Delta + xi + eta`.  In equal characteristic the correction is zero.  In
mixed characteristic both the shifted-polynomial residual and `eta` have
the paper's depth `V - (p-1)t`; the displayed finite sum is the exact
binomial residual before Hensel lifting. -/
theorem oddAS_actualConjugates_of_coordinate {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = p)
    (D : OddTotalBreakData (F := F) (K := K) hp hG) :
    let B₂ := D.B₂
    letI : ValuativeRel B₂ := Basic.intermediateFieldValuativeRel B₂
    letI : TopologicalSpace B₂ := Basic.intermediateFieldTopology B₂
    letI : IsNonarchimedeanLocalField B₂ := Basic.intermediateField_localField B₂
    ∀ (Delta : K) (a : B₂),
      Delta ^ p - Delta = algebraMap B₂ K a →
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) →
      Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ →
      ∀ xi : B₂, xi ^ (p - 1) = 1 →
        ∃ (sigma : Gal(K/B₂)) (eta : K),
          sigma Delta = Delta + algebraMap B₂ K xi + eta ∧
          (Delta + algebraMap B₂ K xi + eta) ^ p -
              (Delta + algebraMap B₂ K xi + eta) = algebraMap B₂ K a ∧
          (Delta + algebraMap B₂ K xi) ^ p -
              (Delta + algebraMap B₂ K xi) - algebraMap B₂ K a =
            (p : K) * ∑ k ∈ Finset.Ioo 0 p,
              Delta ^ k * (algebraMap B₂ K xi) ^ (p - k) *
                ((Nat.choose p k / p : ℕ) : K) ∧
          (((p : K) = 0 ∧ eta = 0) ∨
            ((p : K) ≠ 0 ∧ ∃ V : ℤ,
              ord K (p : K) = (V : WithTop ℤ) ∧
              ((V - ((p - 1) * D.t : ℕ) : ℤ) : WithTop ℤ) ≤
                ord K ((Delta + algebraMap B₂ K xi) ^ p -
                  (Delta + algebraMap B₂ K xi) - algebraMap B₂ K a) ∧
              ((V - ((p - 1) * D.t : ℕ) : ℤ) : WithTop ℤ) ≤ ord K eta)) := by
  dsimp only [OddTotalBreakData.B₂]
  letI : ValuativeRel (IntermediateField.fixedField D.H₂) :=
    Basic.intermediateFieldValuativeRel (IntermediateField.fixedField D.H₂)
  letI : TopologicalSpace (IntermediateField.fixedField D.H₂) :=
    Basic.intermediateFieldTopology (IntermediateField.fixedField D.H₂)
  obtain ⟨hLocal, hFreeFB₂, hFiniteFB₂, hFreeB₂K, hFiniteB₂K, hScalar,
      hValFB₂, hValB₂K, _htotal, _hdegreeLower, hdegreeUpper,
      _hcycFB₂, hcycB₂K⟩ :=
    Basic.intermediateField_tower_compatible hp hG
      (IntermediateField.fixedField D.H₂) D.degree_B₂
  letI : IsNonarchimedeanLocalField (IntermediateField.fixedField D.H₂) := hLocal
  letI : Module.Free F (IntermediateField.fixedField D.H₂) := hFreeFB₂
  letI : Module.Finite F (IntermediateField.fixedField D.H₂) := hFiniteFB₂
  letI : Module.Free (IntermediateField.fixedField D.H₂) K := hFreeB₂K
  letI : Module.Finite (IntermediateField.fixedField D.H₂) K := hFiniteB₂K
  letI : IsScalarTower F (IntermediateField.fixedField D.H₂) K := hScalar
  letI : ValuativeExtension F (IntermediateField.fixedField D.H₂) := hValFB₂
  letI : ValuativeExtension (IntermediateField.fixedField D.H₂) K := hValB₂K
  letI : IsGalois (IntermediateField.fixedField D.H₂) K := hcycB₂K.1
  intro Delta a hDeltaRoot hDeltaOrd hgen xi hxi
  let xiK : K :=
    algebraMap (IntermediateField.fixedField D.H₂) K xi
  have hxiK : xiK ^ (p - 1) = 1 := by
    dsimp only [xiK]
    rw [← map_pow, hxi, map_one]
  have hxiOrd : ord K xiK = 0 :=
    ord_eq_zero_of_pow_eq_one K (Nat.sub_pos_of_lt hp.one_lt) hxiK
  have hcenterOrd : ord K (Delta + xiK) =
      ((-(D.t : ℤ) : ℤ) : WithTop ℤ) := by
    have htposZ : (0 : ℤ) < (D.t : ℤ) := by exact_mod_cast D.t_pos
    have htneg : -(D.t : ℤ) < 0 := neg_neg_of_pos htposZ
    have hne : ord K Delta ≠ ord K xiK := by
      rw [hDeltaOrd, hxiOrd]
      exact ne_of_lt (WithTop.coe_lt_coe.mpr htneg)
    rw [ord_add_eq_min K hne, hDeltaOrd, hxiOrd]
    exact min_eq_left (WithTop.coe_le_coe.mpr htneg.le)
  by_cases hpzero : (p : K) = 0
  · letI : Fact p.Prime := ⟨hp⟩
    letI : CharP K p := (CharP.charP_iff_prime_eq_zero hp).mpr hpzero
    have hxiKP : xiK ^ p = xiK := by
      calc
        xiK ^ p = xiK ^ (p - 1 + 1) := by
          rw [Nat.sub_add_cancel hp.one_le]
        _ = xiK ^ (p - 1) * xiK := pow_succ _ _
        _ = xiK := by rw [hxiK, one_mul]
    have hcenterRoot : (Delta + xiK) ^ p - (Delta + xiK) =
        algebraMap (IntermediateField.fixedField D.H₂) K a := by
      rw [add_pow_char, hxiKP]
      linear_combination hDeltaRoot
    obtain ⟨sigma, hsigma⟩ := artinSchreier_root_is_conjugate
      (IntermediateField.fixedField D.H₂) K hp hdegreeUpper Delta a hgen
        hDeltaRoot hcenterRoot
    refine ⟨sigma, 0, ?_, ?_, ?_, Or.inl ⟨hpzero, rfl⟩⟩
    · simpa [xiK] using hsigma
    · simpa [xiK] using hcenterRoot
    · have heval : (Delta + xiK) ^ p - (Delta + xiK) -
          algebraMap (IntermediateField.fixedField D.H₂) K a = 0 := by
        linear_combination hcenterRoot
      rw [hpzero, zero_mul]
      simpa only [xiK] using heval
  · obtain ⟨V, hVraw⟩ := WithTop.ne_top_iff_exists.mp
      ((ord_ne_top_iff K).2 hpzero)
    have hV : ord K (p : K) = (V : WithTop ℤ) := hVraw.symm
    have hprimeBound := oddTotal_primeValuationBound hp hG hres D
    rw [hV] at hprimeBound
    have hprimeBoundZ :
        (((p * (p - 1) * D.t₂ : ℕ) : ℤ)) ≤ V :=
      WithTop.coe_le_coe.mp hprimeBound
    have hsmall : (p - 1) * D.t < p * (p - 1) * D.t₂ := by
      have hpos : 0 < (p - 1) * D.t :=
        Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) D.t_pos
      have hle : (p - 1) * D.t ≤ (p - 1) * D.t₂ :=
        Nat.mul_le_mul_left (p - 1) D.t_le_t₂
      have hdouble : 2 * ((p - 1) * D.t) ≤
          p * ((p - 1) * D.t₂) :=
        Nat.mul_le_mul D.odd_prime.le hle
      calc
        (p - 1) * D.t < 2 * ((p - 1) * D.t) := by omega
        _ ≤ p * ((p - 1) * D.t₂) := hdouble
        _ = p * (p - 1) * D.t₂ := by ring
    have hkappa : 0 < V - ((p - 1) * D.t : ℕ) := by
      have hcast : (((p - 1) * D.t : ℕ) : ℤ) <
          ((p * (p - 1) * D.t₂ : ℕ) : ℤ) := by exact_mod_cast hsmall
      omega
    obtain ⟨heval, herrMem⟩ := shifted_artinSchreier_error K hp hV
      hDeltaOrd hxiK hDeltaRoot
    have herr : ((V - ((p - 1) * D.t : ℕ) : ℤ) : WithTop ℤ) ≤
        ord K ((Delta + xiK) ^ p - (Delta + xiK) -
          algebraMap (IntermediateField.fixedField D.H₂) K a) := by
      exact (mem_lattice K).1 herrMem
    obtain ⟨eta, hetaRoot, hetaBound⟩ :=
      lift_shifted_artinSchreier_root K hp hV hkappa hcenterOrd herr
    obtain ⟨sigma, hsigma⟩ := artinSchreier_root_is_conjugate
      (IntermediateField.fixedField D.H₂) K hp hdegreeUpper Delta a hgen
        hDeltaRoot hetaRoot
    refine ⟨sigma, eta, ?_, ?_, ?_, Or.inr ⟨hpzero, V, hV, ?_, hetaBound⟩⟩
    · simpa only [xiK, add_assoc] using hsigma
    · simpa only [xiK, add_assoc] using hetaRoot
    · simpa only [xiK] using heval
    · simpa only [xiK] using herr


/-- Preserve the original existential API by choosing its coordinate first and
then applying the conjugate construction for that very coordinate. -/
theorem oddAS_actualConjugates {p : ℕ} (hp : p.Prime)
    (hG : Nonempty
      (Gal(K/F) ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))))
    (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = p)
    (D : OddTotalBreakData (F := F) (K := K) hp hG) :
    let B₂ := D.B₂
    letI : ValuativeRel B₂ := Basic.intermediateFieldValuativeRel B₂
    letI : TopologicalSpace B₂ := Basic.intermediateFieldTopology B₂
    letI : IsNonarchimedeanLocalField B₂ := Basic.intermediateField_localField B₂
    ∃ (Delta : K) (a : B₂),
      Delta ^ p - Delta = algebraMap B₂ K a ∧
      ord K Delta = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ord B₂ a = ((-(D.t : ℤ) : ℤ) : WithTop ℤ) ∧
      ¬ p ∣ D.t ∧
      Algebra.adjoin B₂ ({Delta} : Set K) = ⊤ ∧
      ∀ xi : B₂, xi ^ (p - 1) = 1 →
        ∃ (sigma : Gal(K/B₂)) (eta : K),
          sigma Delta = Delta + algebraMap B₂ K xi + eta ∧
          (Delta + algebraMap B₂ K xi + eta) ^ p -
              (Delta + algebraMap B₂ K xi + eta) = algebraMap B₂ K a ∧
          (Delta + algebraMap B₂ K xi) ^ p -
              (Delta + algebraMap B₂ K xi) - algebraMap B₂ K a =
            (p : K) * ∑ k ∈ Finset.Ioo 0 p,
              Delta ^ k * (algebraMap B₂ K xi) ^ (p - k) *
                ((Nat.choose p k / p : ℕ) : K) ∧
          (((p : K) = 0 ∧ eta = 0) ∨
            ((p : K) ≠ 0 ∧ ∃ V : ℤ,
              ord K (p : K) = (V : WithTop ℤ) ∧
              ((V - ((p - 1) * D.t : ℕ) : ℤ) : WithTop ℤ) ≤
                ord K ((Delta + algebraMap B₂ K xi) ^ p -
                  (Delta + algebraMap B₂ K xi) - algebraMap B₂ K a) ∧
              ((V - ((p - 1) * D.t : ℕ) : ℤ) : WithTop ℤ) ≤ ord K eta)) := by
  dsimp only [OddTotalBreakData.B₂]
  letI : ValuativeRel (IntermediateField.fixedField D.H₂) :=
    Basic.intermediateFieldValuativeRel (IntermediateField.fixedField D.H₂)
  letI : TopologicalSpace (IntermediateField.fixedField D.H₂) :=
    Basic.intermediateFieldTopology (IntermediateField.fixedField D.H₂)
  obtain ⟨hLocal, hFreeFB₂, hFiniteFB₂, hFreeB₂K, hFiniteB₂K, hScalar,
      hValFB₂, hValB₂K, _htotal, _hdegreeLower, hdegreeUpper,
      _hcycFB₂, hcycB₂K⟩ :=
    Basic.intermediateField_tower_compatible hp hG
      (IntermediateField.fixedField D.H₂) D.degree_B₂
  letI : IsNonarchimedeanLocalField (IntermediateField.fixedField D.H₂) := hLocal
  letI : Module.Free F (IntermediateField.fixedField D.H₂) := hFreeFB₂
  letI : Module.Finite F (IntermediateField.fixedField D.H₂) := hFiniteFB₂
  letI : Module.Free (IntermediateField.fixedField D.H₂) K := hFreeB₂K
  letI : Module.Finite (IntermediateField.fixedField D.H₂) K := hFiniteB₂K
  letI : IsScalarTower F (IntermediateField.fixedField D.H₂) K := hScalar
  letI : ValuativeExtension F (IntermediateField.fixedField D.H₂) := hValFB₂
  letI : ValuativeExtension (IntermediateField.fixedField D.H₂) K := hValB₂K
  letI : IsGalois (IntermediateField.fixedField D.H₂) K := hcycB₂K.1
  have hcoordinate := aSCoordinate hp hG hres hchar D
  dsimp only [OddTotalBreakData.B₂] at hcoordinate
  obtain ⟨Delta, a, hDeltaRoot, hDeltaOrd, haOrd, hprime, hgen⟩ := hcoordinate
  refine ⟨Delta, a, hDeltaRoot, hDeltaOrd, haOrd, hprime, hgen, ?_⟩
  have hconj := oddAS_actualConjugates_of_coordinate hp hG hres hchar D
  dsimp only [OddTotalBreakData.B₂] at hconj
  exact hconj Delta a hDeltaRoot hDeltaOrd hgen

end

end LanglandsSecondMainLemma.Odd.Total
