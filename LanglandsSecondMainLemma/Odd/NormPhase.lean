import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsSecondMainLemma.Odd.NormLog

/-!
# Odd / Norm Phase

This is the whole-subgroup conversion of Paper Corollary 6.4
(`O:I:conversion`).  For a ramified prime-cyclic edge of positive break
`t`, put `T = t + 1` and `q₀ = ⌈T / p⌉`.  The supplied chart is the
paper's chart for the actual nontrivial norm character,

`tau (1 - z) = PsiF (P z)` on `𝐭_F^q₀`.

Surjectivity of the truncated logarithm writes every `w ∈ 𝐭_K^q₀`
as `P z`.  The full norm-log identity then shows that
`P(1 - N(1-z))` differs from `Tr(w) + N(w)` by an element of
`𝐭_F^T`.  The paper's exact additive-conductor hypothesis says that
`PsiF` is trivial on that entire lattice.  This gives both displayed
identities, with the paper's negative norm sign in the second one.
-/

namespace LanglandsSecondMainLemma.Odd

noncomputable section

open LanglandsFirstMainLemma

/-- **Whole-subgroup norm-phase conversion** (Paper Corollary 6.4,
`O:I:conversion`).

Let `K/F` be a totally ramified prime-cyclic edge with positive lower
break `t`, prime degree `p`, and `q = ⌈(t+1)/p⌉`.  Let `tau` be a
nontrivial actual norm character.  Suppose `PsiF` realizes `tau` on the
full truncated-logarithm chart at depth `q`:

`tau(1-x) = PsiF(P(x))` for every `x ∈ 𝐭_F^q`.

Then, for every `w ∈ 𝐭_K^q`,

* `PsiF(Tr(w) + N(w)) = 1`, and
* the trace pullback `PsiK` satisfies `PsiK(w) = PsiF(-N(w))`.

The parameter `q` is retained together with its defining equality so the
chart is expressed using FML's proof-bearing `positiveUnitOfLattice`.
The equality `hq` fixes it to the paper's depth; it is not an auxiliary
choice. -/
theorem normPhase
    (F K : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t) (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = Module.finrank F K)
    (hodd : Module.finrank F K ≠ 2)
    (q : ℕ) (hq : q = (t + 1) ⌈/⌉ Module.finrank F K) (hqpos : 0 < q)
    (tau : NormCharacter F K) (_htau : tau ≠ 1)
    (PsiF : ContinuousAddChar F)
    (hPsi : IsAdditiveConductor F PsiF (-((t + 1 : ℕ) : ℤ)))
    (hchart : ∀ x : lattice F (q : ℤ),
      tau.1 (positiveUnitOfLattice F hqpos (-x)) =
        PsiF (truncatedLog (Module.finrank F K) (x : F)))
    (w : K) (hw : w ∈ lattice K (q : ℤ)) :
    PsiF (trace F K w + norm F K w) = 1 ∧
      tracePullbackAddChar F K PsiF w = PsiF (-norm F K w) := by
  classical
  let p : ℕ := Module.finrank F K
  let T : ℕ := t + 1
  have hp : p.Prime := PrimeCyclicExtension.degree_prime F K
  have hpge : 3 ≤ p := by
    have hp2 := hp.two_le
    omega
  have hqt : q ≤ t := by
    rw [hq, ceilDiv_le_iff_le_mul hp.pos]
    calc
      t + 1 ≤ 3 * t := by omega
      _ ≤ p * t := Nat.mul_le_mul_right t hpge
  have hcharK : residueCharacteristic K = p :=
    (residueCharacteristic_extension_eq F K).trans (by simpa [p] using hchar)

  obtain ⟨pi, hpi, hgen⟩ := monogenicUniformizer F K hres

  -- This is the whole-lattice triviality supplied by the paper's statement
  -- that `𝐭_F^T` is the largest triviality ideal of `PsiF`.
  have hPsiT : AddCharTrivialOnLattice F PsiF (T : ℤ) := by
    simpa [T] using hPsi.trivial

  -- Surjectivity of `P` on the specified upper ideal supplies the `z`
  -- used in the paper proof.
  obtain ⟨z, hzw⟩ :=
    (truncatedLogOnLattice_bijective K p q hcharK hp hqpos).2
      (⟨w, hw⟩ : lattice K (q : ℤ))
  have hPz : truncatedLog p (z : K) = w := by
    exact congrArg Subtype.val hzw

  -- The unit `1-z` lies in `U_K^q`, and below-break norm containment
  -- puts its actual field norm in `U_F^q`.
  let uz : unitFiltration K q := positiveUnitOfLattice K hqpos (-z)
  have hnuz : normUnits F K (uz : Kˣ) ∈ unitFiltration F q :=
    normMapsUnitFiltration_belowBreak F K ht hqt hres pi hpi hgen
      (uz : Kˣ) uz.property
  have hnuzCoe :
      (normUnits F K (uz : Kˣ) : F) = norm F K (1 - (z : K)) := by
    simp [uz, sub_eq_add_neg]

  let y : F := 1 - norm F K (1 - (z : K))
  have hnuzDisp :
      (normUnits F K (uz : Kˣ) : F) - 1 ∈ lattice F (q : ℤ) := by
    have hdisp := (mem_unitFiltration_succ_iff_sub_mem_lattice F (q - 1)
      (normUnits F K (uz : Kˣ))).1 (by
        have hqpred : q - 1 + 1 = q := by omega
        simpa only [hqpred] using hnuz)
    have hqpredZ : (((q - 1 + 1 : ℕ) : ℤ)) = (q : ℤ) := by omega
    rw [hqpredZ] at hdisp
    exact hdisp
  have hy : y ∈ lattice F (q : ℤ) := by
    have hneg := neg_mem_lattice F hnuzDisp
    rw [hnuzCoe] at hneg
    simpa [y] using hneg
  let yq : lattice F (q : ℤ) := ⟨y, hy⟩

  -- `1-y = N(1-z)` as actual units, so the norm character is one there.
  have hyUnit :
      (positiveUnitOfLattice F hqpos (-yq) : Fˣ) =
        normUnits F K (uz : Kˣ) := by
    apply Units.ext
    simp only [coe_positiveUnitOfLattice, Submodule.coe_neg, yq]
    rw [hnuzCoe]
    simp [y]
  have htauNorm : tau.1 (positiveUnitOfLattice F hqpos (-yq)) = 1 := by
    rw [hyUnit]
    exact tau.eq_one_on_normRange F K _ ⟨(uz : Kˣ), rfl⟩
  have hPy : PsiF (truncatedLog p y) = 1 := by
    have hc := hchart yq
    rw [htauNorm] at hc
    exact (by simpa only [yq] using hc.symm)

  -- The full norm-log congruence has precisely the required trace, norm,
  -- and sign conventions.
  have hlog := normLog F K ht htpos hres hchar hodd 0 (z : K) (by
    simpa only [zero_add, ← hq] using z.property)
  have herr :
      truncatedLog p y - trace F K w - norm F K w ∈ lattice F (T : ℤ) := by
    simpa only [p, T, y, hPz] using hlog
  have herrorPhase :
      PsiF (truncatedLog p y - trace F K w - norm F K w) = 1 :=
    hPsiT _ herr

  have hsum : PsiF (trace F K w + norm F K w) = 1 := by
    have hquot :
        PsiF (truncatedLog p y) /
            PsiF (trace F K w + norm F K w) = 1 := by
      calc
        PsiF (truncatedLog p y) /
              PsiF (trace F K w + norm F K w) =
            PsiF (truncatedLog p y - (trace F K w + norm F K w)) :=
          (PsiF.toAddChar.map_sub_eq_div _ _).symm
        _ = PsiF (truncatedLog p y - trace F K w - norm F K w) := by
          congr 1
          ring
        _ = 1 := herrorPhase
    exact (div_eq_one.mp hquot).symm.trans hPy

  refine ⟨hsum, ?_⟩
  rw [tracePullbackAddChar_apply]
  apply div_eq_one.mp
  calc
    PsiF (trace F K w) / PsiF (-norm F K w) =
        PsiF (trace F K w - (-norm F K w)) :=
      (PsiF.toAddChar.map_sub_eq_div _ _).symm
    _ = PsiF (trace F K w + norm F K w) := by
      congr 1
      ring
    _ = 1 := hsum

end

end LanglandsSecondMainLemma.Odd
