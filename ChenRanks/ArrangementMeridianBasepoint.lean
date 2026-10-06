import ChenRanks.AffinePivotQuotient
import Mathlib.Algebra.MvPolynomial.Funext

/-! Uncompiled source preparation, outside the active Lean inventory.

The basepoint is constructed on the actual distinguished hyperplane and
outside every other actual hyperplane. A finite product in its proved
pivot-coordinate ring is nonzero; polynomial function extensionality
over the actual infinite field then supplies a genuine complex point.
No generic basepoint, avoidance, or normal direction is assumed.
-/

noncomputable section

namespace ChenRanks

open scoped BigOperators

/-- A finite family of genuinely nonzero multivariate polynomials over
an infinite field has a simultaneous nonzero evaluation. -/
theorem mvPolynomial_exists_simultaneous_nonzero_evaluation
    (k σ ι : Type*) [Field k] [Infinite k] [Fintype ι]
    (p : ι → MvPolynomial σ k) (hp : ∀ i, p i ≠ 0) :
    ∃ y : σ → k, ∀ i, MvPolynomial.eval y (p i) ≠ 0 := by
  classical
  let q : MvPolynomial σ k := ∏ i, p i
  have hq : q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  obtain ⟨y, hy⟩ : ∃ y : σ → k, MvPolynomial.eval y q ≠ 0 := by
    by_contra h
    have hz : ∀ y : σ → k, MvPolynomial.eval y q = 0 :=
      fun y => not_not.mp ((not_exists.mp h) y)
    apply hq
    apply MvPolynomial.funext
    intro y
    simpa only [map_zero] using hz y
  refine ⟨y, ?_⟩
  have hp' : (∏ i, MvPolynomial.eval y (p i)) ≠ 0 := by
    simpa only [q, map_prod] using hy
  exact fun i => (Finset.prod_ne_zero_iff.mp hp') i (Finset.mem_univ i)

namespace AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- Evaluate the actual original coordinates through the proved pivot
restriction. This is an actual point of the original affine space. -/
def hyperplanePivotPoint (H : ι) (j : Fin d)
    (y : {i : Fin d // i ≠ j} → ℂ) : Fin d → ℂ :=
  fun i => MvPolynomial.eval y
    (A.hyperplanePivotRestriction H j (MvPolynomial.X i))

/-- Evaluation at that actual point commutes with the actual original
polynomial restriction, by the universal property on C and X. -/
theorem hyperplanePivotPoint_eval (H : ι) (j : Fin d)
    (y : {i : Fin d // i ≠ j} → ℂ) (p : CoordinateRing (d := d)) :
    MvPolynomial.eval (A.hyperplanePivotPoint H j y) p =
      MvPolynomial.eval y (A.hyperplanePivotRestriction H j p) := by
  have heq : (MvPolynomial.eval y).comp
      (A.hyperplanePivotRestriction H j).toRingHom =
        MvPolynomial.eval (A.hyperplanePivotPoint H j y) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        hyperplanePivotRestriction, affinePivotRestriction_C, MvPolynomial.eval_C]
    · intro i
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        MvPolynomial.eval_X, hyperplanePivotPoint]
  exact (RingHom.congr_fun heq p).symm

/-- The original distinctness of the actual hyperplanes, not an
assumed general-position condition, supplies an actual meridian center. -/
theorem exists_actual_meridian_center (H : ι) :
    ∃ x : Fin d → ℂ, A.normal H x = A.offset H ∧
      ∀ K : ι, K ≠ H → A.normal K x ≠ A.offset K := by
  classical
  obtain ⟨j, hj⟩ := A.exists_hyperplanePivot H
  let p : {K : ι // K ≠ H} → HyperplanePivotRing j :=
    fun K => A.hyperplanePivotRestriction H j (A.equationPolynomial K)
  have hp : ∀ K, p K ≠ 0 := by
    intro K hzero
    have hmem : A.equationPolynomial K ∈
        RingHom.ker (A.hyperplanePivotRestriction H j) := hzero
    rw [A.hyperplanePivotRestriction_ker H j hj] at hmem
    exact A.equationPolynomial_not_mem_hyperplanePrimeIdeal H K
      (Ne.symm K.property) hmem
  obtain ⟨y, hy⟩ := mvPolynomial_exists_simultaneous_nonzero_evaluation
    ℂ {i : Fin d // i ≠ j} {K : ι // K ≠ H} p hp
  let x := A.hyperplanePivotPoint H j y
  refine ⟨x, ?_, ?_⟩
  · have hz : MvPolynomial.eval x (A.equationPolynomial H) = 0 := by
      rw [hyperplanePivotPoint_eval, A.hyperplanePivotRestriction_equation H j hj,
        map_zero]
    rw [A.equationPolynomial_eval H x] at hz
    exact sub_eq_zero.mp hz
  · intro K hKH
    have hz := hy ⟨K, hKH⟩
    change MvPolynomial.eval y
      (A.hyperplanePivotRestriction H j (A.equationPolynomial K)) ≠ 0 at hz
    rw [← A.hyperplanePivotPoint_eval H j y (A.equationPolynomial K),
      A.equationPolynomial_eval K] at hz
    exact sub_ne_zero.mp hz

/-- The same nonzero original normal has an actual transverse vector
on which its value is one. -/
theorem exists_actual_meridian_normal_vector (H : ι) :
    ∃ n : Fin d → ℂ, A.normal H n = 1 := by
  classical
  obtain ⟨j, hj⟩ := A.exists_hyperplanePivot H
  refine ⟨(A.normal H (Pi.single j 1))⁻¹ • Pi.single j 1, ?_⟩
  rw [map_smul, smul_eq_mul]
  exact inv_mul_cancel₀ hj

end AffineArrangement

end ChenRanks
