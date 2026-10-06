import ChenRanks.AffinePivotQuotient
import ChenRanks.ArrangementParallelRelations
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic
import Mathlib.Tactic.LinearCombination

/-!
# Actual degree-one restrictions at an original affine hyperplane

The genuine pivot quotient already identifies its kernel with the
original hyperplane principal ideal. Total degree then identifies its
degree-at-most-one part with the constant multiples of the original
equation. Applied to a difference of two original equations, this gives
the actual affine rank-two relation, retaining every affine constant.

This is neither the full quadratic-kernel reverse inclusion nor a
comparison with topological cup products.
-/

noncomputable section

namespace ChenRanks

section LowDegree

variable {k σ : Type*} [Field k]

/-- Divisibility of a polynomial of degree at most one by a genuine
degree-one polynomial has a constant quotient. -/
theorem constant_multiple_of_degree_one_dvd
    (h p : MvPolynomial σ k) (hh : h.totalDegree = 1)
    (hp : p.totalDegree ≤ 1) (hdvd : h ∣ p) :
    ∃ c : k, p = MvPolynomial.C c * h := by
  classical
  have hn : h ≠ 0 := by
    intro hz
    simp only [hz, MvPolynomial.totalDegree_zero] at hh
    omega
  obtain ⟨q, rfl⟩ := hdvd
  by_cases hq : q = 0
  · subst q
    exact ⟨0, by simp⟩
  have hdegree := MvPolynomial.totalDegree_mul_of_isDomain hn hq
  have hqdegree : q.totalDegree = 0 := by omega
  refine ⟨q.coeff 0, ?_⟩
  calc
    h * q = h * MvPolynomial.C (q.coeff 0) :=
      congrArg (fun r : MvPolynomial σ k ↦ h * r)
        ((MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hqdegree)
    _ = MvPolynomial.C (q.coeff 0) * h := mul_comm h (MvPolynomial.C (q.coeff 0))

end LowDegree

namespace AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The actual pivot restriction preserves literal constant polynomials. -/
@[simp]
theorem hyperplanePivotRestriction_C (H : ι) (j : Fin d) (c : ℂ) :
    A.hyperplanePivotRestriction H j (MvPolynomial.C c) = MvPolynomial.C c :=
  affinePivotRestriction_C ℂ (Fin d) j (A.hyperplanePivotValue H j) c

/-- The actual low-degree restriction kernel consists exactly of the
constant multiples of the actual original hyperplane equation. -/
theorem hyperplanePivotRestriction_lowDegree_eq_zero_iff
    (H : ι) (j : Fin d) (hj : A.normal H (Pi.single j 1) ≠ 0)
    (p : CoordinateRing (d := d)) (hp : p.totalDegree ≤ 1) :
    A.hyperplanePivotRestriction H j p = 0 ↔
      ∃ c : ℂ, p = MvPolynomial.C c * A.equationPolynomial H := by
  classical
  constructor
  · intro hz
    have hker : p ∈ RingHom.ker (A.hyperplanePivotRestriction H j) := hz
    rw [A.hyperplanePivotRestriction_ker H j hj] at hker
    change p ∈ Ideal.span {A.equationPolynomial H} at hker
    exact constant_multiple_of_degree_one_dvd
      (A.equationPolynomial H) p (A.equationPolynomial_totalDegree H) hp
      (Ideal.mem_span_singleton.mp hker)
  · rintro ⟨c, rfl⟩
    rw [map_mul, A.hyperplanePivotRestriction_equation H j hj, mul_zero]

/-- Proportional actual restricted equations are equivalent to an
actual affine linear relation among the original three equations.
No proportionality criterion or affine-flat comparison is assumed. -/
theorem hyperplanePivotRestriction_proportional_iff
    (H K M : ι) (j : Fin d) (hj : A.normal H (Pi.single j 1) ≠ 0)
    (c : ℂ) :
    A.hyperplanePivotRestriction H j (A.equationPolynomial M) =
        MvPolynomial.C c * A.hyperplanePivotRestriction H j (A.equationPolynomial K) ↔
      ∃ e : ℂ, A.equationPolynomial M =
        MvPolynomial.C c * A.equationPolynomial K +
          MvPolynomial.C e * A.equationPolynomial H := by
  classical
  let p := A.equationPolynomial M - MvPolynomial.C c * A.equationPolynomial K
  have hp : p.totalDegree ≤ 1 := by
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · exact (A.equationPolynomial_totalDegree M).le
    · have hm := MvPolynomial.totalDegree_mul
        (MvPolynomial.C c) (A.equationPolynomial K)
      simpa only [MvPolynomial.totalDegree_C,
        A.equationPolynomial_totalDegree K, zero_add] using hm
  constructor
  · intro hprop
    have hz : A.hyperplanePivotRestriction H j p = 0 := by
      dsimp only [p]
      rw [map_sub, map_mul]
      rw [A.hyperplanePivotRestriction_C H j c, hprop, sub_self]
    obtain ⟨e, he⟩ :=
      (A.hyperplanePivotRestriction_lowDegree_eq_zero_iff H j hj p hp).mp hz
    refine ⟨e, ?_⟩
    dsimp only [p] at he
    exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
  · rintro ⟨e, he⟩
    rw [he, map_add, map_mul, map_mul,
      A.hyperplanePivotRestriction_equation H j hj, mul_zero, add_zero]
    rw [A.hyperplanePivotRestriction_C H j c]

/-- Taking the linear parts of an actual affine polynomial identity
does not discard the original affine constants until they have been
cancelled by evaluation at the origin. -/
theorem normal_relation_of_equationPolynomial_affine_relation
    (H K : ι) (c δ : ℂ)
    (hpoly : A.equationPolynomial K =
      MvPolynomial.C c * A.equationPolynomial H + MvPolynomial.C δ) :
    A.normal K = c • A.normal H := by
  classical
  have h0 := congrArg (MvPolynomial.eval (0 : Fin d → ℂ)) hpoly
  simp only [map_add, map_mul, MvPolynomial.eval_C,
    A.equationPolynomial_eval, map_zero] at h0
  apply LinearMap.ext
  intro x
  have hx := congrArg (MvPolynomial.eval x) hpoly
  simp only [map_add, map_mul, MvPolynomial.eval_C,
    A.equationPolynomial_eval] at hx
  simp only [LinearMap.smul_apply, smul_eq_mul]
  linear_combination hx - h0

/-- Constant actual restrictions are exactly the original parallel
pairs. This class is separate from the nonconstant associate classes
that define the affine codimension-two residue blocks. -/
theorem hyperplanePivotRestriction_isConstant_iff_parallel
    (H K : ι) (j : Fin d) (hj : A.normal H (Pi.single j 1) ≠ 0) :
    (∃ δ : ℂ, A.hyperplanePivotRestriction H j (A.equationPolynomial K) =
      MvPolynomial.C δ) ↔ ∃ c : ℂ, A.normal K = c • A.normal H := by
  classical
  constructor
  · rintro ⟨δ, hδ⟩
    let p := A.equationPolynomial K - MvPolynomial.C δ
    have hp : p.totalDegree ≤ 1 := by
      exact (MvPolynomial.totalDegree_sub_C_le _ _).trans
        (A.equationPolynomial_totalDegree K).le
    have hz : A.hyperplanePivotRestriction H j p = 0 := by
      dsimp only [p]
      rw [map_sub, A.hyperplanePivotRestriction_C H j δ, hδ, sub_self]
    obtain ⟨c, hc⟩ :=
      (A.hyperplanePivotRestriction_lowDegree_eq_zero_iff H j hj p hp).mp hz
    refine ⟨c, A.normal_relation_of_equationPolynomial_affine_relation H K c δ ?_⟩
    dsimp only [p] at hc
    exact sub_eq_iff_eq_add.mp hc
  · rintro ⟨c, hc⟩
    exact ⟨c * A.offset H - A.offset K,
      A.hyperplanePivotRestriction_parallel H K j hj c hc⟩

end AffineArrangement

end ChenRanks
