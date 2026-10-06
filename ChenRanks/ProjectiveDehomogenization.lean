import ChenRanks.ProjectivePolynomialBase
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Actual homogeneous dehomogenization has no hidden kernel

For a genuine homogeneous polynomial p of total degree n, its actual
option-variable expansion has coefficients homogeneous of degree n-i.
Evaluation of the homogenizing variable at 1 adds these distinct
homogeneous pieces.  Applying the actual homogeneous projections recovers
each coefficient, so dehomogenization can vanish only when p vanishes.
This is the injectivity ingredient for the actual standard affine chart;
no chart equivalence or homogenization detector is assumed.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry

universe u

variable (k ι : Type u) [Field k] [Finite ι]

/-- The actual dehomogenization uses the actual option-variable algebra
equivalence and the actual polynomial evaluation map at 1. -/
def projectivePolynomialDehomogenization :
    MvPolynomial (Option ι) k →+* MvPolynomial ι k :=
  (Polynomial.evalRingHom (1 : MvPolynomial ι k)).comp
    (MvPolynomial.optionEquivLeft k ι).toRingHom

/-- Distinct actual homogeneous coefficient degrees prohibit cancellation
under genuine dehomogenization of a homogeneous polynomial. -/
theorem projectivePolynomialDehomogenization_eq_zero_iff
    {p : MvPolynomial (Option ι) k} {n : ℕ} (hp : p.IsHomogeneous n) :
    projectivePolynomialDehomogenization k ι p = 0 ↔ p = 0 := by
  classical
  constructor
  · intro hz
    let q := MvPolynomial.optionEquivLeft k ι p
    have hqDegree : q.natDegree ≤ n := by
      dsimp [q]
      rw [MvPolynomial.natDegree_optionEquivLeft]
      exact (MvPolynomial.degreeOf_le_totalDegree p none).trans hp.totalDegree_le
    have hcoeff (i : ℕ) (hi : i ≤ n) : (q.coeff i).IsHomogeneous (n - i) := by
      have hp' : ((MvPolynomial.optionEquivLeft k ι).symm q).IsHomogeneous n := by
        simpa only [q, AlgEquiv.symm_apply_apply] using hp
      exact MvPolynomial.IsHomogeneous.coeff_isHomogeneous_of_optionEquivLeft_symm hp' i (n - i)
        (Nat.add_sub_of_le hi)
    have hsum : (∑ i ∈ Finset.range (n + 1), q.coeff i) = 0 := by
      change q.eval 1 = 0 at hz
      rw [Polynomial.eval_eq_sum_range' (show q.natDegree < n + 1 by omega) 1] at hz
      simpa only [one_pow, mul_one] using hz
    have hq : q = 0 := by
      apply Polynomial.ext
      intro j
      rw [Polynomial.coeff_zero]
      by_cases hj : j ≤ n
      · have hprojected := congrArg (MvPolynomial.homogeneousComponent (n - j)) hsum
        simp only [map_sum, map_zero] at hprojected
        have hrecover : (∑ i ∈ Finset.range (n + 1),
            MvPolynomial.homogeneousComponent (n - j) (q.coeff i)) = q.coeff j := by
          rw [Finset.sum_eq_single j]
          · simpa only [if_pos rfl] using
              (MvPolynomial.homogeneousComponent_of_mem (m := n - j) (hcoeff j hj))
          · intro i hi hij
            have hin : i ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
            rw [MvPolynomial.homogeneousComponent_of_mem (hcoeff i hin), if_neg]
            omega
          · intro hjnot
            exact False.elim (hjnot (Finset.mem_range.mpr (by omega)))
        rw [hrecover] at hprojected
        exact hprojected
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    apply (MvPolynomial.optionEquivLeft k ι).injective
    simpa only [map_zero] using hq
  · intro hpzero
    rw [hpzero, map_zero]

end

end ChenRanks
