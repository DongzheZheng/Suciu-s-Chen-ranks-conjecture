import ChenRanks.AffinePivotLowDegree

/-!
# Actual degrees and prime equations of restricted affine hyperplanes

Solving the original affine equation is an affine polynomial substitution,
so every actual restricted original equation has total degree at most one.
The proved constant-restriction criterion identifies exactly the parallel
pairs. Consequently every nonparallel restriction has genuine degree one
and is irreducible in the actual remaining-coordinate polynomial ring.
No irreducibility or divisor grouping is provided as a hypothesis.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The actual value substituted for the pivot coordinate is affine. -/
theorem hyperplanePivotValue_totalDegree_le_one (H : ι) (j : Fin d) :
    (A.hyperplanePivotValue H j).totalDegree ≤ 1 := by
  classical
  have hsum : (∑ i : {i : Fin d // i ≠ j},
      MvPolynomial.C (A.normal H (Pi.single i.val 1)) * MvPolynomial.X i).totalDegree ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    simpa only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add] using
      MvPolynomial.totalDegree_mul
        (MvPolynomial.C (A.normal H (Pi.single i.val 1))) (MvPolynomial.X i)
  have hsub : (MvPolynomial.C (A.offset H) -
      ∑ i : {i : Fin d // i ≠ j},
        MvPolynomial.C (A.normal H (Pi.single i.val 1)) * MvPolynomial.X i).totalDegree ≤ 1 :=
    (MvPolynomial.totalDegree_sub _ _).trans
      (max_le (by simp only [MvPolynomial.totalDegree_C]; omega) hsum)
  dsimp only [hyperplanePivotValue]
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (by simpa only [MvPolynomial.totalDegree_C, zero_add] using hsub)

/-- Restricting an actual original affine equation preserves the
degree-at-most-one bound, including its actual affine offset. -/
theorem hyperplanePivotRestriction_equation_totalDegree_le_one (H K : ι) (j : Fin d) :
    (A.hyperplanePivotRestriction H j (A.equationPolynomial K)).totalDegree ≤ 1 := by
  classical
  simp only [hyperplanePivotRestriction, equationPolynomial, map_sub, map_sum,
    map_mul, affinePivotRestriction_C]
  apply (MvPolynomial.totalDegree_sub_C_le _ _).trans
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  have hXi : (affinePivotRestriction ℂ (Fin d) j (A.hyperplanePivotValue H j)
      (MvPolynomial.X i)).totalDegree ≤ 1 := by
    by_cases hi : i = j
    · subst i
      rw [affinePivotRestriction_X_self]
      exact A.hyperplanePivotValue_totalDegree_le_one H j
    · rw [affinePivotRestriction_X_other ℂ (Fin d) j (A.hyperplanePivotValue H j) i hi]
      simp only [MvPolynomial.totalDegree_X, le_refl]
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (by simpa only [MvPolynomial.totalDegree_C, zero_add] using hXi)

/-- A genuinely nonparallel original pair has a genuine degree-one
restriction at the same actual pivot hyperplane. -/
theorem hyperplanePivotRestriction_totalDegree_eq_one_of_not_parallel
    (H K : ι) (j : Fin d) (hj : A.normal H (Pi.single j 1) ≠ 0)
    (hparallel : ¬∃ c : ℂ, A.normal K = c • A.normal H) :
    (A.hyperplanePivotRestriction H j (A.equationPolynomial K)).totalDegree = 1 := by
  have hle := A.hyperplanePivotRestriction_equation_totalDegree_le_one H K j
  have hne : (A.hyperplanePivotRestriction H j (A.equationPolynomial K)).totalDegree ≠ 0 := by
    intro hzero
    apply hparallel
    apply (A.hyperplanePivotRestriction_isConstant_iff_parallel H K j hj).mp
    exact ⟨_, MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hzero⟩
  omega

/-- The actual nonparallel restricted equation is irreducible in the
actual remaining-coordinate polynomial ring. -/
theorem hyperplanePivotRestriction_irreducible_of_not_parallel
    (H K : ι) (j : Fin d) (hj : A.normal H (Pi.single j 1) ≠ 0)
    (hparallel : ¬∃ c : ℂ, A.normal K = c • A.normal H) :
    Irreducible (A.hyperplanePivotRestriction H j (A.equationPolynomial K)) := by
  have hdegree := A.hyperplanePivotRestriction_totalDegree_eq_one_of_not_parallel
    H K j hj hparallel
  apply MvPolynomial.irreducible_of_totalDegree_eq_one hdegree
  intro r hr
  by_cases hzero : r = 0
  · subst r
    have hz : A.hyperplanePivotRestriction H j (A.equationPolynomial K) = 0 := by
      apply MvPolynomial.ext
      intro m
      exact zero_dvd_iff.mp (hr m)
    simp only [hz, MvPolynomial.totalDegree_zero] at hdegree
    omega
  · exact isUnit_iff_ne_zero.mpr hzero

end ChenRanks.AffineArrangement
