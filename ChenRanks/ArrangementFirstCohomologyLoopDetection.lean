import ChenRanks.SingularFirstCohomologyLoopDetection
import ChenRanks.ArrangementPathConnected
import ChenRanks.ArrangementMeridianBasepoint

/-!
# Actual all-loop detection of H¹ of the original arrangement complement

Original nonzero equation polynomials give an actual complement point
by simultaneous nonzero evaluation. The already proved actual path
construction then gives path connectedness. The genuine primitive
construction consequently applies to the original native H¹ without
any additional geometric or cohomological hypothesis.

This does not identify a finite meridian family as generating all loops
or assert that the equation classes span H¹.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.AffineArrangement

open SingularCohomology

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The original complement is nonempty for every original finite
affine arrangement, including the empty arrangement in dimension zero. -/
theorem complement_nonempty_by_actual_equations : Nonempty A.Complement := by
  obtain ⟨x, hx⟩ := mvPolynomial_exists_simultaneous_nonzero_evaluation
    ℂ (Fin d) ι A.equationPolynomial A.equationPolynomial_ne_zero
  refine ⟨⟨x, ?_⟩⟩
  intro H
  have hH := hx H
  rw [A.equationPolynomial_eval H x] at hH
  exact sub_ne_zero.mp hH

/-- Actual nonemptiness and the actual complex-line path construction
give actual path connectedness without a supplied basepoint. -/
theorem complement_pathConnectedSpace_from_actual_equations :
    PathConnectedSpace A.Complement :=
  A.complement_pathConnectedSpace
    (Classical.choice A.complement_nonempty_by_actual_equations)

/-- Every actual original H¹ class is detected by all actual original
closed paths; all structural topological inputs are truly constructed. -/
theorem singularH1_eq_zero_iff_all_actual_closed_path_evaluations
    (h : A.singularH1) :
    h = 0 ↔ ∀ (γ : C(I, A.Complement)) (hγ : γ 0 = γ 1),
      closedPathEvaluation ℂ A.Complement γ hγ h = 0 := by
  letI := A.complement_pathConnectedSpace_from_actual_equations
  exact firstCohomology_eq_zero_iff_closed_path_evaluations A.Complement ℂ h

end ChenRanks.AffineArrangement
