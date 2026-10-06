import ChenRanks.CirclePathIntegerIncrement
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.AlgebraicTopology.SingularSet

/-!
# Real lifts of genuine circle-valued singular simplices

The original standard simplex is contracted by actual affine interpolation
from an actual vertex. Native covering homotopy lifting produces a real
lift of every circle-valued simplex. No simple-connectedness hypothesis,
assigned lift, or triangle-cocycle premise is supplied by the caller.
-/

noncomputable section

open unitInterval

namespace ChenRanks

/-- Actual affine interpolation inside the original real standard simplex. -/
def realSimplexContraction (n : ℕ) (v : stdSimplex ℝ (Fin (n + 1))) :
    C(I × stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 1))) where
  toFun tx :=
    ⟨(1 - (tx.1 : ℝ)) • v.val + (tx.1 : ℝ) • tx.2.val,
      (convex_stdSimplex ℝ (Fin (n + 1))) v.property tx.2.property
        (sub_nonneg.mpr tx.1.property.2) tx.1.property.1
        (sub_add_cancel 1 (tx.1 : ℝ))⟩
  continuous_toFun := by fun_prop

theorem realSimplexContraction_zero (n : ℕ) (v x : stdSimplex ℝ (Fin (n + 1))) :
    realSimplexContraction n v (0, x) = v := by
  apply Subtype.ext
  simp [realSimplexContraction]

theorem realSimplexContraction_one (n : ℕ) (v x : stdSimplex ℝ (Fin (n + 1))) :
    realSimplexContraction n v (1, x) = x := by
  apply Subtype.ext
  simp [realSimplexContraction]

/-- Every original continuous circle-valued simplex has an actual real lift,
constructed by native covering homotopy lifting of its actual contraction. -/
theorem circleSimplex_exists_real_lift (n : ℕ)
    (s : C(stdSimplex ℝ (Fin (n + 1)), Circle)) :
    ∃ F : C(stdSimplex ℝ (Fin (n + 1)), ℝ),
      ∀ x, Circle.exp (F x) = s x := by
  let v : stdSimplex ℝ (Fin (n + 1)) := stdSimplex.vertex 0
  let H : C(I × stdSimplex ℝ (Fin (n + 1)), Circle) :=
    s.comp (realSimplexContraction n v)
  let a : C(stdSimplex ℝ (Fin (n + 1)), ℝ) := .const _ (Complex.arg (s v))
  have h0 : ∀ x, H (0, x) = Circle.exp (a x) := by
    intro x
    change s (realSimplexContraction n v (0, x)) = Circle.exp (Complex.arg (s v))
    rw [realSimplexContraction_zero, Circle.exp_arg]
  let G := Circle.isCoveringMap_exp.liftHomotopy H a h0
  let j : C(stdSimplex ℝ (Fin (n + 1)), I × stdSimplex ℝ (Fin (n + 1))) :=
    ⟨fun x => (1, x), continuous_const.prodMk continuous_id⟩
  refine ⟨G.comp j, ?_⟩
  intro x
  have hg := congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts H a h0) (1, x)
  change Circle.exp (G (1, x)) = H (1, x) at hg
  change Circle.exp (G (1, x)) = s x
  rw [hg]
  change s (realSimplexContraction n v (1, x)) = s x
  rw [realSimplexContraction_one]

/-- A genuine real lift of the same original geometric simplex. -/
def circleSimplexArgumentLift (n : ℕ)
    (s : C(stdSimplex ℝ (Fin (n + 1)), Circle)) :
    C(stdSimplex ℝ (Fin (n + 1)), ℝ) :=
  (circleSimplex_exists_real_lift n s).choose

theorem circleSimplexArgumentLift_projects (n : ℕ)
    (s : C(stdSimplex ℝ (Fin (n + 1)), Circle))
    (x : stdSimplex ℝ (Fin (n + 1))) :
    Circle.exp (circleSimplexArgumentLift n s x) = s x :=
  (circleSimplex_exists_real_lift n s).choose_spec x

end ChenRanks
