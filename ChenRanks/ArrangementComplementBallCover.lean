import ChenRanks.ArrangementPathUniformNeighborhood
import Mathlib.Analysis.Convex.Topology

/-! A canonical genuine open-ball cover of the original arrangement
complement. The radii are chosen from the proved openness of the actual
equations' complement. Convexity, openness, containment and the cover
property are derived; no good cover or local frame is an input.
-/
noncomputable section
namespace ChenRanks.AffineArrangement
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- Genuine convex ambient balls contained in the actual original complement. -/
structure ActualComplementBall where
  center : Fin d → ℂ
  radius : ℝ
  positive : 0 < radius
  contained : Metric.ball center radius ⊆ A.ambientComplementSet

variable (U : A.ActualComplementBall)

def actualComplementBallSet : Set (Fin d → ℂ) := Metric.ball U.center U.radius

theorem actualComplementBallSet_convex : Convex ℝ (A.actualComplementBallSet U) :=
  convex_ball U.center U.radius

theorem actualComplementBallSet_isOpen : IsOpen (A.actualComplementBallSet U) :=
  Metric.isOpen_ball

theorem actualComplementBallSet_contained : A.actualComplementBallSet U ⊆ A.ambientComplementSet :=
  U.contained

theorem actualComplementBallSet_center : U.center ∈ A.actualComplementBallSet U :=
  Metric.mem_ball_self U.positive

/-- Actual complement points in the same genuine ambient ball. -/
def actualComplementBallBaseSet : Set A.Complement :=
  {x | x.val ∈ A.actualComplementBallSet U}

theorem actualComplementBallBaseSet_isOpen : IsOpen (A.actualComplementBallBaseSet U) :=
  (A.actualComplementBallSet_isOpen U).preimage continuous_subtype_val

/-- Actual native openness chooses a true ball at every original point. -/
def actualComplementBallAt (x : A.Complement) : A.ActualComplementBall :=
  let h := Metric.isOpen_iff.mp A.ambientComplementSet_isOpen x.val x.property
  { center := x.val
    radius := Classical.choose h
    positive := (Classical.choose_spec h).1
    contained := (Classical.choose_spec h).2 }

@[simp] theorem actualComplementBallAt_center (x : A.Complement) :
    (A.actualComplementBallAt x).center = x.val := rfl

/-- The actual original complement is covered by the actual chosen balls. -/
theorem mem_actualComplementBallBaseSet_at (x : A.Complement) :
    x ∈ A.actualComplementBallBaseSet (A.actualComplementBallAt x) :=
  A.actualComplementBallSet_center (A.actualComplementBallAt x)

end ChenRanks.AffineArrangement
