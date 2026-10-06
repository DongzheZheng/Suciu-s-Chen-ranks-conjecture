import Mathlib.Topology.Homotopy.Lifting

/-! The genuine native monodromy endpoint for an original path.

This only unfolds native homotopy-quotient elimination on an actual
representative. It does not assume endpoint agreement between two lifts.
-/

noncomputable section

namespace ChenRanks.TopologicalComparison

variable {B Z : Type*} [TopologicalSpace B] [TopologicalSpace Z]
variable {p : Z → B} (cov : IsCoveringMap p)

/-- Native monodromy on a genuine path class is the endpoint of its
genuine native lift, with the original source equality. -/
theorem coveringMonodromy_pathClass_val {x y : B}
    (γ : Path x y) (z : p ⁻¹' {x}) :
    (cov.monodromy (Path.Homotopic.Quotient.mk γ) z).val =
      cov.liftPath γ.toContinuousMap z.val (γ.source.trans z.property.symm) 1 := rfl

end ChenRanks.TopologicalComparison
