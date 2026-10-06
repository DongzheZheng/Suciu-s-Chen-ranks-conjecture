import ChenRanks.ArrangementPointLocalization
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Actual neighborhoods avoiding every nonincident original hyperplane

All original hyperplanes not through the actual point are nonzero there.
Their true finite open intersection contains an actual positive metric
ball. This discharges the neighborhood needed to embed the localized
central arrangement's small cycles back into the original complement.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- A genuine positive neighborhood avoids all actual nonincident equations. -/
theorem exists_point_avoidance_radius (x : Fin d → ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : Fin d → ℂ, dist y x < ε →
      ∀ H : ι, A.normal H x ≠ A.offset H → A.normal H y ≠ A.offset H := by
  classical
  let U : Set (Fin d → ℂ) := ⋂ H : {H : ι // A.normal H x ≠ A.offset H},
    {y | A.normal H y ≠ A.offset H}
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro H
    exact isOpen_ne_fun (A.normal H).continuous_of_finiteDimensional continuous_const
  have hx : x ∈ U := by
    apply Set.mem_iInter.mpr
    intro H
    exact H.property
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  refine ⟨ε, hε, ?_⟩
  intro y hy H hHx
  exact Set.mem_iInter.mp (hball hy) ⟨H, hHx⟩

/-- The radius is chosen only from the proved original finite avoidance theorem. -/
def actualPointAvoidanceRadius (x : Fin d → ℂ) : ℝ :=
  (A.exists_point_avoidance_radius x).choose

theorem actualPointAvoidanceRadius_pos (x : Fin d → ℂ) :
    0 < A.actualPointAvoidanceRadius x :=
  (A.exists_point_avoidance_radius x).choose_spec.1

theorem actualPointAvoidanceRadius_avoids (x y : Fin d → ℂ)
    (hy : dist y x < A.actualPointAvoidanceRadius x) (H : ι)
    (hHx : A.normal H x ≠ A.offset H) : A.normal H y ≠ A.offset H :=
  (A.exists_point_avoidance_radius x).choose_spec.2 y hy H hHx

end ChenRanks.AffineArrangement
