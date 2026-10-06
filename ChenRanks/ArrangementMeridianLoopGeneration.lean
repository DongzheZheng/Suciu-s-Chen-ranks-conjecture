import ChenRanks.ArrangementNormalizedFiniteFanCocycle
import ChenRanks.ArrangementPolygonalPathHomotopy

/-!
# Actual canonical meridians detect every original complement loop

The original path determines a genuine finite polygonal subdivision and
fixed-endpoint homotopy in the original complement. A genuine common
finite fan and genuine finite-puncture induction prove the polygon's
normalized cocycle value is zero. Native loop-homotopy invariance returns
that value to the original arbitrary loop. No generation theorem, H¹
spanning, favorable subdivision, fan, or filling is an input.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval
open ChenRanks.SingularCohomology

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (k : Type) [Field k]

/-- An actual closed one-cochain which vanishes on the original
canonical meridians vanishes on every original actual closed path. -/
theorem normalized_closedOne_all_actual_loop_values_eq_zero
    (β : cochains k A.Complement 1) (hβ : differential k A.Complement 1 β = 0)
    (hcanonical : ∀ H : ι, values k A.Complement 1 β
      (simplexOfPath A.Complement (A.meridianDiskPathMap H (A.actualMeridianDisk H))) = 0)
    (γ : C(I, A.Complement)) (hclosed : γ 0 = γ 1) :
    values k A.Complement 1 β (simplexOfPath A.Complement γ) = 0 := by
  let p : Path (γ 0) (γ 1) := ⟨γ, rfl, rfl⟩
  let n := A.actualPolygonalStepCount p
  let v : Fin (n + 1) → A.Complement := fun i => p (A.actualPolygonalGrid p i)
  have hedges (i : Fin n) (t : I) (H : ι) :
      A.normal H (actualComplexLinePoint (v i.castSucc).val (v i.succ).val t) ≠ A.offset H := by
    exact (A.straightenedSubpath p (A.actualPolygonalGrid p i.castSucc)
      (A.actualPolygonalGrid p i.succ) (A.actualPolygonalGrid_oscillation p i) t).property H
  have hvclosed : v 0 = v (Fin.last n) := by
    change p (A.actualPolygonalGrid p 0) = p (A.actualPolygonalGrid p (Fin.last n))
    rw [A.actualPolygonalGrid_zero p, A.actualPolygonalGrid_last p]
    exact hclosed
  have hpolygon := A.normalized_closedOne_finite_straight_loop_value_eq_zero
    k β hβ hcanonical n v hedges hvclosed
  have hsegment (i : Fin n) : A.actualComplementStraightPath (v i.castSucc) (v i.succ) (hedges i) =
      A.straightenedSubpath p (A.actualPolygonalGrid p i.castSucc)
        (A.actualPolygonalGrid p i.succ) (A.actualPolygonalGrid_oscillation p i) := by
    apply Path.ext
    funext t
    apply Subtype.ext
    rfl
  have hconcat : Path.concat v (fun i =>
      A.actualComplementStraightPath (v i.castSucc) (v i.succ) (hedges i)) =
      A.actualPolygonalApproximation p := by
    change Path.concat v (fun i =>
        A.actualComplementStraightPath (v i.castSucc) (v i.succ) (hedges i)) =
      Path.concat v (fun i => A.straightenedSubpath p (A.actualPolygonalGrid p i.castSucc)
        (A.actualPolygonalGrid p i.succ) (A.actualPolygonalGrid_oscillation p i))
    apply congrArg (fun F : (i : Fin n) → Path (v i.castSucc) (v i.succ) => Path.concat v F)
    funext i
    exact hsegment i
  rw [hconcat] at hpolygon
  have hhom := actualPathCochainValue_eq_of_loop_homotopy A.Complement k β hβ hvclosed
    (A.actualPolygonalApproximationHomotopy p)
  have hzero := hhom.symm.trans hpolygon
  unfold actualPathCochainValue at hzero
  rw [A.actualPolygonalFullSubpath_toContinuousMap p] at hzero
  exact hzero

end ChenRanks.AffineArrangement
