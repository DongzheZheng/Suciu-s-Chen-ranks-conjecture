import ChenRanks.ArrangementFinitePuncturedTriangleCocycle
import ChenRanks.ArrangementFanPunctureGeometry
import ChenRanks.ArrangementActualSegmentCocycleValues
import ChenRanks.SingularFinitePathCocycleValues

/-!
# Genuine finite fan cancellation for original normalized cocycles

One simultaneous actual fan center is constructed for all original
straight edges. Every triangle's actual finite punctures are regular,
so the genuine puncture induction proves its actual boundary vanishes.
The same original segment-value function on the same center then
literally telescopes over the finite path. No filling, fan center,
meridian generation, or edge relation is an input.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval
open ChenRanks.SingularCohomology

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (k : Type) [Field k]

/-- Every original finite closed polygon has zero normalized cocycle
value. Its actual fan geometry is constructed from its literal edges. -/
theorem normalized_closedOne_finite_straight_loop_value_eq_zero
    (β : cochains k A.Complement 1) (hβ : differential k A.Complement 1 β = 0)
    (hcanonical : ∀ H : ι, values k A.Complement 1 β
      (simplexOfPath A.Complement (A.meridianDiskPathMap H (A.actualMeridianDisk H))) = 0)
    (n : ℕ) (p : Fin (n + 1) → A.Complement)
    (hedges : ∀ (i : Fin n) (t : I) (H : ι),
      A.normal H (actualComplexLinePoint (p i.castSucc).val (p i.succ).val t) ≠ A.offset H)
    (hclosed : p 0 = p (Fin.last n)) :
    actualPathCochainValue k A.Complement β
      (Path.concat p (fun i => A.actualComplementStraightPath (p i.castSucc) (p i.succ) (hedges i))) = 0 := by
  obtain ⟨z, hgeometry⟩ := A.exists_actual_fan_triangle_puncture_geometry
    (fun i : Fin n => p i.castSucc) (fun i : Fin n => p i.succ) hedges
  let L : Fin (n + 1) → k := fun j => A.actualOriginalSegmentCochainValue k β z (p j)
  have hedgeValues (i : Fin n) :
      A.actualOriginalSegmentCochainValue k β (p i.castSucc) (p i.succ) =
        L i.succ - L i.castSucc := by
    have hg := hgeometry i
    have hzero := A.normalized_closedOne_finite_punctured_triangle_boundary_eq_zero k
      β hβ hcanonical (actualFanTriangleAmbient (p i.castSucc).val (p i.succ).val z.val)
      hg.1 hg.2.1 hg.2.2
    rw [A.actualFanTriangle_boundaryValue_eq_segments k β (p i.castSucc) (p i.succ) z hg.2.1] at hzero
    change A.actualOriginalSegmentCochainValue k β (p i.castSucc) (p i.succ) =
      A.actualOriginalSegmentCochainValue k β z (p i.succ) -
        A.actualOriginalSegmentCochainValue k β z (p i.castSucc)
    linear_combination -hzero
  rw [actualPathCochainValue_concat A.Complement k β hβ n]
  have hsum : (∑ i : Fin n, actualPathCochainValue k A.Complement β
      (A.actualComplementStraightPath (p i.castSucc) (p i.succ) (hedges i))) =
      ∑ i : Fin n, (L i.succ - L i.castSucc) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← A.actualOriginalSegmentCochainValue_of_safe k β (p i.castSucc) (p i.succ) (hedges i)]
    exact hedgeValues i
  rw [hsum, fin_adjacent_difference_sum]
  have hends : L (Fin.last n) = L 0 :=
    congrArg (fun x => A.actualOriginalSegmentCochainValue k β z x) hclosed.symm
  rw [hends, sub_self]

end ChenRanks.AffineArrangement
