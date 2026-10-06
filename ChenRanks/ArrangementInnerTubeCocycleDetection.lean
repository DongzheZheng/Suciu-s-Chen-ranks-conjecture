import ChenRanks.ArrangementSingleHyperplaneInnerTube
import ChenRanks.ArrangementMeridianCocycleNormalization
import ChenRanks.CircleNormalizedCocycleLoopDetection

/-!
# Actual local closed-loop detection in the original complement

The actual inner tube and its two genuine homotopies are constructed
from the original equations. Actual transport of positive meridians
derives the local generator value from the one actual canonical
meridian. Genuine circle-loop detection then gives vanishing on every
actual closed loop in the constructed tube. No local detector, local
homotopy equivalence, or H¹-spanning statement is supplied as a premise.
-/

noncomputable section

open unitInterval
open ChenRanks.SingularCohomology

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (k : Type) [Field k]

/-- The actual canonical generator controls all original closed loops
inside the actual radius proved at any regular point of H. -/
theorem innerTube_closedCochain_loop_value_eq_zero (H : ι)
    (w : A.HyperplaneRegularLocus H)
    (β : cochains k A.Complement 1)
    (hβ : differential k A.Complement 1 β = 0)
    (hcanonical : values k A.Complement 1 β
      (simplexOfPath A.Complement (A.meridianDiskPathMap H (A.actualMeridianDisk H))) = 0)
    (γ : C(I, A.Complement)) (hclosed : γ 0 = γ 1)
    (hnear : ∀ t : I, dist (γ t).val w.val < A.actualInnerTubeRadius H w) :
    values k A.Complement 1 β (simplexOfPath A.Complement γ) = 0 := by
  let m := A.innerTubeMeridianDisk H w
  let f := A.meridianDiskCircleMap H m
  let βcircle := cochainPullback k f 1 β
  have hβcircle : differential k Circle 1 βcircle = 0 := by
    have h := congrArg (fun T => T β) (differential_cochainPullback k f 1)
    simpa only [LinearMap.comp_apply, hβ, map_zero] using h
  have hm : values k A.Complement 1 β
      (simplexOfPath A.Complement (A.meridianDiskPathMap H m)) = 0 :=
    (A.meridianDisk_closedCochain_values_eq k H m (A.actualMeridianDisk H) β hβ).trans
      hcanonical
  have hgenerator : values k Circle 1 βcircle
      (simplexOfPath Circle positiveUnitCircleTraversal) = 0 := by
    change values k Circle 1 (cochainPullback k f 1 β)
      (simplexOfPath Circle positiveUnitCircleTraversal) = 0
    rw [values_cochainPullback, simplexMap_simplexOfPath]
    exact hm
  let cγ := (A.equationComplementCircleMap H).comp γ
  have hcγ : cγ 0 = cγ 1 := congrArg (A.equationComplementCircleMap H) hclosed
  have hcircle := circle_closedCochain_loop_value_eq_zero_of_generator k βcircle
    hβcircle hgenerator cγ hcγ
  have htop : values k A.Complement 1 β
      (simplexOfPath A.Complement (f.comp cγ)) = 0 := by
    rw [values_cochainPullback, simplexMap_simplexOfPath] at hcircle
    exact hcircle
  let F := A.innerTubeRetractionHomotopy H w γ hnear
  let G := A.innerTubeRadialHomotopy H w γ hnear
  have hF := closedCochain_values_squareBottom_eq_top A.Complement k F
    (A.innerTubeRetractionHomotopy_periodic H w γ hnear hclosed) β hβ
  have hG := closedCochain_values_squareBottom_eq_top A.Complement k G
    (A.innerTubeRadialHomotopy_periodic H w γ hnear hclosed) β hβ
  have hbottom : squareBottomPath A.Complement F = γ := by
    apply ContinuousMap.ext
    intro t
    exact A.innerTubeRetractionHomotopy_zero H w γ hnear t
  have hmiddle : squareTopPath A.Complement F = squareBottomPath A.Complement G := by
    apply ContinuousMap.ext
    intro t
    exact (A.innerTubeRadialHomotopy_zero H w γ hnear t).symm
  have hfinal : squareTopPath A.Complement G = f.comp cγ := by
    apply ContinuousMap.ext
    intro t
    exact A.innerTubeRadialHomotopy_one H w γ hnear t
  rw [hbottom, hmiddle] at hF
  rw [hfinal] at hG
  exact hF.trans (hG.trans htop)

/-- The positive radius and all-loop conclusion are genuine outputs
of the original finite configuration, not a locality assumption. -/
theorem exists_actual_innerTube_closedCochain_detector (H : ι)
    (w : A.HyperplaneRegularLocus H)
    (β : cochains k A.Complement 1)
    (hβ : differential k A.Complement 1 β = 0)
    (hcanonical : values k A.Complement 1 β
      (simplexOfPath A.Complement (A.meridianDiskPathMap H (A.actualMeridianDisk H))) = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ γ : C(I, A.Complement), γ 0 = γ 1 →
      (∀ t : I, dist (γ t).val w.val < ε) →
      values k A.Complement 1 β (simplexOfPath A.Complement γ) = 0 := by
  refine ⟨A.actualInnerTubeRadius H w, A.actualInnerTubeRadius_pos H w, ?_⟩
  intro γ hclosed hnear
  exact A.innerTube_closedCochain_loop_value_eq_zero k H w β hβ hcanonical
    γ hclosed hnear

end ChenRanks.AffineArrangement
