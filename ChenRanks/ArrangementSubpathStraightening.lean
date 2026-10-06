import ChenRanks.ArrangementComplexLinePaths
import Mathlib.Topology.Subpath

/-! Actual straightening of a short original subpath. The explicit
homotopy has fixed original endpoints and stays in the original
complement by a metric estimate against the genuine path tube. -/

noncomputable section

open unitInterval

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable {x y : A.Complement} (γ : Path x y) (a b : I)

/-- The actual endpoint estimate follows from the actual subpath
oscillation, by evaluation at the actual terminal parameter. -/
theorem shortSubpath_endpoint_distance
    (hosc : ∀ t : I, dist (γ (Set.Icc.convexCombo a b t)).val (γ a).val <
      A.actualPathAvoidanceRadius γ.toContinuousMap / 4) :
    dist (γ b).val (γ a).val < A.actualPathAvoidanceRadius γ.toContinuousMap := by
  have h := hosc 1
  simp only [Set.Icc.convexCombo_one] at h
  have hp := A.actualPathAvoidanceRadius_pos γ.toContinuousMap
  linarith

/-- The genuine straight segment sharing the original subpath endpoints. -/
def straightenedSubpath
    (hosc : ∀ t : I, dist (γ (Set.Icc.convexCombo a b t)).val (γ a).val <
      A.actualPathAvoidanceRadius γ.toContinuousMap / 4) : Path (γ a) (γ b) :=
  A.segmentInActualPathTube γ.toContinuousMap a (γ b)
    (A.shortSubpath_endpoint_distance γ a b hosc)

/-- Every point of the actual straightened subpath remains within the
proved small endpoint radius of its actual initial point. -/
theorem straightenedSubpath_distance
    (hosc : ∀ t : I, dist (γ (Set.Icc.convexCombo a b t)).val (γ a).val <
      A.actualPathAvoidanceRadius γ.toContinuousMap / 4) (t : I) :
    dist (A.straightenedSubpath γ a b hosc t).val (γ a).val <
      A.actualPathAvoidanceRadius γ.toContinuousMap / 4 := by
  apply (A.segmentInActualPathTube_dist_le γ.toContinuousMap a (γ b)
    (A.shortSubpath_endpoint_distance γ a b hosc) t).trans_lt
  simpa only [Set.Icc.convexCombo_one] using hosc 1

/-- The explicit fixed-endpoint interpolation between the original
subpath and its genuine straight segment stays in the original complement. -/
def subpathStraighteningHomotopy
    (hosc : ∀ t : I, dist (γ (Set.Icc.convexCombo a b t)).val (γ a).val <
      A.actualPathAvoidanceRadius γ.toContinuousMap / 4) :
    (γ.subpath a b).Homotopy (A.straightenedSubpath γ a b hosc) where
  toFun p := ⟨actualComplexLinePoint ((γ.subpath a b) p.2).val
    (A.straightenedSubpath γ a b hosc p.2).val p.1, by
      apply A.actualPathAvoidanceRadius_avoids γ.toContinuousMap a
      have hle := actualComplexLinePoint_dist_center_le
        ((γ.subpath a b) p.2).val
        (A.straightenedSubpath γ a b hosc p.2).val (γ a).val p.1
      have hfirst := hosc p.2
      have hsecond := A.straightenedSubpath_distance γ a b hosc p.2
      have hp := A.actualPathAvoidanceRadius_pos γ.toContinuousMap
      change dist ((γ.subpath a b) p.2).val (γ a).val <
        A.actualPathAvoidanceRadius γ.toContinuousMap / 4 at hfirst
      change dist (actualComplexLinePoint ((γ.subpath a b) p.2).val
        (A.straightenedSubpath γ a b hosc p.2).val p.1) (γ a).val <
          A.actualPathAvoidanceRadius γ.toContinuousMap
      linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun p : I × I => ((γ.subpath a b) p.2).val +
      ((p.1 : ℝ) : ℂ) • ((A.straightenedSubpath γ a b hosc p.2).val -
        ((γ.subpath a b) p.2).val))
    have hp : Continuous (fun p : I × I => ((γ.subpath a b) p.2).val) :=
      continuous_subtype_val.comp ((γ.subpath a b).continuous.comp continuous_snd)
    have hq : Continuous (fun p : I × I =>
        (A.straightenedSubpath γ a b hosc p.2).val) :=
      continuous_subtype_val.comp
        ((A.straightenedSubpath γ a b hosc).continuous.comp continuous_snd)
    have hs : Continuous (fun p : I × I => ((p.1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
    exact hp.add (hs.smul (hq.sub hp))
  map_zero_left t := by
    apply Subtype.ext
    exact actualComplexLinePoint_zero _ _
  map_one_left t := by
    apply Subtype.ext
    exact actualComplexLinePoint_one _ _
  prop' s t ht := by
    rcases ht with rfl | rfl
    · apply Subtype.ext
      change actualComplexLinePoint ((γ.subpath a b) 0).val
        (A.straightenedSubpath γ a b hosc 0).val s = ((γ.subpath a b) 0).val
      rw [Path.source, Path.source, actualComplexLinePoint_self]
    · apply Subtype.ext
      change actualComplexLinePoint ((γ.subpath a b) 1).val
        (A.straightenedSubpath γ a b hosc 1).val s = ((γ.subpath a b) 1).val
      rw [Path.target, Path.target, actualComplexLinePoint_self]

end ChenRanks.AffineArrangement
