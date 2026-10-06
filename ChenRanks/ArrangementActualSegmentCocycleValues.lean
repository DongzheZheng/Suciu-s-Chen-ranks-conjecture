import ChenRanks.ArrangementFanTriangleBoundary
import ChenRanks.SingularPartialTriangleBoundary
import ChenRanks.SingularPathCocycleAdditivity

/-!
# Actual original straight-segment cochain values

Every used segment has a proved whole-path complement condition. Its
native original path has the literal original endpoints. The total value
function is only evaluated through the proved-safe formula. The actual
fan faces, not expected edge classes, derive the fan boundary formula.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval
open ChenRanks.SingularCohomology

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

def actualComplementStraightPath (x y : A.Complement)
    (h : ∀ (t : I) (H : ι), A.normal H (actualComplexLinePoint x.val y.val t) ≠ A.offset H) :
    Path x y where
  toFun t := ⟨actualComplexLinePoint x.val y.val t, h t⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold actualComplexLinePoint
    have hc : Continuous (fun t : I => ((t : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp continuous_subtype_val
    exact continuous_const.add (hc.smul continuous_const)
  source' := by
    apply Subtype.ext
    exact actualComplexLinePoint_zero _ _
  target' := by
    apply Subtype.ext
    exact actualComplexLinePoint_one _ _

variable (k : Type) [Field k]

def actualOriginalSegmentCochainValue (β : cochains k A.Complement 1)
    (x y : A.Complement) : k := by
  classical
  exact if h : ∀ (t : I) (H : ι),
      A.normal H (actualComplexLinePoint x.val y.val t) ≠ A.offset H then
    actualPathCochainValue k A.Complement β (A.actualComplementStraightPath x y h) else 0

theorem actualOriginalSegmentCochainValue_of_safe (β : cochains k A.Complement 1)
    (x y : A.Complement)
    (h : ∀ (t : I) (H : ι), A.normal H (actualComplexLinePoint x.val y.val t) ≠ A.offset H) :
    A.actualOriginalSegmentCochainValue k β x y =
      actualPathCochainValue k A.Complement β (A.actualComplementStraightPath x y h) := by
  classical
  exact dif_pos h

/-- The native fan boundary has precisely its actual three original
straight-segment values, in the actual vertex order z,x,y. -/
theorem actualFanTriangle_boundaryValue_eq_segments
    (β : cochains k A.Complement 1) (x y z : A.Complement)
    (hboundary : ∀ (i : Fin 3) (t : I) (H : ι), A.normal H
      (actualFanTriangleAmbient x.val y.val z.val (realTriangleFacePath i t)) ≠ A.offset H) :
    partialTriangleBoundaryValue (Fin d → ℂ)
      {w | ∀ H : ι, A.normal H w ≠ A.offset H} k β
      (actualFanTriangleAmbient x.val y.val z.val) hboundary =
      A.actualOriginalSegmentCochainValue k β z y -
        A.actualOriginalSegmentCochainValue k β x y -
        A.actualOriginalSegmentCochainValue k β z x := by
  have he₀ (t : I) : actualFanTriangleAmbient x.val y.val z.val (realTriangleFacePath 0 t) =
      actualComplexLinePoint x.val y.val t := by
    simpa only [ite_true] using actualFanTriangleAmbient_face_eq_actual_line x.val y.val z.val 0 t
  have he₁ (t : I) : actualFanTriangleAmbient x.val y.val z.val (realTriangleFacePath 1 t) =
      actualComplexLinePoint z.val y.val t := by
    simpa only [show (1 : Fin 3) ≠ 0 by decide, ite_false, ite_true] using
      actualFanTriangleAmbient_face_eq_actual_line x.val y.val z.val 1 t
  have he₂ (t : I) : actualFanTriangleAmbient x.val y.val z.val (realTriangleFacePath 2 t) =
      actualComplexLinePoint z.val x.val t := by
    simpa only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
      ite_false] using actualFanTriangleAmbient_face_eq_actual_line x.val y.val z.val 2 t
  have hs₀ : ∀ (t : I) (H : ι), A.normal H (actualComplexLinePoint x.val y.val t) ≠ A.offset H := by
    intro t H
    rw [← he₀ t]
    exact hboundary 0 t H
  have hs₁ : ∀ (t : I) (H : ι), A.normal H (actualComplexLinePoint z.val y.val t) ≠ A.offset H := by
    intro t H
    rw [← he₁ t]
    exact hboundary 1 t H
  have hs₂ : ∀ (t : I) (H : ι), A.normal H (actualComplexLinePoint z.val x.val t) ≠ A.offset H := by
    intro t H
    rw [← he₂ t]
    exact hboundary 2 t H
  let U : Set (Fin d → ℂ) := {w | ∀ H : ι, A.normal H w ≠ A.offset H}
  have hf₀ : partialTriangleFacePath (Fin d → ℂ) U
      (actualFanTriangleAmbient x.val y.val z.val) hboundary 0 =
      (A.actualComplementStraightPath x y hs₀).toContinuousMap := by
    apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    exact he₀ t
  have hf₁ : partialTriangleFacePath (Fin d → ℂ) U
      (actualFanTriangleAmbient x.val y.val z.val) hboundary 1 =
      (A.actualComplementStraightPath z y hs₁).toContinuousMap := by
    apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    exact he₁ t
  have hf₂ : partialTriangleFacePath (Fin d → ℂ) U
      (actualFanTriangleAmbient x.val y.val z.val) hboundary 2 =
      (A.actualComplementStraightPath z x hs₂).toContinuousMap := by
    apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    exact he₂ t
  unfold partialTriangleBoundaryValue
  rw [hf₁, hf₂, hf₀]
  rw [A.actualOriginalSegmentCochainValue_of_safe k β z y hs₁,
    A.actualOriginalSegmentCochainValue_of_safe k β x y hs₀,
    A.actualOriginalSegmentCochainValue_of_safe k β z x hs₂]
  simp only [actualPathCochainValue]
  exact sub_right_comm _ _ _

end ChenRanks.AffineArrangement
