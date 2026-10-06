import ChenRanks.ArrangementFanTriangleFiniteZeros
import ChenRanks.ArrangementComplexLinePaths
import ChenRanks.SingularSquareTriangleGeometry
import ChenRanks.RealTriangleBoundaryPoints

/-!
# Actual boundary avoidance for the constructed original fan

The original affine equations and actual radial-line avoidances prove
both center rays stay in the original complement. The third boundary
is the actual original straight edge. No boundary detector is assumed.
-/

noncomputable section

open unitInterval

namespace ChenRanks

theorem complex_real_two_weight_sum_ne_zero
    (u v : ℂ) (hu : u ≠ 0) (hv : v ∉ Submodule.span ℝ ({u} : Set ℂ))
    (r s : ℝ) (hrs : r + s = 1) : r • u + s • v ≠ 0 := by
  intro h
  have hc := real_two_term_coefficients_eq_zero u v hu hv r s h
  linarith [hc.1, hc.2]

namespace AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

theorem actualFanTriangleAmbient_eq_real_sum
    (x y z : Fin d → ℂ) (p : stdSimplex ℝ (Fin 3)) :
    actualFanTriangleAmbient x y z p = p 0 • z + p 1 • x + p 2 • y := by
  funext j
  change (p 0 : ℂ) • z j + (p 1 : ℂ) • x j + (p 2 : ℂ) • y j =
    p 0 • z j + p 1 • x j + p 2 • y j
  simp only [Complex.coe_smul]
  rfl

theorem actualFanTriangleAmbient_face_eq_actual_line
    (x y z : Fin d → ℂ) (i : Fin 3) (t : I) :
    actualFanTriangleAmbient x y z (SingularCohomology.realTriangleFacePath i t) =
      if i = 0 then actualComplexLinePoint x y t
      else if i = 1 then actualComplexLinePoint z y t else actualComplexLinePoint z x t := by
  fin_cases i <;> funext j
  · simp [actualFanTriangleAmbient,
      SingularCohomology.realTriangleFacePath_coordinate, Fin.succAbove,
      actualComplexLinePoint, Pi.add_apply]
    change ((1 - (t : ℝ) : ℝ) : ℂ) * x j + (t : ℂ) * y j =
      x j + (t : ℂ) * (y j - x j)
    push_cast
    ring
  · simp [actualFanTriangleAmbient,
      SingularCohomology.realTriangleFacePath_coordinate, Fin.succAbove,
      actualComplexLinePoint, Pi.add_apply]
    change ((1 - (t : ℝ) : ℝ) : ℂ) * z j + (t : ℂ) * y j =
      z j + (t : ℂ) * (y j - z j)
    push_cast
    ring
  · simp [actualFanTriangleAmbient,
      SingularCohomology.realTriangleFacePath_coordinate, Fin.succAbove,
      actualComplexLinePoint, Pi.add_apply]
    change ((1 - (t : ℝ) : ℝ) : ℂ) * z j + (t : ℂ) * x j =
      z j + (t : ℂ) * (x j - z j)
    push_cast
    ring

/-- Both genuinely constructed fan rays avoid every original
hyperplane, by the actual two-direction independence. -/
theorem actualFan_radial_line_mem_complement
    (x z : A.Complement)
    (hspan : ∀ H : ι, A.normal H z.val - A.offset H ∉
      Submodule.span ℝ ({A.normal H x.val - A.offset H} : Set ℂ)) (t : I) :
    ∀ H : ι, A.normal H (actualComplexLinePoint z.val x.val t) ≠ A.offset H := by
  intro H hzero
  have h := complex_real_two_weight_sum_ne_zero
    (A.normal H x.val - A.offset H) (A.normal H z.val - A.offset H)
    (sub_ne_zero.mpr (x.property H)) (hspan H) (t : ℝ) (1 - (t : ℝ)) (by ring)
  apply h
  change (t : ℂ) * (A.normal H x.val - A.offset H) +
    ((1 - (t : ℝ) : ℝ) : ℂ) * (A.normal H z.val - A.offset H) = 0
  push_cast
  change A.normal H (z.val + (t : ℂ) • (x.val - z.val)) = A.offset H at hzero
  simp only [map_add, map_smul, map_sub, smul_eq_mul] at hzero
  linear_combination hzero

theorem actualFanTriangle_boundary_mem_complement
    (x y z : A.Complement)
    (hxz : ∀ H : ι, A.normal H z.val - A.offset H ∉
      Submodule.span ℝ ({A.normal H x.val - A.offset H} : Set ℂ))
    (hyz : ∀ H : ι, A.normal H z.val - A.offset H ∉
      Submodule.span ℝ ({A.normal H y.val - A.offset H} : Set ℂ))
    (hedge : ∀ t : I, ∀ H : ι,
      A.normal H (actualComplexLinePoint x.val y.val t) ≠ A.offset H)
    (i : Fin 3) (t : I) : ∀ H : ι,
    A.normal H (actualFanTriangleAmbient x.val y.val z.val
      (SingularCohomology.realTriangleFacePath i t)) ≠ A.offset H := by
  rw [actualFanTriangleAmbient_face_eq_actual_line]
  fin_cases i
  · exact hedge t
  · exact A.actualFan_radial_line_mem_complement y z hyz t
  · exact A.actualFan_radial_line_mem_complement x z hxz t

end AffineArrangement
end ChenRanks
