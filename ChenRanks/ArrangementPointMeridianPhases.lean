import ChenRanks.ArrangementPointMeridianSquare
import ChenRanks.NonzeroComplexPhaseMultiplication

/-! Actual incident-equation phases of genuine original localized squares. -/

noncomputable section
open unitInterval
namespace ChenRanks

/-- Positive real multiplication preserves the true phase of any actual nonzero number. -/
theorem nonzeroComplexCircleMap_positive_scale (r : ℝ) (hr : 0 < r)
    (z : NonzeroComplex) :
    nonzeroComplexCircleMap
        ⟨(r : ℂ) * (z : ℂ), mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') z.property⟩ =
      nonzeroComplexCircleMap z := by
  change Circle.exp (Complex.arg ((r : ℂ) * (z : ℂ))) = Circle.exp (Complex.arg (z : ℂ))
  rw [Complex.arg_real_mul _ hr]

namespace AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The original incident equation is computed on the actual constructed square. -/
theorem actualPointMeridianSquare_incident_equation (x : Fin d → ℂ)
    (H K : A.PointLocalizedLabels x) (p : I × I) :
    (A.equationComplementNonzeroComplexMap K.val (A.actualPointMeridianSquare x H p) : ℂ) =
      (A.actualPointMeridianScale x H : ℂ) * (positiveUnitCircleTraversal p.1 : ℂ) *
        ((A.pointLocalizedArrangement x).equationComplementNonzeroComplexMap K
          ((A.pointLocalizedArrangement x).meridianDiskPathMap H
            ((A.pointLocalizedArrangement x).actualMeridianDisk H) p.2) : ℂ) := by
  change A.normal K (x + ((A.actualPointMeridianScale x H : ℂ) *
      (positiveUnitCircleTraversal p.1 : ℂ)) •
        ((A.pointLocalizedArrangement x).meridianDiskPathMap H
          ((A.pointLocalizedArrangement x).actualMeridianDisk H) p.2).val) - A.offset K =
    (A.actualPointMeridianScale x H : ℂ) * (positiveUnitCircleTraversal p.1 : ℂ) *
      (A.normal K
        ((A.pointLocalizedArrangement x).meridianDiskPathMap H
          ((A.pointLocalizedArrangement x).actualMeridianDisk H) p.2).val - 0)
  rw [map_add, K.property, map_smul, smul_eq_mul, sub_zero]
  ring

/-- The true incident phase is the scalar circle times the actual localized meridian phase. -/
theorem actualPointMeridianSquare_incident_phase (x : Fin d → ℂ)
    (H K : A.PointLocalizedLabels x) (p : I × I) :
    A.equationComplementCircleMap K.val (A.actualPointMeridianSquare x H p) =
      positiveUnitCircleTraversal p.1 *
        (A.pointLocalizedArrangement x).equationComplementCircleMap K
          ((A.pointLocalizedArrangement x).meridianDiskPathMap H
            ((A.pointLocalizedArrangement x).actualMeridianDisk H) p.2) := by
  let u := positiveUnitCircleTraversal p.1
  let w := (A.pointLocalizedArrangement x).equationComplementNonzeroComplexMap K
    ((A.pointLocalizedArrangement x).meridianDiskPathMap H
      ((A.pointLocalizedArrangement x).actualMeridianDisk H) p.2)
  let z : NonzeroComplex := ⟨(u : ℂ) * (w : ℂ), mul_ne_zero u.coe_ne_zero w.property⟩
  have heq : A.equationComplementNonzeroComplexMap K.val
      (A.actualPointMeridianSquare x H p) =
      ⟨(A.actualPointMeridianScale x H : ℂ) * (z : ℂ),
        mul_ne_zero (Complex.ofReal_ne_zero.mpr (A.actualPointMeridianScale_pos x H).ne')
          z.property⟩ := by
    apply Subtype.ext
    rw [A.actualPointMeridianSquare_incident_equation]
    change (A.actualPointMeridianScale x H : ℂ) * (u : ℂ) * (w : ℂ) =
      (A.actualPointMeridianScale x H : ℂ) * ((u : ℂ) * (w : ℂ))
    exact mul_assoc _ _ _
  change nonzeroComplexCircleMap
    (A.equationComplementNonzeroComplexMap K.val (A.actualPointMeridianSquare x H p)) = _
  rw [heq, nonzeroComplexCircleMap_positive_scale _ (A.actualPointMeridianScale_pos x H) z]
  rw [nonzeroComplexCircleMap_mul ⟨(u : ℂ), u.coe_ne_zero⟩ w,
    nonzeroComplexCircleMap_circle]
  rfl

end AffineArrangement
end ChenRanks
