import ChenRanks.ArrangementMeridianCircle
import ChenRanks.CircleLoopContractionWinding

/-! Uncompiled source preparation, outside the active Lean inventory.

Every other actual equation stays nonzero on the proved actual small
normal disk. Radial contraction therefore gives a genuine continuous
free contraction of its actual equation-phase loop. The covering
homotopy theorem then proves winding zero. The final statement uses the
disk constructed from the original arrangement, not a supplied disk.
No first-cohomology spanning theorem or Orlik--Solomon comparison is
asserted.
-/

noncomputable section

open unitInterval

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance : DecidableEq ι := Classical.decEq ι

/-- Radial contraction remains in the punctured plane for every other
actual hyperplane equation, because the whole actual disk avoids it. -/
def meridianDiskOtherEquationContractionNonzeroMap
    (H : ι) (m : A.MeridianDisk H) (K : ι) (hKH : K ≠ H) :
    C(I × I, NonzeroComplex) where
  toFun st := ⟨A.normal K
    (m.center + (((st.1 : ℝ) : ℂ) *
      ((m.radius : ℂ) * (positiveUnitCircleTraversal st.2 : ℂ))) •
        m.normalVector) - A.offset K, by
    apply sub_ne_zero.mpr
    apply m.disk_avoids _ _ K hKH
    simp only [norm_mul, Complex.norm_of_nonneg st.1.property.1,
      Complex.norm_of_nonneg m.radius_pos.le, Circle.norm_coe, mul_one]
    nlinarith [st.1.property.2, m.radius_pos]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hc : Continuous (fun st : I × I =>
        m.center + (((st.1 : ℝ) : ℂ) *
          ((m.radius : ℂ) * (positiveUnitCircleTraversal st.2 : ℂ))) •
            m.normalVector) := by fun_prop
    exact ((A.normal K).continuous_of_finiteDimensional.comp hc).sub continuous_const

/-- This is an actual circle-valued free contraction, obtained from
the original nonzero equation on the actual geometric disk. -/
def meridianDiskOtherEquationContraction
    (H : ι) (m : A.MeridianDisk H) (K : ι) (hKH : K ≠ H) :
    C(I × I, Circle) :=
  nonzeroComplexCircleMap.comp
    (A.meridianDiskOtherEquationContractionNonzeroMap H m K hKH)

/-- The actual phase at the actual disk center. -/
def meridianDiskOtherEquationCenterPhase
    (H : ι) (m : A.MeridianDisk H) (K : ι) (hKH : K ≠ H) : Circle :=
  nonzeroComplexCircleMap
    ⟨A.normal K m.center - A.offset K, sub_ne_zero.mpr (m.center_avoids K hKH)⟩

/-- At radial parameter zero the contraction is genuinely constant. -/
theorem meridianDiskOtherEquationContraction_zero
    (H : ι) (m : A.MeridianDisk H) (K : ι) (hKH : K ≠ H) (s : I) :
    A.meridianDiskOtherEquationContraction H m K hKH (0, s) =
      A.meridianDiskOtherEquationCenterPhase H m K hKH := by
  apply congrArg nonzeroComplexCircleMap
  apply Subtype.ext
  change A.normal K
      (m.center + ((((0 : I) : ℝ) : ℂ) *
        ((m.radius : ℂ) * (positiveUnitCircleTraversal s : ℂ))) • m.normalVector) -
          A.offset K = A.normal K m.center - A.offset K
  simp

/-- At radial parameter one it is the actual equation-phase loop. -/
theorem meridianDiskOtherEquationContraction_one
    (H : ι) (m : A.MeridianDisk H) (K : ι) (hKH : K ≠ H) (s : I) :
    A.meridianDiskOtherEquationContraction H m K hKH (1, s) =
      ((A.equationComplementCircleMap K).comp (A.meridianDiskPathMap H m)) s := by
  apply congrArg nonzeroComplexCircleMap
  apply Subtype.ext
  change A.normal K
      (m.center + ((((1 : I) : ℝ) : ℂ) *
        ((m.radius : ℂ) * (positiveUnitCircleTraversal s : ℂ))) • m.normalVector) -
          A.offset K =
    A.normal K
      (m.center + ((m.radius : ℂ) * (positiveUnitCircleTraversal s : ℂ)) •
        m.normalVector) - A.offset K
  simp

/-- Every intermediate path is genuinely a loop; no fixed based-point
condition is needed for the actual covering-space argument. -/
theorem meridianDiskOtherEquationContraction_sides
    (H : ι) (m : A.MeridianDisk H) (K : ι) (hKH : K ≠ H) (t : I) :
    A.meridianDiskOtherEquationContraction H m K hKH (t, 0) =
      A.meridianDiskOtherEquationContraction H m K hKH (t, 1) := by
  apply congrArg nonzeroComplexCircleMap
  apply Subtype.ext
  change A.normal K
      (m.center + (((t : ℝ) : ℂ) *
        ((m.radius : ℂ) * (positiveUnitCircleTraversal 0 : ℂ))) • m.normalVector) -
          A.offset K =
    A.normal K
      (m.center + (((t : ℝ) : ℂ) *
        ((m.radius : ℂ) * (positiveUnitCircleTraversal 1 : ℂ))) • m.normalVector) -
          A.offset K
  rw [positiveUnitCircleTraversal_zero, positiveUnitCircleTraversal_one]

/-- Every other actual equation has zero genuine integer winding on
the actual small meridian, by its constructed disk contraction. -/
theorem meridianDiskPathMap_other_increment_zero
    (H : ι) (m : A.MeridianDisk H) (K : ι) (hKH : K ≠ H) :
    circlePathIntegerIncrement
      ((A.equationComplementCircleMap K).comp (A.meridianDiskPathMap H m)) = 0 :=
  circlePathIntegerIncrement_eq_zero_of_loop_contraction
    ((A.equationComplementCircleMap K).comp (A.meridianDiskPathMap H m))
    (A.meridianDiskOtherEquationContraction H m K hKH)
    (A.meridianDiskOtherEquationCenterPhase H m K hKH)
    (A.meridianDiskOtherEquationContraction_zero H m K hKH)
    (A.meridianDiskOtherEquationContraction_one H m K hKH)
    (A.meridianDiskOtherEquationContraction_sides H m K hKH)

/-- An actual constructed meridian has the genuine Kronecker winding
vector for the original hyperplanes. No point, disk, or winding data is
an input to this statement. -/
theorem actualMeridianPathMap_equation_increment (H K : ι) :
    circlePathIntegerIncrement
      ((A.equationComplementCircleMap K).comp
        (A.meridianDiskPathMap H (A.actualMeridianDisk H))) =
      if K = H then 1 else 0 := by
  classical
  by_cases hKH : K = H
  · subst K
    rw [if_pos rfl]
    exact A.meridianDiskPathMap_distinguished_increment H (A.actualMeridianDisk H)
  · rw [if_neg hKH]
    exact A.meridianDiskPathMap_other_increment_zero H (A.actualMeridianDisk H) K hKH

end ChenRanks.AffineArrangement
