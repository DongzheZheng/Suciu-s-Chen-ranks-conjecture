import ChenRanks.PhaseGridClosingPaths
import ChenRanks.CircleSingularWindingCocycle
import ChenRanks.SingularPathCocycleAdditivity

/-!
# Actual winding of coordinate segments and rectangles

The values here are computed from genuine continuous real argument
lifts of the genuine nonzero paths. A path in the slit plane uses its
principal argument. A path in the left half-plane uses arg(-z)+π, so
its true integer increment is the change of the actual lower-half-plane
endpoint indicator. There is no assigned winding table in the inputs.
-/

noncomputable section

open unitInterval

namespace ChenRanks

/-- Actual concatenation additivity comes from evaluating the proved
native singular winding cocycle on the proved concatenation triangle. -/
theorem circlePathIntegerIncrement_native_trans {x y z : Circle}
    (p : Path x y) (q : Path y z) :
    circlePathIntegerIncrement (p.trans q).toContinuousMap =
      circlePathIntegerIncrement p.toContinuousMap +
        circlePathIntegerIncrement q.toContinuousMap := by
  have h := SingularCohomology.actualPathCochainValue_trans ℝ Circle
    (SingularCohomology.circleWindingCochain ℝ)
    (SingularCohomology.differential_circleWindingCochain_eq_zero ℝ) p q
  apply Int.cast_injective (α := ℝ)
  simpa only [Int.cast_add, SingularCohomology.actualPathCochainValue,
    SingularCohomology.values_circleWindingCochain, SingularCohomology.circleWindingValue,
    SingularCohomology.geometricSimplexPath_simplexOfPath] using h

/-- The actual principal-argument lift of a path that genuinely stays
in the slit plane. -/
def slitPlanePathArgumentLift (γ : C(I, NonzeroComplex))
    (hγ : ∀ t, (γ t : ℂ) ∈ Complex.slitPlane) : C(I, ℝ) where
  toFun t := Complex.arg (γ t : ℂ)
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (Complex.continuousAt_arg (hγ t)).comp
      (f := fun s : I => (γ s : ℂ)) (x := t)
      (continuous_subtype_val.comp γ.continuous).continuousAt

/-- A genuine slit-plane path has actual integer increment zero,
proved from the genuine real lift and the selected endpoint arguments. -/
theorem circlePathIntegerIncrement_slitPlane (γ : C(I, NonzeroComplex))
    (hγ : ∀ t, (γ t : ℂ) ∈ Complex.slitPlane) :
    circlePathIntegerIncrement (nonzeroComplexCircleMap.comp γ) = 0 := by
  let θ := slitPlanePathArgumentLift γ hγ
  have hp (t : I) : Circle.exp (θ t) = nonzeroComplexCircleMap (γ t) := rfl
  have h := circlePathIntegerIncrement_mul_period_eq_lift_difference
    (nonzeroComplexCircleMap.comp γ) θ hp
  change (circlePathIntegerIncrement (nonzeroComplexCircleMap.comp γ) : ℝ) *
      (2 * Real.pi) = θ 1 - θ 0 +
        Complex.arg (nonzeroComplexCircleMap (γ 0) : ℂ) -
        Complex.arg (nonzeroComplexCircleMap (γ 1) : ℂ) at h
  rw [nonzeroComplexCircleMap_arg, nonzeroComplexCircleMap_arg] at h
  change (circlePathIntegerIncrement (nonzeroComplexCircleMap.comp γ) : ℝ) *
      (2 * Real.pi) = Complex.arg (γ 1 : ℂ) - Complex.arg (γ 0 : ℂ) +
        Complex.arg (γ 0 : ℂ) - Complex.arg (γ 1 : ℂ) at h
  have hn : (circlePathIntegerIncrement (nonzeroComplexCircleMap.comp γ) : ℝ) *
      (2 * Real.pi) = 0 := by linear_combination h
  apply Int.cast_injective (α := ℝ)
  simpa only [Int.cast_zero] using
    (mul_eq_zero.mp hn).resolve_right (by positivity : (2 : ℝ) * Real.pi ≠ 0)

/-- The endpoint indicator used by the genuine reflected argument.
It records the original imaginary part, rather than an assigned winding. -/
def lowerHalfPlaneIndicator (y : ℝ) : ℤ := if y < 0 then 1 else 0

private theorem reflectedArgument_endpoint (z : ℂ) (hz : z.re < 0) :
    Complex.arg (-z) + Real.pi = Complex.arg z +
      (lowerHalfPlaneIndicator z.im : ℝ) * (2 * Real.pi) := by
  by_cases hi : z.im < 0
  · rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg hi]
    simp only [lowerHalfPlaneIndicator, if_pos hi, Int.cast_one, one_mul]
    ring
  · have harg : Complex.arg (-z) = Complex.arg z - Real.pi := by
      apply Complex.arg_neg_eq_arg_sub_pi_iff.mpr
      by_cases hip : 0 < z.im
      · exact Or.inl hip
      · exact Or.inr ⟨le_antisymm (le_of_not_gt hip) (le_of_not_gt hi), hz⟩
    rw [harg]
    simp only [lowerHalfPlaneIndicator, if_neg hi, Int.cast_zero, zero_mul, add_zero]
    ring

/-- A genuine left-half-plane path has the continuous real lift
arg(-z)+π; the reflected path lies in the actual right half-plane. -/
def leftHalfPlanePathArgumentLift (γ : C(I, NonzeroComplex))
    (hγ : ∀ t, (γ t : ℂ).re < 0) : C(I, ℝ) where
  toFun t := Complex.arg (-(γ t : ℂ)) + Real.pi
  continuous_toFun := by
    apply Continuous.add _ continuous_const
    apply continuous_iff_continuousAt.mpr
    intro t
    have ht : -(γ t : ℂ) ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      exact Or.inl (by simpa only [Complex.neg_re] using neg_pos.mpr (hγ t))
    exact (Complex.continuousAt_arg ht).comp
      (f := fun s : I => -(γ s : ℂ)) (x := t)
      (continuous_subtype_val.comp γ.continuous).neg.continuousAt

/-- Its exponential is the actual original phase at every point. -/
theorem leftHalfPlanePathArgumentLift_projects (γ : C(I, NonzeroComplex))
    (hγ : ∀ t, (γ t : ℂ).re < 0) (t : I) :
    Circle.exp (leftHalfPlanePathArgumentLift γ hγ t) = nonzeroComplexCircleMap (γ t) := by
  change Circle.exp (Complex.arg (-(γ t : ℂ)) + Real.pi) =
    Circle.exp (Complex.arg (γ t : ℂ))
  rw [reflectedArgument_endpoint _ (hγ t), Circle.exp_add,
    Circle.exp_int_mul_two_pi, mul_one]

/-- The genuine left-half-plane increment is the actual change of the
lower-half-plane endpoint indicator, by the proved real-lift formula. -/
theorem circlePathIntegerIncrement_leftHalfPlane (γ : C(I, NonzeroComplex))
    (hγ : ∀ t, (γ t : ℂ).re < 0) :
    circlePathIntegerIncrement (nonzeroComplexCircleMap.comp γ) =
      lowerHalfPlaneIndicator (γ 1 : ℂ).im - lowerHalfPlaneIndicator (γ 0 : ℂ).im := by
  let θ := leftHalfPlanePathArgumentLift γ hγ
  have h := circlePathIntegerIncrement_mul_period_eq_lift_difference
    (nonzeroComplexCircleMap.comp γ) θ (leftHalfPlanePathArgumentLift_projects γ hγ)
  change (circlePathIntegerIncrement (nonzeroComplexCircleMap.comp γ) : ℝ) *
      (2 * Real.pi) = (Complex.arg (-(γ 1 : ℂ)) + Real.pi) -
        (Complex.arg (-(γ 0 : ℂ)) + Real.pi) +
        Complex.arg (nonzeroComplexCircleMap (γ 0) : ℂ) -
        Complex.arg (nonzeroComplexCircleMap (γ 1) : ℂ) at h
  rw [reflectedArgument_endpoint _ (hγ 1), reflectedArgument_endpoint _ (hγ 0),
    nonzeroComplexCircleMap_arg, nonzeroComplexCircleMap_arg] at h
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_sub]
  apply mul_right_cancel₀ (by positivity : (2 : ℝ) * Real.pi ≠ 0)
  linear_combination h

private theorem coordinate_ne_zero_of_re_ne_zero (x y : ℝ) (hx : x ≠ 0) :
    (⟨x, y⟩ : ℂ) ≠ 0 := by
  intro h
  apply hx
  exact congrArg Complex.re h

private theorem coordinate_ne_zero_of_im_ne_zero (x y : ℝ) (hy : y ≠ 0) :
    (⟨x, y⟩ : ℂ) ≠ 0 := by
  intro h
  apply hy
  exact congrArg Complex.im h

/-- An actual vertical nonzero segment. Its fixed real coordinate
supplies genuine puncture avoidance. -/
def nonzeroComplexVerticalSegment (x : ℝ) (hx : x ≠ 0) (a b : ℝ) :
    Path (⟨⟨x, a⟩, coordinate_ne_zero_of_re_ne_zero x a hx⟩ : NonzeroComplex)
      ⟨⟨x, b⟩, coordinate_ne_zero_of_re_ne_zero x b hx⟩ where
  toFun t := ⟨⟨x, (1 - (t : ℝ)) * a + (t : ℝ) * b⟩,
    coordinate_ne_zero_of_re_ne_zero _ _ hx⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  source' := by apply Subtype.ext; apply Complex.ext <;> simp
  target' := by apply Subtype.ext; apply Complex.ext <;> simp

/-- An actual horizontal nonzero segment. Its fixed imaginary coordinate
supplies genuine puncture avoidance. -/
def nonzeroComplexHorizontalSegment (y : ℝ) (hy : y ≠ 0) (a b : ℝ) :
    Path (⟨⟨a, y⟩, coordinate_ne_zero_of_im_ne_zero a y hy⟩ : NonzeroComplex)
      ⟨⟨b, y⟩, coordinate_ne_zero_of_im_ne_zero b y hy⟩ where
  toFun t := ⟨⟨(1 - (t : ℝ)) * a + (t : ℝ) * b, y⟩,
    coordinate_ne_zero_of_im_ne_zero _ _ hy⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  source' := by apply Subtype.ext; apply Complex.ext <;> simp
  target' := by apply Subtype.ext; apply Complex.ext <;> simp

/-- Every actual horizontal segment away from the puncture has zero
actual covering increment. -/
theorem nonzeroComplexHorizontalSegment_increment (y : ℝ) (hy : y ≠ 0) (a b : ℝ) :
    circlePathIntegerIncrement (nonzeroComplexCircleMap.comp
      (nonzeroComplexHorizontalSegment y hy a b).toContinuousMap) = 0 := by
  apply circlePathIntegerIncrement_slitPlane
  intro t
  apply Complex.mem_slitPlane_iff.mpr
  exact Or.inr hy

/-- Every actual vertical segment has its genuine endpoint formula.
The formula is derived from the real argument branches above. -/
theorem nonzeroComplexVerticalSegment_increment (x : ℝ) (hx : x ≠ 0) (a b : ℝ) :
    circlePathIntegerIncrement (nonzeroComplexCircleMap.comp
      (nonzeroComplexVerticalSegment x hx a b).toContinuousMap) =
      if x < 0 then lowerHalfPlaneIndicator b - lowerHalfPlaneIndicator a else 0 := by
  by_cases hneg : x < 0
  · rw [if_pos hneg]
    have h := circlePathIntegerIncrement_leftHalfPlane
      (nonzeroComplexVerticalSegment x hx a b).toContinuousMap (fun _ => hneg)
    simpa only [Path.coe_toContinuousMap, Path.source, Path.target] using h
  · rw [if_neg hneg]
    apply circlePathIntegerIncrement_slitPlane
    intro t
    apply Complex.mem_slitPlane_iff.mpr
    exact Or.inl (lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hx))

/-- The actual four-segment coordinate rectangle loop, with no assumption
that the puncture lies inside or outside it. The nonzero fixed boundary
coordinates supply actual avoidance for every one of its four edges. -/
def nonzeroComplexRectangleLoop (x₀ x₁ y₀ y₁ : ℝ)
    (hx₀ : x₀ ≠ 0) (hx₁ : x₁ ≠ 0) (hy₀ : y₀ ≠ 0) (hy₁ : y₁ ≠ 0) :
    Path (⟨⟨x₀, y₀⟩, coordinate_ne_zero_of_im_ne_zero x₀ y₀ hy₀⟩ : NonzeroComplex)
      ⟨⟨x₀, y₀⟩, coordinate_ne_zero_of_im_ne_zero x₀ y₀ hy₀⟩ :=
  (((nonzeroComplexHorizontalSegment y₀ hy₀ x₀ x₁).trans
    (nonzeroComplexVerticalSegment x₁ hx₁ y₀ y₁)).trans
    (nonzeroComplexHorizontalSegment y₁ hy₁ x₁ x₀)).trans
    (nonzeroComplexVerticalSegment x₀ hx₀ y₁ y₀)

private theorem phaseMappedPath_increment {z w : NonzeroComplex} (p : Path z w) :
    circlePathIntegerIncrement (p.map nonzeroComplexCircleMap.continuous).toContinuousMap =
      circlePathIntegerIncrement (nonzeroComplexCircleMap.comp p.toContinuousMap) := rfl

/-- The actual rectangle winding is computed by the genuine four edge
increments. This formula includes degeneracies and either orientation;
no expected winding or inside/outside detector is a premise. -/
theorem nonzeroComplexRectangleLoop_increment (x₀ x₁ y₀ y₁ : ℝ)
    (hx₀ : x₀ ≠ 0) (hx₁ : x₁ ≠ 0) (hy₀ : y₀ ≠ 0) (hy₁ : y₁ ≠ 0) :
    circlePathIntegerIncrement (nonzeroComplexCircleMap.comp
      (nonzeroComplexRectangleLoop x₀ x₁ y₀ y₁ hx₀ hx₁ hy₀ hy₁).toContinuousMap) =
      (if x₁ < 0 then lowerHalfPlaneIndicator y₁ - lowerHalfPlaneIndicator y₀ else 0) +
        (if x₀ < 0 then lowerHalfPlaneIndicator y₀ - lowerHalfPlaneIndicator y₁ else 0) := by
  change circlePathIntegerIncrement
    ((nonzeroComplexRectangleLoop x₀ x₁ y₀ y₁ hx₀ hx₁ hy₀ hy₁).map
      nonzeroComplexCircleMap.continuous).toContinuousMap = _
  simp only [nonzeroComplexRectangleLoop, Path.map_trans,
    circlePathIntegerIncrement_native_trans, phaseMappedPath_increment,
    nonzeroComplexHorizontalSegment_increment, nonzeroComplexVerticalSegment_increment,
    zero_add, add_zero]

/-- A counterclockwise genuine rectangle around the puncture has actual
winding +1, derived from the actual argument branches rather than an
assigned orientation convention. -/
theorem nonzeroComplexRectangleLoop_increment_eq_one
    (x₀ x₁ y₀ y₁ : ℝ) (hx₀ : x₀ < 0) (hx₁ : 0 < x₁)
    (hy₀ : y₀ < 0) (hy₁ : 0 < y₁) :
    circlePathIntegerIncrement (nonzeroComplexCircleMap.comp
      (nonzeroComplexRectangleLoop x₀ x₁ y₀ y₁
        hx₀.ne hx₁.ne.symm hy₀.ne hy₁.ne.symm).toContinuousMap) = 1 := by
  rw [nonzeroComplexRectangleLoop_increment,
    if_neg (not_lt.mpr hx₁.le), if_pos hx₀]
  simp only [lowerHalfPlaneIndicator, if_pos hy₀, if_neg (not_lt.mpr hy₁.le),
    zero_add, sub_zero]

/-- Reversing the vertical orientation gives actual winding -1.
This is the negative-coordinate sign test for the rectangle mechanism. -/
theorem nonzeroComplexRectangleLoop_increment_eq_neg_one
    (x₀ x₁ y₀ y₁ : ℝ) (hx₀ : x₀ < 0) (hx₁ : 0 < x₁)
    (hy₀ : 0 < y₀) (hy₁ : y₁ < 0) :
    circlePathIntegerIncrement (nonzeroComplexCircleMap.comp
      (nonzeroComplexRectangleLoop x₀ x₁ y₀ y₁
        hx₀.ne hx₁.ne.symm hy₀.ne.symm hy₁.ne).toContinuousMap) = -1 := by
  rw [nonzeroComplexRectangleLoop_increment,
    if_neg (not_lt.mpr hx₁.le), if_pos hx₀]
  simp only [lowerHalfPlaneIndicator, if_neg (not_lt.mpr hy₀.le), if_pos hy₁,
    zero_add, zero_sub]

/-- A genuine rectangle wholly to the right of the puncture has actual
winding zero, even if its imaginary coordinate interval crosses zero. -/
theorem nonzeroComplexRectangleLoop_increment_eq_zero_of_re_pos
    (x₀ x₁ y₀ y₁ : ℝ) (hx₀ : 0 < x₀) (hx₁ : 0 < x₁)
    (hy₀ : y₀ ≠ 0) (hy₁ : y₁ ≠ 0) :
    circlePathIntegerIncrement (nonzeroComplexCircleMap.comp
      (nonzeroComplexRectangleLoop x₀ x₁ y₀ y₁
        hx₀.ne.symm hx₁.ne.symm hy₀ hy₁).toContinuousMap) = 0 := by
  rw [nonzeroComplexRectangleLoop_increment,
    if_neg (not_lt.mpr hx₁.le), if_neg (not_lt.mpr hx₀.le), add_zero]

end ChenRanks
