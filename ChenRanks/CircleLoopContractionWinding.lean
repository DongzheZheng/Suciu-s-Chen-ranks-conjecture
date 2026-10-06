import ChenRanks.CirclePathLiftIncrementFormula

/-!
# Zero winding of a genuinely contractible circle loop

The original contraction is lifted by the native covering homotopy
lifting theorem. Its two side paths have identical projections and
identical initial values, so uniqueness gives identical lifted endpoint
values. The top loop therefore has actual integer winding zero. Its
base point may move during contraction.
-/

noncomputable section

open unitInterval

namespace ChenRanks

/-- Any genuine real lift with equal endpoint values computes winding zero
for the original closed circle path. -/
theorem circlePathIntegerIncrement_eq_zero_of_closed_real_lift
    (γ : C(I, Circle)) (hγ : γ 0 = γ 1) (θ : C(I, ℝ))
    (hθ : ∀ t, Circle.exp (θ t) = γ t) (he : θ 0 = θ 1) :
    circlePathIntegerIncrement γ = 0 := by
  have h := circlePathIntegerIncrement_mul_period_eq_lift_difference γ θ hθ
  rw [he, hγ, sub_self, zero_add, sub_self] at h
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_zero]
  exact (mul_eq_zero.mp h).resolve_right (by positivity : (2 : ℝ) * Real.pi ≠ 0)

/-- A true continuous free contraction through actual loops forces zero
winding, without assuming a real lift or a winding identity. -/
theorem circlePathIntegerIncrement_eq_zero_of_loop_contraction
    (γ : C(I, Circle)) (H : C(I × I, Circle)) (z : Circle)
    (h0 : ∀ s, H (0, s) = z)
    (h1 : ∀ s, H (1, s) = γ s)
    (hsides : ∀ t, H (t, 0) = H (t, 1)) :
    circlePathIntegerIncrement γ = 0 := by
  let a : C(I, ℝ) := .const _ (Complex.arg z)
  have hstart : ∀ s, H (0, s) = Circle.exp (a s) := by
    intro s
    change H (0, s) = Circle.exp (Complex.arg z)
    rw [h0 s, Circle.exp_arg]
  let G := Circle.isCoveringMap_exp.liftHomotopy H a hstart
  have hG (t s : I) : Circle.exp (G (t, s)) = H (t, s) :=
    congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts H a hstart) (t, s)
  have hG0 (s : I) : G (0, s) = Complex.arg z :=
    Circle.isCoveringMap_exp.liftHomotopy_zero H a hstart s
  let left : C(I, ℝ) := G.comp ⟨fun t => (t, 0), continuous_id.prodMk continuous_const⟩
  let right : C(I, ℝ) := G.comp ⟨fun t => (t, 1), continuous_id.prodMk continuous_const⟩
  have hside : Circle.exp ∘ left = Circle.exp ∘ right := by
    funext t
    change Circle.exp (G (t, 0)) = Circle.exp (G (t, 1))
    rw [hG t 0, hG t 1, hsides t]
  have hside0 : left 0 = right 0 := by
    change G (0, 0) = G (0, 1)
    rw [hG0 0, hG0 1]
  have hlr : (left : I → ℝ) = right :=
    Circle.isCoveringMap_exp.eq_of_comp_eq left.continuous right.continuous hside 0 hside0
  let θ : C(I, ℝ) := G.comp ⟨fun s => (1, s), continuous_const.prodMk continuous_id⟩
  have hθ (s : I) : Circle.exp (θ s) = γ s := (hG 1 s).trans (h1 s)
  have he : θ 0 = θ 1 := congrFun hlr 1
  have hγ : γ 0 = γ 1 := (h1 0).symm.trans ((hsides 1).trans (h1 1))
  exact circlePathIntegerIncrement_eq_zero_of_closed_real_lift γ hγ θ hθ he

end ChenRanks
