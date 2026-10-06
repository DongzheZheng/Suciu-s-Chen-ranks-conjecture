import ChenRanks.CircleStraightPathCocycle

/-!
# A normalized actual closed circle cochain vanishes on every integer turn

The native triangle addition formula and literal periodic path identity
derive this statement for positive and negative integer turns. Its only
normalization input is the actual positive generator value; no circle
cohomology dimension or all-loop detector is postulated.
-/

noncomputable section

namespace ChenRanks.SingularCohomology

variable (k : Type) [Field k]
variable (β : cochains k Circle 1) (hβ : differential k Circle 1 β = 0)
variable (hgenerator : circleStraightPathValue k β 0 (2 * Real.pi) = 0)

include hβ hgenerator

theorem circleStraightPathValue_nat_periods_eq_zero (m : ℕ) :
    circleStraightPathValue k β 0 ((m : ℝ) * (2 * Real.pi)) = 0 := by
  induction m with
  | zero =>
      simpa only [Nat.cast_zero, zero_mul] using
        circleStraightPathValue_self_eq_zero k β hβ 0
  | succ m ih =>
      have hperiod := circleStraightPathValue_periodic k β 0 (2 * Real.pi) (m : ℤ)
      simp only [Int.cast_natCast, zero_add] at hperiod
      have hsum : 2 * Real.pi + (m : ℝ) * (2 * Real.pi) =
          ((m + 1 : ℕ) : ℝ) * (2 * Real.pi) := by
        push_cast
        ring
      rw [hsum] at hperiod
      have hadd := circleStraightPathValue_add k β hβ 0
        ((m : ℝ) * (2 * Real.pi)) (((m + 1 : ℕ) : ℝ) * (2 * Real.pi))
      rw [ih, hperiod, hgenerator, add_zero] at hadd
      exact hadd

theorem circleStraightPathValue_neg_nat_periods_eq_zero (m : ℕ) :
    circleStraightPathValue k β 0 (-((m : ℝ) * (2 * Real.pi))) = 0 := by
  have hperiod := circleStraightPathValue_periodic k β 0
    ((m : ℝ) * (2 * Real.pi)) (-(m : ℤ))
  simp only [Int.cast_neg, Int.cast_natCast, neg_mul, zero_add,
    add_neg_cancel] at hperiod
  have hadd := circleStraightPathValue_add k β hβ 0
    (-((m : ℝ) * (2 * Real.pi))) 0
  rw [circleStraightPathValue_self_eq_zero k β hβ, hperiod,
    circleStraightPathValue_nat_periods_eq_zero k β hβ hgenerator] at hadd
  simpa only [add_zero] using hadd.symm

/-- Actual normalization controls every genuine signed integer turn. -/
theorem circleStraightPathValue_int_periods_eq_zero (n : ℤ) :
    circleStraightPathValue k β 0 ((n : ℝ) * (2 * Real.pi)) = 0 := by
  cases n with
  | ofNat m =>
      simpa only [Int.cast_natCast] using
        circleStraightPathValue_nat_periods_eq_zero k β hβ hgenerator m
  | negSucc m =>
      have hcast : ((Int.negSucc m : ℤ) : ℝ) * (2 * Real.pi) =
          -(((m + 1 : ℕ) : ℝ) * (2 * Real.pi)) := by
        simp <;> ring
      rw [hcast]
      exact circleStraightPathValue_neg_nat_periods_eq_zero k β hβ hgenerator (m + 1)

end ChenRanks.SingularCohomology
