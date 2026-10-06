import ChenRanks.GroupLowerCentralPieceJacobi
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Lie.Basic

/-!
# The genuine rational associated Lie algebra of a group

The underlying space is the native direct sum of the rationalizations
of the original lower-central successive quotients. Its bracket is the
actual quotient commutator, extended by the actual direct-sum universal
property. Antisymmetry and Jacobi are derived from original commutator
identities. No Lie bracket, Jacobi, formality, or higher comparison is
provided as an input.

Component `n` has ordinary positive degree `n+1`. Accordingly, the
actual bracket of components `m,n` lands in native component `m+n+1`.
-/

noncomputable section

open scoped DirectSum TensorProduct

namespace ChenRanks

variable (G : Type*) [Group G]

/-- The native direct sum of the actual rationalized original LCS
pieces, with the original group retained in every summand. -/
abbrev rationalGroupAssociatedGraded := ⨁ n : ℕ, rationalLowerCentralPiece G n

/-- The actual inclusion of one original rationalized quotient. -/
def rationalGroupGradedInclusion (n : ℕ) :
    rationalLowerCentralPiece G n →ₗ[ℚ] rationalGroupAssociatedGraded G :=
  DirectSum.lof ℚ ℕ (rationalLowerCentralPiece G) n

theorem rationalGroupGradedInclusion_reindex {r s : ℕ} (h : r = s)
    (x : rationalLowerCentralPiece G r) :
    rationalGroupGradedInclusion G s (rationalLowerCentralPieceReindex G h x) =
      rationalGroupGradedInclusion G r x := by
  cases h
  rfl

/-- The actual bilinear extension from the original pieces, not a
bracket specified by an expected Lie structure. -/
def rationalGroupGradedBracket :
    rationalGroupAssociatedGraded G →ₗ[ℚ]
      (rationalGroupAssociatedGraded G →ₗ[ℚ] rationalGroupAssociatedGraded G) :=
  DirectSum.toModule ℚ ℕ
    (rationalGroupAssociatedGraded G →ₗ[ℚ] rationalGroupAssociatedGraded G)
    (fun m =>
      (DirectSum.toModule ℚ ℕ
        (rationalLowerCentralPiece G m →ₗ[ℚ] rationalGroupAssociatedGraded G)
        (fun n =>
          ((rationalLowerCentralPieceBracket G m n).compr₂
            (rationalGroupGradedInclusion G (m + n + 1))).flip)).flip)

@[simp] theorem rationalGroupGradedBracket_inclusions (m n : ℕ)
    (x : rationalLowerCentralPiece G m) (y : rationalLowerCentralPiece G n) :
    rationalGroupGradedBracket G (rationalGroupGradedInclusion G m x)
      (rationalGroupGradedInclusion G n y) =
      rationalGroupGradedInclusion G (m + n + 1)
        (rationalLowerCentralPieceBracket G m n x y) := by
  simp only [rationalGroupGradedBracket, rationalGroupGradedInclusion,
    DirectSum.toModule_lof, LinearMap.flip_apply, LinearMap.compr₂_apply]

/-- Antisymmetry on all actual direct-sum elements. -/
theorem rationalGroupGradedBracket_swap
    (x y : rationalGroupAssociatedGraded G) :
    rationalGroupGradedBracket G y x = -rationalGroupGradedBracket G x y := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply, neg_zero]
  | add x₁ x₂ ih₁ ih₂ =>
    simp only [map_add, LinearMap.add_apply, neg_add]
    exact congrArg₂ (· + ·) ih₁ ih₂
  | of m x =>
    induction y using DirectSum.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply, neg_zero]
    | add y₁ y₂ ih₁ ih₂ =>
      simp only [map_add, LinearMap.add_apply, neg_add]
      exact congrArg₂ (· + ·) ih₁ ih₂
    | of n y =>
      change rationalGroupGradedBracket G (rationalGroupGradedInclusion G n y)
        (rationalGroupGradedInclusion G m x) =
          -rationalGroupGradedBracket G (rationalGroupGradedInclusion G m x)
            (rationalGroupGradedInclusion G n y)
      rw [rationalGroupGradedBracket_inclusions, rationalGroupGradedBracket_inclusions]
      have h := congrArg (rationalGroupGradedInclusion G (m + n + 1))
        (rationalLowerCentralPieceBracket_swap G m n x y)
      rw [rationalGroupGradedInclusion_reindex, map_neg] at h
      exact h

theorem rationalGroupGradedBracket_self (x : rationalGroupAssociatedGraded G) :
    rationalGroupGradedBracket G x x = 0 := by
  have h := rationalGroupGradedBracket_swap G x x
  have hsum : rationalGroupGradedBracket G x x + rationalGroupGradedBracket G x x = 0 := by
    calc
      _ = -rationalGroupGradedBracket G x x + rationalGroupGradedBracket G x x :=
        congrArg (fun a => a + rationalGroupGradedBracket G x x) h
      _ = 0 := neg_add_cancel _
  have htwo : (2 : ℚ) • rationalGroupGradedBracket G x x = 0 := by
    simpa only [two_smul] using hsum
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

private def originalGradedJacobiSum (x y z : rationalGroupAssociatedGraded G) :
    rationalGroupAssociatedGraded G :=
  rationalGroupGradedBracket G x (rationalGroupGradedBracket G y z) +
    rationalGroupGradedBracket G y (rationalGroupGradedBracket G z x) +
    rationalGroupGradedBracket G z (rationalGroupGradedBracket G x y)

private theorem originalGradedJacobiSum_zero_left (y z : rationalGroupAssociatedGraded G) :
    originalGradedJacobiSum G 0 y z = 0 := by
  simp only [originalGradedJacobiSum, map_zero, LinearMap.zero_apply, add_zero]

private theorem originalGradedJacobiSum_zero_middle (x z : rationalGroupAssociatedGraded G) :
    originalGradedJacobiSum G x 0 z = 0 := by
  simp only [originalGradedJacobiSum, map_zero, LinearMap.zero_apply, add_zero]

private theorem originalGradedJacobiSum_zero_right (x y : rationalGroupAssociatedGraded G) :
    originalGradedJacobiSum G x y 0 = 0 := by
  simp only [originalGradedJacobiSum, map_zero, LinearMap.zero_apply, add_zero]

private theorem originalGradedJacobiSum_add_left (x₁ x₂ y z : rationalGroupAssociatedGraded G) :
    originalGradedJacobiSum G (x₁ + x₂) y z =
      originalGradedJacobiSum G x₁ y z + originalGradedJacobiSum G x₂ y z := by
  simp only [originalGradedJacobiSum, map_add, LinearMap.add_apply]
  abel

private theorem originalGradedJacobiSum_add_middle (x y₁ y₂ z : rationalGroupAssociatedGraded G) :
    originalGradedJacobiSum G x (y₁ + y₂) z =
      originalGradedJacobiSum G x y₁ z + originalGradedJacobiSum G x y₂ z := by
  simp only [originalGradedJacobiSum, map_add, LinearMap.add_apply]
  abel

private theorem originalGradedJacobiSum_add_right (x y z₁ z₂ : rationalGroupAssociatedGraded G) :
    originalGradedJacobiSum G x y (z₁ + z₂) =
      originalGradedJacobiSum G x y z₁ + originalGradedJacobiSum G x y z₂ := by
  simp only [originalGradedJacobiSum, map_add, LinearMap.add_apply]
  abel

private theorem originalGradedJacobiSum_inclusions (m n p : ℕ)
    (x : rationalLowerCentralPiece G m) (y : rationalLowerCentralPiece G n)
    (z : rationalLowerCentralPiece G p) :
    originalGradedJacobiSum G (rationalGroupGradedInclusion G m x)
      (rationalGroupGradedInclusion G n y) (rationalGroupGradedInclusion G p z) = 0 := by
  have h := congrArg (rationalGroupGradedInclusion G (m + n + p + 2))
    (rationalLowerCentralPieceBracket_jacobi G m n p x y z)
  simp only [map_add, map_zero] at h
  simp only [originalGradedJacobiSum, rationalGroupGradedBracket_inclusions]
  simpa only [rationalLowerCentralPieceJacobiTerm,
    rationalGroupGradedInclusion_reindex] using h

/-- Actual direct-sum induction turns original quotient Jacobi into
Jacobi on all finite sums of original homogeneous elements. -/
theorem rationalGroupGradedBracket_jacobi (x y z : rationalGroupAssociatedGraded G) :
    rationalGroupGradedBracket G x (rationalGroupGradedBracket G y z) +
      rationalGroupGradedBracket G y (rationalGroupGradedBracket G z x) +
      rationalGroupGradedBracket G z (rationalGroupGradedBracket G x y) = 0 := by
  change originalGradedJacobiSum G x y z = 0
  induction x using DirectSum.induction_on with
  | zero => exact originalGradedJacobiSum_zero_left G y z
  | add x₁ x₂ ih₁ ih₂ =>
    rw [originalGradedJacobiSum_add_left, ih₁, ih₂, add_zero]
  | of m x =>
    induction y using DirectSum.induction_on with
    | zero => exact originalGradedJacobiSum_zero_middle G _ z
    | add y₁ y₂ ih₁ ih₂ =>
      rw [originalGradedJacobiSum_add_middle, ih₁, ih₂, add_zero]
    | of n y =>
      induction z using DirectSum.induction_on with
      | zero => exact originalGradedJacobiSum_zero_right G _ _
      | add z₁ z₂ ih₁ ih₂ =>
        rw [originalGradedJacobiSum_add_right, ih₁, ih₂, add_zero]
      | of p z => exact originalGradedJacobiSum_inclusions G m n p x y z

theorem rationalGroupGradedBracket_leibniz (x y z : rationalGroupAssociatedGraded G) :
    rationalGroupGradedBracket G x (rationalGroupGradedBracket G y z) =
      rationalGroupGradedBracket G (rationalGroupGradedBracket G x y) z +
        rationalGroupGradedBracket G y (rationalGroupGradedBracket G x z) := by
  have h := rationalGroupGradedBracket_jacobi G x y z
  rw [rationalGroupGradedBracket_swap G x z, map_neg,
    rationalGroupGradedBracket_swap G (rationalGroupGradedBracket G x y) z] at h
  have h' : rationalGroupGradedBracket G x (rationalGroupGradedBracket G y z) +
      -(rationalGroupGradedBracket G (rationalGroupGradedBracket G x y) z +
        rationalGroupGradedBracket G y (rationalGroupGradedBracket G x z)) = 0 := by
    simpa only [neg_add, add_assoc, add_left_comm, add_comm] using h
  simpa only [neg_neg] using eq_neg_of_add_eq_zero_left h'

instance rationalGroupAssociatedGradedLieRing : LieRing (rationalGroupAssociatedGraded G) where
  toAddCommGroup := inferInstanceAs (AddCommGroup (⨁ n : ℕ, rationalLowerCentralPiece G n))
  bracket x y := rationalGroupGradedBracket G x y
  add_lie x y z := by
    change rationalGroupGradedBracket G (x + y) z = _
    exact LinearMap.congr_fun ((rationalGroupGradedBracket G).map_add x y) z
  lie_add x y z := (rationalGroupGradedBracket G x).map_add y z
  lie_self := rationalGroupGradedBracket_self G
  leibniz_lie := rationalGroupGradedBracket_leibniz G

instance rationalGroupAssociatedGradedLieAlgebra :
    LieAlgebra ℚ (rationalGroupAssociatedGraded G) where
  toModule := inferInstanceAs (_root_.Module ℚ (⨁ n : ℕ, rationalLowerCentralPiece G n))
  lie_smul c x y := (rationalGroupGradedBracket G x).map_smul c y

/-- The actual native Lie bracket computes the original quotient
commutator on each original homogeneous summand. -/
@[simp] theorem rationalGroupAssociatedGraded_lie_inclusions (m n : ℕ)
    (x : rationalLowerCentralPiece G m) (y : rationalLowerCentralPiece G n) :
    ⁅rationalGroupGradedInclusion G m x, rationalGroupGradedInclusion G n y⁆ =
      rationalGroupGradedInclusion G (m + n + 1)
        (rationalLowerCentralPieceBracket G m n x y) :=
  rationalGroupGradedBracket_inclusions G m n x y

/-- Genuine specialization to the maximal metabelian group quotient;
its summands are exactly the original rational Chen spaces. -/
abbrev rationalChenAssociatedGraded :=
  rationalGroupAssociatedGraded (metabelianQuotient G)

end ChenRanks
