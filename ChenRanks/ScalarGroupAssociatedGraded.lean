import ChenRanks.GroupAssociatedGradedLie
import ChenRanks.ScalarLowerCentralPieceBracket
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Actual scalar extension of the original group associated Lie algebra

The Lie algebra is the native scalar extension of the already constructed
rational associated Lie algebra of the original group. Cancellation of
actual tensor scalar extensions identifies each original homogeneous
piece with k tensor the original integral lower-central quotient. Tensor
products distribute over the actual direct sum. The actual bracket is
shown to agree with the original scalar-extended commutator in every
pair of degrees, not just in the first degree.

This does not assume a comparison of rational and complex cup kernels,
and it does not assert holonomy comparison or formality.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct DirectSum

namespace ChenRanks

variable (k : Type*) [Field k] [CharZero k]
variable (G : Type*) [Group G]

/-- The genuine native Lie scalar extension of the original group
associated Lie algebra. -/
abbrev scalarGroupAssociatedGraded := k ⊗[ℚ] rationalGroupAssociatedGraded G

/-- Actual tensor cancellation retains the same original integral
successive group quotient. -/
def scalarGroupPieceBaseChangeEquiv (n : ℕ) :
    (k ⊗[ℚ] rationalLowerCentralPiece G n) ≃ₗ[k] scalarLowerCentralPiece k G n :=
  AlgebraTensorModule.cancelBaseChange ℤ ℚ k k (Additive (lowerCentralPiece G n))

@[simp] theorem scalarGroupPieceBaseChangeEquiv_tmul (n : ℕ) (c : k) (d : ℚ)
    (a : Additive (lowerCentralPiece G n)) :
    scalarGroupPieceBaseChangeEquiv k G n (c ⊗ₜ[ℚ] (d ⊗ₜ[ℤ] a)) =
      (d • c) ⊗ₜ[ℤ] a := rfl

@[simp] theorem scalarGroupPieceBaseChangeEquiv_symm_tmul (n : ℕ) (c : k)
    (a : Additive (lowerCentralPiece G n)) :
    (scalarGroupPieceBaseChangeEquiv k G n).symm (c ⊗ₜ[ℤ] a) =
      c ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] a) := rfl

/-- The same actual homogeneous piece is included through the original
rational degree inclusion after genuine tensor cancellation. -/
def scalarGroupGradedInclusion (n : ℕ) :
    scalarLowerCentralPiece k G n →ₗ[k] scalarGroupAssociatedGraded k G :=
  (AlgebraTensorModule.lTensor k k (rationalGroupGradedInclusion G n)).comp
    (scalarGroupPieceBaseChangeEquiv k G n).symm.toLinearMap

@[simp] theorem scalarGroupGradedInclusion_tmul (n : ℕ) (c : k)
    (a : Additive (lowerCentralPiece G n)) :
    scalarGroupGradedInclusion k G n (c ⊗ₜ[ℤ] a) =
      c ⊗ₜ[ℚ] rationalGroupGradedInclusion G n ((1 : ℚ) ⊗ₜ[ℤ] a) := by
  rw [scalarGroupGradedInclusion, LinearMap.comp_apply]
  change AlgebraTensorModule.lTensor k k (rationalGroupGradedInclusion G n)
    ((scalarGroupPieceBaseChangeEquiv k G n).symm (c ⊗ₜ[ℤ] a)) = _
  rw [scalarGroupPieceBaseChangeEquiv_symm_tmul, AlgebraTensorModule.lTensor_tmul]

/-- This is a genuine linear equivalence with the direct sum of the
original scalarized successive group quotients. -/
def scalarGroupGradedDirectSumEquiv :
    scalarGroupAssociatedGraded k G ≃ₗ[k] ⨁ n : ℕ, scalarLowerCentralPiece k G n :=
  (TensorProduct.directSumRight ℚ k k (rationalLowerCentralPiece G)).trans
    (DirectSum.congrLinearEquiv (fun n => scalarGroupPieceBaseChangeEquiv k G n))

/-- The scalar extension keeps each original degree exactly, with the
actual original quotient retained in that degree. -/
theorem scalarGroupGradedDirectSumEquiv_inclusion (n : ℕ)
    (x : scalarLowerCentralPiece k G n) :
    scalarGroupGradedDirectSumEquiv k G (scalarGroupGradedInclusion k G n x) =
      DirectSum.lof k ℕ (scalarLowerCentralPiece k G) n x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c a =>
    rw [scalarGroupGradedInclusion_tmul]
    change DirectSum.congrLinearEquiv (fun n => scalarGroupPieceBaseChangeEquiv k G n)
      (TensorProduct.directSumRight ℚ k k (rationalLowerCentralPiece G)
        (c ⊗ₜ[ℚ] DirectSum.lof ℚ ℕ (rationalLowerCentralPiece G) n
          ((1 : ℚ) ⊗ₜ[ℤ] a))) = _
    rw [TensorProduct.directSumRight_tmul_lof,
      DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
    change DirectSum.lof k ℕ (scalarLowerCentralPiece k G) n
      (scalarGroupPieceBaseChangeEquiv k G n (c ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] a))) = _
    rw [scalarGroupPieceBaseChangeEquiv_tmul, one_smul]

/-- Injectivity follows from the actual direct-sum equivalence, without
an assumed injective scalar extension or homogeneous projection. -/
theorem scalarGroupGradedInclusion_injective (n : ℕ) :
    Function.Injective (scalarGroupGradedInclusion k G n) := by
  intro x y hxy
  have h := congrArg (scalarGroupGradedDirectSumEquiv k G) hxy
  rw [scalarGroupGradedDirectSumEquiv_inclusion,
    scalarGroupGradedDirectSumEquiv_inclusion] at h
  have hcomp := congrArg (DirectSum.component k ℕ (scalarLowerCentralPiece k G) n) h
  simpa only [DirectSum.component.lof_self] using hcomp

/-- On actual original integral representatives, the native Lie scalar
extension is the actual scalar-extended original commutator. -/
theorem scalarGroupAssociatedGraded_lie_tmul (m n : ℕ) (c d : k)
    (a : Additive (lowerCentralPiece G m)) (b : Additive (lowerCentralPiece G n)) :
    ⁅scalarGroupGradedInclusion k G m (c ⊗ₜ[ℤ] a),
      scalarGroupGradedInclusion k G n (d ⊗ₜ[ℤ] b)⁆ =
      scalarGroupGradedInclusion k G (m + n + 1)
        ((c * d) ⊗ₜ[ℤ] lowerCentralPieceBracketAdd G m n a b) := by
  rw [scalarGroupGradedInclusion_tmul, scalarGroupGradedInclusion_tmul,
    LieAlgebra.ExtendScalars.bracket_tmul,
    rationalGroupAssociatedGraded_lie_inclusions,
    rationalLowerCentralPieceBracket_tmul_tmul, one_mul,
    scalarGroupGradedInclusion_tmul]

/-- Actual bracket compatibility holds in every pair of native original
degrees. In particular it connects the true first scalar bracket used in
the native group cup-kernel construction, without assuming base-change
compatibility of relation kernels. -/
theorem scalarGroupAssociatedGraded_lie_inclusions (m n : ℕ)
    (x : scalarLowerCentralPiece k G m) (y : scalarLowerCentralPiece k G n) :
    ⁅scalarGroupGradedInclusion k G m x, scalarGroupGradedInclusion k G n y⁆ =
      scalarGroupGradedInclusion k G (m + n + 1)
        (scalarLowerCentralPieceBracket k G m n x y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, zero_lie, LinearMap.zero_apply]
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [map_add, add_lie, LinearMap.add_apply, hx₁, hx₂]
  | tmul c a =>
    induction y using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero, LinearMap.zero_apply]
      exact (AddMonoidHom.mk'
        (fun y : scalarGroupAssociatedGraded k G =>
          ⁅scalarGroupGradedInclusion k G m (c ⊗ₜ[ℤ] a), y⁆)
        (LieRing.lie_add _)).map_zero
    | add y₁ y₂ hy₁ hy₂ =>
      simp only [map_add, LieRing.lie_add, LinearMap.add_apply, hy₁, hy₂]
    | tmul d b =>
      rw [scalarLowerCentralPieceBracket_tmul_tmul]
      exact scalarGroupAssociatedGraded_lie_tmul k G m n c d a b

/-- Dimension is compared on the actual original quotient by genuine
scalar cancellation; the equality does not define either dimension. -/
theorem scalarLowerCentralPiece_finrank (n : ℕ) :
    _root_.Module.finrank k (scalarLowerCentralPiece k G n) =
      _root_.Module.finrank ℚ (rationalLowerCentralPiece G n) := by
  calc
    _ = _root_.Module.finrank k (k ⊗[ℚ] rationalLowerCentralPiece G n) :=
      (scalarGroupPieceBaseChangeEquiv k G n).finrank_eq.symm
    _ = _ := _root_.Module.finrank_baseChange

/-- Higher finite dimensionality, when available for the actual rational
piece, transfers to the same actual scalarized group quotient. -/
instance scalarLowerCentralPiece_finiteDimensional (n : ℕ)
    [FiniteDimensional ℚ (rationalLowerCentralPiece G n)] :
    FiniteDimensional k (scalarLowerCentralPiece k G n) :=
  _root_.Module.Finite.of_surjective (scalarGroupPieceBaseChangeEquiv k G n).toLinearMap
    (scalarGroupPieceBaseChangeEquiv k G n).surjective

/-- The same construction retains the actual original maximal metabelian
quotient in every scalarized Chen piece. -/
abbrev scalarChenAssociatedGraded := scalarGroupAssociatedGraded k (metabelianQuotient G)

end ChenRanks
