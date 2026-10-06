import ChenRanks.GroupLowerCentralPieceAlternation
import Mathlib.Algebra.Algebra.Rat

/-! Genuine scalar extension of the original lower-central brackets.
The original native quotient is retained. Field scalars multiply through
the actual tensor universal property. The first-degree alternation is
derived from original integer commutators, not assigned as a Lie input.
-/

noncomputable section
open TensorProduct
open scoped TensorProduct
namespace ChenRanks
variable (k : Type*) [Field k] (G : Type*) [Group G]

abbrev scalarLowerCentralPiece (n : ℕ) := k ⊗[ℤ] Additive (lowerCentralPiece G n)

/-- Genuine rational bilinear scalar extension of the original bracket. -/
def scalarLowerCentralPieceBracket (m n : ℕ) :
    scalarLowerCentralPiece k G m →ₗ[k]
      (scalarLowerCentralPiece k G n →ₗ[k] scalarLowerCentralPiece k G (m + n + 1)) :=
  AlgebraTensorModule.lift (R := ℤ) (A := k) (M := k)
    (N := Additive (lowerCentralPiece G m))
    (P := scalarLowerCentralPiece k G n →ₗ[k] scalarLowerCentralPiece k G (m + n + 1))
    (LinearMap.toSpanSingleton k
      (Additive (lowerCentralPiece G m) →ₗ[ℤ]
        (scalarLowerCentralPiece k G n →ₗ[k] scalarLowerCentralPiece k G (m + n + 1)))
      ((AlgebraTensorModule.lTensor k k).comp (lowerCentralPieceBracketInt G m n)))

@[simp]
theorem scalarLowerCentralPieceBracket_tmul_tmul (m n : ℕ) (c d : k)
    (g : Additive (lowerCentralPiece G m)) (h : Additive (lowerCentralPiece G n)) :
    scalarLowerCentralPieceBracket k G m n (c ⊗ₜ[ℤ] g) (d ⊗ₜ[ℤ] h) =
      (c * d) ⊗ₜ[ℤ] (lowerCentralPieceBracketAdd G m n g h) := by
  simp only [scalarLowerCentralPieceBracket, AlgebraTensorModule.lift_tmul,
    LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    AlgebraTensorModule.lTensor_tmul, lowerCentralPieceBracketInt,
    AddMonoidHom.coe_toIntLinearMap, TensorProduct.smul_tmul', smul_eq_mul]
  rfl

/-- Antisymmetry on the original first scalar-extended quotients. -/
theorem scalarLowerCentralFirstBracket_swap
    (x y : scalarLowerCentralPiece k G 0) :
    scalarLowerCentralPieceBracket k G 0 0 y x =
      -scalarLowerCentralPieceBracket k G 0 0 x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply, neg_zero]
  | add x₁ x₂ hx₁ hx₂ =>
      simp only [map_add, LinearMap.add_apply, hx₁, hx₂, neg_add]
  | tmul c g =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply, neg_zero]
    | add y₁ y₂ hy₁ hy₂ =>
      simp only [map_add, LinearMap.add_apply, hy₁, hy₂, neg_add]
    | tmul d h =>
      rw [scalarLowerCentralPieceBracket_tmul_tmul,
        scalarLowerCentralPieceBracket_tmul_tmul]
      have hs := lowerCentralPieceBracketAdd_swap G 0 0 g h
      change lowerCentralPieceBracketAdd G 0 0 h g =
        -lowerCentralPieceBracketAdd G 0 0 g h at hs
      rw [hs, TensorProduct.tmul_neg, mul_comm]

/-- The actual nonzero scalar two proves genuine first alternation. -/
theorem scalarLowerCentralFirstBracket_self [CharZero k]
    (x : scalarLowerCentralPiece k G 0) :
    scalarLowerCentralPieceBracket k G 0 0 x x = 0 := by
  have hs := scalarLowerCentralFirstBracket_swap k G x x
  have hadd : scalarLowerCentralPieceBracket k G 0 0 x x +
      scalarLowerCentralPieceBracket k G 0 0 x x = 0 := by
    calc
      _ = -scalarLowerCentralPieceBracket k G 0 0 x x +
          scalarLowerCentralPieceBracket k G 0 0 x x :=
        congrArg (fun z => z + scalarLowerCentralPieceBracket k G 0 0 x x) hs
      _ = 0 := neg_add_cancel _
  have htwo : (2 : k) • scalarLowerCentralPieceBracket k G 0 0 x x = 0 := by
    simpa only [two_smul] using hadd
  exact (smul_eq_zero.mp htwo).resolve_left two_ne_zero

end ChenRanks
