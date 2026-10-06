import ChenRanks.GroupLowerCentralBracketGeneration

/-!
# Actual tensor generation and finite lower-central pieces

The next original rationalized quotient is an actual quotient of the
tensor product of its preceding quotient with the first quotient. Thus
finite dimension in degree one implies finite dimension in every degree.
Only the original first quotient is assumed finite; the finiteness of
higher pieces is a conclusion, not an input to the associated Lie algebra.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks

variable (G : Type*) [Group G]

/-- The genuine tensor extension of the original quotient commutator. -/
def nextLowerCentralBracketTensorMap (n : ℕ) :
    (rationalLowerCentralPiece G n ⊗[ℚ] rationalLowerCentralPiece G 0) →ₗ[ℚ]
      rationalLowerCentralPiece G (n + 1) :=
  TensorProduct.lift (rationalLowerCentralPieceBracket G n 0)

@[simp] theorem nextLowerCentralBracketTensorMap_tmul (n : ℕ)
    (x : rationalLowerCentralPiece G n) (y : rationalLowerCentralPiece G 0) :
    nextLowerCentralBracketTensorMap G n (x ⊗ₜ[ℚ] y) =
      rationalLowerCentralPieceBracket G n 0 x y :=
  rfl

/-- The actual span theorem makes this actual tensor map surjective. -/
theorem nextLowerCentralBracketTensorMap_range (n : ℕ) :
    LinearMap.range (nextLowerCentralBracketTensorMap G n) = ⊤ := by
  have hle : nextLowerCentralBracketSpan G n ≤
      LinearMap.range (nextLowerCentralBracketTensorMap G n) := by
    apply Submodule.span_le.mpr
    rintro w ⟨⟨x, y⟩, rfl⟩
    exact ⟨x ⊗ₜ[ℚ] y, nextLowerCentralBracketTensorMap_tmul G n x y⟩
  apply top_unique
  rw [← nextLowerCentralBracketSpan_eq_top G n]
  exact hle

theorem nextLowerCentralBracketTensorMap_surjective (n : ℕ) :
    Function.Surjective (nextLowerCentralBracketTensorMap G n) :=
  LinearMap.range_eq_top.mp (nextLowerCentralBracketTensorMap_range G n)

/-- Finite dimension of each original successive quotient is derived
from the actual first quotient, actual tensor generation, and induction. -/
theorem rationalLowerCentralPiece_finiteDimensional
    [FiniteDimensional ℚ (rationalLowerCentralPiece G 0)] (n : ℕ) :
    FiniteDimensional ℚ (rationalLowerCentralPiece G n) := by
  induction n with
  | zero => infer_instance
  | succ n ih =>
    letI : FiniteDimensional ℚ (rationalLowerCentralPiece G n) := ih
    exact Module.Finite.of_surjective (nextLowerCentralBracketTensorMap G n)
      (nextLowerCentralBracketTensorMap_surjective G n)

/-- The same statement applies to the original maximal metabelian
quotient; no higher Chen-rank finiteness is postulated. -/
theorem rationalChenSpace_finiteDimensional
    [FiniteDimensional ℚ (rationalChenSpace G 0)] (n : ℕ) :
    FiniteDimensional ℚ (rationalChenSpace G n) :=
  rationalLowerCentralPiece_finiteDimensional (metabelianQuotient G) n

end ChenRanks
