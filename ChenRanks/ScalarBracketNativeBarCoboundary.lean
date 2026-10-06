import ChenRanks.ScalarLowerCentralPieceBracket
import ChenRanks.GroupDegreeTwoAlternatingCoboundary

/-! Every genuine scalar functional of the actual first/first bracket
has a proved primitive in the original native group bar complex. Its
cochain is identified pointwise with the original commutator character.
No primitive, vanishing class, cup-kernel condition or formality is input.
-/

noncomputable section
open TensorProduct
open scoped TensorProduct
namespace ChenRanks.GroupComparison

variable (k G : Type) [Field k] [CharZero k] [Group G]

/-- The actual scalar-extended first quotient class of the original g. -/
def originalScalarFirstClass (g : G) : scalarLowerCentralPiece k G 0 :=
  (1 : k) ⊗ₜ[ℤ] Additive.ofMul (originalFirstLowerCentralClass G g)

/-- The actual degree-two scalar functional restricted to the genuine
original integral quotient. -/
def scalarSecondFunctionalCharacter
    (ell : Module.Dual k (scalarLowerCentralPiece k G 1)) :
    Additive (lowerCentralPiece G 1) →+ k :=
  (ell.restrictScalars ℤ).toAddMonoidHom.comp
    ((TensorProduct.mk ℤ k (Additive (lowerCentralPiece G 1))) 1).toAddMonoidHom

@[simp] theorem scalarSecondFunctionalCharacter_apply
    (ell : Module.Dual k (scalarLowerCentralPiece k G 1))
    (a : Additive (lowerCentralPiece G 1)) :
    scalarSecondFunctionalCharacter k G ell a = ell ((1 : k) ⊗ₜ[ℤ] a) := rfl

/-- The actual native antisymmetric bar cochain agrees with evaluation
of the actual scalar-extended original commutator bracket. -/
theorem scalarFirstBracket_evaluation_eq_original_bar
    (ell : Module.Dual k (scalarLowerCentralPiece k G 1)) (g h : G) :
    ell (scalarLowerCentralPieceBracket k G 0 0
      (originalScalarFirstClass k G g) (originalScalarFirstClass k G h)) =
    degreeTwoCharacterAlternatingCochain G k (scalarSecondFunctionalCharacter k G ell) g h := by
  rw [degreeTwoCharacterAlternatingCochain_eq_actual_bracket]
  change ell (scalarLowerCentralPieceBracket k G 0 0
    ((1 : k) ⊗ₜ[ℤ] Additive.ofMul (originalFirstLowerCentralClass G g))
    ((1 : k) ⊗ₜ[ℤ] Additive.ofMul (originalFirstLowerCentralClass G h))) = _
  rw [scalarLowerCentralPieceBracket_tmul_tmul, one_mul,
    scalarSecondFunctionalCharacter_apply]
  rfl

/-- An actual bar primitive follows, before any cup-kernel comparison. -/
theorem scalarFirstBracket_evaluation_has_bar_primitive
    (ell : Module.Dual k (scalarLowerCentralPiece k G 1)) :
    ∃ F : G → k, ∀ g h, F h - F (g * h) + F g =
      ell (scalarLowerCentralPieceBracket k G 0 0
        (originalScalarFirstClass k G g) (originalScalarFirstClass k G h)) := by
  obtain ⟨F, hF⟩ := degreeTwoCharacterAlternating_has_primitive G k
    (scalarSecondFunctionalCharacter k G ell)
  refine ⟨F, ?_⟩
  intro g h
  rw [scalarFirstBracket_evaluation_eq_original_bar]
  exact hF g h

/-- The actual native cocycle, with its genuine original coefficient rep. -/
def scalarFirstBracketNativeCocycle
    (ell : Module.Dual k (scalarLowerCentralPiece k G 1)) :
    groupCohomology.cocycles₂ (groupTrivialCoefficients k G) :=
  degreeTwoCharacterAlternatingCocycle G k (scalarSecondFunctionalCharacter k G ell)

@[simp] theorem scalarFirstBracketNativeCocycle_apply
    (ell : Module.Dual k (scalarLowerCentralPiece k G 1)) (g h : G) :
    scalarFirstBracketNativeCocycle k G ell (g, h) =
      ell (scalarLowerCentralPieceBracket k G 0 0
        (originalScalarFirstClass k G g) (originalScalarFirstClass k G h)) :=
  (scalarFirstBracket_evaluation_eq_original_bar k G ell g h).symm

theorem scalarFirstBracketNativeCocycle_class_zero
    (ell : Module.Dual k (scalarLowerCentralPiece k G 1)) :
    groupCohomology.H2π (groupTrivialCoefficients k G)
      (scalarFirstBracketNativeCocycle k G ell) = 0 :=
  degreeTwoCharacterAlternating_nativeH2_zero G k (scalarSecondFunctionalCharacter k G ell)

end ChenRanks.GroupComparison
