import ChenRanks.ScalarBracketNativeBarCoboundary
import ChenRanks.ArrangementLowerCentralDegreeOneFinite

/-! The actual dual of the original scalar-extended first quotient is
the actual additive-character space. This equivalence preserves original
group evaluations; it is not assigned to force a desired pairing. On an
original arrangement, finiteness is derived over the actual coefficient
field from its proved native cotangent theorem.
-/

noncomputable section
open TensorProduct
open scoped TensorProduct
namespace ChenRanks

variable (k G : Type) [Field k] [Group G]

def scalarFirstLowerCentralCotangentEquiv :
    scalarLowerCentralPiece k G 0 ≃ₗ[k] GroupAlgebra.augmentationCotangent k G :=
  (lowerCentralDegreeOneScalarAbelianizationEquiv G k).trans
    (GroupAlgebra.augmentationCotangentScalarAbelianizationEquiv k G).symm

@[simp] theorem scalarFirstLowerCentralCotangentEquiv_groupClass (g : G) :
    scalarFirstLowerCentralCotangentEquiv k G
      (GroupComparison.originalScalarFirstClass k G g) =
      GroupAlgebra.augmentationCotangentClass k G g := by
  change GroupAlgebra.scalarAbelianizationToCotangent k G
    ((1 : k) ⊗ₜ[ℤ] Additive.ofMul (Abelianization.of g)) = _
  rw [GroupAlgebra.scalarAbelianizationToCotangent_tmul,
    GroupAlgebra.abelianizationCotangentCharacter_of, one_smul]

/-- Genuine duality with the actual original characters. -/
def scalarFirstLowerCentralDualCharacters :
    Module.Dual k (scalarLowerCentralPiece k G 0) ≃ₗ[k] (Additive G →+ k) :=
  (scalarFirstLowerCentralCotangentEquiv k G).symm.dualMap.trans
    (GroupAlgebra.augmentationCotangentDualCharacters k G)

@[simp] theorem scalarFirstLowerCentralDualCharacters_groupClass
    (f : Module.Dual k (scalarLowerCentralPiece k G 0)) (g : G) :
    scalarFirstLowerCentralDualCharacters k G f (Additive.ofMul g) =
      f (GroupComparison.originalScalarFirstClass k G g) := by
  change f ((scalarFirstLowerCentralCotangentEquiv k G).symm
    (GroupAlgebra.augmentationCotangentClass k G g)) = _
  rw [← scalarFirstLowerCentralCotangentEquiv_groupClass k G g,
    LinearEquiv.symm_apply_apply]

namespace AffineArrangement
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

instance actualScalarFirstLowerCentralPiece_finiteDimensional (base : A.Complement) :
    FiniteDimensional k (scalarLowerCentralPiece k (FundamentalGroup A.Complement base) 0) :=
  FiniteDimensional.of_injective
    (scalarFirstLowerCentralCotangentEquiv k (FundamentalGroup A.Complement base)).toLinearMap
    (scalarFirstLowerCentralCotangentEquiv k (FundamentalGroup A.Complement base)).injective

theorem actualScalarFirstLowerCentralPiece_finrank (base : A.Complement) :
    Module.finrank k (scalarLowerCentralPiece k (FundamentalGroup A.Complement base) 0) =
      Fintype.card ι :=
  (scalarFirstLowerCentralCotangentEquiv k (FundamentalGroup A.Complement base)).finrank_eq.trans
    (A.actualGroupCotangent_finrank k base)

end AffineArrangement
end ChenRanks
