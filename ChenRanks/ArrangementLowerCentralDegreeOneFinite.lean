import ChenRanks.ArrangementGroupAugmentationCotangent
import ChenRanks.GroupAugmentationAbelianization
import ChenRanks.GroupLowerCentralDegreeOne
import ChenRanks.GroupLowerCentralPieceBracket

/-! The original arrangement group and its original metabelian quotient
have genuine finite-dimensional first rational lower-central pieces.
The equivalences use the native first quotient, native abelianization,
native tensor scalar extension and the original group-algebra cotangent.
Finiteness and dimension are conclusions from original equations; no
finite-generation or higher Chen/holonomy assertion is used.
-/

noncomputable section
open TensorProduct
open scoped TensorProduct
namespace ChenRanks

variable (G : Type*) [Group G]
variable (k : Type*) [Field k]

def lowerCentralDegreeOneScalarAbelianizationEquiv :
    (k ⊗[ℤ] Additive (lowerCentralPiece G 0)) ≃ₗ[k]
      GroupAlgebra.scalarAbelianization k G :=
  AlgebraTensorModule.congr (LinearEquiv.refl k k)
    (lowerCentralDegreeOneAbelianizationEquiv G).toAdditive.toIntLinearEquiv

namespace AffineArrangement
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

def actualRationalLowerCentralDegreeOneCotangent (base : A.Complement) :
    rationalLowerCentralPiece (FundamentalGroup A.Complement base) 0 ≃ₗ[ℚ]
      GroupAlgebra.augmentationCotangent ℚ (FundamentalGroup A.Complement base) :=
  (lowerCentralDegreeOneScalarAbelianizationEquiv
    (FundamentalGroup A.Complement base) ℚ).trans
    (GroupAlgebra.augmentationCotangentScalarAbelianizationEquiv ℚ
      (FundamentalGroup A.Complement base)).symm

instance actualRationalLowerCentralDegreeOne_finiteDimensional (base : A.Complement) :
    FiniteDimensional ℚ (rationalLowerCentralPiece (FundamentalGroup A.Complement base) 0) :=
  FiniteDimensional.of_injective
    (A.actualRationalLowerCentralDegreeOneCotangent base).toLinearMap
    (A.actualRationalLowerCentralDegreeOneCotangent base).injective

theorem actualRationalLowerCentralDegreeOne_finrank (base : A.Complement) :
    Module.finrank ℚ (rationalLowerCentralPiece (FundamentalGroup A.Complement base) 0) =
      Fintype.card ι :=
  (A.actualRationalLowerCentralDegreeOneCotangent base).finrank_eq.trans
    (A.actualGroupCotangent_finrank ℚ base)

def actualRationalChenDegreeOneCotangent (base : A.Complement) :
    rationalChenSpace (FundamentalGroup A.Complement base) 0 ≃ₗ[ℚ]
      GroupAlgebra.augmentationCotangent ℚ (FundamentalGroup A.Complement base) :=
  (rationalChenDegreeOneAbelianizationEquiv (FundamentalGroup A.Complement base)).trans
    (GroupAlgebra.augmentationCotangentScalarAbelianizationEquiv ℚ
      (FundamentalGroup A.Complement base)).symm

instance actualRationalChenDegreeOne_finiteDimensional (base : A.Complement) :
    FiniteDimensional ℚ (rationalChenSpace (FundamentalGroup A.Complement base) 0) :=
  FiniteDimensional.of_injective (A.actualRationalChenDegreeOneCotangent base).toLinearMap
    (A.actualRationalChenDegreeOneCotangent base).injective

theorem actualRationalChenDegreeOne_finrank (base : A.Complement) :
    Module.finrank ℚ (rationalChenSpace (FundamentalGroup A.Complement base) 0) = Fintype.card ι :=
  (A.actualRationalChenDegreeOneCotangent base).finrank_eq.trans
    (A.actualGroupCotangent_finrank ℚ base)

end AffineArrangement
end ChenRanks
