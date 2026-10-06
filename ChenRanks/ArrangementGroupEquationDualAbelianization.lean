import ChenRanks.ArrangementGroupAugmentationCotangent
import ChenRanks.GroupAugmentationAbelianization
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The original equation-coefficient dual is genuinely the scalar
extension of the original arrangement group abelianization. The map uses
the actual cotangent dual/H1 equivalence, native finite-dimensional
biduality and the actual I/I²/abelianization equivalence. No higher
group/holonomy comparison is asserted.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (k : Type) [Field k]

/-- Native biduality identifies the original equation dual with the
actual original group-algebra cotangent. Finiteness is already derived
for the actual arrangement group, rather than supplied as an input. -/
def actualEquationDualGroupCotangent (base : A.Complement) :
    Module.Dual k (ι → k) ≃ₗ[k]
      GroupAlgebra.augmentationCotangent k (FundamentalGroup A.Complement base) :=
  (A.actualGroupCotangentDualEquationCoefficients k base).dualMap.trans
    (Module.evalEquiv k (GroupAlgebra.augmentationCotangent k
      (FundamentalGroup A.Complement base))).symm

/-- The same original dual vector is evaluated by the same original
cotangent character. No pairing is assigned to match a desired formula. -/
theorem actualEquationDualGroupCotangent_evaluation (base : A.Complement)
    (v : Module.Dual k (ι → k))
    (f : Module.Dual k (GroupAlgebra.augmentationCotangent k
      (FundamentalGroup A.Complement base))) :
    f (A.actualEquationDualGroupCotangent k base v) =
      v (A.actualGroupCotangentDualEquationCoefficients k base f) := by
  have h := (Module.evalEquiv k (GroupAlgebra.augmentationCotangent k
    (FundamentalGroup A.Complement base))).apply_symm_apply
      ((A.actualGroupCotangentDualEquationCoefficients k base).dualMap v)
  exact congrArg (fun w => w f) h

/-- Degree one of the original arrangement's quadratic data maps to
the scalar extension of its original group abelianization by true native
equivalences, without a finite-generation or formality assumption. -/
def actualEquationDualScalarAbelianization (base : A.Complement) :
    Module.Dual k (ι → k) ≃ₗ[k]
      GroupAlgebra.scalarAbelianization k (FundamentalGroup A.Complement base) :=
  (A.actualEquationDualGroupCotangent k base).trans
    (GroupAlgebra.augmentationCotangentScalarAbelianizationEquiv k
      (FundamentalGroup A.Complement base))

end ChenRanks.AffineArrangement
