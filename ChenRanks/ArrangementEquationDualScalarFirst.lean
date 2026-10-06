import ChenRanks.ArrangementGroupEquationDualAbelianization
import ChenRanks.ScalarFirstLowerCentralCharacters

/-! The paper's original equation dual and the original group's first
scalar lower-central quotient are identified by their actual native
cotangent and bidual maps. The same dual evaluation and the same original
singular characters are preserved. No holonomy comparison is presumed.
-/
noncomputable section
namespace ChenRanks.AffineArrangement
open SingularCohomology
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (k : Type) [Field k]
local instance : PathConnectedSpace A.Complement :=
  A.complement_pathConnectedSpace_from_actual_equations

/-- The original coefficient-dual vectors, in the original first quotient. -/
def actualEquationDualScalarFirst (base : A.Complement) :
    Module.Dual k (ι → k) ≃ₗ[k]
      scalarLowerCentralPiece k (FundamentalGroup A.Complement base) 0 :=
  (A.actualEquationDualGroupCotangent k base).trans
    (scalarFirstLowerCentralCotangentEquiv k (FundamentalGroup A.Complement base)).symm

/-- The true equation classes as original native group characters. -/
def actualEquationCoefficientCharacters (base : A.Complement) :
    (ι → k) ≃ₗ[k] (Additive (FundamentalGroup A.Complement base) →+ k) :=
  (A.fieldEquationClassEquiv k).trans
    (firstCohomologyCharactersEquiv A.Complement k base)

def actualScalarFirstDualEquationCoefficients (base : A.Complement) :
    Module.Dual k (scalarLowerCentralPiece k (FundamentalGroup A.Complement base) 0) ≃ₗ[k]
      (ι → k) :=
  (scalarFirstLowerCentralCotangentEquiv k (FundamentalGroup A.Complement base)).symm.dualMap.trans
    (A.actualGroupCotangentDualEquationCoefficients k base)

/-- Evaluation uses the same original dual map, not an assigned pairing. -/
theorem actualEquationDualScalarFirst_evaluation (base : A.Complement)
    (v : Module.Dual k (ι → k))
    (f : Module.Dual k (scalarLowerCentralPiece k (FundamentalGroup A.Complement base) 0)) :
    f (A.actualEquationDualScalarFirst k base v) =
      v (A.actualScalarFirstDualEquationCoefficients k base f) := by
  exact A.actualEquationDualGroupCotangent_evaluation k base v
    ((scalarFirstLowerCentralCotangentEquiv k (FundamentalGroup A.Complement base)).symm.dualMap f)

/-- The actual original character is unchanged under the equation/first
quotient correspondence, including its original group evaluation. -/
theorem actualScalarFirstDualEquationCoefficients_character (base : A.Complement)
    (f : Module.Dual k (scalarLowerCentralPiece k (FundamentalGroup A.Complement base) 0)) :
    A.actualEquationCoefficientCharacters k base
      (A.actualScalarFirstDualEquationCoefficients k base f) =
      scalarFirstLowerCentralDualCharacters k (FundamentalGroup A.Complement base) f := by
  let e := A.actualEquationCoefficientCharacters k base
  let cot := scalarFirstLowerCentralCotangentEquiv k (FundamentalGroup A.Complement base)
  change e (e.symm (GroupAlgebra.augmentationCotangentDualCharacters k
    (FundamentalGroup A.Complement base) (cot.symm.dualMap f))) = _
  exact e.apply_symm_apply _

end ChenRanks.AffineArrangement
