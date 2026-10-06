import ChenRanks.ArrangementEquationDualScalarFirst
import ChenRanks.CharactersClosedPathEvaluation

/-! The original actual meridians identify characters in the original
equation coordinates. This is an intermediate implication; an actual
monodromy application must prove the meridian values from actual lifts
and logarithmic periods. It does not assume formality or identify any
higher lower-central piece.
-/
noncomputable section
namespace ChenRanks.AffineArrangement
open SingularCohomology unitInterval
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (k : Type) [Field k]
local instance : PathConnectedSpace A.Complement :=
  A.complement_pathConnectedSpace_from_actual_equations

/-- The original canonical geometric meridian with its actual endpoint equality. -/
def actualCharacterMeridianLoop (H : ι) :
    Path (A.meridianDiskPathMap H (A.actualMeridianDisk H) 0)
      (A.meridianDiskPathMap H (A.actualMeridianDisk H) 0) :=
  closedContinuousPathLoop A.Complement
    (A.meridianDiskPathMap H (A.actualMeridianDisk H))
    (A.meridianDiskPathMap_endpoints H (A.actualMeridianDisk H))

/-- The proved actual first-cohomology basis turns actual meridian values
into equality with the original actual equation character. -/
theorem actualEquationCharacter_eq_of_actual_meridian_values
    (base : A.Complement) (a : ι → k)
    (χ : Additive (FundamentalGroup A.Complement base) →+ k)
    (hχ : ∀ H : ι, ChenRanks.basedPathCharacterValue A.Complement k base χ
      (A.actualCharacterMeridianLoop H) = a H) :
    A.actualEquationCoefficientCharacters k base a = χ := by
  change firstCohomologyToCharacters A.Complement k base
    (A.fieldEquationClassMap k a) = χ
  rw [← firstCohomologyToCharacters_characterClass A.Complement k base χ]
  apply congrArg (firstCohomologyToCharacters A.Complement k base)
  have hinj : Function.Injective (A.fieldMeridianEvaluationMap k) :=
    (show Function.LeftInverse (A.fieldEquationClassMap k)
      (A.fieldMeridianEvaluationMap k) from
        A.fieldEquationClassMap_meridianEvaluationMap k).injective
  apply hinj
  rw [A.fieldMeridianEvaluationMap_equationClassMap]
  funext H
  change a H = closedPathEvaluation k A.Complement
    (A.meridianDiskPathMap H (A.actualMeridianDisk H))
    (A.meridianDiskPathMap_endpoints H (A.actualMeridianDisk H))
    (characterFirstCohomologyClass A.Complement k base χ)
  rw [characterFirstClass_closedPathEvaluation]
  exact (hχ H).symm

end ChenRanks.AffineArrangement
