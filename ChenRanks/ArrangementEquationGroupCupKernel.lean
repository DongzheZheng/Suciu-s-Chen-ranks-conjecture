import ChenRanks.ArrangementEquationDualScalarFirst
import ChenRanks.ArrangementSingularCupKernelEquality
import ChenRanks.SingularGroupCupComparison
import ChenRanks.GroupCharacterCupAlternation

/-! The paper's original rational logarithmic kernel is the actual
original group cup kernel in the genuine equation coordinates. This uses
the proved injectivity of the original group-to-space H2 map and actual
character cups; no formality or higher Chen comparison is an input. -/
noncomputable section
namespace ChenRanks.AffineArrangement
open SingularCohomology
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
local instance : PathConnectedSpace A.Complement :=
  A.complement_pathConnectedSpace_from_actual_equations

/-- The native group cup on the actual original equation characters. -/
def equationNativeGroupQuadraticCup (base : A.Complement) :
    (⋀[ℂ]^2 (ι → ℂ)) →ₗ[ℂ]
      groupCohomology.H2 (groupTrivialCoefficients ℂ (FundamentalGroup A.Complement base)) :=
  (groupCharacterQuadraticCup ℂ (FundamentalGroup A.Complement base)).comp
    (exteriorPower.map 2 (A.actualEquationCoefficientCharacters ℂ base).toLinearMap)

/-- The original native character inverse returns the original equation class. -/
theorem equationCharacterFirstClass (base : A.Complement) (a : ι → ℂ) :
    characterFirstCohomologyClass A.Complement ℂ base
      (A.actualEquationCoefficientCharacters ℂ base a) = A.equationWindingClassMap a := by
  apply firstCohomologyToCharacters_injective A.Complement ℂ base
  rw [firstCohomologyToCharacters_characterClass]
  rfl

/-- Actual bar-to-singular pullback preserves the entire original equation cup. -/
theorem equationNativeGroupQuadraticCup_pullback (base : A.Complement) :
    (actualGroupH2ToSingularH2 A.Complement ℂ base).comp
      (A.equationNativeGroupQuadraticCup base) = A.equationQuadraticCup := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  have ha : a = ![a 0, a 1] := by
    ext i
    fin_cases i <;> rfl
  rw [ha]
  change actualGroupH2ToSingularH2 A.Complement ℂ base
      (groupCharacterQuadraticCup ℂ (FundamentalGroup A.Complement base)
        (exteriorPower.map 2 (A.actualEquationCoefficientCharacters ℂ base).toLinearMap
          (exteriorWedge (k := ℂ) (a 0) (a 1)))) = _
  rw [exteriorPowerMap_exteriorWedge, groupCharacterQuadraticCup_exteriorWedge,
    actualGroupH2ToSingularH2_characterCup]
  change cup ℂ A.Complement
      (characterFirstCohomologyClass A.Complement ℂ base
        (A.actualEquationCoefficientCharacters ℂ base (a 0)))
      (characterFirstCohomologyClass A.Complement ℂ base
        (A.actualEquationCoefficientCharacters ℂ base (a 1))) =
    A.equationQuadraticCup (exteriorWedge (k := ℂ) (a 0) (a 1))
  rw [A.equationCharacterFirstClass,
    A.equationCharacterFirstClass, A.equationQuadraticCup_exteriorWedge]

/-- The original kernel identity follows from the proved actual H2 injection. -/
theorem equationNativeGroupQuadraticCup_kernel (base : A.Complement) :
    (A.equationNativeGroupQuadraticCup base).ker = A.rationalQuadraticKernel := by
  have hp := A.equationNativeGroupQuadraticCup_pullback base
  ext x
  change A.equationNativeGroupQuadraticCup base x = 0 ↔ x ∈ A.rationalQuadraticKernel
  rw [← A.equationQuadraticCupKernel_eq_rationalQuadraticKernel]
  change A.equationNativeGroupQuadraticCup base x = 0 ↔ A.equationQuadraticCup x = 0
  rw [← hp]
  change A.equationNativeGroupQuadraticCup base x = 0 ↔
    actualGroupH2ToSingularH2 A.Complement ℂ base (A.equationNativeGroupQuadraticCup base x) = 0
  exact ⟨fun h => by rw [h, map_zero],
    fun h => (actualGroupH2ToSingularH2_injective A.Complement ℂ base)
      (h.trans (map_zero _).symm)⟩

end ChenRanks.AffineArrangement
