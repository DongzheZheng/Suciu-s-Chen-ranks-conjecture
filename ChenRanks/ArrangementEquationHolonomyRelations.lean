import ChenRanks.ArrangementEquationGroupCupKernel
import ChenRanks.ScalarGroupHolonomyRelations

/-! The paper's genuine equation-dual quadratic relations vanish in the
actual original group's second lower-central piece. The identification
uses actual equation characters and determinant duality. No quadratic
relation vanishing, formality or group comparison is an input. -/
noncomputable section
namespace ChenRanks.AffineArrangement
open SingularCohomology
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (base : A.Complement)
local instance : PathConnectedSpace A.Complement :=
  A.complement_pathConnectedSpace_from_actual_equations

/-- Actual dual evaluation identifies the two genuine dual maps. -/
theorem equationDualScalarFirst_eval_map :
    (Module.Dual.eval ℂ (scalarLowerCentralPiece ℂ (FundamentalGroup A.Complement base) 0)).comp
      (A.actualEquationDualScalarFirst ℂ base).toLinearMap =
    (A.actualScalarFirstDualEquationCoefficients ℂ base).toLinearMap.dualMap := by
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro ell
  exact A.actualEquationDualScalarFirst_evaluation ℂ base v ell

/-- The determinant pairing is unchanged under the actual equation duality. -/
theorem equationDualScalarFirst_exterior_pairing
    (x : ⋀[ℂ]^2 (Module.Dual ℂ (ι → ℂ)))
    (a : ⋀[ℂ]^2 (Module.Dual ℂ
      (scalarLowerCentralPiece ℂ (FundamentalGroup A.Complement base) 0))) :
    exteriorPower.pairingDual ℂ
      (Module.Dual ℂ (scalarLowerCentralPiece ℂ (FundamentalGroup A.Complement base) 0)) 2
      (exteriorPower.map 2
        (Module.Dual.eval ℂ (scalarLowerCentralPiece ℂ (FundamentalGroup A.Complement base) 0))
        (exteriorPower.map 2 (A.actualEquationDualScalarFirst ℂ base).toLinearMap x)) a =
    exteriorPower.pairingDual ℂ (ι → ℂ) 2 x
      (exteriorPower.map 2 (A.actualScalarFirstDualEquationCoefficients ℂ base).toLinearMap a) := by
  have hext :
      (exteriorPower.map 2
        (Module.Dual.eval ℂ (scalarLowerCentralPiece ℂ (FundamentalGroup A.Complement base) 0))).comp
        (exteriorPower.map 2 (A.actualEquationDualScalarFirst ℂ base).toLinearMap) =
      exteriorPower.map 2 (A.actualScalarFirstDualEquationCoefficients ℂ base).toLinearMap.dualMap := by
    rw [← exteriorPower.map_comp, A.equationDualScalarFirst_eval_map base]
  have hpoint := DFunLike.congr_fun hext x
  simp only [LinearMap.comp_apply] at hpoint
  rw [hpoint]
  exact DFunLike.congr_fun (DFunLike.congr_fun
    (Koszul.exteriorPairingDual_naturality ℂ (ι → ℂ)
      (Module.Dual ℂ (scalarLowerCentralPiece ℂ (FundamentalGroup A.Complement base) 0))
      (A.actualScalarFirstDualEquationCoefficients ℂ base).toLinearMap 2) x) a

/-- Original group cups in first-quotient coordinates are the same true
cups in the actual equation coordinates. -/
theorem scalarFirstGroupQuadraticCup_equations :
    scalarFirstGroupQuadraticCup ℂ (FundamentalGroup A.Complement base) =
      (A.equationNativeGroupQuadraticCup base).comp
        (exteriorPower.map 2 (A.actualScalarFirstDualEquationCoefficients ℂ base).toLinearMap) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  have ha : a = ![a 0, a 1] := by
    ext i
    fin_cases i <;> rfl
  rw [ha]
  change groupCharacterQuadraticCup ℂ (FundamentalGroup A.Complement base)
      (exteriorPower.map 2 (scalarFirstLowerCentralDualCharacters ℂ
        (FundamentalGroup A.Complement base)).toLinearMap
          (exteriorWedge (k := ℂ) (a 0) (a 1))) = _
  rw [exteriorPowerMap_exteriorWedge, groupCharacterQuadraticCup_exteriorWedge]
  change _ = groupCharacterQuadraticCup ℂ (FundamentalGroup A.Complement base)
    (exteriorPower.map 2 (A.actualEquationCoefficientCharacters ℂ base).toLinearMap
      (exteriorPower.map 2 (A.actualScalarFirstDualEquationCoefficients ℂ base).toLinearMap
        (exteriorWedge (k := ℂ) (a 0) (a 1))))
  rw [exteriorPowerMap_exteriorWedge, exteriorPowerMap_exteriorWedge,
    groupCharacterQuadraticCup_exteriorWedge]
  change groupCharacterCup ℂ (FundamentalGroup A.Complement base)
      (scalarFirstLowerCentralDualCharacters ℂ (FundamentalGroup A.Complement base) (a 0))
      (scalarFirstLowerCentralDualCharacters ℂ (FundamentalGroup A.Complement base) (a 1)) =
    groupCharacterCup ℂ (FundamentalGroup A.Complement base)
      (A.actualEquationCoefficientCharacters ℂ base
        (A.actualScalarFirstDualEquationCoefficients ℂ base (a 0)))
      (A.actualEquationCoefficientCharacters ℂ base
        (A.actualScalarFirstDualEquationCoefficients ℂ base (a 1)))
  rw [A.actualScalarFirstDualEquationCoefficients_character,
    A.actualScalarFirstDualEquationCoefficients_character]

/-- The actual paper relation space maps into the actual original group relation space. -/
theorem equationHolonomyRelations_map_le :
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel).map
      (exteriorPower.map 2 (A.actualEquationDualScalarFirst ℂ base).toLinearMap) ≤
      scalarGroupHolonomyRelations ℂ (FundamentalGroup A.Complement base) := by
  rintro _ ⟨x, hx, rfl⟩
  change exteriorPower.pairingDual ℂ
    (Module.Dual ℂ (scalarLowerCentralPiece ℂ (FundamentalGroup A.Complement base) 0)) 2
    (exteriorPower.map 2
      (Module.Dual.eval ℂ (scalarLowerCentralPiece ℂ (FundamentalGroup A.Complement base) 0))
      (exteriorPower.map 2 (A.actualEquationDualScalarFirst ℂ base).toLinearMap x)) ∈
    (scalarFirstGroupCupKernel ℂ (FundamentalGroup A.Complement base)).dualAnnihilator
  apply (Submodule.mem_dualAnnihilator _).mpr
  intro a ha
  rw [A.equationDualScalarFirst_exterior_pairing base]
  apply (Submodule.mem_dualAnnihilator _).mp hx
  rw [← A.equationNativeGroupQuadraticCup_kernel base]
  change A.equationNativeGroupQuadraticCup base
    (exteriorPower.map 2 (A.actualScalarFirstDualEquationCoefficients ℂ base).toLinearMap a) = 0
  change scalarFirstGroupQuadraticCup ℂ (FundamentalGroup A.Complement base) a = 0 at ha
  rw [A.scalarFirstGroupQuadraticCup_equations base] at ha
  exact ha

/-- The paper's original quadratic relations vanish under the genuine
second lower-central bracket of its original fundamental group. -/
theorem equationHolonomyRelations_le_originalBracketKernel :
    Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel ≤
      ((scalarFirstExteriorBracket ℂ (FundamentalGroup A.Complement base)).comp
        (exteriorPower.map 2 (A.actualEquationDualScalarFirst ℂ base).toLinearMap)).ker := by
  intro x hx
  exact scalarGroupHolonomyRelations_le_bracketKernel ℂ (FundamentalGroup A.Complement base)
    (A.equationHolonomyRelations_map_le base ⟨x, hx, rfl⟩)

end ChenRanks.AffineArrangement
