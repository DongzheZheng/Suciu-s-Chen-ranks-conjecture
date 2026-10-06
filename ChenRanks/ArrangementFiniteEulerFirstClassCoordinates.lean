import ChenRanks.ArrangementFiniteEulerMonodromyEquationCharacters
import ChenRanks.ArrangementFiniteEulerAbelianCoordinates
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Original first lower-central classes and actual finite monodromy coordinates

The equation-dual/first-quotient equivalence was constructed from native
abelianization, the original augmentation cotangent and the actual
singular cohomology basis. The actual finite target's abelian coordinate
equivalence was constructed from its true native homogeneous tail.
The calculated original monodromy periods identify these two maps on
the original group classes. Genuine scalar duality proves equality in
the actual vector quotient; no equality of the two maps is assumed.
-/

noncomputable section
namespace ChenRanks.AffineArrangement
open LieComparison
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (c : ℕ) (hc : 1 ≤ c)

local instance firstClassComplementPathConnected : PathConnectedSpace A.Complement :=
  A.complement_pathConnectedSpace_from_actual_equations

/-- A scalar dual functional transported along the two genuine original
linear equivalences. -/
def actualFiniteEulerFirstClassDual (base : A.Complement)
    (ell : Module.Dual ℂ (A.ActualFiniteEulerAxisQuotient c)) :
    Module.Dual ℂ
      (scalarLowerCentralPiece ℂ (FundamentalGroup A.Complement base) 0) :=
  (ell.comp (A.actualFiniteEulerAxisOriginalEquiv c hc).symm.toLinearMap).comp
    (A.actualEquationDualScalarFirst ℂ base).symm.toLinearMap

/-- Its actual original equation coefficients follow from the true
dual evaluation and the proved original generator formula. -/
theorem actualFiniteEulerFirstClassDual_coefficients (base : A.Complement)
    (ell : Module.Dual ℂ (A.ActualFiniteEulerAxisQuotient c)) :
    A.actualScalarFirstDualEquationCoefficients ℂ base
        (A.actualFiniteEulerFirstClassDual c hc base ell) =
      fun H => ell (A.actualFiniteEulerAxisGeneratorClass c H) := by
  funext H
  have he := A.actualEquationDualScalarFirst_evaluation ℂ base
    (LinearMap.proj H) (A.actualFiniteEulerFirstClassDual c hc base ell)
  change A.actualFiniteEulerFirstClassDual c hc base ell
      (A.actualEquationDualScalarFirst ℂ base (LinearMap.proj H)) =
    A.actualScalarFirstDualEquationCoefficients ℂ base
      (A.actualFiniteEulerFirstClassDual c hc base ell) H at he
  rw [← he]
  change ell ((A.actualFiniteEulerAxisOriginalEquiv c hc).symm
      ((A.actualEquationDualScalarFirst ℂ base).symm
        (A.actualEquationDualScalarFirst ℂ base (LinearMap.proj H)))) = _
  rw [LinearEquiv.symm_apply_apply,
    A.actualFiniteEulerAxisOriginalEquiv_symm_projection c hc H]

/-- The genuine original first quotient character is the actual
monodromy character, proved through actual equation characters. -/
theorem actualFiniteEulerFirstClassDual_character (base : A.Complement)
    (ell : Module.Dual ℂ (A.ActualFiniteEulerAxisQuotient c)) :
    scalarFirstLowerCentralDualCharacters ℂ (FundamentalGroup A.Complement base)
        (A.actualFiniteEulerFirstClassDual c hc base ell) =
      A.actualFiniteEulerAxisMonodromyCharacter c base ell := by
  rw [← A.actualScalarFirstDualEquationCoefficients_character ℂ base,
    A.actualFiniteEulerFirstClassDual_coefficients c hc base ell]
  exact A.actualFiniteEulerMonodromy_equationCharacters c base ell

/-- The original group's true first class is carried to the actual
finite monodromy axis class. Neither side is defined from the other. -/
theorem actualFiniteEulerAxisCharacter_originalFirstClass
    (base : A.Complement) (g : FundamentalGroup A.Complement base) :
    Multiplicative.toAdd (A.actualFiniteEulerAxisCharacter c
        (A.actualFiniteEulerMonodromy c base g)) =
      (A.actualFiniteEulerAxisOriginalEquiv c hc).symm
        ((A.actualEquationDualScalarFirst ℂ base).symm
          (GroupComparison.originalScalarFirstClass ℂ
            (FundamentalGroup A.Complement base) g)) := by
  apply _root_.Module.eval_apply_injective ℂ
    (V := A.ActualFiniteEulerAxisQuotient c)
  apply LinearMap.ext
  intro ell
  change ell (Multiplicative.toAdd (A.actualFiniteEulerAxisCharacter c
      (A.actualFiniteEulerMonodromy c base g))) = _
  have he := DFunLike.congr_fun
    (A.actualFiniteEulerFirstClassDual_character c hc base ell) (Additive.ofMul g)
  rw [scalarFirstLowerCentralDualCharacters_groupClass,
    A.actualFiniteEulerAxisMonodromyCharacter_apply c base ell g] at he
  exact he.symm

end ChenRanks.AffineArrangement
