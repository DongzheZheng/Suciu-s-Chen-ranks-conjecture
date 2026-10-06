import ChenRanks.FiniteDimensionalContinuousLieBracket
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.Module.StrongTopology

/-!
# The original complex Lie bracket with its actual real Frechet derivative

The actual complex coordinate norm retains the original complex scalar
action.  Restriction of scalars supplies the actual real normed space and
the actual real continuous bilinear bracket.  Both restriction maps are
native continuous-linear maps; every value is the original complex Lie
bracket.  Thus the derivative domain can be real while the coefficient
operators and the eventual native Lie equivalence remain complex linear.

No real-to-complex linearity or bracket compatibility is supplied as an
input.  These maps are constructed from the original complex structures.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (L : Type*) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

local instance complexBracketNormedAddCommGroup : NormedAddCommGroup L :=
  nativeFiniteNormedAddCommGroup ℂ L
local instance complexBracketNormedSpace : NormedSpace ℂ L := nativeFiniteNormedSpace ℂ L
local instance complexBracketRealNormedSpace : NormedSpace ℝ L :=
  NormedSpace.restrictScalars ℝ ℂ L

local instance complexBracketScalarTower : IsScalarTower ℝ ℂ L where
  smul_assoc r c x := by
    change ((r : ℂ) * c) • x = (r : ℂ) • (c • x)
    exact mul_smul _ _ _

local instance complexBracketSMulCommClass : SMulCommClass ℂ ℝ L where
  smul_comm c r x := by
    change c • ((r : ℂ) • x) = (r : ℂ) • (c • x)
    exact smul_comm _ _ _

/-- The actual real dimension is finite by the original complex dimension. -/
theorem nativeFiniteComplexLieReal_finiteDimensional : FiniteDimensional ℝ L := by
  letI : FiniteDimensional ℝ ℂ := Complex.basisOneI.finiteDimensional_of_finite
  exact FiniteDimensional.trans ℝ ℂ L

/-- The actual complex coordinate norm is complete on the original space. -/
theorem nativeFiniteComplexLie_completeSpace : CompleteSpace L :=
  nativeFinite_completeSpace ℂ L

/-- The real restriction map on actual complex-linear operators, with
its native continuity and unchanged underlying function. -/
def nativeComplexEndRestrictScalars :
    (L →L[ℂ] L) →L[ℝ] (L →L[ℝ] L) :=
  ContinuousLinearMap.restrictScalarsL ℂ L L ℝ ℝ

@[simp] theorem nativeComplexEndRestrictScalars_apply
    (f : L →L[ℂ] L) (x : L) : nativeComplexEndRestrictScalars L f x = f x := rfl

/-- Restriction of scalars respects the actual composition algebra;
this is an actual algebra homomorphism constructed on the same operators. -/
def nativeComplexEndRestrictScalarsAlgHom :
    (L →L[ℂ] L) →ₐ[ℝ] (L →L[ℝ] L) where
  toFun := nativeComplexEndRestrictScalars L
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The original complex bracket, now as an actual real continuous
bilinear map for the original complex norm. -/
def nativeFiniteComplexLieRealBracket : L →L[ℝ] (L →L[ℝ] L) :=
  (nativeComplexEndRestrictScalars L).comp
    ((nativeFiniteContinuousLieBracket ℂ L).restrictScalars ℝ)

@[simp] theorem nativeFiniteComplexLieRealBracket_apply (a b : L) :
    nativeFiniteComplexLieRealBracket L a b = ⁅a, b⁆ := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Genuine real differentiation of the original complex bracket. -/
theorem nativeFiniteComplexLieBracket_hasFDerivAt
    (f g : E → L) (f' g' : E →L[ℝ] L) (x : E)
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun y => ⁅f y, g y⁆)
      ((nativeFiniteComplexLieRealBracket L (f x)).comp g' +
        ((nativeFiniteComplexLieRealBracket L).comp f').flip (g x)) x := by
  have h := ((nativeFiniteComplexLieRealBracket L).hasFDerivAt.comp x hf).clm_apply hg
  simpa only [nativeFiniteComplexLieRealBracket_apply] using h

/-- The actual real derivative still has the original complex brackets. -/
theorem nativeFiniteComplexLieBracket_derivative_apply
    (a b : L) (f' g' : E →L[ℝ] L) (v : E) :
    ((nativeFiniteComplexLieRealBracket L a).comp g' +
      ((nativeFiniteComplexLieRealBracket L).comp f').flip b) v =
    ⁅a, g' v⁆ + ⁅f' v, b⁆ := rfl

end ChenRanks.LieComparison
