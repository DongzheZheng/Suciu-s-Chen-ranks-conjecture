import ChenRanks.FiniteDimensionalNativeNorms
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# The genuine original Lie bracket with its constructed native finite norm

The original finite-dimensional Lie algebra receives the already constructed
coordinate norm.  Its original adjoint map is then made continuous by the
native finite-dimensional operator equivalence, followed by the native
finite-dimensional linear-to-continuous-linear equivalence.  This constructs
the actual continuous bilinear bracket; no continuous bracket, bounded
bracket, bracket-preserving parallel solution or monodromy is an input.

The native Frechet product rule consequently differentiates the actual
original bracket of two actual functions.  This is the analytic bridge needed
to verify bracket preservation of the explicitly constructed parallel sum.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k L : Type*) [NontriviallyNormedField k]
variable [CompleteSpace k]
variable [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]

/-- The actual original bracket, continuous for the actual constructed norm. -/
def nativeFiniteContinuousLieBracket :
    letI := nativeFiniteNormedAddCommGroup k L
    letI := nativeFiniteNormedSpace k L
    L →L[k] (L →L[k] L) := by
  letI := nativeFiniteNormedAddCommGroup k L
  letI := nativeFiniteNormedSpace k L
  exact LinearMap.toContinuousLinearMap
    ((nativeFiniteEndContinuousAlgEquiv k L).toLinearMap.comp
      (LieAlgebra.ad k L).toLinearMap)

/-- This map is precisely the original native bracket on every vector. -/
theorem nativeFiniteContinuousLieBracket_apply :
    letI := nativeFiniteNormedAddCommGroup k L
    letI := nativeFiniteNormedSpace k L
    ∀ x y : L, nativeFiniteContinuousLieBracket k L x y = ⁅x, y⁆ := by
  intro x y
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace k E]

/-- The genuine native product rule for the genuine original bracket. -/
theorem nativeFiniteLieBracket_hasFDerivAt :
    letI := nativeFiniteNormedAddCommGroup k L
    letI := nativeFiniteNormedSpace k L
    ∀ (f g : E → L) (f' g' : E →L[k] L) (x : E),
      HasFDerivAt f f' x → HasFDerivAt g g' x →
      HasFDerivAt (fun y => ⁅f y, g y⁆)
        ((nativeFiniteContinuousLieBracket k L (f x)).comp g' +
          ((nativeFiniteContinuousLieBracket k L).comp f').flip (g x)) x := by
  letI := nativeFiniteNormedAddCommGroup k L
  letI := nativeFiniteNormedSpace k L
  intro f g f' g' x hf hg
  have h := ((nativeFiniteContinuousLieBracket k L).hasFDerivAt.comp x hf).clm_apply hg
  simpa only [nativeFiniteContinuousLieBracket_apply] using h

/-- The derivative really has the original two bracket terms. -/
theorem nativeFiniteLieBracket_derivative_apply :
    letI := nativeFiniteNormedAddCommGroup k L
    letI := nativeFiniteNormedSpace k L
    ∀ (a b : L) (f' g' : E →L[k] L) (v : E),
      ((nativeFiniteContinuousLieBracket k L a).comp g' +
        ((nativeFiniteContinuousLieBracket k L).comp f').flip b) v =
      ⁅a, g' v⁆ + ⁅f' v, b⁆ := by
  intro a b f' g' v
  rfl

end ChenRanks.LieComparison
