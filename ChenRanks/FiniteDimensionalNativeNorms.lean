import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Algebra.Equiv

/-!
# Genuine native norms and native endomorphisms on finite vector spaces

The norm is constructed by pulling back the native sup norm along the
actual finite-basis coordinate equivalence.  The scalar module is the
original module.  Actual finite-dimensional completeness then supplies
the Banach-space structure needed by native vector-valued Poincare.

On the same original finite vector space every actual linear map is
continuous.  The native linear-to-continuous-linear equivalence preserves
actual endomorphism multiplication and the actual identity, so it is an
actual algebra equivalence.  No norm, continuity, operator equivalence,
parallel solution or holonomy comparison is supplied as a premise.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k V : Type*) [NontriviallyNormedField k]

section ConstructedNorm

variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The genuine sup-coordinate norm on the original finite vector space. -/
abbrev nativeFiniteNormedAddCommGroup : NormedAddCommGroup V :=
  NormedAddCommGroup.induced V (Fin (Module.finrank k V) → k)
    (Module.finBasis k V).equivFun.toAddEquiv
    (Module.finBasis k V).equivFun.injective

/-- The original scalar action is a genuine normed-space action for the
actual norm just constructed. -/
abbrev nativeFiniteNormedSpace :
    letI := nativeFiniteNormedAddCommGroup k V
    NormedSpace k V := by
  letI := nativeFiniteNormedAddCommGroup k V
  exact NormedSpace.induced k V (Fin (Module.finrank k V) → k)
    (Module.finBasis k V).equivFun

variable [CompleteSpace k]

/-- Actual finite-dimensionality over the actual complete field gives
actual completeness of the original newly normed vector space. -/
theorem nativeFinite_completeSpace :
    letI := nativeFiniteNormedAddCommGroup k V
    letI := nativeFiniteNormedSpace k V
    CompleteSpace V := by
  letI := nativeFiniteNormedAddCommGroup k V
  letI := nativeFiniteNormedSpace k V
  exact FiniteDimensional.complete k V

end ConstructedNorm

section ExistingNorm

variable [CompleteSpace k] [NormedAddCommGroup V] [NormedSpace k V]
variable [FiniteDimensional k V]

/-- The native finite-dimensional operator equivalence preserves the
actual composition product and the actual identity. -/
def nativeFiniteEndContinuousAlgEquiv :
    Module.End k V ≃ₐ[k] (V →L[k] V) :=
  Module.End.toContinuousLinearMap (𝕜 := k) V

@[simp] theorem nativeFiniteEndContinuousAlgEquiv_apply
    (f : Module.End k V) (x : V) :
    nativeFiniteEndContinuousAlgEquiv k V f x = f x := rfl

@[simp] theorem nativeFiniteEndContinuousAlgEquiv_symm_apply
    (f : V →L[k] V) (x : V) :
    (nativeFiniteEndContinuousAlgEquiv k V).symm f x = f x := rfl

end ExistingNorm

end ChenRanks.LieComparison
