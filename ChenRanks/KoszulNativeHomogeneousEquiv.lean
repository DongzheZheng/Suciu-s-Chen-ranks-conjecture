import ChenRanks.KoszulCanonicalFamilyGradingObjects

/-!
# The proved original grading with cached native scalar parents

All dictionaries are the existing original quotient and homogeneous
quotient dictionaries. The already proved actual grading equivalence is
checked once on generic original V, K and basis data against these same
native parents. Its specialization then retains the native scalar action
without repeatedly unfolding the whole actual dual-subspace quotient.
No action equality, decomposition, or equivalence is an input.
-/

noncomputable section

open scoped DirectSum

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {τ : Type*} [Fintype τ] (b : _root_.Module.Basis τ k V)
variable (K : Submodule k (⋀[k]^2 V))

local instance (priority := 2500) nativeGradingOriginalGroup : AddCommGroup (Module k V K) :=
  originalModuleAddCommGroup k V K

local instance (priority := 2500) nativeGradingOriginalMonoid : AddCommMonoid (Module k V K) :=
  (originalModuleAddCommGroup k V K).toAddCommMonoid

local instance (priority := 2500) nativeGradingOriginalBaseCoefficients :
    _root_.Module k (Module k V K) := originalModuleScalarModule k V K

local instance (priority := 2500) nativeGradingDegreeGroup (r : ℕ) :
    AddCommGroup (homogeneousModule k V b K r) :=
  canonicalHomogeneousQuotientAddCommGroup k V b K r

local instance (priority := 2500) nativeGradingDegreeMonoid (r : ℕ) :
    AddCommMonoid (homogeneousModule k V b K r) :=
  (canonicalHomogeneousQuotientAddCommGroup k V b K r).toAddCommMonoid

local instance (priority := 2500) nativeGradingDegreeBaseCoefficients (r : ℕ) :
    _root_.Module k (homogeneousModule k V b K r) :=
  canonicalHomogeneousQuotientBaseCoefficients k V b K r

/-- The same true original grading equivalence, with its unchanged
native quotient and scalar structures checked once on generic data. -/
def nativeHomogeneousDirectSumEquiv :
    (⨁ r, homogeneousModule k V b K r) ≃ₗ[k] Module k V K :=
  homogeneousDirectSumEquiv k V b K

/-- The native generic equivalence has exactly the original true degree
inclusion on an actual degree insertion. -/
theorem nativeHomogeneousDirectSumEquiv_lof (r : ℕ)
    (z : homogeneousModule k V b K r) :
    nativeHomogeneousDirectSumEquiv k V b K
      (DirectSum.lof k ℕ (homogeneousModule k V b K) r z) =
      degreeQuotientInclusion k V b K r z :=
  assembleHomogeneous_lof k V b K r z

end ChenRanks.Koszul
