import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Genuine two-vector evaluation on the original exterior algebra

The native exterior square is an actual submodule of the original exterior
algebra. A genuine vector-space complement supplies a projection to that
submodule. The native determinant pairing then supplies an actual linear
functional whose value on every product of two original generators is
their determinant. No exterior pairing, projection or evaluation identity
is a premise. Values in other degrees are irrelevant to this construction;
only the proved restriction to the actual exterior square is used.
-/

noncomputable section

namespace ChenRanks

variable (k M : Type*) [Field k] [AddCommGroup M] [Module k M]

/-- The native projection from the original algebra onto its actual
exterior-square submodule, constructed from a true complement. -/
def nativeExteriorTwoProjection :
    ExteriorAlgebra k M →ₗ[k] (⋀[k]^2 M) :=
  (⋀[k]^2 M).linearProjOfIsCompl
    ((⋀[k]^2 M).exists_isCompl.choose)
    ((⋀[k]^2 M).exists_isCompl.choose_spec)

@[simp] theorem nativeExteriorTwoProjection_subtype (w : ⋀[k]^2 M) :
    nativeExteriorTwoProjection k M (w : ExteriorAlgebra k M) = w :=
  Submodule.linearProjOfIsCompl_apply_left
    ((⋀[k]^2 M).exists_isCompl.choose_spec) w

/-- Two original functionals evaluate the original exterior algebra
by the actual native determinant pairing in degree two. -/
def nativeExteriorTwoEvaluation (φ ψ : Module.Dual k M) :
    ExteriorAlgebra k M →ₗ[k] k :=
  (exteriorPower.pairingDual k M 2
    (exteriorPower.ιMulti k 2 ![φ, ψ])).comp
    (nativeExteriorTwoProjection k M)

/-- The original exterior product is the original native exterior-square
element, with no chosen exterior-power identification. -/
theorem nativeExteriorGeneratorProduct_eq_two (u v : M) :
    ExteriorAlgebra.ι k u * ExteriorAlgebra.ι k v =
      (exteriorPower.ιMulti k 2 ![u, v] : ExteriorAlgebra k M) := by
  change _ = ExteriorAlgebra.ιMulti k 2 ![u, v]
  simp [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply,
    Matrix.vecTail]

/-- Genuine evaluation of two original generators is their genuine
determinant; it does not require finite-dimensionality of the generator space. -/
theorem nativeExteriorTwoEvaluation_generator_product
    (φ ψ : Module.Dual k M) (u v : M) :
    nativeExteriorTwoEvaluation k M φ ψ
      (ExteriorAlgebra.ι k u * ExteriorAlgebra.ι k v) =
        φ u * ψ v - ψ u * φ v := by
  rw [nativeExteriorGeneratorProduct_eq_two]
  unfold nativeExteriorTwoEvaluation
  rw [LinearMap.comp_apply, nativeExteriorTwoProjection_subtype,
    exteriorPower.pairingDual_ιMulti_ιMulti]
  simp [Matrix.det_fin_two, Matrix.of_apply]

end ChenRanks
