import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Base-ring finiteness from the actual annihilator quotient

The actual annihilator kills the original module. Native quotient tensor
comparison therefore identifies the literal tensor product with the
original module itself. If the actual annihilator quotient is finite
over the base ring, genuine tensor base-change finiteness and finite
scalar transitivity make the same original module finite over that base.
No scalar action is replaced, and no finite-dimensional conclusion is
assumed for the original module.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable (M : Type*) [AddCommGroup M] [Module S M] [Module R M]
  [IsScalarTower R S M]

/-- The literal tensor with the actual original annihilator quotient is
the actual original module: the genuine quotient submodule is zero. -/
def annihilatorQuotientTensorEquiv :
    (S ⧸ Module.annihilator S M) ⊗[S] M ≃ₗ[S] M := by
  have hsmul : Module.annihilator S M • (⊤ : Submodule S M) = ⊥ := by
    simpa only [Submodule.annihilator_top] using
      Submodule.annihilator_smul (⊤ : Submodule S M)
  exact (quotTensorEquivQuotSMul M (Module.annihilator S M)).trans
    ((Module.annihilator S M • (⊤ : Submodule S M)).quotEquivOfEqBot hsmul)

/-- Genuine finiteness of the actual annihilator quotient descends to
the original finite module via the actual quotient tensor equivalence. -/
theorem finiteModule_of_annihilatorQuotient_finite
    [Module.Finite S M] [Module.Finite R (S ⧸ Module.annihilator S M)] :
    Module.Finite R M := by
  letI : Module.Finite (S ⧸ Module.annihilator S M)
      ((S ⧸ Module.annihilator S M) ⊗[S] M) :=
    Module.Finite.base_change S (S ⧸ Module.annihilator S M) M
  letI : Module.Finite R ((S ⧸ Module.annihilator S M) ⊗[S] M) :=
    Module.Finite.trans (S ⧸ Module.annihilator S M) _
  exact Module.Finite.of_surjective
    ((annihilatorQuotientTensorEquiv S M).restrictScalars R).toLinearMap
    (annihilatorQuotientTensorEquiv S M).surjective

end ChenRanks
