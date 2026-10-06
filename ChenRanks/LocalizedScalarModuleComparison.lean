import Mathlib.RingTheory.Localization.BaseChange

/-!
# True module base change for a genuine scalar localization pushout

The scalar pushout is derived from the two actual localization
properties. Native pushout cancellation then identifies the two literal
module tensor products, with the actual coefficient map on genuine pure
tensors. No tensor-equivalence, module freedom, faithfulness, or local
component-isomorphism assumption is supplied.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks

variable (S R T A : Type*) [CommRing S] [CommRing R] [CommRing T] [CommRing A]
variable [Algebra S R] [Algebra S T] [Algebra T A] [Algebra S A] [Algebra R A]
variable [IsScalarTower S T A] [IsScalarTower S R A]
variable (D : Submonoid S) [hR : IsLocalization D R]
variable [hA : IsLocalization (D.map (algebraMap S T)) A]
variable (N : Type*) [AddCommGroup N] [Module S N] [Module T N] [IsScalarTower S T N]

include D hR hA

/-- The actual scalar pushout is a theorem derived from actual
localization, rather than an additional compatibility premise. -/
theorem localizedScalar_isPushout : Algebra.IsPushout S R T A := by
  letI : IsLocalization (Algebra.algebraMapSubmonoid T D) A := hA
  exact Algebra.IsPushout.symm (Algebra.isPushout_of_isLocalization D R T A)

/-- The two actual tensor localizations are canonically equivalent over
the actual localized ambient ring. -/
def localizedScalarModuleComparison : A ⊗[T] N ≃ₗ[R] R ⊗[S] N := by
  letI := localizedScalar_isPushout S R T A D
  exact Algebra.IsPushout.cancelBaseChange S R T A N

/-- The comparison's inverse uses the genuine coefficient map, giving
the exact pure-tensor diagram needed for the actual canonical map. -/
theorem localizedScalarModuleComparison_symm_tmul (r : R) (n : N) :
    (localizedScalarModuleComparison S R T A D N).symm (r ⊗ₜ[S] n) =
      algebraMap R A r ⊗ₜ[T] n := by
  letI := localizedScalar_isPushout S R T A D
  exact Algebra.IsPushout.cancelBaseChange_symm_tmul S R T A N r n

end ChenRanks
