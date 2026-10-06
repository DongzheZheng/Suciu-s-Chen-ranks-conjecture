import ChenRanks.KoszulTensorCokernel
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.Localization

/-!
# Actual kernel and cokernel under literal tensor localization

Native localization derives flatness, which gives the genuine tensor
kernel equivalence. The actual cokernel is related by the previously
proved native right-exact scalar-extension equivalence. Injectivity and
surjectivity of native base change therefore kill the literal tensor
localizations of the original kernel and cokernel, respectively.
No flatness or exactness conclusion is taken as an extra premise.

This is a generic bridge. Actual finiteness, grading, and support of the
original canonical Koszul family map still require specialization.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks

variable (S R : Type*) [CommRing S] [CommRing R] [Algebra S R]
variable (D : Submonoid S) [hLoc : IsLocalization D R]
variable (M N : Type*) [AddCommGroup M] [AddCommGroup N]
variable [Module S M] [Module S N] (f : M →ₗ[S] N)

include D hLoc

/-- The target is the actual kernel of native base change of the same
original map, identified with the actual tensor of its original kernel. -/
def localizedMapKernelEquiv :
    R ⊗[S] LinearMap.ker f ≃ₗ[R] LinearMap.ker (f.baseChange R) := by
  letI := IsLocalization.flat R D
  exact LinearMap.tensorKerEquiv R R f

/-- Actual injectivity after localization kills the actual original
kernel's literal tensor localization. -/
theorem localizedMapKernel_subsingleton_of_injective
    (hf : Function.Injective (f.baseChange R)) :
    Subsingleton (R ⊗[S] LinearMap.ker f) := by
  have hk : LinearMap.ker (f.baseChange R) = ⊥ := LinearMap.ker_eq_bot.mpr hf
  letI : Subsingleton (LinearMap.ker (f.baseChange R)) :=
    Submodule.subsingleton_iff_eq_bot.mpr hk
  refine ⟨fun z t => (localizedMapKernelEquiv S R D M N f).injective ?_⟩
  exact Subsingleton.elim _ _

omit D hLoc in
/-- Actual surjectivity of scalar extension kills the actual original
cokernel's literal tensor product. This part does not need flatness. -/
theorem baseChangeCokernel_subsingleton_of_surjective
    (hf : Function.Surjective (f.baseChange R)) :
    Subsingleton (R ⊗[S] (N ⧸ LinearMap.range f)) := by
  have hf' : Function.Surjective (AlgebraTensorModule.lTensor R R f) := hf
  have hr : LinearMap.range (AlgebraTensorModule.lTensor R R f) = ⊤ :=
    LinearMap.range_eq_top.mpr hf'
  letI : Subsingleton ((R ⊗[S] N) ⧸ LinearMap.range (AlgebraTensorModule.lTensor R R f)) :=
    Submodule.Quotient.subsingleton_iff.mpr hr
  refine ⟨fun z t => (Koszul.scalarExtensionCokerEquiv R f).injective ?_⟩
  exact Subsingleton.elim _ _

end ChenRanks
