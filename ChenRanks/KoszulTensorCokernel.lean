import ChenRanks.KoszulPointCoefficients
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Actual scalar extension of the original Koszul quotient

The fibre is the genuine tensor product with the original module.  Right
exactness gives a proved cokernel equivalence; it does not redefine the
fibre or assume flatness.  The relation map remains the original map into
the actual first Koszul cycles.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

section ScalarExtensionCokernel

variable {R : Type*} [CommRing R]
variable (A : Type*) [CommRing A] [Algebra R A]
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
variable [_root_.Module R M] [_root_.Module R N]

/-- Tensoring a true image inclusion has the same image as tensoring the
original map.  Surjectivity onto the image is proved before tensoring. -/
theorem scalarExtension_range (f : M →ₗ[R] N) :
    LinearMap.range (AlgebraTensorModule.lTensor A A f) =
      LinearMap.range (AlgebraTensorModule.lTensor A A (LinearMap.range f).subtype) := by
  have hc : (LinearMap.range f).subtype.comp f.rangeRestrict = f := rfl
  have he :
      (AlgebraTensorModule.lTensor A A (LinearMap.range f).subtype).comp
          (AlgebraTensorModule.lTensor A A f.rangeRestrict) =
        AlgebraTensorModule.lTensor A A f := by
    rw [← AlgebraTensorModule.lTensor_comp, hc]
  have hs : Function.Surjective (AlgebraTensorModule.lTensor A A f.rangeRestrict) := by
    change Function.Surjective (f.rangeRestrict.lTensor A)
    apply LinearMap.lTensor_surjective
    rw [← LinearMap.range_eq_top, LinearMap.range_rangeRestrict]
  rw [← he, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr hs)]

/-- A genuine right-exact tensor/cokernel equivalence, with no exactness or
flatness hypothesis on scalar extension. -/
def scalarExtensionCokerEquiv (f : M →ₗ[R] N) :
    (A ⊗[R] (N ⧸ LinearMap.range f)) ≃ₗ[A]
      ((A ⊗[R] N) ⧸ LinearMap.range (AlgebraTensorModule.lTensor A A f)) :=
  (AlgebraTensorModule.tensorQuotientEquiv A R A (LinearMap.range f)).trans
    (Submodule.quotEquivOfEq _ _ (scalarExtension_range A f).symm)

@[simp] theorem scalarExtensionCokerEquiv_tmul_mk (f : M →ₗ[R] N) (a : A) (n : N) :
    scalarExtensionCokerEquiv A f (a ⊗ₜ[R] Submodule.Quotient.mk n) =
      Submodule.Quotient.mk (a ⊗ₜ[R] n) := by
  simp only [scalarExtensionCokerEquiv, LinearEquiv.trans_apply,
    AlgebraTensorModule.tensorQuotientEquiv_apply_tmul, Submodule.quotEquivOfEq_mk]

end ScalarExtensionCokernel

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable (K : Submodule k (⋀[k]^2 V)) (a : V →ₗ[k] k)

/-- The scalar extension of the original quadratic relation map into the
original cycle module, using the actual point evaluation algebra. -/
def pointOriginalRelationExtension :
    (PointScalars k V a ⊗[S k V] (S k V ⊗[k] K)) →ₗ[PointScalars k V a]
      (PointScalars k V a ⊗[S k V] LinearMap.ker (delta1 k V)) :=
  AlgebraTensorModule.lTensor (PointScalars k V a) (PointScalars k V a)
    (relationMap k V K)

/-- The actual tensor fibre of the original Koszul module is proved
equivalent to the cokernel of its genuinely tensor-extended relation map. -/
def pointOriginalCokerEquiv :
    PointFiber k V K a ≃ₗ[k]
      ((PointScalars k V a ⊗[S k V] LinearMap.ker (delta1 k V)) ⧸
        LinearMap.range (pointOriginalRelationExtension k V K a)) :=
  (scalarExtensionCokerEquiv (PointScalars k V a) (relationMap k V K)).restrictScalars k

@[simp] theorem pointOriginalCokerEquiv_tmul_mk
    (c : PointScalars k V a) (z : LinearMap.ker (delta1 k V)) :
    pointOriginalCokerEquiv k V K a (c ⊗ₜ[S k V] Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (c ⊗ₜ[S k V] z) :=
  scalarExtensionCokerEquiv_tmul_mk (PointScalars k V a) (relationMap k V K) c z

end ChenRanks.Koszul
