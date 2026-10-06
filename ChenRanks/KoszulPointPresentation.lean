import ChenRanks.KoszulPresentation
import ChenRanks.KoszulTensorCokernel

/-!
# Tensoring the proved presentation of the original Koszul module

This file starts with the literal tensor fibre of the original first-cycle
quotient. The already proved presentation equivalence and genuine tensor
right exactness give an equivalence to a cokernel on the true free second
Koszul term. No fibre formula or pointwise exactness is supplied as input.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

section ScalarExtensionEquivalence

variable {R : Type*} [CommRing R]
variable (A : Type*) [CommRing A] [Algebra R A]
variable {M T N : Type*} [AddCommGroup M] [AddCommGroup T] [AddCommGroup N]
variable [_root_.Module R M] [_root_.Module R T] [_root_.Module R N]

/-- Extend an actual cokernel equivalence by actual tensor scalar
extension, then use the genuine tensor/cokernel equivalence. -/
def scalarExtensionCokerTransfer (f : M →ₗ[R] T) (e : N ≃ₗ[R] (T ⧸ LinearMap.range f)) :
    (A ⊗[R] N) ≃ₗ[A]
      ((A ⊗[R] T) ⧸ LinearMap.range (AlgebraTensorModule.lTensor A A f)) :=
  (e.baseChange R A _ _).trans (scalarExtensionCokerEquiv A f)

/-- Pure tensors are computed for arbitrary actual equivalences before
any original Koszul quotient or presentation proof is supplied. -/
@[simp] theorem scalarExtensionCokerTransfer_tmul_mk
    (f : M →ₗ[R] T) (e : N ≃ₗ[R] (T ⧸ LinearMap.range f))
    (a : A) (n : N) (z : T) (h : e n = Submodule.Quotient.mk z) :
    scalarExtensionCokerTransfer A f e (a ⊗ₜ[R] n) =
      Submodule.Quotient.mk (a ⊗ₜ[R] z) := by
  rw [scalarExtensionCokerTransfer, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    h, scalarExtensionCokerEquiv_tmul_mk]

end ScalarExtensionEquivalence

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable (K : Submodule k (⋀[k]^2 V)) (a : V →ₗ[k] k)

/-- The actual relation map in the genuine scalar extension of the proved
second-term presentation. -/
def pointPresentationRelationExtension :
    (PointScalars k V a ⊗[S k V] (C3 k V × (S k V ⊗[k] K))) →ₗ[PointScalars k V a]
      (PointScalars k V a ⊗[S k V] C2 k V) :=
  AlgebraTensorModule.lTensor (PointScalars k V a) (PointScalars k V a)
    (presentationRelations k V K)

variable [FiniteDimensional k V] [CharZero k]

/-- The literal original tensor fibre is proved equivalent to the cokernel
on the actual tensor-extended second Koszul term. This combines an actual
presentation theorem with right exactness, rather than redefining the fibre. -/
def pointPresentationCokerEquiv :
    PointFiber k V K a ≃ₗ[k]
      ((PointScalars k V a ⊗[S k V] C2 k V) ⧸
        LinearMap.range (pointPresentationRelationExtension k V K a)) :=
  (scalarExtensionCokerTransfer (PointScalars k V a) (presentationRelations k V K)
    (presentationEquiv k V K).symm).restrictScalars k

/-- On actual representatives the proved fibre/presentation equivalence has
the expected pure-tensor map into the actual extended free-term quotient. -/
@[simp] theorem pointPresentationCokerEquiv_tmul_secondTensorToModule
    (c : PointScalars k V a) (z : C2 k V) :
    pointPresentationCokerEquiv k V K a
        (c ⊗ₜ[S k V] secondTensorToModule k V K z) =
      Submodule.Quotient.mk (c ⊗ₜ[S k V] z) := by
  have hz : (presentationEquiv k V K).symm (secondTensorToModule k V K z) =
      Submodule.Quotient.mk z := by
    apply (presentationEquiv k V K).injective
    simp only [LinearEquiv.apply_symm_apply]
    rfl
  exact scalarExtensionCokerTransfer_tmul_mk (PointScalars k V a)
    (presentationRelations k V K) (presentationEquiv k V K).symm
    c (secondTensorToModule k V K z) z hz

end ChenRanks.Koszul
