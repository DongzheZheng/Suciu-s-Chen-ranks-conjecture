import ChenRanks.KoszulPointContraction

/-!
# The actual point coefficient algebra and genuine tensor fibre

`PointScalars a` is the original field `k`, tagged with the point so that
its actual `S`-algebra structure is unambiguous.  That structure is the
actual symmetric-algebra evaluation.  The base-field algebra is canonical,
and its tower with the evaluation algebra is proved from `ev.commutes`.

`PointFiber` is literally the tensor product of this coefficient field with
the original `ker δ₁ / im δ₂|K` module.  It is not defined as a desired
pointwise cokernel or Aomoto quotient.  This file supplies the genuine tensor
cancellation equivalence on the actual free terms.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]

/-- The original coefficient field, with its point recorded in the type.
There is no new field or quotient here: the underlying type is exactly `k`. -/
def PointScalars (_a : V →ₗ[k] k) := k

instance pointScalarsField (a : V →ₗ[k] k) : Field (PointScalars k V a) :=
  inferInstanceAs (Field k)

instance pointScalarsBaseAlgebra (a : V →ₗ[k] k) : Algebra k (PointScalars k V a) :=
  inferInstanceAs (Algebra k k)

/-- The actual point action of the original polynomial ring on the original field. -/
instance pointScalarsPolynomialAlgebra (a : V →ₗ[k] k) :
    Algebra (S k V) (PointScalars k V a) :=
  (pointEvaluation k V a).toRingHom.toAlgebra

instance pointScalarsTower (a : V →ₗ[k] k) :
    IsScalarTower k (S k V) (PointScalars k V a) := by
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  change c = pointEvaluation k V a (algebraMap k (S k V) c)
  exact ((pointEvaluation k V a).commutes c).symm

/-- The point tag is removed by the actual identity algebra equivalence. -/
def pointScalarsEquiv (a : V →ₗ[k] k) : PointScalars k V a ≃ₐ[k] k :=
  (AlgEquiv.refl : k ≃ₐ[k] k)

@[simp] theorem pointScalars_algebraMap (a : V →ₗ[k] k) (s : S k V) :
    algebraMap (S k V) (PointScalars k V a) s = pointEvaluation k V a s := rfl

/-- The genuine point fibre of the original quotient module, with the actual
evaluation action of `S` on the coefficient field. -/
abbrev PointFiber (K : Submodule k (⋀[k]^2 V)) (a : V →ₗ[k] k) :=
  PointScalars k V a ⊗[S k V] Module k V K

variable (W : Type*) [AddCommGroup W] [_root_.Module k W]

/-- Actual tensor cancellation for the true evaluated free coefficient term. -/
def pointTensorCancel (a : V →ₗ[k] k) :
    (PointScalars k V a ⊗[S k V] (S k V ⊗[k] W)) ≃ₗ[k] W :=
  ((AlgebraTensorModule.cancelBaseChange k (S k V) (PointScalars k V a)
    (PointScalars k V a) W).restrictScalars k).trans (TensorProduct.lid k W)

@[simp] theorem pointTensorCancel_tmul (a : V →ₗ[k] k)
    (c : PointScalars k V a) (s : S k V) (w : W) :
    pointTensorCancel k V W a (c ⊗ₜ[S k V] (s ⊗ₜ[k] w)) =
      (pointScalarsEquiv k V a c * pointEvaluation k V a s) • w := by
  simp only [pointTensorCancel, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    AlgebraTensorModule.cancelBaseChange_tmul]
  change (pointEvaluation k V a s * pointScalarsEquiv k V a c) • w =
    (pointScalarsEquiv k V a c * pointEvaluation k V a s) • w
  rw [mul_comm]

/-- The actual free-term cancellation agrees with the previously constructed
actual coefficient evaluation, on every original tensor. -/
theorem pointTensorCancel_one (a : V →ₗ[k] k) (z : S k V ⊗[k] W) :
    pointTensorCancel k V W a ((1 : PointScalars k V a) ⊗ₜ[S k V] z) =
      specializePolynomialTensor k V W a z := by
  induction z with
  | zero => simp
  | add z w hz hw => simp only [TensorProduct.tmul_add, map_add, hz, hw]
  | tmul s w =>
    simp only [pointTensorCancel_tmul, map_one, one_mul, specializePolynomialTensor_tmul]

end ChenRanks.Koszul
