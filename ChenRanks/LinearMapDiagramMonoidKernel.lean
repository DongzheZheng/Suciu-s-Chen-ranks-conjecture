import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Quotient.Basic

/-! A full original linear-map diagram transports the true kernel already
in additive commutative monoids. The proof needs only the actual native
parents stored in LinearMap/LinearEquiv; no reconstruction of additive
group parents is required. No kernel comparison is assumed. -/

noncomputable section

namespace ChenRanks

variable (R : Type*) [Semiring R]
variable {M M' N N' : Type*}
variable [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N] [AddCommMonoid N']
variable [Module R M] [Module R M'] [Module R N] [Module R N']

/-- The same genuine kernel comparison, derived from a complete proved
original diagram, with every original map and equivalence implicit. -/
def monoidDiagramKernelEquiv
    {f : M →ₗ[R] N} {g : M' →ₗ[R] N'}
    {eM : M' ≃ₗ[R] M} {eN : N' ≃ₗ[R] N}
    (h : eN.toLinearMap.comp g = f.comp eM.toLinearMap) :
    LinearMap.ker g ≃ₗ[R] LinearMap.ker f where
  toFun x := ⟨eM x, by
    apply LinearMap.mem_ker.mpr
    have hx := DFunLike.congr_fun h (x : M')
    have hz : g (x : M') = 0 := LinearMap.mem_ker.mp x.property
    change eN (g (x : M')) = f (eM (x : M')) at hx
    rw [hz, map_zero] at hx
    exact hx.symm⟩
  invFun y := ⟨eM.symm y, by
    apply LinearMap.mem_ker.mpr
    apply eN.injective
    have hy := DFunLike.congr_fun h (eM.symm (y : M))
    change eN (g (eM.symm (y : M))) = f (eM (eM.symm (y : M))) at hy
    rw [eM.apply_symm_apply] at hy
    rw [map_zero]
    exact hy.trans (LinearMap.mem_ker.mp y.property)⟩
  left_inv x := by
    apply Subtype.ext
    exact eM.symm_apply_apply (x : M')
  right_inv y := by
    apply Subtype.ext
    exact eM.apply_symm_apply (y : M)
  map_add' x y := by
    apply Subtype.ext
    exact eM.map_add (x : M') (y : M')
  map_smul' c x := by
    apply Subtype.ext
    exact eM.map_smul c (x : M')

end ChenRanks
