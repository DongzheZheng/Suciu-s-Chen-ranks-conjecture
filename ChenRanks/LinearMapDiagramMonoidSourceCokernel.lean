import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Quotient.Basic

/-! The genuine cokernel comparison only needs additive groups on the
two targets.  The source parents are precisely the additive monoids
already stored in the original maps and equivalences.  Every map is
implicit, so the proved original full diagram supplies its own parents.
No range or cokernel comparison is assumed. -/

noncomputable section

namespace ChenRanks

variable (R : Type*) [Ring R]
variable {M M' N N' : Type*}
variable [AddCommMonoid M] [AddCommMonoid M'] [AddCommGroup N] [AddCommGroup N']
variable [Module R M] [Module R M'] [Module R N] [Module R N']

/-- The original target equivalence carries the actual range onto the
actual range, using only the source equivalence's true surjectivity. -/
theorem monoidSourceDiagramRange_map_eq
    {f : M →ₗ[R] N} {g : M' →ₗ[R] N'}
    {eM : M' ≃ₗ[R] M} {eN : N' ≃ₗ[R] N}
    (h : eN.toLinearMap.comp g = f.comp eM.toLinearMap) :
    (LinearMap.range g).map eN.toLinearMap = LinearMap.range f := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    refine ⟨eM x, ?_⟩
    have hx := DFunLike.congr_fun h x
    change eN (g x) = f (eM x) at hx
    exact hx.symm
  · rintro ⟨x, rfl⟩
    refine ⟨g (eM.symm x), LinearMap.mem_range_self _ _, ?_⟩
    have hx := DFunLike.congr_fun h (eM.symm x)
    change eN (g (eM.symm x)) = f (eM (eM.symm x)) at hx
    exact hx.trans (congrArg f (eM.apply_symm_apply x))

/-- Native target quotients are equivalent through the same complete
original diagram.  No additive-group parent is rebuilt on either source. -/
def monoidSourceDiagramCokernelEquiv
    {f : M →ₗ[R] N} {g : M' →ₗ[R] N'}
    {eM : M' ≃ₗ[R] M} {eN : N' ≃ₗ[R] N}
    (h : eN.toLinearMap.comp g = f.comp eM.toLinearMap) :
    (N' ⧸ LinearMap.range g) ≃ₗ[R] (N ⧸ LinearMap.range f) :=
  Submodule.Quotient.equiv (LinearMap.range g) (LinearMap.range f) eN
    (monoidSourceDiagramRange_map_eq R h)

end ChenRanks
