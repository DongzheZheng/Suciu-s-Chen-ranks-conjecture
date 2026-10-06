import Mathlib.Algebra.Lie.Basic

/-! The genuine group of native Lie automorphisms, with composition,
identity and inverse given by their original native equivalence maps.
This is a target group for actual holonomy representations, never a
replacement for the original topological fundamental group.
-/
noncomputable section
namespace ChenRanks.LieComparison
variable (k L : Type*) [CommRing k] [LieRing L] [LieAlgebra k L]

abbrev NativeLieAutomorphismGroup := L ≃ₗ⁅k⁆ L

instance nativeLieAutomorphismGroup : Group (NativeLieAutomorphismGroup k L) where
  mul f g := g.trans f
  one := LieEquiv.refl
  inv f := f.symm
  mul_assoc f g h := by
    apply LieEquiv.ext
    intro x
    rfl
  one_mul f := by
    apply LieEquiv.ext
    intro x
    rfl
  mul_one f := by
    apply LieEquiv.ext
    intro x
    rfl
  inv_mul_cancel f := by
    apply LieEquiv.ext
    intro x
    exact f.symm_apply_apply x

@[simp] theorem nativeLieAutomorphismGroup_mul_apply
    (f g : NativeLieAutomorphismGroup k L) (x : L) : (f * g) x = f (g x) := rfl

@[simp] theorem nativeLieAutomorphismGroup_one_apply (x : L) :
    (1 : NativeLieAutomorphismGroup k L) x = x := rfl

@[simp] theorem nativeLieAutomorphismGroup_inv_apply
    (f : NativeLieAutomorphismGroup k L) (x : L) : f⁻¹ x = f.symm x := rfl

/-- Forgetting the Lie law retains the actual original automorphism
functions, with the true group operation. -/
def nativeLieAutomorphismUnderlyingPermutation :
    NativeLieAutomorphismGroup k L →* Equiv.Perm L where
  toFun f := f.toLinearEquiv.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

end ChenRanks.LieComparison
