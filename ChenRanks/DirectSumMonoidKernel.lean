import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The true direct-sum kernel with only its stored monoid parents

Both sides are native kernels of the original degree maps. Coordinate
identities for the actual `DirectSum.lmap` derive the comparison. No
kernel comparison or additive-group hypothesis is supplied.
-/

noncomputable section

open scoped DirectSum

namespace ChenRanks

variable (R : Type*) [Semiring R]
variable {ι : Type*} {M N : ι → Type*}
variable [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (N i)]
variable [∀ i, Module R (M i)] [∀ i, Module R (N i)]
variable (f : ∀ i, M i →ₗ[R] N i)

/-- The actual inclusion, retaining the native component kernels. -/
def directSumMonoidKernelInclusion :
    (⨁ i, LinearMap.ker (f i)) →ₗ[R] ⨁ i, M i :=
  DirectSum.lmap (fun i => (LinearMap.ker (f i)).subtype)

/-- Its actual range is exactly the kernel of the original sum map. -/
theorem directSumMonoidKernelInclusion_range :
    LinearMap.range (directSumMonoidKernelInclusion R f) =
      LinearMap.ker (DirectSum.lmap f) := by
  unfold directSumMonoidKernelInclusion
  rw [DirectSum.range_lmap, DirectSum.ker_lmap]
  simp only [Submodule.range_subtype]

/-- The genuine inclusion with its codomain restricted to the kernel. -/
def directSumMonoidKernelMap :
    (⨁ i, LinearMap.ker (f i)) →ₗ[R] LinearMap.ker (DirectSum.lmap f) :=
  (directSumMonoidKernelInclusion R f).codRestrict
    (LinearMap.ker (DirectSum.lmap f)) (by
      intro x
      rw [← directSumMonoidKernelInclusion_range R f]
      exact LinearMap.mem_range_self _ x)

theorem directSumMonoidKernelMap_bijective :
    Function.Bijective (directSumMonoidKernelMap R f) := by
  constructor
  · intro x y hxy
    apply (DirectSum.lmap_injective
      (fun i => (LinearMap.ker (f i)).subtype)).mpr
        (fun _ => Subtype.val_injective)
    exact congrArg Subtype.val hxy
  · intro z
    have hz : (z : ⨁ i, M i) ∈
        LinearMap.range (directSumMonoidKernelInclusion R f) := by
      rw [directSumMonoidKernelInclusion_range R f]
      exact z.property
    obtain ⟨x, hx⟩ := hz
    exact ⟨x, Subtype.ext hx⟩

/-- The native direct-sum kernel comparison derived from coordinates. -/
def directSumComponentMonoidKernelEquiv :
    (⨁ i, LinearMap.ker (f i)) ≃ₗ[R] LinearMap.ker (DirectSum.lmap f) :=
  LinearEquiv.ofBijective (directSumMonoidKernelMap R f)
    (directSumMonoidKernelMap_bijective R f)

end ChenRanks
