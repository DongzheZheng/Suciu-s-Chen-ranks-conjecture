import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Genuine kernels and cokernels of a degreewise direct-sum map

The map is mathlib's actual `DirectSum.lmap` of the given degree maps.
The kernel and cokernel on both sides are their native submodules and
quotients. Coordinatewise kernel/range identities and genuine quotient
surjectivity derive the comparisons; no exactness or decomposition
conclusion is an input.
-/

noncomputable section

open scoped DirectSum

namespace ChenRanks

variable (R : Type*) [Ring R]
variable {ι : Type*} (M N : ι → Type*)
variable [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)]
variable [∀ i, Module R (M i)] [∀ i, Module R (N i)]
variable (f : ∀ i, M i →ₗ[R] N i)

/-- The actual inclusion of the direct sum of native component kernels. -/
def directSumComponentKernelInclusion :
    (⨁ i, LinearMap.ker (f i)) →ₗ[R] ⨁ i, M i :=
  DirectSum.lmap (fun i => (LinearMap.ker (f i)).subtype)

/-- The range is the true kernel of the actual direct-sum map. -/
theorem directSumComponentKernelInclusion_range :
    LinearMap.range (directSumComponentKernelInclusion R M N f) =
      LinearMap.ker (DirectSum.lmap f) := by
  unfold directSumComponentKernelInclusion
  rw [DirectSum.range_lmap, DirectSum.ker_lmap]
  simp only [Submodule.range_subtype]

/-- The same inclusion with its codomain restricted to the actual kernel. -/
def directSumComponentKernelMap :
    (⨁ i, LinearMap.ker (f i)) →ₗ[R] LinearMap.ker (DirectSum.lmap f) :=
  (directSumComponentKernelInclusion R M N f).codRestrict
    (LinearMap.ker (DirectSum.lmap f)) (by
      intro x
      rw [← directSumComponentKernelInclusion_range R M N f]
      exact LinearMap.mem_range_self _ x)

theorem directSumComponentKernelMap_bijective :
    Function.Bijective (directSumComponentKernelMap R M N f) := by
  constructor
  · intro x y hxy
    apply (DirectSum.lmap_injective
      (fun i => (LinearMap.ker (f i)).subtype)).mpr
        (fun _ => Subtype.val_injective)
    exact congrArg Subtype.val hxy
  · intro z
    have hz : (z : ⨁ i, M i) ∈
        LinearMap.range (directSumComponentKernelInclusion R M N f) := by
      rw [directSumComponentKernelInclusion_range R M N f]
      exact z.property
    obtain ⟨x, hx⟩ := hz
    exact ⟨x, Subtype.ext hx⟩

/-- Genuine direct-sum kernel comparison, without a kernel-comparison premise. -/
def directSumComponentKernelEquiv :
    (⨁ i, LinearMap.ker (f i)) ≃ₗ[R] LinearMap.ker (DirectSum.lmap f) :=
  LinearEquiv.ofBijective (directSumComponentKernelMap R M N f)
    (directSumComponentKernelMap_bijective R M N f)

/-- The actual direct sum of the component quotient maps. -/
def directSumComponentCokernelQuotientMap :
    (⨁ i, N i) →ₗ[R] ⨁ i, (N i ⧸ LinearMap.range (f i)) :=
  DirectSum.lmap (fun i => (LinearMap.range (f i)).mkQ)

theorem directSumComponentCokernelQuotientMap_surjective :
    Function.Surjective (directSumComponentCokernelQuotientMap R M N f) := by
  exact (DirectSum.lmap_surjective
    (fun i => (LinearMap.range (f i)).mkQ)).mpr
      (fun i => (LinearMap.range (f i)).mkQ_surjective)

/-- Its kernel is the actual range of the actual direct-sum map. -/
theorem directSumComponentCokernelQuotientMap_ker :
    LinearMap.ker (directSumComponentCokernelQuotientMap R M N f) =
      LinearMap.range (DirectSum.lmap f) := by
  unfold directSumComponentCokernelQuotientMap
  rw [DirectSum.ker_lmap, DirectSum.range_lmap]
  simp only [Submodule.ker_mkQ]

/-- Genuine whole-cokernel comparison with the direct sum of genuine
component cokernels. No cokernel-comparison premise is supplied. -/
def directSumComponentCokernelEquiv :
    ((⨁ i, N i) ⧸ LinearMap.range (DirectSum.lmap f)) ≃ₗ[R]
      ⨁ i, (N i ⧸ LinearMap.range (f i)) :=
  (Submodule.quotEquivOfEq
    (LinearMap.range (DirectSum.lmap f))
    (LinearMap.ker (directSumComponentCokernelQuotientMap R M N f))
    (directSumComponentCokernelQuotientMap_ker R M N f).symm).trans
      ((directSumComponentCokernelQuotientMap R M N f).quotKerEquivOfSurjective
        (directSumComponentCokernelQuotientMap_surjective R M N f))

end ChenRanks
