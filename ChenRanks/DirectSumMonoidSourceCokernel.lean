import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic

/-! The genuine direct-sum cokernel comparison requires additive groups
only on its targets. The sources retain the monoids already stored by
their actual maps. Every quotient is the native quotient by the actual
range; no comparison or range identity is an input. -/

noncomputable section

open scoped DirectSum

namespace ChenRanks

variable (R : Type*) [Ring R]
variable {ι : Type*} (M N : ι → Type*)
variable [∀ i, AddCommMonoid (M i)] [∀ i, AddCommGroup (N i)]
variable [∀ i, Module R (M i)] [∀ i, Module R (N i)]
variable (f : ∀ i, M i →ₗ[R] N i)

/-- The original direct sum of the actual quotient maps. -/
def directSumMonoidSourceCokernelQuotientMap :
    (⨁ i, N i) →ₗ[R] ⨁ i, (N i ⧸ LinearMap.range (f i)) :=
  DirectSum.lmap (fun i => (LinearMap.range (f i)).mkQ)

theorem directSumMonoidSourceCokernelQuotientMap_surjective :
    Function.Surjective (directSumMonoidSourceCokernelQuotientMap R M N f) := by
  exact (DirectSum.lmap_surjective
    (fun i => (LinearMap.range (f i)).mkQ)).mpr
      (fun i => (LinearMap.range (f i)).mkQ_surjective)

/-- The true kernel of this quotient map is the true degree-map range. -/
theorem directSumMonoidSourceCokernelQuotientMap_ker :
    LinearMap.ker (directSumMonoidSourceCokernelQuotientMap R M N f) =
      LinearMap.range (DirectSum.lmap f) := by
  unfold directSumMonoidSourceCokernelQuotientMap
  rw [DirectSum.ker_lmap, DirectSum.range_lmap]
  simp only [Submodule.ker_mkQ]

/-- Actual component cokernels reconstruct the actual whole cokernel. -/
def directSumMonoidSourceCokernelEquiv :
    ((⨁ i, N i) ⧸ LinearMap.range (DirectSum.lmap f)) ≃ₗ[R]
      ⨁ i, (N i ⧸ LinearMap.range (f i)) :=
  (Submodule.quotEquivOfEq
    (LinearMap.range (DirectSum.lmap f))
    (LinearMap.ker (directSumMonoidSourceCokernelQuotientMap R M N f))
    (directSumMonoidSourceCokernelQuotientMap_ker R M N f).symm).trans
      ((directSumMonoidSourceCokernelQuotientMap R M N f).quotKerEquivOfSurjective
        (directSumMonoidSourceCokernelQuotientMap_surjective R M N f))

end ChenRanks
