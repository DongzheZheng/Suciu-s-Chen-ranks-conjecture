import ChenRanks.LieEulerAxisDisplacement

/-!
# Native homogeneous projection and actual one-degree remainder

The projection is the native component of the actual direct-sum
decomposition. Its remainder lies in the next actual tail by span
induction. The inverse-weight Euler map preserves these actual tails.
No triangular remainder, projection, or inverse map is supplied as input.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]

/-- The actual degree-n component, included back into the original Lie algebra. -/
def nativeHomogeneousProjection (n : ℕ) : L →ₗ[k] L :=
  (ℒ n).subtype.comp ((DirectSum.component k ℕ (fun i => ℒ i) n).comp
    (DirectSum.decomposeLinearEquiv ℒ).toLinearMap)

@[simp] theorem nativeHomogeneousProjection_apply (n : ℕ) (x : L) :
    nativeHomogeneousProjection k L ℒ n x = (DirectSum.decompose ℒ x n : L) := rfl

theorem nativeHomogeneousProjection_mem (n : ℕ) (x : L) :
    nativeHomogeneousProjection k L ℒ n x ∈ ℒ n :=
  (DirectSum.decompose ℒ x n).property

theorem nativeHomogeneousProjection_of_mem_same (n : ℕ) (x : L) (hx : x ∈ ℒ n) :
    nativeHomogeneousProjection k L ℒ n x = x := by
  rw [nativeHomogeneousProjection_apply, DirectSum.decompose_of_mem_same ℒ hx]

theorem nativeHomogeneousProjection_of_mem_ne (n i : ℕ) (x : L)
    (hx : x ∈ ℒ i) (hin : i ≠ n) :
    nativeHomogeneousProjection k L ℒ n x = 0 := by
  rw [nativeHomogeneousProjection_apply, DirectSum.decompose_of_mem_ne ℒ hx hin]

/-- Removing the actual leading homogeneous component actually raises
the degree of the remainder. -/
theorem sub_nativeHomogeneousProjection_mem_next_tail (n : ℕ) (x : L)
    (hx : x ∈ nativeGradedTail k L ℒ n) :
    x - nativeHomogeneousProjection k L ℒ n x ∈ nativeGradedTail k L ℒ (n + 1) := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨i, hi, hai⟩ := ha
    by_cases hin : i = n
    · subst i
      rw [nativeHomogeneousProjection_of_mem_same k L ℒ n a hai, sub_self]
      exact Submodule.zero_mem _
    · rw [nativeHomogeneousProjection_of_mem_ne k L ℒ n i a hai hin, sub_zero]
      exact mem_nativeGradedTail_of_mem k L ℒ (n + 1) i a (by omega) hai
  | zero => rw [map_zero, sub_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    rw [map_add, add_sub_add_comm]
    exact Submodule.add_mem _ ha hb
  | smul a x _ hx =>
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ a hx

/-- The true inverse Euler weights preserve every actual graded tail. -/
theorem nativeEulerInverse_mem_tail (n : ℕ) (x : L)
    (hx : x ∈ nativeGradedTail k L ℒ n) :
    nativeEulerInverse k L ℒ x ∈ nativeGradedTail k L ℒ n := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨i, hi, hai⟩ := ha
    have heq := nativeEulerInverse_homogeneous k L ℒ i (⟨a, hai⟩ : ℒ i)
    rw [heq]
    exact Submodule.smul_mem _ _ (mem_nativeGradedTail_of_mem k L ℒ n i a hi hai)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

end ChenRanks.LieComparison
