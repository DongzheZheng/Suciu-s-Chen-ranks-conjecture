import ChenRanks.LieGradedTailProjection

/-!
# Genuine native Euler eigenspaces and the actual next-degree tail

Actual native projections commute with the actual native Euler derivation
by checking the actual homogeneous decomposition. Distinct characteristic-
zero weights force off-degree components to vanish. These results use no
finite-dimensionality, finite degree bound, diagonalization, or eigenspace
decomposition premise beyond the actual native grading.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]

theorem nativeHomogeneousProjection_comp_euler (n : ℕ) :
    (nativeHomogeneousProjection k L ℒ n).comp (nativeEulerDerivation k L ℒ).toLinearMap =
      (n : k) • nativeHomogeneousProjection k L ℒ n := by
  apply DirectSum.decompose_lhom_ext ℒ
  intro i
  apply LinearMap.ext
  intro a
  change nativeHomogeneousProjection k L ℒ n (nativeEulerDerivation k L ℒ a) =
    (n : k) • nativeHomogeneousProjection k L ℒ n a
  rw [nativeEulerDerivation_of_mem k L ℒ i a a.property, map_smul]
  by_cases hin : i = n
  · subst i
    rfl
  · rw [nativeHomogeneousProjection_of_mem_ne k L ℒ n i a a.property hin,
      smul_zero, smul_zero]

theorem nativeHomogeneousProjection_euler (n : ℕ) (x : L) :
    nativeHomogeneousProjection k L ℒ n (nativeEulerDerivation k L ℒ x) =
      (n : k) • nativeHomogeneousProjection k L ℒ n x :=
  congrArg (fun f : L →ₗ[k] L => f x) (nativeHomogeneousProjection_comp_euler k L ℒ n)

/-- A component below an actual tail is actually zero. -/
theorem nativeHomogeneousProjection_eq_zero_of_mem_tail (n m : ℕ) (x : L)
    (hnm : n < m) (hx : x ∈ nativeGradedTail k L ℒ m) :
    nativeHomogeneousProjection k L ℒ n x = 0 := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨i, hi, hai⟩ := ha
    exact nativeHomogeneousProjection_of_mem_ne k L ℒ n i a hai (by omega)
  | zero => exact map_zero _
  | add a b _ _ ha hb => rw [map_add, ha, hb, zero_add]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]

/-- The actual Euler's degree-n eigenvectors are genuinely homogeneous. -/
theorem nativeEuler_eigenvector_mem_homogeneous (n : ℕ) (x : L)
    (hx : nativeEulerDerivation k L ℒ x = (n : k) • x) : x ∈ ℒ n := by
  have hOff (m : ℕ) (hmn : m ≠ n) : nativeHomogeneousProjection k L ℒ m x = 0 := by
    have h := congrArg (nativeHomogeneousProjection k L ℒ m) hx
    rw [nativeHomogeneousProjection_euler, map_smul] at h
    have hscalar : ((m : k) - (n : k)) • nativeHomogeneousProjection k L ℒ m x = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr h
    exact (smul_eq_zero.mp hscalar).resolve_left
      (sub_ne_zero.mpr (Nat.cast_injective.ne hmn))
  have hEq : x = nativeHomogeneousProjection k L ℒ n x := by
    apply (DirectSum.decomposeLinearEquiv ℒ).injective
    apply DirectSum.ext
    intro m
    apply Subtype.ext
    change nativeHomogeneousProjection k L ℒ m x =
      nativeHomogeneousProjection k L ℒ m (nativeHomogeneousProjection k L ℒ n x)
    by_cases hmn : m = n
    · subst m
      rw [nativeHomogeneousProjection_of_mem_same k L ℒ n _
        (nativeHomogeneousProjection_mem k L ℒ n x)]
    · rw [hOff m hmn, nativeHomogeneousProjection_of_mem_ne k L ℒ m n _
        (nativeHomogeneousProjection_mem k L ℒ n x) (Ne.symm hmn)]
  rw [hEq]
  exact nativeHomogeneousProjection_mem k L ℒ n x

/-- A genuine degree-n vector in the actual next tail vanishes. -/
theorem eq_zero_of_homogeneous_mem_next_tail (n : ℕ) (x : L)
    (hhom : x ∈ ℒ n) (htail : x ∈ nativeGradedTail k L ℒ (n + 1)) : x = 0 := by
  have h := nativeHomogeneousProjection_eq_zero_of_mem_tail
    k L ℒ n (n + 1) x (Nat.lt_succ_self n) htail
  rw [nativeHomogeneousProjection_of_mem_same k L ℒ n x hhom] at h
  exact h

end ChenRanks.LieComparison
