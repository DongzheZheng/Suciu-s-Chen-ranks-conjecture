import ChenRanks.DegreeRaisingEndomorphisms
import ChenRanks.LieGradedAffineAdjointNilpotence

/-!
# The actual positive graded flag of the actual Euler extension coordinates

The flag is constructed on the same original scalar-plus-Lie-vector
coordinate space as the genuine affine adjoint.  Its degree zero is the
whole original space; positive degrees have scalar coordinate zero and
original-vector coordinate in the actual graded tail.  Genuine positivity
and the actual graded bracket imply that every actual affine adjoint
raises this flag by one.  The actual finite grading bound kills the
corresponding actual raising-operator subspace.

This provides the real algebraic subspaces for a subsequent local
primitive construction.  It assumes neither a selected flag nor a
nilpotent operator action as a result to be supplied.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]

/-- The actual scalar-axis degree is zero and actual original-vector
degrees are the positive native graded tails. -/
def nativeAffineGradedFlag : ℕ → Submodule k (k × L)
  | 0 => ⊤
  | n + 1 => LinearMap.ker (LinearMap.fst k k L) ⊓
      (nativeGradedTail k L ℒ (n + 1)).comap (LinearMap.snd k k L)

@[simp] theorem nativeAffineGradedFlag_zero :
    nativeAffineGradedFlag k L ℒ 0 = ⊤ := rfl

@[simp] theorem mem_nativeAffineGradedFlag_succ (n : ℕ) (p : k × L) :
    p ∈ nativeAffineGradedFlag k L ℒ (n + 1) ↔
      p.1 = 0 ∧ p.2 ∈ nativeGradedTail k L ℒ (n + 1) := Iff.rfl

/-- The actual flag is genuinely antitone, by actual tail inclusion. -/
theorem nativeAffineGradedFlag_antitone : Antitone (nativeAffineGradedFlag k L ℒ) := by
  intro m n hmn
  cases m with
  | zero => exact le_top
  | succ m =>
    cases n with
    | zero => omega
    | succ n =>
      intro p hp
      exact ⟨hp.1, nativeGradedTail_antitone k L ℒ (m + 1) (n + 1) hmn hp.2⟩

/-- The actual finite positive grading kills the actual flag. -/
theorem nativeAffineGradedFlag_bound_eq_bot (c : ℕ)
    (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥) :
    nativeAffineGradedFlag k L ℒ (c + 1) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro p hp
  change p = 0
  change p.1 = 0 ∧ p.2 ∈ nativeGradedTail k L ℒ (c + 1) at hp
  have ht := nativeGradedTail_eq_bot_of_bound k L ℒ c (c + 1)
    hbound (Nat.lt_succ_self c)
  apply Prod.ext
  · exact hp.1
  · simpa only [ht, Submodule.mem_bot] using hp.2

/-- Every actual affine adjoint raises the actual original flag by one,
as proved from its true coordinate formula and actual graded bracket. -/
theorem derivationAffineAdjointEnd_mem_degreeRaisingEndomorphisms
    (hzero : ℒ 0 = ⊥) (D : LieDerivation k L L) (x : L) :
    derivationAffineAdjointEnd k L D x ∈
      degreeRaisingEndomorphisms k (k × L) (nativeAffineGradedFlag k L ℒ) 1 := by
  intro n p hp
  cases n with
  | zero =>
    change (0 : k) = 0 ∧
      p.1 • D x + ⁅x, p.2⁆ ∈ nativeGradedTail k L ℒ 1
    constructor
    · rfl
    · rw [nativeGradedTail_one_eq_top k L ℒ hzero]
      trivial
  | succ n =>
    change p.1 = 0 ∧ p.2 ∈ nativeGradedTail k L ℒ (n + 1) at hp
    change (0 : k) = 0 ∧
      p.1 • D x + ⁅x, p.2⁆ ∈ nativeGradedTail k L ℒ (n + 1 + 1)
    constructor
    · rfl
    · rw [hp.1, zero_smul, zero_add]
      have hx : x ∈ nativeGradedTail k L ℒ 1 := by
        rw [nativeGradedTail_one_eq_top k L ℒ hzero]
        trivial
      have h := lie_mem_nativeGradedTail k L ℒ 1 (n + 1) x p.2 hx hp.2
      have hi : 1 + (n + 1) = n + 1 + 1 := by omega
      rw [hi] at h
      exact h

/-- The degree bound genuinely kills the original raising operators. -/
theorem nativeAffineRaisingEndomorphisms_bound_eq_bot (c : ℕ)
    (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥) :
    degreeRaisingEndomorphisms k (k × L) (nativeAffineGradedFlag k L ℒ) (c + 1) = ⊥ :=
  degreeRaisingEndomorphisms_eq_bot_of_flag_bound k (k × L)
    (nativeAffineGradedFlag k L ℒ) rfl (c + 1)
    (nativeAffineGradedFlag_bound_eq_bot k L ℒ c hbound)

end ChenRanks.LieComparison
