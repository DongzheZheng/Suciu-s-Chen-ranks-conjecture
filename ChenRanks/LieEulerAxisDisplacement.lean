import ChenRanks.LiePositiveGradingEuler
import ChenRanks.LieGradedAffineAdjointNilpotence

/-!
# The actual finite Euler-axis displacement and its actual correction law

The finite polynomial is built from the actual native Euler derivation
and the actual Lie bracket. The graded-tail correction law is proved by
actual bracket induction. No inverse, surjectivity, automorphism
classification, or triangular correction property is supplied as input.
Identification with the actual native finite exponential and the actual
finite inverse construction are separate subsequent steps.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]

theorem nativeEulerDerivation_mem_tail (n : ℕ) (x : L)
    (hx : x ∈ nativeGradedTail k L ℒ n) :
    nativeEulerDerivation k L ℒ x ∈ nativeGradedTail k L ℒ n := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨i, hi, hai⟩ := ha
    rw [nativeEulerDerivation_of_mem k L ℒ i a hai]
    exact Submodule.smul_mem _ _ (mem_nativeGradedTail_of_mem k L ℒ n i a hi hai)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- The actual successive original Lie brackets appearing in exp(ad x) of the axis. -/
def nativeEulerAxisIterate (x : L) : ℕ → L
  | 0 => nativeEulerDerivation k L ℒ x
  | n + 1 => ⁅x, nativeEulerAxisIterate x n⁆

@[simp] theorem nativeEulerAxisIterate_zero (x : L) :
    nativeEulerAxisIterate k L ℒ x 0 = nativeEulerDerivation k L ℒ x := rfl

@[simp] theorem nativeEulerAxisIterate_succ (x : L) (n : ℕ) :
    nativeEulerAxisIterate k L ℒ x (n + 1) =
      ⁅x, nativeEulerAxisIterate k L ℒ x n⁆ := rfl

theorem nativeEulerAxisIterate_mem_tail (hzero : ℒ 0 = ⊥) (x : L) (n : ℕ) :
    nativeEulerAxisIterate k L ℒ x n ∈ nativeGradedTail k L ℒ (n + 1) := by
  induction n with
  | zero => rw [nativeGradedTail_one_eq_top k L ℒ hzero]; trivial
  | succ n ih =>
    rw [nativeEulerAxisIterate_succ]
    have hx : x ∈ nativeGradedTail k L ℒ 1 := by
      rw [nativeGradedTail_one_eq_top k L ℒ hzero]
      trivial
    simpa only [Nat.add_comm 1 (n + 1)] using
      lie_mem_nativeGradedTail k L ℒ 1 (n + 1) x _ hx ih

/-- The actual difference of successive bracket terms has the genuine
lowest-degree correction, derived from the actual native Euler map. -/
theorem nativeEulerAxisIterate_add_sub_mem_tail (hzero : ℒ 0 = ⊥)
    (x δ : L) (n m : ℕ) (hδ : δ ∈ nativeGradedTail k L ℒ n) :
    nativeEulerAxisIterate k L ℒ (x + δ) m - nativeEulerAxisIterate k L ℒ x m ∈
      nativeGradedTail k L ℒ (n + m) := by
  induction m with
  | zero =>
    simp only [nativeEulerAxisIterate_zero, map_add, add_sub_cancel_left, Nat.add_zero]
    exact nativeEulerDerivation_mem_tail k L ℒ n δ hδ
  | succ m ih =>
    rw [nativeEulerAxisIterate_succ, nativeEulerAxisIterate_succ]
    have heq : ⁅x + δ, nativeEulerAxisIterate k L ℒ (x + δ) m⁆ -
        ⁅x, nativeEulerAxisIterate k L ℒ x m⁆ =
        ⁅x, nativeEulerAxisIterate k L ℒ (x + δ) m -
          nativeEulerAxisIterate k L ℒ x m⁆ +
        ⁅δ, nativeEulerAxisIterate k L ℒ (x + δ) m⁆ := by
      rw [add_lie, lie_sub]
      abel
    rw [heq]
    have hx : x ∈ nativeGradedTail k L ℒ 1 := by
      rw [nativeGradedTail_one_eq_top k L ℒ hzero]
      trivial
    apply Submodule.add_mem
    · have h := lie_mem_nativeGradedTail k L ℒ 1 (n + m) x _ hx ih
      have hindex : 1 + (n + m) = n + (m + 1) := by omega
      rw [hindex] at h
      exact h
    · exact lie_mem_nativeGradedTail k L ℒ n (m + 1) δ _ hδ
        (nativeEulerAxisIterate_mem_tail k L ℒ hzero (x + δ) m)

/-- A genuine finite Lie polynomial, with the actual exponential coefficients. -/
def nativeEulerAxisDisplacement (c : ℕ) (x : L) : L :=
  ∑ n ∈ Finset.range (c + 1), ((n + 1).factorial : k)⁻¹ •
    nativeEulerAxisIterate k L ℒ x n

theorem nativeEulerAxisDisplacement_eq (c : ℕ) (x : L) :
    nativeEulerAxisDisplacement k L ℒ c x =
      (∑ n ∈ Finset.range c, ((n + 2).factorial : k)⁻¹ •
        nativeEulerAxisIterate k L ℒ x (n + 1)) + nativeEulerDerivation k L ℒ x := by
  unfold nativeEulerAxisDisplacement
  rw [Finset.sum_range_succ']
  simp only [Nat.add_assoc, Nat.zero_add, Nat.factorial_one, Nat.cast_one,
    inv_one, one_smul, nativeEulerAxisIterate_zero]

/-- The actual nonlinear correction is one degree higher than the
actual increment. Its proof does not assume a triangular-map interface. -/
theorem nativeEulerAxisDisplacement_add_correction_mem_tail
    (hzero : ℒ 0 = ⊥) (c n : ℕ) (x δ : L)
    (hδ : δ ∈ nativeGradedTail k L ℒ n) :
    nativeEulerAxisDisplacement k L ℒ c (x + δ) -
      nativeEulerAxisDisplacement k L ℒ c x - nativeEulerDerivation k L ℒ δ ∈
        nativeGradedTail k L ℒ (n + 1) := by
  have hsum :
      (∑ m ∈ Finset.range c, ((m + 2).factorial : k)⁻¹ •
        nativeEulerAxisIterate k L ℒ (x + δ) (m + 1)) -
      (∑ m ∈ Finset.range c, ((m + 2).factorial : k)⁻¹ •
        nativeEulerAxisIterate k L ℒ x (m + 1)) ∈
      nativeGradedTail k L ℒ (n + 1) := by
    rw [← Finset.sum_sub_distrib]
    apply Submodule.sum_mem
    intro m _
    rw [← smul_sub]
    apply Submodule.smul_mem
    apply nativeGradedTail_antitone k L ℒ (n + 1) (n + (m + 1)) (by omega)
    exact nativeEulerAxisIterate_add_sub_mem_tail k L ℒ hzero x δ n (m + 1) hδ
  rw [nativeEulerAxisDisplacement_eq, nativeEulerAxisDisplacement_eq, map_add]
  convert hsum using 1 <;> abel

end ChenRanks.LieComparison
