import ChenRanks.LieGradedTailProjection

/-!
# A genuine finite inverse for the actual Euler-axis polynomial

The algorithm takes the actual leading homogeneous component of the
actual remaining error and divides by its nonzero degree. The proved
correction law raises the actual remaining error by one degree per step.
The actual finite degree bound makes the final error zero. Injectivity
follows by the same actual tails and the genuine inverse Euler operator.

No inverse, triangular-map axiom, automorphism bijection, or selected
model comparison is an input. This is a nonlinear set equivalence for
the actual finite Lie polynomial. The native-exponential and positive
automorphism identifications remain separate obligations.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]

/-- The correction uses the actual projection of the actual remaining error. -/
def nativeEulerAxisCorrection (c n : ℕ) (x v : L) : L :=
  (n : k)⁻¹ • nativeHomogeneousProjection k L ℒ n
    (v - nativeEulerAxisDisplacement k L ℒ c x)

theorem nativeEulerAxisCorrection_mem_homogeneous (c n : ℕ) (x v : L) :
    nativeEulerAxisCorrection k L ℒ c n x v ∈ ℒ n :=
  Submodule.smul_mem _ _ (nativeHomogeneousProjection_mem k L ℒ n _)

/-- Nonzero degree makes its actual Euler image exactly the actual leading error. -/
theorem nativeEulerAxisCorrection_euler (c n : ℕ) (x v : L) (hn : n ≠ 0) :
    nativeEulerDerivation k L ℒ (nativeEulerAxisCorrection k L ℒ c n x v) =
      nativeHomogeneousProjection k L ℒ n
        (v - nativeEulerAxisDisplacement k L ℒ c x) := by
  rw [nativeEulerDerivation_of_mem k L ℒ n _
    (nativeEulerAxisCorrection_mem_homogeneous k L ℒ c n x v)]
  change (n : k) • ((n : k)⁻¹ • nativeHomogeneousProjection k L ℒ n
    (v - nativeEulerAxisDisplacement k L ℒ c x)) = _
  rw [smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn), one_smul]

/-- The genuine correction removes the leading degree and raises the genuine residual. -/
theorem nativeEulerAxisCorrection_residual_mem_next_tail
    (hzero : ℒ 0 = ⊥) (c n : ℕ) (x v : L) (hn : n ≠ 0)
    (hres : v - nativeEulerAxisDisplacement k L ℒ c x ∈ nativeGradedTail k L ℒ n) :
    v - nativeEulerAxisDisplacement k L ℒ c
      (x + nativeEulerAxisCorrection k L ℒ c n x v) ∈ nativeGradedTail k L ℒ (n + 1) := by
  let δ := nativeEulerAxisCorrection k L ℒ c n x v
  have hδ : δ ∈ nativeGradedTail k L ℒ n :=
    mem_nativeGradedTail_of_mem k L ℒ n n δ le_rfl
      (nativeEulerAxisCorrection_mem_homogeneous k L ℒ c n x v)
  have herr := nativeEulerAxisDisplacement_add_correction_mem_tail
    k L ℒ hzero c n x δ hδ
  have hrem := sub_nativeHomogeneousProjection_mem_next_tail k L ℒ n
    (v - nativeEulerAxisDisplacement k L ℒ c x) hres
  have hDδ := nativeEulerAxisCorrection_euler k L ℒ c n x v hn
  have h := Submodule.sub_mem (nativeGradedTail k L ℒ (n + 1)) hrem herr
  convert h using 1
  rw [hDδ]
  abel

/-- The finite algorithm starts at zero and corrects genuine degrees 1,2,... . -/
def nativeEulerAxisInverseStage (c : ℕ) (v : L) : ℕ → L
  | 0 => 0
  | n + 1 =>
    let x := nativeEulerAxisInverseStage c v n
    x + nativeEulerAxisCorrection k L ℒ c (n + 1) x v

/-- Its actual residual moves up one genuine degree at every actual step. -/
theorem nativeEulerAxisInverseStage_residual_mem_tail
    (hzero : ℒ 0 = ⊥) (c : ℕ) (v : L) (n : ℕ) :
    v - nativeEulerAxisDisplacement k L ℒ c
      (nativeEulerAxisInverseStage k L ℒ c v n) ∈ nativeGradedTail k L ℒ (n + 1) := by
  induction n with
  | zero => rw [nativeGradedTail_one_eq_top k L ℒ hzero]; trivial
  | succ n ih =>
    exact nativeEulerAxisCorrection_residual_mem_next_tail k L ℒ hzero c (n + 1)
      (nativeEulerAxisInverseStage k L ℒ c v n) v (Nat.succ_ne_zero n) ih

/-- The actual finite degree bound makes the constructed inverse exact. -/
theorem nativeEulerAxisDisplacement_inverseStage
    (hzero : ℒ 0 = ⊥) (c : ℕ) (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥) (v : L) :
    nativeEulerAxisDisplacement k L ℒ c (nativeEulerAxisInverseStage k L ℒ c v c) = v := by
  have h := nativeEulerAxisInverseStage_residual_mem_tail k L ℒ hzero c v c
  rw [nativeGradedTail_eq_bot_of_bound k L ℒ c (c + 1) hbound (Nat.lt_succ_self c)] at h
  exact (sub_eq_zero.mp h).symm

/-- Equality of genuine displacements forces equality, by actual degree induction. -/
theorem nativeEulerAxisDisplacement_injective
    (hzero : ℒ 0 = ⊥) (c : ℕ) (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥) :
    Function.Injective (nativeEulerAxisDisplacement k L ℒ c) := by
  intro x y hxy
  have htail : ∀ n : ℕ, x - y ∈ nativeGradedTail k L ℒ (n + 1) := by
    intro n
    induction n with
    | zero => rw [nativeGradedTail_one_eq_top k L ℒ hzero]; trivial
    | succ n ih =>
      have herr := nativeEulerAxisDisplacement_add_correction_mem_tail
        k L ℒ hzero c (n + 1) y (x - y) ih
      rw [show y + (x - y) = x by abel, hxy, sub_self, zero_sub] at herr
      have hD : nativeEulerDerivation k L ℒ (x - y) ∈ nativeGradedTail k L ℒ (n + 1 + 1) := by
        simpa only [neg_neg] using (nativeGradedTail k L ℒ (n + 1 + 1)).neg_mem herr
      have h := nativeEulerInverse_mem_tail k L ℒ (n + 1 + 1) _ hD
      have hleft := congrArg (fun f : L →ₗ[k] L => f (x - y))
        (nativeEulerInverse_comp_euler k L ℒ hzero)
      change nativeEulerInverse k L ℒ (nativeEulerDerivation k L ℒ (x - y)) = x - y at hleft
      rw [hleft] at h
      exact h
  have h := htail c
  rw [nativeGradedTail_eq_bot_of_bound k L ℒ c (c + 1) hbound (Nat.lt_succ_self c)] at h
  exact sub_eq_zero.mp h

/-- The actual polynomial has a genuine, explicitly constructed inverse.
This is not a supplied positive-automorphism or monodromy classification. -/
def nativeEulerAxisDisplacementEquiv
    (hzero : ℒ 0 = ⊥) (c : ℕ) (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥) : L ≃ L where
  toFun := nativeEulerAxisDisplacement k L ℒ c
  invFun v := nativeEulerAxisInverseStage k L ℒ c v c
  left_inv x := by
    apply nativeEulerAxisDisplacement_injective k L ℒ hzero c hbound
    exact nativeEulerAxisDisplacement_inverseStage k L ℒ hzero c hbound _
  right_inv v := nativeEulerAxisDisplacement_inverseStage k L ℒ hzero c hbound v

end ChenRanks.LieComparison
