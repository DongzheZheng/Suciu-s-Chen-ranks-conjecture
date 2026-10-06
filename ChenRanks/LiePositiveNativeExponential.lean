import ChenRanks.LieGradedNativeExtensionExp

/-!
# Actual finite exponentials preserve the scalar quotient and raise tails

The operator is the original affine adjoint, and its exponential is the
native finite exponential. Its first coordinate and its action on every
original tail follow by induction on its genuine powers. In particular,
neither filtration preservation nor positive-unipotent action is supplied
as an input. These are intermediate theorems for actual positive finite
gradings; the grading of the original holonomy truncation is still a
separate construction.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]

theorem derivationAffineAdjointEnd_pow_original_fst_eq_zero
    (D : LieDerivation k L L) (x w : L) (m : ℕ) :
    (((derivationAffineAdjointEnd k L D x) ^ m) (0, w)).1 = 0 := by
  cases m with
  | zero => rfl
  | succ m => exact derivationAffineAdjointEnd_pow_succ_fst_eq_zero k L D x m (0, w)

/-- Genuine powers move an original tail through genuine higher tails. -/
theorem derivationAffineAdjointEnd_pow_original_snd_mem
    (hzero : ℒ 0 = ⊥) (D : LieDerivation k L L) (x w : L)
    (n m : ℕ) (hw : w ∈ nativeGradedTail k L ℒ n) :
    (((derivationAffineAdjointEnd k L D x) ^ m) (0, w)).2 ∈
      nativeGradedTail k L ℒ (n + m) := by
  induction m with
  | zero => simpa only [pow_zero, Module.End.one_apply, Nat.add_zero] using hw
  | succ m ih =>
    rw [pow_succ']
    change (((derivationAffineAdjointEnd k L D x) ^ m) (0, w)).1 • D x +
      ⁅x, (((derivationAffineAdjointEnd k L D x) ^ m) (0, w)).2⁆ ∈ _
    rw [derivationAffineAdjointEnd_pow_original_fst_eq_zero, zero_smul, zero_add]
    have hx : x ∈ nativeGradedTail k L ℒ 1 := by
      rw [nativeGradedTail_one_eq_top k L ℒ hzero]
      trivial
    have h := lie_mem_nativeGradedTail k L ℒ 1 (n + m) x _ hx ih
    have hindex : 1 + (n + m) = n + (m + 1) := by omega
    rw [hindex] at h
    exact h

private theorem rational_end_smul_apply_fst
    (q : ℚ) (f : Module.End k (k × L)) (p : k × L) :
    ((q • f) p).1 = (algebraMap ℚ k q) * (f p).1 := by
  change ((algebraMap ℚ k q) • f p).1 = _
  rfl

private theorem rational_end_smul_apply_snd
    (q : ℚ) (f : Module.End k (k × L)) (p : k × L) :
    ((q • f) p).2 = (algebraMap ℚ k q) • (f p).2 := by
  change ((algebraMap ℚ k q) • f p).2 = _
  rfl

private theorem end_sum_apply_fst {α : Type*}
    (s : Finset α) (f : α → Module.End k (k × L)) (p : k × L) :
    ((∑ i ∈ s, f i) p).1 = ∑ i ∈ s, (f i p).1 := by
  change (LinearMap.fst k k L) ((∑ i ∈ s, f i) p) = _
  rw [LinearMap.sum_apply, map_sum]
  rfl

private theorem end_sum_apply_snd {α : Type*}
    (s : Finset α) (f : α → Module.End k (k × L)) (p : k × L) :
    ((∑ i ∈ s, f i) p).2 = ∑ i ∈ s, (f i p).2 := by
  change (LinearMap.snd k k L) ((∑ i ∈ s, f i) p) = _
  rw [LinearMap.sum_apply, map_sum]
  rfl

/-- The actual native finite exponential induces the identity on the
actual one-dimensional scalar quotient. -/
theorem derivationAffineExponential_fst
    (hzero : ℒ 0 = ⊥) (c : ℕ) (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥)
    (D : LieDerivation k L L) (x : L) (p : k × L) :
    (IsNilpotent.exp (derivationAffineAdjointEnd k L D x) p).1 = p.1 := by
  have hz : (derivationAffineAdjointEnd k L D x) ^ (c + 1) = 0 := by
    apply LinearMap.ext
    intro q
    apply Prod.ext
    · exact derivationAffineAdjointEnd_pow_succ_fst_eq_zero k L D x c q
    · have h := derivationAffineAdjointEnd_pow_succ_snd_mem k L ℒ hzero D x c q
      rw [nativeGradedTail_eq_bot_of_bound k L ℒ c (c + 1) hbound
        (Nat.lt_succ_self c)] at h
      exact h
  rw [IsNilpotent.exp_eq_sum hz, end_sum_apply_fst, Finset.sum_range_succ']
  have htail : (∑ n ∈ Finset.range c,
      (((((n + 1).factorial : ℚ)⁻¹) •
        (derivationAffineAdjointEnd k L D x) ^ (n + 1)) p).1) = 0 := by
    apply Finset.sum_eq_zero
    intro n _
    rw [rational_end_smul_apply_fst,
      derivationAffineAdjointEnd_pow_succ_fst_eq_zero, mul_zero]
  rw [htail]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero,
    Module.End.one_apply, zero_add]

/-- Its original-vector displacement raises every actual tail by one. -/
theorem derivationAffineExponential_original_snd_sub_mem
    (hzero : ℒ 0 = ⊥) (c : ℕ) (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥)
    (D : LieDerivation k L L) (x w : L) (n : ℕ)
    (hw : w ∈ nativeGradedTail k L ℒ n) :
    (IsNilpotent.exp (derivationAffineAdjointEnd k L D x) (0, w)).2 - w ∈
      nativeGradedTail k L ℒ (n + 1) := by
  have hz : (derivationAffineAdjointEnd k L D x) ^ (c + 1) = 0 := by
    apply LinearMap.ext
    intro q
    apply Prod.ext
    · exact derivationAffineAdjointEnd_pow_succ_fst_eq_zero k L D x c q
    · have h := derivationAffineAdjointEnd_pow_succ_snd_mem k L ℒ hzero D x c q
      rw [nativeGradedTail_eq_bot_of_bound k L ℒ c (c + 1) hbound
        (Nat.lt_succ_self c)] at h
      exact h
  rw [IsNilpotent.exp_eq_sum hz, end_sum_apply_snd, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero,
    Module.End.one_apply, add_sub_cancel_right]
  apply Submodule.sum_mem
  intro m _
  rw [rational_end_smul_apply_snd]
  apply Submodule.smul_mem
  exact nativeGradedTail_antitone k L ℒ (n + 1) (n + (m + 1)) (by omega)
    (derivationAffineAdjointEnd_pow_original_snd_mem k L ℒ hzero D x w n (m + 1) hw)

/-- The actual native exponential on the actual extension has the same
proved scalar-quotient action. -/
theorem nativePositiveFiniteGradingExponential_coordinates_fst
    (hzero : ℒ 0 = ⊥) (c : ℕ) (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥)
    (D : LieDerivation k L L) (x : L) (p : NativeDerivationExtension k L D) :
    (nativeDerivationExtensionCoordinates k L D
      (nativePositiveFiniteGradingExponential k L ℒ hzero c hbound D x p)).1 = p.right := by
  unfold nativePositiveFiniteGradingExponential
  rw [nativeDerivationExtensionExponential_coordinates,
    nativeDerivationExtensionAdjointCoordinateEnd_eq_affine]
  exact derivationAffineExponential_fst k L ℒ hzero c hbound D x _

/-- The actual native exponential raises actual original tails. -/
theorem nativePositiveFiniteGradingExponential_original_snd_sub_mem
    (hzero : ℒ 0 = ⊥) (c : ℕ) (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥)
    (D : LieDerivation k L L) (x w : L) (n : ℕ)
    (hw : w ∈ nativeGradedTail k L ℒ n) :
    (nativeDerivationExtensionCoordinates k L D
      (nativePositiveFiniteGradingExponential k L ℒ hzero c hbound D x
        (nativeDerivationExtensionOriginal k L D w))).2 - w ∈
      nativeGradedTail k L ℒ (n + 1) := by
  unfold nativePositiveFiniteGradingExponential
  rw [nativeDerivationExtensionExponential_coordinates,
    nativeDerivationExtensionAdjointCoordinateEnd_eq_affine]
  exact derivationAffineExponential_original_snd_sub_mem k L ℒ hzero c hbound D x w n hw

end ChenRanks.LieComparison
