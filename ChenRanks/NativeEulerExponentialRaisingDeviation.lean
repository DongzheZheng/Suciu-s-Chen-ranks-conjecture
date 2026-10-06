import ChenRanks.NativeEulerExponentialGroup
import ChenRanks.NativeEulerExtensionRaisingFlag
import ChenRanks.NativeLieAutomorphismUnits

/-!
# Every actual Euler exponential has actual degree-one deviation

The actual native inner adjoint raises the actual Euler flag by one.
Actual powers genuinely raise by their power, and the actual restricted
rational finite exponential is a finite sum of those same operators.
Consequently every element of the already constructed actual exponential
subgroup has deviation in actual J_1. No positivity/deviation property
of the subgroup's elements is supplied as input.

The genuine quadratic remainder also belongs to actual J_2. This is the
operator identity later needed to identify true first leading classes;
it does not yet compute any geometric period or monodromy.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]
variable (hzero : ℒ 0 = ⊥) (c : ℕ) (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥)

omit [CharZero k] in
private theorem nativeEulerRaisingEnd_pow_mem
    (a : Module.End k (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ)))
    (ha : a ∈ degreeRaisingEndomorphisms k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) 1) (n : ℕ) :
    a ^ n ∈ degreeRaisingEndomorphisms k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) n := by
  induction n with
  | zero => simpa only [pow_zero] using one_mem_degreeRaisingEndomorphisms k _ _
  | succ n ih =>
    rw [pow_succ]
    exact mul_mem_degreeRaisingEndomorphisms k _ _ n 1 _ _ ih ha

private theorem rational_nativeEulerEnd_smul_eq
    (r : ℚ)
    (a : Module.End k (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))) :
    r • a = (algebraMap ℚ k r) • a := by
  apply LinearMap.ext
  intro p
  change (algebraMap ℚ k r) • a p = (algebraMap ℚ k r) • a p
  rfl

/-- Actual native finite exponentiation of an actual raising operator
has its actual deviation in the true first raising space. -/
theorem nativeEulerEnd_exp_sub_one_mem
    (a : Module.End k (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ)))
    (ha : a ∈ degreeRaisingEndomorphisms k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) 1) (hna : IsNilpotent a) :
    IsNilpotent.exp a - 1 ∈ degreeRaisingEndomorphisms k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) 1 := by
  obtain ⟨n, hn⟩ := hna
  have hn' : a ^ (n + 1) = 0 := by rw [pow_succ, hn, zero_mul]
  rw [IsNilpotent.exp_eq_sum hn', Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero,
    add_sub_cancel_right]
  apply Submodule.sum_mem
  intro m _hm
  rw [rational_nativeEulerEnd_smul_eq]
  apply Submodule.smul_mem
  exact degreeRaisingEndomorphisms_antitone k _ _
    (nativeEulerExtensionFlag_antitone k L ℒ) 1 (m + 1) (by omega)
    (nativeEulerRaisingEnd_pow_mem k L ℒ a ha (m + 1))

/-- The actual nonlinear operator exponential terms start in actual
raising degree two. -/
theorem nativeEulerEnd_exp_sub_one_sub_mem_two
    (a : Module.End k (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ)))
    (ha : a ∈ degreeRaisingEndomorphisms k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) 1) (hna : IsNilpotent a) :
    IsNilpotent.exp a - 1 - a ∈ degreeRaisingEndomorphisms k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) 2 := by
  obtain ⟨n, hn⟩ := hna
  have hn' : a ^ (n + 2) = 0 := by
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ, hn, zero_mul, zero_mul]
  rw [IsNilpotent.exp_eq_sum hn', Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.zero_add, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one,
    one_smul, pow_zero, pow_one, add_sub_cancel_right]
  apply Submodule.sum_mem
  intro m _hm
  rw [rational_nativeEulerEnd_smul_eq]
  apply Submodule.smul_mem
  exact degreeRaisingEndomorphisms_antitone k _ _
    (nativeEulerExtensionFlag_antitone k L ℒ) 2 ((m + 1) + 1) (by omega)
    (nativeEulerRaisingEnd_pow_mem k L ℒ a ha ((m + 1) + 1))

/-- The genuine unit representation of the actual native Lie
exponential is its same actual original operator exponential. -/
theorem nativeEulerExponentialUnitsEnd_eq_exp (x : L) :
    (nativeLieAutomorphismUnitsEnd k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativePositiveFiniteGradingExponential k L ℒ hzero c hbound
        (nativeEulerDerivation k L ℒ) x) :
      Module.End k (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))) =
      IsNilpotent.exp
        (nativeDerivationExtensionAdjoint k L (nativeEulerDerivation k L ℒ) x).toLinearMap := by
  apply LinearMap.ext
  intro p
  change nativeDerivationExtensionExponential k L (nativeEulerDerivation k L ℒ) x
    (nativeDerivationExtensionAdjoint_isNilpotent_of_positive_finite_grading
      k L ℒ hzero c hbound (nativeEulerDerivation k L ℒ) x) p = _
  exact nativeDerivationExtensionExponential_apply k L (nativeEulerDerivation k L ℒ) x _ p

/-- Every element of the genuine native exponential subgroup has its
actual unit representation's deviation in the actual constructed J_1. -/
theorem nativeEulerExponentialSubgroup_raising_deviation
    (T : nativeEulerExponentialSubgroup k L ℒ hzero c hbound) :
    (nativeLieAutomorphismUnitsEnd k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ)) T.val :
      Module.End k (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))) - 1 ∈
      degreeRaisingEndomorphisms k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
        (nativeEulerExtensionFlag k L ℒ) 1 := by
  obtain ⟨x, hx⟩ := T.property
  rw [← hx, nativeEulerExponentialUnitsEnd_eq_exp]
  exact nativeEulerEnd_exp_sub_one_mem k L ℒ
    (nativeDerivationExtensionAdjoint k L (nativeEulerDerivation k L ℒ) x).toLinearMap
    (nativeEulerExtensionAdjoint_mem_raisingEndomorphisms k L ℒ hzero x)
    (nativeDerivationExtensionAdjoint_isNilpotent_of_positive_finite_grading
      k L ℒ hzero c hbound (nativeEulerDerivation k L ℒ) x)

end ChenRanks.LieComparison
