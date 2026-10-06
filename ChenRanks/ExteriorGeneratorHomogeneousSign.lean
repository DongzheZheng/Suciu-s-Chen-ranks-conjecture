import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Genuine homogeneous sign for a native exterior generator

Native exterior anti-commutation is iterated on genuine exterior products,
then extended to the actual exterior-power submodule by its proved
spanning theorem.  No graded commutation or homogeneous-detection premise
is supplied.  This is the sign identity needed for the actual smooth
coefficient differential's graded Leibniz rule.
-/

noncomputable section

namespace ChenRanks

variable (R : Type*) [CommRing R]
variable (M : Type*) [AddCommGroup M] [Module R M]

/-- A native exterior generator acquires the genuine sign on passing a
genuine `n`-fold native exterior product. -/
theorem exteriorGenerator_mul_iotaMulti_sign
    (m : M) (n : ℕ) (v : Fin n → M) :
    ExteriorAlgebra.ι R m * ExteriorAlgebra.ιMulti R n v =
      (-1 : R) ^ n •
        (ExteriorAlgebra.ιMulti R n v * ExteriorAlgebra.ι R m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hswap : ExteriorAlgebra.ι R m * ExteriorAlgebra.ι R (v 0) =
        -(ExteriorAlgebra.ι R (v 0) * ExteriorAlgebra.ι R m) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap m (v 0))
    rw [ExteriorAlgebra.ιMulti_succ_apply, ← mul_assoc, hswap, neg_mul,
      mul_assoc, ih (Matrix.vecTail v), mul_smul_comm]
    simp only [pow_succ, mul_neg_one, neg_smul, mul_assoc]

/-- The same identity for every actual element of the native homogeneous
submodule, derived from actual spanning rather than assumed. -/
theorem exteriorGenerator_mul_homogeneous_sign
    (m : M) (n : ℕ) (ω : ExteriorAlgebra R M)
    (hω : ω ∈ ⋀[R]^n M) :
    ExteriorAlgebra.ι R m * ω =
      (-1 : R) ^ n • (ω * ExteriorAlgebra.ι R m) := by
  let T : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
    LinearMap.mulLeft R (ExteriorAlgebra.ι R m) -
      (-1 : R) ^ n • LinearMap.mulRight R (ExteriorAlgebra.ι R m)
  have hspan : (⋀[R]^n M) ≤ LinearMap.ker T := by
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree R n]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    change ExteriorAlgebra.ι R m * ExteriorAlgebra.ιMulti R n v -
      (-1 : R) ^ n •
        (ExteriorAlgebra.ιMulti R n v * ExteriorAlgebra.ι R m) = 0
    exact sub_eq_zero.mpr (exteriorGenerator_mul_iotaMulti_sign R M m n v)
  have h := hspan hω
  change ExteriorAlgebra.ι R m * ω -
    (-1 : R) ^ n • (ω * ExteriorAlgebra.ι R m) = 0 at h
  exact sub_eq_zero.mp h

/-- The reverse sign identity is genuine too; the sign has square one in
the actual coefficient ring, including characteristic two. -/
theorem homogeneous_mul_exteriorGenerator_sign
    (m : M) (n : ℕ) (ω : ExteriorAlgebra R M)
    (hω : ω ∈ ⋀[R]^n M) :
    ω * ExteriorAlgebra.ι R m =
      (-1 : R) ^ n • (ExteriorAlgebra.ι R m * ω) := by
  rw [exteriorGenerator_mul_homogeneous_sign R M m n ω hω, smul_smul]
  have hs : (-1 : R) ^ n * (-1 : R) ^ n = 1 := by
    rw [← mul_pow, neg_mul_neg, one_mul, one_pow]
  rw [hs, one_smul]

end ChenRanks
