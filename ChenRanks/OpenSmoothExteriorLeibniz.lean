import ChenRanks.OpenSmoothExteriorDifferential
import ChenRanks.ExteriorGeneratorHomogeneousSign
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The genuine graded Leibniz law for actual smooth coefficients

The ring is the literal tensor product of the actual smooth-function ring
and the native constant exterior algebra.  Its homogeneous submodules are
the actual images of tensoring with native exterior powers.  The sign is
derived from native exterior anti-commutation, and coefficient Leibniz is
derived from the already constructed actual directional derivations.
Neither graded Leibniz nor an expected grading decomposition is a premise.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks.OpenSmoothExterior

open OpenSmoothFunctions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {κ : Type*} [Fintype κ]

local instance leibnizSmoothCommRing (U : TopologicalSpace.Opens E) :
    CommRing (SmoothFunction U) := inferInstanceAs (CommRing ↥(algebra U))

local instance leibnizConstantExteriorRing : Ring (ConstantExterior κ) :=
  inferInstanceAs (Ring (ExteriorAlgebra ℂ (κ → ℂ)))

local instance leibnizCoefficientExteriorRing (U : TopologicalSpace.Opens E) :
    Ring (CoefficientExterior U κ) :=
  Algebra.TensorProduct.instRing (R := ℂ) (A := SmoothFunction U)
    (B := ConstantExterior κ)

/-- The actual map of a coefficient tensor with a native exterior power. -/
def homogeneousInclusion (U : TopologicalSpace.Opens E) (κ : Type*) (p : ℕ) :
    (SmoothFunction U ⊗[ℂ] (⋀[ℂ]^p (κ → ℂ))) →ₗ[ℂ] CoefficientExterior U κ :=
  TensorProduct.map (LinearMap.id : SmoothFunction U →ₗ[ℂ] SmoothFunction U)
    (⋀[ℂ]^p (κ → ℂ)).subtype

/-- Actual homogeneous elements, with no chosen decomposition premise. -/
def homogeneousSubmodule (U : TopologicalSpace.Opens E) (κ : Type*) (p : ℕ) :
    Submodule ℂ (CoefficientExterior U κ) :=
  LinearMap.range (homogeneousInclusion U κ p)

omit [Fintype κ] in
@[simp] theorem homogeneousInclusion_tmul
    (U : TopologicalSpace.Opens E) (p : ℕ)
    (a : SmoothFunction U) (u : ⋀[ℂ]^p (κ → ℂ)) :
    homogeneousInclusion U κ p (a ⊗ₜ[ℂ] u) = a ⊗ₜ[ℂ] u.val := by
  simp [homogeneousInclusion, TensorProduct.map_tmul]

/-- Genuine native exterior sign, with an arbitrary right factor. -/
theorem homogeneous_signed_generator_product
    (p : ℕ) (u : ConstantExterior κ) (hu : u ∈ ⋀[ℂ]^p (κ → ℂ))
    (i : κ) (z : ConstantExterior κ) :
    (-1 : ℂ) ^ p • (u * (generator i * z)) = generator i * (u * z) := by
  classical
  rw [← mul_assoc, ← smul_mul_assoc]
  change ((-1 : ℂ) ^ p • (u * ExteriorAlgebra.ι ℂ (Pi.single i 1))) * z =
    ExteriorAlgebra.ι ℂ (Pi.single i 1) * (u * z)
  rw [← exteriorGenerator_mul_homogeneous_sign ℂ (κ → ℂ)
    (Pi.single i 1) p u hu]
  exact mul_assoc _ _ _

/-- The actual graded Leibniz identity on original coefficient tensors. -/
theorem differential_tmul_mul_tmul
    (U : TopologicalSpace.Opens E) (v : κ → E) (p : ℕ)
    (a b : SmoothFunction U) (u z : ConstantExterior κ)
    (hu : u ∈ ⋀[ℂ]^p (κ → ℂ)) :
    differential U v ((a ⊗ₜ[ℂ] u) * (b ⊗ₜ[ℂ] z)) =
      differential U v (a ⊗ₜ[ℂ] u) * (b ⊗ₜ[ℂ] z) +
        (-1 : ℂ) ^ p • ((a ⊗ₜ[ℂ] u) * differential U v (b ⊗ₜ[ℂ] z)) := by
  classical
  rw [Algebra.TensorProduct.tmul_mul_tmul, differential_tmul,
    differential_tmul, differential_tmul, Finset.sum_mul,
    Finset.mul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hd : directional U (v i) (a * b) =
      a * directional U (v i) b + b * directional U (v i) a :=
    directionalLinearMap_leibniz U (v i) a b
  rw [hd, TensorProduct.add_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, ← TensorProduct.tmul_smul,
    homogeneous_signed_generator_product p u hu i z]
  rw [mul_comm b (directional U (v i) a), mul_assoc]
  exact add_comm _ _

/-- The same law for every actual homogeneous element and every actual
right factor.  Native tensor induction supplies all sums of tensors. -/
theorem differential_mul_of_mem_homogeneousSubmodule
    (U : TopologicalSpace.Opens E) (v : κ → E) (p : ℕ)
    (x y : CoefficientExterior U κ)
    (hx : x ∈ homogeneousSubmodule U κ p) :
    differential U v (x * y) = differential U v x * y +
      (-1 : ℂ) ^ p • (x * differential U v y) := by
  obtain ⟨w, rfl⟩ := hx
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a u =>
    rw [homogeneousInclusion_tmul]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b z => exact differential_tmul_mul_tmul U v p a b u.val z u.property
    | add y z hy hz =>
      simp only [mul_add, map_add, hy, hz, smul_add]
      abel
  | add w z hw hz =>
    simp only [map_add, add_mul, hw, hz, smul_add]
    abel

/-- Actual coefficient differentiation raises the native homogeneous
degree by one. -/
theorem differential_mem_homogeneousSubmodule
    (U : TopologicalSpace.Opens E) (v : κ → E) (p : ℕ)
    (x : CoefficientExterior U κ) (hx : x ∈ homogeneousSubmodule U κ p) :
    differential U v x ∈ homogeneousSubmodule U κ (p + 1) := by
  classical
  obtain ⟨w, rfl⟩ := hx
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | tmul a u =>
    rw [homogeneousInclusion_tmul, differential_tmul]
    apply Submodule.sum_mem
    intro i _
    have hi : generator i ∈ ⋀[ℂ]^1 (κ → ℂ) := by
      simpa only [generator, pow_one] using
        LinearMap.mem_range_self (ExteriorAlgebra.ι ℂ) (Pi.single i 1)
    have hprod : generator i * u.val ∈ ⋀[ℂ]^(p + 1) (κ → ℂ) := by
      simpa only [Nat.add_comm] using (SetLike.GradedMul.mul_mem hi u.property)
    refine ⟨directional U (v i) a ⊗ₜ[ℂ] ⟨generator i * u.val, hprod⟩, ?_⟩
    exact homogeneousInclusion_tmul U (p + 1) _ _
  | add w z hw hz =>
    simp only [map_add]
    exact Submodule.add_mem _ hw hz

end ChenRanks.OpenSmoothExterior
