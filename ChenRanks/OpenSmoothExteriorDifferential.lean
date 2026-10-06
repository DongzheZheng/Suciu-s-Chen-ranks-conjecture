import ChenRanks.OpenSmoothCommutingDerivations
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Actual coefficient differentiation with exterior generators

Coefficients are the actual smooth-function algebra on the actual open
set.  Constant exterior generators use the genuine native exterior
algebra.  Directional differentiation acts on coefficients, followed by
left exterior multiplication.  Actual commuting derivatives and the
native exterior anti-commutation law prove square zero on the literal
tensor product.  Neither of these laws is supplied as a hypothesis.
Identification with native smooth forms, the graded Leibniz law, and
de Rham or formality comparisons remain distinct obligations.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks.OpenSmoothExterior

open OpenSmoothFunctions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {κ : Type*} [Fintype κ]

local instance exteriorCoordinateDecidableEq : DecidableEq κ := Classical.decEq κ

abbrev ConstantExterior (κ : Type*) := ExteriorAlgebra ℂ (κ → ℂ)

abbrev CoefficientExterior (U : TopologicalSpace.Opens E) (κ : Type*) :=
  SmoothFunction U ⊗[ℂ] ConstantExterior κ

/-- The actual native exterior generator attached to a coordinate. -/
def generator (i : κ) : ConstantExterior κ :=
  ExteriorAlgebra.ι ℂ (Pi.single i 1)

/-- The actual coefficient derivative followed by actual left exterior
multiplication, with the same finite family of tangent vectors. -/
def differential (U : TopologicalSpace.Opens E) (v : κ → E) :
    CoefficientExterior U κ →ₗ[ℂ] CoefficientExterior U κ :=
  ∑ i : κ, TensorProduct.map (directionalLinearMap U (v i))
    ((LinearMap.mul ℂ (ConstantExterior κ)) (generator i))

theorem differential_tmul (U : TopologicalSpace.Opens E) (v : κ → E)
    (a : SmoothFunction U) (z : ConstantExterior κ) :
    differential U v (a ⊗ₜ[ℂ] z) =
      ∑ i : κ, directional U (v i) a ⊗ₜ[ℂ] (generator i * z) := by
  simp [differential, TensorProduct.map_tmul, LinearMap.mul]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- The cancellation used by square zero is a true pair of coefficient
derivatives and native exterior products. -/
theorem derivative_exterior_pair_cancels
    (U : TopologicalSpace.Opens E) (v : κ → E)
    (a : SmoothFunction U) (z : ConstantExterior κ) (i j : κ) :
    (directional U (v i) (directional U (v j) a) ⊗ₜ[ℂ]
        (generator i * (generator j * z))) +
      (directional U (v j) (directional U (v i) a) ⊗ₜ[ℂ]
        (generator j * (generator i * z))) = 0 := by
  rw [directional_commute U (v j) (v i) a]
  rw [← TensorProduct.tmul_add]
  have h : generator i * (generator j * z) +
      generator j * (generator i * z) = 0 := by
    rw [← mul_assoc, ← mul_assoc, ← add_mul]
    rw [generator, generator, ExteriorAlgebra.ι_add_mul_swap, zero_mul]
  rw [h, TensorProduct.tmul_zero]

/-- The literal differential squares to zero on actual pure tensors. -/
theorem differential_squared_tmul
    (U : TopologicalSpace.Opens E) (v : κ → E)
    (a : SmoothFunction U) (z : ConstantExterior κ) :
    differential U v (differential U v (a ⊗ₜ[ℂ] z)) = 0 := by
  classical
  rw [differential_tmul, map_sum]
  simp only [differential_tmul]
  let T : κ → κ → CoefficientExterior U κ := fun i j =>
    directional U (v i) (directional U (v j) a) ⊗ₜ[ℂ]
      (generator i * (generator j * z))
  have hp : ∀ i j, T i j + T j i = 0 :=
    derivative_exterior_pair_cancels U v a z
  have hs : (∑ i : κ, ∑ j : κ, (T i j + T j i)) = 0 := by
    simp only [hp, Finset.sum_const_zero]
  have hswap : (∑ i : κ, ∑ j : κ, T j i) = ∑ i : κ, ∑ j : κ, T i j :=
    Finset.sum_comm
  simp only [Finset.sum_add_distrib] at hs
  rw [hswap] at hs
  have htwo : (2 : ℂ) • (∑ i : κ, ∑ j : κ, T i j) = 0 := by
    simpa only [two_smul] using hs
  have hz : (∑ i : κ, ∑ j : κ, T i j) = 0 :=
    (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  change (∑ j : κ, ∑ i : κ, T i j) = 0
  rw [Finset.sum_comm]
  exact hz

/-- The actual operator satisfies the complex-linear square-zero law on
all coefficients, including an empty coordinate family. -/
theorem differential_comp_eq_zero
    (U : TopologicalSpace.Opens E) (v : κ → E) :
    (differential U v).comp (differential U v) = 0 := by
  apply TensorProduct.ext'
  intro a z
  change differential U v (differential U v (a ⊗ₜ[ℂ] z)) = 0
  exact differential_squared_tmul U v a z

end ChenRanks.OpenSmoothExterior
