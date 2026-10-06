import ChenRanks.ArrangementFiniteEulerExponentialFrames

/-!
# The actual inverse derivative and the actual subgroup frame normalization

The same original finite polynomial inverse has its proved infinite
smoothness and its genuine inverse-times-coefficient derivative. The
original exponential frame's inverse is exactly this original inverse,
and its actual anchor is the group identity. These are actual consequences
of the constructed original parallel sum and inverse, not selected
transition or inverse-derivative data.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

open LieComparison OpenSmoothForms

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι) (c : ℕ)

local instance inverseEulerNormedAddCommGroup :
    NormedAddCommGroup (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedAddCommGroup ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance inverseEulerNormedSpace :
    NormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance inverseEulerRealNormedSpace :
    NormedSpace ℝ (A.ActualFiniteLogarithmicEulerSpace c) :=
  NormedSpace.restrictScalars ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance inverseEulerCompleteSpace :
    CompleteSpace (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFinite_completeSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance inverseEulerScalarTower :
    IsScalarTower ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c) where
  smul_assoc r a p := by
    change ((r : ℂ) * a) • p = (r : ℂ) • (a • p)
    exact mul_smul _ _ _
local instance inverseEulerSMulCommClass :
    SMulCommClass ℂ ℝ (A.ActualFiniteLogarithmicEulerSpace c) where
  smul_comm a r p := by
    change a • ((r : ℂ) • p) = (r : ℂ) • (a • p)
    exact smul_comm _ _ _
local instance inverseEulerEndRealNormedAlgebra :
    NormedAlgebra ℝ (A.ActualFiniteLogarithmicEulerCoefficients c) :=
  NormedAlgebra.restrictScalars ℝ ℂ (A.ActualFiniteLogarithmicEulerCoefficients c)
local instance inverseEulerEndRealFiniteDimensional :
    FiniteDimensional ℝ (A.ActualFiniteLogarithmicEulerCoefficients c) := by
  letI : FiniteDimensional ℝ ℂ := Complex.basisOneI.finiteDimensional_of_finite
  exact FiniteDimensional.trans ℝ ℂ (A.ActualFiniteLogarithmicEulerCoefficients c)

variable (s : Set (Fin d → ℂ)) (hs : Convex ℝ s) (hso : IsOpen s)
variable (hscomp : s ⊆ A.ambientComplementSet) (x₀ : Fin d → ℂ)

/-- The actual original finite polynomial inverse is infinitely smooth. -/
theorem actualFiniteEulerParallelInverse_smooth :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (A.actualFiniteEulerParallelInverse c s hs hso hscomp x₀) s :=
  actualFiniteFlatParallelInverseFunction_smooth s hs hso _ _ _ _ _ _ _ _ x₀ c

/-- Its actual real derivative is exactly minus inverse times the
actual original logarithmic coefficient form. -/
theorem actualFiniteEulerParallelInverse_derivative
    (x : Fin d → ℂ) (hx : x ∈ s) :
    HasFDerivAt (A.actualFiniteEulerParallelInverse c s hs hso hscomp x₀)
      (-((ContinuousLinearMap.mul ℝ (A.ActualFiniteLogarithmicEulerCoefficients c))
        (A.actualFiniteEulerParallelInverse c s hs hso hscomp x₀ x)).comp
          (A.actualFiniteEulerLogarithmicOneForm c x)) x :=
  actualFiniteFlatParallelInverseFunction_derivative s hs hso _ _ _ _ _ _ _ _ x₀
    (A.actualFiniteEulerCoefficientFlag_antitone c) c
    (A.actualFiniteEulerCoefficientFlag_bound c) x hx

/-- The inverse of the specific actual subgroup-valued frame is
represented by the same original constructed polynomial inverse. -/
theorem actualFiniteEulerExponentialFrameInverseEnd_eq_parallelInverse
    (hx₀ : x₀ ∈ s) (x : s) :
    A.actualFiniteEulerExponentialEnd c
      ((A.actualFiniteEulerExponentialFrame c s hs hso hscomp x₀ hx₀ x)⁻¹) =
      A.actualFiniteEulerParallelInverse c s hs hso hscomp x₀ x.val := by
  apply ContinuousLinearMap.ext
  intro p
  rfl

/-- The actual original anchored subgroup frame is the group identity. -/
theorem actualFiniteEulerExponentialFrame_anchor (hx₀ : x₀ ∈ s) :
    A.actualFiniteEulerExponentialFrame c s hs hso hscomp x₀ hx₀ ⟨x₀, hx₀⟩ = 1 := by
  apply A.actualFiniteEulerExponentialEnd_injective c
  rw [actualFiniteEulerExponentialFrameEnd_eq_parallel,
    actualFiniteEulerParallelFunction_anchor, map_one]

end ChenRanks.AffineArrangement
