import ChenRanks.ArrangementFiniteEulerLogarithmicRegularity
import ChenRanks.OpenSmoothComplexFlatParallelLie

/-!
# Actual local parallel frames on original convex complement neighborhoods

The input neighborhood is an actual open convex ambient set contained in
the actual original complement, with an actual anchor in that set. Every
coefficient, smoothness proof, closedness proof, commutation proof,
raising space, multiplication law and finite bound is derived from the
original arrangement and its actual native finite Euler model.

The proved original Poincare recursion constructs the actual finite
parallel sum and the explicit finite polynomial inverse. Its actual
bracket defect vanishes by the proved native uniqueness theorem, giving
an actual original complex Lie equivalence. The actual degree-one
deviation follows from the primitive value constraints, and the native
Euler classification applies to that actual constructed equivalence.
No local frames, flatness, automorphism, positivity or monodromy is given
as an input. A final native covering factory will choose the actual
complement neighborhoods and glue these genuinely constructed frames.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

open LieComparison OpenSmoothForms

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι) (c : ℕ)

local instance finiteFrameNormedAddCommGroup :
    NormedAddCommGroup (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedAddCommGroup ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance finiteFrameNormedSpace :
    NormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance finiteFrameRealNormedSpace :
    NormedSpace ℝ (A.ActualFiniteLogarithmicEulerSpace c) :=
  NormedSpace.restrictScalars ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance finiteFrameCompleteSpace : CompleteSpace (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFinite_completeSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance finiteFrameScalarTower : IsScalarTower ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c) where
  smul_assoc r a x := by
    change ((r : ℂ) * a) • x = (r : ℂ) • (a • x)
    exact mul_smul _ _ _
local instance finiteFrameSMulCommClass : SMulCommClass ℂ ℝ (A.ActualFiniteLogarithmicEulerSpace c) where
  smul_comm a r x := by
    change a • ((r : ℂ) • x) = (r : ℂ) • (a • x)
    exact smul_comm _ _ _
local instance finiteFrameEndRealNormedAlgebra :
    NormedAlgebra ℝ (A.ActualFiniteLogarithmicEulerCoefficients c) :=
  NormedAlgebra.restrictScalars ℝ ℂ (A.ActualFiniteLogarithmicEulerCoefficients c)
local instance finiteFrameEndRealFiniteDimensional :
    FiniteDimensional ℝ (A.ActualFiniteLogarithmicEulerCoefficients c) := by
  letI : FiniteDimensional ℝ ℂ := Complex.basisOneI.finiteDimensional_of_finite
  exact FiniteDimensional.trans ℝ ℂ (A.ActualFiniteLogarithmicEulerCoefficients c)

/-- The actual real coefficient spaces, using the same actual original
complex-linear operators and the same actual native Euler flag. -/
def actualFiniteEulerCoefficientFlag (n : ℕ) :
    Submodule ℝ (A.ActualFiniteLogarithmicEulerCoefficients c) :=
  realContinuousDegreeRaisingEndomorphisms (A.ActualFiniteLogarithmicEulerSpace c)
    (nativeEulerExtensionFlag ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c)) n

theorem actualFiniteEulerCoefficientFlag_mul (a b : ℕ)
    (f g : A.ActualFiniteLogarithmicEulerCoefficients c)
    (hf : f ∈ A.actualFiniteEulerCoefficientFlag c a)
    (hg : g ∈ A.actualFiniteEulerCoefficientFlag c b) :
    f * g ∈ A.actualFiniteEulerCoefficientFlag c (a + b) :=
  mul_mem_realContinuousDegreeRaisingEndomorphisms
    (A.ActualFiniteLogarithmicEulerSpace c)
    (nativeEulerExtensionFlag ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c)) a b f g hf hg

theorem actualFiniteEulerCoefficientFlag_one :
    (1 : A.ActualFiniteLogarithmicEulerCoefficients c) ∈
      A.actualFiniteEulerCoefficientFlag c 0 :=
  one_mem_realContinuousDegreeRaisingEndomorphisms
    (A.ActualFiniteLogarithmicEulerSpace c)
    (nativeEulerExtensionFlag ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c))

theorem actualFiniteEulerCoefficientFlag_antitone :
    Antitone (A.actualFiniteEulerCoefficientFlag c) :=
  realContinuousDegreeRaisingEndomorphisms_antitone
    (A.ActualFiniteLogarithmicEulerSpace c)
    (nativeEulerExtensionFlag ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c))
    (nativeEulerExtensionFlag_antitone ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c))

theorem actualFiniteEulerCoefficientFlag_bound :
    A.actualFiniteEulerCoefficientFlag c (c + 1) = ⊥ :=
  realContinuousDegreeRaisingEndomorphisms_eq_bot_of_bound
    (A.ActualFiniteLogarithmicEulerSpace c)
    (nativeEulerExtensionFlag ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c))
    (nativeEulerExtensionFlag_zero ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c)) (c + 1)
    (nativeEulerExtensionFlag_bound_eq_bot ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c) c
      (A.actualFiniteLogarithmicComponent_above c))

theorem actualFiniteEulerLogarithmicOneForm_mem_realFlag
    (x : Fin d → ℂ) (hx : x ∈ A.ambientComplementSet) (u : Fin d → ℂ) :
    A.actualFiniteEulerLogarithmicOneForm c x u ∈ A.actualFiniteEulerCoefficientFlag c 1 :=
  A.actualFiniteEulerLogarithmicOneForm_mem_raising c ⟨x, hx⟩ u

/-- The actual coefficient operator is the actual native derivation,
so its original Leibniz law is proved rather than selected. -/
theorem actualFiniteEulerLogarithmicOneForm_derivation
    (x : Fin d → ℂ) (hx : x ∈ A.ambientComplementSet) (u : Fin d → ℂ)
    (a b : A.ActualFiniteLogarithmicEulerSpace c) :
    A.actualFiniteEulerLogarithmicOneForm c x u ⁅a, b⁆ =
      ⁅A.actualFiniteEulerLogarithmicOneForm c x u a, b⁆ +
      ⁅a, A.actualFiniteEulerLogarithmicOneForm c x u b⁆ := by
  have he := A.actualFiniteEulerLogarithmicOneForm_original_point c ⟨x, hx⟩ u
  rw [he]
  simp only [actualFiniteLogarithmicAdjointRepresentation, LieHom.comp_apply,
    nativeDerivationExtensionContinuousAdjoint_apply]
  rw [LieDerivation.apply_lie_eq_add, add_comm]

variable (s : Set (Fin d → ℂ)) (hs : Convex ℝ s) (hso : IsOpen s)
variable (hscomp : s ⊆ A.ambientComplementSet) (x₀ : Fin d → ℂ)

/-- The actual finite parallel sum on the actual original local set. -/
def actualFiniteEulerParallelFunction :
    (Fin d → ℂ) → A.ActualFiniteLogarithmicEulerCoefficients c :=
  actualFiniteFlatParallelFunction s hs hso (A.actualFiniteEulerLogarithmicOneForm c)
    ((A.actualFiniteEulerLogarithmicOneForm_contDiffOn c).mono hscomp)
    (fun x hx => A.actualFiniteEulerLogarithmicOneForm_extDeriv_eq_zero c x (hscomp hx))
    (fun x hx => A.actualFiniteEulerLogarithmicOneForm_commute c x (hscomp hx))
    (A.actualFiniteEulerCoefficientFlag c) (A.actualFiniteEulerCoefficientFlag_mul c)
    (A.actualFiniteEulerCoefficientFlag_one c)
    (fun x hx => A.actualFiniteEulerLogarithmicOneForm_mem_realFlag c x (hscomp hx)) x₀ c

/-- Its actual explicit finite polynomial inverse, with exactly the same
original coefficients and the same actual constructed primitive choices. -/
def actualFiniteEulerParallelInverse :
    (Fin d → ℂ) → A.ActualFiniteLogarithmicEulerCoefficients c :=
  actualFiniteFlatParallelInverseFunction s hs hso (A.actualFiniteEulerLogarithmicOneForm c)
    ((A.actualFiniteEulerLogarithmicOneForm_contDiffOn c).mono hscomp)
    (fun x hx => A.actualFiniteEulerLogarithmicOneForm_extDeriv_eq_zero c x (hscomp hx))
    (fun x hx => A.actualFiniteEulerLogarithmicOneForm_commute c x (hscomp hx))
    (A.actualFiniteEulerCoefficientFlag c) (A.actualFiniteEulerCoefficientFlag_mul c)
    (A.actualFiniteEulerCoefficientFlag_one c)
    (fun x hx => A.actualFiniteEulerLogarithmicOneForm_mem_realFlag c x (hscomp hx)) x₀ c

theorem actualFiniteEulerParallelFunction_smooth :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (A.actualFiniteEulerParallelFunction c s hs hso hscomp x₀) s :=
  actualFiniteFlatParallelFunction_smooth s hs hso _ _ _ _ _ _ _ _ x₀ c

theorem actualFiniteEulerParallelFunction_anchor :
    A.actualFiniteEulerParallelFunction c s hs hso hscomp x₀ x₀ = 1 :=
  actualFiniteFlatParallelFunction_anchor s hs hso _ _ _ _ _ _ _ _ x₀ c

theorem actualFiniteEulerParallelFunction_derivative (x : Fin d → ℂ) (hx : x ∈ s) :
    HasFDerivAt (A.actualFiniteEulerParallelFunction c s hs hso hscomp x₀)
      (rightProductOneForm (A.actualFiniteEulerLogarithmicOneForm c)
        (A.actualFiniteEulerParallelFunction c s hs hso hscomp x₀) x) x :=
  actualFiniteFlatParallelFunction_derivative s hs hso _ _ _ _ _ _ _ _ x₀ c
    (A.actualFiniteEulerCoefficientFlag_bound c) x hx

theorem actualFiniteEulerParallelInverse_mul_function (x : Fin d → ℂ) :
    A.actualFiniteEulerParallelInverse c s hs hso hscomp x₀ x *
      A.actualFiniteEulerParallelFunction c s hs hso hscomp x₀ x = 1 :=
  actualFiniteFlatParallelInverseFunction_mul_function s hs hso _ _ _ _ _ _ _ _ x₀
    (A.actualFiniteEulerCoefficientFlag_antitone c) c (A.actualFiniteEulerCoefficientFlag_bound c) x

theorem actualFiniteEulerParallelFunction_mul_inverse (x : Fin d → ℂ) :
    A.actualFiniteEulerParallelFunction c s hs hso hscomp x₀ x *
      A.actualFiniteEulerParallelInverse c s hs hso hscomp x₀ x = 1 :=
  actualFiniteFlatParallelFunction_mul_inverseFunction s hs hso _ _ _ _ _ _ _ _ x₀
    (A.actualFiniteEulerCoefficientFlag_antitone c) c (A.actualFiniteEulerCoefficientFlag_bound c) x

/-- The actual constructed sum and inverse give an actual native
complex Lie equivalence, with no selected automorphism witness. -/
def actualFiniteEulerParallelLieEquiv (hx₀ : x₀ ∈ s)
    (x : Fin d → ℂ) (hx : x ∈ s) :
    A.ActualFiniteLogarithmicEulerSpace c ≃ₗ⁅ℂ⁆ A.ActualFiniteLogarithmicEulerSpace c :=
  actualComplexFiniteFlatParallelLieEquiv (A.ActualFiniteLogarithmicEulerSpace c)
    s hs hso (A.actualFiniteEulerLogarithmicOneForm c)
    ((A.actualFiniteEulerLogarithmicOneForm_contDiffOn c).mono hscomp)
    (fun y hy => A.actualFiniteEulerLogarithmicOneForm_extDeriv_eq_zero c y (hscomp hy))
    (fun y hy => A.actualFiniteEulerLogarithmicOneForm_commute c y (hscomp hy))
    (A.actualFiniteEulerCoefficientFlag c) (A.actualFiniteEulerCoefficientFlag_mul c)
    (A.actualFiniteEulerCoefficientFlag_one c)
    (fun y hy => A.actualFiniteEulerLogarithmicOneForm_mem_realFlag c y (hscomp hy)) x₀
    (A.actualFiniteEulerCoefficientFlag_antitone c) c (A.actualFiniteEulerCoefficientFlag_bound c)
    hx₀ (fun y hy => A.actualFiniteEulerLogarithmicOneForm_derivation c y (hscomp hy)) x hx

@[simp] theorem actualFiniteEulerParallelLieEquiv_apply (hx₀ : x₀ ∈ s)
    (x : Fin d → ℂ) (hx : x ∈ s) (a : A.ActualFiniteLogarithmicEulerSpace c) :
    A.actualFiniteEulerParallelLieEquiv c s hs hso hscomp x₀ hx₀ x hx a =
      A.actualFiniteEulerParallelFunction c s hs hso hscomp x₀ x a := rfl

/-- The actual frame differs from the original identity by an actual
degree-one raising operator, derived from the genuine primitive values. -/
theorem actualFiniteEulerParallelLieEquiv_raising_deviation
    (hx₀ : x₀ ∈ s) (x : Fin d → ℂ) (hx : x ∈ s) :
    (A.actualFiniteEulerParallelLieEquiv c s hs hso hscomp x₀ hx₀ x hx).toLinearEquiv.toLinearMap -
      LinearMap.id ∈ degreeRaisingEndomorphisms ℂ (A.ActualFiniteLogarithmicEulerSpace c)
        (nativeEulerExtensionFlag ℂ (A.ActualFiniteLogarithmicLie c)
          (A.actualFiniteLogarithmicComponent c)) 1 := by
  have h := actualFiniteFlatParallelFunction_sub_one_mem s hs hso
    (A.actualFiniteEulerLogarithmicOneForm c)
    ((A.actualFiniteEulerLogarithmicOneForm_contDiffOn c).mono hscomp)
    (fun y hy => A.actualFiniteEulerLogarithmicOneForm_extDeriv_eq_zero c y (hscomp hy))
    (fun y hy => A.actualFiniteEulerLogarithmicOneForm_commute c y (hscomp hy))
    (A.actualFiniteEulerCoefficientFlag c) (A.actualFiniteEulerCoefficientFlag_mul c)
    (A.actualFiniteEulerCoefficientFlag_one c)
    (fun y hy => A.actualFiniteEulerLogarithmicOneForm_mem_realFlag c y (hscomp hy)) x₀
    (A.actualFiniteEulerCoefficientFlag_antitone c) c x
  exact (mem_realContinuousDegreeRaisingEndomorphisms (A.ActualFiniteLogarithmicEulerSpace c)
    (nativeEulerExtensionFlag ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c)) 1 _).mp h

end ChenRanks.AffineArrangement
