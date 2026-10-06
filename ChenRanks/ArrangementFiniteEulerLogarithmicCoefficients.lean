import ChenRanks.ArrangementNativeLogarithmicPointwiseFlatness
import ChenRanks.NativeEulerExtensionContinuousAdjoint
import ChenRanks.QuadraticHolonomyFiniteModel
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Actual original logarithmic coefficients in the actual finite Euler model

The Lie algebra is the actual finite native quotient of the original
metabelian Koszul model, with the original determinant annihilator as its
relations. Its grading, degree bound and finite dimension are obtained
from the actual finite-truncation factory. Its native Euler extension is
then genuinely normed and carries the actual continuous adjoint.

The coefficient form is a genuine finite sum of the original normalized
logarithms with these original adjoint operators. Its pointwise expression
is the already proved original tangent functional mapped along the actual
native quotient and adjoint Lie morphisms. The actual pointwise bracket
identity proves actual operator commutation. Actual raising membership is
derived from the actual Euler grading. No model, flatness, operator flag,
commutation or positive-automorphism witness is supplied as an input.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

open LieComparison

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The original finite native Koszul quotient with the actual original
determinant-annihilator relation subspace. -/
abbrev ActualFiniteLogarithmicLie (c : ℕ) :=
  Koszul.finiteModelTruncation ℂ (Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c

/-- Its actual native homogeneous subspaces. -/
def actualFiniteLogarithmicComponent (c n : ℕ) : Submodule ℂ (A.ActualFiniteLogarithmicLie c) :=
  Koszul.finiteModelComponent ℂ (Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c n

instance actualFiniteLogarithmicGradedLieAlgebra (c : ℕ) :
    GradedLieAlgebra (A.actualFiniteLogarithmicComponent c) :=
  Koszul.finiteModelGradedLieAlgebra ℂ (Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c

instance actualFiniteLogarithmicLie_finiteDimensional (c : ℕ) :
    FiniteDimensional ℂ (A.ActualFiniteLogarithmicLie c) :=
  Koszul.finiteModelTruncation_finiteDimensional ℂ (Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c

theorem actualFiniteLogarithmicComponent_zero (c : ℕ) :
    A.actualFiniteLogarithmicComponent c 0 = ⊥ :=
  Koszul.finiteModelComponent_zero ℂ (Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c

theorem actualFiniteLogarithmicComponent_above (c n : ℕ) (hcn : c < n) :
    A.actualFiniteLogarithmicComponent c n = ⊥ :=
  Koszul.finiteModelComponent_eq_bot_above ℂ (Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c n hcn

/-- The original quadratic holonomy maps by the actual native quotient
maps to that same actual finite model. -/
def actualHolonomyToFiniteLogarithmicLie (c : ℕ) :
    A.ActualLogarithmicHolonomyLie →ₗ⁅ℂ⁆ A.ActualFiniteLogarithmicLie c :=
  quadraticHolonomyToFiniteModel ℂ (Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c

/-- The actual native Euler derivation of that same actual finite model. -/
def actualFiniteLogarithmicEuler (c : ℕ) :
    LieDerivation ℂ (A.ActualFiniteLogarithmicLie c) (A.ActualFiniteLogarithmicLie c) :=
  nativeEulerDerivation ℂ (A.ActualFiniteLogarithmicLie c)
    (A.actualFiniteLogarithmicComponent c)

/-- The genuine native scalar-first Euler extension. -/
abbrev ActualFiniteLogarithmicEulerSpace (c : ℕ) :=
  NativeDerivationExtension ℂ (A.ActualFiniteLogarithmicLie c) (A.actualFiniteLogarithmicEuler c)

instance actualFiniteLogarithmicEulerSpace_finiteDimensional (c : ℕ) :
    FiniteDimensional ℂ (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeDerivationExtension_finiteDimensional ℂ (A.ActualFiniteLogarithmicLie c)
    (A.actualFiniteLogarithmicEuler c)

variable (c : ℕ)

local instance finiteLogEulerNormedAddCommGroup :
    NormedAddCommGroup (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedAddCommGroup ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance finiteLogEulerNormedSpace :
    NormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance finiteLogEulerRealNormedSpace :
    NormedSpace ℝ (A.ActualFiniteLogarithmicEulerSpace c) :=
  NormedSpace.restrictScalars ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance finiteLogEulerScalarTower : IsScalarTower ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c) where
  smul_assoc r a x := by
    change ((r : ℂ) * a) • x = (r : ℂ) • (a • x)
    exact mul_smul _ _ _
local instance finiteLogEulerSMulCommClass : SMulCommClass ℂ ℝ (A.ActualFiniteLogarithmicEulerSpace c) where
  smul_comm a r x := by
    change a • ((r : ℂ) • x) = (r : ℂ) • (a • x)
    exact smul_comm _ _ _

/-- The genuine original complex continuous coefficient algebra. -/
abbrev ActualFiniteLogarithmicEulerCoefficients :=
  A.ActualFiniteLogarithmicEulerSpace c →L[ℂ] A.ActualFiniteLogarithmicEulerSpace c

/-- The actual continuous adjoint Lie morphism, after the actual native
finite quotient. -/
def actualFiniteLogarithmicAdjointRepresentation :
    A.ActualLogarithmicHolonomyLie →ₗ⁅ℂ⁆ A.ActualFiniteLogarithmicEulerCoefficients c :=
  (nativeDerivationExtensionContinuousAdjoint ℂ (A.ActualFiniteLogarithmicLie c)
    (A.actualFiniteLogarithmicEuler c)).comp (A.actualHolonomyToFiniteLogarithmicLie c)

/-- Every original label dual generator has its actual original continuous
adjoint coefficient. -/
def actualFiniteLogarithmicGeneratorCoefficient (H : ι) :
    A.ActualFiniteLogarithmicEulerCoefficients c :=
  A.actualFiniteLogarithmicAdjointRepresentation c
    (A.actualLogHolonomyGeneratorMap (LinearMap.proj H))

/-- The actual coefficient one-form, a finite sum on the original
ambient tangent space with the genuine normalized original logarithms. -/
def actualFiniteEulerLogarithmicOneForm (x : Fin d → ℂ) :
    (Fin d → ℂ) →L[ℝ] A.ActualFiniteLogarithmicEulerCoefficients c :=
  ∑ H : ι,
    ((ContinuousLinearMap.toSpanSingleton ℂ (A.actualFiniteLogarithmicGeneratorCoefficient c H)).restrictScalars ℝ).comp
      ((logarithmicPeriodConstant⁻¹ * (A.normal H x - A.offset H)⁻¹) • A.actualNormalRealCLM H)

/-- The true actual values of the actual constructed coefficient form. -/
theorem actualFiniteEulerLogarithmicOneForm_apply (x : Fin d → ℂ) (u : Fin d → ℂ) :
    A.actualFiniteEulerLogarithmicOneForm c x u =
      ∑ H : ι, (logarithmicPeriodConstant⁻¹ *
        (A.normal H x - A.offset H)⁻¹ * A.normal H u) •
        A.actualFiniteLogarithmicGeneratorCoefficient c H := by
  simp [actualFiniteEulerLogarithmicOneForm, ContinuousLinearMap.toSpanSingleton,
    actualNormalRealCLM_apply, smul_eq_mul]

/-- The actual original functional has the literal finite dual-generator
expansion needed to identify the actual original coefficient form. -/
theorem actualNormalizedNativeLogTangentFunctional_sum
    (x : A.actualSmoothComplementOpen) (u : Fin d → ℂ) :
    A.actualNormalizedNativeLogTangentFunctional x u =
      ∑ H : ι, A.actualNormalizedNativeLogValue H x u •
        (LinearMap.proj H : Module.Dual ℂ (ι → ℂ)) := by
  apply LinearMap.ext
  intro a
  simp [actualNormalizedNativeLogTangentFunctional_apply, mul_comm]

/-- The actual coefficient one-form is the actual original tangent
functional mapped by the actual quotient and native adjoint. -/
theorem actualFiniteEulerLogarithmicOneForm_original_point
    (x : A.actualSmoothComplementOpen) (u : Fin d → ℂ) :
    A.actualFiniteEulerLogarithmicOneForm c x.val u =
      A.actualFiniteLogarithmicAdjointRepresentation c
        (A.actualLogHolonomyGeneratorMap (A.actualNormalizedNativeLogTangentFunctional x u)) := by
  rw [actualFiniteEulerLogarithmicOneForm_apply,
    actualNormalizedNativeLogTangentFunctional_sum, map_sum, map_sum]
  simp only [map_smul, actualNormalizedNativeLogValue,
    actualFiniteLogarithmicGeneratorCoefficient]

/-- Original logarithmic relations prove that the actual coefficient
endomorphisms commute at every actual complement point. -/
theorem actualFiniteEulerLogarithmicOneForm_commute
    (x : Fin d → ℂ) (hx : x ∈ A.ambientComplementSet) (u v : Fin d → ℂ) :
    A.actualFiniteEulerLogarithmicOneForm c x u * A.actualFiniteEulerLogarithmicOneForm c x v =
      A.actualFiniteEulerLogarithmicOneForm c x v * A.actualFiniteEulerLogarithmicOneForm c x u := by
  have h := A.actualNormalizedNativeLogTangent_map_bracket_eq_zero
    (A.actualFiniteLogarithmicAdjointRepresentation c) ⟨x, hx⟩ u v
  rw [← actualFiniteEulerLogarithmicOneForm_original_point,
    ← actualFiniteEulerLogarithmicOneForm_original_point] at h
  change A.actualFiniteEulerLogarithmicOneForm c x u * A.actualFiniteEulerLogarithmicOneForm c x v -
    A.actualFiniteEulerLogarithmicOneForm c x v * A.actualFiniteEulerLogarithmicOneForm c x u = 0 at h
  exact sub_eq_zero.mp h

/-- The actual continuous coefficient belongs to its actual Euler
raising subspace, by the actual model grading and its zero degree. -/
theorem actualFiniteEulerLogarithmicOneForm_mem_raising
    (x : A.actualSmoothComplementOpen) (u : Fin d → ℂ) :
    A.actualFiniteEulerLogarithmicOneForm c x.val u ∈
      continuousDegreeRaisingEndomorphisms ℂ (A.ActualFiniteLogarithmicEulerSpace c)
        (nativeEulerExtensionFlag ℂ (A.ActualFiniteLogarithmicLie c)
          (A.actualFiniteLogarithmicComponent c)) 1 := by
  rw [actualFiniteEulerLogarithmicOneForm_original_point]
  exact nativeEulerExtensionContinuousAdjoint_mem_raising ℂ (A.ActualFiniteLogarithmicLie c)
    (A.actualFiniteLogarithmicComponent c) (A.actualFiniteLogarithmicComponent_zero c)
    (A.actualHolonomyToFiniteLogarithmicLie c
      (A.actualLogHolonomyGeneratorMap (A.actualNormalizedNativeLogTangentFunctional x u)))

end ChenRanks.AffineArrangement
