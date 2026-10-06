import ChenRanks.ArrangementFiniteEulerExponentialFrames
import ChenRanks.ArrangementFiniteEulerAxisObjects

/-!
# The actual local axis character has the original logarithmic derivative

The target is the original finite Lie model modulo its actual degree-two
tail. Evaluating the genuinely constructed local parallel sum on its
actual scalar axis and projecting to this target gives an actual smooth
local function. Its derivative is the actual normalized logarithmic
coefficient form projected along the actual generators.

The scalar axis coordinate is derived from the proved raising deviation.
The native quotient kills the actual bracket term, and the actual finite
generator has genuine degree one, so the native Euler derivation acts
as the identity on it. No comparison with winding, supplied derivative,
character identity, or monodromy is an input. The subsequent path-period
comparison is separate.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

open LieComparison OpenSmoothForms

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι) (c : ℕ)

local instance finiteAxisOriginalNormedAddCommGroup :
    NormedAddCommGroup (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedAddCommGroup ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance finiteAxisOriginalNormedSpace :
    NormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance finiteAxisOriginalRealNormedSpace :
    NormedSpace ℝ (A.ActualFiniteLogarithmicEulerSpace c) :=
  NormedSpace.restrictScalars ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance finiteAxisQuotientNormedAddCommGroup :
    NormedAddCommGroup (A.ActualFiniteEulerAxisQuotient c) :=
  nativeFiniteNormedAddCommGroup ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance finiteAxisQuotientNormedSpace :
    NormedSpace ℂ (A.ActualFiniteEulerAxisQuotient c) :=
  nativeFiniteNormedSpace ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance finiteAxisQuotientRealNormedSpace :
    NormedSpace ℝ (A.ActualFiniteEulerAxisQuotient c) :=
  NormedSpace.restrictScalars ℝ ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance (priority := 4500) finiteAxisQuotientRealModule :
    Module ℝ (A.ActualFiniteEulerAxisQuotient c) :=
  (finiteAxisQuotientRealNormedSpace A c).toModule
local instance (priority := 4500) finiteAxisQuotientRealSMul :
    SMul ℝ (A.ActualFiniteEulerAxisQuotient c) :=
  (finiteAxisQuotientRealModule A c).toSMul
local instance finiteAxisEndRealNormedAlgebra :
    NormedAlgebra ℝ (A.ActualFiniteLogarithmicEulerCoefficients c) :=
  NormedAlgebra.restrictScalars ℝ ℂ (A.ActualFiniteLogarithmicEulerCoefficients c)

local instance finiteAxisOriginalScalarTower :
    IsScalarTower ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c) where
  smul_assoc r a p := by
    change ((r : ℂ) * a) • p = (r : ℂ) • (a • p)
    exact mul_smul _ _ _
local instance finiteAxisQuotientScalarTower :
    IsScalarTower ℝ ℂ (A.ActualFiniteEulerAxisQuotient c) where
  smul_assoc r a p := by
    change ((r : ℂ) * a) • p = (r : ℂ) • (a • p)
    exact mul_smul _ _ _

/-- The original quotient projection after original vector coordinates. -/
def actualFiniteEulerAxisVectorQuotient :
    A.ActualFiniteLogarithmicEulerSpace c →ₗ[ℂ] A.ActualFiniteEulerAxisQuotient c :=
  (nativeGradedTail ℂ (A.ActualFiniteLogarithmicLie c)
    (A.actualFiniteLogarithmicComponent c) 2).mkQ.comp
    ((LinearMap.snd ℂ ℂ (A.ActualFiniteLogarithmicLie c)).comp
      (nativeDerivationExtensionCoordinates ℂ (A.ActualFiniteLogarithmicLie c)
        (A.actualFiniteLogarithmicEuler c)).toLinearMap)

/-- The actual continuous coefficient functional evaluates the original
axis and then takes the actual original vector quotient. -/
def actualFiniteEulerAxisOperatorQuotientLinear :
    A.ActualFiniteLogarithmicEulerCoefficients c →ₗ[ℂ]
      A.ActualFiniteEulerAxisQuotient c where
  toFun f := A.actualFiniteEulerAxisVectorQuotient c
    (f (nativeDerivationExtensionAxis ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicEuler c)))
  map_add' f g := by
    change A.actualFiniteEulerAxisVectorQuotient c (_ + _) = _ + _
    exact map_add _ _ _
  map_smul' a f := by
    change A.actualFiniteEulerAxisVectorQuotient c (a • _) = a • _
    exact map_smul _ _ _

def actualFiniteEulerAxisOperatorQuotient :
    A.ActualFiniteLogarithmicEulerCoefficients c →L[ℝ]
      A.ActualFiniteEulerAxisQuotient c :=
  (A.actualFiniteEulerAxisOperatorQuotientLinear c).toContinuousLinearMap.restrictScalars ℝ

@[simp] theorem actualFiniteEulerAxisOperatorQuotient_apply
    (f : A.ActualFiniteLogarithmicEulerCoefficients c) :
    A.actualFiniteEulerAxisOperatorQuotient c f =
      A.actualFiniteEulerAxisVectorQuotient c
        (f (nativeDerivationExtensionAxis ℂ (A.ActualFiniteLogarithmicLie c)
          (A.actualFiniteLogarithmicEuler c))) := rfl

/-- Original generator images genuinely belong to the original degree one. -/
theorem actualHolonomyToFiniteLogarithmicLie_generator_mem_one
    (a : Module.Dual ℂ (ι → ℂ)) :
    A.actualHolonomyToFiniteLogarithmicLie c (A.actualLogHolonomyGeneratorMap a) ∈
      A.actualFiniteLogarithmicComponent c 1 := by
  change quadraticHolonomyToFiniteModel ℂ (Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c
      (quadraticHolonomyGenerators ℂ (Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis
        (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) a) ∈ _
  rw [quadraticHolonomyToFiniteModel_generator]
  refine ⟨Koszul.MetabelianLieModel.generatorInclusion ℂ
    (Module.Dual ℂ (ι → ℂ))
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) a, ?_, rfl⟩
  change _ ∈ LinearMap.range (Koszul.MetabelianLieModel.generatorInclusion ℂ
    (Module.Dual ℂ (ι → ℂ))
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel))
  exact ⟨a, rfl⟩

/-- Brackets of original actual vectors are killed by the actual degree-two quotient. -/
theorem actualFiniteEulerAxisQuotient_bracket_eq_zero
    (a b : A.ActualFiniteLogarithmicLie c) :
    (nativeGradedTail ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c) 2).mkQ ⁅a, b⁆ = 0 := by
  have ha : a ∈ nativeGradedTail ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c) 1 := by
    rw [nativeGradedTail_one_eq_top ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c) (A.actualFiniteLogarithmicComponent_zero c)]
    trivial
  have hb : b ∈ nativeGradedTail ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c) 1 := by
    rw [nativeGradedTail_one_eq_top ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c) (A.actualFiniteLogarithmicComponent_zero c)]
    trivial
  exact (Submodule.Quotient.mk_eq_zero
    (nativeGradedTail ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c) 2)).mpr
    (lie_mem_nativeGradedTail ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c) 1 1 a b ha hb)

/-- Actual scalar-coordinate one makes the quotient of the original
adjoint action exactly the original normalized logarithmic generator. -/
theorem actualFiniteEulerLogarithmicOneForm_axisQuotient_action
    (x : A.actualSmoothComplementOpen) (u : Fin d → ℂ)
    (p : A.ActualFiniteLogarithmicEulerSpace c)
    (hp : (nativeDerivationExtensionCoordinates ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicEuler c) p).1 = 1) :
    A.actualFiniteEulerAxisVectorQuotient c
      (A.actualFiniteEulerLogarithmicOneForm c x.val u p) =
      (nativeGradedTail ℂ (A.ActualFiniteLogarithmicLie c)
        (A.actualFiniteLogarithmicComponent c) 2).mkQ
        (A.actualHolonomyToFiniteLogarithmicLie c
          (A.actualLogHolonomyGeneratorMap (A.actualNormalizedNativeLogTangentFunctional x u))) := by
  let ξ := A.actualHolonomyToFiniteLogarithmicLie c
    (A.actualLogHolonomyGeneratorMap (A.actualNormalizedNativeLogTangentFunctional x u))
  have hξ := A.actualHolonomyToFiniteLogarithmicLie_generator_mem_one c
    (A.actualNormalizedNativeLogTangentFunctional x u)
  have hD : A.actualFiniteLogarithmicEuler c ξ = ξ := by
    change nativeEulerDerivation ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c) ξ = ξ
    rw [nativeEulerDerivation_of_mem ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c) 1 ξ hξ]
    simp only [Nat.cast_one, one_smul]
  rw [A.actualFiniteEulerLogarithmicOneForm_original_point c x u]
  simp only [actualFiniteLogarithmicAdjointRepresentation, LieHom.comp_apply,
    nativeDerivationExtensionContinuousAdjoint_apply]
  change (nativeGradedTail ℂ (A.ActualFiniteLogarithmicLie c)
    (A.actualFiniteLogarithmicComponent c) 2).mkQ
    ((nativeDerivationExtensionCoordinates ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicEuler c)
      (nativeDerivationExtensionAdjoint ℂ (A.ActualFiniteLogarithmicLie c)
        (A.actualFiniteLogarithmicEuler c) ξ p)).2) = _
  change p.right = 1 at hp
  rw [nativeDerivationExtensionAdjoint_coordinates, hp, one_smul, hD, map_add,
    actualFiniteEulerAxisQuotient_bracket_eq_zero, add_zero]

/-- The actual projected one-form is literally the finite sum of the
original normalized logarithms with the original generator classes. -/
theorem actualFiniteEulerAxisOperatorQuotient_form_value
    (x : A.actualSmoothComplementOpen) (u : Fin d → ℂ) :
    A.actualFiniteEulerAxisOperatorQuotient c
      (A.actualFiniteEulerLogarithmicOneForm c x.val u) =
      ∑ H : ι, A.actualNormalizedNativeLogValue H x u •
        A.actualFiniteEulerAxisGeneratorClass c H := by
  rw [actualFiniteEulerAxisOperatorQuotient_apply,
    A.actualFiniteEulerLogarithmicOneForm_axisQuotient_action c x u
      (nativeDerivationExtensionAxis ℂ (A.ActualFiniteLogarithmicLie c)
        (A.actualFiniteLogarithmicEuler c)) (by rfl),
    actualNormalizedNativeLogTangentFunctional_sum, map_sum, map_sum, map_sum]
  simp only [map_smul, actualFiniteEulerAxisGeneratorClass]

variable (s : Set (Fin d → ℂ)) (hs : Convex ℝ s) (hso : IsOpen s)
variable (hscomp : s ⊆ A.ambientComplementSet) (x₀ : Fin d → ℂ) (hx₀ : x₀ ∈ s)

/-- The actual local axis primitive, defined using the original actual parallel sum. -/
def actualFiniteEulerParallelAxisPrimitive :
    (Fin d → ℂ) → A.ActualFiniteEulerAxisQuotient c :=
  fun x => A.actualFiniteEulerAxisOperatorQuotient c
    (A.actualFiniteEulerParallelFunction c s hs hso hscomp x₀ x)

/-- Its value on the actual neighborhood is exactly the actual native
axis character of the actual subgroup-valued parallel frame. -/
theorem actualFiniteEulerParallelAxisPrimitive_eq_character (x : s) :
    A.actualFiniteEulerParallelAxisPrimitive c s hs hso hscomp x₀ x.val =
      (nativeEulerAxisAbelianCharacter ℂ (A.ActualFiniteLogarithmicLie c)
        (A.actualFiniteLogarithmicComponent c) (A.actualFiniteLogarithmicComponent_zero c) c
        (A.actualFiniteLogarithmicComponent_above c)
        (A.actualFiniteEulerExponentialFrame c s hs hso hscomp x₀ hx₀ x)).toAdd := rfl

include hx₀ in
/-- The genuine local derivative is the actual logarithmic form in the
actual quotient, without a supplied character or period comparison. -/
theorem actualFiniteEulerParallelAxisPrimitive_derivative
    (x : Fin d → ℂ) (hx : x ∈ s) :
    HasFDerivAt (A.actualFiniteEulerParallelAxisPrimitive c s hs hso hscomp x₀)
      ((A.actualFiniteEulerAxisOperatorQuotient c).comp
        (A.actualFiniteEulerLogarithmicOneForm c x)) x := by
  have hU := A.actualFiniteEulerParallelFunction_derivative c s hs hso hscomp x₀ x hx
  have h := (A.actualFiniteEulerAxisOperatorQuotient c).hasFDerivAt.comp x hU
  have he : (A.actualFiniteEulerAxisOperatorQuotient c).comp
      (rightProductOneForm (A.actualFiniteEulerLogarithmicOneForm c)
        (A.actualFiniteEulerParallelFunction c s hs hso hscomp x₀) x) =
      (A.actualFiniteEulerAxisOperatorQuotient c).comp
        (A.actualFiniteEulerLogarithmicOneForm c x) := by
    apply ContinuousLinearMap.ext
    intro u
    let axis := nativeDerivationExtensionAxis ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicEuler c)
    let frame := A.actualFiniteEulerParallelLieEquiv c s hs hso hscomp x₀ hx₀ x hx
    have hscalar := nativeEulerAutomorphism_scalar_of_raising_deviation ℂ
      (A.ActualFiniteLogarithmicLie c) (A.actualFiniteLogarithmicComponent c) frame
      (A.actualFiniteEulerParallelLieEquiv_raising_deviation c s hs hso hscomp x₀ hx₀ x hx)
    change A.actualFiniteEulerAxisVectorQuotient c
        (A.actualFiniteEulerLogarithmicOneForm c x u
          (A.actualFiniteEulerParallelFunction c s hs hso hscomp x₀ x axis)) =
      A.actualFiniteEulerAxisVectorQuotient c
        (A.actualFiniteEulerLogarithmicOneForm c x u axis)
    have hleft := A.actualFiniteEulerLogarithmicOneForm_axisQuotient_action c
      ⟨x, hscomp hx⟩ u (frame axis) hscalar
    have hright := A.actualFiniteEulerLogarithmicOneForm_axisQuotient_action c
      ⟨x, hscomp hx⟩ u axis (by rfl)
    have hframe : frame axis =
        A.actualFiniteEulerParallelFunction c s hs hso hscomp x₀ x axis :=
      A.actualFiniteEulerParallelLieEquiv_apply c s hs hso hscomp x₀ hx₀ x hx axis
    rw [hframe] at hleft
    exact hleft.trans hright.symm
  rw [he] at h
  exact h

end ChenRanks.AffineArrangement
