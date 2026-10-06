import ChenRanks.ArrangementSmoothFormComplex
import ChenRanks.OpenSmoothFunctionAlgebra

/-!
# Actual original affine equations as smooth units

The original equations and their actual reciprocals are proved smooth on
the actual original complement.  Their product identities construct real
units of the native smooth-function ring.  Native Fréchet calculus gives
their actual directional derivatives, including the reciprocal derivative.
No unit, smooth inverse, differential formula, or model field is supplied.
These are the coefficients needed for the original logarithmic generators
in the actual smooth coefficient exterior algebra.
-/

noncomputable section


open scoped Topology

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The same original equation as a genuine smooth coefficient. -/
def actualSmoothEquation (H : ι) :
    OpenSmoothFunctions.SmoothFunction A.actualSmoothComplementOpen := by
  refine ⟨fun x => A.actualAffineEquationFunction H x.val, ?_⟩
  change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
    (OpenSmoothFunctions.zeroExtension A.actualSmoothComplementOpen
      (fun x => A.actualAffineEquationFunction H x.val)) A.actualSmoothComplementOpen
  have hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (A.actualAffineEquationFunction H)
      A.actualSmoothComplementOpen := by
    simpa only [actualAffineEquationFunction, actualNormalRealCLM_apply] using
      ((A.actualNormalRealCLM H).contDiff.sub contDiff_const).contDiffOn
  apply hf.congr
  intro x hx
  exact OpenSmoothFunctions.zeroExtension_apply_mem A.actualSmoothComplementOpen
    (fun y => A.actualAffineEquationFunction H y.val) x hx

@[simp] theorem actualSmoothEquation_apply
    (H : ι) (x : A.actualSmoothComplementOpen) :
    A.actualSmoothEquation H x = A.normal H x.val - A.offset H := rfl

/-- Its actual reciprocal, proved smooth on the original complement. -/
def actualSmoothEquationInverse (H : ι) :
    OpenSmoothFunctions.SmoothFunction A.actualSmoothComplementOpen := by
  refine ⟨fun x => (A.actualAffineEquationFunction H x.val)⁻¹, ?_⟩
  change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
    (OpenSmoothFunctions.zeroExtension A.actualSmoothComplementOpen
      (fun x => (A.actualAffineEquationFunction H x.val)⁻¹)) A.actualSmoothComplementOpen
  have hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (A.actualAffineEquationFunction H)
      A.actualSmoothComplementOpen := by
    simpa only [actualAffineEquationFunction, actualNormalRealCLM_apply] using
      ((A.actualNormalRealCLM H).contDiff.sub contDiff_const).contDiffOn
  have hne : ∀ x ∈ A.actualSmoothComplementOpen,
      A.actualAffineEquationFunction H x ≠ 0 := fun x hx => sub_ne_zero.mpr (hx H)
  apply (hf.inv hne).congr
  intro x hx
  exact OpenSmoothFunctions.zeroExtension_apply_mem A.actualSmoothComplementOpen
    (fun y => (A.actualAffineEquationFunction H y.val)⁻¹) x hx

@[simp] theorem actualSmoothEquationInverse_apply
    (H : ι) (x : A.actualSmoothComplementOpen) :
    A.actualSmoothEquationInverse H x = (A.normal H x.val - A.offset H)⁻¹ := rfl

/-- A genuine unit in the same native smooth-function ring. -/
def actualSmoothEquationUnit (H : ι) :
    (OpenSmoothFunctions.SmoothFunction A.actualSmoothComplementOpen)ˣ where
  val := A.actualSmoothEquation H
  inv := A.actualSmoothEquationInverse H
  val_inv := by
    apply Subtype.ext
    funext x
    change (A.normal H x.val - A.offset H) * (A.normal H x.val - A.offset H)⁻¹ = 1
    exact mul_inv_cancel₀ (sub_ne_zero.mpr (x.property H))
  inv_val := by
    apply Subtype.ext
    funext x
    change (A.normal H x.val - A.offset H)⁻¹ * (A.normal H x.val - A.offset H) = 1
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (x.property H))

/-- The original equation's derivative is the actual constant original
normal evaluated on the actual tangent direction. -/
theorem actualSmoothEquation_directional
    (H : ι) (v : Fin d → ℂ) :
    OpenSmoothFunctions.directionalLinearMap A.actualSmoothComplementOpen v
      (A.actualSmoothEquation H) =
      algebraMap ℂ (OpenSmoothFunctions.SmoothFunction A.actualSmoothComplementOpen)
        (A.normal H v) := by
  apply Subtype.ext
  funext x
  have hg : OpenSmoothFunctions.zeroExtension A.actualSmoothComplementOpen
      (A.actualSmoothEquation H).val =ᶠ[𝓝 x.val]
        A.actualAffineEquationFunction H := by
    filter_upwards [A.ambientComplementSet_isOpen.mem_nhds x.property] with y hy
    rw [OpenSmoothFunctions.zeroExtension_apply_mem A.actualSmoothComplementOpen
      (A.actualSmoothEquation H).val y hy]
    rfl
  change fderiv ℝ (OpenSmoothFunctions.zeroExtension A.actualSmoothComplementOpen
    (A.actualSmoothEquation H).val) x.val v = A.normal H v
  rw [hg.fderiv_eq, (A.actualAffineEquationFunction_hasFDerivAt H x.val).fderiv]
  rfl

/-- The actual reciprocal derivative needed for closedness of logarithmic
generators is proved by native inverse calculus at each original point. -/
theorem actualSmoothEquationInverse_directional
    (H : ι) (v : Fin d → ℂ) :
    OpenSmoothFunctions.directionalLinearMap A.actualSmoothComplementOpen v
      (A.actualSmoothEquationInverse H) =
      -(A.actualSmoothEquationInverse H * A.actualSmoothEquationInverse H) *
        algebraMap ℂ (OpenSmoothFunctions.SmoothFunction A.actualSmoothComplementOpen)
          (A.normal H v) := by
  apply Subtype.ext
  funext x
  have hg : OpenSmoothFunctions.zeroExtension A.actualSmoothComplementOpen
      (A.actualSmoothEquationInverse H).val =ᶠ[𝓝 x.val]
        (fun y => (A.actualAffineEquationFunction H y)⁻¹) := by
    filter_upwards [A.ambientComplementSet_isOpen.mem_nhds x.property] with y hy
    rw [OpenSmoothFunctions.zeroExtension_apply_mem A.actualSmoothComplementOpen
      (A.actualSmoothEquationInverse H).val y hy]
    rfl
  have hne : A.actualAffineEquationFunction H x.val ≠ 0 :=
    sub_ne_zero.mpr (x.property H)
  change fderiv ℝ (OpenSmoothFunctions.zeroExtension A.actualSmoothComplementOpen
    (A.actualSmoothEquationInverse H).val) x.val v =
      -((A.actualAffineEquationFunction H x.val)⁻¹ *
        (A.actualAffineEquationFunction H x.val)⁻¹) * A.normal H v
  rw [hg.fderiv_eq]
  change fderiv ℝ (Inv.inv ∘ A.actualAffineEquationFunction H) x.val v =
    -((A.actualAffineEquationFunction H x.val)⁻¹ *
      (A.actualAffineEquationFunction H x.val)⁻¹) * A.normal H v
  rw [((hasFDerivAt_inv' (𝕜 := ℝ) hne).comp x.val
    (A.actualAffineEquationFunction_hasFDerivAt H x.val)).fderiv]
  simp only [ContinuousLinearMap.comp_apply, actualNormalRealCLM_apply]
  change -((A.actualAffineEquationFunction H x.val)⁻¹ * A.normal H v *
      (A.actualAffineEquationFunction H x.val)⁻¹) =
    -((A.actualAffineEquationFunction H x.val)⁻¹ *
      (A.actualAffineEquationFunction H x.val)⁻¹) * A.normal H v
  ring

end ChenRanks.AffineArrangement
