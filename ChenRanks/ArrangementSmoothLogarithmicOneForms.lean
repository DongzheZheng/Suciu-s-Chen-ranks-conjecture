import ChenRanks.ArrangementSingleNormalRealMap
import ChenRanks.ArrangementPathUniformNeighborhood
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The original logarithmic one-forms as actual smooth real differential forms

The ambient complex affine space is regarded as a real normed space, and
forms have complex values.  The form attached to an original hyperplane is
the actual function `x ↦ (normal H x - offset H)⁻¹ • normal H`.  Its real
Fréchet derivative is constructed from the native inverse derivative and
the same original affine equation.  Native exterior differentiation then
vanishes by the symmetry of the resulting two-variable expression.

No closedness, differential form, comparison, or formality premise is used.
This source is an analytic entrance to the manuscript's logarithmic DGA.
It does not yet construct its products, a strict CDGA map, a topological
1-equivalence, or a Malcev/Chen comparison.
-/

noncomputable section


open ContinuousAlternatingMap

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- Both scalar actions on actual complex-valued forms act on their values. -/
local instance actualRealComplexOneFormScalarTower :
    IsScalarTower ℝ ℂ ((Fin d → ℂ) [⋀^Fin 1]→L[ℝ] ℂ) where
  smul_assoc a c ω := by
    ext v
    exact smul_assoc a c (ω v)

/-- The original normal, continuously linear over the real scalar field. -/
def actualNormalRealCLM (H : ι) : (Fin d → ℂ) →L[ℝ] ℂ :=
  (A.actualSingleNormalRealMap H).toContinuousLinearMap

@[simp] theorem actualNormalRealCLM_apply (H : ι) (v : Fin d → ℂ) :
    A.actualNormalRealCLM H v = A.normal H v := rfl

/-- The same original affine equation, as an actual smooth function. -/
def actualAffineEquationFunction (H : ι) (x : Fin d → ℂ) : ℂ :=
  A.normal H x - A.offset H

/-- The constant real differential of the original affine equation. -/
def actualNormalRealOneForm (H : ι) :
    (Fin d → ℂ) [⋀^Fin 1]→L[ℝ] ℂ :=
  .ofSubsingleton ℝ (Fin d → ℂ) ℂ (0 : Fin 1) (A.actualNormalRealCLM H)

/-- The original logarithmic one-form.  The ambient total function uses the
native total inverse; all smoothness and closedness assertions are made
only where the original equation is nonzero. -/
def actualAmbientLogarithmicOneForm (H : ι) (x : Fin d → ℂ) :
    (Fin d → ℂ) [⋀^Fin 1]→L[ℝ] ℂ :=
  (A.actualAffineEquationFunction H x)⁻¹ • A.actualNormalRealOneForm H

/-- Its value on an actual tangent vector is exactly `dℓ_H/(ℓ_H-offset)`. -/
@[simp] theorem actualAmbientLogarithmicOneForm_apply
    (H : ι) (x : Fin d → ℂ) (v : Fin 1 → (Fin d → ℂ)) :
    A.actualAmbientLogarithmicOneForm H x v =
      (A.normal H x - A.offset H)⁻¹ * A.normal H (v 0) := rfl

/-- The same actual ambient form restricted to the original complement. -/
def actualComplementLogarithmicOneForm (H : ι) (x : A.Complement) :
    (Fin d → ℂ) [⋀^Fin 1]→L[ℝ] ℂ :=
  A.actualAmbientLogarithmicOneForm H x.val

/-- The derivative of the original equation is the original normal. -/
theorem actualAffineEquationFunction_hasFDerivAt
    (H : ι) (x : Fin d → ℂ) :
    HasFDerivAt (A.actualAffineEquationFunction H) (A.actualNormalRealCLM H) x := by
  simpa only [actualAffineEquationFunction, actualNormalRealCLM_apply] using
    (A.actualNormalRealCLM H).hasFDerivAt.sub_const (A.offset H)

/-- The actual logarithmic form is smooth on the original open complement. -/
theorem actualAmbientLogarithmicOneForm_contDiffOn (H : ι) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (A.actualAmbientLogarithmicOneForm H)
      A.ambientComplementSet := by
  have hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (A.actualAffineEquationFunction H)
      A.ambientComplementSet := by
    simpa only [actualAffineEquationFunction, actualNormalRealCLM_apply] using
      ((A.actualNormalRealCLM H).contDiff.sub contDiff_const).contDiffOn
  have hne : ∀ x ∈ A.ambientComplementSet, A.actualAffineEquationFunction H x ≠ 0 := by
    intro x hx
    exact sub_ne_zero.mpr (hx H)
  exact (hf.inv hne).smul_const (A.actualNormalRealOneForm H)

/-- The actual Fréchet derivative is obtained from inverse differentiation,
rather than included in a closedness specification. -/
theorem actualAmbientLogarithmicOneForm_hasFDerivAt
    (H : ι) (x : Fin d → ℂ)
    (hx : A.actualAffineEquationFunction H x ≠ 0) :
    HasFDerivAt (A.actualAmbientLogarithmicOneForm H)
      (((-ContinuousLinearMap.mulLeftRight ℝ ℂ
          (A.actualAffineEquationFunction H x)⁻¹
          (A.actualAffineEquationFunction H x)⁻¹).comp
        (A.actualNormalRealCLM H)).smulRight (A.actualNormalRealOneForm H)) x := by
  exact ((hasFDerivAt_inv' (𝕜 := ℝ) hx).comp x
    (A.actualAffineEquationFunction_hasFDerivAt H x)).smul_const
      (A.actualNormalRealOneForm H)

/-- Genuine native exterior differentiation vanishes off the original
hyperplane: the derivative expression is symmetric in its two tangent
vectors, so its alternation is zero. -/
theorem actualAmbientLogarithmicOneForm_extDeriv_eq_zero
    (H : ι) (x : Fin d → ℂ)
    (hx : A.actualAffineEquationFunction H x ≠ 0) :
    extDeriv (A.actualAmbientLogarithmicOneForm H) x = 0 := by
  rw [extDeriv, (A.actualAmbientLogarithmicOneForm_hasFDerivAt H x hx).fderiv]
  ext v
  have hremove0 : (0 : Fin 2).removeNth v (0 : Fin 1) = v 1 := rfl
  have hremove1 : (1 : Fin 2).removeNth v (0 : Fin 1) = v 0 := rfl
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  change (∑ i : Fin 2, (-1 : ℤ) ^ i.val •
    ((((-ContinuousLinearMap.mulLeftRight ℝ ℂ
          (A.actualAffineEquationFunction H x)⁻¹
          (A.actualAffineEquationFunction H x)⁻¹).comp
        (A.actualNormalRealCLM H)).smulRight (A.actualNormalRealOneForm H))
      (v i) (i.removeNth v))) = 0
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_zsmul, neg_zsmul, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, ContinuousAlternatingMap.smul_apply,
    actualNormalRealOneForm, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    hremove0, hremove1,
    actualNormalRealCLM_apply, smul_eq_mul]
  ring

/-- Closedness with the actual open-complement exterior derivative. -/
theorem actualAmbientLogarithmicOneForm_extDerivWithin_eq_zero
    (H : ι) (x : Fin d → ℂ) (hx : x ∈ A.ambientComplementSet) :
    extDerivWithin (A.actualAmbientLogarithmicOneForm H) A.ambientComplementSet x = 0 := by
  have hne : A.actualAffineEquationFunction H x ≠ 0 := sub_ne_zero.mpr (hx H)
  have hd := (A.actualAmbientLogarithmicOneForm_hasFDerivAt H x hne).differentiableAt
  have hu : UniqueDiffWithinAt ℝ A.ambientComplementSet x :=
    A.ambientComplementSet_isOpen.uniqueDiffWithinAt (𝕜 := ℝ) hx
  rw [extDerivWithin, hd.fderivWithin hu]
  simpa only [extDeriv] using A.actualAmbientLogarithmicOneForm_extDeriv_eq_zero H x hne

end ChenRanks.AffineArrangement
