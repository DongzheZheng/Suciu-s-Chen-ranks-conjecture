import ChenRanks.ArrangementSmoothFormComplex
import ChenRanks.ArrangementLogarithmicOtherMeridianPeriods

/-!
# Genuine linear meridian periods on the actual smooth one-form module

Forms are arbitrary elements of the same actual C-infinity one-form
module, not assigned lists of periods.  Their pullbacks to the original
angular meridians are proved continuous from native smoothness.  Native
Bochner integration then gives genuine complex-linear period maps.  The
original logarithmic generators have the actually proved diagonal period
2 pi i and off-diagonal period zero.

Vanishing on exact forms, a de Rham comparison, and surjectivity remain
separate obligations.
-/

noncomputable section

open Complex MeasureTheory

namespace ChenRanks.AffineArrangement

open OpenSmoothForms

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The true original one-form, original angular meridian, and actual
native tangent determine the integrand. -/
def actualSmoothMeridianIntegrand (H : ι) (m : A.MeridianDisk H)
    (ω : SmoothForm A.actualSmoothComplementOpen 1) (θ : ℝ) : ℂ :=
  ω ⟨A.meridianDiskAngleAmbientMap H m θ,
      A.meridianDiskAngleAmbientMap_mem_complement H m θ⟩
    (fun _ : Fin 1 => deriv (circleMap 0 m.radius) θ • m.normalVector)

/-- Actual smoothness proves actual pullback continuity; it is not
presupposed as an integrability field. -/
theorem actualSmoothMeridianIntegrand_continuous (H : ι) (m : A.MeridianDisk H)
    (ω : SmoothForm A.actualSmoothComplementOpen 1) :
    Continuous (A.actualSmoothMeridianIntegrand H m ω) := by
  let e := ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Fin d → ℂ) (F := ℂ) (0 : Fin 1)
  have ha : Continuous (A.meridianDiskAngleAmbientMap H m) :=
    (show Differentiable ℝ (A.meridianDiskAngleAmbientMap H m) from
      fun θ => (A.meridianDiskAngleAmbientMap_hasDerivAt H m θ).differentiableAt).continuous
  have hraw : Continuous (fun θ =>
      zeroExtension A.actualSmoothComplementOpen 1 ω.val
        (A.meridianDiskAngleAmbientMap H m θ)) :=
    (smooth_zeroExtension A.actualSmoothComplementOpen 1 ω).continuousOn.comp_continuous
      ha (fun θ => A.meridianDiskAngleAmbientMap_mem_complement H m θ)
  have hl : Continuous (fun θ => e.symm
      (zeroExtension A.actualSmoothComplementOpen 1 ω.val
        (A.meridianDiskAngleAmbientMap H m θ))) :=
    e.symm.continuous.comp hraw
  have ht : Continuous (fun θ => deriv (circleMap 0 m.radius) θ • m.normalVector) := by
    simp only [deriv_circleMap]
    fun_prop
  have h := hl.clm_apply ht
  apply h.congr
  intro θ
  rw [zeroExtension_apply_mem A.actualSmoothComplementOpen 1 ω.val _
    (A.meridianDiskAngleAmbientMap_mem_complement H m θ)]
  rfl

/-- Every actual smooth pullback is genuinely Bochner integrable over the
actual angular interval. -/
theorem actualSmoothMeridianIntegrand_intervalIntegrable (H : ι) (m : A.MeridianDisk H)
    (ω : SmoothForm A.actualSmoothComplementOpen 1) :
    IntervalIntegrable (A.actualSmoothMeridianIntegrand H m ω)
      volume 0 (2 * Real.pi) :=
  (A.actualSmoothMeridianIntegrand_continuous H m ω).intervalIntegrable _ _

/-- The genuine complex-linear period functional on arbitrary actual
smooth one-forms on the original complement. -/
def actualSmoothMeridianPeriod (H : ι) (m : A.MeridianDisk H) :
    SmoothForm A.actualSmoothComplementOpen 1 →ₗ[ℂ] ℂ where
  toFun ω := ∫ θ : ℝ in 0..2 * Real.pi, A.actualSmoothMeridianIntegrand H m ω θ
  map_add' ω η := by
    change (∫ θ : ℝ in 0..2 * Real.pi,
      A.actualSmoothMeridianIntegrand H m ω θ +
        A.actualSmoothMeridianIntegrand H m η θ) = _
    exact intervalIntegral.integral_add
      (A.actualSmoothMeridianIntegrand_intervalIntegrable H m ω)
      (A.actualSmoothMeridianIntegrand_intervalIntegrable H m η)
  map_smul' c ω := by
    change (∫ θ : ℝ in 0..2 * Real.pi,
      c • A.actualSmoothMeridianIntegrand H m ω θ) = _
    exact intervalIntegral.integral_smul c _

/-- The actual same distinguished logarithm has its actual computed
period, including the genuine 2 pi i normalization factor. -/
theorem actualSmoothMeridianPeriod_same_logarithm (H : ι) (m : A.MeridianDisk H) :
    A.actualSmoothMeridianPeriod H m (A.actualSmoothLogarithmicForm H) =
      logarithmicPeriodConstant := by
  change A.actualLogarithmicMeridianIntegral H m = logarithmicPeriodConstant
  exact A.actualLogarithmicMeridianIntegral_eq_two_pi_I H m

/-- Other actual original logarithms have zero genuine actual period. -/
theorem actualSmoothMeridianPeriod_other_logarithm
    (H K : ι) (m : A.MeridianDisk H) (hKH : K ≠ H) :
    A.actualSmoothMeridianPeriod H m (A.actualSmoothLogarithmicForm K) = 0 := by
  change A.actualOtherLogarithmicMeridianIntegral H K m = 0
  exact A.actualOtherLogarithmicMeridianIntegral_eq_zero H K m hKH

end ChenRanks.AffineArrangement
