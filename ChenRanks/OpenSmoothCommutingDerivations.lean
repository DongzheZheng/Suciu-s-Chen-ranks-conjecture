import ChenRanks.OpenSmoothFunctionAlgebra
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Actual directional derivations commute on the actual smooth-function ring

The derivative of the zero extension is used only on the original open
set.  There it agrees on a genuine neighborhood with the ambient
derivative function.  Native derivative locality, linear evaluation, and
symmetry of the actual second Fréchet derivative prove commutation.
No commuting-derivative or square-zero premise is supplied.
-/

noncomputable section


open scoped Topology

namespace ChenRanks.OpenSmoothFunctions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The representative of an actual derivative agrees on an actual open
neighborhood with differentiation of the original representative. -/
theorem zeroExtension_directional_eventuallyEq
    (U : TopologicalSpace.Opens E) (v : E) (f : SmoothFunction U) (x : U) :
    zeroExtension U (directional U v f).val =ᶠ[𝓝 x.val]
      (fun y => fderiv ℝ (zeroExtension U f.val) y v) := by
  filter_upwards [U.isOpen.mem_nhds x.property] with y hy
  rw [zeroExtension_apply_mem U (directional U v f).val y hy]
  rfl

/-- Genuine second differentiation: both derivations act on actual
functions on `U`, and their value is the native second ambient derivative. -/
theorem directional_twice_apply
    (U : TopologicalSpace.Opens E) (v w : E) (f : SmoothFunction U) (x : U) :
    directional U v (directional U w f) x =
      fderiv ℝ (fderiv ℝ (zeroExtension U f.val)) x.val v w := by
  change fderiv ℝ (zeroExtension U (directional U w f).val) x.val v = _
  rw [(zeroExtension_directional_eventuallyEq U w f x).fderiv_eq]
  have hdf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fderiv ℝ (zeroExtension U f.val)) U :=
    (smooth_zeroExtension U f).fderiv_of_isOpen U.isOpen (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ (zeroExtension U f.val)) x.val :=
    (hdf.contDiffAt (U.isOpen.mem_nhds x.property)).differentiableAt (by simp)
  rw [fderiv_clm_apply hd (differentiableAt_const w)]
  simp

/-- The actual coordinate differential operators commute, by actual
smooth second-derivative symmetry. -/
theorem directional_commute
    (U : TopologicalSpace.Opens E) (v w : E) (f : SmoothFunction U) :
    directional U v (directional U w f) = directional U w (directional U v f) := by
  apply Subtype.ext
  funext x
  rw [directional_twice_apply, directional_twice_apply]
  exact ((smooth_zeroExtension U f).contDiffAt (U.isOpen.mem_nhds x.property)
    |>.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top)).eq v w

/-- Commutation for the true native derivations, without changing their
underlying ring, scalar action, or original function values. -/
theorem directionalDerivation_commute
    (U : TopologicalSpace.Opens E) (v w : E) (f : SmoothFunction U) :
    directionalDerivation U v (directionalDerivation U w f) =
      directionalDerivation U w (directionalDerivation U v f) :=
  directional_commute U v w f

end ChenRanks.OpenSmoothFunctions
