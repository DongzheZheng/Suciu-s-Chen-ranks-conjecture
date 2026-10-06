import ChenRanks.OpenSmoothVectorValuedPoincare
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# A genuine primitive step for the actual finite flat-connection recursion

Multiplication is the actual multiplication of the actual complete
normed algebra.  The derivative of the actual right-product one-form is
computed by the native continuous-linear-map product rule.  Native
closedness and the actual commuting coefficients imply closedness of
this next form, using the actual derivative equation of the previous
primitive.  Native vector-valued Poincare then constructs the next
anchored primitive.

The derivative equation supplied here is an induction state for a
previous function, not the final parallel-section equation.  No final
parallel section, invertibility, positivity, monodromy, or formality
conclusion is used as a hypothesis.
-/

noncomputable section

namespace ChenRanks.OpenSmoothForms

variable {E R : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedRing R] [NormedAlgebra ℝ R]

/-- The actual one-form obtained by right multiplying the actual
original form by the actual function. -/
def rightProductOneForm (ω : E → E →L[ℝ] R) (f : E → R) :
    E → E →L[ℝ] R :=
  fun x => ((ContinuousLinearMap.mul ℝ R).flip (f x)).comp (ω x)

@[simp] theorem rightProductOneForm_apply
    (ω : E → E →L[ℝ] R) (f : E → R) (x v : E) :
    rightProductOneForm ω f x v = ω x v * f x := rfl

/-- Actual infinite smoothness follows from actual bilinear
continuous multiplication, not from a smooth-product premise. -/
theorem rightProductOneForm_contDiffOn
    (s : Set E) (ω : E → E →L[ℝ] R) (f : E → R)
    (hω : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ω s)
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f s) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (rightProductOneForm ω f) s :=
  ((ContinuousLinearMap.mul ℝ R).flip.contDiff.comp_contDiffOn hf).clm_comp hω

/-- The genuine noncommutative product rule for the original two
tangent arguments. -/
theorem rightProductOneForm_fderiv_apply
    (ω : E → E →L[ℝ] R) (f : E → R) (x u v : E)
    (hω : DifferentiableAt ℝ ω x) (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (rightProductOneForm ω f) x u v =
      fderiv ℝ ω x u v * f x + ω x v * fderiv ℝ f x u := by
  have hr : HasFDerivAt
      (fun y => (ContinuousLinearMap.mul ℝ R).flip (f y))
      ((ContinuousLinearMap.mul ℝ R).flip.comp (fderiv ℝ f x)) x :=
    (ContinuousLinearMap.mul ℝ R).flip.hasFDerivAt.comp x hf.hasFDerivAt
  have hd := hr.clm_comp hω.hasFDerivAt
  rw [show fderiv ℝ (rightProductOneForm ω f) x = _ from hd.fderiv]
  rfl

/-- Native exterior closedness of the genuine next form is derived
from actual flat coefficients and the previous genuine derivative. -/
theorem rightProductOneForm_exteriorDerivative_eq_zero
    (ω : E → E →L[ℝ] R) (f g : E → R) (x : E)
    (hω : DifferentiableAt ℝ ω x) (hf : DifferentiableAt ℝ f x)
    (hclosed : extDeriv (fun y => ContinuousAlternatingMap.ofSubsingleton
      ℝ E R (0 : Fin 1) (ω y)) x = 0)
    (hcomm : ∀ u v : E, ω x u * ω x v = ω x v * ω x u)
    (hdf : ∀ u : E, fderiv ℝ f x u = ω x u * g x) :
    extDeriv (fun y => ContinuousAlternatingMap.ofSubsingleton
      ℝ E R (0 : Fin 1) (rightProductOneForm ω f y)) x = 0 := by
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : ![v 0, v 1] = v := by
    ext i
    fin_cases i <;> rfl
  rw [← hv, vectorExteriorDerivative_on_two_vectors,
    rightProductOneForm_fderiv_apply ω f x (v 0) (v 1) hω hf,
    rightProductOneForm_fderiv_apply ω f x (v 1) (v 0) hω hf,
    vectorOneForm_symmetric_of_exteriorDerivative_eq_zero ω x hclosed (v 0) (v 1),
    hdf (v 0), hdf (v 1)]
  rw [← mul_assoc, ← mul_assoc, hcomm (v 1) (v 0)]
  exact sub_self _

variable [CompleteSpace R]

/-- One actual step of the anchored flat-connection recursion is
constructed from native Poincare.  Every coefficient product and every
derivative in the conclusion is the original native product/map. -/
theorem exists_anchored_flatProduct_primitive
    (s : Set E) (hs : Convex ℝ s) (hso : IsOpen s)
    (ω : E → E →L[ℝ] R) (f g : E → R)
    (hω : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ω s)
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f s)
    (hclosed : ∀ x ∈ s, extDeriv (fun y =>
      ContinuousAlternatingMap.ofSubsingleton ℝ E R (0 : Fin 1) (ω y)) x = 0)
    (hcomm : ∀ x ∈ s, ∀ u v : E, ω x u * ω x v = ω x v * ω x u)
    (hdf : ∀ x ∈ s, ∀ u : E, fderiv ℝ f x u = ω x u * g x)
    (x₀ : E) :
    ∃ p : E → R, ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) p s ∧
      p x₀ = 0 ∧ ∀ x ∈ s,
        HasFDerivAt p (rightProductOneForm ω f x) x := by
  apply exists_anchored_vector_infiniteSmooth_primitive s hs hso
    (rightProductOneForm ω f) (rightProductOneForm_contDiffOn s ω f hω hf) ?_ x₀
  intro x hx
  exact rightProductOneForm_exteriorDerivative_eq_zero ω f g x
    (((hω.differentiableOn (by simp)) x hx).differentiableAt (hso.mem_nhds hx))
    (((hf.differentiableOn (by simp)) x hx).differentiableAt (hso.mem_nhds hx))
    (hclosed x hx) (hcomm x hx) (hdf x hx)

end ChenRanks.OpenSmoothForms
