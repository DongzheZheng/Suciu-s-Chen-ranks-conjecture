import ChenRanks.OpenSmoothDifferentialForms
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Actual smooth closed one-forms have actual local smooth primitives

The native exterior derivative of a genuine continuous one-form is
computed on two tangent vectors.  Its vanishing gives the symmetry needed
by the native convex Poincare theorem.  That theorem constructs the
primitive; its genuine derivative is the original form, so the native
infinite-smoothness criterion proves the primitive is C-infinity.

The final theorem applies this mechanism to the original native smooth
form module on an actual open set, with an actual ball chosen inside that
open set.  No primitive, symmetry, local exactness, de Rham comparison, or
cohomological equivalence is supplied as an input.
-/

noncomputable section

open scoped Topology

namespace ChenRanks.OpenSmoothForms

open ContinuousAlternatingMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The true native degree-one exterior derivative is the actual
antisymmetric part of the original Frechet derivative. -/
theorem exteriorDerivative_of_oneForm_on_two_vectors
    (ω : E → E →L[ℝ] ℂ) (x v w : E) :
    extDeriv (fun y => ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ
      (0 : Fin 1) (ω y)) x ![v, w] =
      fderiv ℝ ω x v w - fderiv ℝ ω x w v := by
  let e := ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ) (0 : Fin 1)
  change alternatizeUncurryFin (fderiv ℝ (e ∘ ω) x) ![v, w] = _
  rw [e.comp_fderiv, alternatizeUncurryFin_apply, Fin.sum_univ_two]
  change (1 : ℤ) • fderiv ℝ ω x v w +
    (-1 : ℤ) • fderiv ℝ ω x w v = _
  simp only [one_zsmul, neg_one_zsmul, sub_eq_add_neg]

/-- Actual native exterior closedness gives the true symmetry condition,
without taking symmetry as a separate premise. -/
theorem oneForm_derivative_symmetric_of_exteriorDerivative_eq_zero
    (ω : E → E →L[ℝ] ℂ) (x : E)
    (hclosed : extDeriv (fun y => ContinuousAlternatingMap.ofSubsingleton
      ℝ E ℂ (0 : Fin 1) (ω y)) x = 0) (v w : E) :
    fderiv ℝ ω x v w = fderiv ℝ ω x w v := by
  apply sub_eq_zero.mp
  rw [← exteriorDerivative_of_oneForm_on_two_vectors ω x v w, hclosed]
  rfl

/-- The primitive is genuinely constructed by native Poincare, and its
infinite smoothness follows from its actual derivative. -/
theorem exists_infiniteSmooth_primitive_on_convex_open
    (s : Set E) (hs : Convex ℝ s) (hso : IsOpen s)
    (ω : E → E →L[ℝ] ℂ) (hω : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ω s)
    (hclosed : ∀ x ∈ s, extDeriv (fun y =>
      ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1) (ω y)) x = 0) :
    ∃ f : E → ℂ, ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f s ∧
      ∀ x ∈ s, HasFDerivAt f (ω x) x := by
  have hsym : ∀ x ∈ s, ∀ v w,
      fderiv ℝ ω x v w = fderiv ℝ ω x w v := by
    intro x hx v w
    exact oneForm_derivative_symmetric_of_exteriorDerivative_eq_zero
      ω x (hclosed x hx) v w
  obtain ⟨f, hf⟩ := hs.exists_forall_hasFDerivAt_of_fderiv_symmetric hso
    (hω.differentiableOn (by simp)) hsym
  refine ⟨f, ?_, hf⟩
  apply (contDiffOn_infty_iff_fderiv_of_isOpen hso).mpr
  refine ⟨fun x hx => (hf x hx).differentiableAt.differentiableWithinAt, ?_⟩
  apply hω.congr
  intro x hx
  exact (hf x hx).fderiv

/-- A closed element of the actual original smooth-form module has a
genuine C-infinity primitive on a genuine ball inside its original open
domain.  The returned derivative is the same native original form. -/
theorem actualClosedOneForm_exists_local_infiniteSmooth_primitive
    (U : TopologicalSpace.Opens E) (ω : SmoothForm U 1)
    (hclosed : differential U 1 ω = 0) (x : U) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball x.val r ⊆ U ∧
      ∃ f : E → ℂ, ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f (Metric.ball x.val r) ∧
        ∀ y ∈ Metric.ball x.val r,
          HasFDerivAt f
            ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ)
              (0 : Fin 1)).symm (zeroExtension U 1 ω.val y)) y := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp U.isOpen x.val x.property
  let e := ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ) (0 : Fin 1)
  let η : E → E →L[ℝ] ℂ := e.symm ∘ zeroExtension U 1 ω.val
  have hη : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) η U := by
    exact e.symm.contDiff.comp_contDiffOn (smooth_zeroExtension U 1 ω)
  have heq : (fun y => ContinuousAlternatingMap.ofSubsingleton
      ℝ E ℂ (0 : Fin 1) (η y)) = zeroExtension U 1 ω.val := by
    funext y
    exact e.apply_symm_apply _
  have hc : ∀ y ∈ Metric.ball x.val r,
      extDeriv (fun z => ContinuousAlternatingMap.ofSubsingleton
        ℝ E ℂ (0 : Fin 1) (η z)) y = 0 := by
    intro y hy
    rw [heq]
    have hyU := hball hy
    have h := congrArg (fun z : SmoothForm U 2 => z ⟨y, hyU⟩) hclosed
    exact h
  obtain ⟨f, hf, hd⟩ := exists_infiniteSmooth_primitive_on_convex_open
    (Metric.ball x.val r) (convex_ball x.val r) Metric.isOpen_ball
    η (hη.mono hball) hc
  exact ⟨r, hr, hball, f, hf, hd⟩

end ChenRanks.OpenSmoothForms
