import ChenRanks.OpenSmoothOneFormLocalExactness

/-!
# Actual vector-valued anchored smooth primitives

The native exterior derivative is used on the actual vector-valued
continuous alternating one-form.  Its vanishing yields the derivative
symmetry required by native Poincare.  The primitive is constructed by
that theorem, has the actual original derivative, and is anchored by
subtracting its actual value at the chosen point.

The codomain may be a genuine complete normed space of matrices or a
genuine complete closed subspace of such matrices.  No primitive,
parallel section, invertibility, monodromy, or cohomological comparison
is supplied as an input.
-/

noncomputable section

namespace ChenRanks.OpenSmoothForms

open ContinuousAlternatingMap

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Native vector-valued exterior differentiation is the actual
antisymmetric part of the original Frechet derivative. -/
theorem vectorExteriorDerivative_on_two_vectors
    (ω : E → E →L[ℝ] F) (x v w : E) :
    extDeriv (fun y => ContinuousAlternatingMap.ofSubsingleton ℝ E F
      (0 : Fin 1) (ω y)) x ![v, w] =
      fderiv ℝ ω x v w - fderiv ℝ ω x w v := by
  let e := ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := E) (F := F) (0 : Fin 1)
  change alternatizeUncurryFin (fderiv ℝ (e ∘ ω) x) ![v, w] = _
  rw [e.comp_fderiv, alternatizeUncurryFin_apply, Fin.sum_univ_two]
  change (1 : ℤ) • fderiv ℝ ω x v w +
    (-1 : ℤ) • fderiv ℝ ω x w v = _
  simp only [one_zsmul, neg_one_zsmul, sub_eq_add_neg]

/-- Actual native vector-valued closedness gives actual derivative
symmetry, rather than taking symmetry as a result to be supplied. -/
theorem vectorOneForm_symmetric_of_exteriorDerivative_eq_zero
    (ω : E → E →L[ℝ] F) (x : E)
    (hclosed : extDeriv (fun y => ContinuousAlternatingMap.ofSubsingleton
      ℝ E F (0 : Fin 1) (ω y)) x = 0) (v w : E) :
    fderiv ℝ ω x v w = fderiv ℝ ω x w v := by
  apply sub_eq_zero.mp
  rw [← vectorExteriorDerivative_on_two_vectors ω x v w, hclosed]
  rfl

variable [CompleteSpace F]

/-- A genuine native vector-valued C-infinity primitive is constructed
from the actual closed form on the actual convex open set. -/
theorem exists_vector_infiniteSmooth_primitive_on_convex_open
    (s : Set E) (hs : Convex ℝ s) (hso : IsOpen s)
    (ω : E → E →L[ℝ] F)
    (hω : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ω s)
    (hclosed : ∀ x ∈ s, extDeriv (fun y =>
      ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (ω y)) x = 0) :
    ∃ f : E → F, ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f s ∧
      ∀ x ∈ s, HasFDerivAt f (ω x) x := by
  have hsym : ∀ x ∈ s, ∀ v w,
      fderiv ℝ ω x v w = fderiv ℝ ω x w v := by
    intro x hx v w
    exact vectorOneForm_symmetric_of_exteriorDerivative_eq_zero
      ω x (hclosed x hx) v w
  obtain ⟨f, hf⟩ := hs.exists_forall_hasFDerivAt_of_fderiv_symmetric hso
    (hω.differentiableOn (by simp)) hsym
  refine ⟨f, ?_, hf⟩
  apply (contDiffOn_infty_iff_fderiv_of_isOpen hso).mpr
  refine ⟨fun x hx => (hf x hx).differentiableAt.differentiableWithinAt, ?_⟩
  apply hω.congr
  intro x hx
  exact (hf x hx).fderiv

/-- The same genuinely constructed primitive is anchored at the actual
chosen point.  Its actual derivative is unchanged by this subtraction. -/
theorem exists_anchored_vector_infiniteSmooth_primitive
    (s : Set E) (hs : Convex ℝ s) (hso : IsOpen s)
    (ω : E → E →L[ℝ] F)
    (hω : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ω s)
    (hclosed : ∀ x ∈ s, extDeriv (fun y =>
      ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (ω y)) x = 0)
    (x₀ : E) :
    ∃ f : E → F, ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f s ∧
      f x₀ = 0 ∧ ∀ x ∈ s, HasFDerivAt f (ω x) x := by
  obtain ⟨f, hf, hd⟩ := exists_vector_infiniteSmooth_primitive_on_convex_open
    s hs hso ω hω hclosed
  refine ⟨fun x => f x - f x₀, hf.sub contDiffOn_const, sub_self _, ?_⟩
  intro x hx
  exact (hd x hx).sub_const _

end ChenRanks.OpenSmoothForms
