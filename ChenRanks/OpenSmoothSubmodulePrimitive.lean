import ChenRanks.OpenSmoothVectorValuedPoincare
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual anchored primitives valued in an actual finite-dimensional subspace

The actual finite-dimensional target has an actual continuous linear
projection onto every actual subspace.  The projection is constructed
from a genuine complement and native finite-dimensional continuity.
Applying it to the genuinely constructed Poincare primitive preserves
the original derivative because that derivative takes values in the
actual subspace.  Thus the primitive itself has values there; this value
constraint is a proved conclusion rather than a selected-primitive input.

This supplies the true degree-raising value constraint in the local
finite flat-connection recursion.  No final parallel equation or
nilpotence conclusion is assumed.
-/

noncomputable section

namespace ChenRanks.OpenSmoothForms

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [FiniteDimensional ℝ F] [CompleteSpace F]

/-- Actual native Poincare gives a primitive valued in the actual
subspace; a genuine continuous projection enforces this value constraint
without changing its actual derivative. -/
theorem exists_anchored_vector_infiniteSmooth_primitive_in_submodule
    (s : Set E) (hs : Convex ℝ s) (hso : IsOpen s)
    (ω : E → E →L[ℝ] F)
    (hω : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ω s)
    (hclosed : ∀ x ∈ s, extDeriv (fun y =>
      ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (ω y)) x = 0)
    (P : Submodule ℝ F) (hvalues : ∀ x ∈ s, ∀ v : E, ω x v ∈ P)
    (x₀ : E) :
    ∃ f : E → F, ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f s ∧
      f x₀ = 0 ∧ (∀ x : E, f x ∈ P) ∧
      ∀ x ∈ s, HasFDerivAt f (ω x) x := by
  obtain ⟨Q, hQ⟩ := P.exists_isCompl
  let p : F →L[ℝ] F :=
    LinearMap.toContinuousLinearMap (Submodule.IsCompl.projection hQ)
  have hp_mem (y : F) : p y ∈ P := Submodule.IsCompl.projection_apply_mem hQ y
  have hp_left (y : F) (hy : y ∈ P) : p y = y := by
    exact Submodule.IsCompl.projection_apply_left hQ ⟨y, hy⟩
  obtain ⟨f, hf, hanchor, hd⟩ :=
    exists_anchored_vector_infiniteSmooth_primitive s hs hso ω hω hclosed x₀
  refine ⟨p ∘ f, p.contDiff.comp_contDiffOn hf, ?_, ?_, ?_⟩
  · change p (f x₀) = 0
    rw [hanchor, map_zero]
  · intro x
    exact hp_mem (f x)
  · intro x hx
    have h := p.hasFDerivAt.comp x (hd x hx)
    have he : p.comp (ω x) = ω x := by
      ext v
      exact hp_left (ω x v) (hvalues x hx v)
    rw [he] at h
    exact h

end ChenRanks.OpenSmoothForms
