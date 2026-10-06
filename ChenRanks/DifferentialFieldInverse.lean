import ChenRanks.DifferentialFieldTransport

/-!
# The actual inverse differential comparison

The native differential map of the inverse field comparison is proved
to be the actual inverse of the original differential comparison. This
uses the entire span of universal derivatives, including rational
function coefficients. It is needed when moving original maximality
and zero wedge relations to and from the actual normal model.
-/

noncomputable section

namespace ChenRanks

variable {k F G : Type*} [Field k] [CharZero k] [Field F] [Field G]
  [Algebra k F] [Algebra k G]

/-- Actual inverse field maps induce actual inverse maps on all one-forms. -/
@[simp]
theorem differentialFieldLinearEquiv_inverse_apply_apply
    (e : F ≃ₐ[k] G) (ω : Ω[F⁄k]) :
    differentialFieldLinearEquiv e.symm (differentialFieldLinearEquiv e ω) = ω := by
  have hω : ω ∈ Submodule.span F (Set.range (KaehlerDifferential.D k F)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hω
  · rintro _ ⟨x, rfl⟩
    simp only [differentialFieldLinearEquiv_D, AlgEquiv.symm_apply_apply]
  · simp only [map_zero]
  · intro x y _ _ hx hy
    simp only [map_add, hx, hy]
  · intro r v _ hv
    rw [differentialFieldLinearEquiv_smul, differentialFieldLinearEquiv_smul,
      AlgEquiv.symm_apply_apply, hv]

/-- The forward composition with the native inverse comparison is also identity. -/
@[simp]
theorem differentialFieldLinearEquiv_apply_inverse_apply
    (e : F ≃ₐ[k] G) (ω : Ω[G⁄k]) :
    differentialFieldLinearEquiv e (differentialFieldLinearEquiv e.symm ω) = ω := by
  exact differentialFieldLinearEquiv_inverse_apply_apply e.symm ω

/-- The native inverse-field differential map is the actual inverse linear equivalence. -/
theorem differentialFieldLinearEquiv_inverse_eq
    (e : F ≃ₐ[k] G) :
    (differentialFieldLinearEquiv e).symm = differentialFieldLinearEquiv e.symm := by
  ext ω
  apply (differentialFieldLinearEquiv e).injective
  rw [LinearEquiv.apply_symm_apply, differentialFieldLinearEquiv_apply_inverse_apply]

end ChenRanks
