import ChenRanks.ClosedCurveField
import ChenRanks.CurveCoefficientDifferentials
import ChenRanks.CurveRestriction

/-!
# Independent restrictions of the actual pulled-back basis

The source forms are chosen using the original pullback witnesses for a
basis of the original subspace.  Their independence follows by applying the
actual ambient differential map; it is not an extra hypothesis.  The proved
injectivity theorem for differential restriction then supplies independence
after any compatible essentially finite-type target field extension.

Constructing the embedding of the coefficient field into the function field
of a horizontal divisor is still a geometric obligation, stated transparently
as the compatible field embedding in the universal conclusion below.
-/

noncomputable section

namespace ChenRanks

section PullbackBasis

variable (C L F : Type*) [Field C] [CharZero C] [Field L] [Field F]
  [Algebra C L] [Algebra C F] [Algebra L F] [IsScalarTower C L F]

/-- Pullback witnesses for the original basis are already enough to prove
source independence and independence after actual field restriction. -/
theorem pullback_basis_exists_with_independent_restrictions
    (P : Submodule C Ω[F⁄C]) [FiniteDimensional C P]
    (hpull : ∀ ω : P, ∃ η : Ω[L⁄C],
      KaehlerDifferential.map C C L F η = (ω : Ω[F⁄C])) :
    ∃ η : Fin (Module.finrank C P) → Ω[L⁄C],
      (∀ i, KaehlerDifferential.map C C L F (η i) =
        (Module.finBasis C P i : Ω[F⁄C])) ∧
      LinearIndependent C η ∧
      ∀ (κ : Type*) [Field κ] [Algebra C κ] [Algebra L κ]
        [IsScalarTower C L κ] [Algebra.EssFiniteType C κ],
        LinearIndependent C (fun i ↦ KaehlerDifferential.map C C L κ (η i)) := by
  classical
  choose η hη using fun i ↦ hpull (Module.finBasis C P i)
  have hambient : LinearIndependent C
      (fun i ↦ (Module.finBasis C P i : Ω[F⁄C])) := by
    exact (P.subtype.linearIndependent_iff_of_injOn
      (fun x _ y _ hxy ↦ Subtype.ext hxy)).mpr (Module.finBasis C P).linearIndependent
  let f : Ω[L⁄C] →ₗ[C] Ω[F⁄C] :=
    (KaehlerDifferential.map C C L F).restrictScalars C
  have hsource : LinearIndependent C η := by
    apply LinearIndependent.of_comp f
    change LinearIndependent C (fun i ↦ KaehlerDifferential.map C C L F (η i))
    simpa only [hη] using hambient
  refine ⟨η, hη, hsource, ?_⟩
  intro κ _ _ _ _ _
  exact curveRestriction_preserves_linearIndependent_of_essFiniteType_over_base
    C L κ η hsource

end PullbackBasis

section ClosedIsotropicSpace

variable (C : Type*) [Field C] [CharZero C] [IsAlgClosed C]
variable {F : Type*} [Field F] [Algebra C F] [Algebra.EssFiniteType C F]

/-- The same actual field produced by the closed-isotropic-space theorem
has an independent source basis whose restrictions stay independent under
every compatible essentially finite-type field embedding.  No source or
restriction independence, nor a differential-injectivity hypothesis, is an
input to this theorem. -/
theorem closed_isotropic_forms_have_independent_curve_restrictions
    (P : Submodule C Ω[F⁄C]) [FiniteDimensional C P]
    (hdim : 2 ≤ Module.finrank C P)
    (hclosed : P ≤ closedRationalForms C F)
    (hisotropic : ∀ p q : P,
      exteriorWedge (k := F) (p : Ω[F⁄C]) (q : Ω[F⁄C]) = 0) :
    ∃ (h a : F) (b : Fin (Module.finrank C P) → F)
      (η : Fin (Module.finrank C P) → Ω[(curveCoefficientField C h a b)⁄C]),
      Transcendental C h ∧ a ≠ 0 ∧
      FiniteDimensional (IntermediateField.adjoin C {h})
        (curveCoefficientField C h a b) ∧
      Module.rank (curveCoefficientField C h a b)
        Ω[(curveCoefficientField C h a b)⁄C] = 1 ∧
      (∀ i, KaehlerDifferential.map C C (curveCoefficientField C h a b) F (η i) =
        (Module.finBasis C P i : Ω[F⁄C])) ∧
      LinearIndependent C η ∧
      ∀ (κ : Type*) [Field κ] [Algebra C κ] [Algebra (curveCoefficientField C h a b) κ]
        [IsScalarTower C (curveCoefficientField C h a b) κ] [Algebra.EssFiniteType C κ],
        LinearIndependent C (fun i ↦
          KaehlerDifferential.map C C (curveCoefficientField C h a b) κ (η i)) := by
  obtain ⟨h, a, b, hh, ha, hfinite, hpull⟩ :=
    closed_isotropic_forms_pull_back_from_curve_field C P hdim hclosed hisotropic
  obtain ⟨η, hη, hsource, hrestriction⟩ :=
    pullback_basis_exists_with_independent_restrictions C (curveCoefficientField C h a b)
      F P hpull
  exact ⟨h, a, b, η, hh, ha, hfinite,
    curveCoefficientField_differential_rank_eq_one C h a b hh hfinite,
    hη, hsource, hrestriction⟩

end ClosedIsotropicSpace

end ChenRanks
