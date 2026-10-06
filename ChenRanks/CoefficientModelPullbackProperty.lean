import ChenRanks.CoefficientModelFieldSquare

/-!
# Exact native differential pullback property

The native differential maps and transported-subspace predicate are
elaborated here for arbitrary actual fields. The concrete coefficient
factory instantiates this exact proposition with its constructed fields
and maps. This definition adds no hypothesis or certificate.
-/

noncomputable section

namespace ChenRanks

variable {k F G : Type*} [Field k] [CharZero k] [Field F] [Field G]
  [Algebra k F] [Algebra k G]
  (L K : Type*) [Field L] [Field K] [Algebra k L] [Algebra k K]
  [Algebra L F] [IsScalarTower k L F]
  [Algebra K G] [IsScalarTower k K G]

/-- Literal native differential pullbacks for the inverse actual
original-field comparison. -/
def actualCoefficientModelPullbackProperty (eF : G ≃ₐ[k] F) : Prop :=
  ∀ (P : Submodule k Ω[F⁄k]),
    (∀ ω : P, ∃ η : Ω[L⁄k],
      KaehlerDifferential.map k k L F η = (ω : Ω[F⁄k])) →
    ∀ ω : P.map (differentialFieldLinearEquiv eF.symm).toLinearMap,
      ∃ η : Ω[K⁄k], KaehlerDifferential.map k k K G η = (ω : Ω[G⁄k])

/-- A proved actual native field identity proves the exact native
pullback property. Its entire field-square computation was proved in
the preceding generic module. -/
theorem actualCoefficientModelPullbackProperty_of_identity
    (eF : G ≃ₐ[k] F) (eL : K ≃ₐ[k] L)
    (h : eF.toRingHom.comp (algebraMap K G) =
      (algebraMap L F).comp eL.toRingHom) :
    actualCoefficientModelPullbackProperty L K eF := by
  intro P hpull
  exact actual_curve_pullbacks_of_inverse_field_identity eF eL h P hpull

end ChenRanks
