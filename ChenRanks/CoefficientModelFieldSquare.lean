import ChenRanks.DifferentialFieldNaturality

/-!
# Inverting actual coefficient-model field comparisons

A proved equality of actual native projection homomorphisms gives the
forward original-to-model square, and hence actual differential pullback
witnesses. All computations use the actual field maps and universal
differentials. This generic implication supplies no model-existence or
projection-compatibility assertion for an arrangement by itself.
-/

noncomputable section

namespace ChenRanks

section InverseSquare

variable {k L K F G : Type*} [Field k] [Field L] [Field K] [Field F] [Field G]
  [Algebra k L] [Algebra k K] [Algebra k F] [Algebra k G] [Algebra L F]

/-- The inverse comparisons turn a proved native projection identity
into the forward original-to-model field square. -/
theorem inverseComparisons_original_field_square
    (eF : G ≃ₐ[k] F) (eL : K ≃ₐ[k] L) (i : K →+* G)
    (h : eF.toRingHom.comp i = (algebraMap L F).comp eL.toRingHom)
    (x : L) :
    eF.symm (algebraMap L F x) = i (eL.symm x) := by
  apply eF.injective
  rw [eF.apply_symm_apply]
  have hx := congrArg (fun f : K →+* F ↦ f (eL.symm x)) h
  change eF (i (eL.symm x)) = algebraMap L F (eL (eL.symm x)) at hx
  rw [eL.apply_symm_apply] at hx
  exact hx.symm

end InverseSquare

section Pullbacks

variable {k L K F G : Type*} [Field k] [CharZero k]
  [Field L] [Field K] [Field F] [Field G]
  [Algebra k L] [Algebra k K] [Algebra k F] [Algebra k G]
  [Algebra L F] [IsScalarTower k L F]
  [Algebra K G] [IsScalarTower k K G]

/-- The proved native coefficient-field identity transports original
pullback witnesses under the inverse constructed comparisons. -/
theorem actual_curve_pullbacks_of_inverse_field_identity
    (eF : G ≃ₐ[k] F) (eL : K ≃ₐ[k] L)
    (h : eF.toRingHom.comp (algebraMap K G) =
      (algebraMap L F).comp eL.toRingHom)
    (P : Submodule k Ω[F⁄k])
    (hpull : ∀ ω : P, ∃ η : Ω[L⁄k],
      KaehlerDifferential.map k k L F η = (ω : Ω[F⁄k])) :
    ∀ ω : P.map (differentialFieldLinearEquiv eF.symm).toLinearMap,
      ∃ η : Ω[K⁄k], KaehlerDifferential.map k k K G η = (ω : Ω[G⁄k]) := by
  exact actual_curve_pullbacks_of_original_field_square eL.symm eF.symm
    (fun x => inverseComparisons_original_field_square eF eL (algebraMap K G) h x)
    P hpull

end Pullbacks

end ChenRanks
