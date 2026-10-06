import ChenRanks.DifferentialFieldTransport

/-!
# Naturality of actual curve pullbacks under actual field comparisons

The two constructed field comparisons transport the original pullback
witnesses exactly when the actual field square commutes. The equality
is proved on universal derivatives and then on their full module span.
For the normalized coefficient model, the required square is the actual
projection equality proved from the original coefficient inclusion.
-/

noncomputable section

namespace ChenRanks

variable {k L K F G : Type*} [Field k] [CharZero k]
  [Field L] [Field K] [Field F] [Field G]
  [Algebra k L] [Algebra k K] [Algebra k F] [Algebra k G]
  [Algebra L F] [IsScalarTower k L F]
  [Algebra K G] [IsScalarTower k K G]

/-- A genuinely commuting original field square commutes on all actual
absolute differentials, not only on universal derivatives. -/
theorem differentialFieldLinearEquiv_map_comp
    (eL : L ≃ₐ[k] K) (eF : F ≃ₐ[k] G)
    (h : ∀ x : L, eF (algebraMap L F x) = algebraMap K G (eL x))
    (ω : Ω[L⁄k]) :
    differentialFieldLinearEquiv eF (KaehlerDifferential.map k k L F ω) =
      KaehlerDifferential.map k k K G (differentialFieldLinearEquiv eL ω) := by
  have hω : ω ∈ Submodule.span L (Set.range (KaehlerDifferential.D k L)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hω
  · rintro _ ⟨x, rfl⟩
    simp only [KaehlerDifferential.map_D, differentialFieldLinearEquiv_D, h]
  · simp only [map_zero]
  · intro x y _ _ hx hy
    simp only [map_add, hx, hy]
  · intro r v _ hv
    rw [(KaehlerDifferential.map k k L F).map_smul,
      ← IsScalarTower.algebraMap_smul F r (KaehlerDifferential.map k k L F v),
      differentialFieldLinearEquiv_smul, differentialFieldLinearEquiv_smul,
      (KaehlerDifferential.map k k K G).map_smul,
      ← IsScalarTower.algebraMap_smul G (eL r)
        (KaehlerDifferential.map k k K G (differentialFieldLinearEquiv eL v)),
      h, hv]

/-- Original curve pullback witnesses give actual curve pullback witnesses
for the transported original subspace. -/
theorem actual_curve_pullbacks_of_original_field_square
    (eL : L ≃ₐ[k] K) (eF : F ≃ₐ[k] G)
    (h : ∀ x : L, eF (algebraMap L F x) = algebraMap K G (eL x))
    (P : Submodule k Ω[F⁄k])
    (hpull : ∀ ω : P, ∃ η : Ω[L⁄k],
      KaehlerDifferential.map k k L F η = (ω : Ω[F⁄k])) :
    ∀ ω : P.map (differentialFieldLinearEquiv eF).toLinearMap,
      ∃ η : Ω[K⁄k], KaehlerDifferential.map k k K G η = (ω : Ω[G⁄k]) := by
  intro ω
  obtain ⟨v, hv, hval⟩ := ω.property
  obtain ⟨η, hη⟩ := hpull ⟨v, hv⟩
  refine ⟨differentialFieldLinearEquiv eL η, ?_⟩
  rw [← differentialFieldLinearEquiv_map_comp eL eF h η, hη]
  exact hval

end ChenRanks
