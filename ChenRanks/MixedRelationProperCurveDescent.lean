import ChenRanks.NormalAffineRowsOverSupportOpen
import ChenRanks.RelativeProperVerticalComplexDifferentials

/-!
# Actual proper-curve descent directly from a mixed relation

The original finite cover constructs the actual avoidance open. A new
actual normal affine cover covers exactly its actual inverse image.
The preceding same-point residue argument proves every actual prime
order row on this new cover. The actual relatively proper generic-fibre
argument then proves that each original complex logarithmic combination
is in the actual curve differential base-change range.

There is no order-kernel, desired product algebraicity, desired fibre
annihilation, or desired differential-range hypothesis. The actual
normal affine covers and actual pullback witnesses are geometric object
data to be supplied by the actual normalized graph and curve-field
comparison constructions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators

namespace ChenRanks

variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]

/-- Every logarithmic coefficient of the actual mixed relation descends
in the differential sense to the actual relatively proper curve field.
All actual order rows and integral-product algebraicity are conclusions. -/
theorem mixed_relation_logarithmic_coefficients_mem_proper_curve_range
    (σX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType σX]
    (σY : Y ⟶ Spec (.of ℂ)) (f : X ⟶ Y) [IsDominant f] [IsProper f]
    (hstructure : f ≫ σY = σX)
    {c : Type} [Fintype c] (U : c → X.Opens)
    [∀ d, Nonempty (U d)] (hAffine : ∀ d, IsAffineOpen (U d))
    [∀ d, IsNoetherianRing Γ(X, U d)]
    [∀ d, IsIntegrallyClosed Γ(X, U d)]
    (hcover : (⊤ : X.Opens) ≤ iSup U)
    {j : Type*} [Fintype j] :
    letI : Algebra ℂ Y.functionField := structureFunctionFieldAlgebra σY
    letI : Algebra ℂ X.functionField := structureFunctionFieldAlgebra σX
    letI : Algebra Y.functionField X.functionField :=
      (dominantFunctionFieldMap f).hom.toAlgebra
    letI : IsScalarTower ℂ Y.functionField X.functionField :=
      functionFieldScalarTower_of_structure_square σX σY f hstructure
    ∀ (P : Submodule ℂ Ω[X.functionField⁄ℂ]) [FiniteDimensional ℂ P],
      (∀ ω : P, ∃ η : Ω[Y.functionField⁄ℂ],
        KaehlerDifferential.map ℂ ℂ Y.functionField X.functionField η =
          (ω : Ω[X.functionField⁄ℂ])) →
      ∀ (F : j → X.functionFieldˣ)
        (β : Fin (Module.finrank ℂ P) → j → ℂ),
      (∑ i, ∑ a, algebraMap ℂ X.functionField (β i a) •
        exteriorWedge (k := X.functionField)
          (logarithmicDifferential ℂ X.functionField (F a))
          (Module.finBasis ℂ P i : Ω[X.functionField⁄ℂ])) = 0 →
      ∀ {v : Type} (V : v → X.Opens) [∀ d, Nonempty (V d)]
        (_hV : ∀ d, IsAffineOpen (V d))
        (_hNormal : ∀ d, IsIntegrallyClosed Γ(X, V d)),
      (∀ d, V d ≤ f ⁻¹ᵁ actualVerticalSupportAvoidanceOpen f U hAffine F) →
      (f ⁻¹ᵁ actualVerticalSupportAvoidanceOpen f U hAffine F ≤ iSup V) →
      ∀ i, relativeLogCombination (L := ℂ) F (β i) ∈
        LinearMap.range (KaehlerDifferential.mapBaseChange ℂ Y.functionField X.functionField) := by
  classical
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian σX
  letI : Algebra ℂ Y.functionField := structureFunctionFieldAlgebra σY
  letI : Algebra ℂ X.functionField := structureFunctionFieldAlgebra σX
  letI : Algebra Y.functionField X.functionField :=
    (dominantFunctionFieldMap f).hom.toAlgebra
  letI : IsScalarTower ℂ Y.functionField X.functionField :=
    functionFieldScalarTower_of_structure_square σX σY f hstructure
  intro P _ hpull F β hrelation v V _ hV hNormal hVW hcoverV i
  let W := actualVerticalSupportAvoidanceOpen f U hAffine F
  letI : Nonempty W := actualVerticalSupportAvoidanceOpen_nonempty f U hAffine F
  letI : ∀ d, IsNoetherianRing Γ(X, V d) :=
    fun d ↦ IsLocallyNoetherian.component_noetherian ⟨V d, hV d⟩
  apply complex_logarithmic_combination_mem_baseChange_range_of_relative_proper_affine_order_kernel
    X V hV hNormal F σX σY f hstructure W hVW hcoverV (β i)
  intro d p hp hh
  letI : IsIntegrallyClosed Γ(X, V d) := hNormal d
  letI : IsFractionRing Γ(X, V d) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X (V d) (hV d)
  have hrows := normalAffinePrime_mixed_relation_zero_rows_over_support_open
    σX σY f hstructure U hAffine hcover P hpull F β hrelation
    (V d) (hV d) (hVW d) p hp hh
  simpa only [affineHeightOnePrimeOrder, mul_comm] using hrows i

end ChenRanks
