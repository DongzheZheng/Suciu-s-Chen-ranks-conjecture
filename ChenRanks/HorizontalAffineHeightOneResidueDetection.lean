import ChenRanks.HorizontalFiniteTypeResidueDetection
import ChenRanks.ActualHeightOneOrderComparison

/-!
# Actual horizontal residue rows on normal affine height-one charts

At an actual horizontal height-one point of an actual normal Noetherian
affine chart, the actual stalk DVR structure is proved.  The actual
finite-type horizontal residue detector then gives its actual local
order relation.  The proved canonical localization comparison identifies
that order with the actual height-one prime order on the same original
scheme function field.

No DVR, local smoothness, differential restriction injectivity, local
regular lift, independence, or residue formula is a hypothesis.  The
actual chart's normal Noetherian properties, its actual prime height,
the actual structure square, and actual curve-field pullback witnesses
are retained.  These chart properties are supplied by actual normal
chart constructions; this file does not declare their global gluing or
the original coefficient-field comparison completed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

namespace ChenRanks

universe u

variable {k : Type u} [Field k] [CharZero k]
  {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- A mixed relation at an actual horizontal height-one point forces
zero coefficient rows for the actual chart prime orders on the same
scheme function field.  All local geometric detectors are derived. -/
theorem horizontal_normalAffineHeightOne_mixed_relation_has_zero_order_coefficients
    (σX : X ⟶ Spec (.of k)) [LocallyOfFiniteType σX]
    (σY : Y ⟶ Spec (.of k)) (f : X ⟶ Y)
    (hstructure : f ≫ σY = σX)
    (U : X.Opens) (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(X, U)] [IsIntegrallyClosed Γ(X, U)]
    (x : U) (hx : f x = genericPoint Y)
    (hheight : (hU.primeIdealOf x).asIdeal.height = 1)
    {ι : Type*} [Fintype ι] :
    letI : Nonempty U := ⟨x⟩
    letI : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    letI : IsDominant f := horizontalPoint_isDominant f x hx
    letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
    letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
    letI : IsScalarTower k Y.functionField X.functionField :=
      functionFieldScalarTower_of_structure_square σX σY f hstructure
    ∀ (P : Submodule k Ω[X.functionField⁄k]) [FiniteDimensional k P],
      (∀ ω : P, ∃ η : Ω[Y.functionField⁄k],
        KaehlerDifferential.map k k Y.functionField X.functionField η =
          (ω : Ω[X.functionField⁄k])) →
      ∀ (u : ι → X.functionFieldˣ)
        (β : Fin (Module.finrank k P) → ι → k),
      (∑ i, ∑ j, algebraMap k X.functionField (β i j) •
        exteriorWedge (k := X.functionField)
          (logarithmicDifferential k X.functionField (u j))
          (Module.finBasis k P i : Ω[X.functionField⁄k])) = 0 →
      ∀ i, ∑ j, β i j *
        (heightOnePrimeOrder Γ(X, U) X.functionField
          (hU.primeIdealOf x).asIdeal (hU.primeIdealOf x).isPrime hheight
          (u j : X.functionField) : k) = 0 := by
  classical
  letI : Nonempty U := ⟨x⟩
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsDominant f := horizontalPoint_isDominant f x hx
  letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
  letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
  letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
  letI : IsScalarTower k Y.functionField X.functionField :=
    functionFieldScalarTower_of_structure_square σX σY f hstructure
  intro P _ hpull u β hrelation
  letI : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    normalAffineHeightOneStalk_isDiscreteValuationRing U hU x hheight
  have hrows := horizontal_finiteType_pullback_basis_mixed_relation_has_zero_order_coefficients
    σX σY f hstructure x hx P hpull u β hrelation
  intro i
  simpa only [normalAffineHeightOneStalk_order_eq_heightOnePrimeOrder U hU x hheight]
    using hrows i

end ChenRanks
