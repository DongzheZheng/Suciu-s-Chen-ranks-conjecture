import ChenRanks.GenericNormalizationScalars
import ChenRanks.NormalizationChartRegularity
import ChenRanks.RationalGraphFunctionField
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The actual normal graph model over the actual coefficient curve

The object is the native finite normalization of the actual graph image.
Its map to the curve is proper by the original proper source, actual
base change, actual closed image, and proved finite normalization. Its
function field is compared with the original source field over the
original scalar field. These properties are constructed rather than
supplied as properties of a selected model.

Only relative properness is asserted: an affine coefficient curve need
not be proper over the scalar field. The vertical-kernel argument uses
precisely this relative properness. Horizontal residue detection and
shrinking away actual vertical support remain subsequent obligations.
-/

noncomputable section

namespace ChenRanks

open AlgebraicGeometry CategoryTheory

universe u

variable {k : Type u} [Field k] [CharZero k]
  {X C : Scheme.{u}} [IsIntegral X]
  (σX : X ⟶ Spec (.of k)) (σC : C ⟶ Spec (.of k))
  [IsProper σX] [LocallyOfFiniteType σC]
  (φ : {r : X.RationalMap C // r.compHom σC = σX.toRationalMap})

/-- The graph's actual structural map is locally of finite type. -/
instance rationalGraphScalarMorphism_locallyOfFiniteType :
    LocallyOfFiniteType (rationalGraphScalarMorphism σX σC φ) := by
  rw [← rationalGraphProjectionCurve_structure]
  infer_instance

/-- The actual native normalization of the actual graph image. -/
abbrev normalizedRationalGraph : Scheme.{u} :=
  actualFiniteTypeNormalization (rationalGraphImage σX σC φ)

/-- The actual projection from the normalized graph to the curve. -/
abbrev normalizedRationalGraphToCurve : normalizedRationalGraph σX σC φ ⟶ C :=
  actualFiniteTypeNormalizationMap (rationalGraphImage σX σC φ) ≫
    rationalGraphProjectionCurve σX σC φ

/-- The original scalar structure on the actual normalized graph. -/
abbrev normalizedRationalGraphScalarMorphism :
    normalizedRationalGraph σX σC φ ⟶ Spec (.of k) :=
  actualNormalizationScalarMorphism (rationalGraphImage σX σC φ)
    (rationalGraphScalarMorphism σX σC φ)

instance normalizedRationalGraph_isIntegral :
    IsIntegral (normalizedRationalGraph σX σC φ) := by
  infer_instance

/-- Finiteness is derived for the actual normalization projection. -/
instance normalizedRationalGraphProjection_isFinite :
    IsFinite (actualFiniteTypeNormalizationMap (rationalGraphImage σX σC φ)) :=
  actualFiniteTypeNormalizationMap_isFinite (rationalGraphImage σX σC φ)
    (rationalGraphScalarMorphism σX σC φ)

instance normalizedRationalGraphScalarMorphism_locallyOfFiniteType :
    LocallyOfFiniteType (normalizedRationalGraphScalarMorphism σX σC φ) := by
  dsimp [normalizedRationalGraphScalarMorphism, actualNormalizationScalarMorphism]
  infer_instance

instance normalizedRationalGraph_isLocallyNoetherian :
    IsLocallyNoetherian (normalizedRationalGraph σX σC φ) :=
  LocallyOfFiniteType.isLocallyNoetherian
    (normalizedRationalGraphScalarMorphism σX σC φ)

/-- The actual map to the curve is proper. -/
instance normalizedRationalGraphToCurve_isProper :
    IsProper (normalizedRationalGraphToCurve σX σC φ) := by
  dsimp [normalizedRationalGraphToCurve]
  infer_instance

omit [CharZero k] [IsProper σX] in
/-- The actual structure square commutes. -/
theorem normalizedRationalGraphToCurve_structure :
    normalizedRationalGraphToCurve σX σC φ ≫ σC =
      normalizedRationalGraphScalarMorphism σX σC φ := by
  dsimp [normalizedRationalGraphToCurve, normalizedRationalGraphScalarMorphism,
    actualNormalizationScalarMorphism]
  rw [Category.assoc, rationalGraphProjectionCurve_structure]

/-- Actual generic-arrow dominance supplies actual curve dominance. -/
instance normalizedRationalGraphToCurve_isDominant
    [IsDominant (rationalGraphGenericArrow σX σC φ)] :
    IsDominant (normalizedRationalGraphToCurve σX σC φ) := by
  letI : IsDominant (rationalGraphProjectionCurve σX σC φ) :=
    rationalGraphProjectionCurve_isDominant σX σC φ
  dsimp [normalizedRationalGraphToCurve]
  infer_instance

/-- The constructed comparison preserves the original scalar action. -/
def normalizedRationalGraphFunctionFieldAlgEquiv :
    letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
    letI : Algebra k (normalizedRationalGraph σX σC φ).functionField :=
      structureFunctionFieldAlgebra (normalizedRationalGraphScalarMorphism σX σC φ)
    (normalizedRationalGraph σX σC φ).functionField ≃ₐ[k] X.functionField := by
  letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
  letI : Algebra k (rationalGraphImage σX σC φ).functionField :=
    structureFunctionFieldAlgebra (rationalGraphScalarMorphism σX σC φ)
  letI : Algebra k (normalizedRationalGraph σX σC φ).functionField :=
    structureFunctionFieldAlgebra (normalizedRationalGraphScalarMorphism σX σC φ)
  exact (actualNormalizationFunctionFieldAlgEquiv
    (rationalGraphImage σX σC φ) (rationalGraphScalarMorphism σX σC φ)).trans
    (rationalGraphImageFunctionFieldAlgEquiv σX σC φ)

end ChenRanks
