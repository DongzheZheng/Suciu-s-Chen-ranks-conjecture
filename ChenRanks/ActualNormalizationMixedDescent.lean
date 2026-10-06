import ChenRanks.MixedRelationProperCurveDescent
import ChenRanks.FiniteAffineOpenCover
import ChenRanks.NormalizationAllAffineCharts
import ChenRanks.GenericNormalizationScalars

/-!
# Cover-free mixed differential descent on the actual normalization

The source is the native normalization of the actual finite-type
integral scheme, not a supplied normal model. Its actual finite
normalization projection proves finite type of its original scalar
structure. Actual properness over the actual compact curve proves
compactness of the source. It is therefore Noetherian, and every actual
open has a native finite affine cover. Actual all-affine normality of
the native normalization proves normality of both actual cover families.

The actual avoidance open and all actual order rows are derived inside
the proof. The only pullback input refers to the actual morphism and
actual function fields; a model's original coefficient-field comparison
supplies it. No affine cover, smooth model, normality, avoidance open,
residue detector, order kernel, or product algebraicity is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators

namespace ChenRanks

variable {Y : Scheme} [IsIntegral Y] [CompactSpace Y]

/-- On the actual normalization, every original logarithmic coefficient
of the actual mixed relation belongs to the actual curve differential
image. Both actual finite normal affine covers and all order rows are
constructed, with no cover or normality input. -/
theorem actualNormalization_mixed_relation_logarithmic_coefficients_mem_curve_range
    (Z : Scheme) [IsIntegral Z]
    (σZ : Z ⟶ Spec (.of ℂ)) [LocallyOfFiniteType σZ]
    (σY : Y ⟶ Spec (.of ℂ))
    (f : actualFiniteTypeNormalization Z ⟶ Y) [IsDominant f] [IsProper f]
    (hstructure : f ≫ σY = actualNormalizationScalarMorphism Z σZ)
    {j : Type*} [Fintype j] :
    letI : Algebra ℂ Y.functionField := structureFunctionFieldAlgebra σY
    letI : Algebra ℂ (actualFiniteTypeNormalization Z).functionField :=
      structureFunctionFieldAlgebra (actualNormalizationScalarMorphism Z σZ)
    letI : Algebra Y.functionField (actualFiniteTypeNormalization Z).functionField :=
      (dominantFunctionFieldMap f).hom.toAlgebra
    letI : IsScalarTower ℂ Y.functionField (actualFiniteTypeNormalization Z).functionField :=
      functionFieldScalarTower_of_structure_square
        (actualNormalizationScalarMorphism Z σZ) σY f hstructure
    ∀ (P : Submodule ℂ Ω[(actualFiniteTypeNormalization Z).functionField⁄ℂ])
      [FiniteDimensional ℂ P],
      (∀ ω : P, ∃ η : Ω[Y.functionField⁄ℂ],
        KaehlerDifferential.map ℂ ℂ Y.functionField
          (actualFiniteTypeNormalization Z).functionField η =
          (ω : Ω[(actualFiniteTypeNormalization Z).functionField⁄ℂ])) →
      ∀ (F : j → (actualFiniteTypeNormalization Z).functionFieldˣ)
        (β : Fin (Module.finrank ℂ P) → j → ℂ),
      (∑ i, ∑ a, algebraMap ℂ (actualFiniteTypeNormalization Z).functionField (β i a) •
        exteriorWedge (k := (actualFiniteTypeNormalization Z).functionField)
          (logarithmicDifferential ℂ (actualFiniteTypeNormalization Z).functionField (F a))
          (Module.finBasis ℂ P i :
            Ω[(actualFiniteTypeNormalization Z).functionField⁄ℂ])) = 0 →
      ∀ i, relativeLogCombination (L := ℂ) F (β i) ∈
        LinearMap.range (KaehlerDifferential.mapBaseChange ℂ Y.functionField
          (actualFiniteTypeNormalization Z).functionField) := by
  classical
  let X := actualFiniteTypeNormalization Z
  let σX := actualNormalizationScalarMorphism Z σZ
  letI : IsFinite (actualFiniteTypeNormalizationMap Z) :=
    actualFiniteTypeNormalizationMap_isFinite Z σZ
  letI : LocallyOfFiniteType σX := by
    dsimp only [σX, actualNormalizationScalarMorphism]
    infer_instance
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian σX
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  letI : IsNoetherian X := ⟨⟩
  letI : NoetherianSpace X := IsNoetherian.noetherianSpace
  letI : NoetherianSpace (⊤ : X.Opens) := NoetherianSpace.set _
  letI : CompactSpace (⊤ : X.Opens) := NoetherianSpace.compactSpace _
  letI : Algebra ℂ Y.functionField := structureFunctionFieldAlgebra σY
  letI : Algebra ℂ X.functionField := structureFunctionFieldAlgebra σX
  letI : Algebra Y.functionField X.functionField :=
    (dominantFunctionFieldMap f).hom.toAlgebra
  letI : IsScalarTower ℂ Y.functionField X.functionField :=
    functionFieldScalarTower_of_structure_square σX σY f hstructure
  intro P _ hpull F β hrelation
  let U := actualNonemptyAffineCoverOpen X (⊤ : X.Opens)
  letI : Fintype (actualNonemptyAffineCoverIndex X (⊤ : X.Opens)) := Fintype.ofFinite _
  have hU : ∀ d, IsAffineOpen (U d) :=
    actualNonemptyAffineCoverOpen_isAffine X (⊤ : X.Opens)
  letI : ∀ d, Nonempty (U d) :=
    actualNonemptyAffineCoverOpen_nonempty X (⊤ : X.Opens)
  letI : ∀ d, IsNoetherianRing Γ(X, U d) :=
    fun d ↦ IsLocallyNoetherian.component_noetherian ⟨U d, hU d⟩
  letI : ∀ d, IsIntegrallyClosed Γ(X, U d) :=
    fun d ↦ actualNormalizationAffineSections_isIntegrallyClosed Z σZ (U d) (hU d)
  have hcoverU : (⊤ : X.Opens) ≤ iSup U :=
    actualNonemptyAffineCoverOpen_cover X (⊤ : X.Opens)
  let W := actualVerticalSupportAvoidanceOpen f U hU F
  letI : NoetherianSpace (f ⁻¹ᵁ W) := NoetherianSpace.set _
  letI : CompactSpace (f ⁻¹ᵁ W) := NoetherianSpace.compactSpace _
  let V := actualNonemptyAffineCoverOpen X (f ⁻¹ᵁ W)
  have hV : ∀ d, IsAffineOpen (V d) :=
    actualNonemptyAffineCoverOpen_isAffine X (f ⁻¹ᵁ W)
  letI : ∀ d, Nonempty (V d) :=
    actualNonemptyAffineCoverOpen_nonempty X (f ⁻¹ᵁ W)
  have hNormalV : ∀ d, IsIntegrallyClosed Γ(X, V d) :=
    fun d ↦ actualNormalizationAffineSections_isIntegrallyClosed Z σZ (V d) (hV d)
  exact mixed_relation_logarithmic_coefficients_mem_proper_curve_range
    σX σY f hstructure U hU hcoverU P hpull F β hrelation V hV hNormalV
    (actualNonemptyAffineCoverOpen_le X (f ⁻¹ᵁ W))
    (actualNonemptyAffineCoverOpen_cover X (f ⁻¹ᵁ W))

end ChenRanks
