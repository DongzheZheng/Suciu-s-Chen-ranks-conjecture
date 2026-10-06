import ChenRanks.ProjectivePolynomialChart
import ChenRanks.AffineFunctionFieldScalars

/-!
# The original function field of the actual projective ambient

The actual standard-chart ring equivalence gives an actual fraction-ring
structure on the original rational-function field.  The actual open
immersion into the actual projective ambient is proved dominant and is a
native preimmersion, so its actual generic-stalk map is an equivalence.
The native chart structure square and the actual coordinate scalar
identity prove that both constructed comparisons preserve the original
base field.  No source function-field comparison or compatibility is an
input.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

universe u

variable (k ι : Type u) [Field k] [Finite ι]

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev projectivePolynomialOriginalFunctionField := FractionRing (MvPolynomial ι k)

/-- The original scalar action is the actual constant-polynomial map
followed by the actual polynomial fraction-ring map. -/
abbrev projectivePolynomialOriginalFieldAlgebra :
    Algebra k (projectivePolynomialOriginalFunctionField k ι) :=
  ((algebraMap (MvPolynomial ι k) (projectivePolynomialOriginalFunctionField k ι)).comp
    MvPolynomial.C).toAlgebra

/-- The actual chart-ring action on the original fraction field. -/
abbrev projectivePolynomialChartFractionAlgebra :
    Algebra (projectivePolynomialChartRing k ι) (projectivePolynomialOriginalFunctionField k ι) :=
  ((algebraMap (MvPolynomial ι k) (projectivePolynomialOriginalFunctionField k ι)).comp
    (projectivePolynomialChartEquiv k ι).toRingHom).toAlgebra

/-- The actual chart comparison derives the fraction-ring property. -/
theorem projectivePolynomialChartFraction_isFractionRing :
    letI := projectivePolynomialChartFractionAlgebra k ι
    IsFractionRing (projectivePolynomialChartRing k ι)
      (projectivePolynomialOriginalFunctionField k ι) := by
  letI := projectivePolynomialChartFractionAlgebra k ι
  exact IsFractionRing.of_ringEquiv_left (projectivePolynomialChartEquiv k ι) (fun _ => rfl)

/-- The chart-ring action respects the original constant polynomials. -/
theorem projectivePolynomialChartFraction_scalar (c : k) :
    letI := projectivePolynomialChartFractionAlgebra k ι
    letI := projectivePolynomialOriginalFieldAlgebra k ι
    algebraMap (projectivePolynomialChartRing k ι) (projectivePolynomialOriginalFunctionField k ι)
        (projectivePolynomialChartScalarHom k ι c) =
      algebraMap k (projectivePolynomialOriginalFunctionField k ι) c := by
  letI := projectivePolynomialChartFractionAlgebra k ι
  letI := projectivePolynomialOriginalFieldAlgebra k ι
  change algebraMap (MvPolynomial ι k) (projectivePolynomialOriginalFunctionField k ι)
      (projectivePolynomialChartMap k ι (projectivePolynomialChartScalarHom k ι c)) =
    algebraMap (MvPolynomial ι k) (projectivePolynomialOriginalFunctionField k ι) (MvPolynomial.C c)
  rw [projectivePolynomialChartMap_scalar]

instance projectivePolynomialChartRing_isDomain : IsDomain (projectivePolynomialChartRing k ι) :=
  Function.Injective.isDomain (projectivePolynomialChartMap k ι)
    (projectivePolynomialChartMap_injective k ι)

/-- The actual native standard-chart inclusion. -/
abbrev projectivePolynomialChartInclusion :
    Spec (.of (projectivePolynomialChartRing k ι)) ⟶ projectivePolynomialAmbient k (Option ι) :=
  Proj.awayι (projectivePolynomialGrading k (Option ι))
    (projectivePolynomialHomogenizingVariable k ι) (MvPolynomial.isHomogeneous_X k none)
    Nat.zero_lt_one

instance projectivePolynomialChartInclusion_isOpenImmersion :
    IsOpenImmersion (projectivePolynomialChartInclusion k ι) := by
  infer_instance

/-- The actual nonempty integral chart has the actual projective generic
point in its image, giving actual dominance. -/
instance projectivePolynomialChartInclusion_isDominant :
    IsDominant (projectivePolynomialChartInclusion k ι) := by
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff,
    ← genericPoint_closure (projectivePolynomialAmbient k (Option ι))]
  apply closure_mono
  exact Set.singleton_subset_iff.mpr
    ⟨genericPoint (Spec (.of (projectivePolynomialChartRing k ι))),
      genericPoint_eq_of_isOpenImmersion (projectivePolynomialChartInclusion k ι)⟩

omit [Finite ι] in
/-- Native Proj's actual chart square has exactly the actual chart
scalar ring map, with no supplied commutative-square premise. -/
theorem projectivePolynomialChartInclusion_structure :
    projectivePolynomialChartInclusion k ι ≫ projectivePolynomialScalarMorphism k (Option ι) =
      Spec.map (CommRingCat.ofHom (projectivePolynomialChartScalarHom k ι)) := by
  change Proj.awayι (projectivePolynomialGrading k (Option ι))
      (projectivePolynomialHomogenizingVariable k ι) (MvPolynomial.isHomogeneous_X k none)
      Nat.zero_lt_one ≫
    (Proj.toSpecZero (projectivePolynomialGrading k (Option ι)) ≫
      Spec.map (projectivePolynomialGradeZeroEquiv k (Option ι)).toCommRingCatIso.hom) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The actual chart generic-stalk equivalence preserves the actual
projective original-field structure, by the actual chart square. -/
def projectivePolynomialChartSourceFunctionFieldAlgEquiv :
    letI : Algebra k (projectivePolynomialAmbient k (Option ι)).functionField :=
      structureFunctionFieldAlgebra (projectivePolynomialScalarMorphism k (Option ι))
    letI : Algebra k (Spec (.of (projectivePolynomialChartRing k ι))).functionField :=
      structureFunctionFieldAlgebra
        (Spec.map (CommRingCat.ofHom (projectivePolynomialChartScalarHom k ι)))
    (projectivePolynomialAmbient k (Option ι)).functionField ≃ₐ[k]
      (Spec (.of (projectivePolynomialChartRing k ι))).functionField := by
  letI : Algebra k (projectivePolynomialAmbient k (Option ι)).functionField :=
    structureFunctionFieldAlgebra (projectivePolynomialScalarMorphism k (Option ι))
  letI : Algebra k (Spec (.of (projectivePolynomialChartRing k ι))).functionField :=
    structureFunctionFieldAlgebra
      (Spec.map (CommRingCat.ofHom (projectivePolynomialChartScalarHom k ι)))
  refine { dominantPreimmersionFunctionFieldEquiv (projectivePolynomialChartInclusion k ι) with
    commutes' := ?_ }
  intro c
  change dominantFunctionFieldMap (projectivePolynomialChartInclusion k ι)
      (structureFunctionFieldScalarHom (projectivePolynomialScalarMorphism k (Option ι)) c) =
    structureFunctionFieldScalarHom
      (Spec.map (CommRingCat.ofHom (projectivePolynomialChartScalarHom k ι))) c
  exact congrArg
    (fun h : (.of k) ⟶ (Spec (.of (projectivePolynomialChartRing k ι))).functionField => h c)
    (structureFunctionFieldScalarHom_comp_dominantFunctionFieldMap
      (Spec.map (CommRingCat.ofHom (projectivePolynomialChartScalarHom k ι)))
      (projectivePolynomialScalarMorphism k (Option ι)) (projectivePolynomialChartInclusion k ι)
      (projectivePolynomialChartInclusion_structure k ι))

/-- The actual affine-chart fraction comparison also preserves the
original actual constant-polynomial action. -/
def projectivePolynomialChartFunctionFieldAlgEquiv :
    letI : Algebra k (Spec (.of (projectivePolynomialChartRing k ι))).functionField :=
      structureFunctionFieldAlgebra
        (Spec.map (CommRingCat.ofHom (projectivePolynomialChartScalarHom k ι)))
    letI := projectivePolynomialOriginalFieldAlgebra k ι
    (Spec (.of (projectivePolynomialChartRing k ι))).functionField ≃ₐ[k]
      projectivePolynomialOriginalFunctionField k ι := by
  letI := projectivePolynomialChartFractionAlgebra k ι
  letI := projectivePolynomialChartFraction_isFractionRing k ι
  letI : Algebra k (Spec (.of (projectivePolynomialChartRing k ι))).functionField :=
    structureFunctionFieldAlgebra
      (Spec.map (CommRingCat.ofHom (projectivePolynomialChartScalarHom k ι)))
  letI := projectivePolynomialOriginalFieldAlgebra k ι
  refine { (affineCoordinateFunctionFieldEquiv (projectivePolynomialChartRing k ι)
    (projectivePolynomialOriginalFunctionField k ι)).toRingEquiv with commutes' := ?_ }
  intro c
  change affineCoordinateFunctionFieldEquiv (projectivePolynomialChartRing k ι)
      (projectivePolynomialOriginalFunctionField k ι)
      (structureFunctionFieldScalarHom
        (Spec.map (CommRingCat.ofHom (projectivePolynomialChartScalarHom k ι))) c) =
    algebraMap k (projectivePolynomialOriginalFunctionField k ι) c
  rw [affineFunctionFieldScalarHom_eq_coordinates]
  change affineCoordinateFunctionFieldEquiv (projectivePolynomialChartRing k ι)
      (projectivePolynomialOriginalFunctionField k ι)
      (algebraMap (projectivePolynomialChartRing k ι)
        (Spec (.of (projectivePolynomialChartRing k ι))).functionField
          (projectivePolynomialChartScalarHom k ι c)) =
    algebraMap k (projectivePolynomialOriginalFunctionField k ι) c
  rw [(affineCoordinateFunctionFieldEquiv (projectivePolynomialChartRing k ι)
    (projectivePolynomialOriginalFunctionField k ι)).commutes]
  exact projectivePolynomialChartFraction_scalar k ι c

/-- The actual polynomial Proj has precisely the original rational
function field, through constructed comparisons over the original k. -/
def projectivePolynomialFunctionFieldAlgEquiv :
    letI : Algebra k (projectivePolynomialAmbient k (Option ι)).functionField :=
      structureFunctionFieldAlgebra (projectivePolynomialScalarMorphism k (Option ι))
    letI := projectivePolynomialOriginalFieldAlgebra k ι
    (projectivePolynomialAmbient k (Option ι)).functionField ≃ₐ[k]
      projectivePolynomialOriginalFunctionField k ι := by
  letI : Algebra k (projectivePolynomialAmbient k (Option ι)).functionField :=
    structureFunctionFieldAlgebra (projectivePolynomialScalarMorphism k (Option ι))
  letI : Algebra k (Spec (.of (projectivePolynomialChartRing k ι))).functionField :=
    structureFunctionFieldAlgebra
      (Spec.map (CommRingCat.ofHom (projectivePolynomialChartScalarHom k ι)))
  letI := projectivePolynomialOriginalFieldAlgebra k ι
  exact (projectivePolynomialChartSourceFunctionFieldAlgEquiv k ι).trans
    (projectivePolynomialChartFunctionFieldAlgEquiv k ι)

end

end ChenRanks
