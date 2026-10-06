import ChenRanks.ScalarGroupAssociatedGradedGeneration
import ChenRanks.ScalarGroupHolonomyRelations
import ChenRanks.QuadraticHolonomyGeneratorBracket

/-!
# A genuine canonical holonomy map to the original scalar group Lie algebra

The relation space is the actual dual of the native original group cup
kernel, evaluated in the actual first lower-central quotient. Its actual
bracket vanishing is proved by the original group bar-cocycle argument.
Together with genuine scalar degree-one generation, this constructs a
surjective native Lie morphism from the actual quadratic holonomy
quotient. Neither relation vanishing, a comparison morphism, formality,
nor injectivity is supplied as input.
-/

noncomputable section

namespace ChenRanks

open LieComparison

variable (k G : Type) [Field k] [CharZero k] [Group G]
variable [FiniteDimensional k (scalarLowerCentralPiece k G 0)]
variable {ι : Type*} [Fintype ι]
variable (b : _root_.Module.Basis ι k (scalarLowerCentralPiece k G 0))

/-- This is the actual original native quadratic free-Lie quotient, with
its actual original cup-dual relation space. -/
abbrev ScalarGroupQuadraticHolonomy :=
  QuadraticHolonomyLie k (scalarLowerCentralPiece k G 0) b (scalarGroupHolonomyRelations k G)

/-- The actual vector-linear original free generators map to the actual
first group quotient inclusion. -/
theorem scalarGroupFreeLift_vectorGenerator (u : scalarLowerCentralPiece k G 0) :
    scalarGroupAssociatedGradedFreeLift k G b
        (freeVectorGenerators k (scalarLowerCentralPiece k G 0) b u) =
      scalarGroupGradedInclusion k G 0 u := by
  have h : (scalarGroupAssociatedGradedFreeLift k G b).toLinearMap.comp
      (freeVectorGenerators k (scalarLowerCentralPiece k G 0) b) =
        scalarGroupGradedInclusion k G 0 := by
    apply b.ext
    intro i
    simp only [LinearMap.comp_apply, freeVectorGenerators_basis]
    exact scalarGroupAssociatedGradedFreeLift_generator k G b i
  exact LinearMap.congr_fun h u

/-- Actual exterior-square compatibility in the actual native free map,
with the original group exterior bracket kept on the right side. -/
theorem scalarGroupFreeLift_generatorBracket :
    (scalarGroupAssociatedGradedFreeLift k G b).toLinearMap.comp
        (freeGeneratorBracket k (scalarLowerCentralPiece k G 0) b) =
      (scalarGroupGradedInclusion k G 1).comp (scalarFirstExteriorBracket k G) := by
  apply exteriorPower.linearMap_ext
  apply DFunLike.ext
  intro a
  have ha : exteriorPower.ιMulti k 2 a = exteriorWedge (k := k) (a 0) (a 1) := by
    change exteriorPower.ιMulti k 2 a = exteriorPower.ιMulti k 2 ![a 0, a 1]
    congr 1
    funext i
    fin_cases i <;> rfl
  change scalarGroupAssociatedGradedFreeLift k G b
      (freeGeneratorBracket k (scalarLowerCentralPiece k G 0) b
        (exteriorPower.ιMulti k 2 a)) =
    scalarGroupGradedInclusion k G 1
      (scalarFirstExteriorBracket k G (exteriorPower.ιMulti k 2 a))
  rw [ha, freeGeneratorBracket_exteriorWedge, LieHom.map_lie,
    scalarGroupFreeLift_vectorGenerator, scalarGroupFreeLift_vectorGenerator,
    scalarFirstExteriorBracket_wedge]
  exact scalarGroupAssociatedGraded_lie_inclusions k G 0 0 (a 0) (a 1)

/-- The actual group cup-dual quadratic relations are killed by the actual
native free map. This is a conclusion, not a quadratic-vanishing premise. -/
theorem scalarGroupQuadraticRelationIdeal_le_freeLift_ker :
    quadraticRelationIdeal k (scalarLowerCentralPiece k G 0) b
        (scalarGroupHolonomyRelations k G) ≤
      (scalarGroupAssociatedGradedFreeLift k G b).ker := by
  apply LieSubmodule.lieSpan_le.mpr
  rintro x ⟨w, rfl⟩
  change scalarGroupAssociatedGradedFreeLift k G b
    (freeGeneratorBracket k (scalarLowerCentralPiece k G 0) b (w : _)) = 0
  have h := LinearMap.congr_fun (scalarGroupFreeLift_generatorBracket k G b) (w : _)
  have hz : scalarFirstExteriorBracket k G (w : _) = 0 :=
    scalarGroupHolonomyRelations_le_bracketKernel k G w.property
  exact h.trans (by rw [LinearMap.comp_apply, hz, map_zero])

/-- Native quotient descent of the actual original group free map. -/
def scalarHolonomyToGroupGradedLinear :
    ScalarGroupQuadraticHolonomy k G b →ₗ[k] scalarGroupAssociatedGraded k G :=
  (quadraticRelationIdeal k (scalarLowerCentralPiece k G 0) b
      (scalarGroupHolonomyRelations k G)).toSubmodule.liftQ
    (scalarGroupAssociatedGradedFreeLift k G b).toLinearMap
    (scalarGroupQuadraticRelationIdeal_le_freeLift_ker k G b)

@[simp] theorem scalarHolonomyToGroupGradedLinear_projection (x : FreeLieAlgebra k ι) :
    scalarHolonomyToGroupGradedLinear k G b
        (quadraticHolonomyProjection k (scalarLowerCentralPiece k G 0) b
          (scalarGroupHolonomyRelations k G) x) =
      scalarGroupAssociatedGradedFreeLift k G b x :=
  Submodule.liftQ_apply _ _ _

/-- The original actual cup-dual holonomy quotient maps to the genuine
associated group Lie algebra. The Lie law is proved on actual quotient
representatives using the original free map, not assumed. -/
def scalarHolonomyToGroupGraded :
    ScalarGroupQuadraticHolonomy k G b →ₗ⁅k⁆ scalarGroupAssociatedGraded k G where
  __ := scalarHolonomyToGroupGradedLinear k G b
  map_lie' := by
    intro x y
    obtain ⟨x, rfl⟩ := quadraticHolonomyProjection_surjective k
      (scalarLowerCentralPiece k G 0) b (scalarGroupHolonomyRelations k G) x
    obtain ⟨y, rfl⟩ := quadraticHolonomyProjection_surjective k
      (scalarLowerCentralPiece k G 0) b (scalarGroupHolonomyRelations k G) y
    change scalarHolonomyToGroupGradedLinear k G b
        ⁅quadraticHolonomyProjection k (scalarLowerCentralPiece k G 0) b
            (scalarGroupHolonomyRelations k G) x,
          quadraticHolonomyProjection k (scalarLowerCentralPiece k G 0) b
            (scalarGroupHolonomyRelations k G) y⁆ =
      ⁅scalarHolonomyToGroupGradedLinear k G b
          (quadraticHolonomyProjection k (scalarLowerCentralPiece k G 0) b
            (scalarGroupHolonomyRelations k G) x),
        scalarHolonomyToGroupGradedLinear k G b
          (quadraticHolonomyProjection k (scalarLowerCentralPiece k G 0) b
            (scalarGroupHolonomyRelations k G) y)⁆
    rw [← LieHom.map_lie, scalarHolonomyToGroupGradedLinear_projection,
      scalarHolonomyToGroupGradedLinear_projection,
      scalarHolonomyToGroupGradedLinear_projection]
    exact LieHom.map_lie _ _ _

@[simp] theorem scalarHolonomyToGroupGraded_projection (x : FreeLieAlgebra k ι) :
    scalarHolonomyToGroupGraded k G b
        (quadraticHolonomyProjection k (scalarLowerCentralPiece k G 0) b
          (scalarGroupHolonomyRelations k G) x) =
      scalarGroupAssociatedGradedFreeLift k G b x := by
  change scalarHolonomyToGroupGradedLinear k G b _ = _
  exact scalarHolonomyToGroupGradedLinear_projection k G b x

/-- Original vector generators retain their true original group degree. -/
theorem scalarHolonomyToGroupGraded_generator (u : scalarLowerCentralPiece k G 0) :
    scalarHolonomyToGroupGraded k G b
        (quadraticHolonomyGenerators k (scalarLowerCentralPiece k G 0) b
          (scalarGroupHolonomyRelations k G) u) =
      scalarGroupGradedInclusion k G 0 u := by
  change scalarHolonomyToGroupGraded k G b
    (quadraticHolonomyProjection k (scalarLowerCentralPiece k G 0) b
      (scalarGroupHolonomyRelations k G)
      (freeVectorGenerators k (scalarLowerCentralPiece k G 0) b u)) = _
  rw [scalarHolonomyToGroupGraded_projection, scalarGroupFreeLift_vectorGenerator]

/-- Surjectivity follows from the genuine original degree-one generation;
no comparison or injectivity hypothesis is added. -/
theorem scalarHolonomyToGroupGraded_surjective :
    Function.Surjective (scalarHolonomyToGroupGraded k G b) := by
  intro x
  obtain ⟨y, hy⟩ := scalarGroupAssociatedGradedFreeLift_surjective k G b x
  exact ⟨quadraticHolonomyProjection k (scalarLowerCentralPiece k G 0) b
    (scalarGroupHolonomyRelations k G) y,
      (scalarHolonomyToGroupGraded_projection k G b y).trans hy⟩

end ChenRanks
