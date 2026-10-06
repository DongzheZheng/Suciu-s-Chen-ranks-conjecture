import ChenRanks.ScalarGroupHolonomyComparison
import ChenRanks.ScalarGroupAssociatedGradedMap
import ChenRanks.ScalarGroupAssociatedGradedMetabelian
import ChenRanks.KoszulQuadraticMetabelianEquivalence

/-!
# Actual metabelian holonomy descent to the actual scalar Chen Lie algebra

The source uses the actual original group's cup-dual quadratic relations.
The target retains the native lower-central quotients of its actual
maximal metabelian quotient. Both genuine surjections and native Lie
derived-ideal functoriality construct the descent; neither metabelianity
nor relation annihilation is supplied as a comparison hypothesis.

The genuine original Koszul Lie model consequently has a surjective
native Lie map to this actual Chen Lie algebra. These maps do not assert
injectivity or equality of Chen and holonomy ranks.
-/

noncomputable section

namespace ChenRanks

open LieComparison

variable (k G : Type) [Field k] [CharZero k] [Group G]
variable [FiniteDimensional k (scalarLowerCentralPiece k G 0)]
variable {ι : Type*} [Fintype ι]
variable (b : _root_.Module.Basis ι k (scalarLowerCentralPiece k G 0))

/-- The original holonomy map followed by the actual original maximal
metabelian group projection. -/
def scalarHolonomyToChenGraded :
    ScalarGroupQuadraticHolonomy k G b →ₗ⁅k⁆ scalarChenAssociatedGraded k G :=
  (scalarGroupToChenGradedLieHom k G).comp (scalarHolonomyToGroupGraded k G b)

theorem scalarHolonomyToChenGraded_surjective :
    Function.Surjective (scalarHolonomyToChenGraded k G b) :=
  (scalarGroupToChenGradedLieHom_surjective k G).comp
    (scalarHolonomyToGroupGraded_surjective k G b)

/-- The original holonomy algebra's own second derived ideal is killed
because the target's actual second derived ideal has been proved zero. -/
theorem scalarHolonomySecondDerived_le_chenMap_ker :
    LieAlgebra.derivedSeries k (ScalarGroupQuadraticHolonomy k G b) 2 ≤
      (scalarHolonomyToChenGraded k G b).ker := by
  apply LieIdeal.map_eq_bot_iff.mp
  apply le_bot_iff.mp
  have h := LieIdeal.derivedSeries_map_le
    (f := scalarHolonomyToChenGraded k G b) 2
  rw [scalarChenAssociatedGraded_second_derived_eq_bot] at h
  exact h

/-- The actual native metabelian quotient of the original cup-dual
holonomy algebra is kept, with its own original derived ideal. -/
abbrev ScalarGroupHolonomyMetabelian :=
  HolonomyMetabelianQuotient k (scalarLowerCentralPiece k G 0) b
    (scalarGroupHolonomyRelations k G)

def scalarHolonomyMetabelianToChenLinear :
    ScalarGroupHolonomyMetabelian k G b →ₗ[k] scalarChenAssociatedGraded k G :=
  (LieAlgebra.derivedSeries k (ScalarGroupQuadraticHolonomy k G b) 2).toSubmodule.liftQ
    (scalarHolonomyToChenGraded k G b).toLinearMap
    (scalarHolonomySecondDerived_le_chenMap_ker k G b)

@[simp] theorem scalarHolonomyMetabelianToChenLinear_projection
    (x : ScalarGroupQuadraticHolonomy k G b) :
    scalarHolonomyMetabelianToChenLinear k G b
      (holonomyMetabelianProjection k (scalarLowerCentralPiece k G 0) b
        (scalarGroupHolonomyRelations k G) x) =
      scalarHolonomyToChenGraded k G b x :=
  Submodule.liftQ_apply _ _ _

/-- The Lie law follows on actual original quotient representatives. -/
def scalarHolonomyMetabelianToChen :
    ScalarGroupHolonomyMetabelian k G b →ₗ⁅k⁆ scalarChenAssociatedGraded k G where
  __ := scalarHolonomyMetabelianToChenLinear k G b
  map_lie' := by
    intro x y
    obtain ⟨x, rfl⟩ := holonomyMetabelianProjection_surjective k
      (scalarLowerCentralPiece k G 0) b (scalarGroupHolonomyRelations k G) x
    obtain ⟨y, rfl⟩ := holonomyMetabelianProjection_surjective k
      (scalarLowerCentralPiece k G 0) b (scalarGroupHolonomyRelations k G) y
    change scalarHolonomyMetabelianToChenLinear k G b
      ⁅holonomyMetabelianProjection k (scalarLowerCentralPiece k G 0) b
          (scalarGroupHolonomyRelations k G) x,
        holonomyMetabelianProjection k (scalarLowerCentralPiece k G 0) b
          (scalarGroupHolonomyRelations k G) y⁆ =
      ⁅scalarHolonomyMetabelianToChenLinear k G b
          (holonomyMetabelianProjection k (scalarLowerCentralPiece k G 0) b
            (scalarGroupHolonomyRelations k G) x),
        scalarHolonomyMetabelianToChenLinear k G b
          (holonomyMetabelianProjection k (scalarLowerCentralPiece k G 0) b
            (scalarGroupHolonomyRelations k G) y)⁆
    rw [← LieHom.map_lie, scalarHolonomyMetabelianToChenLinear_projection,
      scalarHolonomyMetabelianToChenLinear_projection,
      scalarHolonomyMetabelianToChenLinear_projection]
    exact LieHom.map_lie _ x y

@[simp] theorem scalarHolonomyMetabelianToChen_projection
    (x : ScalarGroupQuadraticHolonomy k G b) :
    scalarHolonomyMetabelianToChen k G b
      (holonomyMetabelianProjection k (scalarLowerCentralPiece k G 0) b
        (scalarGroupHolonomyRelations k G) x) =
      scalarHolonomyToChenGraded k G b x :=
  scalarHolonomyMetabelianToChenLinear_projection k G b x

theorem scalarHolonomyMetabelianToChen_surjective :
    Function.Surjective (scalarHolonomyMetabelianToChen k G b) := by
  intro x
  obtain ⟨y, hy⟩ := scalarHolonomyToChenGraded_surjective k G b x
  refine ⟨holonomyMetabelianProjection k (scalarLowerCentralPiece k G 0) b
    (scalarGroupHolonomyRelations k G) y, ?_⟩
  exact (scalarHolonomyMetabelianToChen_projection k G b y).trans hy

/-- The actual original cup-dual Koszul Lie model maps to the same
actual Chen target through two proved genuine native Lie equivalences. -/
def scalarKoszulModelToChen :
    Koszul.MetabelianLieModel k (scalarLowerCentralPiece k G 0)
        (scalarGroupHolonomyRelations k G) →ₗ⁅k⁆ scalarChenAssociatedGraded k G :=
  (scalarHolonomyMetabelianToChen k G b).comp
    ((holonomyMetabelianQuadraticEquiv k (scalarLowerCentralPiece k G 0) b
      (scalarGroupHolonomyRelations k G)).symm.toLieHom.comp
        (quadraticMetabelianKoszulLieEquiv k (scalarLowerCentralPiece k G 0) b
          (scalarGroupHolonomyRelations k G)).symm.toLieHom)

theorem scalarKoszulModelToChen_surjective :
    Function.Surjective (scalarKoszulModelToChen k G b) :=
  (scalarHolonomyMetabelianToChen_surjective k G b).comp
    ((holonomyMetabelianQuadraticEquiv k (scalarLowerCentralPiece k G 0) b
      (scalarGroupHolonomyRelations k G)).symm.surjective.comp
        (quadraticMetabelianKoszulLieEquiv k (scalarLowerCentralPiece k G 0) b
          (scalarGroupHolonomyRelations k G)).symm.surjective)

end ChenRanks
