import ChenRanks.CentralDeconeComplement
import ChenRanks.NonzeroComplexWindingClassOperations
import ChenRanks.ArrangementSingularWindingClasses
import ChenRanks.SingularPullbackComposition

/-!
# Original equation classes under the genuine central decone projection

Normalizing by the chosen original equation makes each remaining equation
its genuine original quotient function. The native winding class of a
quotient is the difference of the two native winding classes. This gives
the actual degree-one cohomology formula needed for central resonance,
without a product-cohomology or Orlik--Solomon model assumption.
-/

noncomputable section
namespace ChenRanks.AffineArrangement
open SingularCohomology
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (hcentral : ∀ i, A.offset i = 0) (i₀ : ι)
local instance centralDeconeEquationClassesDecidableEq : DecidableEq ι := Classical.decEq ι

/-- The genuine projection defined by the original normalization and
the constructed actual affine coordinates. -/
def actualCentralDeconeProjection :
    C(A.Complement, (A.actualCentralDecone hcentral i₀).Complement) where
  toFun x := A.actualCentralSliceToDecone hcentral i₀ (A.centralSlicePoint hcentral i₀ x)
  continuous_toFun := (A.actualCentralSliceToDecone_continuous hcentral i₀).comp
    (A.centralSlicePoint_continuous hcentral i₀)

/-- The actual unit-scale slice section of the same original projection. -/
def actualCentralDeconeSection :
    C((A.actualCentralDecone hcentral i₀).Complement, A.Complement) where
  toFun x := A.centralRescale hcentral i₀ (A.actualDeconeToCentralSlice hcentral i₀ x, 1)
  continuous_toFun := (A.centralRescale_continuous hcentral i₀).comp
    ((A.actualDeconeToCentralSlice_continuous hcentral i₀).prodMk continuous_const)

/-- Native inverse identities prove that the actual section is a true
right inverse of the original projection. -/
theorem actualCentralDeconeProjection_section
    (x : (A.actualCentralDecone hcentral i₀).Complement) :
    A.actualCentralDeconeProjection hcentral i₀
      (A.actualCentralDeconeSection hcentral i₀ x) = x := by
  have he := congrArg Prod.fst
    ((A.centralComplementSliceHomeomorph hcentral i₀).apply_symm_apply
      (A.actualDeconeToCentralSlice hcentral i₀ x, 1))
  change A.centralSlicePoint hcentral i₀
      (A.actualCentralDeconeSection hcentral i₀ x) =
    A.actualDeconeToCentralSlice hcentral i₀ x at he
  change A.actualCentralSliceToDecone hcentral i₀
      (A.centralSlicePoint hcentral i₀
        (A.actualCentralDeconeSection hcentral i₀ x)) = x
  rw [he, A.actualCentralSliceToDecone_deconeToSlice hcentral i₀ x]

/-- The original affine decone function is the original central
function evaluated at the actual slice point, with no rescaling constant. -/
theorem actualCentralDeconeEquation_value (H : A.ActualCentralDeconeLabels i₀)
    (x : Fin (A.actualCentralDeconeDimension i₀) → ℂ) :
    (A.actualCentralDecone hcentral i₀).normal H x -
        (A.actualCentralDecone hcentral i₀).offset H =
      A.normal H.val (A.actualCentralDeconeEmbedding i₀ x) := by
  change A.normal H.val (A.actualCentralDeconeDirectionMap i₀ x) -
      (-A.normal H.val (A.actualCentralSliceBase i₀)) = _
  rw [sub_neg_eq_add, actualCentralDeconeEmbedding, map_add, add_comm]

/-- The normalized genuine point has exactly the original quotient
equation on the actual original complement. -/
theorem actualCentralDeconeProjection_nonzeroEquation
    (H : A.ActualCentralDeconeLabels i₀) :
    ((A.actualCentralDecone hcentral i₀).equationComplementNonzeroComplexMap H).comp
        (A.actualCentralDeconeProjection hcentral i₀) =
      nonzeroComplexMapQuotient (A.equationComplementNonzeroComplexMap H.val)
        (A.equationComplementNonzeroComplexMap i₀) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (A.actualCentralDecone hcentral i₀).normal H
      (A.actualCentralDeconeCoordinate i₀ (A.centralSlicePoint hcentral i₀ x).val
        (A.centralSlicePoint hcentral i₀ x).property.1) -
        (A.actualCentralDecone hcentral i₀).offset H =
    (A.normal H.val x.val - A.offset H.val) / (A.normal i₀ x.val - A.offset i₀)
  rw [A.actualCentralDeconeEquation_value hcentral i₀ H,
    A.actualCentralDeconeEmbedding_coordinate i₀
      (A.centralSlicePoint hcentral i₀ x).val (A.centralSlicePoint hcentral i₀ x).property.1]
  change A.normal H.val ((A.normal i₀ x.val)⁻¹ • x.val) = _
  rw [map_smul, smul_eq_mul, hcentral H.val, hcentral i₀, sub_zero, sub_zero]
  simp only [div_eq_mul_inv, mul_comm]

/-- The native first cohomology identity follows from the actual original
quotient function and genuine singular pullback composition. -/
theorem actualCentralDeconeProjection_equationClass
    (k : Type) [Field k] (H : A.ActualCentralDeconeLabels i₀) :
    cohomologyPullback k (A.actualCentralDeconeProjection hcentral i₀) 1
        ((A.actualCentralDecone hcentral i₀).equationWindingClass k H) =
      A.equationWindingClass k H.val - A.equationWindingClass k i₀ := by
  rw [equationWindingClass, cohomologyPullback_comp_apply]
  have he : ((A.actualCentralDecone hcentral i₀).equationComplementCircleMap H).comp
      (A.actualCentralDeconeProjection hcentral i₀) =
    nonzeroComplexCircleMap.comp
      (nonzeroComplexMapQuotient (A.equationComplementNonzeroComplexMap H.val)
        (A.equationComplementNonzeroComplexMap i₀)) := by
    apply ContinuousMap.ext
    intro x
    exact congrArg nonzeroComplexCircleMap
      (DFunLike.congr_fun (A.actualCentralDeconeProjection_nonzeroEquation hcentral i₀ H) x)
  rw [he, cohomologyPullback_nonzero_winding_quotient]
  rfl

end ChenRanks.AffineArrangement
