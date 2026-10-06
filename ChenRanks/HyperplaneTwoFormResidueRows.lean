import ChenRanks.HyperplaneResiduePivotDifferentials
import ChenRanks.LogarithmicMixedRegularRelations

/-!
# Actual original-hyperplane two-form residue rows

At the original hyperplane H, every other original equation has a proved
actual regular logarithm. A vanishing original mixed two-form row, together
with an actual regular-tensor remainder, therefore gives an actual relation
among the logarithms of the same pivot-restricted equations.

The true residue and the true other-equation regular lifts are instantiated
internally. The true self order is nonzero, so its common integer factor
is cancelled. No row detector, restricted-log independence, or assigned
self residue is a premise. A later exterior-coordinate decomposition is
still needed to obtain this input equality from an arbitrary original
quadratic-kernel element; this file does not claim that decomposition.
-/

noncomputable section

open scoped TensorProduct BigOperators

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance hyperplaneTwoFormResidueRowsDecidableEq : DecidableEq ι := Classical.decEq ι

local instance hyperplaneRows_commRing (H : ι) : CommRing (A.hyperplaneLocalRing H) :=
  A.hyperplaneLocalRing_commRing H

local instance hyperplaneRows_commMonoid (H : ι) : CommMonoid (A.hyperplaneLocalRing H) :=
  (hyperplaneRows_commRing A H).toCommMonoid

local instance hyperplaneRows_selfAlgebra (H : ι) :
    Algebra (A.hyperplaneLocalRing H) (A.hyperplaneLocalRing H) :=
  Algebra.id (A.hyperplaneLocalRing H)

local instance hyperplaneRows_selfModule (H : ι) :
    Module (A.hyperplaneLocalRing H) (A.hyperplaneLocalRing H) := Algebra.toModule

local instance hyperplaneRows_selfSMul (H : ι) :
    SMul (A.hyperplaneLocalRing H) (A.hyperplaneLocalRing H) :=
  (hyperplaneRows_selfAlgebra A H).toSMul

local instance hyperplaneRows_residueAlgebra (H : ι) :
    Algebra (A.hyperplaneLocalRing H) (IsLocalRing.ResidueField (A.hyperplaneLocalRing H)) :=
  IsLocalRing.ResidueField.algebra (A.hyperplaneLocalRing H)
    (R₀ := A.hyperplaneLocalRing H)

local instance hyperplaneRows_nativeLieRing (H : ι) :
    LieRing (A.hyperplaneLocalRing H) := LieRing.ofAssociativeRing

local instance hyperplaneRows_residueModule (H : ι) :
    Module (A.hyperplaneLocalRing H) (IsLocalRing.ResidueField (A.hyperplaneLocalRing H)) :=
  Algebra.toModule

local instance hyperplaneRows_residueSMul (H : ι) :
    SMul (A.hyperplaneLocalRing H) (IsLocalRing.ResidueField (A.hyperplaneLocalRing H)) :=
  (hyperplaneRows_residueAlgebra A H).toSMul

local instance hyperplaneRows_residueConstantAlgebra (H : ι) :
    Algebra ℂ (IsLocalRing.ResidueField (A.hyperplaneLocalRing H)) :=
  IsLocalRing.ResidueField.algebra (A.hyperplaneLocalRing H) (R₀ := ℂ)

local instance hyperplaneRows_residueConstantModule (H : ι) :
    Module ℂ (IsLocalRing.ResidueField (A.hyperplaneLocalRing H)) :=
  Algebra.toModule

local instance hyperplaneRows_residueConstantSMul (H : ι) :
    SMul ℂ (IsLocalRing.ResidueField (A.hyperplaneLocalRing H)) :=
  (hyperplaneRows_residueConstantAlgebra A H).toSMul

local instance hyperplaneRows_residueConstantMulAction (H : ι) :
    MulAction ℂ (IsLocalRing.ResidueField (A.hyperplaneLocalRing H)) :=
  (hyperplaneRows_residueConstantModule A H).toDistribMulAction.toMulAction

local instance hyperplaneRows_residueConstantComm (H : ι) :
    SMulCommClass ℂ ℂ (IsLocalRing.ResidueField (A.hyperplaneLocalRing H)) where
  smul_comm c e f := by
    change algebraMap ℂ (IsLocalRing.ResidueField (A.hyperplaneLocalRing H)) c *
        (algebraMap ℂ (IsLocalRing.ResidueField (A.hyperplaneLocalRing H)) e * f) =
      algebraMap ℂ (IsLocalRing.ResidueField (A.hyperplaneLocalRing H)) e *
        (algebraMap ℂ (IsLocalRing.ResidueField (A.hyperplaneLocalRing H)) c * f)
    exact @mul_left_comm _ (IsLocalRing.ResidueField.field
      (A.hyperplaneLocalRing H)).toCommRing.toCommMonoid.toCommSemigroup _ _ _

local instance hyperplaneRows_residueConstantDifferentialModule (H : ι) :
    Module ℂ Ω[IsLocalRing.ResidueField (A.hyperplaneLocalRing H)⁄ℂ] :=
  KaehlerDifferential.module' ℂ (IsLocalRing.ResidueField (A.hyperplaneLocalRing H))

local instance hyperplaneRows_localScalarComm (H : ι) :
    SMulCommClass ℂ (A.hyperplaneLocalRing H) (A.hyperplaneLocalRing H) where
  smul_comm c a b := by
    simp only [Algebra.smul_def]
    change algebraMap ℂ (A.hyperplaneLocalRing H) c * (a * b) =
      a * (algebraMap ℂ (A.hyperplaneLocalRing H) c * b)
    exact @mul_left_comm _ (hyperplaneRows_commRing A H).toCommMonoid.toCommSemigroup _ _ _

local instance hyperplaneRows_localDifferentialModule (H : ι) :
    Module (A.hyperplaneLocalRing H) Ω[A.hyperplaneLocalRing H⁄ℂ] :=
  KaehlerDifferential.module' ℂ (A.hyperplaneLocalRing H)

local instance hyperplaneRows_pivotConstantComm (j : Fin d) :
    SMulCommClass ℂ ℂ (HyperplanePivotField j) where
  smul_comm c e f := by
    change algebraMap ℂ (HyperplanePivotField j) c *
        (algebraMap ℂ (HyperplanePivotField j) e * f) =
      algebraMap ℂ (HyperplanePivotField j) e *
        (algebraMap ℂ (HyperplanePivotField j) c * f)
    exact mul_left_comm _ _ _

local instance hyperplaneRows_pivotDifferentialModule (j : Fin d) :
    Module ℂ Ω[HyperplanePivotField j⁄ℂ] :=
  KaehlerDifferential.module' ℂ (HyperplanePivotField j)

local instance hyperplaneRows_twoFormModule (H : ι) :
    Module (A.hyperplaneLocalRing H) (RationalTwoForms (d := d)) :=
  exteriorTwoFormModuleRestriction ℂ (A.hyperplaneLocalRing H) (RationalFunctionField (d := d))

local instance hyperplaneRows_twoFormSMul (H : ι) :
    SMul (A.hyperplaneLocalRing H) (RationalTwoForms (d := d)) :=
  (hyperplaneRows_twoFormModule A H).toSMul

set_option maxHeartbeats 400000 in
/-- Applying the genuine hyperplane residue to an actual original
mixed-plus-regular relation yields the exact same restricted dlog row.
Parallel restrictions are retained as actual nonzero constant units. -/
theorem hyperplaneTwoForm_relation_restricts_to_pivot_logarithmic_row
    (H : ι) (j : Fin d) (hj : A.normal H (Pi.single j 1) ≠ 0)
    (c : {K : ι // K ≠ H} → ℂ)
    (τ : Ω[A.hyperplaneLocalRing H⁄ℂ] ⊗[A.hyperplaneLocalRing H]
      Ω[A.hyperplaneLocalRing H⁄ℂ])
    (h : (∑ K : {K : ι // K ≠ H},
      algebraMap ℂ (A.hyperplaneLocalRing H) (c K) •
        exteriorWedge (k := RationalFunctionField (d := d))
          (logarithmicDifferential ℂ (RationalFunctionField (d := d)) (A.equationUnit H))
          (logarithmicDifferential ℂ (RationalFunctionField (d := d)) (A.equationUnit K.val))) +
      regularTwoFormMap ℂ (A.hyperplaneLocalRing H) (RationalFunctionField (d := d)) τ = 0) :
    ∑ K : {K : ι // K ≠ H}, c K • logarithmicDifferential ℂ (HyperplanePivotField j)
      (A.hyperplaneRestrictedEquationUnit H K.val K.property.symm j hj) = 0 := by
  classical
  let S := A.hyperplaneLocalRing H
  let F := RationalFunctionField (d := d)
  let η : {K : ι // K ≠ H} → Ω[S⁄ℂ] :=
    fun K ↦ A.hyperplaneOtherEquationRegularLog H K.val K.property.symm
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  have hactual : (∑ K : {K : ι // K ≠ H}, algebraMap ℂ S (c K) •
      exteriorWedge (k := F) (logarithmicDifferential ℂ F (A.equationUnit H))
        (KaehlerDifferential.map ℂ ℂ S F (η K))) + regularTwoFormMap ℂ S F τ = 0 := by
    have hη (K : {K : ι // K ≠ H}) : KaehlerDifferential.map ℂ ℂ S F (η K) =
        logarithmicDifferential ℂ F (A.equationUnit K.val) :=
      A.hyperplaneOtherEquationRegularLog_map_fraction H K.val K.property.symm
    have hs : (∑ K : {K : ι // K ≠ H}, algebraMap ℂ S (c K) •
        exteriorWedge (k := F) (logarithmicDifferential ℂ F (A.equationUnit H))
          (KaehlerDifferential.map ℂ ℂ S F (η K))) =
        ∑ K : {K : ι // K ≠ H}, algebraMap ℂ S (c K) •
          exteriorWedge (k := F) (logarithmicDifferential ℂ F (A.equationUnit H))
            (logarithmicDifferential ℂ F (A.equationUnit K.val)) := by
      apply Finset.sum_congr rfl
      intro K _
      exact congrArg (fun ω : Ω[F⁄ℂ] ↦ algebraMap ℂ S (c K) •
        exteriorWedge (k := F) (logarithmicDifferential ℂ F (A.equationUnit H)) ω) (hη K)
    rw [hs]
    exact h
  have hr := logarithmicMixed_regularTensor_constant_relation_restricts_to_order_relation
    ℂ S F π hπ Finset.univ c (fun _ ↦ A.equationUnit H) η τ hactual
  have hn : (localDVRUnitOrder S F (A.equationUnit H) : ℂ) ≠ 0 :=
    Int.cast_ne_zero.mpr (A.hyperplaneLocalOrder_self_ne_zero H)
  have hscaled : (localDVRUnitOrder S F (A.equationUnit H) : ℂ) •
      (∑ K : {K : ι // K ≠ H}, c K •
        KaehlerDifferential.map ℂ ℂ S (IsLocalRing.ResidueField S) (η K)) = 0 := by
    simpa only [Finset.smul_sum, smul_smul, mul_comm] using hr
  have hrestricted : ∑ K : {K : ι // K ≠ H}, c K •
      KaehlerDifferential.map ℂ ℂ S (IsLocalRing.ResidueField S) (η K) = 0 :=
    (smul_eq_zero.mp hscaled).resolve_left hn
  have hpivot := congrArg (differentialFieldLinearEquiv
    (A.hyperplaneResiduePivotAlgEquiv H j hj)) hrestricted
  have hpivot' : (∑ K : {K : ι // K ≠ H}, c K •
      differentialFieldLinearEquiv (A.hyperplaneResiduePivotAlgEquiv H j hj)
        (KaehlerDifferential.map ℂ ℂ S (IsLocalRing.ResidueField S) (η K))) = 0 := by
    simpa only [map_sum, map_smul, map_zero] using hpivot
  have hpoint (K : {K : ι // K ≠ H}) :
      differentialFieldLinearEquiv (A.hyperplaneResiduePivotAlgEquiv H j hj)
        (KaehlerDifferential.map ℂ ℂ S (IsLocalRing.ResidueField S) (η K)) =
      logarithmicDifferential ℂ (HyperplanePivotField j)
        (A.hyperplaneRestrictedEquationUnit H K.val K.property.symm j hj) :=
    A.hyperplaneOtherEquationRegularLog_restrict_pivot H K.val K.property.symm j hj
  have hsum : (∑ K : {K : ι // K ≠ H}, c K •
      differentialFieldLinearEquiv (A.hyperplaneResiduePivotAlgEquiv H j hj)
        (KaehlerDifferential.map ℂ ℂ S (IsLocalRing.ResidueField S) (η K))) =
      ∑ K : {K : ι // K ≠ H}, c K • logarithmicDifferential ℂ (HyperplanePivotField j)
        (A.hyperplaneRestrictedEquationUnit H K.val K.property.symm j hj) := by
    apply Finset.sum_congr rfl
    intro K _
    exact congrArg (fun ω : Ω[HyperplanePivotField j⁄ℂ] ↦ c K • ω) (hpoint K)
  exact hsum.symm.trans hpivot'

end ChenRanks.AffineArrangement
