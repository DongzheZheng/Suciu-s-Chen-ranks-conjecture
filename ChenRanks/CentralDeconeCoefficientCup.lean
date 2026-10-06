import ChenRanks.CentralDeconeCohomologyInjection
import ChenRanks.ArrangementBoundaryCupPullbacks

/-! The genuine decone coefficient inclusion and its original native cup
comparison. Each decone coefficient multiplies the original difference
of two equation classes. A true continuous section proves the target
pullback injective; cup equality is not an input. -/
noncomputable section
open scoped BigOperators
namespace ChenRanks.AffineArrangement
open SingularCohomology
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
local instance centralDeconeCoefficientCupDecidableEq : DecidableEq ι := Classical.decEq ι
variable (i₀ : ι)

/-- The original coefficient vector for the genuine difference of
remaining equation classes and the chosen original equation class. -/
def actualCentralDeconeCoefficientInclusion :
    (A.ActualCentralDeconeLabels i₀ → ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun a := ∑ H, a H • (Pi.single H.val 1 - Pi.single i₀ 1)
  map_add' a b := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_smul, Finset.smul_sum,
      RingHom.id_apply, smul_eq_mul]

/-- The original sum-of-coefficients functional. -/
def actualCentralTotalCoefficient (_A : AffineArrangement d ι) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun a := ∑ H, a H
  map_add' a b := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]

theorem actualCentralTotalCoefficient_single (H : ι) :
    A.actualCentralTotalCoefficient (Pi.single H 1) = 1 := by
  classical
  simp [actualCentralTotalCoefficient, Pi.single_apply]

/-- Every genuine included decone direction has no radial coefficient. -/
theorem actualCentralDeconeCoefficientInclusion_total_zero
    (a : A.ActualCentralDeconeLabels i₀ → ℂ) :
    A.actualCentralTotalCoefficient (A.actualCentralDeconeCoefficientInclusion i₀ a) = 0 := by
  change A.actualCentralTotalCoefficient
    (∑ H, a H • (Pi.single H.val 1 - Pi.single i₀ 1)) = 0
  simp only [map_sum, map_smul, map_sub,
    A.actualCentralTotalCoefficient_single, sub_self, smul_zero,
    Finset.sum_const_zero]

variable (hcentral : ∀ H, A.offset H = 0)

/-- The full genuine coefficient-class map commutes with the actual
projection, from the verified individual original equation identities. -/
theorem actualCentralDeconeProjection_equationClassMap
    (a : A.ActualCentralDeconeLabels i₀ → ℂ) :
    cohomologyPullback ℂ (A.actualCentralDeconeProjection hcentral i₀) 1
      ((A.actualCentralDecone hcentral i₀).equationWindingClassMap a) =
    A.equationWindingClassMap (A.actualCentralDeconeCoefficientInclusion i₀ a) := by
  change cohomologyPullback ℂ (A.actualCentralDeconeProjection hcentral i₀) 1
    (∑ H, a H • (A.actualCentralDecone hcentral i₀).equationWindingClass ℂ H) =
    A.equationWindingClassMap
      (∑ H, a H • (Pi.single H.val 1 - Pi.single i₀ 1))
  simp only [map_sum, map_smul, map_sub,
    A.actualCentralDeconeProjection_equationClass hcentral i₀,
    A.equationWindingClassMap_single]

/-- The original cup of the genuine coefficient inclusion is the
actual pullback of the original decone cup. -/
theorem actualCentralDeconeProjection_coefficientCup
    (a b : A.ActualCentralDeconeLabels i₀ → ℂ) :
    cohomologyPullback ℂ (A.actualCentralDeconeProjection hcentral i₀) 2
      ((A.actualCentralDecone hcentral i₀).singularCup
        ((A.actualCentralDecone hcentral i₀).equationWindingClassMap a)
        ((A.actualCentralDecone hcentral i₀).equationWindingClassMap b)) =
      A.singularCup
        (A.equationWindingClassMap (A.actualCentralDeconeCoefficientInclusion i₀ a))
        (A.equationWindingClassMap (A.actualCentralDeconeCoefficientInclusion i₀ b)) := by
  rw [singularCup, cohomologyPullback_cup,
    A.actualCentralDeconeProjection_equationClassMap i₀ hcentral,
    A.actualCentralDeconeProjection_equationClassMap i₀ hcentral]

/-- The actual original cup kernel agrees in both directions on the
actual decone directions; the converse uses the true native H² injection. -/
theorem actualCentralDecone_coefficientCup_zero_iff
    (a b : A.ActualCentralDeconeLabels i₀ → ℂ) :
    A.singularCup
        (A.equationWindingClassMap (A.actualCentralDeconeCoefficientInclusion i₀ a))
        (A.equationWindingClassMap (A.actualCentralDeconeCoefficientInclusion i₀ b)) = 0 ↔
      (A.actualCentralDecone hcentral i₀).singularCup
        ((A.actualCentralDecone hcentral i₀).equationWindingClassMap a)
        ((A.actualCentralDecone hcentral i₀).equationWindingClassMap b) = 0 := by
  rw [← A.actualCentralDeconeProjection_coefficientCup i₀ hcentral]
  constructor
  · intro h
    apply A.actualCentralDeconeProjection_cohomologyPullback_injective
      hcentral i₀ ℂ 2
    rw [map_zero]
    exact h
  · intro h
    rw [h, map_zero]

end ChenRanks.AffineArrangement
