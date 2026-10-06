import ChenRanks.CentralDeconeEquationClasses
import ChenRanks.SingularPullbackIdentity

/-! The actual central decone has a genuine original unit-scale section.
Its native singular pullback is consequently injective in every degree,
including the actual cup-product target. -/
noncomputable section
namespace ChenRanks.AffineArrangement
open SingularCohomology
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (hcentral : ∀ i, A.offset i = 0) (i₀ : ι)

theorem actualCentralDeconeProjection_cohomologyPullback_injective
    (k : Type) [Field k] (n : ℕ) :
    Function.Injective
      (cohomologyPullback k (A.actualCentralDeconeProjection hcentral i₀) n) :=
  cohomologyPullback_injective_of_section k
    (A.actualCentralDeconeProjection hcentral i₀)
    (A.actualCentralDeconeSection hcentral i₀)
    (A.actualCentralDeconeProjection_section hcentral i₀) n

end ChenRanks.AffineArrangement
