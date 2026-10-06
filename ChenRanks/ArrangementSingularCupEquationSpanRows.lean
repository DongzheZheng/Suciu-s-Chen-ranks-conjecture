import ChenRanks.ArrangementPointCupContraction
import ChenRanks.ArrangementEquationSpanIncidence
import ChenRanks.ExteriorContractionPairingSymmetry

/-!
# Actual singular cup relations obey original affine equation-span rows

The point realizing the original equation-span incidence is constructed
by the actual quotient-dual argument. The genuine original complement
cycle at that point detects the actual cup. Contraction symmetry then
gives the original coordinate-row sum, retaining all affine offsets.
No generic point, prescribed block detector, or kernel identification
is assumed. These are necessary row conditions, before the full kernel
comparison and H¹ spanning have been proved.
-/

noncomputable section
open scoped BigOperators

namespace ChenRanks.AffineArrangement
open SingularCohomology

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
local instance : DecidableEq ℂ := Classical.decEq ℂ
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A genuine native cup relation has zero original coordinate-row sum
over the actual hyperplanes incident to any original point. -/
theorem equationQuadraticCupKernel_point_coordinate_row_sum_zero
    (z : ⋀[ℂ]^2 (ι → ℂ)) (hz : z ∈ A.equationQuadraticCupKernel)
    (x : Fin d → ℂ) (H : A.PointLocalizedLabels x) :
    (∑ K, if A.normal K x = A.offset K then
      Koszul.coordinateExteriorRow ℂ ι H.val z K else 0) = 0 := by
  have hzero := A.equationQuadraticCupKernel_point_contraction_eq_zero z hz x H
  have heq := DFunLike.congr_fun
    (Koszul.functional_pointDeltaTwo_swap ℂ (ι → ℂ)
      (A.pointIncidentCoefficientFunctional x) (LinearMap.proj H.val)) z
  change A.pointIncidentCoefficientFunctional x
      (Koszul.coordinateExteriorRow ℂ ι H.val z) =
    -(Koszul.pointDeltaTwo ℂ (ι → ℂ) (A.pointIncidentCoefficientFunctional x) z H.val) at heq
  rw [hzero, neg_zero, A.pointIncidentCoefficientFunctional_apply] at heq
  exact heq

/-- The row condition for an original equation subspace is proved by
constructing its actual point and actual singular cycle. -/
theorem equationQuadraticCupKernel_equation_span_coordinate_row_sum_zero
    (z : ⋀[ℂ]^2 (ι → ℂ)) (hz : z ∈ A.equationQuadraticCupKernel)
    (X : Submodule ℂ (CoordinateRing (d := d)))
    (hX : (1 : CoordinateRing (d := d)) ∉ X)
    (H : ι) (hH : A.equationPolynomial H ∈ X) :
    (∑ K, if A.equationPolynomial K ∈ X then
      Koszul.coordinateExteriorRow ℂ ι H z K else 0) = 0 := by
  obtain ⟨x, hx⟩ := A.exists_actual_point_with_equation_span_incidence X hX
  let Hx : A.PointLocalizedLabels x := ⟨H, (hx H).mpr hH⟩
  have hrow := A.equationQuadraticCupKernel_point_coordinate_row_sum_zero z hz x Hx
  simpa only [hx] using hrow

end ChenRanks.AffineArrangement
