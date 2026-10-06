import ChenRanks.ArrangementCentralRadialSquare

/-!
# Genuine radial cup pairings force central isotropic directions

The original scalar-circle action gives actual singular two-cycles in
the original complement. The already calculated original cup pairing
on those cycles is the coefficient-sum determinant. Two independent
original coefficient vectors with vanishing actual cup product must
therefore both have zero total coefficient. This is the central
direction obstruction needed in comparing original resonance families.
-/

noncomputable section
namespace ChenRanks.AffineArrangement
open SingularCohomology
open scoped BigOperators
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (hcentral : ∀ H, A.offset H = 0)

include hcentral in
/-- Actual zero cup product has zero pairing on each genuine original
radial-meridian cycle, so its original coefficient determinant vanishes. -/
theorem actualCentralCup_totalCoefficient_determinant (a b : ι → ℂ)
    (hcup : A.singularCup (A.equationWindingClassMap a)
      (A.equationWindingClassMap b) = 0) (H : ι) :
    (∑ K, a K) * b H - a H * (∑ K, b K) = 0 := by
  have he := A.centralRadialMeridianSquare_coefficientCup hcentral H a b
  dsimp only at he
  rw [hcup, map_zero] at he
  exact he.symm

include hcentral in
/-- Independent actual coefficient vectors with zero actual cup cannot
have a radial component. Their independence is an explicit intermediate
condition, to be supplied by a genuine isotropic subspace. -/
theorem actualCentralCup_independent_totalCoefficients_zero
    (a b : ι → ℂ) (ha : a ≠ 0) (hab : ∀ t : ℂ, b ≠ t • a)
    (hcup : A.singularCup (A.equationWindingClassMap a)
      (A.equationWindingClassMap b) = 0) :
    (∑ H, a H) = 0 ∧ (∑ H, b H) = 0 := by
  classical
  have hdet := A.actualCentralCup_totalCoefficient_determinant hcentral a b hcup
  have hsumA : (∑ H, a H) = 0 := by
    by_contra hn
    apply hab ((∑ H, b H) / (∑ H, a H))
    funext H
    change b H = ((∑ K, b K) / (∑ K, a K)) * a H
    have he : (∑ K, a K) * b H = a H * (∑ K, b K) :=
      sub_eq_zero.mp (hdet H)
    calc
      b H = ((∑ K, a K) * b H) / (∑ K, a K) := by field_simp [hn]
      _ = (a H * (∑ K, b K)) / (∑ K, a K) := by rw [he]
      _ = ((∑ K, b K) / (∑ K, a K)) * a H := by ring
  obtain ⟨H, hH⟩ : ∃ H, a H ≠ 0 := by
    by_contra hh
    apply ha
    funext H
    exact not_not.mp ((not_exists.mp hh) H)
  have he : a H * (∑ K, b K) = 0 := by
    have hx := sub_eq_zero.mp (hdet H)
    rw [hsumA, zero_mul] at hx
    exact hx.symm
  exact ⟨hsumA, (mul_eq_zero.mp he).resolve_left hH⟩

end ChenRanks.AffineArrangement
