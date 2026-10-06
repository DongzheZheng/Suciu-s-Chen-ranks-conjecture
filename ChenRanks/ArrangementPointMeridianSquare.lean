import ChenRanks.ArrangementPointMeridianScale
import ChenRanks.SingularPeriodicSquareCycle

/-!
# Genuine localized meridian squares in the original affine complement

Every point and hyperplane is from the original arrangement. The
localized disk is actually constructed, its small scale is proved to
fit the original avoidance neighborhood, and the scaled circle action
therefore defines a genuine periodic continuous map into the original
complement. The native singular two-cycle follows from those true edge
identities. No torus map, membership, or cycle is an input.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval
namespace ChenRanks.AffineArrangement

open SingularCohomology

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The genuinely constructed scaled local square in the original affine complement. -/
def actualPointMeridianSquare (x : Fin d → ℂ) (H : A.PointLocalizedLabels x) :
    C(I × I, A.Complement) where
  toFun p := ⟨x + ((A.actualPointMeridianScale x H : ℂ) *
      (positiveUnitCircleTraversal p.1 : ℂ)) •
        ((A.pointLocalizedArrangement x).meridianDiskPathMap H
          ((A.pointLocalizedArrangement x).actualMeridianDisk H) p.2).val, by
    intro K
    by_cases hKx : A.normal K x = A.offset K
    · let Kx : A.PointLocalizedLabels x := ⟨K, hKx⟩
      let y := (A.pointLocalizedArrangement x).meridianDiskPathMap H
        ((A.pointLocalizedArrangement x).actualMeridianDisk H) p.2
      have hy : A.normal K y.val ≠ 0 := y.property Kx
      have hc : (A.actualPointMeridianScale x H : ℂ) *
          (positiveUnitCircleTraversal p.1 : ℂ) ≠ 0 :=
        mul_ne_zero (Complex.ofReal_ne_zero.mpr (A.actualPointMeridianScale_pos x H).ne')
          (positiveUnitCircleTraversal p.1).coe_ne_zero
      rw [map_add, hKx, map_smul, smul_eq_mul]
      intro heq
      have hzero : ((A.actualPointMeridianScale x H : ℂ) *
          (positiveUnitCircleTraversal p.1 : ℂ)) * A.normal K y.val = 0 :=
        add_left_cancel (heq.trans (add_zero (A.offset K)).symm)
      exact mul_ne_zero hc hy hzero
    · apply A.actualPointAvoidanceRadius_avoids x _ _ K hKx
      rw [dist_eq_norm]
      simp only [add_sub_cancel_left]
      exact A.scaledLocalizedMeridian_norm_lt_radius x H
        (positiveUnitCircleTraversal p.1) p.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.add
      ((continuous_const.mul
        (continuous_subtype_val.comp (positiveUnitCircleTraversal.continuous.comp continuous_fst))).smul
        (continuous_subtype_val.comp
          (((A.pointLocalizedArrangement x).meridianDiskPathMap H
            ((A.pointLocalizedArrangement x).actualMeridianDisk H)).continuous.comp continuous_snd)))

theorem actualPointMeridianSquare_vertical_periodic (x : Fin d → ℂ)
    (H : A.PointLocalizedLabels x) (s : I) :
    A.actualPointMeridianSquare x H (1, s) = A.actualPointMeridianSquare x H (0, s) := by
  apply Subtype.ext
  change x + ((A.actualPointMeridianScale x H : ℂ) *
      (positiveUnitCircleTraversal 1 : ℂ)) • _ =
    x + ((A.actualPointMeridianScale x H : ℂ) *
      (positiveUnitCircleTraversal 0 : ℂ)) • _
  rw [positiveUnitCircleTraversal_one, positiveUnitCircleTraversal_zero]

theorem actualPointMeridianSquare_horizontal_periodic (x : Fin d → ℂ)
    (H : A.PointLocalizedLabels x) (t : I) :
    A.actualPointMeridianSquare x H (t, 0) = A.actualPointMeridianSquare x H (t, 1) := by
  apply Subtype.ext
  exact congrArg (fun y : (A.pointLocalizedArrangement x).Complement =>
    x + ((A.actualPointMeridianScale x H : ℂ) * (positiveUnitCircleTraversal t : ℂ)) • y.val)
      ((A.pointLocalizedArrangement x).meridianDiskPathMap_endpoints H
        ((A.pointLocalizedArrangement x).actualMeridianDisk H))

/-- Every actually constructed square point lies in the original avoidance ball. -/
theorem actualPointMeridianSquare_dist_lt_radius (x : Fin d → ℂ)
    (H : A.PointLocalizedLabels x) (p : I × I) :
    dist (A.actualPointMeridianSquare x H p).val x < A.actualPointAvoidanceRadius x := by
  change dist (x + ((A.actualPointMeridianScale x H : ℂ) *
      (positiveUnitCircleTraversal p.1 : ℂ)) •
        ((A.pointLocalizedArrangement x).meridianDiskPathMap H
          ((A.pointLocalizedArrangement x).actualMeridianDisk H) p.2).val) x < _
  rw [dist_eq_norm]
  simp only [add_sub_cancel_left]
  exact A.scaledLocalizedMeridian_norm_lt_radius x H (positiveUnitCircleTraversal p.1) p.2

/-- The original complement's native singular two-chain is a true cycle. -/
theorem boundary_actualPointMeridianSquare_eq_zero (x : Fin d → ℂ)
    (H : A.PointLocalizedLabels x) :
    ((chains ℂ A.Complement).d 2 1).hom
      (periodicSquareChain A.Complement ℂ (A.actualPointMeridianSquare x H)) = 0 :=
  boundary_periodicSquareChain_eq_zero A.Complement ℂ _
    (A.actualPointMeridianSquare_vertical_periodic x H)
    (A.actualPointMeridianSquare_horizontal_periodic x H)

end ChenRanks.AffineArrangement
