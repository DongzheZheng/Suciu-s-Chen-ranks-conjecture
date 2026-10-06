import ChenRanks.ArrangementMeridianClassIndependence
import ChenRanks.ArrangementPeriodicCupPairing
import ChenRanks.CentralSliceDeconing
import ChenRanks.NonzeroComplexPhaseMultiplication
import ChenRanks.CircleClosedPathProducts

/-!
# Actual radial squares in an original central complement

The first coordinate is the genuine complex scalar circle action on
the original central complement. The second is a genuine original loop.
Their actual product square is periodic, hence gives the already proved
native singular two-cycle. Actual equation phases and winding integers
are computed from the original normal maps; no labelled torus, cup
pairing, or linear cohomology model is supplied.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval
open scoped BigOperators

namespace ChenRanks

/-- The integer winding of the genuine positive circle traversal. -/
theorem circlePathIntegerIncrement_positiveUnitCircleTraversal :
    circlePathIntegerIncrement positiveUnitCircleTraversal = 1 := by
  exact circlePathIntegerIncrement_of_exp_path
    ⟨fun t => (2 * Real.pi) * (t : ℝ), by fun_prop⟩ 1
    (by simp) (by simp)

namespace AffineArrangement

open SingularCohomology

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (hcentral : ∀ H, A.offset H = 0)

/-- The actual unit-circle scaling of original complement points. -/
def centralCircleScaleMap : C(Circle × A.Complement, A.Complement) where
  toFun p := ⟨(p.1 : ℂ) • p.2.val, by
    intro H
    rw [map_smul, hcentral H, smul_eq_mul]
    exact mul_ne_zero p.1.coe_ne_zero
      (A.normal_ne_zero_on_central_complement hcentral p.2 H)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd)

/-- Every actual equation has the actual multiplicative phase under the original scaling. -/
theorem centralCircleScaleMap_phase (u : Circle) (x : A.Complement) (H : ι) :
    A.equationComplementCircleMap H (A.centralCircleScaleMap hcentral (u, x)) =
      u * A.equationComplementCircleMap H x := by
  have heq : A.equationComplementNonzeroComplexMap H
      (A.centralCircleScaleMap hcentral (u, x)) =
      ⟨(u : ℂ) * (A.equationComplementNonzeroComplexMap H x : ℂ),
        mul_ne_zero u.coe_ne_zero (A.equationComplementNonzeroComplexMap H x).property⟩ := by
    apply Subtype.ext
    change A.normal H ((u : ℂ) • x.val) - A.offset H =
      (u : ℂ) * (A.normal H x.val - A.offset H)
    rw [map_smul, hcentral H, sub_zero, sub_zero, smul_eq_mul]
  change nonzeroComplexCircleMap
    (A.equationComplementNonzeroComplexMap H
      (A.centralCircleScaleMap hcentral (u, x))) = _
  rw [heq, nonzeroComplexCircleMap_mul ⟨(u : ℂ), u.coe_ne_zero⟩
    (A.equationComplementNonzeroComplexMap H x), nonzeroComplexCircleMap_circle]
  rfl

/-- The genuine periodic square of original scalar action and an original loop. -/
def centralRadialSquare (γ : C(I, A.Complement)) : C(I × I, A.Complement) :=
  (A.centralCircleScaleMap hcentral).comp
    ((positiveUnitCircleTraversal.comp (⟨Prod.fst, continuous_fst⟩ : C(I × I, I))).prodMk
      (γ.comp (⟨Prod.snd, continuous_snd⟩ : C(I × I, I))))

theorem centralRadialSquare_vertical_periodic (γ : C(I, A.Complement)) (s : I) :
    A.centralRadialSquare hcentral γ (1, s) =
      A.centralRadialSquare hcentral γ (0, s) := by
  simp [centralRadialSquare]

theorem centralRadialSquare_horizontal_periodic (γ : C(I, A.Complement))
    (hγ : γ 0 = γ 1) (t : I) :
    A.centralRadialSquare hcentral γ (t, 0) =
      A.centralRadialSquare hcentral γ (t, 1) := by
  change A.centralCircleScaleMap hcentral (positiveUnitCircleTraversal t, γ 0) =
    A.centralCircleScaleMap hcentral (positiveUnitCircleTraversal t, γ 1)
  rw [hγ]

/-- The actual horizontal equation loop is the true scalar circle times its constant phase. -/
theorem centralRadialSquare_horizontal_equationPath (γ : C(I, A.Complement)) (H : ι) :
    (A.equationComplementCircleMap H).comp
        (periodicSquareHorizontalPath A.Complement (A.centralRadialSquare hcentral γ)) =
      positiveUnitCircleTraversal *
        (ContinuousMap.const I (A.equationComplementCircleMap H (γ 0))) := by
  apply ContinuousMap.ext
  intro t
  exact A.centralCircleScaleMap_phase hcentral (positiveUnitCircleTraversal t) (γ 0) H

/-- The actual vertical path is literally the original complement loop. -/
theorem centralRadialSquare_vertical_path (γ : C(I, A.Complement)) :
    periodicSquareVerticalPath A.Complement (A.centralRadialSquare hcentral γ) = γ := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  change (positiveUnitCircleTraversal 0 : ℂ) • (γ s).val = (γ s).val
  rw [positiveUnitCircleTraversal_zero, Circle.coe_one, one_smul]

/-- All genuine horizontal equation windings are one, by actual path-lift additivity. -/
theorem centralRadialSquare_horizontal_increment (γ : C(I, A.Complement)) (H : ι) :
    circlePathIntegerIncrement ((A.equationComplementCircleMap H).comp
      (periodicSquareHorizontalPath A.Complement (A.centralRadialSquare hcentral γ))) = 1 := by
  rw [A.centralRadialSquare_horizontal_equationPath hcentral γ H,
    circlePathIntegerIncrement_mul_closed _ _
      (by simp) rfl,
    circlePathIntegerIncrement_positiveUnitCircleTraversal,
    circlePathIntegerIncrement_const, add_zero]

/-- The cup pairing on the genuinely constructed radial/meridian two-cycle
has the exact original augmentation-row determinant. -/
theorem centralRadialMeridianSquare_coefficientCup
    (H : ι) (a b : ι → ℂ) :
    let γ := A.meridianDiskPathMap H (A.actualMeridianDisk H)
    let F := A.centralRadialSquare hcentral γ
    cycleEvaluation ℂ A.Complement 1 (periodicSquareChain A.Complement ℂ F)
        (boundary_periodicSquareChain_eq_zero A.Complement ℂ F
          (A.centralRadialSquare_vertical_periodic hcentral γ)
          (A.centralRadialSquare_horizontal_periodic hcentral γ
            (A.meridianDiskPathMap_endpoints H (A.actualMeridianDisk H))))
        (A.singularCup (A.equationWindingClassMap a) (A.equationWindingClassMap b)) =
      (∑ K, a K) * b H - a H * (∑ K, b K) := by
  dsimp only
  rw [A.cycleEvaluation_equationCoefficientCup_periodicSquare
    (A.centralRadialSquare hcentral (A.meridianDiskPathMap H (A.actualMeridianDisk H)))
    (A.centralRadialSquare_vertical_periodic hcentral _)
    (A.centralRadialSquare_horizontal_periodic hcentral _
      (A.meridianDiskPathMap_endpoints H (A.actualMeridianDisk H)))]
  simp only [A.centralRadialSquare_horizontal_increment hcentral,
    A.centralRadialSquare_vertical_path hcentral]
  simp [A.actualMeridianPathMap_equation_increment, smul_eq_mul]

end AffineArrangement
end ChenRanks
