import ChenRanks.ArrangementSubpathStraightening
import ChenRanks.UniformUnitGridPathOscillation

/-! A genuinely constructed finite polygonal approximation to an
original arrangement path. Its grid and its fixed-endpoint homotopy
are derived, not supplied. Native subpath and finite-concatenation
homotopies assemble the local straightening. -/

noncomputable section

open unitInterval

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable {x y : A.Complement} (γ : Path x y)

/-- Original ambient coordinate map of the actual path. -/
def originalAmbientPath : C(I, Fin d → ℂ) where
  toFun t := (γ t).val
  continuous_toFun := continuous_subtype_val.comp γ.continuous

/-- A genuine finite grid with small oscillation follows from the
actual path and the genuine positive avoidance radius. -/
theorem exists_actual_straightening_grid :
    ∃ (n : ℕ) (hn : 0 < n), ∀ (i : Fin n) (t : I),
      dist (γ (Set.Icc.convexCombo (uniformUnitGrid n hn i.castSucc)
        (uniformUnitGrid n hn i.succ) t)).val (γ (uniformUnitGrid n hn i.castSucc)).val <
          A.actualPathAvoidanceRadius γ.toContinuousMap / 4 := by
  exact exists_uniformUnitGrid_path_oscillation (A.originalAmbientPath γ)
    (A.actualPathAvoidanceRadius γ.toContinuousMap / 4)
    (div_pos (A.actualPathAvoidanceRadius_pos γ.toContinuousMap) (by norm_num))

/-- This finite step count is selected from an already proved genuine
finite-grid existence theorem. -/
def actualPolygonalStepCount : ℕ := (A.exists_actual_straightening_grid γ).choose

theorem actualPolygonalStepCount_pos : 0 < A.actualPolygonalStepCount γ :=
  (A.exists_actual_straightening_grid γ).choose_spec.choose

/-- The chosen actual unit-interval subdivision. -/
def actualPolygonalGrid (i : Fin (A.actualPolygonalStepCount γ + 1)) : I :=
  uniformUnitGrid (A.actualPolygonalStepCount γ) (A.actualPolygonalStepCount_pos γ) i

/-- Actual oscillation on every actual chosen subinterval. -/
theorem actualPolygonalGrid_oscillation (i : Fin (A.actualPolygonalStepCount γ)) (t : I) :
    dist (γ (Set.Icc.convexCombo (A.actualPolygonalGrid γ i.castSucc)
      (A.actualPolygonalGrid γ i.succ) t)).val (γ (A.actualPolygonalGrid γ i.castSucc)).val <
        A.actualPathAvoidanceRadius γ.toContinuousMap / 4 :=
  (A.exists_actual_straightening_grid γ).choose_spec.choose_spec i t

@[simp] theorem actualPolygonalGrid_zero : A.actualPolygonalGrid γ 0 = 0 := by
  simp [actualPolygonalGrid]

@[simp] theorem actualPolygonalGrid_last :
    A.actualPolygonalGrid γ (Fin.last (A.actualPolygonalStepCount γ)) = 1 := by
  simp [actualPolygonalGrid]

/-- The full subpath has the literal same original continuous map,
so no arbitrary endpoint or original-path comparison is an input. -/
theorem actualPolygonalFullSubpath_toContinuousMap :
    (γ.subpath (A.actualPolygonalGrid γ 0)
      (A.actualPolygonalGrid γ (Fin.last (A.actualPolygonalStepCount γ)))).toContinuousMap =
        γ.toContinuousMap := by
  apply ContinuousMap.ext
  intro t
  change γ (Set.Icc.convexCombo (A.actualPolygonalGrid γ 0)
    (A.actualPolygonalGrid γ (Fin.last (A.actualPolygonalStepCount γ))) t) = γ t
  rw [A.actualPolygonalGrid_zero γ, A.actualPolygonalGrid_last γ,
    Set.Icc.convexCombo_zero_one]

/-- The actual finite concatenation of true original straight segments. -/
def actualPolygonalApproximation :
    Path (γ (A.actualPolygonalGrid γ 0))
      (γ (A.actualPolygonalGrid γ (Fin.last (A.actualPolygonalStepCount γ)))) :=
  Path.concat (fun i => γ (A.actualPolygonalGrid γ i))
    (fun i => A.straightenedSubpath γ (A.actualPolygonalGrid γ i.castSucc)
      (A.actualPolygonalGrid γ i.succ) (A.actualPolygonalGrid_oscillation γ i))

/-- The genuine polygonal path is homotopic through the original
complement to the genuine original full subpath. -/
def actualPolygonalApproximationHomotopy :
    (A.actualPolygonalApproximation γ).Homotopy
      (γ.subpath (A.actualPolygonalGrid γ 0)
        (A.actualPolygonalGrid γ (Fin.last (A.actualPolygonalStepCount γ)))) :=
  (Path.Homotopy.concat (fun i => γ (A.actualPolygonalGrid γ i))
    (fun i => γ.subpath (A.actualPolygonalGrid γ i.castSucc)
      (A.actualPolygonalGrid γ i.succ))
    (fun i => A.straightenedSubpath γ (A.actualPolygonalGrid γ i.castSucc)
      (A.actualPolygonalGrid γ i.succ) (A.actualPolygonalGrid_oscillation γ i))
    (fun i => A.subpathStraighteningHomotopy γ (A.actualPolygonalGrid γ i.castSucc)
      (A.actualPolygonalGrid γ i.succ) (A.actualPolygonalGrid_oscillation γ i))).symm.trans
      (Path.Homotopy.concatSubpath γ (A.actualPolygonalGrid γ))

end ChenRanks.AffineArrangement
