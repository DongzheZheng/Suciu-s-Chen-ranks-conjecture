import ChenRanks.PhaseGridTotalWindingOperations
import ChenRanks.SignedIntegerThresholdSums

/-!
# Actual vertical-first deck discrepancy winding

The loop is constructed from the actual selected native deck paths.
Every edge computation uses the actual argument lift formulas. Its
actual pointwise winding is identified with a genuine product of signed
integer threshold differences; the genuine finite sum then computes
n₁m₂. No assigned winding, rectangle-value, or finite-support premise
is used in the final statement.
-/

noncomputable section

open unitInterval

namespace ChenRanks

private def deckPuncturePathIncrement {x y : PhaseGridComplement}
    (i : ℤ × ℤ) (p : Path x y) : ℤ :=
  circlePathIntegerIncrement (p.map (phaseGridPointCircleMap i).continuous).toContinuousMap

private theorem deckPuncturePathIncrement_trans {x y z : PhaseGridComplement}
    (i : ℤ × ℤ) (p : Path x y) (q : Path y z) :
    deckPuncturePathIncrement i (p.trans q) =
      deckPuncturePathIncrement i p + deckPuncturePathIncrement i q := by
  unfold deckPuncturePathIncrement
  rw [Path.map_trans, circlePathIntegerIncrement_native_trans]

private theorem deckPuncturePathIncrement_symm {x y : PhaseGridComplement}
    (i : ℤ × ℤ) (p : Path x y) :
    deckPuncturePathIncrement i p.symm = -deckPuncturePathIncrement i p := by
  change circlePathIntegerIncrement
    (p.map (phaseGridPointCircleMap i).continuous).symm.toContinuousMap = _
  exact circlePathIntegerIncrement_native_symm _

private theorem period_sub_grid_coordinate_factor (a r : ℤ) :
    (a : ℝ) * (2 * Real.pi) - (Real.pi + (r : ℝ) * (2 * Real.pi)) =
      ((2 * (a - r) - 1 : ℤ) : ℝ) * Real.pi := by
  push_cast
  ring

private theorem period_sub_grid_coordinate_ne_zero (a r : ℤ) :
    (a : ℝ) * (2 * Real.pi) - (Real.pi + (r : ℝ) * (2 * Real.pi)) ≠ 0 := by
  rw [period_sub_grid_coordinate_factor]
  apply mul_ne_zero _ Real.pi_ne_zero
  intro h
  have hz : (2 * (a - r) - 1 : ℤ) = 0 := by exact_mod_cast h
  omega

private theorem period_sub_grid_coordinate_lt_zero_iff (a r : ℤ) :
    (a : ℝ) * (2 * Real.pi) - (Real.pi + (r : ℝ) * (2 * Real.pi)) < 0 ↔ a ≤ r := by
  rw [period_sub_grid_coordinate_factor]
  constructor
  · intro h
    have hc : ((2 * (a - r) - 1 : ℤ) : ℝ) < 0 := by
      by_contra hn
      have hp := mul_nonneg (le_of_not_gt hn) Real.pi_pos.le
      exact (not_le_of_gt h) hp
    have hi : (2 * (a - r) - 1 : ℤ) < 0 := by exact_mod_cast hc
    omega
  · intro h
    have hi : (2 * (a - r) - 1 : ℤ) < 0 := by omega
    have hc : ((2 * (a - r) - 1 : ℤ) : ℝ) < 0 := by exact_mod_cast hi
    exact mul_neg_of_neg_of_pos hc Real.pi_pos

private theorem period_sub_grid_lower_indicator (a r : ℤ) :
    lowerHalfPlaneIndicator
      ((a : ℝ) * (2 * Real.pi) - (Real.pi + (r : ℝ) * (2 * Real.pi))) =
        if a ≤ r then 1 else 0 := by
  unfold lowerHalfPlaneIndicator
  simp only [period_sub_grid_coordinate_lt_zero_iff]

private theorem deckPuncture_increment_of_actual_relative_path
    {x y : PhaseGridComplement} (i : ℤ × ℤ) (p : Path x y)
    (γ : C(I, NonzeroComplex))
    (hγ : ∀ t, argumentPlaneComplexMap (p t).val - windingPhaseGridComplexPoint i = (γ t : ℂ)) :
    deckPuncturePathIncrement i p =
      circlePathIntegerIncrement (nonzeroComplexCircleMap.comp γ) := by
  change circlePathIntegerIncrement
    (p.map (phaseGridPointCircleMap i).continuous).toContinuousMap = _
  apply congrArg circlePathIntegerIncrement
  apply ContinuousMap.ext
  intro t
  change nonzeroComplexCircleMap (phaseGridPointNonzeroMap i (p t)) = nonzeroComplexCircleMap (γ t)
  apply congrArg nonzeroComplexCircleMap
  apply Subtype.ext
  exact hγ t

private theorem actual_period_vertical_increment
    {x y : PhaseGridComplement} (i : ℤ × ℤ) (p : Path x y) (a b c : ℤ)
    (hp : ∀ t, (p t).val =
      ((a : ℝ) * (2 * Real.pi),
        (1 - (t : ℝ)) * ((b : ℝ) * (2 * Real.pi)) +
          (t : ℝ) * ((c : ℝ) * (2 * Real.pi)))) :
    deckPuncturePathIncrement i p =
      if a ≤ i.1 then signedIntegerThreshold b c i.2 else 0 := by
  let γ := nonzeroComplexVerticalSegment
    ((a : ℝ) * (2 * Real.pi) - (Real.pi + (i.1 : ℝ) * (2 * Real.pi)))
    (period_sub_grid_coordinate_ne_zero a i.1)
    ((b : ℝ) * (2 * Real.pi) - (Real.pi + (i.2 : ℝ) * (2 * Real.pi)))
    ((c : ℝ) * (2 * Real.pi) - (Real.pi + (i.2 : ℝ) * (2 * Real.pi)))
  have hγ (t : I) : argumentPlaneComplexMap (p t).val - windingPhaseGridComplexPoint i =
      (γ t : ℂ) := by
    rw [hp t]
    apply Complex.ext
    · change (a : ℝ) * (2 * Real.pi) - (Real.pi + (i.1 : ℝ) * (2 * Real.pi)) =
        (a : ℝ) * (2 * Real.pi) - (Real.pi + (i.1 : ℝ) * (2 * Real.pi))
      rfl
    · change ((1 - (t : ℝ)) * ((b : ℝ) * (2 * Real.pi)) +
          (t : ℝ) * ((c : ℝ) * (2 * Real.pi))) -
          (Real.pi + (i.2 : ℝ) * (2 * Real.pi)) =
        (1 - (t : ℝ)) * ((b : ℝ) * (2 * Real.pi) -
          (Real.pi + (i.2 : ℝ) * (2 * Real.pi))) +
        (t : ℝ) * ((c : ℝ) * (2 * Real.pi) -
          (Real.pi + (i.2 : ℝ) * (2 * Real.pi)))
      ring
  rw [deckPuncture_increment_of_actual_relative_path i p γ.toContinuousMap hγ,
    nonzeroComplexVerticalSegment_increment]
  simp only [period_sub_grid_coordinate_lt_zero_iff, period_sub_grid_lower_indicator]
  rfl

private theorem actual_period_horizontal_increment
    {x y : PhaseGridComplement} (i : ℤ × ℤ) (p : Path x y) (a b c : ℤ)
    (hp : ∀ t, (p t).val =
      ((1 - (t : ℝ)) * ((b : ℝ) * (2 * Real.pi)) +
          (t : ℝ) * ((c : ℝ) * (2 * Real.pi)),
        (a : ℝ) * (2 * Real.pi))) :
    deckPuncturePathIncrement i p = 0 := by
  let γ := nonzeroComplexHorizontalSegment
    ((a : ℝ) * (2 * Real.pi) - (Real.pi + (i.2 : ℝ) * (2 * Real.pi)))
    (period_sub_grid_coordinate_ne_zero a i.2)
    ((b : ℝ) * (2 * Real.pi) - (Real.pi + (i.1 : ℝ) * (2 * Real.pi)))
    ((c : ℝ) * (2 * Real.pi) - (Real.pi + (i.1 : ℝ) * (2 * Real.pi)))
  have hγ (t : I) : argumentPlaneComplexMap (p t).val - windingPhaseGridComplexPoint i =
      (γ t : ℂ) := by
    rw [hp t]
    apply Complex.ext
    · change ((1 - (t : ℝ)) * ((b : ℝ) * (2 * Real.pi)) +
          (t : ℝ) * ((c : ℝ) * (2 * Real.pi))) -
          (Real.pi + (i.1 : ℝ) * (2 * Real.pi)) =
        (1 - (t : ℝ)) * ((b : ℝ) * (2 * Real.pi) -
          (Real.pi + (i.1 : ℝ) * (2 * Real.pi))) +
        (t : ℝ) * ((c : ℝ) * (2 * Real.pi) -
          (Real.pi + (i.1 : ℝ) * (2 * Real.pi)))
      ring
    · change (a : ℝ) * (2 * Real.pi) - (Real.pi + (i.2 : ℝ) * (2 * Real.pi)) =
        (a : ℝ) * (2 * Real.pi) - (Real.pi + (i.2 : ℝ) * (2 * Real.pi))
      rfl
  rw [deckPuncture_increment_of_actual_relative_path i p γ.toContinuousMap hγ]
  exact nonzeroComplexHorizontalSegment_increment _ _ _ _

private theorem selected_deck_path_increment (i n : ℤ × ℤ) :
    deckPuncturePathIncrement i (phaseGridDeckPath n) =
      if 0 ≤ i.1 then signedIntegerThreshold 0 n.2 i.2 else 0 := by
  rw [phaseGridDeckPath, deckPuncturePathIncrement_trans]
  have hv : deckPuncturePathIncrement i (phaseGridDeckVerticalPath n) =
      if 0 ≤ i.1 then signedIntegerThreshold 0 n.2 i.2 else 0 := by
    apply actual_period_vertical_increment i _ 0 0 n.2
    intro t
    apply Prod.ext <;> simp [phaseGridDeckVerticalPath]
  have hh : deckPuncturePathIncrement i (phaseGridDeckHorizontalPath n) = 0 := by
    apply actual_period_horizontal_increment i _ n.2 0 n.1
    intro t
    apply Prod.ext <;> simp [phaseGridDeckHorizontalPath]
  rw [hv, hh, add_zero]

/-- The actual translated selected deck path, with its actual endpoints
cast by proved coordinate identities. -/
def phaseGridTranslatedDeckPath (n m : ℤ × ℤ) :
    Path (phaseGridDeckEndpoint n) (phaseGridDeckEndpoint (n + m)) :=
  ((phaseGridDeckPath m).map (phaseGridDeckTranslation n).continuous).cast
    (by apply Subtype.ext; simp [phaseGridOrigin, phaseGridDeckEndpoint])
    (by
      apply Subtype.ext
      change windingPhaseDeckPoint (n + m) =
        windingPhaseDeckPoint m + windingPhaseDeckPoint n
      apply Prod.ext
      · change ((n.1 + m.1 : ℤ) : ℝ) * (2 * Real.pi) =
          (m.1 : ℝ) * (2 * Real.pi) + (n.1 : ℝ) * (2 * Real.pi)
        rw [Int.cast_add]
        ring
      · change ((n.2 + m.2 : ℤ) : ℝ) * (2 * Real.pi) =
          (m.2 : ℝ) * (2 * Real.pi) + (n.2 : ℝ) * (2 * Real.pi)
        rw [Int.cast_add]
        ring)

private theorem translated_selected_deck_path_increment (i n m : ℤ × ℤ) :
    deckPuncturePathIncrement i (phaseGridTranslatedDeckPath n m) =
      if n.1 ≤ i.1 then signedIntegerThreshold n.2 (n.2 + m.2) i.2 else 0 := by
  change deckPuncturePathIncrement i
    ((phaseGridDeckPath m).map (phaseGridDeckTranslation n).continuous) = _
  rw [phaseGridDeckPath, Path.map_trans, deckPuncturePathIncrement_trans]
  have hv : deckPuncturePathIncrement i
      ((phaseGridDeckVerticalPath m).map (phaseGridDeckTranslation n).continuous) =
        if n.1 ≤ i.1 then signedIntegerThreshold n.2 (n.2 + m.2) i.2 else 0 := by
    apply actual_period_vertical_increment i _ n.1 n.2 (n.2 + m.2)
    intro t
    apply Prod.ext
    · change (0 : ℝ) + (n.1 : ℝ) * (2 * Real.pi) = (n.1 : ℝ) * (2 * Real.pi)
      rw [zero_add]
    · change (t : ℝ) * ((m.2 : ℝ) * (2 * Real.pi)) + (n.2 : ℝ) * (2 * Real.pi) =
        (1 - (t : ℝ)) * ((n.2 : ℝ) * (2 * Real.pi)) +
          (t : ℝ) * (((n.2 + m.2 : ℤ) : ℝ) * (2 * Real.pi))
      push_cast
      ring
  have hh : deckPuncturePathIncrement i
      ((phaseGridDeckHorizontalPath m).map (phaseGridDeckTranslation n).continuous) = 0 := by
    apply actual_period_horizontal_increment i _ (n.2 + m.2) n.1 (n.1 + m.1)
    intro t
    apply Prod.ext
    · change (t : ℝ) * ((m.1 : ℝ) * (2 * Real.pi)) + (n.1 : ℝ) * (2 * Real.pi) =
        (1 - (t : ℝ)) * ((n.1 : ℝ) * (2 * Real.pi)) +
          (t : ℝ) * (((n.1 + m.1 : ℤ) : ℝ) * (2 * Real.pi))
      push_cast
      ring
    · change (m.2 : ℝ) * (2 * Real.pi) + (n.2 : ℝ) * (2 * Real.pi) =
        ((n.2 + m.2 : ℤ) : ℝ) * (2 * Real.pi)
      push_cast
      ring
  rw [hv, hh, add_zero]

/-- The genuine discrepancy loop of the selected vertical-first deck
paths. It is not replaced by a prescribed rectangle. -/
def phaseGridDeckDiscrepancyLoop (n m : ℤ × ℤ) : Path phaseGridOrigin phaseGridOrigin :=
  ((phaseGridDeckPath n).trans (phaseGridTranslatedDeckPath n m)).trans
    (phaseGridDeckPath (n + m)).symm

/-- The same actual loop in the actual argument coordinates. -/
def phaseGridDeckDiscrepancyCoordinatePath (n m : ℤ × ℤ) : C(I, ℝ × ℝ) :=
  phaseGridLoopCoordinatePath (phaseGridDeckDiscrepancyLoop n m)

theorem phaseGridDeckDiscrepancyCoordinatePath_closed (n m : ℤ × ℤ) :
    phaseGridDeckDiscrepancyCoordinatePath n m 0 =
      phaseGridDeckDiscrepancyCoordinatePath n m 1 :=
  phaseGridLoopCoordinatePath_closed (phaseGridDeckDiscrepancyLoop n m)

theorem phaseGridDeckDiscrepancyCoordinatePath_not_mem_grid (n m : ℤ × ℤ) (t : I) :
    phaseGridDeckDiscrepancyCoordinatePath n m t ∉ windingPhaseGrid :=
  (phaseGridDeckDiscrepancyLoop n m t).property

/-- The actual puncture winding of the actual six-segment discrepancy
loop is the literal product of two integer threshold differences. -/
theorem phaseGridDeckDiscrepancy_point_winding (n m i : ℤ × ℤ) :
    phaseGridPathWindingValues (phaseGridDeckDiscrepancyCoordinatePath n m)
      (phaseGridDeckDiscrepancyCoordinatePath_not_mem_grid n m) i =
      signedIntegerThreshold 0 n.1 i.1 *
        signedIntegerThreshold n.2 (n.2 + m.2) i.2 := by
  change deckPuncturePathIncrement i (phaseGridDeckDiscrepancyLoop n m) = _
  rw [phaseGridDeckDiscrepancyLoop, deckPuncturePathIncrement_trans,
    deckPuncturePathIncrement_trans, deckPuncturePathIncrement_symm,
    selected_deck_path_increment, translated_selected_deck_path_increment,
    selected_deck_path_increment]
  change (if 0 ≤ i.1 then signedIntegerThreshold 0 n.2 i.2 else 0) +
      (if n.1 ≤ i.1 then signedIntegerThreshold n.2 (n.2 + m.2) i.2 else 0) -
      (if 0 ≤ i.1 then signedIntegerThreshold 0 (n.2 + m.2) i.2 else 0) = _
  unfold signedIntegerThreshold
  split_ifs <;> ring

/-- The actual winding Finsupp equals the proved finite threshold
product, by genuine pointwise path computations. -/
theorem phaseGridDeckDiscrepancy_windingFinsupp_eq (n m : ℤ × ℤ) :
    phaseGridPathWindingFinsupp (phaseGridDeckDiscrepancyCoordinatePath n m)
      (phaseGridDeckDiscrepancyCoordinatePath_closed n m)
      (phaseGridDeckDiscrepancyCoordinatePath_not_mem_grid n m) =
      signedIntegerThresholdProductFinsupp 0 n.1 n.2 (n.2 + m.2) := by
  ext i
  rw [phaseGridPathWindingFinsupp_apply, signedIntegerThresholdProductFinsupp_apply]
  exact phaseGridDeckDiscrepancy_point_winding n m i

/-- The genuine total winding of the actual selected discrepancy loop
is n₁m₂. Finite support, the actual six edge windings, integer thresholds,
and their finite sum are all proved rather than input hypotheses. -/
theorem phaseGridDeckDiscrepancy_total_winding (n m : ℤ × ℤ) :
    phaseGridPathTotalWinding (phaseGridDeckDiscrepancyCoordinatePath n m)
      (phaseGridDeckDiscrepancyCoordinatePath_closed n m)
      (phaseGridDeckDiscrepancyCoordinatePath_not_mem_grid n m) = n.1 * m.2 := by
  unfold phaseGridPathTotalWinding
  rw [phaseGridDeckDiscrepancy_windingFinsupp_eq]
  exact signedIntegerThresholdProductFinsupp_deck_sum n.1 m.2 n.2

/-- The same actual discrepancy table in the native loop-winding
interface, without any new winding definition. -/
theorem phaseGridDeckDiscrepancy_loopWindingTable_eq (n m : ℤ × ℤ) :
    phaseGridLoopWindingTable (phaseGridDeckDiscrepancyLoop n m) =
      signedIntegerThresholdProductFinsupp 0 n.1 n.2 (n.2 + m.2) :=
  phaseGridDeckDiscrepancy_windingFinsupp_eq n m

/-- The same actual total in the native loop interface used by the
concatenation, deck translation and homotopy operations. -/
theorem phaseGridDeckDiscrepancy_loopTotalWinding (n m : ℤ × ℤ) :
    phaseGridLoopTotalWinding (phaseGridDeckDiscrepancyLoop n m) = n.1 * m.2 := by
  unfold phaseGridLoopTotalWinding
  rw [phaseGridDeckDiscrepancy_loopWindingTable_eq]
  exact signedIntegerThresholdProductFinsupp_deck_sum n.1 m.2 n.2

end ChenRanks
