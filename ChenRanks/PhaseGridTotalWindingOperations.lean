import ChenRanks.PhaseGridClosingPaths
import ChenRanks.PhaseGridRectangularWinding
import Mathlib.Data.Finsupp.Basic

/-!
# Operations on the genuine finite total grid winding

Every table below is the previously constructed winding table of an
actual closed path. Actual path concatenation and reversal give its
additive identities. Actual deck translation permutes the original
punctures, so the same genuine finite total is invariant. No table,
finite-support property, or winding identity is an input.
-/

noncomputable section

open unitInterval

namespace ChenRanks

theorem circlePathIntegerIncrement_native_symm {x y : Circle} (p : Path x y) :
    circlePathIntegerIncrement p.symm.toContinuousMap =
      -circlePathIntegerIncrement p.toContinuousMap := by
  let θ : C(I, ℝ) := ⟨fun t => circlePathArgumentLift p.toContinuousMap (unitInterval.symm t),
    (circlePathArgumentLift p.toContinuousMap).continuous.comp unitInterval.continuous_symm⟩
  have hp (t : I) : Circle.exp (θ t) = p.symm.toContinuousMap t :=
    circlePathArgumentLift_projects p.toContinuousMap (unitInterval.symm t)
  have h := circlePathIntegerIncrement_mul_period_eq_lift_difference
    p.symm.toContinuousMap θ hp
  change (circlePathIntegerIncrement p.symm.toContinuousMap : ℝ) * (2 * Real.pi) =
    circlePathArgumentLift p.toContinuousMap (unitInterval.symm 1) -
      circlePathArgumentLift p.toContinuousMap (unitInterval.symm 0) +
      Complex.arg (p.symm 0 : ℂ) - Complex.arg (p.symm 1 : ℂ) at h
  simp only [unitInterval.symm_one, unitInterval.symm_zero, Path.symm_apply,
    Function.comp_apply, circlePathArgumentLift_zero, circlePathIntegerIncrement_formula] at h
  simp only [Path.coe_toContinuousMap, Path.source, Path.target] at h
  have he : (circlePathIntegerIncrement p.symm.toContinuousMap : ℝ) =
      -(circlePathIntegerIncrement p.toContinuousMap : ℝ) := by
    nlinarith [Real.pi_pos]
  apply Int.cast_injective (α := ℝ)
  simpa only [Int.cast_neg] using he

theorem argumentPlaneComplexMap_add (p q : ℝ × ℝ) :
    argumentPlaneComplexMap (p + q) = argumentPlaneComplexMap p + argumentPlaneComplexMap q := by
  apply Complex.ext <;> rfl

theorem windingPhaseGridComplexPoint_add_deck (m n : ℤ × ℤ) :
    windingPhaseGridComplexPoint (m + n) = windingPhaseGridComplexPoint m +
      argumentPlaneComplexMap (windingPhaseDeckPoint n) := by
  exact congrArg argumentPlaneComplexMap (windingPhaseGridPoint_add_deck m n) |>.trans
    (argumentPlaneComplexMap_add _ _)

def phaseGridPointNonzeroMap (n : ℤ × ℤ) : C(PhaseGridComplement, NonzeroComplex) where
  toFun p := ⟨argumentPlaneComplexMap p.val - windingPhaseGridComplexPoint n, by
    apply sub_ne_zero.mpr
    intro h
    apply p.property
    exact ⟨n, (argumentPlaneComplexMap_injective h).symm⟩⟩
  continuous_toFun := Continuous.subtype_mk
    ((argumentPlaneComplexMap.continuous.comp continuous_subtype_val).sub continuous_const) _

def phaseGridPointCircleMap (n : ℤ × ℤ) : C(PhaseGridComplement, Circle) :=
  nonzeroComplexCircleMap.comp (phaseGridPointNonzeroMap n)

def phaseGridLoopCoordinatePath {x : PhaseGridComplement} (p : Path x x) : C(I, ℝ × ℝ) :=
  ⟨fun t => (p t).val, continuous_subtype_val.comp p.continuous⟩

theorem phaseGridLoopCoordinatePath_closed {x : PhaseGridComplement} (p : Path x x) :
    phaseGridLoopCoordinatePath p 0 = phaseGridLoopCoordinatePath p 1 := by
  change (p 0).val = (p 1).val
  rw [Path.source, Path.target]

def phaseGridLoopWindingTable {x : PhaseGridComplement} (p : Path x x) : (ℤ × ℤ) →₀ ℤ :=
  phaseGridPathWindingFinsupp (phaseGridLoopCoordinatePath p)
    (phaseGridLoopCoordinatePath_closed p) (fun t => (p t).property)

theorem phaseGridLoopWindingTable_apply {x : PhaseGridComplement} (p : Path x x)
    (n : ℤ × ℤ) :
    phaseGridLoopWindingTable p n = circlePathIntegerIncrement
      (p.map (phaseGridPointCircleMap n).continuous).toContinuousMap := rfl

def phaseGridLoopTotalWinding {x : PhaseGridComplement} (p : Path x x) : ℤ :=
  (phaseGridLoopWindingTable p).sum (fun _ v => v)

theorem phaseGridLoopTotalWinding_closing (γ : C(I, TwicePuncturedComplex)) :
    phaseGridLoopTotalWinding (twicePuncturedPhaseClosingLoop γ) =
      twicePuncturedPathClosingWinding γ := rfl

theorem phaseGridLoopWindingTable_trans {x : PhaseGridComplement} (p q : Path x x) :
    phaseGridLoopWindingTable (p.trans q) =
      phaseGridLoopWindingTable p + phaseGridLoopWindingTable q := by
  apply Finsupp.ext
  intro n
  simp only [phaseGridLoopWindingTable_apply, Finsupp.add_apply, Path.map_trans,
    circlePathIntegerIncrement_native_trans]

theorem phaseGridLoopWindingTable_symm {x : PhaseGridComplement} (p : Path x x) :
    phaseGridLoopWindingTable p.symm = -phaseGridLoopWindingTable p := by
  apply Finsupp.ext
  intro n
  rw [phaseGridLoopWindingTable_apply, Finsupp.neg_apply, phaseGridLoopWindingTable_apply,
    ← Path.map_symm, circlePathIntegerIncrement_native_symm]

theorem phaseGridLoopTotalWinding_trans {x : PhaseGridComplement} (p q : Path x x) :
    phaseGridLoopTotalWinding (p.trans q) =
      phaseGridLoopTotalWinding p + phaseGridLoopTotalWinding q := by
  unfold phaseGridLoopTotalWinding
  rw [phaseGridLoopWindingTable_trans]
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

theorem phaseGridLoopTotalWinding_symm {x : PhaseGridComplement} (p : Path x x) :
    phaseGridLoopTotalWinding p.symm = -phaseGridLoopTotalWinding p := by
  have h := phaseGridLoopTotalWinding_trans p p.symm
  have hz : phaseGridLoopWindingTable (p.trans p.symm) = 0 := by
    rw [phaseGridLoopWindingTable_trans, phaseGridLoopWindingTable_symm, add_neg_cancel]
  have ht : phaseGridLoopTotalWinding (p.trans p.symm) = 0 := by
    simp only [phaseGridLoopTotalWinding, hz, Finsupp.sum_zero_index]
  rw [ht] at h
  linarith [h]

theorem phaseGridLoopWindingTable_conjugate {x y : PhaseGridComplement}
    (p : Path x y) (q : Path y y) :
    phaseGridLoopWindingTable ((p.trans q).trans p.symm) =
      phaseGridLoopWindingTable q := by
  apply Finsupp.ext
  intro n
  simp only [phaseGridLoopWindingTable_apply, Path.map_trans,
    circlePathIntegerIncrement_native_trans]
  rw [← Path.map_symm, circlePathIntegerIncrement_native_symm]
  abel

theorem phaseGridLoopTotalWinding_conjugate {x y : PhaseGridComplement}
    (p : Path x y) (q : Path y y) :
    phaseGridLoopTotalWinding ((p.trans q).trans p.symm) =
      phaseGridLoopTotalWinding q := by
  unfold phaseGridLoopTotalWinding
  rw [phaseGridLoopWindingTable_conjugate]

theorem phaseGridPointCircleMap_deck (m n : ℤ × ℤ) (p : PhaseGridComplement) :
    phaseGridPointCircleMap (m + n) (phaseGridDeckTranslation n p) =
      phaseGridPointCircleMap m p := by
  apply congrArg nonzeroComplexCircleMap
  apply Subtype.ext
  change argumentPlaneComplexMap (p.val + windingPhaseDeckPoint n) -
      windingPhaseGridComplexPoint (m + n) =
    argumentPlaneComplexMap p.val - windingPhaseGridComplexPoint m
  rw [argumentPlaneComplexMap_add, windingPhaseGridComplexPoint_add_deck]
  abel

theorem phaseGridLoopWindingTable_deck_apply {x : PhaseGridComplement}
    (n : ℤ × ℤ) (p : Path x x) (m : ℤ × ℤ) :
    phaseGridLoopWindingTable (p.map (phaseGridDeckTranslation n).continuous) (m + n) =
      phaseGridLoopWindingTable p m := by
  rw [phaseGridLoopWindingTable_apply, phaseGridLoopWindingTable_apply]
  apply congrArg circlePathIntegerIncrement
  apply ContinuousMap.ext
  intro t
  exact phaseGridPointCircleMap_deck m n (p t)

theorem phaseGridLoopWindingTable_deck {x : PhaseGridComplement}
    (n : ℤ × ℤ) (p : Path x x) :
    phaseGridLoopWindingTable (p.map (phaseGridDeckTranslation n).continuous) =
      Finsupp.mapDomain (fun m => m + n) (phaseGridLoopWindingTable p) := by
  apply Finsupp.ext
  intro m
  have hinj : Function.Injective (fun m : ℤ × ℤ => m + n) := by
    intro a b hab
    exact add_right_cancel hab
  have hmap := Finsupp.mapDomain_apply hinj
    (phaseGridLoopWindingTable p) (m - n)
  rw [sub_add_cancel] at hmap
  rw [hmap]
  have h := phaseGridLoopWindingTable_deck_apply n p (m - n)
  simpa only [sub_add_cancel] using h

theorem phaseGridLoopTotalWinding_deck {x : PhaseGridComplement}
    (n : ℤ × ℤ) (p : Path x x) :
    phaseGridLoopTotalWinding (p.map (phaseGridDeckTranslation n).continuous) =
      phaseGridLoopTotalWinding p := by
  unfold phaseGridLoopTotalWinding
  rw [phaseGridLoopWindingTable_deck]
  simpa only [AddMonoidHom.id_apply] using
    (Finsupp.sum_mapDomain_index_addMonoidHom
      (f := fun m : ℤ × ℤ => m + n) (s := phaseGridLoopWindingTable p)
      (fun _ => AddMonoidHom.id ℤ))

theorem twicePuncturedArgumentDeckIncrement_native_trans
    {x y z : TwicePuncturedComplex} (p : Path x y) (q : Path y z) :
    twicePuncturedArgumentDeckIncrement (p.trans q).toContinuousMap =
      twicePuncturedArgumentDeckIncrement p.toContinuousMap +
        twicePuncturedArgumentDeckIncrement q.toContinuousMap := by
  apply Prod.ext
  · have h := circlePathIntegerIncrement_native_trans
      (p.map twicePuncturedComplexZeroPhase.continuous)
      (q.map twicePuncturedComplexZeroPhase.continuous)
    rw [← Path.map_trans] at h
    exact h
  · have h := circlePathIntegerIncrement_native_trans
      (p.map twicePuncturedComplexOnePhase.continuous)
      (q.map twicePuncturedComplexOnePhase.continuous)
    rw [← Path.map_trans] at h
    exact h

end ChenRanks
