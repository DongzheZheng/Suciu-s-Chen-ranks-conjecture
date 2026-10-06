import ChenRanks.TwicePuncturedLiftedPathConcatenation
import ChenRanks.PhaseGridDeckDiscrepancyWinding

/-!
# Genuine closing-table concatenation

For each actual puncture, expand the genuine four pieces of each
closing loop and the genuine three selected deck paths of the
discrepancy loop. The actual lifted-path concatenation theorem and
actual deck composition cancel the intermediate principal paths.
Thus the equality is proved for the already constructed finite winding
tables. Summing these actual tables gives the true n₁m₂ correction.

No winding table, correction formula, finite-support property, or
closing concatenation identity is an input. The singular triangle
comparison and the resulting cochain coboundary are separate steps.
-/

noncomputable section

open unitInterval

namespace ChenRanks

private def closingPuncturePathIncrement {x y : PhaseGridComplement}
    (i : ℤ × ℤ) (p : Path x y) : ℤ :=
  circlePathIntegerIncrement
    (p.map (phaseGridPointCircleMap i).continuous).toContinuousMap

private theorem closingPuncturePathIncrement_trans
    {x y z : PhaseGridComplement} (i : ℤ × ℤ) (p : Path x y) (q : Path y z) :
    closingPuncturePathIncrement i (p.trans q) =
      closingPuncturePathIncrement i p + closingPuncturePathIncrement i q := by
  unfold closingPuncturePathIncrement
  rw [Path.map_trans, circlePathIntegerIncrement_native_trans]

private theorem closingPuncturePathIncrement_symm
    {x y : PhaseGridComplement} (i : ℤ × ℤ) (p : Path x y) :
    closingPuncturePathIncrement i p.symm = -closingPuncturePathIncrement i p := by
  change circlePathIntegerIncrement
    (p.map (phaseGridPointCircleMap i).continuous).symm.toContinuousMap = _
  exact circlePathIntegerIncrement_native_symm _

private theorem closingPuncturePathIncrement_map_symm
    {x y : PhaseGridComplement} (i n : ℤ × ℤ) (p : Path x y) :
    closingPuncturePathIncrement i (p.symm.map (phaseGridDeckTranslation n).continuous) =
      -closingPuncturePathIncrement i (p.map (phaseGridDeckTranslation n).continuous) := by
  rw [← Path.map_symm]
  exact closingPuncturePathIncrement_symm i _

private theorem closingPuncturePathIncrement_deck_deck
    {x y : PhaseGridComplement} (i n m : ℤ × ℤ) (p : Path x y) :
    closingPuncturePathIncrement i
        ((p.map (phaseGridDeckTranslation m).continuous).map
          (phaseGridDeckTranslation n).continuous) =
      closingPuncturePathIncrement i
        (p.map (phaseGridDeckTranslation (n + m)).continuous) := by
  apply congrArg circlePathIntegerIncrement
  apply ContinuousMap.ext
  intro t
  change phaseGridPointCircleMap i
      (phaseGridDeckTranslation n (phaseGridDeckTranslation m (p t))) =
    phaseGridPointCircleMap i (phaseGridDeckTranslation (n + m) (p t))
  rw [phaseGridDeckTranslation_add_apply]

private theorem closingPuncturePathIncrement_native_lift_trans
    {x y z : TwicePuncturedComplex} (i : ℤ × ℤ) (p : Path x y) (q : Path y z) :
    closingPuncturePathIncrement i (phaseGridNativeLiftedPath (p.trans q)) =
      closingPuncturePathIncrement i (phaseGridNativeLiftedPath p) +
        closingPuncturePathIncrement i
          ((phaseGridNativeLiftedPath q).map
            (phaseGridDeckTranslation
              (twicePuncturedArgumentDeckIncrement p.toContinuousMap)).continuous) := by
  rw [phaseGridNativeLiftedPath_trans, closingPuncturePathIncrement_trans]
  rfl

private theorem closingTable_native_apply
    {x y : TwicePuncturedComplex} (p : Path x y) (i : ℤ × ℤ) :
    phaseGridLoopWindingTable (twicePuncturedPhaseClosingLoop p.toContinuousMap) i =
      closingPuncturePathIncrement i (phaseGridPrincipalPath x) +
        closingPuncturePathIncrement i (phaseGridNativeLiftedPath p) -
        closingPuncturePathIncrement i
          ((phaseGridPrincipalPath y).map
            (phaseGridDeckTranslation
              (twicePuncturedArgumentDeckIncrement p.toContinuousMap)).continuous) -
        closingPuncturePathIncrement i
          (phaseGridDeckPath (twicePuncturedArgumentDeckIncrement p.toContinuousMap)) := by
  change closingPuncturePathIncrement i
      (twicePuncturedPhaseClosingLoop p.toContinuousMap) = _
  rw [twicePuncturedPhaseClosingLoop, closingPuncturePathIncrement_trans,
    closingPuncturePathIncrement_trans, closingPuncturePathIncrement_trans,
    closingPuncturePathIncrement_symm, closingPuncturePathIncrement_symm]
  simp only [Path.coe_toContinuousMap]
  have hs : closingPuncturePathIncrement i (phaseGridPrincipalPath (p 0)) =
      closingPuncturePathIncrement i (phaseGridPrincipalPath x) :=
    congrArg (fun z : TwicePuncturedComplex =>
      closingPuncturePathIncrement i (phaseGridPrincipalPath z)) p.source
  have hl : closingPuncturePathIncrement i (phaseGridLiftedOriginalPath p.toContinuousMap) =
      closingPuncturePathIncrement i (phaseGridNativeLiftedPath p) := rfl
  have ht : closingPuncturePathIncrement i
      (phaseGridTranslatedPrincipalPath (twicePuncturedArgumentDeckIncrement p.toContinuousMap)
        (p 1)) =
      closingPuncturePathIncrement i ((phaseGridPrincipalPath y).map
        (phaseGridDeckTranslation
          (twicePuncturedArgumentDeckIncrement p.toContinuousMap)).continuous) :=
    congrArg (fun z : TwicePuncturedComplex => closingPuncturePathIncrement i
      (phaseGridTranslatedPrincipalPath (twicePuncturedArgumentDeckIncrement p.toContinuousMap)
        z)) p.target
  simp only [hs, hl, ht, sub_eq_add_neg]

private theorem translatedClosingTable_native_apply
    {x y : TwicePuncturedComplex} (n : ℤ × ℤ) (p : Path x y) (i : ℤ × ℤ) :
    phaseGridLoopWindingTable
        ((twicePuncturedPhaseClosingLoop p.toContinuousMap).map
          (phaseGridDeckTranslation n).continuous) i =
      closingPuncturePathIncrement i
          ((phaseGridPrincipalPath x).map (phaseGridDeckTranslation n).continuous) +
        closingPuncturePathIncrement i
          ((phaseGridNativeLiftedPath p).map (phaseGridDeckTranslation n).continuous) -
        closingPuncturePathIncrement i
          ((phaseGridPrincipalPath y).map
            (phaseGridDeckTranslation
              (n + twicePuncturedArgumentDeckIncrement p.toContinuousMap)).continuous) -
        closingPuncturePathIncrement i
          ((phaseGridDeckPath (twicePuncturedArgumentDeckIncrement p.toContinuousMap)).map
            (phaseGridDeckTranslation n).continuous) := by
  change closingPuncturePathIncrement i
      ((twicePuncturedPhaseClosingLoop p.toContinuousMap).map
        (phaseGridDeckTranslation n).continuous) = _
  rw [twicePuncturedPhaseClosingLoop]
  simp only [Path.map_trans]
  rw [closingPuncturePathIncrement_trans, closingPuncturePathIncrement_trans,
    closingPuncturePathIncrement_trans, closingPuncturePathIncrement_map_symm,
    closingPuncturePathIncrement_map_symm]
  simp only [Path.coe_toContinuousMap]
  have hs : closingPuncturePathIncrement i
      ((phaseGridPrincipalPath (p 0)).map (phaseGridDeckTranslation n).continuous) =
      closingPuncturePathIncrement i
        ((phaseGridPrincipalPath x).map (phaseGridDeckTranslation n).continuous) :=
    congrArg (fun z : TwicePuncturedComplex => closingPuncturePathIncrement i
      ((phaseGridPrincipalPath z).map (phaseGridDeckTranslation n).continuous)) p.source
  have hl : closingPuncturePathIncrement i
      ((phaseGridLiftedOriginalPath p.toContinuousMap).map
        (phaseGridDeckTranslation n).continuous) =
      closingPuncturePathIncrement i ((phaseGridNativeLiftedPath p).map
        (phaseGridDeckTranslation n).continuous) := rfl
  have ht : closingPuncturePathIncrement i
      ((phaseGridTranslatedPrincipalPath
        (twicePuncturedArgumentDeckIncrement p.toContinuousMap) (p 1)).map
          (phaseGridDeckTranslation n).continuous) =
      closingPuncturePathIncrement i
        (((phaseGridPrincipalPath y).map
          (phaseGridDeckTranslation
            (twicePuncturedArgumentDeckIncrement p.toContinuousMap)).continuous).map
          (phaseGridDeckTranslation n).continuous) :=
    congrArg (fun z : TwicePuncturedComplex => closingPuncturePathIncrement i
      ((phaseGridTranslatedPrincipalPath
        (twicePuncturedArgumentDeckIncrement p.toContinuousMap) z).map
          (phaseGridDeckTranslation n).continuous)) p.target
  simp only [hs, hl, ht, closingPuncturePathIncrement_deck_deck, sub_eq_add_neg]

private theorem discrepancyTable_apply (n m i : ℤ × ℤ) :
    phaseGridLoopWindingTable (phaseGridDeckDiscrepancyLoop n m) i =
      closingPuncturePathIncrement i (phaseGridDeckPath n) +
        closingPuncturePathIncrement i
          ((phaseGridDeckPath m).map (phaseGridDeckTranslation n).continuous) -
        closingPuncturePathIncrement i (phaseGridDeckPath (n + m)) := by
  change closingPuncturePathIncrement i (phaseGridDeckDiscrepancyLoop n m) = _
  rw [phaseGridDeckDiscrepancyLoop, closingPuncturePathIncrement_trans,
    closingPuncturePathIncrement_trans, closingPuncturePathIncrement_symm]
  rfl

/-- The genuine pointwise identity of the four closing words. The
translated second loop and selected discrepancy loop are actual paths;
all cancellations use actual native increments and actual lift equality. -/
theorem twicePuncturedClosingWindingTable_native_trans_apply
    {x y z : TwicePuncturedComplex} (p : Path x y) (q : Path y z) (i : ℤ × ℤ) :
    phaseGridLoopWindingTable (twicePuncturedPhaseClosingLoop p.toContinuousMap) i +
        phaseGridLoopWindingTable
          ((twicePuncturedPhaseClosingLoop q.toContinuousMap).map
            (phaseGridDeckTranslation
              (twicePuncturedArgumentDeckIncrement p.toContinuousMap)).continuous) i =
      phaseGridLoopWindingTable
          (twicePuncturedPhaseClosingLoop (p.trans q).toContinuousMap) i -
        phaseGridLoopWindingTable
          (phaseGridDeckDiscrepancyLoop
            (twicePuncturedArgumentDeckIncrement p.toContinuousMap)
            (twicePuncturedArgumentDeckIncrement q.toContinuousMap)) i := by
  rw [closingTable_native_apply, translatedClosingTable_native_apply,
    closingTable_native_apply, discrepancyTable_apply]
  have hterminal := congrArg (fun n : ℤ × ℤ => closingPuncturePathIncrement i
    ((phaseGridPrincipalPath z).map (phaseGridDeckTranslation n).continuous))
    (twicePuncturedArgumentDeckIncrement_native_trans p q)
  have hdeck := congrArg (fun n : ℤ × ℤ =>
    closingPuncturePathIncrement i (phaseGridDeckPath n))
    (twicePuncturedArgumentDeckIncrement_native_trans p q)
  dsimp only at hterminal hdeck
  rw [hterminal, hdeck, closingPuncturePathIncrement_native_lift_trans]
  abel

/-- Equality of the genuine finite winding tables, with no assigned
table or finite-support premise. Tables may have different loop basepoints. -/
theorem twicePuncturedClosingWindingTable_native_trans
    {x y z : TwicePuncturedComplex} (p : Path x y) (q : Path y z) :
    phaseGridLoopWindingTable (twicePuncturedPhaseClosingLoop p.toContinuousMap) +
        phaseGridLoopWindingTable
          ((twicePuncturedPhaseClosingLoop q.toContinuousMap).map
            (phaseGridDeckTranslation
              (twicePuncturedArgumentDeckIncrement p.toContinuousMap)).continuous) =
      phaseGridLoopWindingTable
          (twicePuncturedPhaseClosingLoop (p.trans q).toContinuousMap) -
        phaseGridLoopWindingTable
          (phaseGridDeckDiscrepancyLoop
            (twicePuncturedArgumentDeckIncrement p.toContinuousMap)
            (twicePuncturedArgumentDeckIncrement q.toContinuousMap)) := by
  apply Finsupp.ext
  intro i
  simp only [Finsupp.add_apply, Finsupp.sub_apply]
  exact twicePuncturedClosingWindingTable_native_trans_apply p q i

/-- The genuine closing winding of the genuine concatenated original
path has correction n₁(p)n₂(q). Actual finite support, actual deck
invariance, actual lift concatenation, and actual discrepancy area have
all been proved internally; none is a caller-supplied detector. -/
theorem twicePuncturedPathClosingWinding_native_trans
    {x y z : TwicePuncturedComplex} (p : Path x y) (q : Path y z) :
    twicePuncturedPathClosingWinding (p.trans q).toContinuousMap =
      twicePuncturedPathClosingWinding p.toContinuousMap +
        twicePuncturedPathClosingWinding q.toContinuousMap +
        (twicePuncturedArgumentDeckIncrement p.toContinuousMap).1 *
          (twicePuncturedArgumentDeckIncrement q.toContinuousMap).2 := by
  have h := congrArg (fun w : (ℤ × ℤ) →₀ ℤ => w.sum (fun _ v => v))
    (twicePuncturedClosingWindingTable_native_trans p q)
  dsimp only at h
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_sub_index (fun _ _ _ => rfl)] at h
  change
    phaseGridLoopTotalWinding (twicePuncturedPhaseClosingLoop p.toContinuousMap) +
      phaseGridLoopTotalWinding
        ((twicePuncturedPhaseClosingLoop q.toContinuousMap).map
          (phaseGridDeckTranslation
            (twicePuncturedArgumentDeckIncrement p.toContinuousMap)).continuous) =
    phaseGridLoopTotalWinding
        (twicePuncturedPhaseClosingLoop (p.trans q).toContinuousMap) -
      phaseGridLoopTotalWinding
        (phaseGridDeckDiscrepancyLoop
          (twicePuncturedArgumentDeckIncrement p.toContinuousMap)
          (twicePuncturedArgumentDeckIncrement q.toContinuousMap)) at h
  rw [phaseGridLoopTotalWinding_deck, phaseGridLoopTotalWinding_closing,
    phaseGridLoopTotalWinding_closing, phaseGridLoopTotalWinding_closing,
    phaseGridDeckDiscrepancy_loopTotalWinding] at h
  linarith

end ChenRanks
