import ChenRanks.PhaseGridTotalWindingOperations

/-!
# Genuine concatenation of the selected lifted paths

The paths below are the already constructed lifts of the two original
phase paths of z and 1-z. Their endpoints are expressed using the actual
integers extracted from the covering lift. Concatenating the first lift
with the deck translate of the second produces the selected lift of the
original concatenated path. The proof uses uniqueness for the actual
covering map Circle.exp, separately in the two real coordinates.

No lift equality, loop homotopy, winding identity, or cup-product
vanishing is assumed. This is only the path-level bridge needed to use
the genuine closing loops in the subsequent cochain construction.
-/

noncomputable section

open unitInterval

namespace ChenRanks

/-- The actual deck vector is additive in its actual integer index. -/
theorem windingPhaseDeckPoint_add (n m : ℤ × ℤ) :
    windingPhaseDeckPoint (n + m) =
      windingPhaseDeckPoint n + windingPhaseDeckPoint m := by
  apply Prod.ext
  · change ((n.1 + m.1 : ℤ) : ℝ) * (2 * Real.pi) =
      (n.1 : ℝ) * (2 * Real.pi) + (m.1 : ℝ) * (2 * Real.pi)
    rw [Int.cast_add, add_mul]
  · change ((n.2 + m.2 : ℤ) : ℝ) * (2 * Real.pi) =
      (n.2 : ℝ) * (2 * Real.pi) + (m.2 : ℝ) * (2 * Real.pi)
    rw [Int.cast_add, add_mul]

/-- Actual deck translations compose according to their actual indices. -/
theorem phaseGridDeckTranslation_add_apply (n m : ℤ × ℤ)
    (x : PhaseGridComplement) :
    phaseGridDeckTranslation (n + m) x =
      phaseGridDeckTranslation n (phaseGridDeckTranslation m x) := by
  apply Subtype.ext
  change x.val + windingPhaseDeckPoint (n + m) =
    (x.val + windingPhaseDeckPoint m) + windingPhaseDeckPoint n
  rw [windingPhaseDeckPoint_add]
  abel

/-- Actual deck translation preserves the two actual exponential phases. -/
theorem argumentPlanePhaseMap_deckTranslation (n : ℤ × ℤ)
    (x : PhaseGridComplement) :
    argumentPlanePhaseMap (phaseGridDeckTranslation n x).val =
      argumentPlanePhaseMap x.val := by
  change (Circle.exp (x.val.1 + (n.1 : ℝ) * (2 * Real.pi)),
    Circle.exp (x.val.2 + (n.2 : ℝ) * (2 * Real.pi))) =
      (Circle.exp x.val.1, Circle.exp x.val.2)
  simp only [Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]

/-- The same genuine selected lift, with native original endpoints.
The endpoint casts use the actual source and target identities of p. -/
def phaseGridNativeLiftedPath {x y : TwicePuncturedComplex} (p : Path x y) :
    Path (phaseGridPrincipalPoint x)
      (phaseGridDeckTranslation (twicePuncturedArgumentDeckIncrement p.toContinuousMap)
        (phaseGridPrincipalPoint y)) :=
  (phaseGridLiftedOriginalPath p.toContinuousMap).cast
    (by simp only [Path.coe_toContinuousMap, Path.source])
    (by simp only [Path.coe_toContinuousMap, Path.target])

@[simp] theorem phaseGridNativeLiftedPath_val
    {x y : TwicePuncturedComplex} (p : Path x y) (t : I) :
    (phaseGridNativeLiftedPath p t).val =
      twicePuncturedPathArgumentPair p.toContinuousMap t := rfl

/-- This lift projects to the phases of the actual original path at
every parameter value, including the actual source and target. -/
theorem phaseGridNativeLiftedPath_projects
    {x y : TwicePuncturedComplex} (p : Path x y) (t : I) :
    argumentPlanePhaseMap (phaseGridNativeLiftedPath p t).val =
      twicePuncturedComplexPhasePair (p t) := by
  change
    (Circle.exp (circlePathArgumentLift
      (twicePuncturedComplexZeroPhase.comp p.toContinuousMap) t),
      Circle.exp (circlePathArgumentLift
        (twicePuncturedComplexOnePhase.comp p.toContinuousMap) t)) =
    (twicePuncturedComplexZeroPhase (p t), twicePuncturedComplexOnePhase (p t))
  exact Prod.ext
    (circlePathArgumentLift_projects
      (twicePuncturedComplexZeroPhase.comp p.toContinuousMap) t)
    (circlePathArgumentLift_projects
      (twicePuncturedComplexOnePhase.comp p.toContinuousMap) t)

private theorem phaseGridTranslatedNativeLiftedPath_target
    {x y z : TwicePuncturedComplex} (p : Path x y) (q : Path y z) :
    phaseGridDeckTranslation
        (twicePuncturedArgumentDeckIncrement (p.trans q).toContinuousMap)
        (phaseGridPrincipalPoint z) =
      phaseGridDeckTranslation
        (twicePuncturedArgumentDeckIncrement p.toContinuousMap)
        (phaseGridDeckTranslation
          (twicePuncturedArgumentDeckIncrement q.toContinuousMap)
          (phaseGridPrincipalPoint z)) := by
  rw [twicePuncturedArgumentDeckIncrement_native_trans,
    phaseGridDeckTranslation_add_apply]

/-- The second genuine lift, translated by the first genuine integer
increment. Its actual terminal point is the actual terminal point of
the lift of p.trans q, by the previously proved increment additivity. -/
def phaseGridTranslatedNativeLiftedPath
    {x y z : TwicePuncturedComplex} (p : Path x y) (q : Path y z) :
    Path
      (phaseGridDeckTranslation (twicePuncturedArgumentDeckIncrement p.toContinuousMap)
        (phaseGridPrincipalPoint y))
      (phaseGridDeckTranslation
        (twicePuncturedArgumentDeckIncrement (p.trans q).toContinuousMap)
        (phaseGridPrincipalPoint z)) :=
  ((phaseGridNativeLiftedPath q).map
    (phaseGridDeckTranslation
      (twicePuncturedArgumentDeckIncrement p.toContinuousMap)).continuous).cast
    rfl (phaseGridTranslatedNativeLiftedPath_target p q)

@[simp] theorem phaseGridTranslatedNativeLiftedPath_apply
    {x y z : TwicePuncturedComplex} (p : Path x y) (q : Path y z) (t : I) :
    phaseGridTranslatedNativeLiftedPath p q t =
      phaseGridDeckTranslation
        (twicePuncturedArgumentDeckIncrement p.toContinuousMap)
        (phaseGridNativeLiftedPath q t) := rfl

/-- Genuine uniqueness in the grid complement follows from genuine
covering-space uniqueness for Circle.exp in each coordinate. -/
theorem phaseGridPath_eq_of_projected_phase_eq
    {x y : PhaseGridComplement} (p q : Path x y)
    (hphase : ∀ t : I, argumentPlanePhaseMap (p t).val =
      argumentPlanePhaseMap (q t).val) : p = q := by
  let p₁ : C(I, ℝ) := ⟨fun t => (p t).val.1,
    continuous_fst.comp (continuous_subtype_val.comp p.continuous)⟩
  let q₁ : C(I, ℝ) := ⟨fun t => (q t).val.1,
    continuous_fst.comp (continuous_subtype_val.comp q.continuous)⟩
  let p₂ : C(I, ℝ) := ⟨fun t => (p t).val.2,
    continuous_snd.comp (continuous_subtype_val.comp p.continuous)⟩
  let q₂ : C(I, ℝ) := ⟨fun t => (q t).val.2,
    continuous_snd.comp (continuous_subtype_val.comp q.continuous)⟩
  have h₁ : Circle.exp ∘ p₁ = Circle.exp ∘ q₁ := by
    funext t
    exact congrArg Prod.fst (hphase t)
  have h₂ : Circle.exp ∘ p₂ = Circle.exp ∘ q₂ := by
    funext t
    exact congrArg Prod.snd (hphase t)
  have h₁₀ : p₁ 0 = q₁ 0 := by
    change (p 0).val.1 = (q 0).val.1
    rw [Path.source, Path.source]
  have h₂₀ : p₂ 0 = q₂ 0 := by
    change (p 0).val.2 = (q 0).val.2
    rw [Path.source, Path.source]
  have he₁ : (p₁ : I → ℝ) = q₁ :=
    Circle.isCoveringMap_exp.eq_of_comp_eq p₁.continuous q₁.continuous h₁ 0 h₁₀
  have he₂ : (p₂ : I → ℝ) = q₂ :=
    Circle.isCoveringMap_exp.eq_of_comp_eq p₂.continuous q₂.continuous h₂ 0 h₂₀
  apply Path.ext
  funext t
  apply Subtype.ext
  exact Prod.ext (congrFun he₁ t) (congrFun he₂ t)

/-- The actual concatenation of the first lift and the actual translate
of the second projects to the actual concatenation of the original
phase paths. The piecewise parameter is the native Path.trans parameter. -/
theorem phaseGridNativeLiftedPath_trans_projects
    {x y z : TwicePuncturedComplex} (p : Path x y) (q : Path y z) (t : I) :
    argumentPlanePhaseMap
      (((phaseGridNativeLiftedPath p).trans
        (phaseGridTranslatedNativeLiftedPath p q)) t).val =
      twicePuncturedComplexPhasePair ((p.trans q) t) := by
  simp only [Path.trans_apply]
  split_ifs with ht
  · exact phaseGridNativeLiftedPath_projects p _
  · rw [phaseGridTranslatedNativeLiftedPath_apply,
      argumentPlanePhaseMap_deckTranslation]
    exact phaseGridNativeLiftedPath_projects q _

/-- Selected lifting commutes with native concatenation after the
genuine deck translate required by the genuine first integer increment.
This is an equality of actual native paths, with actual matching endpoints. -/
theorem phaseGridNativeLiftedPath_trans
    {x y z : TwicePuncturedComplex} (p : Path x y) (q : Path y z) :
    phaseGridNativeLiftedPath (p.trans q) =
      (phaseGridNativeLiftedPath p).trans (phaseGridTranslatedNativeLiftedPath p q) := by
  apply phaseGridPath_eq_of_projected_phase_eq
  intro t
  exact (phaseGridNativeLiftedPath_projects (p.trans q) t).trans
    (phaseGridNativeLiftedPath_trans_projects p q t).symm

/-- The same concatenation identity for the literal real argument pair
used in the previously constructed closing loop. -/
theorem twicePuncturedPathArgumentPair_native_trans
    {x y z : TwicePuncturedComplex} (p : Path x y) (q : Path y z) (t : I) :
    twicePuncturedPathArgumentPair (p.trans q).toContinuousMap t =
      (((phaseGridNativeLiftedPath p).trans
        (phaseGridTranslatedNativeLiftedPath p q)) t).val := by
  rw [← phaseGridNativeLiftedPath_val, phaseGridNativeLiftedPath_trans]

end ChenRanks
