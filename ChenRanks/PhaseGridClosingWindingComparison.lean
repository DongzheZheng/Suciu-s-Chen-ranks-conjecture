import ChenRanks.PhaseGridTotalWindingOperations

/-!
# Comparing the actual closing loops from actual middle-path increments

Expanding the genuine four-piece closing loops shows that equal actual
endpoint data, equal actual deck increments and equal puncture increments
of the actual lifted middle paths give equal actual finite winding tables.
The geometric triangle construction separately proves these concrete
equalities when applying this helper. No cohomology vanishing is assumed.
-/

noncomputable section

open unitInterval

namespace ChenRanks

def phaseGridPuncturePathIncrement {x y : PhaseGridComplement}
    (i : ℤ × ℤ) (p : Path x y) : ℤ :=
  circlePathIntegerIncrement
    (p.map (phaseGridPointCircleMap i).continuous).toContinuousMap

theorem phaseGridPuncturePathIncrement_trans
    {x y z : PhaseGridComplement} (i : ℤ × ℤ) (p : Path x y) (q : Path y z) :
    phaseGridPuncturePathIncrement i (p.trans q) =
      phaseGridPuncturePathIncrement i p + phaseGridPuncturePathIncrement i q := by
  unfold phaseGridPuncturePathIncrement
  rw [Path.map_trans, circlePathIntegerIncrement_native_trans]

theorem phaseGridPuncturePathIncrement_symm
    {x y : PhaseGridComplement} (i : ℤ × ℤ) (p : Path x y) :
    phaseGridPuncturePathIncrement i p.symm = -phaseGridPuncturePathIncrement i p := by
  change circlePathIntegerIncrement
    (p.map (phaseGridPointCircleMap i).continuous).symm.toContinuousMap = _
  exact circlePathIntegerIncrement_native_symm _

theorem phaseGridClosingWindingTable_apply
    (γ : C(I, TwicePuncturedComplex)) (i : ℤ × ℤ) :
    phaseGridLoopWindingTable (twicePuncturedPhaseClosingLoop γ) i =
      phaseGridPuncturePathIncrement i (phaseGridPrincipalPath (γ 0)) +
        phaseGridPuncturePathIncrement i (phaseGridLiftedOriginalPath γ) -
        phaseGridPuncturePathIncrement i
          (phaseGridTranslatedPrincipalPath (twicePuncturedArgumentDeckIncrement γ) (γ 1)) -
        phaseGridPuncturePathIncrement i
          (phaseGridDeckPath (twicePuncturedArgumentDeckIncrement γ)) := by
  change phaseGridPuncturePathIncrement i (twicePuncturedPhaseClosingLoop γ) = _
  rw [twicePuncturedPhaseClosingLoop, phaseGridPuncturePathIncrement_trans,
    phaseGridPuncturePathIncrement_trans, phaseGridPuncturePathIncrement_trans,
    phaseGridPuncturePathIncrement_symm, phaseGridPuncturePathIncrement_symm]
  rfl

theorem phaseGridClosingWindingTable_eq_of_lift_increments
    (γ δ : C(I, TwicePuncturedComplex))
    (h0 : γ 0 = δ 0) (h1 : γ 1 = δ 1)
    (hn : twicePuncturedArgumentDeckIncrement γ = twicePuncturedArgumentDeckIncrement δ)
    (hlift : ∀ i : ℤ × ℤ,
      phaseGridPuncturePathIncrement i (phaseGridLiftedOriginalPath γ) =
        phaseGridPuncturePathIncrement i (phaseGridLiftedOriginalPath δ)) :
    phaseGridLoopWindingTable (twicePuncturedPhaseClosingLoop γ) =
      phaseGridLoopWindingTable (twicePuncturedPhaseClosingLoop δ) := by
  apply Finsupp.ext
  intro i
  rw [phaseGridClosingWindingTable_apply, phaseGridClosingWindingTable_apply,
    hlift i, h0, h1, hn]

theorem twicePuncturedPathClosingWinding_eq_of_lift_increments
    (γ δ : C(I, TwicePuncturedComplex))
    (h0 : γ 0 = δ 0) (h1 : γ 1 = δ 1)
    (hn : twicePuncturedArgumentDeckIncrement γ = twicePuncturedArgumentDeckIncrement δ)
    (hlift : ∀ i : ℤ × ℤ,
      phaseGridPuncturePathIncrement i (phaseGridLiftedOriginalPath γ) =
        phaseGridPuncturePathIncrement i (phaseGridLiftedOriginalPath δ)) :
    twicePuncturedPathClosingWinding γ = twicePuncturedPathClosingWinding δ := by
  rw [← phaseGridLoopTotalWinding_closing, ← phaseGridLoopTotalWinding_closing]
  unfold phaseGridLoopTotalWinding
  rw [phaseGridClosingWindingTable_eq_of_lift_increments γ δ h0 h1 hn hlift]

end ChenRanks
