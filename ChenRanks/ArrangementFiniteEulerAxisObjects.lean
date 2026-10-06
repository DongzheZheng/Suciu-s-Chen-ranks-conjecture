import ChenRanks.ArrangementFiniteEulerLogarithmicCoefficients
import ChenRanks.NativeEulerAxisAbelianCharacter

/-! The original finite model's native degree-two quotient and original
generator classes. These algebraic objects precede the local analytic
frame and period constructions; their definitions are unchanged.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

open LieComparison

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι) (c : ℕ)

abbrev ActualFiniteEulerAxisQuotient :=
  A.ActualFiniteLogarithmicLie c ⧸ nativeGradedTail ℂ
    (A.ActualFiniteLogarithmicLie c) (A.actualFiniteLogarithmicComponent c) 2

/-- Each original label has its actual original vector class in the
actual degree-two quotient. -/
def actualFiniteEulerAxisGeneratorClass (H : ι) : A.ActualFiniteEulerAxisQuotient c :=
  (nativeGradedTail ℂ (A.ActualFiniteLogarithmicLie c)
    (A.actualFiniteLogarithmicComponent c) 2).mkQ
    (A.actualHolonomyToFiniteLogarithmicLie c
      (A.actualLogHolonomyGeneratorMap (LinearMap.proj H)))

end ChenRanks.AffineArrangement
