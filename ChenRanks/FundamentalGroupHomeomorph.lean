import ChenRanks.FundamentalGroupProduct

/-!
# Actual pointed fundamental-group comparison under a homeomorphism

The native fundamental-groupoid functor of the original homeomorphism
is fully faithful by its genuine homotopy equivalence. Restriction to
the original vertex endomorphisms gives the actual group equivalence,
with optional transport along an actual basepoint equality.
-/

noncomputable section

namespace ChenRanks

open CategoryTheory

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The original homeomorphism induces an actual pointed group
equivalence on the native homotopy classes of loops. -/
def fundamentalGroupHomeomorphEquiv (e : X ≃ₜ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) := by
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e.toHomotopyEquiv
  exact MulEquiv.ofBijective (E.functor.mapEnd (FundamentalGroupoid.mk x))
    (E.fullyFaithfulFunctor.map_bijective (FundamentalGroupoid.mk x)
      (FundamentalGroupoid.mk x))

/-- The same original pointed equivalence, transported only along the
given actual equality of target basepoints. -/
def fundamentalGroupHomeomorphEquivOfEq (e : X ≃ₜ Y) (x : X) (y : Y) (h : e x = y) :
    FundamentalGroup X x ≃* FundamentalGroup Y y :=
  (fundamentalGroupHomeomorphEquiv e x).trans
    (eqToIso (congrArg FundamentalGroupoid.mk h)).conj

end ChenRanks
