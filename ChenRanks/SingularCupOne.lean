import ChenRanks.SingularSimplexCochains
import Mathlib.LinearAlgebra.BilinearMap

/-!
# The actual Alexander--Whitney cochain product in degrees one and one

On an actual singular two-simplex the value is the value of the first
cochain on its edge [0,1] times the value of the second on [1,2]. The native
coproduct equivalence extends these values to the original chain module.

This source constructs the true bilinear cochain product. Descent to the
actual cohomology objects, alternation on cohomology, and identification
with logarithmic forms remain separate proofs.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace ChenRanks.SingularCohomology

variable (k : Type) [Field k] (X : Type) [TopologicalSpace X]

/-- A genuine edge of a genuine singular two-simplex, via the native face map. -/
def edge (i : Fin 3) : simplices X 2 → simplices X 1 :=
  (TopCat.toSSet.obj (TopCat.of X)).δ i

/-- Restriction of original cochain values to an actual edge of each two-simplex. -/
def edgeValues (i : Fin 3) : cochains k X 1 →ₗ[k] (simplices X 2 → k) where
  toFun a s := values k X 1 a (edge X i s)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The native bilinear Alexander--Whitney product of two degree-one cochains. -/
def cupOne : cochains k X 1 →ₗ[k] cochains k X 1 →ₗ[k] cochains k X 2 :=
  ((LinearMap.mul k (simplices X 2 → k)).compl₁₂
    (edgeValues k X 2) (edgeValues k X 0)).compr₂
      (valuesEquiv k X 2).symm.toLinearMap

/-- The product on the original chain module has exactly its genuine simplex values. -/
theorem values_cupOne (a b : cochains k X 1) (s : simplices X 2) :
    values k X 2 (cupOne k X a b) s =
      values k X 1 a (edge X 2 s) * values k X 1 b (edge X 0 s) := by
  change (valuesEquiv k X 2)
    ((valuesEquiv k X 2).symm ((edgeValues k X 2 a) * (edgeValues k X 0 b))) s = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end ChenRanks.SingularCohomology
