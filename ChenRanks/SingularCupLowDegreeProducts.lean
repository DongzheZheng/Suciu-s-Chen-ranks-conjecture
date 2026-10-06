import ChenRanks.SingularCupOne

/-!
# Actual low-degree cochain products and the commutativity homotopy

Every product is defined on the original singular cochains via the
proved native simplex-value equivalence. Later differential identities
use these actual cochains to prove independence of cocycle representatives.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace ChenRanks.SingularCohomology

variable (k : Type) [Field k] (X : Type) [TopologicalSpace X]

/-- An actual endpoint of an original singular edge. -/
def vertex (i : Fin 2) : simplices X 1 → simplices X 0 :=
  (TopCat.toSSet.obj (TopCat.of X)).δ i

/-- Values of an actual zero-cochain on an actual endpoint. -/
def vertexValues (i : Fin 2) : cochains k X 0 →ₗ[k] (simplices X 1 → k) where
  toFun a s := values k X 0 a (vertex X i s)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual degree-zero by degree-one Alexander--Whitney product. -/
def cupZeroOne : cochains k X 0 →ₗ[k] cochains k X 1 →ₗ[k] cochains k X 1 :=
  ((LinearMap.mul k (simplices X 1 → k)).compl₁₂
    (vertexValues k X 1) (values k X 1)).compr₂
      (valuesEquiv k X 1).symm.toLinearMap

/-- The actual degree-one by degree-zero Alexander--Whitney product. -/
def cupOneZero : cochains k X 1 →ₗ[k] cochains k X 0 →ₗ[k] cochains k X 1 :=
  ((LinearMap.mul k (simplices X 1 → k)).compl₁₂
    (values k X 1) (vertexValues k X 0)).compr₂
      (valuesEquiv k X 1).symm.toLinearMap

/-- The actual pointwise product on singular edges. Its differential
supplies the degree-one commutativity homotopy. -/
def edgePointProduct : cochains k X 1 →ₗ[k] cochains k X 1 →ₗ[k] cochains k X 1 :=
  ((LinearMap.mul k (simplices X 1 → k)).compl₁₂
    (values k X 1) (values k X 1)).compr₂
      (valuesEquiv k X 1).symm.toLinearMap

/-- The zero-one product has the original starting-vertex simplex value. -/
theorem values_cupZeroOne (a : cochains k X 0) (b : cochains k X 1)
    (s : simplices X 1) :
    values k X 1 (cupZeroOne k X a b) s =
      values k X 0 a (vertex X 1 s) * values k X 1 b s := by
  change (valuesEquiv k X 1)
    ((valuesEquiv k X 1).symm ((vertexValues k X 1 a) * (values k X 1 b))) s = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The one-zero product has the original ending-vertex simplex value. -/
theorem values_cupOneZero (a : cochains k X 1) (b : cochains k X 0)
    (s : simplices X 1) :
    values k X 1 (cupOneZero k X a b) s =
      values k X 1 a s * values k X 0 b (vertex X 0 s) := by
  change (valuesEquiv k X 1)
    ((valuesEquiv k X 1).symm ((values k X 1 a) * (vertexValues k X 0 b))) s = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The homotopy cochain has the literal product of the actual edge values. -/
theorem values_edgePointProduct (a b : cochains k X 1) (s : simplices X 1) :
    values k X 1 (edgePointProduct k X a b) s =
      values k X 1 a s * values k X 1 b s := by
  change (valuesEquiv k X 1)
    ((valuesEquiv k X 1).symm ((values k X 1 a) * (values k X 1 b))) s = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end ChenRanks.SingularCohomology
