import ChenRanks.SingularPathConcatenationTriangle

/-!
# Actual closed-cochain values under actual path concatenation

The additive formula follows by evaluating the genuine singular
coboundary on the explicitly constructed native triangle. It is not
postulated as a path integration rule.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

variable (k : Type) [Field k] (X : Type) [TopologicalSpace X]

/-- Evaluate the original singular one-cochain on the original simplex
of a path, retaining the actual endpoints in the type. -/
def actualPathCochainValue (a : cochains k X 1) {x y : X} (p : Path x y) : k :=
  values k X 1 a (simplexOfPath X p.toContinuousMap)

/-- Actual closed one-cochains are additive under actual concatenation,
by their genuine native triangle relation. -/
theorem actualPathCochainValue_trans (a : cochains k X 1)
    (ha : differential k X 1 a = 0) {x y z : X}
    (p : Path x y) (q : Path y z) :
    actualPathCochainValue k X a (p.trans q) =
      actualPathCochainValue k X a p + actualPathCochainValue k X a q := by
  have ht := closedOne_triangle_relation k X a ha (pathConcatenationTriangle X p q)
  simpa [edge_pathConcatenationTriangle, actualPathCochainValue] using ht

/-- If a genuine closed cochain vanishes on all genuine closed paths,
its value on any path is the difference of values on genuinely chosen
paths from a basepoint. Path connectedness provides those paths. -/
theorem actualPathCochainValue_eq_endpoint_difference
    [PathConnectedSpace X] (a : cochains k X 1)
    (ha : differential k X 1 a = 0)
    (hloops : ∀ γ : C(I, X), γ 0 = γ 1 →
      values k X 1 a (simplexOfPath X γ) = 0)
    (base : X) {x y : X} (p : Path x y) :
    actualPathCochainValue k X a p =
      actualPathCochainValue k X a (PathConnectedSpace.somePath base y) -
        actualPathCochainValue k X a (PathConnectedSpace.somePath base x) := by
  let px := PathConnectedSpace.somePath base x
  let py := PathConnectedSpace.somePath base y
  let γ := (px.trans p).trans py.symm
  have hγ : actualPathCochainValue k X a γ = 0 :=
    hloops γ.toContinuousMap (by change γ 0 = γ 1; simp)
  have hy : actualPathCochainValue k X a (py.trans py.symm) = 0 :=
    hloops (py.trans py.symm).toContinuousMap (by simp)
  change actualPathCochainValue k X a ((px.trans p).trans py.symm) = 0 at hγ
  rw [actualPathCochainValue_trans k X a ha,
    actualPathCochainValue_trans k X a ha] at hγ
  rw [actualPathCochainValue_trans k X a ha] at hy
  change actualPathCochainValue k X a p =
    actualPathCochainValue k X a py - actualPathCochainValue k X a px
  linear_combination hγ - hy

end ChenRanks.SingularCohomology
