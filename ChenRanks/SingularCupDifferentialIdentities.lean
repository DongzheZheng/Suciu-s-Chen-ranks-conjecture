import ChenRanks.SingularCupCocycles
import ChenRanks.SingularCupLowDegreeProducts

/-!
# Genuine boundary and skew-commutativity identities

These are equalities in the original singular cochain modules. They
supply actual boundary representatives for the change-of-representative
and skew-commutativity identities required on actual cohomology.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace ChenRanks.SingularCohomology

variable (k : Type) [Field k] (X : Type) [TopologicalSpace X]

/-- The genuine zero-cochain differential is ending value minus starting value. -/
theorem values_differential_zero (a : cochains k X 0) (s : simplices X 1) :
    values k X 1 (differential k X 0 a) s =
      values k X 0 a (vertex X 0 s) - values k X 0 a (vertex X 1 s) := by
  rw [values_differential]
  simp [Fin.sum_univ_succ, vertex, sub_eq_add_neg]

/-- Changing the first closed representative by an actual boundary
changes the product by this actual coboundary. -/
theorem differential_cupZeroOne (a : cochains k X 0) (b : cochains k X 1)
    (hb : differential k X 1 b = 0) :
    differential k X 1 (cupZeroOne k X a b) =
      cupOne k X (differential k X 0 a) b := by
  apply cochain_ext k X 2
  intro s
  change values k X 2 (differential k X 1 (cupZeroOne k X a b)) s =
    values k X 2 (cupOne k X (differential k X 0 a) b) s
  rw [values_differential_one, values_cupOne]
  simp only [values_cupZeroOne, values_differential_zero]
  let S := TopCat.toSSet.obj (TopCat.of X)
  have h11 : S.δ (1 : Fin 2) (S.δ (1 : Fin 3) s) =
      S.δ (1 : Fin 2) (S.δ (2 : Fin 3) s) :=
    S.δ_comp_δ_self_apply (i := (1 : Fin 2)) s
  have h02 : S.δ (0 : Fin 2) (S.δ (2 : Fin 3) s) =
      S.δ (1 : Fin 2) (S.δ (0 : Fin 3) s) :=
    S.δ_comp_δ_apply (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide) s
  change values k X 0 a (S.δ 1 (S.δ 0 s)) * values k X 1 b (S.δ 0 s) -
      values k X 0 a (S.δ 1 (S.δ 1 s)) * values k X 1 b (S.δ 1 s) +
      values k X 0 a (S.δ 1 (S.δ 2 s)) * values k X 1 b (S.δ 2 s) =
    (values k X 0 a (S.δ 0 (S.δ 2 s)) -
      values k X 0 a (S.δ 1 (S.δ 2 s))) * values k X 1 b (S.δ 0 s)
  rw [h11, h02]
  have ht := closedOne_triangle_relation k X b hb s
  change values k X 1 b (S.δ 1 s) =
    values k X 1 b (S.δ 2 s) + values k X 1 b (S.δ 0 s) at ht
  rw [ht]
  ring

/-- Changing the second closed representative by an actual boundary
changes the product by minus this actual coboundary. -/
theorem differential_cupOneZero (a : cochains k X 1) (b : cochains k X 0)
    (ha : differential k X 1 a = 0) :
    differential k X 1 (cupOneZero k X a b) =
      -(cupOne k X a (differential k X 0 b)) := by
  apply cochain_ext k X 2
  intro s
  change values k X 2 (differential k X 1 (cupOneZero k X a b)) s =
    values k X 2 (-(cupOne k X a (differential k X 0 b))) s
  rw [values_differential_one]
  simp only [map_neg, Pi.neg_apply, values_cupOne,
    values_cupOneZero, values_differential_zero]
  let S := TopCat.toSSet.obj (TopCat.of X)
  have h01 : S.δ (0 : Fin 2) (S.δ (1 : Fin 3) s) =
      S.δ (0 : Fin 2) (S.δ (0 : Fin 3) s) :=
    S.δ_comp_δ_apply (i := (0 : Fin 2)) (j := (0 : Fin 2)) (by decide) s
  have h10 : S.δ (1 : Fin 2) (S.δ (0 : Fin 3) s) =
      S.δ (0 : Fin 2) (S.δ (2 : Fin 3) s) :=
    (S.δ_comp_δ_apply (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide) s).symm
  change values k X 1 a (S.δ 0 s) * values k X 0 b (S.δ 0 (S.δ 0 s)) -
      values k X 1 a (S.δ 1 s) * values k X 0 b (S.δ 0 (S.δ 1 s)) +
      values k X 1 a (S.δ 2 s) * values k X 0 b (S.δ 0 (S.δ 2 s)) =
    -(values k X 1 a (S.δ 2 s) *
      (values k X 0 b (S.δ 0 (S.δ 0 s)) -
        values k X 0 b (S.δ 1 (S.δ 0 s))))
  rw [h01, h10]
  have ht := closedOne_triangle_relation k X a ha s
  change values k X 1 a (S.δ 1 s) =
    values k X 1 a (S.δ 2 s) + values k X 1 a (S.δ 0 s) at ht
  rw [ht]
  ring

/-- The original one-cochain point product is a genuine homotopy
between the two cup orders on original closed representatives. -/
theorem differential_edgePointProduct (a b : cochains k X 1)
    (ha : differential k X 1 a = 0) (hb : differential k X 1 b = 0) :
    differential k X 1 (edgePointProduct k X a b) =
      -(cupOne k X a b + cupOne k X b a) := by
  apply cochain_ext k X 2
  intro s
  change values k X 2 (differential k X 1 (edgePointProduct k X a b)) s =
    values k X 2 (-(cupOne k X a b + cupOne k X b a)) s
  rw [values_differential_one]
  simp only [map_neg, Pi.neg_apply, map_add, Pi.add_apply,
    values_edgePointProduct, values_cupOne]
  rw [closedOne_triangle_relation k X a ha s,
    closedOne_triangle_relation k X b hb s]
  ring

end ChenRanks.SingularCohomology
