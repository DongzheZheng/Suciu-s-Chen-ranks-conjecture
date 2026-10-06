import ChenRanks.SingularCupOne
import ChenRanks.SingularCochainBoundaryValues

/-!
# Closure of the actual Alexander--Whitney product

The cocycle relation is obtained from the genuine dual singular boundary.
The degree-three calculation uses the native simplicial face identities.
No cocycle-product compatibility is assumed.
-/

noncomputable section

open CategoryTheory AlgebraicTopology
open scoped BigOperators

namespace ChenRanks.SingularCohomology

variable (k : Type) [Field k] (X : Type) [TopologicalSpace X]

/-- The true singular degree-one coboundary, on an actual triangle. -/
theorem values_differential_one (a : cochains k X 1) (s : simplices X 2) :
    values k X 2 (differential k X 1 a) s =
      values k X 1 a (edge X 0 s) - values k X 1 a (edge X 1 s) +
        values k X 1 a (edge X 2 s) := by
  rw [values_differential]
  simp [Fin.sum_univ_succ, edge, sub_eq_add_neg, add_assoc]

/-- An original closed one-cochain is additive along the actual triangle edges. -/
theorem closedOne_triangle_relation (a : cochains k X 1)
    (ha : differential k X 1 a = 0) (s : simplices X 2) :
    values k X 1 a (edge X 1 s) =
      values k X 1 a (edge X 2 s) + values k X 1 a (edge X 0 s) := by
  have h := values_differential_one k X a s
  simp only [ha, map_zero, Pi.zero_apply] at h
  linear_combination h

/-- The genuine product of two original closed one-cochains is closed. -/
theorem differential_cupOne_eq_zero (a b : cochains k X 1)
    (ha : differential k X 1 a = 0) (hb : differential k X 1 b = 0) :
    differential k X 2 (cupOne k X a b) = 0 := by
  apply cochain_ext k X 3
  intro s
  change values k X 3 (differential k X 2 (cupOne k X a b)) s = 0
  rw [values_differential]
  simp [Fin.sum_univ_succ, values_cupOne, add_assoc]
  norm_num only [pow_succ, pow_zero, neg_mul, mul_neg, one_mul, mul_one, neg_neg]
  let S := TopCat.toSSet.obj (TopCat.of X)
  have h20 : S.δ (2 : Fin 3) (S.δ (0 : Fin 4) s) =
      S.δ (0 : Fin 3) (S.δ (3 : Fin 4) s) :=
    (S.δ_comp_δ_apply (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide) s).symm
  have h21 : S.δ (2 : Fin 3) (S.δ (1 : Fin 4) s) =
      S.δ (1 : Fin 3) (S.δ (3 : Fin 4) s) :=
    (S.δ_comp_δ_apply (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide) s).symm
  have h22 : S.δ (2 : Fin 3) (S.δ (2 : Fin 4) s) =
      S.δ (2 : Fin 3) (S.δ (3 : Fin 4) s) :=
    (S.δ_comp_δ_apply (i := (2 : Fin 3)) (j := (2 : Fin 3)) (by decide) s).symm
  have h01 : S.δ (0 : Fin 3) (S.δ (1 : Fin 4) s) =
      S.δ (0 : Fin 3) (S.δ (0 : Fin 4) s) :=
    S.δ_comp_δ_apply (i := (0 : Fin 3)) (j := (0 : Fin 3)) (by decide) s
  have h02 : S.δ (0 : Fin 3) (S.δ (2 : Fin 4) s) =
      S.δ (1 : Fin 3) (S.δ (0 : Fin 4) s) :=
    S.δ_comp_δ_apply (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide) s
  have h03 : S.δ (0 : Fin 3) (S.δ (3 : Fin 4) s) =
      S.δ (2 : Fin 3) (S.δ (0 : Fin 4) s) :=
    S.δ_comp_δ_apply (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide) s
  change values k X 1 a (S.δ 2 (S.δ 0 s)) *
        values k X 1 b (S.δ 0 (S.δ 0 s)) +
      (-(values k X 1 a (S.δ 2 (S.δ 1 s)) *
        values k X 1 b (S.δ 0 (S.δ 1 s))) +
      (values k X 1 a (S.δ 2 (S.δ 2 s)) *
        values k X 1 b (S.δ 0 (S.δ 2 s)) +
      -(values k X 1 a (S.δ 2 (S.δ 3 s)) *
        values k X 1 b (S.δ 0 (S.δ 3 s))))) = 0
  rw [congrArg (values k X 1 a) h20, congrArg (values k X 1 a) h21,
    congrArg (values k X 1 a) h22, congrArg (values k X 1 b) h01,
    congrArg (values k X 1 b) h02, congrArg (values k X 1 b) h03]
  have hat := closedOne_triangle_relation k X a ha (S.δ 3 s)
  have hbt := closedOne_triangle_relation k X b hb (S.δ 0 s)
  change values k X 1 a (S.δ 1 (S.δ 3 s)) =
    values k X 1 a (S.δ 2 (S.δ 3 s)) +
      values k X 1 a (S.δ 0 (S.δ 3 s)) at hat
  change values k X 1 b (S.δ 1 (S.δ 0 s)) =
    values k X 1 b (S.δ 2 (S.δ 0 s)) +
      values k X 1 b (S.δ 0 (S.δ 0 s)) at hbt
  rw [hat, hbt]
  ring

end ChenRanks.SingularCohomology
