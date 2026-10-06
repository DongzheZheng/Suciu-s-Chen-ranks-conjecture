import ChenRanks.SingularClosedCocyclePathReversal
import ChenRanks.SingularPathCocycleAdditivity
import ChenRanks.SingularSquareCocycleHomotopy
import Mathlib.Topology.Subpath

/-! Actual finite-path values and native loop-homotopy invariance.

The finite concatenation formula follows from the native concat recursion
and the proved genuine two-path triangle. Loop-homotopy invariance follows
from the actual two triangles of the square. No integration rule or
cohomological classification is a premise. -/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

variable (X : Type) [TopologicalSpace X] (k : Type) [Field k]

theorem actualPathCochainValue_concat
    (β : cochains k X 1) (hβ : differential k X 1 β = 0) (n : ℕ) :
    ∀ (p : Fin (n + 1) → X) (F : (i : Fin n) → Path (p i.castSucc) (p i.succ)),
      actualPathCochainValue k X β (Path.concat p F) =
        ∑ i : Fin n, actualPathCochainValue k X β (F i) := by
  induction n with
  | zero =>
    intro p F
    rw [Path.concat_zero]
    simp only [Fin.sum_univ_zero]
    exact closedOne_constant_path_value_eq_zero k X β hβ (p 0)
  | succ n ih =>
    intro p F
    rw [Path.concat_succ]
    have ht := actualPathCochainValue_trans k X β hβ
      (Path.concat (p ∘ Fin.castSucc) (fun i : Fin n => F i.castSucc)) (F (Fin.last n))
    have hi := ih (p ∘ Fin.castSucc) (fun i => F i.castSucc)
    have hs := Fin.sum_univ_castSucc (fun i : Fin (n + 1) => actualPathCochainValue k X β (F i))
    unfold actualPathCochainValue at ht hi hs ⊢
    linear_combination ht + hi - hs

/-- This loop theorem retains the actual native cochain value and
actual endpoint equality through the genuine fixed-endpoint homotopy. -/
theorem actualPathCochainValue_eq_of_loop_homotopy
    (β : cochains k X 1) (hβ : differential k X 1 β = 0)
    {x y : X} (hxy : x = y) {p q : Path x y} (H : p.Homotopy q) :
    actualPathCochainValue k X β p = actualPathCochainValue k X β q := by
  let F : C(I × I, X) := ⟨fun z => H (z.2, z.1), H.continuous.comp continuous_swap⟩
  have hv : ∀ s : I, F (1, s) = F (0, s) := by
    intro s
    change H (s, 1) = H (s, 0)
    rw [Path.Homotopy.target, Path.Homotopy.source]
    exact hxy.symm
  have hb : squareBottomPath X F = p.toContinuousMap := by
    apply ContinuousMap.ext
    intro t
    exact H.toHomotopy.apply_zero t
  have ht : squareTopPath X F = q.toContinuousMap := by
    apply ContinuousMap.ext
    intro t
    exact H.toHomotopy.apply_one t
  have h := closedCochain_values_squareBottom_eq_top X k F hv β hβ
  simpa only [hb, ht, actualPathCochainValue] using h

end ChenRanks.SingularCohomology

namespace ChenRanks

/-- The actual finite adjacent-edge sum telescopes, including n=0. -/
theorem fin_adjacent_difference_sum {k : Type*} [Field k]
    (n : ℕ) (L : Fin (n + 1) → k) :
    (∑ i : Fin n, (L i.succ - L i.castSucc)) = L (Fin.last n) - L 0 := by
  rw [Finset.sum_sub_distrib]
  have hs := Fin.sum_univ_succ L
  have hc := Fin.sum_univ_castSucc L
  linear_combination hc - hs

end ChenRanks
