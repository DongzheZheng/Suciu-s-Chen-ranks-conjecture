import ChenRanks.ValuationKernelDifferentials
import ChenRanks.ExteriorSeparation

/-!
# Expanding the actual coefficients of a mixed logarithmic relation

Membership in the actual logarithmic image supplies genuine coefficient
vectors. Bilinearity over the actual function field, with the original
complex scalar action explicitly compared, gives exactly the double sum
used in horizontal residue detection. This statement does not assume an
identification between an original basis and a model's native basis.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks

variable {G : Type*} [Field G] [Algebra ℂ G]
  {j i : Type*} [Fintype j] [Fintype i]

/-- The original complex logarithmic combination expands in the actual
function-field exterior square with the actual scalar embedding. -/
theorem relativeLogCombination_exteriorWedge
    (F : j → Gˣ) (β : j → ℂ) (p : Ω[G⁄ℂ]) :
    exteriorWedge (k := G) (relativeLogCombination (L := ℂ) F β) p =
      ∑ a, algebraMap ℂ G (β a) • exteriorWedge (k := G)
        (logarithmicDifferential ℂ G (F a)) p := by
  change exteriorWedgeBilin (k := G)
    (∑ a, β a • logarithmicDifferential ℂ G (F a)) p = _
  rw [map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [← IsScalarTower.algebraMap_smul G (β a)
    (logarithmicDifferential ℂ G (F a)), map_smul, LinearMap.smul_apply]
  rfl

/-- Actual image membership and a mixed relation construct its genuine
coefficient matrix and the exact double-sum relation. -/
theorem exists_actual_logarithmic_mixed_coefficient_matrix
    (F : j → Gˣ) (p g : i → Ω[G⁄ℂ])
    (hg : ∀ t, g t ∈ LinearMap.range (relativeLogCombination (L := ℂ) F))
    (hrelation : (∑ t, exteriorWedge (k := G) (g t) (p t)) = 0) :
    ∃ β : i → j → ℂ,
      (∀ t, relativeLogCombination (L := ℂ) F (β t) = g t) ∧
      (∑ t, ∑ a, algebraMap ℂ G (β t a) • exteriorWedge (k := G)
        (logarithmicDifferential ℂ G (F a)) (p t)) = 0 := by
  classical
  choose β hβ using hg
  refine ⟨β, hβ, ?_⟩
  calc
    (∑ t, ∑ a, algebraMap ℂ G (β t a) • exteriorWedge (k := G)
      (logarithmicDifferential ℂ G (F a)) (p t)) =
        ∑ t, exteriorWedge (k := G) (g t) (p t) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [← relativeLogCombination_exteriorWedge, hβ t]
    _ = 0 := hrelation

end ChenRanks
