import ChenRanks.GroupAlgebraAugmentationCharacters

/-! The actual augmentation kernel is spanned by the actual differences
of original group elements. This follows from finite-support linearity
in the native group algebra. Additive characters kill its actual square,
not an assigned quadratic relation space. No injection of higher group
lower-central quotients or formality assertion is made here.
-/

noncomputable section

namespace ChenRanks.GroupAlgebra

variable (k G : Type*) [Field k] [Group G]

def augmentationLinearIdeal : Submodule k (MonoidAlgebra k G) :=
  (augmentationIdeal k G).restrictScalars k

private def augmentationDifferenceCombination :
    MonoidAlgebra k G →ₗ[k] MonoidAlgebra k G :=
  Finsupp.linearCombination k (augmentationDifference k G)

private theorem augmentationDifferenceCombination_zero :
    Finsupp.linearCombination k (augmentationDifference k G)
      (0 : MonoidAlgebra k G) = 0 :=
  (augmentationDifferenceCombination k G).map_zero

private theorem augmentationDifferenceCombination_add (a b : MonoidAlgebra k G) :
    Finsupp.linearCombination k (augmentationDifference k G) (a + b) =
      Finsupp.linearCombination k (augmentationDifference k G) a +
        Finsupp.linearCombination k (augmentationDifference k G) b :=
  (augmentationDifferenceCombination k G).map_add a b

private theorem augmentation_zero_value :
    augmentation k G (0 : MonoidAlgebra k G) = 0 := map_zero (augmentation k G)

private theorem augmentation_add_value (a b : MonoidAlgebra k G) :
    augmentation k G (a + b) = augmentation k G a + augmentation k G b :=
  map_add (augmentation k G) a b

/-- Original finite-support reconstruction, with the actual scalar
augmentation error retained. -/
theorem augmentationDifference_linearCombination (a : MonoidAlgebra k G) :
    Finsupp.linearCombination k (augmentationDifference k G) a =
      a - augmentation k G a • (1 : MonoidAlgebra k G) := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero =>
    rw [augmentationDifferenceCombination_zero,
      augmentation_zero_value, zero_smul, sub_zero]
  | add a b ha hb =>
    rw [augmentationDifferenceCombination_add,
      ha, hb, augmentation_add_value, add_smul]
    abel
  | single g c =>
    rw [Finsupp.linearCombination_single]
    change c • (MonoidAlgebra.of k G g - 1) =
      MonoidAlgebra.single g c - augmentation k G (MonoidAlgebra.single g c) • 1
    simp only [augmentation, MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul, mul_one,
      smul_sub]
    congr 1
    change c • MonoidAlgebra.single g (1 : k) = MonoidAlgebra.single g c
    simp only [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]

/-- An equality for the original kernel, with its genuine base-field action. -/
theorem augmentationLinearIdeal_eq_span :
    augmentationLinearIdeal k G =
      Submodule.span k (Set.range (augmentationDifference k G)) := by
  apply le_antisymm
  · intro a ha
    have hε : augmentation k G a = 0 := ha
    have hrep := augmentationDifference_linearCombination k G a
    rw [hε, zero_smul, sub_zero] at hrep
    rw [← hrep, ← Finsupp.range_linearCombination]
    exact LinearMap.mem_range.mpr ⟨a, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact augmentationDifference_mem k G g

variable (M : Type*) [AddCommGroup M] [Module k M]

/-- The genuine square of the original augmentation ideal is killed by
the actual character extension, including all its finite sums. -/
theorem characterLinear_augmentation_square_zero (χ : Additive G →+ M)
    (a : MonoidAlgebra k G) (ha : a ∈ (augmentationIdeal k G) ^ 2) :
    characterLinear k G M χ a = 0 := by
  rw [Submodule.pow_succ, Submodule.pow_one] at ha
  refine Submodule.mul_induction_on ha ?_ ?_
  · intro x hx y hy
    exact characterLinear_augmentation_product_zero k G M χ x y hx hy
  · intro x y hx hy
    rw [(characterLinear k G M χ).map_add, hx, hy, zero_add]

end ChenRanks.GroupAlgebra
