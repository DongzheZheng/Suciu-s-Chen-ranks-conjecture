import Mathlib

/-! Genuine augmentation data for the original group algebra.

The filtration is given by powers of the actual augmentation kernel in
the native group algebra, including its noncommutative multiplication.
The first-order character is constructed in the actual quotient by the
square of that kernel. No completion, Malcev comparison, formality, or
Chen comparison is assumed or asserted here. These are foundations for
the group-theoretic comparison used in the manuscript.
-/

noncomputable section

namespace ChenRanks.GroupAlgebra

variable (k G : Type*) [Field k] [Group G]

/-- The actual augmentation sends each original group element to one. -/
def augmentation : MonoidAlgebra k G →ₐ[k] k :=
  MonoidAlgebra.lift k k G (1 : G →* k)

@[simp] theorem augmentation_of (g : G) :
    augmentation k G (MonoidAlgebra.of k G g) = 1 := by
  simp [augmentation]

/-- The actual two-sided augmentation ideal of the original group algebra. -/
def augmentationIdeal : Ideal (MonoidAlgebra k G) :=
  RingHom.ker (augmentation k G).toRingHom

instance augmentationIdeal_isTwoSided : (augmentationIdeal k G).IsTwoSided := by
  unfold augmentationIdeal
  infer_instance

/-- The native quotient by the actual power, not an assigned graded model. -/
abbrev augmentationTruncation (n : ℕ) :=
  MonoidAlgebra k G ⧸ (augmentationIdeal k G) ^ n

def augmentationDifference (g : G) : MonoidAlgebra k G :=
  MonoidAlgebra.of k G g - 1

theorem augmentationDifference_mem (g : G) :
    augmentationDifference k G g ∈ augmentationIdeal k G := by
  change augmentation k G (augmentationDifference k G g) = 0
  change augmentation k G (MonoidAlgebra.of k G g - 1) = 0
  simpa only [augmentation_of, map_one, sub_self] using
    (map_sub (augmentation k G) (MonoidAlgebra.of k G g) 1)

/-- The quadratic error is retained in the original noncommutative ring. -/
theorem augmentationDifference_mul (g h : G) :
    augmentationDifference k G (g * h) =
      augmentationDifference k G g + augmentationDifference k G h +
        augmentationDifference k G g * augmentationDifference k G h := by
  simp only [augmentationDifference, map_mul]
  noncomm_ring

def firstOrderProjection : MonoidAlgebra k G →+* augmentationTruncation k G 2 :=
  Ideal.Quotient.mk ((augmentationIdeal k G) ^ 2)

theorem firstOrderProjection_quadratic_error (g h : G) :
    firstOrderProjection k G
      (augmentationDifference k G g * augmentationDifference k G h) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [Submodule.pow_succ, Submodule.pow_one]
  exact Ideal.mul_mem_mul (augmentationDifference_mem k G g)
    (augmentationDifference_mem k G h)

/-- The genuine first-order additive character of the original group. -/
def augmentationFirstOrderCharacter : Additive G →+ augmentationTruncation k G 2 where
  toFun g := firstOrderProjection k G (augmentationDifference k G g.toMul)
  map_zero' := by
    change firstOrderProjection k G (MonoidAlgebra.of k G 1 - 1) = 0
    rw [(MonoidAlgebra.of k G).map_one, sub_self, (firstOrderProjection k G).map_zero]
  map_add' g h := by
    change firstOrderProjection k G (augmentationDifference k G (g.toMul * h.toMul)) =
      firstOrderProjection k G (augmentationDifference k G g.toMul) +
        firstOrderProjection k G (augmentationDifference k G h.toMul)
    rw [augmentationDifference_mul, (firstOrderProjection k G).map_add,
      (firstOrderProjection k G).map_add,
      firstOrderProjection_quadratic_error, add_zero]

@[simp] theorem augmentationFirstOrderCharacter_ofMul (g : G) :
    augmentationFirstOrderCharacter k G (Additive.ofMul g) =
      firstOrderProjection k G (augmentationDifference k G g) := rfl

end ChenRanks.GroupAlgebra
