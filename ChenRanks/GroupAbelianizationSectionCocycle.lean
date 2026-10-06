import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Tactic.Group

/-! The actual normalized section of original group abelianization and
its actual commutator-valued multiplication error. Both identities are
proved in the original group. No group presentation, cocycle primitive,
formality, or higher Chen comparison is assumed.
-/

noncomputable section

open scoped commutatorElement

namespace ChenRanks.GroupComparison

variable (G : Type*) [Group G]

/-- An actual normalized section chosen from the actual quotient map. -/
def normalizedAbelianizationSection (a : Abelianization G) : G := by
  classical
  exact if a = 1 then 1 else
    Classical.choose (QuotientGroup.mk_surjective a)

@[simp] theorem normalizedAbelianizationSection_one :
    normalizedAbelianizationSection G 1 = 1 := by
  classical
  simp [normalizedAbelianizationSection]

@[simp] theorem normalizedAbelianizationSection_projection (a : Abelianization G) :
    Abelianization.of (normalizedAbelianizationSection G a) = a := by
  classical
  unfold normalizedAbelianizationSection
  split_ifs with h
  · simpa only [map_one] using h.symm
  · exact Classical.choose_spec (QuotientGroup.mk_surjective a)

/-- The actual multiplication error takes values in the original
commutator subgroup, by the actual quotient-kernel identity. -/
def abelianizationSectionError (a b : Additive (Abelianization G)) : commutator G :=
  ⟨normalizedAbelianizationSection G a.toMul *
      normalizedAbelianizationSection G b.toMul *
        (normalizedAbelianizationSection G (a + b).toMul)⁻¹, by
    rw [← Abelianization.ker_of]
    change Abelianization.of
      (normalizedAbelianizationSection G a.toMul *
        normalizedAbelianizationSection G b.toMul *
          (normalizedAbelianizationSection G (a + b).toMul)⁻¹) = 1
    rw [map_mul, map_mul, map_inv,
      normalizedAbelianizationSection_projection,
      normalizedAbelianizationSection_projection,
      normalizedAbelianizationSection_projection]
    change a.toMul * b.toMul * (a.toMul * b.toMul)⁻¹ = 1
    exact mul_inv_cancel _⟩

@[simp] theorem abelianizationSectionError_zero_right
    (a : Additive (Abelianization G)) : abelianizationSectionError G a 0 = 1 := by
  apply Subtype.ext
  change normalizedAbelianizationSection G a.toMul *
    normalizedAbelianizationSection G (0 : Additive (Abelianization G)).toMul *
      (normalizedAbelianizationSection G (a + 0).toMul)⁻¹ = 1
  rw [add_zero]
  change normalizedAbelianizationSection G a.toMul *
    normalizedAbelianizationSection G 1 *
      (normalizedAbelianizationSection G a.toMul)⁻¹ = 1
  rw [normalizedAbelianizationSection_one, mul_one, mul_inv_cancel]

@[simp] theorem abelianizationSectionError_zero_left
    (a : Additive (Abelianization G)) : abelianizationSectionError G 0 a = 1 := by
  apply Subtype.ext
  change normalizedAbelianizationSection G (0 : Additive (Abelianization G)).toMul *
    normalizedAbelianizationSection G a.toMul *
      (normalizedAbelianizationSection G (0 + a).toMul)⁻¹ = 1
  rw [zero_add]
  change normalizedAbelianizationSection G 1 *
    normalizedAbelianizationSection G a.toMul *
      (normalizedAbelianizationSection G a.toMul)⁻¹ = 1
  rw [normalizedAbelianizationSection_one, one_mul, mul_inv_cancel]

/-- The genuine section error satisfies the genuine conjugated cocycle
identity in the original group, before any character is applied. -/
theorem abelianizationSectionError_cocycle (a b d : Additive (Abelianization G)) :
    (abelianizationSectionError G a b : G) * abelianizationSectionError G (a + b) d =
      normalizedAbelianizationSection G a.toMul * abelianizationSectionError G b d *
        (normalizedAbelianizationSection G a.toMul)⁻¹ *
          abelianizationSectionError G a (b + d) := by
  change (normalizedAbelianizationSection G a.toMul *
      normalizedAbelianizationSection G b.toMul *
      (normalizedAbelianizationSection G (a + b).toMul)⁻¹) *
    (normalizedAbelianizationSection G (a + b).toMul *
      normalizedAbelianizationSection G d.toMul *
      (normalizedAbelianizationSection G ((a + b) + d).toMul)⁻¹) =
    normalizedAbelianizationSection G a.toMul *
    (normalizedAbelianizationSection G b.toMul *
      normalizedAbelianizationSection G d.toMul *
      (normalizedAbelianizationSection G (b + d).toMul)⁻¹) *
    (normalizedAbelianizationSection G a.toMul)⁻¹ *
    (normalizedAbelianizationSection G a.toMul *
      normalizedAbelianizationSection G (b + d).toMul *
      (normalizedAbelianizationSection G (a + (b + d)).toMul)⁻¹)
  rw [add_assoc]
  group

/-- The true antisymmetric part of the actual section error is exactly
the original group commutator, with its actual sign convention. -/
theorem abelianizationSectionError_skew (a b : Additive (Abelianization G)) :
    (abelianizationSectionError G a b : G) * (abelianizationSectionError G b a : G)⁻¹ =
      ⁅normalizedAbelianizationSection G a.toMul,
        normalizedAbelianizationSection G b.toMul⁆ := by
  change (normalizedAbelianizationSection G a.toMul *
    normalizedAbelianizationSection G b.toMul *
    (normalizedAbelianizationSection G (a + b).toMul)⁻¹) *
    (normalizedAbelianizationSection G b.toMul *
    normalizedAbelianizationSection G a.toMul *
    (normalizedAbelianizationSection G (b + a).toMul)⁻¹)⁻¹ = _
  rw [add_comm b a, commutatorElement_def]
  group

end ChenRanks.GroupComparison
