import ChenRanks.GroupAlgebraAugmentation

/-! Actual additive characters extend to augmentation derivations on the
native group algebra. Both the group law and the algebra multiplication
are the original operations. The twisted Leibniz rule is proved from
finite-support linearity; it is not a supplied comparison hypothesis.
-/

noncomputable section

namespace ChenRanks.GroupAlgebra

variable (k G : Type*) [Field k] [Group G]
variable (M : Type*) [AddCommGroup M] [Module k M]

def characterLinear (χ : Additive G →+ M) : MonoidAlgebra k G →ₗ[k] M :=
  Finsupp.linearCombination k (fun g => χ (Additive.ofMul g))

@[simp] theorem characterLinear_single (χ : Additive G →+ M) (g : G) (c : k) :
    characterLinear k G M χ (MonoidAlgebra.single g c) = c • χ (Additive.ofMul g) :=
  Finsupp.linearCombination_single k c g

private theorem augmentation_zero_value :
    augmentation k G 0 = 0 := map_zero (augmentation k G)

private theorem augmentation_add_value (a b : MonoidAlgebra k G) :
    augmentation k G (a + b) = augmentation k G a + augmentation k G b :=
  map_add (augmentation k G) a b

@[simp] theorem characterLinear_of (χ : Additive G →+ M) (g : G) :
    characterLinear k G M χ (MonoidAlgebra.of k G g) = χ (Additive.ofMul g) := by
  change characterLinear k G M χ (MonoidAlgebra.single g 1) = _
  rw [characterLinear_single, one_smul]

@[simp] theorem characterLinear_one (χ : Additive G →+ M) :
    characterLinear k G M χ 1 = 0 := by
  change characterLinear k G M χ (MonoidAlgebra.of k G 1) = 0
  rw [characterLinear_of]
  exact χ.map_zero

@[simp] theorem characterLinear_difference (χ : Additive G →+ M) (g : G) :
    characterLinear k G M χ (augmentationDifference k G g) = χ (Additive.ofMul g) := by
  rw [augmentationDifference, (characterLinear k G M χ).map_sub,
    characterLinear_of, characterLinear_one, sub_zero]

/-- The original characters give true augmentation derivations. -/
theorem characterLinear_mul (χ : Additive G →+ M) (a b : MonoidAlgebra k G) :
    characterLinear k G M χ (a * b) =
      augmentation k G a • characterLinear k G M χ b +
        augmentation k G b • characterLinear k G M χ a := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero =>
    simp only [zero_mul, (characterLinear k G M χ).map_zero,
      augmentation_zero_value, zero_smul, smul_zero, zero_add]
  | add a a' ha ha' =>
    rw [add_mul, (characterLinear k G M χ).map_add, ha, ha',
      augmentation_add_value, (characterLinear k G M χ).map_add,
      add_smul, smul_add]
    abel
  | single g c =>
    induction b using MonoidAlgebra.induction_linear with
    | zero =>
      simp only [mul_zero, (characterLinear k G M χ).map_zero,
        augmentation_zero_value, zero_smul, smul_zero, zero_add]
    | add b b' hb hb' =>
      rw [mul_add, (characterLinear k G M χ).map_add, hb, hb',
        augmentation_add_value, (characterLinear k G M χ).map_add,
        add_smul, smul_add]
      abel
    | single h e =>
      have hχ : χ (Additive.ofMul (g * h)) =
          χ (Additive.ofMul g) + χ (Additive.ofMul h) := χ.map_add _ _
      simp only [MonoidAlgebra.single_mul_single, characterLinear_single,
        augmentation, MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul,
        mul_one, hχ, smul_add, smul_smul]
      rw [mul_comm c e]
      abel

theorem characterLinear_augmentation_product_zero (χ : Additive G →+ M)
    (a b : MonoidAlgebra k G) (ha : a ∈ augmentationIdeal k G)
    (hb : b ∈ augmentationIdeal k G) :
    characterLinear k G M χ (a * b) = 0 := by
  have hεa : augmentation k G a = 0 := ha
  have hεb : augmentation k G b = 0 := hb
  simp only [characterLinear_mul, hεa, hεb, zero_smul, zero_add]

end ChenRanks.GroupAlgebra
