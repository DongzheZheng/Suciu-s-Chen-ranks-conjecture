import ChenRanks.GroupAlgebraAugmentation
import ChenRanks.ChenObjects
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Native group lower-central elements in actual augmentation powers

Every construction uses the original group, its original group algebra,
and the powers of the actual augmentation kernel. The dimension subgroup
is an auxiliary genuine subgroup defined by this actual membership test.
The original noncommutative commutator identity proves its filtered bracket
property. Native lower-central recursion then proves the forward inclusion.
The actual quadratic multiplication error descends to the original
successive group quotients and their rational Chen spaces.

No dimension-subgroup equality, rational injection, formality, Malcev
equivalence, or Chen/Koszul comparison is a premise or conclusion here.
-/

noncomputable section

open TensorProduct
open scoped commutatorElement TensorProduct

namespace ChenRanks.GroupAlgebra

variable (k G : Type*) [Field k] [Group G]

/-- The exact original inverse identity, retaining the original ring action. -/
theorem augmentationDifference_inv (g : G) :
    augmentationDifference k G g⁻¹ =
      -(MonoidAlgebra.of k G g⁻¹ * augmentationDifference k G g) := by
  have hmul : MonoidAlgebra.of k G g⁻¹ * MonoidAlgebra.of k G g = 1 := by
    rw [← (MonoidAlgebra.of k G).map_mul, inv_mul_cancel, map_one]
  simp only [augmentationDifference, mul_sub, hmul, mul_one]
  abel

/-- Conjugation in the group is actual two-sided multiplication in its ring. -/
theorem augmentationDifference_conjugate (g h : G) :
    augmentationDifference k G (h * g * h⁻¹) =
      MonoidAlgebra.of k G h * augmentationDifference k G g * MonoidAlgebra.of k G h⁻¹ := by
  have hmul : MonoidAlgebra.of k G h * MonoidAlgebra.of k G h⁻¹ = 1 := by
    rw [← (MonoidAlgebra.of k G).map_mul, mul_inv_cancel, map_one]
  simp only [augmentationDifference, map_mul, mul_sub, sub_mul, mul_one, hmul]

/-- A genuine subgroup defined by actual augmentation-power membership. -/
def augmentationDimensionSubgroup (n : ℕ) : Subgroup G where
  carrier := {g | augmentationDifference k G g ∈ (augmentationIdeal k G) ^ n}
  one_mem' := by
    change augmentationDifference k G 1 ∈ (augmentationIdeal k G) ^ n
    simp only [augmentationDifference, map_one, sub_self]
    exact Ideal.zero_mem _
  mul_mem' {g h} hg hh := by
    change augmentationDifference k G (g * h) ∈ (augmentationIdeal k G) ^ n
    rw [augmentationDifference_mul]
    exact Ideal.add_mem _ (Ideal.add_mem _ hg hh)
      (Ideal.mul_mem_right (augmentationDifference k G h)
        ((augmentationIdeal k G) ^ n) hg)
  inv_mem' {g} hg := by
    change augmentationDifference k G g⁻¹ ∈ (augmentationIdeal k G) ^ n
    rw [augmentationDifference_inv]
    exact (((augmentationIdeal k G) ^ n)).neg_mem (Ideal.mul_mem_left _ _ hg)

@[simp]
theorem mem_augmentationDimensionSubgroup (n : ℕ) (g : G) :
    g ∈ augmentationDimensionSubgroup k G n ↔
      augmentationDifference k G g ∈ (augmentationIdeal k G) ^ n := Iff.rfl

instance augmentationDimensionSubgroup_normal (n : ℕ) :
    (augmentationDimensionSubgroup k G n).Normal where
  conj_mem g hg h := by
    change augmentationDifference k G (h * g * h⁻¹) ∈ (augmentationIdeal k G) ^ n
    rw [augmentationDifference_conjugate]
    exact Ideal.mul_mem_right (MonoidAlgebra.of k G h⁻¹)
      ((augmentationIdeal k G) ^ n)
      (Ideal.mul_mem_left _ _ hg)

theorem augmentationDimensionSubgroup_antitone :
    Antitone (augmentationDimensionSubgroup k G) := by
  intro m n hmn g hg
  exact Ideal.pow_le_pow_right hmn hg

@[simp]
theorem augmentationDimensionSubgroup_zero : augmentationDimensionSubgroup k G 0 = ⊤ := by
  ext g
  simp only [mem_augmentationDimensionSubgroup, Submodule.pow_zero, Ideal.one_eq_top,
    Submodule.mem_top, Subgroup.mem_top]

@[simp]
theorem augmentationDimensionSubgroup_one : augmentationDimensionSubgroup k G 1 = ⊤ := by
  apply top_unique
  intro g _hg
  change augmentationDifference k G g ∈ (augmentationIdeal k G) ^ 1
  rw [Submodule.pow_one]
  exact augmentationDifference_mem k G g

/-- This noncommutative identity has exactly the original group commutator
convention `g*h*g^-1*h^-1`. No commuting ring generators are assumed. -/
theorem augmentationDifference_commutator (g h : G) :
    augmentationDifference k G ⁅g, h⁆ =
      (augmentationDifference k G g * augmentationDifference k G h -
        augmentationDifference k G h * augmentationDifference k G g) *
          (MonoidAlgebra.of k G g⁻¹ * MonoidAlgebra.of k G h⁻¹) := by
  have hdiff : augmentationDifference k G g * augmentationDifference k G h -
      augmentationDifference k G h * augmentationDifference k G g =
        MonoidAlgebra.of k G g * MonoidAlgebra.of k G h -
          MonoidAlgebra.of k G h * MonoidAlgebra.of k G g := by
    simp only [augmentationDifference]
    noncomm_ring
  have hcancel : (MonoidAlgebra.of k G h * MonoidAlgebra.of k G g) *
      (MonoidAlgebra.of k G g⁻¹ * MonoidAlgebra.of k G h⁻¹) = 1 := by
    rw [← (MonoidAlgebra.of k G).map_mul, ← (MonoidAlgebra.of k G).map_mul,
      ← (MonoidAlgebra.of k G).map_mul]
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, map_one]
  rw [hdiff, sub_mul, hcancel]
  simp only [augmentationDifference, commutatorElement_def, map_mul, mul_assoc]

/-- The actual dimension subgroups satisfy their genuine commutator
filtration property in every degree, including degree zero. -/
theorem augmentationDimensionSubgroup_commutator_le (m n : ℕ) :
    ⁅augmentationDimensionSubgroup k G m, augmentationDimensionSubgroup k G n⁆ ≤
      augmentationDimensionSubgroup k G (m + n) := by
  apply Subgroup.commutator_le.mpr
  intro g hg h hh
  change augmentationDifference k G ⁅g, h⁆ ∈ (augmentationIdeal k G) ^ (m + n)
  rw [augmentationDifference_commutator]
  have hgh : augmentationDifference k G g * augmentationDifference k G h ∈
      (augmentationIdeal k G) ^ (m + n) := by
    rw [Ideal.IsTwoSided.pow_add]
    exact Ideal.mul_mem_mul hg hh
  have hhg : augmentationDifference k G h * augmentationDifference k G g ∈
      (augmentationIdeal k G) ^ (m + n) := by
    rw [Nat.add_comm m n, Ideal.IsTwoSided.pow_add]
    exact Ideal.mul_mem_mul hh hg
  exact Ideal.mul_mem_right
    (MonoidAlgebra.of k G g⁻¹ * MonoidAlgebra.of k G h⁻¹)
    ((augmentationIdeal k G) ^ (m + n)) (Ideal.sub_mem _ hgh hhg)

/-- Native group LCS starts at zero. Its `n` term is ordinary Gamma_(n+1),
and genuinely maps into the corresponding actual augmentation power. -/
theorem lowerCentralSeries_le_augmentationDimensionSubgroup (n : ℕ) :
    lowerCentralSeries G n ≤ augmentationDimensionSubgroup k G (n + 1) := by
  induction n with
  | zero =>
    rw [lowerCentralSeries_zero, augmentationDimensionSubgroup_one]
  | succ n ih =>
    change ⁅lowerCentralSeries G n, (⊤ : Subgroup G)⁆ ≤
      augmentationDimensionSubgroup k G ((n + 1) + 1)
    have htop : (⊤ : Subgroup G) ≤ augmentationDimensionSubgroup k G 1 := by
      rw [augmentationDimensionSubgroup_one]
    exact (Subgroup.commutator_mono ih htop).trans
      (augmentationDimensionSubgroup_commutator_le k G (n + 1) 1)

theorem augmentationDifference_mem_pow_of_lowerCentralSeries (n : ℕ) (g : G)
    (hg : g ∈ lowerCentralSeries G n) :
    augmentationDifference k G g ∈ (augmentationIdeal k G) ^ (n + 1) :=
  lowerCentralSeries_le_augmentationDimensionSubgroup k G n hg

/-- The actual quotient map in which products of two current LCS
differences have been proved to vanish. -/
def lowerCentralAugmentationProjection (n : ℕ) :
    MonoidAlgebra k G →+* augmentationTruncation k G (n + 2) :=
  Ideal.Quotient.mk ((augmentationIdeal k G) ^ (n + 2))

theorem lowerCentralAugmentationProjection_product_zero (n : ℕ)
    (g h : lowerCentralSeries G n) :
    lowerCentralAugmentationProjection k G n
      (augmentationDifference k G g * augmentationDifference k G h) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hmem : augmentationDifference k G g * augmentationDifference k G h ∈
      (augmentationIdeal k G) ^ ((n + 1) + (n + 1)) := by
    rw [Ideal.IsTwoSided.pow_add]
    exact Ideal.mul_mem_mul
      (augmentationDifference_mem_pow_of_lowerCentralSeries k G n g g.property)
      (augmentationDifference_mem_pow_of_lowerCentralSeries k G n h h.property)
  exact Ideal.pow_le_pow_right (show n + 2 ≤ (n + 1) + (n + 1) by omega) hmem

/-- An actual group homomorphism, with addition encoded by the native
multiplicative wrapper. Its additivity is the original multiplication
error killed in the genuine next augmentation quotient. -/
def lowerCentralAugmentationHom (n : ℕ) :
    lowerCentralSeries G n →* Multiplicative (augmentationTruncation k G (n + 2)) where
  toFun g := Multiplicative.ofAdd
    (lowerCentralAugmentationProjection k G n (augmentationDifference k G g))
  map_one' := by
    change lowerCentralAugmentationProjection k G n
      (augmentationDifference k G 1) = 0
    simp only [augmentationDifference, map_one, sub_self, map_zero]
  map_mul' g h := by
    change lowerCentralAugmentationProjection k G n
      (augmentationDifference k G ((g : G) * h)) =
      lowerCentralAugmentationProjection k G n (augmentationDifference k G g) +
        lowerCentralAugmentationProjection k G n (augmentationDifference k G h)
    rw [augmentationDifference_mul,
      (lowerCentralAugmentationProjection k G n).map_add,
      (lowerCentralAugmentationProjection k G n).map_add,
      lowerCentralAugmentationProjection_product_zero k G n g h, add_zero]

/-- The actual next group lower-central term lies in the actual kernel. -/
theorem nextLowerCentralIn_le_augmentationHom_ker (n : ℕ) :
    ChenRanks.nextLowerCentralIn G n ≤ (lowerCentralAugmentationHom k G n).ker := by
  intro g hg
  change lowerCentralAugmentationProjection k G n
    (augmentationDifference k G (g : G)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact augmentationDifference_mem_pow_of_lowerCentralSeries k G (n + 1) g hg

/-- True descent through the original native group lower-central quotient. -/
def lowerCentralPieceAugmentationHom (n : ℕ) :
    ChenRanks.lowerCentralPiece G n →*
      Multiplicative (augmentationTruncation k G (n + 2)) :=
  QuotientGroup.lift (ChenRanks.nextLowerCentralIn G n)
    (lowerCentralAugmentationHom k G n)
    (nextLowerCentralIn_le_augmentationHom_ker k G n)

/-- An actual additive character on the original successive group quotient. -/
def lowerCentralPieceAugmentationCharacter (n : ℕ) :
    Additive (ChenRanks.lowerCentralPiece G n) →+
      augmentationTruncation k G (n + 2) where
  toFun g := Multiplicative.toAdd
    (lowerCentralPieceAugmentationHom k G n (Additive.toMul g))
  map_zero' := (lowerCentralPieceAugmentationHom k G n).map_one
  map_add' g h := (lowerCentralPieceAugmentationHom k G n).map_mul
    (Additive.toMul g) (Additive.toMul h)

@[simp]
theorem lowerCentralPieceAugmentationCharacter_mk (n : ℕ) (g : lowerCentralSeries G n) :
    lowerCentralPieceAugmentationCharacter k G n
      (Additive.ofMul (QuotientGroup.mk' (ChenRanks.nextLowerCentralIn G n) g)) =
        lowerCentralAugmentationProjection k G n (augmentationDifference k G g) := rfl

/-- The map's image is in the actual degree-(n+1) augmentation layer:
its image vanishes in the genuine preceding truncation. -/
theorem lowerCentralPieceAugmentationCharacter_previous_zero (n : ℕ)
    (g : Additive (ChenRanks.lowerCentralPiece G n)) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (show n + 1 ≤ n + 2 by omega))
      (lowerCentralPieceAugmentationCharacter k G n g) =
        (0 : augmentationTruncation k G (n + 1)) := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    (ChenRanks.nextLowerCentralIn G n) (Additive.toMul g)
  have hg : g = Additive.ofMul
      (QuotientGroup.mk' (ChenRanks.nextLowerCentralIn G n) x) := by
    exact congrArg Additive.ofMul hx.symm
  rw [hg]
  have hmk : lowerCentralPieceAugmentationCharacter k G n
      (Additive.ofMul (QuotientGroup.mk' (ChenRanks.nextLowerCentralIn G n) x)) =
      lowerCentralAugmentationProjection k G n (augmentationDifference k G x) :=
    lowerCentralPieceAugmentationCharacter_mk k G n x
  have hmap := congrArg (fun y : augmentationTruncation k G (n + 2) =>
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (show n + 1 ≤ n + 2 by omega)) y) hmk
  apply hmap.trans
  change Ideal.Quotient.mk ((augmentationIdeal k G) ^ (n + 1))
      (augmentationDifference k G x) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (augmentationDifference_mem_pow_of_lowerCentralSeries k G n x x.property)

end ChenRanks.GroupAlgebra

namespace ChenRanks.GroupAlgebra

variable (G : Type*) [Group G]

/-- Scalar extension of the true additive map on the original metabelian
group quotient. This domain is the existing actual `rationalChenSpace`;
it is not a replacement definition for the Chen space. -/
def rationalChenAugmentationMap (n : ℕ) :
    ChenRanks.rationalChenSpace G n →ₗ[ℚ]
      augmentationTruncation ℚ (ChenRanks.metabelianQuotient G) (n + 2) :=
  AlgebraTensorModule.lift (R := ℤ) (A := ℚ) (M := ℚ)
    (N := Additive (ChenRanks.lowerCentralPiece (ChenRanks.metabelianQuotient G) n))
    (P := augmentationTruncation ℚ (ChenRanks.metabelianQuotient G) (n + 2))
    (LinearMap.toSpanSingleton ℚ
      (Additive (ChenRanks.lowerCentralPiece (ChenRanks.metabelianQuotient G) n) →ₗ[ℤ]
        augmentationTruncation ℚ (ChenRanks.metabelianQuotient G) (n + 2))
      (lowerCentralPieceAugmentationCharacter ℚ (ChenRanks.metabelianQuotient G) n).toIntLinearMap)

@[simp]
theorem rationalChenAugmentationMap_tmul (n : ℕ) (c : ℚ)
    (g : Additive (ChenRanks.lowerCentralPiece (ChenRanks.metabelianQuotient G) n)) :
    rationalChenAugmentationMap G n (c ⊗ₜ[ℤ] g) =
      c • lowerCentralPieceAugmentationCharacter ℚ (ChenRanks.metabelianQuotient G) n g := by
  simp only [rationalChenAugmentationMap, AlgebraTensorModule.lift_tmul,
    LinearMap.toSpanSingleton_apply, LinearMap.smul_apply,
    AddMonoidHom.coe_toIntLinearMap]

end ChenRanks.GroupAlgebra
