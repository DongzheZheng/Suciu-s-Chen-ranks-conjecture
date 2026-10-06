import ChenRanks.KoszulPolynomialHomotopy
import ChenRanks.KoszulFree
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Genuine full-relation and small-dimension Koszul pieces

Full quadratic relations kill every actual homogeneous cycle, by the
proved polynomial homotopy and the genuine homogeneous tensor image.
In dimension at most one, every actual cycle is already zero by its
proved dimension formula. These are unconditional boundary calculations
on the original homogeneous quotient; no eventual or effective bound
is a premise.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} [Fintype ι] (b : _root_.Module.Basis ι k V)

section FullRelations

variable [CharZero k]

/-- The actual full-relation homogeneous map surjects onto all actual
cycles. Its preimage is constructed from the genuine polynomial
homotopy and homogeneous tensor inclusion. -/
theorem relationDegree_top_surjective (r : ℕ) :
    Function.Surjective
      (relationDegree k V b (⊤ : Submodule k (⋀[k]^2 V)) r) := by
  classical
  intro z
  obtain ⟨y, hy, he⟩ := cycleDegree_preimage k V b r z
  have hyrange : y ∈ LinearMap.range
      (homogeneousTensorInclusion k V b (⋀[k]^2 V) r) := by
    rw [← tensorHomogeneous_eq_range]
    exact hy
  obtain ⟨t, ht⟩ := hyrange
  let f : (⋀[k]^2 V) →ₗ[k] (⊤ : Submodule k (⋀[k]^2 V)) :=
    (Submodule.topEquiv : (⊤ : Submodule k (⋀[k]^2 V)) ≃ₗ[k] (⋀[k]^2 V)).symm.toLinearMap
  have hmap :
      (TensorProduct.map (homogeneousS k V b r).subtype
          (⊤ : Submodule k (⋀[k]^2 V)).subtype).comp
        (TensorProduct.map (LinearMap.id : homogeneousS k V b r →ₗ[k]
          homogeneousS k V b r) f) =
      homogeneousTensorInclusion k V b (⋀[k]^2 V) r := by
    apply TensorProduct.ext'
    intro s w
    rfl
  refine ⟨TensorProduct.map (LinearMap.id : homogeneousS k V b r →ₗ[k]
    homogeneousS k V b r) f t, ?_⟩
  apply Subtype.ext
  change delta2 k V
    (TensorProduct.map (homogeneousS k V b r).subtype
      (⊤ : Submodule k (⋀[k]^2 V)).subtype
      (TensorProduct.map (LinearMap.id : homogeneousS k V b r →ₗ[k]
        homogeneousS k V b r) f t)) = (z : C1 k V)
  have hx : TensorProduct.map (homogeneousS k V b r).subtype
      (⊤ : Submodule k (⋀[k]^2 V)).subtype
      (TensorProduct.map (LinearMap.id : homogeneousS k V b r →ₗ[k]
        homogeneousS k V b r) f t) = y := by
    change ((TensorProduct.map (homogeneousS k V b r).subtype
        (⊤ : Submodule k (⋀[k]^2 V)).subtype).comp
      (TensorProduct.map (LinearMap.id : homogeneousS k V b r →ₗ[k]
        homogeneousS k V b r) f)) t = y
    rw [hmap]
    exact ht
  rw [hx]
  exact he

/-- Every genuine full-relation degree quotient is a zero module. -/
theorem homogeneousModule_top_subsingleton (r : ℕ) :
    Subsingleton (homogeneousModule k V b (⊤ : Submodule k (⋀[k]^2 V)) r) :=
  Submodule.Quotient.subsingleton_iff.mpr
    (LinearMap.range_eq_top.mpr (relationDegree_top_surjective k V b r))

/-- Full quadratic relations give zero dimension in every actual degree. -/
theorem homogeneousModule_top_finrank (r : ℕ) :
    _root_.Module.finrank k
      (homogeneousModule k V b (⊤ : Submodule k (⋀[k]^2 V)) r) = 0 := by
  letI := homogeneousModule_top_subsingleton k V b r
  exact _root_.Module.finrank_zero_of_subsingleton

end FullRelations

/-- In dimension at most one every genuine homogeneous cycle vanishes,
as a consequence of its actual finite-dimensional calculation. -/
theorem cycleDegree_subsingleton_of_finrank_le_one
    (hV : _root_.Module.finrank k V ≤ 1) (r : ℕ) :
    Subsingleton (cycleDegree k V b r) := by
  have hcard : Fintype.card ι ≤ 1 := by
    simpa only [_root_.Module.finrank_eq_card_basis b] using hV
  have hchoose : (Fintype.card ι + r).choose (r + 2) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  have hzero : _root_.Module.finrank k (cycleDegree k V b r) = 0 := by
    rw [cycleDegree_finrank, hchoose, mul_zero]
  exact (_root_.Module.finrank_eq_zero_iff_of_free k (cycleDegree k V b r)).mp hzero

/-- Any genuine quadratic-relation quotient is zero in dimensions zero
and one, without a separability or characteristic-zero assumption. -/
theorem homogeneousModule_subsingleton_of_finrank_le_one
    (K : Submodule k (⋀[k]^2 V))
    (hV : _root_.Module.finrank k V ≤ 1) (r : ℕ) :
    Subsingleton (homogeneousModule k V b K r) := by
  letI := cycleDegree_subsingleton_of_finrank_le_one k V b hV r
  infer_instance

theorem homogeneousModule_finrank_of_finrank_le_one
    (K : Submodule k (⋀[k]^2 V))
    (hV : _root_.Module.finrank k V ≤ 1) (r : ℕ) :
    _root_.Module.finrank k (homogeneousModule k V b K r) = 0 := by
  letI := homogeneousModule_subsingleton_of_finrank_le_one k V b K hV r
  exact _root_.Module.finrank_zero_of_subsingleton

end ChenRanks.Koszul
