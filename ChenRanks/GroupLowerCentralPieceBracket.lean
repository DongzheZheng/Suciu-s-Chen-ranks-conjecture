import ChenRanks.ChenObjects
import ChenRanks.GroupJointLowerCentralCommutator
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Tactic

/-!
# The actual bracket on original lower-central successive quotients

The original commutator is first placed in its actual native LCS term.
Its class is proved additive in each representative variable, then descends
through both actual next-LCS subgroups. Rationalization uses the actual
tensor-product scalar-extension functor. No bracket, additivity, Jacobi,
augmentation injection, or group/Lie comparison is supplied as a premise.

This file does not yet assert Jacobi or build a direct-sum Lie algebra.
-/

noncomputable section

open TensorProduct
open scoped commutatorElement TensorProduct

namespace ChenRanks

variable (G : Type*) [Group G]

/-- The original successive group quotient maps to the original ambient
quotient by the same next term. -/
def lowerCentralPieceAmbientHom (r : ℕ) :
    lowerCentralPiece G r →* G ⧸ lowerCentralSeries G (r + 1) :=
  QuotientGroup.lift (nextLowerCentralIn G r)
    ((QuotientGroup.mk' (lowerCentralSeries G (r + 1))).comp
      (lowerCentralSeries G r).subtype) (by
    intro g hg
    change QuotientGroup.mk' (lowerCentralSeries G (r + 1)) (g : G) = 1
    exact (QuotientGroup.eq_one_iff (g : G)).mpr hg)

@[simp]
theorem lowerCentralPieceAmbientHom_mk (r : ℕ) (g : lowerCentralSeries G r) :
    lowerCentralPieceAmbientHom G r
      (QuotientGroup.mk' (nextLowerCentralIn G r) g) =
      QuotientGroup.mk' (lowerCentralSeries G (r + 1)) (g : G) := rfl

/-- This ambient map is injective because its representative kernel is
exactly the original next-LCS subgroup. -/
theorem lowerCentralPieceAmbientHom_injective (r : ℕ) :
    Function.Injective (lowerCentralPieceAmbientHom G r) := by
  have hker :
      ((QuotientGroup.mk' (lowerCentralSeries G (r + 1))).comp
        (lowerCentralSeries G r).subtype).ker = nextLowerCentralIn G r := by
    ext g
    change (QuotientGroup.mk' (lowerCentralSeries G (r + 1)) (g : G) = 1) ↔
      (g : G) ∈ lowerCentralSeries G (r + 1)
    exact QuotientGroup.eq_one_iff (g : G)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  change (QuotientGroup.lift _ _ _).ker = ⊥
  rw [QuotientGroup.ker_lift, hker, QuotientGroup.map_mk'_self]

/-- The actual image of a current lower-central element centralizes every
original element modulo the actual next term. -/
theorem lowerCentral_ambient_image_commute (r : ℕ) (g : G)
    (hg : g ∈ lowerCentralSeries G r) (x : G) :
    Commute (QuotientGroup.mk' (lowerCentralSeries G (r + 1)) g)
      (QuotientGroup.mk' (lowerCentralSeries G (r + 1)) x) := by
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← map_commutatorElement]
  change QuotientGroup.mk' (lowerCentralSeries G (r + 1)) ⁅g, x⁆ = 1
  apply (QuotientGroup.eq_one_iff ⁅g, x⁆).mpr
  exact Subgroup.commutator_mem_commutator hg (Subgroup.mem_top x)

private theorem commutator_mul_left_of_commute {Q : Type*} [Group Q]
    (x y z : Q) (hc : Commute x ⁅y, z⁆) :
    ⁅x * y, z⁆ = ⁅y, z⁆ * ⁅x, z⁆ := by
  have hconj : x * ⁅y, z⁆ * x⁻¹ = ⁅y, z⁆ := by
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  calc
    ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
      simp only [commutatorElement_def]
      group
    _ = ⁅y, z⁆ * ⁅x, z⁆ := by rw [hconj]

private theorem commutator_mul_right_of_commute {Q : Type*} [Group Q]
    (x y z : Q) (hc : Commute y ⁅x, z⁆) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have hconj : y * ⁅x, z⁆ * y⁻¹ = ⁅x, z⁆ := by
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  calc
    ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    _ = ⁅x, y⁆ * ⁅x, z⁆ := by rw [hconj]

/-- The actual class of the original representative commutator. -/
def lowerCentralRepresentativeBracket (m n : ℕ)
    (g : lowerCentralSeries G m) (h : lowerCentralSeries G n) :
    lowerCentralPiece G (m + n + 1) :=
  QuotientGroup.mk' (nextLowerCentralIn G (m + n + 1))
    ⟨⁅(g : G), (h : G)⁆,
      group_commutator_mem_lowerCentralSeries (G := G) m n (g : G) (h : G)
        g.property h.property⟩

@[simp]
theorem lowerCentralRepresentativeBracket_ambient (m n : ℕ)
    (g : lowerCentralSeries G m) (h : lowerCentralSeries G n) :
    lowerCentralPieceAmbientHom G (m + n + 1)
      (lowerCentralRepresentativeBracket G m n g h) =
      ⁅QuotientGroup.mk' (lowerCentralSeries G ((m + n + 1) + 1)) (g : G),
        QuotientGroup.mk' (lowerCentralSeries G ((m + n + 1) + 1)) (h : G)⁆ := by
  change QuotientGroup.mk' (lowerCentralSeries G ((m + n + 1) + 1))
    ⁅(g : G), (h : G)⁆ = _
  exact map_commutatorElement _ _ _

/-- Actual additivity in the first variable, retaining multiplication in
the native abelian quotient. -/
def lowerCentralRepresentativeLeftHom (m n : ℕ) (h : lowerCentralSeries G n) :
    lowerCentralSeries G m →* lowerCentralPiece G (m + n + 1) where
  toFun g := lowerCentralRepresentativeBracket G m n g h
  map_one' := by
    apply lowerCentralPieceAmbientHom_injective G (m + n + 1)
    rw [lowerCentralRepresentativeBracket_ambient, map_one]
    change ⁅QuotientGroup.mk' _ (1 : G), _⁆ = 1
    rw [map_one, commutatorElement_one_left]
  map_mul' g₁ g₂ := by
    apply lowerCentralPieceAmbientHom_injective G (m + n + 1)
    rw [map_mul, lowerCentralRepresentativeBracket_ambient,
      lowerCentralRepresentativeBracket_ambient,
      lowerCentralRepresentativeBracket_ambient]
    let q : G →* G ⧸ lowerCentralSeries G ((m + n + 1) + 1) :=
      QuotientGroup.mk' _
    change ⁅q ((g₁ : G) * g₂), q (h : G)⁆ =
      ⁅q (g₁ : G), q (h : G)⁆ * ⁅q (g₂ : G), q (h : G)⁆
    rw [q.map_mul]
    have hc : Commute (q (g₁ : G)) ⁅q (g₂ : G), q (h : G)⁆ := by
      rw [← map_commutatorElement]
      exact (lowerCentral_ambient_image_commute G (m + n + 1)
        ⁅(g₂ : G), (h : G)⁆
        (group_commutator_mem_lowerCentralSeries (G := G) m n (g₂ : G) (h : G)
          g₂.property h.property)
        g₁).symm
    rw [commutator_mul_left_of_commute _ _ _ hc]
    simpa only [map_commutatorElement] using (lowerCentral_ambient_image_commute G (m + n + 1)
      ⁅(g₂ : G), (h : G)⁆
      (group_commutator_mem_lowerCentralSeries (G := G) m n (g₂ : G) (h : G)
        g₂.property h.property)
      ⁅(g₁ : G), (h : G)⁆).eq

theorem nextLowerCentralIn_le_representativeLeftHom_ker (m n : ℕ)
    (h : lowerCentralSeries G n) :
    nextLowerCentralIn G m ≤ (lowerCentralRepresentativeLeftHom G m n h).ker := by
  intro g hg
  change lowerCentralRepresentativeBracket G m n g h = 1
  apply lowerCentralPieceAmbientHom_injective G (m + n + 1)
  rw [lowerCentralRepresentativeBracket_ambient, map_one,
    ← map_commutatorElement]
  apply (QuotientGroup.eq_one_iff ⁅(g : G), (h : G)⁆).mpr
  have hmem := group_commutator_mem_lowerCentralSeries (G := G) (m + 1) n
    (g : G) (h : G) hg h.property
  simpa only [show (m + 1) + n + 1 = (m + n + 1) + 1 by omega] using hmem

/-- First genuine quotient descent. -/
def lowerCentralFirstVariableBracket (m n : ℕ) (h : lowerCentralSeries G n) :
    lowerCentralPiece G m →* lowerCentralPiece G (m + n + 1) :=
  QuotientGroup.lift (nextLowerCentralIn G m)
    (lowerCentralRepresentativeLeftHom G m n h)
    (nextLowerCentralIn_le_representativeLeftHom_ker G m n h)

@[simp]
theorem lowerCentralFirstVariableBracket_mk (m n : ℕ)
    (g : lowerCentralSeries G m) (h : lowerCentralSeries G n) :
    lowerCentralFirstVariableBracket G m n h
      (QuotientGroup.mk' (nextLowerCentralIn G m) g) =
      lowerCentralRepresentativeBracket G m n g h := rfl

/-- Actual additivity in the second variable after the first descent. -/
def lowerCentralRepresentativeRightHom (m n : ℕ) (g : lowerCentralPiece G m) :
    lowerCentralSeries G n →* lowerCentralPiece G (m + n + 1) where
  toFun h := lowerCentralFirstVariableBracket G m n h g
  map_one' := by
    refine QuotientGroup.induction_on g fun g => ?_
    change lowerCentralFirstVariableBracket G m n 1
      (QuotientGroup.mk' (nextLowerCentralIn G m) g) = 1
    rw [lowerCentralFirstVariableBracket_mk]
    apply lowerCentralPieceAmbientHom_injective G (m + n + 1)
    rw [lowerCentralRepresentativeBracket_ambient, map_one]
    change ⁅_, QuotientGroup.mk' _ (1 : G)⁆ = 1
    rw [map_one, commutatorElement_one_right]
  map_mul' h₁ h₂ := by
    refine QuotientGroup.induction_on g fun g => ?_
    change lowerCentralFirstVariableBracket G m n (h₁ * h₂)
        (QuotientGroup.mk' (nextLowerCentralIn G m) g) =
      lowerCentralFirstVariableBracket G m n h₁
        (QuotientGroup.mk' (nextLowerCentralIn G m) g) *
      lowerCentralFirstVariableBracket G m n h₂
        (QuotientGroup.mk' (nextLowerCentralIn G m) g)
    rw [lowerCentralFirstVariableBracket_mk,
      lowerCentralFirstVariableBracket_mk, lowerCentralFirstVariableBracket_mk]
    apply lowerCentralPieceAmbientHom_injective G (m + n + 1)
    rw [map_mul, lowerCentralRepresentativeBracket_ambient,
      lowerCentralRepresentativeBracket_ambient,
      lowerCentralRepresentativeBracket_ambient]
    let q : G →* G ⧸ lowerCentralSeries G ((m + n + 1) + 1) :=
      QuotientGroup.mk' _
    change ⁅q (g : G), q ((h₁ : G) * h₂)⁆ =
      ⁅q (g : G), q (h₁ : G)⁆ * ⁅q (g : G), q (h₂ : G)⁆
    rw [q.map_mul]
    have hc : Commute (q (h₁ : G)) ⁅q (g : G), q (h₂ : G)⁆ := by
      rw [← map_commutatorElement]
      exact (lowerCentral_ambient_image_commute G (m + n + 1)
        ⁅(g : G), (h₂ : G)⁆
        (group_commutator_mem_lowerCentralSeries (G := G) m n (g : G) (h₂ : G)
          g.property h₂.property)
        h₁).symm
    exact commutator_mul_right_of_commute _ _ _ hc

theorem nextLowerCentralIn_le_representativeRightHom_ker (m n : ℕ)
    (g : lowerCentralPiece G m) :
    nextLowerCentralIn G n ≤ (lowerCentralRepresentativeRightHom G m n g).ker := by
  intro h hh
  refine QuotientGroup.induction_on g fun g => ?_
  change lowerCentralFirstVariableBracket G m n h
    (QuotientGroup.mk' (nextLowerCentralIn G m) g) = 1
  rw [lowerCentralFirstVariableBracket_mk]
  apply lowerCentralPieceAmbientHom_injective G (m + n + 1)
  rw [lowerCentralRepresentativeBracket_ambient, map_one,
    ← map_commutatorElement]
  apply (QuotientGroup.eq_one_iff ⁅(g : G), (h : G)⁆).mpr
  have hmem := group_commutator_mem_lowerCentralSeries (G := G) m (n + 1)
    (g : G) (h : G) g.property hh
  simpa only [show m + (n + 1) + 1 = (m + n + 1) + 1 by omega] using hmem

/-- The genuine bracket descends through both original successive group
quotients; it is a homomorphism in each variable. -/
def lowerCentralPieceBracket (m n : ℕ) :
    lowerCentralPiece G m →* (lowerCentralPiece G n →* lowerCentralPiece G (m + n + 1)) where
  toFun g := QuotientGroup.lift (nextLowerCentralIn G n)
    (lowerCentralRepresentativeRightHom G m n g)
    (nextLowerCentralIn_le_representativeRightHom_ker G m n g)
  map_one' := by
    apply MonoidHom.ext
    intro h
    refine QuotientGroup.induction_on h fun h => ?_
    change lowerCentralFirstVariableBracket G m n h 1 = 1
    exact (lowerCentralFirstVariableBracket G m n h).map_one
  map_mul' g₁ g₂ := by
    apply MonoidHom.ext
    intro h
    refine QuotientGroup.induction_on h fun h => ?_
    change lowerCentralFirstVariableBracket G m n h (g₁ * g₂) =
      lowerCentralFirstVariableBracket G m n h g₁ *
        lowerCentralFirstVariableBracket G m n h g₂
    exact (lowerCentralFirstVariableBracket G m n h).map_mul _ _

@[simp]
theorem lowerCentralPieceBracket_mk_mk (m n : ℕ)
    (g : lowerCentralSeries G m) (h : lowerCentralSeries G n) :
    lowerCentralPieceBracket G m n
      (QuotientGroup.mk' (nextLowerCentralIn G m) g)
      (QuotientGroup.mk' (nextLowerCentralIn G n) h) =
      QuotientGroup.mk' (nextLowerCentralIn G (m + n + 1))
        ⟨⁅(g : G), (h : G)⁆,
          group_commutator_mem_lowerCentralSeries (G := G) m n (g : G) (h : G)
            g.property h.property⟩ := rfl

/-- The additive form uses the original abelian group quotients. -/
def lowerCentralPieceBracketAdd (m n : ℕ) :
    Additive (lowerCentralPiece G m) →+
      (Additive (lowerCentralPiece G n) →+ Additive (lowerCentralPiece G (m + n + 1))) where
  toFun g :=
    { toFun := fun h => Additive.ofMul
        (lowerCentralPieceBracket G m n (Additive.toMul g) (Additive.toMul h))
      map_zero' := (lowerCentralPieceBracket G m n (Additive.toMul g)).map_one
      map_add' h₁ h₂ := (lowerCentralPieceBracket G m n (Additive.toMul g)).map_mul
        (Additive.toMul h₁) (Additive.toMul h₂) }
  map_zero' := by
    apply AddMonoidHom.ext
    intro h
    change lowerCentralPieceBracket G m n 1 (Additive.toMul h) = 1
    exact congrArg (fun f : lowerCentralPiece G n →* lowerCentralPiece G (m + n + 1) =>
      f (Additive.toMul h)) (lowerCentralPieceBracket G m n).map_one
  map_add' g₁ g₂ := by
    apply AddMonoidHom.ext
    intro h
    change lowerCentralPieceBracket G m n
      (Additive.toMul g₁ * Additive.toMul g₂) (Additive.toMul h) =
      lowerCentralPieceBracket G m n (Additive.toMul g₁) (Additive.toMul h) *
        lowerCentralPieceBracket G m n (Additive.toMul g₂) (Additive.toMul h)
    exact congrArg (fun f : lowerCentralPiece G n →* lowerCentralPiece G (m + n + 1) =>
      f (Additive.toMul h)) ((lowerCentralPieceBracket G m n).map_mul
        (Additive.toMul g₁) (Additive.toMul g₂))

/-- Integer bilinearity is obtained from actual additive homomorphisms. -/
def lowerCentralPieceBracketInt (m n : ℕ) :
    Additive (lowerCentralPiece G m) →ₗ[ℤ]
      (Additive (lowerCentralPiece G n) →ₗ[ℤ] Additive (lowerCentralPiece G (m + n + 1))) :=
  (show Additive (lowerCentralPiece G m) →+
      (Additive (lowerCentralPiece G n) →ₗ[ℤ] Additive (lowerCentralPiece G (m + n + 1))) from
    { toFun := fun g => (lowerCentralPieceBracketAdd G m n g).toIntLinearMap
      map_zero' := by
        ext h
        change lowerCentralPieceBracketAdd G m n 0 h = 0
        exact congrArg
          (fun f : Additive (lowerCentralPiece G n) →+
            Additive (lowerCentralPiece G (m + n + 1)) => f h)
          (lowerCentralPieceBracketAdd G m n).map_zero
      map_add' g₁ g₂ := by
        ext h
        change lowerCentralPieceBracketAdd G m n (g₁ + g₂) h =
          lowerCentralPieceBracketAdd G m n g₁ h + lowerCentralPieceBracketAdd G m n g₂ h
        exact congrArg
          (fun f : Additive (lowerCentralPiece G n) →+
            Additive (lowerCentralPiece G (m + n + 1)) => f h)
          ((lowerCentralPieceBracketAdd G m n).map_add g₁ g₂) }).toIntLinearMap

/-- Rationalization of an original LCS piece, before any metabelian
specialization. This is the actual tensor product of the original piece. -/
abbrev rationalLowerCentralPiece (n : ℕ) := ℚ ⊗[ℤ] Additive (lowerCentralPiece G n)

/-- Genuine rational bilinear scalar extension of the original bracket. -/
def rationalLowerCentralPieceBracket (m n : ℕ) :
    rationalLowerCentralPiece G m →ₗ[ℚ]
      (rationalLowerCentralPiece G n →ₗ[ℚ] rationalLowerCentralPiece G (m + n + 1)) :=
  AlgebraTensorModule.lift (R := ℤ) (A := ℚ) (M := ℚ)
    (N := Additive (lowerCentralPiece G m))
    (P := rationalLowerCentralPiece G n →ₗ[ℚ] rationalLowerCentralPiece G (m + n + 1))
    (LinearMap.toSpanSingleton ℚ
      (Additive (lowerCentralPiece G m) →ₗ[ℤ]
        (rationalLowerCentralPiece G n →ₗ[ℚ] rationalLowerCentralPiece G (m + n + 1)))
      ((AlgebraTensorModule.lTensor ℚ ℚ).comp (lowerCentralPieceBracketInt G m n)))

@[simp]
theorem rationalLowerCentralPieceBracket_tmul_tmul (m n : ℕ) (c d : ℚ)
    (g : Additive (lowerCentralPiece G m)) (h : Additive (lowerCentralPiece G n)) :
    rationalLowerCentralPieceBracket G m n (c ⊗ₜ[ℤ] g) (d ⊗ₜ[ℤ] h) =
      (c * d) ⊗ₜ[ℤ] (lowerCentralPieceBracketAdd G m n g h) := by
  simp only [rationalLowerCentralPieceBracket, AlgebraTensorModule.lift_tmul,
    LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    AlgebraTensorModule.lTensor_tmul, lowerCentralPieceBracketInt,
    AddMonoidHom.coe_toIntLinearMap, TensorProduct.smul_tmul', smul_eq_mul]
  rfl

/-- The same actual construction applied to the original maximal
metabelian group quotient, with exactly the previously defined Chen
spaces as its domain and codomain. -/
def rationalChenPieceBracket (m n : ℕ) :
    rationalChenSpace G m →ₗ[ℚ]
      (rationalChenSpace G n →ₗ[ℚ] rationalChenSpace G (m + n + 1)) :=
  rationalLowerCentralPieceBracket (metabelianQuotient G) m n

end ChenRanks
