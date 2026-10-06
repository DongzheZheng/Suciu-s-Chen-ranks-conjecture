import ChenRanks.ScalarGroupAssociatedGradedMap
import ChenRanks.GroupLowerCentralDegreeOne

/-!
# The genuine group-to-Chen map is an isomorphism in degree one

The source and target retain their native original lower-central
quotients. Their actual abelianization equivalences identify the actual
projection G to G/G'' with a genuine degree-one equivalence. Scalar
extension keeps this same original map. This proves its injectivity on
the actual first homogeneous subspace, without any formality assertion.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks

variable (G : Type*) [Group G]

/-- Actual first lower-central quotients are linked by their actual
original abelianization maps. -/
def lowerCentralFirstChenEquiv :
    lowerCentralPiece G 0 ≃* lowerCentralPiece (metabelianQuotient G) 0 :=
  ((lowerCentralDegreeOneAbelianizationEquiv G).trans
    (metabelianAbelianizationEquiv G)).trans
      (lowerCentralDegreeOneAbelianizationEquiv (metabelianQuotient G)).symm

/-- This equivalence is the actual original group projection's
successive-quotient map, rather than an unspecified first-piece map. -/
theorem lowerCentralPieceMap_firstChen_eq (x : lowerCentralPiece G 0) :
    lowerCentralPieceMap
        (QuotientGroup.mk' (derivedSeries G 2) : G →* metabelianQuotient G) 0 x =
      lowerCentralFirstChenEquiv G x := by
  refine QuotientGroup.induction_on x fun g => ?_
  apply (lowerCentralDegreeOneAbelianizationEquiv (metabelianQuotient G)).injective
  change lowerCentralDegreeOneAbelianizationEquiv (metabelianQuotient G)
      (lowerCentralPieceMap
        (QuotientGroup.mk' (derivedSeries G 2) : G →* metabelianQuotient G) 0
        (QuotientGroup.mk' (nextLowerCentralIn G 0) g)) =
    lowerCentralDegreeOneAbelianizationEquiv (metabelianQuotient G)
      (lowerCentralFirstChenEquiv G (QuotientGroup.mk' (nextLowerCentralIn G 0) g))
  rw [lowerCentralPieceMap_mk]
  change lowerCentralDegreeOneAbelianizationEquiv (metabelianQuotient G)
      (QuotientGroup.mk' (nextLowerCentralIn (metabelianQuotient G) 0)
        (lowerCentralRepresentativeMap
          (QuotientGroup.mk' (derivedSeries G 2) : G →* metabelianQuotient G) 0 g)) =
    lowerCentralDegreeOneAbelianizationEquiv (metabelianQuotient G)
      ((lowerCentralDegreeOneAbelianizationEquiv (metabelianQuotient G)).symm
        (metabelianAbelianizationEquiv G
          (lowerCentralDegreeOneAbelianizationEquiv G
            (QuotientGroup.mk' (nextLowerCentralIn G 0) g))))
  rw [MulEquiv.apply_symm_apply, lowerCentralDegreeOneAbelianizationEquiv_mk,
    lowerCentralDegreeOneAbelianizationEquiv_mk, metabelianAbelianizationEquiv_of]
  rfl

theorem lowerCentralPieceMap_firstChen_bijective :
    Function.Bijective (lowerCentralPieceMap
      (QuotientGroup.mk' (derivedSeries G 2) : G →* metabelianQuotient G) 0) := by
  have heq : lowerCentralPieceMap
        (QuotientGroup.mk' (derivedSeries G 2) : G →* metabelianQuotient G) 0 =
      (lowerCentralFirstChenEquiv G).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    exact lowerCentralPieceMap_firstChen_eq G x
  rw [heq]
  exact (lowerCentralFirstChenEquiv G).bijective

variable (k : Type*) [Field k] [CharZero k]

/-- True scalar extension of the same original integral equivalence. -/
def scalarFirstChenEquiv :
    scalarLowerCentralPiece k G 0 ≃ₗ[k]
      scalarLowerCentralPiece k (metabelianQuotient G) 0 :=
  AlgebraTensorModule.congr (LinearEquiv.refl k k)
    (lowerCentralFirstChenEquiv G).toAdditive.toIntLinearEquiv

omit [CharZero k] in
@[simp] theorem scalarFirstChenEquiv_tmul (c : k)
    (a : Additive (lowerCentralPiece G 0)) :
    scalarFirstChenEquiv G k (c ⊗ₜ[ℤ] a) =
      c ⊗ₜ[ℤ] Additive.ofMul
        (lowerCentralFirstChenEquiv G (Additive.toMul a)) := rfl

/-- The native scalar quotient map is this actual equivalence. -/
theorem scalarLowerCentralPieceMap_firstChen_eq
    (x : scalarLowerCentralPiece k G 0) :
    scalarLowerCentralPieceMap k
        (QuotientGroup.mk' (derivedSeries G 2) : G →* metabelianQuotient G) 0 x =
      scalarFirstChenEquiv G k x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]; rfl
  | tmul c a =>
    change c ⊗ₜ[ℤ] Additive.ofMul
        (lowerCentralPieceMap
          (QuotientGroup.mk' (derivedSeries G 2) : G →* metabelianQuotient G) 0
          (Additive.toMul a)) =
      c ⊗ₜ[ℤ] Additive.ofMul
        (lowerCentralFirstChenEquiv G (Additive.toMul a))
    rw [lowerCentralPieceMap_firstChen_eq]
    rfl

theorem scalarLowerCentralPieceMap_firstChen_bijective :
    Function.Bijective (scalarLowerCentralPieceMap k
      (QuotientGroup.mk' (derivedSeries G 2) : G →* metabelianQuotient G) 0) := by
  have heq : scalarLowerCentralPieceMap k
        (QuotientGroup.mk' (derivedSeries G 2) : G →* metabelianQuotient G) 0 =
      (scalarFirstChenEquiv G k).toLinearMap := by
    apply LinearMap.ext
    intro x
    exact scalarLowerCentralPieceMap_firstChen_eq G k x
  rw [heq]
  exact (scalarFirstChenEquiv G k).bijective

/-- The actual native group-to-Chen Lie map keeps the canonical first
original generators via the actual first quotient equivalence. -/
theorem scalarGroupToChenGradedLieHom_first_inclusion
    (x : scalarLowerCentralPiece k G 0) :
    scalarGroupToChenGradedLieHom k G (scalarGroupGradedInclusion k G 0 x) =
      scalarGroupGradedInclusion k (metabelianQuotient G) 0
        (scalarFirstChenEquiv G k x) := by
  change scalarGroupAssociatedGradedLieHom k
      (QuotientGroup.mk' (derivedSeries G 2) : G →* metabelianQuotient G)
      (scalarGroupGradedInclusion k G 0 x) = _
  rw [scalarGroupAssociatedGradedLieHom_inclusion,
    scalarLowerCentralPieceMap_firstChen_eq]
  rfl

/-- Injectivity is certified on the original homogeneous degree-one
subspace; no higher-degree injectivity is asserted. -/
theorem scalarGroupToChenGradedLieHom_injective_first :
    Function.Injective (fun x : scalarLowerCentralPiece k G 0 =>
      scalarGroupToChenGradedLieHom k G (scalarGroupGradedInclusion k G 0 x)) := by
  intro x y hxy
  change scalarGroupToChenGradedLieHom k G (scalarGroupGradedInclusion k G 0 x) =
    scalarGroupToChenGradedLieHom k G (scalarGroupGradedInclusion k G 0 y) at hxy
  rw [scalarGroupToChenGradedLieHom_first_inclusion,
    scalarGroupToChenGradedLieHom_first_inclusion] at hxy
  exact (scalarFirstChenEquiv G k).injective
    (scalarGroupGradedInclusion_injective k (metabelianQuotient G) 0 hxy)

end ChenRanks
