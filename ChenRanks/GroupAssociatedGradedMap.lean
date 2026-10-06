import ChenRanks.GroupAssociatedGradedLie
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The genuine degree-preserving associated Lie map of a group homomorphism

The original group homomorphism actually preserves the native lower
central terms. Native quotient descent, integral linearization, rational
scalar extension, and direct-sum extension construct its associated Lie
map. Its bracket compatibility and exact homogeneous degree preservation
are conclusions about these actual constructions, not additional data.
-/

noncomputable section

open scoped TensorProduct DirectSum commutatorElement

namespace ChenRanks

variable {G H : Type*} [Group G] [Group H]

/-- The actual group map restricted to actual native lower-central terms. -/
def lowerCentralRepresentativeMap (f : G →* H) (n : ℕ) :
    lowerCentralSeries G n →* lowerCentralSeries H n where
  toFun g := ⟨f (g : G), lowerCentralSeries.map f n
    (Subgroup.mem_map_of_mem f g.property)⟩
  map_one' := Subtype.ext f.map_one
  map_mul' g h := Subtype.ext (f.map_mul (g : G) (h : G))

@[simp] theorem lowerCentralRepresentativeMap_coe (f : G →* H) (n : ℕ)
    (g : lowerCentralSeries G n) :
    (lowerCentralRepresentativeMap f n g : H) = f (g : G) := rfl

theorem nextLowerCentralIn_le_representativeMap_ker (f : G →* H) (n : ℕ) :
    nextLowerCentralIn G n ≤
      ((QuotientGroup.mk' (nextLowerCentralIn H n)).comp
        (lowerCentralRepresentativeMap f n)).ker := by
  intro g hg
  change QuotientGroup.mk' (nextLowerCentralIn H n)
    (lowerCentralRepresentativeMap f n g) = 1
  apply (QuotientGroup.eq_one_iff (lowerCentralRepresentativeMap f n g)).mpr
  change f (g : G) ∈ lowerCentralSeries H (n + 1)
  exact lowerCentralSeries.map f (n + 1) (Subgroup.mem_map_of_mem f hg)

/-- Actual quotient descent uses the proved preservation of the next
native term. -/
def lowerCentralPieceMap (f : G →* H) (n : ℕ) :
    lowerCentralPiece G n →* lowerCentralPiece H n :=
  QuotientGroup.lift (nextLowerCentralIn G n)
    ((QuotientGroup.mk' (nextLowerCentralIn H n)).comp
      (lowerCentralRepresentativeMap f n))
    (nextLowerCentralIn_le_representativeMap_ker f n)

@[simp] theorem lowerCentralPieceMap_mk (f : G →* H) (n : ℕ)
    (g : lowerCentralSeries G n) :
    lowerCentralPieceMap f n (QuotientGroup.mk' (nextLowerCentralIn G n) g) =
      QuotientGroup.mk' (nextLowerCentralIn H n) (lowerCentralRepresentativeMap f n g) :=
  rfl

/-- Original commutator naturality descends through both original
successive quotients. -/
theorem lowerCentralPieceMap_bracket (f : G →* H) (m n : ℕ)
    (x : lowerCentralPiece G m) (y : lowerCentralPiece G n) :
    lowerCentralPieceMap f (m + n + 1) (lowerCentralPieceBracket G m n x y) =
      lowerCentralPieceBracket H m n (lowerCentralPieceMap f m x)
        (lowerCentralPieceMap f n y) := by
  refine QuotientGroup.induction_on x fun x => ?_
  refine QuotientGroup.induction_on y fun y => ?_
  change lowerCentralPieceMap f (m + n + 1)
      (lowerCentralPieceBracket G m n
        (QuotientGroup.mk' (nextLowerCentralIn G m) x)
        (QuotientGroup.mk' (nextLowerCentralIn G n) y)) =
    lowerCentralPieceBracket H m n
      (lowerCentralPieceMap f m (QuotientGroup.mk' (nextLowerCentralIn G m) x))
      (lowerCentralPieceMap f n (QuotientGroup.mk' (nextLowerCentralIn G n) y))
  apply lowerCentralPieceAmbientHom_injective H (m + n + 1)
  simp only [lowerCentralPieceBracket_mk_mk, lowerCentralPieceMap_mk,
    lowerCentralPieceAmbientHom_mk]
  change QuotientGroup.mk' (lowerCentralSeries H (m + n + 1 + 1))
      (f ⁅(x : G), (y : G)⁆) =
    QuotientGroup.mk' (lowerCentralSeries H (m + n + 1 + 1))
      ⁅f (x : G), f (y : G)⁆
  rw [map_commutatorElement]

def lowerCentralPieceMapAdd (f : G →* H) (n : ℕ) :
    Additive (lowerCentralPiece G n) →+ Additive (lowerCentralPiece H n) where
  toFun x := Additive.ofMul (lowerCentralPieceMap f n (Additive.toMul x))
  map_zero' := (lowerCentralPieceMap f n).map_one
  map_add' x y := (lowerCentralPieceMap f n).map_mul (Additive.toMul x) (Additive.toMul y)

def lowerCentralPieceMapInt (f : G →* H) (n : ℕ) :
    Additive (lowerCentralPiece G n) →ₗ[ℤ] Additive (lowerCentralPiece H n) :=
  (lowerCentralPieceMapAdd f n).toIntLinearMap

theorem lowerCentralPieceMapAdd_bracket (f : G →* H) (m n : ℕ)
    (x : Additive (lowerCentralPiece G m)) (y : Additive (lowerCentralPiece G n)) :
    lowerCentralPieceMapAdd f (m + n + 1) (lowerCentralPieceBracketAdd G m n x y) =
      lowerCentralPieceBracketAdd H m n (lowerCentralPieceMapAdd f m x)
        (lowerCentralPieceMapAdd f n y) :=
  congrArg Additive.ofMul
    (lowerCentralPieceMap_bracket f m n (Additive.toMul x) (Additive.toMul y))

/-- Real scalar extension on the original rationalized group quotient. -/
def rationalLowerCentralPieceMap (f : G →* H) (n : ℕ) :
    rationalLowerCentralPiece G n →ₗ[ℚ] rationalLowerCentralPiece H n :=
  TensorProduct.AlgebraTensorModule.lTensor ℚ ℚ (lowerCentralPieceMapInt f n)

@[simp] theorem rationalLowerCentralPieceMap_tmul (f : G →* H) (n : ℕ)
    (c : ℚ) (x : Additive (lowerCentralPiece G n)) :
    rationalLowerCentralPieceMap f n (c ⊗ₜ[ℤ] x) =
      c ⊗ₜ[ℤ] (lowerCentralPieceMapAdd f n x) := by
  rw [rationalLowerCentralPieceMap, TensorProduct.AlgebraTensorModule.lTensor_tmul]
  rfl

/-- Two genuine tensor inductions preserve the original bilinear bracket. -/
theorem rationalLowerCentralPieceMap_bracket (f : G →* H) (m n : ℕ)
    (x : rationalLowerCentralPiece G m) (y : rationalLowerCentralPiece G n) :
    rationalLowerCentralPieceMap f (m + n + 1)
        (rationalLowerCentralPieceBracket G m n x y) =
      rationalLowerCentralPieceBracket H m n (rationalLowerCentralPieceMap f m x)
        (rationalLowerCentralPieceMap f n y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x₁ x₂ ih₁ ih₂ =>
    simp only [map_add, LinearMap.add_apply, ih₁, ih₂]
  | tmul c x =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add y₁ y₂ ih₁ ih₂ =>
      simp only [map_add, LinearMap.add_apply, ih₁, ih₂]
    | tmul d y =>
      rw [rationalLowerCentralPieceBracket_tmul_tmul,
        rationalLowerCentralPieceMap_tmul, rationalLowerCentralPieceMap_tmul,
        rationalLowerCentralPieceMap_tmul, rationalLowerCentralPieceBracket_tmul_tmul,
        lowerCentralPieceMapAdd_bracket]

/-- The actual direct-sum extension sends each native degree to exactly
the same native degree. -/
def rationalGroupAssociatedGradedMap (f : G →* H) :
    rationalGroupAssociatedGraded G →ₗ[ℚ] rationalGroupAssociatedGraded H :=
  DirectSum.toModule ℚ ℕ (rationalGroupAssociatedGraded H)
    (fun n => (rationalGroupGradedInclusion H n).comp (rationalLowerCentralPieceMap f n))

@[simp] theorem rationalGroupAssociatedGradedMap_inclusion (f : G →* H) (n : ℕ)
    (x : rationalLowerCentralPiece G n) :
    rationalGroupAssociatedGradedMap f (rationalGroupGradedInclusion G n x) =
      rationalGroupGradedInclusion H n (rationalLowerCentralPieceMap f n x) := by
  simp only [rationalGroupAssociatedGradedMap, rationalGroupGradedInclusion,
    DirectSum.toModule_lof, LinearMap.comp_apply]

theorem rationalGroupAssociatedGradedMap_lie (f : G →* H)
    (x y : rationalGroupAssociatedGraded G) :
    rationalGroupAssociatedGradedMap f ⁅x, y⁆ =
      ⁅rationalGroupAssociatedGradedMap f x, rationalGroupAssociatedGradedMap f y⁆ := by
  induction x using DirectSum.induction_on with
  | zero => simp only [zero_lie, map_zero]
  | add x₁ x₂ ih₁ ih₂ => rw [add_lie, map_add, map_add, add_lie, ih₁, ih₂]
  | of m x =>
    induction y using DirectSum.induction_on with
    | zero => simp only [lie_zero, map_zero]
    | add y₁ y₂ ih₁ ih₂ => rw [lie_add, map_add, map_add, lie_add, ih₁, ih₂]
    | of n y =>
      change rationalGroupAssociatedGradedMap f
          ⁅rationalGroupGradedInclusion G m x, rationalGroupGradedInclusion G n y⁆ =
        ⁅rationalGroupAssociatedGradedMap f (rationalGroupGradedInclusion G m x),
          rationalGroupAssociatedGradedMap f (rationalGroupGradedInclusion G n y)⁆
      rw [rationalGroupAssociatedGraded_lie_inclusions,
        rationalGroupAssociatedGradedMap_inclusion,
        rationalGroupAssociatedGradedMap_inclusion,
        rationalGroupAssociatedGradedMap_inclusion,
        rationalGroupAssociatedGraded_lie_inclusions,
        rationalLowerCentralPieceMap_bracket]

/-- The original group homomorphism induces a genuine native Lie homomorphism. -/
def rationalGroupAssociatedGradedLieHom (f : G →* H) :
    rationalGroupAssociatedGraded G →ₗ⁅ℚ⁆ rationalGroupAssociatedGraded H where
  __ := rationalGroupAssociatedGradedMap f
  map_lie' := by
    intro x y
    exact rationalGroupAssociatedGradedMap_lie f x y

@[simp] theorem rationalGroupAssociatedGradedLieHom_inclusion (f : G →* H) (n : ℕ)
    (x : rationalLowerCentralPiece G n) :
    rationalGroupAssociatedGradedLieHom f (rationalGroupGradedInclusion G n x) =
      rationalGroupGradedInclusion H n (rationalLowerCentralPieceMap f n x) :=
  rationalGroupAssociatedGradedMap_inclusion f n x

/-- The actual maximal-metabelian group projection gives the actual
degree-preserving Lie map to the original Chen direct sum. -/
def rationalGroupToChenGradedLieHom (G : Type*) [Group G] :
    rationalGroupAssociatedGraded G →ₗ⁅ℚ⁆ rationalChenAssociatedGraded G :=
  rationalGroupAssociatedGradedLieHom
    (QuotientGroup.mk' (derivedSeries G 2) : G →* metabelianQuotient G)

@[simp] theorem rationalGroupToChenGradedLieHom_inclusion (G : Type*) [Group G]
    (n : ℕ) (x : rationalLowerCentralPiece G n) :
    rationalGroupToChenGradedLieHom G (rationalGroupGradedInclusion G n x) =
      rationalGroupGradedInclusion (metabelianQuotient G) n
        (rationalLowerCentralPieceMap
          (QuotientGroup.mk' (derivedSeries G 2) : G →* metabelianQuotient G) n x) :=
  rationalGroupAssociatedGradedLieHom_inclusion _ n x

end ChenRanks
