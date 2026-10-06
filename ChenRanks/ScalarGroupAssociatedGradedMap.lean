import ChenRanks.ScalarGroupAssociatedGraded
import ChenRanks.GroupAssociatedGradedMap
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Genuine scalar associated-Lie maps of the original group maps

The actual group homomorphism acts on the actual native lower-central
terms and their original successive quotients. Surjectivity of the group
map proves surjectivity of all these actual quotient maps; it is not a
field of an associated-graded interface. Native scalar extension then
retains the original degrees and actual commutator brackets. In particular
the genuine projection G to G/G'' induces a surjective native scalar Lie
map to the original scalarized Chen associated Lie algebra.

There is no assertion of injectivity, formality, or holonomy comparison.
-/

noncomputable section

open scoped TensorProduct DirectSum

namespace ChenRanks

variable {G H : Type*} [Group G] [Group H]

/-- Surjective actual group maps send each whole native lower-central
term onto the corresponding actual target term. -/
theorem lowerCentralSeries_map_eq_of_surjective (f : G →* H)
    (hf : Function.Surjective f) (n : ℕ) :
    (lowerCentralSeries G n).map f = lowerCentralSeries H n := by
  induction n with
  | zero =>
    rw [lowerCentralSeries_zero, lowerCentralSeries_zero]
    exact Subgroup.map_top_of_surjective f hf
  | succ n ih =>
    change Subgroup.map f ⁅lowerCentralSeries G n, (⊤ : Subgroup G)⁆ =
      ⁅lowerCentralSeries H n, (⊤ : Subgroup H)⁆
    rw [Subgroup.map_commutator, ih, Subgroup.map_top_of_surjective f hf]

/-- The representative map is onto the actual target numerator, not
only onto its ambient group. -/
theorem lowerCentralRepresentativeMap_surjective (f : G →* H)
    (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (lowerCentralRepresentativeMap f n) := by
  intro h
  have hh : (h : H) ∈ (lowerCentralSeries G n).map f := by
    rw [lowerCentralSeries_map_eq_of_surjective f hf n]
    exact h.property
  obtain ⟨g, hg, hgh⟩ := Subgroup.mem_map.mp hh
  exact ⟨⟨g, hg⟩, Subtype.ext hgh⟩

/-- The original successive quotient map is genuinely surjective. -/
theorem lowerCentralPieceMap_surjective (f : G →* H)
    (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (lowerCentralPieceMap f n) := by
  intro x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (nextLowerCentralIn H n) x
  obtain ⟨g, rfl⟩ := lowerCentralRepresentativeMap_surjective f hf n h
  exact ⟨QuotientGroup.mk' (nextLowerCentralIn G n) g,
    lowerCentralPieceMap_mk f n g⟩

theorem lowerCentralPieceMapInt_surjective (f : G →* H)
    (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (lowerCentralPieceMapInt f n) := by
  intro x
  obtain ⟨g, hg⟩ := lowerCentralPieceMap_surjective f hf n (Additive.toMul x)
  refine ⟨Additive.ofMul g, ?_⟩
  change Additive.ofMul (lowerCentralPieceMap f n g) = x
  exact congrArg Additive.ofMul hg

/-- Tensor right exactness applies to the actual original quotient map. -/
theorem rationalLowerCentralPieceMap_surjective (f : G →* H)
    (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (rationalLowerCentralPieceMap f n) :=
  LinearMap.lTensor_surjective ℚ (lowerCentralPieceMapInt_surjective f hf n)

/-- Each actual homogeneous preimage combines in the native direct sum. -/
theorem rationalGroupAssociatedGradedLieHom_surjective (f : G →* H)
    (hf : Function.Surjective f) :
    Function.Surjective (rationalGroupAssociatedGradedLieHom f) := by
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by rw [map_add, hu, hv]⟩
  | of n x =>
    obtain ⟨y, hy⟩ := rationalLowerCentralPieceMap_surjective f hf n x
    refine ⟨rationalGroupGradedInclusion G n y, ?_⟩
    rw [rationalGroupAssociatedGradedLieHom_inclusion, hy]
    rfl

variable (k : Type*) [Field k] [CharZero k]

/-- The actual integral quotient map is scalarized directly. -/
def scalarLowerCentralPieceMap (f : G →* H) (n : ℕ) :
    scalarLowerCentralPiece k G n →ₗ[k] scalarLowerCentralPiece k H n :=
  TensorProduct.AlgebraTensorModule.lTensor k k (lowerCentralPieceMapInt f n)

@[simp] theorem scalarLowerCentralPieceMap_tmul (f : G →* H) (n : ℕ)
    (c : k) (x : Additive (lowerCentralPiece G n)) :
    scalarLowerCentralPieceMap k f n (c ⊗ₜ[ℤ] x) =
      c ⊗ₜ[ℤ] lowerCentralPieceMapAdd f n x := rfl

/-- This is the native k-linear scalar extension of the original
rational associated-group map. -/
def scalarGroupAssociatedGradedMap (f : G →* H) :
    scalarGroupAssociatedGraded k G →ₗ[k] scalarGroupAssociatedGraded k H :=
  TensorProduct.AlgebraTensorModule.lTensor k k
    (rationalGroupAssociatedGradedLieHom f).toLinearMap

@[simp] theorem scalarGroupAssociatedGradedMap_tmul (f : G →* H)
    (c : k) (x : rationalGroupAssociatedGraded G) :
    scalarGroupAssociatedGradedMap k f (c ⊗ₜ[ℚ] x) =
      c ⊗ₜ[ℚ] rationalGroupAssociatedGradedLieHom f x := rfl

/-- The genuine native Lie scalar-extension law proves the Lie law
for this actual k-linear map. -/
def scalarGroupAssociatedGradedLieHom (f : G →* H) :
    scalarGroupAssociatedGraded k G →ₗ⁅k⁆ scalarGroupAssociatedGraded k H where
  __ := scalarGroupAssociatedGradedMap k f
  map_lie' := by
    intro x y
    change LieAlgebra.ExtendScalars.map (AlgHom.id ℚ k)
        (rationalGroupAssociatedGradedLieHom f) ⁅x, y⁆ =
      ⁅LieAlgebra.ExtendScalars.map (AlgHom.id ℚ k)
          (rationalGroupAssociatedGradedLieHom f) x,
        LieAlgebra.ExtendScalars.map (AlgHom.id ℚ k)
          (rationalGroupAssociatedGradedLieHom f) y⁆
    exact LieHom.map_lie _ x y

/-- The scalar map preserves each same original successive quotient. -/
theorem scalarGroupAssociatedGradedLieHom_inclusion (f : G →* H) (n : ℕ)
    (x : scalarLowerCentralPiece k G n) :
    scalarGroupAssociatedGradedLieHom k f (scalarGroupGradedInclusion k G n x) =
      scalarGroupGradedInclusion k H n (scalarLowerCentralPieceMap k f n x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c a =>
    change scalarGroupAssociatedGradedMap k f
      (scalarGroupGradedInclusion k G n (c ⊗ₜ[ℤ] a)) = _
    rw [scalarGroupGradedInclusion_tmul, scalarGroupAssociatedGradedMap_tmul,
      rationalGroupAssociatedGradedLieHom_inclusion,
      rationalLowerCentralPieceMap_tmul, scalarLowerCentralPieceMap_tmul,
      scalarGroupGradedInclusion_tmul]

/-- Surjectivity is proved from the actual original group map. -/
theorem scalarGroupAssociatedGradedLieHom_surjective (f : G →* H)
    (hf : Function.Surjective f) :
    Function.Surjective (scalarGroupAssociatedGradedLieHom k f) :=
  LinearMap.lTensor_surjective k (rationalGroupAssociatedGradedLieHom_surjective f hf)

/-- The actual maximal-metabelian group projection gives the genuine
native scalar group-to-Chen Lie map. -/
def scalarGroupToChenGradedLieHom (G : Type*) [Group G] :
    scalarGroupAssociatedGraded k G →ₗ⁅k⁆ scalarChenAssociatedGraded k G :=
  scalarGroupAssociatedGradedLieHom k
    (QuotientGroup.mk' (derivedSeries G 2) : G →* metabelianQuotient G)

theorem scalarGroupToChenGradedLieHom_surjective (G : Type*) [Group G] :
    Function.Surjective (scalarGroupToChenGradedLieHom k G) :=
  scalarGroupAssociatedGradedLieHom_surjective k
    (QuotientGroup.mk' (derivedSeries G 2)) (QuotientGroup.mk'_surjective _)

end ChenRanks
