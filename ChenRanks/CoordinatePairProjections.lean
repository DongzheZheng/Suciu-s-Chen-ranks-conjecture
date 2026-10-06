import ChenRanks.CoordinateExteriorRows

/-!
# Actual coordinate-pair sums and symmetric exterior projections

An actual coefficient array gives an actual linear sum of actual coordinate
wedges. Its actual contraction entries are computed directly. A symmetric
pair predicate then defines a genuine linear endomorphism of the original
exterior square by masking its proved contraction entries and taking the
actual half-sum. The resulting contraction entries are proved to be exactly
the masked original entries. No prescribed coefficient array or row law is
an assumption.

This is the coordinate mechanism for a later actual affine pair-span
partition. Neither that partition nor its OS-block conclusion is asserted
in this file.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks.Koszul

variable (k ι : Type*) [Field k] [Fintype ι]

local instance : DecidableEq ι := Classical.decEq ι
local instance coordinatePairProjections_propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The genuine linear sum of actual coordinate wedges from actual coefficients. -/
def coordinatePairSum : (ι → ι → k) →ₗ[k] (⋀[k]^2 (ι → k)) where
  toFun α := ∑ H, ∑ K, α H K • exteriorWedge (k := k) (Pi.single H 1) (Pi.single K 1)
  map_add' α β := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c α := by
    simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul]

/-- The actual coordinate table, obtained from actual Koszul contractions. -/
def coordinateExteriorRowTable : (⋀[k]^2 (ι → k)) →ₗ[k] (ι → ι → k) where
  toFun z H K := coordinateExteriorRow k ι H z K
  map_add' x y := by ext H K; simp only [map_add, Pi.add_apply]
  map_smul' c x := by ext H K; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

/-- A genuine linear mask on actual coefficient arrays. -/
def coordinatePairMask (s : ι → ι → Prop) : (ι → ι → k) →ₗ[k] (ι → ι → k) where
  toFun α H K := if s H K then α H K else 0
  map_add' α β := by
    ext H K
    by_cases h : s H K <;> simp only [Pi.add_apply, h, ↓reduceIte, zero_add]
  map_smul' c α := by
    ext H K
    by_cases h : s H K <;> simp only [Pi.smul_apply, h, ↓reduceIte, smul_zero, RingHom.id_apply]

/-- The exact coordinate entries of a genuine exterior pair sum. -/
theorem coordinatePairSum_row_entry (α : ι → ι → k) (H K : ι) :
    coordinateExteriorRow k ι H (coordinatePairSum k ι α) K = α H K - α K H := by
  change ((LinearMap.proj K).comp (coordinateExteriorRow k ι H))
    (∑ i, ∑ j, α i j • exteriorWedge (k := k) (Pi.single i 1) (Pi.single j 1)) = _
  simp only [map_sum, map_smul, LinearMap.comp_apply, LinearMap.proj_apply,
    coordinateExteriorRow_wedge, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp [Pi.single_apply, mul_sub, Finset.sum_sub_distrib, mul_ite]

variable [CharZero k]

/-- The actual exterior endomorphism obtained by masking the actual
coordinate contraction table and using the actual half-sum. -/
def coordinatePairProjection (s : ι → ι → Prop) :
    (⋀[k]^2 (ι → k)) →ₗ[k] (⋀[k]^2 (ι → k)) :=
  (2 : k)⁻¹ • (coordinatePairSum k ι).comp
    ((coordinatePairMask k ι s).comp (coordinateExteriorRowTable k ι))

/-- A symmetric actual pair mask acts on each actual contraction entry
by exactly that mask. Symmetry is a structural predicate condition,
not an assumed exterior projection law. -/
theorem coordinatePairProjection_row_entry (s : ι → ι → Prop)
    (hs : ∀ H K, s H K ↔ s K H) (H K : ι) (z : ⋀[k]^2 (ι → k)) :
    coordinateExteriorRow k ι H (coordinatePairProjection k ι s z) K =
      if s H K then coordinateExteriorRow k ι H z K else 0 := by
  change ((LinearMap.proj K).comp (coordinateExteriorRow k ι H))
    ((2 : k)⁻¹ • coordinatePairSum k ι
      (coordinatePairMask k ι s (coordinateExteriorRowTable k ι z))) = _
  rw [map_smul]
  change (2 : k)⁻¹ * coordinateExteriorRow k ι H
    (coordinatePairSum k ι (coordinatePairMask k ι s (coordinateExteriorRowTable k ι z))) K = _
  rw [coordinatePairSum_row_entry]
  change (2 : k)⁻¹ *
    ((if s H K then coordinateExteriorRow k ι H z K else 0) -
      (if s K H then coordinateExteriorRow k ι K z H else 0)) = _
  rw [coordinateExteriorRow_swap k ι K H z]
  by_cases h : s H K
  · have h' : s K H := (hs H K).mp h
    simp only [h, h', ↓reduceIte, sub_neg_eq_add]
    rw [← two_mul, ← mul_assoc, inv_mul_cancel₀ (show (2 : k) ≠ 0 by norm_num), one_mul]
  · have h' : ¬s K H := fun h' ↦ h ((hs H K).mpr h')
    simp only [h, h', ↓reduceIte, sub_self, mul_zero]

end ChenRanks.Koszul
