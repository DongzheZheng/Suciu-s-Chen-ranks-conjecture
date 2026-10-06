import ChenRanks.KoszulCanonicalFamilyHilbertTarget
import ChenRanks.FiniteDimensionFiberSum

/-!
# Degreewise numerical consequence of the actual canonical map

This algebraic reduction takes bijectivity of the literal original
degree map as an explicit hypothesis.  Its target is the actual finite
family of original zero-relation Koszul degrees.  The resulting count
is derived from native finite-dimensional linear algebra.  This file
does not establish bijectivity in the effective geometric range.
-/
noncomputable section
open scoped BigOperators
namespace ChenRanks.Koszul
open ChenRanks.Resonance
variable (k : Type*) [Field k] [CharZero k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))
attribute [local instance 2000]
  hilbertHomogeneousGroup hilbertHomogeneousMonoid hilbertHomogeneousBaseCoefficients
  hilbertFamilyDegreeGroup hilbertFamilyDegreeMonoid hilbertFamilyDegreeBaseCoefficients
variable (hsep : ∀ P : Submodule k E,
  IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
  2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)
local instance originalDegreeHilbertFamilyFintype :
    Fintype (OriginalMaximalIsotropicFamily (cupQuotient I)) :=
  canonicalFamilyFintype k E I hsep
variable {τ : Type*} [Fintype τ]
variable (b : _root_.Module.Basis τ k (_root_.Module.Dual k E))

theorem originalCanonicalFamilyHomogeneous_counted_finrank_of_bijective
    (r : ℕ) (hbij : Function.Bijective (originalCanonicalFamilyHomogeneousMap k E I b r)) :
    letI := originalDegreeHilbertFamilyFintype k E I hsep
    _root_.Module.finrank k
      (homogeneousModule k (_root_.Module.Dual k E) b (exteriorAnnihilator k E 2 I) r) =
      ∑ m ∈ Finset.range (_root_.Module.finrank k E + 1),
        Fintype.card {P : OriginalMaximalIsotropicFamily (cupQuotient I) //
          _root_.Module.finrank k P.val = m} * ((r + 1) * (m + r).choose (r + 2)) := by
  letI := originalDegreeHilbertFamilyFintype k E I hsep
  have e := LinearEquiv.ofBijective (originalCanonicalFamilyHomogeneousMap k E I b r) hbij
  rw [e.finrank_eq, canonicalFamilyHomogeneousDegree_finrank k E I hsep r]
  exact ChenRanks.sum_by_bounded_nat_fibers
    (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) => _root_.Module.finrank k P.val)
    (_root_.Module.finrank k E) (fun P => P.val.finrank_le)
    (fun m => (r + 1) * (m + r).choose (r + 2))

end ChenRanks.Koszul
