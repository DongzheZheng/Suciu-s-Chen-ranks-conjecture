import ChenRanks.KoszulCanonicalFamilyGradedDefects
import ChenRanks.KoszulCanonicalFamilyHilbertTarget
import ChenRanks.FiniteDimensionFiberSum

/-!
# Eventual Hilbert formula for the genuine canonical family

The actual homogeneous canonical map is eventually bijective by its
proved finite defects. The target dimension is separately computed
from the genuine original finite family. No effective bound or Chen
comparison is a hypothesis.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))

attribute [local instance 2000]
  hilbertHomogeneousGroup hilbertHomogeneousMonoid hilbertHomogeneousBaseCoefficients
  hilbertFamilyDegreeGroup hilbertFamilyDegreeMonoid hilbertFamilyDegreeBaseCoefficients

variable [CharZero k]
variable (hsep : ∀ P : Submodule k E,
  IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
  2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)

include hsep

local instance eventualHilbertFamilyFintype :
    Fintype (OriginalMaximalIsotropicFamily (cupQuotient I)) :=
  hilbertFamilyFintype k E I hsep

variable {τ : Type*} [Fintype τ]
variable (b : _root_.Module.Basis τ k (_root_.Module.Dual k E))
variable [IsAlgClosed k]

/-- Eventual Hilbert formula for the literal original homogeneous
Koszul quotient. Its bound is existential. -/
theorem originalCanonicalFamilyHomogeneous_eventual_finrank :
    letI := eventualHilbertFamilyFintype k E I hsep
    ∃ B : ℕ, ∀ r ≥ B,
      _root_.Module.finrank k
          (homogeneousModule k (_root_.Module.Dual k E) b
            (exteriorAnnihilator k E 2 I) r) =
        ∑ P : OriginalMaximalIsotropicFamily (cupQuotient I),
          (r + 1) * (_root_.Module.finrank k P.val + r).choose (r + 2) := by
  letI := eventualHilbertFamilyFintype k E I hsep
  obtain ⟨B, hB⟩ := originalCanonicalFamilyHomogeneousMap_eventually_bijective
    k E I b hsep
  refine ⟨B, fun r hr => ?_⟩
  have e := LinearEquiv.ofBijective
    (originalCanonicalFamilyHomogeneousMap k E I b r) (hB r hr)
  exact e.finrank_eq.trans (canonicalFamilyHomogeneousDegree_finrank k E I hsep r)

/-- The same genuine Hilbert formula, grouped by literal dimension
fibers of the original family, rather than by an assumed count. -/
theorem originalCanonicalFamilyHomogeneous_eventual_counted_finrank :
    letI := eventualHilbertFamilyFintype k E I hsep
    ∃ B : ℕ, ∀ r ≥ B,
      _root_.Module.finrank k
          (homogeneousModule k (_root_.Module.Dual k E) b
            (exteriorAnnihilator k E 2 I) r) =
        ∑ m ∈ Finset.range (_root_.Module.finrank k E + 1),
          Fintype.card {P : OriginalMaximalIsotropicFamily (cupQuotient I) //
              _root_.Module.finrank k P.val = m} *
            ((r + 1) * (m + r).choose (r + 2)) := by
  letI := eventualHilbertFamilyFintype k E I hsep
  obtain ⟨B, hB⟩ := originalCanonicalFamilyHomogeneous_eventual_finrank k E I hsep b
  refine ⟨B, fun r hr => ?_⟩
  rw [hB r hr]
  exact ChenRanks.sum_by_bounded_nat_fibers
    (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
      _root_.Module.finrank k P.val) (_root_.Module.finrank k E)
    (fun P => P.val.finrank_le) (fun m => (r + 1) * (m + r).choose (r + 2))

end ChenRanks.Koszul
