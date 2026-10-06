import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Canonical residue fields of actual prime localizations

The actual uniqueness equivalence of two prime localizations induces the
actual residue-field equivalence. It preserves the original coordinate
ring action by the actual residue-map naturality formula. Neither a
residue-field comparison nor its compatibility is assumed.
-/

noncomputable section

namespace ChenRanks

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p] [IsLocalRing S]

/-- The residue field of an actual prime localization is canonically
identified with the prime's native residue field, over the original ring. -/
def actualLocalizationResidueFieldAlgEquiv :
    IsLocalRing.ResidueField S ≃ₐ[R] p.ResidueField := by
  let e : S ≃ₐ[R] Localization.AtPrime p :=
    IsLocalization.algEquiv p.primeCompl S (Localization.AtPrime p)
  letI : IsLocalHom e.toRingEquiv.toRingHom :=
    isLocalHom_of_leftInverse e.symm.toRingHom e.left_inv
  refine { IsLocalRing.ResidueField.mapEquiv e.toRingEquiv with commutes' := ?_ }
  intro r
  change IsLocalRing.ResidueField.map e.toRingHom
      (IsLocalRing.residue S (algebraMap R S r)) =
    IsLocalRing.residue (Localization.AtPrime p) (algebraMap R (Localization.AtPrime p) r)
  rw [IsLocalRing.ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue (Localization.AtPrime p)) (e.commutes r)

/-- The constructed equivalence fixes the actual residue of every
original coordinate-ring element. -/
@[simp]
theorem actualLocalizationResidueFieldAlgEquiv_algebraMap (r : R) :
    actualLocalizationResidueFieldAlgEquiv R S p
      (algebraMap R (IsLocalRing.ResidueField S) r) =
      algebraMap R p.ResidueField r :=
  (actualLocalizationResidueFieldAlgEquiv R S p).commutes r

end ChenRanks
