import ChenRanks.AffinePivotQuotient
import ChenRanks.LocalizationResidueFieldComparison
import ChenRanks.ArrangementHyperplaneResidues

/-!
# The actual hyperplane residue field in pivot coordinates

The actual prime-localization residue field is first identified canonically
with the prime's native residue field. The already constructed actual
hyperplane quotient then supplies a fraction-ring structure on the actual
remaining-coordinate field. Uniqueness of fraction rings gives the actual
field comparison, and fixes the actual residue of each original polynomial.
No residue-field comparison or coordinate compatibility is assumed.
-/

noncomputable section

namespace ChenRanks

open scoped nonZeroDivisors

section QuotientField

variable {R B : Type*} [CommRing R] [CommRing B] [IsDomain B]
  (p : Ideal R) [p.IsPrime]

/-- A constructed quotient-coordinate ring equivalence determines the
actual native residue-field comparison through uniqueness of fraction rings. -/
def quotientCoordinateResidueFieldEquiv (e : (R ⧸ p) ≃+* B) :
    p.ResidueField ≃+* FractionRing B := by
  letI : Algebra (R ⧸ p) (FractionRing B) :=
    ((algebraMap B (FractionRing B)).comp e.toRingHom).toAlgebra
  letI : IsFractionRing (R ⧸ p) (FractionRing B) :=
    IsFractionRing.of_ringEquiv_left e (fun _ => rfl)
  exact (IsLocalization.algEquiv (nonZeroDivisors (R ⧸ p))
    p.ResidueField (FractionRing B)).toRingEquiv

omit [IsDomain B] in
/-- The constructed field comparison fixes every actual quotient element. -/
theorem quotientCoordinateResidueFieldEquiv_algebraMap
    (e : (R ⧸ p) ≃+* B) (q : R ⧸ p) :
    quotientCoordinateResidueFieldEquiv p e
      (algebraMap (R ⧸ p) p.ResidueField q) =
      algebraMap B (FractionRing B) (e q) := by
  letI : Algebra (R ⧸ p) (FractionRing B) :=
    ((algebraMap B (FractionRing B)).comp e.toRingHom).toAlgebra
  letI : IsFractionRing (R ⧸ p) (FractionRing B) :=
    IsFractionRing.of_ringEquiv_left e (fun _ => rfl)
  exact (IsLocalization.algEquiv (nonZeroDivisors (R ⧸ p))
    p.ResidueField (FractionRing B)).commutes q

omit [IsDomain B] in
/-- Consequently it preserves the actual residue of every original
coordinate-ring polynomial, through the actual quotient map. -/
theorem quotientCoordinateResidueFieldEquiv_original
    (e : (R ⧸ p) ≃+* B) (r : R) :
    quotientCoordinateResidueFieldEquiv p e (algebraMap R p.ResidueField r) =
      algebraMap B (FractionRing B) (e (Ideal.Quotient.mk p r)) := by
  rw [← Ideal.algebraMap_quotient_residueField_mk]
  exact quotientCoordinateResidueFieldEquiv_algebraMap p e _

end QuotientField

namespace AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The native residue field of the actual original hyperplane divisor is
its actual remaining-coordinate fraction field, by the two constructed maps. -/
def hyperplaneResiduePivotRingEquiv (H : ι) (j : Fin d)
    (hj : A.normal H (Pi.single j 1) ≠ 0) :
    IsLocalRing.ResidueField (A.hyperplaneLocalRing H) ≃+*
      FractionRing (HyperplanePivotRing j) :=
  (actualLocalizationResidueFieldAlgEquiv (CoordinateRing (d := d))
    (A.hyperplaneLocalRing H) (A.hyperplanePrimeIdeal H)).toRingEquiv.trans
    (quotientCoordinateResidueFieldEquiv (A.hyperplanePrimeIdeal H)
      (A.hyperplanePivotQuotientAlgEquiv H j hj).toRingEquiv)

/-- The comparison is compatible with the actual residue of every
original polynomial, using the actual pivot restriction from the same H. -/
theorem hyperplaneResiduePivotRingEquiv_algebraMap (H : ι) (j : Fin d)
    (hj : A.normal H (Pi.single j 1) ≠ 0) (r : CoordinateRing (d := d)) :
    A.hyperplaneResiduePivotRingEquiv H j hj
      (algebraMap (CoordinateRing (d := d))
        (IsLocalRing.ResidueField (A.hyperplaneLocalRing H)) r) =
      algebraMap (HyperplanePivotRing j) (FractionRing (HyperplanePivotRing j))
        (A.hyperplanePivotRestriction H j r) := by
  change quotientCoordinateResidueFieldEquiv (A.hyperplanePrimeIdeal H)
      (A.hyperplanePivotQuotientAlgEquiv H j hj).toRingEquiv
      (actualLocalizationResidueFieldAlgEquiv (CoordinateRing (d := d))
        (A.hyperplaneLocalRing H) (A.hyperplanePrimeIdeal H)
          (algebraMap (CoordinateRing (d := d))
            (IsLocalRing.ResidueField (A.hyperplaneLocalRing H)) r)) = _
  rw [actualLocalizationResidueFieldAlgEquiv_algebraMap,
    quotientCoordinateResidueFieldEquiv_original]
  change algebraMap (HyperplanePivotRing j) (FractionRing (HyperplanePivotRing j))
      (A.hyperplanePivotQuotientAlgEquiv H j hj
        (Ideal.Quotient.mk (A.hyperplanePrimeIdeal H) r)) = _
  exact congrArg (algebraMap (HyperplanePivotRing j) (FractionRing (HyperplanePivotRing j)))
    (A.hyperplanePivotQuotientAlgEquiv_mk H j hj r)

end AffineArrangement

end ChenRanks
