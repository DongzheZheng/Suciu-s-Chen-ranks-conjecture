import ChenRanks.HyperplaneResiduePivot
import ChenRanks.AffinePivotLowDegree
import ChenRanks.ArrangementParallelRelations
import ChenRanks.DifferentialFieldTransport

/-!
# Actual regular logarithms and pivot residue differentials

Every other original affine equation is a genuine unit in the actual
hyperplane local ring. Its actual unit and actual regular logarithmic
differential are constructed from the proved original principal-prime
membership criterion. The actual fraction image is the same original
equation unit, without choosing a regular lift as a hypothesis.

The previously constructed actual residue-field ring equivalence is
upgraded to an equivalence over the original complex scalars, using its
proved polynomial compatibility. Its actual differential transport then
identifies the restriction of each constructed regular logarithm with
the logarithmic differential of the actual pivot-restricted polynomial.
Affine offsets, parallel equations, and repeated restricted divisors are
all retained; there is no independence or OS-kernel premise.
-/

noncomputable section

namespace ChenRanks

section UnitDifferentialMap

variable (k A G : Type*) [Field k] [CommRing A] [Field G]
  [Algebra k A] [Algebra k G] [Algebra A G] [IsScalarTower k A G]

/-- The image of the actual regular logarithm of a local unit is its
actual field logarithm, by the universal derivation and unit inverse. -/
theorem localUnitLogDifferential_map_eq_logarithmic (u : Aˣ) :
    KaehlerDifferential.map k k A G (LogResidueCore.localUnitLogDifferential k A u) =
      logarithmicDifferential k G (Units.map (algebraMap A G).toMonoidHom u) := by
  change KaehlerDifferential.map k k A G
      (((u⁻¹ : Aˣ) : A) • KaehlerDifferential.D k A (u : A)) =
    (algebraMap A G (u : A))⁻¹ • KaehlerDifferential.D k G (algebraMap A G (u : A))
  rw [map_smul, KaehlerDifferential.map_D,
    ← algebraMap_smul G ((u⁻¹ : Aˣ) : A)]
  congr 1
  simpa only [Units.val_inv_eq_inv_val] using
    (Units.coe_map_inv (algebraMap A G).toMonoidHom u).symm

end UnitDifferentialMap

namespace AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The genuine function field of the actual pivot hyperplane. -/
abbrev HyperplanePivotField (j : Fin d) := FractionRing (HyperplanePivotRing j)

instance hyperplanePivotField_complexAlgebra (j : Fin d) :
    Algebra ℂ (HyperplanePivotField j) :=
  ((algebraMap (HyperplanePivotRing j) (HyperplanePivotField j)).comp MvPolynomial.C).toAlgebra

instance hyperplanePivotField_pivotModule (j : Fin d) :
    Module (HyperplanePivotRing j) (HyperplanePivotField j) :=
  Algebra.toModule

instance hyperplanePivotField_pivotSMul (j : Fin d) :
    SMul (HyperplanePivotRing j) (HyperplanePivotField j) :=
  (inferInstance : Algebra (HyperplanePivotRing j) (HyperplanePivotField j)).toSMul

instance hyperplanePivotField_complexModule (j : Fin d) :
    Module ℂ (HyperplanePivotField j) :=
  Algebra.toModule

instance hyperplanePivotField_complexSMul (j : Fin d) :
    SMul ℂ (HyperplanePivotField j) := (hyperplanePivotField_complexAlgebra j).toSMul

instance hyperplanePivotField_complexTower (j : Fin d) :
    IsScalarTower ℂ (HyperplanePivotRing j) (HyperplanePivotField j) :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := HyperplanePivotRing j)
    (A := HyperplanePivotField j) fun _ ↦ rfl

local instance hyperplaneLocalRing_selfAlgebra (H : ι) :
    Algebra (A.hyperplaneLocalRing H) (A.hyperplaneLocalRing H) :=
  Algebra.id (A.hyperplaneLocalRing H)

local instance hyperplaneLocalResidue_nativeAlgebra (H : ι) :
    Algebra (A.hyperplaneLocalRing H) (IsLocalRing.ResidueField (A.hyperplaneLocalRing H)) :=
  IsLocalRing.ResidueField.algebra (A.hyperplaneLocalRing H)
    (R₀ := A.hyperplaneLocalRing H)

local instance hyperplaneLocalResidue_nativeModule (H : ι) :
    Module (A.hyperplaneLocalRing H) (IsLocalRing.ResidueField (A.hyperplaneLocalRing H)) :=
  Algebra.toModule

local instance hyperplaneLocalResidue_nativeSMul (H : ι) :
    SMul (A.hyperplaneLocalRing H) (IsLocalRing.ResidueField (A.hyperplaneLocalRing H)) :=
  (hyperplaneLocalResidue_nativeAlgebra A H).toSMul

local instance hyperplaneLocalRing_nativeLieRing (H : ι) :
    LieRing (A.hyperplaneLocalRing H) := LieRing.ofAssociativeRing

/-- The actual residue-field comparison preserves the original complex
scalars because it already preserves every original polynomial. -/
def hyperplaneResiduePivotAlgEquiv (H : ι) (j : Fin d)
    (hj : A.normal H (Pi.single j 1) ≠ 0) :
    IsLocalRing.ResidueField (A.hyperplaneLocalRing H) ≃ₐ[ℂ] HyperplanePivotField j :=
  { A.hyperplaneResiduePivotRingEquiv H j hj with
    commutes' := by
      intro c
      have h := A.hyperplaneResiduePivotRingEquiv_algebraMap H j hj (MvPolynomial.C c)
      rw [A.hyperplanePivotRestriction_C H j c] at h
      have hC : (MvPolynomial.C c : CoordinateRing (d := d)) =
          algebraMap ℂ (CoordinateRing (d := d)) c := rfl
      have hC' : (MvPolynomial.C c : HyperplanePivotRing j) =
          algebraMap ℂ (HyperplanePivotRing j) c := rfl
      rw [hC, hC'] at h
      rw [← IsScalarTower.algebraMap_apply ℂ (CoordinateRing (d := d))
          (IsLocalRing.ResidueField (A.hyperplaneLocalRing H)),
        ← IsScalarTower.algebraMap_apply ℂ (HyperplanePivotRing j)
          (HyperplanePivotField j)] at h
      exact h }

/-- Original distinctness makes every different equation an actual
unit in this same original hyperplane local ring. -/
theorem hyperplaneOtherEquation_isUnit (H K : ι) (hHK : H ≠ K) :
    IsUnit (algebraMap (CoordinateRing (d := d)) (A.hyperplaneLocalRing H)
      (A.equationPolynomial K)) :=
  (IsLocalization.AtPrime.isUnit_to_map_iff (A.hyperplaneLocalRing H)
    (A.hyperplanePrimeIdeal H) (A.equationPolynomial K)).mpr
      (A.equationPolynomial_not_mem_hyperplanePrimeIdeal H K hHK)

/-- The actual unit, rather than an assumed regular lift. -/
def hyperplaneOtherEquationLocalUnit (H K : ι) (hHK : H ≠ K) :
    (A.hyperplaneLocalRing H)ˣ :=
  (A.hyperplaneOtherEquation_isUnit H K hHK).unit

@[simp]
theorem hyperplaneOtherEquationLocalUnit_coe (H K : ι) (hHK : H ≠ K) :
    (A.hyperplaneOtherEquationLocalUnit H K hHK : A.hyperplaneLocalRing H) =
      algebraMap (CoordinateRing (d := d)) (A.hyperplaneLocalRing H)
        (A.equationPolynomial K) :=
  (A.hyperplaneOtherEquation_isUnit H K hHK).unit_spec

/-- Its actual fraction image is the same original equation unit. -/
theorem hyperplaneOtherEquationLocalUnit_map_fraction (H K : ι) (hHK : H ≠ K) :
    Units.map (algebraMap (A.hyperplaneLocalRing H)
      (RationalFunctionField (d := d))).toMonoidHom
        (A.hyperplaneOtherEquationLocalUnit H K hHK) = A.equationUnit K := by
  apply Units.ext
  change algebraMap (A.hyperplaneLocalRing H) (RationalFunctionField (d := d))
    (A.hyperplaneOtherEquationLocalUnit H K hHK : A.hyperplaneLocalRing H) =
      A.equationFunction K
  rw [A.hyperplaneOtherEquationLocalUnit_coe]
  rfl

/-- The actual regular logarithmic form of the other equation in the
same actual local-ring differential module. -/
def hyperplaneOtherEquationRegularLog (H K : ι) (hHK : H ≠ K) :
    Ω[A.hyperplaneLocalRing H⁄ℂ] :=
  LogResidueCore.localUnitLogDifferential ℂ (A.hyperplaneLocalRing H)
    (A.hyperplaneOtherEquationLocalUnit H K hHK)

/-- The constructed regular logarithm pulls to the actual original
logarithm in the original rational-function field. -/
theorem hyperplaneOtherEquationRegularLog_map_fraction (H K : ι) (hHK : H ≠ K) :
    KaehlerDifferential.map ℂ ℂ (A.hyperplaneLocalRing H) (RationalFunctionField (d := d))
        (A.hyperplaneOtherEquationRegularLog H K hHK) =
      logarithmicDifferential ℂ (RationalFunctionField (d := d)) (A.equationUnit K) := by
  rw [hyperplaneOtherEquationRegularLog, localUnitLogDifferential_map_eq_logarithmic,
    A.hyperplaneOtherEquationLocalUnit_map_fraction]

/-- The actual restricted nonzero polynomial determines its genuine
unit in the actual pivot fraction field. -/
def hyperplaneRestrictedEquationUnit (H K : ι) (hHK : H ≠ K) (j : Fin d)
    (hj : A.normal H (Pi.single j 1) ≠ 0) : (HyperplanePivotField j)ˣ :=
  Units.mk0
    (algebraMap (HyperplanePivotRing j) (HyperplanePivotField j)
      (A.hyperplanePivotRestriction H j (A.equationPolynomial K)))
    ((map_ne_zero_iff _ (IsFractionRing.injective (HyperplanePivotRing j)
      (HyperplanePivotField j))).mpr
        (A.hyperplanePivotRestriction_other_ne_zero H K hHK j hj))

/-- The constructed residue field equivalence sends the actual local
unit residue to exactly the actual restricted polynomial unit. -/
theorem hyperplaneOtherEquationLocalUnit_residue_pivot (H K : ι) (hHK : H ≠ K)
    (j : Fin d) (hj : A.normal H (Pi.single j 1) ≠ 0) :
    Units.map (A.hyperplaneResiduePivotAlgEquiv H j hj).toRingHom.toMonoidHom
      (Units.map (algebraMap (A.hyperplaneLocalRing H)
        (IsLocalRing.ResidueField (A.hyperplaneLocalRing H))).toMonoidHom
          (A.hyperplaneOtherEquationLocalUnit H K hHK)) =
        A.hyperplaneRestrictedEquationUnit H K hHK j hj := by
  apply Units.ext
  change A.hyperplaneResiduePivotRingEquiv H j hj
      (algebraMap (A.hyperplaneLocalRing H)
        (IsLocalRing.ResidueField (A.hyperplaneLocalRing H))
          (A.hyperplaneOtherEquationLocalUnit H K hHK : A.hyperplaneLocalRing H)) =
    algebraMap (HyperplanePivotRing j) (HyperplanePivotField j)
      (A.hyperplanePivotRestriction H j (A.equationPolynomial K))
  rw [A.hyperplaneOtherEquationLocalUnit_coe]
  change A.hyperplaneResiduePivotRingEquiv H j hj
    (algebraMap (CoordinateRing (d := d))
      (IsLocalRing.ResidueField (A.hyperplaneLocalRing H)) (A.equationPolynomial K)) = _
  exact A.hyperplaneResiduePivotRingEquiv_algebraMap H j hj (A.equationPolynomial K)

/-- The actual residue restriction of the actual regular logarithm,
transported through the genuine scalar-compatible field comparison,
is exactly the actual logarithm of the restricted original equation. -/
theorem hyperplaneOtherEquationRegularLog_restrict_pivot (H K : ι) (hHK : H ≠ K)
    (j : Fin d) (hj : A.normal H (Pi.single j 1) ≠ 0) :
    differentialFieldLinearEquiv (A.hyperplaneResiduePivotAlgEquiv H j hj)
      (KaehlerDifferential.map ℂ ℂ (A.hyperplaneLocalRing H)
        (IsLocalRing.ResidueField (A.hyperplaneLocalRing H))
          (A.hyperplaneOtherEquationRegularLog H K hHK)) =
      logarithmicDifferential ℂ (HyperplanePivotField j)
        (A.hyperplaneRestrictedEquationUnit H K hHK j hj) := by
  change differentialFieldLinearEquiv (A.hyperplaneResiduePivotAlgEquiv H j hj)
    (KaehlerDifferential.map ℂ ℂ (A.hyperplaneLocalRing H)
      (IsLocalRing.ResidueField (A.hyperplaneLocalRing H))
        (LogResidueCore.localUnitLogDifferential ℂ (A.hyperplaneLocalRing H)
          (A.hyperplaneOtherEquationLocalUnit H K hHK))) = _
  rw [localUnitLogDifferential_map_eq_logarithmic,
    differentialFieldLinearEquiv_logarithmic, A.hyperplaneOtherEquationLocalUnit_residue_pivot]

end AffineArrangement

end ChenRanks
