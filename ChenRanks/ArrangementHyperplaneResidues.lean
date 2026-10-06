import ChenRanks.ArrangementDivisors
import ChenRanks.LogarithmicResidueCoefficients

/-!
# Residues at the original arrangement hyperplanes

The local rings are the actual prime localizations inside the original
rational-function field. Polynomial localization proves their formal
smoothness and their essentially finite-type structure. The one-form
residue is consequently instantiated without a smoothness premise.
These actual residues detect every coefficient of the original
logarithmic realization.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

instance hyperplaneLocalRing_commRing (H : ι) : CommRing (A.hyperplaneLocalRing H) :=
  Subalgebra.toCommRing (primeLocalizationInFractionField (CoordinateRing (d := d))
    (RationalFunctionField (d := d)) (A.hyperplanePrimeIdeal H)
      (A.hyperplanePrimeIdeal_isPrime H))

instance hyperplaneLocalRing_coordinateAlgebra (H : ι) :
    Algebra (CoordinateRing (d := d)) (A.hyperplaneLocalRing H) :=
  Subalgebra.algebra (primeLocalizationInFractionField (CoordinateRing (d := d))
    (RationalFunctionField (d := d)) (A.hyperplanePrimeIdeal H)
      (A.hyperplanePrimeIdeal_isPrime H))

instance hyperplaneLocalRing_fractionAlgebra (H : ι) :
    Algebra (A.hyperplaneLocalRing H) (RationalFunctionField (d := d)) :=
  Subalgebra.toAlgebra (primeLocalizationInFractionField (CoordinateRing (d := d))
    (RationalFunctionField (d := d)) (A.hyperplanePrimeIdeal H)
      (A.hyperplanePrimeIdeal_isPrime H))

instance hyperplaneLocalRing_isDomain (H : ι) : IsDomain (A.hyperplaneLocalRing H) :=
  Subalgebra.isDomain (primeLocalizationInFractionField (CoordinateRing (d := d))
    (RationalFunctionField (d := d)) (A.hyperplanePrimeIdeal H)
      (A.hyperplanePrimeIdeal_isPrime H))

instance hyperplaneLocalRing_atPrime (H : ι) :
    IsLocalization.AtPrime (A.hyperplaneLocalRing H) (A.hyperplanePrimeIdeal H) := by
  change IsLocalization (A.hyperplanePrimeIdeal H).primeCompl
    (Localization.subalgebra (RationalFunctionField (d := d))
      (A.hyperplanePrimeIdeal H).primeCompl
      (A.hyperplanePrimeIdeal H).primeCompl_le_nonZeroDivisors)
  infer_instance

instance hyperplaneLocalRing_complexAlgebra (H : ι) :
    Algebra ℂ (A.hyperplaneLocalRing H) :=
  ((algebraMap (CoordinateRing (d := d)) (A.hyperplaneLocalRing H)).comp
    MvPolynomial.C).toAlgebra

instance hyperplaneLocalRing_coordinateTower (H : ι) :
    IsScalarTower ℂ (CoordinateRing (d := d)) (A.hyperplaneLocalRing H) :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := CoordinateRing (d := d))
    (A := A.hyperplaneLocalRing H) fun _ ↦ rfl

instance hyperplaneLocalRing_fractionTower (H : ι) :
    IsScalarTower ℂ (A.hyperplaneLocalRing H) (RationalFunctionField (d := d)) where
  smul_assoc c s x := by
    change (algebraMap ℂ (RationalFunctionField (d := d)) c *
      (s : RationalFunctionField (d := d))) * x =
      algebraMap ℂ (RationalFunctionField (d := d)) c *
        ((s : RationalFunctionField (d := d)) * x)
    exact mul_assoc _ _ _

instance hyperplaneLocalRing_essFiniteType (H : ι) :
    Algebra.EssFiniteType ℂ (A.hyperplaneLocalRing H) := by
  letI : Algebra.EssFiniteType (CoordinateRing (d := d)) (A.hyperplaneLocalRing H) :=
    Algebra.EssFiniteType.of_isLocalization (A.hyperplaneLocalRing H)
      (A.hyperplanePrimeIdeal H).primeCompl
  exact Algebra.EssFiniteType.comp ℂ (CoordinateRing (d := d)) (A.hyperplaneLocalRing H)

instance hyperplaneLocalRing_formallySmooth (H : ι) :
    Algebra.FormallySmooth ℂ (A.hyperplaneLocalRing H) :=
  polynomialLocalization_formallySmooth ℂ (Fin d) (A.hyperplaneLocalRing H)
    (A.hyperplanePrimeIdeal H).primeCompl

/-- The actual order of any different original equation is zero in this
actual hyperplane local ring. -/
theorem hyperplaneLocalOrder_other_equation_zero (H K : ι) (hHK : H ≠ K) :
    localDVRUnitOrder (A.hyperplaneLocalRing H) (RationalFunctionField (d := d))
      (A.equationUnit K) = 0 := by
  have h := heightOnePrimeLocalUnitOrder_eq (CoordinateRing (d := d))
    (RationalFunctionField (d := d)) (A.hyperplanePrimeIdeal H)
    (A.hyperplanePrimeIdeal_isPrime H) (A.hyperplanePrimeIdeal_height H)
    (A.equationUnit K)
  change localDVRUnitOrder (A.hyperplaneLocalRing H) _ (A.equationUnit K) = _ at h
  rw [h]
  exact A.hyperplaneOrder_other_equation_zero H K hHK

/-- The equation of this actual hyperplane has nonzero actual order.
This follows from its original principal ideal, not from an assigned
residue label. -/
theorem hyperplaneLocalOrder_self_ne_zero (H : ι) :
    localDVRUnitOrder (A.hyperplaneLocalRing H) (RationalFunctionField (d := d))
      (A.equationUnit H) ≠ 0 := by
  intro hz
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (A.hyperplaneLocalRing H)
  obtain ⟨u, hu⟩ := exists_fraction_unit_uniformizer_order_factorization
    (A.hyperplaneLocalRing H) (RationalFunctionField (d := d)) π hπ (A.equationUnit H)
  have hfield : A.equationFunction H =
      algebraMap (A.hyperplaneLocalRing H) (RationalFunctionField (d := d))
        (u : A.hyperplaneLocalRing H) := by
    have h := congrArg (fun v : (RationalFunctionField (d := d))ˣ ↦
      (v : RationalFunctionField (d := d))) hu
    simpa only [hz, zpow_zero, mul_one, equationUnit_coe, Units.coe_map] using h
  have hlocal : algebraMap (CoordinateRing (d := d)) (A.hyperplaneLocalRing H)
      (A.equationPolynomial H) = (u : A.hyperplaneLocalRing H) := by
    apply IsFractionRing.injective (A.hyperplaneLocalRing H)
      (RationalFunctionField (d := d))
    exact hfield
  have hun : IsUnit (algebraMap (CoordinateRing (d := d)) (A.hyperplaneLocalRing H)
      (A.equationPolynomial H)) := hlocal.symm ▸ u.isUnit
  have hnot := (IsLocalization.AtPrime.isUnit_to_map_iff (A.hyperplaneLocalRing H)
    (A.hyperplanePrimeIdeal H) (A.equationPolynomial H)).mp hun
  exact hnot (Ideal.mem_span_singleton_self (A.equationPolynomial H))

/-- The constructed actual residue detects the coefficient of each
original hyperplane in an actual constant-coefficient logarithmic relation. -/
theorem logarithmicRelation_coefficient_zero (H : ι) (c : ι → ℂ)
    (h : ∑ K, c K • logarithmicDifferential ℂ (RationalFunctionField (d := d))
      (A.equationUnit K) = 0) : c H = 0 := by
  classical
  let S := A.hyperplaneLocalRing H
  letI : CommRing S := A.hyperplaneLocalRing_commRing H
  letI : IsDiscreteValuationRing S := A.hyperplaneLocalRing_isDiscreteValuationRing H
  letI : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S (A.hyperplanePrimeIdeal H)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  have hA : ∑ K, algebraMap ℂ S (c K) •
      logarithmicDifferential ℂ (RationalFunctionField (d := d)) (A.equationUnit K) = 0 := by
    simpa only [algebraMap_smul S] using h
  have hr := logarithmicOneForm_constant_relation_orders ℂ S (RationalFunctionField (d := d))
    Finset.univ π hπ c A.equationUnit hA
  have hsingle : ∑ K, c K *
      (localDVRUnitOrder S (RationalFunctionField (d := d)) (A.equationUnit K) : ℂ) =
      c H * (localDVRUnitOrder S (RationalFunctionField (d := d)) (A.equationUnit H) : ℂ) := by
    apply Finset.sum_eq_single H
    · intro K _ hKH
      have hz : localDVRUnitOrder S (RationalFunctionField (d := d)) (A.equationUnit K) = 0 :=
        A.hyperplaneLocalOrder_other_equation_zero H K hKH.symm
      rw [hz, Int.cast_zero, mul_zero]
    · simp
  have hn : (localDVRUnitOrder S (RationalFunctionField (d := d))
      (A.equationUnit H) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (A.hyperplaneLocalOrder_self_ne_zero H)
  exact (mul_eq_zero.mp (hsingle ▸ hr)).resolve_right hn

/-- The degree-one logarithmic realization in the paper is injective for
the actual distinct affine arrangement. There is no independence premise. -/
theorem logarithmicRealization_injective : Function.Injective A.logarithmicRealization := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro c hc
  change c = 0
  apply funext
  intro H
  exact A.logarithmicRelation_coefficient_zero H c
    (show ∑ K, c K • logarithmicDifferential ℂ (RationalFunctionField (d := d))
      (A.equationUnit K) = 0 from hc)

end ChenRanks.AffineArrangement
