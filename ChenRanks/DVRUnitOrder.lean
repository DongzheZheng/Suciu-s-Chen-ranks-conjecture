import Mathlib
import ChenRanks.LogarithmicResidues

/-!
# The actual normalized order of a DVR fraction

The integer is constructed from the genuine maximal-ideal valuation on
the actual fraction field.  The actual valuation of a local unit is one,
and the actual valuation of an actual uniformizer is exp(-1).  Therefore
the integer exponent in the genuine unit/uniformizer factorization is
proved to equal the normalized order, rather than identified by naming.

For a genuine height-one localization inside the actual ambient fraction
field, the order is identified with the actual heightOnePrimeOrder from
DivisorOrderRegularity.  Its geometric identification with an actual
scheme divisor remains a separate construction.
-/

noncomputable section

namespace ChenRanks

section ActualDVRValuation

variable (A F : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field F] [Algebra A F] [IsFractionRing A F]

/-- The actual maximal ideal as a genuine height-one prime of the DVR. -/
def localDVRHeightOnePrime : IsDedekindDomain.HeightOneSpectrum A :=
  ⟨IsLocalRing.maximalIdeal A, inferInstance, IsDiscreteValuationRing.not_a_field A⟩

/-- The genuine maximal-ideal valuation on the actual fraction field. -/
def localDVRFractionValuation : Valuation F (WithZero (Multiplicative ℤ)) :=
  (localDVRHeightOnePrime A).valuation F

/-- The normalized order of an actual nonzero fraction. -/
def localDVRUnitOrder (f : Fˣ) : ℤ :=
  -WithZero.log (localDVRFractionValuation A F (f : F))

theorem localDVRFractionValuation_localUnit (u : Aˣ) :
    localDVRFractionValuation A F (algebraMap A F (u : A)) = 1 := by
  rw [localDVRFractionValuation, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  apply IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr
  change (u : A) ∉ IsLocalRing.maximalIdeal A
  exact IsLocalRing.notMem_maximalIdeal.mpr u.isUnit

theorem localDVRFractionValuation_uniformizer (π : A) (hπ : Irreducible π) :
    localDVRFractionValuation A F (algebraMap A F π) = WithZero.exp (-1 : ℤ) := by
  rw [localDVRFractionValuation, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact (localDVRHeightOnePrime A).intValuation_singleton hπ.ne_zero hπ.maximalIdeal_eq

@[simp]
theorem localDVRUnitOrder_localUnit (u : Aˣ) :
    localDVRUnitOrder A F (Units.map (algebraMap A F) u) = 0 := by
  change -WithZero.log (localDVRFractionValuation A F (algebraMap A F (u : A))) = 0
  rw [localDVRFractionValuation_localUnit, WithZero.log_one, neg_zero]

@[simp]
theorem localDVRUnitOrder_uniformizer (π : A) (hπ : Irreducible π) :
    localDVRUnitOrder A F (LogResidueCore.fractionUniformizerUnit A F π hπ) = 1 := by
  change -WithZero.log (localDVRFractionValuation A F (algebraMap A F π)) = 1
  rw [localDVRFractionValuation_uniformizer A F π hπ, WithZero.log_exp]
  norm_num

theorem localDVRUnitOrder_mul (f g : Fˣ) :
    localDVRUnitOrder A F (f * g) = localDVRUnitOrder A F f + localDVRUnitOrder A F g := by
  have hf : localDVRFractionValuation A F (f : F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr f.ne_zero
  have hg : localDVRFractionValuation A F (g : F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr g.ne_zero
  change -WithZero.log (localDVRFractionValuation A F ((f : F) * (g : F))) = _
  rw [map_mul, WithZero.log_mul hf hg, neg_add]
  rfl

theorem localDVRUnitOrder_zpow (f : Fˣ) (n : ℤ) :
    localDVRUnitOrder A F (f ^ n) = n * localDVRUnitOrder A F f := by
  simp only [localDVRUnitOrder, Units.val_zpow_eq_zpow_val, map_zpow₀,
    WithZero.log_zpow, zsmul_eq_mul, mul_neg, Int.cast_id]

/-- The actual factorization exponent is exactly the actual normalized
order, proved using the actual valuation of its unit and uniformizer. -/
theorem exists_fraction_unit_uniformizer_order_factorization (π : A) (hπ : Irreducible π)
    (f : Fˣ) :
    ∃ u : Aˣ, f = Units.map (algebraMap A F) u *
      (LogResidueCore.fractionUniformizerUnit A F π hπ) ^ localDVRUnitOrder A F f := by
  obtain ⟨n, u, hf⟩ := LogResidueCore.exists_fraction_unit_uniformizer_zpow A F π hπ f
  have hn : localDVRUnitOrder A F f = n := by
    rw [hf, localDVRUnitOrder_mul, localDVRUnitOrder_localUnit, localDVRUnitOrder_zpow,
      localDVRUnitOrder_uniformizer]
    simp only [mul_one, zero_add]
  refine ⟨u, ?_⟩
  rw [hn]
  exact hf

end ActualDVRValuation

section ActualOrderedLogarithmicDifferentials

variable (C A F : Type*) [Field C] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field F] [Algebra C A] [Algebra C F] [Algebra A F] [IsScalarTower C A F]
  [IsFractionRing A F]

/-- The coefficient in the actual logarithmic differential decomposition
is the actual normalized order.  It is not an independent residue label. -/
theorem exists_logarithmicDifferential_uniformizer_order_decomposition
    (π : A) (hπ : Irreducible π) (f : Fˣ) :
    ∃ ω : Ω[A⁄C], logarithmicDifferential C F f =
      localDVRUnitOrder A F f • logarithmicDifferential C F
        (LogResidueCore.fractionUniformizerUnit A F π hπ) +
          KaehlerDifferential.map C C A F ω := by
  obtain ⟨u, hf⟩ := exists_fraction_unit_uniformizer_order_factorization A F π hπ f
  obtain ⟨ω, hω⟩ := LogResidueCore.localUnit_logarithmicDifferential_mem_map_range C A F u
  refine ⟨ω, ?_⟩
  calc
    logarithmicDifferential C F f = logarithmicDifferential C F
        (Units.map (algebraMap A F) u *
          (LogResidueCore.fractionUniformizerUnit A F π hπ) ^ localDVRUnitOrder A F f) :=
      congrArg (logarithmicDifferential C F) hf
    _ = logarithmicDifferential C F (Units.map (algebraMap A F) u) +
        localDVRUnitOrder A F f • logarithmicDifferential C F
          (LogResidueCore.fractionUniformizerUnit A F π hπ) := by
      rw [logarithmicDifferential_mul, logarithmicDifferential_zpow]
    _ = _ := by rw [← hω]; exact add_comm _ _

end ActualOrderedLogarithmicDifferentials

section ActualHeightOneLocalization

variable (A F : Type*) [CommRing A] [IsDomain A] [Field F]
  [Algebra A F] [IsFractionRing A F] [IsNoetherianRing A] [IsIntegrallyClosed A]

/-- The normalized local DVR order on the actual height-one localization
constructed inside the actual ambient fraction field. -/
def heightOnePrimeLocalUnitOrder (p : Ideal A) (hp : p.IsPrime) (hheight : p.height = 1)
    (f : Fˣ) : ℤ := by
  let S := primeLocalizationInFractionField A F p hp
  letI : IsDiscreteValuationRing S :=
    height_one_primeLocalization_isDiscreteValuationRing A F p hp hheight
  exact localDVRUnitOrder S F f

/-- The new local factorization order is the existing actual integer
height-one order, by the identical genuine maximal-ideal valuation. -/
theorem heightOnePrimeLocalUnitOrder_eq (p : Ideal A) (hp : p.IsPrime)
    (hheight : p.height = 1) (f : Fˣ) :
    heightOnePrimeLocalUnitOrder A F p hp hheight f =
      heightOnePrimeOrder A F p hp hheight (f : F) := rfl

end ActualHeightOneLocalization

end ChenRanks
