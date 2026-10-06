import Mathlib
import ChenRanks.LogarithmicDifferentials
import ChenRanks.DivisorOrderRegularity

/-!
# Actual uniformizer decomposition before logarithmic residues

For a DVR `A` and its actual fraction field `F`, every actual nonzero
fraction has the form `u π^n`, with `u : Aˣ` and `n : ℤ`.  Its actual
logarithmic Kähler differential is an integer multiple of `dlog π` plus
the image of an explicitly constructed form in `Ω[A/C]`.

This establishes the uniformizer decomposition used to construct
logarithmic residues.  It does not yet define a residue linear map on
actual logarithmic one-forms or two-forms.  In particular, uniqueness of
the pole coefficient as a function of a differential is not stipulated.
-/

noncomputable section

namespace ChenRanks
namespace LogResidueCore

section FractionFactorization

variable (A F : Type*) [CommRing A] [IsDomain A] [Field F]
  [Algebra A F] [IsFractionRing A F]

/-- A genuine DVR uniformizer as an actual unit of its fraction field. -/
def fractionUniformizerUnit (π : A) (hπ : Irreducible π) : Fˣ :=
  Units.mk0 (algebraMap A F π)
    ((map_ne_zero_iff _ (IsFractionRing.injective A F)).mpr hπ.ne_zero)

omit [IsDomain A] in
@[simp] theorem fractionUniformizerUnit_coe (π : A) (hπ : Irreducible π) :
    (fractionUniformizerUnit A F π hπ : F) = algebraMap A F π := rfl

/-- The factorization of an actual fraction into a genuine local unit
and an integer power of a genuine uniformizer. -/
theorem exists_fraction_unit_uniformizer_zpow [IsDiscreteValuationRing A]
    (π : A) (hπ : Irreducible π) (f : Fˣ) :
    ∃ n : ℤ, ∃ u : Aˣ,
      f = Units.map (algebraMap A F) u * (fractionUniformizerUnit A F π hπ) ^ n := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A (f : F)
  have ha : a ≠ 0 := by
    intro hz
    rw [hz, map_zero, zero_div] at hab
    exact f.ne_zero hab.symm
  have hbne : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  obtain ⟨na, ua, haeq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  obtain ⟨nb, ub, hbeq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hbne hπ
  let uaF : Fˣ := Units.map (algebraMap A F) ua
  let ubF : Fˣ := Units.map (algebraMap A F) ub
  let πF := fractionUniformizerUnit A F π hπ
  have hf : f = (uaF * πF ^ na) * (ubF * πF ^ nb)⁻¹ := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    simpa [uaF, ubF, πF, haeq, hbeq, map_mul, map_pow, div_eq_mul_inv] using hab.symm
  refine ⟨(na : ℤ) - (nb : ℤ), ua * ub⁻¹, ?_⟩
  rw [hf]
  simp only [map_mul, map_inv, zpow_sub, zpow_natCast]
  change (uaF * πF ^ na) * (ubF * πF ^ nb)⁻¹ =
    (uaF * ubF⁻¹) * (πF ^ na * (πF ^ nb)⁻¹)
  group
  exact mul_right_comm uaF (πF ^ ((na : ℤ) - (nb : ℤ))) (ubF ^ (-1 : ℤ))

end FractionFactorization

section ActualDifferentials

variable (C A F : Type*) [Field C] [CommRing A] [IsDomain A] [Field F]
  [Algebra C A] [Algebra C F] [Algebra A F] [IsScalarTower C A F]

/-- The actual regular logarithmic differential of a local-ring unit. -/
def localUnitLogDifferential (u : Aˣ) : Ω[A⁄C] :=
  ((u⁻¹ : Aˣ) : A) • KaehlerDifferential.D C A (u : A)

omit [IsDomain A] in
/-- A unit's logarithmic differential comes from the actual local-ring
Kähler module, with its actual local unit inverse as coefficient. -/
theorem localUnit_logarithmicDifferential_mem_map_range (u : Aˣ) :
    logarithmicDifferential C F (Units.map (algebraMap A F) u) ∈
      LinearMap.range (KaehlerDifferential.map C C A F) := by
  refine ⟨localUnitLogDifferential C A u, ?_⟩
  change KaehlerDifferential.map C C A F
      (((u⁻¹ : Aˣ) : A) • KaehlerDifferential.D C A (u : A)) =
    (algebraMap A F (u : A))⁻¹ • KaehlerDifferential.D C F (algebraMap A F (u : A))
  rw [map_smul, KaehlerDifferential.map_D,
    ← algebraMap_smul F ((u⁻¹ : Aˣ) : A)]
  congr 1
  simpa only [Units.val_inv_eq_inv_val] using
    (Units.coe_map_inv (algebraMap A F).toMonoidHom u).symm

/-- The actual logarithmic differential has a genuine uniformizer term
and a genuine regular term.  This is a decomposition theorem, not an
assumed or artificially defined residue map. -/
theorem exists_logarithmicDifferential_uniformizer_decomposition
    [IsFractionRing A F] [IsDiscreteValuationRing A]
    (π : A) (hπ : Irreducible π) (f : Fˣ) :
    ∃ n : ℤ, ∃ ω : Ω[A⁄C],
      logarithmicDifferential C F f =
        n • logarithmicDifferential C F (fractionUniformizerUnit A F π hπ) +
          KaehlerDifferential.map C C A F ω := by
  obtain ⟨n, u, hf⟩ := exists_fraction_unit_uniformizer_zpow A F π hπ f
  obtain ⟨ω, hω⟩ := localUnit_logarithmicDifferential_mem_map_range C A F u
  refine ⟨n, ω, ?_⟩
  rw [hf, logarithmicDifferential_mul, logarithmicDifferential_zpow, ← hω]
  exact add_comm _ _

end ActualDifferentials

end LogResidueCore
end ChenRanks
