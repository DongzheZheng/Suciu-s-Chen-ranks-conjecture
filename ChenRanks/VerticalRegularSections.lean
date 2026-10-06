import ChenRanks.DivisorOrderRegularity
import ChenRanks.FibreRegularConstancy

/-!
# Actual regular units from height-one order vanishing

This is the regular-section step of the manuscript's integral valuation
kernel argument. The orders are constructed from actual prime localizations
of actual affine section rings in the actual scheme function field.
Order vanishing constructs both a section and its inverse by the proved
normal-domain theorem and actual sheaf gluing. Their rational germs prove
that the resulting section is a unit.

Normality of the charts and control of every height-one prime on these
charts remain geometric inputs. In particular, this file does not assume
that vanishing at horizontal divisors already gives that control: deleting
the actual vertical images and proving this implication is a separate step.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace ChenRanks

universe u

open scoped BigOperators

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]

/-- The actual order on an actual normal affine chart, computed in the
actual generic-point function field via the proved fraction-field comparison. -/
def affineHeightOnePrimeOrder (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hNormal : IsIntegrallyClosed Γ(X, U))
    (p : Ideal Γ(X, U)) (hp : p.IsPrime) (hheight : p.height = 1)
    (x : X.functionField) : ℤ := by
  letI : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI : IsIntegrallyClosed Γ(X, U) := hNormal
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  exact heightOnePrimeOrder Γ(X, U) X.functionField p hp hheight x

/-- Actual affine chart orders satisfy the integer-product identity. -/
theorem affineHeightOnePrimeOrder_unit_prod_zpow
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hNormal : IsIntegrallyClosed Γ(X, U))
    (p : Ideal Γ(X, U)) (hp : p.IsPrime) (hh : p.height = 1)
    {j : Type*} (s : Finset j) (f : j → X.functionFieldˣ) (n : j → ℤ) :
    affineHeightOnePrimeOrder X U hU hNormal p hp hh
        ((∏ a ∈ s, f a ^ n a : X.functionFieldˣ) : X.functionField) =
      ∑ a ∈ s, n a * affineHeightOnePrimeOrder X U hU hNormal p hp hh
        (f a : X.functionField) := by
  letI : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI : IsIntegrallyClosed Γ(X, U) := hNormal
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  exact heightOnePrimeOrder_unit_prod_zpow Γ(X, U) X.functionField p hp hh s f n

/-- Zero actual orders on every actual affine chart produce an actual
regular unit section, including an actual section for its rational inverse.
The regularity, inverse and compatibility assertions are conclusions. -/
theorem exists_regular_unit_section_of_affine_heightOnePrimeOrders_zero
    (V : X.Opens) [Nonempty V] {ι : Type u} (U : ι → X.Opens)
    [∀ i, Nonempty (U i)] (hAffine : ∀ i, IsAffineOpen (U i))
    (hUV : ∀ i, U i ≤ V) (hcover : V ≤ iSup U)
    (hNormal : ∀ i, IsIntegrallyClosed Γ(X, U i)) (x : X.functionFieldˣ)
    (horder : ∀ i, ∀ p : Ideal Γ(X, U i), ∀ hp : p.IsPrime, ∀ hh : p.height = 1,
      affineHeightOnePrimeOrder X (U i) (hAffine i) (hNormal i) p hp hh (x : X.functionField) = 0) :
    ∃ s : Γ(X, V), X.germToFunctionField V s = (x : X.functionField) ∧
      IsUnit s ∧ ∃ t : Γ(X, V),
        X.germToFunctionField V t = (x : X.functionField)⁻¹ := by
  have hlocal : ∀ i, ∀ p : Ideal Γ(X, U i), ∀ hp : p.IsPrime, p.height = 1 →
      (x : X.functionField) ∈ affinePrimeLocalizationInFunctionField X (U i) (hAffine i) p hp ∧
      (x : X.functionField)⁻¹ ∈ affinePrimeLocalizationInFunctionField X (U i) (hAffine i) p hp := by
    intro i p hp hh
    letI : IsNoetherianRing Γ(X, U i) :=
      IsLocallyNoetherian.component_noetherian ⟨U i, hAffine i⟩
    letI : IsIntegrallyClosed Γ(X, U i) := hNormal i
    letI : IsFractionRing Γ(X, U i) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X (U i) (hAffine i)
    have hz : heightOnePrimeOrder Γ(X, U i) X.functionField p hp hh (x : X.functionField) = 0 :=
      horder i p hp hh
    exact fraction_and_inverse_mem_of_heightOnePrimeValuation_eq_one
      Γ(X, U i) X.functionField p hp hh (x : X.functionField)
      ((heightOnePrimeOrder_eq_zero_iff Γ(X, U i) X.functionField p hp hh
        (x : X.functionField) x.ne_zero).mp hz)
  obtain ⟨s, hs, _⟩ := existsUnique_section_of_affine_no_codimension_one_poles
    X V U hAffine hUV hcover hNormal (x : X.functionField)
    (fun i p hp hh ↦ (hlocal i p hp hh).1)
  obtain ⟨t, ht, _⟩ := existsUnique_section_of_affine_no_codimension_one_poles
    X V U hAffine hUV hcover hNormal (x : X.functionField)⁻¹
    (fun i p hp hh ↦ (hlocal i p hp hh).2)
  exact ⟨s, hs, section_isUnit_of_inverse_generic_germs V
    (x : X.functionField) x.ne_zero s t hs ht, t, ht⟩

/-- An integer vector annihilating the actual chart order rows constructs
an actual regular unit for its actual function product. The chart orders
are not replaced by a presumed abstract divisor detector. -/
theorem exists_regular_unit_section_of_affine_order_integer_kernel
    (V : X.Opens) [Nonempty V] {ι : Type u} (U : ι → X.Opens)
    [∀ i, Nonempty (U i)] (hAffine : ∀ i, IsAffineOpen (U i))
    (hUV : ∀ i, U i ≤ V) (hcover : V ≤ iSup U)
    (hNormal : ∀ i, IsIntegrallyClosed Γ(X, U i))
    {j : Type*} (s : Finset j) (f : j → X.functionFieldˣ) (n : j → ℤ)
    (hkernel : ∀ i, ∀ p : Ideal Γ(X, U i), ∀ hp : p.IsPrime, ∀ hh : p.height = 1,
      (∑ a ∈ s, n a * affineHeightOnePrimeOrder X (U i) (hAffine i)
        (hNormal i) p hp hh (f a : X.functionField)) = 0) :
    ∃ t : Γ(X, V),
      X.germToFunctionField V t =
        ((∏ a ∈ s, f a ^ n a : X.functionFieldˣ) : X.functionField) ∧ IsUnit t := by
  obtain ⟨t, ht, hunit, _⟩ :=
    exists_regular_unit_section_of_affine_heightOnePrimeOrders_zero
      X V U hAffine hUV hcover hNormal (∏ a ∈ s, f a ^ n a)
      (fun i p hp hh ↦ (affineHeightOnePrimeOrder_unit_prod_zpow
        X (U i) (hAffine i) (hNormal i) p hp hh s f n).trans (hkernel i p hp hh))
  exact ⟨t, ht, hunit⟩

end ChenRanks
