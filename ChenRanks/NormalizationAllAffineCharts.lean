import ChenRanks.NormalizationChartRegularity
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Normality on all actual affine opens of the native normalization

Normality of native pullback charts proves normality of every actual
stalk. The actual affine localization comparisons then prove normality
on every actual nonempty affine open, including opens obtained by
shrinking over the coefficient curve. No normality of those new opens
is supplied as an additional hypothesis.
-/

noncomputable section

namespace ChenRanks

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-- Actual normal stalks imply actual normal affine section rings. -/
theorem affineSections_isIntegrallyClosed_of_stalks
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U)
    [Nonempty U] (h : ∀ x : U, IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIntegrallyClosed Γ(X, U) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  letI : p.IsMaximal := hp
  let q : PrimeSpectrum Γ(X, U) := ⟨p, hp.isPrime⟩
  let x : U := hU.isoSpec.inv q
  letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec q)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf _
  letI : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec q)) p :=
    hU.isLocalization_stalk' q x.2
  letI : IsIntegrallyClosed (X.presheaf.stalk (hU.fromSpec q)) := h x
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk (hU.fromSpec q))
      (Localization.AtPrime p)).toRingEquiv

variable {k : Type u} [Field k] [CharZero k]
  (X : Scheme.{u}) [IsIntegral X]
  (σ : X ⟶ Spec (.of k)) [LocallyOfFiniteType σ]

include σ

/-- Each actual native normalization stalk is normal, by a constructed
nonempty original affine chart containing its actual image. -/
theorem actualNormalizationStalk_isIntegrallyClosed
    (x : actualFiniteTypeNormalization X) :
    IsIntegrallyClosed ((actualFiniteTypeNormalization X).presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show actualFiniteTypeNormalizationMap X x ∈ (⊤ : X.Opens) from trivial)
    (⊤ : X.Opens).isOpen
  letI : Nonempty U := ⟨⟨actualFiniteTypeNormalizationMap X x, hx⟩⟩
  letI : IsFinite (actualFiniteTypeNormalizationMap X) :=
    actualFiniteTypeNormalizationMap_isFinite X σ
  let V : (actualFiniteTypeNormalization X).Opens :=
    actualFiniteTypeNormalizationMap X ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage (actualFiniteTypeNormalizationMap X)
  let y : V := ⟨x, hx⟩
  letI : Nonempty V := ⟨y⟩
  letI : IsIntegrallyClosed Γ(actualFiniteTypeNormalization X, V) :=
    actualNormalizationChart_isIntegrallyClosed X U hU
  letI : Algebra Γ(actualFiniteTypeNormalization X, V)
      ((actualFiniteTypeNormalization X).presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk (actualFiniteTypeNormalization X).presheaf y
  letI : IsLocalization.AtPrime
      ((actualFiniteTypeNormalization X).presheaf.stalk x)
      (hV.primeIdealOf y).asIdeal := hV.isLocalization_stalk y
  exact isIntegrallyClosed_of_isLocalization
    ((actualFiniteTypeNormalization X).presheaf.stalk x)
    (hV.primeIdealOf y).asIdeal.primeCompl
    (hV.primeIdealOf y).asIdeal.primeCompl_le_nonZeroDivisors

/-- Every actual nonempty affine open of the actual normalization is normal. -/
theorem actualNormalizationAffineSections_isIntegrallyClosed
    (V : (actualFiniteTypeNormalization X).Opens) (hV : IsAffineOpen V)
    [Nonempty V] : IsIntegrallyClosed Γ(actualFiniteTypeNormalization X, V) :=
  affineSections_isIntegrallyClosed_of_stalks (actualFiniteTypeNormalization X) V hV
    (fun x ↦ actualNormalizationStalk_isIntegrallyClosed X σ x)

end ChenRanks
