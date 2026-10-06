import ChenRanks.ActualHeightOneOrderComparison

/-!
# Actual height-one orders are independent of the actual affine chart

The heights agree because both actual affine prime localizations are
one and the same actual scheme stalk. On normal Noetherian charts,
the previously proved normalized order comparison then identifies both
orders with the actual order of that stalk in the actual original
scheme function field. This comparison is needed after shrinking over
the coefficient curve; primes of different chart rings are not equated.
-/

noncomputable section

namespace ChenRanks

open AlgebraicGeometry CategoryTheory

universe u

variable {X : Scheme.{u}} [IsIntegral X]

omit [IsIntegral X] in
/-- Actual prime heights at one actual point agree across actual affine charts. -/
theorem actualAffinePointHeight_eq
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.height =
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.height := by
  have hdimU : ringKrullDim (X.presheaf.stalk x) =
      ((hU.primeIdealOf ⟨x, hxU⟩).asIdeal.height : WithBot ℕ∞) := by
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
    letI : IsLocalization.AtPrime (X.presheaf.stalk x)
        (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
    exact IsLocalization.AtPrime.ringKrullDim_eq_height
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal (X.presheaf.stalk x)
  have hdimV : ringKrullDim (X.presheaf.stalk x) =
      ((hV.primeIdealOf ⟨x, hxV⟩).asIdeal.height : WithBot ℕ∞) := by
    letI : Algebra Γ(X, V) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
    letI : IsLocalization.AtPrime (X.presheaf.stalk x)
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := hV.isLocalization_stalk ⟨x, hxV⟩
    exact IsLocalization.AtPrime.ringKrullDim_eq_height
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal (X.presheaf.stalk x)
  exact WithBot.coe_inj.mp (hdimU.symm.trans hdimV)

/-- On actual normal Noetherian charts, the same actual height-one point
has the same actual normalized order on the original scheme field. -/
theorem actualAffineHeightOneOrder_eq
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    [IsNoetherianRing Γ(X, U)] [IsIntegrallyClosed Γ(X, U)]
    [IsNoetherianRing Γ(X, V)] [IsIntegrallyClosed Γ(X, V)]
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (hheightU : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.height = 1)
    (hheightV : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.height = 1)
    (f : X.functionFieldˣ) :
    letI : Nonempty U := ⟨⟨x, hxU⟩⟩
    letI : Nonempty V := ⟨⟨x, hxV⟩⟩
    letI : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    letI : IsFractionRing Γ(X, V) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X V hV
    heightOnePrimeOrder Γ(X, U) X.functionField
        (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
        (hU.primeIdealOf ⟨x, hxU⟩).isPrime hheightU (f : X.functionField) =
      heightOnePrimeOrder Γ(X, V) X.functionField
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
        (hV.primeIdealOf ⟨x, hxV⟩).isPrime hheightV (f : X.functionField) := by
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsFractionRing Γ(X, V) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X V hV
  letI : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    normalAffineHeightOneStalk_isDiscreteValuationRing U hU ⟨x, hxU⟩ hheightU
  exact (normalAffineHeightOneStalk_order_eq_heightOnePrimeOrder
    U hU ⟨x, hxU⟩ hheightU f).symm.trans
    (normalAffineHeightOneStalk_order_eq_heightOnePrimeOrder
      V hV ⟨x, hxV⟩ hheightV f)

end ChenRanks
