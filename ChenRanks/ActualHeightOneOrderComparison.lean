import ChenRanks.NormalAffineHeightOneStalk
import ChenRanks.DVRUnitOrder

/-!
# The same actual height-one order in an affine stalk and the function field

The canonical comparison between two actual localizations commutes with
their actual maps to the same ambient ring, by the localization universal
property and the actual scalar towers.  A DVR isomorphism respecting the
actual fraction-field maps preserves the actual normalized order, proved
by transporting a genuine unit/uniformizer factorization.

For an actual normal Noetherian affine chart and its actual height-one
point, the actual scheme stalk and the actual prime localization inside
the original scheme function field are those two localizations.  Thus
the actual stalk order used in horizontal residue detection equals the
actual height-one order used in the codimension-one pole argument.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ChenRanks

universe u

section ActualLocalizationMaps

variable (R S T K : Type*) [CommRing R] [CommRing S] [CommRing T] [CommRing K]
  [Algebra R S] [Algebra R T] [Algebra R K]
  [Algebra S K] [Algebra T K]
  [IsScalarTower R S K] [IsScalarTower R T K]

/-- The canonical actual localization comparison commutes with the
actual ambient maps; this is proved from both actual base-ring towers. -/
theorem canonicalLocalizations_fractionMap_comp
    (M : Submonoid R) [IsLocalization M S] [IsLocalization M T] :
    (algebraMap T K).comp (IsLocalization.algEquiv M S T).toRingHom =
      algebraMap S K := by
  apply IsLocalization.ringHom_ext M
  apply RingHom.ext
  intro r
  change algebraMap T K (IsLocalization.algEquiv M S T (algebraMap R S r)) =
    algebraMap S K (algebraMap R S r)
  rw [(IsLocalization.algEquiv M S T).commutes,
    ← IsScalarTower.algebraMap_apply R T K,
    ← IsScalarTower.algebraMap_apply R S K]

end ActualLocalizationMaps

section ActualDVROrders

variable (S T F : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Field F] [Algebra S F] [IsFractionRing S F]
  [Algebra T F] [IsFractionRing T F]

/-- A genuine DVR equivalence preserves actual normalized order when
its actual maps to the same fraction field commute.  The statement is
proved by the already proved genuine unit/uniformizer factorization. -/
theorem localDVRUnitOrder_eq_of_ringEquiv_fractionMap
    (e : S ≃+* T) (hmap : (algebraMap T F).comp e.toRingHom = algebraMap S F)
    (f : Fˣ) : localDVRUnitOrder S F f = localDVRUnitOrder T F f := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  have hπT : Irreducible (e π) := (MulEquiv.irreducible_iff e).mpr hπ
  obtain ⟨u, hf⟩ := exists_fraction_unit_uniformizer_order_factorization S F π hπ f
  have hunit :
      Units.map (algebraMap T F).toMonoidHom (Units.map e.toRingHom.toMonoidHom u) =
        Units.map (algebraMap S F).toMonoidHom u := by
    apply Units.ext
    change algebraMap T F (e (u : S)) = algebraMap S F (u : S)
    exact congrArg (fun g : S →+* F ↦ g (u : S)) hmap
  have hπmap :
      LogResidueCore.fractionUniformizerUnit T F (e π) hπT =
        LogResidueCore.fractionUniformizerUnit S F π hπ := by
    apply Units.ext
    change algebraMap T F (e π) = algebraMap S F π
    exact congrArg (fun g : S →+* F ↦ g π) hmap
  have hfT : f = Units.map (algebraMap T F).toMonoidHom (Units.map e.toRingHom.toMonoidHom u) *
      (LogResidueCore.fractionUniformizerUnit T F (e π) hπT) ^
        localDVRUnitOrder S F f := by
    rw [hunit, hπmap]
    exact hf
  have hunitorder : localDVRUnitOrder T F
      (Units.map (algebraMap T F).toMonoidHom (Units.map e.toRingHom.toMonoidHom u)) = 0 :=
    localDVRUnitOrder_localUnit T F (Units.map e.toRingHom.toMonoidHom u)
  have horder : localDVRUnitOrder T F f = localDVRUnitOrder S F f := by
    calc
      _ = localDVRUnitOrder T F
          (Units.map (algebraMap T F).toMonoidHom (Units.map e.toRingHom.toMonoidHom u) *
            (LogResidueCore.fractionUniformizerUnit T F (e π) hπT) ^
              localDVRUnitOrder S F f) :=
        congrArg (localDVRUnitOrder T F) hfT
      _ = localDVRUnitOrder S F f := by
        rw [localDVRUnitOrder_mul T F, hunitorder,
          localDVRUnitOrder_zpow T F, localDVRUnitOrder_uniformizer T F (e π) hπT]
        simp only [zero_add, mul_one]
  exact horder.symm

end ActualDVROrders

section ActualAffinePointOrders

variable {X : Scheme.{u}} [IsIntegral X]

/-- The actual height-one order on the original scheme function field
equals the actual order of the same fraction in the same point's stalk.
Both the actual DVR structure and the ambient-map equality are proved. -/
theorem normalAffineHeightOneStalk_order_eq_heightOnePrimeOrder
    (U : X.Opens) (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(X, U)] [IsIntegrallyClosed Γ(X, U)]
    (x : U) (hheight : (hU.primeIdealOf x).asIdeal.height = 1)
    (f : X.functionFieldˣ) :
    letI : Nonempty U := ⟨x⟩
    letI : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    letI : IsDiscreteValuationRing (X.presheaf.stalk x) :=
      normalAffineHeightOneStalk_isDiscreteValuationRing U hU x hheight
    localDVRUnitOrder (X.presheaf.stalk x) X.functionField f =
      heightOnePrimeOrder Γ(X, U) X.functionField (hU.primeIdealOf x).asIdeal
        (hU.primeIdealOf x).isPrime hheight (f : X.functionField) := by
  letI : Nonempty U := ⟨x⟩
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf x
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  letI : IsScalarTower Γ(X, U) (X.presheaf.stalk x) X.functionField :=
    functionField_isScalarTower X U x
  letI : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    normalAffineHeightOneStalk_isDiscreteValuationRing U hU x hheight
  let p := (hU.primeIdealOf x).asIdeal
  letI : p.IsPrime := (hU.primeIdealOf x).isPrime
  let S := primeLocalizationInFractionField Γ(X, U) X.functionField p
    (hU.primeIdealOf x).isPrime
  letI : CommRing S := Subalgebra.toCommRing S
  letI : IsDomain S := Subalgebra.isDomain S
  letI : Algebra Γ(X, U) S := Subalgebra.algebra S
  letI : Algebra S X.functionField := Subalgebra.toAlgebra S
  letI : IsLocalization.AtPrime S p := by
    change IsLocalization p.primeCompl
      (Localization.subalgebra X.functionField p.primeCompl p.primeCompl_le_nonZeroDivisors)
    infer_instance
  letI : IsScalarTower Γ(X, U) S X.functionField :=
    IsScalarTower.subalgebra' Γ(X, U) X.functionField X.functionField S
  letI : IsDiscreteValuationRing S :=
    height_one_primeLocalization_isDiscreteValuationRing
      Γ(X, U) X.functionField p (hU.primeIdealOf x).isPrime hheight
  let e : S ≃ₐ[Γ(X, U)] X.presheaf.stalk x :=
    IsLocalization.algEquiv p.primeCompl S (X.presheaf.stalk x)
  have hmap :
      (algebraMap (X.presheaf.stalk x) X.functionField).comp e.toRingHom =
        algebraMap S X.functionField :=
    canonicalLocalizations_fractionMap_comp Γ(X, U) S (X.presheaf.stalk x)
      X.functionField p.primeCompl
  have horder := localDVRUnitOrder_eq_of_ringEquiv_fractionMap
    S (X.presheaf.stalk x) X.functionField e.toRingEquiv hmap f
  exact horder.symm

end ActualAffinePointOrders

end ChenRanks
