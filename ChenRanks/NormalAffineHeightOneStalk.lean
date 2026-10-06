import ChenRanks.ScalarSchemeCharts
import ChenRanks.HorizontalSmoothStalk
import ChenRanks.DVRFormalSmoothness
import ChenRanks.DivisorOrderRegularity

/-!
# Actual normal affine height-one stalks and original scalar actions

The actual affine stalk is the localization of the actual section ring
at the actual point's prime ideal.  Its canonical localization comparison
with the section ring's localization inside the actual function field
transports the proved height-one DVR structure to the actual stalk.

The original base-field scalar action on the chart, on the actual stalk,
and on the original scheme function field is compared through genuine
section and germ maps.  No DVR structure, scalar compatibility, or local
formal smoothness is introduced as an additional hypothesis.

The actual chart ring is required to be Noetherian and integrally closed,
and the actual point prime is required to have height one.  These are the
ring properties supplied by an actual normal chart; constructing a global
normalization and identifying its full divisor domain remain separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace ChenRanks

universe u

section OriginalScalars

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The actual chart scalar map followed by the actual germ equals the
original structural scalar map at this same point. -/
theorem chartScalarMap_comp_germ
    (σ : X ⟶ Spec (.of k)) (U : X.Opens) (x : U) :
    (X.presheaf.germ U x x.2).hom.comp (chartScalarMap σ U) =
      (structureStalkScalarHom σ x).hom := by
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ σ.appLE ⊤ U (by simp) ≫
      X.presheaf.germ U x x.2).hom =
    ((Scheme.ΓSpecIso (.of k)).inv ≫ σ.appTop ≫
      X.presheaf.germ ⊤ x (by trivial)).hom
  rw [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res']
  rfl

/-- The actual chart and stalk actions of the original coefficient
field form a scalar tower, proved from the actual germ equality. -/
theorem chartStructureStalkScalarTower
    (σ : X ⟶ Spec (.of k)) (U : X.Opens) (x : U) :
    letI : Algebra k Γ(X, U) := chartScalarAlgebra σ U
    letI : Algebra k (X.presheaf.stalk x) := structureStalkAlgebra σ x
    IsScalarTower k Γ(X, U) (X.presheaf.stalk x) := by
  letI : Algebra k Γ(X, U) := chartScalarAlgebra σ U
  letI : Algebra k (X.presheaf.stalk x) := structureStalkAlgebra σ x
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change structureStalkScalarHom σ x c =
    X.presheaf.germ U x x.2 (chartScalarMap σ U c)
  exact (congrArg (fun g : k →+* X.presheaf.stalk x ↦ g c)
    (chartScalarMap_comp_germ σ U x)).symm

variable [IsIntegral X]

/-- The actual chart scalar map followed by the actual generic germ
equals the original structural map to the scheme function field. -/
theorem chartScalarMap_comp_germToFunctionField
    (σ : X ⟶ Spec (.of k)) (U : X.Opens) [Nonempty U] :
    (X.germToFunctionField U).hom.comp (chartScalarMap σ U) =
      (structureFunctionFieldScalarHom σ).hom := by
  let x : U := ⟨genericPoint X,
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U))⟩
  exact chartScalarMap_comp_germ σ U x

/-- The actual chart and original scheme function-field actions of
the original coefficient field form a scalar tower. -/
theorem chartStructureFunctionFieldScalarTower
    (σ : X ⟶ Spec (.of k)) (U : X.Opens) [Nonempty U] :
    letI : Algebra k Γ(X, U) := chartScalarAlgebra σ U
    letI : Algebra k X.functionField := structureFunctionFieldAlgebra σ
    IsScalarTower k Γ(X, U) X.functionField := by
  letI : Algebra k Γ(X, U) := chartScalarAlgebra σ U
  letI : Algebra k X.functionField := structureFunctionFieldAlgebra σ
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change structureFunctionFieldScalarHom σ c =
    X.germToFunctionField U (chartScalarMap σ U c)
  exact (congrArg (fun g : k →+* X.functionField ↦ g c)
    (chartScalarMap_comp_germToFunctionField σ U)).symm

end OriginalScalars

section ActualHeightOneStalk

private theorem actualPrimeLocalization_isDiscreteValuationRing
    (A K S : Type*) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing S] [IsDomain S] [Algebra A S]
    (p : Ideal A) [hp : p.IsPrime] (hheight : p.height = 1)
    [IsLocalization.AtPrime S p] : IsDiscreteValuationRing S := by
  letI : p.IsPrime := hp
  let B := primeLocalizationInFractionField A K p hp
  letI : IsLocalization.AtPrime B p := by
    change IsLocalization p.primeCompl
      (Localization.subalgebra K p.primeCompl p.primeCompl_le_nonZeroDivisors)
    infer_instance
  letI : IsDiscreteValuationRing B :=
    height_one_primeLocalization_isDiscreteValuationRing A K p hp hheight
  let e : B ≃ₐ[A] S := IsLocalization.algEquiv p.primeCompl B S
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e

variable {X : Scheme.{u}} [IsIntegral X]

/-- The actual height-one stalk of an actual normal Noetherian affine
chart is a DVR.  The actual DVR structure is a conclusion, rather than
an input attached to a formal divisor label. -/
theorem normalAffineHeightOneStalk_isDiscreteValuationRing
    (U : X.Opens) (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(X, U)] [IsIntegrallyClosed Γ(X, U)]
    (x : U) (hheight : (hU.primeIdealOf x).asIdeal.height = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  letI : Nonempty U := ⟨x⟩
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf x
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  exact actualPrimeLocalization_isDiscreteValuationRing
    Γ(X, U) X.functionField (X.presheaf.stalk x)
    (hU.primeIdealOf x).asIdeal hheight

/-- At an actual height-one point on such a chart, an actual finite-type
characteristic-zero structural map gives formal smoothness of the actual
stalk with its original coefficient action. -/
theorem normalAffineHeightOneStalk_formallySmooth
    {k : Type u} [Field k] [CharZero k]
    (σ : X ⟶ Spec (.of k)) [LocallyOfFiniteType σ]
    (U : X.Opens) (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(X, U)] [IsIntegrallyClosed Γ(X, U)]
    (x : U) (hheight : (hU.primeIdealOf x).asIdeal.height = 1) :
    letI : Algebra k (X.presheaf.stalk x) := structureStalkAlgebra σ x
    Algebra.FormallySmooth k (X.presheaf.stalk x) := by
  letI : Algebra k (X.presheaf.stalk x) := structureStalkAlgebra σ x
  letI : Algebra.EssFiniteType k (X.presheaf.stalk x) :=
    structureStalkAlgebra_essFiniteType σ x
  letI : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    normalAffineHeightOneStalk_isDiscreteValuationRing U hU x hheight
  exact dvr_formallySmooth_of_essFiniteType k (X.presheaf.stalk x)

end ActualHeightOneStalk

end ChenRanks
