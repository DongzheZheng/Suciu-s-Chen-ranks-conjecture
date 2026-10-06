import ChenRanks.HorizontalSmoothStalk
import ChenRanks.DVRFormalSmoothness
import ChenRanks.CurveBasisRestrictions
import ChenRanks.OrderedLogarithmicResidue

/-!
# Actual finite-type horizontal residue detection

At an actual horizontal point of an integral finite-type model, the
actual DVR stalk is formally smooth over the characteristic-zero base
field.  This is derived from its actual essential finite type and the
actual DVR uniformizer construction.  A globally smooth model is not
an input.

The original finite basis retains actual curve-field pullback witnesses.
Its regular local lifts come from the actual morphism on stalks, and
its residue-field restrictions are proved independent.  The constructed
logarithmic two-form residue then detects the actual order-coefficient
rows of a genuine mixed relation at this same point.

The theorem applies to every point satisfying the stated horizontal
and DVR conditions, without restricting to original arrangement
divisors.  Building the actual normal model, identifying all its
codimension-one stalks, and connecting the original closed-form field
to the actual curve projection remain separate obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

namespace ChenRanks

universe u

variable {k : Type u} [Field k] [CharZero k]
  {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- A genuine mixed relation between the original finite basis and
actual logarithmic generators forces every coefficient row to lie in
the kernel of the actual horizontal valuation row.  The actual local
lifts and restriction independence are constructed in the proof. -/
theorem horizontal_finiteType_pullback_basis_mixed_relation_has_zero_order_coefficients
    (σX : X ⟶ Spec (.of k)) [LocallyOfFiniteType σX]
    (σY : Y ⟶ Spec (.of k)) (f : X ⟶ Y)
    (hstructure : f ≫ σY = σX) (x : X) (hx : f x = genericPoint Y)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] {ι : Type*} [Fintype ι] :
    letI : IsDominant f := horizontalPoint_isDominant f x hx
    letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
    letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
    letI : IsScalarTower k Y.functionField X.functionField :=
      functionFieldScalarTower_of_structure_square σX σY f hstructure
    ∀ (P : Submodule k Ω[X.functionField⁄k]) [FiniteDimensional k P],
      (∀ ω : P, ∃ η : Ω[Y.functionField⁄k],
        KaehlerDifferential.map k k Y.functionField X.functionField η =
          (ω : Ω[X.functionField⁄k])) →
      ∀ (u : ι → X.functionFieldˣ)
        (β : Fin (Module.finrank k P) → ι → k),
      (∑ i, ∑ j, algebraMap k X.functionField (β i j) •
        exteriorWedge (k := X.functionField)
          (logarithmicDifferential k X.functionField (u j))
          (Module.finBasis k P i : Ω[X.functionField⁄k])) = 0 →
      ∀ i, ∑ j, β i j *
        (localDVRUnitOrder (X.presheaf.stalk x) X.functionField (u j) : k) = 0 := by
  classical
  letI : IsDominant f := horizontalPoint_isDominant f x hx
  letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
  letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
  letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
  letI : IsScalarTower k Y.functionField X.functionField :=
    functionFieldScalarTower_of_structure_square σX σY f hstructure
  intro P _ hpull u β hrelation
  let A := X.presheaf.stalk x
  let κ := IsLocalRing.ResidueField A
  letI : Algebra k A := structureStalkAlgebra σX x
  letI : Algebra Y.functionField A := horizontalFunctionFieldStalkAlgebra f x hx
  letI : Algebra Y.functionField κ := horizontalFunctionFieldResidueAlgebra f x hx
  letI : IsScalarTower k Y.functionField A :=
    horizontalFunctionFieldStalkScalarTower σX σY f hstructure x hx
  letI : IsScalarTower k Y.functionField κ :=
    horizontalFunctionFieldResidueScalarTower σX σY f hstructure x hx
  letI : IsScalarTower k A X.functionField :=
    structureStalkFunctionFieldScalarTower σX x
  letI : IsScalarTower Y.functionField A X.functionField :=
    horizontalLocalFunctionFieldScalarTower f x hx
  letI : IsScalarTower Y.functionField A κ :=
    horizontalFunctionFieldResidueLocalScalarTower f x hx
  letI : Algebra.EssFiniteType k A := structureStalkAlgebra_essFiniteType σX x
  letI : Algebra.FormallySmooth k A := dvr_formallySmooth_of_essFiniteType k A
  letI : Algebra.EssFiniteType k κ := structureStalkResidueField_essFiniteType σX x
  letI : Module X.functionField (⋀[X.functionField]^2 Ω[X.functionField⁄k]) :=
    exteriorTwoFormNativeFieldModule k X.functionField
  letI : SMul X.functionField (⋀[X.functionField]^2 Ω[X.functionField⁄k]) :=
    (exteriorTwoFormNativeFieldModule k X.functionField).toSMul
  letI : Module A (⋀[X.functionField]^2 Ω[X.functionField⁄k]) :=
    exteriorTwoFormModuleRestriction k A X.functionField
  letI : SMul A (⋀[X.functionField]^2 Ω[X.functionField⁄k]) :=
    (exteriorTwoFormModuleRestriction k A X.functionField).toSMul
  obtain ⟨η, hη, _, hrestriction⟩ :=
    pullback_basis_exists_with_independent_restrictions k Y.functionField X.functionField P hpull
  have hindependent : LinearIndependent k
      (fun i ↦ KaehlerDifferential.map k k Y.functionField κ (η i)) :=
    hrestriction κ
  let ζ : Fin (Module.finrank k P) → Ω[A⁄k] :=
    fun i ↦ KaehlerDifferential.map k k Y.functionField A (η i)
  have hζambient (i : Fin (Module.finrank k P)) :
      KaehlerDifferential.map k k A X.functionField (ζ i) =
        (Module.finBasis k P i : Ω[X.functionField⁄k]) := by
    exact (actualDifferentialMap_comp k Y.functionField A X.functionField (η i)).trans (hη i)
  have hζresidue (i : Fin (Module.finrank k P)) :
      KaehlerDifferential.map k k A κ (ζ i) =
        KaehlerDifferential.map k k Y.functionField κ (η i) :=
    actualDifferentialMap_comp k Y.functionField A κ (η i)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hlocal :
      (∑ p : Fin (Module.finrank k P) × ι,
        algebraMap k A (β p.1 p.2) • exteriorWedge (k := X.functionField)
          (logarithmicDifferential k X.functionField (u p.2))
          (KaehlerDifferential.map k k A X.functionField (ζ p.1))) = 0 := by
    change (∑ p : Fin (Module.finrank k P) × ι,
      algebraMap A X.functionField (algebraMap k A (β p.1 p.2)) •
        exteriorWedge (k := X.functionField)
          (logarithmicDifferential k X.functionField (u p.2))
          (KaehlerDifferential.map k k A X.functionField (ζ p.1))) = 0
    simp only [← IsScalarTower.algebraMap_apply k A X.functionField, hζambient]
    simpa only [Fintype.sum_prod_type] using hrelation
  have hresidue := logarithmicMixed_constant_relation_restricts_to_order_relation
    k A X.functionField π hπ (Finset.univ : Finset (Fin (Module.finrank k P) × ι))
    (fun p ↦ β p.1 p.2) (fun p ↦ u p.2) (fun p ↦ ζ p.1) hlocal
  have hgrouped :
      (∑ i, (∑ j, β i j * (localDVRUnitOrder A X.functionField (u j) : k)) •
        KaehlerDifferential.map k k A κ (ζ i)) = 0 := by
    simpa only [Fintype.sum_prod_type, ← Finset.sum_smul] using hresidue
  have hrows :
      (∑ i, (∑ j, β i j * (localDVRUnitOrder A X.functionField (u j) : k)) •
        KaehlerDifferential.map k k Y.functionField κ (η i)) = 0 := by
    calc
      _ = ∑ i, (∑ j, β i j * (localDVRUnitOrder A X.functionField (u j) : k)) •
          KaehlerDifferential.map k k A κ (ζ i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg
          (fun w : Ω[κ⁄k] ↦
            (∑ j, β i j * (localDVRUnitOrder A X.functionField (u j) : k)) • w)
          (hζresidue i).symm
      _ = 0 := hgrouped
  exact (Fintype.linearIndependent_iff.mp hindependent) _ hrows

end ChenRanks
