import ChenRanks.StructureFunctionFieldTower
import ChenRanks.CurveRestriction

/-!
# Actual local lifts at a horizontal point

If the actual image of x under f is the generic point of the integral
base, its actual stalk map is an actual map from the base function field
to the local ring at x.  The scalar compatibility and the comparison
with the actual ambient function-field map are proved by the actual
stalk and Spec identities.

Actual curve differentials are then mapped to actual local-ring
differentials.  Their ambient pullbacks and residue-field restrictions
are the actual Kähler maps of the constructed algebra structures.  No
vanishing-order detector or unspecified regular-lift assumption is used.
This module does not construct a resolved model or identify arbitrary
points with actual prime divisors.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

section ActualStalkScalars

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Actual scalar values in the actual local ring, obtained from the
structure morphism and the actual germ at the given point. -/
def structureStalkScalarHom (σ : X ⟶ Spec (.of k)) (x : X) :
    (.of k) ⟶ X.presheaf.stalk x :=
  (Scheme.ΓSpecIso (.of k)).inv ≫ σ.appTop ≫ X.presheaf.germ ⊤ x (by trivial)

/-- The actual local scalar map is geometrically the actual structural
morphism restricted to the actual stalk spectrum. -/
@[reassoc]
theorem structureStalkScalarHom_spec (σ : X ⟶ Spec (.of k)) (x : X) :
    Spec.map (structureStalkScalarHom σ x) = X.fromSpecStalk x ≫ σ := by
  rw [structureStalkScalarHom, Spec.map_comp, Spec.map_comp]
  change Spec.map (X.presheaf.germ ⊤ x (by trivial)) ≫
    Spec.map σ.appTop ≫ Spec.map (Scheme.ΓSpecIso (.of k)).inv = _
  rw [← Scheme.fromSpecStalk_toSpecΓ]
  simp only [Category.assoc]
  rw [← Scheme.toSpecΓ_naturality_assoc σ]
  simp

/-- The actual base-field algebra structure on the actual local ring. -/
abbrev structureStalkAlgebra (σ : X ⟶ Spec (.of k)) (x : X) :
    Algebra k (X.presheaf.stalk x) :=
  (structureStalkScalarHom σ x).hom.toAlgebra

end ActualStalkScalars

section ActualHorizontalRingMaps

variable {X Y : Scheme.{u}} [IsIntegral Y]

/-- The actual local-ring map at an actual horizontal point. -/
def horizontalFunctionFieldStalkMap (f : X ⟶ Y) (x : X)
    (h : f x = genericPoint Y) : Y.functionField ⟶ X.presheaf.stalk x :=
  (Y.presheaf.stalkCongr (Inseparable.of_eq h)).inv ≫ f.stalkMap x

@[reassoc]
theorem horizontalFunctionFieldStalkMap_spec_comp (f : X ⟶ Y) (x : X)
    (h : f x = genericPoint Y) :
    Spec.map (horizontalFunctionFieldStalkMap f x h) ≫
      Y.fromSpecStalk (genericPoint Y) = X.fromSpecStalk x ≫ f := by
  rw [horizontalFunctionFieldStalkMap, Spec.map_comp, Category.assoc,
    TopCat.Presheaf.stalkCongr_inv,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- The actual existence of a point over the generic point implies
actual dominance, rather than adding dominance as a detector premise. -/
theorem horizontalPoint_isDominant (f : X ⟶ Y) (x : X)
    (h : f x = genericPoint Y) : IsDominant f := by
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff, ← genericPoint_closure Y]
  apply closure_mono
  exact Set.singleton_subset_iff.mpr ⟨x, h⟩

theorem horizontalFunctionFieldStalkMap_injective (f : X ⟶ Y) (x : X)
    (h : f x = genericPoint Y) :
    Function.Injective (horizontalFunctionFieldStalkMap f x h) :=
  (horizontalFunctionFieldStalkMap f x h).hom.injective

/-- The actual curve-field algebra structure on the actual local ring. -/
abbrev horizontalFunctionFieldStalkAlgebra (f : X ⟶ Y) (x : X)
    (h : f x = genericPoint Y) : Algebra Y.functionField (X.presheaf.stalk x) :=
  (horizontalFunctionFieldStalkMap f x h).hom.toAlgebra

/-- The actual induced map to the actual residue field. -/
def horizontalFunctionFieldResidueMap (f : X ⟶ Y) (x : X)
    (h : f x = genericPoint Y) :
    Y.functionField →+* IsLocalRing.ResidueField (X.presheaf.stalk x) :=
  (algebraMap (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x))).comp
    (horizontalFunctionFieldStalkMap f x h).hom

theorem horizontalFunctionFieldResidueMap_injective (f : X ⟶ Y) (x : X)
    (h : f x = genericPoint Y) :
    Function.Injective (horizontalFunctionFieldResidueMap f x h) :=
  (horizontalFunctionFieldResidueMap f x h).injective

abbrev horizontalFunctionFieldResidueAlgebra (f : X ⟶ Y) (x : X)
    (h : f x = genericPoint Y) :
    Algebra Y.functionField (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
  (horizontalFunctionFieldResidueMap f x h).toAlgebra

theorem horizontalFunctionFieldResidueLocalScalarTower (f : X ⟶ Y) (x : X)
    (h : f x = genericPoint Y) :
    letI : Algebra Y.functionField (X.presheaf.stalk x) :=
      horizontalFunctionFieldStalkAlgebra f x h
    letI : Algebra Y.functionField (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
      horizontalFunctionFieldResidueAlgebra f x h
    IsScalarTower Y.functionField (X.presheaf.stalk x)
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
  letI : Algebra Y.functionField (X.presheaf.stalk x) :=
    horizontalFunctionFieldStalkAlgebra f x h
  letI : Algebra Y.functionField (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    horizontalFunctionFieldResidueAlgebra f x h
  apply IsScalarTower.of_algebraMap_eq
  intro a
  rfl

variable {k : Type u} [Field k]

/-- The actual local curve-field map respects the original actual scalar
maps, as a consequence of the actual commutative structure square. -/
theorem horizontalFunctionFieldStalkMap_scalar_compatibility
    (σX : X ⟶ Spec (.of k)) (σY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) (hstructure : f ≫ σY = σX)
    (x : X) (h : f x = genericPoint Y) :
    structureFunctionFieldScalarHom σY ≫ horizontalFunctionFieldStalkMap f x h =
      structureStalkScalarHom σX x := by
  apply Spec.map_injective
  calc
    Spec.map (structureFunctionFieldScalarHom σY ≫ horizontalFunctionFieldStalkMap f x h) =
        Spec.map (horizontalFunctionFieldStalkMap f x h) ≫
          (Y.fromSpecStalk (genericPoint Y) ≫ σY) := by
      rw [Spec.map_comp, structureFunctionFieldScalarHom_spec]
    _ = (X.fromSpecStalk x ≫ f) ≫ σY := by
      rw [← Category.assoc, horizontalFunctionFieldStalkMap_spec_comp]
    _ = X.fromSpecStalk x ≫ σX := by rw [Category.assoc, hstructure]
    _ = Spec.map (structureStalkScalarHom σX x) := by rw [structureStalkScalarHom_spec]

theorem horizontalFunctionFieldStalkScalarTower
    (σX : X ⟶ Spec (.of k)) (σY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) (hstructure : f ≫ σY = σX)
    (x : X) (h : f x = genericPoint Y) :
    letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
    letI : Algebra k (X.presheaf.stalk x) := structureStalkAlgebra σX x
    letI : Algebra Y.functionField (X.presheaf.stalk x) :=
      horizontalFunctionFieldStalkAlgebra f x h
    IsScalarTower k Y.functionField (X.presheaf.stalk x) := by
  letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
  letI : Algebra k (X.presheaf.stalk x) := structureStalkAlgebra σX x
  letI : Algebra Y.functionField (X.presheaf.stalk x) :=
    horizontalFunctionFieldStalkAlgebra f x h
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change structureStalkScalarHom σX x a =
    horizontalFunctionFieldStalkMap f x h (structureFunctionFieldScalarHom σY a)
  exact (congrArg (fun φ : (.of k) ⟶ X.presheaf.stalk x => φ a)
    (horizontalFunctionFieldStalkMap_scalar_compatibility σX σY f hstructure x h)).symm

/-- The actual residue-field action of the curve field respects the
actual original constants, by the proved local scalar compatibility. -/
theorem horizontalFunctionFieldResidueScalarTower
    (σX : X ⟶ Spec (.of k)) (σY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) (hstructure : f ≫ σY = σX)
    (x : X) (h : f x = genericPoint Y) :
    letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
    letI : Algebra k (X.presheaf.stalk x) := structureStalkAlgebra σX x
    letI : Algebra Y.functionField (X.presheaf.stalk x) :=
      horizontalFunctionFieldStalkAlgebra f x h
    letI : Algebra Y.functionField (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
      horizontalFunctionFieldResidueAlgebra f x h
    IsScalarTower k Y.functionField (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
  letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
  letI : Algebra k (X.presheaf.stalk x) := structureStalkAlgebra σX x
  letI : Algebra Y.functionField (X.presheaf.stalk x) :=
    horizontalFunctionFieldStalkAlgebra f x h
  letI : Algebra Y.functionField (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    horizontalFunctionFieldResidueAlgebra f x h
  letI : IsScalarTower k Y.functionField (X.presheaf.stalk x) :=
    horizontalFunctionFieldStalkScalarTower σX σY f hstructure x h
  apply IsScalarTower.of_algebraMap_eq
  intro a
  rw [IsScalarTower.algebraMap_apply k (X.presheaf.stalk x)
    (IsLocalRing.ResidueField (X.presheaf.stalk x))]
  change algebraMap (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (algebraMap k (X.presheaf.stalk x) a) =
    algebraMap (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (algebraMap Y.functionField (X.presheaf.stalk x) (algebraMap k Y.functionField a))
  exact congrArg
    (algebraMap (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x)))
    (IsScalarTower.algebraMap_apply k Y.functionField (X.presheaf.stalk x) a)

end ActualHorizontalRingMaps

section ActualAmbientComparison

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The actual local-to-function-field specialization map. -/
abbrev actualStalkToFunctionFieldMap (x : X) : X.presheaf.stalk x ⟶ X.functionField :=
  X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)

@[reassoc]
theorem horizontalFunctionFieldStalkMap_comp_ambient (f : X ⟶ Y) [IsDominant f]
    (x : X) (h : f x = genericPoint Y) :
    horizontalFunctionFieldStalkMap f x h ≫ actualStalkToFunctionFieldMap x =
      dominantFunctionFieldMap f := by
  apply Spec.map_injective
  apply (cancel_mono (Y.fromSpecStalk (genericPoint Y))).mp
  calc
    Spec.map (horizontalFunctionFieldStalkMap f x h ≫ actualStalkToFunctionFieldMap x) ≫
        Y.fromSpecStalk (genericPoint Y) =
        Spec.map (actualStalkToFunctionFieldMap x) ≫
          (Spec.map (horizontalFunctionFieldStalkMap f x h) ≫
            Y.fromSpecStalk (genericPoint Y)) := by rw [Spec.map_comp, Category.assoc]
    _ = Spec.map (actualStalkToFunctionFieldMap x) ≫ (X.fromSpecStalk x ≫ f) := by
      rw [horizontalFunctionFieldStalkMap_spec_comp]
    _ = X.fromSpecStalk (genericPoint X) ≫ f := by
      rw [← Category.assoc, actualStalkToFunctionFieldMap,
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    _ = Spec.map (dominantFunctionFieldMap f) ≫ Y.fromSpecStalk (genericPoint Y) := by
      rw [dominantFunctionFieldMap_spec_comp]

variable {k : Type u} [Field k]

theorem structureStalkScalarHom_comp_ambient (σX : X ⟶ Spec (.of k)) (x : X) :
    structureStalkScalarHom σX x ≫ actualStalkToFunctionFieldMap x =
      structureFunctionFieldScalarHom σX := by
  apply Spec.map_injective
  rw [Spec.map_comp, structureStalkScalarHom_spec, ← Category.assoc,
    actualStalkToFunctionFieldMap, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    structureFunctionFieldScalarHom_spec]

theorem structureStalkFunctionFieldScalarTower (σX : X ⟶ Spec (.of k)) (x : X) :
    letI : Algebra k (X.presheaf.stalk x) := structureStalkAlgebra σX x
    letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
    IsScalarTower k (X.presheaf.stalk x) X.functionField := by
  letI : Algebra k (X.presheaf.stalk x) := structureStalkAlgebra σX x
  letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change structureFunctionFieldScalarHom σX a =
    actualStalkToFunctionFieldMap x (structureStalkScalarHom σX x a)
  exact (congrArg (fun φ : (.of k) ⟶ X.functionField => φ a)
    (structureStalkScalarHom_comp_ambient σX x)).symm

theorem horizontalLocalFunctionFieldScalarTower (f : X ⟶ Y) [IsDominant f]
    (x : X) (h : f x = genericPoint Y) :
    letI : Algebra Y.functionField (X.presheaf.stalk x) :=
      horizontalFunctionFieldStalkAlgebra f x h
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
    IsScalarTower Y.functionField (X.presheaf.stalk x) X.functionField := by
  letI : Algebra Y.functionField (X.presheaf.stalk x) :=
    horizontalFunctionFieldStalkAlgebra f x h
  letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change dominantFunctionFieldMap f a =
    actualStalkToFunctionFieldMap x (horizontalFunctionFieldStalkMap f x h a)
  exact (congrArg (fun φ : Y.functionField ⟶ X.functionField => φ a)
    (horizontalFunctionFieldStalkMap_comp_ambient f x h)).symm

end ActualAmbientComparison

section ActualDifferentialComposition

variable (k L A T : Type*) [CommRing k] [CommRing L] [CommRing A] [CommRing T]
  [Algebra k L] [Algebra k A] [Algebra k T]
  [Algebra L A] [Algebra L T] [Algebra A T]
  [IsScalarTower k L A] [IsScalarTower k L T] [IsScalarTower k A T] [IsScalarTower L A T]

/-- Functoriality of the actual Kähler maps in an actual algebra tower. -/
theorem actualDifferentialMap_comp (η : Ω[L⁄k]) :
    KaehlerDifferential.map k k A T (KaehlerDifferential.map k k L A η) =
      KaehlerDifferential.map k k L T η := by
  have he : ((KaehlerDifferential.map k k A T).restrictScalars L).comp
      (KaehlerDifferential.map k k L A) = KaehlerDifferential.map k k L T := by
    apply Derivation.liftKaehlerDifferential_unique
    ext a
    change KaehlerDifferential.map k k A T
      (KaehlerDifferential.map k k L A (KaehlerDifferential.D k L a)) =
      KaehlerDifferential.map k k L T (KaehlerDifferential.D k L a)
    simp only [KaehlerDifferential.map_D, IsScalarTower.algebraMap_apply L A T]
  exact LinearMap.congr_fun he η

end ActualDifferentialComposition

section ActualHorizontalCurveForms

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The actual base curve form has an actual local lift at the actual
horizontal point. Its ambient pullback is computed by the actual
morphism-induced function-field map. -/
theorem horizontalCurveDifferential_has_actual_local_lift
    (σX : X ⟶ Spec (.of k)) (σY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) (hstructure : f ≫ σY = σX) (x : X)
    (h : f x = genericPoint Y) :
    letI : IsDominant f := horizontalPoint_isDominant f x h
    letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
    letI : Algebra k (X.presheaf.stalk x) := structureStalkAlgebra σX x
    letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
    letI : Algebra Y.functionField (X.presheaf.stalk x) :=
      horizontalFunctionFieldStalkAlgebra f x h
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
    letI : IsScalarTower k Y.functionField (X.presheaf.stalk x) :=
      horizontalFunctionFieldStalkScalarTower σX σY f hstructure x h
    letI : IsScalarTower k Y.functionField X.functionField :=
      functionFieldScalarTower_of_structure_square σX σY f hstructure
    letI : IsScalarTower k (X.presheaf.stalk x) X.functionField :=
      structureStalkFunctionFieldScalarTower σX x
    ∀ η : Ω[Y.functionField⁄k], ∃ ω : Ω[X.presheaf.stalk x⁄k],
      KaehlerDifferential.map k k (X.presheaf.stalk x) X.functionField ω =
        KaehlerDifferential.map k k Y.functionField X.functionField η := by
  letI : IsDominant f := horizontalPoint_isDominant f x h
  letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
  letI : Algebra k (X.presheaf.stalk x) := structureStalkAlgebra σX x
  letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
  letI : Algebra Y.functionField (X.presheaf.stalk x) :=
    horizontalFunctionFieldStalkAlgebra f x h
  letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
  letI : IsScalarTower k Y.functionField (X.presheaf.stalk x) :=
    horizontalFunctionFieldStalkScalarTower σX σY f hstructure x h
  letI : IsScalarTower k Y.functionField X.functionField :=
    functionFieldScalarTower_of_structure_square σX σY f hstructure
  letI : IsScalarTower k (X.presheaf.stalk x) X.functionField :=
    structureStalkFunctionFieldScalarTower σX x
  letI : IsScalarTower Y.functionField (X.presheaf.stalk x) X.functionField :=
    horizontalLocalFunctionFieldScalarTower f x h
  intro η
  refine ⟨KaehlerDifferential.map k k Y.functionField (X.presheaf.stalk x) η, ?_⟩
  exact actualDifferentialMap_comp k Y.functionField (X.presheaf.stalk x) X.functionField η

omit [IsIntegral X] in
/-- The actual local lift restricts to precisely the actual curve-field
pullback in the actual residue-field differential module. -/
theorem horizontalCurveDifferential_actual_residue_restriction
    (σX : X ⟶ Spec (.of k)) (σY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) (hstructure : f ≫ σY = σX) (x : X)
    (h : f x = genericPoint Y) :
    letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
    letI : Algebra k (X.presheaf.stalk x) := structureStalkAlgebra σX x
    letI : Algebra Y.functionField (X.presheaf.stalk x) :=
      horizontalFunctionFieldStalkAlgebra f x h
    letI : Algebra Y.functionField (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
      horizontalFunctionFieldResidueAlgebra f x h
    letI : IsScalarTower k Y.functionField (X.presheaf.stalk x) :=
      horizontalFunctionFieldStalkScalarTower σX σY f hstructure x h
    letI : IsScalarTower k Y.functionField (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
      horizontalFunctionFieldResidueScalarTower σX σY f hstructure x h
    ∀ η : Ω[Y.functionField⁄k],
      KaehlerDifferential.map k k (X.presheaf.stalk x)
        (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (KaehlerDifferential.map k k Y.functionField (X.presheaf.stalk x) η) =
      KaehlerDifferential.map k k Y.functionField
        (IsLocalRing.ResidueField (X.presheaf.stalk x)) η := by
  letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
  letI : Algebra k (X.presheaf.stalk x) := structureStalkAlgebra σX x
  letI : Algebra Y.functionField (X.presheaf.stalk x) :=
    horizontalFunctionFieldStalkAlgebra f x h
  letI : Algebra Y.functionField (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    horizontalFunctionFieldResidueAlgebra f x h
  letI : IsScalarTower k Y.functionField (X.presheaf.stalk x) :=
    horizontalFunctionFieldStalkScalarTower σX σY f hstructure x h
  letI : IsScalarTower k Y.functionField (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    horizontalFunctionFieldResidueScalarTower σX σY f hstructure x h
  letI : IsScalarTower Y.functionField (X.presheaf.stalk x)
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    horizontalFunctionFieldResidueLocalScalarTower f x h
  intro η
  exact actualDifferentialMap_comp k Y.functionField (X.presheaf.stalk x)
    (IsLocalRing.ResidueField (X.presheaf.stalk x)) η

end ActualHorizontalCurveForms

end

end ChenRanks
