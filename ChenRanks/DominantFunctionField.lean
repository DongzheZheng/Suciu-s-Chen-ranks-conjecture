import ChenRanks.ProperAlgebraicity
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-!
# Actual function-field maps of dominant scheme morphisms

All field maps below are constructed from actual stalk maps.  Their
compatibility with `Spec` and the actual generic-point morphisms is
proved, rather than supplied as an unspecified comparison hypothesis.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

variable {X Y S : Scheme.{u}}

/-- Actual properness of the source structure map and actual
separatedness of the target structure map imply properness of the
actual morphism which commutes with these maps. -/
theorem proper_of_structure_comp
    (f : X ⟶ Y) (σX : X ⟶ S) (σY : Y ⟶ S)
    [IsProper σX] [IsSeparated σY] (h : f ≫ σY = σX) : IsProper f := by
  haveI : IsProper (f ≫ σY) := by rw [h]; infer_instance
  exact IsProper.of_comp f σY

variable [IsIntegral X] [IsIntegral Y]

/-- An actual dominant morphism sends the actual generic point to the
actual generic point. -/
theorem dominant_map_genericPoint (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  apply IsGenericPoint.eq ?_ (genericPoint_spec Y)
  simpa only [Set.image_univ, f.denseRange.closure_range] using
    (genericPoint_spec X).image f.continuous

/-- The actual function-field homomorphism, obtained from the actual
generic stalk map and the equality-induced actual stalk isomorphism. -/
def dominantFunctionFieldMap (f : X ⟶ Y) [IsDominant f] :
    Y.functionField ⟶ X.functionField :=
  (Y.presheaf.stalkCongr (Inseparable.of_eq (dominant_map_genericPoint f))).inv ≫
    f.stalkMap (genericPoint X)

@[reassoc]
theorem dominantFunctionFieldMap_spec_comp (f : X ⟶ Y) [IsDominant f] :
    Spec.map (dominantFunctionFieldMap f) ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f := by
  rw [dominantFunctionFieldMap, Spec.map_comp, Category.assoc,
    TopCat.Presheaf.stalkCongr_inv,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem dominantFunctionFieldMap_injective (f : X ⟶ Y) [IsDominant f] :
    Function.Injective (dominantFunctionFieldMap f) :=
  (dominantFunctionFieldMap f).hom.injective

/-- A dominant preimmersion gives a bijection on actual generic stalks:
surjectivity is the actual preimmersion's stalk condition, and
injectivity is that of the actual field homomorphism. -/
theorem dominantFunctionFieldMap_bijective
    (f : X ⟶ Y) [IsDominant f] [IsPreimmersion f] :
    Function.Bijective (dominantFunctionFieldMap f) := by
  refine ⟨dominantFunctionFieldMap_injective f, ?_⟩
  exact (f.stalkMap_surjective (genericPoint X)).comp
    (ConcreteCategory.bijective_of_isIso
      (Y.presheaf.stalkCongr (Inseparable.of_eq (dominant_map_genericPoint f))).inv).2

/-- The actual function-field ring equivalence of a dominant
preimmersion.  Compatibility with any base-field scalar action is a
separate statement, not inferred from this abstract equivalence. -/
def dominantPreimmersionFunctionFieldEquiv
    (f : X ⟶ Y) [IsDominant f] [IsPreimmersion f] :
    Y.functionField ≃+* X.functionField :=
  RingEquiv.ofBijective (dominantFunctionFieldMap f).hom
    (dominantFunctionFieldMap_bijective f)

variable {k : Type u} [Field k] [CharZero k]

/-- The actual scalar-to-function-field map is an injective field
homomorphism, so the actual function field inherits characteristic zero. -/
theorem functionField_charZero_from_structure (σ : Y ⟶ Spec (.of k)) :
    CharZero Y.functionField := by
  let φ : k →+* Y.functionField :=
    (topFunctionFieldGerm Y).hom.comp (globalScalarMap σ)
  refine ⟨fun m n h => ?_⟩
  apply Nat.cast_injective (R := k)
  apply φ.injective
  simpa only [map_natCast] using h

end

end ChenRanks
