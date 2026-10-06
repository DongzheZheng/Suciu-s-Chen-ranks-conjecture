import ChenRanks.GenericFibreAlgebraicity

/-!
# Actual generic-fibre restriction of an actual regular section

An actual regular section on the inverse image of a nonempty base open
restricts to an actual global section on the actual reduced generic fibre.
The actual appLE restriction and the actual stalk maps prove compatibility
of their rational germs. Properness gives algebraicity over the actual
base function field, and the proved scalar-compatible comparison returns
this algebraicity to the original ambient function field.

The input here is an actual regular section, not an assumed vanishing
relative differential or a placeholder vertical-function detector.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

universe u

variable {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]

/-- The actual generic point lies in each actual nonempty open. -/
theorem genericPoint_mem_nonempty_open (W : X.Opens) [hW : Nonempty W] :
    genericPoint X ∈ W :=
  ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr (by simpa using hW)

/-- For an actual dominant morphism which factors through an actual
open, the actual section restriction has exactly the expected rational
germ under the actual generic-stalk function-field map. -/
theorem dominantFunctionFieldMap_regularSectionRestriction
    (j : Z ⟶ X) [IsDominant j] (V : X.Opens) [Nonempty V]
    (g : Z ⟶ V.toScheme) (hfactor : g ≫ V.ι = j) (s : Γ(X, V)) :
    dominantFunctionFieldMap j (X.germToFunctionField V s) =
      topFunctionFieldGerm Z (regularSectionRestriction V g s) := by
  have hx : genericPoint X ∈ V := genericPoint_mem_nonempty_open V
  have hjx : j (genericPoint Z) ∈ V := by
    rw [dominant_map_genericPoint j]
    exact hx
  have hgerm :
      (X.presheaf.stalkCongr (Inseparable.of_eq (dominant_map_genericPoint j))).inv
          (X.germToFunctionField V s) =
        X.presheaf.germ V (j (genericPoint Z)) hjx s := by
    change X.presheaf.stalkSpecializes
        (Inseparable.of_eq (dominant_map_genericPoint j)).le
        (X.presheaf.germ V (genericPoint X) hx s) = _
    exact congrArg
      (fun h : Γ(X, V) ⟶ X.presheaf.stalk (j (genericPoint Z)) => h s)
      (X.presheaf.germ_stalkSpecializes hx
        (Inseparable.of_eq (dominant_map_genericPoint j)).le)
  have hr := regularSectionRestriction_germ V g s (genericPoint Z)
  subst j
  rw [dominantFunctionFieldMap, CommRingCat.comp_apply, hgerm]
  exact hr

variable {Y : Scheme.{u}} [IsIntegral Y]

/-- The image of the actual generic-point spectrum is contained in
every actual nonempty open of the base. -/
theorem genericBase_range_subset_nonempty_open (W : Y.Opens) [Nonempty W] :
    Set.range (Y.fromSpecStalk (genericPoint Y)) ⊆ W := by
  rw [Scheme.range_fromSpecStalk]
  intro p hp
  exact hp.mem_open W.isOpen (genericPoint_mem_nonempty_open W)

instance dominant_preimage_nonempty_open (f : X ⟶ Y) [IsDominant f]
    (W : Y.Opens) [Nonempty W] : Nonempty (f ⁻¹ᵁ W) := by
  refine ⟨⟨genericPoint X, ?_⟩⟩
  change f (genericPoint X) ∈ W
  rw [dominant_map_genericPoint f]
  exact genericPoint_mem_nonempty_open W

/-- The actual reduced generic fibre maps to the actual inverse image
of an actual nonempty base open by the actual open-immersion lift. -/
def reducedGenericFibreToNonemptyOpen (f : X ⟶ Y) [IsDominant f]
    (W : Y.Opens) [Nonempty W] :
    reducedGenericFibre f ⟶ (f ⁻¹ᵁ W).toScheme :=
  reducedGenericFibreι f ≫ rationalPointFibreToOpen f
    (Y.fromSpecStalk (genericPoint Y)) W (genericBase_range_subset_nonempty_open W)

omit [IsIntegral X] in
@[reassoc (attr := simp)]
theorem reducedGenericFibreToNonemptyOpen_fac (f : X ⟶ Y) [IsDominant f]
    (W : Y.Opens) [Nonempty W] :
    reducedGenericFibreToNonemptyOpen f W ≫ (f ⁻¹ᵁ W).ι =
      reducedGenericFibreProjection f := by
  simp only [reducedGenericFibreToNonemptyOpen, reducedGenericFibreProjection,
    rawGenericFibreProjection, Category.assoc, rationalPointFibreToOpen_fac]

/-- Restriction of the actual ambient section along this constructed
map is compatible with the actual projection-induced function-field map. -/
theorem reducedGenericFibre_regularSectionRestriction_germ
    (f : X ⟶ Y) [IsDominant f] (W : Y.Opens) [Nonempty W]
    (s : X.presheaf.obj (op (f ⁻¹ᵁ W))) :
    reducedGenericFibreFunctionFieldMap f (X.germToFunctionField (f ⁻¹ᵁ W) s) =
      topFunctionFieldGerm (reducedGenericFibre f)
        (regularSectionRestriction (f ⁻¹ᵁ W) (reducedGenericFibreToNonemptyOpen f W) s) :=
  dominantFunctionFieldMap_regularSectionRestriction
    (reducedGenericFibreProjection f) (f ⁻¹ᵁ W)
    (reducedGenericFibreToNonemptyOpen f W) (reducedGenericFibreToNonemptyOpen_fac f W) s

/-- Actual regularity over a nonempty base open implies algebraicity
of the original rational germ over the actual base function field.
The reduced generic fibre and the scalar-compatible comparison are
constructed, rather than supplied as existence assumptions. -/
theorem regular_germ_isAlgebraic_over_baseFunctionField
    (f : X ⟶ Y) [IsDominant f] [IsProper f]
    (W : Y.Opens) [Nonempty W] (s : X.presheaf.obj (op (f ⁻¹ᵁ W))) :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
    IsAlgebraic Y.functionField (X.germToFunctionField (f ⁻¹ᵁ W) s) := by
  letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
  letI : Algebra Y.functionField (reducedGenericFibre f).functionField :=
    structureFunctionFieldAlgebra (reducedGenericFibreScalarMorphism f)
  let e := reducedGenericFibreFunctionFieldAlgEquiv f
  have hg := global_regular_function_germ_isAlgebraic
    (reducedGenericFibreScalarMorphism f)
    (regularSectionRestriction (f ⁻¹ᵁ W) (reducedGenericFibreToNonemptyOpen f W) s)
  have hg' : IsAlgebraic Y.functionField (e (X.germToFunctionField (f ⁻¹ᵁ W) s)) := by
    change IsAlgebraic Y.functionField
      (reducedGenericFibreFunctionFieldMap f (X.germToFunctionField (f ⁻¹ᵁ W) s))
    rw [reducedGenericFibre_regularSectionRestriction_germ]
    exact hg
  exact (isAlgebraic_algHom_iff e.toAlgHom e.injective).mp hg'

/-- In characteristic zero the same actual rational germ has zero
relative differential in the original ambient function field. -/
theorem regular_germ_relative_differential_eq_zero [CharZero Y.functionField]
    (f : X ⟶ Y) [IsDominant f] [IsProper f]
    (W : Y.Opens) [Nonempty W] (s : X.presheaf.obj (op (f ⁻¹ᵁ W))) :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
    KaehlerDifferential.D Y.functionField X.functionField
      (X.germToFunctionField (f ⁻¹ᵁ W) s) = 0 := by
  letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
  exact relative_differential_eq_zero_of_isAlgebraic _
    (regular_germ_isAlgebraic_over_baseFunctionField f W s)

variable {k : Type u} [Field k] [CharZero k]

/-- The original proper-source/separated-base structural morphisms
supply both properness of the actual curve morphism and characteristic
zero of its actual function field. Regularity is the remaining input. -/
theorem regular_germ_relative_differential_eq_zero_of_proper_source
    (σX : X ⟶ Spec (.of k)) (σY : Y ⟶ Spec (.of k))
    [IsProper σX] [IsSeparated σY] (f : X ⟶ Y) [IsDominant f]
    (hstructure : f ≫ σY = σX)
    (W : Y.Opens) [Nonempty W] (s : X.presheaf.obj (op (f ⁻¹ᵁ W))) :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
    KaehlerDifferential.D Y.functionField X.functionField
      (X.germToFunctionField (f ⁻¹ᵁ W) s) = 0 := by
  letI : IsProper f := proper_of_structure_comp f σX σY hstructure
  letI : CharZero Y.functionField := functionField_charZero_from_structure σY
  exact regular_germ_relative_differential_eq_zero f W s

end

end ChenRanks
