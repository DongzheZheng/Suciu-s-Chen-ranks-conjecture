import ChenRanks.DominantFunctionField
import ChenRanks.ProperFibreComponent

/-!
# The actual reduced generic fibre and its actual function field

The raw fibre is the actual scheme pullback along the generic stalk's
canonical map.  Its reduction is the actual nilradical subscheme, not a
scheme whose desired properties are postulated.  A point constructed by
the pullback universal property proves irreducibility; the actual radical
quotient cover proves reducedness.  Properness follows from actual base
change and an actual closed immersion.

The resulting projection is a dominant preimmersion.  Its actual generic
stalk map supplies the function-field equivalence.  Compatibility with
the actual base-field scalar action will be proved separately.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The actual generic base change; this is not identified with its
reduction in the definitions or conclusions below. -/
abbrev rawGenericFibre (f : X ⟶ Y) : Scheme.{u} :=
  pullback f (Y.fromSpecStalk (genericPoint Y))

abbrev rawGenericFibreProjection (f : X ⟶ Y) : rawGenericFibre f ⟶ X :=
  pullback.fst f (Y.fromSpecStalk (genericPoint Y))

abbrev rawGenericFibreScalarMorphism (f : X ⟶ Y) :
    rawGenericFibre f ⟶ Spec (.of Y.functionField) :=
  pullback.snd f (Y.fromSpecStalk (genericPoint Y))

instance rawGenericFibreProjection_isPreimmersion (f : X ⟶ Y) :
    IsPreimmersion (rawGenericFibreProjection f) := by
  dsimp [rawGenericFibreProjection]
  infer_instance

instance rawGenericFibreScalarMorphism_isProper (f : X ⟶ Y) [IsProper f] :
    IsProper (rawGenericFibreScalarMorphism f) := by
  dsimp [rawGenericFibreScalarMorphism]
  infer_instance

/-- The actual generic-point morphism of the ambient space lifts to
the actual generic pullback square. -/
def rawGenericFibreFieldLift (f : X ⟶ Y) [IsDominant f] :
    Spec X.functionField ⟶ rawGenericFibre f :=
  pullback.lift (X.fromSpecStalk (genericPoint X))
    (Spec.map (dominantFunctionFieldMap f)) (dominantFunctionFieldMap_spec_comp f).symm

@[reassoc (attr := simp)]
theorem rawGenericFibreFieldLift_projection (f : X ⟶ Y) [IsDominant f] :
    rawGenericFibreFieldLift f ≫ rawGenericFibreProjection f =
      X.fromSpecStalk (genericPoint X) :=
  pullback.lift_fst _ _ _

/-- An actual point of the actual raw generic fibre, constructed by
evaluating the actual lifted field-spectrum morphism. -/
def rawGenericFibrePoint (f : X ⟶ Y) [IsDominant f] : rawGenericFibre f :=
  rawGenericFibreFieldLift f (IsLocalRing.closedPoint X.functionField)

@[simp]
theorem rawGenericFibrePoint_projection (f : X ⟶ Y) [IsDominant f] :
    rawGenericFibreProjection f (rawGenericFibrePoint f) = genericPoint X := by
  rw [rawGenericFibrePoint, ← Scheme.Hom.comp_apply, rawGenericFibreFieldLift_projection]
  exact Scheme.fromSpecStalk_closedPoint

/-- The actual constructed point is generic in the actual raw fibre;
the actual projection embedding reflects specialization. -/
theorem rawGenericFibrePoint_isGeneric (f : X ⟶ Y) [IsDominant f] :
    IsGenericPoint (rawGenericFibrePoint f) Set.univ := by
  rw [isGenericPoint_iff_specializes]
  intro z
  simp only [Set.mem_univ, iff_true]
  apply (rawGenericFibreProjection f).isEmbedding.isInducing.specializes_iff.mp
  rw [rawGenericFibrePoint_projection]
  exact genericPoint_specializes ((rawGenericFibreProjection f) z)

instance rawGenericFibre_irreducibleSpace (f : X ⟶ Y) [IsDominant f] :
    IrreducibleSpace (rawGenericFibre f) :=
  (irreducibleSpace_def ↥(rawGenericFibre f)).mpr
    (rawGenericFibrePoint_isGeneric f).isIrreducible

/-- The actual nilradical subscheme of the actual generic base change. -/
def reducedGenericFibre (f : X ⟶ Y) : Scheme.{u} :=
  (rawGenericFibre f).nilradical.subscheme

def reducedGenericFibreι (f : X ⟶ Y) : reducedGenericFibre f ⟶ rawGenericFibre f :=
  (rawGenericFibre f).nilradical.subschemeι

instance reducedGenericFibreι_isClosedImmersion (f : X ⟶ Y) :
    IsClosedImmersion (reducedGenericFibreι f) :=
  inferInstanceAs (IsClosedImmersion (rawGenericFibre f).nilradical.subschemeι)

instance reducedGenericFibre_isReduced (f : X ⟶ Y) : IsReduced (reducedGenericFibre f) :=
  radical_subscheme_isReduced (⊥ : (rawGenericFibre f).IdealSheafData)

instance reducedGenericFibre_irreducibleSpace (f : X ⟶ Y) [IsDominant f] :
    IrreducibleSpace (reducedGenericFibre f) := by
  change IrreducibleSpace (Set.univ : Set (rawGenericFibre f))
  exact Subtype.irreducibleSpace (IrreducibleSpace.isIrreducible_univ (rawGenericFibre f))

instance reducedGenericFibre_isIntegral (f : X ⟶ Y) [IsDominant f] :
    IsIntegral (reducedGenericFibre f) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

def reducedGenericFibreProjection (f : X ⟶ Y) : reducedGenericFibre f ⟶ X :=
  reducedGenericFibreι f ≫ rawGenericFibreProjection f

def reducedGenericFibreScalarMorphism (f : X ⟶ Y) :
    reducedGenericFibre f ⟶ Spec (.of Y.functionField) :=
  reducedGenericFibreι f ≫ rawGenericFibreScalarMorphism f

instance reducedGenericFibreProjection_isPreimmersion (f : X ⟶ Y) :
    IsPreimmersion (reducedGenericFibreProjection f) := by
  dsimp [reducedGenericFibreProjection]
  infer_instance

instance reducedGenericFibreScalarMorphism_isProper (f : X ⟶ Y) [IsProper f] :
    IsProper (reducedGenericFibreScalarMorphism f) := by
  dsimp [reducedGenericFibreScalarMorphism]
  infer_instance

/-- The constructed generic point also exists in the actual reduction,
whose underlying support is the whole raw fibre. -/
def reducedGenericFibrePoint (f : X ⟶ Y) [IsDominant f] : reducedGenericFibre f :=
  ⟨rawGenericFibrePoint f, by trivial⟩

@[simp]
theorem reducedGenericFibrePoint_projection (f : X ⟶ Y) [IsDominant f] :
    reducedGenericFibreProjection f (reducedGenericFibrePoint f) = genericPoint X := by
  change rawGenericFibreProjection f (rawGenericFibrePoint f) = genericPoint X
  exact rawGenericFibrePoint_projection f

instance reducedGenericFibreProjection_isDominant (f : X ⟶ Y) [IsDominant f] :
    IsDominant (reducedGenericFibreProjection f) := by
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff, ← genericPoint_closure X]
  apply closure_mono
  exact Set.singleton_subset_iff.mpr
    ⟨reducedGenericFibrePoint f, reducedGenericFibrePoint_projection f⟩

omit [IsIntegral X] in
@[reassoc]
theorem reducedGenericFibre_square (f : X ⟶ Y) :
    reducedGenericFibreProjection f ≫ f =
      reducedGenericFibreScalarMorphism f ≫ Y.fromSpecStalk (genericPoint Y) := by
  simp only [reducedGenericFibreProjection, reducedGenericFibreScalarMorphism,
    rawGenericFibreProjection, rawGenericFibreScalarMorphism, Category.assoc,
    pullback.condition]

/-- The actual projection-induced map on actual function fields. -/
abbrev reducedGenericFibreFunctionFieldMap (f : X ⟶ Y) [IsDominant f] :
    X.functionField ⟶ (reducedGenericFibre f).functionField :=
  dominantFunctionFieldMap (reducedGenericFibreProjection f)

/-- The actual function-field equivalence follows from the proved
dominant preimmersion, without any comparison-equivalence premise. -/
abbrev reducedGenericFibreFunctionFieldEquiv (f : X ⟶ Y) [IsDominant f] :
    X.functionField ≃+* (reducedGenericFibre f).functionField :=
  dominantPreimmersionFunctionFieldEquiv (reducedGenericFibreProjection f)

end

end ChenRanks
