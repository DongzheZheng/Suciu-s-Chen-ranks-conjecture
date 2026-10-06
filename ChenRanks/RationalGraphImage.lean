import ChenRanks.ActualSchemeImage
import ChenRanks.CurveAffineRationalMap

/-!
# The actual scheme-theoretic graph of an actual rational map

An actual rational map over the common base determines its actual
generic-point arrow by the native rational-map equivalence.  The native
pullback lift constructs the generic graph, and its native kernel image
constructs the graph closure.  Reducedness, integrality and the generic
preimmersion are conclusions.  No existence of a desired graph model or
function-field comparison is supplied.

The graph projection to the target is proper when the original source
structure morphism is proper.  This is an actual base-change and closed
immersion argument.  The target projection is not claimed dominant for
arbitrary rational maps: constant maps are a genuine boundary case.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

variable {X C S : Scheme.{u}} [IsIntegral X]
  (σX : X ⟶ S) (σC : C ⟶ S) [LocallyOfFiniteType σC]
  (φ : {r : X.RationalMap C // r.compHom σC = σX.toRationalMap})

/-- The actual generic arrow is extracted from the actual base-compatible
rational map by the native equivalence. -/
abbrev rationalGraphGenericArrow : Spec X.functionField ⟶ C :=
  ((Scheme.RationalMap.equivFunctionField σX σC).symm φ).1

theorem rationalGraphGenericArrow_structure :
    rationalGraphGenericArrow σX σC φ ≫ σC = X.fromSpecStalk (genericPoint X) ≫ σX :=
  ((Scheme.RationalMap.equivFunctionField σX σC).symm φ).2

/-- The actual generic graph in the actual fibre product. -/
def rationalGraphGenericMap : Spec X.functionField ⟶ pullback σX σC :=
  pullback.lift (X.fromSpecStalk (genericPoint X))
    (rationalGraphGenericArrow σX σC φ) (rationalGraphGenericArrow_structure σX σC φ).symm

@[reassoc (attr := simp)]
theorem rationalGraphGenericMap_fst :
    rationalGraphGenericMap σX σC φ ≫ pullback.fst σX σC = X.fromSpecStalk (genericPoint X) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem rationalGraphGenericMap_snd :
    rationalGraphGenericMap σX σC φ ≫ pullback.snd σX σC = rationalGraphGenericArrow σX σC φ :=
  pullback.lift_snd _ _ _

instance rationalGraphGenericMap_quasiCompact : QuasiCompact (rationalGraphGenericMap σX σC φ) :=
  fieldSpectrumMorphism_quasiCompact _

/-- The actual generic graph is a preimmersion.  Its source has one
actual point, and its actual stalk map is surjective because the
composition with the source projection is the native generic inclusion. -/
instance rationalGraphGenericMap_isPreimmersion :
    IsPreimmersion (rationalGraphGenericMap σX σC φ) := by
  letI : Subsingleton ↥(Spec X.functionField) := by
    change Subsingleton (PrimeSpectrum X.functionField)
    infer_instance
  refine { isEmbedding := Topology.IsEmbedding.of_subsingleton _, stalkMap_surjective := ?_ }
  intro z
  have hs : Function.Surjective
      ((rationalGraphGenericMap σX σC φ ≫ pullback.fst σX σC).stalkMap z) := by
    rw [rationalGraphGenericMap_fst]
    exact (X.fromSpecStalk (genericPoint X)).stalkMap_surjective z
  rw [Scheme.Hom.stalkMap_comp] at hs
  exact Function.Surjective.of_comp hs

/-- The graph closure is the actual native kernel subscheme image. -/
abbrev rationalGraphImage : Scheme.{u} := (rationalGraphGenericMap σX σC φ).image

abbrev rationalGraphToImage : Spec X.functionField ⟶ rationalGraphImage σX σC φ :=
  (rationalGraphGenericMap σX σC φ).toImage

instance rationalGraphImage_isIntegral : IsIntegral (rationalGraphImage σX σC φ) :=
  quasiCompactImage_isIntegral (rationalGraphGenericMap σX σC φ)

instance rationalGraphToImage_isDominant : IsDominant (rationalGraphToImage σX σC φ) :=
  inferInstanceAs (IsDominant (rationalGraphGenericMap σX σC φ).toImage)

instance rationalGraphToImage_isPreimmersion : IsPreimmersion (rationalGraphToImage σX σC φ) := by
  haveI : IsPreimmersion
      ((rationalGraphGenericMap σX σC φ).toImage ≫ (rationalGraphGenericMap σX σC φ).imageι) := by
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  exact IsPreimmersion.of_comp
    (rationalGraphGenericMap σX σC φ).toImage (rationalGraphGenericMap σX σC φ).imageι

/-- The two actual projections of the constructed graph image. -/
def rationalGraphProjectionSource : rationalGraphImage σX σC φ ⟶ X :=
  (rationalGraphGenericMap σX σC φ).imageι ≫ pullback.fst σX σC

def rationalGraphProjectionCurve : rationalGraphImage σX σC φ ⟶ C :=
  (rationalGraphGenericMap σX σC φ).imageι ≫ pullback.snd σX σC

@[reassoc (attr := simp)]
theorem rationalGraphToImage_projectionSource :
    rationalGraphToImage σX σC φ ≫ rationalGraphProjectionSource σX σC φ =
      X.fromSpecStalk (genericPoint X) := by
  simp only [rationalGraphToImage, rationalGraphProjectionSource,
    Scheme.Hom.toImage_imageι_assoc, rationalGraphGenericMap_fst]

@[reassoc (attr := simp)]
theorem rationalGraphToImage_projectionCurve :
    rationalGraphToImage σX σC φ ≫ rationalGraphProjectionCurve σX σC φ =
      rationalGraphGenericArrow σX σC φ := by
  simp only [rationalGraphToImage, rationalGraphProjectionCurve,
    Scheme.Hom.toImage_imageι_assoc, rationalGraphGenericMap_snd]

/-- An actual graph point lies over the original actual generic point. -/
def rationalGraphImageGenericPoint : rationalGraphImage σX σC φ :=
  rationalGraphToImage σX σC φ (IsLocalRing.closedPoint X.functionField)

@[simp]
theorem rationalGraphImageGenericPoint_projection :
    rationalGraphProjectionSource σX σC φ (rationalGraphImageGenericPoint σX σC φ) =
      genericPoint X := by
  have hp := congrArg (fun h : Spec X.functionField ⟶ X => h (IsLocalRing.closedPoint X.functionField))
    (rationalGraphToImage_projectionSource σX σC φ)
  simpa only [Scheme.Hom.comp_apply, rationalGraphImageGenericPoint,
    Scheme.fromSpecStalk_closedPoint] using hp

instance rationalGraphProjectionSource_isDominant :
    IsDominant (rationalGraphProjectionSource σX σC φ) := by
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff, ← genericPoint_closure X]
  apply closure_mono
  exact Set.singleton_subset_iff.mpr
    ⟨rationalGraphImageGenericPoint σX σC φ, rationalGraphImageGenericPoint_projection σX σC φ⟩

/-- Actual properness of the original source structure gives actual
properness of the graph-to-curve projection, through the actual
base-changed source and the actual closed image immersion. -/
instance rationalGraphProjectionCurve_isProper [IsProper σX] :
    IsProper (rationalGraphProjectionCurve σX σC φ) := by
  dsimp [rationalGraphProjectionCurve]
  infer_instance

/-- Curve dominance requires actual dominance of the generic arrow.
It is supplied by the proved injectivity of our coefficient-field map,
not by an assertion valid for every rational map. -/
theorem rationalGraphProjectionCurve_isDominant
    [IsDominant (rationalGraphGenericArrow σX σC φ)] :
    IsDominant (rationalGraphProjectionCurve σX σC φ) := by
  haveI : IsDominant
      (rationalGraphToImage σX σC φ ≫ rationalGraphProjectionCurve σX σC φ) := by
    rw [rationalGraphToImage_projectionCurve]
    infer_instance
  exact IsDominant.of_comp (rationalGraphToImage σX σC φ)
    (rationalGraphProjectionCurve σX σC φ)

end

end ChenRanks
