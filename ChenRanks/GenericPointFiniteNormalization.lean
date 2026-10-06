import ChenRanks.GenericPointChartSections
import ChenRanks.ScalarSchemeCharts

/-!
# Native finite normalization of an actual finite-type integral scheme

The object is the library's glued relative normalization of the actual
generic-point morphism. Its actual affine diagram rings are compared
with the original chart integral closures through actual pullbacks and
germs. Characteristic-zero finite type proves their finiteness, hence
the original glued normalization morphism is finite and proper.

No finite normalization morphism or selected normalized model is supplied
as an input. Function-field comparison and the local divisor interfaces
remain separate obligations.
-/

noncomputable section

namespace ChenRanks

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

variable (X : Scheme.{u}) [IsIntegral X]

instance genericPointMorphism_quasiCompact : QuasiCompact (genericPointMorphism X) :=
  fieldSpectrumMorphism_quasiCompact (genericPointMorphism X)

instance genericPointMorphism_quasiSeparated : QuasiSeparated (genericPointMorphism X) := by
  infer_instance

/-- The actual glued normalization of the original integral scheme. -/
abbrev actualFiniteTypeNormalization : Scheme.{u} :=
  (genericPointMorphism X).normalization

/-- The actual native normalization projection to the original scheme. -/
abbrev actualFiniteTypeNormalizationMap : actualFiniteTypeNormalization X ⟶ X :=
  (genericPointMorphism X).fromNormalization

instance actualFiniteTypeNormalization_isIntegral :
    IsIntegral (actualFiniteTypeNormalization X) := by
  infer_instance

/-- The actual integral-closure chart ring, with the native pullback
algebra dictionary fixed before constructing its ring structure. -/
def actualNormalizationChartRing (U : X.Opens) : Type u :=
  letI : Algebra Γ(X, U)
      Γ(Spec X.functionField, genericPointMorphism X ⁻¹ᵁ U) :=
    ((genericPointMorphism X).app U).hom.toAlgebra
  integralClosure Γ(X, U) Γ(Spec X.functionField, genericPointMorphism X ⁻¹ᵁ U)

instance actualNormalizationChartRing_commRing (U : X.Opens) :
    CommRing (actualNormalizationChartRing X U) := by
  letI : Algebra Γ(X, U)
      Γ(Spec X.functionField, genericPointMorphism X ⁻¹ᵁ U) :=
    ((genericPointMorphism X).app U).hom.toAlgebra
  exact Subalgebra.toCommRing (integralClosure Γ(X, U)
    Γ(Spec X.functionField, genericPointMorphism X ⁻¹ᵁ U))

instance actualNormalizationChartRing_algebra (U : X.Opens) :
    Algebra Γ(X, U) (actualNormalizationChartRing X U) := by
  letI : Algebra Γ(X, U)
      Γ(Spec X.functionField, genericPointMorphism X ⁻¹ᵁ U) :=
    ((genericPointMorphism X).app U).hom.toAlgebra
  exact Subalgebra.algebra (integralClosure Γ(X, U)
    Γ(Spec X.functionField, genericPointMorphism X ⁻¹ᵁ U))

variable {k : Type u} [Field k] [CharZero k]

/-- Every actual chart in the native normalization diagram is finite;
the empty-chart boundary is handled in the actual sheaf rings as well. -/
theorem actualNormalizationDiagramChart_finite
    (σ : X ⟶ Spec (.of k)) [LocallyOfFiniteType σ]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) (actualNormalizationChartRing X U) := by
  classical
  letI : Algebra Γ(X, U)
      Γ(Spec X.functionField, genericPointMorphism X ⁻¹ᵁ U) :=
    ((genericPointMorphism X).app U).hom.toAlgebra
  cases isEmpty_or_nonempty U with
  | inl h =>
    letI : IsEmpty U := h
    letI : IsEmpty (genericPointMorphism X ⁻¹ᵁ U) :=
      ⟨fun z ↦ h.false (⟨genericPointMorphism X z.val, z.property⟩ : U)⟩
    letI : Subsingleton Γ(Spec X.functionField, genericPointMorphism X ⁻¹ᵁ U) :=
      ⟨fun s t ↦ TopCat.Presheaf.section_ext (Spec X.functionField).sheaf _ s t
        (fun x hx ↦ False.elim (h.false (⟨genericPointMorphism X x, hx⟩ : U)))⟩
    letI : Subsingleton (actualNormalizationChartRing X U) := by
      change Subsingleton (integralClosure Γ(X, U)
        Γ(Spec X.functionField, genericPointMorphism X ⁻¹ᵁ U))
      infer_instance
    infer_instance
  | inr h =>
    letI : Nonempty U := h
    let e := (genericPointPreimageSectionIso X U).commRingCatIsoToRingEquiv
    let eA : Γ(Spec X.functionField, genericPointMorphism X ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
        X.functionField :=
      { e with
        commutes' := by
          intro a
          exact congrArg (fun φ ↦ φ.hom a) (genericPointPreimageSectionIso_pullback X U) }
    letI : Module.Finite Γ(X, U) (integralClosure Γ(X, U) X.functionField) :=
      originalAffineChart_integralClosure_finite σ U hU
    let C := integralClosure Γ(X, U) X.functionField
    let fC : C →ₗ[Γ(X, U)] actualNormalizationChartRing X U :=
      eA.symm.mapIntegralClosure.toLinearMap
    exact Module.Finite.of_surjective fC eA.symm.mapIntegralClosure.surjective

/-- The actual native normalization morphism is finite, by its actual
affine diagram and the preceding finiteness proof. -/
theorem actualFiniteTypeNormalizationMap_isFinite
    (σ : X ⟶ Spec (.of k)) [LocallyOfFiniteType σ] :
    IsFinite (actualFiniteTypeNormalizationMap X) := by
  refine { finite_app := ?_ }
  intro U hU
  letI : Algebra Γ(X, U)
      Γ(Spec X.functionField, genericPointMorphism X ⁻¹ᵁ U) :=
    ((genericPointMorphism X).app U).hom.toAlgebra
  letI : Module.Finite Γ(X, U) (actualNormalizationChartRing X U) :=
    actualNormalizationDiagramChart_finite X σ U hU
  have hfin : (algebraMap Γ(X, U) (actualNormalizationChartRing X U)).Finite :=
    RingHom.finite_algebraMap.mpr
      (actualNormalizationDiagramChart_finite X σ U hU)
  rw [Scheme.Hom.fromNormalization_app]
  exact (RingHom.Finite.of_surjective _
      ((genericPointMorphism X).normalizationObjIso hU).symm.commRingCatIsoToRingEquiv.surjective).comp
    hfin

/-- Properness of the actual projection follows from the proved finite
normalization, and is available for the original graph model. -/
theorem actualFiniteTypeNormalizationMap_isProper
    (σ : X ⟶ Spec (.of k)) [LocallyOfFiniteType σ] :
    IsProper (actualFiniteTypeNormalizationMap X) := by
  letI : IsFinite (actualFiniteTypeNormalizationMap X) :=
    actualFiniteTypeNormalizationMap_isFinite X σ
  infer_instance

end ChenRanks
