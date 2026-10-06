import ChenRanks.KoszulCanonicalFamilyObjects
import ChenRanks.FiniteProductTensorLocalization
import ChenRanks.KoszulOffComponentLocalization
import ChenRanks.KoszulNonresonantLocalization
import ChenRanks.SeparatedIsotropicIntersections

/-!
# Native family localization at every actual nonzero evaluation point

The source, target factors, family subtype, and family map are the
original objects. Actual separation derives family finiteness and
nonzero-intersection uniqueness. At a resonant point its genuine
component map is bijective and the other original factors localize to
zero. At a nonresonant point the actual original source and all actual
factors localize to zero. Native finite-product tensor comparison then
proves bijectivity of native base change of the same original family
map, at every actual nonzero evaluation point.

This is not yet an all-prime, graded eventual-isomorphism, effective
degree-bound, or Chen-ranks statement.
-/

noncomputable section

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E] [CharZero k]
variable (I : Submodule k (⋀[k]^2 E))

local instance familyEvaluationSourceAddCommGroup :
    AddCommGroup (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  originalModuleAddCommGroup k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

local instance (priority := 2000) familyEvaluationSourceAddCommMonoid :
    AddCommMonoid (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  (originalModuleAddCommGroup k (_root_.Module.Dual k E)
    (exteriorAnnihilator k E 2 I)).toAddCommMonoid

@[implicit_reducible] private def familyEvaluationOriginalCoefficients
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) :=
  inferInstance

local instance familyEvaluationSourceCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E))
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  familyEvaluationOriginalCoefficients k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

local instance (priority := 2000) familyEvaluationSourceScalarAction :
    SMul (S k (_root_.Module.Dual k E))
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  (familyEvaluationSourceCoefficients k E I).toSMul

local instance familyEvaluationGroups :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommGroup (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentAddCommGroups k E I

local instance (priority := 2000) familyEvaluationMonoids :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommMonoid (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentAddCommMonoids k E I

local instance (priority := 2000) familyEvaluationCoefficients :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      _root_.Module (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentCoefficients k E I

local instance (priority := 2000) familyEvaluationScalarActions :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      SMul (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentScalarActions k E I

/-- Actual separation makes the native localization of the original
canonical family map bijective at every actual nonzero evaluation
point. No local-map or finite-family conclusion is a final premise. -/
theorem originalCanonicalFamilyLocalization_bijective_of_nonzero
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
      2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)
    (e : E) (he : e ≠ 0) :
    Function.Bijective (originalCanonicalFamilyLocalization k E I e) := by
  classical
  letI := canonicalFamilyFintype k E I hsep
  let R := PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e)
  let N := fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
    ComponentAmbientModule k E P.val
  let f := fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
    isotropicComponentAmbientModuleMap k E P.val I (canonicalFamily_component_isotropy k E I P)
  by_cases hres : e ∈ resonance I
  · obtain ⟨P, hP, hdim, heP⟩ := nonzero_resonance_mem_maximal_isotropic I he hres
    let Pidx : OriginalMaximalIsotropicFamily (cupQuotient I) := ⟨P, hP, hdim⟩
    let eP : P := ⟨e, heP⟩
    have hePne : eP ≠ 0 := by
      intro hz
      exact he (congrArg Subtype.val hz)
    have hsepP : I ⊓ mixedExterior P ≤ pureExterior P := by
      rw [inf_comm, hsep P hP hdim]
    apply ChenRanks.finiteProductTensor_baseChange_bijective_of_one_component
      (S k (_root_.Module.Dual k E)) R
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) N f Pidx
    · change Function.Bijective (isotropicComponentCanonicalLocalization k E P I eP
        (canonicalFamily_component_isotropy k E I Pidx))
      exact isotropicComponentCanonicalLocalization_bijective_of_nonzero k E P I
        (canonicalFamily_component_isotropy k E I Pidx) hsepP eP hePne
    · intro Q hQP
      have heQ : e ∉ Q.val := by
        intro hmem
        apply hQP
        apply Subtype.ext
        have hsepQ : mixedExterior Q.val ⊓ LinearMap.ker (cupQuotient I) =
            pureExterior Q.val := by
          simpa only [cupQuotient, Submodule.ker_mkQ] using
            hsep Q.val Q.property.1 Q.property.2
        exact maximalIsotropic_eq_of_nonzero_intersection_of_separated
          (cupQuotient I) Q.val P Q.property.1 hP hsepQ hmem heP he
      exact componentAmbientModule_localization_subsingleton_of_not_mem k E Q.val e heQ
  · letI := originalKoszul_localization_subsingleton_of_nonresonant k E I e he hres
    apply ChenRanks.finiteProductTensor_baseChange_bijective_of_subsingleton
      (S k (_root_.Module.Dual k E)) R
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) N f
    intro P
    have heP : e ∉ P.val := by
      intro hmem
      exact hres ((isotropic_subspace_subset_resonance I P.val P.property.2
        (canonicalFamily_component_isotropy k E I P)) hmem)
    exact componentAmbientModule_localization_subsingleton_of_not_mem k E P.val e heP

end ChenRanks.Koszul
