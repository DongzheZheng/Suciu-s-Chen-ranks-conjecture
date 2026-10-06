import ChenRanks.KoszulLocalInverseCalculus

/-! Actual separation supplies the genuine polynomial-action and exterior-class
corrections. Generic original-module naturality combines them on every actual
second-term class. This bounded component specialization assumes no inverse. -/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]

local instance localCorrectionOriginalAddCommGroup
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : AddCommGroup (Module k V K) :=
  originalModuleAddCommGroup k V K

@[implicit_reducible] private def localCorrectionOriginalCoefficientDictionary
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) := inferInstance

local instance localCorrectionOriginalCoefficients
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) :=
  localCorrectionOriginalCoefficientDictionary k V K

local instance localCorrectionOriginalScalarModule
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module k (Module k V K) :=
  originalModuleScalarModule k V K

@[implicit_reducible] private def localCorrectionExtendedNativeModule
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) (R : Type*) [CommRing R] [Algebra (S k V) R] :
    _root_.Module R (CoefficientExtendedModule k V K R) := inferInstance

variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (P : Submodule k E) (I : Submodule k (⋀[k]^2 E)) [CharZero k]

local instance localCorrectionPointNativeModule (eP : P) :
    _root_.Module (ambientComponentPointLocalRing k E P eP)
      (componentPointOriginalModule k E P I eP) :=
  localCorrectionExtendedNativeModule k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)
    (ambientComponentPointLocalRing k E P eP)

local instance (priority := 2000) localCorrectionComponentZeroAddCommMonoid :
    AddCommMonoid (Module k (_root_.Module.Dual k P) ⊥) :=
  (originalModuleAddCommGroup k (_root_.Module.Dual k P) ⊥).toAddCommMonoid

/-- The actual two quotient maps' reverse composite fixes every
literal second-term presentation class after true localization. -/
theorem actualPointLocalized_sectionMap_secondClass
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I)
    (hsep : I ⊓ mixedExterior P ≤ pureExterior P) (eP : P)
    (v : _root_.Module.Dual k E) (hv : v (eP : E) = 1)
    (z : C2 k (_root_.Module.Dual k E)) :
    (1 : ambientComponentPointLocalRing k E P eP) ⊗ₜ[S k (_root_.Module.Dual k E)]
        isotropicComponentModuleSection k E P I
          (isotropicComponentModuleMap k E I P hiso
            (secondTensorToModule k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I) z)) =
      coefficientExtendedSecondMap k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)
        (ambientComponentPointLocalRing k E P eP) z := by
  exact quotient_secondClass_projection_correction k
    (_root_.Module.Dual k E) (_root_.Module.Dual k P)
    (exteriorAnnihilator k E 2 I) ⊥
    (componentDualQuotient k E P) (componentDualSection k E P)
    (isotropicComponentRelationContainment k E I P hiso)
    (isotropicComponentSectionRelationContainment k E P I)
    (ambientComponentPointLocalRing k E P eP)
    (actualPointLocalized_projectedPolynomial_action k E P I hsep eP v hv)
    (fun w ↦ by
      simpa only [componentPointExteriorClassLinear_apply] using
        actualPointLocalized_projectedExterior_class k E P I hsep eP v hv w) z

end ChenRanks.Koszul
