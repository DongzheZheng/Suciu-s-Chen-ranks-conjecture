import ChenRanks.KoszulIsotropicComponentLocalCorrection

/-! The genuine second-term surjection extends the already proved actual
second-class correction to every element of the actual original quotient.
The actual semilinear maps retain their original quotient functions. -/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]

local instance localConstantTensorOriginalAddCommGroup
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : AddCommGroup (Module k V K) :=
  originalModuleAddCommGroup k V K

@[implicit_reducible] private def localConstantTensorOriginalCoefficientDictionary
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) := inferInstance

local instance localConstantTensorOriginalCoefficients
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) :=
  localConstantTensorOriginalCoefficientDictionary k V K

local instance localConstantTensorOriginalScalarModule
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module k (Module k V K) :=
  originalModuleScalarModule k V K

@[implicit_reducible] private def localConstantTensorExtendedNativeModule
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) (R : Type*) [CommRing R] [Algebra (S k V) R] :
    _root_.Module R (CoefficientExtendedModule k V K R) := inferInstance

variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (P : Submodule k E) (I : Submodule k (⋀[k]^2 E)) [CharZero k]

local instance localConstantTensorPointNativeModule (eP : P) :
    _root_.Module (ambientComponentPointLocalRing k E P eP)
      (componentPointOriginalModule k E P I eP) :=
  localConstantTensorExtendedNativeModule k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)
    (ambientComponentPointLocalRing k E P eP)

local instance (priority := 2000) localConstantTensorComponentZeroAddCommMonoid :
    AddCommMonoid (Module k (_root_.Module.Dual k P) ⊥) :=
  (originalModuleAddCommGroup k (_root_.Module.Dual k P) ⊥).toAddCommMonoid

/-- The actual original quotient has genuine second-term representatives;
the already proved surjection now extends the actual correction identity
to every original quotient element. -/
theorem actualPointLocalized_sectionMap_constantTensor
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I)
    (hsep : I ⊓ mixedExterior P ≤ pureExterior P) (eP : P)
    (v : _root_.Module.Dual k E) (hv : v (eP : E) = 1)
    (z : Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :
    (1 : ambientComponentPointLocalRing k E P eP) ⊗ₜ[S k (_root_.Module.Dual k E)]
        isotropicComponentModuleSemilinearSection k E P I
          (isotropicComponentModuleSemilinearMap k E P I hiso z) =
      (1 : ambientComponentPointLocalRing k E P eP) ⊗ₜ[S k (_root_.Module.Dual k E)] z := by
  exact quotient_constantTensor_projection_correction k
    (_root_.Module.Dual k E) (_root_.Module.Dual k P)
    (exteriorAnnihilator k E 2 I) ⊥
    (componentDualQuotient k E P) (componentDualSection k E P)
    (isotropicComponentRelationContainment k E I P hiso)
    (isotropicComponentSectionRelationContainment k E P I)
    (ambientComponentPointLocalRing k E P eP)
    (actualPointLocalized_sectionMap_secondClass k E P I hiso hsep eP v hv) z

end ChenRanks.Koszul
