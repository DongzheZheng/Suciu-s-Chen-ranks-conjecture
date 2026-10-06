import ChenRanks.KoszulIsotropicComponentLocalConstantTensor

/-!
# Genuine inverse of the actual local isotropic component map

The genuine second-term surjection supplies actual presentation
representatives for every original quotient element. Naturality of the
actual quotient maps, equality of the actual projected polynomial action,
and equality of the actual projected exterior class show that the
reverse composite fixes every such literal tensor class. Native tensor
induction extends this equality to the whole original localization.

The nonzero-point theorem derives the normalized functional from actual
dual evaluation. Its hypotheses are original finite dimension,
characteristic zero, actual isotropy and actual separation of the
subspace, and an actual nonzero vector in it. No freeness, generator
surjectivity, faithfulness, class identity, or local isomorphism is a
hypothesis. The conclusion is about the two stated literal affine
evaluation-point tensor localizations, not a native Proj stalk.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]

local instance inverseOriginalAddCommGroup
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : AddCommGroup (Module k V K) :=
  originalModuleAddCommGroup k V K

@[implicit_reducible] private def inverseOriginalCoefficientDictionary
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) := inferInstance

local instance inverseOriginalCoefficients
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) :=
  inverseOriginalCoefficientDictionary k V K

local instance inverseOriginalScalarModule
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module k (Module k V K) :=
  originalModuleScalarModule k V K

@[implicit_reducible] private def inverseExtendedNativeModule
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) (R : Type*) [CommRing R] [Algebra (S k V) R] :
    _root_.Module R (CoefficientExtendedModule k V K R) := inferInstance

variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (P : Submodule k E) (I : Submodule k (⋀[k]^2 E)) [CharZero k]

local instance inversePointNativeModule (eP : P) :
    _root_.Module (ambientComponentPointLocalRing k E P eP)
      (componentPointOriginalModule k E P I eP) :=
  inverseExtendedNativeModule k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)
    (ambientComponentPointLocalRing k E P eP)

local instance (priority := 2000) inverseComponentZeroAddCommMonoid :
    AddCommMonoid (Module k (_root_.Module.Dual k P) ⊥) :=
  (originalModuleAddCommGroup k (_root_.Module.Dual k P) ⊥).toAddCommMonoid

/-- Separation proves the actual reverse tensor map composed with the
actual canonical tensor map is the identity on the literal original
localization. -/
theorem isotropicComponentLocalizedSection_map_apply
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I)
    (hsep : I ⊓ mixedExterior P ≤ pureExterior P) (eP : P)
    (v : _root_.Module.Dual k E) (hv : v (eP : E) = 1)
    (z : componentPointOriginalModule k E P I eP) :
    isotropicComponentLocalizedSection k E P I eP
      (isotropicComponentLocalizedMap k E P I eP hiso z) = z := by
  exact semilinearTensorMap_inverse_apply
    (S k (_root_.Module.Dual k E)) (S k (_root_.Module.Dual k P))
    (ambientComponentPointLocalRing k E P eP) (componentPointLocalRing k E P eP)
    (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I))
    (Module k (_root_.Module.Dual k P) ⊥)
    (componentSymmetricProjection k E P).toRingHom (componentSymmetricSection k E P).toRingHom
    (componentLocalCoefficientSemilinearProjection k E P eP)
    (isotropicComponentModuleSemilinearMap k E P I hiso)
    (componentLocalCoefficientSemilinearSection k E P eP)
    (isotropicComponentModuleSemilinearSection k E P I)
    (actualPointLocalized_sectionMap_constantTensor k E P I hiso hsep eP v hv)
    (actualPointLocalized_retraction_action k E P I hsep eP v hv) z

/-- At every actual nonzero vector in an actual separated isotropic
subspace, the actual canonical map between the two explicitly stated
literal evaluation-point localizations is bijective. The normalized
dual functional used by the proof is derived from actual nonzeroness. -/
theorem isotropicComponentLocalizedMap_bijective_of_nonzero
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I)
    (hsep : I ⊓ mixedExterior P ≤ pureExterior P) (eP : P) (heP : eP ≠ 0) :
    Function.Bijective (isotropicComponentLocalizedMap k E P I eP hiso) := by
  have he : (eP : E) ≠ 0 := by
    intro h
    apply heP
    exact Subtype.ext h
  obtain ⟨v, hv⟩ := exists_point_normalized_vector k (_root_.Module.Dual k E)
    (pointOfVector k E (eP : E)) (pointOfVector_ne_zero k E he)
  refine ⟨?_, isotropicComponentLocalizedMap_surjective k E P I eP hiso⟩
  intro z t hzt
  have h := congrArg (isotropicComponentLocalizedSection k E P I eP) hzt
  simpa only [isotropicComponentLocalizedSection_map_apply k E P I hiso hsep eP v hv] using h

end ChenRanks.Koszul
