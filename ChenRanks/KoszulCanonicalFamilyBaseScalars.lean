import ChenRanks.KoszulCanonicalFamilyObjects
import ChenRanks.KoszulDirectSum

/-!
# The original base-field action on the actual canonical target

The component synonym retains the original quotient's base-field
action. Compatibility with its already constructed ambient action is
proved from the true symmetric projection's algebra-map compatibility,
not from a newly chosen scalar action or a scalar-tower hypothesis.
The base-linear canonical map is the original ambient-linear map with
native scalar restriction, and its function equals the already proved
original homogeneous-functorial map.
-/

noncomputable section

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E]
variable (P : Submodule k E)

local instance (priority := 2000) canonicalBaseComponentGroup :
    AddCommGroup (ComponentAmbientModule k E P) :=
  componentAmbientModuleAddCommGroup k E P

local instance (priority := 2000) canonicalBaseComponentMonoid :
    AddCommMonoid (ComponentAmbientModule k E P) :=
  componentAmbientModuleAddCommMonoid k E P

local instance (priority := 2000) canonicalBaseProjectionAlgebra :
    Algebra (S k (_root_.Module.Dual k E)) (S k (_root_.Module.Dual k P)) :=
  componentSymmetricProjectionAlgebra k E P

local instance (priority := 2000) canonicalBaseComponentOriginalCoefficients :
    _root_.Module (S k (_root_.Module.Dual k P)) (ComponentAmbientModule k E P) :=
  componentAmbientModuleOriginalCoefficients k E P

local instance (priority := 2000) canonicalBaseComponentOriginalScalarAction :
    SMul (S k (_root_.Module.Dual k P)) (ComponentAmbientModule k E P) :=
  componentAmbientModuleOriginalScalarAction k E P

local instance (priority := 2000) canonicalBaseComponentCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P) :=
  componentAmbientModuleCoefficients k E P

local instance (priority := 2000) canonicalBaseComponentScalarAction :
    SMul (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P) :=
  componentAmbientModuleScalarAction k E P

/-- The actual original quotient's native base-field action. -/
@[implicit_reducible] def componentAmbientModuleBaseCoefficients :
    _root_.Module k (ComponentAmbientModule k E P) :=
  originalModuleScalarModule k (_root_.Module.Dual k P) ⊥

local instance (priority := 2000) canonicalBaseComponentBaseCoefficients :
    _root_.Module k (ComponentAmbientModule k E P) :=
  componentAmbientModuleBaseCoefficients k E P

/-- Its explicit native scalar parent. -/
@[implicit_reducible] def componentAmbientModuleBaseScalarAction :
    SMul k (ComponentAmbientModule k E P) :=
  (componentAmbientModuleBaseCoefficients k E P).toSMul

local instance (priority := 2000) canonicalBaseComponentBaseScalarAction :
    SMul k (ComponentAmbientModule k E P) :=
  componentAmbientModuleBaseScalarAction k E P

@[implicit_reducible] private def originalKoszulBaseCoefficientTower
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : IsScalarTower k (S k V) (Module k V K) :=
  inferInstance

local instance canonicalBaseComponentOriginalTower :
    IsScalarTower k (S k (_root_.Module.Dual k P)) (ComponentAmbientModule k E P) :=
  originalKoszulBaseCoefficientTower k (_root_.Module.Dual k P) ⊥

/-- The existing ambient action and original base action are a true
scalar tower, because the actual symmetric projection is a k-algebra map. -/
theorem componentAmbientModuleBaseCoefficientScalarTower :
    IsScalarTower k (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P) := by
  apply IsScalarTower.of_algebraMap_smul
  intro c z
  change componentSymmetricProjection k E P
      (algebraMap k (S k (_root_.Module.Dual k E)) c) • z = c • z
  rw [(componentSymmetricProjection k E P).commutes]
  exact algebraMap_smul (S k (_root_.Module.Dual k P)) c z

local instance canonicalBaseComponentAmbientTower :
    IsScalarTower k (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P) :=
  componentAmbientModuleBaseCoefficientScalarTower k E P

variable [FiniteDimensional k E] (I : Submodule k (⋀[k]^2 E))

local instance (priority := 2000) canonicalBaseSourceGroup :
    AddCommGroup (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  originalModuleAddCommGroup k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

local instance (priority := 2000) canonicalBaseSourceMonoid :
    AddCommMonoid (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  (canonicalBaseSourceGroup k E I).toAddCommMonoid

local instance (priority := 2000) canonicalBaseSourceBaseCoefficients :
    _root_.Module k (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  originalModuleScalarModule k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

@[implicit_reducible] private def canonicalBaseOriginalCoefficients
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) :=
  inferInstance

local instance (priority := 2000) canonicalBaseSourceCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E))
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  canonicalBaseOriginalCoefficients k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

local instance canonicalBaseSourceTower :
    IsScalarTower k (S k (_root_.Module.Dual k E))
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  originalKoszulBaseCoefficientTower k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

/-- Native base-field scalar restriction of the actual canonical map. -/
def isotropicComponentAmbientBaseMap
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I) :=
  (isotropicComponentAmbientModuleMap k E P I hiso).restrictScalars k

/-- This is the already constructed original canonical map as a function,
so its true homogeneous maps apply to the same original map. -/
theorem isotropicComponentAmbientBaseMap_apply
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I)
    (z : Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :
    isotropicComponentAmbientBaseMap k E P I hiso z =
      isotropicComponentModuleMap k E I P hiso z := rfl

end ChenRanks.Koszul
