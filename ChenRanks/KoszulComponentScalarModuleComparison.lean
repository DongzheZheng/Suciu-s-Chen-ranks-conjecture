import ChenRanks.KoszulComponentLocalAlgebras
import ChenRanks.LocalizedScalarModuleComparison
import ChenRanks.KoszulOriginalModuleStructures
import Mathlib.Algebra.Algebra.RestrictScalars

/-!
# The literal component module under actual scalar base change

The component is the original zero-relation Koszul quotient. Its
ambient scalar action is its native component action restricted through
the actual symmetric projection. `RestrictScalars` is mathlib's genuine
scalar-restriction type synonym; it does not change the underlying
quotient. Both local rings remain the already constructed actual native
evaluation-prime localizations.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks.Koszul

attribute [local instance] RestrictScalars.moduleOrig

variable (k : Type*) [Field k]

local instance componentComparisonOriginalAddCommGroup
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : AddCommGroup (Module k V K) :=
  originalModuleAddCommGroup k V K

@[implicit_reducible] private def componentComparisonOriginalCoefficients
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) :=
  inferInstance

local instance componentComparisonOriginalCoefficientModule
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) :=
  componentComparisonOriginalCoefficients k V K

variable (E : Type*) [AddCommGroup E] [_root_.Module k E]
variable (P : Submodule k E)

local instance componentComparisonProjectionAlgebra :
    Algebra (S k (_root_.Module.Dual k E)) (S k (_root_.Module.Dual k P)) :=
  componentSymmetricProjectionAlgebra k E P

local instance componentComparisonAmbientAlgebra (eP : P) :
    Algebra (S k (_root_.Module.Dual k E)) (componentPointLocalRing k E P eP) :=
  componentPointAmbientCoefficientAlgebra k E P eP

local instance componentComparisonLocalAlgebra (eP : P) :
    Algebra (ambientComponentPointLocalRing k E P eP) (componentPointLocalRing k E P eP) :=
  componentPointLocalProjectionAlgebra k E P eP

local instance (priority := 2000) componentComparisonAmbientScalarAction (eP : P) :
    SMul (S k (_root_.Module.Dual k E)) (componentPointLocalRing k E P eP) :=
  (componentPointAmbientCoefficientAlgebra k E P eP).toSMul

local instance componentComparisonComponentTower (eP : P) :
    IsScalarTower (S k (_root_.Module.Dual k E)) (S k (_root_.Module.Dual k P))
      (componentPointLocalRing k E P eP) :=
  componentPointAmbientComponentScalarTower k E P eP

local instance componentComparisonLocalTower (eP : P) :
    IsScalarTower (S k (_root_.Module.Dual k E)) (ambientComponentPointLocalRing k E P eP)
      (componentPointLocalRing k E P eP) :=
  componentPointAmbientLocalScalarTower k E P eP

/-- The original zero-relation component quotient with its true ambient
action restricted through the actual symmetric projection. -/
abbrev ComponentAmbientModule :=
  RestrictScalars (S k (_root_.Module.Dual k E)) (S k (_root_.Module.Dual k P))
    (Module k (_root_.Module.Dual k P) ⊥)

local instance (priority := 2000) componentComparisonZeroOriginalAddCommMonoid :
    AddCommMonoid (Module k (_root_.Module.Dual k P) ⊥) :=
  (originalModuleAddCommGroup k (_root_.Module.Dual k P) ⊥).toAddCommMonoid

local instance (priority := 2000) componentComparisonZeroOriginalCoefficients :
    _root_.Module (S k (_root_.Module.Dual k P))
      (Module k (_root_.Module.Dual k P) ⊥) :=
  componentComparisonOriginalCoefficients k (_root_.Module.Dual k P) ⊥

/-- Cached native additive parent of the same original component quotient. -/
@[implicit_reducible] def componentAmbientModuleAddCommGroup :
    AddCommGroup (ComponentAmbientModule k E P) :=
  originalModuleAddCommGroup k (_root_.Module.Dual k P) ⊥

/-- The explicit native parent avoids repeating quotient inference. -/
@[implicit_reducible] def componentAmbientModuleAddCommMonoid :
    AddCommMonoid (ComponentAmbientModule k E P) :=
  (componentAmbientModuleAddCommGroup k E P).toAddCommMonoid

local instance (priority := 2000) componentComparisonRestrictedAddCommGroup :
    AddCommGroup (ComponentAmbientModule k E P) :=
  componentAmbientModuleAddCommGroup k E P

local instance (priority := 2000) componentComparisonRestrictedAddCommMonoid :
    AddCommMonoid (ComponentAmbientModule k E P) :=
  componentAmbientModuleAddCommMonoid k E P

/-- The same native component action on the genuine restriction synonym. -/
@[implicit_reducible] def componentAmbientModuleOriginalCoefficients :
    _root_.Module (S k (_root_.Module.Dual k P)) (ComponentAmbientModule k E P) :=
  componentComparisonOriginalCoefficients k (_root_.Module.Dual k P) ⊥

local instance (priority := 2000) componentComparisonRestrictedOriginalCoefficients :
    _root_.Module (S k (_root_.Module.Dual k P)) (ComponentAmbientModule k E P) :=
  componentAmbientModuleOriginalCoefficients k E P

/-- The explicit native parent of the same original component action. -/
@[implicit_reducible] def componentAmbientModuleOriginalScalarAction :
    SMul (S k (_root_.Module.Dual k P)) (ComponentAmbientModule k E P) :=
  (componentAmbientModuleOriginalCoefficients k E P).toSMul

local instance (priority := 2000) componentComparisonRestrictedOriginalScalarAction :
    SMul (S k (_root_.Module.Dual k P)) (ComponentAmbientModule k E P) :=
  componentAmbientModuleOriginalScalarAction k E P

/-- Native restriction of the original action through the actual π. -/
@[implicit_reducible] def componentAmbientModuleCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P) :=
  _root_.Module.restrictScalars (S k (_root_.Module.Dual k E))
    (S k (_root_.Module.Dual k P)) (Module k (_root_.Module.Dual k P) ⊥)

local instance (priority := 2000) componentComparisonRestrictedCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P) :=
  componentAmbientModuleCoefficients k E P

/-- The explicit native parent of restriction through the actual π. -/
@[implicit_reducible] def componentAmbientModuleScalarAction :
    SMul (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P) :=
  (componentAmbientModuleCoefficients k E P).toSMul

local instance (priority := 2000) componentComparisonRestrictedScalarAction :
    SMul (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P) :=
  componentAmbientModuleScalarAction k E P

/-- The native scalar-restriction tower, with no new compatibility input. -/
@[implicit_reducible] def componentAmbientModuleScalarTower :
    IsScalarTower (S k (_root_.Module.Dual k E)) (S k (_root_.Module.Dual k P))
      (ComponentAmbientModule k E P) :=
  IsScalarTower.restrictScalars (S k (_root_.Module.Dual k E))
    (S k (_root_.Module.Dual k P)) (Module k (_root_.Module.Dual k P) ⊥)

local instance componentComparisonRestrictedScalarTower :
    IsScalarTower (S k (_root_.Module.Dual k E)) (S k (_root_.Module.Dual k P))
      (ComponentAmbientModule k E P) :=
  componentAmbientModuleScalarTower k E P

local instance componentComparisonMappedLocalization (eP : P) :
    IsLocalization
      ((pointEvaluationKernel k (_root_.Module.Dual k E)
        (pointOfVector k E (eP : E))).primeCompl.map
          (algebraMap (S k (_root_.Module.Dual k E)) (S k (_root_.Module.Dual k P))))
      (componentPointLocalRing k E P eP) :=
  componentTarget_mappedDenominators_isLocalization k E P eP

/-- The actual component scalar-localization comparison is the native
pushout cancellation equivalence, with its native return type inferred
once on these actual data. Neither localization is a newly defined
replacement for the desired module. -/
def componentCanonicalScalarLocalizationComparison (eP : P) :=
  ChenRanks.localizedScalarModuleComparison
    (S k (_root_.Module.Dual k E)) (ambientComponentPointLocalRing k E P eP)
    (S k (_root_.Module.Dual k P)) (componentPointLocalRing k E P eP)
    (pointEvaluationKernel k (_root_.Module.Dual k E)
      (pointOfVector k E (eP : E))).primeCompl
    (ComponentAmbientModule k E P)

/-- On actual pure tensors, the comparison's inverse is the actual
localized coefficient projection and the same original component class. -/
theorem componentCanonicalScalarLocalizationComparison_symm_tmul (eP : P)
    (r : ambientComponentPointLocalRing k E P eP) (n : ComponentAmbientModule k E P) :
    (componentCanonicalScalarLocalizationComparison k E P eP).symm (r ⊗ₜ[_] n) =
      componentLocalScalarProjection k E P eP r ⊗ₜ[_] n := by
  exact ChenRanks.localizedScalarModuleComparison_symm_tmul
    (S k (_root_.Module.Dual k E)) (ambientComponentPointLocalRing k E P eP)
    (S k (_root_.Module.Dual k P)) (componentPointLocalRing k E P eP)
    (pointEvaluationKernel k (_root_.Module.Dual k E)
      (pointOfVector k E (eP : E))).primeCompl
    (ComponentAmbientModule k E P) r n

end ChenRanks.Koszul
