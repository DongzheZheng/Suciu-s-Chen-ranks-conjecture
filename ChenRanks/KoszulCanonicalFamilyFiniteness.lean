import ChenRanks.KoszulCanonicalFamilyObjects
import ChenRanks.KoszulPolynomialHomotopy
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finiteness of the actual canonical Koszul family and its defects

Every target factor is the original zero-relation Koszul quotient with
the actual ambient action restricted through the true dual projection.
The projection is genuinely surjective, so its coefficient ring is a
finite module over the ambient coefficient ring. The proved original
Koszul finiteness then gives ambient finiteness of each actual factor.
Separation supplies finiteness of the actual maximal-isotropic index
type; native finite products give finiteness of the same family target.

The actual coefficient ring is Noetherian by its true finite-basis
polynomial equivalence. Consequently the genuine kernel and cokernel
of the original family map are finite. No finite-generation, component
enumeration, support, eventual-isomorphism, or effective-bound premise
is supplied.
-/

noncomputable section

namespace ChenRanks.Koszul

open ChenRanks.Resonance

attribute [local instance] RestrictScalars.moduleOrig

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E]
variable (P : Submodule k E)

@[implicit_reducible] private def familyFiniteCycleAddCommGroup
    (V : Type*) [AddCommGroup V] [_root_.Module k V] :
    AddCommGroup (LinearMap.ker (delta1 k V)) := inferInstance

local instance (priority := 2000) familyFiniteOriginalCycleGroups
    (V : Type*) [AddCommGroup V] [_root_.Module k V] :
    AddCommGroup (LinearMap.ker (delta1 k V)) :=
  familyFiniteCycleAddCommGroup k V

local instance (priority := 2000) familyFiniteOriginalModuleGroups
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : AddCommGroup (Module k V K) :=
  originalModuleAddCommGroup k V K

local instance familyFiniteProjectionAlgebra :
    Algebra (S k (_root_.Module.Dual k E)) (S k (_root_.Module.Dual k P)) :=
  componentSymmetricProjectionAlgebra k E P

local instance (priority := 2000) familyFiniteComponentGroup :
    AddCommGroup (ComponentAmbientModule k E P) :=
  componentAmbientModuleAddCommGroup k E P

local instance (priority := 2000) familyFiniteComponentMonoid :
    AddCommMonoid (ComponentAmbientModule k E P) :=
  componentAmbientModuleAddCommMonoid k E P

local instance (priority := 2000) familyFiniteComponentOriginalCoefficients :
    _root_.Module (S k (_root_.Module.Dual k P)) (ComponentAmbientModule k E P) :=
  componentAmbientModuleOriginalCoefficients k E P

local instance (priority := 2000) familyFiniteComponentOriginalScalarAction :
    SMul (S k (_root_.Module.Dual k P)) (ComponentAmbientModule k E P) :=
  componentAmbientModuleOriginalScalarAction k E P

local instance (priority := 2000) familyFiniteComponentCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P) :=
  componentAmbientModuleCoefficients k E P

local instance (priority := 2000) familyFiniteComponentScalarAction :
    SMul (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P) :=
  componentAmbientModuleScalarAction k E P

local instance familyFiniteComponentScalarTower :
    IsScalarTower (S k (_root_.Module.Dual k E)) (S k (_root_.Module.Dual k P))
      (ComponentAmbientModule k E P) :=
  componentAmbientModuleScalarTower k E P

/-- True surjectivity of the coefficient projection makes the genuine
component coefficient ring finite over the original ambient ring. -/
theorem componentCoefficientRing_ambientFinite :
    _root_.Module.Finite (S k (_root_.Module.Dual k E))
      (S k (_root_.Module.Dual k P)) := by
  apply _root_.Module.Finite.of_surjective
    (Algebra.linearMap (S k (_root_.Module.Dual k E)) (S k (_root_.Module.Dual k P)))
  exact componentSymmetricProjection_surjective k E P

variable [FiniteDimensional k E] [CharZero k]

/-- The actual original zero-relation component is finite for its true
ambient action, derived from the proved original Koszul finiteness. -/
theorem componentAmbientModule_finite :
    _root_.Module.Finite (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P) := by
  letI := componentCoefficientRing_ambientFinite k E P
  letI : _root_.Module.Finite (S k (_root_.Module.Dual k P))
      (ComponentAmbientModule k E P) :=
    actual_koszulModule_finite k (_root_.Module.Dual k P) ⊥
  exact _root_.Module.Finite.trans (S k (_root_.Module.Dual k P))
    (ComponentAmbientModule k E P)

omit [CharZero k] in
/-- The true symmetric coefficient ring is Noetherian, using its actual
finite-basis equivalence with a polynomial ring. -/
theorem canonicalFamilyCoefficientRing_noetherian :
    IsNoetherianRing (S k (_root_.Module.Dual k E)) := by
  let b := _root_.Module.finBasis k (_root_.Module.Dual k E)
  exact isNoetherianRing_of_ringEquiv _
    (SymmetricAlgebra.equivMvPolynomial b).symm.toRingEquiv

variable (I : Submodule k (⋀[k]^2 E))

local instance (priority := 2000) familyFiniteSourceGroup :
    AddCommGroup (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  originalModuleAddCommGroup k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

local instance (priority := 2000) familyFiniteSourceMonoid :
    AddCommMonoid (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  (originalModuleAddCommGroup k (_root_.Module.Dual k E)
    (exteriorAnnihilator k E 2 I)).toAddCommMonoid

@[implicit_reducible] private def familyFiniteOriginalCoefficients
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) :=
  inferInstance

local instance (priority := 2000) familyFiniteSourceCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E))
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  familyFiniteOriginalCoefficients k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

local instance (priority := 2000) familyFiniteSourceScalarAction :
    SMul (S k (_root_.Module.Dual k E))
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  (familyFiniteSourceCoefficients k E I).toSMul

local instance (priority := 2000) familyFiniteGroups :
    (Q : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommGroup (ComponentAmbientModule k E Q.val) :=
  canonicalFamilyComponentAddCommGroups k E I

local instance (priority := 2000) familyFiniteMonoids :
    (Q : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommMonoid (ComponentAmbientModule k E Q.val) :=
  canonicalFamilyComponentAddCommMonoids k E I

local instance (priority := 2000) familyFiniteCoefficients :
    (Q : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      _root_.Module (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E Q.val) :=
  canonicalFamilyComponentCoefficients k E I

local instance (priority := 2000) familyFiniteScalarActions :
    (Q : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      SMul (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E Q.val) :=
  canonicalFamilyComponentScalarActions k E I

@[implicit_reducible] private def finitePiGroup
    {ι : Type*} (A : ι → Type*) [∀ i, AddCommGroup (A i)] :
    AddCommGroup (∀ i, A i) := inferInstance

@[implicit_reducible] private def finitePiModule
    (R : Type*) [Semiring R] {ι : Type*} (A : ι → Type*)
    [∀ i, AddCommMonoid (A i)] [∀ i, _root_.Module R (A i)] :
    _root_.Module R (∀ i, A i) := inferInstance

local instance (priority := 2000) familyFiniteTargetGroup :
    AddCommGroup (CanonicalFamilyModule k E I) :=
  finitePiGroup (fun Q : OriginalMaximalIsotropicFamily (cupQuotient I) =>
    ComponentAmbientModule k E Q.val)

local instance (priority := 2000) familyFiniteTargetMonoid :
    AddCommMonoid (CanonicalFamilyModule k E I) :=
  (familyFiniteTargetGroup k E I).toAddCommMonoid

local instance (priority := 2000) familyFiniteTargetCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E)) (CanonicalFamilyModule k E I) :=
  finitePiModule (S k (_root_.Module.Dual k E))
    (fun Q : OriginalMaximalIsotropicFamily (cupQuotient I) =>
      ComponentAmbientModule k E Q.val)

local instance (priority := 2000) familyFiniteTargetScalarAction :
    SMul (S k (_root_.Module.Dual k E)) (CanonicalFamilyModule k E I) :=
  (familyFiniteTargetCoefficients k E I).toSMul

@[implicit_reducible] private def finiteQuotientGroup
    (R M : Type*) [Ring R] [AddCommGroup M] [_root_.Module R M]
    (Q : Submodule R M) : AddCommGroup (M ⧸ Q) := inferInstance

@[implicit_reducible] private def finiteQuotientModule
    (R M : Type*) [Ring R] [AddCommGroup M] [_root_.Module R M]
    (Q : Submodule R M) : _root_.Module R (M ⧸ Q) := inferInstance

local instance (priority := 2000) familyFiniteCokernelGroup :
    AddCommGroup ((CanonicalFamilyModule k E I) ⧸
      LinearMap.range (originalCanonicalFamilyModuleMap k E I)) :=
  finiteQuotientGroup (S k (_root_.Module.Dual k E)) (CanonicalFamilyModule k E I)
    (LinearMap.range (originalCanonicalFamilyModuleMap k E I))

local instance (priority := 2000) familyFiniteCokernelMonoid :
    AddCommMonoid ((CanonicalFamilyModule k E I) ⧸
      LinearMap.range (originalCanonicalFamilyModuleMap k E I)) :=
  (familyFiniteCokernelGroup k E I).toAddCommMonoid

local instance (priority := 2000) familyFiniteCokernelCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E))
      ((CanonicalFamilyModule k E I) ⧸
        LinearMap.range (originalCanonicalFamilyModuleMap k E I)) :=
  finiteQuotientModule (S k (_root_.Module.Dual k E)) (CanonicalFamilyModule k E I)
    (LinearMap.range (originalCanonicalFamilyModuleMap k E I))

variable (hsep : ∀ Q : Submodule k E,
  IsMaximalIsotropic (relationWedge (cupQuotient I)) Q →
  2 ≤ _root_.Module.finrank k Q → mixedExterior Q ⊓ I = pureExterior Q)

include hsep

/-- The actual canonical product over every original maximal isotropic
subspace of dimension at least two is finite over the original ring. -/
theorem originalCanonicalFamilyModule_finite :
    _root_.Module.Finite (S k (_root_.Module.Dual k E)) (CanonicalFamilyModule k E I) := by
  letI := canonicalFamilyFintype k E I hsep
  letI : (Q : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      _root_.Module.Finite (S k (_root_.Module.Dual k E))
        (ComponentAmbientModule k E Q.val) :=
    fun Q => componentAmbientModule_finite k E Q.val
  infer_instance

omit hsep in
/-- The original source module is finite for its genuine quadratic
annihilator relation subspace. -/
theorem originalCanonicalFamilySource_finite :
    _root_.Module.Finite (S k (_root_.Module.Dual k E))
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  actual_koszulModule_finite k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

omit hsep in
/-- The kernel is the actual kernel of the original canonical map. Its
finiteness follows from Noetherianity of the genuine original source. -/
theorem originalCanonicalFamilyKernel_finite :
    _root_.Module.Finite (S k (_root_.Module.Dual k E))
      (LinearMap.ker (originalCanonicalFamilyModuleMap k E I)) := by
  letI := canonicalFamilyCoefficientRing_noetherian k E
  letI := originalCanonicalFamilySource_finite k E I
  letI : IsNoetherian (S k (_root_.Module.Dual k E))
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  apply _root_.Module.Finite.of_fg
  exact (isNoetherian_def.mp (inferInstance : IsNoetherian
    (S k (_root_.Module.Dual k E))
    (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)))) _

/-- The cokernel is the actual quotient by the range of the same
original family map, and is finite by actual target finiteness. -/
theorem originalCanonicalFamilyCokernel_finite :
    _root_.Module.Finite (S k (_root_.Module.Dual k E))
      ((CanonicalFamilyModule k E I) ⧸ LinearMap.range (originalCanonicalFamilyModuleMap k E I)) := by
  letI := originalCanonicalFamilyModule_finite k E I hsep
  exact _root_.Module.Finite.of_surjective
    (LinearMap.range (originalCanonicalFamilyModuleMap k E I)).mkQ
    (LinearMap.range (originalCanonicalFamilyModuleMap k E I)).mkQ_surjective

end ChenRanks.Koszul
