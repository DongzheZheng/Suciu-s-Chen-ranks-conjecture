import ChenRanks.KoszulCanonicalComponentLocalization
import ChenRanks.MaximalIsotropicFiniteFamily
import ChenRanks.ResonanceObjects

/-!
# The original canonical map to the genuine maximal-isotropic family

The index subtype consists of all original maximal isotropic subspaces
of the actual cup quotient, of dimension at least two. Its finite
enumeration is derived from actual separation. Each target factor is
the same original zero-relation Koszul quotient with its genuine
restricted ambient scalar action. The family map is native
`LinearMap.pi`, and its localization is native `LinearMap.baseChange`.
No component list, finite-family premise, decomposition, or Chen-rank
formula is input or encoded in these objects.
-/

noncomputable section

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))

local instance canonicalFamilySourceAddCommGroup :
    AddCommGroup (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  originalModuleAddCommGroup k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

local instance (priority := 2000) canonicalFamilySourceAddCommMonoid :
    AddCommMonoid (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  (originalModuleAddCommGroup k (_root_.Module.Dual k E)
    (exteriorAnnihilator k E 2 I)).toAddCommMonoid

@[implicit_reducible] private def canonicalFamilyOriginalCoefficients
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) :=
  inferInstance

local instance canonicalFamilySourceCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E))
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  canonicalFamilyOriginalCoefficients k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

local instance (priority := 2000) canonicalFamilySourceScalarAction :
    SMul (S k (_root_.Module.Dual k E))
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  (canonicalFamilySourceCoefficients k E I).toSMul

/-- The genuine additive parents are the original quotient parents. -/
@[implicit_reducible] def canonicalFamilyComponentAddCommGroups :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommGroup (ComponentAmbientModule k E P.val) :=
  fun P => componentAmbientModuleAddCommGroup k E P.val

local instance canonicalFamilyGroups :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommGroup (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentAddCommGroups k E I

/-- The explicit native parents avoid repeating deep quotient inference. -/
@[implicit_reducible] def canonicalFamilyComponentAddCommMonoids :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommMonoid (ComponentAmbientModule k E P.val) :=
  fun P => componentAmbientModuleAddCommMonoid k E P.val

local instance (priority := 2000) canonicalFamilyMonoids :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommMonoid (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentAddCommMonoids k E I

/-- Every ambient action is the actual original component action
restricted through the actual component symmetric projection. -/
@[implicit_reducible] def canonicalFamilyComponentCoefficients :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      _root_.Module (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P.val) :=
  fun P => componentAmbientModuleCoefficients k E P.val

local instance (priority := 2000) canonicalFamilyCoefficients :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      _root_.Module (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentCoefficients k E I

/-- Explicit native scalar parents of those same restricted actions. -/
@[implicit_reducible] def canonicalFamilyComponentScalarActions :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      SMul (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P.val) :=
  fun P => componentAmbientModuleScalarAction k E P.val

local instance (priority := 2000) canonicalFamilyScalarActions :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      SMul (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentScalarActions k E I

omit [FiniteDimensional k E] in
/-- Actual maximal isotropy supplies the true original quadratic
containment for each genuine canonical component map. -/
theorem canonicalFamily_component_isotropy
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) :
    LinearMap.range (exteriorPower.map 2 P.val.subtype) ≤ I :=
  (isCupIsotropic_iff_isIsotropic I P.val).mpr P.property.1.1

/-- The target is the actual product over the true original family. -/
abbrev CanonicalFamilyModule :=
  (P : OriginalMaximalIsotropicFamily (cupQuotient I)) → ComponentAmbientModule k E P.val

/-- Native product of the actual original canonical component maps. -/
def originalCanonicalFamilyModuleMap :=
  LinearMap.pi (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
    isotropicComponentAmbientModuleMap k E P.val I (canonicalFamily_component_isotropy k E I P))

/-- Native localization of that same original family map. -/
def originalCanonicalFamilyLocalization (e : E) :=
  (originalCanonicalFamilyModuleMap k E I).baseChange
    (PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e))

/-- The actual family is finite by actual separation, rather than by a
supplied component count or enumeration. -/
@[implicit_reducible] def canonicalFamilyFintype [CharZero k]
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
      2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P) :
    Fintype (OriginalMaximalIsotropicFamily (cupQuotient I)) :=
  originalMaximalIsotropicFamilyFintype (cupQuotient I) (fun P hP hdim => by
    simpa only [cupQuotient, Submodule.ker_mkQ] using hsep P hP hdim)

end ChenRanks.Koszul
