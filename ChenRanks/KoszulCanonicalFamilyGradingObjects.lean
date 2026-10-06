import ChenRanks.KoszulCanonicalFamilyBaseScalars
import ChenRanks.KoszulIsotropicComponentMaps

/-!
# Genuine original canonical family grading objects and native parents

The source degrees are the already constructed actual homogeneous
quotients. Each true maximal-isotropic target uses those same original
zero-relation degrees in a genuine finite vector-space basis. This file
constructs the original base-linear map, actual degreewise maps and
cached native scalar parents. The separate recomposition and diagram
files derive the genuine target reconstruction and full original-map
diagram. No eventual or effective bijectivity assertion is made here.
-/

noncomputable section

open scoped DirectSum

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))

@[implicit_reducible] private def gradingCycleDegreeGroup
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} (c : _root_.Module.Basis τ k V) (r : ℕ) :
    AddCommGroup (cycleDegree k V c r) := inferInstance

local instance (priority := 2000) gradingGenericCycleDegreeGroups
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} (c : _root_.Module.Basis τ k V) (r : ℕ) :
    AddCommGroup (cycleDegree k V c r) := gradingCycleDegreeGroup k V c r

@[implicit_reducible] private def gradingHomogeneousGroup
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) :
    AddCommGroup (homogeneousModule k V c K r) := inferInstance

local instance (priority := 2000) gradingGenericHomogeneousGroups
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) :
    AddCommGroup (homogeneousModule k V c K r) := gradingHomogeneousGroup k V c K r

local instance (priority := 2000) gradingGenericHomogeneousMonoids
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) :
    AddCommMonoid (homogeneousModule k V c K r) :=
  (gradingHomogeneousGroup k V c K r).toAddCommMonoid

@[implicit_reducible] private def gradingHomogeneousModule
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) :
    _root_.Module k (homogeneousModule k V c K r) := inferInstance

local instance (priority := 2000) gradingGenericHomogeneousModules
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) :
    _root_.Module k (homogeneousModule k V c K r) := gradingHomogeneousModule k V c K r

local instance (priority := 2000) familyGradingGroups :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommGroup (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentAddCommGroups k E I

local instance (priority := 2000) familyGradingMonoids :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommMonoid (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentAddCommMonoids k E I

local instance (priority := 2000) familyGradingCoefficients :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      _root_.Module (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentCoefficients k E I

local instance (priority := 2000) familyGradingScalarActions :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      SMul (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentScalarActions k E I

/-- Every actual component keeps its original base-field module. -/
@[implicit_reducible] def canonicalFamilyComponentBaseCoefficients :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      _root_.Module k (ComponentAmbientModule k E P.val) :=
  fun P => componentAmbientModuleBaseCoefficients k E P.val

local instance (priority := 2000) familyGradingBaseCoefficients :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      _root_.Module k (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentBaseCoefficients k E I

local instance (priority := 2000) familyGradingBaseScalarActions :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      SMul k (ComponentAmbientModule k E P.val) :=
  fun P => componentAmbientModuleBaseScalarAction k E P.val

local instance familyGradingComponentTowers :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      IsScalarTower k (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P.val) :=
  fun P => componentAmbientModuleBaseCoefficientScalarTower k E P.val

@[implicit_reducible] private def gradingPiGroup
    {ι : Type*} (A : ι → Type*) [∀ i, AddCommGroup (A i)] :
    AddCommGroup (∀ i, A i) := inferInstance

@[implicit_reducible] private def gradingPiModule
    (R : Type*) [Semiring R] {ι : Type*} (A : ι → Type*)
    [∀ i, AddCommMonoid (A i)] [∀ i, _root_.Module R (A i)] :
    _root_.Module R (∀ i, A i) := inferInstance

local instance (priority := 2000) familyGradingTargetGroup :
    AddCommGroup (CanonicalFamilyModule k E I) :=
  gradingPiGroup (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
    ComponentAmbientModule k E P.val)

local instance (priority := 2000) familyGradingTargetMonoid :
    AddCommMonoid (CanonicalFamilyModule k E I) :=
  (familyGradingTargetGroup k E I).toAddCommMonoid

/-- Actual componentwise original base-field action on the same target. -/
@[implicit_reducible] def canonicalFamilyTargetBaseCoefficients :
    _root_.Module k (CanonicalFamilyModule k E I) :=
  gradingPiModule k (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
    ComponentAmbientModule k E P.val)

local instance (priority := 2000) familyGradingTargetBaseCoefficients :
    _root_.Module k (CanonicalFamilyModule k E I) :=
  canonicalFamilyTargetBaseCoefficients k E I

local instance (priority := 2000) familyGradingTargetBaseScalarAction :
    SMul k (CanonicalFamilyModule k E I) :=
  (canonicalFamilyTargetBaseCoefficients k E I).toSMul

local instance (priority := 2000) familyGradingTargetCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E)) (CanonicalFamilyModule k E I) :=
  gradingPiModule (S k (_root_.Module.Dual k E))
    (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
      ComponentAmbientModule k E P.val)

local instance (priority := 2000) familyGradingTargetScalarAction :
    SMul (S k (_root_.Module.Dual k E)) (CanonicalFamilyModule k E I) :=
  (familyGradingTargetCoefficients k E I).toSMul

omit [FiniteDimensional k E] in
/-- The target's original ambient and base actions really form a tower. -/
theorem canonicalFamilyTargetBaseCoefficientScalarTower :
    IsScalarTower k (S k (_root_.Module.Dual k E)) (CanonicalFamilyModule k E I) := by
  infer_instance

local instance familyGradingTargetTower :
    IsScalarTower k (S k (_root_.Module.Dual k E)) (CanonicalFamilyModule k E I) :=
  canonicalFamilyTargetBaseCoefficientScalarTower k E I

local instance (priority := 2000) familyGradingSourceGroup :
    AddCommGroup (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  originalModuleAddCommGroup k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

local instance (priority := 2000) familyGradingSourceMonoid :
    AddCommMonoid (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  (familyGradingSourceGroup k E I).toAddCommMonoid

local instance (priority := 2000) familyGradingSourceBaseCoefficients :
    _root_.Module k (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  originalModuleScalarModule k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

@[implicit_reducible] private def gradingOriginalCoefficients
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) :=
  inferInstance

local instance (priority := 2000) familyGradingSourceCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E))
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  gradingOriginalCoefficients k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

@[implicit_reducible] private def gradingOriginalBaseTower
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : IsScalarTower k (S k V) (Module k V K) :=
  inferInstance

local instance familyGradingSourceTower :
    IsScalarTower k (S k (_root_.Module.Dual k E))
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  gradingOriginalBaseTower k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

/-- Native base restriction of the same original ungraded family map. -/
def originalCanonicalFamilyBaseMap :=
  (originalCanonicalFamilyModuleMap k E I).restrictScalars k

/-- A genuine finite-dimensional basis for each original component. -/
def canonicalFamilyComponentBasis
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) :=
  _root_.Module.finBasis k (_root_.Module.Dual k P.val)

/-- True degreewise product of the original homogeneous component quotients. -/
abbrev CanonicalFamilyHomogeneousDegree (r : ℕ) :=
  (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
    homogeneousModule k (_root_.Module.Dual k P.val)
      (canonicalFamilyComponentBasis k E I P) ⊥ r

local instance (priority := 2000) familyGradingHomogeneousComponentGroups (r : ℕ) :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommGroup (homogeneousModule k (_root_.Module.Dual k P.val)
        (canonicalFamilyComponentBasis k E I P) ⊥ r) :=
  fun P => gradingHomogeneousGroup k (_root_.Module.Dual k P.val)
    (canonicalFamilyComponentBasis k E I P) ⊥ r

local instance (priority := 2000) familyGradingHomogeneousComponentMonoids (r : ℕ) :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommMonoid (homogeneousModule k (_root_.Module.Dual k P.val)
        (canonicalFamilyComponentBasis k E I P) ⊥ r) :=
  fun P => (familyGradingHomogeneousComponentGroups k E I r P).toAddCommMonoid

local instance (priority := 2000) familyGradingHomogeneousComponentModules (r : ℕ) :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      _root_.Module k (homogeneousModule k (_root_.Module.Dual k P.val)
        (canonicalFamilyComponentBasis k E I P) ⊥ r) :=
  fun P => gradingHomogeneousModule k (_root_.Module.Dual k P.val)
    (canonicalFamilyComponentBasis k E I P) ⊥ r

local instance (priority := 2000) familyGradingHomogeneousDegreeGroups (r : ℕ) :
    AddCommGroup (CanonicalFamilyHomogeneousDegree k E I r) :=
  gradingPiGroup (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
    homogeneousModule k (_root_.Module.Dual k P.val)
      (canonicalFamilyComponentBasis k E I P) ⊥ r)

local instance (priority := 2000) familyGradingHomogeneousDegreeMonoids (r : ℕ) :
    AddCommMonoid (CanonicalFamilyHomogeneousDegree k E I r) :=
  (familyGradingHomogeneousDegreeGroups k E I r).toAddCommMonoid

local instance (priority := 2000) familyGradingHomogeneousDegreeModules (r : ℕ) :
    _root_.Module k (CanonicalFamilyHomogeneousDegree k E I r) :=
  gradingPiModule k (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
    homogeneousModule k (_root_.Module.Dual k P.val)
      (canonicalFamilyComponentBasis k E I P) ⊥ r)

variable {ι : Type*} [Fintype ι]
variable (b : _root_.Module.Basis ι k (_root_.Module.Dual k E))

/-- The actual degreewise original canonical family map. -/
def originalCanonicalFamilyHomogeneousMap (r : ℕ) :=
  LinearMap.pi (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
    isotropicComponentHomogeneousMap k E I P.val b
      (canonicalFamilyComponentBasis k E I P)
      (canonicalFamily_component_isotropy k E I P) r)

/-- The previously constructed degree-image equivalence has precisely
the previously constructed original quotient inclusion as its function. -/
theorem homogeneousOriginalDegree_val_eq_inclusion
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ)
    (z : homogeneousModule k V c K r) :
    ((homogeneousModuleEquivOriginalDegree k V c K r z) : Module k V K) =
      degreeQuotientInclusion k V c K r z := by
  refine Submodule.Quotient.induction_on _ z ?_
  intro w
  rfl

/-- Cached original componentwise additive parent of the actual target. -/
@[implicit_reducible] def canonicalFamilyTargetAddCommGroup :
    AddCommGroup (CanonicalFamilyModule k E I) := familyGradingTargetGroup k E I

/-- Cached original componentwise additive-monoid parent. -/
@[implicit_reducible] def canonicalFamilyTargetAddCommMonoid :
    AddCommMonoid (CanonicalFamilyModule k E I) := familyGradingTargetMonoid k E I

/-- Cached unchanged ambient componentwise target action. -/
@[implicit_reducible] def canonicalFamilyTargetCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E)) (CanonicalFamilyModule k E I) :=
  familyGradingTargetCoefficients k E I

/-- Native original homogeneous-quotient additive parent, on genuine data. -/
@[implicit_reducible] def canonicalHomogeneousQuotientAddCommGroup
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) :
    AddCommGroup (homogeneousModule k V c K r) := gradingHomogeneousGroup k V c K r

/-- Native original homogeneous-quotient module, on genuine data. -/
@[implicit_reducible] def canonicalHomogeneousQuotientBaseCoefficients
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) :
    _root_.Module k (homogeneousModule k V c K r) := gradingHomogeneousModule k V c K r

/-- Native additive parent of the actual degreewise family product. -/
@[implicit_reducible] def canonicalFamilyHomogeneousDegreeAddCommGroup (r : ℕ) :
    AddCommGroup (CanonicalFamilyHomogeneousDegree k E I r) :=
  familyGradingHomogeneousDegreeGroups k E I r

/-- Native additive-monoid parent of that same original degreewise product. -/
@[implicit_reducible] def canonicalFamilyHomogeneousDegreeAddCommMonoid (r : ℕ) :
    AddCommMonoid (CanonicalFamilyHomogeneousDegree k E I r) :=
  familyGradingHomogeneousDegreeMonoids k E I r

/-- Native original base-field action of that same degreewise product. -/
@[implicit_reducible] def canonicalFamilyHomogeneousDegreeBaseCoefficients (r : ℕ) :
    _root_.Module k (CanonicalFamilyHomogeneousDegree k E I r) :=
  familyGradingHomogeneousDegreeModules k E I r

end ChenRanks.Koszul
