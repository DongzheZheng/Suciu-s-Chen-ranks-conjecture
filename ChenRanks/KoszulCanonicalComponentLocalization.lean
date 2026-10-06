import ChenRanks.KoszulComponentScalarModuleComparison
import ChenRanks.KoszulIsotropicComponentLocalInverse

/-!
# Localization of the original canonical component map

The target is the original zero-relation component quotient, with its
ambient action genuinely restricted through dual restriction. The map
is therefore an actual ambient-linear map; its localization is native
`LinearMap.baseChange`. The scalar cancellation diagram identifies this
literal base change with the independently proved map between the two
literal evaluation-prime tensor localizations.

The result remains a statement at an affine evaluation maximal prime.
It does not identify an evaluation prime with a homogeneous line prime,
or supply an eventual-isomorphism theorem or an effective degree bound.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks.Koszul

attribute [local instance] RestrictScalars.moduleOrig

private theorem canonicalBaseChange_diagram
    (S R M N Q : Type*) [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q]
    [_root_.Module S M] [_root_.Module S N]
    (f : M →ₗ[S] N) (e : R ⊗[S] N →+ Q) (g : R ⊗[S] M →+ Q)
    (hpure : ∀ r m, e (r ⊗ₜ[S] f m) = g (r ⊗ₜ[S] m))
    (z : R ⊗[S] M) : e (f.baseChange R z) = g z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add z t hz ht => rw [map_add, map_add, map_add, hz, ht]
  | tmul r m => rw [LinearMap.baseChange_tmul, hpure]

private theorem bijective_of_equiv_composite
    (M N Q : Type*) (e : N ≃ Q) (f : M → N) (g : M → Q)
    (hcomp : ∀ z, e (f z) = g z) (hg : Function.Bijective g) :
    Function.Bijective f := by
  constructor
  · intro z t hzt
    apply hg.injective
    rw [← hcomp z, ← hcomp t, hzt]
  · intro y
    obtain ⟨z, hz⟩ := hg.surjective (e y)
    refine ⟨z, e.injective ?_⟩
    rw [hcomp z, hz]

variable (k : Type*) [Field k]

local instance canonicalLocalizationOriginalAddCommGroup
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : AddCommGroup (Module k V K) :=
  originalModuleAddCommGroup k V K

@[implicit_reducible] private def canonicalLocalizationOriginalCoefficients
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) :=
  inferInstance

local instance canonicalLocalizationOriginalCoefficientModule
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) :=
  canonicalLocalizationOriginalCoefficients k V K

variable (E : Type*) [AddCommGroup E] [_root_.Module k E]
variable (P : Submodule k E) (I : Submodule k (⋀[k]^2 E))

local instance canonicalLocalizationProjectionAlgebra :
    Algebra (S k (_root_.Module.Dual k E)) (S k (_root_.Module.Dual k P)) :=
  componentSymmetricProjectionAlgebra k E P

local instance (priority := 2000) canonicalLocalizationComponentAddCommMonoid :
    AddCommMonoid (Module k (_root_.Module.Dual k P) ⊥) :=
  (originalModuleAddCommGroup k (_root_.Module.Dual k P) ⊥).toAddCommMonoid

local instance (priority := 2000) canonicalLocalizationComponentCoefficients :
    _root_.Module (S k (_root_.Module.Dual k P))
      (Module k (_root_.Module.Dual k P) ⊥) :=
  canonicalLocalizationOriginalCoefficients k (_root_.Module.Dual k P) ⊥

local instance (priority := 2000) canonicalLocalizationRestrictedAddCommGroup :
    AddCommGroup (ComponentAmbientModule k E P) :=
  componentAmbientModuleAddCommGroup k E P

local instance (priority := 2000) canonicalLocalizationRestrictedAddCommMonoid :
    AddCommMonoid (ComponentAmbientModule k E P) :=
  componentAmbientModuleAddCommMonoid k E P

local instance (priority := 2000) canonicalLocalizationRestrictedOriginalCoefficients :
    _root_.Module (S k (_root_.Module.Dual k P)) (ComponentAmbientModule k E P) :=
  componentAmbientModuleOriginalCoefficients k E P

local instance (priority := 2000) canonicalLocalizationRestrictedCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P) :=
  componentAmbientModuleCoefficients k E P

local instance (priority := 2000) canonicalLocalizationRestrictedOriginalScalarAction :
    SMul (S k (_root_.Module.Dual k P)) (ComponentAmbientModule k E P) :=
  componentAmbientModuleOriginalScalarAction k E P

local instance (priority := 2000) canonicalLocalizationRestrictedScalarAction :
    SMul (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P) :=
  componentAmbientModuleScalarAction k E P

local instance canonicalLocalizationLocalProjectionAlgebra (eP : P) :
    Algebra (ambientComponentPointLocalRing k E P eP) (componentPointLocalRing k E P eP) :=
  componentPointLocalProjectionAlgebra k E P eP

@[implicit_reducible] private def canonicalLocalizationTensorTargetModule
    (T R A N : Type*) [CommRing T] [CommRing R] [CommRing A]
    [Algebra T A] [Algebra R A] [AddCommGroup N] [_root_.Module T N] :
    _root_.Module R (A ⊗[T] N) :=
  inferInstance

-- This is the native left tensor action induced by the actual localized
-- coefficient projection. Cache its parent once on generic tensor data.
local instance (priority := 2000) canonicalLocalizationLocalizedTargetModule (eP : P) :
    _root_.Module (ambientComponentPointLocalRing k E P eP)
      (componentPointLocalRing k E P eP ⊗[S k (_root_.Module.Dual k P)]
        ComponentAmbientModule k E P) :=
  canonicalLocalizationTensorTargetModule
    (S k (_root_.Module.Dual k P)) (ambientComponentPointLocalRing k E P eP)
    (componentPointLocalRing k E P eP) (ComponentAmbientModule k E P)

local instance (priority := 2000) canonicalLocalizationLocalizedTargetScalarAction (eP : P) :
    SMul (ambientComponentPointLocalRing k E P eP)
      (componentPointLocalRing k E P eP ⊗[S k (_root_.Module.Dual k P)]
        ComponentAmbientModule k E P) :=
  (canonicalLocalizationLocalizedTargetModule k E P eP).toSMul

variable [FiniteDimensional k E]

/-- The actual original canonical component map is ambient-linear
after genuine scalar restriction through its actual symmetric map. -/
def isotropicComponentAmbientModuleMap
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I) :=
  (show Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I) →ₗ[
      S k (_root_.Module.Dual k E)] ComponentAmbientModule k E P from
    { toFun := isotropicComponentModuleSemilinearMap k E P I hiso
      map_add' := (isotropicComponentModuleSemilinearMap k E P I hiso).map_add
      map_smul' := fun s z => by
        change isotropicComponentModuleSemilinearMap k E P I hiso (s • z) =
          componentSymmetricProjection k E P s •
            isotropicComponentModuleSemilinearMap k E P I hiso z
        exact (isotropicComponentModuleSemilinearMap k E P I hiso).map_smul' s z })

/-- This is the native scalar extension of the same original canonical
map, rather than a separately defined replacement for its localization. -/
def isotropicComponentCanonicalLocalization (eP : P)
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I) :=
  (isotropicComponentAmbientModuleMap k E P I hiso).baseChange
    (ambientComponentPointLocalRing k E P eP)

@[simp] theorem isotropicComponentCanonicalLocalization_tmul (eP : P)
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I)
    (r : ambientComponentPointLocalRing k E P eP)
    (z : Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :
    isotropicComponentCanonicalLocalization k E P I eP hiso
        (r ⊗ₜ[S k (_root_.Module.Dual k E)] z) =
      r ⊗ₜ[S k (_root_.Module.Dual k E)]
        isotropicComponentAmbientModuleMap k E P I hiso z := rfl

/-- The native base-change diagram commutes on the entire original
tensor product, as derived from its genuine pure-tensor formula. -/
theorem isotropicComponentCanonicalLocalization_diagram (eP : P)
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I)
    (z : componentPointOriginalModule k E P I eP) :
    (componentCanonicalScalarLocalizationComparison k E P eP).symm
        (isotropicComponentCanonicalLocalization k E P I eP hiso z) =
      isotropicComponentLocalizedMap k E P I eP hiso z := by
  apply canonicalBaseChange_diagram
    (S k (_root_.Module.Dual k E)) (ambientComponentPointLocalRing k E P eP)
    (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I))
    (ComponentAmbientModule k E P) (componentPointZeroRelationModule k E P eP)
    (isotropicComponentAmbientModuleMap k E P I hiso)
    (componentCanonicalScalarLocalizationComparison k E P eP).symm.toAddEquiv.toAddMonoidHom
    (isotropicComponentLocalizedMap k E P I eP hiso).toAddMonoidHom
    ?_ z
  intro r m
  change (componentCanonicalScalarLocalizationComparison k E P eP).symm
      (r ⊗ₜ[S k (_root_.Module.Dual k E)]
        isotropicComponentAmbientModuleMap k E P I hiso m) =
    isotropicComponentLocalizedMap k E P I eP hiso
      (r ⊗ₜ[S k (_root_.Module.Dual k E)] m)
  rw [componentCanonicalScalarLocalizationComparison_symm_tmul k E P eP r
    (isotropicComponentAmbientModuleMap k E P I hiso m)]
  rfl

/-- Actual separation proves bijectivity of the native localization of
the original canonical component map at every actual nonzero point of
the component. No localized-isomorphism hypothesis is supplied. -/
theorem isotropicComponentCanonicalLocalization_bijective_of_nonzero [CharZero k]
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I)
    (hsep : I ⊓ mixedExterior P ≤ pureExterior P) (eP : P) (heP : eP ≠ 0) :
    Function.Bijective (isotropicComponentCanonicalLocalization k E P I eP hiso) := by
  exact bijective_of_equiv_composite _ _ _
    (componentCanonicalScalarLocalizationComparison k E P eP).symm.toEquiv
    (isotropicComponentCanonicalLocalization k E P I eP hiso)
    (isotropicComponentLocalizedMap k E P I eP hiso)
    (isotropicComponentCanonicalLocalization_diagram k E P I eP hiso)
    (isotropicComponentLocalizedMap_bijective_of_nonzero k E P I hiso hsep eP heP)

end ChenRanks.Koszul
