import ChenRanks.KoszulIsotropicComponentLocalScalars

/-!
# Actual tensor maps between the two literal component localizations

The source is the actual ambient coefficient ring tensored over the
original symmetric algebra with the original Koszul quotient. The target
is the actual component coefficient ring tensored over the component
symmetric algebra with the original zero-relation component quotient.

Both tensor maps use native TensorProduct.map of the actual semilinear
quotient maps and the actual local coefficient maps. The forward map's
right inverse follows from the independently proved true scalar and
original-module right inverses. No local injectivity or identification
with projective sheaf stalks is assumed or asserted here.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

private def localCoefficientSemilinear
    (S T R A : Type*) [CommRing S] [CommRing T] [CommRing R] [CommRing A]
    [Algebra S R] [Algebra T A] (φ : S →+* T) (Φ : R →+* A)
    (hΦ : ∀ s, Φ (algebraMap S R s) = algebraMap T A (φ s)) :
    R →ₛₗ[φ] A where
  toFun := Φ
  map_add' := Φ.map_add
  map_smul' s r := by
    simp only [Algebra.smul_def, map_mul, hΦ]

private theorem semilinearTensorMap_section_apply
    (S T : Type*) [CommRing S] [CommRing T]
    (R A M N : Type*) [AddCommGroup R] [AddCommGroup A]
    [AddCommGroup M] [AddCommGroup N]
    [_root_.Module S R] [_root_.Module T A]
    [_root_.Module S M] [_root_.Module T N]
    (φ : S →+* T) (ψ : T →+* S)
    (F : R →ₛₗ[φ] A) (G : M →ₛₗ[φ] N)
    (F' : A →ₛₗ[ψ] R) (G' : N →ₛₗ[ψ] M)
    (hF : ∀ a, F (F' a) = a) (hG : ∀ n, G (G' n) = n)
    (z : A ⊗[T] N) :
    TensorProduct.map F G (TensorProduct.map F' G' z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add z t hz ht => rw [map_add, map_add, hz, ht]
  | tmul a n => rw [TensorProduct.map_tmul, TensorProduct.map_tmul, hF, hG]

variable (k : Type*) [Field k]

-- These cache the native quotient dictionaries, without changing any
-- scalar action or adding any assumption.
local instance localComparisonOriginalAddCommGroup
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : AddCommGroup (Module k V K) :=
  originalModuleAddCommGroup k V K

@[implicit_reducible] private def originalCoefficientModuleDictionary
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) :=
  inferInstance

local instance localComparisonOriginalCoefficientModule
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) :=
  originalCoefficientModuleDictionary k V K

private theorem zero_relation_semilinearModuleMap_section_apply
    (V W : Type*) [AddCommGroup V] [AddCommGroup W]
    [_root_.Module k V] [_root_.Module k W]
    (f : V →ₗ[k] W) (s : W →ₗ[k] V)
    (K : Submodule k (⋀[k]^2 V))
    (hf : K ≤ (⊥ : Submodule k (⋀[k]^2 W)).comap (exteriorPower.map 2 f))
    (hs : f.comp s = LinearMap.id) (z : Module k W ⊥) :
    moduleMapSemilinear k V W f K ⊥ hf
      (moduleMapSemilinear k W V s ⊥ K bot_le z) = z := by
  have hcomp : (moduleMap k V W f K ⊥ hf).comp
      (moduleMap k W V s ⊥ K bot_le) = LinearMap.id := by
    rw [moduleMap_comp]
    simp only [hs]
    exact moduleMap_id k W (⊥ : Submodule k (⋀[k]^2 W))
  exact DFunLike.congr_fun hcomp z

variable (E : Type*) [AddCommGroup E] [_root_.Module k E]
variable (P : Submodule k E) (I : Submodule k (⋀[k]^2 E))

-- The zero-relation quotient on the actual dual of P is a deep native
-- quotient expression. Cache its exact parent monoid and coefficient
-- action directly, rather than searching quotient/group parent paths
-- again when native TensorProduct.map requests AddCommMonoid.
local instance (priority := 2000) componentZeroOriginalAddCommMonoid :
    AddCommMonoid (Module k (_root_.Module.Dual k P) ⊥) :=
  (originalModuleAddCommGroup k (_root_.Module.Dual k P) ⊥).toAddCommMonoid

local instance (priority := 2000) componentZeroOriginalCoefficients :
    _root_.Module (S k (_root_.Module.Dual k P))
      (Module k (_root_.Module.Dual k P) ⊥) :=
  originalCoefficientModuleDictionary k (_root_.Module.Dual k P) ⊥

/-- The actual local coefficient projection with its proved semilinear
compatibility over the actual symmetric-algebra projection. -/
def componentLocalCoefficientSemilinearProjection (eP : P) :=
  localCoefficientSemilinear
    (S k (_root_.Module.Dual k E)) (S k (_root_.Module.Dual k P))
    (ambientComponentPointLocalRing k E P eP) (componentPointLocalRing k E P eP)
    (componentSymmetricProjection k E P).toRingHom (componentLocalScalarProjection k E P eP)
    (componentLocalScalarProjection_algebraMap k E P eP)

/-- The actual local coefficient section with its proved semilinear
compatibility over the actual symmetric-algebra section. -/
def componentLocalCoefficientSemilinearSection (eP : P) :=
  localCoefficientSemilinear
    (S k (_root_.Module.Dual k P)) (S k (_root_.Module.Dual k E))
    (componentPointLocalRing k E P eP) (ambientComponentPointLocalRing k E P eP)
    (componentSymmetricSection k E P).toRingHom (componentLocalScalarSection k E P eP)
    (componentLocalScalarSection_algebraMap k E P eP)

/-- Literal localization of the original zero-relation component
Koszul module over its own true symmetric coefficient algebra. -/
abbrev componentPointZeroRelationModule (eP : P) :=
  CoefficientExtendedModule k (_root_.Module.Dual k P)
    (⊥ : Submodule k (⋀[k]^2 (_root_.Module.Dual k P)))
    (componentPointLocalRing k E P eP)

/-- The actual reverse original-module map as a semilinear map. -/
def isotropicComponentModuleSemilinearSection :=
  moduleMapSemilinear k (_root_.Module.Dual k P) (_root_.Module.Dual k E)
    (componentDualSection k E P) ⊥ (exteriorAnnihilator k E 2 I)
    (isotropicComponentSectionRelationContainment k E P I)

variable [FiniteDimensional k E]

/-- The actual forward original-module map as a semilinear map; the
true quadratic containment is derived from actual isotropy. -/
def isotropicComponentModuleSemilinearMap
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I) :=
  moduleMapSemilinear k (_root_.Module.Dual k E) (_root_.Module.Dual k P)
    (componentDualQuotient k E P) (exteriorAnnihilator k E 2 I) ⊥
    (isotropicComponentRelationContainment k E I P hiso)

/-- The native tensor-product map from the literal ambient localization
to the literal component localization. No isomorphism is input. -/
def isotropicComponentLocalizedMap (eP : P)
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I) :=
  TensorProduct.map (componentLocalCoefficientSemilinearProjection k E P eP)
    (isotropicComponentModuleSemilinearMap k E P I hiso)

/-- The native reverse tensor-product map using the actual derived
coefficient and original-module sections. -/
def isotropicComponentLocalizedSection (eP : P) :=
  TensorProduct.map (componentLocalCoefficientSemilinearSection k E P eP)
    (isotropicComponentModuleSemilinearSection k E P I)

@[simp] theorem isotropicComponentLocalizedMap_tmul (eP : P)
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I)
    (r : ambientComponentPointLocalRing k E P eP)
    (z : Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :
    isotropicComponentLocalizedMap k E P I eP hiso (r ⊗ₜ[S k (_root_.Module.Dual k E)] z) =
      componentLocalScalarProjection k E P eP r ⊗ₜ[S k (_root_.Module.Dual k P)]
        isotropicComponentModuleMap k E I P hiso z := rfl

omit [FiniteDimensional k E] in
@[simp] theorem isotropicComponentLocalizedSection_tmul (eP : P)
    (r : componentPointLocalRing k E P eP)
    (z : Module k (_root_.Module.Dual k P) ⊥) :
    isotropicComponentLocalizedSection k E P I eP (r ⊗ₜ[S k (_root_.Module.Dual k P)] z) =
      componentLocalScalarSection k E P eP r ⊗ₜ[S k (_root_.Module.Dual k E)]
        isotropicComponentModuleSection k E P I z := rfl

/-- The actual forward tensor map composed with the actual reverse
tensor map is the identity. This is proved on the true tensor product,
from the already proved actual scalar and original-module identities. -/
theorem isotropicComponentLocalizedMap_section_apply (eP : P)
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I)
    (z : componentPointZeroRelationModule k E P eP) :
    isotropicComponentLocalizedMap k E P I eP hiso
      (isotropicComponentLocalizedSection k E P I eP z) = z := by
  exact semilinearTensorMap_section_apply
    (S k (_root_.Module.Dual k E)) (S k (_root_.Module.Dual k P))
    (ambientComponentPointLocalRing k E P eP) (componentPointLocalRing k E P eP)
    (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I))
    (Module k (_root_.Module.Dual k P) ⊥)
    (componentSymmetricProjection k E P).toRingHom (componentSymmetricSection k E P).toRingHom
    (componentLocalCoefficientSemilinearProjection k E P eP)
    (isotropicComponentModuleSemilinearMap k E P I hiso)
    (componentLocalCoefficientSemilinearSection k E P eP)
    (isotropicComponentModuleSemilinearSection k E P I)
    (componentLocalScalarProjection_section_apply k E P eP)
    (zero_relation_semilinearModuleMap_section_apply k
      (_root_.Module.Dual k E) (_root_.Module.Dual k P)
      (componentDualQuotient k E P) (componentDualSection k E P)
      (exteriorAnnihilator k E 2 I)
      (isotropicComponentRelationContainment k E I P hiso)
      (componentDualQuotient_comp_section k E P)) z

/-- The actual map between the two literal localizations is genuinely
surjective. Local injectivity still requires separation. -/
theorem isotropicComponentLocalizedMap_surjective (eP : P)
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I) :
    Function.Surjective (isotropicComponentLocalizedMap k E P I eP hiso) := by
  intro z
  exact ⟨isotropicComponentLocalizedSection k E P I eP z,
    isotropicComponentLocalizedMap_section_apply k E P I eP hiso z⟩

end ChenRanks.Koszul
