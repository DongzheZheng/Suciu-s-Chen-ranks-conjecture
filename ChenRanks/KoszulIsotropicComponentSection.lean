import ChenRanks.KoszulIsotropicComponentMaps
import ChenRanks.KoszulFunctorialityCalculus
import ChenRanks.KoszulOriginalModuleStructures
import Mathlib.Algebra.Module.Projective

/-!
# A genuine field-linear section of the actual isotropic component map

The generating-space map is the actual restriction of dual functionals
to the original subspace. Its already proved surjectivity supplies a
genuine linear section over the field, using native projectivity derived
from a genuine vector-space basis.

The reverse map of original Koszul quotients has zero source relations,
so its quadratic containment is proved, rather than assumed. Actual
isotropy proves that the original relations restrict to zero. Identity
and composition of the actual original quotient maps then show that the
canonical component map has a true field-linear right inverse and is
globally surjective.

The reverse map is semilinear through the symmetric-algebra section. An
S-linear global splitting, local injectivity, component-map local
isomorphism, finite-family decomposition, effective bounds, reducedness,
and the Chen formula are not claimed here.
-/

noncomputable section

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]

-- These are the already cached native quotient dictionaries, not new
-- actions or hypotheses. Cache them before elaborating actual map types.
local instance sectionOriginalAddCommGroup
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : AddCommGroup (Module k V K) :=
  originalModuleAddCommGroup k V K

local instance sectionOriginalScalarModule
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module k (Module k V K) :=
  originalModuleScalarModule k V K

variable (E : Type*) [AddCommGroup E] [_root_.Module k E]
variable (P : Submodule k E)

/-- A section of actual dual restriction is derived from its true
surjectivity. Projectivity of the actual target vector space is derived
from its native vector-space basis; it is not an input. -/
theorem componentDualQuotient_exists_section :
    ∃ s : _root_.Module.Dual k P →ₗ[k] _root_.Module.Dual k E,
      (componentDualQuotient k E P).comp s = LinearMap.id := by
  letI : _root_.Module.Free k (_root_.Module.Dual k P) :=
    _root_.Module.Free.of_basis
      (_root_.Module.Basis.ofVectorSpace k (_root_.Module.Dual k P))
  letI : _root_.Module.Projective k (_root_.Module.Dual k P) :=
    _root_.Module.Projective.of_free
  exact (componentDualQuotient k E P).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (componentDualQuotient_surjective k E P))

/-- A chosen genuine linear section of the actual dual restriction map. -/
def componentDualSection : _root_.Module.Dual k P →ₗ[k] _root_.Module.Dual k E :=
  Classical.choose (componentDualQuotient_exists_section k E P)

/-- The actual generating-space section is a right inverse of the actual
restriction map. This equation follows from the proved existence theorem. -/
@[simp] theorem componentDualQuotient_comp_section :
    (componentDualQuotient k E P).comp (componentDualSection k E P) =
      LinearMap.id :=
  Classical.choose_spec (componentDualQuotient_exists_section k E P)

@[simp] theorem componentDualQuotient_section_apply
    (w : _root_.Module.Dual k P) :
    componentDualQuotient k E P (componentDualSection k E P w) = w :=
  DFunLike.congr_fun (componentDualQuotient_comp_section k E P) w

private theorem zero_relation_moduleMap_comp_section
    (V W : Type*) [AddCommGroup V] [AddCommGroup W]
    [_root_.Module k V] [_root_.Module k W]
    (f : V →ₗ[k] W) (s : W →ₗ[k] V)
    (K : Submodule k (⋀[k]^2 V))
    (hf : K ≤ (⊥ : Submodule k (⋀[k]^2 W)).comap (exteriorPower.map 2 f))
    (hs : f.comp s = LinearMap.id) :
    (moduleMap k V W f K ⊥ hf).comp
        (moduleMap k W V s ⊥ K bot_le) = LinearMap.id := by
  rw [moduleMap_comp]
  simp only [hs]
  exact moduleMap_id k W (⊥ : Submodule k (⋀[k]^2 W))

private theorem zero_relation_moduleMap_section_apply
    (V W : Type*) [AddCommGroup V] [AddCommGroup W]
    [_root_.Module k V] [_root_.Module k W]
    (f : V →ₗ[k] W) (s : W →ₗ[k] V)
    (K : Submodule k (⋀[k]^2 V))
    (hf : K ≤ (⊥ : Submodule k (⋀[k]^2 W)).comap (exteriorPower.map 2 f))
    (hs : f.comp s = LinearMap.id) (z : Module k W ⊥) :
    moduleMap k V W f K ⊥ hf (moduleMap k W V s ⊥ K bot_le z) = z :=
  DFunLike.congr_fun (zero_relation_moduleMap_comp_section k V W f s K hf hs) z

variable (I : Submodule k (⋀[k]^2 E))

/-- The actual section carries zero source quadratic relations into the
actual original relation space. No relation-lifting assumption is added. -/
theorem isotropicComponentSectionRelationContainment :
    (⊥ : Submodule k (⋀[k]^2 (_root_.Module.Dual k P))) ≤
      (exteriorAnnihilator k E 2 I).comap
        (exteriorPower.map 2 (componentDualSection k E P)) :=
  bot_le

/-- The actual reverse map on the original Koszul quotients. Its source
has zero quadratic relations; its target is the original quotient. -/
def isotropicComponentModuleSection :=
  moduleMap k (_root_.Module.Dual k P) (_root_.Module.Dual k E)
    (componentDualSection k E P) ⊥ (exteriorAnnihilator k E 2 I)
    (isotropicComponentSectionRelationContainment k E P I)

variable [FiniteDimensional k E]

/-- True isotropy and the actual generating-space section prove that
the genuine canonical component map composed with the genuine reverse
original-module map is the identity. No separation hypothesis is used. -/
theorem isotropicComponentModuleMap_comp_section
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I) :
    ∀ z : Module k (_root_.Module.Dual k P) ⊥,
      isotropicComponentModuleMap k E I P hiso
        (isotropicComponentModuleSection k E P I z) = z := by
  intro z
  exact zero_relation_moduleMap_section_apply k
    (_root_.Module.Dual k E) (_root_.Module.Dual k P)
    (componentDualQuotient k E P) (componentDualSection k E P)
    (exteriorAnnihilator k E 2 I)
    (isotropicComponentRelationContainment k E I P hiso)
    (componentDualQuotient_comp_section k E P) z

/-- The constructed reverse map is a genuine field-linear right inverse
of the original canonical isotropic component map. -/
theorem isotropicComponentModuleSection_rightInverse
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I) :
    Function.RightInverse (isotropicComponentModuleSection k E P I)
      (isotropicComponentModuleMap k E I P hiso) := by
  intro z
  exact isotropicComponentModuleMap_comp_section k E P I hiso z

/-- The actual canonical isotropic component map is globally surjective
as a field-linear map. This is not a local-injectivity or effective-range
statement, and its chosen section is not asserted to be S-linear. -/
theorem isotropicComponentModuleMap_surjective
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I) :
    Function.Surjective (isotropicComponentModuleMap k E I P hiso) := by
  intro z
  exact ⟨isotropicComponentModuleSection k E P I z,
    isotropicComponentModuleSection_rightInverse k E P I hiso z⟩

end ChenRanks.Koszul
