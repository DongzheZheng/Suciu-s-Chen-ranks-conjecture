import ChenRanks.KoszulComponentDuality
import ChenRanks.KoszulGradedFunctoriality
import ChenRanks.KoszulOriginalModuleStructures

/-!
# Canonical maps to isotropic component modules

The determinant annihilator of `I` is the quadratic relation space.
Dualizing the subspace inclusion gives the generating-space map.
Isotropy makes the image relations zero, so the quotient and homogeneous
maps land in the zero-relation component modules. These maps are
constructed in every degree.
-/

noncomputable section

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E)) (P : Submodule k E)

/-- Actual isotropy kills the actual restriction of the original dual
quadratic relations. This is proved, rather than a quotient-map premise. -/
theorem isotropicComponentRelationContainment
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I) :
    exteriorAnnihilator k E 2 I ≤
      (⊥ : Submodule k (⋀[k]^2 (_root_.Module.Dual k P))).comap
        (exteriorPower.map 2 (componentDualQuotient k E P)) := by
  have h := quadraticImage_containment k (_root_.Module.Dual k E)
    (_root_.Module.Dual k P) (componentDualQuotient k E P)
    (exteriorAnnihilator k E 2 I)
  rw [quadraticImage_eq_bot_of_isotropic k E P I hiso] at h
  exact h

/-- The actual original-module map to the actual zero-relation component. -/
def isotropicComponentModuleMap
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I) :=
  moduleMap k (_root_.Module.Dual k E) (_root_.Module.Dual k P)
    (componentDualQuotient k E P) (exteriorAnnihilator k E 2 I) ⊥
    (isotropicComponentRelationContainment k E I P hiso)

variable {ι τ : Type*} [Fintype ι] [Fintype τ]
  (b : _root_.Module.Basis ι k (_root_.Module.Dual k E))
  (c : _root_.Module.Basis τ k (_root_.Module.Dual k P))

/-- The actual canonical component map in each genuine homogeneous degree. -/
def isotropicComponentHomogeneousMap
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I) (r : ℕ) :
    homogeneousModule k (_root_.Module.Dual k E) b (exteriorAnnihilator k E 2 I) r →ₗ[k]
      homogeneousModule k (_root_.Module.Dual k P) c ⊥ r :=
  homogeneousModuleMap k (_root_.Module.Dual k E) (_root_.Module.Dual k P)
    b c (componentDualQuotient k E P) (exteriorAnnihilator k E 2 I) ⊥
    (isotropicComponentRelationContainment k E I P hiso) r

/-- The genuine homogeneous component map commutes with the actual map
on the original ungraded quotients, retaining the original definitions. -/
theorem isotropicComponentHomogeneousMap_originalDiagram
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I) (r : ℕ)
    (z : homogeneousModule k (_root_.Module.Dual k E) b (exteriorAnnihilator k E 2 I) r) :
    ((homogeneousModuleEquivOriginalDegree k (_root_.Module.Dual k P) c ⊥ r)
      (isotropicComponentHomogeneousMap k E I P b c hiso r z) :
        Module k (_root_.Module.Dual k P) ⊥) =
      isotropicComponentModuleMap k E I P hiso
        (homogeneousModuleEquivOriginalDegree k (_root_.Module.Dual k E) b
          (exteriorAnnihilator k E 2 I) r z) :=
  homogeneousModuleMap_originalDiagram k (_root_.Module.Dual k E) (_root_.Module.Dual k P)
    b c (componentDualQuotient k E P) (exteriorAnnihilator k E 2 I) ⊥
    (isotropicComponentRelationContainment k E I P hiso) r z

end ChenRanks.Koszul
