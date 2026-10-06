import ChenRanks.KoszulCanonicalFamilyGradingObjects
import ChenRanks.MaximalIsotropicFiniteFamily

/-!
# The AFRS effective decomposition input

`AFRSEffectiveCanonicalDecomposition` records the effective canonical
Koszul decomposition over the complex numbers. It is a proposition supplied
as an explicit argument to the main theorems. For a finite-dimensional
space of dimension at least three, separation of its maximal isotropic
subspaces implies that the canonical homogeneous map is bijective in
degree at least the ambient dimension minus three.

The small-dimensional cases are proved in the arrangement applications.
Separation, the group comparison, and resonance-component counts are also
proved there.
-/
noncomputable section
namespace ChenRanks.Koszul
universe u

def AFRSEffectiveCanonicalDecomposition : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [_root_.Module ℂ E] [FiniteDimensional ℂ E]
    (I : Submodule ℂ (⋀[ℂ]^2 E)),
    3 ≤ _root_.Module.finrank ℂ E →
    (∀ P : Submodule ℂ E,
      IsMaximalIsotropic (relationWedge (Resonance.cupQuotient I)) P →
      2 ≤ _root_.Module.finrank ℂ P →
      mixedExterior P ⊓ LinearMap.ker (Resonance.cupQuotient I) = pureExterior P) →
    ∀ (τ : Type) [Fintype τ]
      (b : _root_.Module.Basis τ ℂ (_root_.Module.Dual ℂ E)) (r : ℕ),
      _root_.Module.finrank ℂ E - 3 ≤ r →
      Function.Bijective (originalCanonicalFamilyHomogeneousMap ℂ E I b r)

end ChenRanks.Koszul
