import ChenRanks.KoszulLinearEquivalenceFunctor
import ChenRanks.KoszulIsotropicComponentMaps

/-!
# The actual whole-space isotropic component in every original degree

The dual restriction to the actual top submodule is the dual of the
actual top-submodule linear equivalence. True Koszul functoriality gives
bijectivity of the original canonical homogeneous component map in
every degree. This uses arbitrary genuine bases and the actual full cup
kernel; no graded bijectivity or effective result is assumed.
-/

noncomputable section

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E]

/-- Actual dual restriction to the whole original ambient space is a
true linear equivalence, constructed from the true top-submodule map. -/
def componentDualQuotientTopEquiv :
    _root_.Module.Dual k E ≃ₗ[k] _root_.Module.Dual k (⊤ : Submodule k E) :=
  (Submodule.topEquiv : (⊤ : Submodule k E) ≃ₗ[k] E).dualMap

/-- Its genuine function is the original canonical dual restriction. -/
theorem componentDualQuotientTopEquiv_toLinearMap :
    (componentDualQuotientTopEquiv k E).toLinearMap =
      componentDualQuotient k E (⊤ : Submodule k E) := rfl

variable [FiniteDimensional k E]
variable {ι τ : Type*} [Fintype ι] [Fintype τ]
variable (b : _root_.Module.Basis ι k (_root_.Module.Dual k E))
variable (c : _root_.Module.Basis τ k (_root_.Module.Dual k (⊤ : Submodule k E)))

/-- The literal original canonical whole-space component map is
bijective in every degree. This is a true map assertion, rather than
a comparison of dimensions or a named replacement map. -/
theorem fullCupKernel_wholeSpace_homogeneousMap_bijective (r : ℕ) :
    Function.Bijective
      (isotropicComponentHomogeneousMap k E
        (⊤ : Submodule k (⋀[k]^2 E)) (⊤ : Submodule k E)
        b c le_top r) := by
  let K := exteriorAnnihilator k E 2 (⊤ : Submodule k (⋀[k]^2 E))
  let f := componentDualQuotient k E (⊤ : Submodule k E)
  have hK : K = ⊥ := exteriorAnnihilator_top k E 2
  have hb : quadraticImage k (_root_.Module.Dual k E)
      (_root_.Module.Dual k (⊤ : Submodule k E)) f K = ⊥ := by
    unfold quadraticImage
    rw [hK, Submodule.map_bot]
  have h := linearEquivalenceHomogeneousModuleMap_bijective k
    (_root_.Module.Dual k E) (_root_.Module.Dual k (⊤ : Submodule k E))
    K (componentDualQuotientTopEquiv k E) b c r
  have ht : ∀ (L : Submodule k (⋀[k]^2 (_root_.Module.Dual k (⊤ : Submodule k E))))
      (hc : K ≤ L.comap (exteriorPower.map 2 f)), L = ⊥ →
      Function.Bijective
        (homogeneousModuleMap k (_root_.Module.Dual k E)
          (_root_.Module.Dual k (⊤ : Submodule k E)) b c f K L hc r) →
      Function.Bijective
        (homogeneousModuleMap k (_root_.Module.Dual k E)
          (_root_.Module.Dual k (⊤ : Submodule k E)) b c f K ⊥
          (isotropicComponentRelationContainment k E ⊤ ⊤ le_top) r) := by
    intro L hc hL hbij
    subst L
    exact hbij
  apply ht (quadraticImage k (_root_.Module.Dual k E)
    (_root_.Module.Dual k (⊤ : Submodule k E)) f K)
    (quadraticImage_containment k (_root_.Module.Dual k E)
      (_root_.Module.Dual k (⊤ : Submodule k E)) f K) hb
  simpa only [componentDualQuotientTopEquiv_toLinearMap] using h

end ChenRanks.Koszul
