import ChenRanks.ExteriorSeparationLinearEquiv

/-!
# Actual isotropic subspaces under a coefficient equivalence

The source relation is the genuine pullback of the target quadratic
map by the native exterior square of a linear equivalence. Isotropy,
maximality and subspace dimensions are transported by actual map and
comap. These lemmas supply a dictionary, without assuming an isotropic
family or identifying native cohomology with coefficients by definition.
-/

noncomputable section

namespace ChenRanks

variable {k E F W : Type*} [Field k]
variable [AddCommGroup E] [Module k E] [AddCommGroup F] [Module k F]
variable [AddCommGroup W] [Module k W]

theorem relationWedge_pullback_equiv (e : E ≃ₗ[k] F)
    (φ : (⋀[k]^2 F) →ₗ[k] W) (a b : E) :
    relationWedge (φ.comp (exteriorPower.map 2 e.toLinearMap)) a b =
      relationWedge φ (e a) (e b) := by
  simp only [relationWedge_apply, LinearMap.comp_apply, exteriorPowerMap_exteriorWedge]
  rfl

theorem isIsotropic_map_equiv (e : E ≃ₗ[k] F)
    (φ : (⋀[k]^2 F) →ₗ[k] W) (P : Submodule k E) :
    IsIsotropic (relationWedge φ) (P.map e.toLinearMap) ↔
      IsIsotropic (relationWedge (φ.comp (exteriorPower.map 2 e.toLinearMap))) P := by
  constructor
  · intro h a ha b hb
    rw [relationWedge_pullback_equiv]
    exact h (e a) (Submodule.mem_map.mpr ⟨a, ha, rfl⟩)
      (e b) (Submodule.mem_map.mpr ⟨b, hb, rfl⟩)
  · intro h a ha b hb
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hb
    exact (relationWedge_pullback_equiv e φ x y) ▸ h x hx y hy

theorem isIsotropic_comap_equiv (e : E ≃ₗ[k] F)
    (φ : (⋀[k]^2 F) →ₗ[k] W) (Q : Submodule k F) :
    IsIsotropic (relationWedge (φ.comp (exteriorPower.map 2 e.toLinearMap)))
        (Q.comap e.toLinearMap) ↔ IsIsotropic (relationWedge φ) Q := by
  constructor
  · intro h a ha b hb
    have hx : e.symm a ∈ Q.comap e.toLinearMap := by
      change e (e.symm a) ∈ Q
      simpa using ha
    have hy : e.symm b ∈ Q.comap e.toLinearMap := by
      change e (e.symm b) ∈ Q
      simpa using hb
    have hxy := h (e.symm a) hx (e.symm b) hy
    rw [relationWedge_pullback_equiv] at hxy
    simpa only [LinearEquiv.apply_symm_apply] using hxy
  · intro h a ha b hb
    rw [relationWedge_pullback_equiv]
    exact h (e a) ha (e b) hb

theorem isMaximalIsotropic_map_equiv (e : E ≃ₗ[k] F)
    (φ : (⋀[k]^2 F) →ₗ[k] W) (P : Submodule k E) :
    IsMaximalIsotropic (relationWedge φ) (P.map e.toLinearMap) ↔
      IsMaximalIsotropic (relationWedge (φ.comp (exteriorPower.map 2 e.toLinearMap))) P := by
  constructor
  · rintro ⟨hiso, hmax⟩
    refine ⟨(isIsotropic_map_equiv e φ P).mp hiso, ?_⟩
    intro T hPT hT
    have hm := hmax (T.map e.toLinearMap) (Submodule.map_mono hPT)
      ((isIsotropic_map_equiv e φ T).mpr hT)
    intro a ha
    have hea := hm (Submodule.mem_map.mpr ⟨a, ha, rfl⟩)
    obtain ⟨b, hb, hba⟩ := Submodule.mem_map.mp hea
    have hba' : b = a := e.injective hba
    simpa only [hba'] using hb
  · rintro ⟨hiso, hmax⟩
    refine ⟨(isIsotropic_map_equiv e φ P).mpr hiso, ?_⟩
    intro Q hPQ hQ
    have hle : P ≤ Q.comap e.toLinearMap := by
      intro a ha
      exact hPQ (Submodule.mem_map.mpr ⟨a, ha, rfl⟩)
    have hm := hmax (Q.comap e.toLinearMap) hle
      ((isIsotropic_comap_equiv e φ Q).mpr hQ)
    intro a ha
    have hx : e.symm a ∈ Q.comap e.toLinearMap := by
      change e (e.symm a) ∈ Q
      simpa using ha
    exact Submodule.mem_map.mpr
      ⟨e.symm a, hm hx, LinearEquiv.apply_symm_apply e a⟩

theorem finrank_submodule_map_equiv (e : E ≃ₗ[k] F) (P : Submodule k E) :
    Module.finrank k (P.map e.toLinearMap) = Module.finrank k P :=
  (Submodule.equivMapOfInjective e.toLinearMap e.injective P).finrank_eq.symm

end ChenRanks
