import ChenRanks.ExteriorSeparation

/-!
# Transport of genuine exterior separation under a linear equivalence

The exterior map is the native exterior-power functor. Its bijectivity,
and its images of the genuine mixed and pure exterior subspaces, are
proved from the actual underlying linear equivalence. This permits a
verified coefficient-to-cohomology equivalence to transport separation
without replacing either exterior space or supplying a transport law.
-/

noncomputable section

namespace ChenRanks

variable {k E F W : Type*} [Field k]
variable [AddCommGroup E] [Module k E] [AddCommGroup F] [Module k F]
variable [AddCommGroup W] [Module k W]

theorem exteriorPowerMap_exteriorWedge (f : E →ₗ[k] F) (a b : E) :
    exteriorPower.map 2 f (exteriorWedge a b) = exteriorWedge (f a) (f b) := by
  rw [exteriorWedge, exteriorPower.map_apply_ιMulti]
  unfold exteriorWedge
  congr 1
  ext i
  fin_cases i <;> rfl

/-- The actual exterior square of the actual linear equivalence. -/
def exteriorSquareEquiv (e : E ≃ₗ[k] F) : (⋀[k]^2 E) ≃ₗ[k] (⋀[k]^2 F) :=
  LinearEquiv.ofBijective (exteriorPower.map 2 e.toLinearMap)
    ⟨exteriorPower.map_injective_field e.injective,
      exteriorPower.map_surjective e.surjective⟩

@[simp] theorem exteriorSquareEquiv_apply (e : E ≃ₗ[k] F) (z : ⋀[k]^2 E) :
    exteriorSquareEquiv e z = exteriorPower.map 2 e.toLinearMap z := rfl

theorem mixedExterior_map_equiv (e : E ≃ₗ[k] F) (P : Submodule k E) :
    mixedExterior (P.map e.toLinearMap) =
      (mixedExterior P).map (exteriorPower.map 2 e.toLinearMap) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨p, x, rfl⟩
    obtain ⟨a, ha, hea⟩ := Submodule.mem_map.mp p.property
    refine Submodule.mem_map.mpr ⟨exteriorWedge a (e.symm x),
      exteriorWedge_mem_mixed P ⟨a, ha⟩ (e.symm x), ?_⟩
    rw [exteriorPowerMap_exteriorWedge]
    simp only [LinearEquiv.coe_coe, hea, LinearEquiv.apply_symm_apply]
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro z ⟨p, x, rfl⟩
    change exteriorPower.map 2 e.toLinearMap (exteriorWedge (p : E) x) ∈
      mixedExterior (P.map e.toLinearMap)
    rw [exteriorPowerMap_exteriorWedge]
    exact exteriorWedge_mem_mixed (P.map e.toLinearMap)
      ⟨e p, Submodule.mem_map.mpr ⟨p, p.property, rfl⟩⟩ (e x)

theorem pureExterior_map_equiv (e : E ≃ₗ[k] F) (P : Submodule k E) :
    pureExterior (P.map e.toLinearMap) =
      (pureExterior P).map (exteriorPower.map 2 e.toLinearMap) := by
  apply le_antisymm
  · rw [pureExterior_eq_span]
    apply Submodule.span_le.mpr
    rintro z ⟨p, q, rfl⟩
    obtain ⟨a, ha, hea⟩ := Submodule.mem_map.mp p.property
    obtain ⟨b, hb, heb⟩ := Submodule.mem_map.mp q.property
    refine Submodule.mem_map.mpr ⟨exteriorWedge a b,
      exteriorWedge_mem_pure P ⟨a, ha⟩ ⟨b, hb⟩, ?_⟩
    rw [exteriorPowerMap_exteriorWedge]
    simp only [hea, heb]
  · apply Submodule.map_le_iff_le_comap.mpr
    rw [pureExterior_eq_span]
    apply Submodule.span_le.mpr
    rintro z ⟨p, q, rfl⟩
    change exteriorPower.map 2 e.toLinearMap (exteriorWedge (p : E) (q : E)) ∈
      pureExterior (P.map e.toLinearMap)
    rw [exteriorPowerMap_exteriorWedge]
    exact exteriorWedge_mem_pure (P.map e.toLinearMap)
      ⟨e p, Submodule.mem_map.mpr ⟨p, p.property, rfl⟩⟩
      ⟨e q, Submodule.mem_map.mpr ⟨q, q.property, rfl⟩⟩

theorem exterior_kernel_map_equiv (e : E ≃ₗ[k] F) (φ : (⋀[k]^2 F) →ₗ[k] W) :
    (LinearMap.ker (φ.comp (exteriorPower.map 2 e.toLinearMap))).map
        (exteriorPower.map 2 e.toLinearMap) = LinearMap.ker φ := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hz
    obtain ⟨y, rfl⟩ := exteriorPower.map_surjective (n := 2) e.surjective z
    exact Submodule.mem_map.mpr ⟨y, hz, rfl⟩

theorem exterior_separation_map_equiv (e : E ≃ₗ[k] F)
    (φ : (⋀[k]^2 F) →ₗ[k] W) (P : Submodule k E)
    (hP : mixedExterior P ⊓
      LinearMap.ker (φ.comp (exteriorPower.map 2 e.toLinearMap)) = pureExterior P) :
    mixedExterior (P.map e.toLinearMap) ⊓ LinearMap.ker φ =
      pureExterior (P.map e.toLinearMap) := by
  rw [mixedExterior_map_equiv, pureExterior_map_equiv,
    ← exterior_kernel_map_equiv e φ]
  rw [← Submodule.map_inf (exteriorPower.map 2 e.toLinearMap)
    (exteriorPower.map_injective_field e.injective), hP]

end ChenRanks
