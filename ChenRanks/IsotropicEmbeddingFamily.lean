import ChenRanks.MaximalIsotropicFiniteFamily

/-! Genuine maximal-isotropic families under an actual injective linear
map. The two structural conditions are explicit intermediate conditions:
zero cup is reflected, and all target isotropic subspaces of dimension
at least two lie in the actual range. Actual geometry must discharge
them before this dictionary gives an application. -/
noncomputable section
namespace ChenRanks.Resonance
variable {k E F W Z : Type*} [Field k] [Infinite k]
variable [AddCommGroup E] [Module k E] [AddCommGroup F] [Module k F]
variable [AddCommGroup W] [Module k W] [AddCommGroup Z] [Module k Z]
variable [FiniteDimensional k E] [FiniteDimensional k F]
variable (φ : (⋀[k]^2 E) →ₗ[k] W) (ψ : (⋀[k]^2 F) →ₗ[k] Z)
variable (e : E →ₗ[k] F) (hinj : Function.Injective e)
variable (hzero : ∀ a b : E, relationWedge ψ (e a) (e b) = 0 ↔
  relationWedge φ a b = 0)
variable (hrange : ∀ Q : Submodule k F, IsIsotropic (relationWedge ψ) Q →
  2 ≤ Module.finrank k Q → Q ≤ e.range)

include hinj in
theorem isotropicEmbedding_finrank_map (P : Submodule k E) :
    Module.finrank k (P.map e) = Module.finrank k P :=
  (Submodule.equivMapOfInjective e hinj P).finrank_eq.symm

include hzero in
theorem isotropicEmbedding_isotropic_map_iff (P : Submodule k E) :
    IsIsotropic (relationWedge ψ) (P.map e) ↔
      IsIsotropic (relationWedge φ) P := by
  constructor
  · intro h a ha b hb
    exact (hzero a b).mp
      (h (e a) (Submodule.mem_map.mpr ⟨a, ha, rfl⟩)
        (e b) (Submodule.mem_map.mpr ⟨b, hb, rfl⟩))
  · intro h a ha b hb
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hb
    exact (hzero x y).mpr (h x hx y hy)

include hzero in
theorem isotropicEmbedding_isotropic_comap (Q : Submodule k F)
    (hQ : IsIsotropic (relationWedge ψ) Q) :
    IsIsotropic (relationWedge φ) (Q.comap e) := by
  intro a ha b hb
  exact (hzero a b).mp (hQ (e a) ha (e b) hb)

include hrange in
theorem isotropicEmbedding_map_comap (Q : Submodule k F)
    (hQ : IsIsotropic (relationWedge ψ) Q)
    (hdim : 2 ≤ Module.finrank k Q) :
    (Q.comap e).map e = Q := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    exact hx
  · intro y hy
    obtain ⟨x, hx⟩ := hrange Q hQ hdim hy
    have hxc : x ∈ Q.comap e := by
      change e x ∈ Q
      rw [hx]
      exact hy
    exact Submodule.mem_map.mpr ⟨x, hxc, hx⟩

include hinj in
theorem isotropicEmbedding_comap_map (P : Submodule k E) :
    (P.map e).comap e = P := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
    exact hinj hyx ▸ hy
  · intro x hx
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

include hinj hzero hrange in
theorem isotropicEmbedding_maximal_map (P : Submodule k E)
    (hP : IsMaximalIsotropic (relationWedge φ) P)
    (hdim : 2 ≤ Module.finrank k P) :
    IsMaximalIsotropic (relationWedge ψ) (P.map e) := by
  refine ⟨(isotropicEmbedding_isotropic_map_iff φ ψ e hzero P).mpr hP.1, ?_⟩
  intro Q hPQ hQ
  have hdimQ : 2 ≤ Module.finrank k Q := by
    have h := Submodule.finrank_mono hPQ
    rw [isotropicEmbedding_finrank_map e hinj P] at h
    omega
  have hPC : P ≤ Q.comap e := by
    intro x hx
    exact hPQ (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
  have hm := hP.2 (Q.comap e) hPC
    (isotropicEmbedding_isotropic_comap φ ψ e hzero Q hQ)
  rw [← isotropicEmbedding_map_comap ψ e hrange Q hQ hdimQ]
  exact Submodule.map_mono hm

include hinj hzero hrange in
theorem isotropicEmbedding_maximal_comap (Q : Submodule k F)
    (hQ : IsMaximalIsotropic (relationWedge ψ) Q)
    (hdim : 2 ≤ Module.finrank k Q) :
    IsMaximalIsotropic (relationWedge φ) (Q.comap e) := by
  refine ⟨isotropicEmbedding_isotropic_comap φ ψ e hzero Q hQ.1, ?_⟩
  intro P hQP hP
  have hQe : Q = (Q.comap e).map e :=
    (isotropicEmbedding_map_comap ψ e hrange Q hQ.1 hdim).symm
  have hQP' : Q ≤ P.map e := by
    rw [hQe]
    exact Submodule.map_mono hQP
  have hm := hQ.2 (P.map e) hQP'
    ((isotropicEmbedding_isotropic_map_iff φ ψ e hzero P).mpr hP)
  intro x hx
  exact hm (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)

include hinj hzero hrange in
/-- Actual map/comap constructs a bijection of the original families,
with their genuine subspace dimensions retained. -/
def isotropicEmbeddingFamilyEquiv :
    OriginalMaximalIsotropicFamily φ ≃ OriginalMaximalIsotropicFamily ψ where
  toFun P := ⟨P.val.map e,
    isotropicEmbedding_maximal_map φ ψ e hinj hzero hrange P.val P.property.1 P.property.2,
    by rw [isotropicEmbedding_finrank_map e hinj P.val]; exact P.property.2⟩
  invFun Q := ⟨Q.val.comap e,
    isotropicEmbedding_maximal_comap φ ψ e hinj hzero hrange Q.val Q.property.1 Q.property.2,
    by
      have hd := Q.property.2
      rw [← isotropicEmbedding_map_comap ψ e hrange Q.val Q.property.1.1 Q.property.2,
        isotropicEmbedding_finrank_map e hinj] at hd
      exact hd⟩
  left_inv P := by
    apply Subtype.ext
    exact isotropicEmbedding_comap_map e hinj P.val
  right_inv Q := by
    apply Subtype.ext
    exact isotropicEmbedding_map_comap ψ e hrange Q.val Q.property.1.1 Q.property.2

include hinj hzero hrange in
theorem isotropicEmbeddingFamilyEquiv_finrank
    (P : OriginalMaximalIsotropicFamily φ) :
    Module.finrank k (isotropicEmbeddingFamilyEquiv φ ψ e hinj hzero hrange P).val =
      Module.finrank k P.val :=
  isotropicEmbedding_finrank_map e hinj P.val

end ChenRanks.Resonance
