import ChenRanks.ArrangementNonparallelNormalPair
import ChenRanks.ArrangementSingleNormalRealMap
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Every actual real affine line in one original equation-value plane
has a proper original ambient inverse image. This supplies genuine
finite avoidance conditions for transverse fan triangles and their
radial boundary edges, including constant-equation edge degenerations. -/

noncomputable section

namespace ChenRanks

/-- A surjective actual linear map has proper inverse images of
proper actual subspaces. -/
theorem submodule_comap_ne_top_of_surjective {k V W : Type*} [Field k]
    [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W]
    (f : V →ₗ[k] W) (hf : Function.Surjective f) (S : Submodule k W)
    (hS : S ≠ ⊤) : S.comap f ≠ ⊤ := by
  intro htop
  apply hS
  apply Submodule.ext
  intro w
  simp only [Submodule.mem_top, iff_true]
  obtain ⟨v, rfl⟩ := hf w
  have hv : v ∈ S.comap f := by
    rw [htop]
    exact Submodule.mem_top
  exact hv

/-- A genuine real span of one complex number is always proper,
including the zero direction. -/
theorem complex_real_singleton_span_ne_top (v : ℂ) :
    Submodule.span ℝ ({v} : Set ℂ) ≠ ⊤ := by
  classical
  have h := finrank_span_finset_le_card (R := ℝ) ({v} : Finset ℂ)
  intro htop
  have hdim : Module.finrank ℝ (Submodule.span ℝ ({v} : Set ℂ)) ≤ 1 := by
    simpa only [Finset.coe_singleton, Finset.card_singleton] using h
  rw [htop, _root_.finrank_top, Complex.finrank_real_complex] at hdim
  omega

namespace AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The actual original complex normal is surjective as a real map. -/
theorem actualSingleNormalRealMap_surjective (H : ι) :
    Function.Surjective (A.actualSingleNormalRealMap H) := by
  obtain ⟨n, hn⟩ := A.exists_actual_meridian_normal_vector H
  intro w
  refine ⟨w • n, ?_⟩
  change A.normal H (w • n) = w
  rw [map_smul, smul_eq_mul, hn, mul_one]

/-- Every actual one-equation real-line direction has a proper actual
ambient inverse image. No nonzero direction is assumed. -/
theorem actualSingleNormalRealLine_comap_ne_top (H : ι) (v : ℂ) :
    (Submodule.span ℝ ({v} : Set ℂ)).comap
      (A.actualSingleNormalRealMap H) ≠ ⊤ :=
  submodule_comap_ne_top_of_surjective (A.actualSingleNormalRealMap H)
    (A.actualSingleNormalRealMap_surjective H) _ (complex_real_singleton_span_ne_top v)

end AffineArrangement
end ChenRanks
