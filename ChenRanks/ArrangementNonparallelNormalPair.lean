import ChenRanks.ArrangementMeridianBasepoint
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The original nonparallel normal pair supplies a genuine surjective
real map to `ℂ²`, so the genuine intersection-flat direction has real
codimension four. Surjectivity and the codimension are derived from the
original normals, not from an assumed generic-flat model. -/

noncomputable section

namespace ChenRanks

/-- Native real scalar multiplication on complex modules really moves
through every complex-linear map. This is proved from the actual
complex scalar action, independently of typeclass-search choices. -/
theorem complexLinearMapCompatibleRealScalars
    (V W : Type*) [AddCommGroup V] [AddCommGroup W] [Module ℂ V] [Module ℂ W] :
    LinearMap.CompatibleSMul V W ℝ ℂ := by
  constructor
  intro f r v
  simpa only [Complex.coe_smul] using f.map_smul (r : ℂ) v

namespace AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance : LinearMap.CompatibleSMul (Fin d → ℂ) (ℂ × ℂ) ℝ ℂ :=
  complexLinearMapCompatibleRealScalars _ _

/-- The actual two original normal values, regarded as a real linear map. -/
def actualNormalPairRealMap (H K : ι) :
    (Fin d → ℂ) →ₗ[ℝ] (ℂ × ℂ) where
  toFun v := (A.normal H v, A.normal K v)
  map_add' v w := by
    apply Prod.ext
    · change A.normal H (v + w) = A.normal H v + A.normal H w
      exact (A.normal H).map_add v w
    · change A.normal K (v + w) = A.normal K v + A.normal K w
      exact (A.normal K).map_add v w
  map_smul' r v := by
    apply Prod.ext
    · change A.normal H ((r : ℂ) • v) = (r : ℂ) * A.normal H v
      rw [map_smul, smul_eq_mul]
    · change A.normal K ((r : ℂ) • v) = (r : ℂ) * A.normal K v
      rw [map_smul, smul_eq_mul]

/-- Nonproportional original normals supply genuine dual-coordinate
vectors. No generic-coordinate or normal-pair-surjectivity input occurs. -/
theorem exists_actual_normal_pair_coordinate_vectors (H K : ι)
    (hnonparallel : ∀ c : ℂ, A.normal K ≠ c • A.normal H) :
    ∃ (v₁ v₂ : Fin d → ℂ), A.normal H v₁ = 1 ∧ A.normal K v₁ = 0 ∧
      A.normal H v₂ = 0 ∧ A.normal K v₂ = 1 := by
  obtain ⟨n, hn⟩ := A.exists_actual_meridian_normal_vector H
  have hv : ∃ v : Fin d → ℂ, A.normal H v = 0 ∧ A.normal K v ≠ 0 := by
    by_contra h
    have hvanish : ∀ v : Fin d → ℂ, A.normal H v = 0 → A.normal K v = 0 := by
      intro v hvH
      by_contra hvK
      exact h ⟨v, hvH, hvK⟩
    apply hnonparallel (A.normal K n)
    apply LinearMap.ext
    intro x
    have hx : A.normal H (x - A.normal H x • n) = 0 := by
      simp only [map_sub, map_smul, smul_eq_mul, hn, mul_one, sub_self]
    have hz := hvanish (x - A.normal H x • n) hx
    simp only [map_sub, map_smul, smul_eq_mul] at hz
    change A.normal K x = A.normal K n * A.normal H x
    rw [mul_comm]
    exact sub_eq_zero.mp hz
  obtain ⟨v, hvH, hvK⟩ := hv
  let v₂ := (A.normal K v)⁻¹ • v
  have hH₂ : A.normal H v₂ = 0 := by
    simp only [v₂, map_smul, smul_eq_mul, hvH, mul_zero]
  have hK₂ : A.normal K v₂ = 1 := by
    rw [show A.normal K v₂ = (A.normal K v)⁻¹ * A.normal K v from by
      simp only [v₂, map_smul, smul_eq_mul], inv_mul_cancel₀ hvK]
  let v₁ := n - A.normal K n • v₂
  have hH₁ : A.normal H v₁ = 1 := by
    simp only [v₁, map_sub, map_smul, smul_eq_mul, hn, hH₂, mul_zero, sub_zero]
  have hK₁ : A.normal K v₁ = 0 := by
    simp only [v₁, map_sub, map_smul, smul_eq_mul, hK₂, mul_one, sub_self]
  exact ⟨v₁, v₂, hH₁, hK₁, hH₂, hK₂⟩

/-- The genuine original real normal-pair map is surjective. -/
theorem actualNormalPairRealMap_surjective (H K : ι)
    (hnonparallel : ∀ c : ℂ, A.normal K ≠ c • A.normal H) :
    Function.Surjective (A.actualNormalPairRealMap H K) := by
  obtain ⟨v₁, v₂, hH₁, hK₁, hH₂, hK₂⟩ :=
    A.exists_actual_normal_pair_coordinate_vectors H K hnonparallel
  intro z
  refine ⟨z.1 • v₁ + z.2 • v₂, ?_⟩
  apply Prod.ext
  · change A.normal H (z.1 • v₁ + z.2 • v₂) = z.1
    simp only [map_add, map_smul, smul_eq_mul, hH₁, hH₂,
      mul_one, mul_zero, add_zero]
  · change A.normal K (z.1 • v₁ + z.2 • v₂) = z.2
    simp only [map_add, map_smul, smul_eq_mul, hK₁, hK₂,
      mul_one, mul_zero, zero_add]

/-- The true original pair-flat direction has real codimension four. -/
theorem actualNormalPairRealMap_kernel_finrank (H K : ι)
    (hnonparallel : ∀ c : ℂ, A.normal K ≠ c • A.normal H) :
    Module.finrank ℝ (LinearMap.ker (A.actualNormalPairRealMap H K)) + 4 =
      Module.finrank ℝ (Fin d → ℂ) := by
  have h := (A.actualNormalPairRealMap H K).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr
    (A.actualNormalPairRealMap_surjective H K hnonparallel), _root_.finrank_top,
    Module.finrank_prod, Complex.finrank_real_complex] at h
  omega

end AffineArrangement
end ChenRanks
