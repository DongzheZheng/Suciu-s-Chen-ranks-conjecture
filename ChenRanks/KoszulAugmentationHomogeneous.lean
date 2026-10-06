import ChenRanks.KoszulMetabelianLowerCentralSeries
import ChenRanks.KoszulHomogeneousAnnihilator
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Actual homogeneous pieces inside the actual augmentation powers

The symmetric homogeneous pieces remain the original basis-transported
multivariate polynomial pieces. The augmentation ideal remains the kernel
of the genuine symmetric augmentation. Their degree-one and power
identities are proved through the actual algebra equivalence. Genuine
homogeneous second-differential preimages then put every original `W_r`
inside the actual `m^r W`. No identification of the successive quotient
with `W_r`, no graded Lie comparison, and no Chen-rank formula is supplied
as a hypothesis or definition.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} (b : _root_.Module.Basis ι k V)

/-- The original homogeneous subspace is the actual inverse image under
the original algebra equivalence, also expressed as its genuine map. -/
theorem homogeneousS_eq_map_polynomial (r : ℕ) :
    homogeneousS k V b r =
      (MvPolynomial.homogeneousSubmodule ι k r).map
        (SymmetricAlgebra.equivMvPolynomial b).symm.toLinearMap := by
  ext s
  constructor
  · intro hs
    exact ⟨SymmetricAlgebra.equivMvPolynomial b s, hs,
      (SymmetricAlgebra.equivMvPolynomial b).symm_apply_apply s⟩
  · rintro ⟨p, hp, rfl⟩
    change SymmetricAlgebra.equivMvPolynomial b
      ((SymmetricAlgebra.equivMvPolynomial b).symm p) ∈
        MvPolynomial.homogeneousSubmodule ι k r
    rw [AlgEquiv.apply_symm_apply]
    exact hp

/-- Actual multiplication of degree-one symmetric subspaces produces the
original homogeneous subspace in every degree. -/
theorem homogeneousS_one_pow (r : ℕ) :
    homogeneousS k V b 1 ^ r = homogeneousS k V b r := by
  rw [homogeneousS_eq_map_polynomial k V b 1]
  change ((MvPolynomial.homogeneousSubmodule ι k 1).map
    (SymmetricAlgebra.equivMvPolynomial b).symm.toAlgHom.toLinearMap) ^ r =
      homogeneousS k V b r
  rw [← Submodule.map_pow
    (M := MvPolynomial.homogeneousSubmodule ι k 1)
    (SymmetricAlgebra.equivMvPolynomial b).symm.toAlgHom r,
    MvPolynomial.homogeneousSubmodule_one_pow]
  exact (homogeneousS_eq_map_polynomial k V b r).symm

/-- Every actual degree-one coefficient lies in the actual augmentation kernel. -/
theorem homogeneousS_one_le_augmentation :
    homogeneousS k V b 1 ≤ (actualAugmentationIdeal k V).restrictScalars k := by
  rw [homogeneousS_eq_map_polynomial,
    MvPolynomial.homogeneousSubmodule_one_eq_span_X]
  rintro _ ⟨p, hp, rfl⟩
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    change (SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.X i) ∈
      actualAugmentationIdeal k V
    rw [SymmetricAlgebra.equivMvPolynomial_symm_X]
    exact actualAugmentationIdeal_ι_mem k V (b i)
  | zero =>
    rw [map_zero]
    exact Ideal.zero_mem _
  | add p q _hp _hq ihp ihq =>
    rw [map_add]
    exact Ideal.add_mem _ ihp ihq
  | smul c p _hp ih =>
    rw [map_smul]
    simpa only [algebraMap_smul] using
      (actualAugmentationIdeal k V).smul_mem (algebraMap k (S k V) c) ih

/-- Actual homogeneous coefficients of degree `r` belong to actual `m^r`. -/
theorem homogeneousS_le_augmentation_pow (r : ℕ) :
    homogeneousS k V b r ≤ (actualAugmentationIdeal k V ^ r).restrictScalars k := by
  by_cases hr : r = 0
  · subst r
    intro s _hs
    change s ∈ actualAugmentationIdeal k V ^ 0
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  · rw [← homogeneousS_one_pow k V b r,
      Submodule.restrictScalars_pow (A := k) hr]
    exact pow_le_pow_left' (homogeneousS_one_le_augmentation k V b) r

variable [Fintype ι] (K : Submodule k (⋀[k]^2 V))

local instance originalHomogeneousKoszulBaseModule : _root_.Module k (Module k V K) :=
  Submodule.Quotient.module' (S := k) (LinearMap.range (relationMap k V K))

/-- Actual homogeneous second tensors land in the original actual degree image. -/
theorem secondTensorToModule_tmul_mem_originalDegree (r : ℕ)
    (s : S k V) (hs : s ∈ homogeneousS k V b r) (w : ⋀[k]^2 V) :
    secondTensorToModule k V K (s ⊗ₜ[k] w) ∈
      LinearMap.range (degreeCycleToUngraded k V b K r) := by
  let z : cycleDegree k V b r :=
    ⟨delta2 k V (s ⊗ₜ[k] w),
      ⟨delta2_preserves_degree k V b r
        (tmul_mem_tensorHomogeneous k V b (⋀[k]^2 V) r s hs w),
        DFunLike.congr_fun (delta1_comp_delta2 k V) (s ⊗ₜ[k] w)⟩⟩
  exact ⟨z, rfl⟩

omit [Fintype ι] in
/-- Every actual homogeneous second tensor belongs, after its real quotient
map, to the actual augmentation power on the original module. -/
theorem c2Degree_le_augmentationPower_comap (r : ℕ) :
    c2Degree k V b r ≤
      ((augmentationPowerModule k V K r).restrictScalars k).comap
        ((secondTensorToModule k V K).restrictScalars k) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, hs, w, rfl⟩
  change secondTensorToModule k V K (s ⊗ₜ[k] w) ∈ augmentationPowerModule k V K r
  have he : secondTensorToModule k V K (s ⊗ₜ[k] w) = s • constantWedgeClass k V K w := by
    rw [constantWedgeClass_apply, ← map_smul]
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [he]
  exact Submodule.smul_mem_smul (homogeneousS_le_augmentation_pow k V b r hs)
    (show constantWedgeClass k V K w ∈ (⊤ : Submodule (S k V) (Module k V K)) from trivial)

variable [CharZero k]

/-- The genuine homogeneous cycle preimage puts each original degree piece
inside the actual augmentation power, without a degree-generation input. -/
theorem originalDegree_le_augmentationPower (r : ℕ) :
    LinearMap.range (degreeCycleToUngraded k V b K r) ≤
      (augmentationPowerModule k V K r).restrictScalars k := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨y, hy, he⟩ := cycleDegree_preimage k V b r z
  have hcycle : delta2ToCycles k V y = degreeCycleInclusion k V b r z := by
    apply Subtype.ext
    exact he
  have hquot : secondTensorToModule k V K y = degreeCycleToUngraded k V b K r z := by
    change (LinearMap.range (relationMap k V K)).mkQ (delta2ToCycles k V y) =
      (LinearMap.range (relationMap k V K)).mkQ (degreeCycleInclusion k V b r z)
    rw [hcycle]
  rw [← hquot]
  exact c2Degree_le_augmentationPower_comap k V b K r hy

/-- The actual original `W_r` inclusion lands in actual `m^r W`. -/
theorem degreeQuotientInclusion_mem_augmentationPower (r : ℕ)
    (w : homogeneousModule k V b K r) :
    degreeQuotientInclusion k V b K r w ∈ augmentationPowerModule k V K r :=
  originalDegree_le_augmentationPower k V b K r
    (degreeQuotientInclusion_mem_originalDegree k V b K r w)

end ChenRanks.Koszul
