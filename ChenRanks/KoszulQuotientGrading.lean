import ChenRanks.KoszulHomogeneousBasis

/-!
# Genuine homogeneous quotients inside the original Koszul quotient

Homogeneous projection commutes with the actual second differential, with
the correct degree shift.  This recovers homogeneous relation witnesses
from arbitrary original relation witnesses.  Consequently the degreewise
Koszul quotient is genuinely equivalent to its actual image in the original
ungraded quotient; no injectivity or homogeneous relation hypothesis is used.

The global direct-sum recomposition is a separate subsequent assertion.
-/

noncomputable section

open TensorProduct
open scoped BigOperators TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} (b : _root_.Module.Basis ι k V)

/-- Projection of a product with a genuinely homogeneous factor has the
proved degree shift. -/
theorem homogeneousProjection_mul_of_homogeneous
    (n m : ℕ) (s t : S k V) (ht : t ∈ homogeneousS k V b m) :
    homogeneousProjection k V b (n + m) (s * t) =
      homogeneousProjection k V b n s * t := by
  classical
  have hl : homogeneousProjection k V b (n + m) (s * t) =
      ∑ i ∈ Finset.range ((SymmetricAlgebra.equivMvPolynomial b s).totalDegree + 1),
        homogeneousProjection k V b (n + m) (homogeneousProjection k V b i s * t) := by
    rw [← map_sum, ← Finset.sum_mul, sum_homogeneousProjection]
  have hr : homogeneousProjection k V b n s * t =
      ∑ i ∈ Finset.range ((SymmetricAlgebra.equivMvPolynomial b s).totalDegree + 1),
        homogeneousProjection k V b n (homogeneousProjection k V b i s) * t := by
    rw [← Finset.sum_mul, ← map_sum, sum_homogeneousProjection]
  rw [hl, hr]
  apply Finset.sum_congr rfl
  intro i _
  rw [homogeneousProjection_of_mem k V b
      (homogeneousS_mul k V b (homogeneousProjection_mem k V b i s) ht),
    homogeneousProjection_of_mem k V b (homogeneousProjection_mem k V b i s)]
  by_cases h : n = i <;> simp [h, Nat.add_right_cancel_iff]

section TensorProjection

variable (W : Type*) [AddCommGroup W] [_root_.Module k W]

/-- Actual coefficientwise projection on the original tensor module. -/
def tensorProjection (n : ℕ) :
    (S k V ⊗[k] W) →ₗ[k] (S k V ⊗[k] W) :=
  TensorProduct.map (homogeneousProjection k V b n) LinearMap.id

@[simp] theorem tensorProjection_tmul (n : ℕ) (s : S k V) (w : W) :
    tensorProjection k V b W n (s ⊗ₜ[k] w) =
      homogeneousProjection k V b n s ⊗ₜ[k] w := rfl

theorem tensorProjection_mem (n : ℕ) (x : S k V ⊗[k] W) :
    tensorProjection k V b W n x ∈ tensorHomogeneous k V b W n := by
  induction x with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using (tensorHomogeneous k V b W n).add_mem hx hy
  | tmul s w =>
    exact tmul_mem_tensorHomogeneous k V b W n
      (homogeneousProjection k V b n s) (homogeneousProjection_mem k V b n s) w

theorem tensorProjection_of_mem {n m : ℕ} {x : S k V ⊗[k] W}
    (hx : x ∈ tensorHomogeneous k V b W m) :
    tensorProjection k V b W n x = if n = m then x else 0 := by
  classical
  have hle : tensorHomogeneous k V b W m ≤ LinearMap.eqLocus
      (tensorProjection k V b W n) (if n = m then LinearMap.id else 0) := by
    apply Submodule.span_le.mpr
    rintro x ⟨s, hs, w, rfl⟩
    change tensorProjection k V b W n (s ⊗ₜ[k] w) =
      (if n = m then LinearMap.id else 0) (s ⊗ₜ[k] w)
    rw [tensorProjection_tmul, homogeneousProjection_of_mem k V b hs]
    by_cases h : n = m <;> simp [h]
  have h := hle hx
  change tensorProjection k V b W n x = (if n = m then LinearMap.id else 0) x at h
  by_cases hnm : n = m <;> simpa [hnm] using h

end TensorProjection

/-- The actual second differential commutes with homogeneous projection,
with its genuine coefficient-degree shift. -/
theorem delta2_projection_commutes [Fintype ι] (n : ℕ) :
    tensorProjection k V b V (n + 1) ∘ₗ (delta2 k V).restrictScalars k =
      (delta2 k V).restrictScalars k ∘ₗ tensorProjection k V b (⋀[k]^2 V) n := by
  apply TensorProduct.ext'
  intro s w
  change tensorProjection k V b V (n + 1) (delta2 k V (s ⊗ₜ[k] w)) =
    delta2 k V (homogeneousProjection k V b n s ⊗ₜ[k] w)
  let f : (⋀[k]^2 V) →ₗ[k] C1 k V :=
    tensorProjection k V b V (n + 1) ∘ₗ (delta2 k V).restrictScalars k ∘ₗ
      TensorProduct.mk k (S k V) (⋀[k]^2 V) s
  let g : (⋀[k]^2 V) →ₗ[k] C1 k V :=
    (delta2 k V).restrictScalars k ∘ₗ
      TensorProduct.mk k (S k V) (⋀[k]^2 V) (homogeneousProjection k V b n s)
  have hfg : f = g := by
    apply exteriorPower.linearMap_ext
    ext a
    simp only [f, g, LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, TensorProduct.mk_apply, delta2_tmul,
      delta2Linear_wedge, smul_sub, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one, map_sub, tensorProjection_tmul]
    rw [homogeneousProjection_mul_of_homogeneous k V b n 1 s
        (SymmetricAlgebra.ι k V (a 0)) (homogeneousS_ι k V b (a 0)),
      homogeneousProjection_mul_of_homogeneous k V b n 1 s
        (SymmetricAlgebra.ι k V (a 1)) (homogeneousS_ι k V b (a 1))]
  exact DFunLike.congr_fun hfg w

variable [Fintype ι] (K : Submodule k (⋀[k]^2 V))

theorem delta2K_projection_commutes (n : ℕ) (x : S k V ⊗[k] K) :
    tensorProjection k V b V (n + 1) (delta2K k V K x) =
      delta2K k V K (tensorProjection k V b K n x) := by
  induction x with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul s w =>
    change tensorProjection k V b V (n + 1) (delta2 k V (s ⊗ₜ[k] (w : ⋀[k]^2 V))) =
      delta2 k V (homogeneousProjection k V b n s ⊗ₜ[k] (w : ⋀[k]^2 V))
    exact DFunLike.congr_fun (delta2_projection_commutes k V b n) (s ⊗ₜ[k] (w : ⋀[k]^2 V))

/-- The original homogeneous projection, with codomain the actual piece. -/
def homogeneousProjectionInto (n : ℕ) : S k V →ₗ[k] homogeneousS k V b n :=
  (homogeneousProjection k V b n).codRestrict (homogeneousS k V b n)
    (homogeneousProjection_mem k V b n)

/-- Recover actual homogeneous relation coefficients from arbitrary original
coefficients, retaining their actual quadratic relation factors. -/
def projectedRelationCoefficients (n : ℕ) :
    (S k V ⊗[k] K) →ₗ[k] (homogeneousS k V b n ⊗[k] K) :=
  TensorProduct.map (homogeneousProjectionInto k V b n) LinearMap.id

theorem projectedRelation_degree_coe (n : ℕ) (x : S k V ⊗[k] K) :
    (relationDegree k V b K n (projectedRelationCoefficients k V b K n x) : C1 k V) =
      tensorProjection k V b V (n + 1) (delta2K k V K x) := by
  induction x with
  | zero => simp
  | add x y hx hy => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hx hy
  | tmul s w =>
    change delta2 k V (homogeneousProjection k V b n s ⊗ₜ[k] (w : ⋀[k]^2 V)) =
      tensorProjection k V b V (n + 1) (delta2 k V (s ⊗ₜ[k] (w : ⋀[k]^2 V)))
    exact (DFunLike.congr_fun (delta2_projection_commutes k V b n)
      (s ⊗ₜ[k] (w : ⋀[k]^2 V))).symm

/-- The actual inclusion of homogeneous cycles in the original cycle module. -/
def degreeCycleInclusion (r : ℕ) :
    cycleDegree k V b r →ₗ[k] LinearMap.ker (delta1 k V) where
  toFun z := ⟨z.val, z.property.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem relationDegree_original_relation (r : ℕ)
    (x : homogeneousS k V b r ⊗[k] K) :
    relationMap k V K
        (TensorProduct.map (homogeneousS k V b r).subtype LinearMap.id x) =
      degreeCycleInclusion k V b r (relationDegree k V b K r x) := by
  apply Subtype.ext
  induction x with
  | zero => simp
  | add x y hx hy => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hx hy
  | tmul s w => rfl

/-- An original relation which is homogeneous has a genuine homogeneous
relation witness.  This is the essential non-assumed quotient-grading bridge. -/
theorem degreeCycle_mem_original_relations_iff (r : ℕ) (z : cycleDegree k V b r) :
    degreeCycleInclusion k V b r z ∈ LinearMap.range (relationMap k V K) ↔
      z ∈ LinearMap.range (relationDegree k V b K r) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨projectedRelationCoefficients k V b K r x, ?_⟩
    apply Subtype.ext
    rw [projectedRelation_degree_coe]
    have hx' : delta2K k V K x = (z : C1 k V) := congrArg Subtype.val hx
    rw [hx', tensorProjection_of_mem k V b V z.property.1]
    simp
  · rintro ⟨x, rfl⟩
    exact ⟨TensorProduct.map (homogeneousS k V b r).subtype LinearMap.id x,
      relationDegree_original_relation k V b K r x⟩

/-- The actual homogeneous cycles mapped into the original ungraded quotient. -/
def degreeCycleToUngraded (r : ℕ) :
    cycleDegree k V b r →ₗ[k] Module k V K :=
  (LinearMap.range (relationMap k V K)).mkQ.restrictScalars k ∘ₗ
    degreeCycleInclusion k V b r

theorem degreeCycleToUngraded_ker (r : ℕ) :
    LinearMap.ker (degreeCycleToUngraded k V b K r) =
      LinearMap.range (relationDegree k V b K r) := by
  ext z
  rw [LinearMap.mem_ker]
  change (Submodule.Quotient.mk (degreeCycleInclusion k V b r z) : Module k V K) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  exact degreeCycle_mem_original_relations_iff k V b K r z

/-- A genuine degreewise quotient is equivalent to its actual image inside
the original quotient.  The equality of the kernels was proved above. -/
def homogeneousModuleEquivOriginalDegree (r : ℕ) :
    homogeneousModule k V b K r ≃ₗ[k]
      LinearMap.range (degreeCycleToUngraded k V b K r) :=
  Submodule.quotEquivOfEq _ _ (degreeCycleToUngraded_ker k V b K r).symm ≪≫ₗ
    (degreeCycleToUngraded k V b K r).quotKerEquivRange

end ChenRanks.Koszul
