import ChenRanks.KoszulCycleGrading

/-!
# Actual direct-sum recomposition of the Koszul quotient

The actual cycle projections descend to the original quotient because they
carry original relations to genuine homogeneous relations.  They extract
exactly the corresponding degreewise quotient and annihilate other degrees.
These identities prove that the canonical assembly map from the direct sum
is injective.  The proved finite cycle decomposition proves surjectivity.

The inherited action of genuinely homogeneous symmetric-algebra elements
also carries an actual quotient-degree image to the correct new degree.
Neither a grading decomposition nor a relation-homogeneity premise is input.
-/

noncomputable section

open TensorProduct
open scoped BigOperators TensorProduct DirectSum

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} [Fintype ι] (b : _root_.Module.Basis ι k V)
variable (K : Submodule k (⋀[k]^2 V))

/-- The actual map from a degreewise quotient to the original quotient,
constructed by its proved kernel rather than supplied as an inclusion. -/
def degreeQuotientInclusion (r : ℕ) :
    homogeneousModule k V b K r →ₗ[k] Module k V K :=
  (LinearMap.range (relationDegree k V b K r)).liftQ
    (degreeCycleToUngraded k V b K r)
    (by rw [degreeCycleToUngraded_ker])

@[simp] theorem degreeQuotientInclusion_mk (r : ℕ) (z : cycleDegree k V b r) :
    degreeQuotientInclusion k V b K r (Submodule.Quotient.mk z) =
      degreeCycleToUngraded k V b K r z := rfl

/-- Projecting an original relation gives an actual degreewise relation. -/
theorem cycleProjection_relationMap (r : ℕ) (x : S k V ⊗[k] K) :
    cycleProjection k V b r (relationMap k V K x) =
      relationDegree k V b K r (projectedRelationCoefficients k V b K r x) := by
  apply Subtype.ext
  exact (projectedRelation_degree_coe k V b K r x).symm

/-- Original cycles mapped to their actual homogeneous quotient. -/
def cycleToHomogeneousQuotient (r : ℕ) :
    LinearMap.ker (delta1 k V) →ₗ[k] homogeneousModule k V b K r :=
  (LinearMap.range (relationDegree k V b K r)).mkQ ∘ₗ cycleProjection k V b r

/-- An original relation is in the proved kernel of the quotient-valued
cycle projection, with the original polynomial-scalar action restricted. -/
theorem original_relations_le_projection_kernel (r : ℕ) :
    (LinearMap.range (relationMap k V K)).restrictScalars k ≤
      LinearMap.ker (cycleToHomogeneousQuotient k V b K r) := by
  rintro z ⟨x, rfl⟩
  apply LinearMap.mem_ker.mpr
  change (Submodule.Quotient.mk (cycleProjection k V b r (relationMap k V K x)) :
    homogeneousModule k V b K r) = 0
  rw [Submodule.Quotient.mk_eq_zero, cycleProjection_relationMap]
  exact LinearMap.mem_range_self _ _

/-- The actual degree projection on the original quotient.  The scalar
restriction equivalence is the genuine canonical quotient equivalence. -/
def quotientProjection (r : ℕ) : Module k V K →ₗ[k] homogeneousModule k V b K r :=
  ((LinearMap.range (relationMap k V K)).restrictScalars k).liftQ
      (cycleToHomogeneousQuotient k V b K r)
      (original_relations_le_projection_kernel k V b K r) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv k
      (LinearMap.range (relationMap k V K))).symm.toLinearMap

@[simp] theorem quotientProjection_mk (r : ℕ) (z : LinearMap.ker (delta1 k V)) :
    quotientProjection k V b K r (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (cycleProjection k V b r z) := rfl

theorem cycleProjection_degreeCycleInclusion_self (r : ℕ) (z : cycleDegree k V b r) :
    cycleProjection k V b r (degreeCycleInclusion k V b r z) = z := by
  apply Subtype.ext
  change tensorProjection k V b V (r + 1) z = z.val
  rw [tensorProjection_of_mem k V b V z.property.1]
  simp

theorem cycleProjection_degreeCycleInclusion_ne (r m : ℕ) (h : r ≠ m)
    (z : cycleDegree k V b m) :
    cycleProjection k V b r (degreeCycleInclusion k V b m z) = 0 := by
  apply Subtype.ext
  change tensorProjection k V b V (r + 1) z = 0
  rw [tensorProjection_of_mem k V b V z.property.1]
  simp [Nat.add_right_cancel_iff, h]

/-- The descended projection extracts its own actual degreewise quotient. -/
theorem quotientProjection_degreeQuotientInclusion_self (r : ℕ)
    (w : homogeneousModule k V b K r) :
    quotientProjection k V b K r (degreeQuotientInclusion k V b K r w) = w := by
  refine Submodule.Quotient.induction_on _ w ?_
  intro z
  rw [degreeQuotientInclusion_mk]
  change quotientProjection k V b K r
    (Submodule.Quotient.mk (degreeCycleInclusion k V b r z)) = Submodule.Quotient.mk z
  rw [quotientProjection_mk, cycleProjection_degreeCycleInclusion_self]

/-- Different actual degreewise quotients are annihilated by the projection. -/
theorem quotientProjection_degreeQuotientInclusion_ne (r m : ℕ) (h : r ≠ m)
    (w : homogeneousModule k V b K m) :
    quotientProjection k V b K r (degreeQuotientInclusion k V b K m w) = 0 := by
  refine Submodule.Quotient.induction_on _ w ?_
  intro z
  rw [degreeQuotientInclusion_mk]
  change quotientProjection k V b K r
    (Submodule.Quotient.mk (degreeCycleInclusion k V b m z)) = 0
  rw [quotientProjection_mk, cycleProjection_degreeCycleInclusion_ne k V b r m h]
  exact map_zero (LinearMap.range (relationDegree k V b K r)).mkQ

/-- Canonical assembly from the actual direct sum of degreewise quotients
to the original quotient. -/
def assembleHomogeneous :
    (⨁ r : ℕ, homogeneousModule k V b K r) →ₗ[k] Module k V K :=
  DirectSum.toModule k ℕ (Module k V K) (degreeQuotientInclusion k V b K)

@[simp] theorem assembleHomogeneous_lof (r : ℕ) (w : homogeneousModule k V b K r) :
    assembleHomogeneous k V b K
      (DirectSum.lof k ℕ (homogeneousModule k V b K) r w) =
      degreeQuotientInclusion k V b K r w := DirectSum.toModule_lof k r w

/-- The actual quotient projection composed with assembly is the genuine
direct-sum component map. -/
theorem quotientProjection_comp_assembleHomogeneous (r : ℕ) :
    quotientProjection k V b K r ∘ₗ assembleHomogeneous k V b K =
      DirectSum.component k ℕ (homogeneousModule k V b K) r := by
  apply DirectSum.linearMap_ext
  intro m
  apply LinearMap.ext
  intro w
  change quotientProjection k V b K r
      (assembleHomogeneous k V b K (DirectSum.lof k ℕ (homogeneousModule k V b K) m w)) =
    DirectSum.component k ℕ (homogeneousModule k V b K) r
      (DirectSum.lof k ℕ (homogeneousModule k V b K) m w)
  rw [assembleHomogeneous_lof]
  by_cases h : r = m
  · subst m
    rw [quotientProjection_degreeQuotientInclusion_self, DirectSum.component.lof_self]
  · rw [quotientProjection_degreeQuotientInclusion_ne k V b K r m h,
      DirectSum.component.of]
    simp [Ne.symm h]

theorem assembleHomogeneous_injective :
    Function.Injective (assembleHomogeneous k V b K) := by
  intro x y h
  apply DirectSum.ext_component k
  intro r
  have hx := DFunLike.congr_fun (quotientProjection_comp_assembleHomogeneous k V b K r) x
  have hy := DFunLike.congr_fun (quotientProjection_comp_assembleHomogeneous k V b K r) y
  change quotientProjection k V b K r (assembleHomogeneous k V b K x) =
    DirectSum.component k ℕ (homogeneousModule k V b K) r x at hx
  change quotientProjection k V b K r (assembleHomogeneous k V b K y) =
    DirectSum.component k ℕ (homogeneousModule k V b K) r y at hy
  exact hx.symm.trans ((congrArg (quotientProjection k V b K r) h).trans hy)

/-- Surjectivity follows from the proved finite decomposition of original
cycles, including the proved absence of coefficient-degree-zero cycles. -/
theorem assembleHomogeneous_surjective :
    Function.Surjective (assembleHomogeneous k V b K) := by
  intro w
  refine Submodule.Quotient.induction_on _ w ?_
  intro z
  obtain ⟨N, hN⟩ := exists_sum_cycleProjection k V b z
  refine ⟨∑ r ∈ Finset.range N, DirectSum.lof k ℕ (homogeneousModule k V b K) r
      (Submodule.Quotient.mk (cycleProjection k V b r z)), ?_⟩
  rw [map_sum]
  simp only [assembleHomogeneous_lof, degreeQuotientInclusion_mk]
  change (∑ r ∈ Finset.range N,
    (LinearMap.range (relationMap k V K)).mkQ
      (degreeCycleInclusion k V b r (cycleProjection k V b r z))) =
    (LinearMap.range (relationMap k V K)).mkQ z
  rw [← map_sum, hN]

/-- Actual recomposition of the manuscript's genuine `W_r` into the
original Koszul quotient.  Both inverse identities follow from actual
projection and finite decomposition proofs, rather than a grading input. -/
def homogeneousDirectSumEquiv :
    (⨁ r : ℕ, homogeneousModule k V b K r) ≃ₗ[k] Module k V K :=
  LinearEquiv.ofBijective (assembleHomogeneous k V b K)
    ⟨assembleHomogeneous_injective k V b K, assembleHomogeneous_surjective k V b K⟩

/-- Genuinely homogeneous polynomial scalars carry actual cycle degrees
to the correct shifted degree. -/
def homogeneousSmulCycle (n r : ℕ) (s : homogeneousS k V b n)
    (z : cycleDegree k V b r) : cycleDegree k V b (n + r) :=
  ⟨(s : S k V) • (z : C1 k V), ⟨by
    simpa only [Nat.add_assoc] using smul_mem_tensorHomogeneous k V b V
      (s : S k V) s.property (z : C1 k V) z.property.1,
    by
      change delta1 k V ((s : S k V) • (z : C1 k V)) = 0
      have hz : delta1 k V (z : C1 k V) = 0 := LinearMap.mem_ker.mp z.property.2
      rw [map_smul, hz, smul_zero]⟩⟩

omit [Fintype ι] in
/-- The original polynomial-scalar action respects the actual quotient
degree images; the scalar and image memberships are genuine homogeneous
memberships, not an assumed graded-module structure. -/
theorem homogeneous_smul_originalDegree_mem (n r : ℕ) (s : homogeneousS k V b n)
    (w : Module k V K)
    (hw : w ∈ LinearMap.range (degreeCycleToUngraded k V b K r)) :
    (s : S k V) • w ∈ LinearMap.range (degreeCycleToUngraded k V b K (n + r)) := by
  obtain ⟨z, rfl⟩ := hw
  refine ⟨homogeneousSmulCycle k V b n r s z, ?_⟩
  change (LinearMap.range (relationMap k V K)).mkQ
      (degreeCycleInclusion k V b (n + r) (homogeneousSmulCycle k V b n r s z)) =
    (s : S k V) • (LinearMap.range (relationMap k V K)).mkQ (degreeCycleInclusion k V b r z)
  rw [← map_smul]
  rfl

end ChenRanks.Koszul
