import ChenRanks.KoszulMetabelianPositiveComponents

/-!
# The original Koszul model is genuinely positively graded

The grading is the actual family of original submodules constructed in
`KoszulMetabelianPositiveComponents`. Generator-generator brackets are
the actual constant second-tensor classes. Generator-invariant brackets
are the actual homogeneous symmetric-generator action, and two invariant
coordinates bracket to zero. These facts prove the native graded-bracket
instance; no homogeneous-bracket or grading law is an input.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct DirectSum BigOperators

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} [Fintype ι] (b : _root_.Module.Basis ι k V)
variable (K : Submodule k (⋀[k]^2 V))

local instance positiveBracketOriginalGroup : AddCommGroup (Module k V K) :=
  originalModuleAddCommGroup k V K

local instance positiveBracketOriginalMonoid : AddCommMonoid (Module k V K) :=
  (originalModuleAddCommGroup k V K).toAddCommMonoid

local instance positiveBracketOriginalScalars : _root_.Module k (Module k V K) :=
  originalModuleScalarModule k V K

local instance positiveBracketDegreeGroup (r : ℕ) : AddCommGroup (homogeneousModule k V b K r) :=
  canonicalHomogeneousQuotientAddCommGroup k V b K r

local instance positiveBracketDegreeMonoid (r : ℕ) : AddCommMonoid (homogeneousModule k V b K r) :=
  (canonicalHomogeneousQuotientAddCommGroup k V b K r).toAddCommMonoid

local instance positiveBracketDegreeScalars (r : ℕ) :
    _root_.Module k (homogeneousModule k V b K r) :=
  canonicalHomogeneousQuotientBaseCoefficients k V b K r

open MetabelianLieModel

/-- An actual homogeneous cycle image gives an actual ordinary-degree
element after the original invariant inclusion. -/
theorem invariantInclusion_mem_modelPositiveComponent (r : ℕ) (w : Module k V K)
    (hw : w ∈ LinearMap.range (degreeCycleToUngraded k V b K r)) :
    invariantInclusion k V K w ∈ modelPositiveComponent k V b K (r + 2) := by
  obtain ⟨z, rfl⟩ := hw
  refine ⟨Submodule.Quotient.mk z, ?_⟩
  rfl

/-- The actual constant bracket belongs to the original degree-zero
Koszul image and therefore to ordinary Lie degree two. -/
theorem generators_bracket_mem_modelPositiveComponent (u v : V) :
    ⁅generatorInclusion k V K u, generatorInclusion k V K v⁆ ∈
      modelPositiveComponent k V b K 2 := by
  rw [generators_bracket]
  apply invariantInclusion_mem_modelPositiveComponent k V b K 0
  change secondTensorToModule k V K
      ((1 : S k V) ⊗ₜ[k] exteriorWedge u v) ∈
    LinearMap.range (degreeCycleToUngraded k V b K 0)
  exact secondTensorToModule_tmul_mem_originalDegree k V b K 0 1
    (homogeneousS_one k V b) (exteriorWedge u v)

/-- The actual symmetric generator action raises the ordinary degree by one. -/
theorem generator_invariant_degree_bracket_mem (r : ℕ) (u : V)
    (w : homogeneousModule k V b K r) :
    ⁅generatorInclusion k V K u, modelInvariantDegreeInclusion k V b K r w⁆ ∈
      modelPositiveComponent k V b K (r + 3) := by
  change ⁅generatorInclusion k V K u,
      invariantInclusion k V K (degreeQuotientInclusion k V b K r w)⁆ ∈
    modelPositiveComponent k V b K (r + 3)
  rw [generator_invariant_bracket]
  have hw := homogeneous_smul_originalDegree_mem k V b K 1 r
    ⟨SymmetricAlgebra.ι k V u, homogeneousS_ι k V b u⟩
    (degreeQuotientInclusion k V b K r w)
    (degreeQuotientInclusion_mem_originalDegree k V b K r w)
  have h := invariantInclusion_mem_modelPositiveComponent k V b K (1 + r)
    (SymmetricAlgebra.ι k V u • degreeQuotientInclusion k V b K r w) hw
  simpa only [show (1 + r) + 2 = r + 3 by omega] using h

/-- Brackets of actual homogeneous submodules add their ordinary degrees. -/
theorem modelPositiveComponent_bracket_mem {i j : ℕ}
    {x y : MetabelianLieModel k V K}
    (hx : x ∈ modelPositiveComponent k V b K i)
    (hy : y ∈ modelPositiveComponent k V b K j) :
    ⁅x, y⁆ ∈ modelPositiveComponent k V b K (i + j) := by
  cases i with
  | zero =>
    have hx0 : x = 0 := (Submodule.mem_bot k).mp hx
    rw [hx0, zero_lie]
    exact Submodule.zero_mem _
  | succ i =>
    cases j with
    | zero =>
      have hy0 : y = 0 := (Submodule.mem_bot k).mp hy
      rw [hy0, lie_zero]
      exact Submodule.zero_mem _
    | succ j =>
      cases i with
      | zero =>
        obtain ⟨u, rfl⟩ := hx
        cases j with
        | zero =>
          obtain ⟨v, rfl⟩ := hy
          exact generators_bracket_mem_modelPositiveComponent k V b K u v
        | succ r =>
          obtain ⟨w, rfl⟩ := hy
          simpa only [show 1 + (r + 2) = r + 3 by omega] using
            generator_invariant_degree_bracket_mem k V b K r u w
      | succ r =>
        obtain ⟨w, rfl⟩ := hx
        cases j with
        | zero =>
          obtain ⟨u, rfl⟩ := hy
          rw [← lie_skew]
          apply Submodule.neg_mem
          simpa only [show (r + 2) + 1 = r + 3 by omega] using
            generator_invariant_degree_bracket_mem k V b K r u w
        | succ s =>
          obtain ⟨z, rfl⟩ := hy
          have hzero : ⁅modelInvariantDegreeInclusion k V b K r w,
              modelInvariantDegreeInclusion k V b K s z⁆ = 0 :=
            bracket_eq_zero_of_generator_eq_zero k V K rfl rfl
          rw [hzero]
          exact Submodule.zero_mem _

instance modelPositiveGradedBracket :
    SetLike.GradedBracket (modelPositiveComponent k V b K) where
  bracket_mem := by
    intro i j n x y hi hx hy
    rcases hi with rfl
    exact modelPositiveComponent_bracket_mem k V b K hx hy

/-- The original model carries a native graded Lie algebra structure,
constructed from its proved bracket law and its proved internal direct sum. -/
instance modelPositiveGradedLieAlgebra :
    GradedLieAlgebra (modelPositiveComponent k V b K) where
  toGradedBracket := modelPositiveGradedBracket k V b K
  toDecomposition := modelPositiveComponentDecomposition k V b K

end ChenRanks.Koszul
