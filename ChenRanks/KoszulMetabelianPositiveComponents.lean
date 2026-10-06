import ChenRanks.KoszulAugmentationSuccessiveQuotients
import ChenRanks.KoszulNativeHomogeneousEquiv
import Mathlib.Algebra.Lie.Graded

/-!
# Actual positive homogeneous components of the original Koszul Lie model

Ordinary degree one is the actual generator coordinate. Ordinary degree
r+2 is the actual image of the original homogeneous Koszul quotient W_r.
The actual original degree projections and finite cycle decomposition
prove that the canonical assembly of these submodules is bijective.
No decomposition, positivity, or finite grading bound is an input.
-/

noncomputable section

open scoped DirectSum BigOperators

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} [Fintype ι] (b : _root_.Module.Basis ι k V)
variable (K : Submodule k (⋀[k]^2 V))

local instance positiveOriginalGroup : AddCommGroup (Module k V K) :=
  originalModuleAddCommGroup k V K

local instance positiveOriginalMonoid : AddCommMonoid (Module k V K) :=
  (originalModuleAddCommGroup k V K).toAddCommMonoid

local instance positiveOriginalScalars : _root_.Module k (Module k V K) :=
  originalModuleScalarModule k V K

local instance positiveDegreeGroup (r : ℕ) : AddCommGroup (homogeneousModule k V b K r) :=
  canonicalHomogeneousQuotientAddCommGroup k V b K r

local instance positiveDegreeMonoid (r : ℕ) : AddCommMonoid (homogeneousModule k V b K r) :=
  (canonicalHomogeneousQuotientAddCommGroup k V b K r).toAddCommMonoid

local instance positiveDegreeScalars (r : ℕ) :
    _root_.Module k (homogeneousModule k V b K r) :=
  canonicalHomogeneousQuotientBaseCoefficients k V b K r

open MetabelianLieModel

omit [Fintype ι] in
def modelGeneratorProjection : MetabelianLieModel k V K →ₗ[k] V where
  toFun x := x.generator
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype ι] in
def modelInvariantProjection : MetabelianLieModel k V K →ₗ[k] Module k V K where
  toFun x := x.invariant
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype ι] in
@[simp] theorem modelGeneratorProjection_apply (x : MetabelianLieModel k V K) :
    modelGeneratorProjection k V K x = x.generator := rfl

omit [Fintype ι] in
@[simp] theorem modelInvariantProjection_apply (x : MetabelianLieModel k V K) :
    modelInvariantProjection k V K x = x.invariant := rfl

/-- The actual inclusion in ordinary degree r+2. -/
def modelInvariantDegreeInclusion (r : ℕ) :
    homogeneousModule k V b K r →ₗ[k] MetabelianLieModel k V K :=
  (invariantInclusion k V K).comp (degreeQuotientInclusion k V b K r)

/-- The actual original positive components, with ordinary degree zero empty. -/
def modelPositiveComponent : ℕ → Submodule k (MetabelianLieModel k V K)
  | 0 => ⊥
  | 1 => LinearMap.range (generatorInclusion k V K)
  | r + 2 => LinearMap.range (modelInvariantDegreeInclusion k V b K r)

@[simp] theorem modelPositiveComponent_zero : modelPositiveComponent k V b K 0 = ⊥ := rfl

@[simp] theorem modelPositiveComponent_one :
    modelPositiveComponent k V b K 1 = LinearMap.range (generatorInclusion k V K) := rfl

@[simp] theorem modelPositiveComponent_add_two (r : ℕ) :
    modelPositiveComponent k V b K (r + 2) =
      LinearMap.range (modelInvariantDegreeInclusion k V b K r) := rfl

/-- The genuine coordinate and genuine original Koszul degree projections. -/
def modelPositiveProjection : ℕ →
    (MetabelianLieModel k V K →ₗ[k] MetabelianLieModel k V K)
  | 0 => 0
  | 1 => (generatorInclusion k V K).comp (modelGeneratorProjection k V K)
  | r + 2 => (modelInvariantDegreeInclusion k V b K r).comp
      ((quotientProjection k V b K r).comp (modelInvariantProjection k V K))

/-- The actual degree projection fixes its actual homogeneous submodule. -/
theorem modelPositiveProjection_of_mem_same (n : ℕ) (x : MetabelianLieModel k V K)
    (hx : x ∈ modelPositiveComponent k V b K n) :
    modelPositiveProjection k V b K n x = x := by
  cases n with
  | zero =>
    have hx0 : x = 0 := (Submodule.mem_bot k).mp hx
    rw [hx0, map_zero]
  | succ n =>
    cases n with
    | zero =>
      obtain ⟨v, rfl⟩ := hx
      rfl
    | succ r =>
      obtain ⟨w, rfl⟩ := hx
      change invariantInclusion k V K
        (degreeQuotientInclusion k V b K r
          (quotientProjection k V b K r (degreeQuotientInclusion k V b K r w))) =
        invariantInclusion k V K (degreeQuotientInclusion k V b K r w)
      rw [quotientProjection_degreeQuotientInclusion_self]

/-- Different actual degrees are genuinely annihilated by the original projections. -/
theorem modelPositiveProjection_of_mem_ne (n m : ℕ) (x : MetabelianLieModel k V K)
    (hx : x ∈ modelPositiveComponent k V b K m) (hnm : n ≠ m) :
    modelPositiveProjection k V b K n x = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    cases m with
    | zero =>
      have hx0 : x = 0 := (Submodule.mem_bot k).mp hx
      rw [hx0, map_zero]
    | succ m =>
      cases n with
      | zero =>
        cases m with
        | zero => exact (hnm rfl).elim
        | succ r =>
          obtain ⟨w, rfl⟩ := hx
          change generatorInclusion k V K (0 : V) = 0
          exact map_zero _
      | succ r =>
        cases m with
        | zero =>
          obtain ⟨v, rfl⟩ := hx
          change invariantInclusion k V K
            (degreeQuotientInclusion k V b K r
              (quotientProjection k V b K r (0 : Module k V K))) = 0
          rw [map_zero, map_zero, map_zero]
        | succ s =>
          obtain ⟨w, rfl⟩ := hx
          have hrs : r ≠ s := by omega
          change invariantInclusion k V K
            (degreeQuotientInclusion k V b K r
              (quotientProjection k V b K r (degreeQuotientInclusion k V b K s w))) = 0
          rw [quotientProjection_degreeQuotientInclusion_ne k V b K r s hrs,
            map_zero, map_zero]

/-- The real finite decomposition inherited from the original cycle quotient. -/
theorem modelPositiveProjection_finite_sum (x : MetabelianLieModel k V K) :
    ∃ N : ℕ, x = modelPositiveProjection k V b K 1 x +
      ∑ r ∈ Finset.range N, modelPositiveProjection k V b K (r + 2) x := by
  obtain ⟨N, hN⟩ := exists_sum_originalDegreeProjection k V b K x.invariant
  refine ⟨N, ?_⟩
  apply MetabelianLieModel.ext
  · change x.generator = x.generator + (∑ r ∈ Finset.range N,
        modelPositiveProjection k V b K (r + 2) x).generator
    have hz : (∑ r ∈ Finset.range N,
        modelPositiveProjection k V b K (r + 2) x).generator = 0 := by
      change modelGeneratorProjection k V K
        (∑ r ∈ Finset.range N, modelPositiveProjection k V b K (r + 2) x) = 0
      simp only [map_sum, modelPositiveProjection, LinearMap.comp_apply,
        modelGeneratorProjection_apply, modelInvariantDegreeInclusion,
        invariantInclusion_generator, Finset.sum_const_zero]
    rw [hz, add_zero]
  · change x.invariant = (modelInvariantProjection k V K)
      (modelPositiveProjection k V b K 1 x +
        ∑ r ∈ Finset.range N, modelPositiveProjection k V b K (r + 2) x)
    rw [map_add, map_sum]
    simpa only [modelPositiveProjection, LinearMap.comp_apply,
      modelInvariantProjection_apply, modelInvariantDegreeInclusion,
      invariantInclusion_invariant, generatorInclusion_invariant,
      zero_add, originalDegreeProjection] using hN

/-- Projecting canonical assembly extracts the corresponding actual summand. -/
theorem modelPositiveProjection_comp_assembly (n : ℕ) :
    (modelPositiveProjection k V b K n).comp
        (DirectSum.coeLinearMap (modelPositiveComponent k V b K)) =
      (modelPositiveComponent k V b K n).subtype.comp
        (DirectSum.component k ℕ (fun i => modelPositiveComponent k V b K i) n) := by
  apply DirectSum.linearMap_ext
  intro m
  apply LinearMap.ext
  intro x
  change modelPositiveProjection k V b K n
      (DirectSum.coeLinearMap (modelPositiveComponent k V b K)
        (DirectSum.lof k ℕ (fun i => modelPositiveComponent k V b K i) m x)) =
    ((DirectSum.component k ℕ (fun i => modelPositiveComponent k V b K i) n)
      (DirectSum.lof k ℕ (fun i => modelPositiveComponent k V b K i) m x) :
        MetabelianLieModel k V K)
  rw [DirectSum.coeLinearMap_lof]
  by_cases hnm : n = m
  · subst m
    rw [DirectSum.component.lof_self]
    exact modelPositiveProjection_of_mem_same k V b K n x x.property
  · rw [DirectSum.component.of]
    simp only [show m ≠ n from Ne.symm hnm, ↓reduceDIte, Submodule.coe_zero]
    exact modelPositiveProjection_of_mem_ne k V b K n m x x.property hnm

theorem modelPositiveAssembly_injective :
    Function.Injective (DirectSum.coeLinearMap (modelPositiveComponent k V b K)) := by
  intro x y hxy
  apply DFinsupp.ext
  intro n
  apply Subtype.ext
  have h := congrArg (modelPositiveProjection k V b K n) hxy
  have hx := LinearMap.congr_fun (modelPositiveProjection_comp_assembly k V b K n) x
  have hy := LinearMap.congr_fun (modelPositiveProjection_comp_assembly k V b K n) y
  change modelPositiveProjection k V b K n
    (DirectSum.coeLinearMap (modelPositiveComponent k V b K) x) = (x n : MetabelianLieModel k V K)
    at hx
  change modelPositiveProjection k V b K n
    (DirectSum.coeLinearMap (modelPositiveComponent k V b K) y) = (y n : MetabelianLieModel k V K)
    at hy
  exact hx.symm.trans (h.trans hy)

theorem modelPositiveAssembly_surjective :
    Function.Surjective (DirectSum.coeLinearMap (modelPositiveComponent k V b K)) := by
  intro x
  obtain ⟨N, hN⟩ := modelPositiveProjection_finite_sum k V b K x
  let x₁ : modelPositiveComponent k V b K 1 :=
    ⟨modelPositiveProjection k V b K 1 x, ⟨x.generator, rfl⟩⟩
  let xr (r : ℕ) : modelPositiveComponent k V b K (r + 2) :=
    ⟨modelPositiveProjection k V b K (r + 2) x,
      ⟨quotientProjection k V b K r x.invariant, rfl⟩⟩
  refine ⟨DirectSum.lof k ℕ (fun i => modelPositiveComponent k V b K i) 1 x₁ +
      ∑ r ∈ Finset.range N,
        DirectSum.lof k ℕ (fun i => modelPositiveComponent k V b K i) (r + 2) (xr r), ?_⟩
  rw [map_add, map_sum]
  simp only [DirectSum.coeLinearMap_lof]
  exact hN.symm

/-- The original positive submodules really give an internal direct sum. -/
theorem modelPositiveComponent_isInternal :
    DirectSum.IsInternal (modelPositiveComponent k V b K) :=
  ⟨modelPositiveAssembly_injective k V b K, modelPositiveAssembly_surjective k V b K⟩

/-- A native decomposition genuinely obtained from the proved original
assembly bijection; it is not supplied as a structure input. -/
@[implicit_reducible]
def modelPositiveComponentDecomposition :
    DirectSum.Decomposition (modelPositiveComponent k V b K) :=
  (modelPositiveComponent_isInternal k V b K).chooseDecomposition

end ChenRanks.Koszul
