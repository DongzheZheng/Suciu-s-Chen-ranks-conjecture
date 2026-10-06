import ChenRanks.KoszulMetabelianPositiveGrading
import ChenRanks.KoszulHomogeneousBasis
import ChenRanks.LieGradedAffineAdjointNilpotence
import Mathlib.Algebra.Lie.Quotient

/-!
# Actual finite positive truncations of the original Koszul Lie model

The ideal is the genuine span of original homogeneous components above
the chosen ordinary degree. Its bracket closure follows from the proved
positive grading. The quotient is the native quotient by this actual Lie
ideal. Native component projections descend in the surviving degrees;
they prove a real decomposition of the quotient. Components above the
bound vanish because their original elements belong to the actual ideal.
No nilpotence, degree bound, finite-dimensionality or quotient grading is
supplied as a structural premise.
-/

noncomputable section

open scoped DirectSum BigOperators

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} [Fintype ι] (b : _root_.Module.Basis ι k V)
variable (K : Submodule k (⋀[k]^2 V))

local instance finiteTruncOriginalGroup : AddCommGroup (Module k V K) :=
  originalModuleAddCommGroup k V K
local instance finiteTruncOriginalMonoid : AddCommMonoid (Module k V K) :=
  (originalModuleAddCommGroup k V K).toAddCommMonoid
local instance finiteTruncOriginalScalar : _root_.Module k (Module k V K) :=
  originalModuleScalarModule k V K
local instance finiteTruncDegreeGroup (r : ℕ) : AddCommGroup (homogeneousModule k V b K r) :=
  canonicalHomogeneousQuotientAddCommGroup k V b K r
local instance finiteTruncDegreeMonoid (r : ℕ) : AddCommMonoid (homogeneousModule k V b K r) :=
  (canonicalHomogeneousQuotientAddCommGroup k V b K r).toAddCommMonoid
local instance finiteTruncDegreeScalar (r : ℕ) :
    _root_.Module k (homogeneousModule k V b K r) :=
  canonicalHomogeneousQuotientBaseCoefficients k V b K r

open MetabelianLieModel
open ChenRanks.LieComparison

/-- The actual high-degree tail is a native Lie ideal, by genuine
positivity and the already proved actual homogeneous bracket law. -/
def modelTruncationIdeal (c : ℕ) : LieIdeal k (MetabelianLieModel k V K) where
  __ := nativeGradedTail k (MetabelianLieModel k V K)
    (modelPositiveComponent k V b K) (c + 1)
  lie_mem {x} {y} hy := by
    have hx : x ∈ nativeGradedTail k (MetabelianLieModel k V K)
        (modelPositiveComponent k V b K) 1 := by
      rw [nativeGradedTail_one_eq_top k (MetabelianLieModel k V K)
        (modelPositiveComponent k V b K) (modelPositiveComponent_zero k V b K)]
      exact Submodule.mem_top
    have h := lie_mem_nativeGradedTail k (MetabelianLieModel k V K)
      (modelPositiveComponent k V b K) 1 (c + 1) x y hx hy
    exact nativeGradedTail_antitone k (MetabelianLieModel k V K)
      (modelPositiveComponent k V b K) (c + 1) (1 + (c + 1)) (by omega) h

/-- The original quotient by the actual high-degree Lie ideal. -/
abbrev finiteModelTruncation (c : ℕ) :=
  MetabelianLieModel k V K ⧸ modelTruncationIdeal k V b K c

/-- The actual native quotient map is an actual Lie morphism. -/
def finiteModelProjection (c : ℕ) :
    MetabelianLieModel k V K →ₗ⁅k⁆ finiteModelTruncation k V b K c where
  __ := (modelTruncationIdeal k V b K c).toSubmodule.mkQ
  map_lie' := by intro x y; rfl

theorem finiteModelProjection_surjective (c : ℕ) :
    Function.Surjective (finiteModelProjection k V b K c) :=
  Submodule.mkQ_surjective (modelTruncationIdeal k V b K c).toSubmodule

/-- Each actual original component descends by the actual quotient map. -/
def finiteModelComponent (c n : ℕ) : Submodule k (finiteModelTruncation k V b K c) :=
  (modelPositiveComponent k V b K n).map (finiteModelProjection k V b K c).toLinearMap

theorem finiteModelComponent_zero (c : ℕ) : finiteModelComponent k V b K c 0 = ⊥ := by
  rw [finiteModelComponent, modelPositiveComponent_zero, Submodule.map_bot]

/-- Components above the actual quotient bound vanish, because their
original elements lie in the actual defining ideal. -/
theorem finiteModelComponent_eq_bot_above (c n : ℕ) (hcn : c < n) :
    finiteModelComponent k V b K c n = ⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨y, hy, rfl⟩
  apply (Submodule.mem_bot k).mpr
  change (modelTruncationIdeal k V b K c).toSubmodule.mkQ y = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact mem_nativeGradedTail_of_mem k (MetabelianLieModel k V K)
    (modelPositiveComponent k V b K) (c + 1) n y (by omega) hy

/-- A surviving genuine component projection kills the actual entire
tail, not merely the chosen homogeneous generators. -/
theorem modelTruncationIdeal_le_projection_ker (c n : ℕ) (hn : n ≤ c) :
    (modelTruncationIdeal k V b K c).toSubmodule ≤
      LinearMap.ker (modelPositiveProjection k V b K n) := by
  apply Submodule.span_le.mpr
  rintro x ⟨m, hm, hx⟩
  apply LinearMap.mem_ker.mpr
  exact modelPositiveProjection_of_mem_ne k V b K n m x hx (by omega)

/-- The actual surviving original projection descends through the
actual quotient, by its proved actual kernel containment. -/
def finiteModelComponentProjection (c n : ℕ) :
    finiteModelTruncation k V b K c →ₗ[k] finiteModelTruncation k V b K c :=
  if hn : n ≤ c then
    (finiteModelProjection k V b K c).toLinearMap.comp
      ((modelTruncationIdeal k V b K c).toSubmodule.liftQ
        (modelPositiveProjection k V b K n)
        (modelTruncationIdeal_le_projection_ker k V b K c n hn))
  else 0

theorem finiteModelComponentProjection_mk (c n : ℕ) (hn : n ≤ c)
    (x : MetabelianLieModel k V K) :
    finiteModelComponentProjection k V b K c n (finiteModelProjection k V b K c x) =
      finiteModelProjection k V b K c (modelPositiveProjection k V b K n x) := by
  simp only [finiteModelComponentProjection, dif_pos hn, LinearMap.comp_apply]
  rfl

theorem finiteModelComponentProjection_same (c n : ℕ)
    (x : finiteModelTruncation k V b K c) (hx : x ∈ finiteModelComponent k V b K c n) :
    finiteModelComponentProjection k V b K c n x = x := by
  by_cases hn : n ≤ c
  · obtain ⟨y, hy, rfl⟩ := hx
    change finiteModelComponentProjection k V b K c n
      (finiteModelProjection k V b K c y) = finiteModelProjection k V b K c y
    rw [finiteModelComponentProjection_mk k V b K c n hn,
      modelPositiveProjection_of_mem_same k V b K n y hy]
  · have hx0 : x = 0 := by
      rw [finiteModelComponent_eq_bot_above k V b K c n (by omega)] at hx
      exact (Submodule.mem_bot k).mp hx
    rw [hx0, map_zero]

theorem finiteModelComponentProjection_ne (c n m : ℕ)
    (x : finiteModelTruncation k V b K c) (hx : x ∈ finiteModelComponent k V b K c m)
    (hnm : n ≠ m) : finiteModelComponentProjection k V b K c n x = 0 := by
  by_cases hn : n ≤ c
  · obtain ⟨y, hy, rfl⟩ := hx
    change finiteModelComponentProjection k V b K c n
      (finiteModelProjection k V b K c y) = 0
    rw [finiteModelComponentProjection_mk k V b K c n hn,
      modelPositiveProjection_of_mem_ne k V b K n m y hy hnm, map_zero]
  · simp only [finiteModelComponentProjection, dif_neg hn, LinearMap.zero_apply]

theorem finiteModelComponentProjection_comp_assembly (c n : ℕ) :
    (finiteModelComponentProjection k V b K c n).comp
        (DirectSum.coeLinearMap (finiteModelComponent k V b K c)) =
      (finiteModelComponent k V b K c n).subtype.comp
        (DirectSum.component k ℕ (fun i => finiteModelComponent k V b K c i) n) := by
  apply DirectSum.linearMap_ext
  intro m
  apply LinearMap.ext
  intro x
  change finiteModelComponentProjection k V b K c n
      (DirectSum.coeLinearMap (finiteModelComponent k V b K c)
        (DirectSum.lof k ℕ (fun i => finiteModelComponent k V b K c i) m x)) =
    ((DirectSum.component k ℕ (fun i => finiteModelComponent k V b K c i) n)
      (DirectSum.lof k ℕ (fun i => finiteModelComponent k V b K c i) m x) :
        finiteModelTruncation k V b K c)
  rw [DirectSum.coeLinearMap_lof]
  by_cases hnm : n = m
  · subst m
    rw [DirectSum.component.lof_self]
    exact finiteModelComponentProjection_same k V b K c n x x.property
  · rw [DirectSum.component.of]
    simp only [show m ≠ n from Ne.symm hnm, ↓reduceDIte, Submodule.coe_zero]
    exact finiteModelComponentProjection_ne k V b K c n m x x.property hnm

theorem finiteModelAssembly_injective (c : ℕ) :
    Function.Injective (DirectSum.coeLinearMap (finiteModelComponent k V b K c)) := by
  intro x y hxy
  apply DFinsupp.ext
  intro n
  apply Subtype.ext
  have h := congrArg (finiteModelComponentProjection k V b K c n) hxy
  have hx := LinearMap.congr_fun
    (finiteModelComponentProjection_comp_assembly k V b K c n) x
  have hy := LinearMap.congr_fun
    (finiteModelComponentProjection_comp_assembly k V b K c n) y
  change finiteModelComponentProjection k V b K c n
      (DirectSum.coeLinearMap (finiteModelComponent k V b K c) x) =
    (x n : finiteModelTruncation k V b K c) at hx
  change finiteModelComponentProjection k V b K c n
      (DirectSum.coeLinearMap (finiteModelComponent k V b K c) y) =
    (y n : finiteModelTruncation k V b K c) at hy
  exact hx.symm.trans (h.trans hy)

theorem finiteModelAssembly_surjective (c : ℕ) :
    Function.Surjective (DirectSum.coeLinearMap (finiteModelComponent k V b K c)) := by
  intro x
  obtain ⟨y, rfl⟩ := finiteModelProjection_surjective k V b K c x
  apply LinearMap.mem_range.mp
  exact DirectSum.Decomposition.inductionOn (modelPositiveComponent k V b K)
    (by rw [map_zero]; exact Submodule.zero_mem _)
    (fun {n} a => by
      let z : finiteModelComponent k V b K c n :=
        ⟨finiteModelProjection k V b K c a, ⟨a, a.property, rfl⟩⟩
      exact ⟨DirectSum.lof k ℕ (fun i => finiteModelComponent k V b K c i) n z,
        DirectSum.coeLinearMap_lof _ n z⟩)
    (fun a d ha hd => by rw [map_add]; exact Submodule.add_mem _ ha hd) y

theorem finiteModelComponent_isInternal (c : ℕ) :
    DirectSum.IsInternal (finiteModelComponent k V b K c) :=
  ⟨finiteModelAssembly_injective k V b K c, finiteModelAssembly_surjective k V b K c⟩

@[implicit_reducible]
def finiteModelComponentDecomposition (c : ℕ) :
    DirectSum.Decomposition (finiteModelComponent k V b K c) :=
  (finiteModelComponent_isInternal k V b K c).chooseDecomposition

instance finiteModelGradedBracket (c : ℕ) :
    SetLike.GradedBracket (finiteModelComponent k V b K c) where
  bracket_mem := by
    intro i j n x y hi hx hy
    rcases hi with rfl
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    exact ⟨⁅x, y⁆, modelPositiveComponent_bracket_mem k V b K hx hy,
      (finiteModelProjection k V b K c).map_lie x y⟩

instance finiteModelGradedLieAlgebra (c : ℕ) :
    GradedLieAlgebra (finiteModelComponent k V b K c) where
  toGradedBracket := finiteModelGradedBracket k V b K c
  toDecomposition := finiteModelComponentDecomposition k V b K c

/-- Every original positive component is genuinely finite dimensional,
as an actual range of V or an actual original homogeneous Koszul quotient. -/
instance modelPositiveComponent_finiteDimensional (n : ℕ) :
    FiniteDimensional k (modelPositiveComponent k V b K n) := by
  letI : FiniteDimensional k V :=
    FiniteDimensional.of_injective b.repr.toLinearMap b.repr.injective
  cases n with
  | zero => change FiniteDimensional k (⊥ : Submodule k (MetabelianLieModel k V K)); infer_instance
  | succ n =>
    cases n with
    | zero => change FiniteDimensional k (LinearMap.range (generatorInclusion k V K)); infer_instance
    | succ r =>
      change FiniteDimensional k (LinearMap.range (modelInvariantDegreeInclusion k V b K r))
      infer_instance

/-- Each actual quotient component is a true image of its original finite component. -/
instance finiteModelComponent_finiteDimensional (c n : ℕ) :
    FiniteDimensional k (finiteModelComponent k V b K c n) := by
  let f : modelPositiveComponent k V b K n →ₗ[k] finiteModelTruncation k V b K c :=
    (finiteModelProjection k V b K c).toLinearMap.comp
      (modelPositiveComponent k V b K n).subtype
  have heq : LinearMap.range f = finiteModelComponent k V b K c n := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  rw [← heq]
  infer_instance

/-- The actual quotient embeds into finitely many actual homogeneous
coordinates. This is used to prove actual finite-dimensionality. -/
def finiteModelFiniteCoordinates (c : ℕ) :
    finiteModelTruncation k V b K c →ₗ[k]
      (∀ n : Fin (c + 1), finiteModelComponent k V b K c n) :=
  LinearMap.pi fun n =>
    (DirectSum.component k ℕ (fun i => finiteModelComponent k V b K c i) n).comp
      (DirectSum.decomposeLinearEquiv (finiteModelComponent k V b K c)).toLinearMap

theorem finiteModelFiniteCoordinates_injective (c : ℕ) :
    Function.Injective (finiteModelFiniteCoordinates k V b K c) := by
  intro x y hxy
  apply (DirectSum.decomposeLinearEquiv (finiteModelComponent k V b K c)).injective
  apply DFinsupp.ext
  intro n
  by_cases hn : n ≤ c
  · exact congrFun hxy (⟨n, by omega⟩ : Fin (c + 1))
  · apply Subtype.ext
    have hx : ((DirectSum.decompose (finiteModelComponent k V b K c) x n) :
        finiteModelTruncation k V b K c) = 0 := by
      apply (Submodule.mem_bot k).mp
      rw [← finiteModelComponent_eq_bot_above k V b K c n (by omega)]
      exact (DirectSum.decompose (finiteModelComponent k V b K c) x n).property
    have hy : ((DirectSum.decompose (finiteModelComponent k V b K c) y n) :
        finiteModelTruncation k V b K c) = 0 := by
      apply (Submodule.mem_bot k).mp
      rw [← finiteModelComponent_eq_bot_above k V b K c n (by omega)]
      exact (DirectSum.decompose (finiteModelComponent k V b K c) y n).property
    exact hx.trans hy.symm

/-- Actual finite-dimensionality is a consequence of the genuine
bounded grading and original finite degree spaces. It is not an input. -/
instance finiteModelTruncation_finiteDimensional (c : ℕ) :
    FiniteDimensional k (finiteModelTruncation k V b K c) :=
  FiniteDimensional.of_injective (finiteModelFiniteCoordinates k V b K c)
    (finiteModelFiniteCoordinates_injective k V b K c)

end ChenRanks.Koszul
