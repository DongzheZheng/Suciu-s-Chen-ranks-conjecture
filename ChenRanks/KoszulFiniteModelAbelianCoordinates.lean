import ChenRanks.KoszulMetabelianTruncationFiltration
import ChenRanks.KoszulMetabelianLowerCentralSeries

/-!
# Actual abelian coordinates of the actual finite model

For a truncation retaining degree one, the original generator projection
descends through the actual truncation ideal. Its genuine kernel is the
actual degree-two tail of the quotient's proved native grading. The native
quotient by that actual tail is therefore linearly equivalent to the
original generator space, with the original generator inclusion as inverse.

The necessary bound `1 ≤ c` is explicit. For c=0 the actual truncation
is zero and such an equivalence with a nonzero generator space is false.
No kernel identity, generator faithfulness, degree-one comparison or
quotient equivalence is supplied as an input.
-/

noncomputable section

namespace ChenRanks.Koszul

open MetabelianLieModel ChenRanks.LieComparison

variable (k : Type*) [Field k] [CharZero k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} [Fintype ι] (b : _root_.Module.Basis ι k V)
variable (K : Submodule k (⋀[k]^2 V)) (c : ℕ) (hc : 1 ≤ c)

local instance finiteAbelianOriginalGroup : AddCommGroup (Module k V K) :=
  originalModuleAddCommGroup k V K
local instance finiteAbelianOriginalMonoid : AddCommMonoid (Module k V K) :=
  (originalModuleAddCommGroup k V K).toAddCommMonoid
local instance finiteAbelianOriginalScalar : _root_.Module k (Module k V K) :=
  originalModuleScalarModule k V K

include hc in
omit [CharZero k] in
/-- The actual truncation ideal kills the original generator coordinate
because the original surviving degree-one projection kills that ideal. -/
theorem modelTruncationIdeal_le_generatorProjection_ker :
    (modelTruncationIdeal k V b K c).toSubmodule ≤
      LinearMap.ker (modelGeneratorProjection k V K) := by
  intro x hx
  have hp := LinearMap.mem_ker.mp
    (modelTruncationIdeal_le_projection_ker k V b K c 1 hc hx)
  change generatorInclusion k V K (modelGeneratorProjection k V K x) = 0 at hp
  apply LinearMap.mem_ker.mpr
  exact congrArg (fun y : MetabelianLieModel k V K => y.generator) hp

/-- The true original generator projection descended along the actual quotient. -/
def finiteModelGeneratorProjection : finiteModelTruncation k V b K c →ₗ[k] V :=
  (modelTruncationIdeal k V b K c).toSubmodule.liftQ (modelGeneratorProjection k V K)
    (modelTruncationIdeal_le_generatorProjection_ker k V b K c hc)

@[simp] theorem finiteModelGeneratorProjection_mk (x : MetabelianLieModel k V K) :
    finiteModelGeneratorProjection k V b K c hc (finiteModelProjection k V b K c x) =
      x.generator := rfl

/-- The original vector generators included by the actual finite quotient. -/
def finiteModelOriginalGeneratorInclusion : V →ₗ[k] finiteModelTruncation k V b K c :=
  (finiteModelProjection k V b K c).toLinearMap.comp (generatorInclusion k V K)

@[simp] theorem finiteModelGeneratorProjection_originalGenerator (v : V) :
    finiteModelGeneratorProjection k V b K c hc
      (finiteModelOriginalGeneratorInclusion k V b K c v) = v := rfl

omit [CharZero k] in
/-- The actual projection maps each actual original graded tail to the
actual quotient tail, by genuine homogeneous-image membership. -/
theorem finiteModelProjection_mem_nativeTail (n : ℕ) (x : MetabelianLieModel k V K)
    (hx : x ∈ nativeGradedTail k (MetabelianLieModel k V K)
      (modelPositiveComponent k V b K) n) :
    finiteModelProjection k V b K c x ∈ nativeGradedTail k
      (finiteModelTruncation k V b K c) (finiteModelComponent k V b K c) n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, hxi⟩ := hx
    exact mem_nativeGradedTail_of_mem k (finiteModelTruncation k V b K c)
      (finiteModelComponent k V b K c) n i (finiteModelProjection k V b K c x) hi
      ⟨x, hxi, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- The actual whole kernel is exactly the actual quotient's degree-two tail. -/
theorem finiteModelGeneratorProjection_ker :
    LinearMap.ker (finiteModelGeneratorProjection k V b K c hc) =
      nativeGradedTail k (finiteModelTruncation k V b K c)
        (finiteModelComponent k V b K c) 2 := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := finiteModelProjection_surjective k V b K c x
    have hygen : y.generator = 0 := LinearMap.mem_ker.mp hx
    have hy : y ∈ nativeGradedTail k (MetabelianLieModel k V K)
        (modelPositiveComponent k V b K) 2 := by
      change y ∈ modelTruncationIdeal k V b K (0 + 1)
      rw [modelTruncationIdeal_eq_augmentationPower k V b K 0,
        augmentationPowerInvariantIdeal_zero]
      exact hygen
    exact finiteModelProjection_mem_nativeTail k V b K c 2 y hy
  · apply Submodule.span_le.mpr
    rintro x ⟨i, hi, hxi⟩
    obtain ⟨y, hy, rfl⟩ := hxi
    apply LinearMap.mem_ker.mpr
    change y.generator = 0
    cases i with
    | zero => omega
    | succ i =>
      cases i with
      | zero => omega
      | succ r =>
        obtain ⟨w, rfl⟩ := hy
        rfl

/-- The actual quotient by the actual original degree-two tail. -/
abbrev finiteModelAbelianQuotient :=
  finiteModelTruncation k V b K c ⧸ nativeGradedTail k
    (finiteModelTruncation k V b K c) (finiteModelComponent k V b K c) 2

/-- The original projection descends again through its genuine kernel. -/
def finiteModelAbelianToOriginal : finiteModelAbelianQuotient k V b K c →ₗ[k] V :=
  (nativeGradedTail k (finiteModelTruncation k V b K c)
    (finiteModelComponent k V b K c) 2).liftQ
    (finiteModelGeneratorProjection k V b K c hc)
    (le_of_eq (finiteModelGeneratorProjection_ker k V b K c hc).symm)

/-- The genuine inverse uses the original actual vector generators. -/
def originalToFiniteModelAbelian : V →ₗ[k] finiteModelAbelianQuotient k V b K c :=
  (nativeGradedTail k (finiteModelTruncation k V b K c)
    (finiteModelComponent k V b K c) 2).mkQ.comp
    (finiteModelOriginalGeneratorInclusion k V b K c)

@[simp] theorem finiteModelAbelianToOriginal_originalTo (v : V) :
    finiteModelAbelianToOriginal k V b K c hc
      (originalToFiniteModelAbelian k V b K c v) = v := rfl

theorem originalToFiniteModelAbelian_finiteModelTo
    (z : finiteModelAbelianQuotient k V b K c) :
    originalToFiniteModelAbelian k V b K c
      (finiteModelAbelianToOriginal k V b K c hc z) = z := by
  let J := nativeGradedTail k (finiteModelTruncation k V b K c)
    (finiteModelComponent k V b K c) 2
  obtain ⟨y, rfl⟩ := J.mkQ_surjective z
  change J.mkQ (finiteModelOriginalGeneratorInclusion k V b K c
      (finiteModelGeneratorProjection k V b K c hc y)) = J.mkQ y
  have hd : y - finiteModelOriginalGeneratorInclusion k V b K c
      (finiteModelGeneratorProjection k V b K c hc y) ∈ J := by
    change y - finiteModelOriginalGeneratorInclusion k V b K c
      (finiteModelGeneratorProjection k V b K c hc y) ∈
        nativeGradedTail k (finiteModelTruncation k V b K c)
          (finiteModelComponent k V b K c) 2
    rw [← finiteModelGeneratorProjection_ker k V b K c hc]
    apply LinearMap.mem_ker.mpr
    rw [map_sub, finiteModelGeneratorProjection_originalGenerator, sub_self]
  have he := (Submodule.Quotient.mk_eq_zero J).mpr hd
  change J.mkQ (y - finiteModelOriginalGeneratorInclusion k V b K c
    (finiteModelGeneratorProjection k V b K c hc y)) = 0 at he
  rw [map_sub] at he
  exact (sub_eq_zero.mp he).symm

/-- The genuine native linear equivalence, keeping the original vector
space and both original quotient maps. -/
def finiteModelAbelianOriginalEquiv : finiteModelAbelianQuotient k V b K c ≃ₗ[k] V :=
  LinearEquiv.ofLinear (finiteModelAbelianToOriginal k V b K c hc)
    (originalToFiniteModelAbelian k V b K c)
    (LinearMap.ext fun v => finiteModelAbelianToOriginal_originalTo k V b K c hc v)
    (LinearMap.ext fun z => originalToFiniteModelAbelian_finiteModelTo k V b K c hc z)

@[simp] theorem finiteModelAbelianOriginalEquiv_originalGenerator (v : V) :
    finiteModelAbelianOriginalEquiv k V b K c hc
      (originalToFiniteModelAbelian k V b K c v) = v := rfl

end ChenRanks.Koszul
