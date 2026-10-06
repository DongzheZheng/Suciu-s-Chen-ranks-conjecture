import ChenRanks.KoszulMetabelianFiniteTruncation

/-!
# The actual truncation tail is the actual lower-central ideal

The positive homogeneous tail is compared with the already proved
original homogeneous Koszul tail. The latter is genuinely equal to a
power of the native symmetric augmentation ideal. This identifies the
defining truncation ideal with the model's native lower-central series,
rather than defining that series by the proposed grading.
-/

noncomputable section

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} [Fintype ι] (b : _root_.Module.Basis ι k V)
variable (K : Submodule k (⋀[k]^2 V))

local instance truncationFiltrationOriginalGroup : AddCommGroup (Module k V K) :=
  originalModuleAddCommGroup k V K
local instance truncationFiltrationOriginalMonoid : AddCommMonoid (Module k V K) :=
  (originalModuleAddCommGroup k V K).toAddCommMonoid
local instance truncationFiltrationOriginalScalar : _root_.Module k (Module k V K) :=
  originalModuleScalarModule k V K
local instance truncationFiltrationDegreeGroup (r : ℕ) :
    AddCommGroup (homogeneousModule k V b K r) :=
  canonicalHomogeneousQuotientAddCommGroup k V b K r
local instance truncationFiltrationDegreeMonoid (r : ℕ) :
    AddCommMonoid (homogeneousModule k V b K r) :=
  (canonicalHomogeneousQuotientAddCommGroup k V b K r).toAddCommMonoid
local instance truncationFiltrationDegreeScalar (r : ℕ) :
    _root_.Module k (homogeneousModule k V b K r) :=
  canonicalHomogeneousQuotientBaseCoefficients k V b K r

open MetabelianLieModel
open ChenRanks.LieComparison

/-- A surviving actual homogeneous element is not killed by the actual
truncation map. This follows from the original projection's true kernel
containment, not from an assumed faithful homogeneous quotient. -/
theorem finiteModelProjection_eq_zero_of_homogeneous (c n : ℕ) (hn : n ≤ c)
    (x : MetabelianLieModel k V K) (hx : x ∈ modelPositiveComponent k V b K n)
    (hzero : finiteModelProjection k V b K c x = 0) : x = 0 := by
  have htail : x ∈ (modelTruncationIdeal k V b K c).toSubmodule :=
    (Submodule.Quotient.mk_eq_zero _).mp hzero
  have hp : modelPositiveProjection k V b K n x = 0 :=
    LinearMap.mem_ker.mp (modelTruncationIdeal_le_projection_ker k V b K c n hn htail)
  rw [modelPositiveProjection_of_mem_same k V b K n x hx] at hp
  exact hp

/-- The actual truncation is injective on each actual surviving original
component, while it genuinely kills the components above its bound. -/
theorem finiteModelProjection_injective_on_component (c n : ℕ) (hn : n ≤ c)
    (x y : MetabelianLieModel k V K)
    (hx : x ∈ modelPositiveComponent k V b K n)
    (hy : y ∈ modelPositiveComponent k V b K n)
    (hxy : finiteModelProjection k V b K c x = finiteModelProjection k V b K c y) :
    x = y := by
  apply sub_eq_zero.mp
  apply finiteModelProjection_eq_zero_of_homogeneous k V b K c n hn (x - y)
    ((modelPositiveComponent k V b K n).sub_mem hx hy)
  rw [map_sub, hxy, sub_self]

/-- Ordinary degree-one generators remain genuinely distinguishable in
every actual nonzero-degree truncation. -/
theorem finiteModelProjection_generator_injective (c : ℕ) (hc : 1 ≤ c) :
    Function.Injective (fun u : V =>
      finiteModelProjection k V b K c (generatorInclusion k V K u)) := by
  intro u v huv
  have h := finiteModelProjection_injective_on_component k V b K c 1 hc
    (generatorInclusion k V K u) (generatorInclusion k V K v)
    ⟨u, rfl⟩ ⟨v, rfl⟩ huv
  exact congrArg MetabelianLieModel.generator h

/-- A genuine original Koszul tail maps into the genuine corresponding
positive tail of the actual Lie model. -/
theorem invariantInclusion_mem_modelTruncationIdeal (r : ℕ) (w : Module k V K)
    (hw : w ∈ originalDegreeTail k V b K r) :
    invariantInclusion k V K w ∈ modelTruncationIdeal k V b K (r + 1) := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, hrn, hn⟩ := hw
    exact mem_nativeGradedTail_of_mem k (MetabelianLieModel k V K)
      (modelPositiveComponent k V b K) ((r + 1) + 1) (n + 2)
      (invariantInclusion k V K w) (by omega)
      (invariantInclusion_mem_modelPositiveComponent k V b K n w hn)
  | zero => rw [map_zero]; exact (modelTruncationIdeal k V b K (r + 1)).zero_mem
  | add w z _ _ hw hz =>
    rw [map_add]
    exact (modelTruncationIdeal k V b K (r + 1)).add_mem hw hz
  | smul c w _ hw =>
    rw [map_smul]
    exact (modelTruncationIdeal k V b K (r + 1)).smul_mem c hw

variable [CharZero k]

/-- The actual positive tail starting in ordinary degree r+2 is exactly
the actual r-th augmentation power on the original invariant coordinate. -/
theorem modelTruncationIdeal_eq_augmentationPower (r : ℕ) :
    modelTruncationIdeal k V b K (r + 1) = augmentationPowerInvariantIdeal k V K r := by
  apply le_antisymm
  · change (modelTruncationIdeal k V b K (r + 1)).toSubmodule ≤
      (augmentationPowerInvariantIdeal k V K r).toSubmodule
    apply Submodule.span_le.mpr
    rintro x ⟨n, hn, hx⟩
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => omega
      | succ s =>
        obtain ⟨w, rfl⟩ := hx
        change (modelInvariantDegreeInclusion k V b K s w).generator = 0 ∧
          (modelInvariantDegreeInclusion k V b K s w).invariant ∈ augmentationPowerModule k V K r
        refine ⟨rfl, ?_⟩
        change degreeQuotientInclusion k V b K s w ∈ augmentationPowerModule k V K r
        rw [augmentationPower_eq_originalPolynomialTail k V b K r]
        exact originalDegree_mem_tail k V b K r s (by omega)
          (degreeQuotientInclusion_mem_originalDegree k V b K s w)
  · intro x hx
    have hgen : x.generator = 0 := hx.1
    have hw : x.invariant ∈ augmentationPowerModule k V K r := hx.2
    rw [augmentationPower_eq_originalPolynomialTail k V b K r] at hw
    rw [eq_invariantInclusion_of_generator_eq_zero k V K x hgen]
    exact invariantInclusion_mem_modelTruncationIdeal k V b K r x.invariant hw

/-- In ordinary indexing the defining ideal for the truncation at c=r+1
is Gamma_(c+1), i.e. the model's native zero-based term c. -/
theorem modelTruncationIdeal_eq_nativeLowerCentral (r : ℕ) :
    modelTruncationIdeal k V b K (r + 1) =
      LieModule.lowerCentralSeries k (MetabelianLieModel k V K)
        (MetabelianLieModel k V K) (r + 1) := by
  letI : FiniteDimensional k V := _root_.Module.Finite.of_basis b
  rw [model_lowerCentralSeries_eq_augmentationPower]
  exact modelTruncationIdeal_eq_augmentationPower k V b K r

end ChenRanks.Koszul
