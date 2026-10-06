import ChenRanks.KoszulAugmentationHomogeneous

/-!
# The original homogeneous Koszul module as an actual augmentation quotient

The degree tail is first the ordinary base-field span of genuine degree
images. The inherited symmetric action is proved to preserve it, and the
actual augmentation ideal is proved to raise it. These facts identify this
tail with the true augmentation power on the original Koszul quotient.
The original degree projection then induces an actual linear equivalence
from consecutive augmentation quotients to the original `W_r`.

No filtration, homogeneous decomposition, generation, kernel equality,
or associated-graded comparison is supplied as a premise. The final group
Malcev/Chen comparison is not asserted here.
-/

noncomputable section

open scoped BigOperators TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} [Fintype ι] (b : _root_.Module.Basis ι k V)
variable (K : Submodule k (⋀[k]^2 V))

local instance augmentationQuotientBaseAddCommGroup : AddCommGroup (Module k V K) :=
  Submodule.Quotient.addCommGroup (LinearMap.range (relationMap k V K))

local instance augmentationQuotientBaseAddCommMonoid : AddCommMonoid (Module k V K) :=
  (augmentationQuotientBaseAddCommGroup k V K).toAddCommMonoid

local instance augmentationQuotientBaseModule : _root_.Module k (Module k V K) :=
  Submodule.Quotient.module' (S := k) (LinearMap.range (relationMap k V K))

local instance augmentationQuotientBaseSMulZero : SMulZeroClass k (Module k V K) :=
  Submodule.Quotient.smulZeroClass' (S := k) (LinearMap.range (relationMap k V K))

local instance augmentationQuotientBasePolynomialComm :
    SMulCommClass k (S k V) (Module k V K) :=
  Submodule.Quotient.smulCommClass (S := k)
    (P := LinearMap.range (relationMap k V K)) (S k V)

local instance augmentationQuotientPolynomialBaseComm :
    SMulCommClass (S k V) k (Module k V K) :=
  SMulCommClass.symm k (S k V) (Module k V K)

/-- An ordinary base-field span of actual quotient-degree images. -/
def originalDegreeTail (r : ℕ) : Submodule k (Module k V K) :=
  Submodule.span k {w | ∃ n : ℕ, r ≤ n ∧
    w ∈ LinearMap.range (degreeCycleToUngraded k V b K n)}

omit [Fintype ι] in
theorem originalDegree_mem_tail (r n : ℕ) (hrn : r ≤ n)
    {w : Module k V K}
    (hw : w ∈ LinearMap.range (degreeCycleToUngraded k V b K n)) :
    w ∈ originalDegreeTail k V b K r :=
  Submodule.subset_span ⟨n, hrn, hw⟩

omit [Fintype ι] in
/-- Genuine homogeneous scalar multiplication raises the genuine tail. -/
theorem homogeneous_smul_mem_tail (i r : ℕ) (s : homogeneousS k V b i)
    {w : Module k V K} (hw : w ∈ originalDegreeTail k V b K r) :
    (s : S k V) • w ∈ originalDegreeTail k V b K (i + r) := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, hrn, hn⟩ := hw
    exact originalDegree_mem_tail k V b K (i + r) (i + n)
      (Nat.add_le_add_left hrn i)
      (homogeneous_smul_originalDegree_mem k V b K i n s w hn)
  | zero =>
    rw [smul_zero]
    exact (originalDegreeTail k V b K (i + r)).zero_mem
  | add x y _hx _hy ihx ihy =>
    rw [smul_add]
    exact (originalDegreeTail k V b K (i + r)).add_mem ihx ihy
  | smul c x _hx ih =>
    rw [smul_comm (s : S k V) c x]
    exact (originalDegreeTail k V b K (i + r)).smul_mem c ih

omit [Fintype ι] in
/-- Tail inclusions follow from their genuine defining degree ranges. -/
theorem originalDegreeTail_antitone {r n : ℕ} (hrn : r ≤ n) :
    originalDegreeTail k V b K n ≤ originalDegreeTail k V b K r := by
  apply Submodule.span_le.mpr
  rintro w ⟨m, hnm, hm⟩
  exact originalDegree_mem_tail k V b K r m (hrn.trans hnm) hm

omit [Fintype ι] in
/-- The inherited action of an arbitrary actual symmetric coefficient
preserves the tail, by its true finite homogeneous expansion. -/
theorem scalar_smul_mem_tail (r : ℕ) (s : S k V)
    {w : Module k V K} (hw : w ∈ originalDegreeTail k V b K r) :
    s • w ∈ originalDegreeTail k V b K r := by
  classical
  rw [← sum_homogeneousProjection k V b s, Finset.sum_smul]
  apply (originalDegreeTail k V b K r).sum_mem
  intro i _hi
  exact originalDegreeTail_antitone k V b K (Nat.le_add_left r i)
    (homogeneous_smul_mem_tail k V b K i r
      ⟨homogeneousProjection k V b i s, homogeneousProjection_mem k V b i s⟩ hw)

/-- The actual inherited symmetric action turns the proved degree tail
into an ordinary symmetric-algebra submodule of the original quotient. -/
def originalPolynomialTail (r : ℕ) : Submodule (S k V) (Module k V K) where
  carrier := originalDegreeTail k V b K r
  zero_mem' := (originalDegreeTail k V b K r).zero_mem
  add_mem' := (originalDegreeTail k V b K r).add_mem
  smul_mem' := scalar_smul_mem_tail k V b K r

omit [Fintype ι] in
@[simp]
theorem originalPolynomialTail_restrictScalars (r : ℕ) :
    (originalPolynomialTail k V b K r).restrictScalars k =
      originalDegreeTail k V b K r := rfl

/-- Every original quotient element has the actual finite expansion
given by the already proved cycle projections. -/
theorem exists_sum_originalDegreeProjection (w : Module k V K) :
    ∃ N : ℕ, w = ∑ n ∈ Finset.range N, originalDegreeProjection k V b K n w := by
  refine Submodule.Quotient.induction_on _ w ?_
  intro z
  obtain ⟨N, hN⟩ := exists_sum_cycleProjection k V b z
  refine ⟨N, ?_⟩
  have h := congrArg (LinearMap.range (relationMap k V K)).mkQ hN
  rw [map_sum] at h
  change (∑ n ∈ Finset.range N,
      degreeCycleToUngraded k V b K n (cycleProjection k V b n z)) =
    (LinearMap.range (relationMap k V K)).mkQ z at h
  simpa only [originalDegreeProjection, LinearMap.comp_apply,
    quotientProjection_mk, degreeQuotientInclusion_mk] using h.symm

theorem originalPolynomialTail_zero : originalPolynomialTail k V b K 0 = ⊤ := by
  apply top_unique
  intro w _hw
  obtain ⟨N, hN⟩ := exists_sum_originalDegreeProjection k V b K w
  rw [hN]
  change (∑ n ∈ Finset.range N, originalDegreeProjection k V b K n w) ∈
    originalDegreeTail k V b K 0
  apply (originalDegreeTail k V b K 0).sum_mem
  intro n _hn
  exact originalDegree_mem_tail k V b K 0 n (Nat.zero_le n)
    (degreeQuotientInclusion_mem_originalDegree k V b K n
      (quotientProjection k V b K n w))

/-- The genuine augmentation generators raise the genuine degree tail;
their actual ideal closure supplies arbitrary augmentation coefficients. -/
theorem augmentation_smul_tail_le (r : ℕ) :
    actualAugmentationIdeal k V • originalPolynomialTail k V b K r ≤
      originalPolynomialTail k V b K (r + 1) := by
  apply Submodule.smul_le.mpr
  intro s hs w hw
  rw [actualAugmentationIdeal_eq_span] at hs
  induction hs using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨u, rfl⟩ := hs
    have h := homogeneous_smul_mem_tail k V b K 1 r
      ⟨SymmetricAlgebra.ι k V u, homogeneousS_ι k V b u⟩ hw
    simpa only [Nat.add_comm 1 r] using h
  | zero =>
    rw [zero_smul]
    exact (originalPolynomialTail k V b K (r + 1)).zero_mem
  | add s t _hs _ht ihs iht =>
    rw [add_smul]
    exact (originalPolynomialTail k V b K (r + 1)).add_mem ihs iht
  | smul a s _hs ih =>
    rw [smul_eq_mul, mul_smul]
    exact (originalPolynomialTail k V b K (r + 1)).smul_mem a ih

/-- A genuine augmentation power is contained in the corresponding
genuine degree tail, by the actual ideal-power recursion. -/
theorem augmentationPower_le_tail (r : ℕ) :
    augmentationPowerModule k V K r ≤ originalPolynomialTail k V b K r := by
  induction r with
  | zero =>
    rw [originalPolynomialTail_zero]
    exact le_top
  | succ r ih =>
    rw [augmentationPowerModule_succ]
    exact (Submodule.smul_mono le_rfl ih).trans (augmentation_smul_tail_le k V b K r)

variable [CharZero k]

/-- The opposite inclusion follows from actual homogeneous second-tensor
generation, not from an assumed generation-in-degree-zero statement. -/
theorem tail_le_augmentationPower (r : ℕ) :
    originalPolynomialTail k V b K r ≤ augmentationPowerModule k V K r := by
  change originalDegreeTail k V b K r ≤
    (augmentationPowerModule k V K r).restrictScalars k
  apply Submodule.span_le.mpr
  rintro w ⟨n, hrn, hn⟩
  have hw : w ∈ augmentationPowerModule k V K n :=
    originalDegree_le_augmentationPower k V b K n hn
  exact Submodule.smul_mono (Ideal.pow_le_pow_right hrn) le_rfl hw

/-- The actual augmentation powers equal the actual homogeneous tails. -/
theorem augmentationPower_eq_originalPolynomialTail (r : ℕ) :
    augmentationPowerModule k V K r = originalPolynomialTail k V b K r :=
  le_antisymm (augmentationPower_le_tail k V b K r) (tail_le_augmentationPower k V b K r)

omit [CharZero k] in
/-- The original projection vanishes on a different genuine degree image. -/
theorem quotientProjection_eq_zero_of_originalDegree (r n : ℕ) (hrn : r ≠ n)
    {w : Module k V K}
    (hw : w ∈ LinearMap.range (degreeCycleToUngraded k V b K n)) :
    quotientProjection k V b K r w = 0 := by
  obtain ⟨z, rfl⟩ := hw
  change quotientProjection k V b K r
    (degreeQuotientInclusion k V b K n (Submodule.Quotient.mk z)) = 0
  exact quotientProjection_degreeQuotientInclusion_ne k V b K r n hrn _

/-- Membership in a true augmentation power forces the lower genuine
quotient-degree projections to vanish. -/
theorem quotientProjection_eq_zero_of_mem_augmentationPower
    (r n : ℕ) (hnr : n < r) {w : Module k V K}
    (hw : w ∈ augmentationPowerModule k V K r) :
    quotientProjection k V b K n w = 0 := by
  rw [augmentationPower_eq_originalPolynomialTail k V b K r] at hw
  change w ∈ originalDegreeTail k V b K r at hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨m, hrm, hm⟩ := hw
    exact quotientProjection_eq_zero_of_originalDegree k V b K n m (by omega) hm
  | zero => exact map_zero _
  | add x y _hx _hy ihx ihy => rw [map_add, ihx, ihy, add_zero]
  | smul c x _hx ih => rw [map_smul, ih, smul_zero]

/-- Conversely, the actual finite quotient-degree expansion recovers
membership in a true augmentation power from its lower vanishing. -/
theorem mem_augmentationPower_of_lower_projections_eq_zero
    (r : ℕ) (w : Module k V K)
    (hw : ∀ n : ℕ, n < r → quotientProjection k V b K n w = 0) :
    w ∈ augmentationPowerModule k V K r := by
  obtain ⟨N, hN⟩ := exists_sum_originalDegreeProjection k V b K w
  rw [hN]
  apply (augmentationPowerModule k V K r).sum_mem
  intro n _hn
  by_cases hnr : n < r
  · change degreeQuotientInclusion k V b K n (quotientProjection k V b K n w) ∈
      augmentationPowerModule k V K r
    rw [hw n hnr, map_zero]
    exact (augmentationPowerModule k V K r).zero_mem
  · have hrn : r ≤ n := Nat.le_of_not_gt hnr
    exact Submodule.smul_mono (Ideal.pow_le_pow_right hrn) le_rfl
      (degreeQuotientInclusion_mem_augmentationPower k V b K n
        (quotientProjection k V b K n w))

theorem mem_augmentationPower_iff_lower_projections_eq_zero
    (r : ℕ) (w : Module k V K) :
    w ∈ augmentationPowerModule k V K r ↔
      ∀ n : ℕ, n < r → quotientProjection k V b K n w = 0 := by
  constructor
  · intro hw n hn
    exact quotientProjection_eq_zero_of_mem_augmentationPower k V b K r n hn hw
  · exact mem_augmentationPower_of_lower_projections_eq_zero k V b K r w

/-- The actual restriction of the original degree projection to the
actual augmentation-power submodule. -/
def augmentationPowerDegreeProjection (r : ℕ) :
    (augmentationPowerModule k V K r).restrictScalars k →ₗ[k]
      homogeneousModule k V b K r :=
  (quotientProjection k V b K r).comp
    ((augmentationPowerModule k V K r).restrictScalars k).subtype

/-- The next actual augmentation power, viewed inside the previous one. -/
def nextAugmentationPowerWithin (r : ℕ) :
    Submodule k ((augmentationPowerModule k V K r).restrictScalars k) :=
  ((augmentationPowerModule k V K (r + 1)).restrictScalars k).comap
    ((augmentationPowerModule k V K r).restrictScalars k).subtype

/-- The actual projection kernel is exactly the next actual power. -/
theorem augmentationPowerDegreeProjection_ker (r : ℕ) :
    LinearMap.ker (augmentationPowerDegreeProjection k V b K r) =
      nextAugmentationPowerWithin k V K r := by
  ext w
  change quotientProjection k V b K r (w : Module k V K) = 0 ↔
    (w : Module k V K) ∈ augmentationPowerModule k V K (r + 1)
  constructor
  · intro hz
    apply mem_augmentationPower_of_lower_projections_eq_zero k V b K (r + 1) w
    intro n hn
    by_cases hnr : n = r
    · subst n
      exact hz
    · exact quotientProjection_eq_zero_of_mem_augmentationPower k V b K r n
        (by omega) w.property
  · intro hw
    exact quotientProjection_eq_zero_of_mem_augmentationPower k V b K (r + 1) r
      (Nat.lt_succ_self r) hw

/-- Surjectivity is witnessed by the original degree inclusion, whose
actual power membership was proved by homogeneous second tensors. -/
theorem augmentationPowerDegreeProjection_surjective (r : ℕ) :
    Function.Surjective (augmentationPowerDegreeProjection k V b K r) := by
  intro w
  refine ⟨⟨degreeQuotientInclusion k V b K r w,
    degreeQuotientInclusion_mem_augmentationPower k V b K r w⟩, ?_⟩
  exact quotientProjection_degreeQuotientInclusion_self k V b K r w

local instance augmentationPowerSubtypeAddCommGroup (r : ℕ) :
    AddCommGroup ((augmentationPowerModule k V K r).restrictScalars k) :=
  Submodule.addCommGroup ((augmentationPowerModule k V K r).restrictScalars k)

local instance augmentationPowerSubtypeAddCommMonoid (r : ℕ) :
    AddCommMonoid ((augmentationPowerModule k V K r).restrictScalars k) :=
  (augmentationPowerSubtypeAddCommGroup k V K r).toAddCommMonoid

local instance augmentationPowerSubtypeBaseModule (r : ℕ) :
    _root_.Module k ((augmentationPowerModule k V K r).restrictScalars k) :=
  Submodule.module ((augmentationPowerModule k V K r).restrictScalars k)

local instance augmentationSuccessiveNativeAddCommGroup (r : ℕ) :
    AddCommGroup ((augmentationPowerModule k V K r).restrictScalars k ⧸
      nextAugmentationPowerWithin k V K r) :=
  Submodule.Quotient.addCommGroup (nextAugmentationPowerWithin k V K r)

local instance augmentationSuccessiveNativeAddCommMonoid (r : ℕ) :
    AddCommMonoid ((augmentationPowerModule k V K r).restrictScalars k ⧸
      nextAugmentationPowerWithin k V K r) :=
  (augmentationSuccessiveNativeAddCommGroup k V K r).toAddCommMonoid

local instance augmentationSuccessiveNativeBaseModule (r : ℕ) :
    _root_.Module k ((augmentationPowerModule k V K r).restrictScalars k ⧸
      nextAugmentationPowerWithin k V K r) :=
  Submodule.Quotient.module (nextAugmentationPowerWithin k V K r)

local instance augmentationProjectionKerAddCommGroup (r : ℕ) :
    AddCommGroup ((augmentationPowerModule k V K r).restrictScalars k ⧸
      (augmentationPowerDegreeProjection k V b K r).ker) :=
  Submodule.Quotient.addCommGroup (augmentationPowerDegreeProjection k V b K r).ker

local instance augmentationProjectionKerAddCommMonoid (r : ℕ) :
    AddCommMonoid ((augmentationPowerModule k V K r).restrictScalars k ⧸
      (augmentationPowerDegreeProjection k V b K r).ker) :=
  (augmentationProjectionKerAddCommGroup k V b K r).toAddCommMonoid

local instance augmentationProjectionKerBaseModule (r : ℕ) :
    _root_.Module k ((augmentationPowerModule k V K r).restrictScalars k ⧸
      (augmentationPowerDegreeProjection k V b K r).ker) :=
  Submodule.Quotient.module (augmentationPowerDegreeProjection k V b K r).ker

/-- An actual associated-graded equivalence for the genuine augmentation
filtration, with the manuscript's original homogeneous quotient. -/
def augmentationSuccessiveQuotientEquiv (r : ℕ) :
    ((augmentationPowerModule k V K r).restrictScalars k ⧸
      nextAugmentationPowerWithin k V K r) ≃ₗ[k]
      homogeneousModule k V b K r :=
  (Submodule.quotEquivOfEq _ _
    (augmentationPowerDegreeProjection_ker k V b K r).symm).trans
    ((augmentationPowerDegreeProjection k V b K r).quotKerEquivOfSurjective
      (augmentationPowerDegreeProjection_surjective k V b K r))

@[simp]
theorem augmentationSuccessiveQuotientEquiv_mk (r : ℕ)
    (w : (augmentationPowerModule k V K r).restrictScalars k) :
    augmentationSuccessiveQuotientEquiv k V b K r (Submodule.Quotient.mk w) =
      quotientProjection k V b K r (w : Module k V K) := by
  simp only [augmentationSuccessiveQuotientEquiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

end ChenRanks.Koszul
