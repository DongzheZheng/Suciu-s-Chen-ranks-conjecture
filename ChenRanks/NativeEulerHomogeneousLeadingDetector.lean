import ChenRanks.GroupFlagAugmentation
import ChenRanks.NativeEulerExtensionRaisingFlag

/-!
# Actual homogeneous Euler adjoints have faithful actual leading classes

The flag is the actual coordinate-pulled Euler extension flag of the
actual native positive grading. A degree-q vector has its actual native
adjoint in J_q. If that adjoint belongs to J_(q+1), evaluating on the
original axis forces its actual Euler derivative into the next tail.
The already proved native homogeneous-tail separation and actual Euler
injectivity then force the original vector to vanish.

This is a genuine injection into the actual operator quotient, not an
assumed detector. It uses no finite-dimensionality or degree bound. In
the finite Koszul application the grading and positivity are obtained
from the actual finite quotient factory; no group or monodromy premise
is used by this statement.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]
variable (hzero : ℒ 0 = ⊥)

include hzero

/-- The actual degree-q Euler adjoint raises the actual affine flag by
the actual degree q, proved from the native graded bracket. -/
theorem nativeEulerAffineAdjoint_mem_homogeneous_degree (q : ℕ) (hq : 1 ≤ q)
    (x : L) (hx : x ∈ ℒ q) :
    derivationAffineAdjointEnd k L (nativeEulerDerivation k L ℒ) x ∈
      degreeRaisingEndomorphisms k (k × L) (nativeAffineGradedFlag k L ℒ) q := by
  cases q with
  | zero => omega
  | succ q =>
    intro n p hp
    have hxtail : x ∈ nativeGradedTail k L ℒ (q + 1) :=
      mem_nativeGradedTail_of_mem k L ℒ (q + 1) (q + 1) x le_rfl hx
    cases n with
    | zero =>
      rw [Nat.zero_add]
      change (0 : k) = 0 ∧
        p.1 • nativeEulerDerivation k L ℒ x + ⁅x, p.2⁆ ∈
          nativeGradedTail k L ℒ (q + 1)
      refine ⟨rfl, ?_⟩
      apply Submodule.add_mem
      · rw [nativeEulerDerivation_of_mem k L ℒ (q + 1) x hx]
        exact Submodule.smul_mem _ p.1
          (Submodule.smul_mem _ ((q + 1 : ℕ) : k) hxtail)
      · have hptail : p.2 ∈ nativeGradedTail k L ℒ 1 := by
          rw [nativeGradedTail_one_eq_top k L ℒ hzero]
          exact Submodule.mem_top
        exact nativeGradedTail_antitone k L ℒ (q + 1) ((q + 1) + 1)
          (by omega) (lie_mem_nativeGradedTail k L ℒ (q + 1) 1 x p.2 hxtail hptail)
    | succ n =>
      change p.1 = 0 ∧ p.2 ∈ nativeGradedTail k L ℒ (n + 1) at hp
      change (0 : k) = 0 ∧
        p.1 • nativeEulerDerivation k L ℒ x + ⁅x, p.2⁆ ∈
          nativeGradedTail k L ℒ ((n + 1) + (q + 1))
      refine ⟨rfl, ?_⟩
      rw [hp.1, zero_smul, zero_add]
      have h := lie_mem_nativeGradedTail k L ℒ (q + 1) (n + 1) x p.2 hxtail hp.2
      simpa only [Nat.add_comm (q + 1) (n + 1)] using h

/-- Actual coordinate compatibility gives the same degree for the
actual native extension adjoint, not a substituted affine action. -/
theorem nativeEulerExtensionAdjoint_mem_homogeneous_degree (q : ℕ) (hq : 1 ≤ q)
    (x : L) (hx : x ∈ ℒ q) :
    (nativeDerivationExtensionAdjoint k L (nativeEulerDerivation k L ℒ) x).toLinearMap ∈
      degreeRaisingEndomorphisms k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
        (nativeEulerExtensionFlag k L ℒ) q := by
  intro n p hp
  let D := nativeEulerDerivation k L ℒ
  let e := nativeDerivationExtensionCoordinates k L D
  have h := nativeEulerAffineAdjoint_mem_homogeneous_degree k L ℒ hzero q hq x hx
    n (e p) hp
  change e (nativeDerivationExtensionAdjoint k L D x p) ∈
    nativeAffineGradedFlag k L ℒ (n + q)
  rw [nativeDerivationExtensionAdjoint_coordinates]
  exact h

/-- Testing the actual next-degree operator condition on the original
axis forces actual vanishing of the original homogeneous vector. -/
theorem nativeEulerHomogeneousAdjoint_next_implies_zero (q : ℕ)
    (x : L) (hx : x ∈ ℒ q)
    (hnext : (nativeDerivationExtensionAdjoint k L (nativeEulerDerivation k L ℒ) x).toLinearMap ∈
      degreeRaisingEndomorphisms k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
        (nativeEulerExtensionFlag k L ℒ) (q + 1)) : x = 0 := by
  let D := nativeEulerDerivation k L ℒ
  let axis := nativeDerivationExtensionAxis k L D
  have haxis : axis ∈ nativeEulerExtensionFlag k L ℒ 0 := by
    rw [nativeEulerExtensionFlag_zero]
    exact Submodule.mem_top
  have h := hnext 0 axis haxis
  simp only [Nat.zero_add] at h
  change nativeDerivationExtensionCoordinates k L D
    (nativeDerivationExtensionAdjoint k L D x axis) ∈
      nativeAffineGradedFlag k L ℒ (q + 1) at h
  rw [nativeDerivationExtensionAdjoint_coordinates] at h
  change (0 : k) = 0 ∧ (1 : k) • D x + ⁅x, (0 : L)⁆ ∈
    nativeGradedTail k L ℒ (q + 1) at h
  have htail : D x ∈ nativeGradedTail k L ℒ (q + 1) := by
    simpa only [one_smul, lie_zero, add_zero] using h.2
  have hhom : D x ∈ ℒ q := by
    rw [nativeEulerDerivation_of_mem k L ℒ q x hx]
    exact Submodule.smul_mem _ (q : k) hx
  have hd := eq_zero_of_homogeneous_mem_next_tail k L ℒ q (D x) hhom htail
  apply nativeEulerDerivation_injective k L ℒ hzero
  exact hd.trans (map_zero _).symm

/-- The actual native homogeneous adjoint with its proved current
operator degree, as a genuine linear map. -/
def nativeEulerHomogeneousAdjointCurrent (q : ℕ) (hq : 1 ≤ q) :
    ℒ q →ₗ[k] degreeRaisingEndomorphisms k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) q where
  toFun x := ⟨(nativeDerivationExtensionAdjoint k L (nativeEulerDerivation k L ℒ) x).toLinearMap,
    nativeEulerExtensionAdjoint_mem_homogeneous_degree k L ℒ hzero q hq x x.property⟩
  map_add' x y := by
    apply Subtype.ext
    apply LinearMap.ext
    intro p
    let D := nativeEulerDerivation k L ℒ
    let e := nativeDerivationExtensionCoordinates k L D
    apply e.injective
    change e (nativeDerivationExtensionAdjoint k L D ((x : L) + y) p) =
      e (nativeDerivationExtensionAdjoint k L D x p +
        nativeDerivationExtensionAdjoint k L D y p)
    rw [map_add, nativeDerivationExtensionAdjoint_coordinates,
      nativeDerivationExtensionAdjoint_coordinates, nativeDerivationExtensionAdjoint_coordinates]
    apply Prod.ext
    · exact (zero_add (0 : k)).symm
    · change p.right • D ((x : L) + y) + ⁅(x : L) + y, p.left⁆ =
        (p.right • D x + ⁅(x : L), p.left⁆) + (p.right • D y + ⁅(y : L), p.left⁆)
      rw [map_add, smul_add, add_lie]
      abel
  map_smul' c x := by
    apply Subtype.ext
    apply LinearMap.ext
    intro p
    let D := nativeEulerDerivation k L ℒ
    let e := nativeDerivationExtensionCoordinates k L D
    apply e.injective
    change e (nativeDerivationExtensionAdjoint k L D (c • (x : L)) p) =
      e (c • nativeDerivationExtensionAdjoint k L D x p)
    rw [map_smul, nativeDerivationExtensionAdjoint_coordinates,
      nativeDerivationExtensionAdjoint_coordinates]
    apply Prod.ext
    · change (0 : k) = c • (0 : k)
      exact (smul_zero c).symm
    · change p.right • D (c • (x : L)) + ⁅c • (x : L), p.left⁆ =
        c • (p.right • D x + ⁅(x : L), p.left⁆)
      rw [map_smul, smul_lie, smul_add, smul_comm]

/-- The actual native adjoint's actual leading class in the actual
operator successive quotient. -/
def nativeEulerHomogeneousLeading (q : ℕ) (hq : 1 ≤ q) :
    ℒ q →ₗ[k] DegreeRaisingPiece k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) q :=
  (nextDegreeRaisingWithin k
    (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
    (nativeEulerExtensionFlag k L ℒ) q).mkQ.comp
      (nativeEulerHomogeneousAdjointCurrent k L ℒ hzero q hq)

theorem nativeEulerHomogeneousLeading_eq_zero (q : ℕ) (hq : 1 ≤ q)
    (x : ℒ q) (hx : nativeEulerHomogeneousLeading k L ℒ hzero q hq x = 0) : x = 0 := by
  change (nextDegreeRaisingWithin k
    (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
    (nativeEulerExtensionFlag k L ℒ) q).mkQ
      (nativeEulerHomogeneousAdjointCurrent k L ℒ hzero q hq x) = 0 at hx
  have hcurrent : nativeEulerHomogeneousAdjointCurrent k L ℒ hzero q hq x ∈
      nextDegreeRaisingWithin k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
        (nativeEulerExtensionFlag k L ℒ) q :=
    (Submodule.Quotient.mk_eq_zero (nextDegreeRaisingWithin k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) q)).mp hx
  have hnext :
      (nativeDerivationExtensionAdjoint k L (nativeEulerDerivation k L ℒ) x).toLinearMap ∈
        degreeRaisingEndomorphisms k
          (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
          (nativeEulerExtensionFlag k L ℒ) (q + 1) :=
    hcurrent
  apply Subtype.ext
  exact nativeEulerHomogeneousAdjoint_next_implies_zero k L ℒ hzero q x x.property hnext

/-- Injection follows from original axis evaluation and the actual
graded Euler, not from a desired leading-term detector premise. -/
theorem nativeEulerHomogeneousLeading_injective (q : ℕ) (hq : 1 ≤ q) :
    Function.Injective (nativeEulerHomogeneousLeading k L ℒ hzero q hq) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply nativeEulerHomogeneousLeading_eq_zero k L ℒ hzero q hq
  rw [map_sub, hxy, sub_self]

end ChenRanks.LieComparison
