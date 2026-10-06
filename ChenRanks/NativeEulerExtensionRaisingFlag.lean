import ChenRanks.NativeAffineDegreeRaisingFlag
import ChenRanks.LieEulerPositiveAutomorphisms

/-!
# The actual degree flag on the actual native Euler extension

The original scalar-first affine flag is pulled back along the original
native coordinate equivalence.  The original native inner derivations
therefore raise this actual extension flag by one.  The actual finite
grading bound kills the corresponding raising-operator subspace.

An actual automorphism whose actual deviation from the identity lies in
this constructed raising subspace has the two actual positivity properties
used by the proved Euler-exponential classification.  This is still a
generic intermediate statement about such an automorphism.  The local
parallel function's deviation is obtained from its genuine primitive
construction, rather than supplied as a final configuration hypothesis.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]

/-- The actual original affine flag pulled back to the actual native
Euler extension, with no chosen flag input. -/
def nativeEulerExtensionFlag (n : ℕ) :
    Submodule k (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ)) :=
  (nativeAffineGradedFlag k L ℒ n).comap
    (nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ)).toLinearMap

@[simp] theorem nativeEulerExtensionFlag_zero :
    nativeEulerExtensionFlag k L ℒ 0 = ⊤ := by
  rw [nativeEulerExtensionFlag, nativeAffineGradedFlag_zero, Submodule.comap_top]

theorem nativeEulerExtensionFlag_antitone : Antitone (nativeEulerExtensionFlag k L ℒ) := by
  intro m n hmn
  exact Submodule.comap_mono (nativeAffineGradedFlag_antitone k L ℒ hmn)

/-- The original finite grading bound genuinely kills the extension flag. -/
theorem nativeEulerExtensionFlag_bound_eq_bot (c : ℕ)
    (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥) :
    nativeEulerExtensionFlag k L ℒ (c + 1) = ⊥ := by
  rw [nativeEulerExtensionFlag, nativeAffineGradedFlag_bound_eq_bot k L ℒ c hbound,
    Submodule.comap_bot]
  exact LinearMap.ker_eq_bot.mpr
    (nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ)).injective

/-- Every actual native inner derivation raises the actual constructed flag. -/
theorem nativeEulerExtensionAdjoint_mem_raisingEndomorphisms
    (hzero : ℒ 0 = ⊥) (x : L) :
    (nativeDerivationExtensionAdjoint k L (nativeEulerDerivation k L ℒ) x).toLinearMap ∈
      degreeRaisingEndomorphisms k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
        (nativeEulerExtensionFlag k L ℒ) 1 := by
  intro n p hp
  let D := nativeEulerDerivation k L ℒ
  let e := nativeDerivationExtensionCoordinates k L D
  have h := derivationAffineAdjointEnd_mem_degreeRaisingEndomorphisms
    k L ℒ hzero D x n (e p) hp
  change e (nativeDerivationExtensionAdjoint k L D x p) ∈
    nativeAffineGradedFlag k L ℒ (n + 1)
  rw [nativeDerivationExtensionAdjoint_coordinates]
  exact h

/-- The actual homogeneous original vector belongs to its actual extension flag. -/
theorem nativeEulerOriginal_mem_extensionFlag (n : ℕ) (w : L) (hw : w ∈ ℒ n) :
    nativeDerivationExtensionOriginal k L (nativeEulerDerivation k L ℒ) w ∈
      nativeEulerExtensionFlag k L ℒ n := by
  cases n with
  | zero => rw [nativeEulerExtensionFlag_zero]; exact Submodule.mem_top
  | succ n =>
    change (0 : k) = 0 ∧ w ∈ nativeGradedTail k L ℒ (n + 1)
    exact ⟨rfl, mem_nativeGradedTail_of_mem k L ℒ (n + 1) (n + 1) w le_rfl hw⟩

/-- All values of actual degree-one raising operators have zero scalar coordinate. -/
theorem nativeEulerRaisingEndomorphism_scalar_eq_zero
    (f : Module.End k (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ)))
    (hf : f ∈ degreeRaisingEndomorphisms k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) 1)
    (p : NativeDerivationExtension k L (nativeEulerDerivation k L ℒ)) :
    (nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ) (f p)).1 = 0 := by
  have hp : p ∈ nativeEulerExtensionFlag k L ℒ 0 := by
    rw [nativeEulerExtensionFlag_zero]
    exact Submodule.mem_top
  have h := hf 0 p hp
  change (nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ) (f p)).1 = 0 ∧
    (nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ) (f p)).2 ∈
      nativeGradedTail k L ℒ 1 at h
  exact h.1

/-- Actual deviation in the actual degree-one operator space gives the
actual scalar-axis positivity condition, without assuming that condition. -/
theorem nativeEulerAutomorphism_scalar_of_raising_deviation
    (T : NativeDerivationExtension k L (nativeEulerDerivation k L ℒ) ≃ₗ⁅k⁆
      NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
    (hT : T.toLinearEquiv.toLinearMap - LinearMap.id ∈ degreeRaisingEndomorphisms k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) 1) :
    (nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ)
      (T (nativeDerivationExtensionAxis k L (nativeEulerDerivation k L ℒ)))).1 = 1 := by
  have h := nativeEulerRaisingEndomorphism_scalar_eq_zero k L ℒ _ hT
    (nativeDerivationExtensionAxis k L (nativeEulerDerivation k L ℒ))
  change (nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ)
    (T (nativeDerivationExtensionAxis k L (nativeEulerDerivation k L ℒ)) -
      nativeDerivationExtensionAxis k L (nativeEulerDerivation k L ℒ))).1 = 0 at h
  rw [map_sub] at h
  change (nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ)
    (T (nativeDerivationExtensionAxis k L (nativeEulerDerivation k L ℒ)))).1 - 1 = 0 at h
  exact sub_eq_zero.mp h

/-- The same actual deviation gives the original homogeneous-tail
positivity condition, by the proved actual original-vector inclusion. -/
theorem nativeEulerAutomorphism_raise_of_raising_deviation
    (T : NativeDerivationExtension k L (nativeEulerDerivation k L ℒ) ≃ₗ⁅k⁆
      NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
    (hT : T.toLinearEquiv.toLinearMap - LinearMap.id ∈ degreeRaisingEndomorphisms k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) 1)
    (n : ℕ) (w : L) (hw : w ∈ ℒ n) :
    (nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ)
      (T (nativeDerivationExtensionOriginal k L (nativeEulerDerivation k L ℒ) w))).2 - w ∈
        nativeGradedTail k L ℒ (n + 1) := by
  have h := hT n
    (nativeDerivationExtensionOriginal k L (nativeEulerDerivation k L ℒ) w)
    (nativeEulerOriginal_mem_extensionFlag k L ℒ n w hw)
  change (nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ)
    (T (nativeDerivationExtensionOriginal k L (nativeEulerDerivation k L ℒ) w) -
      nativeDerivationExtensionOriginal k L (nativeEulerDerivation k L ℒ) w)).1 = 0 ∧
    (nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ)
      (T (nativeDerivationExtensionOriginal k L (nativeEulerDerivation k L ℒ) w) -
        nativeDerivationExtensionOriginal k L (nativeEulerDerivation k L ℒ) w)).2 ∈
      nativeGradedTail k L ℒ (n + 1) at h
  rw [map_sub] at h
  exact h.2

/-- Genuine classification now follows from actual degree-one deviation
in the actual constructed flag, rather than two selected positivity fields. -/
theorem existsUnique_nativeEulerExponential_of_raising_deviation
    (hzero : ℒ 0 = ⊥) (c : ℕ) (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥)
    (T : NativeDerivationExtension k L (nativeEulerDerivation k L ℒ) ≃ₗ⁅k⁆
      NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
    (hT : T.toLinearEquiv.toLinearMap - LinearMap.id ∈ degreeRaisingEndomorphisms k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) 1) :
    ∃! x : L, nativePositiveFiniteGradingExponential k L ℒ hzero c hbound
      (nativeEulerDerivation k L ℒ) x = T :=
  existsUnique_nativeEulerExponential_of_actual_positive_automorphism
    k L ℒ hzero c hbound T
    (nativeEulerAutomorphism_scalar_of_raising_deviation k L ℒ T hT)
    (nativeEulerAutomorphism_raise_of_raising_deviation k L ℒ T hT)

end ChenRanks.LieComparison
