import ChenRanks.DegreeRaisingEndomorphisms
import ChenRanks.FiniteDimensionalNativeNorms
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-!
# Actual raising-operator subspaces in the original continuous coefficient algebra

The actual raising subspaces of original linear endomorphisms are transported
along the genuine native finite-dimensional algebra equivalence.  Their
membership, multiplication, unit, inclusion and finite-bound identities are
therefore proved for the original continuous endomorphisms.  In the complex
case restriction of the scalar submodule gives the original real subspaces
needed by real Poincare, while each element remains complex linear.

No filtered coefficient algebra or multiplication-vanishing field is selected
as an input.  The flag itself is an explicit intermediate parameter; its
native Euler-extension construction has been supplied separately.
-/

noncomputable section

namespace ChenRanks.LieComparison

section Native

variable (k T : Type*) [NontriviallyNormedField k] [CompleteSpace k]
variable [NormedAddCommGroup T] [NormedSpace k T] [FiniteDimensional k T]

/-- The actual original raising-operator subspace in the actual continuous algebra. -/
def continuousDegreeRaisingEndomorphisms (F : ℕ → Submodule k T) (m : ℕ) :
    Submodule k (T →L[k] T) :=
  (degreeRaisingEndomorphisms k T F m).map
    (nativeFiniteEndContinuousAlgEquiv k T).toLinearMap

/-- Membership tests the very same original operator and its original action. -/
theorem mem_continuousDegreeRaisingEndomorphisms
    (F : ℕ → Submodule k T) (m : ℕ) (f : T →L[k] T) :
    f ∈ continuousDegreeRaisingEndomorphisms k T F m ↔
      f.toLinearMap ∈ degreeRaisingEndomorphisms k T F m := by
  constructor
  · rintro ⟨g, hg, hgf⟩
    have he := congrArg ContinuousLinearMap.toLinearMap hgf
    change g = f.toLinearMap at he
    exact he ▸ hg
  · intro hf
    exact ⟨f.toLinearMap, hf, rfl⟩

/-- Actual continuous composition adds the actual raising degrees. -/
theorem mul_mem_continuousDegreeRaisingEndomorphisms
    (F : ℕ → Submodule k T) (a b : ℕ) (f g : T →L[k] T)
    (hf : f ∈ continuousDegreeRaisingEndomorphisms k T F a)
    (hg : g ∈ continuousDegreeRaisingEndomorphisms k T F b) :
    f * g ∈ continuousDegreeRaisingEndomorphisms k T F (a + b) := by
  apply (mem_continuousDegreeRaisingEndomorphisms k T F (a + b) (f * g)).mpr
  exact mul_mem_degreeRaisingEndomorphisms k T F a b f.toLinearMap g.toLinearMap
    ((mem_continuousDegreeRaisingEndomorphisms k T F a f).mp hf)
    ((mem_continuousDegreeRaisingEndomorphisms k T F b g).mp hg)

/-- The actual continuous identity has genuine raising degree zero. -/
theorem one_mem_continuousDegreeRaisingEndomorphisms (F : ℕ → Submodule k T) :
    (1 : T →L[k] T) ∈ continuousDegreeRaisingEndomorphisms k T F 0 :=
  (mem_continuousDegreeRaisingEndomorphisms k T F 0 1).mpr
    (one_mem_degreeRaisingEndomorphisms k T F)

theorem continuousDegreeRaisingEndomorphisms_antitone
    (F : ℕ → Submodule k T) (hF : Antitone F) :
    Antitone (continuousDegreeRaisingEndomorphisms k T F) := by
  intro m n hmn
  exact Submodule.map_mono (degreeRaisingEndomorphisms_antitone k T F hF m n hmn)

/-- The actual finite flag bound genuinely kills its actual continuous raising subspace. -/
theorem continuousDegreeRaisingEndomorphisms_eq_bot_of_bound
    (F : ℕ → Submodule k T) (hzero : F 0 = ⊤) (b : ℕ) (hbound : F b = ⊥) :
    continuousDegreeRaisingEndomorphisms k T F b = ⊥ := by
  rw [continuousDegreeRaisingEndomorphisms,
    degreeRaisingEndomorphisms_eq_bot_of_flag_bound k T F hzero b hbound,
    Submodule.map_bot]

end Native

section Complex

variable (T : Type*) [NormedAddCommGroup T] [NormedSpace ℂ T]
variable [NormedSpace ℝ T] [IsScalarTower ℝ ℂ T] [FiniteDimensional ℂ T]

/-- The actual real coefficient subspace, consisting of the original
complex-linear operators with the original constructed raising property. -/
def realContinuousDegreeRaisingEndomorphisms (F : ℕ → Submodule ℂ T) (m : ℕ) :
    Submodule ℝ (T →L[ℂ] T) :=
  (continuousDegreeRaisingEndomorphisms ℂ T F m).restrictScalars ℝ

theorem mem_realContinuousDegreeRaisingEndomorphisms
    (F : ℕ → Submodule ℂ T) (m : ℕ) (f : T →L[ℂ] T) :
    f ∈ realContinuousDegreeRaisingEndomorphisms T F m ↔
      f.toLinearMap ∈ degreeRaisingEndomorphisms ℂ T F m :=
  mem_continuousDegreeRaisingEndomorphisms ℂ T F m f

/-- The real coefficient filtration has its genuine complex composition law. -/
theorem mul_mem_realContinuousDegreeRaisingEndomorphisms
    (F : ℕ → Submodule ℂ T) (a b : ℕ) (f g : T →L[ℂ] T)
    (hf : f ∈ realContinuousDegreeRaisingEndomorphisms T F a)
    (hg : g ∈ realContinuousDegreeRaisingEndomorphisms T F b) :
    f * g ∈ realContinuousDegreeRaisingEndomorphisms T F (a + b) :=
  mul_mem_continuousDegreeRaisingEndomorphisms ℂ T F a b f g hf hg

theorem one_mem_realContinuousDegreeRaisingEndomorphisms (F : ℕ → Submodule ℂ T) :
    (1 : T →L[ℂ] T) ∈ realContinuousDegreeRaisingEndomorphisms T F 0 :=
  one_mem_continuousDegreeRaisingEndomorphisms ℂ T F

theorem realContinuousDegreeRaisingEndomorphisms_antitone
    (F : ℕ → Submodule ℂ T) (hF : Antitone F) :
    Antitone (realContinuousDegreeRaisingEndomorphisms T F) := by
  intro m n hmn
  exact continuousDegreeRaisingEndomorphisms_antitone ℂ T F hF hmn

/-- The actual finite flag bound also kills the original real coefficient subspace. -/
theorem realContinuousDegreeRaisingEndomorphisms_eq_bot_of_bound
    (F : ℕ → Submodule ℂ T) (hzero : F 0 = ⊤) (b : ℕ) (hbound : F b = ⊥) :
    realContinuousDegreeRaisingEndomorphisms T F b = ⊥ := by
  rw [realContinuousDegreeRaisingEndomorphisms,
    continuousDegreeRaisingEndomorphisms_eq_bot_of_bound ℂ T F hzero b hbound,
    Submodule.restrictScalars_bot]

end Complex

end ChenRanks.LieComparison
