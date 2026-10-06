import ChenRanks.ArrangementFiniteEulerParallelFrames
import ChenRanks.NativeEulerExponentialGroup

/-!
# The actual local parallel frames take values in the actual exponential group

The actual finite Euler exponential subgroup is the previously constructed
subgroup of original native complex Lie automorphisms. The actual finite
parallel sum has a genuinely proved degree-one deviation. The native
Euler classification therefore places this specific parallel frame in the
actual subgroup. Its original continuous-operator interpretation is exactly
the constructed parallel sum, and is injective and multiplicative.

Neither an exponential representation nor subgroup membership, selected
local frames, positivity, or monodromy is supplied as an input. The only
local data are the actual open convex complement neighborhood and its
actual anchor. The actual covering construction remains a separate step.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

open LieComparison

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι) (c : ℕ)

local instance finiteExpFrameNormedAddCommGroup :
    NormedAddCommGroup (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedAddCommGroup ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance finiteExpFrameNormedSpace :
    NormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c)

/-- The actual subgroup with the original composition law, constructed
from the actual finite positive grading and its proved bound. -/
abbrev ActualFiniteEulerExponentialGroup :=
  nativeEulerExponentialSubgroup ℂ (A.ActualFiniteLogarithmicLie c)
    (A.actualFiniteLogarithmicComponent c)
    (A.actualFiniteLogarithmicComponent_zero c) c
    (A.actualFiniteLogarithmicComponent_above c)

/-- Original native automorphisms act by their actual continuous complex
endomorphisms. This is the genuine composition monoid homomorphism. -/
def actualFiniteEulerExponentialEnd :
    A.ActualFiniteEulerExponentialGroup c →*
      A.ActualFiniteLogarithmicEulerCoefficients c where
  toFun h := nativeFiniteEndContinuousAlgEquiv ℂ
    (A.ActualFiniteLogarithmicEulerSpace c) h.val.toLinearEquiv.toLinearMap
  map_one' := by
    apply ContinuousLinearMap.ext
    intro p
    rfl
  map_mul' h g := by
    apply ContinuousLinearMap.ext
    intro p
    rfl

@[simp] theorem actualFiniteEulerExponentialEnd_apply
    (h : A.ActualFiniteEulerExponentialGroup c)
    (p : A.ActualFiniteLogarithmicEulerSpace c) :
    A.actualFiniteEulerExponentialEnd c h p = h.val p := rfl

/-- The original endomorphism interpretation detects equality of the
actual subgroup elements, by equality on all original vectors. -/
theorem actualFiniteEulerExponentialEnd_injective :
    Function.Injective (A.actualFiniteEulerExponentialEnd c) := by
  intro h g hEnd
  apply Subtype.ext
  apply LieEquiv.ext
  intro p
  exact congrArg (fun f : A.ActualFiniteLogarithmicEulerCoefficients c => f p) hEnd

variable (s : Set (Fin d → ℂ)) (hs : Convex ℝ s) (hso : IsOpen s)
variable (hscomp : s ⊆ A.ambientComplementSet)
variable (x₀ : Fin d → ℂ) (hx₀ : x₀ ∈ s)

/-- The specific constructed parallel frame is in the actual native
exponential subgroup, by its proved actual degree-one deviation. -/
theorem actualFiniteEulerParallelLieEquiv_mem_exponentialGroup
    (x : Fin d → ℂ) (hx : x ∈ s) :
    A.actualFiniteEulerParallelLieEquiv c s hs hso hscomp x₀ hx₀ x hx ∈
      nativeEulerExponentialSubgroup ℂ (A.ActualFiniteLogarithmicLie c)
        (A.actualFiniteLogarithmicComponent c)
        (A.actualFiniteLogarithmicComponent_zero c) c
        (A.actualFiniteLogarithmicComponent_above c) := by
  let T := A.actualFiniteEulerParallelLieEquiv c s hs hso hscomp x₀ hx₀ x hx
  have hT := A.actualFiniteEulerParallelLieEquiv_raising_deviation c
    s hs hso hscomp x₀ hx₀ x hx
  exact nativeEulerExponentialSubgroup_mem_of_positive ℂ
    (A.ActualFiniteLogarithmicLie c) (A.actualFiniteLogarithmicComponent c)
    (A.actualFiniteLogarithmicComponent_zero c) c
    (A.actualFiniteLogarithmicComponent_above c) T
    (nativeEulerAutomorphism_scalar_of_raising_deviation ℂ
      (A.ActualFiniteLogarithmicLie c) (A.actualFiniteLogarithmicComponent c) T hT)
    (nativeEulerAutomorphism_raise_of_raising_deviation ℂ
      (A.ActualFiniteLogarithmicLie c) (A.actualFiniteLogarithmicComponent c) T hT)

/-- Actual subgroup-valued local frames on the actual original set. -/
def actualFiniteEulerExponentialFrame (x : s) : A.ActualFiniteEulerExponentialGroup c :=
  ⟨A.actualFiniteEulerParallelLieEquiv c s hs hso hscomp x₀ hx₀ x.val x.property,
    A.actualFiniteEulerParallelLieEquiv_mem_exponentialGroup c
      s hs hso hscomp x₀ hx₀ x.val x.property⟩

@[simp] theorem actualFiniteEulerExponentialFrameEnd_eq_parallel (x : s) :
    A.actualFiniteEulerExponentialEnd c
      (A.actualFiniteEulerExponentialFrame c s hs hso hscomp x₀ hx₀ x) =
      A.actualFiniteEulerParallelFunction c s hs hso hscomp x₀ x.val := by
  apply ContinuousLinearMap.ext
  intro p
  rfl

end ChenRanks.AffineArrangement
