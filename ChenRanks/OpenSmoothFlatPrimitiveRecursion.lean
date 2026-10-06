import ChenRanks.OpenSmoothFlatProductPrimitive

/-!
# Actual anchored primitives for the flat-connection recursion

Each successive function is actually chosen from the native Poincare
existence theorem proved for the actual preceding right-product form.
The induction data below contain proved derivatives of previously
constructed functions; they are not supplied as a final parallel-solution
input.  The initial functions are the actual zero and the actual unit.

The resulting sequence consists of actual C-infinity functions, with
the actual original derivative equation in every degree and the actual
anchor zero in all positive degrees.  A finite truncation is not yet
asserted to solve the final parallel equation: the actual raising-degree
construction still has to make its last product vanish.  Invertibility,
Lie bracket preservation, positive action, and monodromy remain further
proofs.
-/

noncomputable section

namespace ChenRanks.OpenSmoothForms

variable {E R : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

/-- Actual previously constructed functions and their already proved
original derivative equation.  This is internal induction data. -/
structure FlatPrimitiveStage (s : Set E) (ω : E → E →L[ℝ] R) where
  previous : E → R
  current : E → R
  previous_smooth : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) previous s
  current_smooth : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) current s
  current_derivative : ∀ x ∈ s,
    HasFDerivAt current (rightProductOneForm ω previous x) x

/-- The genuine initial stage: derivative of the actual unit is the
actual product of the original form with the actual zero function. -/
def initialFlatPrimitiveStage (s : Set E) (ω : E → E →L[ℝ] R) :
    FlatPrimitiveStage s ω where
  previous := fun _ => 0
  current := fun _ => 1
  previous_smooth := contDiffOn_const
  current_smooth := contDiffOn_const
  current_derivative := by
    intro x hx
    have hz : rightProductOneForm ω (fun _ => 0) x = 0 := by
      ext v
      simp only [rightProductOneForm_apply, mul_zero, ContinuousLinearMap.zero_apply]
    rw [hz]
    exact hasFDerivAt_const (1 : R) x

variable (s : Set E) (hs : Convex ℝ s) (hso : IsOpen s)
variable (ω : E → E →L[ℝ] R)
variable (hω : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ω s)
variable (hclosed : ∀ x ∈ s, extDeriv (fun y =>
  ContinuousAlternatingMap.ofSubsingleton ℝ E R (0 : Fin 1) (ω y)) x = 0)
variable (hcomm : ∀ x ∈ s, ∀ u v : E, ω x u * ω x v = ω x v * ω x u)
variable (x₀ : E)

include hs hso hω hclosed hcomm

/-- The next actual primitive is genuinely constructed from the actual
current stage, using the native anchored Poincare theorem. -/
theorem exists_nextFlatPrimitive (q : FlatPrimitiveStage s ω) :
    ∃ p : E → R, ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) p s ∧
      p x₀ = 0 ∧ ∀ x ∈ s,
        HasFDerivAt p (rightProductOneForm ω q.current x) x := by
  apply exists_anchored_flatProduct_primitive s hs hso ω q.current q.previous
    hω q.current_smooth hclosed hcomm ?_ x₀
  intro x hx u
  have h := congrArg (fun d : E →L[ℝ] R => d u) (q.current_derivative x hx).fderiv
  simpa only [rightProductOneForm_apply] using h

/-- Native choice selects only the genuinely proved next primitive. -/
def nextFlatPrimitiveStage (q : FlatPrimitiveStage s ω) : FlatPrimitiveStage s ω where
  previous := q.current
  current := Classical.choose (exists_nextFlatPrimitive s hs hso ω hω hclosed hcomm x₀ q)
  previous_smooth := q.current_smooth
  current_smooth :=
    (Classical.choose_spec (exists_nextFlatPrimitive s hs hso ω hω hclosed hcomm x₀ q)).1
  current_derivative :=
    (Classical.choose_spec (exists_nextFlatPrimitive s hs hso ω hω hclosed hcomm x₀ q)).2.2

@[simp] theorem nextFlatPrimitiveStage_previous (q : FlatPrimitiveStage s ω) :
    (nextFlatPrimitiveStage s hs hso ω hω hclosed hcomm x₀ q).previous = q.current := rfl

theorem nextFlatPrimitiveStage_anchor (q : FlatPrimitiveStage s ω) :
    (nextFlatPrimitiveStage s hs hso ω hω hclosed hcomm x₀ q).current x₀ = 0 :=
  (Classical.choose_spec (exists_nextFlatPrimitive s hs hso ω hω hclosed hcomm x₀ q)).2.1

/-- The actual sequence is produced recursively from the actual
initial stage and the proved actual native primitive step. -/
def actualFlatPrimitiveStage : ℕ → FlatPrimitiveStage s ω
  | 0 => initialFlatPrimitiveStage s ω
  | n + 1 => nextFlatPrimitiveStage s hs hso ω hω hclosed hcomm x₀
      (actualFlatPrimitiveStage n)

/-- The actual n-th function of this genuinely constructed recursion. -/
def actualFlatPrimitiveFunction (n : ℕ) : E → R :=
  (actualFlatPrimitiveStage s hs hso ω hω hclosed hcomm x₀ n).current

@[simp] theorem actualFlatPrimitiveFunction_zero :
    actualFlatPrimitiveFunction s hs hso ω hω hclosed hcomm x₀ 0 = fun _ => 1 := rfl

theorem actualFlatPrimitiveFunction_smooth (n : ℕ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (actualFlatPrimitiveFunction s hs hso ω hω hclosed hcomm x₀ n) s :=
  (actualFlatPrimitiveStage s hs hso ω hω hclosed hcomm x₀ n).current_smooth

theorem actualFlatPrimitiveFunction_succ_anchor (n : ℕ) :
    actualFlatPrimitiveFunction s hs hso ω hω hclosed hcomm x₀ (n + 1) x₀ = 0 :=
  nextFlatPrimitiveStage_anchor s hs hso ω hω hclosed hcomm x₀ _

/-- The genuine original derivative equation in every positive degree
is a proved property of the actually constructed sequence. -/
theorem actualFlatPrimitiveFunction_succ_derivative (n : ℕ) (x : E) (hx : x ∈ s) :
    HasFDerivAt
      (actualFlatPrimitiveFunction s hs hso ω hω hclosed hcomm x₀ (n + 1))
      (rightProductOneForm ω
        (actualFlatPrimitiveFunction s hs hso ω hω hclosed hcomm x₀ n) x) x :=
  (actualFlatPrimitiveStage s hs hso ω hω hclosed hcomm x₀ (n + 1)).current_derivative x hx

end ChenRanks.OpenSmoothForms
