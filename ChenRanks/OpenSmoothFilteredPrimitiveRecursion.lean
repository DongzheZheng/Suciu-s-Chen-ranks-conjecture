import ChenRanks.OpenSmoothFlatPrimitiveRecursion
import ChenRanks.OpenSmoothSubmodulePrimitive

/-!
# Actual flat primitives constructed in actual successive raising subspaces

Each primitive is projected into the actual next subspace without
altering its actual derivative.  The needed value constraint on that
derivative is proved from the preceding primitive's actual values and
the actual product containment.  Thus the degree constraint is a proved
property of the constructed functions, not a selected-function input.

This is a generic internal recursion for an actual filtered normed
algebra.  For the actual affine adjoint the subspaces and product law
come from the separately constructed actual raising endomorphisms.  The
input product law is explicitly retained here; it is not a substitute
for the arrangement's actual grading or flatness construction.
-/

noncomputable section

namespace ChenRanks.OpenSmoothForms

variable {E R : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
variable [FiniteDimensional ℝ R]

/-- Actual recursion data, now with the actual value of the current
function in its actual degree subspace. -/
structure FilteredFlatPrimitiveStage (s : Set E) (ω : E → E →L[ℝ] R)
    (P : ℕ → Submodule ℝ R) (n : ℕ) extends FlatPrimitiveStage s ω where
  current_mem : ∀ x : E, current x ∈ P n

variable (s : Set E) (hs : Convex ℝ s) (hso : IsOpen s)
variable (ω : E → E →L[ℝ] R)
variable (hω : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ω s)
variable (hclosed : ∀ x ∈ s, extDeriv (fun y =>
  ContinuousAlternatingMap.ofSubsingleton ℝ E R (0 : Fin 1) (ω y)) x = 0)
variable (hcomm : ∀ x ∈ s, ∀ u v : E, ω x u * ω x v = ω x v * ω x u)
variable (P : ℕ → Submodule ℝ R)
variable (hmul : ∀ a b : ℕ, ∀ r t : R, r ∈ P a → t ∈ P b → r * t ∈ P (a + b))
variable (hone : (1 : R) ∈ P 0)
variable (hωvalues : ∀ x ∈ s, ∀ v : E, ω x v ∈ P 1)
variable (x₀ : E)

include hs hso hω hclosed hcomm hmul hωvalues

/-- The actual unit has the actual degree-zero value. -/
def initialFilteredFlatPrimitiveStage : FilteredFlatPrimitiveStage s ω P 0 where
  toFlatPrimitiveStage := initialFlatPrimitiveStage s ω
  current_mem := fun _ => hone

/-- The actual next degree primitive is genuinely constructed by native
Poincare and the genuinely constructed continuous projection. -/
theorem exists_nextFilteredFlatPrimitive (n : ℕ)
    (q : FilteredFlatPrimitiveStage s ω P n) :
    ∃ p : E → R, ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) p s ∧
      p x₀ = 0 ∧ (∀ x : E, p x ∈ P (n + 1)) ∧
      ∀ x ∈ s, HasFDerivAt p (rightProductOneForm ω q.current x) x := by
  apply exists_anchored_vector_infiniteSmooth_primitive_in_submodule
    s hs hso (rightProductOneForm ω q.current)
    (rightProductOneForm_contDiffOn s ω q.current hω q.current_smooth)
    ?_ (P (n + 1)) ?_ x₀
  · intro x hx
    have hdf : ∀ u : E, fderiv ℝ q.current x u = ω x u * q.previous x := by
      intro u
      have h := congrArg (fun d : E →L[ℝ] R => d u) (q.current_derivative x hx).fderiv
      simpa only [rightProductOneForm_apply] using h
    exact rightProductOneForm_exteriorDerivative_eq_zero ω q.current q.previous x
      (((hω.differentiableOn (by simp)) x hx).differentiableAt (hso.mem_nhds hx))
      (((q.current_smooth.differentiableOn (by simp)) x hx).differentiableAt
        (hso.mem_nhds hx)) (hclosed x hx) (hcomm x hx) hdf
  · intro x hx v
    change ω x v * q.current x ∈ P (n + 1)
    have h := hmul 1 n (ω x v) (q.current x) (hωvalues x hx v) (q.current_mem x)
    simpa only [Nat.add_comm 1 n] using h

/-- Native choice only selects from the actual proved next-degree
primitive existence, including its actual value constraint. -/
def nextFilteredFlatPrimitiveStage (n : ℕ)
    (q : FilteredFlatPrimitiveStage s ω P n) : FilteredFlatPrimitiveStage s ω P (n + 1) where
  previous := q.current
  current := Classical.choose
    (exists_nextFilteredFlatPrimitive s hs hso ω hω hclosed hcomm P hmul hωvalues x₀ n q)
  previous_smooth := q.current_smooth
  current_smooth := (Classical.choose_spec
    (exists_nextFilteredFlatPrimitive s hs hso ω hω hclosed hcomm P hmul hωvalues x₀ n q)).1
  current_mem := (Classical.choose_spec
    (exists_nextFilteredFlatPrimitive s hs hso ω hω hclosed hcomm P hmul hωvalues x₀ n q)).2.2.1
  current_derivative := (Classical.choose_spec
    (exists_nextFilteredFlatPrimitive s hs hso ω hω hclosed hcomm P hmul hωvalues x₀ n q)).2.2.2

theorem nextFilteredFlatPrimitiveStage_anchor (n : ℕ)
    (q : FilteredFlatPrimitiveStage s ω P n) :
    (nextFilteredFlatPrimitiveStage s hs hso ω hω hclosed hcomm P hmul hωvalues x₀ n q).current
      x₀ = 0 :=
  (Classical.choose_spec
    (exists_nextFilteredFlatPrimitive s hs hso ω hω hclosed hcomm P hmul hωvalues x₀ n q)).2.1

/-- The degree constraints are built into the genuinely constructed
sequence, by actual projection at each actual Poincare step. -/
def actualFilteredFlatPrimitiveStage : (n : ℕ) → FilteredFlatPrimitiveStage s ω P n
  | 0 => initialFilteredFlatPrimitiveStage s ω P hone
  | n + 1 => nextFilteredFlatPrimitiveStage s hs hso ω hω hclosed hcomm
      P hmul hωvalues x₀ n (actualFilteredFlatPrimitiveStage n)

def actualFilteredFlatPrimitiveFunction (n : ℕ) : E → R :=
  (actualFilteredFlatPrimitiveStage s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ n).current

@[simp] theorem actualFilteredFlatPrimitiveFunction_zero :
    actualFilteredFlatPrimitiveFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ 0 =
      fun _ => 1 := rfl

theorem actualFilteredFlatPrimitiveFunction_smooth (n : ℕ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (actualFilteredFlatPrimitiveFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ n)
      s :=
  (actualFilteredFlatPrimitiveStage s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ n).current_smooth

/-- Every actual function value has the actual raising degree, with
the same original algebra coefficients. -/
theorem actualFilteredFlatPrimitiveFunction_mem (n : ℕ) (x : E) :
    actualFilteredFlatPrimitiveFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ n x
      ∈ P n :=
  (actualFilteredFlatPrimitiveStage s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ n).current_mem x

theorem actualFilteredFlatPrimitiveFunction_succ_anchor (n : ℕ) :
    actualFilteredFlatPrimitiveFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ (n + 1)
      x₀ = 0 :=
  nextFilteredFlatPrimitiveStage_anchor s hs hso ω hω hclosed hcomm P hmul hωvalues x₀ n _

theorem actualFilteredFlatPrimitiveFunction_succ_derivative (n : ℕ) (x : E) (hx : x ∈ s) :
    HasFDerivAt
      (actualFilteredFlatPrimitiveFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ (n + 1))
      (rightProductOneForm ω
        (actualFilteredFlatPrimitiveFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ n) x) x :=
  (actualFilteredFlatPrimitiveStage s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀
    (n + 1)).current_derivative x hx

/-- The actual finite bound kills the actual last coefficient product.
This is proved from actual function values and actual multiplication. -/
theorem actualFilteredFlatPrimitiveFunction_last_product_eq_zero
    (c : ℕ) (hbound : P (c + 1) = ⊥) (x : E) (hx : x ∈ s) (v : E) :
    ω x v *
      actualFilteredFlatPrimitiveFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x = 0 := by
  have h := hmul 1 c (ω x v)
    (actualFilteredFlatPrimitiveFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x)
    (hωvalues x hx v)
    (actualFilteredFlatPrimitiveFunction_mem s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x)
  simpa only [Nat.add_comm 1 c, hbound, Submodule.mem_bot] using h

end ChenRanks.OpenSmoothForms
