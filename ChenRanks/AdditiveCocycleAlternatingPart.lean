import ChenRanks.AdditiveSymmetricCocycleSplitting
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The alternating part of an actual additive two-cocycle on an abelian
base is genuinely biadditive. Its actual symmetric part has an actual
primitive over a characteristic-zero field, obtained from the native
central-extension splitting rather than supplied as a premise.
-/

noncomputable section
namespace ChenRanks.GroupComparison

variable (A : Type*) [AddCommGroup A] (k : Type*) [Field k] [CharZero k]

/-- Explicit intermediate identities for an actual normalized additive
cocycle. Applications construct this data from the original section. -/
structure NormalizedAdditiveCocycle where
  toFun : A → A → k
  zero_right : ∀ a, toFun a 0 = 0
  zero_left : ∀ a, toFun 0 a = 0
  cocycle : ∀ a b d, toFun a b + toFun (a + b) d =
    toFun b d + toFun a (b + d)

variable {A k} (c : NormalizedAdditiveCocycle A k)

def cocycleAlternatingPart (a b : A) : k := c.toFun a b - c.toFun b a

@[simp] theorem cocycleAlternatingPart_self (a : A) :
    cocycleAlternatingPart c a a = 0 := sub_self _

theorem cocycleAlternatingPart_skew (a b : A) :
    cocycleAlternatingPart c b a = -cocycleAlternatingPart c a b := by
  unfold cocycleAlternatingPart
  ring

theorem cocycleAlternatingPart_add_left (a b d : A) :
    cocycleAlternatingPart c (a + b) d =
      cocycleAlternatingPart c a d + cocycleAlternatingPart c b d := by
  have h1 := c.cocycle a b d
  have h2 := c.cocycle d a b
  have h3 := c.cocycle a d b
  rw [add_comm d a] at h2
  rw [add_comm d b] at h3
  unfold cocycleAlternatingPart
  linear_combination h1 + h2 - h3

theorem cocycleAlternatingPart_add_right (a b d : A) :
    cocycleAlternatingPart c a (b + d) =
      cocycleAlternatingPart c a b + cocycleAlternatingPart c a d := by
  have h := cocycleAlternatingPart_skew c (b + d) a
  rw [cocycleAlternatingPart_add_left,
    cocycleAlternatingPart_skew c a b, cocycleAlternatingPart_skew c a d] at h
  linear_combination h

/-- The actual symmetric average, with all its identities proved from c. -/
def cocycleSymmetricPart : NormalizedSymmetricCocycle A k where
  toFun a b := (2 : k)⁻¹ * (c.toFun a b + c.toFun b a)
  zero_right a := by rw [c.zero_right, c.zero_left, add_zero, mul_zero]
  symmetric a b := by rw [add_comm]
  cocycle a b d := by
    have h1 := c.cocycle a b d
    have h2 := (c.cocycle d b a).symm
    rw [add_comm d b, add_comm b a] at h2
    linear_combination (2 : k)⁻¹ * h1 + (2 : k)⁻¹ * h2

/-- The actual primitive of the symmetric part leaves exactly half the
actual alternating part, with no primitive assumption. -/
theorem additiveCocycle_has_symmetric_primitive :
    ∃ f : A → k, ∀ a b,
      c.toFun a b - (f b - f (a + b) + f a) =
        (2 : k)⁻¹ * cocycleAlternatingPart c a b := by
  obtain ⟨f, hf⟩ := normalizedSymmetricCocycle_has_primitive (cocycleSymmetricPart c)
  refine ⟨f, ?_⟩
  intro a b
  rw [hf]
  change c.toFun a b - (2 : k)⁻¹ * (c.toFun a b + c.toFun b a) =
    (2 : k)⁻¹ * (c.toFun a b - c.toFun b a)
  field_simp
  ring

end ChenRanks.GroupComparison
