import ChenRanks.GroupFlagAugmentation
import Mathlib.LinearAlgebra.BilinearMap

/-!
# Actual mixed bracket on the actual raising-operator quotients

The bracket is the original noncommutative endomorphism commutator.
Composition genuinely adds raising degrees. Changing either representative
by its actual next raising subspace changes the commutator by the actual
next target subspace. Two actual quotient universal properties therefore
construct an actual bilinear map. No bracket or well-definedness field is
supplied. The direct-sum Lie structure is a further step.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k E : Type*) [Field k] [AddCommGroup E] [Module k E]
variable (F : ℕ → Submodule k E)

/-- The actual ring commutator, with its genuinely proved target degree. -/
def raisingCommutatorBilinear (q r : ℕ) :
    degreeRaisingEndomorphisms k E F q →ₗ[k]
      degreeRaisingEndomorphisms k E F r →ₗ[k]
        degreeRaisingEndomorphisms k E F (q + r) :=
  LinearMap.mk₂ k
    (fun a b => ⟨(a : Module.End k E) * b - (b : Module.End k E) * a,
      commutator_mem_degreeRaisingEndomorphisms k E F q r a b a.property b.property⟩)
    (by
      intro a₁ a₂ b
      apply Subtype.ext
      change ((a₁ : Module.End k E) + a₂) * b -
          (b : Module.End k E) * (a₁ + a₂) =
        ((a₁ : Module.End k E) * b - (b : Module.End k E) * a₁) +
          ((a₂ : Module.End k E) * b - (b : Module.End k E) * a₂)
      noncomm_ring)
    (by
      intro c a b
      apply Subtype.ext
      change (c • (a : Module.End k E)) * b -
          (b : Module.End k E) * (c • a) =
        c • ((a : Module.End k E) * b - (b : Module.End k E) * a)
      rw [smul_mul_assoc, mul_smul_comm, smul_sub])
    (by
      intro a b₁ b₂
      apply Subtype.ext
      change (a : Module.End k E) * ((b₁ : Module.End k E) + b₂) -
          ((b₁ : Module.End k E) + b₂) * a =
        ((a : Module.End k E) * b₁ - (b₁ : Module.End k E) * a) +
          ((a : Module.End k E) * b₂ - (b₂ : Module.End k E) * a)
      noncomm_ring)
    (by
      intro c a b
      apply Subtype.ext
      change (a : Module.End k E) * (c • (b : Module.End k E)) -
          (c • (b : Module.End k E)) * a =
        c • ((a : Module.End k E) * b - (b : Module.End k E) * a)
      rw [mul_smul_comm, smul_mul_assoc, smul_sub])

/-- The actual current commutator is projected into the actual target
successive quotient. -/
def raisingProjectedCommutator (q r : ℕ) :
    degreeRaisingEndomorphisms k E F q →ₗ[k]
      degreeRaisingEndomorphisms k E F r →ₗ[k] DegreeRaisingPiece k E F (q + r) :=
  (raisingCommutatorBilinear k E F q r).compr₂
    (nextDegreeRaisingWithin k E F (q + r)).mkQ

/-- Actual next-degree changes in the first slot disappear after the
actual target quotient projection. -/
theorem nextDegreeRaisingWithin_le_projectedCommutator_ker (q r : ℕ) :
    nextDegreeRaisingWithin k E F q ≤
      (raisingProjectedCommutator k E F q r).ker := by
  intro a ha
  apply LinearMap.ext
  intro b
  change (nextDegreeRaisingWithin k E F (q + r)).mkQ
    (raisingCommutatorBilinear k E F q r a b) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change (a : Module.End k E) * b - (b : Module.End k E) * a ∈
    degreeRaisingEndomorphisms k E F ((q + r) + 1)
  have h := commutator_mem_degreeRaisingEndomorphisms k E F (q + 1) r a b ha b.property
  simpa only [show (q + 1) + r = (q + r) + 1 by omega] using h

def raisingCommutatorLeftQuotient (q r : ℕ) :
    DegreeRaisingPiece k E F q →ₗ[k]
      degreeRaisingEndomorphisms k E F r →ₗ[k] DegreeRaisingPiece k E F (q + r) :=
  (nextDegreeRaisingWithin k E F q).liftQ
    (raisingProjectedCommutator k E F q r)
    (nextDegreeRaisingWithin_le_projectedCommutator_ker k E F q r)

/-- The second actual quotient also descends, after the first one,
using actual representatives of that original quotient. -/
theorem nextDegreeRaisingWithin_le_leftQuotient_ker (q r : ℕ)
    (x : DegreeRaisingPiece k E F q) :
    nextDegreeRaisingWithin k E F r ≤
      (raisingCommutatorLeftQuotient k E F q r x).ker := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (nextDegreeRaisingWithin k E F q) x
  intro b hb
  change (nextDegreeRaisingWithin k E F (q + r)).mkQ
    (raisingCommutatorBilinear k E F q r a b) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change (a : Module.End k E) * b - (b : Module.End k E) * a ∈
    degreeRaisingEndomorphisms k E F ((q + r) + 1)
  have h := commutator_mem_degreeRaisingEndomorphisms k E F q (r + 1) a b a.property hb
  simpa only [show q + (r + 1) = (q + r) + 1 by omega] using h

/-- The true bilinear bracket of the true actual operator layers. -/
def raisingPieceBracket (q r : ℕ) :
    DegreeRaisingPiece k E F q →ₗ[k]
      DegreeRaisingPiece k E F r →ₗ[k] DegreeRaisingPiece k E F (q + r) where
  toFun x := (nextDegreeRaisingWithin k E F r).liftQ
    (raisingCommutatorLeftQuotient k E F q r x)
    (nextDegreeRaisingWithin_le_leftQuotient_ker k E F q r x)
  map_add' x y := by
    apply LinearMap.ext
    intro z
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective (nextDegreeRaisingWithin k E F r) z
    change raisingCommutatorLeftQuotient k E F q r (x + y) b =
      raisingCommutatorLeftQuotient k E F q r x b +
        raisingCommutatorLeftQuotient k E F q r y b
    rw [map_add, LinearMap.add_apply]
  map_smul' c x := by
    apply LinearMap.ext
    intro z
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective (nextDegreeRaisingWithin k E F r) z
    change raisingCommutatorLeftQuotient k E F q r (c • x) b =
      c • raisingCommutatorLeftQuotient k E F q r x b
    rw [map_smul, LinearMap.smul_apply]

@[simp] theorem raisingPieceBracket_mk_mk (q r : ℕ)
    (a : degreeRaisingEndomorphisms k E F q)
    (b : degreeRaisingEndomorphisms k E F r) :
    raisingPieceBracket k E F q r
      ((nextDegreeRaisingWithin k E F q).mkQ a)
      ((nextDegreeRaisingWithin k E F r).mkQ b) =
      (nextDegreeRaisingWithin k E F (q + r)).mkQ
        (raisingCommutatorBilinear k E F q r a b) := rfl

end ChenRanks.LieComparison
