import ChenRanks.KoszulMetabelianFiniteTruncation

/-!
# The actual degree-two tail of the actual finite Koszul model is abelian

Every original component of ordinary degree at least two has zero
generator coordinate. The actual quotient's actual degree-two tail is
therefore contained in the image of the original invariant ideal.
The original invariant coordinates genuinely commute, and the actual
quotient Lie morphism preserves that equality. This discharges the
tail-abelian structural input of the native Euler exponential group;
no metabelian group property or expected tail commutation is assumed.
-/

noncomputable section

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} [Fintype ι] (b : _root_.Module.Basis ι k V)
variable (K : Submodule k (⋀[k]^2 V))

open MetabelianLieModel
open ChenRanks.LieComparison

/-- Every actual original positive component above degree one has its
actual generator coordinate zero. -/
theorem modelPositiveComponent_generator_eq_zero (n : ℕ) (hn : 2 ≤ n)
    (x : MetabelianLieModel k V K) (hx : x ∈ modelPositiveComponent k V b K n) :
    x.generator = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ r =>
      obtain ⟨w, rfl⟩ := hx
      rfl

/-- The actual tail, formed from all actual quotient components, lies
in the actual image of the original invariant ideal. -/
theorem finiteModelTail_two_le_invariantImage (c : ℕ) :
    nativeGradedTail k (finiteModelTruncation k V b K c)
        (finiteModelComponent k V b K c) 2 ≤
      (invariantIdeal k V K).toSubmodule.map
        (finiteModelProjection k V b K c).toLinearMap := by
  apply Submodule.span_le.mpr
  rintro x ⟨n, hn, hx⟩
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, modelPositiveComponent_generator_eq_zero k V b K n hn y hy, rfl⟩

/-- The real original invariant image is abelian in the real quotient. -/
theorem finiteModelInvariantImage_bracket_eq_zero (c : ℕ)
    (x y : finiteModelTruncation k V b K c)
    (hx : x ∈ (invariantIdeal k V K).toSubmodule.map
      (finiteModelProjection k V b K c).toLinearMap)
    (hy : y ∈ (invariantIdeal k V K).toSubmodule.map
      (finiteModelProjection k V b K c).toLinearMap) : ⁅x, y⁆ = 0 := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  change ⁅finiteModelProjection k V b K c u, finiteModelProjection k V b K c v⁆ = 0
  rw [← LieHom.map_lie,
    bracket_eq_zero_of_generator_eq_zero k V K hu hv, map_zero]

/-- The tail-abelian input needed for the actual native Euler group is
a theorem of the actual finite model and its original positive grading. -/
theorem finiteModelTail_two_isAbelian (c : ℕ) :
    ∀ x ∈ nativeGradedTail k (finiteModelTruncation k V b K c)
      (finiteModelComponent k V b K c) 2,
    ∀ y ∈ nativeGradedTail k (finiteModelTruncation k V b K c)
      (finiteModelComponent k V b K c) 2, ⁅x, y⁆ = 0 := by
  intro x hx y hy
  exact finiteModelInvariantImage_bracket_eq_zero k V b K c x y
    (finiteModelTail_two_le_invariantImage k V b K c hx)
    (finiteModelTail_two_le_invariantImage k V b K c hy)

end ChenRanks.Koszul
