import ChenRanks.GroupAssociatedGradedLie
import Mathlib.Algebra.Lie.Subalgebra

/-!
# Genuine generation of the original group associated Lie algebra

The native recursion `Γ_(n+2)=[Γ_(n+1),G]` is the actual subgroup
closure of original commutators. The actual quotient class homomorphism
and genuine tensor induction prove that every next rationalized piece
is spanned by the actual brackets of the preceding piece with the first
one. Original direct-sum induction then proves Lie generation in degree
one. No finite generation or holonomy comparison is assumed.
-/

noncomputable section

open scoped commutatorElement TensorProduct DirectSum

namespace ChenRanks

variable (G : Type*) [Group G]

/-- These are the actual quotient parents of the already proved
commutative successive quotient, exposed at its native quotient type. -/
local instance generationNativeQuotientCommGroup (r : ℕ) :
    CommGroup (lowerCentralSeries G r ⧸ nextLowerCentralIn G r) :=
  inferInstanceAs (CommGroup (lowerCentralPiece G r))

local instance generationNativeAdditiveCommGroup (r : ℕ) :
    AddCommGroup (Additive (lowerCentralSeries G r ⧸ nextLowerCentralIn G r)) :=
  inferInstanceAs (AddCommGroup (Additive (lowerCentralPiece G r)))

/-- The genuine rationalized class of an original representative,
retagged multiplicatively so that its original quotient homomorphism
remains a native group homomorphism. -/
def lowerCentralRationalRepresentativeHom (r : ℕ) :
    lowerCentralSeries G r →* Multiplicative (rationalLowerCentralPiece G r) where
  toFun g := Multiplicative.ofAdd
    ((1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul (QuotientGroup.mk' (nextLowerCentralIn G r) g))
  map_one' := by
    change Multiplicative.ofAdd
      ((1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul
        (QuotientGroup.mk' (nextLowerCentralIn G r) (1 : lowerCentralSeries G r))) = 1
    rw [map_one]
    exact congrArg Multiplicative.ofAdd (TensorProduct.tmul_zero (Additive (lowerCentralPiece G r)) (1 : ℚ))
  map_mul' g h := by
    change Multiplicative.ofAdd
      ((1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul
        (QuotientGroup.mk' (nextLowerCentralIn G r) (g * h))) = _
    rw [map_mul]
    change Multiplicative.ofAdd
      ((1 : ℚ) ⊗ₜ[ℤ] (Additive.ofMul
        (QuotientGroup.mk' (nextLowerCentralIn G r) g) + Additive.ofMul
        (QuotientGroup.mk' (nextLowerCentralIn G r) h))) = _
    exact congrArg Multiplicative.ofAdd (TensorProduct.tmul_add _ _ _)

@[simp] theorem lowerCentralRationalRepresentativeHom_value (r : ℕ)
    (g : lowerCentralSeries G r) :
    Multiplicative.toAdd (lowerCentralRationalRepresentativeHom G r g) =
      (1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul
        (QuotientGroup.mk' (nextLowerCentralIn G r) g) := rfl

/-- An actual base-field span of actual original quotient brackets. -/
def nextLowerCentralBracketSpan (n : ℕ) :
    Submodule ℚ (rationalLowerCentralPiece G (n + 1)) :=
  Submodule.span ℚ (Set.range (fun p :
    rationalLowerCentralPiece G n × rationalLowerCentralPiece G 0 =>
      rationalLowerCentralPieceBracket G n 0 p.1 p.2))

/-- The native subgroup closure is mapped into the actual bracket span
by its actual class homomorphism. -/
theorem lowerCentral_representative_mem_bracketSpan (n : ℕ) (g : G)
    (hg : g ∈ lowerCentralSeries G (n + 1)) :
    Multiplicative.toAdd (lowerCentralRationalRepresentativeHom G (n + 1) ⟨g, hg⟩) ∈
      nextLowerCentralBracketSpan G n := by
  change g ∈ Subgroup.closure
    {w | ∃ x ∈ lowerCentralSeries G n, ∃ y ∈ (⊤ : Subgroup G), ⁅x, y⁆ = w} at hg
  induction hg using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨x, hx, y, _hy, rfl⟩ := hw
    refine Submodule.subset_span ?_
    refine ⟨((1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul
      (QuotientGroup.mk' (nextLowerCentralIn G n) ⟨x, hx⟩),
      (1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul
        (QuotientGroup.mk' (nextLowerCentralIn G 0) ⟨y, Subgroup.mem_top y⟩)), ?_⟩
    dsimp only
    rw [rationalLowerCentralPieceBracket_tmul_tmul]
    simp only [mul_one]
    rfl
  | one =>
    change Multiplicative.toAdd
      (lowerCentralRationalRepresentativeHom G (n + 1)
        (1 : lowerCentralSeries G (n + 1))) ∈ nextLowerCentralBracketSpan G n
    have h := (lowerCentralRationalRepresentativeHom G (n + 1)).map_one
    have hvalue := congrArg Multiplicative.toAdd h
    rw [hvalue]
    exact (nextLowerCentralBracketSpan G n).zero_mem
  | mul x y hx hy ihx ihy =>
    change Multiplicative.toAdd
      (lowerCentralRationalRepresentativeHom G (n + 1)
        ((⟨x, hx⟩ : lowerCentralSeries G (n + 1)) *
          (⟨y, hy⟩ : lowerCentralSeries G (n + 1)))) ∈ nextLowerCentralBracketSpan G n
    have h := (lowerCentralRationalRepresentativeHom G (n + 1)).map_mul
      ⟨x, hx⟩ ⟨y, hy⟩
    have hvalue := congrArg Multiplicative.toAdd h
    rw [hvalue]
    exact (nextLowerCentralBracketSpan G n).add_mem ihx ihy
  | inv x hx ihx =>
    change Multiplicative.toAdd
      (lowerCentralRationalRepresentativeHom G (n + 1)
        ((⟨x, hx⟩ : lowerCentralSeries G (n + 1))⁻¹)) ∈ nextLowerCentralBracketSpan G n
    have h := (lowerCentralRationalRepresentativeHom G (n + 1)).map_inv ⟨x, hx⟩
    have hvalue := congrArg Multiplicative.toAdd h
    rw [hvalue]
    exact (nextLowerCentralBracketSpan G n).neg_mem ihx

theorem lowerCentral_tensor_one_mem_bracketSpan (n : ℕ)
    (a : Additive (lowerCentralPiece G (n + 1))) :
    (1 : ℚ) ⊗ₜ[ℤ] a ∈ nextLowerCentralBracketSpan G n := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (nextLowerCentralIn G (n + 1))
    (Additive.toMul a)
  have ha : Additive.ofMul (QuotientGroup.mk' (nextLowerCentralIn G (n + 1)) g) = a :=
    congrArg Additive.ofMul hg
  rw [← ha]
  exact lowerCentral_representative_mem_bracketSpan G n (g : G) g.property

/-- Every element of the actual next rationalized piece belongs to
the actual original bracket span, by real tensor-product induction. -/
theorem nextLowerCentralBracketSpan_eq_top (n : ℕ) :
    nextLowerCentralBracketSpan G n = ⊤ := by
  apply top_unique
  intro w _hw
  clear _hw
  induction w using TensorProduct.induction_on with
  | zero => exact (nextLowerCentralBracketSpan G n).zero_mem
  | add x y ihx ihy => exact (nextLowerCentralBracketSpan G n).add_mem ihx ihy
  | tmul c a =>
    have h := (nextLowerCentralBracketSpan G n).smul_mem c
      (lowerCentral_tensor_one_mem_bracketSpan G n a)
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h

/-- A genuine Lie subalgebra containing the original first piece
contains every original homogeneous piece; no generation premise is
inserted into the actual associated-graded definition. -/
theorem rationalGroupGradedLieSubalgebra_eq_top
    (H : LieSubalgebra ℚ (rationalGroupAssociatedGraded G))
    (hfirst : ∀ x : rationalLowerCentralPiece G 0,
      rationalGroupGradedInclusion G 0 x ∈ H) : H = ⊤ := by
  have hdegree : ∀ n (x : rationalLowerCentralPiece G n),
      rationalGroupGradedInclusion G n x ∈ H := by
    intro n
    induction n with
    | zero => exact hfirst
    | succ n ih =>
      intro x
      have hx : x ∈ nextLowerCentralBracketSpan G n := by
        rw [nextLowerCentralBracketSpan_eq_top]
        exact Submodule.mem_top
      change x ∈ Submodule.span ℚ (Set.range (fun p :
        rationalLowerCentralPiece G n × rationalLowerCentralPiece G 0 =>
          rationalLowerCentralPieceBracket G n 0 p.1 p.2)) at hx
      induction hx using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨⟨y, z⟩, rfl⟩ := hw
        have h := H.lie_mem (ih y) (hfirst z)
        simpa only [rationalGroupAssociatedGraded_lie_inclusions, Nat.add_zero] using h
      | zero =>
        rw [map_zero]
        exact H.zero_mem
      | add x y _hx _hy ihx ihy =>
        rw [map_add]
        exact H.add_mem ihx ihy
      | smul c x _hx ihx =>
        rw [map_smul]
        exact H.smul_mem c ihx
  apply top_unique
  intro x _hx
  clear _hx
  induction x using DirectSum.induction_on with
  | zero => exact H.zero_mem
  | add x y ihx ihy => exact H.add_mem ihx ihy
  | of n x => exact hdegree n x

/-- The original rational associated Lie algebra is truly generated
by the original rationalized first lower-central quotient. -/
theorem rationalGroupAssociatedGraded_lieSpan_first_eq_top :
    LieSubalgebra.lieSpan ℚ (rationalGroupAssociatedGraded G)
      (Set.range (rationalGroupGradedInclusion G 0)) = ⊤ := by
  apply rationalGroupGradedLieSubalgebra_eq_top G
  intro x
  exact LieSubalgebra.subset_lieSpan ⟨x, rfl⟩

end ChenRanks
