import ChenRanks.NativeEulerAxisAbelianCharacter
import Mathlib.GroupTheory.Solvable

/-! Actual commuting Lie vectors have actual commuting native finite
exponentials. Consequently, the actual positive Euler group is metabelian
when its actual degree-two tail is abelian. The latter is an intermediate
structural condition to be proved for the original finite Koszul model;
no commutativity or metabelian group law is taken as input or defined.
-/
noncomputable section
open scoped commutatorElement
namespace ChenRanks.LieComparison
variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]
variable (hzero : ℒ 0 = ⊥) (c : ℕ) (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥)

/-- The genuine native exponential in genuine affine coordinates. -/
theorem nativePositiveFiniteExponential_affine_coordinates
    (D : LieDerivation k L L) (x : L) (p : NativeDerivationExtension k L D) :
    nativeDerivationExtensionCoordinates k L D
      (nativePositiveFiniteGradingExponential k L ℒ hzero c hbound D x p) =
    IsNilpotent.exp (derivationAffineAdjointEnd k L D x)
      (nativeDerivationExtensionCoordinates k L D p) := by
  unfold nativePositiveFiniteGradingExponential
  rw [nativeDerivationExtensionExponential_coordinates,
    nativeDerivationExtensionAdjointCoordinateEnd_eq_affine]

/-- The true affine Lie morphism carries commuting vectors to commuting operators. -/
theorem derivationAffineAdjointEnd_commute
    (D : LieDerivation k L L) (x y : L) (hxy : ⁅x, y⁆ = 0) :
    Commute (derivationAffineAdjointEnd k L D x) (derivationAffineAdjointEnd k L D y) := by
  have h := (derivationAffineAdjoint k L D).map_lie x y
  rw [hxy, map_zero, LieRing.of_associative_ring_bracket] at h
  exact sub_eq_zero.mp h.symm

/-- Native finite exponentiation preserves actual commutation. -/
theorem nativePositiveFiniteExponential_commute
    (D : LieDerivation k L L) (x y : L) (hxy : ⁅x, y⁆ = 0) :
    Commute (nativePositiveFiniteGradingExponential k L ℒ hzero c hbound D x)
      (nativePositiveFiniteGradingExponential k L ℒ hzero c hbound D y) := by
  let a := derivationAffineAdjointEnd k L D x
  let b := derivationAffineAdjointEnd k L D y
  have hab : Commute a b := derivationAffineAdjointEnd_commute k L D x y hxy
  have ha : IsNilpotent a := derivationAffineAdjointEnd_isNilpotent_of_positive_finite_grading
    k L ℒ hzero c hbound D x
  have hb : IsNilpotent b := derivationAffineAdjointEnd_isNilpotent_of_positive_finite_grading
    k L ℒ hzero c hbound D y
  have hex : IsNilpotent.exp a * IsNilpotent.exp b = IsNilpotent.exp b * IsNilpotent.exp a := by
    calc
      IsNilpotent.exp a * IsNilpotent.exp b = IsNilpotent.exp (a + b) :=
        (IsNilpotent.exp_add_of_commute hab ha hb).symm
      _ = IsNilpotent.exp (b + a) := congrArg IsNilpotent.exp (add_comm a b)
      _ = IsNilpotent.exp b * IsNilpotent.exp a :=
        IsNilpotent.exp_add_of_commute hab.symm hb ha
  apply LieEquiv.ext
  intro p
  apply (nativeDerivationExtensionCoordinates k L D).injective
  change nativeDerivationExtensionCoordinates k L D
      (nativePositiveFiniteGradingExponential k L ℒ hzero c hbound D x
        (nativePositiveFiniteGradingExponential k L ℒ hzero c hbound D y p)) =
    nativeDerivationExtensionCoordinates k L D
      (nativePositiveFiniteGradingExponential k L ℒ hzero c hbound D y
        (nativePositiveFiniteGradingExponential k L ℒ hzero c hbound D x p))
  rw [nativePositiveFiniteExponential_affine_coordinates,
    nativePositiveFiniteExponential_affine_coordinates,
    nativePositiveFiniteExponential_affine_coordinates,
    nativePositiveFiniteExponential_affine_coordinates]
  exact DFunLike.congr_fun hex (nativeDerivationExtensionCoordinates k L D p)

variable (hAb : ∀ x ∈ nativeGradedTail k L ℒ 2,
  ∀ y ∈ nativeGradedTail k L ℒ 2, ⁅x, y⁆ = 0)
include hAb in
/-- The actual kernel of the actual axis character is abelian. -/
theorem nativeEulerAxisCharacter_kernel_commute
    (T S : nativeEulerExponentialSubgroup k L ℒ hzero c hbound)
    (hT : T ∈ (nativeEulerAxisAbelianCharacter k L ℒ hzero c hbound).ker)
    (hS : S ∈ (nativeEulerAxisAbelianCharacter k L ℒ hzero c hbound).ker) : Commute T S := by
  obtain ⟨x, hx⟩ := T.property
  obtain ⟨y, hy⟩ := S.property
  have hxTail := (nativeEulerAxisAbelianCharacter_eq_one_iff k L ℒ hzero c hbound T x hx).mp hT
  have hyTail := (nativeEulerAxisAbelianCharacter_eq_one_iff k L ℒ hzero c hbound S y hy).mp hS
  apply Subtype.ext
  change T.val * S.val = S.val * T.val
  rw [← hx, ← hy]
  exact nativePositiveFiniteExponential_commute k L ℒ hzero c hbound
    (nativeEulerDerivation k L ℒ) x y (hAb x hxTail y hyTail)

include hAb in
/-- The original derived series of the actual native exponential group
vanishes in degree two, derived from its actual abelian character kernel. -/
theorem nativeEulerExponentialGroup_secondDerived_eq_bot :
    derivedSeries (nativeEulerExponentialSubgroup k L ℒ hzero c hbound) 2 = ⊥ := by
  let H := nativeEulerExponentialSubgroup k L ℒ hzero c hbound
  let sigma := nativeEulerAxisAbelianCharacter k L ℒ hzero c hbound
  have hD : derivedSeries H 1 ≤ sigma.ker := by
    change ⁅(⊤ : Subgroup H), ⊤⁆ ≤ sigma.ker
    apply Subgroup.commutator_le.mpr
    intro T hT S hS
    change sigma ⁅T, S⁆ = 1
    rw [map_commutatorElement]
    exact (Commute.all _ _).commutator_eq
  apply bot_unique
  change ⁅derivedSeries H 1, derivedSeries H 1⁆ ≤ ⊥
  apply Subgroup.commutator_le.mpr
  intro T hT S hS
  change ⁅T, S⁆ = 1
  exact (nativeEulerAxisCharacter_kernel_commute k L ℒ hzero c hbound hAb T S
    (hD hT) (hD hS)).commutator_eq

end ChenRanks.LieComparison
