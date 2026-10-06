import ChenRanks.NativeEulerExponentialGroup

/-! The actual axis displacement of the genuine Euler exponential group
has a genuine additive character modulo the original degree-two tail.
Its kernel is detected by the actual exponent lying in that same tail.
This is an intermediate structural construction for the later proof that
the actual finite metabelian model gives a metabelian monodromy target.
No exponent identity, character, or kernel description is supplied.
-/
noncomputable section
namespace ChenRanks.LieComparison
variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]
variable (hzero : ℒ 0 = ⊥) (c : ℕ) (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥)

include hzero in
/-- The actual nonlinear axis terms start in the original degree-two tail. -/
theorem nativeEulerAxisDisplacement_sub_euler_mem_two (x : L) :
    nativeEulerAxisDisplacement k L ℒ c x - nativeEulerDerivation k L ℒ x ∈
      nativeGradedTail k L ℒ 2 := by
  rw [nativeEulerAxisDisplacement_eq, add_sub_cancel_right]
  apply Submodule.sum_mem
  intro m hm
  apply Submodule.smul_mem
  exact nativeGradedTail_antitone k L ℒ 2 (m + 2) (by omega)
    (nativeEulerAxisIterate_mem_tail k L ℒ hzero x (m + 1))

include hzero in
/-- The true axis displacement detects the original degree-two tail. -/
theorem nativeEulerAxisDisplacement_mem_two_iff (x : L) :
    nativeEulerAxisDisplacement k L ℒ c x ∈ nativeGradedTail k L ℒ 2 ↔
      x ∈ nativeGradedTail k L ℒ 2 := by
  have hd := nativeEulerAxisDisplacement_sub_euler_mem_two k L ℒ hzero c x
  constructor
  · intro hx
    have hD : nativeEulerDerivation k L ℒ x ∈ nativeGradedTail k L ℒ 2 := by
      convert (nativeGradedTail k L ℒ 2).sub_mem hx hd using 1 <;> abel
    have hi := nativeEulerInverse_mem_tail k L ℒ 2 _ hD
    have he := DFunLike.congr_fun (nativeEulerInverse_comp_euler k L ℒ hzero) x
    change nativeEulerInverse k L ℒ (nativeEulerDerivation k L ℒ x) = x at he
    rw [he] at hi
    exact hi
  · intro hx
    have hD := nativeEulerDerivation_mem_tail k L ℒ 2 x hx
    convert (nativeGradedTail k L ℒ 2).add_mem hd hD using 1 <;> abel

/-- Genuine axis displacement in the genuine original quotient. -/
def nativeEulerAxisAbelianCharacter :
    (nativeEulerExponentialSubgroup k L ℒ hzero c hbound) →*
      Multiplicative (L ⧸ nativeGradedTail k L ℒ 2) where
  toFun T := Multiplicative.ofAdd ((nativeGradedTail k L ℒ 2).mkQ
    ((nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ))
      ((T : NativeLieAutomorphismGroup k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ)))
        (nativeDerivationExtensionAxis k L (nativeEulerDerivation k L ℒ)))).2)
  map_one' := by
    change (nativeGradedTail k L ℒ 2).mkQ 0 = 0
    exact map_zero _
  map_mul' T S := by
    let D := nativeEulerDerivation k L ℒ
    let e := nativeDerivationExtensionCoordinates k L D
    let v := (e ((S : NativeLieAutomorphismGroup k (NativeDerivationExtension k L D))
      (nativeDerivationExtensionAxis k L D))).2
    obtain ⟨x, hx⟩ := T.property
    obtain ⟨y, hy⟩ := S.property
    have hSfirst : (e ((S : NativeLieAutomorphismGroup k (NativeDerivationExtension k L D))
        (nativeDerivationExtensionAxis k L D))).1 = 1 := by
      rw [← hy, nativePositiveFiniteGradingExponential_coordinates_fst]
      rfl
    have hSaxis : (S : NativeLieAutomorphismGroup k (NativeDerivationExtension k L D))
        (nativeDerivationExtensionAxis k L D) =
      nativeDerivationExtensionAxis k L D + nativeDerivationExtensionOriginal k L D v := by
      apply e.injective
      apply Prod.ext
      · change (e ((S : NativeLieAutomorphismGroup k (NativeDerivationExtension k L D))
          (nativeDerivationExtensionAxis k L D))).1 = 1 + 0
        simpa only [add_zero] using hSfirst
      · change v = 0 + v
        exact (zero_add v).symm
    have hvTail : v ∈ nativeGradedTail k L ℒ 1 := by
      rw [nativeGradedTail_one_eq_top k L ℒ hzero]
      trivial
    have hr : (e ((T : NativeLieAutomorphismGroup k (NativeDerivationExtension k L D))
        (nativeDerivationExtensionOriginal k L D v))).2 - v ∈ nativeGradedTail k L ℒ 2 := by
      rw [← hx]
      exact nativePositiveFiniteGradingExponential_original_snd_sub_mem
        k L ℒ hzero c hbound D x v 1 hvTail
    have hq : (nativeGradedTail k L ℒ 2).mkQ
        ((e ((T : NativeLieAutomorphismGroup k (NativeDerivationExtension k L D))
          (nativeDerivationExtensionOriginal k L D v))).2) =
        (nativeGradedTail k L ℒ 2).mkQ v := by
      apply sub_eq_zero.mp
      rw [← map_sub]
      exact (Submodule.Quotient.mk_eq_zero (nativeGradedTail k L ℒ 2)).mpr hr
    change (nativeGradedTail k L ℒ 2).mkQ
      ((e ((T : NativeLieAutomorphismGroup k (NativeDerivationExtension k L D))
        ((S : NativeLieAutomorphismGroup k (NativeDerivationExtension k L D))
          (nativeDerivationExtensionAxis k L D)))).2) = _
    conv_lhs => rw [hSaxis, map_add, map_add]
    change (nativeGradedTail k L ℒ 2).mkQ
      ((e ((T : NativeLieAutomorphismGroup k (NativeDerivationExtension k L D))
        (nativeDerivationExtensionAxis k L D))).2 +
        (e ((T : NativeLieAutomorphismGroup k (NativeDerivationExtension k L D))
          (nativeDerivationExtensionOriginal k L D v))).2) = _
    rw [map_add, hq]
    rfl

/-- Actual kernel membership is exactly the original exponent's actual tail membership. -/
theorem nativeEulerAxisAbelianCharacter_eq_one_iff
    (T : nativeEulerExponentialSubgroup k L ℒ hzero c hbound)
    (x : L) (hx : nativePositiveFiniteGradingExponential k L ℒ hzero c hbound
      (nativeEulerDerivation k L ℒ) x = T.val) :
    nativeEulerAxisAbelianCharacter k L ℒ hzero c hbound T = 1 ↔
      x ∈ nativeGradedTail k L ℒ 2 := by
  change (nativeGradedTail k L ℒ 2).mkQ
    ((nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ))
      (T.val (nativeDerivationExtensionAxis k L (nativeEulerDerivation k L ℒ)))).2 = 0 ↔ _
  rw [← hx, nativePositiveFiniteGradingExponential_axis_displacement]
  exact (Submodule.Quotient.mk_eq_zero (nativeGradedTail k L ℒ 2)).trans
    (nativeEulerAxisDisplacement_mem_two_iff k L ℒ hzero c x)

end ChenRanks.LieComparison
