import ChenRanks.LieEulerExponentialAxis
import ChenRanks.LieEulerFixedAxisAutomorphism
import ChenRanks.LiePositiveNativeExponential

/-!
# Classification of actual positive automorphisms of the actual Euler extension

The input is an actual native Lie automorphism inducing the identity on
the scalar quotient and raising each original homogeneous vector by one
tail. These conditions describe the automorphism being classified; no
exponential representation, inverse, or classification is supplied.
The actual axis-displacement inverse constructs its exponent. The genuine
native inverse exponential and fixed-axis rigidity prove equality.

An application to actual parallel transport must separately construct
the grading and prove these two actual positivity conditions. This file
does not assume or assert such a monodromy application or formality.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]

/-- Negating the original vector negates its actual native adjoint. -/
theorem nativeDerivationExtensionAdjoint_neg
    (D : LieDerivation k L L) (x : L) :
    nativeDerivationExtensionAdjoint k L D (-x) =
      -nativeDerivationExtensionAdjoint k L D x := by
  apply LieDerivation.ext
  intro p
  apply (nativeDerivationExtensionCoordinates k L D).injective
  calc
    nativeDerivationExtensionCoordinates k L D
        (nativeDerivationExtensionAdjoint k L D (-x) p) =
        (0, p.right • D (-x) + ⁅-x, p.left⁆) :=
      nativeDerivationExtensionAdjoint_coordinates k L D (-x) p
    _ = -(0, p.right • D x + ⁅x, p.left⁆) := by
      apply Prod.ext
      · change (0 : k) = -(0 : k)
        exact neg_zero.symm
      · change p.right • D (-x) + ⁅-x, p.left⁆ = -(p.right • D x + ⁅x, p.left⁆)
        rw [map_neg, smul_neg, neg_lie, neg_add]
    _ = -(nativeDerivationExtensionCoordinates k L D
        (nativeDerivationExtensionAdjoint k L D x p)) :=
      congrArg Neg.neg (nativeDerivationExtensionAdjoint_coordinates k L D x p).symm
    _ = nativeDerivationExtensionCoordinates k L D
        ((-nativeDerivationExtensionAdjoint k L D x) p) := by
      exact ((nativeDerivationExtensionCoordinates k L D).map_neg
        (nativeDerivationExtensionAdjoint k L D x p)).symm

variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]

/-- The genuine inverse automorphism is the genuine native exponential
of the negative original vector. -/
theorem nativePositiveFiniteGradingExponential_neg_eq_symm
    (hzero : ℒ 0 = ⊥) (c : ℕ) (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥)
    (D : LieDerivation k L L) (x : L) :
    nativePositiveFiniteGradingExponential k L ℒ hzero c hbound D (-x) =
      (nativePositiveFiniteGradingExponential k L ℒ hzero c hbound D x).symm := by
  apply LieEquiv.ext
  intro p
  change IsNilpotent.exp (nativeDerivationExtensionAdjoint k L D (-x)).toLinearMap p =
    IsNilpotent.exp (-(nativeDerivationExtensionAdjoint k L D x).toLinearMap) p
  rw [nativeDerivationExtensionAdjoint_neg]
  rfl

/-- The genuine Euler bracket forces every homogeneous original image
to have zero scalar coordinate, even before any positivity is imposed. -/
theorem nativeEulerAutomorphismOriginal_fst_eq_zero
    (hzero : ℒ 0 = ⊥)
    (T : NativeDerivationExtension k L (nativeEulerDerivation k L ℒ) ≃ₗ⁅k⁆
      NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
    (n : ℕ) (w : L) (hw : w ∈ ℒ n) :
    (nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ)
      (T (nativeDerivationExtensionOriginal k L (nativeEulerDerivation k L ℒ) w))).1 = 0 := by
  by_cases hn : n = 0
  · subst n
    have hwzero : w = 0 := by rw [hzero] at hw; exact hw
    rw [hwzero]
    change ((nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ))
      (T (0 : NativeDerivationExtension k L (nativeEulerDerivation k L ℒ)))).1 = 0
    rw [map_zero]
    rfl
  · let D := nativeEulerDerivation k L ℒ
    let e := nativeDerivationExtensionCoordinates k L D
    have hbracket : ⁅nativeDerivationExtensionAxis k L D,
        nativeDerivationExtensionOriginal k L D w⁆ =
        nativeDerivationExtensionOriginal k L D (-D w) := by
      apply e.injective
      rw [nativeDerivationExtensionAxis_bracket_original]
      rfl
    have hmap := congrArg (fun p => (e p).1)
      (T.map_lie (nativeDerivationExtensionAxis k L D)
        (nativeDerivationExtensionOriginal k L D w))
    rw [hbracket, nativeEulerDerivation_of_mem k L ℒ n w hw] at hmap
    simp only [map_neg, map_smul] at hmap
    change -((n : k) * (e (T (nativeDerivationExtensionOriginal k L D w))).1) =
      ⁅(T (nativeDerivationExtensionAxis k L D)).right,
        (T (nativeDerivationExtensionOriginal k L D w)).right⁆ at hmap
    have hright : ⁅(T (nativeDerivationExtensionAxis k L D)).right,
        (T (nativeDerivationExtensionOriginal k L D w)).right⁆ = (0 : k) := by
      simp [Ring.lie_def, mul_comm]
    rw [hright] at hmap
    exact (mul_eq_zero.mp (neg_eq_zero.mp hmap)).resolve_left (Nat.cast_ne_zero.mpr hn)

/-- The actual native exponential map is injective, detected by its
actual Euler-axis polynomial, whose inverse was genuinely constructed. -/
theorem nativeEulerPositiveFiniteGradingExponential_injective
    (hzero : ℒ 0 = ⊥) (c : ℕ) (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥) :
    Function.Injective (nativePositiveFiniteGradingExponential k L ℒ hzero c hbound
      (nativeEulerDerivation k L ℒ)) := by
  intro x y hxy
  apply nativeEulerAxisDisplacement_injective k L ℒ hzero c hbound
  have h := congrArg (fun T =>
    (nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ)
      (T (nativeDerivationExtensionAxis k L (nativeEulerDerivation k L ℒ)))).2) hxy
  simpa only [nativePositiveFiniteGradingExponential_axis_displacement] using h

/-- Every actual positive automorphism has a unique actual native
exponent. The proof constructs it from its actual axis displacement. -/
theorem existsUnique_nativeEulerExponential_of_actual_positive_automorphism
    (hzero : ℒ 0 = ⊥) (c : ℕ) (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥)
    (T : NativeDerivationExtension k L (nativeEulerDerivation k L ℒ) ≃ₗ⁅k⁆
      NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
    (hscalar : (nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ)
      (T (nativeDerivationExtensionAxis k L (nativeEulerDerivation k L ℒ)))).1 = 1)
    (hraise : ∀ (n : ℕ) (w : L), w ∈ ℒ n →
      (nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ)
        (T (nativeDerivationExtensionOriginal k L (nativeEulerDerivation k L ℒ) w))).2 - w ∈
          nativeGradedTail k L ℒ (n + 1)) :
    ∃! x : L, nativePositiveFiniteGradingExponential k L ℒ hzero c hbound
      (nativeEulerDerivation k L ℒ) x = T := by
  let D := nativeEulerDerivation k L ℒ
  let e := nativeDerivationExtensionCoordinates k L D
  let v := (e (T (nativeDerivationExtensionAxis k L D))).2
  let x := nativeEulerAxisInverseStage k L ℒ c v c
  let E := nativePositiveFiniteGradingExponential k L ℒ hzero c hbound D x
  have hEaxis : E (nativeDerivationExtensionAxis k L D) =
      T (nativeDerivationExtensionAxis k L D) := by
    apply e.injective
    apply Prod.ext
    · rw [nativePositiveFiniteGradingExponential_coordinates_fst]
      exact hscalar.symm
    · rw [nativePositiveFiniteGradingExponential_axis_displacement]
      exact nativeEulerAxisDisplacement_inverseStage k L ℒ hzero c hbound v
  let S := T.trans E.symm
  have hSaxis : S (nativeDerivationExtensionAxis k L D) =
      nativeDerivationExtensionAxis k L D := by
    change E.symm (T (nativeDerivationExtensionAxis k L D)) = _
    rw [← hEaxis]
    exact E.symm_apply_apply _
  have hSraise (n : ℕ) (w : L) (hw : w ∈ ℒ n) :
      (e (S (nativeDerivationExtensionOriginal k L D w))).2 - w ∈
        nativeGradedTail k L ℒ (n + 1) := by
    let z := (e (T (nativeDerivationExtensionOriginal k L D w))).2
    have hTfirst := nativeEulerAutomorphismOriginal_fst_eq_zero k L ℒ hzero T n w hw
    have hToriginal : T (nativeDerivationExtensionOriginal k L D w) =
        nativeDerivationExtensionOriginal k L D z := by
      apply e.injective
      apply Prod.ext
      · exact hTfirst
      · rfl
    have hwTail := mem_nativeGradedTail_of_mem k L ℒ n n w le_rfl hw
    have hzTail : z ∈ nativeGradedTail k L ℒ n := by
      have hd := nativeGradedTail_antitone k L ℒ n (n + 1) (Nat.le_succ n)
        (hraise n w hw)
      convert (nativeGradedTail k L ℒ n).add_mem hd hwTail using 1 <;> abel
    have hEr := nativePositiveFiniteGradingExponential_original_snd_sub_mem
      k L ℒ hzero c hbound D (-x) z n hzTail
    rw [nativePositiveFiniteGradingExponential_neg_eq_symm] at hEr
    have h := (nativeGradedTail k L ℒ (n + 1)).add_mem hEr (hraise n w hw)
    change (e (E.symm (T (nativeDerivationExtensionOriginal k L D w)))).2 - w ∈ _
    rw [hToriginal]
    convert h using 1 <;> abel
  have hSid := nativeEulerPositiveAutomorphism_eq_refl_of_fixed_axis
    k L ℒ hzero S hSaxis hSraise
  have hET : E = T := by
    apply LieEquiv.ext
    intro p
    have h := congrArg (fun Q => Q p) hSid
    change E.symm (T p) = p at h
    calc
      E p = E (E.symm (T p)) := congrArg E h.symm
      _ = T p := E.apply_symm_apply _
  refine ⟨x, hET, ?_⟩
  intro y hy
  apply nativeEulerPositiveFiniteGradingExponential_injective k L ℒ hzero c hbound
  exact hy.trans hET.symm

end ChenRanks.LieComparison
