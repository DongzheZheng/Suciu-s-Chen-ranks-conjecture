import ChenRanks.NativeLieAutomorphismGroup
import ChenRanks.LieEulerPositiveAutomorphisms

/-! The actual native exponentials of the actual positive Euler extension
form a genuine subgroup of its native Lie automorphism group. Closure is
proved from the actual positive action and the proved axis classification;
no Baker--Campbell--Hausdorff formula or supplied exponential group law is
used. Application to geometric monodromy remains a separate construction.
-/
noncomputable section
namespace ChenRanks.LieComparison
variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]
variable (hzero : ℒ 0 = ⊥) (c : ℕ) (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥)

/-- The actual exponentials, with the original native composition law. -/
def nativeEulerExponentialSubgroup :
    Subgroup (NativeLieAutomorphismGroup k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))) where
  carrier := {T | ∃ x : L, nativePositiveFiniteGradingExponential k L ℒ hzero c hbound
    (nativeEulerDerivation k L ℒ) x = T}
  one_mem' := by
    obtain ⟨x, hx, _⟩ := existsUnique_nativeEulerExponential_of_actual_positive_automorphism
      k L ℒ hzero c hbound (1 : NativeLieAutomorphismGroup k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ)))
      (by rfl) (by
        intro n w hw
        change w - w ∈ nativeGradedTail k L ℒ (n + 1)
        rw [sub_self]
        exact Submodule.zero_mem _)
    exact ⟨x, hx⟩
  inv_mem' := by
    rintro T ⟨x, rfl⟩
    exact ⟨-x, nativePositiveFiniteGradingExponential_neg_eq_symm
      k L ℒ hzero c hbound (nativeEulerDerivation k L ℒ) x⟩
  mul_mem' := by
    rintro T S ⟨x, rfl⟩ ⟨y, rfl⟩
    let D := nativeEulerDerivation k L ℒ
    let e := nativeDerivationExtensionCoordinates k L D
    let E := nativePositiveFiniteGradingExponential k L ℒ hzero c hbound D x
    let F := nativePositiveFiniteGradingExponential k L ℒ hzero c hbound D y
    have hscalar : (e ((E * F) (nativeDerivationExtensionAxis k L D))).1 = 1 := by
      change (e (E (F (nativeDerivationExtensionAxis k L D)))).1 = 1
      rw [nativePositiveFiniteGradingExponential_coordinates_fst]
      change (e (F (nativeDerivationExtensionAxis k L D))).1 = 1
      rw [nativePositiveFiniteGradingExponential_coordinates_fst]
      rfl
    have hraise (n : ℕ) (w : L) (hw : w ∈ ℒ n) :
        (e ((E * F) (nativeDerivationExtensionOriginal k L D w))).2 - w ∈
          nativeGradedTail k L ℒ (n + 1) := by
      let z := (e (F (nativeDerivationExtensionOriginal k L D w))).2
      have hFfirst : (e (F (nativeDerivationExtensionOriginal k L D w))).1 = 0 := by
        rw [nativePositiveFiniteGradingExponential_coordinates_fst]
        rfl
      have hForiginal : F (nativeDerivationExtensionOriginal k L D w) =
          nativeDerivationExtensionOriginal k L D z := by
        apply e.injective
        apply Prod.ext
        · exact hFfirst
        · rfl
      have hwTail := mem_nativeGradedTail_of_mem k L ℒ n n w le_rfl hw
      have hFraise := nativePositiveFiniteGradingExponential_original_snd_sub_mem
        k L ℒ hzero c hbound D y w n hwTail
      have hzTail : z ∈ nativeGradedTail k L ℒ n := by
        have hd := nativeGradedTail_antitone k L ℒ n (n + 1) (Nat.le_succ n) hFraise
        convert (nativeGradedTail k L ℒ n).add_mem hd hwTail using 1 <;> abel
      have hEraise := nativePositiveFiniteGradingExponential_original_snd_sub_mem
        k L ℒ hzero c hbound D x z n hzTail
      have h := (nativeGradedTail k L ℒ (n + 1)).add_mem hEraise hFraise
      change (e (E (F (nativeDerivationExtensionOriginal k L D w)))).2 - w ∈ _
      rw [hForiginal]
      convert h using 1 <;> abel
    obtain ⟨z, hz, _⟩ := existsUnique_nativeEulerExponential_of_actual_positive_automorphism
      k L ℒ hzero c hbound (E * F) hscalar hraise
    exact ⟨z, hz⟩

@[simp] theorem mem_nativeEulerExponentialSubgroup
    (T : NativeLieAutomorphismGroup k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))) :
    T ∈ nativeEulerExponentialSubgroup k L ℒ hzero c hbound ↔
      ∃ x : L, nativePositiveFiniteGradingExponential k L ℒ hzero c hbound
        (nativeEulerDerivation k L ℒ) x = T := Iff.rfl

/-- The proved classifier supplies subgroup membership for an actual
native automorphism once its actual positivity has been established. -/
theorem nativeEulerExponentialSubgroup_mem_of_positive
    (T : NativeLieAutomorphismGroup k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ)))
    (hscalar : (nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ)
      (T (nativeDerivationExtensionAxis k L (nativeEulerDerivation k L ℒ)))).1 = 1)
    (hraise : ∀ (n : ℕ) (w : L), w ∈ ℒ n →
      (nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ)
        (T (nativeDerivationExtensionOriginal k L (nativeEulerDerivation k L ℒ) w))).2 - w ∈
          nativeGradedTail k L ℒ (n + 1)) :
    T ∈ nativeEulerExponentialSubgroup k L ℒ hzero c hbound := by
  obtain ⟨x, hx, _⟩ := existsUnique_nativeEulerExponential_of_actual_positive_automorphism
    k L ℒ hzero c hbound T hscalar hraise
  exact ⟨x, hx⟩

end ChenRanks.LieComparison
