import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

/-!
# Joint commutators of the native group lower-central terms

The general normal-subgroup form of the Three Subgroups Lemma is proved
inside the actual group quotient, using the native Hall--Witt consequence.
The joint bound then follows by native lower-central recursion. No group
ring, augmentation detection, rational injection, graded Lie structure,
or formality premise is used.
-/

open scoped commutatorElement

namespace ChenRanks

variable {G : Type*} [Group G]

/-- The native Hall--Witt consequence applied in the actual quotient by
`N`, with its genuine quotient map and kernel. -/
theorem groupThreeSubgroups_le_normal (H₁ H₂ H₃ N : Subgroup G) [N.Normal]
    (h₁ : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N) (h₂ : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) :
    ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hqker : q.ker = N := QuotientGroup.ker_mk' N
  have hmap₁ : (⁅⁅H₂, H₃⁆, H₁⁆).map q = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (by rw [hqker]; exact h₁)
  have hmap₂ : (⁅⁅H₃, H₁⁆, H₂⁆).map q = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (by rw [hqker]; exact h₂)
  have hrotate₁ : ⁅⁅H₂.map q, H₃.map q⁆, H₁.map q⁆ = ⊥ := by
    simpa only [Subgroup.map_commutator] using hmap₁
  have hrotate₂ : ⁅⁅H₃.map q, H₁.map q⁆, H₂.map q⁆ = ⊥ := by
    simpa only [Subgroup.map_commutator] using hmap₂
  have hrotate := Subgroup.commutator_commutator_eq_bot_of_rotate hrotate₁ hrotate₂
  have hmap : (⁅⁅H₁, H₂⁆, H₃⁆).map q = ⊥ := by
    simpa only [Subgroup.map_commutator] using hrotate
  have hle := (Subgroup.map_eq_bot_iff (⁅⁅H₁, H₂⁆, H₃⁆)).mp hmap
  rw [hqker] at hle
  exact hle

/-- Mathlib's native term `m` is ordinary Gamma_(m+1). Thus the correct
joint bound has the native index `m+n+1`, including `m=0` or `n=0`. -/
theorem group_lowerCentralSeries_commutator_le (m n : ℕ) :
    ⁅lowerCentralSeries G m, lowerCentralSeries G n⁆ ≤
      lowerCentralSeries G (m + n + 1) := by
  induction m generalizing n with
  | zero =>
    rw [lowerCentralSeries_zero, Subgroup.commutator_comm]
    change lowerCentralSeries G (n + 1) ≤ lowerCentralSeries G (0 + n + 1)
    simp only [Nat.zero_add]
    exact le_rfl
  | succ m ih =>
    change ⁅⁅lowerCentralSeries G m, (⊤ : Subgroup G)⁆, lowerCentralSeries G n⁆ ≤
      lowerCentralSeries G ((m + 1) + n + 1)
    apply groupThreeSubgroups_le_normal (lowerCentralSeries G m)
      (⊤ : Subgroup G) (lowerCentralSeries G n)
      (lowerCentralSeries G ((m + 1) + n + 1))
    · rw [Subgroup.commutator_comm (⊤ : Subgroup G) (lowerCentralSeries G n)]
      change ⁅lowerCentralSeries G (n + 1), lowerCentralSeries G m⁆ ≤ _
      rw [Subgroup.commutator_comm]
      have h := ih (n + 1)
      simpa only [show m + (n + 1) + 1 = (m + 1) + n + 1 by omega] using h
    · have hinner : ⁅lowerCentralSeries G n, lowerCentralSeries G m⁆ ≤
          lowerCentralSeries G (m + n + 1) := by
        rw [Subgroup.commutator_comm]
        exact ih n
      have h := Subgroup.commutator_mono hinner
        (show (⊤ : Subgroup G) ≤ ⊤ from le_rfl)
      change ⁅⁅lowerCentralSeries G n, lowerCentralSeries G m⁆, (⊤ : Subgroup G)⁆ ≤
        lowerCentralSeries G ((m + n + 1) + 1) at h
      simpa only [show (m + n + 1) + 1 = (m + 1) + n + 1 by omega] using h

/-- The same genuinely joint bound applied to original group elements.
This is the representative-level input for the successive quotients. -/
theorem group_commutator_mem_lowerCentralSeries (m n : ℕ) (g h : G)
    (hg : g ∈ lowerCentralSeries G m) (hh : h ∈ lowerCentralSeries G n) :
    ⁅g, h⁆ ∈ lowerCentralSeries G (m + n + 1) :=
  group_lowerCentralSeries_commutator_le m n
    (Subgroup.commutator_mem_commutator hg hh)

end ChenRanks
