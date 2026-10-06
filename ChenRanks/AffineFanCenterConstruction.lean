import ChenRanks.AffineFanFlatAvoidance
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Actual simultaneous fan centers for finite affine-flat families.
The strict dimension inequality proves each original bad translate is
proper; the original center is then constructed by the proved finite
avoidance theorem. This layer does not assert that arrangement pair
flats satisfy the inequality: that is a separate actual-normal calculation. -/

noncomputable section

namespace ChenRanks

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V]

/-- Adding the two actual edge directions leaves a proper subspace
when the original affine flat has real codimension at least three. -/
theorem affineFan_badSubmodule_ne_top (W : Submodule k V) (a x y : V)
    (hdim : Module.finrank k W + 2 < Module.finrank k V) :
    W ⊔ Submodule.span k ({x - a, y - a} : Set V) ≠ ⊤ := by
  classical
  have hspan : Module.finrank k
      (Submodule.span k ({x - a, y - a} : Set V)) ≤ 2 := by
    have h := finrank_span_finset_le_card (R := k)
      ({x - a, y - a} : Finset V)
    have hcard : ({x - a, y - a} : Finset V).card ≤ 2 := by
      by_cases hxy : x - a = y - a <;> simp [hxy]
    have h' : Module.finrank k
        (Submodule.span k ({x - a, y - a} : Set V)) ≤
          ({x - a, y - a} : Finset V).card := by
      simpa only [Finset.coe_pair] using h
    exact h'.trans hcard
  have hbound := Submodule.finrank_add_le_finrank_add_finrank W
    (Submodule.span k ({x - a, y - a} : Set V))
  intro htop
  rw [htop, _root_.finrank_top] at hbound
  omega

variable [Infinite k] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- One genuinely constructed original point simultaneously avoids
all original affine flats on every fan triangle interior. Empty flat
and edge families are allowed. The only dimension input describes the
original flats; no good-center or transversality premise is supplied. -/
theorem exists_actual_affine_fan_center (W : ι → Submodule k V) (a : ι → V)
    (x y : κ → V) (hdim : ∀ i, Module.finrank k (W i) + 2 < Module.finrank k V) :
    ∃ z : V, ∀ (i : ι) (j : κ) (r s t : k), r ≠ 0 → r + s + t = 1 →
      r • z + s • x j + t • y j - a i ∉ W i := by
  let S : ι × κ → Submodule k V := fun p =>
    W p.1 ⊔ Submodule.span k ({x p.2 - a p.1, y p.2 - a p.1} : Set V)
  obtain ⟨z, hz⟩ := exists_point_avoiding_finite_affine_subspaces S
    (fun p => a p.1)
    (fun p => affineFan_badSubmodule_ne_top (W p.1) (a p.1)
      (x p.2) (y p.2) (hdim p.1))
  refine ⟨z, ?_⟩
  intro i j r s t hr hsum
  exact affineFan_nonzero_center_weight_avoids_flat (W i) (a i) (x j) (y j) z
    (hz (i, j)) r s t hr hsum

end ChenRanks
