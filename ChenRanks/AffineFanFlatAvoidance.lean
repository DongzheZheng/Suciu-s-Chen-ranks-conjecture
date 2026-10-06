import ChenRanks.FiniteAffineSubspaceAvoidance

/-! The actual affine obstruction for a fan triangle to meet a flat.
An interior point meeting `a + W` forces the center into the explicit
bad affine translate `a + (W + span{x-a,y-a})`. The contrapositive is
proved from the original affine combination, with no transversality or
intersection-detector premise. -/

noncomputable section

namespace ChenRanks

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- A fan triangle whose center avoids its true bad affine translate
cannot meet the original flat at any point with nonzero center weight.
No sign or general-position assumption is needed for this algebraic fact. -/
theorem affineFan_nonzero_center_weight_avoids_flat
    (W : Submodule k V) (a x y z : V)
    (hz : z - a ∉ W ⊔ Submodule.span k ({x - a, y - a} : Set V))
    (r s t : k) (hr : r ≠ 0) (hsum : r + s + t = 1) :
    r • z + s • x + t • y - a ∉ W := by
  intro hflat
  let S := W ⊔ Submodule.span k ({x - a, y - a} : Set V)
  have hx : x - a ∈ S :=
    (show Submodule.span k ({x - a, y - a} : Set V) ≤ S from le_sup_right)
      (Submodule.subset_span (by simp))
  have hy : y - a ∈ S :=
    (show Submodule.span k ({x - a, y - a} : Set V) ≤ S from le_sup_right)
      (Submodule.subset_span (by simp))
  have hxy : s • (x - a) + t • (y - a) ∈ S :=
    S.add_mem (S.smul_mem s hx) (S.smul_mem t hy)
  have hscalar : r • a + s • a + t • a = a := by
    rw [← add_smul, ← add_smul, hsum, one_smul]
  have hidentity : r • (z - a) + (s • (x - a) + t • (y - a)) =
      r • z + s • x + t • y - a := by
    rw [smul_sub, smul_sub, smul_sub]
    calc
      r • z - r • a + (s • x - s • a + (t • y - t • a)) =
          (r • z + s • x + t • y) - (r • a + s • a + t • a) := by abel
      _ = _ := by rw [hscalar]
  have htotal : r • (z - a) + (s • (x - a) + t • (y - a)) ∈ S := by
    rw [hidentity]
    exact (show W ≤ S from le_sup_left) hflat
  have hmul : r • (z - a) ∈ S := by
    have h := S.sub_mem htotal hxy
    simpa only [add_sub_cancel_right] using h
  have hcenter := S.smul_mem r⁻¹ hmul
  apply hz
  simpa only [smul_smul, inv_mul_cancel₀ hr, one_smul] using hcenter

end ChenRanks
