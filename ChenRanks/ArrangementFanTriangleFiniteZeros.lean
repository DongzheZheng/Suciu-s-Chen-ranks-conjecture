import ChenRanks.ArrangementTransverseFanCenter
import ChenRanks.RealFanTriangleFiniteZeros
import Mathlib.AlgebraicTopology.SingularSet

/-! Actual affine fan triangles in the original ambient space and
genuine finite puncture sets constructed from the original arrangement.
The actual equation comparison is proved from the original linear
functionals and barycentric sum. The final factory has no transversality
or finite-puncture hypothesis. -/

noncomputable section

open AlgebraicTopology

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The actual original ambient fan triangle, with vertex order
center, source, target. -/
def actualFanTriangleAmbient (x y z : Fin d → ℂ) :
    C(stdSimplex ℝ (Fin 3), Fin d → ℂ) where
  toFun p := ((p 0 : ℝ) : ℂ) • z + ((p 1 : ℝ) : ℂ) • x + ((p 2 : ℝ) : ℂ) • y
  continuous_toFun := by
    have hc (i : Fin 3) : Continuous (fun p : stdSimplex ℝ (Fin 3) =>
        ((p i : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_subtype_val)
    exact (((hc 0).smul continuous_const).add
      ((hc 1).smul continuous_const)).add ((hc 2).smul continuous_const)

/-- Actual equation evaluation on that actual triangle equals the
actual scalar triangle equation, including the original affine offset. -/
theorem actualFanTriangleAmbient_equation (H : ι) (x y z : Fin d → ℂ)
    (p : stdSimplex ℝ (Fin 3)) :
    A.normal H (actualFanTriangleAmbient x y z p) - A.offset H =
      realFanTriangleEquation (A.normal H x - A.offset H)
        (A.normal H y - A.offset H) (A.normal H z - A.offset H) p := by
  have hs := p.property.2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change p 0 + (p 1 + p 2) = 1 at hs
  have hsum : ((p 0 : ℝ) : ℂ) + ((p 1 : ℝ) : ℂ) + ((p 2 : ℝ) : ℂ) = 1 := by
    exact_mod_cast (show p 0 + p 1 + p 2 = 1 by linarith)
  change A.normal H (((p 0 : ℝ) : ℂ) • z +
      ((p 1 : ℝ) : ℂ) • x + ((p 2 : ℝ) : ℂ) • y) - A.offset H = _
  simp only [map_add, map_smul, smul_eq_mul, realFanTriangleEquation]
  change (p 0 : ℂ) * A.normal H z + (p 1 : ℂ) * A.normal H x +
      (p 2 : ℂ) * A.normal H y - A.offset H =
    (p 0 : ℂ) * (A.normal H z - A.offset H) +
      (p 1 : ℂ) * (A.normal H x - A.offset H) +
      (p 2 : ℂ) * (A.normal H y - A.offset H)
  linear_combination A.offset H * hsum

variable {κ : Type*} [Fintype κ]

/-- Every finite family of actual complement edges has a genuinely
constructed original complement center with finite actual triangle
puncture sets. Constant-edge equations are accounted for exactly. -/
theorem exists_actual_complement_fan_with_finite_punctures
    (x y : κ → A.Complement) :
    ∃ z : A.Complement, ∀ (H : ι) (j : κ),
      Set.Finite {p : stdSimplex ℝ (Fin 3) |
        A.normal H (actualFanTriangleAmbient (x j).val (y j).val z.val p) = A.offset H} := by
  obtain ⟨z, hlines, _hdoubles⟩ := A.exists_actual_transverse_complement_fan_center x y
  refine ⟨z, ?_⟩
  intro H j
  have hedge : (A.normal H z.val - A.offset H) - (A.normal H (x j).val - A.offset H) ∉
      Submodule.span ℝ
        ({(A.normal H (y j).val - A.offset H) - (A.normal H (x j).val - A.offset H)} : Set ℂ) := by
    have hleft : (A.normal H z.val - A.offset H) -
        (A.normal H (x j).val - A.offset H) = A.normal H z.val - A.normal H (x j).val := by ring
    have hright : (A.normal H (y j).val - A.offset H) -
        (A.normal H (x j).val - A.offset H) = A.normal H ((y j).val - (x j).val) := by
      rw [map_sub]
      ring
    rw [hleft, hright]
    exact (hlines H j).1
  have hfinite := realFanTriangleEquation_zeroSet_finite
    (A.normal H (x j).val - A.offset H) (A.normal H (y j).val - A.offset H)
    (A.normal H z.val - A.offset H) (sub_ne_zero.mpr ((x j).property H))
    hedge (hlines H j).2.1
  have heq : {p : stdSimplex ℝ (Fin 3) |
        A.normal H (actualFanTriangleAmbient (x j).val (y j).val z.val p) = A.offset H} =
      {p : stdSimplex ℝ (Fin 3) |
        realFanTriangleEquation (A.normal H (x j).val - A.offset H)
          (A.normal H (y j).val - A.offset H) (A.normal H z.val - A.offset H) p = 0} := by
    ext p
    constructor
    · intro hp
      have hzero := sub_eq_zero.mpr hp
      rwa [A.actualFanTriangleAmbient_equation] at hzero
    · intro hp
      apply sub_eq_zero.mp
      rwa [A.actualFanTriangleAmbient_equation]
  rw [heq]
  exact hfinite

end ChenRanks.AffineArrangement
