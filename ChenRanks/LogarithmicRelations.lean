import ChenRanks.LogarithmicDifferentials
import ChenRanks.ExteriorSeparation

/-!
# Actual logarithmic quadratic relations

The paper's lemma on the logarithmic kernel first proves that the
Orlik–Solomon boundaries of codimension-two triples vanish as rational
two-forms. The identity below is that calculation for three actual
nonzero functions whose third function is a constant linear combination
of the first two. The exterior product is over the actual function field.
-/

noncomputable section

namespace ChenRanks

section ExteriorIdentities

variable {k E : Type*} [Field k] [AddCommGroup E] [Module k E]

theorem wedge_smul_left (c : k) (x y : E) :
    exteriorWedge (k := k) (c • x) y = c • exteriorWedge (k := k) x y := by
  apply Subtype.ext
  simp

theorem wedge_smul_right (c : k) (x y : E) :
    exteriorWedge (k := k) x (c • y) = c • exteriorWedge (k := k) x y := by
  apply Subtype.ext
  simp

theorem wedge_add_right (x y z : E) :
    exteriorWedge (k := k) x (y + z) =
      exteriorWedge (k := k) x y + exteriorWedge (k := k) x z := by
  apply Subtype.ext
  simp [mul_add]

theorem wedge_self (x : E) : exteriorWedge (k := k) x x = 0 := by
  apply Subtype.ext
  simp

theorem wedge_swap (x y : E) :
    exteriorWedge (k := k) x y = -exteriorWedge (k := k) y x := by
  apply Subtype.ext
  simpa using eq_neg_iff_add_eq_zero.mpr (ExteriorAlgebra.ι_add_mul_swap x y)

end ExteriorIdentities

variable {C F : Type*} [Field C] [Field F] [Algebra C F]

/-- The actual rational realization of an Orlik–Solomon triple boundary. -/
theorem logarithmic_triple_relation (u v w : Fˣ) (a b : C)
    (hw : (w : F) = algebraMap C F a * (u : F) + algebraMap C F b * (v : F)) :
    exteriorWedge (k := F) (logarithmicDifferential C F v) (logarithmicDifferential C F w) -
      exteriorWedge (k := F) (logarithmicDifferential C F u) (logarithmicDifferential C F w) +
      exteriorWedge (k := F) (logarithmicDifferential C F u) (logarithmicDifferential C F v) = 0 := by
  have hD : KaehlerDifferential.D C F (w : F) =
      algebraMap C F a • KaehlerDifferential.D C F (u : F) +
      algebraMap C F b • KaehlerDifferential.D C F (v : F) := by
    rw [hw]
    simp [Derivation.leibniz]
  have hc : -((w : F)⁻¹ * (algebraMap C F a * (v : F)⁻¹)) -
      (w : F)⁻¹ * (algebraMap C F b * (u : F)⁻¹) + (v : F)⁻¹ * (u : F)⁻¹ = 0 := by
    field_simp [u.ne_zero, v.ne_zero, w.ne_zero]
    rw [hw]
    ring
  simp only [logarithmicDifferential, hD, wedge_smul_left, wedge_smul_right,
    wedge_add_right, wedge_self, smul_zero, add_zero, zero_add, smul_smul]
  rw [wedge_swap (KaehlerDifferential.D C F (v : F))
    (KaehlerDifferential.D C F (u : F))]
  simp only [smul_neg]
  rw [← neg_smul, ← sub_smul, ← add_smul, hc, zero_smul]

end ChenRanks
