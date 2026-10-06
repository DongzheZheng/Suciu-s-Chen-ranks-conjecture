import ChenRanks.ArrangementObjects

/-!
# The actual arrangement localized at an original affine point

The labels are precisely the original hyperplanes containing the
original point. Translating that point to zero gives their actual
central arrangement. Distinctness is derived from the original affine
hyperplanes; no local model or incidence list is supplied.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The actual original hyperplanes containing the actual affine point. -/
abbrev PointLocalizedLabels (x : Fin d → ℂ) :=
  {H : ι // A.normal H x = A.offset H}

instance pointLocalizedLabels_fintype (x : Fin d → ℂ) :
    Fintype (A.PointLocalizedLabels x) := by
  classical
  unfold PointLocalizedLabels
  infer_instance

/-- The original incident hyperplanes, genuinely translated to zero. -/
def pointLocalizedArrangement (x : Fin d → ℂ) :
    AffineArrangement d (A.PointLocalizedLabels x) where
  normal H := A.normal H
  offset _ := 0
  normal_ne_zero H := A.normal_ne_zero H
  distinct := by
    intro H K hHK hsets
    have hv : H.val ≠ K.val := fun h => hHK (Subtype.ext h)
    apply A.distinct hv
    apply Set.ext
    intro y
    have he : A.normal H (y - x) = 0 ↔ A.normal K (y - x) = 0 :=
      Set.ext_iff.mp hsets (y - x)
    simpa only [map_sub, H.property, K.property, sub_eq_zero] using he

/-- Every actual translated hyperplane has actual zero offset. -/
theorem pointLocalizedArrangement_central (x : Fin d → ℂ)
    (H : A.PointLocalizedLabels x) :
    (A.pointLocalizedArrangement x).offset H = 0 := rfl

/-- Translating a genuine local-complement point preserves all actual incident equations. -/
theorem normal_translate_localized_complement (x : Fin d → ℂ)
    (y : (A.pointLocalizedArrangement x).Complement) (H : A.PointLocalizedLabels x) :
    A.normal H (x + y.val) ≠ A.offset H := by
  rw [map_add, H.property]
  intro h
  have hzero : A.normal H y.val = 0 :=
    add_left_cancel (h.trans (add_zero (A.offset H)).symm)
  exact y.property H hzero

end ChenRanks.AffineArrangement
