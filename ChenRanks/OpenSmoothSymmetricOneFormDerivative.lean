import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-! Native exterior differentiation of a one-form with a symmetric derivative.

This is the actual two-term alternating calculation on the original
continuous-linear-map object. Its hypotheses are derivative data;
the arrangement application supplies them from genuine inverse calculus.
-/

noncomputable section

namespace ChenRanks.OpenSmoothForms

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem extDeriv_oneForm_eq_zero_of_symmetric_derivative
    (ω : E → E →L[ℝ] F) (D : E →L[ℝ] E →L[ℝ] F) (x : E)
    (hω : HasFDerivAt ω D x) (hD : ∀ u v, D u v = D v u) :
    extDeriv (fun y => ContinuousAlternatingMap.ofSubsingleton ℝ E F
      (0 : Fin 1) (ω y)) x = 0 := by
  let e := ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ)
    (E := E) (F := F) (0 : Fin 1)
  let eL : (E →L[ℝ] F) →L[ℝ] (E [⋀^Fin 1]→L[ℝ] F) :=
    e.toContinuousLinearEquiv.toContinuousLinearMap
  have h : HasFDerivAt (fun y => eL (ω y)) (eL.comp D) x :=
    eL.hasFDerivAt.comp x hω
  change ContinuousAlternatingMap.alternatizeUncurryFin
    (fderiv ℝ (fun y => eL (ω y)) x) = 0
  rw [h.fderiv]
  ext v
  have hremove0 : (0 : Fin 2).removeNth v (0 : Fin 1) = v 1 := rfl
  have hremove1 : (1 : Fin 2).removeNth v (0 : Fin 1) = v 0 := rfl
  have he (f : E →L[ℝ] F) (w : Fin 1 → E) : e f w = f (w 0) := rfl
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  change (∑ i : Fin 2, (-1 : ℤ) ^ i.val •
    (e (D (v i))) (i.removeNth v)) = 0
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_zsmul]
  simp only [he, hremove0, hremove1]
  rw [hD]
  exact add_neg_cancel _

end ChenRanks.OpenSmoothForms
