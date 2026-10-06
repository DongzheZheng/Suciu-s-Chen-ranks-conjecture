import ChenRanks.CentralDeconeCoefficientCup

/-! Actual coordinates on the zero-sum coefficient hyperplane.
The genuine difference-vector inclusion has the original remaining
coefficients as its inverse. Thus it identifies the real decone
coefficient space with the actual radial kernel, with no assumed
resonance or dimension comparison. -/
noncomputable section
open scoped BigOperators
namespace ChenRanks.AffineArrangement
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
local instance centralDeconeCoefficientCoordinatesDecidableEq : DecidableEq ι := Classical.decEq ι
variable (i₀ : ι)

theorem actualCentralDeconeCoefficientInclusion_remaining
    (a : A.ActualCentralDeconeLabels i₀ → ℂ) (H : A.ActualCentralDeconeLabels i₀) :
    A.actualCentralDeconeCoefficientInclusion i₀ a H.val = a H := by
  change (∑ K : A.ActualCentralDeconeLabels i₀,
    a K • (Pi.single K.val (1 : ℂ) - Pi.single i₀ (1 : ℂ)) : ι → ℂ) H.val = a H
  rw [Finset.sum_apply]
  classical
  rw [Finset.sum_eq_single H]
  · simp [Pi.single_apply, H.property.symm]
  · intro K _hK hKH
    have hv : K.val ≠ H.val := fun he => hKH (Subtype.ext he)
    simp [Pi.single_apply, hv, H.property.symm]
  · simp

theorem actualCentralDeconeCoefficientInclusion_chosen
    (a : A.ActualCentralDeconeLabels i₀ → ℂ) :
    A.actualCentralDeconeCoefficientInclusion i₀ a i₀ = -(∑ H, a H) := by
  change (∑ K : A.ActualCentralDeconeLabels i₀,
    a K • (Pi.single K.val (1 : ℂ) - Pi.single i₀ (1 : ℂ)) : ι → ℂ) i₀ = -(∑ H, a H)
  rw [Finset.sum_apply]
  have ht (K : A.ActualCentralDeconeLabels i₀) :
      (a K • (Pi.single K.val (1 : ℂ) - Pi.single i₀ (1 : ℂ)) : ι → ℂ) i₀ = -a K := by
    simp [Pi.single_apply, K.property]
  simp only [ht, Finset.sum_neg_distrib]

/-- Genuine restriction is a left inverse; injectivity is proved on
original coordinates rather than inferred from a resonance assertion. -/
theorem actualCentralDeconeCoefficientInclusion_injective :
    Function.Injective (A.actualCentralDeconeCoefficientInclusion i₀) := by
  intro a b hab
  funext H
  have h := congrArg (fun f : ι → ℂ => f H.val) hab
  simpa only [A.actualCentralDeconeCoefficientInclusion_remaining i₀] using h

/-- Every actual zero-sum direction is genuinely reconstructed from
its remaining original coefficients. -/
theorem actualCentralDeconeCoefficientInclusion_reconstruct
    (a : ι → ℂ) (ha : A.actualCentralTotalCoefficient a = 0) :
    A.actualCentralDeconeCoefficientInclusion i₀ (fun H => a H.val) = a := by
  funext H
  by_cases hH : H = i₀
  · subst H
    rw [A.actualCentralDeconeCoefficientInclusion_chosen i₀]
    have hs : a i₀ + (∑ H : A.ActualCentralDeconeLabels i₀, a H.val) = 0 := by
      have he := Fintype.sum_eq_add_sum_subtype_ne a i₀
      change (∑ H, a H) = 0 at ha
      rw [ha] at he
      exact he.symm
    exact (eq_neg_of_add_eq_zero_left hs).symm
  · exact A.actualCentralDeconeCoefficientInclusion_remaining i₀
      (fun K => a K.val) ⟨H, hH⟩

/-- The actual radial hyperplane retains the original ambient
coefficient space and its genuine sum functional. -/
abbrev ActualCentralZeroSum := (A.actualCentralTotalCoefficient).ker

/-- The genuine decone coefficient equivalence onto the actual radial
kernel, proved by two true coordinate inverse identities. -/
def actualCentralDeconeZeroSumEquiv :
    (A.ActualCentralDeconeLabels i₀ → ℂ) ≃ₗ[ℂ] A.ActualCentralZeroSum where
  toFun a := ⟨A.actualCentralDeconeCoefficientInclusion i₀ a,
    A.actualCentralDeconeCoefficientInclusion_total_zero i₀ a⟩
  invFun a H := a.val H.val
  left_inv a := by
    funext H
    exact A.actualCentralDeconeCoefficientInclusion_remaining i₀ a H
  right_inv a := by
    apply Subtype.ext
    exact A.actualCentralDeconeCoefficientInclusion_reconstruct i₀ a.val a.property
  map_add' a b := by
    apply Subtype.ext
    exact (A.actualCentralDeconeCoefficientInclusion i₀).map_add a b
  map_smul' c a := by
    apply Subtype.ext
    exact (A.actualCentralDeconeCoefficientInclusion i₀).map_smul c a

end ChenRanks.AffineArrangement
