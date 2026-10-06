import ChenRanks.ActualArrangementRationalMaximalFamily

/-!
# Original and kernel-quotient rational maximal families

The actual kernel-quotient maximality equivalence gives an equivalence of
the genuine families which keeps every original subspace literally the
same. The dimension fibers are then genuinely equivalent, and cardinal
congruence compares the two intrinsic dimension counts. Neither an
irreducible-component count nor a topological Chen count is assumed.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

attribute [local irreducible] quadraticLogarithmicRealization logarithmicRealization

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The original subspace is unchanged under the true kernel-quotient
comparison of the actual maximal-isotropic families. -/
def rationalMaximalIsotropicKernelQuotientEquiv :
    Resonance.OriginalMaximalIsotropicFamily
      (Resonance.cupQuotient A.rationalQuadraticKernel) ≃
      A.RationalMaximalIsotropicFamily where
  toFun P := ⟨P.val,
    (A.rationalQuadraticKernel_cupQuotient_maximal_iff P.val).mp P.property.1,
    P.property.2⟩
  invFun P := ⟨P.val,
    (A.rationalQuadraticKernel_cupQuotient_maximal_iff P.val).mpr P.property.1,
    P.property.2⟩
  left_inv P := by apply Subtype.ext; rfl
  right_inv P := by apply Subtype.ext; rfl

@[simp] theorem rationalMaximalIsotropicKernelQuotientEquiv_val
    (P : Resonance.OriginalMaximalIsotropicFamily
      (Resonance.cupQuotient A.rationalQuadraticKernel)) :
    (A.rationalMaximalIsotropicKernelQuotientEquiv P).val = P.val := rfl

@[simp] theorem rationalMaximalIsotropicKernelQuotientEquiv_symm_val
    (P : A.RationalMaximalIsotropicFamily) :
    (A.rationalMaximalIsotropicKernelQuotientEquiv.symm P).val = P.val := rfl

/-- The actual dimension fibers are genuinely equivalent because the
comparison preserves the same original coefficient subspace. -/
def rationalMaximalIsotropicDimensionFiberEquiv (m : ℕ) :
    {P : Resonance.OriginalMaximalIsotropicFamily
      (Resonance.cupQuotient A.rationalQuadraticKernel) //
        Module.finrank ℂ P.val = m} ≃
      {P : A.RationalMaximalIsotropicFamily // Module.finrank ℂ P.val = m} where
  toFun P := ⟨A.rationalMaximalIsotropicKernelQuotientEquiv P.val, P.property⟩
  invFun P := ⟨A.rationalMaximalIsotropicKernelQuotientEquiv.symm P.val, P.property⟩
  left_inv P := by
    apply Subtype.ext
    exact A.rationalMaximalIsotropicKernelQuotientEquiv.left_inv P.val
  right_inv P := by
    apply Subtype.ext
    exact A.rationalMaximalIsotropicKernelQuotientEquiv.right_inv P.val

private theorem rationalQuotientRealization_all_maximal_separated :
    ∀ P : Submodule ℂ (ι → ℂ),
      IsMaximalIsotropic
        (relationWedge (Resonance.cupQuotient A.rationalQuadraticKernel)) P →
      2 ≤ Module.finrank ℂ P →
        mixedExterior P ⊓ LinearMap.ker (Resonance.cupQuotient A.rationalQuadraticKernel) =
          pureExterior P := by
  intro P hP hdim
  simpa only [Resonance.cupQuotient, Submodule.ker_mkQ] using
    A.rationalQuadraticKernel_cupQuotient_separated P hP hdim

/-- The intrinsic dimension count computed using the actual quotient
realization, with its required separation already derived. -/
def rationalKernelQuotientDimensionCount (m : ℕ) : ℕ :=
  Resonance.originalMaximalIsotropicDimensionCount
    (Resonance.cupQuotient A.rationalQuadraticKernel)
    A.rationalQuotientRealization_all_maximal_separated m

/-- Genuine fiber cardinal congruence identifies the actual quotient
count with the actual original logarithmic maximal-space count. -/
theorem rationalKernelQuotientDimensionCount_eq_original (m : ℕ) :
    A.rationalKernelQuotientDimensionCount m =
      A.rationalMaximalIsotropicDimensionCount m := by
  classical
  letI := Resonance.originalMaximalIsotropicFamilyFintype
    (Resonance.cupQuotient A.rationalQuadraticKernel)
    A.rationalQuotientRealization_all_maximal_separated
  letI := Resonance.originalMaximalIsotropicFamilyFintype A.quadraticLogarithmicRealization
    (fun P hP hdim ↦ A.rationalQuadraticKernel_separated P hP hdim)
  unfold rationalKernelQuotientDimensionCount rationalMaximalIsotropicDimensionCount
    Resonance.originalMaximalIsotropicDimensionCount
  exact Fintype.card_congr (A.rationalMaximalIsotropicDimensionFiberEquiv m)

end ChenRanks.AffineArrangement
