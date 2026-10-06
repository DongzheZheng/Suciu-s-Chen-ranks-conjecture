import ChenRanks.MaximalIsotropicFiniteFamily

/-!
# The original quadratic map and its actual kernel-quotient family

The comparison keeps each subspace unchanged. Its maximality proofs come
from the proved equality of the two isotropy relations. Consequently the
literal dimension fibers are equivalent and their genuine counts agree.
-/

noncomputable section

namespace ChenRanks.Resonance

variable {k E W : Type*} [Field k] [AddCommGroup E] [Module k E]
  [AddCommGroup W] [Module k W]

def originalMaximalIsotropicKernelQuotientEquiv
    (φ : (⋀[k]^2 E) →ₗ[k] W) :
    OriginalMaximalIsotropicFamily (cupQuotient (LinearMap.ker φ)) ≃
      OriginalMaximalIsotropicFamily φ where
  toFun P := ⟨P.val, (isMaximalIsotropic_kernel_quotient_iff φ P.val).mp P.property.1,
    P.property.2⟩
  invFun P := ⟨P.val, (isMaximalIsotropic_kernel_quotient_iff φ P.val).mpr P.property.1,
    P.property.2⟩
  left_inv P := by apply Subtype.ext; rfl
  right_inv P := by apply Subtype.ext; rfl

def originalMaximalIsotropicKernelQuotientDimensionFiberEquiv
    (φ : (⋀[k]^2 E) →ₗ[k] W) (m : ℕ) :
    {P : OriginalMaximalIsotropicFamily (cupQuotient (LinearMap.ker φ)) //
      Module.finrank k P.val = m} ≃
    {P : OriginalMaximalIsotropicFamily φ // Module.finrank k P.val = m} where
  toFun P := ⟨originalMaximalIsotropicKernelQuotientEquiv φ P.val, P.property⟩
  invFun P := ⟨(originalMaximalIsotropicKernelQuotientEquiv φ).symm P.val, P.property⟩
  left_inv P := by
    apply Subtype.ext
    exact (originalMaximalIsotropicKernelQuotientEquiv φ).left_inv P.val
  right_inv P := by
    apply Subtype.ext
    exact (originalMaximalIsotropicKernelQuotientEquiv φ).right_inv P.val

variable [FiniteDimensional k E] [Infinite k]

theorem originalMaximalIsotropicDimensionCount_kernel_quotient
    (φ : (⋀[k]^2 E) →ₗ[k] W)
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge φ) P → 2 ≤ Module.finrank k P →
        mixedExterior P ⊓ LinearMap.ker φ = pureExterior P) (m : ℕ) :
    originalMaximalIsotropicDimensionCount (cupQuotient (LinearMap.ker φ))
        (fun P hP hdim => by
          simpa only [cupQuotient, Submodule.ker_mkQ] using
            hsep P ((isMaximalIsotropic_kernel_quotient_iff φ P).mp hP) hdim) m =
      originalMaximalIsotropicDimensionCount φ hsep m := by
  classical
  let hsep' : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient (LinearMap.ker φ))) P →
        2 ≤ Module.finrank k P →
          mixedExterior P ⊓ LinearMap.ker (cupQuotient (LinearMap.ker φ)) = pureExterior P :=
    fun P hP hdim => by
      simpa only [cupQuotient, Submodule.ker_mkQ] using
        hsep P ((isMaximalIsotropic_kernel_quotient_iff φ P).mp hP) hdim
  letI := originalMaximalIsotropicFamilyFintype φ hsep
  letI := originalMaximalIsotropicFamilyFintype (cupQuotient (LinearMap.ker φ)) hsep'
  unfold originalMaximalIsotropicDimensionCount
  exact Fintype.card_congr (originalMaximalIsotropicKernelQuotientDimensionFiberEquiv φ m)

end ChenRanks.Resonance
