import ChenRanks.KoszulCanonicalFamilyUnifiedCokernelTransport

/-! The public original degree-cokernel comparison is the already
constructed single-parent native comparison. Its literal original
source and target are checked independently in
`ActualUnifiedCanonicalCokernelAudit`; no compatibility or substitute
quotient is introduced by this public alias. -/

noncomputable section

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))
variable {ι : Type*} [Fintype ι]
variable (b : _root_.Module.Basis ι k (_root_.Module.Dual k E))
variable [CharZero k]
variable (hsep : ∀ P : Submodule k E,
  IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
  2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)

/-- The same original public native degree-sum cokernel comparison. -/
def canonicalFamilyDegreeCokernelDirectSumEquiv :=
  canonicalFamilyUnifiedDegreeCokernelDirectSumEquiv k E I b hsep

end ChenRanks.Koszul
