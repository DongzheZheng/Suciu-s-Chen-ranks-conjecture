import ChenRanks.ModuleAnnihilatorLocalization
import ChenRanks.LocalizedTensorVanishing
import Mathlib.RingTheory.Localization.BaseChange

/-!
# An actual annihilating denominator from finite localized vanishing

For a finite module and a genuine ring localization, vanishing of the
literal tensor localization produces one actual denominator that
annihilates the whole original module. The common denominator is derived
from the proved annihilator-localization theorem, not supplied as a
support detector. A denominator from a larger prime's complement remains
outside every smaller prime, giving true further-localization vanishing.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks

variable (S R : Type*) [CommRing S] [CommRing R] [Algebra S R]
variable (D : Submonoid S) [hLoc : IsLocalization D R]
variable (M : Type*) [AddCommGroup M] [Module S M] [Module.Finite S M]

/-- Literal tensor-localization vanishing yields a genuine denominator
in the actual original annihilator of the finite module. -/
theorem finiteModule_exists_annihilating_denominator
    [Subsingleton (R ⊗[S] M)] :
    ∃ d : S, d ∈ D ∧ d ∈ Module.annihilator S M := by
  let f : M →ₗ[S] R ⊗[S] M := TensorProduct.mk S R M 1
  letI : IsLocalizedModule D f := by
    change IsLocalizedModule D (TensorProduct.mk S R M 1)
    infer_instance
  have heq : Module.annihilator R (R ⊗[S] M) =
      (Module.annihilator S M).map (algebraMap S R) :=
    localizedModule_annihilator_eq_map S D R M (R ⊗[S] M) f
  have h1 : (1 : R) ∈ Module.annihilator R (R ⊗[S] M) := by
    rw [Module.mem_annihilator]
    intro z
    exact Subsingleton.elim _ _
  have hm : algebraMap S R (1 : S) ∈
      (Module.annihilator S M).map (algebraMap S R) := by
    rw [map_one, ← heq]
    exact h1
  obtain ⟨d, hd, hdann⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff D R
      (Module.annihilator S M) 1).mp hm
  exact ⟨d, hd, by simpa only [mul_one] using hdann⟩

omit D hLoc in
/-- A literal localization at `p` that vanishes also vanishes at every
`q ≤ p`, via a genuine common original annihilating denominator. -/
theorem finiteModule_furtherLocalization_subsingleton
    (p q : Ideal S) [p.IsPrime] [q.IsPrime] (hqp : q ≤ p)
    [IsLocalization p.primeCompl R] [Subsingleton (R ⊗[S] M)]
    (A : Type*) [CommRing A] [Algebra S A] [IsLocalization q.primeCompl A] :
    Subsingleton (A ⊗[S] M) := by
  obtain ⟨d, hd, hdm⟩ :=
    finiteModule_exists_annihilating_denominator S R p.primeCompl M
  have hdq : d ∈ q.primeCompl := by
    intro hdmem
    exact hd (hqp hdmem)
  exact localizedTensor_subsingleton_of_annihilating_denominator S A q.primeCompl M
    d hdq (Module.mem_annihilator.mp hdm)

end ChenRanks
