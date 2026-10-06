import Mathlib.Algebra.Module.Submodule.Equiv

/-! Ordinary implicit parents are read from the supplied actual linear
equivalences. They are not synthesis-implicit typeclass obligations.
The body is the unchanged native composition. -/

namespace ChenRanks

/-- Compose the actual equivalences using their stored additive and
scalar parents, without searching for a new structure on the carriers. -/
def linearEquivStoredParentComposition (R : Type*) [Semiring R]
    {M N P : Type*}
    {mM : AddCommMonoid M} {mN : AddCommMonoid N} {mP : AddCommMonoid P}
    {sM : @_root_.Module R M (inferInstance : Semiring R) mM}
    {sN : @_root_.Module R N (inferInstance : Semiring R) mN}
    {sP : @_root_.Module R P (inferInstance : Semiring R) mP}
    (e : letI := mM; letI := mN; letI := sM; letI := sN; M ≃ₗ[R] N)
    (f : letI := mN; letI := mP; letI := sN; letI := sP; N ≃ₗ[R] P) :
    letI := mM; letI := mP; letI := sM; letI := sP; M ≃ₗ[R] P := by
  letI := mM
  letI := mN
  letI := mP
  letI := sM
  letI := sN
  letI := sP
  exact e.trans f

end ChenRanks
