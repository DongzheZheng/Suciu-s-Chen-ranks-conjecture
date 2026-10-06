import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finiteness through the supplied native equivalence

The additive and scalar parents are ordinary implicit arguments read
from the actual equivalence and the actual finiteness proof. The proof
uses the unchanged native inverse equivalence in a generic context.
There is no finiteness, comparison, or action hypothesis supplied to an
original mathematical endpoint by this helper.
-/

namespace ChenRanks

/-- Transport actual target finiteness back through the actual supplied
equivalence, retaining its stored additive and scalar structures. -/
theorem moduleFiniteOfStoredParentEquivInverse (R : Type*) [Semiring R]
    {M N : Type*}
    {mM : AddCommMonoid M} {mN : AddCommMonoid N}
    {sM : @_root_.Module R M (inferInstance : Semiring R) mM}
    {sN : @_root_.Module R N (inferInstance : Semiring R) mN}
    (e : letI := mM; letI := mN; letI := sM; letI := sN; M ≃ₗ[R] N)
    (hN : letI := mN; letI := sN; _root_.Module.Finite R N) :
    letI := mM; letI := sM; _root_.Module.Finite R M := by
  letI := mM
  letI := mN
  letI := sM
  letI := sN
  letI : _root_.Module.Finite R N := hN
  exact _root_.Module.Finite.equiv e.symm

end ChenRanks
