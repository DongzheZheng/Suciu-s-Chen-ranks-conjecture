import ChenRanks.ProjectivePolynomialFunctionField

/-!
# Scalar actions on the original polynomial fraction field

The original scalar action is the actual constant-polynomial map followed
by the actual fraction-ring map. The module and scalar-tower dictionaries
below are derived from that action; they do not modify its scalar map.
-/

noncomputable section

namespace ChenRanks

universe u

variable (k ι : Type u) [Field k]

abbrev projectivePolynomialOriginalFieldSMul :
    SMul k (projectivePolynomialOriginalFunctionField k ι) :=
  (projectivePolynomialOriginalFieldAlgebra k ι).toSMul

abbrev projectivePolynomialOriginalFieldModule :
    letI : Algebra k (projectivePolynomialOriginalFunctionField k ι) :=
      projectivePolynomialOriginalFieldAlgebra k ι
    Module k (projectivePolynomialOriginalFunctionField k ι) :=
  @Algebra.toModule k (projectivePolynomialOriginalFunctionField k ι)
    (inferInstanceAs (CommSemiring k))
    (inferInstanceAs (Semiring (projectivePolynomialOriginalFunctionField k ι)))
    (projectivePolynomialOriginalFieldAlgebra k ι)

/-- The actual original coefficient action associates with multiplication
in the coefficient field. -/
theorem projectivePolynomialOriginalField_selfScalarTower :
    letI : Algebra k (projectivePolynomialOriginalFunctionField k ι) :=
      projectivePolynomialOriginalFieldAlgebra k ι
    letI : SMul k (projectivePolynomialOriginalFunctionField k ι) :=
      projectivePolynomialOriginalFieldSMul k ι
    IsScalarTower k k (projectivePolynomialOriginalFunctionField k ι) := by
  letI : Algebra k (projectivePolynomialOriginalFunctionField k ι) :=
    projectivePolynomialOriginalFieldAlgebra k ι
  letI : SMul k (projectivePolynomialOriginalFunctionField k ι) :=
    projectivePolynomialOriginalFieldSMul k ι
  constructor
  intro a b x
  change algebraMap k (projectivePolynomialOriginalFunctionField k ι) (a * b) * x =
    algebraMap k (projectivePolynomialOriginalFunctionField k ι) a *
      (algebraMap k (projectivePolynomialOriginalFunctionField k ι) b * x)
  rw [map_mul, mul_assoc]

end ChenRanks
