import ChenRanks.DirectSumMonoidSourceCokernel
import ChenRanks.LinearMapDiagramMonoidSourceCokernel

/-! Component quotients, the full original diagram and the original
scalar-restriction quotient equivalence are composed with a single set
of explicitly retained native target-group parents. The maps and source
parents are ordinary implicit arguments determined by the actual full
diagram. No compatibility, range or cokernel comparison is assumed. -/

noncomputable section

open scoped DirectSum

namespace ChenRanks

variable (R : Type*) [Ring R]

/-- One native factory from actual component cokernels to the actual
whole-diagram cokernel. Its target groups are retained once throughout. -/
def directSumStoredDiagramCokernelEquiv
    {ι : Type*} {M N : ι → Type*}
    {aM : ∀ i, AddCommMonoid (M i)} {aN : ∀ i, AddCommGroup (N i)}
    {sM : ∀ i, @Module R (M i) (inferInstance : Semiring R) (aM i)}
    {sN : ∀ i, @Module R (N i) (inferInstance : Semiring R)
      (aN i).toAddCommMonoid}
    {W Z : Type*} {aW : AddCommMonoid W} {aZ : AddCommGroup Z}
    {sW : @Module R W (inferInstance : Semiring R) aW}
    {sZ : @Module R Z (inferInstance : Semiring R) aZ.toAddCommMonoid}
    {f : letI := aM; letI := aN; letI := sM; letI := sN;
      ∀ i, M i →ₗ[R] N i}
    {θ : letI := aW; letI := aZ; letI := sW; letI := sZ; W →ₗ[R] Z}
    {eM : letI := aM; letI := sM; letI := aW; letI := sW;
      (⨁ i, M i) ≃ₗ[R] W}
    {eN : letI := aN; letI := sN; letI := aZ; letI := sZ;
      (⨁ i, N i) ≃ₗ[R] Z}
    (h : letI := aM; letI := aN; letI := sM; letI := sN;
      letI := aW; letI := aZ; letI := sW; letI := sZ;
      eN.toLinearMap.comp (DirectSum.lmap f) = θ.comp eM.toLinearMap) :
    letI := aM; letI := aN; letI := sM; letI := sN;
    letI := aW; letI := aZ; letI := sW; letI := sZ;
    (⨁ i, (N i ⧸ LinearMap.range (f i))) ≃ₗ[R]
      (Z ⧸ LinearMap.range θ) := by
  letI := aM
  letI := aN
  letI := sM
  letI := sN
  letI := aW
  letI := aZ
  letI := sW
  letI := sZ
  exact (directSumMonoidSourceCokernelEquiv R M N f).symm.trans
    (monoidSourceDiagramCokernelEquiv R h)

/-- The same single-parent factory followed by an already proved actual
whole-quotient equivalence. The intermediate quotient is constructed
only once, rather than normalized between two independent factories. -/
def directSumStoredDiagramCokernelEquivTo
    {ι : Type*} {M N : ι → Type*}
    {aM : ∀ i, AddCommMonoid (M i)} {aN : ∀ i, AddCommGroup (N i)}
    {sM : ∀ i, @Module R (M i) (inferInstance : Semiring R) (aM i)}
    {sN : ∀ i, @Module R (N i) (inferInstance : Semiring R)
      (aN i).toAddCommMonoid}
    {W Z Q : Type*} {aW : AddCommMonoid W} {aZ : AddCommGroup Z}
    {aQ : AddCommMonoid Q}
    {sW : @Module R W (inferInstance : Semiring R) aW}
    {sZ : @Module R Z (inferInstance : Semiring R) aZ.toAddCommMonoid}
    {sQ : @Module R Q (inferInstance : Semiring R) aQ}
    {f : letI := aM; letI := aN; letI := sM; letI := sN;
      ∀ i, M i →ₗ[R] N i}
    {θ : letI := aW; letI := aZ; letI := sW; letI := sZ; W →ₗ[R] Z}
    {eM : letI := aM; letI := sM; letI := aW; letI := sW;
      (⨁ i, M i) ≃ₗ[R] W}
    {eN : letI := aN; letI := sN; letI := aZ; letI := sZ;
      (⨁ i, N i) ≃ₗ[R] Z}
    (h : letI := aM; letI := aN; letI := sM; letI := sN;
      letI := aW; letI := aZ; letI := sW; letI := sZ;
      eN.toLinearMap.comp (DirectSum.lmap f) = θ.comp eM.toLinearMap)
    (eQ : letI := aW; letI := aZ; letI := sW; letI := sZ;
      letI := aQ; letI := sQ; (Z ⧸ LinearMap.range θ) ≃ₗ[R] Q) :
    letI := aM; letI := aN; letI := sM; letI := sN;
    letI := aQ; letI := sQ;
    (⨁ i, (N i ⧸ LinearMap.range (f i))) ≃ₗ[R] Q := by
  letI := aM
  letI := aN
  letI := sM
  letI := sN
  letI := aW
  letI := aZ
  letI := sW
  letI := sZ
  letI := aQ
  letI := sQ
  exact (directSumStoredDiagramCokernelEquiv R h).trans eQ

end ChenRanks
