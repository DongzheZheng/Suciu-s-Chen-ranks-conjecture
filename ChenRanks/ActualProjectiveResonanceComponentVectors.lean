import ChenRanks.ActualProjectiveResonanceComponents
import ChenRanks.KoszulProjectiveEvaluation

/-!
# Actual vector spans of native projective resonance components

The vectors of a projective component are defined by the actual
projective evaluation points of nonzero vectors, together with the
origin. This definition uses the native quotient-Proj map and the
actual component set. It does not assign a dimension to a component
by an index or by a proposed Chen-rank formula.

For a genuine separated maximal isotropic subspace, the vector set of
its actual component is proved to be the original subspace itself.
Thus its actual affine vector span has the original dimension.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

namespace ChenRanks.Koszul

open ChenRanks.Resonance

universe u

variable (k E : Type u) [Field k] [AddCommGroup E] [_root_.Module k E]
variable {ι : Type u} [Fintype ι]
  (b : _root_.Module.Basis ι k (_root_.Module.Dual k E))

theorem symmetricDualLinearIdeal_le_lineKernel_iff
    (P : Submodule k E) (e : E) :
    symmetricDualLinearIdeal k E P ≤ (lineHomogeneousKernel k E b e).toIdeal ↔ e ∈ P := by
  constructor
  · intro h
    exact (symmetricDualLinearIdeal_le_evaluationKernel_iff k E P e).mp
      (h.trans (lineHomogeneousKernel_le_pointEvaluationKernel k E b e))
  · intro he
    apply Ideal.span_le.mpr
    rintro s ⟨φ, rfl⟩
    apply (mem_lineHomogeneousKernel k E b e _).mpr
    have hφ : (φ : _root_.Module.Dual k E) e = 0 :=
      (Submodule.mem_dualAnnihilator (W := P) φ.val).mp φ.property e he
    simp [lineSymmetricMap, pointOfVector, _root_.Module.Dual.eval_apply, hφ]

variable [FiniteDimensional k E]

theorem vectorProjectivePoint_mem_linearCone_iff (P : Submodule k E)
    {e : E} (he : e ≠ 0) :
    vectorProjectivePoint k E b e he ∈ ProjectiveSpectrum.zeroLocus
      (homogeneousS k (_root_.Module.Dual k E) b)
      (symmetricDualLinearIdeal k E P : Set (S k (_root_.Module.Dual k E))) ↔ e ∈ P :=
  symmetricDualLinearIdeal_le_lineKernel_iff k E b P e

variable (I : Submodule k (⋀[k]^2 E))

/-- Actual vectors whose nonzero projective evaluation points come
from the actual component C, with the origin included. -/
def actualProjectiveComponentAffineVectors
    (C : Set (actualProjectiveResonanceScheme k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I))) : Set E :=
  {e | e = 0 ∨ ∃ he : e ≠ 0,
    vectorProjectivePoint k E b e he ∈
      quotientProjectivePointMap k (_root_.Module.Dual k E) b
        (actualHomogeneousAnnihilator k (_root_.Module.Dual k E) b
          (exteriorAnnihilator k E 2 I)) '' C}

/-- The native linear span of the component's actual vectors. -/
def actualProjectiveComponentAffineSpan
    (C : Set (actualProjectiveResonanceScheme k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I))) : Submodule k E :=
  Submodule.span k (actualProjectiveComponentAffineVectors k E b I C)

variable [IsAlgClosed k] [CharZero k]

theorem actualProjectiveComponentAffineVectors_linearCone
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
      2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) :
    actualProjectiveComponentAffineVectors k E b I
      (actualProjectiveLinearCone k E b I P.val) = (P.val : Set E) := by
  ext e
  constructor
  · rintro (rfl | ⟨he, q, hq, hqe⟩)
    · exact P.val.zero_mem
    · change quotientProjectivePointMap k (_root_.Module.Dual k E) b
        (actualHomogeneousAnnihilator k (_root_.Module.Dual k E) b
          (exteriorAnnihilator k E 2 I)) q ∈ ProjectiveSpectrum.zeroLocus
          (homogeneousS k (_root_.Module.Dual k E) b)
          (symmetricDualLinearIdeal k E P.val : Set (S k (_root_.Module.Dual k E))) at hq
      rw [hqe] at hq
      exact (vectorProjectivePoint_mem_linearCone_iff k E b P.val he).mp hq
  · intro heP
    by_cases he : e = 0
    · exact Or.inl he
    · apply Or.inr
      refine ⟨he, ?_⟩
      have hline := (vectorProjectivePoint_mem_linearCone_iff k E b P.val he).mpr heP
      have hAnn : actualHomogeneousAnnihilator k (_root_.Module.Dual k E) b
          (exteriorAnnihilator k E 2 I) ≤
          (vectorProjectivePoint k E b e he).asHomogeneousIdeal :=
        (actualHomogeneousAnnihilator_le_linearCone k E b I hsep P).trans hline
      let q := quotientProjectivePointLift k (_root_.Module.Dual k E) b
        (actualHomogeneousAnnihilator k (_root_.Module.Dual k E) b
          (exteriorAnnihilator k E 2 I)) (vectorProjectivePoint k E b e he) hAnn
      have hq : quotientProjectivePointMap k (_root_.Module.Dual k E) b
          (actualHomogeneousAnnihilator k (_root_.Module.Dual k E) b
            (exteriorAnnihilator k E 2 I)) q = vectorProjectivePoint k E b e he :=
        quotientProjectivePointMap_lift k (_root_.Module.Dual k E) b
          (actualHomogeneousAnnihilator k (_root_.Module.Dual k E) b
            (exteriorAnnihilator k E 2 I)) (vectorProjectivePoint k E b e he) hAnn
      refine ⟨q, ?_, hq⟩
      change quotientProjectivePointMap k (_root_.Module.Dual k E) b
        (actualHomogeneousAnnihilator k (_root_.Module.Dual k E) b
          (exteriorAnnihilator k E 2 I)) q ∈ ProjectiveSpectrum.zeroLocus
          (homogeneousS k (_root_.Module.Dual k E) b)
          (symmetricDualLinearIdeal k E P.val : Set (S k (_root_.Module.Dual k E)))
      rw [hq]
      exact hline

theorem actualProjectiveComponentAffineSpan_linearCone
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
      2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) :
    actualProjectiveComponentAffineSpan k E b I
      (actualProjectiveLinearCone k E b I P.val) = P.val := by
  rw [actualProjectiveComponentAffineSpan,
    actualProjectiveComponentAffineVectors_linearCone k E b I hsep P]
  exact Submodule.span_eq P.val

end ChenRanks.Koszul
