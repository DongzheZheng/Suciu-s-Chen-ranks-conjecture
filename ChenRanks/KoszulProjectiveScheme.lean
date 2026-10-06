import ChenRanks.KoszulHomogeneousAnnihilator
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The native canonical projective resonance scheme

The coefficient quotient is the actual ring quotient by a genuine
homogeneous ideal. Its degree pieces are the actual images of the
original coefficient pieces. Original coefficient projections descend
because the ideal is genuinely homogeneous. Their actual action on each
piece proves internal direct-sum decomposition; multiplication gives a
native graded-ring dictionary.

For the original Koszul module, the ideal is its actual mathlib module
annihilator with the homogeneity already proved in the preceding file.
The resulting object is mathlib's actual scheme `Proj(S / Ann W)` from
the manuscript's canonical projective resonance definition. No
reducedness, component classification, or effective decomposition is
assumed or proved here. The construction also allows the whole-ring
annihilator and its actual zero quotient ring.
-/

noncomputable section

open scoped BigOperators DirectSum

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} (b : _root_.Module.Basis ι k V)
variable (H : HomogeneousIdeal (homogeneousS k V b))

/-- The actual coefficient ring quotient by the genuine homogeneous ideal. -/
abbrev HomogeneousCoefficientQuotient := S k V ⧸ H.toIdeal

/-- The actual image of the original degree-`n` coefficient subspace. -/
def quotientCoefficientPiece (n : ℕ) : Submodule k (HomogeneousCoefficientQuotient k V b H) :=
  (homogeneousS k V b n).map (Ideal.Quotient.mkₐ k H.toIdeal).toLinearMap

/-- The native homogeneous-ideal condition preserves the previously
constructed genuine coefficient projections. -/
theorem homogeneousIdeal_projection_mem (n : ℕ) (s : S k V) (hs : s ∈ H.toIdeal) :
    homogeneousProjection k V b n s ∈ H.toIdeal := by
  rw [← homogeneousS_gradedRing_proj, GradedRing.proj_apply]
  exact H.isHomogeneous n hs

/-- The actual ideal belongs to the actual kernel of the quotient-valued
coefficient projection. This is proved before descending that map. -/
theorem homogeneousIdeal_le_coefficientProjection_kernel (n : ℕ) :
    H.toIdeal.restrictScalars k ≤ LinearMap.ker
      ((Ideal.Quotient.mkₐ k H.toIdeal).toLinearMap.comp
        (homogeneousProjection k V b n)) := by
  intro s hs
  apply LinearMap.mem_ker.mpr
  change Ideal.Quotient.mk H.toIdeal (homogeneousProjection k V b n s) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (homogeneousIdeal_projection_mem k V b H n s hs)

/-- The true coefficient projection descended to the actual ring quotient,
using the native scalar-restriction quotient equivalence. -/
def quotientCoefficientProjection (n : ℕ) :
    HomogeneousCoefficientQuotient k V b H →ₗ[k] HomogeneousCoefficientQuotient k V b H :=
  (H.toIdeal.restrictScalars k).liftQ
      ((Ideal.Quotient.mkₐ k H.toIdeal).toLinearMap.comp
        (homogeneousProjection k V b n))
      (homogeneousIdeal_le_coefficientProjection_kernel k V b H n) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv k H.toIdeal).symm.toLinearMap

@[simp] theorem quotientCoefficientProjection_mk (n : ℕ) (s : S k V) :
    quotientCoefficientProjection k V b H n (Ideal.Quotient.mk H.toIdeal s) =
      Ideal.Quotient.mk H.toIdeal (homogeneousProjection k V b n s) := rfl

/-- The actual descended projection is the identity in the matching
degree image and zero on different degree images. -/
theorem quotientCoefficientProjection_of_mem (n m : ℕ)
    {q : HomogeneousCoefficientQuotient k V b H}
    (hq : q ∈ quotientCoefficientPiece k V b H m) :
    quotientCoefficientProjection k V b H n q = if n = m then q else 0 := by
  obtain ⟨s, hs, rfl⟩ := hq
  change quotientCoefficientProjection k V b H n (Ideal.Quotient.mk H.toIdeal s) =
    if n = m then Ideal.Quotient.mk H.toIdeal s else 0
  rw [quotientCoefficientProjection_mk, homogeneousProjection_of_mem k V b hs]
  by_cases h : n = m <;> simp [h]

/-- Every true quotient projection lies in the actual image degree. -/
theorem quotientCoefficientProjection_mem (n : ℕ)
    (q : HomogeneousCoefficientQuotient k V b H) :
    quotientCoefficientProjection k V b H n q ∈ quotientCoefficientPiece k V b H n := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [quotientCoefficientProjection_mk]
  exact ⟨homogeneousProjection k V b n s, homogeneousProjection_mem k V b n s, rfl⟩

/-- The genuine quotient degree projection detects its corresponding
component under actual canonical assembly. -/
theorem quotientCoefficientProjection_comp_coeLinearMap (n : ℕ) :
    (quotientCoefficientProjection k V b H n).comp
        (DirectSum.coeLinearMap (quotientCoefficientPiece k V b H)) =
      (quotientCoefficientPiece k V b H n).subtype.comp
        (DirectSum.component k ℕ (fun n ↦ ↥(quotientCoefficientPiece k V b H n)) n) := by
  apply DirectSum.linearMap_ext
  intro m
  apply LinearMap.ext
  intro q
  simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof]
  change quotientCoefficientProjection k V b H n
      (q : HomogeneousCoefficientQuotient k V b H) =
    (DirectSum.component k ℕ (fun n ↦ ↥(quotientCoefficientPiece k V b H n)) n
      (DirectSum.lof k ℕ (fun n ↦ ↥(quotientCoefficientPiece k V b H n)) m q) :
      HomogeneousCoefficientQuotient k V b H)
  rw [quotientCoefficientProjection_of_mem k V b H n m q.property]
  by_cases h : n = m
  · subst m
    simp only [ite_true, DirectSum.component.lof_self]
  · rw [DirectSum.component.of]
    simp [h, Ne.symm h]

/-- The actual quotient pieces give an actual internal direct-sum
decomposition, by the proved projections and true finite coefficient
expansion of each actual quotient representative. -/
theorem quotientCoefficientPiece_isInternal :
    DirectSum.IsInternal (quotientCoefficientPiece k V b H) := by
  change Function.Bijective (DirectSum.coeLinearMap (quotientCoefficientPiece k V b H))
  constructor
  · intro x y h
    apply DirectSum.ext_component k
    intro n
    apply Subtype.ext
    have hx := DFunLike.congr_fun
      (quotientCoefficientProjection_comp_coeLinearMap k V b H n) x
    have hy := DFunLike.congr_fun
      (quotientCoefficientProjection_comp_coeLinearMap k V b H n) y
    exact hx.symm.trans ((congrArg (quotientCoefficientProjection k V b H n) h).trans hy)
  · intro q
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨∑ n ∈ Finset.range ((SymmetricAlgebra.equivMvPolynomial b s).totalDegree + 1),
      DirectSum.lof k ℕ (fun n ↦ ↥(quotientCoefficientPiece k V b H n)) n
        ⟨Ideal.Quotient.mk H.toIdeal (homogeneousProjection k V b n s),
          ⟨homogeneousProjection k V b n s, homogeneousProjection_mem k V b n s, rfl⟩⟩, ?_⟩
    rw [map_sum]
    simp only [DirectSum.coeLinearMap_lof]
    change (∑ n ∈ Finset.range ((SymmetricAlgebra.equivMvPolynomial b s).totalDegree + 1),
      Ideal.Quotient.mk H.toIdeal (homogeneousProjection k V b n s)) =
        Ideal.Quotient.mk H.toIdeal s
    rw [← map_sum, sum_homogeneousProjection]

/-- The actual quotient's unit belongs to its true degree-zero image. -/
theorem quotientCoefficientPiece_one :
    (1 : HomogeneousCoefficientQuotient k V b H) ∈ quotientCoefficientPiece k V b H 0 :=
  ⟨1, homogeneousS_one k V b, rfl⟩

/-- Multiplication adds true quotient coefficient degrees, using actual
representatives and the genuine ring quotient multiplication. -/
theorem quotientCoefficientPiece_mul {m n : ℕ}
    {s t : HomogeneousCoefficientQuotient k V b H}
    (hs : s ∈ quotientCoefficientPiece k V b H m)
    (ht : t ∈ quotientCoefficientPiece k V b H n) :
    s * t ∈ quotientCoefficientPiece k V b H (m + n) := by
  obtain ⟨s, hs, rfl⟩ := hs
  obtain ⟨t, ht, rfl⟩ := ht
  exact ⟨s * t, homogeneousS_mul k V b hs ht,
    (Ideal.Quotient.mkₐ k H.toIdeal).map_mul s t⟩

/-- Native grading of the actual ring quotient, derived from the proved
internal decomposition and actual multiplication. -/
instance quotientCoefficientPiece_gradedRing : GradedRing (quotientCoefficientPiece k V b H) where
  one_mem := quotientCoefficientPiece_one k V b H
  mul_mem := fun {_m _n} {_s _t} hs ht ↦ quotientCoefficientPiece_mul k V b H hs ht
  toDecomposition := (quotientCoefficientPiece_isInternal k V b H).chooseDecomposition

variable [Fintype ι] (K : Submodule k (⋀[k]^2 V))

/-- The actual degree images in the actual canonical annihilator quotient
ring, with the original Koszul module unchanged. -/
abbrev actualResonanceQuotientDegree (n : ℕ) :
    Submodule k (S k V ⧸ _root_.Module.annihilator (S k V) (Module k V K)) :=
  quotientCoefficientPiece k V b (actualHomogeneousAnnihilator k V b K) n

/-- The canonical quotient grading uses the native graded-ring dictionary
already proved for the genuine quotient by its actual homogeneous ideal. -/
instance actualResonanceQuotientDegree_gradedRing :
    GradedRing (actualResonanceQuotientDegree k V b K) :=
  quotientCoefficientPiece_gradedRing k V b (actualHomogeneousAnnihilator k V b K)

/-- The manuscript's canonical projective resonance object is the genuine
native scheme `Proj(S / Ann(original W))`, equipped with the actual
quotient grading proved above. Reducedness is not part of its definition. -/
def actualProjectiveResonanceScheme : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Proj (actualResonanceQuotientDegree k V b K)

/-- A genuine canonical quotient degree consists exactly of true quotient
classes with actual original homogeneous representatives. -/
theorem mem_actualResonanceQuotientDegree_iff (n : ℕ)
    (q : S k V ⧸ _root_.Module.annihilator (S k V) (Module k V K)) :
    q ∈ actualResonanceQuotientDegree k V b K n ↔
      ∃ s : S k V, s ∈ homogeneousS k V b n ∧
        Ideal.Quotient.mk (_root_.Module.annihilator (S k V) (Module k V K)) s = q := Iff.rfl

end ChenRanks.Koszul
