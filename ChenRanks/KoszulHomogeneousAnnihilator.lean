import ChenRanks.KoszulDirectSum
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# The actual Koszul annihilator is homogeneous

The genuine symmetric-algebra homogeneous pieces form a native graded
ring, by their proved finite decomposition and their actual projections.
On the original Koszul quotient, projecting a scalar action on a genuine
degree `r` element isolates the scalar's genuine degree `n` part in degree
`n+r`. The actual direct-sum recomposition then proves that each
homogeneous part of an annihilating scalar annihilates the original module.

The annihilator remains mathlib's actual module annihilator. Neither
annihilator homogeneity, a graded-module structure, projective reducedness,
nor a support comparison is an input.
-/

noncomputable section

open scoped BigOperators DirectSum

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} (b : _root_.Module.Basis ι k V)

/-- A genuine homogeneous coefficient projection extracts the matching
component from canonical homogeneous assembly. -/
theorem homogeneousProjection_comp_coeLinearMap (n : ℕ) :
    (homogeneousProjection k V b n).comp
        (DirectSum.coeLinearMap (homogeneousS k V b)) =
      (homogeneousS k V b n).subtype.comp
        (DirectSum.component k ℕ (fun n ↦ ↥(homogeneousS k V b n)) n) := by
  apply DirectSum.linearMap_ext
  intro m
  apply LinearMap.ext
  intro s
  simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof]
  change homogeneousProjection k V b n (s : S k V) =
    (DirectSum.component k ℕ (fun n ↦ ↥(homogeneousS k V b n)) n
      (DirectSum.lof k ℕ (fun n ↦ ↥(homogeneousS k V b n)) m s) : S k V)
  rw [homogeneousProjection_of_mem k V b s.property]
  by_cases h : n = m
  · subst m
    simp only [ite_true, DirectSum.component.lof_self]
  · rw [DirectSum.component.of]
    simp [h, Ne.symm h]

/-- The genuine polynomial coefficient decomposition is internal. Its
injectivity is detected by the actual coefficient projections; its
surjectivity is the already proved finite polynomial expansion. -/
theorem homogeneousS_isInternal : DirectSum.IsInternal (homogeneousS k V b) := by
  change Function.Bijective (DirectSum.coeLinearMap (homogeneousS k V b))
  constructor
  · intro x y h
    apply DirectSum.ext_component k
    intro n
    apply Subtype.ext
    have hx := DFunLike.congr_fun
      (homogeneousProjection_comp_coeLinearMap k V b n) x
    have hy := DFunLike.congr_fun
      (homogeneousProjection_comp_coeLinearMap k V b n) y
    exact hx.symm.trans ((congrArg (homogeneousProjection k V b n) h).trans hy)
  · intro s
    refine ⟨∑ n ∈ Finset.range
        ((SymmetricAlgebra.equivMvPolynomial b s).totalDegree + 1),
      DirectSum.lof k ℕ (fun n ↦ ↥(homogeneousS k V b n)) n
        ⟨homogeneousProjection k V b n s, homogeneousProjection_mem k V b n s⟩, ?_⟩
    rw [map_sum]
    simp only [DirectSum.coeLinearMap_lof]
    exact sum_homogeneousProjection k V b s

/-- The native graded-ring dictionary is constructed from actual
coefficient multiplication and the proved internal decomposition. -/
instance homogeneousS_gradedRing : GradedRing (homogeneousS k V b) where
  one_mem := homogeneousS_one k V b
  mul_mem := fun {_m _n} {_s _t} hs ht ↦ homogeneousS_mul k V b hs ht
  toDecomposition := (homogeneousS_isInternal k V b).chooseDecomposition

/-- The native graded-ring projection is exactly the previously
constructed actual polynomial homogeneous projection. -/
theorem homogeneousS_gradedRing_proj (n : ℕ) (s : S k V) :
    GradedRing.proj (homogeneousS k V b) n s = homogeneousProjection k V b n s := by
  rw [GradedRing.proj_apply]
  have h := DFunLike.congr_fun
    (homogeneousProjection_comp_coeLinearMap k V b n)
    (DirectSum.decompose (homogeneousS k V b) s)
  change homogeneousProjection k V b n
      ((DirectSum.decompose (homogeneousS k V b)).symm
        (DirectSum.decompose (homogeneousS k V b) s)) =
    (DirectSum.decompose (homogeneousS k V b) s n : S k V) at h
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

variable [Fintype ι] (K : Submodule k (⋀[k]^2 V))

/-- The original quotient's genuine degree projection, with codomain
returned to the original quotient by the actual degree inclusion. -/
def originalDegreeProjection (r : ℕ) : Module k V K →ₗ[k] Module k V K :=
  (degreeQuotientInclusion k V b K r).comp (quotientProjection k V b K r)

/-- An actual degree inclusion lands in the actual original degree image. -/
theorem degreeQuotientInclusion_mem_originalDegree (r : ℕ)
    (w : homogeneousModule k V b K r) :
    degreeQuotientInclusion k V b K r w ∈
      LinearMap.range (degreeCycleToUngraded k V b K r) := by
  refine Submodule.Quotient.induction_on _ w ?_
  intro z
  exact ⟨z, rfl⟩

/-- The original quotient projection is the identity on its actual degree
image and zero on every different actual degree image. -/
theorem originalDegreeProjection_of_mem (n m : ℕ) {w : Module k V K}
    (hw : w ∈ LinearMap.range (degreeCycleToUngraded k V b K m)) :
    originalDegreeProjection k V b K n w = if n = m then w else 0 := by
  obtain ⟨z, rfl⟩ := hw
  change degreeQuotientInclusion k V b K n
      (quotientProjection k V b K n
        (degreeQuotientInclusion k V b K m (Submodule.Quotient.mk z))) =
    if n = m then degreeQuotientInclusion k V b K m (Submodule.Quotient.mk z) else 0
  by_cases h : n = m
  · subst m
    rw [quotientProjection_degreeQuotientInclusion_self]
    simp
  · rw [quotientProjection_degreeQuotientInclusion_ne k V b K n m h, map_zero]
    simp only [h, ite_false]

/-- Projecting the genuine finite scalar expansion isolates its degree
`n` action on a genuine degree `r` element. In particular, if the full
scalar kills that element, each actual homogeneous coefficient does. -/
theorem homogeneousProjection_smul_eq_zero_of_smul_eq_zero
    (s : S k V) (n r : ℕ) (w : Module k V K)
    (hw : w ∈ LinearMap.range (degreeCycleToUngraded k V b K r))
    (hz : s • w = 0) : homogeneousProjection k V b n s • w = 0 := by
  classical
  let N := max (n + 1) ((SymmetricAlgebra.equivMvPolynomial b s).totalDegree + 1)
  have hN : (SymmetricAlgebra.equivMvPolynomial b s).totalDegree + 1 ≤ N :=
    le_max_right _ _
  have hn : n ∈ Finset.range N := Finset.mem_range.mpr (by
    have := le_max_left (n + 1)
      ((SymmetricAlgebra.equivMvPolynomial b s).totalDegree + 1)
    omega)
  have hterms : ∀ i : ℕ,
      originalDegreeProjection k V b K (n + r)
        (homogeneousProjection k V b i s • w) =
      if i = n then homogeneousProjection k V b n s • w else 0 := by
    intro i
    rw [originalDegreeProjection_of_mem k V b K (n + r) (i + r)
      (homogeneous_smul_originalDegree_mem k V b K i r
        ⟨homogeneousProjection k V b i s, homogeneousProjection_mem k V b i s⟩ w hw)]
    by_cases hi : i = n
    · subst i
      simp
    · have hne : n + r ≠ i + r := fun h ↦ hi (Nat.add_right_cancel h).symm
      simp only [hi, hne, ite_false]
  have hzero : originalDegreeProjection k V b K (n + r)
      (∑ i ∈ Finset.range N, homogeneousProjection k V b i s • w) = 0 := by
    rw [← Finset.sum_smul, sum_homogeneousProjection_of_le k V b s N hN,
      hz, map_zero]
  rw [map_sum] at hzero
  simp only [hterms] at hzero
  simpa [hn] using hzero

/-- Every genuine homogeneous coefficient of an actual annihilating
scalar annihilates the original Koszul module. Actual direct-sum
recomposition extends the degreewise calculation to every original
quotient element. -/
theorem homogeneousProjection_mem_annihilator (s : S k V) (n : ℕ)
    (hs : s ∈ _root_.Module.annihilator (S k V) (Module k V K)) :
    homogeneousProjection k V b n s ∈
      _root_.Module.annihilator (S k V) (Module k V K) := by
  apply _root_.Module.mem_annihilator.mpr
  intro w
  obtain ⟨x, rfl⟩ := assembleHomogeneous_surjective k V b K w
  refine DirectSum.induction_on x ?_ ?_ ?_
  · simp
  · intro r z
    change homogeneousProjection k V b n s •
      assembleHomogeneous k V b K (DirectSum.lof k ℕ (homogeneousModule k V b K) r z) = 0
    rw [assembleHomogeneous_lof]
    exact homogeneousProjection_smul_eq_zero_of_smul_eq_zero k V b K s n r _
      (degreeQuotientInclusion_mem_originalDegree k V b K r z)
      (_root_.Module.mem_annihilator.mp hs _)
  · intro x y hx hy
    simp only [map_add, smul_add, hx, hy, add_zero]

/-- The canonical annihilator of the original Koszul module is a genuine
homogeneous ideal for the native actual symmetric-algebra grading. -/
theorem actual_annihilator_isHomogeneous :
    (_root_.Module.annihilator (S k V) (Module k V K)).IsHomogeneous
      (homogeneousS k V b) := by
  intro n s hs
  change (DirectSum.decompose (homogeneousS k V b) s n : S k V) ∈
    _root_.Module.annihilator (S k V) (Module k V K)
  rw [← GradedRing.proj_apply, homogeneousS_gradedRing_proj]
  exact homogeneousProjection_mem_annihilator k V b K s n hs

/-- The native homogeneous ideal carries the actual original
annihilator, with homogeneity supplied by the preceding actual proof. -/
def actualHomogeneousAnnihilator : HomogeneousIdeal (homogeneousS k V b) :=
  ⟨_root_.Module.annihilator (S k V) (Module k V K), actual_annihilator_isHomogeneous k V b K⟩

@[simp] theorem actualHomogeneousAnnihilator_toIdeal :
    (actualHomogeneousAnnihilator k V b K).toIdeal =
      _root_.Module.annihilator (S k V) (Module k V K) := rfl

end ChenRanks.Koszul
