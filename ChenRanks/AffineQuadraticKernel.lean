import ChenRanks.HyperplaneQuadraticResidueClasses
import ChenRanks.AffineEquationPairSpans
import ChenRanks.CoordinatePairProjections
import ChenRanks.AffineQuadraticBoundaries

/-!
# The actual affine quadratic logarithmic kernel

The blocks are the actual spans of pairs of the original affine equation
polynomials. Their finite family is proved finite from the original finite
arrangement. Actual coordinate contractions construct the pair projections
and prove that their sum is the original exterior vector. At a nonparallel
block, genuine hyperplane residues force the actual augmentation
contraction to vanish. The actual complementary exterior map expands this
block into actual three-equation boundaries. Parallel blocks expand into
the actual parallel pair relations.

The boundary span is independently specified by the original affine
normals and equation polynomials. Neither a block kernel, a partition,
geometric flat, nor a regular remainder is a hypothesis. The last theorem
is an equality for the original rational-form kernel; it does not identify
this with the complement's singular cup-product kernel.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks.AffineArrangement

open Koszul

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance affineQuadraticKernelDecidableEq : DecidableEq ι := Classical.decEq ι
local instance affineQuadraticKernel_propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
local instance : Fintype A.ActualEquationPairSpanFamily := Fintype.ofFinite _

/-- The genuine pair predicate of one actual affine equation span. -/
def affineEquationBlockPairs (X : A.ActualEquationPairSpanFamily) (H K : ι) : Prop :=
  H ≠ K ∧ A.affineEquationPairSpan H K = X.val

private theorem affineEquationBlockPairs_symm (X : A.ActualEquationPairSpanFamily)
    (H K : ι) : A.affineEquationBlockPairs X H K ↔ A.affineEquationBlockPairs X K H := by
  constructor
  · rintro ⟨hHK, hspan⟩
    exact ⟨hHK.symm, (A.affineEquationPairSpan_swap K H).trans hspan⟩
  · rintro ⟨hKH, hspan⟩
    exact ⟨hKH.symm, (A.affineEquationPairSpan_swap H K).trans hspan⟩

/-- A true linear projection defined by the actual pair mask and actual
coordinate contractions of the original exterior vector. -/
def affineEquationBlockProjection (X : A.ActualEquationPairSpanFamily) :
    (⋀[ℂ]^2 (ι → ℂ)) →ₗ[ℂ] (⋀[ℂ]^2 (ι → ℂ)) :=
  coordinatePairProjection ℂ ι (A.affineEquationBlockPairs X)

theorem affineEquationBlockProjection_row_entry (X : A.ActualEquationPairSpanFamily)
    (H K : ι) (z : ⋀[ℂ]^2 (ι → ℂ)) :
    coordinateExteriorRow ℂ ι H (A.affineEquationBlockProjection X z) K =
      if A.affineEquationBlockPairs X H K then coordinateExteriorRow ℂ ι H z K else 0 :=
  coordinatePairProjection_row_entry ℂ ι (A.affineEquationBlockPairs X)
    (A.affineEquationBlockPairs_symm X) H K z

private theorem affineEquationBlockPairs_members (X : A.ActualEquationPairSpanFamily)
    {H K : ι} (h : A.affineEquationBlockPairs X H K) :
    A.equationPolynomial H ∈ X.val ∧ A.equationPolynomial K ∈ X.val := by
  constructor
  · exact h.right ▸ (Submodule.subset_span (by simp) :
      A.equationPolynomial H ∈ A.affineEquationPairSpan H K)
  · exact h.right ▸ (Submodule.subset_span (by simp) :
      A.equationPolynomial K ∈ A.affineEquationPairSpan H K)

private theorem affineEquationPairSpan_eq_block_of_members (X : A.ActualEquationPairSpanFamily)
    (H K : ι) (hHK : H ≠ K)
    (hH : A.equationPolynomial H ∈ X.val) (hK : A.equationPolynomial K ∈ X.val) :
    A.affineEquationPairSpan H K = X.val := by
  obtain ⟨R, T, hRT, hX⟩ := X.property
  by_cases hHR : H = R
  · subst H
    rw [hX] at hK ⊢
    exact A.affineEquationPairSpan_eq_of_mem R T K hHK hK
  · have hRH : A.affineEquationPairSpan R H = X.val := by
      rw [hX] at hH ⊢
      exact A.affineEquationPairSpan_eq_of_mem R T H (Ne.symm hHR) hH
    have hHRspan : A.affineEquationPairSpan H R = X.val := by
      rw [A.affineEquationPairSpan_swap H R]
      exact hRH
    have hK' : A.equationPolynomial K ∈ A.affineEquationPairSpan H R := hHRspan.symm ▸ hK
    exact (A.affineEquationPairSpan_eq_of_mem H R K hHK hK').trans hHRspan

private theorem exists_affineEquationBlock_partner (X : A.ActualEquationPairSpanFamily)
    (H : ι) (hH : A.equationPolynomial H ∈ X.val) :
    ∃ K : ι, A.affineEquationBlockPairs X H K := by
  obtain ⟨R, T, hRT, hX⟩ := X.property
  have hR : A.equationPolynomial R ∈ X.val := by
    rw [hX]
    exact Submodule.subset_span (by simp)
  have hT : A.equationPolynomial T ∈ X.val := by
    rw [hX]
    exact Submodule.subset_span (by simp)
  by_cases hHR : H = R
  · subst H
    exact ⟨T, hRT, A.affineEquationPairSpan_eq_block_of_members X R T hRT hR hT⟩
  · exact ⟨R, hHR, A.affineEquationPairSpan_eq_block_of_members X H R hHR hH hR⟩

/-- The actual finite equation-span projections reconstruct every
original exterior vector. Finiteness and the pair partition are derived. -/
theorem affineEquationBlockProjections_reconstruct (z : ⋀[ℂ]^2 (ι → ℂ)) :
    z = ∑ X : A.ActualEquationPairSpanFamily, A.affineEquationBlockProjection X z := by
  have hsum (H K : ι) :
      (∑ X : A.ActualEquationPairSpanFamily,
        coordinateExteriorRow ℂ ι H (A.affineEquationBlockProjection X z) K) =
          coordinateExteriorRow ℂ ι H z K := by
    by_cases hHK : H = K
    · subst K
      simp only [coordinateExteriorRow_self_zero, Finset.sum_const_zero]
    · let X : A.ActualEquationPairSpanFamily :=
        ⟨A.affineEquationPairSpan H K, H, K, hHK, rfl⟩
      rw [Finset.sum_eq_single X]
      · rw [A.affineEquationBlockProjection_row_entry, if_pos]
        exact ⟨hHK, rfl⟩
      · intro Y _ hYX
        rw [A.affineEquationBlockProjection_row_entry, if_neg]
        intro h
        apply hYX
        apply Subtype.ext
        exact h.right.symm
      · intro hX
        exact (hX (Finset.mem_univ X)).elim
  have hzero : z - ∑ X : A.ActualEquationPairSpanFamily,
      A.affineEquationBlockProjection X z = 0 := by
    apply exterior_eq_zero_of_coordinateRows_zero ℂ ι
    intro H
    ext K
    simp only [map_sub, map_sum, Pi.sub_apply, Finset.sum_apply]
    rw [hsum H K]
    exact sub_self _
  exact sub_eq_zero.mp hzero

private def affineCoordinateAugmentation : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun x := ∑ H, x H
  map_add' x y := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c x := by simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]

private theorem affineCoordinateAugmentation_basis (H : ι) :
    affineCoordinateAugmentation (ι := ι) (Pi.single H 1) = 1 := by
  simp [affineCoordinateAugmentation]

private theorem augmentationDeltaTwo_eq_sum_rows :
    pointDeltaTwo ℂ (ι → ℂ) (affineCoordinateAugmentation (ι := ι)) =
      ∑ H : ι, coordinateExteriorRow ℂ ι H := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  have hv : exteriorPower.ιMulti ℂ 2 v = exteriorWedge (k := ℂ) (v 0) (v 1) := by
    change exteriorPower.ιMulti ℂ 2 v = exteriorPower.ιMulti ℂ 2 ![v 0, v 1]
    congr 1
    ext i
    fin_cases i <;> rfl
  change pointDeltaTwo ℂ (ι → ℂ) (affineCoordinateAugmentation (ι := ι))
      (exteriorPower.ιMulti ℂ 2 v) =
    (∑ H : ι, coordinateExteriorRow ℂ ι H) (exteriorPower.ιMulti ℂ 2 v)
  rw [hv]
  simp only [pointDeltaTwo_wedge, affineCoordinateAugmentation,
    LinearMap.sum_apply, coordinateExteriorRow_wedge,
    Finset.sum_sub_distrib]
  change (∑ H : ι, v 0 H) • v 1 - (∑ H : ι, v 1 H) • v 0 =
    (∑ H : ι, v 0 H • v 1) - (∑ H : ι, v 1 H • v 0)
  rw [Finset.sum_smul, Finset.sum_smul]

/-- The actual block row equations, specified by membership of the
original affine equation polynomials in the actual pair span. This is
independent of either the rational or the singular cup-product kernel. -/
def affineEquationBlockRowRelations (z : ⋀[ℂ]^2 (ι → ℂ)) : Prop :=
  ∀ X : A.ActualEquationPairSpanFamily, (1 : CoordinateRing (d := d)) ∉ X.val →
    ∀ H : ι, A.equationPolynomial H ∈ X.val →
      (∑ K : ι, if A.equationPolynomial K ∈ X.val then
        coordinateExteriorRow ℂ ι H z K else 0) = 0

private theorem nonparallelBlock_row_sum_zero (X : A.ActualEquationPairSpanFamily)
    (hX : (1 : CoordinateRing (d := d)) ∉ X.val)
    (z : ⋀[ℂ]^2 (ι → ℂ)) (hrows : A.affineEquationBlockRowRelations z) (H : ι) :
    (∑ K : ι, coordinateExteriorRow ℂ ι H (A.affineEquationBlockProjection X z) K) = 0 := by
  by_cases hH : A.equationPolynomial H ∈ X.val
  · have hrow := hrows X hX H hH
    have hsum : (∑ K : ι,
        coordinateExteriorRow ℂ ι H (A.affineEquationBlockProjection X z) K) =
        ∑ K : ι, if A.equationPolynomial K ∈ X.val then
          coordinateExteriorRow ℂ ι H z K else 0 := by
      apply Finset.sum_congr rfl
      intro K _
      by_cases hHK : H = K
      · subst K
        simp only [coordinateExteriorRow_self_zero, ite_self]
      · have hclass : A.affineEquationBlockPairs X H K ↔ A.equationPolynomial K ∈ X.val := by
          constructor
          · intro h
            exact (A.affineEquationBlockPairs_members X h).right
          · intro hK
            exact ⟨hHK, A.affineEquationPairSpan_eq_block_of_members X H K hHK hH hK⟩
        rw [A.affineEquationBlockProjection_row_entry, hclass]
    exact hsum.trans hrow
  · apply Finset.sum_eq_zero
    intro K _
    rw [A.affineEquationBlockProjection_row_entry, if_neg]
    intro h
    exact hH (A.affineEquationBlockPairs_members X h).left

private theorem nonparallelBlock_augmentation_zero (X : A.ActualEquationPairSpanFamily)
    (hX : (1 : CoordinateRing (d := d)) ∉ X.val)
    (z : ⋀[ℂ]^2 (ι → ℂ)) (hrows : A.affineEquationBlockRowRelations z) :
    pointDeltaTwo ℂ (ι → ℂ) (affineCoordinateAugmentation (ι := ι))
      (A.affineEquationBlockProjection X z) = 0 := by
  rw [augmentationDeltaTwo_eq_sum_rows, LinearMap.sum_apply]
  ext H
  simp only [Finset.sum_apply, Pi.zero_apply]
  change (∑ K : ι, coordinateExteriorRow ℂ ι K (A.affineEquationBlockProjection X z) H) = 0
  calc
    (∑ K : ι, coordinateExteriorRow ℂ ι K (A.affineEquationBlockProjection X z) H) =
        ∑ K : ι, -coordinateExteriorRow ℂ ι H (A.affineEquationBlockProjection X z) K := by
      apply Finset.sum_congr rfl
      intro K _
      exact coordinateExteriorRow_swap ℂ ι K H _
    _ = -(∑ K : ι, coordinateExteriorRow ℂ ι H (A.affineEquationBlockProjection X z) K) :=
      Finset.sum_neg_distrib _
    _ = 0 := by rw [A.nonparallelBlock_row_sum_zero X hX z hrows H, neg_zero]

omit [Fintype ι] in
private theorem exterior_map_wedge (f : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) (x y : ι → ℂ) :
    exteriorPower.map 2 f (exteriorWedge (k := ℂ) x y) =
      exteriorWedge (k := ℂ) (f x) (f y) := by
  simp only [exteriorWedge, exteriorPower.map_apply_ιMulti]
  congr 1
  ext i
  fin_cases i <;> rfl

private theorem coordinate_difference_wedge (R H K : ι) :
    exteriorWedge (k := ℂ) (Pi.single H 1 - Pi.single R 1)
      (Pi.single K 1 - Pi.single R 1) = tripleBoundary R H K := by
  change exteriorWedgeBilin (k := ℂ) (Pi.single H 1 - Pi.single R 1)
    (Pi.single K 1 - Pi.single R 1) = _
  simp only [map_sub, LinearMap.sub_apply, exteriorWedgeBilin_apply,
    tripleBoundary, wedge_self, sub_zero]
  rw [wedge_swap (k := ℂ) (E := ι → ℂ)
    (Pi.single R (1 : ℂ) : ι → ℂ) (Pi.single H (1 : ℂ) : ι → ℂ)]
  abel

private theorem block_triangle_mem_boundarySpan (X : A.ActualEquationPairSpanFamily)
    (R : ι) (hR : A.equationPolynomial R ∈ X.val) (H K : ι)
    (hHK : A.affineEquationBlockPairs X H K) :
    tripleBoundary R H K ∈ A.affineQuadraticEquationBoundarySpan := by
  by_cases hRH : R = H
  · subst H
    simp only [tripleBoundary, sub_self, wedge_self, zero_add]
    exact Submodule.zero_mem _
  · have hmembers := A.affineEquationBlockPairs_members X hHK
    have hspan : A.affineEquationPairSpan R H = X.val :=
      A.affineEquationPairSpan_eq_block_of_members X R H hRH hR hmembers.left
    have hK : A.equationPolynomial K ∈
        Submodule.span ℂ {A.equationPolynomial R, A.equationPolynomial H} := by
      change A.equationPolynomial K ∈ A.affineEquationPairSpan R H
      rw [hspan]
      exact hmembers.right
    exact Submodule.subset_span (Or.inr ⟨R, H, K, hK, rfl⟩)

/-- A nonparallel actual equation block satisfying the actual original
row equations is a sum of actual three-equation boundaries. -/
theorem nonparallelBlock_mem_affineQuadraticEquationBoundarySpan
    (X : A.ActualEquationPairSpanFamily) (hX : (1 : CoordinateRing (d := d)) ∉ X.val)
    (z : ⋀[ℂ]^2 (ι → ℂ)) (hrows : A.affineEquationBlockRowRelations z) :
    A.affineEquationBlockProjection X z ∈ A.affineQuadraticEquationBoundarySpan := by
  obtain ⟨R, T, hRT, hXspan⟩ := X.property
  have hR : A.equationPolynomial R ∈ X.val := by
    rw [hXspan]
    exact Submodule.subset_span (by simp)
  let q := coordinateComplementProjection ℂ (ι → ℂ)
    (affineCoordinateAugmentation (ι := ι)) (Pi.single R 1)
  have hqbasis (H : ι) : q (Pi.single H 1) = Pi.single H 1 - Pi.single R 1 := by
    simp only [q, coordinateComplementProjection_apply,
      affineCoordinateAugmentation_basis, one_smul]
  have hδ := A.nonparallelBlock_augmentation_zero X hX z hrows
  have hdecomp := exteriorCoordinateRow_decomposition ℂ (ι → ℂ)
    (affineCoordinateAugmentation (ι := ι)) (Pi.single R 1)
      (A.affineEquationBlockProjection X z)
  have hwzero : exteriorWedge (k := ℂ) (Pi.single R 1 : ι → ℂ) 0 = 0 := by
    apply Subtype.ext
    simp
  rw [hδ, hwzero, zero_add] at hdecomp
  rw [hdecomp]
  change exteriorPower.map 2 q ((2 : ℂ)⁻¹ • coordinatePairSum ℂ ι
    (coordinatePairMask ℂ ι (A.affineEquationBlockPairs X)
      (coordinateExteriorRowTable ℂ ι z))) ∈ _
  rw [map_smul]
  apply Submodule.smul_mem
  change exteriorPower.map 2 q (∑ H : ι, ∑ K : ι,
    (if A.affineEquationBlockPairs X H K then coordinateExteriorRow ℂ ι H z K else 0) •
      exteriorWedge (k := ℂ) (Pi.single H 1) (Pi.single K 1)) ∈ _
  rw [map_sum]
  apply Submodule.sum_mem
  intro H _
  rw [map_sum]
  apply Submodule.sum_mem
  intro K _
  rw [map_smul]
  by_cases hHK : A.affineEquationBlockPairs X H K
  · rw [if_pos hHK]
    apply Submodule.smul_mem
    rw [exterior_map_wedge, hqbasis, hqbasis, coordinate_difference_wedge]
    exact A.block_triangle_mem_boundarySpan X R hR H K hHK
  · rw [if_neg hHK, zero_smul]
    exact Submodule.zero_mem _

/-- A parallel actual equation block is a sum of actual original
parallel pair relations. The parallel condition is derived from its span. -/
theorem parallelBlock_mem_affineQuadraticEquationBoundarySpan
    (X : A.ActualEquationPairSpanFamily) (hX : (1 : CoordinateRing (d := d)) ∈ X.val)
    (z : ⋀[ℂ]^2 (ι → ℂ)) :
    A.affineEquationBlockProjection X z ∈ A.affineQuadraticEquationBoundarySpan := by
  change (2 : ℂ)⁻¹ • (∑ H : ι, ∑ K : ι,
    (if A.affineEquationBlockPairs X H K then coordinateExteriorRow ℂ ι H z K else 0) •
      exteriorWedge (k := ℂ) (Pi.single H 1) (Pi.single K 1)) ∈ _
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro H _
  apply Submodule.sum_mem
  intro K _
  by_cases hHK : A.affineEquationBlockPairs X H K
  · rw [if_pos hHK]
    apply Submodule.smul_mem
    have hparallel : ∃ c : ℂ, A.normal K = c • A.normal H :=
      (A.one_mem_affineEquationPairSpan_iff_parallel H K hHK.left).mp (hHK.right.symm ▸ hX)
    exact Submodule.subset_span (Or.inl ⟨H, K, hparallel, rfl⟩)
  · rw [if_neg hHK, zero_smul]
    exact Submodule.zero_mem _

/-- Actual original equation-block row relations imply membership in
the independently defined original affine boundary span. This genuine
linear-algebra converse can be used with either proved rational-form
residues or proved evaluations of actual topological cup products. -/
theorem affineQuadraticEquationBoundarySpan_mem_of_block_row_relations
    (z : ⋀[ℂ]^2 (ι → ℂ)) (hrows : A.affineEquationBlockRowRelations z) :
    z ∈ A.affineQuadraticEquationBoundarySpan := by
  rw [A.affineEquationBlockProjections_reconstruct z]
  apply Submodule.sum_mem
  intro X _
  by_cases hX : (1 : CoordinateRing (d := d)) ∈ X.val
  · exact A.parallelBlock_mem_affineQuadraticEquationBoundarySpan X hX z
  · exact A.nonparallelBlock_mem_affineQuadraticEquationBoundarySpan X hX z hrows

/-- The original rational quadratic kernel is exactly the independently
defined actual affine equation boundary span. The actual block row
conditions are derived by actual residues, rather than assumed. -/
theorem rationalQuadraticKernel_eq_affineQuadraticEquationBoundarySpan :
    A.rationalQuadraticKernel = A.affineQuadraticEquationBoundarySpan := by
  apply le_antisymm
  · intro z hz
    apply A.affineQuadraticEquationBoundarySpan_mem_of_block_row_relations z
    intro X hX H hH
    obtain ⟨K, hHK, hspan⟩ := A.exists_affineEquationBlock_partner X H hH
    have hparallel : ¬∃ c : ℂ, A.normal K = c • A.normal H := by
      intro h
      apply hX
      exact hspan ▸ (A.one_mem_affineEquationPairSpan_iff_parallel H K hHK).mpr h
    obtain ⟨j, hj⟩ := A.exists_hyperplanePivot H
    have hr := A.rationalQuadraticKernel_restrictedDivisorClass_row_sum_zero
      z hz H K hHK j hj hparallel
    have hfilter : Finset.univ.filter (fun M : {M : ι // M ≠ H} ↦
        A.hyperplanePivotRestriction H j (A.equationPolynomial K) ∣
          A.hyperplanePivotRestriction H j (A.equationPolynomial M.val)) =
        Finset.univ.filter (fun M : {M : ι // M ≠ H} ↦
          A.equationPolynomial M.val ∈ X.val) := by
      ext M
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [A.hyperplaneRestricted_dvd_iff_mem_affineEquationPairSpan H K M.val j hj hparallel,
        hspan]
    rw [hfilter] at hr
    rw [Fintype.sum_eq_add_sum_subtype_ne _ H, coordinateExteriorRow_self_zero, ite_self,
      zero_add, ← Finset.sum_filter]
    exact hr
  · exact A.affineQuadraticEquationBoundarySpan_le_rationalQuadraticKernel

end ChenRanks.AffineArrangement
