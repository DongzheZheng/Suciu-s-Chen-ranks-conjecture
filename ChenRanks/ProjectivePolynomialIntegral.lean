import ChenRanks.ProjectivePolynomialBase
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Localization.Defs

/-!
# Integrality and actual affine opens of the actual polynomial Proj

Every actual homogeneous affine localization is reduced: at zero it is
subsingleton, and away from a nonzero element its actual localization
embedding goes into an actual domain.  The native affine cover therefore
proves that the actual projective ambient is reduced.  The actual zero
homogeneous prime is relevant because a genuine variable lies in the
irrelevant ideal and is nonzero.  Its actual singleton closure is the
whole projective spectrum, giving irreducibility and hence integrality.
No integral projective ambient or generic point is an input.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

universe u

variable (k ι : Type u) [Field k]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual homogeneous localizations of the actual polynomial ring are
reduced, including the degenerate zero-denominator case. -/
theorem projectivePolynomialAway_isReduced (f : MvPolynomial ι k) :
    _root_.IsReduced (HomogeneousLocalization.Away (projectivePolynomialGrading k ι) f) := by
  by_cases hf : f = 0
  · letI : Subsingleton
        (HomogeneousLocalization.Away (projectivePolynomialGrading k ι) f) :=
      HomogeneousLocalization.subsingleton (projectivePolynomialGrading k ι)
        (show (0 : MvPolynomial ι k) ∈ Submonoid.powers f from ⟨1, by simp [hf]⟩)
    infer_instance
  · have hM : Submonoid.powers f ≤ nonZeroDivisors (MvPolynomial ι k) := by
      rintro x ⟨n, rfl⟩
      exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hf)
    letI : IsDomain (Localization (Submonoid.powers f)) :=
      IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
    exact isReduced_of_injective
      (algebraMap (HomogeneousLocalization.Away (projectivePolynomialGrading k ι) f)
        (Localization (Submonoid.powers f)))
      (HomogeneousLocalization.val_injective (Submonoid.powers f))

/-- The native actual affine cover proves reducedness of the native Proj. -/
instance projectivePolynomialAmbient_isReduced :
    IsReduced (projectivePolynomialAmbient k ι) := by
  haveI : ∀ i : (Proj.affineOpenCover (projectivePolynomialGrading k ι)).I₀,
      IsReduced ((Proj.affineOpenCover (projectivePolynomialGrading k ι)).openCover.X i) := by
    intro i
    change IsReduced (Spec (.of (HomogeneousLocalization.Away
      (projectivePolynomialGrading k ι) (i.2 : MvPolynomial ι k))))
    letI := projectivePolynomialAway_isReduced k ι (i.2 : MvPolynomial ι k)
    infer_instance
  exact IsReduced.of_openCover (projectivePolynomialAmbient k ι)
    (Proj.affineOpenCover (projectivePolynomialGrading k ι)).openCover

variable [Nonempty ι]

/-- The actual zero homogeneous prime is a genuine point of this Proj. -/
def projectivePolynomialZeroPoint : projectivePolynomialAmbient k ι where
  asHomogeneousIdeal := ⊥
  isPrime := by
    change (⊥ : Ideal (MvPolynomial ι k)).IsPrime
    infer_instance
  not_irrelevant_le := by
    intro h
    let i : ι := Classical.ofNonempty
    have hx : MvPolynomial.X i ∈ HomogeneousIdeal.irrelevant (projectivePolynomialGrading k ι) :=
      HomogeneousIdeal.mem_irrelevant_of_mem (projectivePolynomialGrading k ι)
        (show 0 < (1 : ℕ) from Nat.zero_lt_one) (MvPolynomial.isHomogeneous_X k i)
    have hzero := h hx
    change MvPolynomial.X i ∈ (⊥ : Ideal (MvPolynomial ι k)) at hzero
    exact MvPolynomial.X_ne_zero i (Ideal.mem_bot.mp hzero)

/-- The closure of this actual zero prime is the whole actual Proj. -/
theorem projectivePolynomialZeroPoint_closure :
    closure ({projectivePolynomialZeroPoint k ι} : Set (projectivePolynomialAmbient k ι)) =
      Set.univ := by
  change closure ({projectivePolynomialZeroPoint k ι} :
    Set (ProjectiveSpectrum (projectivePolynomialGrading k ι))) = Set.univ
  rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  have hVI : ProjectiveSpectrum.vanishingIdeal
      ({projectivePolynomialZeroPoint k ι} :
        Set (ProjectiveSpectrum (projectivePolynomialGrading k ι))) =
      (projectivePolynomialZeroPoint k ι).asHomogeneousIdeal :=
    ProjectiveSpectrum.vanishingIdeal_singleton
      (𝒜 := projectivePolynomialGrading k ι) (projectivePolynomialZeroPoint k ι)
  rw [hVI]
  exact ProjectiveSpectrum.zeroLocus_bot (projectivePolynomialGrading k ι)

instance projectivePolynomialAmbient_irreducibleSpace :
    IrreducibleSpace (projectivePolynomialAmbient k ι) := by
  rw [irreducibleSpace_def]
  change IsIrreducible (Set.univ : Set (projectivePolynomialAmbient k ι))
  rw [← projectivePolynomialZeroPoint_closure k ι]
  exact (isIrreducible_singleton (x := projectivePolynomialZeroPoint k ι)).closure

/-- Reducedness and the proved actual zero-prime genericity give an
actual integral proper-source candidate. -/
instance projectivePolynomialAmbient_isIntegral :
    IsIntegral (projectivePolynomialAmbient k ι) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- A standard chart is an actual open of the actual polynomial Proj. -/
abbrev projectivePolynomialStandardOpen (i : ι) :
    (projectivePolynomialAmbient k ι).Opens :=
  Proj.basicOpen (projectivePolynomialGrading k ι) (MvPolynomial.X i)

omit [Nonempty ι] in
/-- Its affine structure is supplied by the actual homogeneous
localization construction, not an assumed affine chart. -/
theorem projectivePolynomialStandardOpen_isAffineOpen (i : ι) :
    IsAffineOpen (projectivePolynomialStandardOpen k ι i) :=
  Proj.isAffineOpen_basicOpen (projectivePolynomialGrading k ι) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one

instance projectivePolynomialStandardOpen_nonempty (i : ι) :
    Nonempty (projectivePolynomialStandardOpen k ι i) := by
  refine ⟨⟨projectivePolynomialZeroPoint k ι, ?_⟩⟩
  change MvPolynomial.X i ∉ (⊥ : Ideal (MvPolynomial ι k))
  simpa only [Ideal.mem_bot] using (MvPolynomial.X_ne_zero i)

end

end ChenRanks
