import ChenRanks.ProjectiveDehomogenization
import ChenRanks.ProjectivePolynomialIntegral
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The actual standard projective chart is the original affine coordinate ring

The map out of the actual degree-zero homogeneous localization is the
actual localization lift of dehomogenization.  Its injectivity follows
from the proved no-hidden-kernel result for actual homogeneous numerators.
The genuine fractions Xi/Z0 and genuine constants give an inverse map
from the original polynomial ring by its actual universal property.
Thus the chart comparison is constructed, rather than assumed.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

variable (k ι : Type u) [Field k] [Finite ι]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual homogeneous coordinate corresponding to the affine chart. -/
abbrev projectivePolynomialHomogenizingVariable : MvPolynomial (Option ι) k :=
  MvPolynomial.X none

/-- The actual degree-zero coordinate ring of the actual standard chart. -/
abbrev projectivePolynomialChartRing :=
  HomogeneousLocalization.Away (projectivePolynomialGrading k (Option ι))
    (projectivePolynomialHomogenizingVariable k ι)

omit [Finite ι] in
theorem projectivePolynomialDehomogenization_none :
    projectivePolynomialDehomogenization k ι (MvPolynomial.X none) = 1 := by
  change Polynomial.eval 1 (MvPolynomial.optionEquivLeft k ι (MvPolynomial.X none)) = 1
  rw [MvPolynomial.optionEquivLeft_X_none, Polynomial.eval_X]

omit [Finite ι] in
theorem projectivePolynomialDehomogenization_some (i : ι) :
    projectivePolynomialDehomogenization k ι (MvPolynomial.X (some i)) = MvPolynomial.X i := by
  change Polynomial.eval 1 (MvPolynomial.optionEquivLeft k ι (MvPolynomial.X (some i))) = _
  rw [MvPolynomial.optionEquivLeft_X_some, Polynomial.eval_C]

omit [Finite ι] in
theorem projectivePolynomialDehomogenization_C (c : k) :
    projectivePolynomialDehomogenization k ι (MvPolynomial.C c) = MvPolynomial.C c := by
  change Polynomial.eval 1 (MvPolynomial.optionEquivLeft k ι (MvPolynomial.C c)) = _
  rw [MvPolynomial.optionEquivLeft_C, Polynomial.eval_C]

/-- The actual denominator evaluates to the actual unit 1. -/
theorem projectivePolynomialDehomogenization_denominator_inverse :
    projectivePolynomialDehomogenization k ι
        (projectivePolynomialHomogenizingVariable k ι) * (1 : MvPolynomial ι k) = 1 := by
  rw [projectivePolynomialDehomogenization_none, mul_one]

/-- The actual ordinary-localization map exists by the actual unit denominator. -/
abbrev projectivePolynomialChartLocalizationMap :
    Localization.Away (projectivePolynomialHomogenizingVariable k ι) →+* MvPolynomial ι k :=
  Localization.awayLift (projectivePolynomialDehomogenization k ι)
    (projectivePolynomialHomogenizingVariable k ι)
    (isUnit_iff_exists_inv.mpr
      ⟨1, projectivePolynomialDehomogenization_denominator_inverse k ι⟩)

/-- The chart map is the actual homogeneous-localization inclusion
followed by the actual localization lift. -/
def projectivePolynomialChartMap : projectivePolynomialChartRing k ι →+* MvPolynomial ι k :=
  (projectivePolynomialChartLocalizationMap k ι).comp
    (algebraMap (projectivePolynomialChartRing k ι)
      (Localization.Away (projectivePolynomialHomogenizingVariable k ι)))

/-- Genuine homogeneous fractions dehomogenize to their genuine numerators,
because the actual homogenizing denominator becomes 1. -/
theorem projectivePolynomialChartMap_mk (n : ℕ) (p : MvPolynomial (Option ι) k)
    (hp : p ∈ projectivePolynomialGrading k (Option ι) (n • (1 : ℕ))) :
    projectivePolynomialChartMap k ι
      (HomogeneousLocalization.Away.mk (projectivePolynomialGrading k (Option ι))
        (MvPolynomial.isHomogeneous_X k none) n p hp) =
      projectivePolynomialDehomogenization k ι p := by
  change projectivePolynomialChartLocalizationMap k ι
    (HomogeneousLocalization.Away.mk (projectivePolynomialGrading k (Option ι))
      (MvPolynomial.isHomogeneous_X k none) n p hp).val = _
  rw [HomogeneousLocalization.Away.val_mk]
  simpa only [one_pow, mul_one] using
    (Localization.awayLift_mk (projectivePolynomialDehomogenization k ι)
      (projectivePolynomialHomogenizingVariable k ι) p 1
      (projectivePolynomialDehomogenization_denominator_inverse k ι) n)

/-- The original base scalar map into the actual chart ring. -/
def projectivePolynomialChartScalarHom : k →+* projectivePolynomialChartRing k ι :=
  (HomogeneousLocalization.fromZeroRingHom (projectivePolynomialGrading k (Option ι))
    (Submonoid.powers (projectivePolynomialHomogenizingVariable k ι))).comp
      (projectivePolynomialGradeZeroHom k (Option ι))

/-- The original variable is represented by its actual degree-zero fraction Xi/Z0. -/
def projectivePolynomialChartCoordinate (i : ι) : projectivePolynomialChartRing k ι :=
  HomogeneousLocalization.Away.mk (projectivePolynomialGrading k (Option ι))
    (MvPolynomial.isHomogeneous_X k none) 1 (MvPolynomial.X (some i))
    (by simpa using (MvPolynomial.isHomogeneous_X k (some i)))

theorem projectivePolynomialChartMap_scalar (c : k) :
    projectivePolynomialChartMap k ι (projectivePolynomialChartScalarHom k ι c) =
      MvPolynomial.C c := by
  change projectivePolynomialChartMap k ι
    (HomogeneousLocalization.Away.mk (projectivePolynomialGrading k (Option ι))
      (MvPolynomial.isHomogeneous_X k none) 0 (MvPolynomial.C c)
      (MvPolynomial.isHomogeneous_C (Option ι) c)) = _
  rw [projectivePolynomialChartMap_mk, projectivePolynomialDehomogenization_C]

theorem projectivePolynomialChartMap_coordinate (i : ι) :
    projectivePolynomialChartMap k ι (projectivePolynomialChartCoordinate k ι i) =
      MvPolynomial.X i := by
  rw [projectivePolynomialChartCoordinate, projectivePolynomialChartMap_mk,
    projectivePolynomialDehomogenization_some]

/-- Actual homogeneous numerators have no hidden dehomogenization kernel. -/
theorem projectivePolynomialChartMap_injective :
    Function.Injective (projectivePolynomialChartMap k ι) := by
  intro x y hxy
  have hz : projectivePolynomialChartMap k ι (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨n, p, hp, hrep⟩ := HomogeneousLocalization.Away.mk_surjective
    (projectivePolynomialGrading k (Option ι)) (MvPolynomial.isHomogeneous_X k none) (x - y)
  rw [← hrep, projectivePolynomialChartMap_mk] at hz
  have hph : p.IsHomogeneous n := by simpa using hp
  have hpzero := (projectivePolynomialDehomogenization_eq_zero_iff k ι hph).mp hz
  have hfrac : HomogeneousLocalization.Away.mk (projectivePolynomialGrading k (Option ι))
      (MvPolynomial.isHomogeneous_X k none) n p hp = 0 := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk, hpzero, HomogeneousLocalization.val_zero]
    exact Localization.mk_zero _
  exact sub_eq_zero.mp (hrep ▸ hfrac)

/-- The inverse map is given by the original polynomial ring's actual
universal property, using the genuine scalar and coordinate fractions. -/
def projectivePolynomialChartInverse : MvPolynomial ι k →+* projectivePolynomialChartRing k ι :=
  MvPolynomial.eval₂Hom (projectivePolynomialChartScalarHom k ι)
    (projectivePolynomialChartCoordinate k ι)

theorem projectivePolynomialChartMap_comp_inverse :
    (projectivePolynomialChartMap k ι).comp (projectivePolynomialChartInverse k ι) =
      RingHom.id (MvPolynomial ι k) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change projectivePolynomialChartMap k ι
      (MvPolynomial.eval₂Hom (projectivePolynomialChartScalarHom k ι)
        (projectivePolynomialChartCoordinate k ι) (MvPolynomial.C c)) = MvPolynomial.C c
    rw [MvPolynomial.eval₂Hom_C, projectivePolynomialChartMap_scalar]
  · intro i
    change projectivePolynomialChartMap k ι
      (MvPolynomial.eval₂Hom (projectivePolynomialChartScalarHom k ι)
        (projectivePolynomialChartCoordinate k ι) (MvPolynomial.X i)) = MvPolynomial.X i
    rw [MvPolynomial.eval₂Hom_X', projectivePolynomialChartMap_coordinate]

/-- The actual standard chart ring and original coordinate ring are
actually equivalent; neither the equivalence nor its injectivity is assumed. -/
def projectivePolynomialChartEquiv :
    projectivePolynomialChartRing k ι ≃+* MvPolynomial ι k :=
  RingEquiv.ofBijective (projectivePolynomialChartMap k ι)
    ⟨projectivePolynomialChartMap_injective k ι,
      (show Function.RightInverse (projectivePolynomialChartInverse k ι)
        (projectivePolynomialChartMap k ι) from fun p =>
          RingHom.congr_fun (projectivePolynomialChartMap_comp_inverse k ι) p).surjective⟩

/-- The actual affine section ring comparison uses the native Proj
basic-open section isomorphism and the constructed chart equivalence. -/
def projectivePolynomialStandardSectionsEquiv :
    ((projectivePolynomialAmbient k (Option ι)).presheaf.obj
      (op (projectivePolynomialStandardOpen k (Option ι) none))) ≃+* MvPolynomial ι k :=
  ((Proj.basicOpenIsoAway (projectivePolynomialGrading k (Option ι))
    (projectivePolynomialHomogenizingVariable k ι) (MvPolynomial.isHomogeneous_X k none)
    Nat.zero_lt_one).commRingCatIsoToRingEquiv).symm.trans (projectivePolynomialChartEquiv k ι)

end

end ChenRanks
