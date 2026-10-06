import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.FiniteType

/-!
# The actual proper projective ambient over the original field

The ambient scheme is the native Proj of the original multivariable
polynomial ring with its actual homogeneous-degree grading.  Its degree
zero ring is proved equivalent to the original field by the actual
constant polynomial and constant-coefficient maps.  Native Proj
properness is then applied to its actual degree-zero structure morphism.
This file does not yet identify its standard affine chart with the
original arrangement coordinate ring or compare their function fields.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

variable (k ι : Type u) [Field k]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual standard degree grading of the actual polynomial ring. -/
abbrev projectivePolynomialGrading : ℕ → Submodule k (MvPolynomial ι k) :=
  MvPolynomial.homogeneousSubmodule ι k

/-- The actual native projective polynomial ambient. -/
abbrev projectivePolynomialAmbient : Scheme.{u} :=
  Proj (projectivePolynomialGrading k ι)

/-- Original scalars are actual constant homogeneous polynomials. -/
def projectivePolynomialGradeZeroHom : k →+* projectivePolynomialGrading k ι 0 where
  toFun c := ⟨MvPolynomial.C c, MvPolynomial.isHomogeneous_C ι c⟩
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_add' a b := Subtype.ext (map_add MvPolynomial.C a b)
  map_mul' a b := Subtype.ext (map_mul MvPolynomial.C a b)

theorem projectivePolynomialGradeZeroHom_bijective :
    Function.Bijective (projectivePolynomialGradeZeroHom k ι) := by
  constructor
  · intro a b hab
    have h := congrArg (fun p : projectivePolynomialGrading k ι 0 =>
      MvPolynomial.constantCoeff (p : MvPolynomial ι k)) hab
    simpa only [projectivePolynomialGradeZeroHom, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, MvPolynomial.constantCoeff_C] using h
  · intro p
    refine ⟨MvPolynomial.constantCoeff (p : MvPolynomial ι k), Subtype.ext ?_⟩
    have hd : (p : MvPolynomial ι k).totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous ι).mpr p.property
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd).symm

/-- The actual degree-zero ring comparison is constructed, not supplied. -/
def projectivePolynomialGradeZeroEquiv :
    k ≃+* projectivePolynomialGrading k ι 0 :=
  RingEquiv.ofBijective (projectivePolynomialGradeZeroHom k ι)
    (projectivePolynomialGradeZeroHom_bijective k ι)

@[simp]
theorem projectivePolynomialGradeZeroEquiv_coe (c : k) :
    (projectivePolynomialGradeZeroEquiv k ι c : MvPolynomial ι k) = MvPolynomial.C c :=
  rfl

variable [Finite ι]

/-- Actual polynomial finite type descends to the actual degree-zero
base action, because its composition with the actual scalar comparison
is exactly the original constant-polynomial action. -/
instance projectivePolynomial_finiteType_gradeZero :
    Algebra.FiniteType (projectivePolynomialGrading k ι 0) (MvPolynomial ι k) := by
  have hC : (MvPolynomial.C : k →+* MvPolynomial ι k).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  have hcomp : (algebraMap (projectivePolynomialGrading k ι 0) (MvPolynomial ι k)).comp
      (projectivePolynomialGradeZeroEquiv k ι).toRingHom = MvPolynomial.C := by
    ext c
    rfl
  apply RingHom.finiteType_algebraMap.mp
  apply RingHom.FiniteType.of_comp_finiteType
    (f := (projectivePolynomialGradeZeroEquiv k ι).toRingHom)
  rwa [hcomp]

/-- The actual original-field structure map of the actual projective
ambient, using the proved degree-zero comparison. -/
def projectivePolynomialScalarMorphism :
    projectivePolynomialAmbient k ι ⟶ Spec (.of k) :=
  Proj.toSpecZero (projectivePolynomialGrading k ι) ≫
    Spec.map ((projectivePolynomialGradeZeroEquiv k ι).toCommRingCatIso).hom

/-- Actual properness is derived from the native polynomial Proj and the
actual degree-zero isomorphism; no proper ambient is an input. -/
instance projectivePolynomialScalarMorphism_isProper :
    IsProper (projectivePolynomialScalarMorphism k ι) := by
  let e := (projectivePolynomialGradeZeroEquiv k ι).toCommRingCatIso
  letI : IsIso e.hom := e.isIso_hom
  letI : IsIso (Spec.map e.hom) := inferInstance
  letI : IsProper (Spec.map e.hom) := MorphismProperty.of_isIso @IsProper (Spec.map e.hom)
  letI : IsProper (Proj.toSpecZero (projectivePolynomialGrading k ι)) := inferInstance
  change IsProper (Proj.toSpecZero (projectivePolynomialGrading k ι) ≫ Spec.map e.hom)
  infer_instance

end

end ChenRanks
