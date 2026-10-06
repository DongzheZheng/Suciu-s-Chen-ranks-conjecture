import ChenRanks.KoszulFunctoriality
import ChenRanks.KoszulQuotientGrading

/-!
# Genuine degreewise canonical Koszul maps

The symmetric-algebra map preserves actual homogeneous polynomial spaces:
in monomial coordinates it is evaluation at actual degree-one generators.
Consequently the original quotient map carries actual homogeneous images
into actual homogeneous images. The degreewise map is transported through
the previously proved equivalences with those original images.

This proves actual grading compatibility of the canonical maps in the
paper. It does not assert their eventual bijectivity or effective range.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V W : Type*) [AddCommGroup V] [AddCommGroup W]
  [_root_.Module k V] [_root_.Module k W]
variable {ι τ : Type*} [Fintype ι] [Fintype τ]
  (b : _root_.Module.Basis ι k V) (c : _root_.Module.Basis τ k W)
  (f : V →ₗ[k] W)

omit [Fintype ι] [Fintype τ] in
/-- The actual map of symmetric algebras is actual polynomial substitution
in the original basis coordinates. -/
theorem symmetricMap_polynomialCoordinates :
    ((SymmetricAlgebra.equivMvPolynomial c).toAlgHom.comp
      (symmetricMap k V W f)).comp
        (SymmetricAlgebra.equivMvPolynomial b).symm.toAlgHom =
      MvPolynomial.aeval (fun i ↦ SymmetricAlgebra.equivMvPolynomial c
        (SymmetricAlgebra.ι k W (f (b i)))) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp

omit [Fintype ι] in
/-- Actual homogeneous coefficients keep their actual degree. -/
theorem symmetricMap_homogeneous (n : ℕ) (s : S k V)
    (hs : s ∈ homogeneousS k V b n) :
    symmetricMap k V W f s ∈ homogeneousS k W c n := by
  have hp := (mem_homogeneousS k V b n s).mp hs
  have heval := hp.aeval
    (fun i ↦ SymmetricAlgebra.equivMvPolynomial c (SymmetricAlgebra.ι k W (f (b i))))
    (fun i ↦ (mem_homogeneousS k W c 1 _).mp (homogeneousS_ι k W c (f (b i))))
  rw [← symmetricMap_polynomialCoordinates k V W b c f] at heval
  apply (mem_homogeneousS k W c n _).mpr
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply,
    one_mul] using heval

omit [Fintype ι] in
/-- The actual first tensor map carries each actual coefficient degree
into the same actual coefficient degree. -/
theorem tensorOneMap_homogeneous (n : ℕ) :
    c1Degree k V b n ≤ (c1Degree k W c n).comap (tensorOneMap k V W f) := by
  apply Submodule.span_le.mpr
  rintro z ⟨s, hs, v, rfl⟩
  exact tmul_mem_tensorHomogeneous k W c W n _
    (symmetricMap_homogeneous k V W b c f n s hs) (f v)

/-- Actual degreewise cycles are mapped to actual degreewise cycles. -/
def homogeneousCycleMap (r : ℕ) : cycleDegree k V b r →ₗ[k] cycleDegree k W c r :=
  ((tensorOneMap k V W f).comp (cycleDegree k V b r).subtype).codRestrict
    (cycleDegree k W c r) (fun z ↦ ⟨tensorOneMap_homogeneous k V W b c f (r + 1) z.property.1,
      by
        apply LinearMap.mem_ker.mpr
        change delta1 k W (tensorOneMap k V W f z.val) = 0
        have hz : delta1 k V z.val = 0 := LinearMap.mem_ker.mp z.property.2
        rw [delta1_tensorOneMap, hz, map_zero]⟩)

variable (K : Submodule k (⋀[k]^2 V)) (L : Submodule k (⋀[k]^2 W))

omit [Fintype ι] in
/-- Actual homogeneous quotient images are preserved by the original map. -/
theorem moduleMap_originalDegree_mem
    (h : K ≤ L.comap (exteriorPower.map 2 f)) (r : ℕ)
    (z : Module k V K) (hz : z ∈ LinearMap.range (degreeCycleToUngraded k V b K r)) :
    moduleMap k V W f K L h z ∈
      LinearMap.range (degreeCycleToUngraded k W c L r) := by
  obtain ⟨t, rfl⟩ := hz
  refine ⟨homogeneousCycleMap k V W b c f r t, ?_⟩
  change Submodule.Quotient.mk
      (degreeCycleInclusion k W c r (homogeneousCycleMap k V W b c f r t)) =
    moduleMap k V W f K L h (Submodule.Quotient.mk (degreeCycleInclusion k V b r t))
  rw [moduleMap_mk]
  rfl

/-- The constructed original quotient map restricted to its genuine
homogeneous images. -/
def originalDegreeMap (h : K ≤ L.comap (exteriorPower.map 2 f)) (r : ℕ) :
    LinearMap.range (degreeCycleToUngraded k V b K r) →ₗ[k]
      LinearMap.range (degreeCycleToUngraded k W c L r) :=
  ((moduleMap k V W f K L h).comp
    (LinearMap.range (degreeCycleToUngraded k V b K r)).subtype).codRestrict
      (LinearMap.range (degreeCycleToUngraded k W c L r))
      (fun z ↦ moduleMap_originalDegree_mem k V W b c f K L h r z.val z.property)

/-- The actual degreewise quotient map, through the proved original-image
identifications. -/
def homogeneousModuleMap (h : K ≤ L.comap (exteriorPower.map 2 f)) (r : ℕ) :
    homogeneousModule k V b K r →ₗ[k] homogeneousModule k W c L r :=
  (homogeneousModuleEquivOriginalDegree k W c L r).symm.toLinearMap ∘ₗ
    originalDegreeMap k V W b c f K L h r ∘ₗ
      (homogeneousModuleEquivOriginalDegree k V b K r).toLinearMap

/-- The degreewise map commutes with the actual original quotient map. -/
theorem homogeneousModuleMap_originalDiagram
    (h : K ≤ L.comap (exteriorPower.map 2 f)) (r : ℕ)
    (z : homogeneousModule k V b K r) :
    ((homogeneousModuleEquivOriginalDegree k W c L r)
      (homogeneousModuleMap k V W b c f K L h r z) : Module k W L) =
      moduleMap k V W f K L h
        (homogeneousModuleEquivOriginalDegree k V b K r z) := by
  change ((homogeneousModuleEquivOriginalDegree k W c L r)
    ((homogeneousModuleEquivOriginalDegree k W c L r).symm
      (originalDegreeMap k V W b c f K L h r
        (homogeneousModuleEquivOriginalDegree k V b K r z)))).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The canonical map with actual image relations, in each actual degree. -/
def canonicalHomogeneousModuleMap (r : ℕ) :
    homogeneousModule k V b K r →ₗ[k]
      homogeneousModule k W c (quadraticImage k V W f K) r :=
  homogeneousModuleMap k V W b c f K (quadraticImage k V W f K)
    (quadraticImage_containment k V W f K) r

end ChenRanks.Koszul
