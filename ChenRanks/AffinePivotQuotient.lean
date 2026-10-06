import ChenRanks.ArrangementDivisors
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Data.Fintype.BigOperators

/-!
# Actual affine pivot restriction and hyperplane quotient

A distinguished coordinate is evaluated at the polynomial obtained by
solving the original affine hyperplane equation. The kernel is computed
from the genuine polynomial evaluation kernel. The original irreducible
hyperplane equation identifies that kernel with its actual principal
ideal. No quotient comparison or desired kernel equality is an input.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks

section Pivot

variable (k σ : Type*) [Field k] [DecidableEq σ]

/-- Separate one actual coordinate from all the other coordinates. -/
def affinePivotPolynomialEquiv (j : σ) :
    MvPolynomial σ k ≃ₐ[k] Polynomial (MvPolynomial {i : σ // i ≠ j} k) :=
  (MvPolynomial.renameEquiv k (Equiv.optionSubtypeNe j).symm).trans
    (MvPolynomial.optionEquivLeft k {i : σ // i ≠ j})

/-- Actual evaluation of the distinguished coordinate at `q`. -/
def affinePivotRestriction (j : σ) (q : MvPolynomial {i : σ // i ≠ j} k) :
    MvPolynomial σ k →ₐ[k] MvPolynomial {i : σ // i ≠ j} k :=
  ((Polynomial.aeval q).restrictScalars k).comp
    (affinePivotPolynomialEquiv k σ j).toAlgHom

/-- The actual graph equation of this polynomial coordinate evaluation. -/
def affinePivotGenerator (j : σ) (q : MvPolynomial {i : σ // i ≠ j} k) :
    MvPolynomial σ k :=
  (affinePivotPolynomialEquiv k σ j).symm (Polynomial.X - Polynomial.C q)

@[simp]
theorem affinePivotRestriction_C (j : σ)
    (q : MvPolynomial {i : σ // i ≠ j} k) (c : k) :
    affinePivotRestriction k σ j q (MvPolynomial.C c) = MvPolynomial.C c :=
  (affinePivotRestriction k σ j q).commutes c

@[simp]
theorem affinePivotRestriction_X_self (j : σ)
    (q : MvPolynomial {i : σ // i ≠ j} k) :
    affinePivotRestriction k σ j q (MvPolynomial.X j) = q := by
  simp [affinePivotRestriction, affinePivotPolynomialEquiv,
    MvPolynomial.renameEquiv_apply]

@[simp]
theorem affinePivotRestriction_X_other (j : σ)
    (q : MvPolynomial {i : σ // i ≠ j} k) (i : σ) (hi : i ≠ j) :
    affinePivotRestriction k σ j q (MvPolynomial.X i) = MvPolynomial.X ⟨i, hi⟩ := by
  simp [affinePivotRestriction, affinePivotPolynomialEquiv,
    MvPolynomial.renameEquiv_apply, Equiv.optionSubtypeNe_symm_of_ne hi]

/-- Surjectivity follows from the actual polynomial coordinate section. -/
theorem affinePivotRestriction_surjective (j : σ)
    (q : MvPolynomial {i : σ // i ≠ j} k) :
    Function.Surjective (affinePivotRestriction k σ j q) := by
  intro p
  refine ⟨(affinePivotPolynomialEquiv k σ j).symm (Polynomial.C p), ?_⟩
  simp [affinePivotRestriction]

/-- The actual evaluation kernel is its actual graph principal ideal. -/
theorem affinePivotRestriction_ker (j : σ)
    (q : MvPolynomial {i : σ // i ≠ j} k) :
    RingHom.ker (affinePivotRestriction k σ j q) =
      Ideal.span {affinePivotGenerator k σ j q} := by
  ext p
  change (affinePivotPolynomialEquiv k σ j p).eval q = 0 ↔
    p ∈ Ideal.span {affinePivotGenerator k σ j q}
  rw [Ideal.mem_span_singleton, ← map_dvd_iff (affinePivotPolynomialEquiv k σ j)]
  simp only [affinePivotGenerator, AlgEquiv.apply_symm_apply]
  exact Polynomial.dvd_iff_isRoot.symm

/-- A genuine evaluation graph equation is not a unit. -/
theorem affinePivotGenerator_not_isUnit (j : σ)
    (q : MvPolynomial {i : σ // i ≠ j} k) :
    ¬IsUnit (affinePivotGenerator k σ j q) := by
  intro hu
  have hz : affinePivotGenerator k σ j q ∈
      RingHom.ker (affinePivotRestriction k σ j q) := by
    rw [affinePivotRestriction_ker]
    exact Ideal.mem_span_singleton_self _
  change affinePivotRestriction k σ j q (affinePivotGenerator k σ j q) = 0 at hz
  have hm := hu.map (affinePivotRestriction k σ j q).toRingHom
  exact not_isUnit_zero (hz ▸ hm)

end Pivot

namespace AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The actual other-coordinate ring at the chosen original coordinate. -/
abbrev HyperplanePivotRing (j : Fin d) := MvPolynomial {i : Fin d // i ≠ j} ℂ

/-- The value of the pivot coordinate obtained by solving the original
hyperplane equation, in the actual other-coordinate polynomial ring. -/
def hyperplanePivotValue (H : ι) (j : Fin d) : HyperplanePivotRing j :=
  MvPolynomial.C ((A.normal H (Pi.single j 1))⁻¹) *
    (MvPolynomial.C (A.offset H) -
      ∑ i : {i : Fin d // i ≠ j},
        MvPolynomial.C (A.normal H (Pi.single i.1 1)) * MvPolynomial.X i)

/-- The actual original hyperplane restriction map. -/
def hyperplanePivotRestriction (H : ι) (j : Fin d) :
    CoordinateRing (d := d) →ₐ[ℂ] HyperplanePivotRing j :=
  affinePivotRestriction ℂ (Fin d) j (A.hyperplanePivotValue H j)

/-- A nonzero original normal actually has a usable pivot coordinate. -/
theorem exists_hyperplanePivot (H : ι) :
    ∃ j : Fin d, A.normal H (Pi.single j 1) ≠ 0 := by
  classical
  by_contra h
  have hc : ∀ j : Fin d, A.normal H (Pi.single j 1) = 0 :=
    fun j => not_not.mp ((not_exists.mp h) j)
  apply A.normal_ne_zero H
  apply LinearMap.ext
  intro x
  rw [A.normal_eq_coordinate_sum H x]
  simp [hc]

/-- Solving the equation makes the actual original equation vanish. -/
theorem hyperplanePivotRestriction_equation (H : ι) (j : Fin d)
    (hj : A.normal H (Pi.single j 1) ≠ 0) :
    A.hyperplanePivotRestriction H j (A.equationPolynomial H) = 0 := by
  classical
  simp only [hyperplanePivotRestriction, equationPolynomial, map_sub, map_sum, map_mul,
    affinePivotRestriction_C]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j]
  have hother (i : {i : Fin d // i ≠ j}) :
      affinePivotRestriction ℂ (Fin d) j (A.hyperplanePivotValue H j)
        (MvPolynomial.X i.1) = MvPolynomial.X i :=
    affinePivotRestriction_X_other ℂ (Fin d) j (A.hyperplanePivotValue H j) i.1 i.property
  simp only [affinePivotRestriction_X_self, hother]
  simp only [hyperplanePivotValue]
  rw [← mul_assoc, ← MvPolynomial.C_mul, mul_inv_cancel₀ hj, map_one, one_mul]
  ring

/-- The original principal hyperplane ideal, rather than an assumed
comparison ideal, is the actual coordinate restriction kernel. -/
theorem hyperplanePivotRestriction_ker (H : ι) (j : Fin d)
    (hj : A.normal H (Pi.single j 1) ≠ 0) :
    RingHom.ker (A.hyperplanePivotRestriction H j) = A.hyperplanePrimeIdeal H := by
  let q := A.hyperplanePivotValue H j
  let g := affinePivotGenerator ℂ (Fin d) j q
  have hdvd : g ∣ A.equationPolynomial H := by
    rw [← Ideal.mem_span_singleton, ← affinePivotRestriction_ker]
    exact A.hyperplanePivotRestriction_equation H j hj
  have ha : Associated (A.equationPolynomial H) g :=
    ((A.equationPolynomial_irreducible H).dvd_iff.mp hdvd).resolve_left
      (affinePivotGenerator_not_isUnit ℂ (Fin d) j q)
  ext p
  change p ∈ RingHom.ker (affinePivotRestriction ℂ (Fin d) j q) ↔
    p ∈ Ideal.span {A.equationPolynomial H}
  rw [affinePivotRestriction_ker, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  exact ha.symm.dvd_iff_dvd_left

/-- The actual quotient of the original coordinate ring by its actual
hyperplane ideal is the actual ring of the remaining coordinates. -/
def hyperplanePivotQuotientAlgEquiv (H : ι) (j : Fin d)
    (hj : A.normal H (Pi.single j 1) ≠ 0) :
    (CoordinateRing (d := d) ⧸ A.hyperplanePrimeIdeal H) ≃ₐ[ℂ] HyperplanePivotRing j :=
  (Ideal.quotientEquivAlgOfEq ℂ (A.hyperplanePivotRestriction_ker H j hj).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (affinePivotRestriction_surjective ℂ (Fin d) j (A.hyperplanePivotValue H j)))

@[simp]
theorem hyperplanePivotQuotientAlgEquiv_mk (H : ι) (j : Fin d)
    (hj : A.normal H (Pi.single j 1) ≠ 0) (p : CoordinateRing (d := d)) :
    A.hyperplanePivotQuotientAlgEquiv H j hj
      (Ideal.Quotient.mk (A.hyperplanePrimeIdeal H) p) =
      A.hyperplanePivotRestriction H j p := by
  simp [hyperplanePivotQuotientAlgEquiv]

end AffineArrangement

end ChenRanks
