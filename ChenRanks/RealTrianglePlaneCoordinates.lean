import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Actual plane coordinates of the real standard triangle

These maps are defined on the genuine standard simplex and actual
complex plane. Their inverse identities follow from the true
barycentric sum, and preserve actual affine segment parametrizations.
-/

noncomputable section

namespace ChenRanks

def realTrianglePlaneCoordinate (p : stdSimplex ℝ (Fin 3)) : ℂ :=
  (p 0 : ℂ) + (p 1 : ℂ) * Complex.I

def complexTriangleCoordinate (z : ℂ) (i : Fin 3) : ℝ :=
  if i = 0 then z.re else if i = 1 then z.im else 1 - z.re - z.im

@[simp] theorem complexTriangleCoordinate_zero (z : ℂ) :
    complexTriangleCoordinate z 0 = z.re := by simp [complexTriangleCoordinate]

@[simp] theorem complexTriangleCoordinate_one (z : ℂ) :
    complexTriangleCoordinate z 1 = z.im := by simp [complexTriangleCoordinate]

@[simp] theorem complexTriangleCoordinate_two (z : ℂ) :
    complexTriangleCoordinate z 2 = 1 - z.re - z.im := by
  simp [complexTriangleCoordinate]

theorem complexTriangleCoordinate_continuous (i : Fin 3) :
    Continuous (fun z : ℂ => complexTriangleCoordinate z i) := by
  fin_cases i
  · change Continuous Complex.re
    exact Complex.continuous_re
  · change Continuous Complex.im
    exact Complex.continuous_im
  · change Continuous (fun z : ℂ => 1 - z.re - z.im)
    exact (continuous_const.sub Complex.continuous_re).sub Complex.continuous_im

@[simp] theorem complexTriangleCoordinate_sum (z : ℂ) :
    (∑ i : Fin 3, complexTriangleCoordinate z i) = 1 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change z.re + (z.im + (1 - z.re - z.im)) = 1
  ring

theorem complexTriangleCoordinate_plane (p : stdSimplex ℝ (Fin 3)) (i : Fin 3) :
    complexTriangleCoordinate (realTrianglePlaneCoordinate p) i = p i := by
  have hs := p.property.2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change p 0 + (p 1 + p 2) = 1 at hs
  fin_cases i
  · simp [complexTriangleCoordinate, realTrianglePlaneCoordinate]
  · simp [complexTriangleCoordinate, realTrianglePlaneCoordinate]
  · change 1 - (realTrianglePlaneCoordinate p).re -
      (realTrianglePlaneCoordinate p).im = p 2
    simp only [realTrianglePlaneCoordinate, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      mul_zero, zero_mul, sub_zero, Complex.add_im, Complex.mul_im,
      mul_one, zero_add, add_zero]
    linarith

theorem realTrianglePlaneCoordinate_injective :
    Function.Injective realTrianglePlaneCoordinate := by
  intro p q h
  apply Subtype.ext
  funext i
  change p i = q i
  rw [← complexTriangleCoordinate_plane p i, ← complexTriangleCoordinate_plane q i, h]

def realTrianglePointOfPlane (z : ℂ)
    (hz : ∀ i : Fin 3, 0 ≤ complexTriangleCoordinate z i) :
    stdSimplex ℝ (Fin 3) :=
  ⟨complexTriangleCoordinate z, hz, complexTriangleCoordinate_sum z⟩

@[simp] theorem realTrianglePlaneCoordinate_pointOfPlane (z : ℂ)
    (hz : ∀ i : Fin 3, 0 ≤ complexTriangleCoordinate z i) :
    realTrianglePlaneCoordinate (realTrianglePointOfPlane z hz) = z := by
  change (complexTriangleCoordinate z 0 : ℂ) +
    (complexTriangleCoordinate z 1 : ℂ) * Complex.I = z
  apply Complex.ext <;> simp [complexTriangleCoordinate]

/-- Both actual plane coordinates vary affinely on the literal real
segment. The affine third coordinate is included. -/
theorem complexTriangleCoordinate_affine (a b : ℂ) (t : ℝ) (i : Fin 3) :
    complexTriangleCoordinate ((1 - t) • a + t • b) i =
      (1 - t) * complexTriangleCoordinate a i + t * complexTriangleCoordinate b i := by
  fin_cases i
  · change ((1 - t) • a + t • b).re = (1 - t) * a.re + t * b.re
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  · change ((1 - t) • a + t • b).im = (1 - t) * a.im + t * b.im
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  · change 1 - ((1 - t) • a + t • b).re - ((1 - t) • a + t • b).im =
      (1 - t) * (1 - a.re - a.im) + t * (1 - b.re - b.im)
    simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
      smul_eq_mul]
    ring

end ChenRanks
