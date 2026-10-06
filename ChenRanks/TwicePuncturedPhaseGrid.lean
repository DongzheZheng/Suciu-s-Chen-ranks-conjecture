import ChenRanks.TwicePuncturedComplexMaps
import ChenRanks.CirclePathIntegerIncrement
import ChenRanks.CircleSimplexArgumentLift

/-!
# Actual phase-pair avoidance and actual argument lifts off the phase grid

The deleted circle point is the genuine value exp(π), with complex
coordinate -1. Two actual nonzero numbers z and 1-z cannot both have
this phase, since both would have negative real part. Consequently the
two genuine covering lifts of every original path or simplex avoid all
actual grid points (π+2πm, π+2πn).

No lattice-winding finite support or cochain primitive is asserted here.
-/

noncomputable section

open AlgebraicTopology unitInterval

namespace ChenRanks

/-- The actual deleted phase; its complex coordinate is precisely -1. -/
def windingPhaseCutPoint : Circle := Circle.exp Real.pi

@[simp] theorem windingPhaseCutPoint_coe : (windingPhaseCutPoint : ℂ) = -1 := by
  change Complex.exp ((Real.pi : ℂ) * Complex.I) = -1
  exact Complex.exp_pi_mul_I

@[simp] theorem windingPhaseCutPoint_arg :
    Complex.arg (windingPhaseCutPoint : ℂ) = Real.pi :=
  Circle.arg_exp (by linarith [Real.pi_pos]) le_rfl

/-- The actual nonzero-complex phase retains its actual principal argument. -/
theorem nonzeroComplexCircleMap_arg (z : NonzeroComplex) :
    Complex.arg (nonzeroComplexCircleMap z : ℂ) = Complex.arg (z : ℂ) := by
  change Complex.arg (Circle.exp (Complex.arg (z : ℂ)) : ℂ) = Complex.arg (z : ℂ)
  exact Circle.arg_exp (Complex.neg_pi_lt_arg _) (Complex.arg_le_pi _)

/-- The cut phase is exactly the actual negative real ray. -/
theorem nonzeroComplexCircleMap_eq_cut_iff (z : NonzeroComplex) :
    nonzeroComplexCircleMap z = windingPhaseCutPoint ↔
      (z : ℂ).re < 0 ∧ (z : ℂ).im = 0 := by
  constructor
  · intro h
    have ha := congrArg (fun w : Circle => Complex.arg (w : ℂ)) h
    change Complex.arg (nonzeroComplexCircleMap z : ℂ) =
      Complex.arg (windingPhaseCutPoint : ℂ) at ha
    rw [nonzeroComplexCircleMap_arg, windingPhaseCutPoint_arg] at ha
    exact Complex.arg_eq_pi_iff.mp ha
  · intro h
    change Circle.exp (Complex.arg (z : ℂ)) = Circle.exp Real.pi
    rw [Complex.arg_eq_pi_iff.mpr h]

/-- The actual pair of phases of z and 1-z. -/
def twicePuncturedComplexPhasePair : C(TwicePuncturedComplex, Circle × Circle) :=
  twicePuncturedComplexZeroPhase.prodMk twicePuncturedComplexOnePhase

/-- Its image avoids the actual deleted point (-1,-1), by the original
additive relation z+(1-z)=1. -/
theorem twicePuncturedComplexPhasePair_ne_cut (z : TwicePuncturedComplex) :
    twicePuncturedComplexPhasePair z ≠ (windingPhaseCutPoint, windingPhaseCutPoint) := by
  intro h
  have hzero := congrArg Prod.fst h
  have hone := congrArg Prod.snd h
  change nonzeroComplexCircleMap (twicePuncturedComplexZeroMap z) = windingPhaseCutPoint at hzero
  change nonzeroComplexCircleMap (twicePuncturedComplexOneMap z) = windingPhaseCutPoint at hone
  have hz := (nonzeroComplexCircleMap_eq_cut_iff (twicePuncturedComplexZeroMap z)).mp hzero
  have h1 := (nonzeroComplexCircleMap_eq_cut_iff (twicePuncturedComplexOneMap z)).mp hone
  change z.val.re < 0 ∧ z.val.im = 0 at hz
  change (1 - z.val).re < 0 ∧ (1 - z.val).im = 0 at h1
  simp only [Complex.sub_re, Complex.one_re] at h1
  linarith [hz.1, h1.1]

/-- The genuine period-grid point indexed by two integers. -/
def windingPhaseGridPoint (n : ℤ × ℤ) : ℝ × ℝ :=
  (Real.pi + (n.1 : ℝ) * (2 * Real.pi),
    Real.pi + (n.2 : ℝ) * (2 * Real.pi))

/-- The actual deleted grid in the real argument plane. -/
def windingPhaseGrid : Set (ℝ × ℝ) := Set.range windingPhaseGridPoint

/-- The actual product of the two original covering maps. -/
def argumentPlanePhaseMap : C(ℝ × ℝ, Circle × Circle) where
  toFun p := (Circle.exp p.1, Circle.exp p.2)
  continuous_toFun :=
    (Circle.exp.continuous.comp continuous_fst).prodMk
      (Circle.exp.continuous.comp continuous_snd)

/-- Every actual deleted grid point projects to the same actual cut pair. -/
@[simp] theorem argumentPlanePhaseMap_gridPoint (n : ℤ × ℤ) :
    argumentPlanePhaseMap (windingPhaseGridPoint n) =
      (windingPhaseCutPoint, windingPhaseCutPoint) := by
  change (Circle.exp (Real.pi + (n.1 : ℝ) * (2 * Real.pi)),
    Circle.exp (Real.pi + (n.2 : ℝ) * (2 * Real.pi))) =
      (Circle.exp Real.pi, Circle.exp Real.pi)
  simp only [Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]

/-- Any pair of genuine argument values of the same original point
avoids the actual grid. The next statements supply these values by the
proved covering lifts, rather than assuming existence of such lifts. -/
theorem twicePunctured_argumentPair_avoids_grid (z : TwicePuncturedComplex)
    (a b : ℝ) (ha : Circle.exp a = twicePuncturedComplexZeroPhase z)
    (hb : Circle.exp b = twicePuncturedComplexOnePhase z) :
    (a, b) ∉ windingPhaseGrid := by
  rintro ⟨n, hn⟩
  have hp := congrArg argumentPlanePhaseMap hn
  rw [argumentPlanePhaseMap_gridPoint] at hp
  change (windingPhaseCutPoint, windingPhaseCutPoint) = (Circle.exp a, Circle.exp b) at hp
  rw [ha, hb] at hp
  exact twicePuncturedComplexPhasePair_ne_cut z hp.symm

/-- The actual selected principal-argument pair at an actual point. -/
def twicePuncturedPrincipalArgumentPair (z : TwicePuncturedComplex) : ℝ × ℝ :=
  (Complex.arg (twicePuncturedComplexZeroPhase z : ℂ),
    Complex.arg (twicePuncturedComplexOnePhase z : ℂ))

theorem twicePuncturedPrincipalArgumentPair_not_mem_grid (z : TwicePuncturedComplex) :
    twicePuncturedPrincipalArgumentPair z ∉ windingPhaseGrid :=
  twicePunctured_argumentPair_avoids_grid z _ _ (Circle.exp_arg _) (Circle.exp_arg _)

theorem twicePuncturedPrincipalArgumentPair_bounds (z : TwicePuncturedComplex) :
    -Real.pi < (twicePuncturedPrincipalArgumentPair z).1 ∧
      (twicePuncturedPrincipalArgumentPair z).1 ≤ Real.pi ∧
      -Real.pi < (twicePuncturedPrincipalArgumentPair z).2 ∧
      (twicePuncturedPrincipalArgumentPair z).2 ≤ Real.pi :=
  ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _, Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩

/-- The actual two covering lifts of an actual original path. -/
def twicePuncturedPathArgumentPair (γ : C(I, TwicePuncturedComplex)) : C(I, ℝ × ℝ) :=
  (circlePathArgumentLift (twicePuncturedComplexZeroPhase.comp γ)).prodMk
    (circlePathArgumentLift (twicePuncturedComplexOnePhase.comp γ))

theorem twicePuncturedPathArgumentPair_not_mem_grid
    (γ : C(I, TwicePuncturedComplex)) (t : I) :
    twicePuncturedPathArgumentPair γ t ∉ windingPhaseGrid :=
  twicePunctured_argumentPair_avoids_grid (γ t) _ _
    (circlePathArgumentLift_projects (twicePuncturedComplexZeroPhase.comp γ) t)
    (circlePathArgumentLift_projects (twicePuncturedComplexOnePhase.comp γ) t)

/-- The same construction on an actual original geometric singular simplex. -/
def twicePuncturedSimplexArgumentPair (n : ℕ)
    (s : C(stdSimplex ℝ (Fin (n + 1)), TwicePuncturedComplex)) :
    C(stdSimplex ℝ (Fin (n + 1)), ℝ × ℝ) :=
  (circleSimplexArgumentLift n (twicePuncturedComplexZeroPhase.comp s)).prodMk
    (circleSimplexArgumentLift n (twicePuncturedComplexOnePhase.comp s))

theorem twicePuncturedSimplexArgumentPair_not_mem_grid (n : ℕ)
    (s : C(stdSimplex ℝ (Fin (n + 1)), TwicePuncturedComplex))
    (x : stdSimplex ℝ (Fin (n + 1))) :
    twicePuncturedSimplexArgumentPair n s x ∉ windingPhaseGrid :=
  twicePunctured_argumentPair_avoids_grid (s x) _ _
    (circleSimplexArgumentLift_projects n (twicePuncturedComplexZeroPhase.comp s) x)
    (circleSimplexArgumentLift_projects n (twicePuncturedComplexOnePhase.comp s) x)

end ChenRanks
