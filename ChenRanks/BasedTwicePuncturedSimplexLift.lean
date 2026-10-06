import ChenRanks.PhaseGridClosingPaths

/-!
# Genuine simplex lifts based at the selected principal argument

The original covering lift is normalized by its actual value at the
first vertex. Its exponential is unchanged, and its value at that vertex
is precisely the original principal argument. Applying this construction
to the actual phases of z and 1-z gives a continuous simplex in the
complement of the original period grid. No choice normalization or
simplex filling identity is an input.
-/

noncomputable section

open AlgebraicTopology unitInterval

namespace ChenRanks

def basedCircleSimplexArgumentLift (n : ℕ)
    (s : C(stdSimplex ℝ (Fin (n + 1)), Circle)) :
    C(stdSimplex ℝ (Fin (n + 1)), ℝ) where
  toFun x := circleSimplexArgumentLift n s x -
    circleSimplexArgumentLift n s (stdSimplex.vertex 0) +
      Complex.arg (s (stdSimplex.vertex 0) : ℂ)
  continuous_toFun :=
    ((circleSimplexArgumentLift n s).continuous.sub continuous_const).add continuous_const

theorem basedCircleSimplexArgumentLift_projects (n : ℕ)
    (s : C(stdSimplex ℝ (Fin (n + 1)), Circle))
    (x : stdSimplex ℝ (Fin (n + 1))) :
    Circle.exp (basedCircleSimplexArgumentLift n s x) = s x := by
  change Circle.exp (circleSimplexArgumentLift n s x -
    circleSimplexArgumentLift n s (stdSimplex.vertex 0) +
      Complex.arg (s (stdSimplex.vertex 0) : ℂ)) = s x
  rw [Circle.exp_add, Circle.exp_sub,
    circleSimplexArgumentLift_projects, circleSimplexArgumentLift_projects, Circle.exp_arg]
  exact div_mul_cancel _ _

@[simp] theorem basedCircleSimplexArgumentLift_vertex_zero (n : ℕ)
    (s : C(stdSimplex ℝ (Fin (n + 1)), Circle)) :
    basedCircleSimplexArgumentLift n s (stdSimplex.vertex 0) =
      Complex.arg (s (stdSimplex.vertex 0) : ℂ) := by
  simp only [basedCircleSimplexArgumentLift, ContinuousMap.coe_mk, sub_self, zero_add]

def basedTwicePuncturedSimplexArgumentPair (n : ℕ)
    (s : C(stdSimplex ℝ (Fin (n + 1)), TwicePuncturedComplex)) :
    C(stdSimplex ℝ (Fin (n + 1)), ℝ × ℝ) :=
  (basedCircleSimplexArgumentLift n (twicePuncturedComplexZeroPhase.comp s)).prodMk
    (basedCircleSimplexArgumentLift n (twicePuncturedComplexOnePhase.comp s))

theorem basedTwicePuncturedSimplexArgumentPair_not_mem_grid (n : ℕ)
    (s : C(stdSimplex ℝ (Fin (n + 1)), TwicePuncturedComplex))
    (x : stdSimplex ℝ (Fin (n + 1))) :
    basedTwicePuncturedSimplexArgumentPair n s x ∉ windingPhaseGrid :=
  twicePunctured_argumentPair_avoids_grid (s x) _ _
    (basedCircleSimplexArgumentLift_projects n (twicePuncturedComplexZeroPhase.comp s) x)
    (basedCircleSimplexArgumentLift_projects n (twicePuncturedComplexOnePhase.comp s) x)

def basedTwicePuncturedSimplexGridLift (n : ℕ)
    (s : C(stdSimplex ℝ (Fin (n + 1)), TwicePuncturedComplex)) :
    C(stdSimplex ℝ (Fin (n + 1)), PhaseGridComplement) where
  toFun x := ⟨basedTwicePuncturedSimplexArgumentPair n s x,
    basedTwicePuncturedSimplexArgumentPair_not_mem_grid n s x⟩
  continuous_toFun := (basedTwicePuncturedSimplexArgumentPair n s).continuous.subtype_mk _

theorem basedTwicePuncturedSimplexGridLift_projects (n : ℕ)
    (s : C(stdSimplex ℝ (Fin (n + 1)), TwicePuncturedComplex))
    (x : stdSimplex ℝ (Fin (n + 1))) :
    argumentPlanePhaseMap (basedTwicePuncturedSimplexGridLift n s x).val =
      twicePuncturedComplexPhasePair (s x) := by
  apply Prod.ext
  · exact basedCircleSimplexArgumentLift_projects n (twicePuncturedComplexZeroPhase.comp s) x
  · exact basedCircleSimplexArgumentLift_projects n (twicePuncturedComplexOnePhase.comp s) x

@[simp] theorem basedTwicePuncturedSimplexGridLift_vertex_zero (n : ℕ)
    (s : C(stdSimplex ℝ (Fin (n + 1)), TwicePuncturedComplex)) :
    basedTwicePuncturedSimplexGridLift n s (stdSimplex.vertex 0) =
      phaseGridPrincipalPoint (s (stdSimplex.vertex 0)) := by
  apply Subtype.ext
  apply Prod.ext <;>
    exact basedCircleSimplexArgumentLift_vertex_zero n _

end ChenRanks
