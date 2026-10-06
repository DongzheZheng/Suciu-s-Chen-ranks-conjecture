import ChenRanks.ArrangementMeridianOtherWinding
import ChenRanks.ArrangementWindingEvaluation

/-!
# Independence of original singular equation classes

The meridians are constructed from the actual hyperplanes and lie in
the actual complement. Their genuine winding matrix is the identity.
Native cohomology evaluation therefore supplies an actual left inverse
of the actual equation-class map. Only independence is concluded; the
spanning theorem and logarithmic quadratic-kernel comparison remain
separate obligations.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.AffineArrangement

open SingularCohomology

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- Evaluation of actual native first cohomology on the actual constructed meridians. -/
def actualMeridianEvaluationMap : A.singularH1 →ₗ[ℂ] (ι → ℂ) :=
  LinearMap.pi (fun H => closedPathEvaluation ℂ A.Complement
    (A.meridianDiskPathMap H (A.actualMeridianDisk H))
    (A.meridianDiskPathMap_endpoints H (A.actualMeridianDisk H)))

/-- The genuine meridian evaluation matrix is the identity on original coefficients. -/
theorem actualMeridianEvaluationMap_equationWindingClassMap (a : ι → ℂ) :
    A.actualMeridianEvaluationMap (A.equationWindingClassMap a) = a := by
  classical
  funext H
  change closedPathEvaluation ℂ A.Complement
      (A.meridianDiskPathMap H (A.actualMeridianDisk H))
      (A.meridianDiskPathMap_endpoints H (A.actualMeridianDisk H))
      (A.equationWindingClassMap a) = a H
  rw [closedPathEvaluation_equationWindingClassMap]
  simp [A.actualMeridianPathMap_equation_increment]

/-- The original coefficient-space map to original singular H¹ is truly injective. -/
theorem equationWindingClassMap_injective : Function.Injective A.equationWindingClassMap :=
  (show Function.LeftInverse A.actualMeridianEvaluationMap A.equationWindingClassMap from
    A.actualMeridianEvaluationMap_equationWindingClassMap).injective

/-- The genuine constructed meridian evaluation map is truly surjective. -/
theorem actualMeridianEvaluationMap_surjective : Function.Surjective A.actualMeridianEvaluationMap := by
  intro a
  exact ⟨A.equationWindingClassMap a, A.actualMeridianEvaluationMap_equationWindingClassMap a⟩

end ChenRanks.AffineArrangement
