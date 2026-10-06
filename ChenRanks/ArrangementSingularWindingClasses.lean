import ChenRanks.ArrangementEquationPhaseMaps
import ChenRanks.CircleSingularWindingCocycle
import ChenRanks.SingularCocycleFunctoriality

/-!
# Genuine singular winding classes of the original hyperplane equations

Each class is actual singular pullback of the actual integer winding
cocycle along the actual nonvanishing equation's circle map. Its cochain
values are true winding integers of the image singular paths. The
coefficient-space map is only constructed here: completeness,
independence, and logarithmic quadratic-kernel comparison are separate
proof obligations and are not part of its definition.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks.AffineArrangement

open SingularCohomology

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The original equation's genuine winding class in actual singular cohomology. -/
def equationWindingClass (k : Type) [Field k] (H : ι) :
    cohomology k A.Complement 1 :=
  cohomologyPullback k (A.equationComplementCircleMap H) 1 (circleWindingClass k)

/-- A genuine native cocycle representative for that original equation class. -/
def equationWindingCocycle (k : Type) [Field k] (H : ι) :
    cocycles k A.Complement 1 :=
  cocyclePullback k (A.equationComplementCircleMap H) 1 (circleWindingCocycle k)

theorem equationWindingClass_eq_cocycleClass (k : Type) [Field k] (H : ι) :
    A.equationWindingClass k H =
      cocycleClass k A.Complement 1 (A.equationWindingCocycle k H) :=
  cohomologyPullback_cocycleClass k (A.equationComplementCircleMap H) 1
    (circleWindingCocycle k)

/-- The values are the true integers of the true image paths of the original simplices. -/
theorem equationWindingCocycle_values (k : Type) [Field k] (H : ι)
    (s : simplices A.Complement 1) :
    values k A.Complement 1
        (cocycleCochain k A.Complement 1 (A.equationWindingCocycle k H)) s =
      (circleWindingValue (simplexMap (A.equationComplementCircleMap H) 1 s) : k) := by
  rw [equationWindingCocycle, cocycleCochain_cocyclePullback,
    values_cochainPullback]
  exact values_circleWindingCochain k
    (simplexMap (A.equationComplementCircleMap H) 1 s)

/-- The genuine coefficient-space map to the original complex first cohomology.
It is not defined as an equivalence or assumed to be surjective. -/
def equationWindingClassMap : (ι → ℂ) →ₗ[ℂ] A.singularH1 where
  toFun a := ∑ H, a H • A.equationWindingClass ℂ H
  map_add' a b := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul]

end ChenRanks.AffineArrangement
