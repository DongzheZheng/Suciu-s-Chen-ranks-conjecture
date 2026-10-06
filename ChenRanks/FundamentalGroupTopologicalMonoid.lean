import ChenRanks.FundamentalGroupProduct

/-!
# The actual identity fundamental group of a topological monoid

Continuous multiplication induces a homomorphism from the actual product
fundamental group. Its restrictions to the two factors are the identity,
as checked on the original loop representatives. The two factor subgroups
commute inside the original product, so the identity fundamental group
is abelian. This supplies the abelian factor needed by the manuscript's
central deconing reduction without assuming a cyclic-group comparison.
-/

noncomputable section

namespace ChenRanks

variable (T : Type*) [TopologicalSpace T] [Monoid T] [ContinuousMul T]

/-- The original continuous multiplication map. -/
def topologicalMonoidMultiplication : C(T × T, T) :=
  ⟨fun x ↦ x.1 * x.2, continuous_fst.mul continuous_snd⟩

/-- The actual induced fundamental-group homomorphism, transported only
by the already proved genuine product equivalence. -/
def fundamentalGroupMultiplicationMap :
    FundamentalGroup T (1 : T) × FundamentalGroup T (1 : T) →*
      FundamentalGroup T (1 : T) :=
  (FundamentalGroup.mapOfEq (topologicalMonoidMultiplication T)
    (show topologicalMonoidMultiplication T (1, 1) = (1 : T) by simp
      [topologicalMonoidMultiplication])).comp
    (fundamentalGroupProductEquiv T T 1 1).symm.toMonoidHom

/-- The original multiplication acts as the identity on the left loop
factor, proved on actual loop representatives. -/
theorem fundamentalGroupMultiplicationMap_left (p : FundamentalGroup T (1 : T)) :
    fundamentalGroupMultiplicationMap T (p, 1) = p := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    change FundamentalGroup.mapOfEq (topologicalMonoidMultiplication T)
      (show topologicalMonoidMultiplication T (1, 1) = (1 : T) by simp
        [topologicalMonoidMultiplication])
      (FundamentalGroup.fromPath (.mk (p.prod (Path.refl 1)))) =
        FundamentalGroup.fromPath (.mk p)
    rw [FundamentalGroup.mapOfEq_apply]
    congr 1
    congr 1
    ext t
    simp [topologicalMonoidMultiplication]

/-- The original multiplication acts as the identity on the right loop
factor, proved on actual loop representatives. -/
theorem fundamentalGroupMultiplicationMap_right (p : FundamentalGroup T (1 : T)) :
    fundamentalGroupMultiplicationMap T (1, p) = p := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    change FundamentalGroup.mapOfEq (topologicalMonoidMultiplication T)
      (show topologicalMonoidMultiplication T (1, 1) = (1 : T) by simp
        [topologicalMonoidMultiplication])
      (FundamentalGroup.fromPath (.mk ((Path.refl 1).prod p))) =
        FundamentalGroup.fromPath (.mk p)
    rw [FundamentalGroup.mapOfEq_apply]
    congr 1
    congr 1
    ext t
    simp [topologicalMonoidMultiplication]

/-- A homomorphism from the genuine product that restricts to the
identity on both factors forces commutativity of the original group. -/
theorem group_mul_comm_of_product_hom {M : Type*} [Group M]
    (f : M × M →* M) (hl : ∀ x, f (x, 1) = x) (hr : ∀ x, f (1, x) = x)
    (x y : M) : x * y = y * x := by
  have hp : ((x, 1) : M × M) * (1, y) = (1, y) * (x, 1) := by
    apply Prod.ext <;> simp
  have h := congrArg f hp
  simpa only [map_mul, hl, hr] using h

/-- The actual fundamental group at the identity is commutative. -/
instance fundamentalGroupIdentity_commGroup : CommGroup (FundamentalGroup T (1 : T)) :=
  { (inferInstance : Group (FundamentalGroup T (1 : T))) with
    mul_comm := group_mul_comm_of_product_hom (fundamentalGroupMultiplicationMap T)
      (fundamentalGroupMultiplicationMap_left T) (fundamentalGroupMultiplicationMap_right T) }

end ChenRanks
