import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# The actual polynomial adjoint action on an actual metabelian derived ideal

The acted-on module is the native first derived ideal of a genuine Lie
algebra. Its native adjoint operators commute when the native second
derived ideal is zero, as a consequence of Jacobi and ideal membership.
An actual tensor-algebra homomorphism therefore respects the original
`TensorAlgebra.SymRel`, and descends through the actual `RingQuot` defining
the symmetric algebra. The target endomorphism ring is not declared
commutative.

The structural metabelian condition in this general lemma must be proved
when it is applied to the actual quadratic metabelian free-Lie quotient.
No action, commuting-operator detector, or comparison is supplied as data.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k : Type*) [Field k]
variable (L : Type*) [LieRing L] [LieAlgebra k L]
variable (V : Type*) [AddCommGroup V] [Module k V]

/-- The original native derived ideal, with its original adjoint module structure. -/
abbrev ActualDerivedIdeal := LieAlgebra.derivedSeries k L 1

local instance actualDerivedLieRingModule : LieRingModule L (ActualDerivedIdeal k L) :=
  LieSubmodule.instLieRingModuleSubtypeMem (N := ActualDerivedIdeal k L)

local instance actualDerivedLieModule : LieModule k L (ActualDerivedIdeal k L) :=
  LieSubmodule.instLieModule (N := ActualDerivedIdeal k L)

/-- The actual adjoint generators, restricted to the actual derived ideal. -/
def adjointGeneratorMap (g : V →ₗ[k] L) :
    V →ₗ[k] Module.End k (ActualDerivedIdeal k L) :=
  (LieModule.toEnd k L (ActualDerivedIdeal k L)).toLinearMap.comp g

@[simp]
theorem adjointGeneratorMap_apply (g : V →ₗ[k] L) (u : V)
    (d : ActualDerivedIdeal k L) :
    adjointGeneratorMap k L V g u d = ⁅g u, d⁆ := rfl

/-- Jacobi and actual second-derived vanishing prove actual operator commutation. -/
theorem adjointGeneratorMap_mul_comm (g : V →ₗ[k] L)
    (hmetabelian : LieAlgebra.derivedSeries k L 2 = ⊥) (u v : V) :
    adjointGeneratorMap k L V g u * adjointGeneratorMap k L V g v =
      adjointGeneratorMap k L V g v * adjointGeneratorMap k L V g u := by
  apply LinearMap.ext
  intro d
  apply Subtype.ext
  change ⁅g u, ⁅g v, (d : L)⁆⁆ = ⁅g v, ⁅g u, (d : L)⁆⁆
  have huv : ⁅g u, g v⁆ ∈ ActualDerivedIdeal k L := by
    change ⁅g u, g v⁆ ∈ ⁅(⊤ : LieIdeal k L), ⊤⁆
    exact LieSubmodule.lie_mem_lie (show g u ∈ (⊤ : LieIdeal k L) from trivial)
      (show g v ∈ (⊤ : LieIdeal k L) from trivial)
  have hz : ⁅⁅g u, g v⁆, (d : L)⁆ = 0 := by
    have hm := LieSubmodule.lie_mem_lie huv d.property
    change ⁅⁅g u, g v⁆, (d : L)⁆ ∈ LieAlgebra.derivedSeries k L 2 at hm
    rw [hmetabelian, LieSubmodule.mem_bot] at hm
    exact hm
  rw [leibniz_lie, hz, zero_add]

/-- First extend the actual adjoint linear map to the actual tensor algebra. -/
def tensorAdjointAction (g : V →ₗ[k] L) :
    TensorAlgebra k V →ₐ[k] Module.End k (ActualDerivedIdeal k L) :=
  TensorAlgebra.lift k (adjointGeneratorMap k L V g)

theorem tensorAdjointAction_respectsSymRel (g : V →ₗ[k] L)
    (hmetabelian : LieAlgebra.derivedSeries k L 2 = ⊥)
    {x y : TensorAlgebra k V} (hxy : TensorAlgebra.SymRel k V x y) :
    tensorAdjointAction k L V g x = tensorAdjointAction k L V g y := by
  cases hxy with
  | mul_comm u v =>
    simp only [tensorAdjointAction, map_mul, TensorAlgebra.lift_ι_apply]
    exact adjointGeneratorMap_mul_comm k L V g hmetabelian u v

/-- The genuine symmetric-algebra action, descended through its defining quotient. -/
def symmetricAdjointAction (g : V →ₗ[k] L)
    (hmetabelian : LieAlgebra.derivedSeries k L 2 = ⊥) :
    SymmetricAlgebra k V →ₐ[k] Module.End k (ActualDerivedIdeal k L) :=
  RingQuot.liftAlgHom k
    ⟨tensorAdjointAction k L V g,
      fun {_ _} h => tensorAdjointAction_respectsSymRel k L V g hmetabelian h⟩

@[simp]
theorem symmetricAdjointAction_ι (g : V →ₗ[k] L)
    (hmetabelian : LieAlgebra.derivedSeries k L 2 = ⊥) (u : V) :
    symmetricAdjointAction k L V g hmetabelian (SymmetricAlgebra.ι k V u) =
      adjointGeneratorMap k L V g u := by
  change (RingQuot.liftAlgHom k
    ⟨tensorAdjointAction k L V g,
      fun {_ _} h => tensorAdjointAction_respectsSymRel k L V g hmetabelian h⟩)
      ((RingQuot.mkAlgHom k (TensorAlgebra.SymRel k V)) (TensorAlgebra.ι k u)) = _
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  exact TensorAlgebra.lift_ι_apply (adjointGeneratorMap k L V g) u

/-- The actual module structure induced by the constructed algebra homomorphism. -/
@[implicit_reducible]
def adjointSymmetricModule (g : V →ₗ[k] L)
    (hmetabelian : LieAlgebra.derivedSeries k L 2 = ⊥) :
    Module (SymmetricAlgebra k V) (ActualDerivedIdeal k L) :=
  Module.compHom (ActualDerivedIdeal k L)
    (symmetricAdjointAction k L V g hmetabelian).toRingHom

theorem adjointSymmetricModule_generator_smul (g : V →ₗ[k] L)
    (hmetabelian : LieAlgebra.derivedSeries k L 2 = ⊥) (u : V)
    (d : ActualDerivedIdeal k L) :
    letI := adjointSymmetricModule k L V g hmetabelian
    SymmetricAlgebra.ι k V u • d = ⁅g u, d⁆ := by
  letI := adjointSymmetricModule k L V g hmetabelian
  change symmetricAdjointAction k L V g hmetabelian (SymmetricAlgebra.ι k V u) d = _
  rw [symmetricAdjointAction_ι]
  rfl

theorem adjointSymmetricModule_scalarTower (g : V →ₗ[k] L)
    (hmetabelian : LieAlgebra.derivedSeries k L 2 = ⊥) :
    letI := adjointSymmetricModule k L V g hmetabelian
    IsScalarTower k (SymmetricAlgebra k V) (ActualDerivedIdeal k L) := by
  letI := adjointSymmetricModule k L V g hmetabelian
  constructor
  intro c s d
  change symmetricAdjointAction k L V g hmetabelian (c • s) d =
    c • (symmetricAdjointAction k L V g hmetabelian s d)
  rw [map_smul]
  rfl

theorem adjointSymmetricModule_smulCommClass (g : V →ₗ[k] L)
    (hmetabelian : LieAlgebra.derivedSeries k L 2 = ⊥) :
    letI := adjointSymmetricModule k L V g hmetabelian
    SMulCommClass k (SymmetricAlgebra k V) (ActualDerivedIdeal k L) := by
  letI := adjointSymmetricModule k L V g hmetabelian
  constructor
  intro c s d
  change c • (symmetricAdjointAction k L V g hmetabelian s d) =
    symmetricAdjointAction k L V g hmetabelian s (c • d)
  exact ((symmetricAdjointAction k L V g hmetabelian s).map_smul c d).symm

end ChenRanks.LieComparison
