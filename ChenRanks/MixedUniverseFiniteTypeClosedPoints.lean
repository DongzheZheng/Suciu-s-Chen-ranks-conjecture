import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Actual scalar points of finite-type algebras in independent universes

A genuine maximal ideal supplies its actual quotient field. Zariski's
lemma makes that quotient finite over the original base field, and the
native algebraically-closed-field lift produces a scalar-compatible map
to the original base. Injectivity of the quotient-field map proves that
the original maximal ideal is exactly its actual kernel.

No point, field isomorphism, kernel comparison, or common universe is an
input. This pure ring argument avoids a scalar Scheme morphism between
rings belonging to different universe levels.
-/

noncomputable section

namespace ChenRanks

variable {k R : Type*} [Field k] [IsAlgClosed k] [CommRing R]
  [Algebra k R] [Algebra.FiniteType k R]

/-- Every genuine maximal ideal of the original finite-type algebra is
the kernel of an actual base-field algebra map. -/
theorem finiteType_maximalIdeal_exists_scalar_point
    (m : Ideal R) (hm : m.IsMaximal) :
    ∃ a : R →ₐ[k] k, RingHom.ker a.toRingHom = m := by
  letI : m.IsMaximal := hm
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  letI : Module.Finite k (R ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  let f : (R ⧸ m) →ₐ[k] k := IsAlgClosed.lift
  let a : R →ₐ[k] k := f.comp (Ideal.Quotient.mkₐ k m)
  refine ⟨a, ?_⟩
  apply Ideal.ext
  intro r
  change f (Ideal.Quotient.mk m r) = 0 ↔ r ∈ m
  have hf : Function.Injective f := RingHom.injective f.toRingHom
  constructor
  · intro hr
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hf (hr.trans f.map_zero.symm))
  · intro hr
    exact (congrArg f (Ideal.Quotient.eq_zero_iff_mem.mpr hr)).trans f.map_zero

end ChenRanks
