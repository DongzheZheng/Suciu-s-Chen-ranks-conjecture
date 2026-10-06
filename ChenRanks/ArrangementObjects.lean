import ChenRanks.ChenObjects

/-!
# Actual complex affine arrangement complements

Hyperplanes are represented by nonzero complex linear equations.  The
`distinct` field requires their zero sets to differ, so the finite index
cardinality counts hyperplanes rather than repeated equations.

The complement is a subtype of complex affine space, and its group is the
actual fundamental group of that topological space.  Its Chen ranks use the
lower central quotients of the actual maximal metabelian quotient as defined
in `ChenObjects`; no rank formula is part of the definition.
-/

noncomputable section

namespace ChenRanks

/-- A finite complex affine hyperplane arrangement specified by nonzero
linear functionals and constants.  Nonzeroness ensures each equation is a
hyperplane; the normals are actual linear maps, rather than formal labels. -/
structure AffineArrangement (d : ℕ) (ι : Type*) [Fintype ι] where
  normal : ι → (Fin d → ℂ) →ₗ[ℂ] ℂ
  offset : ι → ℂ
  normal_ne_zero : ∀ i, normal i ≠ 0
  distinct : Pairwise fun i j ↦
    {x : Fin d → ℂ | normal i x = offset i} ≠
      {x : Fin d → ℂ | normal j x = offset j}

namespace AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The actual topological arrangement complement, with the induced
topology from complex affine space. -/
def Complement := {x : Fin d → ℂ // ∀ i, A.normal i x ≠ A.offset i}

instance : TopologicalSpace A.Complement := by
  unfold Complement
  infer_instance

/-- The actual fundamental group of the complement at a supplied basepoint. -/
abbrev complementGroup (x : A.Complement) := FundamentalGroup A.Complement x

/-- Actual rational Chen rank of an affine arrangement group in ordinary
Chen degree `k+1`.  There is no presumed resonance formula in this definition. -/
def chenRank (x : A.Complement) (k : ℕ) : Cardinal :=
  rationalChenRank (A.complementGroup x) k

end AffineArrangement

end ChenRanks
