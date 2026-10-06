import ChenRanks.GroupAlgebraAugmentationCotangentDual
import ChenRanks.ArrangementFieldSingularH1
import ChenRanks.CharactersSingularFirstCohomology

/-! The actual original arrangement group's augmentation cotangent is
finite dimensional over the original coefficient field. Its genuine
dual is identified with the actual equation coefficients through native
singular H1 and original group characters. The dimension is proved from
these equivalences, not assumed. This remains a first-order assertion,
not the higher Chen/holonomy comparison in the manuscript.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

open SingularCohomology

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (k : Type) [Field k]

local instance actualCotangentArrangementConnected : PathConnectedSpace A.Complement :=
  A.complement_pathConnectedSpace_from_actual_equations

/-- The original group-algebra cotangent dual, actual native H1 and
the original equation-coefficient vector space are genuinely identified. -/
def actualGroupCotangentDualEquationCoefficients (base : A.Complement) :
    Module.Dual k (GroupAlgebra.augmentationCotangent k
      (FundamentalGroup A.Complement base)) ≃ₗ[k] (ι → k) :=
  (GroupAlgebra.augmentationCotangentDualCharacters k
      (FundamentalGroup A.Complement base)).trans
    ((firstCohomologyCharactersEquiv A.Complement k base).symm.trans
      (A.fieldEquationClassEquiv k).symm)

instance actualGroupCotangentDual_finiteDimensional (base : A.Complement) :
    FiniteDimensional k (Module.Dual k (GroupAlgebra.augmentationCotangent k
      (FundamentalGroup A.Complement base))) :=
  FiniteDimensional.of_injective
    (A.actualGroupCotangentDualEquationCoefficients k base).toLinearMap
    (A.actualGroupCotangentDualEquationCoefficients k base).injective

/-- Genuine cotangent finiteness follows from its actual dual, without
assuming finite generation of the original fundamental group. -/
instance actualGroupCotangent_finiteDimensional (base : A.Complement) :
    FiniteDimensional k (GroupAlgebra.augmentationCotangent k
      (FundamentalGroup A.Complement base)) := by
  letI : Module.Free k (GroupAlgebra.augmentationCotangent k
      (FundamentalGroup A.Complement base)) :=
    Module.Free.of_divisionRing k _
  exact (Module.finite_dual_iff k).mp inferInstance

/-- The actual original augmentation degree one has one dimension per
original hyperplane, over Q as well as C. -/
theorem actualGroupCotangent_finrank (base : A.Complement) :
    Module.finrank k (GroupAlgebra.augmentationCotangent k
      (FundamentalGroup A.Complement base)) = Fintype.card ι := by
  rw [← Subspace.dual_finrank_eq]
  rw [(A.actualGroupCotangentDualEquationCoefficients k base).finrank_eq]
  simp

end ChenRanks.AffineArrangement
