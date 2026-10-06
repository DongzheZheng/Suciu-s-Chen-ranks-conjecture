import ChenRanks.TwicePuncturedWindingCupPrimitive
import ChenRanks.ArrangementSingularCupKernelContainment

/-!
# The actual original singular equation cup kernel

The explicit twice-punctured-plane primitive kills each original affine
parallel or dependent-triple boundary cup. The independently certified
opposite containment then identifies the actual native singular equation
cup kernel with the original rational logarithmic quadratic kernel.
The coefficient map is still the original equation-class map: no first
cohomology spanning or group Chen comparison is built into this identity.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

open SingularCohomology

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance cupKernelEqualityDecidableEq : DecidableEq ι := Classical.decEq ι

theorem parallelBoundaryCup_eq_zero (H K : ι) (c : ℂ)
    (hc : A.normal K = c • A.normal H) :
    A.equationQuadraticCup
      (exteriorWedge (k := ℂ) (Pi.single H 1) (Pi.single K 1)) = 0 := by
  by_cases hHK : H = K
  · subst K
    rw [A.equationQuadraticCup_exteriorWedge]
    exact cup_self_eq_zero ℂ A.Complement _
  · rw [A.parallelBoundaryCup_eq_actual_pullback H K hHK c hc,
      twicePuncturedWindingCup_eq_zero, map_zero]

theorem tripleBoundaryCup_eq_zero (H K L : ι) (a b : ℂ)
    (h : A.equationPolynomial L =
      a • A.equationPolynomial H + b • A.equationPolynomial K) :
    A.equationQuadraticCup (tripleBoundary H K L) = 0 := by
  by_cases hHL : H = L
  · rw [tripleBoundary_eq_zero_of_repeated H K L (Or.inr (Or.inl hHL)), map_zero]
  by_cases hKL : K = L
  · rw [tripleBoundary_eq_zero_of_repeated H K L (Or.inr (Or.inr hKL)), map_zero]
  rw [A.tripleBoundaryCup_eq_neg_actual_pullback H K L hHL hKL a b h,
    twicePuncturedWindingCup_eq_zero, map_zero, neg_zero]

theorem affineQuadraticEquationBoundarySpan_le_equationQuadraticCupKernel :
    A.affineQuadraticEquationBoundarySpan ≤ A.equationQuadraticCupKernel := by
  apply Submodule.span_le.mpr
  rintro z (hparallel | htriple)
  · obtain ⟨H, K, ⟨c, hc⟩, rfl⟩ := hparallel
    exact A.parallelBoundaryCup_eq_zero H K c hc
  · obtain ⟨H, K, L, hspan, rfl⟩ := htriple
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hspan
    exact A.tripleBoundaryCup_eq_zero H K L a b hab.symm

theorem equationQuadraticCupKernel_eq_affineQuadraticEquationBoundarySpan :
    A.equationQuadraticCupKernel = A.affineQuadraticEquationBoundarySpan :=
  le_antisymm A.equationQuadraticCupKernel_le_affineQuadraticEquationBoundarySpan
    A.affineQuadraticEquationBoundarySpan_le_equationQuadraticCupKernel

theorem equationQuadraticCupKernel_eq_rationalQuadraticKernel :
    A.equationQuadraticCupKernel = A.rationalQuadraticKernel := by
  rw [A.rationalQuadraticKernel_eq_affineQuadraticEquationBoundarySpan,
    A.equationQuadraticCupKernel_eq_affineQuadraticEquationBoundarySpan]

end ChenRanks.AffineArrangement
