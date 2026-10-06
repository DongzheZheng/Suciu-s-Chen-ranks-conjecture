import ChenRanks.ArrangementSingularCupEquationSpanRows
import ChenRanks.AffineQuadraticKernel

/-!
# Actual singular cup relations are actual logarithmic relations

The genuine native cup relation supplies all original affine block-row
conditions, using constructed original incidence points and cycles.
The independently proved actual coordinate-block converse puts it in
the independently defined affine equation boundary span, and hence in
the actual rational logarithmic kernel.

Only this inclusion is proved here. The reverse singular-cup inclusion,
H¹ spanning and group comparisons remain separate obligations.
-/

noncomputable section
namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- Actual native cup relations satisfy the independent original
affine equation boundaries, with every block condition internally proved. -/
theorem equationQuadraticCupKernel_le_affineQuadraticEquationBoundarySpan :
    A.equationQuadraticCupKernel ≤ A.affineQuadraticEquationBoundarySpan := by
  intro z hz
  apply A.affineQuadraticEquationBoundarySpan_mem_of_block_row_relations z
  intro X hX H hH
  exact A.equationQuadraticCupKernel_equation_span_coordinate_row_sum_zero
    z hz X.val hX H hH

/-- The genuine singular coefficient cup kernel is contained in the
actual rational logarithmic kernel, without a kernel-comparison premise. -/
theorem equationQuadraticCupKernel_le_rationalQuadraticKernel :
    A.equationQuadraticCupKernel ≤ A.rationalQuadraticKernel :=
  A.equationQuadraticCupKernel_le_affineQuadraticEquationBoundarySpan.trans
    A.affineQuadraticEquationBoundarySpan_le_rationalQuadraticKernel

end ChenRanks.AffineArrangement
