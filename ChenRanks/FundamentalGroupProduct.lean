import Mathlib

/-!
# Fundamental group of an actual topological product

The original homotopy classes of loops are projected and recombined by
the native path-product operations. Their proved inverse identities give
the actual fundamental-group product equivalence. No fundamental group
is replaced by a presentation chosen for this proof.

This supplies the product-functor part of the manuscript's central
arrangement reduction, before the actual deconing homeomorphism.
-/

noncomputable section

namespace ChenRanks

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual product fundamental group, with the original basepoints
and native loop-homotopy quotients retained. -/
def fundamentalGroupProductEquiv (x : X) (y : Y) :
    FundamentalGroup (X × Y) (x, y) ≃* FundamentalGroup X x × FundamentalGroup Y y where
  toFun p := (FundamentalGroup.fromPath (Path.Homotopic.projLeft p.toPath),
    FundamentalGroup.fromPath (Path.Homotopic.projRight p.toPath))
  invFun p := FundamentalGroup.fromPath (Path.Homotopic.prod p.1.toPath p.2.toPath)
  left_inv p := Path.Homotopic.prod_projLeft_projRight p.toPath
  right_inv p := Prod.ext (Path.Homotopic.projLeft_prod p.1.toPath p.2.toPath)
    (Path.Homotopic.projRight_prod p.1.toPath p.2.toPath)
  map_mul' p q := by
    apply Prod.ext
    · exact (FundamentalGroup.map (⟨Prod.fst, continuous_fst⟩ : C(X × Y, X))
        (x, y)).map_mul p q
    · exact (FundamentalGroup.map (⟨Prod.snd, continuous_snd⟩ : C(X × Y, Y))
        (x, y)).map_mul p q

end ChenRanks
