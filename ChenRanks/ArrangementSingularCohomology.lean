import ChenRanks.ArrangementObjects
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Actual singular cohomology of the original arrangement complement

The chains are the library's actual singular chains of the original
topological complement. Cochains are their linear duals, with the actual
dual boundary. The square-zero identity is derived from that boundary,
rather than supplied as a cohomology or formality premise.

This source defines the actual cohomology spaces used in the paper.
It does not identify them with logarithmic forms, define their cup
product, or assert a Chen--Koszul comparison.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace ChenRanks.SingularCohomology

variable (k : Type) [Field k] (X : Type) [TopologicalSpace X]

/-- The actual singular chain complex with coefficients in the field. -/
def chains : ChainComplex (ModuleCat.{0} k) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{0} k)).obj
    (ModuleCat.of k k)).obj (TopCat.of X)

/-- All linear cochains on the actual singular chains. -/
abbrev cochains (n : ℕ) := Module.Dual k ((chains k X).X n)

/-- The actual dual of the singular boundary. -/
def differential (n : ℕ) : cochains k X n →ₗ[k] cochains k X (n + 1) :=
  ((chains k X).d (n + 1) n).hom.dualMap

/-- The square-zero identity follows from the original singular boundary. -/
theorem differential_comp_differential (n : ℕ) :
    (differential k X (n + 1)).comp (differential k X n) = 0 := by
  ext ℓ z
  let C := chains k X
  have h := C.d_comp_d (n + 2) (n + 1) n
  have hlinear : (C.d (n + 1) n).hom.comp (C.d (n + 2) (n + 1)).hom = 0 :=
    congrArg (fun f => f.hom) h
  have hz := DFunLike.congr_fun hlinear z
  change (C.d (n + 1) n).hom ((C.d (n + 2) (n + 1)).hom z) = 0 at hz
  change ℓ ((C.d (n + 1) n).hom ((C.d (n + 2) (n + 1)).hom z)) = 0
  rw [hz]
  exact map_zero ℓ

/-- The genuine singular cochain complex, in cohomological degrees. -/
def complex : CochainComplex (ModuleCat.{0} k) ℕ :=
  CochainComplex.of
    (fun n => ModuleCat.of k (cochains k X n))
    (fun n => ModuleCat.ofHom (differential k X n))
    (fun n => by
      apply ModuleCat.hom_ext
      exact differential_comp_differential k X n)

/-- Actual singular cohomology, as the homology object of the true dual complex. -/
abbrev cohomology (n : ℕ) : ModuleCat.{0} k := (complex k X).homology n

end ChenRanks.SingularCohomology

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The original complement's singular cochain complex over the complexes. -/
abbrev singularCochainComplex : CochainComplex (ModuleCat.{0} ℂ) ℕ :=
  SingularCohomology.complex ℂ A.Complement

/-- The actual complex singular cohomology of the original complement. -/
abbrev singularCohomology (n : ℕ) : ModuleCat.{0} ℂ :=
  SingularCohomology.cohomology ℂ A.Complement n

/-- The actual degree-one space, before any comparison with logarithmic forms. -/
abbrev singularH1 : ModuleCat.{0} ℂ := A.singularCohomology 1

/-- The actual degree-two space, before any Orlik--Solomon comparison. -/
abbrev singularH2 : ModuleCat.{0} ℂ := A.singularCohomology 2

end ChenRanks.AffineArrangement
