import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# A finite family of actual nonempty affine opens covering an actual open

The family is extracted from the native affine cover of the actual open
subscheme. Empty components are removed by their actual underlying
nonemptiness. The maps to the original scheme are genuine composed open
immersions. This supplies the actual finite chart family for shrinking
away vertical order support, with both containment and coverage proved.
-/

noncomputable section

namespace ChenRanks

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

variable (X : Scheme.{u}) (V : X.Opens) [CompactSpace V]

/-- The native finite affine cover of the actual open subscheme. -/
abbrev actualOpenFiniteAffineCover := V.toScheme.affineCover.finiteSubcover

/-- Its actual chart maps to the original scheme. -/
abbrev actualOpenFiniteAffineChartMap (i : (actualOpenFiniteAffineCover X V).I₀) :
    (actualOpenFiniteAffineCover X V).X i ⟶ X :=
  (actualOpenFiniteAffineCover X V).f i ≫ V.ι

/-- The actual chart ranges in the original scheme. -/
abbrev actualOpenFiniteAffineChart (i : (actualOpenFiniteAffineCover X V).I₀) : X.Opens :=
  (actualOpenFiniteAffineChartMap X V i).opensRange

/-- Keep exactly the actually nonempty chart ranges. -/
abbrev actualNonemptyAffineCoverIndex : Type u :=
  {i : (actualOpenFiniteAffineCover X V).I₀ // Nonempty (actualOpenFiniteAffineChart X V i)}

instance actualNonemptyAffineCoverIndex_finite : Finite (actualNonemptyAffineCoverIndex X V) := by
  infer_instance

/-- The finite family consists of actual opens of the original scheme. -/
abbrev actualNonemptyAffineCoverOpen (i : actualNonemptyAffineCoverIndex X V) : X.Opens :=
  actualOpenFiniteAffineChart X V i.val

instance actualNonemptyAffineCoverOpen_nonempty (i : actualNonemptyAffineCoverIndex X V) :
    Nonempty (actualNonemptyAffineCoverOpen X V i) := i.property

/-- Actual affineness follows from the actual affine source and actual open immersion. -/
theorem actualNonemptyAffineCoverOpen_isAffine (i : actualNonemptyAffineCoverIndex X V) :
    IsAffineOpen (actualNonemptyAffineCoverOpen X V i) :=
  isAffineOpen_opensRange (actualOpenFiniteAffineChartMap X V i.val)

/-- Every actual chart lies in the original actual open. -/
theorem actualNonemptyAffineCoverOpen_le (i : actualNonemptyAffineCoverIndex X V) :
    actualNonemptyAffineCoverOpen X V i ≤ V := by
  rintro x ⟨z, rfl⟩
  exact ((actualOpenFiniteAffineCover X V).f i.val z).property

/-- The actually nonempty native chart ranges cover the entire original actual open. -/
theorem actualNonemptyAffineCoverOpen_cover :
    V ≤ iSup (actualNonemptyAffineCoverOpen X V) := by
  intro x hx
  let xv : V.toScheme := ⟨x, hx⟩
  let i := (actualOpenFiniteAffineCover X V).idx xv
  obtain ⟨z, hz⟩ := (actualOpenFiniteAffineCover X V).covers xv
  have hxchart : x ∈ actualOpenFiniteAffineChart X V i := by
    refine ⟨z, ?_⟩
    exact congrArg Subtype.val hz
  exact Opens.mem_iSup.mpr ⟨⟨i, ⟨⟨x, hxchart⟩⟩⟩, hxchart⟩

/-- Both coverage and containment give the actual cover identity. -/
theorem actualNonemptyAffineCoverOpen_iSup :
    iSup (actualNonemptyAffineCoverOpen X V) = V :=
  le_antisymm (iSup_le (actualNonemptyAffineCoverOpen_le X V))
    (actualNonemptyAffineCoverOpen_cover X V)

end ChenRanks
