import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Actual path-connected groupoid transport to the original based group

Genuine paths supply isomorphisms from the original basepoint to each
original point, with the basepoint connector normalized to the identity.
The actual groupoid inverse identities prove the transport composition
law. This is the path-coordinate ingredient for constructing singular
cocycles from actual characters, not a cohomology comparison premise.
-/

noncomputable section

open CategoryTheory

namespace ChenRanks

variable (X : Type) [TopologicalSpace X] [PathConnectedSpace X]

/-- Actual connectors are native path classes; the base connector is
the actual identity. No choice of a presentation or loop detector occurs. -/
def basedFundamentalConnector (base x : X) :
    FundamentalGroupoid.mk base ≅ FundamentalGroupoid.mk x := by
  classical
  exact if hx : x = base then eqToIso (congrArg FundamentalGroupoid.mk hx.symm)
    else (Groupoid.isoEquivHom _ _).symm
      (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath base x))

@[simp]
theorem basedFundamentalConnector_base (base : X) :
    basedFundamentalConnector X base base = Iso.refl (FundamentalGroupoid.mk base) := by
  classical
  simp [basedFundamentalConnector]

/-- An actual original groupoid arrow is transported into the actual
based FundamentalGroup through these actual connectors. -/
def basedFundamentalArrow (base : X) {x y : X}
    (f : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) : FundamentalGroup X base :=
  FundamentalGroup.fromArrow
    ((basedFundamentalConnector X base x).hom ≫ f ≫
      (basedFundamentalConnector X base y).inv)

/-- Native End multiplication reverses composition, so its order is
explicitly reversed in this exact actual groupoid identity. -/
theorem basedFundamentalArrow_comp (base : X) {x y z : X}
    (f : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y)
    (g : FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk z) :
    basedFundamentalArrow X base (f ≫ g) =
      basedFundamentalArrow X base g * basedFundamentalArrow X base f := by
  change (basedFundamentalConnector X base x).hom ≫ (f ≫ g) ≫
      (basedFundamentalConnector X base z).inv =
    ((basedFundamentalConnector X base x).hom ≫ f ≫
      (basedFundamentalConnector X base y).inv) ≫
    ((basedFundamentalConnector X base y).hom ≫ g ≫
      (basedFundamentalConnector X base z).inv)
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

@[simp]
theorem basedFundamentalArrow_id (base x : X) :
    basedFundamentalArrow X base (𝟙 (FundamentalGroupoid.mk x)) = 1 := by
  change (basedFundamentalConnector X base x).hom ≫ 𝟙 _ ≫
    (basedFundamentalConnector X base x).inv = 𝟙 _
  simp

@[simp]
theorem basedFundamentalArrow_loop (base : X) (g : FundamentalGroup X base) :
    basedFundamentalArrow X base g.toArrow = g := by
  simp only [basedFundamentalArrow, basedFundamentalConnector_base,
    Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]

/-- The actual based group element of an actual original path. -/
def basedFundamentalPath (base : X) {x y : X} (p : Path x y) : FundamentalGroup X base :=
  basedFundamentalArrow X base (Path.Homotopic.Quotient.mk p)

theorem basedFundamentalPath_trans (base : X) {x y z : X} (p : Path x y) (q : Path y z) :
    basedFundamentalPath X base (p.trans q) =
      basedFundamentalPath X base q * basedFundamentalPath X base p :=
  basedFundamentalArrow_comp X base (Path.Homotopic.Quotient.mk p)
    (Path.Homotopic.Quotient.mk q)

theorem basedFundamentalPath_eq_of_homotopic (base : X) {x y : X}
    {p q : Path x y} (hpq : p.Homotopic q) :
    basedFundamentalPath X base p = basedFundamentalPath X base q :=
  congrArg (fun f : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y =>
    basedFundamentalArrow X base f) (Quotient.sound hpq)

@[simp]
theorem basedFundamentalPath_refl (base x : X) :
    basedFundamentalPath X base (Path.refl x) = 1 :=
  basedFundamentalArrow_id X base x

@[simp]
theorem basedFundamentalPath_loop (base : X) (p : Path base base) :
    basedFundamentalPath X base p =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) :=
  basedFundamentalArrow_loop X base _

variable (k : Type) [Field k]

/-- Actual additive characters evaluated on these genuine path classes. -/
def basedPathCharacterValue (base : X) (χ : Additive (FundamentalGroup X base) →+ k)
    {x y : X} (p : Path x y) : k :=
  χ (Additive.ofMul (basedFundamentalPath X base p))

theorem basedPathCharacterValue_trans (base : X)
    (χ : Additive (FundamentalGroup X base) →+ k)
    {x y z : X} (p : Path x y) (q : Path y z) :
    basedPathCharacterValue X k base χ (p.trans q) =
      basedPathCharacterValue X k base χ p + basedPathCharacterValue X k base χ q := by
  unfold basedPathCharacterValue
  rw [basedFundamentalPath_trans]
  change χ (Additive.ofMul (basedFundamentalPath X base q) +
    Additive.ofMul (basedFundamentalPath X base p)) = _
  rw [map_add]
  exact add_comm _ _

theorem basedPathCharacterValue_eq_of_homotopic (base : X)
    (χ : Additive (FundamentalGroup X base) →+ k) {x y : X}
    {p q : Path x y} (hpq : p.Homotopic q) :
    basedPathCharacterValue X k base χ p = basedPathCharacterValue X k base χ q := by
  unfold basedPathCharacterValue
  rw [basedFundamentalPath_eq_of_homotopic X base hpq]

end ChenRanks
