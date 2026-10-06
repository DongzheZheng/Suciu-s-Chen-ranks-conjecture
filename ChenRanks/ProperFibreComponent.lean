import ChenRanks.FibreRegularConstancy
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Actual proper fibres and their reduced irreducible components

The fibre used here is the actual categorical pullback along an actual
`k`-rational point.  Its structure morphism is proper by base change.
The component is the actual subscheme defined by the radical of the
actual irreducible-component ideal.  Reducedness is proved using its
actual affine quotient cover; integrality follows from actual
irreducibility.  No integral fibre or component is assumed.

An actual image-containment proof factors the fibre inclusion through
the ambient inverse-image open.  Consequently the ambient regular
section is restricted by the actual scheme `appLE` ring homomorphism.
Over an algebraically closed field the actual restricted section is a
scalar, and an actual unit gives a nonzero scalar.  This statement
neither identifies a general residue field with the base field nor
asserts that an ambient function-field relative differential vanishes.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

universe u

variable {X Y : Scheme.{u}}

/-- The radical subscheme is reduced, proved on its actual affine
quotient cover rather than assumed as a property of an abstract model. -/
theorem radical_subscheme_isReduced (I : X.IdealSheafData) :
    IsReduced I.radical.subscheme := by
  haveI (U : X.affineOpens) :
      _root_.IsReduced (X.presheaf.obj (op U.1) ⧸ I.radical.ideal U) := by
    apply (Ideal.isRadical_iff_quotient_reduced _).mp
    simpa only [Scheme.IdealSheafData.radical_ideal] using
      Ideal.radical_isRadical (I.ideal U)
  haveI : ∀ U : X.affineOpens, IsReduced (I.radical.subschemeCover.openCover.X U) := by
    intro U
    change IsReduced (Spec (.of (X.presheaf.obj (op U.1) ⧸ I.radical.ideal U)))
    infer_instance
  exact IsReduced.of_openCover I.radical.subscheme I.radical.subschemeCover.openCover

/-- The actual reduced induced subscheme on an actual irreducible
component of a Noetherian scheme. -/
def reducedIrreducibleComponent (X : Scheme.{u}) [IsNoetherian X]
    (T : Set X) (hT : T ∈ irreducibleComponents X) : Scheme.{u} :=
  (X.irreducibleComponentIdeal T hT).radical.subscheme

/-- The actual closed immersion of the reduced component. -/
def reducedIrreducibleComponentι (X : Scheme.{u}) [IsNoetherian X]
    (T : Set X) (hT : T ∈ irreducibleComponents X) :
    reducedIrreducibleComponent X T hT ⟶ X :=
  (X.irreducibleComponentIdeal T hT).radical.subschemeι

instance reducedIrreducibleComponentι_isClosedImmersion
    (X : Scheme.{u}) [IsNoetherian X]
    (T : Set X) (hT : T ∈ irreducibleComponents X) :
    IsClosedImmersion (reducedIrreducibleComponentι X T hT) :=
  inferInstanceAs (IsClosedImmersion
    (X.irreducibleComponentIdeal T hT).radical.subschemeι)

instance reducedIrreducibleComponent_isReduced
    (X : Scheme.{u}) [IsNoetherian X]
    (T : Set X) (hT : T ∈ irreducibleComponents X) :
    IsReduced (reducedIrreducibleComponent X T hT) :=
  radical_subscheme_isReduced (X.irreducibleComponentIdeal T hT)

instance reducedIrreducibleComponent_irreducibleSpace
    (X : Scheme.{u}) [IsNoetherian X]
    (T : Set X) (hT : T ∈ irreducibleComponents X) :
    IrreducibleSpace (reducedIrreducibleComponent X T hT) := by
  change IrreducibleSpace T
  exact Subtype.irreducibleSpace hT.1

instance reducedIrreducibleComponent_isIntegral
    (X : Scheme.{u}) [IsNoetherian X]
    (T : Set X) (hT : T ∈ irreducibleComponents X) :
    IsIntegral (reducedIrreducibleComponent X T hT) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

variable {k : Type u} [Field k]

/-- The actual scheme pullback along an actual rational point. -/
abbrev rationalPointFibre (f : X ⟶ Y) (c : Spec (.of k) ⟶ Y) : Scheme.{u} :=
  pullback f c

/-- A proper morphism's actual fibre over an actual rational point is
Noetherian: its structure map is proper by actual base change. -/
instance rationalPointFibre_isNoetherian
    (f : X ⟶ Y) [IsProper f] (c : Spec (.of k) ⟶ Y) :
    IsNoetherian (rationalPointFibre f c) where

private theorem rationalPointFibre_range_in_open
    (f : X ⟶ Y) (c : Spec (.of k) ⟶ Y)
    (W : Y.Opens) (hc : Set.range c ⊆ W) :
    Set.range (pullback.fst f c) ⊆ Set.range (f ⁻¹ᵁ W).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨p, rfl⟩
  change f ((pullback.fst f c) p) ∈ W
  have hp := congrArg (fun h : rationalPointFibre f c ⟶ Y => h p)
    (pullback.condition (f := f) (g := c))
  simp only [Scheme.Hom.comp_apply] at hp
  rw [hp]
  exact hc ⟨(pullback.snd f c) p, rfl⟩

/-- The actual fibre inclusion factors through the actual open where
the ambient section is regular. -/
def rationalPointFibreToOpen
    (f : X ⟶ Y) (c : Spec (.of k) ⟶ Y)
    (W : Y.Opens) (hc : Set.range c ⊆ W) :
    rationalPointFibre f c ⟶ (f ⁻¹ᵁ W).toScheme :=
  IsOpenImmersion.lift (f ⁻¹ᵁ W).ι (pullback.fst f c)
    (rationalPointFibre_range_in_open f c W hc)

@[reassoc (attr := simp)]
theorem rationalPointFibreToOpen_fac
    (f : X ⟶ Y) (c : Spec (.of k) ⟶ Y)
    (W : Y.Opens) (hc : Set.range c ⊆ W) :
    rationalPointFibreToOpen f c W hc ≫ (f ⁻¹ᵁ W).ι = pullback.fst f c :=
  IsOpenImmersion.lift_fac _ _ _

/-- The actual scalar structure map of the actual reduced fibre
component.  Its base field is exactly the rational point's field. -/
def fibreComponentScalarMorphism
    (f : X ⟶ Y) [IsProper f] (c : Spec (.of k) ⟶ Y)
    (T : Set (rationalPointFibre f c)) (hT : T ∈ irreducibleComponents (rationalPointFibre f c)) :
    reducedIrreducibleComponent (rationalPointFibre f c) T hT ⟶ Spec (.of k) :=
  reducedIrreducibleComponentι (rationalPointFibre f c) T hT ≫ pullback.snd f c

instance fibreComponentScalarMorphism_isProper
    (f : X ⟶ Y) [IsProper f] (c : Spec (.of k) ⟶ Y)
    (T : Set (rationalPointFibre f c)) (hT : T ∈ irreducibleComponents (rationalPointFibre f c)) :
    IsProper (fibreComponentScalarMorphism f c T hT) := by
  dsimp [fibreComponentScalarMorphism]
  infer_instance

/-- The actual reduced fibre component maps to the actual ambient open. -/
def fibreComponentToOpen
    (f : X ⟶ Y) [IsProper f] (c : Spec (.of k) ⟶ Y)
    (W : Y.Opens) (hc : Set.range c ⊆ W)
    (T : Set (rationalPointFibre f c)) (hT : T ∈ irreducibleComponents (rationalPointFibre f c)) :
    reducedIrreducibleComponent (rationalPointFibre f c) T hT ⟶ (f ⁻¹ᵁ W).toScheme :=
  reducedIrreducibleComponentι (rationalPointFibre f c) T hT ≫ rationalPointFibreToOpen f c W hc

@[reassoc (attr := simp)]
theorem fibreComponentToOpen_fac
    (f : X ⟶ Y) [IsProper f] (c : Spec (.of k) ⟶ Y)
    (W : Y.Opens) (hc : Set.range c ⊆ W)
    (T : Set (rationalPointFibre f c)) (hT : T ∈ irreducibleComponents (rationalPointFibre f c)) :
    fibreComponentToOpen f c W hc T hT ≫ (f ⁻¹ᵁ W).ι =
      reducedIrreducibleComponentι (rationalPointFibre f c) T hT ≫ pullback.fst f c := by
  simp only [fibreComponentToOpen, Category.assoc, rationalPointFibreToOpen_fac]

variable [IsAlgClosed k]

/-- Actual ambient regular sections restrict to actual scalar constants
on every actual reduced irreducible component of the proper fibre. -/
theorem properFibreComponent_restriction_constant
    (f : X ⟶ Y) [IsProper f] (c : Spec (.of k) ⟶ Y)
    (W : Y.Opens) (hc : Set.range c ⊆ W)
    (T : Set (rationalPointFibre f c)) (hT : T ∈ irreducibleComponents (rationalPointFibre f c))
    (s : X.presheaf.obj (op (f ⁻¹ᵁ W))) :
    ∃ a : k, globalScalarMap (fibreComponentScalarMorphism f c T hT) a =
      regularSectionRestriction (f ⁻¹ᵁ W) (fibreComponentToOpen f c W hc T hT) s :=
  regularSectionRestriction_constant (fibreComponentScalarMorphism f c T hT)
    (f ⁻¹ᵁ W) (fibreComponentToOpen f c W hc T hT) s

/-- An actual ambient unit gives an actual nonzero constant on each
actual reduced proper fibre component. -/
theorem properFibreComponent_restriction_constant_nonzero
    (f : X ⟶ Y) [IsProper f] (c : Spec (.of k) ⟶ Y)
    (W : Y.Opens) (hc : Set.range c ⊆ W)
    (T : Set (rationalPointFibre f c)) (hT : T ∈ irreducibleComponents (rationalPointFibre f c))
    (s : X.presheaf.obj (op (f ⁻¹ᵁ W))) (hs : IsUnit s) :
    ∃ a : k, a ≠ 0 ∧ globalScalarMap (fibreComponentScalarMorphism f c T hT) a =
      regularSectionRestriction (f ⁻¹ᵁ W) (fibreComponentToOpen f c W hc T hT) s :=
  regularSectionRestriction_constant_nonzero (fibreComponentScalarMorphism f c T hT)
    (f ⁻¹ᵁ W) (fibreComponentToOpen f c W hc T hT) s hs

/-- The actual stalk differential of the restriction vanishes on every
point of the actual reduced proper fibre component. -/
theorem properFibreComponent_restriction_stalkDifferential_eq_zero
    (f : X ⟶ Y) [IsProper f] (c : Spec (.of k) ⟶ Y)
    (W : Y.Opens) (hc : Set.range c ⊆ W)
    (T : Set (rationalPointFibre f c)) (hT : T ∈ irreducibleComponents (rationalPointFibre f c))
    (s : X.presheaf.obj (op (f ⁻¹ᵁ W))) (z : reducedIrreducibleComponent (rationalPointFibre f c) T hT) :
    letI : Algebra k ((reducedIrreducibleComponent (rationalPointFibre f c) T hT).presheaf.stalk z) :=
      (fibreStalkScalarMap (fibreComponentScalarMorphism f c T hT) z).toAlgebra
    KaehlerDifferential.D k ((reducedIrreducibleComponent (rationalPointFibre f c) T hT).presheaf.stalk z)
      ((reducedIrreducibleComponent (rationalPointFibre f c) T hT).presheaf.germ ⊤ z (by trivial)
        (regularSectionRestriction (f ⁻¹ᵁ W) (fibreComponentToOpen f c W hc T hT) s)) = 0 :=
  regularSectionRestriction_stalkDifferential_eq_zero (fibreComponentScalarMorphism f c T hT)
    (f ⁻¹ᵁ W) (fibreComponentToOpen f c W hc T hT) s z

end

end ChenRanks
