import ChenRanks.DiscretePrincipalFrameCovering
import ChenRanks.BasedFundamentalGroupoidTransport

/-! Genuine transport between different original fibers.

Native covering path lifts commute with the actual global right
translations. Their genuine fiber-coordinate maps are therefore left
translations. Actual concatenation reverses the order of the two
coordinate multipliers, exactly as in the original fundamental-group
convention. This provides the actual basepoint transport needed when
comparing canonical meridians at their original geometric basepoints.
No transport map, equivariance, presentation or conjugacy is an input.
-/
noncomputable section
namespace ChenRanks.TopologicalComparison
open Set Topology CategoryTheory
variable {ι H : Type*} {B : Type} [TopologicalSpace B] [Group H]
variable [TopologicalSpace H] [DiscreteTopology H]
variable (D : DiscretePrincipalFrameCover (ι := ι) (B := B) (H := H))

/-- True global right translations restrict to every true original fiber. -/
def discretePrincipalFrameFiberRightTranslation (base : B) (r : H)
    (p : (discretePrincipalFrameProjection D) ⁻¹' {base}) :
    (discretePrincipalFrameProjection D) ⁻¹' {base} :=
  ⟨discretePrincipalFrameRightTranslation D r p,
    (show discretePrincipalFrameProjection D
      (discretePrincipalFrameRightTranslation D r p) =
      discretePrincipalFrameProjection D p from rfl).trans p.property⟩

@[simp] theorem discretePrincipalFrameFiberRightTranslation_coordinates
    (base : B) (r : H) (p : (discretePrincipalFrameProjection D) ⁻¹' {base}) :
    discretePrincipalFrameFiberCoordinates D base
      (discretePrincipalFrameFiberRightTranslation D base r p) =
      discretePrincipalFrameFiberCoordinates D base p * r := rfl

/-- Native path lifting intertwines the same genuine right translations
even when the two original endpoints are different. -/
theorem discretePrincipalFramePathLift_right_translation {x y : B}
    (γ : Path.Homotopic.Quotient x y) (r : H)
    (p : (discretePrincipalFrameProjection D) ⁻¹' {x}) :
    (discretePrincipalFrame_isCoveringMap D).monodromy γ
      (discretePrincipalFrameFiberRightTranslation D x r p) =
      discretePrincipalFrameFiberRightTranslation D y r
        ((discretePrincipalFrame_isCoveringMap D).monodromy γ p) := by
  let cov := discretePrincipalFrame_isCoveringMap D
  obtain ⟨γ⟩ := γ
  apply Subtype.ext
  let hp : γ 0 = discretePrincipalFrameProjection D p := γ.source.trans p.property.symm
  let hr : γ 0 = discretePrincipalFrameProjection D
      (discretePrincipalFrameRightTranslation D r p) := hp
  let T : C(DiscretePrincipalFrameTotalSpace D, DiscretePrincipalFrameTotalSpace D) :=
    ⟨discretePrincipalFrameRightTranslation D r,
      discretePrincipalFrameRightTranslation_continuous D r⟩
  have hlift : T.comp (cov.liftPath γ p hp) =
      cov.liftPath γ (T p) hr := by
    apply (cov.eq_liftPath_iff' hr).mpr
    constructor
    · funext t
      change discretePrincipalFrameProjection D
        (discretePrincipalFrameRightTranslation D r (cov.liftPath γ p hp t)) = γ t
      exact congrFun (cov.liftPath_lifts γ p hp) t
    · change T (cov.liftPath γ p hp 0) = T p
      rw [cov.liftPath_zero]
  exact (DFunLike.congr_fun hlift 1).symm

/-- Actual native path transport expressed in the original fiber coordinates. -/
def discretePrincipalFramePathTransport {x y : B}
    (γ : Path.Homotopic.Quotient x y) : H :=
  discretePrincipalFrameFiberCoordinates D y
    ((discretePrincipalFrame_isCoveringMap D).monodromy γ
      ((discretePrincipalFrameFiberCoordinates D x).symm 1))

theorem discretePrincipalFramePathTransport_coordinates {x y : B}
    (γ : Path.Homotopic.Quotient x y)
    (p : (discretePrincipalFrameProjection D) ⁻¹' {x}) :
    discretePrincipalFrameFiberCoordinates D y
      ((discretePrincipalFrame_isCoveringMap D).monodromy γ p) =
      discretePrincipalFramePathTransport D γ * discretePrincipalFrameFiberCoordinates D x p := by
  have hp : discretePrincipalFrameFiberRightTranslation D x
      (discretePrincipalFrameFiberCoordinates D x p)
      ((discretePrincipalFrameFiberCoordinates D x).symm 1) = p := by
    apply (discretePrincipalFrameFiberCoordinates D x).injective
    rw [discretePrincipalFrameFiberRightTranslation_coordinates,
      Equiv.apply_symm_apply, one_mul]
  conv_lhs => rw [← hp]
  rw [discretePrincipalFramePathLift_right_translation,
    discretePrincipalFrameFiberRightTranslation_coordinates]
  rfl

@[simp] theorem discretePrincipalFramePathTransport_refl (x : B) :
    discretePrincipalFramePathTransport D (Path.Homotopic.Quotient.refl x) = 1 := by
  unfold discretePrincipalFramePathTransport
  rw [(discretePrincipalFrame_isCoveringMap D).monodromy_refl]
  exact Equiv.apply_symm_apply _ 1

/-- Genuine concatenation has the original reversed multiplier order. -/
theorem discretePrincipalFramePathTransport_trans {x y z : B}
    (γ : Path.Homotopic.Quotient x y) (δ : Path.Homotopic.Quotient y z) :
    discretePrincipalFramePathTransport D (γ.trans δ) =
      discretePrincipalFramePathTransport D δ * discretePrincipalFramePathTransport D γ := by
  unfold discretePrincipalFramePathTransport
  rw [(discretePrincipalFrame_isCoveringMap D).monodromy_trans_apply]
  exact discretePrincipalFramePathTransport_coordinates D δ _

/-- For a genuine original loop, path transport is the original
fundamental-group monodromy already constructed from the covering. -/
@[simp] theorem discretePrincipalFramePathTransport_loop (base : B)
    (g : FundamentalGroup B base) :
    discretePrincipalFramePathTransport D g.toPath =
      discretePrincipalFrameMonodromy D base g := rfl

variable {V : Type*} [AddCommGroup V] (σ : H →* Multiplicative V)

/-- The character of original monodromy is unchanged by genuine
groupoid transport to another original basepoint. The conjugating
multiplier is derived from actual path lifts, not supplied. -/
theorem discretePrincipalFrameMonodromy_character_transport
    (base x : B) (C : FundamentalGroupoid.mk base ≅ FundamentalGroupoid.mk x)
    (g : FundamentalGroup B x) :
    σ (discretePrincipalFrameMonodromy D base
      (FundamentalGroup.fromArrow (C.hom ≫ g.toArrow ≫ C.inv))) =
      σ (discretePrincipalFrameMonodromy D x g) := by
  have hprod : discretePrincipalFramePathTransport D C.inv *
      discretePrincipalFramePathTransport D C.hom = 1 := by
    rw [← discretePrincipalFramePathTransport_trans]
    change discretePrincipalFramePathTransport D (C.hom ≫ C.inv) = 1
    rw [C.hom_inv_id]
    exact discretePrincipalFramePathTransport_refl D base
  rw [← Category.assoc C.hom g.toArrow C.inv]
  change σ (discretePrincipalFramePathTransport D
    ((C.hom.trans g.toPath).trans C.inv)) =
      σ (discretePrincipalFramePathTransport D g.toPath)
  rw [discretePrincipalFramePathTransport_trans,
    discretePrincipalFramePathTransport_trans, map_mul, map_mul]
  calc
    σ (discretePrincipalFramePathTransport D C.inv) *
        (σ (discretePrincipalFramePathTransport D g.toPath) *
          σ (discretePrincipalFramePathTransport D C.hom)) =
      σ (discretePrincipalFramePathTransport D g.toPath) *
        (σ (discretePrincipalFramePathTransport D C.inv) *
          σ (discretePrincipalFramePathTransport D C.hom)) := by ac_rfl
    _ = σ (discretePrincipalFramePathTransport D g.toPath) := by
      rw [← map_mul, hprod, map_one, mul_one]

variable [PathConnectedSpace B]

/-- Actual original based-path character evaluation on a geometric loop
is its actual covering character at that loop's geometric basepoint. -/
theorem discretePrincipalFrameMonodromy_character_basedLoop
    (base x : B) (p : Path x x) :
    σ (discretePrincipalFrameMonodromy D base
      (ChenRanks.basedFundamentalPath B base p)) =
      σ (discretePrincipalFrameMonodromy D x
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))) :=
  discretePrincipalFrameMonodromy_character_transport D σ base x
    (ChenRanks.basedFundamentalConnector B base x) _

end ChenRanks.TopologicalComparison
