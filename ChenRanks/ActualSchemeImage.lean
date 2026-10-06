import ChenRanks.DominantFunctionField
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Reduced and integral actual scheme-theoretic images

The image is the native kernel ideal subscheme.  Reducedness is proved
on its actual quotient-ring cover, using the actual source section rings
and the actual kernel identity for a quasi-compact morphism.  Integral
images are therefore constructed from integral sources, rather than
supplied as desired graph models.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

variable {X Y : Scheme.{u}}

/-- Every actual morphism from a field spectrum is quasi-compact: every
actual preimage has a finite underlying set. -/
theorem fieldSpectrumMorphism_quasiCompact
    {K : Type u} [Field K] (f : Spec (.of K) ⟶ Y) : QuasiCompact f := by
  letI : Subsingleton ↥(Spec (.of K)) := by
    change Subsingleton (PrimeSpectrum K)
    infer_instance
  constructor
  intro U _ _
  exact (Set.Finite.of_subsingleton (f ⁻¹' U)).isCompact

/-- The native scheme-theoretic image of an actual quasi-compact
morphism from a reduced scheme is reduced. -/
theorem quasiCompactImage_isReduced [IsReduced X]
    (f : X ⟶ Y) [QuasiCompact f] : IsReduced f.image := by
  haveI (U : Y.affineOpens) :
      _root_.IsReduced (Y.presheaf.obj (op U.1) ⧸ f.ker.ideal U) := by
    let ψ : (Y.presheaf.obj (op U.1) ⧸ f.ker.ideal U) →+*
        X.presheaf.obj (op (f ⁻¹ᵁ U.1)) :=
      Ideal.Quotient.lift _ (f.app U.1).hom (f.ideal_ker_le U)
    have hker : RingHom.ker (f.app U.1).hom ≤ f.ker.ideal U := by
      rw [f.ker_apply]
    exact isReduced_of_injective ψ
      (RingHom.lift_injective_of_ker_le_ideal _ _ hker)
  haveI : ∀ U : Y.affineOpens, IsReduced (f.ker.subschemeCover.openCover.X U) := by
    intro U
    change IsReduced (Spec (.of (Y.presheaf.obj (op U.1) ⧸ f.ker.ideal U)))
    infer_instance
  exact IsReduced.of_openCover f.image f.ker.subschemeCover.openCover

/-- The native quasi-compact image of an integral source is integral.
Actual dominance of the native image factorization supplies
irreducibility, and the preceding quotient-cover argument supplies
reducedness. -/
theorem quasiCompactImage_isIntegral [IsIntegral X]
    (f : X ⟶ Y) [QuasiCompact f] : IsIntegral f.image := by
  letI : IsReduced f.image := quasiCompactImage_isReduced f
  letI : IrreducibleSpace f.image := by
    rw [irreducibleSpace_def]
    simpa only [Set.image_univ, f.toImage.denseRange.closure_range] using
      ((IrreducibleSpace.isIrreducible_univ X).image
        f.toImage f.toImage.continuous.continuousOn).closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end

end ChenRanks
