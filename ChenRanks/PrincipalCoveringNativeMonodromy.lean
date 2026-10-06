import Mathlib.Topology.Homotopy.Lifting

/-! A genuine native covering has an actual fundamental-group
representation whenever its actual fiber coordinates intertwine genuine
continuous right translations. Homotopy descent and path lifting use the
original library covering theorem. These explicit principal-coordinate
data are an intermediate interface; an arrangement application must
construct them from its actual local parallel frames.
-/
noncomputable section
namespace ChenRanks.TopologicalComparison
variable {X E H : Type*} [TopologicalSpace X] [TopologicalSpace E] [Group H]
variable {p : E → X} (cov : IsCoveringMap p) (base : X)

/-- Actual fiber coordinates and actual continuous translations of the
same original covering. No monodromy or group representation is an input. -/
structure PrincipalCoveringCoordinates (_cov : IsCoveringMap p) (base : X) where
  coordinates : (p ⁻¹' {base}) ≃ H
  translation : H → C(E, E)
  projection_translation : ∀ r x, p (translation r x) = p x
  coordinates_translation : ∀ r (x : p ⁻¹' {base}),
    coordinates ⟨translation r x,
      (projection_translation r x).trans x.property⟩ = coordinates x * r

variable (D : PrincipalCoveringCoordinates cov base (H := H))

/-- Original continuous translation on the actual original fiber. -/
def principalFiberTranslation (r : H) (x : p ⁻¹' {base}) : p ⁻¹' {base} :=
  ⟨D.translation r x, (D.projection_translation r x).trans x.property⟩

@[simp] theorem principalFiberTranslation_coordinates (r : H) (x : p ⁻¹' {base}) :
    D.coordinates (principalFiberTranslation cov base D r x) = D.coordinates x * r :=
  D.coordinates_translation r x

/-- Genuine path lifting commutes with genuine continuous translations. -/
theorem nativeMonodromy_principalFiberTranslation
    (gamma : Path.Homotopic.Quotient base base) (r : H) (x : p ⁻¹' {base}) :
    cov.monodromy gamma (principalFiberTranslation cov base D r x) =
      principalFiberTranslation cov base D r (cov.monodromy gamma x) := by
  obtain ⟨gamma⟩ := gamma
  apply Subtype.ext
  let hx : gamma 0 = p x := gamma.source.trans x.property.symm
  let hr : gamma 0 = p (D.translation r x) :=
    hx.trans (D.projection_translation r x).symm
  have hlift :
      (D.translation r).comp (cov.liftPath gamma x hx) =
        cov.liftPath gamma (D.translation r x) hr := by
    apply (cov.eq_liftPath_iff' hr).mpr
    constructor
    · funext t
      change p (D.translation r (cov.liftPath gamma x hx t)) = gamma t
      rw [D.projection_translation]
      exact congrFun (cov.liftPath_lifts gamma x hx) t
    · change D.translation r (cov.liftPath gamma x hx 0) = D.translation r x
      rw [cov.liftPath_zero]
  exact (DFunLike.congr_fun hlift 1).symm

/-- Actual original monodromy is left multiplication in the proved
principal coordinates, derived from actual path-lift equivariance. -/
theorem nativeMonodromy_principal_coordinates
    (gamma : Path.Homotopic.Quotient base base) (x : p ⁻¹' {base}) :
    D.coordinates (cov.monodromy gamma x) =
      D.coordinates (cov.monodromy gamma (D.coordinates.symm 1)) * D.coordinates x := by
  have hx : principalFiberTranslation cov base D (D.coordinates x)
      (D.coordinates.symm 1) = x := by
    apply D.coordinates.injective
    rw [principalFiberTranslation_coordinates, Equiv.apply_symm_apply, one_mul]
  conv_lhs => rw [← hx]
  rw [nativeMonodromy_principalFiberTranslation,
    principalFiberTranslation_coordinates]

/-- A representation of the original native fundamental group.
Its multiplication convention is the original reversed path composition. -/
def principalCoveringNativeMonodromy : FundamentalGroup X base →* H where
  toFun g := D.coordinates (cov.monodromy g.toPath (D.coordinates.symm 1))
  map_one' := by
    change D.coordinates (cov.monodromy (Path.Homotopic.Quotient.refl base)
      (D.coordinates.symm 1)) = 1
    rw [cov.monodromy_refl]
    exact D.coordinates.apply_symm_apply 1
  map_mul' g h := by
    change D.coordinates (cov.monodromy (h.toPath.trans g.toPath)
      (D.coordinates.symm 1)) = _
    rw [cov.monodromy_trans_apply]
    exact nativeMonodromy_principal_coordinates cov base D g.toPath
      (cov.monodromy h.toPath (D.coordinates.symm 1))

@[simp] theorem principalCoveringNativeMonodromy_apply (g : FundamentalGroup X base) :
    principalCoveringNativeMonodromy cov base D g =
      D.coordinates (cov.monodromy g.toPath (D.coordinates.symm 1)) := rfl

end ChenRanks.TopologicalComparison
