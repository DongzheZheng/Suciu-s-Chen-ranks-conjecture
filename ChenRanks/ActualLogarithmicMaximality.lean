import ChenRanks.ArrangementIsotropicRealization
import ChenRanks.CurveDifferentialBasisTransport
import ChenRanks.CurveDifferentialLine
import ChenRanks.DifferentialFieldInverse
import ChenRanks.ExteriorDifferentialFieldTransport

/-!
# Actual maximality inside the original logarithmic space

Maximality is relative to the actual logarithmic subspace, not to the
entire rational differential module. The original arrangement's genuine
quadratic maximality implies maximality of its actual logarithmic image.
The actual field comparison preserves rational wedges in both directions
and therefore transports this relative maximality as a theorem.

For an actual separable curve field over the actual rational-function
field, the proved generating differential and the actual curve-field
comparison make the actual base-change image isotropic. Intersecting
that image with the original logarithmic space constructs the actual
isotropic enlargement; maximality absorbs it. No abstract residue,
horizontal-kernel isotropy, or assumed transported maximality is used.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks

variable {k F G : Type*} [Field k] [CharZero k] [Field F] [Field G]
  [Algebra k F] [Algebra k G]

omit [CharZero k] in
/-- Isotropy uses the actual exterior square over the actual function field. -/
def IsRationallyIsotropic (P : Submodule k Ω[F⁄k]) : Prop :=
  ∀ ω ∈ P, ∀ η ∈ P, exteriorWedge (k := F) ω η = 0

omit [CharZero k] in
/-- Maximal rational isotropy is tested only inside the specified actual
logarithmic subspace. It makes no maximality claim in the whole module. -/
def IsMaximalRationallyIsotropicIn
    (E P : Submodule k Ω[F⁄k]) : Prop :=
  P ≤ E ∧ IsRationallyIsotropic P ∧
    ∀ Q : Submodule k Ω[F⁄k], P ≤ Q → Q ≤ E → IsRationallyIsotropic Q → Q ≤ P

/-- The actual exterior algebra lift preserves zero rational wedges. -/
theorem rationalWedge_zero_map_of_field_equiv (e : F ≃ₐ[k] G)
    (ω η : Ω[F⁄k]) (h : exteriorWedge (k := F) ω η = 0) :
    exteriorWedge (k := G) (differentialFieldLinearEquiv e ω)
      (differentialFieldLinearEquiv e η) = 0 := by
  letI : Algebra F (ExteriorAlgebra G Ω[G⁄k]) := fieldEquivExteriorTargetAlgebra e
  have hEA : (exteriorWedge (k := F) ω η : ExteriorAlgebra F Ω[F⁄k]) = 0 :=
    congrArg (Submodule.subtype (ExteriorAlgebra.exteriorPower F 2 Ω[F⁄k])) h
  have ht := congrArg (fun z ↦ differentialExteriorFieldHom e z) hEA
  apply (ExteriorAlgebra.exteriorPower G 2 Ω[G⁄k]).subtype_injective
  simpa only [differentialExteriorFieldHom_wedge, map_zero] using ht

/-- The native inverse-field differential comparison proves reflection
as well as preservation of actual rational wedge vanishing. -/
theorem rationalWedge_zero_map_iff_of_field_equiv (e : F ≃ₐ[k] G)
    (ω η : Ω[F⁄k]) :
    exteriorWedge (k := G) (differentialFieldLinearEquiv e ω)
      (differentialFieldLinearEquiv e η) = 0 ↔
      exteriorWedge (k := F) ω η = 0 := by
  constructor
  · intro h
    simpa only [differentialFieldLinearEquiv_inverse_apply_apply] using
      rationalWedge_zero_map_of_field_equiv e.symm
        (differentialFieldLinearEquiv e ω) (differentialFieldLinearEquiv e η) h
  · exact rationalWedge_zero_map_of_field_equiv e ω η

/-- Isotropy is transported by the actual differential field equivalence. -/
theorem isRationallyIsotropic_map_iff (e : F ≃ₐ[k] G)
    (P : Submodule k Ω[F⁄k]) :
    IsRationallyIsotropic (P.map (differentialFieldLinearEquiv e).toLinearMap) ↔
      IsRationallyIsotropic P := by
  constructor
  · intro h ω hω η hη
    apply (rationalWedge_zero_map_iff_of_field_equiv e ω η).mp
    exact h _ ⟨ω, hω, rfl⟩ _ ⟨η, hη, rfl⟩
  · intro h ω hω η hη
    obtain ⟨x, hx, rfl⟩ := hω
    obtain ⟨y, hy, rfl⟩ := hη
    exact rationalWedge_zero_map_of_field_equiv e x y (h x hx y hy)

/-- Relative maximality on the actual image is derived from original
relative maximality. No transported maximality is supplied as an input. -/
theorem isMaximalRationallyIsotropicIn_map (e : F ≃ₐ[k] G)
    (E P : Submodule k Ω[F⁄k]) (hP : IsMaximalRationallyIsotropicIn E P) :
    IsMaximalRationallyIsotropicIn
      (E.map (differentialFieldLinearEquiv e).toLinearMap)
      (P.map (differentialFieldLinearEquiv e).toLinearMap) := by
  refine ⟨Submodule.map_mono hP.1, (isRationallyIsotropic_map_iff e P).mpr hP.2.1, ?_⟩
  intro Q hPQ hQE hQ
  let R := Q.comap (differentialFieldLinearEquiv e).toLinearMap
  have hPR : P ≤ R := by
    intro ω hω
    exact hPQ ⟨ω, hω, rfl⟩
  have hRE : R ≤ E := by
    intro ω hω
    obtain ⟨η, hη, heq⟩ := hQE hω
    have : η = ω := (differentialFieldLinearEquiv e).injective heq
    exact this ▸ hη
  have hR : IsRationallyIsotropic R := by
    intro ω hω η hη
    exact (rationalWedge_zero_map_iff_of_field_equiv e ω η).mp (hQ _ hω _ hη)
  have hRP : R ≤ P := hP.2.2 R hPR hRE hR
  intro ω hω
  obtain ⟨η, rfl⟩ := (differentialFieldLinearEquiv e).surjective ω
  exact ⟨η, hRP hω, rfl⟩

section ActualCurveImage

variable {L K : Type*} [Field L] [Field K]
  [Algebra k L] [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L]
  [Algebra.IsSeparable (RatFunc k) L] [Algebra k K]
  [Algebra K G] [IsScalarTower k K G]

/-- Actual curve pullbacks and the actual generating differential
construct an isotropic enlargement inside the original log space.
Every actual logarithmic coefficient in the curve image is then absorbed. -/
theorem mem_maximal_rational_isotropic_of_actual_curve_image
    (e : L ≃ₐ[k] K) (E P : Submodule k Ω[G⁄k])
    (hP : IsMaximalRationallyIsotropicIn E P)
    (hpull : ∀ ω : P, ∃ η : Ω[K⁄k],
      KaehlerDifferential.map k k K G η = (ω : Ω[G⁄k]))
    (g : Ω[G⁄k]) (hgE : g ∈ E)
    (hgCurve : g ∈ LinearMap.range (KaehlerDifferential.mapBaseChange k K G)) :
    g ∈ P := by
  let R := (LinearMap.range (KaehlerDifferential.mapBaseChange k K G)).restrictScalars k
  let Q := E ⊓ R
  have hPQ : P ≤ Q := by
    intro ω hω
    refine ⟨hP.1 hω, ?_⟩
    obtain ⟨η, hη⟩ := hpull ⟨ω, hω⟩
    exact ⟨1 ⊗ₜ[K] η, by
      simpa only [KaehlerDifferential.mapBaseChange_tmul, one_smul] using hη⟩
  have hQ : IsRationallyIsotropic Q := by
    intro ω hω η hη
    exact actual_curve_baseChange_exteriorWedge_eq_zero_of_field_equiv
      e (curveDifferentialGenerator k L) (curve_differential_eq_smul k L)
      ω η hω.2 hη.2
  exact hP.2.2 Q hPQ inf_le_left hQ ⟨hgE, hgCurve⟩

end ActualCurveImage

namespace AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- Original genuine quadratic maximality implies relative maximality
inside the original finite actual logarithmic image. It is not an
assumed property of the realized subspace. -/
theorem realizedLogarithmicSubspace_maximal_in_logarithmicForms
    (P : Submodule ℂ (ι → ℂ))
    (hP : IsMaximalIsotropic (relationWedge A.quadraticLogarithmicRealization) P) :
    IsMaximalRationallyIsotropicIn A.logarithmicForms (A.realizedLogarithmicSubspace P) := by
  refine ⟨A.realizedLogarithmicSubspace_le_logarithmicForms P, ?_, ?_⟩
  · intro ω hω η hη
    obtain ⟨p, rfl⟩ := hω
    obtain ⟨q, rfl⟩ := hη
    have h := hP.1 p p.property q q.property
    simpa only [relationWedge_apply, quadraticLogarithmicRealization_exteriorWedge] using h
  · intro Q hPQ hQE hQ
    let R := Q.comap A.logarithmicRealization
    have hPR : P ≤ R := by
      intro p hp
      exact hPQ ⟨⟨p, hp⟩, rfl⟩
    have hR : IsIsotropic (relationWedge A.quadraticLogarithmicRealization) R := by
      intro p hp q hq
      simpa only [relationWedge_apply, quadraticLogarithmicRealization_exteriorWedge] using
        hQ (A.logarithmicRealization p) hp (A.logarithmicRealization q) hq
    have hRP : R ≤ P := hP.2 R hPR hR
    intro ω hω
    obtain ⟨p, hp⟩ := hQE hω
    have hpR : p ∈ R := by
      change A.logarithmicRealization p ∈ Q
      exact hp.symm ▸ hω
    exact ⟨⟨p, hRP hpR⟩, hp⟩

end AffineArrangement

end ChenRanks
