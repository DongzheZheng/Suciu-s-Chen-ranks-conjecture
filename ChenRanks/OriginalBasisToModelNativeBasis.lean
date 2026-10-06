import ChenRanks.ArrangementIsotropicRealization
import ChenRanks.ActualLogarithmicMaximality
import ChenRanks.ExteriorDifferentialFieldTransport
import ChenRanks.ValuationKernelDifferentials
import ChenRanks.ActualLogarithmicFieldTransport
import ChenRanks.LogarithmicMixedCoefficientExpansion

/-!
# Pull the native model basis back to the original generator subspace

The actual model logarithmic realization is the original realization
followed by the actual differential field equivalence. Original
hyperplane residues prove its injectivity. The original subspace is
therefore genuinely isomorphic to its actual model image. Pulling the
native finite basis of that image back along this equivalence produces
the basis used for the original mixed exterior representation.

No equality between two independently chosen bases is assumed. Every
original mixed relation is transported with this pulled-back basis,
the original coefficient vectors, and the actual transported equation
units. Actual model coefficient membership reflects back to the original
subspace and proves membership in its actual pure exterior square.
The geometry which proves those memberships is provided separately.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks

private theorem fieldTransport_sum_wedges {F G I : Type*}
    [Field F] [Field G] [Algebra ℂ F] [Algebra ℂ G] [Fintype I]
    (e : F ≃ₐ[ℂ] G) (p g : I → Ω[F⁄ℂ])
    (h : (∑ i, exteriorWedge (k := F) (p i) (g i)) = 0) :
    (∑ i, exteriorWedge (k := G) (differentialFieldLinearEquiv e (p i))
      (differentialFieldLinearEquiv e (g i))) = 0 := by
  letI : Algebra F (ExteriorAlgebra G Ω[G⁄ℂ]) := fieldEquivExteriorTargetAlgebra e
  have hEA : (∑ i, (exteriorWedge (k := F) (p i) (g i) :
      ExteriorAlgebra F Ω[F⁄ℂ])) = 0 := by
    simpa only [map_sum, map_zero] using congrArg
      (Submodule.subtype (ExteriorAlgebra.exteriorPower F 2 Ω[F⁄ℂ])) h
  have ht := congrArg (fun z ↦ differentialExteriorFieldHom e z) hEA
  apply (ExteriorAlgebra.exteriorPower G 2 Ω[G⁄ℂ]).subtype_injective
  simpa only [map_sum, map_zero, differentialExteriorFieldHom_wedge] using ht

namespace AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
  {G : Type*} [Field G] [Algebra ℂ G]

/-- The genuine original logarithmic map followed by the actual field map. -/
def modelLogarithmicRealization
    (e : RationalFunctionField (d := d) ≃ₐ[ℂ] G) :
    (ι → ℂ) →ₗ[ℂ] Ω[G⁄ℂ] :=
  (differentialFieldLinearEquiv e).toLinearMap.comp A.logarithmicRealization

theorem modelLogarithmicRealization_injective
    (e : RationalFunctionField (d := d) ≃ₐ[ℂ] G) :
    Function.Injective (A.modelLogarithmicRealization e) :=
  (differentialFieldLinearEquiv e).injective.comp A.logarithmicRealization_injective

/-- The actual equation functions are transported as actual units. -/
def modelEquationUnit (e : RationalFunctionField (d := d) ≃ₐ[ℂ] G) (a : ι) : Gˣ :=
  Units.map e.toRingHom.toMonoidHom (A.equationUnit a)

/-- The actual model logarithmic realization retains the original coefficients
and the actual transported equation units. -/
theorem modelLogarithmicRealization_eq_logCombination
    (e : RationalFunctionField (d := d) ≃ₐ[ℂ] G) (c : ι → ℂ) :
    A.modelLogarithmicRealization e c =
      relativeLogCombination (L := ℂ) (A.modelEquationUnit e) c := by
  change differentialFieldLinearEquiv e
    (relativeLogCombination (L := ℂ) A.equationUnit c) =
      relativeLogCombination (L := ℂ)
        (fun a ↦ Units.map e.toRingHom.toMonoidHom (A.equationUnit a)) c
  exact (relativeLogCombination_mapUnits_eq e A.equationUnit c).symm

/-- The actual model image of the original subspace. -/
def modelLogarithmicSubspace
    (e : RationalFunctionField (d := d) ≃ₐ[ℂ] G) (P : Submodule ℂ (ι → ℂ)) :
    Submodule ℂ Ω[G⁄ℂ] :=
  LinearMap.range ((A.modelLogarithmicRealization e).comp P.subtype)

/-- The native model subspace is exactly the actual differential image
of the original realized subspace. -/
theorem modelLogarithmicSubspace_eq_map_realized
    (e : RationalFunctionField (d := d) ≃ₐ[ℂ] G) (P : Submodule ℂ (ι → ℂ)) :
    A.modelLogarithmicSubspace e P =
      (A.realizedLogarithmicSubspace P).map (differentialFieldLinearEquiv e).toLinearMap := by
  ext ω
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨A.logarithmicRealization p, ⟨p, rfl⟩, hp⟩
  · rintro ⟨η, ⟨p, hp⟩, hη⟩
    refine ⟨p, ?_⟩
    change differentialFieldLinearEquiv e (A.logarithmicRealization p) = ω
    exact congrArg (differentialFieldLinearEquiv e) hp |>.trans hη

/-- The entire actual model logarithmic space equals the actual
differential image of the original finite logarithmic space. -/
theorem model_logCombination_range_eq_map_logarithmicForms
    (e : RationalFunctionField (d := d) ≃ₐ[ℂ] G) :
    LinearMap.range (relativeLogCombination (L := ℂ) (A.modelEquationUnit e)) =
      A.logarithmicForms.map (differentialFieldLinearEquiv e).toLinearMap := by
  ext ω
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨A.logarithmicRealization c, ⟨c, rfl⟩, ?_⟩
    exact (A.modelLogarithmicRealization_eq_logCombination e c).trans hc
  · rintro ⟨η, ⟨c, hc⟩, hη⟩
    refine ⟨c, ?_⟩
    rw [← A.modelLogarithmicRealization_eq_logCombination e c]
    exact congrArg (differentialFieldLinearEquiv e) hc |>.trans hη

/-- Original actual quadratic maximality proves the exact model maximality
needed by the native normalization mixed-coefficient absorption theorem. -/
theorem modelLogarithmicSubspace_maximal_in_model_logCombination_range
    (e : RationalFunctionField (d := d) ≃ₐ[ℂ] G) (P : Submodule ℂ (ι → ℂ))
    (hP : IsMaximalIsotropic (relationWedge A.quadraticLogarithmicRealization) P) :
    IsMaximalRationallyIsotropicIn
      (LinearMap.range (relativeLogCombination (L := ℂ) (A.modelEquationUnit e)))
      (A.modelLogarithmicSubspace e P) := by
  rw [A.model_logCombination_range_eq_map_logarithmicForms e,
    A.modelLogarithmicSubspace_eq_map_realized e P]
  exact isMaximalRationallyIsotropicIn_map e A.logarithmicForms
    (A.realizedLogarithmicSubspace P)
    (A.realizedLogarithmicSubspace_maximal_in_logarithmicForms P hP)

instance modelLogarithmicSubspace_finiteDimensional
    (e : RationalFunctionField (d := d) ≃ₐ[ℂ] G) (P : Submodule ℂ (ι → ℂ)) :
    FiniteDimensional ℂ (A.modelLogarithmicSubspace e P) :=
  LinearMap.finiteDimensional_range ((A.modelLogarithmicRealization e).comp P.subtype)

/-- The native injective logarithmic map supplies the actual subspace equivalence. -/
def originalToModelLogarithmicSubspaceEquiv
    (e : RationalFunctionField (d := d) ≃ₐ[ℂ] G) (P : Submodule ℂ (ι → ℂ)) :
    P ≃ₗ[ℂ] A.modelLogarithmicSubspace e P :=
  LinearEquiv.ofInjective ((A.modelLogarithmicRealization e).comp P.subtype)
    ((A.modelLogarithmicRealization_injective e).comp P.subtype_injective)

/-- Pull back the model's actual native basis rather than equating it
with the transport of an independently chosen original basis. -/
def originalBasisFromModelNativeBasis
    (e : RationalFunctionField (d := d) ≃ₐ[ℂ] G) (P : Submodule ℂ (ι → ℂ)) :
    Module.Basis (Fin (Module.finrank ℂ (A.modelLogarithmicSubspace e P))) ℂ P :=
  (Module.finBasis ℂ (A.modelLogarithmicSubspace e P)).map
    (A.originalToModelLogarithmicSubspaceEquiv e P).symm

/-- The inverse identity proves the exact native basis identity used
by the actual mixed differential descent theorem. -/
theorem modelLogarithmicRealization_originalBasisFromModelNativeBasis
    (e : RationalFunctionField (d := d) ≃ₐ[ℂ] G) (P : Submodule ℂ (ι → ℂ))
    (i : Fin (Module.finrank ℂ (A.modelLogarithmicSubspace e P))) :
    A.modelLogarithmicRealization e (A.originalBasisFromModelNativeBasis e P i) =
      (Module.finBasis ℂ (A.modelLogarithmicSubspace e P) i : Ω[G⁄ℂ]) := by
  change ((A.originalToModelLogarithmicSubspaceEquiv e P)
    ((A.originalToModelLogarithmicSubspaceEquiv e P).symm
      (Module.finBasis ℂ (A.modelLogarithmicSubspace e P) i)) : Ω[G⁄ℂ]) = _
  rw [LinearEquiv.apply_symm_apply]

/-- Actual model coefficient membership reflects to the original
generator subspace by proved degree-one injectivity. -/
theorem modelLogarithmicRealization_mem_modelLogarithmicSubspace_iff
    (e : RationalFunctionField (d := d) ≃ₐ[ℂ] G) (P : Submodule ℂ (ι → ℂ))
    (c : ι → ℂ) :
    A.modelLogarithmicRealization e c ∈ A.modelLogarithmicSubspace e P ↔ c ∈ P := by
  constructor
  · rintro ⟨p, hp⟩
    have hpc : (p : ι → ℂ) = c := A.modelLogarithmicRealization_injective e hp
    exact hpc ▸ p.property
  · intro hc
    exact ⟨⟨c, hc⟩, rfl⟩

private theorem rationalWedge_swap {K M : Type*} [Field K]
    [AddCommGroup M] [Module K M] (x y : M) :
    exteriorWedge (k := K) x y = -exteriorWedge (k := K) y x := by
  apply (ExteriorAlgebra.exteriorPower K 2 M).subtype_injective
  change (exteriorWedge (k := K) x y : ExteriorAlgebra K M) =
    -(exteriorWedge (k := K) y x : ExteriorAlgebra K M)
  rw [exteriorWedge_coe, exteriorWedge_coe]
  exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap x y)

/-- The pulled-back basis gives every original mixed quadratic relation
an actual model relation written in precisely the model native basis.
The original coefficient vectors and true equation units are retained. -/
theorem original_mixed_relation_has_model_native_basis_representation
    (e : RationalFunctionField (d := d) ≃ₐ[ℂ] G) (P : Submodule ℂ (ι → ℂ))
    (z : ⋀[ℂ]^2 (ι → ℂ))
    (hz : z ∈ mixedExterior P) (hrelation : A.quadraticLogarithmicRealization z = 0) :
    ∃ c : Fin (Module.finrank ℂ (A.modelLogarithmicSubspace e P)) → ι → ℂ,
      (∑ i, exteriorWedge (k := ℂ)
        (A.originalBasisFromModelNativeBasis e P i : ι → ℂ) (c i)) = z ∧
      (∑ i, ∑ a, algebraMap ℂ G (c i a) • exteriorWedge (k := G)
        (logarithmicDifferential ℂ G (A.modelEquationUnit e a))
        (Module.finBasis ℂ (A.modelLogarithmicSubspace e P) i : Ω[G⁄ℂ])) = 0 := by
  classical
  letI : AddCommGroup (RationalTwoForms (d := d)) := rationalTwoForms_addCommGroup
  obtain ⟨c, hc⟩ := exists_basis_mixed_representation P
    (A.originalBasisFromModelNativeBasis e P) hz
  refine ⟨c, hc, ?_⟩
  have hforward :
      (∑ i, exteriorWedge (k := RationalFunctionField (d := d))
        (A.logarithmicRealization (A.originalBasisFromModelNativeBasis e P i))
        (A.logarithmicRealization (c i))) = 0 := by
    have h := congrArg A.quadraticLogarithmicRealization hc
    simpa only [map_sum, quadraticLogarithmicRealization_exteriorWedge, hrelation] using h
  have hnative (i : Fin (Module.finrank ℂ (A.modelLogarithmicSubspace e P))) :
      differentialFieldLinearEquiv e
        (A.logarithmicRealization (A.originalBasisFromModelNativeBasis e P i)) =
        (Module.finBasis ℂ (A.modelLogarithmicSubspace e P) i : Ω[G⁄ℂ]) :=
    A.modelLogarithmicRealization_originalBasisFromModelNativeBasis e P i
  have hmodel :
      (∑ i, exteriorWedge (k := G)
        (Module.finBasis ℂ (A.modelLogarithmicSubspace e P) i : Ω[G⁄ℂ])
        (A.modelLogarithmicRealization e (c i))) = 0 := by
    have ht := fieldTransport_sum_wedges e
      (fun i ↦ A.logarithmicRealization (A.originalBasisFromModelNativeBasis e P i))
      (fun i ↦ A.logarithmicRealization (c i)) hforward
    change (∑ i, exteriorWedge (k := G)
      (differentialFieldLinearEquiv e
        (A.logarithmicRealization (A.originalBasisFromModelNativeBasis e P i)))
      (A.modelLogarithmicRealization e (c i))) = 0 at ht
    simpa only [hnative] using ht
  have hswap :
      (∑ i, exteriorWedge (k := G) (A.modelLogarithmicRealization e (c i))
        (Module.finBasis ℂ (A.modelLogarithmicSubspace e P) i : Ω[G⁄ℂ])) = 0 := by
    calc
      _ = ∑ i, -exteriorWedge (k := G)
          (Module.finBasis ℂ (A.modelLogarithmicSubspace e P) i : Ω[G⁄ℂ])
          (A.modelLogarithmicRealization e (c i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact rationalWedge_swap _ _
      _ = -(∑ i, exteriorWedge (k := G)
          (Module.finBasis ℂ (A.modelLogarithmicSubspace e P) i : Ω[G⁄ℂ])
          (A.modelLogarithmicRealization e (c i))) := by rw [Finset.sum_neg_distrib]
      _ = 0 := by rw [hmodel, neg_zero]
  simpa only [modelLogarithmicRealization_eq_logCombination,
    relativeLogCombination_exteriorWedge] using hswap

/-- The linear final step reflects actual model coefficient membership
back to the original subspace and proves the actual pure exterior conclusion.
Its membership inputs are the outputs of the separate geometric theorem. -/
theorem original_mixed_representation_mem_pure_of_actual_model_coefficients
    (e : RationalFunctionField (d := d) ≃ₐ[ℂ] G) (P : Submodule ℂ (ι → ℂ))
    (z : ⋀[ℂ]^2 (ι → ℂ))
    (c : Fin (Module.finrank ℂ (A.modelLogarithmicSubspace e P)) → ι → ℂ)
    (hc : (∑ i, exteriorWedge (k := ℂ)
      (A.originalBasisFromModelNativeBasis e P i : ι → ℂ) (c i)) = z)
    (hmem : ∀ i, A.modelLogarithmicRealization e (c i) ∈ A.modelLogarithmicSubspace e P) :
    z ∈ pureExterior P := by
  classical
  rw [← hc]
  apply Submodule.sum_mem
  intro i _
  exact exteriorWedge_mem_pure P (A.originalBasisFromModelNativeBasis e P i)
    ⟨c i, (A.modelLogarithmicRealization_mem_modelLogarithmicSubspace_iff e P (c i)).mp (hmem i)⟩

end AffineArrangement

end ChenRanks
