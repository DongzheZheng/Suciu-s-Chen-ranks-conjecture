import ChenRanks.DifferentialFieldTransport
import ChenRanks.ExteriorSeparation

/-!
# Actual exterior relations under the constructed field comparison

The target is the native exterior algebra over the actual target field,
not an exterior algebra over the unchanged source field.  Its source-field
algebra action is the actual composite through the field equivalence.
The genuine differential map becomes a source-field linear generator
map into this target.  Its squares vanish by the native exterior-algebra
relation, so the universal lift constructs the actual algebra map.
Wedge preservation and transport of mixed finite relations are conclusions.
-/

namespace ChenRanks

noncomputable section

open scoped BigOperators

variable {k F G : Type*} [Field k] [CharZero k] [Field F] [Field G]
  [Algebra k F] [Algebra k G]

/-- The actual source-field action on the actual target-field exterior
algebra is the actual field equivalence followed by its native scalar map. -/
abbrev fieldEquivExteriorTargetAlgebra (e : F ≃ₐ[k] G) :
    Algebra F (ExteriorAlgebra G Ω[G⁄k]) :=
  Algebra.compHom (ExteriorAlgebra G Ω[G⁄k]) e.toRingHom

/-- The actual differential generator map is source-field linear for
the constructed target action; native semilinearity proves this. -/
def differentialExteriorFieldGenerator (e : F ≃ₐ[k] G) :
    letI : Algebra F (ExteriorAlgebra G Ω[G⁄k]) := fieldEquivExteriorTargetAlgebra e
    Ω[F⁄k] →ₗ[F] ExteriorAlgebra G Ω[G⁄k] := by
  letI : Algebra F (ExteriorAlgebra G Ω[G⁄k]) := fieldEquivExteriorTargetAlgebra e
  refine
    { toFun := fun ω => ExteriorAlgebra.ι G (differentialFieldLinearEquiv e ω)
      map_add' := ?_
      map_smul' := ?_ }
  · intro ω η
    rw [map_add, map_add]
  · intro a ω
    rw [differentialFieldLinearEquiv_smul, map_smul]
    simp only [Algebra.smul_def]
    rfl

/-- The actual universal exterior lift supplies the map between native
exterior algebras over the two different actual fields. -/
def differentialExteriorFieldHom (e : F ≃ₐ[k] G) :
    letI : Algebra F (ExteriorAlgebra G Ω[G⁄k]) := fieldEquivExteriorTargetAlgebra e
    ExteriorAlgebra F Ω[F⁄k] →ₐ[F] ExteriorAlgebra G Ω[G⁄k] := by
  letI : Algebra F (ExteriorAlgebra G Ω[G⁄k]) := fieldEquivExteriorTargetAlgebra e
  exact ExteriorAlgebra.lift F ⟨differentialExteriorFieldGenerator e,
    fun ω => ExteriorAlgebra.ι_sq_zero (differentialFieldLinearEquiv e ω)⟩

/-- The universal lift carries the actual degree-one generator. -/
@[simp]
theorem differentialExteriorFieldHom_ι (e : F ≃ₐ[k] G) (ω : Ω[F⁄k]) :
    letI : Algebra F (ExteriorAlgebra G Ω[G⁄k]) := fieldEquivExteriorTargetAlgebra e
    differentialExteriorFieldHom e (ExteriorAlgebra.ι F ω) =
      ExteriorAlgebra.ι G (differentialFieldLinearEquiv e ω) := by
  letI : Algebra F (ExteriorAlgebra G Ω[G⁄k]) := fieldEquivExteriorTargetAlgebra e
  exact ExteriorAlgebra.lift_ι_apply F (differentialExteriorFieldGenerator e)
    (fun ω => ExteriorAlgebra.ι_sq_zero (differentialFieldLinearEquiv e ω)) ω

/-- The actual lift is semilinear with exactly the original field map. -/
theorem differentialExteriorFieldHom_smul (e : F ≃ₐ[k] G)
    (a : F) (z : ExteriorAlgebra F Ω[F⁄k]) :
    letI : Algebra F (ExteriorAlgebra G Ω[G⁄k]) := fieldEquivExteriorTargetAlgebra e
    differentialExteriorFieldHom e (a • z) = e a • differentialExteriorFieldHom e z := by
  letI : Algebra F (ExteriorAlgebra G Ω[G⁄k]) := fieldEquivExteriorTargetAlgebra e
  rw [map_smul]
  simp only [Algebra.smul_def]
  rfl

/-- Wedge preservation follows from the actual algebra lift and native
degree-one multiplication formula; it is not a hypothesis. -/
theorem differentialExteriorFieldHom_wedge (e : F ≃ₐ[k] G)
    (ω η : Ω[F⁄k]) :
    letI : Algebra F (ExteriorAlgebra G Ω[G⁄k]) := fieldEquivExteriorTargetAlgebra e
    differentialExteriorFieldHom e
        (exteriorWedge (k := F) ω η : ExteriorAlgebra F Ω[F⁄k]) =
      (exteriorWedge (k := G) (differentialFieldLinearEquiv e ω)
        (differentialFieldLinearEquiv e η) : ExteriorAlgebra G Ω[G⁄k]) := by
  letI : Algebra F (ExteriorAlgebra G Ω[G⁄k]) := fieldEquivExteriorTargetAlgebra e
  rw [exteriorWedge_coe, exteriorWedge_coe, map_mul,
    differentialExteriorFieldHom_ι, differentialExteriorFieldHom_ι]

/-- Every actual finite mixed quadratic relation is preserved, including
relations with arbitrary original rational-function coefficients. -/
theorem differentialFieldTransport_mixed_relation
    (e : F ≃ₐ[k] G) {I J : Type*} [Fintype I] [Fintype J]
    (β : I → J → F) (ω : J → Ω[F⁄k]) (p : I → Ω[F⁄k])
    (h : (∑ i, ∑ j, β i j • exteriorWedge (k := F) (ω j) (p i)) = 0) :
    (∑ i, ∑ j, e (β i j) • exteriorWedge (k := G)
      (differentialFieldLinearEquiv e (ω j))
      (differentialFieldLinearEquiv e (p i))) = 0 := by
  letI : Algebra F (ExteriorAlgebra G Ω[G⁄k]) := fieldEquivExteriorTargetAlgebra e
  have hEA : (∑ i, ∑ j, β i j •
      (exteriorWedge (k := F) (ω j) (p i) : ExteriorAlgebra F Ω[F⁄k])) = 0 := by
    simpa only [map_sum, map_smul, map_zero] using
      congrArg (Submodule.subtype (ExteriorAlgebra.exteriorPower F 2 Ω[F⁄k])) h
  have ht := congrArg (fun z => differentialExteriorFieldHom e z) hEA
  have ht' : (∑ i, ∑ j, e (β i j) •
      (exteriorWedge (k := G) (differentialFieldLinearEquiv e (ω j))
        (differentialFieldLinearEquiv e (p i)) : ExteriorAlgebra G Ω[G⁄k])) = 0 := by
    simpa only [map_sum, map_zero,
      differentialExteriorFieldHom_smul, differentialExteriorFieldHom_wedge] using ht
  apply (ExteriorAlgebra.exteriorPower G 2 Ω[G⁄k]).subtype_injective
  simpa only [map_sum, map_smul, map_zero] using ht'

/-- In particular actual coefficients in the original constant field
remain those same constants after the actual field comparison. -/
theorem differentialFieldTransport_constant_mixed_relation
    (e : F ≃ₐ[k] G) {I J : Type*} [Fintype I] [Fintype J]
    (β : I → J → k) (ω : J → Ω[F⁄k]) (p : I → Ω[F⁄k])
    (h : (∑ i, ∑ j, algebraMap k F (β i j) •
      exteriorWedge (k := F) (ω j) (p i)) = 0) :
    (∑ i, ∑ j, algebraMap k G (β i j) • exteriorWedge (k := G)
      (differentialFieldLinearEquiv e (ω j))
      (differentialFieldLinearEquiv e (p i))) = 0 := by
  simpa only [e.commutes] using
    differentialFieldTransport_mixed_relation e (fun i j => algebraMap k F (β i j)) ω p h

end

end ChenRanks
