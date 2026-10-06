import ChenRanks.QuadraticMetabelianFreeLie
import ChenRanks.KoszulPresentation

/-!
# The actual reverse Koszul map into the actual metabelian derived ideal

The target is the native first derived ideal of the original quadratic
metabelian free-Lie quotient. Its polynomial action is the actual adjoint
action descended through the tensor-algebra commutativity relations.
The constant second-tensor generators map to actual brackets. Jacobi
kills the actual third Koszul differential, and the original quadratic
ideal kills the original quadratic inclusion. The proved presentation of
the original Koszul quotient therefore constructs the polynomial-linear
map below. Neither a Lie–Koszul isomorphism nor a Chen comparison is a
hypothesis or a definition.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.LieComparison

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [Module k V]
variable {ι : Type*} (b : _root_.Module.Basis ι k V)
variable (K : Submodule k (⋀[k]^2 V))

/-- The native derived ideal of the original native quadratic quotient. -/
abbrev QuadraticMetabelianDerived :=
  ActualDerivedIdeal k (QuadraticMetabelianFreeQuotient k V b K)

/-- The action is constructed from actual adjoint operators; its
metabelian condition is discharged inside this instance. -/
local instance actualQuadraticDerivedPolynomialModule :
    Module (Koszul.S k V) (QuadraticMetabelianDerived k V b K) :=
  adjointSymmetricModule k (QuadraticMetabelianFreeQuotient k V b K) V
    (quadraticMetabelianGenerators k V b K)
    (quadraticMetabelianFreeQuotient_derived_two_eq_bot k V b K)

local instance actualQuadraticDerivedScalarTower :
    IsScalarTower k (Koszul.S k V) (QuadraticMetabelianDerived k V b K) :=
  adjointSymmetricModule_scalarTower k (QuadraticMetabelianFreeQuotient k V b K) V
    (quadraticMetabelianGenerators k V b K)
    (quadraticMetabelianFreeQuotient_derived_two_eq_bot k V b K)

local instance actualQuadraticDerivedSMulCommClass :
    SMulCommClass k (Koszul.S k V) (QuadraticMetabelianDerived k V b K) :=
  adjointSymmetricModule_smulCommClass k (QuadraticMetabelianFreeQuotient k V b K) V
    (quadraticMetabelianGenerators k V b K)
    (quadraticMetabelianFreeQuotient_derived_two_eq_bot k V b K)

/-- Every actual generator bracket belongs to the native first derived ideal. -/
theorem quadraticMetabelianGenerators_bracket_mem_derived (u v : V) :
    ⁅quadraticMetabelianGenerators k V b K u,
      quadraticMetabelianGenerators k V b K v⁆ ∈
        QuadraticMetabelianDerived k V b K := by
  change ⁅quadraticMetabelianGenerators k V b K u,
    quadraticMetabelianGenerators k V b K v⁆ ∈
      ⁅(⊤ : LieIdeal k (QuadraticMetabelianFreeQuotient k V b K)), ⊤⁆
  exact LieSubmodule.lie_mem_lie
    (show quadraticMetabelianGenerators k V b K u ∈
      (⊤ : LieIdeal k (QuadraticMetabelianFreeQuotient k V b K)) from trivial)
    (show quadraticMetabelianGenerators k V b K v ∈
      (⊤ : LieIdeal k (QuadraticMetabelianFreeQuotient k V b K)) from trivial)

/-- Actual generator brackets, with their proved native derived membership. -/
def quadraticDerivedBracketAlternating :
    V [⋀^Fin 2]→ₗ[k] QuadraticMetabelianDerived k V b K where
  toFun a := ⟨⁅quadraticMetabelianGenerators k V b K (a 0),
    quadraticMetabelianGenerators k V b K (a 1)⁆,
    quadraticMetabelianGenerators_bracket_mem_derived k V b K (a 0) (a 1)⟩
  map_update_add' a i x y := by
    apply Subtype.ext
    fin_cases i <;> simp [Function.update, map_add, add_lie, lie_add] <;> rfl
  map_update_smul' a i c x := by
    apply Subtype.ext
    fin_cases i <;> simp [Function.update, map_smul, smul_lie] <;> rfl
  map_eq_zero_of_eq' a i j h hij := by
    apply Subtype.ext
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change a 0 = a 1 at h
      change ⁅quadraticMetabelianGenerators k V b K (a 0),
        quadraticMetabelianGenerators k V b K (a 1)⁆ = 0
      rw [h, lie_self]
    · change a 1 = a 0 at h
      change ⁅quadraticMetabelianGenerators k V b K (a 0),
        quadraticMetabelianGenerators k V b K (a 1)⁆ = 0
      rw [h, lie_self]
    · exact (hij rfl).elim

/-- The genuine exterior-square bracket map into the native derived ideal. -/
def quadraticDerivedBracket :
    (⋀[k]^2 V) →ₗ[k] QuadraticMetabelianDerived k V b K :=
  exteriorPower.alternatingMapLinearEquiv (quadraticDerivedBracketAlternating k V b K)

@[simp]
theorem quadraticDerivedBracket_exteriorWedge (u v : V) :
    (quadraticDerivedBracket k V b K (exteriorWedge u v) :
      QuadraticMetabelianFreeQuotient k V b K) =
        ⁅quadraticMetabelianGenerators k V b K u,
          quadraticMetabelianGenerators k V b K v⁆ := by
  simp only [quadraticDerivedBracket, exteriorWedge,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- The bracket map is the actual projected original free-Lie bracket map. -/
theorem quadraticDerivedBracket_coe (w : ⋀[k]^2 V) :
    (quadraticDerivedBracket k V b K w : QuadraticMetabelianFreeQuotient k V b K) =
      quadraticMetabelianProjection k V b K (freeGeneratorBracket k V b w) := by
  have h : (QuadraticMetabelianDerived k V b K).toSubmodule.subtype.comp
        (quadraticDerivedBracket k V b K) =
      (quadraticMetabelianProjection k V b K).toLinearMap.comp
        (freeGeneratorBracket k V b) := by
    apply exteriorPower.linearMap_ext
    apply DFunLike.ext
    intro a
    have ha : exteriorPower.ιMulti k 2 a = exteriorWedge (a 0) (a 1) := by
      change exteriorPower.ιMulti k 2 a = exteriorPower.ιMulti k 2 ![a 0, a 1]
      congr 1
      funext i
      fin_cases i <;> rfl
    change (quadraticDerivedBracket k V b K (exteriorPower.ιMulti k 2 a) :
      QuadraticMetabelianFreeQuotient k V b K) =
      quadraticMetabelianProjection k V b K (freeGeneratorBracket k V b (exteriorPower.ιMulti k 2 a))
    rw [ha, quadraticDerivedBracket_exteriorWedge,
      freeGeneratorBracket_exteriorWedge, LieHom.map_lie]
    rfl
  exact LinearMap.congr_fun h w

/-- The original quadratic relations vanish by the actual quotient ideal. -/
theorem quadraticDerivedBracket_eq_zero_of_mem {w : ⋀[k]^2 V} (hw : w ∈ K) :
    quadraticDerivedBracket k V b K w = 0 := by
  apply Subtype.ext
  change (quadraticDerivedBracket k V b K w :
    QuadraticMetabelianFreeQuotient k V b K) = 0
  rw [quadraticDerivedBracket_coe, quadraticMetabelianProjection_eq_zero_iff]
  have hle : quadraticRelationIdeal k V b K ≤
      quadraticMetabelianRelationIdeal k V b K := le_sup_left
  exact hle (LieSubmodule.subset_lieSpan ⟨(⟨w, hw⟩ : K), rfl⟩)

/-- Polynomial generator action is actual bracketing by the original vector generator. -/
theorem quadraticDerived_generator_smul (u : V) (d : QuadraticMetabelianDerived k V b K) :
    SymmetricAlgebra.ι k V u • d = ⁅quadraticMetabelianGenerators k V b K u, d⁆ :=
  adjointSymmetricModule_generator_smul k (QuadraticMetabelianFreeQuotient k V b K) V
    (quadraticMetabelianGenerators k V b K)
    (quadraticMetabelianFreeQuotient_derived_two_eq_bot k V b K) u d

/-- Actual Lie Jacobi gives precisely the third Koszul relation. -/
theorem quadraticDerivedBracket_jacobi (u v w : V) :
    SymmetricAlgebra.ι k V u • quadraticDerivedBracket k V b K (exteriorWedge v w) -
      SymmetricAlgebra.ι k V v • quadraticDerivedBracket k V b K (exteriorWedge u w) +
        SymmetricAlgebra.ι k V w • quadraticDerivedBracket k V b K (exteriorWedge u v) = 0 := by
  rw [quadraticDerived_generator_smul, quadraticDerived_generator_smul,
    quadraticDerived_generator_smul]
  apply Subtype.ext
  change ⁅quadraticMetabelianGenerators k V b K u,
      (quadraticDerivedBracket k V b K (exteriorWedge v w) :
        QuadraticMetabelianFreeQuotient k V b K)⁆ -
    ⁅quadraticMetabelianGenerators k V b K v,
      (quadraticDerivedBracket k V b K (exteriorWedge u w) :
        QuadraticMetabelianFreeQuotient k V b K)⁆ +
    ⁅quadraticMetabelianGenerators k V b K w,
      (quadraticDerivedBracket k V b K (exteriorWedge u v) :
        QuadraticMetabelianFreeQuotient k V b K)⁆ = 0
  simp only [quadraticDerivedBracket_exteriorWedge]
  have hj := lie_jacobi (quadraticMetabelianGenerators k V b K u)
    (quadraticMetabelianGenerators k V b K v) (quadraticMetabelianGenerators k V b K w)
  have hs : ⁅quadraticMetabelianGenerators k V b K w,
      quadraticMetabelianGenerators k V b K u⁆ =
      -⁅quadraticMetabelianGenerators k V b K u,
        quadraticMetabelianGenerators k V b K w⁆ :=
    (lie_skew (quadraticMetabelianGenerators k V b K w)
      (quadraticMetabelianGenerators k V b K u)).symm
  rw [hs, lie_neg] at hj
  simpa only [sub_eq_add_neg] using hj

/-- The actual scalar-linear extension of original generator brackets. -/
def secondTensorToQuadraticDerived :
    Koszul.C2 k V →ₗ[Koszul.S k V] QuadraticMetabelianDerived k V b K :=
  Koszul.extendScalarLinear (quadraticDerivedBracket k V b K)

@[simp]
theorem secondTensorToQuadraticDerived_tmul (s : Koszul.S k V) (w : ⋀[k]^2 V) :
    secondTensorToQuadraticDerived k V b K (s ⊗ₜ[k] w) =
      s • quadraticDerivedBracket k V b K w :=
  Koszul.extendScalarLinear_tmul (quadraticDerivedBracket k V b K) s w

theorem secondTensorToQuadraticDerived_delta3Linear :
    (secondTensorToQuadraticDerived k V b K).restrictScalars k ∘ₗ
      Koszul.delta3Linear k V = 0 := by
  apply exteriorPower.linearMap_ext
  apply DFunLike.ext
  intro a
  change secondTensorToQuadraticDerived k V b K
    (Koszul.delta3Linear k V (exteriorPower.ιMulti k 3 a)) = 0
  simp only [Koszul.delta3Linear_wedge, map_add, map_sub,
    map_smul, secondTensorToQuadraticDerived_tmul, one_smul]
  exact quadraticDerivedBracket_jacobi k V b K (a 0) (a 1) (a 2)

/-- The genuine third differential is killed on every polynomial tensor. -/
theorem secondTensorToQuadraticDerived_comp_delta3 :
    secondTensorToQuadraticDerived k V b K ∘ₗ Koszul.delta3 k V = 0 := by
  apply AlgebraTensorModule.ext
  intro s w
  simp only [LinearMap.comp_apply, Koszul.delta3_tmul, map_smul]
  have hw := LinearMap.congr_fun (secondTensorToQuadraticDerived_delta3Linear k V b K) w
  simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearMap.zero_apply, smul_zero] using
      congrArg (fun d : QuadraticMetabelianDerived k V b K => s • d) hw

/-- The actual inclusion of original quadratic relations is killed. -/
theorem secondTensorToQuadraticDerived_comp_quadraticInclusion :
    secondTensorToQuadraticDerived k V b K ∘ₗ Koszul.quadraticInclusion k V K = 0 := by
  apply AlgebraTensorModule.ext
  intro s w
  simp only [LinearMap.comp_apply, Koszul.quadraticInclusion_tmul,
    secondTensorToQuadraticDerived_tmul,
    quadraticDerivedBracket_eq_zero_of_mem k V b K w.property,
    smul_zero, LinearMap.zero_apply]
  rfl

/-- The original presentation relations lie in the actual constructed kernel. -/
theorem presentationRelations_le_secondTensorToQuadraticDerived_ker :
    LinearMap.range (Koszul.presentationRelations k V K) ≤
      LinearMap.ker (secondTensorToQuadraticDerived k V b K) := by
  rintro _ ⟨⟨y, x⟩, rfl⟩
  change secondTensorToQuadraticDerived k V b K
    (Koszul.presentationRelations k V K (y, x)) = 0
  rw [Koszul.presentationRelations_apply, map_add]
  have hy := LinearMap.congr_fun (secondTensorToQuadraticDerived_comp_delta3 k V b K) y
  have hx := LinearMap.congr_fun
    (secondTensorToQuadraticDerived_comp_quadraticInclusion k V b K) x
  change secondTensorToQuadraticDerived k V b K (Koszul.delta3 k V y) = 0 at hy
  change secondTensorToQuadraticDerived k V b K (Koszul.quadraticInclusion k V K x) = 0 at hx
  rw [hy, hx]
  exact zero_add 0

/-- Genuine descent through the actual second-tensor presentation quotient. -/
def secondTensorQuotientToQuadraticDerived :
    (Koszul.C2 k V ⧸ LinearMap.range (Koszul.presentationRelations k V K)) →ₗ[Koszul.S k V]
      QuadraticMetabelianDerived k V b K :=
  (LinearMap.range (Koszul.presentationRelations k V K)).liftQ
    (secondTensorToQuadraticDerived k V b K)
    (presentationRelations_le_secondTensorToQuadraticDerived_ker k V b K)

@[simp]
theorem secondTensorQuotientToQuadraticDerived_mk (z : Koszul.C2 k V) :
    secondTensorQuotientToQuadraticDerived k V b K (Submodule.Quotient.mk z) =
      secondTensorToQuadraticDerived k V b K z :=
  Submodule.liftQ_apply _ _ _

variable [FiniteDimensional k V] [CharZero k]

/-- The existing genuine presentation equivalence computes on the actual quotient class. -/
theorem koszulPresentationEquiv_mk (z : Koszul.C2 k V) :
    Koszul.presentationEquiv k V K (Submodule.Quotient.mk z) =
      Koszul.secondTensorToModule k V K z := rfl

theorem koszulPresentationEquiv_symm_secondTensorToModule (z : Koszul.C2 k V) :
    (Koszul.presentationEquiv k V K).symm (Koszul.secondTensorToModule k V K z) =
      Submodule.Quotient.mk z := by
  apply (Koszul.presentationEquiv k V K).injective
  rw [LinearEquiv.apply_symm_apply, koszulPresentationEquiv_mk]

/-- The original Koszul quotient maps to the native derived ideal, by the
proved presentation equivalence and the proved Jacobi kernel containment. -/
def koszulModuleToQuadraticDerived :
    Koszul.Module k V K →ₗ[Koszul.S k V] QuadraticMetabelianDerived k V b K :=
  (secondTensorQuotientToQuadraticDerived k V b K).comp
    (Koszul.presentationEquiv k V K).symm.toLinearMap

theorem koszulModuleToQuadraticDerived_secondTensorToModule (z : Koszul.C2 k V) :
    koszulModuleToQuadraticDerived k V b K (Koszul.secondTensorToModule k V K z) =
      secondTensorToQuadraticDerived k V b K z := by
  simp only [koszulModuleToQuadraticDerived, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, koszulPresentationEquiv_symm_secondTensorToModule,
    secondTensorQuotientToQuadraticDerived_mk]

/-- The actual generator calculation for the reverse original-module map. -/
theorem koszulModuleToQuadraticDerived_constantWedge (u v : V) :
    (koszulModuleToQuadraticDerived k V b K
      (Koszul.wedgeClassBilinear k V K u v) : QuadraticMetabelianFreeQuotient k V b K) =
      ⁅quadraticMetabelianGenerators k V b K u,
        quadraticMetabelianGenerators k V b K v⁆ := by
  rw [Koszul.wedgeClassBilinear_apply,
    koszulModuleToQuadraticDerived_secondTensorToModule,
    secondTensorToQuadraticDerived_tmul, one_smul,
    quadraticDerivedBracket_exteriorWedge]

end ChenRanks.LieComparison
