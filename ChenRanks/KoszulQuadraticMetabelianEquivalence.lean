import ChenRanks.KoszulToQuadraticMetabelianDerived

/-!
# Actual inverse maps for the quadratic metabelian Lie presentation

The polynomial-linear map from the original Koszul module to the native
derived ideal was constructed from actual Jacobi and the original
quadratic ideal. The quotient's genuine universal map to the Koszul Lie
model gives the opposite map. Its polynomial linearity is proved by
induction in the actual symmetric algebra. The two original quotient
maps are proved inverse, first on original second tensors and then by
the genuine free-Lie universal property.

The finite-dimensional characteristic-zero hypotheses are used only for
the previously proved exact Koszul presentation. No freeness of the
derived ideal, graded dimension formula, formality, or Chen comparison
is asserted as input data.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.LieComparison

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [Module k V]
variable {ι : Type*} (b : _root_.Module.Basis ι k V)
variable (K : Submodule k (⋀[k]^2 V))

local instance originalKoszulBaseModule : Module k (Koszul.Module k V K) :=
  Submodule.Quotient.module' (S := k) (LinearMap.range (Koszul.relationMap k V K))

local instance originalKoszulBaseSMulZeroClass : SMulZeroClass k (Koszul.Module k V K) :=
  Submodule.Quotient.smulZeroClass' (S := k)
    (LinearMap.range (Koszul.relationMap k V K))

local instance originalDerivedPolynomialModule :
    Module (Koszul.S k V) (QuadraticMetabelianDerived k V b K) :=
  adjointSymmetricModule k (QuadraticMetabelianFreeQuotient k V b K) V
    (quadraticMetabelianGenerators k V b K)
    (quadraticMetabelianFreeQuotient_derived_two_eq_bot k V b K)

local instance originalDerivedScalarTower :
    IsScalarTower k (Koszul.S k V) (QuadraticMetabelianDerived k V b K) :=
  adjointSymmetricModule_scalarTower k (QuadraticMetabelianFreeQuotient k V b K) V
    (quadraticMetabelianGenerators k V b K)
    (quadraticMetabelianFreeQuotient_derived_two_eq_bot k V b K)

local instance originalDerivedSMulCommClass :
    SMulCommClass k (Koszul.S k V) (QuadraticMetabelianDerived k V b K) :=
  adjointSymmetricModule_smulCommClass k (QuadraticMetabelianFreeQuotient k V b K) V
    (quadraticMetabelianGenerators k V b K)
    (quadraticMetabelianFreeQuotient_derived_two_eq_bot k V b K)

/-- The genuine first coordinate projection of the genuine Koszul Lie model. -/
def koszulModelGeneratorProjection : Koszul.MetabelianLieModel k V K →ₗ[k] V where
  toFun x := x.generator
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The genuine second coordinate projection to the original Koszul module. -/
def koszulModelInvariantProjection :
    Koszul.MetabelianLieModel k V K →ₗ[k] Koszul.Module k V K where
  toFun x := x.invariant
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual derived-series functoriality puts the image in the invariant coordinate. -/
theorem quadraticDerived_image_generator_eq_zero (d : QuadraticMetabelianDerived k V b K) :
    (quadraticMetabelianToKoszulModel k V b K
      (d : QuadraticMetabelianFreeQuotient k V b K)).generator = 0 := by
  have hd : quadraticMetabelianToKoszulModel k V b K
      (d : QuadraticMetabelianFreeQuotient k V b K) ∈
      LieAlgebra.derivedSeries k (Koszul.MetabelianLieModel k V K) 1 :=
    (LieIdeal.derivedSeries_map_le (f := quadraticMetabelianToKoszulModel k V b K) 1)
      (LieIdeal.mem_map (f := quadraticMetabelianToKoszulModel k V b K) d.property)
  exact Koszul.MetabelianLieModel.derived_one_le_invariantIdeal k V K hd

/-- The actual quotient Lie map, restricted to the actual derived ideal and
then projected to the original Koszul coordinate. -/
def quadraticDerivedToKoszulLinear :
    QuadraticMetabelianDerived k V b K →ₗ[k] Koszul.Module k V K :=
  (koszulModelInvariantProjection k V K).comp
    ((quadraticMetabelianToKoszulModel k V b K).toLinearMap.comp
      (QuadraticMetabelianDerived k V b K).toSubmodule.subtype)

@[simp]
theorem quadraticDerivedToKoszulLinear_apply (d : QuadraticMetabelianDerived k V b K) :
    quadraticDerivedToKoszulLinear k V b K d =
      (quadraticMetabelianToKoszulModel k V b K
        (d : QuadraticMetabelianFreeQuotient k V b K)).invariant := rfl

theorem quadraticDerivedToKoszulLinear_generator_smul (u : V)
    (d : QuadraticMetabelianDerived k V b K) :
    quadraticDerivedToKoszulLinear k V b K (SymmetricAlgebra.ι k V u • d) =
      SymmetricAlgebra.ι k V u • quadraticDerivedToKoszulLinear k V b K d := by
  rw [quadraticDerived_generator_smul]
  change (quadraticMetabelianToKoszulModel k V b K
      ⁅quadraticMetabelianGenerators k V b K u,
        (d : QuadraticMetabelianFreeQuotient k V b K)⁆).invariant = _
  rw [LieHom.map_lie, quadraticMetabelianToKoszulModel_generator]
  simp only [Koszul.MetabelianLieModel.invariant_bracket,
    Koszul.MetabelianLieModel.generatorInclusion_generator,
    Koszul.MetabelianLieModel.generatorInclusion_invariant,
    quadraticDerived_image_generator_eq_zero, map_zero, smul_zero,
    zero_add, sub_zero, quadraticDerivedToKoszulLinear_apply]

/-- Polynomial linearity follows from actual symmetric-algebra induction. -/
theorem quadraticDerivedToKoszulLinear_smul (s : Koszul.S k V)
    (d : QuadraticMetabelianDerived k V b K) :
    quadraticDerivedToKoszulLinear k V b K (s • d) =
      s • quadraticDerivedToKoszulLinear k V b K d := by
  induction s using SymmetricAlgebra.induction generalizing d with
  | algebraMap c => simp only [algebraMap_smul, map_smul]
  | ι u => exact quadraticDerivedToKoszulLinear_generator_smul k V b K u d
  | mul s t hs ht => rw [mul_smul, hs, ht, mul_smul]
  | add s t hs ht => rw [add_smul, map_add, hs, ht, add_smul]

/-- The actual reverse polynomial-linear map into the original quotient. -/
def quadraticDerivedToKoszul :
    QuadraticMetabelianDerived k V b K →ₗ[Koszul.S k V] Koszul.Module k V K where
  toFun := quadraticDerivedToKoszulLinear k V b K
  map_add' := (quadraticDerivedToKoszulLinear k V b K).map_add
  map_smul' s d := quadraticDerivedToKoszulLinear_smul k V b K s d

@[simp]
theorem quadraticDerivedToKoszul_apply (d : QuadraticMetabelianDerived k V b K) :
    quadraticDerivedToKoszul k V b K d = quadraticDerivedToKoszulLinear k V b K d := rfl

/-- The reverse map computes on actual original generator brackets. -/
theorem quadraticDerivedToKoszul_bracket_wedge (u v : V) :
    quadraticDerivedToKoszul k V b K
      (quadraticDerivedBracket k V b K (exteriorWedge u v)) =
        Koszul.wedgeClassBilinear k V K u v := by
  change (quadraticMetabelianToKoszulModel k V b K
    (quadraticDerivedBracket k V b K (exteriorWedge u v) :
      QuadraticMetabelianFreeQuotient k V b K)).invariant = _
  rw [quadraticDerivedBracket_exteriorWedge, LieHom.map_lie,
    quadraticMetabelianToKoszulModel_generator,
    quadraticMetabelianToKoszulModel_generator,
    Koszul.MetabelianLieModel.generators_bracket]
  rfl

theorem quadraticDerivedToKoszul_bracket (w : ⋀[k]^2 V) :
    quadraticDerivedToKoszul k V b K (quadraticDerivedBracket k V b K w) =
      Koszul.constantWedgeClass k V K w := by
  have h : (quadraticDerivedToKoszul k V b K).restrictScalars k ∘ₗ
      quadraticDerivedBracket k V b K = Koszul.constantWedgeClass k V K := by
    apply exteriorPower.linearMap_ext
    ext a
    have ha : exteriorPower.ιMulti k 2 a = exteriorWedge (a 0) (a 1) := by
      change exteriorPower.ιMulti k 2 a = exteriorPower.ιMulti k 2 ![a 0, a 1]
      congr 1
      funext i
      fin_cases i <;> rfl
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, ha, quadraticDerivedToKoszul_bracket_wedge]
    rfl
  exact LinearMap.congr_fun h w

variable [FiniteDimensional k V] [CharZero k]

/-- One inverse identity is proved on the original second tensor term. -/
theorem quadraticDerivedToKoszul_comp_koszulModuleToQuadraticDerived :
    quadraticDerivedToKoszul k V b K ∘ₗ koszulModuleToQuadraticDerived k V b K =
      LinearMap.id := by
  have h : (quadraticDerivedToKoszul k V b K ∘ₗ
      koszulModuleToQuadraticDerived k V b K) ∘ₗ Koszul.secondTensorToModule k V K =
      Koszul.secondTensorToModule k V K := by
    apply AlgebraTensorModule.ext
    intro s w
    simp only [LinearMap.comp_apply,
      koszulModuleToQuadraticDerived_secondTensorToModule,
      secondTensorToQuadraticDerived_tmul, map_smul,
      quadraticDerivedToKoszul_bracket, Koszul.constantWedgeClass_apply]
    exact ((Koszul.secondTensorToModule k V K).map_smul s
      ((1 : Koszul.S k V) ⊗ₜ[k] w)).symm.trans (by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one])
  apply LinearMap.ext
  intro m
  obtain ⟨z, rfl⟩ := Koszul.secondTensorToModule_surjective k V K m
  exact LinearMap.congr_fun h z

theorem quadraticDerivedToKoszul_koszulModuleToQuadraticDerived (m : Koszul.Module k V K) :
    quadraticDerivedToKoszul k V b K (koszulModuleToQuadraticDerived k V b K m) = m :=
  LinearMap.congr_fun
    (quadraticDerivedToKoszul_comp_koszulModuleToQuadraticDerived k V b K) m

/-- The actual original-module map, followed by the actual derived subtype inclusion. -/
def koszulModuleToQuadraticLie :
    Koszul.Module k V K →ₗ[k] QuadraticMetabelianFreeQuotient k V b K :=
  (QuadraticMetabelianDerived k V b K).toSubmodule.subtype.comp
    ((koszulModuleToQuadraticDerived k V b K).restrictScalars k)

@[simp]
theorem koszulModuleToQuadraticLie_apply (m : Koszul.Module k V K) :
    koszulModuleToQuadraticLie k V b K m =
      (koszulModuleToQuadraticDerived k V b K m :
        QuadraticMetabelianFreeQuotient k V b K) := rfl

/-- The original invariant module map computes on the original constant wedge. -/
theorem koszulModuleToQuadraticLie_wedgeClass (u v : V) :
    koszulModuleToQuadraticLie k V b K (Koszul.wedgeClassBilinear k V K u v) =
      ⁅quadraticMetabelianGenerators k V b K u,
        quadraticMetabelianGenerators k V b K v⁆ :=
  koszulModuleToQuadraticDerived_constantWedge k V b K u v

theorem koszulModuleToQuadraticLie_generator_smul (u : V) (m : Koszul.Module k V K) :
    koszulModuleToQuadraticLie k V b K (SymmetricAlgebra.ι k V u • m) =
      ⁅quadraticMetabelianGenerators k V b K u, koszulModuleToQuadraticLie k V b K m⁆ := by
  change (koszulModuleToQuadraticDerived k V b K (SymmetricAlgebra.ι k V u • m) :
    QuadraticMetabelianFreeQuotient k V b K) = _
  rw [map_smul, quadraticDerived_generator_smul]
  rfl

/-- Two actual images of invariant elements bracket to zero, by actual
second-derived vanishing in the actual quotient. -/
theorem koszulModuleToQuadraticLie_bracket_eq_zero (m n : Koszul.Module k V K) :
    ⁅koszulModuleToQuadraticLie k V b K m, koszulModuleToQuadraticLie k V b K n⁆ = 0 := by
  have h := LieSubmodule.lie_mem_lie
    (koszulModuleToQuadraticDerived k V b K m).property
    (koszulModuleToQuadraticDerived k V b K n).property
  change ⁅koszulModuleToQuadraticLie k V b K m,
    koszulModuleToQuadraticLie k V b K n⁆ ∈
      LieAlgebra.derivedSeries k (QuadraticMetabelianFreeQuotient k V b K) 2 at h
  rw [quadraticMetabelianFreeQuotient_derived_two_eq_bot,
    LieSubmodule.mem_bot] at h
  exact h

/-- The actual reverse vector-linear map, using both genuine coordinates. -/
def koszulModelToQuadraticLinear :
    Koszul.MetabelianLieModel k V K →ₗ[k] QuadraticMetabelianFreeQuotient k V b K :=
  (quadraticMetabelianGenerators k V b K).comp (koszulModelGeneratorProjection k V K) +
    (koszulModuleToQuadraticLie k V b K).comp (koszulModelInvariantProjection k V K)

@[simp]
theorem koszulModelToQuadraticLinear_apply (x : Koszul.MetabelianLieModel k V K) :
    koszulModelToQuadraticLinear k V b K x =
      quadraticMetabelianGenerators k V b K x.generator +
        koszulModuleToQuadraticLie k V b K x.invariant := rfl

/-- Jacobi-derived scalar action and actual metabelianity make the reverse
coordinate map a genuine Lie homomorphism. -/
def koszulModelToQuadratic :
    Koszul.MetabelianLieModel k V K →ₗ⁅k⁆ QuadraticMetabelianFreeQuotient k V b K where
  __ := koszulModelToQuadraticLinear k V b K
  map_lie' := by
    intro x y
    change koszulModelToQuadraticLinear k V b K ⁅x, y⁆ =
      ⁅koszulModelToQuadraticLinear k V b K x,
        koszulModelToQuadraticLinear k V b K y⁆
    simp only [koszulModelToQuadraticLinear_apply,
      Koszul.MetabelianLieModel.generator_bracket,
      Koszul.MetabelianLieModel.invariant_bracket, map_zero, zero_add,
      map_add, map_sub, koszulModuleToQuadraticLie_wedgeClass,
      koszulModuleToQuadraticLie_generator_smul, add_lie, lie_add,
      koszulModuleToQuadraticLie_bracket_eq_zero, add_zero]
    rw [← lie_skew (koszulModuleToQuadraticLie k V b K x.invariant)
      (quadraticMetabelianGenerators k V b K y.generator)]
    abel

@[simp]
theorem koszulModelToQuadratic_generator (u : V) :
    koszulModelToQuadratic k V b K (Koszul.MetabelianLieModel.generatorInclusion k V K u) =
      quadraticMetabelianGenerators k V b K u := by
  change quadraticMetabelianGenerators k V b K u + koszulModuleToQuadraticLie k V b K 0 = _
  rw [map_zero, add_zero]

omit [FiniteDimensional k V] [CharZero k] in
theorem quadraticMetabelianToKoszulModel_derived (d : QuadraticMetabelianDerived k V b K) :
    quadraticMetabelianToKoszulModel k V b K
        (d : QuadraticMetabelianFreeQuotient k V b K) =
      Koszul.MetabelianLieModel.invariantInclusion k V K
        (quadraticDerivedToKoszul k V b K d) := by
  apply Koszul.MetabelianLieModel.ext
  · exact quadraticDerived_image_generator_eq_zero k V b K d
  · rfl

/-- The actual module calculation identifies the image of every original invariant. -/
theorem quadraticMetabelianToKoszulModel_koszulModuleToQuadraticLie
    (m : Koszul.Module k V K) :
    quadraticMetabelianToKoszulModel k V b K (koszulModuleToQuadraticLie k V b K m) =
      Koszul.MetabelianLieModel.invariantInclusion k V K m := by
  rw [koszulModuleToQuadraticLie_apply, quadraticMetabelianToKoszulModel_derived,
    quadraticDerivedToKoszul_koszulModuleToQuadraticDerived]

/-- The first actual Lie inverse identity holds on both original coordinates. -/
theorem quadraticMetabelianToKoszulModel_koszulModelToQuadratic
    (x : Koszul.MetabelianLieModel k V K) :
    quadraticMetabelianToKoszulModel k V b K (koszulModelToQuadratic k V b K x) = x := by
  change quadraticMetabelianToKoszulModel k V b K
    (quadraticMetabelianGenerators k V b K x.generator +
      koszulModuleToQuadraticLie k V b K x.invariant) = x
  rw [map_add, quadraticMetabelianToKoszulModel_generator,
    quadraticMetabelianToKoszulModel_koszulModuleToQuadraticLie]
  apply Koszul.MetabelianLieModel.ext <;> simp

/-- The second inverse identity follows from the genuine original free-Lie
universal property and genuine quotient surjectivity. -/
theorem koszulModelToQuadratic_quadraticMetabelianToKoszulModel
    (x : QuadraticMetabelianFreeQuotient k V b K) :
    koszulModelToQuadratic k V b K (quadraticMetabelianToKoszulModel k V b K x) = x := by
  have h : (koszulModelToQuadratic k V b K).comp
      ((quadraticMetabelianToKoszulModel k V b K).comp
        (quadraticMetabelianProjection k V b K)) = quadraticMetabelianProjection k V b K := by
    apply FreeLieAlgebra.hom_ext
    intro i
    change koszulModelToQuadratic k V b K
      (quadraticMetabelianToKoszulModel k V b K
        (quadraticMetabelianProjection k V b K (FreeLieAlgebra.of k i))) = _
    rw [← quadraticMetabelianGenerators_basis,
      quadraticMetabelianToKoszulModel_generator, koszulModelToQuadratic_generator,
      quadraticMetabelianGenerators_basis]
  obtain ⟨y, rfl⟩ := quadraticMetabelianProjection_surjective k V b K x
  exact DFunLike.congr_fun h y

/-- The original native quadratic metabelian free-Lie quotient is genuinely
Lie-equivalent to the original Koszul Lie model. -/
def quadraticMetabelianKoszulLieEquiv :
    QuadraticMetabelianFreeQuotient k V b K ≃ₗ⁅k⁆ Koszul.MetabelianLieModel k V K :=
  LieEquiv.ofBijective (quadraticMetabelianToKoszulModel k V b K)
    ⟨Function.LeftInverse.injective
      (koszulModelToQuadratic_quadraticMetabelianToKoszulModel k V b K),
      Function.RightInverse.surjective
        (quadraticMetabelianToKoszulModel_koszulModelToQuadratic k V b K)⟩

/-- The native derived ideal and the original Koszul quotient are genuinely
equivalent with their actual polynomial adjoint and coefficient actions. -/
def quadraticMetabelianDerivedKoszulEquiv :
    QuadraticMetabelianDerived k V b K ≃ₗ[Koszul.S k V] Koszul.Module k V K where
  __ := quadraticDerivedToKoszul k V b K
  invFun := koszulModuleToQuadraticDerived k V b K
  left_inv d := by
    apply Subtype.ext
    have h := koszulModelToQuadratic_quadraticMetabelianToKoszulModel k V b K
      (d : QuadraticMetabelianFreeQuotient k V b K)
    rw [quadraticMetabelianToKoszulModel_derived] at h
    change quadraticMetabelianGenerators k V b K 0 +
      koszulModuleToQuadraticLie k V b K (quadraticDerivedToKoszul k V b K d) =
      (d : QuadraticMetabelianFreeQuotient k V b K) at h
    simpa only [map_zero, zero_add, koszulModuleToQuadraticLie_apply] using h
  right_inv := quadraticDerivedToKoszul_koszulModuleToQuadraticDerived k V b K

end ChenRanks.LieComparison
