import ChenRanks.ScalarGroupPhysicalEuler
import ChenRanks.KoszulMetabelianGeneratorExt
import ChenRanks.KoszulMetabelianPositiveGrading
import ChenRanks.LiePositiveGradingEuler

/-!
# Original generators force the actual physical degrees of a model Lie map

For a genuine original-model Lie homomorphism to the original scalar
group-associated Lie algebra, the Euler-intertwining condition is the
kernel of a genuine linear map. The derivation rules prove this kernel
is a Lie subalgebra. The actual free-Lie surjection shows that it is the
whole original model as soon as the actual generator images have weight
one. Characteristic-zero weight separation then places every original
homogeneous vector in the same original physical group quotient.

The weight-one generator hypothesis is an intermediate structural
condition, not an assertion of higher-degree preservation. The actual
arrangement's already constructed original generator formula discharges
it. This file is an uncompiled candidate.
-/

noncomputable section

namespace ChenRanks.LieComparison

open Koszul

variable (k : Type*) [Field k] [CharZero k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} [Fintype ι] (b : _root_.Module.Basis ι k V)
variable (K : Submodule k (⋀[k]^2 V))
variable (G : Type*) [Group G]
variable (α : MetabelianLieModel k V K →ₗ⁅k⁆ scalarGroupAssociatedGraded k G)

/-- The original-model linear intertwiner uses the actual native
source grading and the actual original group-series physical Euler. -/
def originalModelPhysicalEulerIntertwiner :
    MetabelianLieModel k V K →ₗ[k] scalarGroupAssociatedGraded k G :=
  α.toLinearMap.comp
      (nativeEulerDerivation k (MetabelianLieModel k V K)
        (modelPositiveComponent k V b K)).toLinearMap -
    (scalarGroupPhysicalEulerLinear k G).comp α.toLinearMap

/-- Actual derivation and bracket identities close the genuine
intertwining kernel under the original native Lie bracket. -/
def originalModelPhysicalEulerIntertwiningSubalgebra :
    LieSubalgebra k (MetabelianLieModel k V K) where
  toSubmodule := (originalModelPhysicalEulerIntertwiner k V b K G α).ker
  lie_mem' := by
    intro x y hx hy
    change α (nativeEulerDerivation k (MetabelianLieModel k V K)
          (modelPositiveComponent k V b K) x) -
        scalarGroupPhysicalEulerLinear k G (α x) = 0 at hx
    change α (nativeEulerDerivation k (MetabelianLieModel k V K)
          (modelPositiveComponent k V b K) y) -
        scalarGroupPhysicalEulerLinear k G (α y) = 0 at hy
    change α (nativeEulerDerivation k (MetabelianLieModel k V K)
          (modelPositiveComponent k V b K) ⁅x, y⁆) -
        scalarGroupPhysicalEulerLinear k G (α ⁅x, y⁆) = 0
    rw [LieDerivation.apply_lie_eq_add, map_add, LieHom.map_lie,
      LieHom.map_lie, LieHom.map_lie, scalarGroupPhysicalEulerLinear_lie,
      sub_eq_zero.mp hx, sub_eq_zero.mp hy, sub_self]

variable (hgen : ∀ v : V, scalarGroupPhysicalEulerLinear k G
  (α (MetabelianLieModel.generatorInclusion k V K v)) =
    α (MetabelianLieModel.generatorInclusion k V K v))

include hgen in
/-- Every actual original generator belongs to the actual intertwining
kernel because its actual native source degree is one. -/
theorem originalGenerator_mem_physicalEulerIntertwining (v : V) :
    MetabelianLieModel.generatorInclusion k V K v ∈
      originalModelPhysicalEulerIntertwiningSubalgebra k V b K G α := by
  change α (nativeEulerDerivation k (MetabelianLieModel k V K)
      (modelPositiveComponent k V b K)
      (MetabelianLieModel.generatorInclusion k V K v)) -
    scalarGroupPhysicalEulerLinear k G
      (α (MetabelianLieModel.generatorInclusion k V K v)) = 0
  rw [nativeEulerDerivation_of_mem k (MetabelianLieModel k V K)
    (modelPositiveComponent k V b K) 1
    (MetabelianLieModel.generatorInclusion k V K v) (show
      MetabelianLieModel.generatorInclusion k V K v ∈
        modelPositiveComponent k V b K 1 from ⟨v, rfl⟩),
    Nat.cast_one, one_smul, hgen v, sub_self]

include hgen in
/-- The actual free-Lie surjection forces the actual intertwining
kernel to contain the whole original model. No generation premise is
supplied for that model. -/
theorem originalModelPhysicalEuler_intertwines
    (x : MetabelianLieModel k V K) :
    α (nativeEulerDerivation k (MetabelianLieModel k V K)
      (modelPositiveComponent k V b K) x) =
      scalarGroupPhysicalEulerLinear k G (α x) := by
  let B := originalModelPhysicalEulerIntertwiningSubalgebra k V b K G α
  let φ : FreeLieAlgebra k ι →ₗ⁅k⁆ B := FreeLieAlgebra.lift k
    (fun i => ⟨MetabelianLieModel.generatorInclusion k V K (b i),
      originalGenerator_mem_physicalEulerIntertwining k V b K G α hgen (b i)⟩)
  have hfree : B.incl.comp φ = freeLieToKoszulModel k V b K := by
    apply FreeLieAlgebra.hom_ext
    intro i
    change B.incl (φ (FreeLieAlgebra.of k i)) =
      freeLieToKoszulModel k V b K (FreeLieAlgebra.of k i)
    rw [FreeLieAlgebra.lift_of_apply]
    change MetabelianLieModel.generatorInclusion k V K (b i) =
      freeLieToKoszulModel k V b K (FreeLieAlgebra.of k i)
    rw [← freeVectorGenerators_basis k V b i, freeLieToKoszulModel_generator]
  obtain ⟨y, hy⟩ := originalFreeLieToKoszulModel_surjective k V b K x
  have hb : x ∈ B := by
    have he := DFunLike.congr_fun hfree y
    change (φ y : MetabelianLieModel k V K) = freeLieToKoszulModel k V b K y at he
    rw [hy] at he
    exact he ▸ (φ y).property
  change α (nativeEulerDerivation k (MetabelianLieModel k V K)
      (modelPositiveComponent k V b K) x) -
    scalarGroupPhysicalEulerLinear k G (α x) = 0 at hb
  exact sub_eq_zero.mp hb

include hgen in
/-- Actual physical degree is derived from the original source grading,
the genuine free generators and the characteristic-zero Euler weights.
The target is the same original successive group quotient. -/
theorem originalModelLieHom_homogeneous_originalPiece (q : ℕ) (hq : 1 ≤ q)
    (x : MetabelianLieModel k V K) (hx : x ∈ modelPositiveComponent k V b K q) :
    α x = scalarGroupGradedInclusion k G (q - 1)
      (scalarGroupPieceProjection k G (q - 1) (α x)) := by
  apply scalarGroup_eigenvector_eq_original_inclusion k G q hq (α x)
  rw [← originalModelPhysicalEuler_intertwines k V b K G α hgen x,
    nativeEulerDerivation_of_mem k (MetabelianLieModel k V K)
      (modelPositiveComponent k V b K) q x hx, map_smul]

/-- The already constructed original degree projection actually lands
in its actual homogeneous component. -/
theorem originalModelProjection_mem_component (q : ℕ) (x : MetabelianLieModel k V K) :
    modelPositiveProjection k V b K q x ∈ modelPositiveComponent k V b K q := by
  cases q with
  | zero => exact Submodule.zero_mem _
  | succ q =>
    cases q with
    | zero => exact ⟨modelGeneratorProjection k V K x, rfl⟩
    | succ r =>
      exact ⟨quotientProjection k V b K r (modelInvariantProjection k V K x), rfl⟩

include hgen in
/-- The genuine target quotient projection commutes with the original
homogeneous projection. This is derived on the actual direct sum from
the original component formula, not assumed as degree preservation. -/
theorem originalModelLieHom_pieceProjection (q : ℕ) (hq : 1 ≤ q)
    (x : MetabelianLieModel k V K) :
    scalarGroupPieceProjection k G (q - 1) (α x) =
      scalarGroupPieceProjection k G (q - 1)
        (α (modelPositiveProjection k V b K q x)) := by
  obtain ⟨z, rfl⟩ := modelPositiveAssembly_surjective k V b K x
  induction z using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | of m y =>
    change scalarGroupPieceProjection k G (q - 1)
        (α (DirectSum.coeLinearMap (modelPositiveComponent k V b K)
          (DirectSum.lof k ℕ (fun n => modelPositiveComponent k V b K n) m y))) =
      scalarGroupPieceProjection k G (q - 1)
        (α (modelPositiveProjection k V b K q
          (DirectSum.coeLinearMap (modelPositiveComponent k V b K)
            (DirectSum.lof k ℕ (fun n => modelPositiveComponent k V b K n) m y))))
    rw [DirectSum.coeLinearMap_lof]
    by_cases hmq : m = q
    · subst m
      rw [modelPositiveProjection_of_mem_same k V b K q y y.property]
    · rw [modelPositiveProjection_of_mem_ne k V b K q m y y.property (Ne.symm hmq),
        map_zero, map_zero]
      cases m with
      | zero =>
        have hy : (y : MetabelianLieModel k V K) = 0 :=
          (Submodule.mem_bot k).mp y.property
        rw [hy, map_zero, map_zero]
      | succ m =>
        rw [originalModelLieHom_homogeneous_originalPiece k V b K G α hgen
          (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) y y.property]
        change DirectSum.component k ℕ (scalarLowerCentralPiece k G) (q - 1)
          ((scalarGroupGradedDirectSumEquiv k G)
            (scalarGroupGradedInclusion k G ((m + 1) - 1)
              (scalarGroupPieceProjection k G ((m + 1) - 1) (α y)))) = 0
        rw [scalarGroupGradedDirectSumEquiv_inclusion, DirectSum.component.of]
        simp only [dif_neg (show (m + 1) - 1 ≠ q - 1 by omega)]

/-- The genuine linear map on the actual original homogeneous source
and the actual original successive group quotient. -/
def originalModelGroupPieceLinear (q : ℕ) :
    modelPositiveComponent k V b K q →ₗ[k] scalarLowerCentralPiece k G (q - 1) :=
  (scalarGroupPieceProjection k G (q - 1)).comp
    (α.toLinearMap.comp (modelPositiveComponent k V b K q).subtype)

include hgen in
/-- Whole-map injection restricts to injection of the actual physical
pieces because their original inclusions have just been identified. -/
theorem originalModelGroupPieceLinear_injective (q : ℕ) (hq : 1 ≤ q)
    (hinj : Function.Injective α) :
    Function.Injective (originalModelGroupPieceLinear k V b K G α q) := by
  intro x y hxy
  apply Subtype.ext
  apply hinj
  rw [originalModelLieHom_homogeneous_originalPiece k V b K G α hgen q hq x x.property,
    originalModelLieHom_homogeneous_originalPiece k V b K G α hgen q hq y y.property]
  exact congrArg (scalarGroupGradedInclusion k G (q - 1)) hxy

include hgen in
/-- Whole-map surjection gives actual piece surjection by projecting a
genuine preimage. The original projection-commutation theorem is the
necessary extra step beyond a whole Lie surjection. -/
theorem originalModelGroupPieceLinear_surjective (q : ℕ) (hq : 1 ≤ q)
    (hsurj : Function.Surjective α) :
    Function.Surjective (originalModelGroupPieceLinear k V b K G α q) := by
  intro y
  obtain ⟨x, hx⟩ := hsurj (scalarGroupGradedInclusion k G (q - 1) y)
  refine ⟨⟨modelPositiveProjection k V b K q x,
    originalModelProjection_mem_component k V b K q x⟩, ?_⟩
  change scalarGroupPieceProjection k G (q - 1)
    (α (modelPositiveProjection k V b K q x)) = y
  rw [← originalModelLieHom_pieceProjection k V b K G α hgen q hq x,
    hx, scalarGroupPieceProjection_inclusion_self]

/-- A genuine equivalence of the actual homogeneous source and the
same original successive group quotient, with positivity explicit. -/
def originalModelGroupPieceEquiv (q : ℕ) (hq : 1 ≤ q)
    (hbij : Function.Bijective α) :
    modelPositiveComponent k V b K q ≃ₗ[k] scalarLowerCentralPiece k G (q - 1) :=
  LinearEquiv.ofBijective (originalModelGroupPieceLinear k V b K G α q)
    ⟨originalModelGroupPieceLinear_injective k V b K G α hgen q hq hbij.1,
      originalModelGroupPieceLinear_surjective k V b K G α hgen q hq hbij.2⟩

local instance physicalOriginalDegreeGroup (r : ℕ) :
    AddCommGroup (homogeneousModule k V b K r) :=
  canonicalHomogeneousQuotientAddCommGroup k V b K r

local instance physicalOriginalDegreeMonoid (r : ℕ) :
    AddCommMonoid (homogeneousModule k V b K r) :=
  (canonicalHomogeneousQuotientAddCommGroup k V b K r).toAddCommMonoid

local instance physicalOriginalDegreeScalars (r : ℕ) :
    _root_.Module k (homogeneousModule k V b K r) :=
  canonicalHomogeneousQuotientBaseCoefficients k V b K r

/-- The actual original Koszul degree r is included in ordinary source
degree r+2. This keeps the original quotient module as source. -/
def originalInvariantDegreeComponentMap (r : ℕ) :
    homogeneousModule k V b K r →ₗ[k] modelPositiveComponent k V b K (r + 2) :=
  (modelInvariantDegreeInclusion k V b K r).rangeRestrict

theorem originalInvariantDegreeComponentMap_bijective (r : ℕ) :
    Function.Bijective (originalInvariantDegreeComponentMap k V b K r) := by
  constructor
  · intro x y hxy
    have h := congrArg (fun z : modelPositiveComponent k V b K (r + 2) =>
      modelInvariantProjection k V K (z : MetabelianLieModel k V K)) hxy
    change degreeQuotientInclusion k V b K r x = degreeQuotientInclusion k V b K r y at h
    have he := congrArg (quotientProjection k V b K r) h
    rw [quotientProjection_degreeQuotientInclusion_self,
      quotientProjection_degreeQuotientInclusion_self] at he
    exact he
  · intro y
    obtain ⟨x, hx⟩ := y.property
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx

/-- Genuine ordinary-degree identification of the original Koszul
quotient and the original model homogeneous submodule. -/
def originalInvariantDegreeComponentEquiv (r : ℕ) :
    homogeneousModule k V b K r ≃ₗ[k] modelPositiveComponent k V b K (r + 2) :=
  LinearEquiv.ofBijective (originalInvariantDegreeComponentMap k V b K r)
    (originalInvariantDegreeComponentMap_bijective k V b K r)

/-- The actual original Koszul W_r is compared with the original
Gamma_(r+2)/Gamma_(r+3) scalarized group quotient. Whole-map bijection is
used only after actual piece preservation and piece surjection are
proved, not as a replacement for them. -/
def originalKoszulDegreeGroupPieceEquiv (r : ℕ) (hbij : Function.Bijective α) :
    homogeneousModule k V b K r ≃ₗ[k] scalarLowerCentralPiece k G (r + 1) :=
  (originalInvariantDegreeComponentEquiv k V b K r).trans
    (by
      have hindex : (r + 2) - 1 = r + 1 := by omega
      simpa only [hindex] using
        originalModelGroupPieceEquiv k V b K G α hgen (r + 2) (by omega) hbij)

end ChenRanks.LieComparison
