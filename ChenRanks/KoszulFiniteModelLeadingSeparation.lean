import ChenRanks.NativeEulerGradedLeadingLie
import ChenRanks.KoszulMetabelianFiniteTruncation

/-!
# The actual finite quotient leading maps separate the original Koszul Lie model

Each genuine finite-tail quotient has its proved actual positive grading.
The genuine graded Euler leading Lie map is faithful on that quotient.
Composing with the original native finite projection gives a genuine
family of Lie maps on the original Koszul model. Their common kernel is
zero, because the original actual homogeneous decomposition is a genuine
finite sum for each original element.

The conclusion supplies no group representation, monodromy period,
formality or Chen comparison. To compare with the original Chen Lie one
must still identify the genuine monodromy leading maps with this same
family, using their actual degree-one generator values.
-/

noncomputable section

namespace ChenRanks.Koszul

open ChenRanks.LieComparison

variable (k : Type*) [Field k] [CharZero k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} [Fintype ι] (b : _root_.Module.Basis ι k V)
variable (K : Submodule k (⋀[k]^2 V))

private abbrev actualFiniteLeadingPieceGroups (R E : Type*) [Field R]
    [AddCommGroup E] [_root_.Module R E] (F : ℕ → Submodule R E) :
    (i : ℕ) → AddCommGroup (DegreeRaisingPiece R E F i) :=
  fun i => Submodule.Quotient.addCommGroup (nextDegreeRaisingWithin R E F i)

local instance finiteLeadingOriginalPieceGroups (c : ℕ) :
    (i : ℕ) → AddCommGroup (DegreeRaisingPiece k
      (NativeDerivationExtension k (finiteModelTruncation k V b K c)
        (nativeEulerDerivation k (finiteModelTruncation k V b K c)
          (finiteModelComponent k V b K c)))
      (nativeEulerExtensionFlag k (finiteModelTruncation k V b K c)
        (finiteModelComponent k V b K c)) i) :=
  actualFiniteLeadingPieceGroups k
    (NativeDerivationExtension k (finiteModelTruncation k V b K c)
      (nativeEulerDerivation k (finiteModelTruncation k V b K c)
        (finiteModelComponent k V b K c)))
    (nativeEulerExtensionFlag k (finiteModelTruncation k V b K c)
      (finiteModelComponent k V b K c))

/-- The genuine leading Lie map of the genuine finite quotient's
actual native positive grading. -/
def finiteModelLeadingLieHom (c : ℕ) :
    finiteModelTruncation k V b K c →ₗ⁅k⁆ flagAssociatedGraded k
      (NativeDerivationExtension k (finiteModelTruncation k V b K c)
        (nativeEulerDerivation k (finiteModelTruncation k V b K c)
          (finiteModelComponent k V b K c)))
      (nativeEulerExtensionFlag k (finiteModelTruncation k V b K c)
        (finiteModelComponent k V b K c)) :=
  nativeEulerGradedLeadingLieHom k (finiteModelTruncation k V b K c)
    (finiteModelComponent k V b K c) (finiteModelComponent_zero k V b K c)

/-- Faithfulness is proved for the actual native finite quotient,
including the genuine zero quotient at truncation bound zero. -/
theorem finiteModelLeadingLieHom_injective (c : ℕ) :
    Function.Injective (finiteModelLeadingLieHom k V b K c) :=
  nativeEulerGradedLeadingLieHom_injective k (finiteModelTruncation k V b K c)
    (finiteModelComponent k V b K c) (finiteModelComponent_zero k V b K c)

/-- The actual family of original projection-followed leading maps. -/
def originalModelFiniteLeading (c : ℕ) :
    MetabelianLieModel k V K →ₗ⁅k⁆ flagAssociatedGraded k
      (NativeDerivationExtension k (finiteModelTruncation k V b K c)
        (nativeEulerDerivation k (finiteModelTruncation k V b K c)
          (finiteModelComponent k V b K c)))
      (nativeEulerExtensionFlag k (finiteModelTruncation k V b K c)
        (finiteModelComponent k V b K c)) :=
  (finiteModelLeadingLieHom k V b K c).comp (finiteModelProjection k V b K c)

theorem originalModelFiniteLeading_eq_zero_iff (c : ℕ)
    (x : MetabelianLieModel k V K) :
    originalModelFiniteLeading k V b K c x = 0 ↔ finiteModelProjection k V b K c x = 0 := by
  constructor
  · intro h
    apply finiteModelLeadingLieHom_injective k V b K c
    exact h.trans (map_zero (finiteModelLeadingLieHom k V b K c)).symm
  · intro h
    change finiteModelLeadingLieHom k V b K c (finiteModelProjection k V b K c x) = 0
    rw [h, map_zero]

omit [CharZero k] in
/-- All actual finite-tail projections separate the actual original
Koszul model. No filtration-separation hypothesis is supplied. -/
theorem originalModel_eq_zero_of_all_finite_projections
    (x : MetabelianLieModel k V K)
    (hx : ∀ c : ℕ, finiteModelProjection k V b K c x = 0) : x = 0 := by
  have hp (n : ℕ) : modelPositiveProjection k V b K n x = 0 := by
    have hxIdeal : x ∈ (modelTruncationIdeal k V b K n).toSubmodule :=
      (Submodule.Quotient.mk_eq_zero _).mp (hx n)
    exact LinearMap.mem_ker.mp
      (modelTruncationIdeal_le_projection_ker k V b K n n le_rfl hxIdeal)
  obtain ⟨N, hN⟩ := modelPositiveProjection_finite_sum k V b K x
  exact hN.trans (by simp only [hp, Finset.sum_const_zero, zero_add])

/-- The actual faithful quotient maps together genuinely detect every
original element, by the original finite homogeneous decomposition. -/
theorem originalModel_eq_zero_of_all_finite_leading
    (x : MetabelianLieModel k V K)
    (hx : ∀ c : ℕ, originalModelFiniteLeading k V b K c x = 0) : x = 0 :=
  originalModel_eq_zero_of_all_finite_projections k V b K x
    (fun c => (originalModelFiniteLeading_eq_zero_iff k V b K c x).mp (hx c))

omit [CharZero k] in
/-- The actual original finite generator belongs to the actual quotient
component one, from the original image definition rather than a degree
preservation assumption. -/
theorem finiteOriginalGenerator_mem_component_one (c : ℕ) (v : V) :
    finiteModelProjection k V b K c (MetabelianLieModel.generatorInclusion k V K v) ∈
      finiteModelComponent k V b K c 1 :=
  ⟨MetabelianLieModel.generatorInclusion k V K v, ⟨v, rfl⟩, rfl⟩

/-- The actual family has the actual generator leading value in the
actual physical operator degree one. -/
theorem originalModelFiniteLeading_generator (c : ℕ) (v : V) :
    originalModelFiniteLeading k V b K c (MetabelianLieModel.generatorInclusion k V K v) =
      flagGradedInclusion k
        (NativeDerivationExtension k (finiteModelTruncation k V b K c)
          (nativeEulerDerivation k (finiteModelTruncation k V b K c)
            (finiteModelComponent k V b K c)))
        (nativeEulerExtensionFlag k (finiteModelTruncation k V b K c)
          (finiteModelComponent k V b K c)) 1
        (nativeEulerLeadingComponent k (finiteModelTruncation k V b K c)
          (finiteModelComponent k V b K c) (finiteModelComponent_zero k V b K c) 1
          ⟨finiteModelProjection k V b K c (MetabelianLieModel.generatorInclusion k V K v),
            finiteOriginalGenerator_mem_component_one k V b K c v⟩) :=
  nativeEulerGradedLeadingLieHom_of_mem k (finiteModelTruncation k V b K c)
    (finiteModelComponent k V b K c) (finiteModelComponent_zero k V b K c) 1 _
    (finiteOriginalGenerator_mem_component_one k V b K c v)

end ChenRanks.Koszul
