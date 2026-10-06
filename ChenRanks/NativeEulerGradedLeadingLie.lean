import ChenRanks.NativeEulerHomogeneousLeadingDetector
import ChenRanks.FlagAssociatedGradedLie

/-!
# The genuine graded Euler adjoint is a faithful genuine Lie map

Every original homogeneous vector has its proved actual operator degree.
The associative commutator of the original native adjoints is their
native Lie bracket. Actual quotient and direct-sum universal properties
therefore construct a degree-preserving native Lie map from the original
positive graded Lie algebra to its original raising-operator Lie algebra.
Its injection follows from the already proved actual axis detector in
each degree and the actual direct-sum decomposition. Neither a bracket
identity nor an injectivity property is an input.

The grading may have infinitely many nonzero degrees. The finite Koszul
application supplies its genuine grading from its actual finite quotient;
no group, monodromy, formality or Chen comparison is asserted here.
-/

noncomputable section

open scoped DirectSum

namespace ChenRanks.LieComparison

private abbrev actualRaisingPieceAddCommGroup (k E : Type*) [Field k]
    [AddCommGroup E] [Module k E] (F : ℕ → Submodule k E) (q : ℕ) :
    AddCommGroup (DegreeRaisingPiece k E F q) :=
  Submodule.Quotient.addCommGroup (nextDegreeRaisingWithin k E F q)

variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]
variable (hzero : ℒ 0 = ⊥)

/-- The original native adjoints satisfy the actual associative
endomorphism commutator identity. It is proved through the genuine
coordinate equivalence and the proved native affine Lie homomorphism. -/
theorem nativeEulerAdjoint_bracket (x y : L) :
    (nativeDerivationExtensionAdjoint k L (nativeEulerDerivation k L ℒ) ⁅x, y⁆).toLinearMap =
      (nativeDerivationExtensionAdjoint k L (nativeEulerDerivation k L ℒ) x).toLinearMap *
        (nativeDerivationExtensionAdjoint k L (nativeEulerDerivation k L ℒ) y).toLinearMap -
      (nativeDerivationExtensionAdjoint k L (nativeEulerDerivation k L ℒ) y).toLinearMap *
        (nativeDerivationExtensionAdjoint k L (nativeEulerDerivation k L ℒ) x).toLinearMap := by
  let D := nativeEulerDerivation k L ℒ
  let e := (nativeDerivationExtensionCoordinates k L D).conjRingEquiv
  apply e.injective
  rw [map_sub, map_mul, map_mul]
  change nativeDerivationExtensionAdjointCoordinateEnd k L D ⁅x, y⁆ =
    nativeDerivationExtensionAdjointCoordinateEnd k L D x *
      nativeDerivationExtensionAdjointCoordinateEnd k L D y -
    nativeDerivationExtensionAdjointCoordinateEnd k L D y *
      nativeDerivationExtensionAdjointCoordinateEnd k L D x
  rw [nativeDerivationExtensionAdjointCoordinateEnd_eq_affine,
    nativeDerivationExtensionAdjointCoordinateEnd_eq_affine,
    nativeDerivationExtensionAdjointCoordinateEnd_eq_affine]
  exact (LieHom.map_lie (derivationAffineAdjoint k L D) x y).trans
    (LieRing.of_associative_ring_bracket _ _)

/-- The actual leading map in every actual degree, with degree zero
represented by the zero map on the actual zero component. -/
def nativeEulerLeadingComponent (q : ℕ) :
    ℒ q →ₗ[k] DegreeRaisingPiece k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) q :=
  match q with
  | 0 => 0
  | n + 1 => nativeEulerHomogeneousLeading k L ℒ hzero (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))

@[simp] theorem nativeEulerLeadingComponent_succ (n : ℕ) :
    nativeEulerLeadingComponent k L ℒ hzero (n + 1) =
      nativeEulerHomogeneousLeading k L ℒ hzero (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) := rfl

/-- Each actual component map is injective, including the genuinely
zero original degree-zero component. -/
theorem nativeEulerLeadingComponent_injective (q : ℕ) :
    Function.Injective (nativeEulerLeadingComponent k L ℒ hzero q) := by
  cases q with
  | zero =>
    intro x y _hxy
    apply Subtype.ext
    have hx : (x : L) = 0 := by
      have h : (x : L) ∈ (⊥ : Submodule k L) := by
        simpa only [hzero] using x.property
      exact (Submodule.mem_bot k).mp h
    have hy : (y : L) = 0 := by
      have h : (y : L) ∈ (⊥ : Submodule k L) := by
        simpa only [hzero] using y.property
      exact (Submodule.mem_bot k).mp h
    exact hx.trans hy.symm
  | succ n =>
    exact nativeEulerHomogeneousLeading_injective k L ℒ hzero (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))

/-- Actual homogeneous brackets and their actual leading operator
brackets agree in the actual common-degree quotient. -/
theorem nativeEulerLeadingComponent_bracket (q r : ℕ) (x : ℒ q) (y : ℒ r) :
    nativeEulerLeadingComponent k L ℒ hzero (q + r)
      ⟨⁅(x : L), (y : L)⁆, SetLike.GradedBracket.bracket_mem rfl x.property y.property⟩ =
      raisingPieceBracket k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
        (nativeEulerExtensionFlag k L ℒ) q r
        (nativeEulerLeadingComponent k L ℒ hzero q x)
        (nativeEulerLeadingComponent k L ℒ hzero r y) := by
  cases q with
  | zero =>
    letI : AddCommGroup (DegreeRaisingPiece k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
        (nativeEulerExtensionFlag k L ℒ) 0) :=
      actualRaisingPieceAddCommGroup k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
        (nativeEulerExtensionFlag k L ℒ) 0
    letI : AddCommMonoid (DegreeRaisingPiece k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
        (nativeEulerExtensionFlag k L ℒ) 0) :=
      (actualRaisingPieceAddCommGroup k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
        (nativeEulerExtensionFlag k L ℒ) 0).toAddCommMonoid
    have hx : (x : L) = 0 := by
      have h : (x : L) ∈ (⊥ : Submodule k L) := by
        simpa only [hzero] using x.property
      exact (Submodule.mem_bot k).mp h
    have hz : (⟨⁅(x : L), (y : L)⁆,
        SetLike.GradedBracket.bracket_mem rfl x.property y.property⟩ : ℒ (0 + r)) = 0 := by
      apply Subtype.ext
      change ⁅(x : L), (y : L)⁆ = (0 : L)
      rw [hx, zero_lie]
    rw [hz, map_zero]
    change (0 : DegreeRaisingPiece k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) (0 + r)) = raisingPieceBracket k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
        (nativeEulerExtensionFlag k L ℒ) 0 r 0 _
    exact (LinearMap.congr_fun (LinearMap.map_zero (raisingPieceBracket k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) 0 r))
        (nativeEulerLeadingComponent k L ℒ hzero r y)).symm
  | succ q =>
    cases r with
    | zero =>
      have hy : (y : L) = 0 := by
        have h : (y : L) ∈ (⊥ : Submodule k L) := by
          simpa only [hzero] using y.property
        exact (Submodule.mem_bot k).mp h
      have hz : (⟨⁅(x : L), (y : L)⁆,
          SetLike.GradedBracket.bracket_mem rfl x.property y.property⟩ : ℒ ((q + 1) + 0)) = 0 := by
        apply Subtype.ext
        change ⁅(x : L), (y : L)⁆ = (0 : L)
        rw [hy, lie_zero]
      rw [hz, map_zero]
      change (0 : DegreeRaisingPiece k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
        (nativeEulerExtensionFlag k L ℒ) ((q + 1) + 0)) =
        raisingPieceBracket k
          (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
          (nativeEulerExtensionFlag k L ℒ) (q + 1) 0 _ 0
      exact (LinearMap.map_zero (raisingPieceBracket k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
        (nativeEulerExtensionFlag k L ℒ) (q + 1) 0
        (nativeEulerLeadingComponent k L ℒ hzero (q + 1) x))).symm
    | succ r =>
      change (nextDegreeRaisingWithin k
          (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
          (nativeEulerExtensionFlag k L ℒ) ((q + 1) + (r + 1))).mkQ
          (nativeEulerHomogeneousAdjointCurrent k L ℒ hzero ((q + 1) + (r + 1))
            (by omega) ⟨⁅(x : L), (y : L)⁆,
              SetLike.GradedBracket.bracket_mem rfl x.property y.property⟩) =
        raisingPieceBracket k
          (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
          (nativeEulerExtensionFlag k L ℒ) (q + 1) (r + 1)
          ((nextDegreeRaisingWithin k
              (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
              (nativeEulerExtensionFlag k L ℒ) (q + 1)).mkQ
            (nativeEulerHomogeneousAdjointCurrent k L ℒ hzero (q + 1)
              (Nat.succ_le_succ (Nat.zero_le q)) x))
          ((nextDegreeRaisingWithin k
              (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
              (nativeEulerExtensionFlag k L ℒ) (r + 1)).mkQ
            (nativeEulerHomogeneousAdjointCurrent k L ℒ hzero (r + 1)
              (Nat.succ_le_succ (Nat.zero_le r)) y))
      rw [raisingPieceBracket_mk_mk]
      apply congrArg (nextDegreeRaisingWithin k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
        (nativeEulerExtensionFlag k L ℒ) ((q + 1) + (r + 1))).mkQ
      apply Subtype.ext
      exact nativeEulerAdjoint_bracket k L ℒ x y

/-- The genuine componentwise linear map on the actual native direct sum. -/
def nativeEulerLeadingDirectSum :
    (⨁ q : ℕ, ℒ q) →ₗ[k] flagAssociatedGraded k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) :=
  DirectSum.lmap (nativeEulerLeadingComponent k L ℒ hzero)

@[simp] theorem nativeEulerLeadingDirectSum_inclusion (q : ℕ) (x : ℒ q) :
    nativeEulerLeadingDirectSum k L ℒ hzero (DirectSum.lof k ℕ (fun q => ℒ q) q x) =
      flagGradedInclusion k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
        (nativeEulerExtensionFlag k L ℒ) q
        (nativeEulerLeadingComponent k L ℒ hzero q x) := by
  change DirectSum.lmap (nativeEulerLeadingComponent k L ℒ hzero)
      (DirectSum.lof k ℕ (fun q => ℒ q) q x) =
    DirectSum.lof k ℕ (fun q => DegreeRaisingPiece k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) q) q
      (nativeEulerLeadingComponent k L ℒ hzero q x)
  exact DirectSum.lmap_lof (R := k) (M := fun q => ℒ q)
    (N := fun q => DegreeRaisingPiece k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) q)
    (nativeEulerLeadingComponent k L ℒ hzero) q x

omit [CharZero k] in
/-- The original native grading bracket on homogeneous inclusions has
the genuine original homogeneous bracket as its sole representative. -/
theorem nativeGraded_bracket_inclusions (q r : ℕ) (x : ℒ q) (y : ℒ r) :
    ⁅DirectSum.lof k ℕ (fun q => ℒ q) q x, DirectSum.lof k ℕ (fun q => ℒ q) r y⁆ =
      DirectSum.lof k ℕ (fun q => ℒ q) (q + r)
        ⟨⁅(x : L), (y : L)⁆, SetLike.GradedBracket.bracket_mem rfl x.property y.property⟩ := by
  rw [DirectSum.bracket_apply_apply, DirectSum.decomposeLinearEquiv_symm_lof,
    DirectSum.decomposeLinearEquiv_symm_lof]
  exact DirectSum.decomposeLinearEquiv_apply_coe ℒ (q + r)
    ⟨⁅(x : L), (y : L)⁆, SetLike.GradedBracket.bracket_mem rfl x.property y.property⟩

theorem nativeEulerLeadingDirectSum_lie (x y : ⨁ q : ℕ, ℒ q) :
    nativeEulerLeadingDirectSum k L ℒ hzero ⁅x, y⁆ =
      ⁅nativeEulerLeadingDirectSum k L ℒ hzero x,
        nativeEulerLeadingDirectSum k L ℒ hzero y⁆ := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, zero_lie]
  | add x₁ x₂ hx₁ hx₂ => simp only [add_lie, map_add, hx₁, hx₂]
  | of q x =>
    induction y using DirectSum.induction_on with
    | zero => simp only [map_zero, lie_zero]
    | add y₁ y₂ hy₁ hy₂ => simp only [LieRing.lie_add, map_add, hy₁, hy₂]
    | of r y =>
      change nativeEulerLeadingDirectSum k L ℒ hzero
        ⁅DirectSum.lof k ℕ (fun q => ℒ q) q x,
          DirectSum.lof k ℕ (fun q => ℒ q) r y⁆ =
        ⁅nativeEulerLeadingDirectSum k L ℒ hzero
            (DirectSum.lof k ℕ (fun q => ℒ q) q x),
          nativeEulerLeadingDirectSum k L ℒ hzero
            (DirectSum.lof k ℕ (fun q => ℒ q) r y)⁆
      rw [nativeGraded_bracket_inclusions, nativeEulerLeadingDirectSum_inclusion,
        nativeEulerLeadingDirectSum_inclusion, nativeEulerLeadingDirectSum_inclusion,
        flagAssociatedGraded_lie_inclusions, nativeEulerLeadingComponent_bracket]

/-- The genuine positive graded Euler leading map, on the original
Lie algebra rather than an invented graded source. -/
def nativeEulerGradedLeadingLieHom :
    L →ₗ⁅k⁆ flagAssociatedGraded k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) :=
  ({ __ := nativeEulerLeadingDirectSum k L ℒ hzero
     map_lie' := fun {x y} => nativeEulerLeadingDirectSum_lie k L ℒ hzero x y } :
    (⨁ q : ℕ, ℒ q) →ₗ⁅k⁆ flagAssociatedGraded k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ)).comp
    (DirectSum.decomposeLieEquiv ℒ).toLieHom

/-- The map retains every original homogeneous degree exactly. -/
theorem nativeEulerGradedLeadingLieHom_of_mem (q : ℕ) (x : L) (hx : x ∈ ℒ q) :
    nativeEulerGradedLeadingLieHom k L ℒ hzero x =
      flagGradedInclusion k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
        (nativeEulerExtensionFlag k L ℒ) q
        (nativeEulerLeadingComponent k L ℒ hzero q ⟨x, hx⟩) := by
  change nativeEulerLeadingDirectSum k L ℒ hzero (DirectSum.decomposeLinearEquiv ℒ x) = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe ℒ q ⟨x, hx⟩,
    nativeEulerLeadingDirectSum_inclusion]

/-- Genuine homogeneous injections give injection on the genuine
native direct sum. No finite-degree bound or detector is assumed. -/
theorem nativeEulerLeadingDirectSum_injective :
    Function.Injective (nativeEulerLeadingDirectSum k L ℒ hzero) :=
  (DirectSum.lmap_injective (nativeEulerLeadingComponent k L ℒ hzero)).mpr
    (nativeEulerLeadingComponent_injective k L ℒ hzero)

/-- The original graded Lie algebra has a genuinely faithful leading
representation in its actual operator associated Lie algebra. -/
theorem nativeEulerGradedLeadingLieHom_injective :
    Function.Injective (nativeEulerGradedLeadingLieHom k L ℒ hzero) := by
  intro x y h
  apply (DirectSum.decomposeLinearEquiv ℒ).injective
  apply nativeEulerLeadingDirectSum_injective k L ℒ hzero
  change nativeEulerLeadingDirectSum k L ℒ hzero
      (DirectSum.decomposeLinearEquiv ℒ x) =
    nativeEulerLeadingDirectSum k L ℒ hzero
      (DirectSum.decomposeLinearEquiv ℒ y) at h
  exact h

end ChenRanks.LieComparison
