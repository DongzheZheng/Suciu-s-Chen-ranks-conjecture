import ChenRanks.NativeEulerExponentialRaisingDeviation
import ChenRanks.NativeEulerHomogeneousLeadingDetector
import ChenRanks.NativeEulerAxisAbelianCharacter

/-!
# The actual first operator leading class is determined by the actual axis character

The original native adjoint is linear. Every actual degree-two tail
vector has its actual adjoint in J_2, by the real homogeneous grading.
It therefore induces a true linear map from the original tail quotient
to J_1/J_2. Genuine exponential remainder and the actual Euler identity
on the first quotient identify every actual exponential group's first
operator class with this map applied to its actual axis character.

There is no supplied first-term identity, geometric period, generator
classification, representation condition or comparison detector. The
geometric monodromy must still compute the actual axis character using
its actual angular integral; this algebraic identity does not assume or
perform that computation.
-/

noncomputable section

namespace ChenRanks.LieComparison

private def actualFirstRaisingQuotientMap (k E M : Type*) [Field k]
    [AddCommGroup E] [Module k E] [AddCommGroup M] [Module k M]
    (F : ℕ → Submodule k E)
    (f : M →ₗ[k] degreeRaisingEndomorphisms k E F 1) :
    M →ₗ[k] DegreeRaisingPiece k E F 1 :=
  (nextDegreeRaisingWithin k E F 1).mkQ.comp f

variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]
variable (hzero : ℒ 0 = ⊥)

/-- The genuine linear original native adjoint, retaining the original
inner derivation and its original endomorphism. -/
def nativeEulerAdjointLinear :
    L →ₗ[k] Module.End k (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ)) :=
  -((LieDerivation.toLinearMapLieHom k
    (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))).toLinearMap.comp
      ((LieDerivation.inner k
          (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
          (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))).comp
        (nativeDerivationExtensionOriginal k L (nativeEulerDerivation k L ℒ)).toLinearMap))

omit [CharZero k] in
@[simp] theorem nativeEulerAdjointLinear_apply (x : L) :
    nativeEulerAdjointLinear k L ℒ x =
      (nativeDerivationExtensionAdjoint k L (nativeEulerDerivation k L ℒ) x).toLinearMap := rfl

include hzero

include hzero in
/-- The actual whole graded tail, not just individual homogeneous
vectors, has its actual adjoint in the actual same-degree operator space. -/
theorem nativeEulerAdjoint_mem_degree_of_mem_tail (q : ℕ) (hq : 1 ≤ q)
    (x : L) (hx : x ∈ nativeGradedTail k L ℒ q) :
    nativeEulerAdjointLinear k L ℒ x ∈ degreeRaisingEndomorphisms k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) q := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨i, hqi, hai⟩ := ha
    rw [nativeEulerAdjointLinear_apply]
    exact degreeRaisingEndomorphisms_antitone k _ _
      (nativeEulerExtensionFlag_antitone k L ℒ) q i hqi
      (nativeEulerExtensionAdjoint_mem_homogeneous_degree k L ℒ hzero i
        (hq.trans hqi) a hai)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- The original native adjoint is a genuine current-degree-one map. -/
def nativeEulerFirstAdjointCurrent :
    L →ₗ[k] degreeRaisingEndomorphisms k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) 1 :=
  (nativeEulerAdjointLinear k L ℒ).codRestrict _
    (fun x => nativeEulerExtensionAdjoint_mem_raisingEndomorphisms k L ℒ hzero x)

/-- The original actual first operator leading map before descent. -/
def nativeEulerFirstAdjointLeading : L →ₗ[k] DegreeRaisingPiece k
    (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
    (nativeEulerExtensionFlag k L ℒ) 1 :=
  actualFirstRaisingQuotientMap k
    (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ)) L
    (nativeEulerExtensionFlag k L ℒ) (nativeEulerFirstAdjointCurrent k L ℒ hzero)

theorem nativeEulerTail_two_le_firstLeading_ker :
    nativeGradedTail k L ℒ 2 ≤ (nativeEulerFirstAdjointLeading k L ℒ hzero).ker := by
  intro x hx
  change (nextDegreeRaisingWithin k _ _ 1).mkQ
    (nativeEulerFirstAdjointCurrent k L ℒ hzero x) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact nativeEulerAdjoint_mem_degree_of_mem_tail k L ℒ hzero 2 (by omega) x hx

/-- True descent along the actual original degree-two tail. -/
def nativeEulerAbelianLeading :
    (L ⧸ nativeGradedTail k L ℒ 2) →ₗ[k] DegreeRaisingPiece k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) 1 :=
  (nativeGradedTail k L ℒ 2).liftQ
    (nativeEulerFirstAdjointLeading k L ℒ hzero)
    (nativeEulerTail_two_le_firstLeading_ker k L ℒ hzero)

@[simp] theorem nativeEulerAbelianLeading_mk (x : L) :
    nativeEulerAbelianLeading k L ℒ hzero ((nativeGradedTail k L ℒ 2).mkQ x) =
      nativeEulerFirstAdjointLeading k L ℒ hzero x :=
  Submodule.liftQ_apply _ _ _

include hzero in
/-- The genuine Euler acts as the identity on the genuine original
first-degree quotient. This is proved from the original decomposition. -/
theorem nativeEuler_sub_identity_mem_two (x : L) :
    nativeEulerDerivation k L ℒ x - x ∈ nativeGradedTail k L ℒ 2 := by
  have h : (nativeGradedTail k L ℒ 2).mkQ.comp
      ((nativeEulerDerivation k L ℒ).toLinearMap - LinearMap.id) = 0 := by
    apply DirectSum.decompose_lhom_ext ℒ
    intro i
    apply LinearMap.ext
    intro a
    change (nativeGradedTail k L ℒ 2).mkQ
      (nativeEulerDerivation k L ℒ (a : L) - a) = 0
    cases i with
    | zero =>
      have ha : (a : L) = 0 := by
        have ha : (a : L) ∈ (⊥ : Submodule k L) := by
          simpa only [hzero] using a.property
        exact (Submodule.mem_bot k).mp ha
      rw [ha, map_zero, sub_self, map_zero]
    | succ i =>
      cases i with
      | zero =>
        rw [nativeEulerDerivation_of_mem k L ℒ 1 a a.property]
        simp only [Nat.cast_one, one_smul, sub_self, map_zero]
      | succ i =>
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        have ha := mem_nativeGradedTail_of_mem k L ℒ 2 (i + 1 + 1) a (by omega) a.property
        rw [nativeEulerDerivation_of_mem k L ℒ (i + 1 + 1) a a.property]
        exact Submodule.sub_mem _
          (Submodule.smul_mem _ ((i + 1 + 1 : ℕ) : k) ha) ha
  apply (Submodule.Quotient.mk_eq_zero _).mp
  exact LinearMap.congr_fun h x

include hzero in
/-- The actual finite exponential's original axis displacement has
the same actual first-degree quotient as its original exponent. -/
theorem nativeEulerAxisDisplacement_sub_identity_mem_two (c : ℕ) (x : L) :
    nativeEulerAxisDisplacement k L ℒ c x - x ∈ nativeGradedTail k L ℒ 2 := by
  have ha := nativeEulerAxisDisplacement_sub_euler_mem_two k L ℒ hzero c x
  have hb := nativeEuler_sub_identity_mem_two k L ℒ hzero x
  convert (nativeGradedTail k L ℒ 2).add_mem ha hb using 1
  abel

variable (c : ℕ) (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥)

/-- Every actual native exponential subgroup element supplies its real
current deviation, using the proved subgroup-wide degree-one theorem. -/
def nativeEulerExponentialDifferenceCurrent
    (T : nativeEulerExponentialSubgroup k L ℒ hzero c hbound) :
    degreeRaisingEndomorphisms k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) 1 :=
  ⟨(nativeLieAutomorphismUnitsEnd k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ)) T.val :
      Module.End k (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))) - 1,
    nativeEulerExponentialSubgroup_raising_deviation k L ℒ hzero c hbound T⟩

/-- The genuine first operator class of every genuine native subgroup
element is exactly the actual abelian leading map of its actual axis
character. No period or first-term equation is supplied. -/
theorem nativeEulerExponentialFirstLeading_eq_axisCharacter
    (T : nativeEulerExponentialSubgroup k L ℒ hzero c hbound) :
    (nextDegreeRaisingWithin k _ _ 1).mkQ
      (nativeEulerExponentialDifferenceCurrent k L ℒ hzero c hbound T) =
      nativeEulerAbelianLeading k L ℒ hzero
        (Multiplicative.toAdd (nativeEulerAxisAbelianCharacter k L ℒ hzero c hbound T)) := by
  obtain ⟨x, hx⟩ := T.property
  have hd := nativeEulerEnd_exp_sub_one_sub_mem_two k L ℒ
    (nativeDerivationExtensionAdjoint k L (nativeEulerDerivation k L ℒ) x).toLinearMap
    (nativeEulerExtensionAdjoint_mem_raisingEndomorphisms k L ℒ hzero x)
    (nativeDerivationExtensionAdjoint_isNilpotent_of_positive_finite_grading
      k L ℒ hzero c hbound (nativeEulerDerivation k L ℒ) x)
  have htail : x - nativeEulerAxisDisplacement k L ℒ c x ∈ nativeGradedTail k L ℒ 2 := by
    have h := (nativeGradedTail k L ℒ 2).neg_mem
      (nativeEulerAxisDisplacement_sub_identity_mem_two k L ℒ hzero c x)
    simpa only [neg_sub] using h
  have ha := nativeEulerAdjoint_mem_degree_of_mem_tail k L ℒ hzero 2 (by omega)
    (x - nativeEulerAxisDisplacement k L ℒ c x) htail
  rw [map_sub, nativeEulerAdjointLinear_apply, nativeEulerAdjointLinear_apply] at ha
  change (nextDegreeRaisingWithin k _ _ 1).mkQ
      (nativeEulerExponentialDifferenceCurrent k L ℒ hzero c hbound T) =
    nativeEulerAbelianLeading k L ℒ hzero ((nativeGradedTail k L ℒ 2).mkQ
      ((nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ))
        (T.val (nativeDerivationExtensionAxis k L (nativeEulerDerivation k L ℒ)))).2)
  rw [← hx, nativePositiveFiniteGradingExponential_axis_displacement,
    nativeEulerAbelianLeading_mk]
  apply (Submodule.Quotient.eq _).mpr
  change (nativeLieAutomorphismUnitsEnd k _ T.val : Module.End k _) - 1 -
    (nativeDerivationExtensionAdjoint k L (nativeEulerDerivation k L ℒ)
      (nativeEulerAxisDisplacement k L ℒ c x)).toLinearMap ∈
    degreeRaisingEndomorphisms k _ _ 2
  rw [← hx, nativeEulerExponentialUnitsEnd_eq_exp]
  convert (degreeRaisingEndomorphisms k _ _ 2).add_mem hd ha using 1 <;> abel

end ChenRanks.LieComparison
