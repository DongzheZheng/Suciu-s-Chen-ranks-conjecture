import ChenRanks.KoszulSmallAmbientRelations
import ChenRanks.KoszulWholeSpaceComponent
import ChenRanks.KoszulCanonicalFamilyGradingObjects
import ChenRanks.FunctionPiSingleIndex

/-!
# The actual canonical homogeneous family map in dimensions at most two

This is only the low-dimensional boundary of the effective theorem.
The original quadratic kernel is genuinely zero or full. For zero
kernel the actual source and target vanish. For full kernel the actual
maximal-isotropic family is empty in dimensions zero and one, and is a
true singleton whole-space component in dimension two. Its actual map
is bijective in every degree by proved genuine functoriality. No
general effective bound or Chen comparison is claimed.
-/

noncomputable section

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]

local instance (priority := 2500) smallAmbientHomogeneousGroups
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) : AddCommGroup (homogeneousModule k V c K r) :=
  canonicalHomogeneousQuotientAddCommGroup k V c K r

local instance (priority := 2500) smallAmbientHomogeneousMonoids
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) : AddCommMonoid (homogeneousModule k V c K r) :=
  (canonicalHomogeneousQuotientAddCommGroup k V c K r).toAddCommMonoid

local instance (priority := 2500) smallAmbientHomogeneousCoefficients
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) : _root_.Module k (homogeneousModule k V c K r) :=
  canonicalHomogeneousQuotientBaseCoefficients k V c K r

/-- The genuine original full-cup-kernel component subtype has at most
one element, since each actual maximal subspace is the original top. -/
theorem fullCupKernel_originalFamily_subsingleton :
    Subsingleton (OriginalMaximalIsotropicFamily (cupQuotient (⊤ : Submodule k (⋀[k]^2 E)))) := by
  constructor
  intro P Q
  apply Subtype.ext
  exact (fullCupKernel_maximal_isotropic_eq_top k E P.val P.property.1).trans
    (fullCupKernel_maximal_isotropic_eq_top k E Q.val Q.property.1).symm

/-- The actual family is empty whenever the original ambient dimension
is at most one; this holds for every true quadratic cup kernel. -/
theorem originalFamily_isEmpty_of_finrank_le_one
    (I : Submodule k (⋀[k]^2 E)) (hE : _root_.Module.finrank k E ≤ 1) :
    IsEmpty (OriginalMaximalIsotropicFamily (cupQuotient I)) := by
  constructor
  intro P
  have hge := P.property.2
  have hle := P.val.finrank_le
  omega

variable {ι : Type*} [Fintype ι]
variable (b : _root_.Module.Basis ι k (_root_.Module.Dual k E))
variable [CharZero k]

private theorem proposition_of_two_equalities {T : Sort*} {x a c : T}
    (P : T → Prop) (hx : x = a ∨ x = c) (ha : P a) (hc : P c) : P x := by
  rcases hx with h | h
  · exact h.symm ▸ ha
  · exact h.symm ▸ hc

/-- The zero original cup kernel has zero source and zero target in
every original degree. No transport of a dependent original map is used. -/
private theorem zeroCupKernel_canonicalHomogeneousMap_bijective (r : ℕ) :
    Function.Bijective
      (originalCanonicalFamilyHomogeneousMap k E
        (⊥ : Submodule k (⋀[k]^2 E)) b r) := by
  classical
  letI := zeroCupKernel_originalFamily_isEmpty k E
  letI : Subsingleton
      (homogeneousModule k (_root_.Module.Dual k E) b
        (exteriorAnnihilator k E 2 (⊥ : Submodule k (⋀[k]^2 E))) r) := by
    rw [exteriorAnnihilator_bot]
    exact homogeneousModule_top_subsingleton k (_root_.Module.Dual k E) b r
  constructor
  · intro x y _h
    exact Subsingleton.elim x y
  · intro y
    refine ⟨0, ?_⟩
    apply funext
    intro P
    exact isEmptyElim P

omit [CharZero k] in
/-- For a full original cup kernel the actual family is either empty or
the genuine whole-space singleton, and its original map is bijective. -/
private theorem fullCupKernel_canonicalHomogeneousMap_bijective (r : ℕ) :
    Function.Bijective
      (originalCanonicalFamilyHomogeneousMap k E
        (⊤ : Submodule k (⋀[k]^2 E)) b r) := by
  classical
  by_cases hsmall : _root_.Module.finrank k E ≤ 1
  · letI := originalFamily_isEmpty_of_finrank_le_one k E ⊤ hsmall
    have hd : _root_.Module.finrank k (_root_.Module.Dual k E) ≤ 1 := by
      simpa only [Subspace.dual_finrank_eq] using hsmall
    letI := homogeneousModule_subsingleton_of_finrank_le_one k (_root_.Module.Dual k E)
      b (exteriorAnnihilator k E 2 (⊤ : Submodule k (⋀[k]^2 E))) hd r
    constructor
    · intro x y _h
      exact Subsingleton.elim x y
    · intro y
      refine ⟨0, ?_⟩
      apply funext
      intro P
      exact isEmptyElim P
  · have hdim : 2 ≤ _root_.Module.finrank k E := by omega
    let P : OriginalMaximalIsotropicFamily
        (cupQuotient (⊤ : Submodule k (⋀[k]^2 E))) :=
      ⟨⊤, ⟨⟨(isCupIsotropic_iff_isIsotropic ⊤ ⊤).mp le_top,
        fun T _hT _hiso => le_top⟩, by simpa only [_root_.finrank_top] using hdim⟩⟩
    letI := fullCupKernel_originalFamily_subsingleton k E
    have hp : Function.Bijective
        (isotropicComponentHomogeneousMap k E
          (⊤ : Submodule k (⋀[k]^2 E)) (⊤ : Submodule k E)
          b (canonicalFamilyComponentBasis k E ⊤ P) le_top r) :=
      fullCupKernel_wholeSpace_homogeneousMap_bijective k E b
        (canonicalFamilyComponentBasis k E ⊤ P) r
    change Function.Bijective
      (fun x (Q : OriginalMaximalIsotropicFamily
        (cupQuotient (⊤ : Submodule k (⋀[k]^2 E)))) =>
        isotropicComponentHomogeneousMap k E ⊤ Q.val b
          (canonicalFamilyComponentBasis k E ⊤ Q)
          (canonicalFamily_component_isotropy k E ⊤ Q) r x)
    apply ChenRanks.function_pi_bijective_of_subsingleton_index P
    exact hp

/-- The actual original family map is bijective in every original
homogeneous degree in dimensions zero, one and two. The conclusion is
not an eventual assertion and does not cover higher dimensions. -/
theorem originalCanonicalFamilyHomogeneousMap_bijective_of_finrank_le_two
    (I : Submodule k (⋀[k]^2 E)) (hE : _root_.Module.finrank k E ≤ 2) (r : ℕ) :
    Function.Bijective (originalCanonicalFamilyHomogeneousMap k E I b r) := by
  exact proposition_of_two_equalities
    (fun J : Submodule k (⋀[k]^2 E) =>
      Function.Bijective (originalCanonicalFamilyHomogeneousMap k E J b r))
    (quadraticSubmodule_eq_bot_or_top_of_finrank_le_two k E I hE)
    (zeroCupKernel_canonicalHomogeneousMap_bijective k E b r)
    (fullCupKernel_canonicalHomogeneousMap_bijective k E b r)

end ChenRanks.Koszul
