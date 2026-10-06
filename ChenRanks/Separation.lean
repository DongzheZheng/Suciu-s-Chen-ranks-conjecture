import Mathlib

/-!
The linear algebra following horizontal residue detection in the logarithmic
separation argument. The construction and geometric properties of the actual
residue maps are deliberately not supplied by this module.
-/

namespace ChenRanks

open scoped BigOperators

variable {k E W : Type*} [Field k]
  [AddCommGroup E] [Module k E] [AddCommGroup W] [Module k W]

def IsIsotropic (wedge : E →ₗ[k] E →ₗ[k] W) (P : Submodule k E) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, wedge x y = 0

def IsMaximalIsotropic (wedge : E →ₗ[k] E →ₗ[k] W)
    (P : Submodule k E) : Prop :=
  IsIsotropic wedge P ∧
    ∀ T : Submodule k E, P ≤ T → IsIsotropic wedge T → T ≤ P

/-- Maximality absorbs an isotropic enlargement; this is independent of geometry. -/
theorem maximal_isotropic_eq_of_le
    (wedge : E →ₗ[k] E →ₗ[k] W) (P T : Submodule k E)
    (hP : IsMaximalIsotropic wedge P) (hPT : P ≤ T)
    (hT : IsIsotropic wedge T) : T = P := by
  exact le_antisymm (hP.2 T hPT hT) hPT

def horizontalKernel {D : Type*} (residue : D → E →ₗ[k] k) : Submodule k E :=
  ⨅ d, LinearMap.ker (residue d)

@[simp]
theorem mem_horizontalKernel {D : Type*} (residue : D → E →ₗ[k] k) (g : E) :
    g ∈ horizontalKernel residue ↔ ∀ d, residue d g = 0 := by
  simp [horizontalKernel, LinearMap.mem_ker]

/-- Independent restricted forms detect every coefficient of a mixed relation. -/
theorem residues_zero_of_mixed_relation
    {ι D : Type*} {Ω : D → Type*} [Fintype ι]
    [∀ d, AddCommGroup (Ω d)] [∀ d, Module k (Ω d)]
    (wedge : E →ₗ[k] E →ₗ[k] W) (p g : ι → E)
    (residue : D → E →ₗ[k] k) (restricted : ∀ d, ι → Ω d)
    (twoResidue : ∀ d, W →ₗ[k] Ω d)
    (hIndependent : ∀ d, LinearIndependent k (restricted d))
    (hResidue : ∀ d i x,
      twoResidue d (wedge (p i) x) = residue d x • restricted d i)
    (hRelation : ∑ i, wedge (p i) (g i) = 0) :
    ∀ i d, residue d (g i) = 0 := by
  intro i d
  have h := congrArg (twoResidue d) hRelation
  simp only [map_sum, hResidue, map_zero] at h
  exact (Fintype.linearIndependent_iff.mp (hIndependent d)) _ h i

/--
The algebraic residue-to-separation implication. The horizontal kernel's
isotropy and containment of P are explicit geometric inputs, not conclusions
about actual varieties established by this module.
-/
theorem mixed_coefficients_mem_of_residue_system
    {ι D : Type*} {Ω : D → Type*} [Fintype ι]
    [∀ d, AddCommGroup (Ω d)] [∀ d, Module k (Ω d)]
    (wedge : E →ₗ[k] E →ₗ[k] W) (P : Submodule k E)
    (p : ι → P) (g : ι → E)
    (residue : D → E →ₗ[k] k) (restrictForm : ∀ d, P →ₗ[k] Ω d)
    (twoResidue : ∀ d, W →ₗ[k] Ω d)
    (hP : IsMaximalIsotropic wedge P)
    (hContainment : P ≤ horizontalKernel residue)
    (hVertical : IsIsotropic wedge (horizontalKernel residue))
    (hIndependent : ∀ d,
      LinearIndependent k (fun i ↦ restrictForm d (p i)))
    (hResidue : ∀ d i x,
      twoResidue d (wedge (p i) x) = residue d x • restrictForm d (p i))
    (hRelation : ∑ i, wedge (p i) (g i) = 0) :
    ∀ i, g i ∈ P := by
  have hZero := residues_zero_of_mixed_relation wedge (fun i ↦ (p i : E)) g
    residue (fun d i ↦ restrictForm d (p i)) twoResidue hIndependent hResidue hRelation
  intro i
  apply hP.2 (horizontalKernel residue) hContainment hVertical
  exact (mem_horizontalKernel residue (g i)).mpr (hZero i)

end ChenRanks
