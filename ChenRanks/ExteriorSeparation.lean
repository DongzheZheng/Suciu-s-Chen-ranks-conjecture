import ChenRanks.Separation
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# From residue detection to an equality of genuine exterior subspaces

The source of the quadratic relation map is mathlib's second exterior power,
not a replacement type carrying an assumed separation property.  A finite basis
of `P` represents every element of `P ∧ E` as a sum with those basis vectors in
the first factors.  The coefficient detection theorem then proves that a
relation lies in the image of `⋀² P → ⋀² E`.

The construction and geometric properties of the residue maps remain explicit
hypotheses.  This file does not assert them for arrangements or varieties.
-/

open scoped BigOperators

namespace ChenRanks

noncomputable section

universe u v w

variable {k : Type u} [Field k]
variable {E : Type v} [AddCommGroup E] [Module k E]
variable {W : Type w} [AddCommGroup W] [Module k W]

/-- The canonical exterior product of two vectors, in the second exterior power. -/
def exteriorWedge (x y : E) : ⋀[k]^2 E :=
  exteriorPower.ιMulti k 2 ![x, y]

@[simp]
theorem exteriorWedge_coe (x y : E) :
    (exteriorWedge (k := k) x y : ExteriorAlgebra k E) =
      ExteriorAlgebra.ι k x * ExteriorAlgebra.ι k y := by
  simp [exteriorWedge, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_apply]

/-- The exterior product as a bilinear map. -/
def exteriorWedgeBilin : E →ₗ[k] E →ₗ[k] ⋀[k]^2 E :=
  LinearMap.mk₂ k (exteriorWedge (k := k))
    (by intro x₁ x₂ y; apply Subtype.ext; simp [add_mul])
    (by intro a x y; apply Subtype.ext; simp)
    (by intro x y₁ y₂; apply Subtype.ext; simp [mul_add])
    (by intro a x y; apply Subtype.ext; simp)

@[simp]
theorem exteriorWedgeBilin_apply (x y : E) :
    exteriorWedgeBilin (k := k) x y = exteriorWedge x y := rfl

/-- Applying a genuine quadratic relation map to the canonical exterior product. -/
def relationWedge (φ : ⋀[k]^2 E →ₗ[k] W) : E →ₗ[k] E →ₗ[k] W :=
  (exteriorWedgeBilin (k := k)).compr₂ φ

@[simp]
theorem relationWedge_apply (φ : ⋀[k]^2 E →ₗ[k] W) (x y : E) :
    relationWedge φ x y = φ (exteriorWedge x y) := rfl

/-- The actual subspace `P ∧ E` of the second exterior power. -/
def mixedExterior (P : Submodule k E) : Submodule k (⋀[k]^2 E) :=
  Submodule.span k {z | ∃ p : P, ∃ x : E, z = exteriorWedge (p : E) x}

/-- The actual image of the second exterior power of `P` in that of `E`. -/
def pureExterior (P : Submodule k E) : Submodule k (⋀[k]^2 E) :=
  LinearMap.range (exteriorPower.map 2 P.subtype)

theorem exteriorWedge_mem_mixed (P : Submodule k E) (p : P) (x : E) :
    exteriorWedge (p : E) x ∈ mixedExterior P :=
  Submodule.subset_span ⟨p, x, rfl⟩

theorem exteriorWedge_mem_pure (P : Submodule k E) (p q : P) :
    exteriorWedge (p : E) (q : E) ∈ pureExterior P := by
  refine ⟨exteriorWedge (k := k) p q, ?_⟩
  simp only [exteriorWedge, exteriorPower.map_apply_ιMulti]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- The second exterior power is spanned by exterior products of two vectors. -/
theorem exteriorWedge_span :
    Submodule.span k {z : ⋀[k]^2 E | ∃ x y : E, z = exteriorWedge x y} = ⊤ := by
  apply top_unique
  rw [← exteriorPower.ιMulti_span k 2 E]
  apply Submodule.span_le.mpr
  rintro z ⟨a, rfl⟩
  apply Submodule.subset_span
  refine ⟨a 0, a 1, ?_⟩
  unfold exteriorWedge
  congr 1
  ext i
  fin_cases i <;> rfl

/-- The image `⋀² P` is exactly the span of exterior products with both factors in `P`. -/
theorem pureExterior_eq_span (P : Submodule k E) :
    pureExterior P =
      Submodule.span k {z | ∃ p q : P, z = exteriorWedge (p : E) (q : E)} := by
  apply le_antisymm
  · rw [pureExterior, LinearMap.range_eq_map,
      ← exteriorWedge_span (k := k) (E := P), Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro z ⟨x, ⟨p, q, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨p, q, ?_⟩
    simp only [exteriorWedge, exteriorPower.map_apply_ιMulti]
    congr 1
    ext i
    fin_cases i <;> rfl
  · apply Submodule.span_le.mpr
    rintro z ⟨p, q, rfl⟩
    exact exteriorWedge_mem_pure P p q

theorem pureExterior_le_mixed (P : Submodule k E) : pureExterior P ≤ mixedExterior P := by
  rw [pureExterior_eq_span]
  apply Submodule.span_le.mpr
  rintro z ⟨p, q, rfl⟩
  exact exteriorWedge_mem_mixed P p (q : E)

/-- A subspace isotropic for the quadratic relation map has all of its exterior
square in the relation kernel. -/
theorem pureExterior_le_ker (φ : ⋀[k]^2 E →ₗ[k] W) (P : Submodule k E)
    (hP : IsIsotropic (relationWedge φ) P) :
    pureExterior P ≤ LinearMap.ker φ := by
  rw [pureExterior_eq_span]
  apply Submodule.span_le.mpr
  rintro z ⟨p, q, rfl⟩
  exact hP p p.property q q.property

section FiniteBasis

variable {ι : Type*} [Fintype ι]

/-- All mixed sums having the chosen basis vectors as their first factors. -/
def basisMixedMap (P : Submodule k E) (b : Module.Basis ι k P) :
    (ι → E) →ₗ[k] ⋀[k]^2 E where
  toFun g := ∑ i, exteriorWedge (b i : E) (g i)
  map_add' g h := by
    change (∑ i, exteriorWedgeBilin (b i : E) (g i + h i)) = _
    simp only [map_add, Finset.sum_add_distrib]
    rfl
  map_smul' a g := by
    change (∑ i, exteriorWedgeBilin (b i : E) (a • g i)) = _
    simp only [map_smul, ← Finset.smul_sum]
    rfl

@[simp]
theorem basisMixedMap_apply (P : Submodule k E) (b : Module.Basis ι k P) (g : ι → E) :
    basisMixedMap P b g = ∑ i, exteriorWedge (b i : E) (g i) := rfl

/-- Every mixed exterior vector has a representation using one fixed finite
basis of `P`, including vectors that are not decomposable. -/
theorem mixedExterior_eq_range_basisMixedMap
    (P : Submodule k E) (b : Module.Basis ι k P) :
    mixedExterior P = LinearMap.range (basisMixedMap P b) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨p, x, rfl⟩
    refine ⟨fun i ↦ b.repr p i • x, ?_⟩
    have hp : (∑ i, b.repr p i • (b i : E)) = (p : E) := by
      simpa only [map_sum, map_smul] using congrArg P.subtype (b.sum_repr p)
    change (∑ i, exteriorWedgeBilin (b i : E) (b.repr p i • x)) =
      exteriorWedgeBilin (p : E) x
    rw [← hp]
    simp only [map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply]
  · rintro z ⟨g, rfl⟩
    apply Submodule.sum_mem
    intro i hi
    exact exteriorWedge_mem_mixed P (b i) (g i)

theorem exists_basis_mixed_representation
    (P : Submodule k E) (b : Module.Basis ι k P) {z : ⋀[k]^2 E}
    (hz : z ∈ mixedExterior P) :
    ∃ g : ι → E, (∑ i, exteriorWedge (b i : E) (g i)) = z := by
  rw [mixedExterior_eq_range_basisMixedMap P b] at hz
  exact hz

/-- Residue detection proves the actual exterior-subspace separation equality.
The only hypotheses beyond linear algebra concern the explicit residue system;
the separation equality itself is a conclusion. -/
theorem exterior_separation_of_residue_system
    {D : Type*} {Ω : D → Type*}
    [∀ d, AddCommGroup (Ω d)] [∀ d, Module k (Ω d)]
    (φ : ⋀[k]^2 E →ₗ[k] W) (P : Submodule k E) (b : Module.Basis ι k P)
    (residue : D → E →ₗ[k] k) (restrictForm : ∀ d, P →ₗ[k] Ω d)
    (twoResidue : ∀ d, W →ₗ[k] Ω d)
    (hP : IsMaximalIsotropic (relationWedge φ) P)
    (hContainment : P ≤ horizontalKernel residue)
    (hVertical : IsIsotropic (relationWedge φ) (horizontalKernel residue))
    (hIndependent : ∀ d, LinearIndependent k (fun i ↦ restrictForm d (b i)))
    (hResidue : ∀ d i x,
      twoResidue d (relationWedge φ (b i) x) = residue d x • restrictForm d (b i)) :
    mixedExterior P ⊓ LinearMap.ker φ = pureExterior P := by
  apply le_antisymm
  · intro z hz
    obtain ⟨g, hg⟩ := exists_basis_mixed_representation P b hz.1
    have hRelation : ∑ i, relationWedge φ (b i) (g i) = 0 := by
      have hzφ : φ z = 0 := hz.2
      simpa only [relationWedge_apply, ← map_sum, hg] using hzφ
    have hMem := mixed_coefficients_mem_of_residue_system
      (relationWedge φ) P (fun i ↦ b i) g residue restrictForm twoResidue
      hP hContainment hVertical hIndependent hResidue hRelation
    rw [← hg]
    apply Submodule.sum_mem
    intro i hi
    exact exteriorWedge_mem_pure P (b i) ⟨g i, hMem i⟩
  · exact le_inf (pureExterior_le_mixed P) (pureExterior_le_ker φ P hP.1)

end FiniteBasis

end

end ChenRanks
