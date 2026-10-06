import ChenRanks.KoszulGrading

/-!
# Genuine homogeneous coordinates and finite dimensions

Degree-`n` exponent vectors are genuinely equivalent to multisets of size
`n`.  The polynomial homogeneous subspace is genuinely equivalent to finitely
supported coefficients on these exponent vectors.  This proves its finite
dimension and its dimension count.  Tensor homogeneous spans are proved to
be the images of the original homogeneous tensor modules, with injectivity
obtained from flatness over the field.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

/-- Exponent vectors of total degree `n` are actual size-`n` multisets. -/
def degreeExponentEquivSym (ι : Type*) (n : ℕ) :
    {d : ι →₀ ℕ | d.degree = n} ≃ Sym ι n := by
  classical
  refine
    { toFun := fun d ↦ ⟨d.val.toMultiset, ?_⟩
      invFun := fun s ↦ ⟨Multiset.toFinsupp (s : Multiset ι), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [Finsupp.card_toMultiset]
    exact d.property
  · exact (Multiset.toFinsupp_sum_eq (s : Multiset ι)).trans s.property
  · intro d
    apply Subtype.ext
    exact Finsupp.toMultiset_toFinsupp d.val
  · intro s
    apply Sym.coe_injective
    exact Multiset.toFinsupp_toMultiset (s : Multiset ι)

instance degreeExponentsFintype (ι : Type*) [Fintype ι] (n : ℕ) :
    Fintype {d : ι →₀ ℕ | d.degree = n} := by
  classical
  exact Fintype.ofEquiv (Sym ι n) (degreeExponentEquivSym ι n).symm

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} (b : _root_.Module.Basis ι k V)

/-- Coordinates of the actual homogeneous polynomial subspace. -/
def homogeneousPolynomialEquivCoefficients (n : ℕ) :
    MvPolynomial.homogeneousSubmodule ι k n ≃ₗ[k]
      ({d : ι →₀ ℕ | d.degree = n} →₀ k) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact Finsupp.supportedEquivFinsupp (R := k) {d : ι →₀ ℕ | d.degree = n}

/-- Actual homogeneous symmetric-algebra elements have actual monomial
coordinates, transported by the original basis algebra equivalence. -/
def homogeneousSEquivCoefficients (n : ℕ) :
    homogeneousS k V b n ≃ₗ[k] ({d : ι →₀ ℕ | d.degree = n} →₀ k) :=
  (SymmetricAlgebra.equivMvPolynomial b).toLinearEquiv.ofSubmodule'
      (MvPolynomial.homogeneousSubmodule ι k n) ≪≫ₗ
    homogeneousPolynomialEquivCoefficients k (ι := ι) n

instance homogeneousS_finiteDimensional [Fintype ι] (n : ℕ) :
    FiniteDimensional k (homogeneousS k V b n) :=
  FiniteDimensional.of_injective (homogeneousSEquivCoefficients k V b n).toLinearMap
    (homogeneousSEquivCoefficients k V b n).injective

/-- The genuine monomial count gives the actual homogeneous dimension. -/
theorem homogeneousS_finrank [Fintype ι] (n : ℕ) :
    _root_.Module.finrank k (homogeneousS k V b n) = Nat.multichoose (Fintype.card ι) n := by
  classical
  rw [(homogeneousSEquivCoefficients k V b n).finrank_eq,
    _root_.Module.finrank_finsupp_self]
  rw [Fintype.card_congr (degreeExponentEquivSym ι n)]
  exact Sym.card_sym_eq_multichoose ι n

section TensorCoordinates

variable (W : Type*) [AddCommGroup W] [_root_.Module k W]

/-- The original homogeneous coefficient inclusion on tensor modules. -/
def homogeneousTensorInclusion (n : ℕ) :
    (homogeneousS k V b n ⊗[k] W) →ₗ[k] (S k V ⊗[k] W) :=
  TensorProduct.map (homogeneousS k V b n).subtype LinearMap.id

/-- The actual tensor inclusion is injective by genuine flatness over a field. -/
theorem homogeneousTensorInclusion_injective (n : ℕ) :
    Function.Injective (homogeneousTensorInclusion k V b W n) :=
  _root_.Module.Flat.rTensor_preserves_injective_linearMap
    (M := W) (homogeneousS k V b n).subtype Subtype.val_injective

/-- The tensor homogeneous span equals the actual tensor-inclusion image. -/
theorem tensorHomogeneous_eq_range (n : ℕ) :
    tensorHomogeneous k V b W n =
      LinearMap.range (homogeneousTensorInclusion k V b W n) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨s, hs, w, rfl⟩
    exact ⟨(⟨s, hs⟩ : homogeneousS k V b n) ⊗ₜ[k] w, rfl⟩
  · rintro x ⟨t, rfl⟩
    induction t with
    | zero => simp
    | add t u ht hu => simpa only [map_add] using (tensorHomogeneous k V b W n).add_mem ht hu
    | tmul s w =>
      simpa only [homogeneousTensorInclusion, TensorProduct.map_tmul,
        LinearMap.id_apply, Submodule.subtype_apply] using
        tmul_mem_tensorHomogeneous k V b W n s s.property w

/-- The paper's homogeneous tensor module is genuinely equivalent to its
original coefficient-degree subspace. -/
def homogeneousTensorEquiv (n : ℕ) :
    (homogeneousS k V b n ⊗[k] W) ≃ₗ[k] tensorHomogeneous k V b W n :=
  LinearEquiv.ofInjective (homogeneousTensorInclusion k V b W n)
      (homogeneousTensorInclusion_injective k V b W n) ≪≫ₗ
    LinearEquiv.ofEq _ _ (tensorHomogeneous_eq_range k V b W n).symm

instance tensorHomogeneous_finiteDimensional [Fintype ι] [FiniteDimensional k W] (n : ℕ) :
    FiniteDimensional k (tensorHomogeneous k V b W n) :=
  FiniteDimensional.of_surjective (homogeneousTensorEquiv k V b W n).toLinearMap
    (homogeneousTensorEquiv k V b W n).surjective

theorem tensorHomogeneous_finrank [Fintype ι] [FiniteDimensional k W] (n : ℕ) :
    _root_.Module.finrank k (tensorHomogeneous k V b W n) =
      Nat.multichoose (Fintype.card ι) n * _root_.Module.finrank k W := by
  rw [← (homogeneousTensorEquiv k V b W n).finrank_eq,
    _root_.Module.finrank_tensorProduct, homogeneousS_finrank]

end TensorCoordinates

instance c1Degree_finiteDimensional [Fintype ι] (n : ℕ) :
    FiniteDimensional k (c1Degree k V b n) := by
  letI : FiniteDimensional k V :=
    FiniteDimensional.of_injective b.repr.toLinearMap b.repr.injective
  exact tensorHomogeneous_finiteDimensional k V b V n

instance cycleDegree_finiteDimensional [Fintype ι] (r : ℕ) :
    FiniteDimensional k (cycleDegree k V b r) := by
  let f : cycleDegree k V b r →ₗ[k] c1Degree k V b (r + 1) :=
    Submodule.inclusion inf_le_left
  exact FiniteDimensional.of_injective f (Submodule.inclusion_injective inf_le_left)

instance homogeneousModule_finiteDimensional [Fintype ι]
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) :
    FiniteDimensional k (homogeneousModule k V b K r) := inferInstance

end ChenRanks.Koszul
