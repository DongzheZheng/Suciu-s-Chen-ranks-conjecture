import Mathlib

/-!
# The integer valuation-kernel step

For a finite integer matrix, its complex kernel is the complex span of its
integer kernel.  This is the first algebraic step of the manuscript's lemma
on integer valuation kernels and vertical rational functions.

The proof first uses the flatness of a vector space over `ℚ` to commute a
kernel with extension to `ℂ`.  It then clears the finitely many denominators
of each rational kernel vector.  Neither scalar extension nor denominator
clearing is assumed as an additional hypothesis.

This file does not formalize divisors, logarithmic differentials, or the
geometric assertion that a vertical divisor makes a rational function
constant on the components of a general projective fiber.
-/

noncomputable section

open TensorProduct

namespace ChenRanks

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Coordinatewise extension of a rational vector to the complex numbers. -/
def complexOfRat (q : n → ℚ) : n → ℂ := fun j ↦ (q j : ℂ)

/-- Coordinatewise extension of an integer vector to the complex numbers. -/
def complexOfInt (z : n → ℤ) : n → ℂ := fun j ↦ (z j : ℂ)

/-- The rational kernel vectors, regarded as complex vectors. -/
def rationalKernelVectors (A : Matrix m n ℚ) : Set (n → ℂ) :=
  {v | ∃ q : n → ℚ, A.mulVec q = 0 ∧ v = complexOfRat q}

/-- The integer kernel vectors, regarded as complex vectors. -/
def integerKernelVectors (B : Matrix m n ℤ) : Set (n → ℂ) :=
  {v | ∃ z : n → ℤ, B.mulVec z = 0 ∧ v = complexOfInt z}

/-- Every vector in a finite rational matrix's complex kernel is a complex
linear combination of rational kernel vectors. -/
theorem complex_kernel_mem_span_rational
    (A : Matrix m n ℚ) (v : n → ℂ)
    (hv : (A.map (algebraMap ℚ ℂ)).mulVec v = 0) :
    v ∈ Submodule.span ℂ (rationalKernelVectors A) := by
  classical
  let f : (n → ℚ) →ₗ[ℚ] (m → ℚ) := A.mulVecLin
  let g : (n → ℂ) →ₗ[ℂ] (m → ℂ) :=
    (A.map (algebraMap ℚ ℂ)).mulVecLin
  let en : ℂ ⊗[ℚ] (n → ℚ) ≃ₗ[ℂ] (n → ℂ) :=
    TensorProduct.piScalarRight ℚ ℂ ℂ n
  let em : ℂ ⊗[ℚ] (m → ℚ) ≃ₗ[ℂ] (m → ℂ) :=
    TensorProduct.piScalarRight ℚ ℂ ℂ m
  have compat (t : ℂ ⊗[ℚ] (n → ℚ)) :
      em (AlgebraTensorModule.lTensor ℂ ℂ f t) = g (en t) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c q =>
      ext i
      simp [en, em, f, g, Matrix.mulVec, dotProduct, Algebra.smul_def,
        Finset.sum_mul, mul_assoc]
    | add x y hx hy => simp only [map_add, hx, hy]
  have ht : en.symm v ∈
      LinearMap.ker (AlgebraTensorModule.lTensor ℂ ℂ f) := by
    apply LinearMap.mem_ker.mpr
    apply em.injective
    calc
      em (AlgebraTensorModule.lTensor ℂ ℂ f (en.symm v)) = g v := by
        rw [compat, en.apply_symm_apply]
      _ = 0 := hv
      _ = em 0 := by simp
  rw [Module.Flat.ker_lTensor_eq ℂ ℂ f] at ht
  obtain ⟨u, hu⟩ := ht
  have span_image (u : ℂ ⊗[ℚ] LinearMap.ker f) :
      en (AlgebraTensorModule.lTensor ℂ ℂ (LinearMap.ker f).subtype u) ∈
        Submodule.span ℂ (rationalKernelVectors A) := by
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul c q =>
      have hq : complexOfRat (q : n → ℚ) ∈
          Submodule.span ℂ (rationalKernelVectors A) :=
        Submodule.subset_span ⟨(q : n → ℚ), q.property, rfl⟩
      have hpoint :
          en (AlgebraTensorModule.lTensor ℂ ℂ (LinearMap.ker f).subtype
            (c ⊗ₜ[ℚ] q)) = c • complexOfRat (q : n → ℚ) := by
        ext j
        change (q.val j : ℚ) • c = c * (q.val j : ℂ)
        simp [Algebra.smul_def, mul_comm]
      rw [hpoint]
      exact (Submodule.span ℂ (rationalKernelVectors A)).smul_mem c hq
    | add x y hx hy =>
      simpa using (Submodule.span ℂ (rationalKernelVectors A)).add_mem hx hy
  have h := span_image u
  have hu' := congrArg en hu
  rw [en.apply_symm_apply] at hu'
  rwa [hu'] at h

omit [Fintype m] in
/-- Clearing denominators preserves the kernel: a rational solution of an
integer system has a nonzero integer multiple which is an integer solution. -/
theorem rational_kernel_clear_denominators
    (B : Matrix m n ℤ) (q : n → ℚ)
    (hq : (B.map (algebraMap ℤ ℚ)).mulVec q = 0) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ z : n → ℤ,
      B.mulVec z = 0 ∧ ∀ j, (z j : ℚ) = (d : ℚ) * q j := by
  classical
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
  choose z hz using hd
  have hz' (j : n) : (z j : ℚ) = ((d : ℤ) : ℚ) * q j := by
    simpa [Algebra.smul_def] using hz j
  have hvector : (fun j ↦ (z j : ℚ)) = ((d : ℤ) : ℚ) • q := by
    ext j
    exact hz' j
  have hzQ : (B.map (algebraMap ℤ ℚ)).mulVec (fun j ↦ (z j : ℚ)) = 0 := by
    rw [hvector]
    change (B.map (algebraMap ℤ ℚ)).mulVecLin (((d : ℤ) : ℚ) • q) = 0
    rw [map_smul]
    change ((d : ℤ) : ℚ) • (B.map (algebraMap ℤ ℚ)).mulVec q = 0
    rw [hq, smul_zero]
  have hzZ : B.mulVec z = 0 := by
    ext i
    have hi := congrFun hzQ i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at hi ⊢
    simp only [algebraMap_int_eq, Int.coe_castRingHom] at hi
    exact_mod_cast hi
  exact ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp d.property, z, hzZ, hz'⟩

omit [Fintype m] in
/-- A rational kernel vector of an integer matrix belongs to the complex span
of the integer kernel. -/
theorem rational_kernel_mem_span_integer
    (B : Matrix m n ℤ) (q : n → ℚ)
    (hq : (B.map (algebraMap ℤ ℚ)).mulVec q = 0) :
    complexOfRat q ∈ Submodule.span ℂ (integerKernelVectors B) := by
  obtain ⟨d, hd, z, hz, hcoordinates⟩ :=
    rational_kernel_clear_denominators B q hq
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hscale : complexOfInt z = (d : ℂ) • complexOfRat q := by
    ext j
    have hj := hcoordinates j
    change (z j : ℂ) = (d : ℂ) * (q j : ℂ)
    exact_mod_cast hj
  have hzSpan : complexOfInt z ∈ Submodule.span ℂ (integerKernelVectors B) :=
    Submodule.subset_span ⟨z, hz, rfl⟩
  have h := (Submodule.span ℂ (integerKernelVectors B)).smul_mem (d : ℂ)⁻¹ hzSpan
  simpa [hscale, smul_smul, hdC] using h

/-- The complex kernel of any finite integer matrix is spanned over `ℂ` by
its integer kernel vectors.  This includes empty matrices and zero kernels. -/
theorem integer_matrix_complex_kernel_eq_span (B : Matrix m n ℤ) :
    LinearMap.ker (B.map (algebraMap ℤ ℂ)).mulVecLin =
      Submodule.span ℂ (integerKernelVectors B) := by
  apply le_antisymm
  · intro v hv
    have hv' : ((B.map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℂ)).mulVec v = 0 := by
      have hcast : (B.map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℂ) =
          B.map (algebraMap ℤ ℂ) := by
        ext i j
        simp
      rw [hcast]
      exact hv
    have hspan := complex_kernel_mem_span_rational (B.map (algebraMap ℤ ℚ)) v hv'
    exact (Submodule.span_le.mpr (fun w hw ↦ by
      obtain ⟨q, hq, rfl⟩ := hw
      exact rational_kernel_mem_span_integer B q hq)) hspan
  · apply Submodule.span_le.mpr
    intro v hv
    obtain ⟨z, hz, rfl⟩ := hv
    apply LinearMap.mem_ker.mpr
    change (B.map (algebraMap ℤ ℂ)).mulVec (complexOfInt z) = 0
    ext i
    have hi := congrFun hz i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, complexOfInt,
      Pi.zero_apply] at hi ⊢
    simp only [algebraMap_int_eq, Int.coe_castRingHom]
    exact_mod_cast hi

end ChenRanks
