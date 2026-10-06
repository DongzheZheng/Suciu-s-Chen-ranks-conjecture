import ChenRanks.IsotropicFrameObjects
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Genuine polynomial change of basis and translation for ordered frames

Two actual finite bases of the same original vector space and two actual
center vectors determine mutually inverse polynomial coordinate changes.
Their evaluations are computed on the same original vectors by the genuine
basis reconstruction formula. The inverse polynomial identities are proved
by the already established polynomial evaluation theorem over an infinite
field; in the intended complex specialization `Infinite ℂ` is a native
mathlib instance. No original subspace, component family, separation property,
relation ideal equality, freedom, or model comparison is an input.

-/

noncomputable section

open scoped BigOperators

namespace ChenRanks.Resonance.IsotropicFrame

universe u v

variable {k σ τ : Type u} {E : Type v} [Field k] [AddCommGroup E] [Module k E]
  [Fintype σ] [Fintype τ]

/-- The actual first-basis coordinates of the two center vectors. -/
def centerCoordinates (b₀ : _root_.Module.Basis σ k E) (c : Fin 2 → E) :
    Fin 2 × σ → k := fun q ↦ b₀.repr (c q.1) q.2

/-- The actual coordinate center reconstructs the same original vectors. -/
theorem row_centerCoordinates (b₀ : _root_.Module.Basis σ k E)
    (c : Fin 2 → E) (r : Fin 2) :
    row b₀ (centerCoordinates b₀ c) r = c r := by
  simpa only [row, centerCoordinates] using b₀.sum_repr (c r)

/-- Actual centered coordinates, in the second basis, of the same two
original vectors expressed in the first basis. -/
def centeredCoordinates (b₀ : _root_.Module.Basis σ k E)
    (b₁ : _root_.Module.Basis τ k E) (c : Fin 2 → E)
    (x : Fin 2 × σ → k) : Fin 2 × τ → k :=
  fun q ↦ b₁.repr (row b₀ x q.1 - c q.1) q.2

/-- Actual original coordinates, in the first basis, of the center plus
the two original directions expressed in the second basis. -/
def uncenteredCoordinates (b₀ : _root_.Module.Basis σ k E)
    (b₁ : _root_.Module.Basis τ k E) (c : Fin 2 → E)
    (y : Fin 2 × τ → k) : Fin 2 × σ → k :=
  fun q ↦ b₀.repr (c q.1 + row b₁ y q.1) q.2

omit [Fintype τ] in
/-- The actual original center is sent to the genuine coordinate origin. -/
theorem centeredCoordinates_centerCoordinates
    (b₀ : _root_.Module.Basis σ k E) (b₁ : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) :
    centeredCoordinates b₀ b₁ c (centerCoordinates b₀ c) = 0 := by
  funext q
  change b₁.repr (row b₀ (centerCoordinates b₀ c) q.1 - c q.1) q.2 = 0
  rw [row_centerCoordinates, sub_self, map_zero, Finsupp.zero_apply]

/-- The actual second-basis row of centered coordinates reconstructs the
same original first-basis row minus its actual center vector. -/
theorem row_centeredCoordinates
    (b₀ : _root_.Module.Basis σ k E) (b₁ : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) (x : Fin 2 × σ → k) (r : Fin 2) :
    row b₁ (centeredCoordinates b₀ b₁ c x) r = row b₀ x r - c r := by
  simpa only [row, centeredCoordinates] using b₁.sum_repr (row b₀ x r - c r)

/-- The actual first-basis row of uncentered coordinates reconstructs
the same original center plus second-basis direction. -/
theorem row_uncenteredCoordinates
    (b₀ : _root_.Module.Basis σ k E) (b₁ : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) (y : Fin 2 × τ → k) (r : Fin 2) :
    row b₀ (uncenteredCoordinates b₀ b₁ c y) r = c r + row b₁ y r := by
  simpa only [row, uncenteredCoordinates] using b₀.sum_repr (c r + row b₁ y r)

/-- Two actual coordinate operations in opposite directions return each
original coordinate, by reconstruction of the same original vectors. -/
theorem uncenteredCoordinates_centeredCoordinates
    (b₀ : _root_.Module.Basis σ k E) (b₁ : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) (x : Fin 2 × σ → k) :
    uncenteredCoordinates b₀ b₁ c (centeredCoordinates b₀ b₁ c x) = x := by
  funext q
  change b₀.repr (c q.1 + row b₁ (centeredCoordinates b₀ b₁ c x) q.1) q.2 = x q
  rw [row_centeredCoordinates]
  have hvector : c q.1 + (row b₀ x q.1 - c q.1) = row b₀ x q.1 := by abel
  rw [hvector]
  exact repr_row b₀ x q.1 q.2

/-- The other order of the actual coordinate operations also returns the
original centered directions. -/
theorem centeredCoordinates_uncenteredCoordinates
    (b₀ : _root_.Module.Basis σ k E) (b₁ : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) (y : Fin 2 × τ → k) :
    centeredCoordinates b₀ b₁ c (uncenteredCoordinates b₀ b₁ c y) = y := by
  funext q
  change b₁.repr (row b₀ (uncenteredCoordinates b₀ b₁ c y) q.1 - c q.1) q.2 = y q
  rw [row_uncenteredCoordinates]
  have hvector : c q.1 + row b₁ y q.1 - c q.1 = row b₁ y q.1 := by abel
  rw [hvector]
  exact repr_row b₁ y q.1 q.2

/-- The genuine forward polynomial substitution, from original coordinate
functions to center-plus-direction coordinate functions. -/
def coordinateChangeForward (b₀ : _root_.Module.Basis σ k E)
    (b₁ : _root_.Module.Basis τ k E) (c : Fin 2 → E) :
    CoordinateRing k σ →ₐ[k] CoordinateRing k τ :=
  MvPolynomial.aeval (fun q ↦ MvPolynomial.C (b₀.repr (c q.1) q.2) +
    ∑ j, MvPolynomial.X (q.1, j) * MvPolynomial.C (b₀.repr (b₁ j) q.2))

/-- The genuine reverse polynomial substitution, from centered directions
to original coordinates minus the actual center coordinates. -/
def coordinateChangeBackward (b₀ : _root_.Module.Basis σ k E)
    (b₁ : _root_.Module.Basis τ k E) (c : Fin 2 → E) :
    CoordinateRing k τ →ₐ[k] CoordinateRing k σ :=
  MvPolynomial.aeval (fun q ↦
    (∑ i, MvPolynomial.X (q.1, i) * MvPolynomial.C (b₁.repr (b₀ i) q.2)) -
      MvPolynomial.C (b₁.repr (c q.1) q.2))

omit [Fintype σ] in
/-- Actual evaluation of a forward generator is precisely the same
original vector's uncentered coordinate. -/
theorem aeval_coordinateChangeForward_X
    (b₀ : _root_.Module.Basis σ k E) (b₁ : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) (y : Fin 2 × τ → k) (q : Fin 2 × σ) :
    MvPolynomial.aeval y (coordinateChangeForward b₀ b₁ c (MvPolynomial.X q)) =
      uncenteredCoordinates b₀ b₁ c y q := by
  classical
  simp [coordinateChangeForward, uncenteredCoordinates, row, map_sum, map_smul,
    smul_eq_mul]

omit [Fintype τ] in
/-- Actual evaluation of a reverse generator is precisely the same
original vector's centered coordinate. -/
theorem aeval_coordinateChangeBackward_X
    (b₀ : _root_.Module.Basis σ k E) (b₁ : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) (x : Fin 2 × σ → k) (q : Fin 2 × τ) :
    MvPolynomial.aeval x (coordinateChangeBackward b₀ b₁ c (MvPolynomial.X q)) =
      centeredCoordinates b₀ b₁ c x q := by
  classical
  simp [coordinateChangeBackward, centeredCoordinates, row, map_sum, map_smul,
    smul_eq_mul]

omit [Fintype σ] in
/-- Polynomial evaluation commutes with the genuine forward substitution
on every original polynomial, proved on the actual generators. -/
theorem aeval_comp_coordinateChangeForward
    (b₀ : _root_.Module.Basis σ k E) (b₁ : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) (y : Fin 2 × τ → k) :
    (MvPolynomial.aeval y).comp (coordinateChangeForward b₀ b₁ c) =
      MvPolynomial.aeval (uncenteredCoordinates b₀ b₁ c y) := by
  ext q
  simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using
    aeval_coordinateChangeForward_X b₀ b₁ c y q

omit [Fintype τ] in
/-- Polynomial evaluation commutes with the genuine reverse substitution
on every centered polynomial, proved on the actual generators. -/
theorem aeval_comp_coordinateChangeBackward
    (b₀ : _root_.Module.Basis σ k E) (b₁ : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) (x : Fin 2 × σ → k) :
    (MvPolynomial.aeval x).comp (coordinateChangeBackward b₀ b₁ c) =
      MvPolynomial.aeval (centeredCoordinates b₀ b₁ c x) := by
  ext q
  simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using
    aeval_coordinateChangeBackward_X b₀ b₁ c x q

omit [Fintype σ] in
/-- The actual forward polynomial evaluation identity for an arbitrary
original polynomial. -/
theorem aeval_coordinateChangeForward
    (b₀ : _root_.Module.Basis σ k E) (b₁ : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) (y : Fin 2 × τ → k) (p : CoordinateRing k σ) :
    MvPolynomial.aeval y (coordinateChangeForward b₀ b₁ c p) =
      MvPolynomial.aeval (uncenteredCoordinates b₀ b₁ c y) p :=
  AlgHom.congr_fun (aeval_comp_coordinateChangeForward b₀ b₁ c y) p

omit [Fintype τ] in
/-- The actual reverse polynomial evaluation identity for an arbitrary
centered polynomial. -/
theorem aeval_coordinateChangeBackward
    (b₀ : _root_.Module.Basis σ k E) (b₁ : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) (x : Fin 2 × σ → k) (p : CoordinateRing k τ) :
    MvPolynomial.aeval x (coordinateChangeBackward b₀ b₁ c p) =
      MvPolynomial.aeval (centeredCoordinates b₀ b₁ c x) p :=
  AlgHom.congr_fun (aeval_comp_coordinateChangeBackward b₀ b₁ c x) p

section InfiniteField

variable [Infinite k]

/-- The genuine reverse homomorphism composed with the forward one is
identity. Polynomial funext is applied only with the explicit, proved
infinite-field structure; inverse coordinate reconstruction supplies every
actual scalar evaluation equality. -/
theorem coordinateChangeBackward_comp_forward
    (b₀ : _root_.Module.Basis σ k E) (b₁ : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) :
    (coordinateChangeBackward b₀ b₁ c).comp (coordinateChangeForward b₀ b₁ c) =
      AlgHom.id k (CoordinateRing k σ) := by
  apply MvPolynomial.algHom_ext
  intro q
  apply MvPolynomial.funext
  intro x
  change MvPolynomial.aeval x (coordinateChangeBackward b₀ b₁ c
      (coordinateChangeForward b₀ b₁ c (MvPolynomial.X q))) =
    MvPolynomial.aeval x (MvPolynomial.X q)
  rw [aeval_coordinateChangeBackward, aeval_coordinateChangeForward,
    uncenteredCoordinates_centeredCoordinates]

/-- The genuine forward homomorphism composed with the reverse one is
identity, proved from the other actual coordinate reconstruction identity. -/
theorem coordinateChangeForward_comp_backward
    (b₀ : _root_.Module.Basis σ k E) (b₁ : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) :
    (coordinateChangeForward b₀ b₁ c).comp (coordinateChangeBackward b₀ b₁ c) =
      AlgHom.id k (CoordinateRing k τ) := by
  apply MvPolynomial.algHom_ext
  intro q
  apply MvPolynomial.funext
  intro y
  change MvPolynomial.aeval y (coordinateChangeForward b₀ b₁ c
      (coordinateChangeBackward b₀ b₁ c (MvPolynomial.X q))) =
    MvPolynomial.aeval y (MvPolynomial.X q)
  rw [aeval_coordinateChangeForward, aeval_coordinateChangeBackward,
    centeredCoordinates_uncenteredCoordinates]

/-- The actual polynomial algebra equivalence for changing between two
actual bases of E while translating by the actual pair of center vectors. -/
def coordinateChangeAlgEquiv (b₀ : _root_.Module.Basis σ k E)
    (b₁ : _root_.Module.Basis τ k E) (c : Fin 2 → E) :
    CoordinateRing k σ ≃ₐ[k] CoordinateRing k τ :=
  AlgEquiv.ofAlgHom (coordinateChangeForward b₀ b₁ c)
    (coordinateChangeBackward b₀ b₁ c)
    (coordinateChangeForward_comp_backward b₀ b₁ c)
    (coordinateChangeBackward_comp_forward b₀ b₁ c)

/-- The genuine algebra equivalence has the displayed forward formula
on every actual polynomial generator. -/
@[simp] theorem coordinateChangeAlgEquiv_X
    (b₀ : _root_.Module.Basis σ k E) (b₁ : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) (q : Fin 2 × σ) :
    coordinateChangeAlgEquiv b₀ b₁ c (MvPolynomial.X q) =
      MvPolynomial.C (b₀.repr (c q.1) q.2) +
        ∑ j, MvPolynomial.X (q.1, j) * MvPolynomial.C (b₀.repr (b₁ j) q.2) := by
  change coordinateChangeForward b₀ b₁ c (MvPolynomial.X q) = _
  simp only [coordinateChangeForward, MvPolynomial.aeval_X]

/-- The genuine inverse equivalence has the displayed reverse formula
on every actual polynomial generator. -/
@[simp] theorem coordinateChangeAlgEquiv_symm_X
    (b₀ : _root_.Module.Basis σ k E) (b₁ : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) (q : Fin 2 × τ) :
    (coordinateChangeAlgEquiv b₀ b₁ c).symm (MvPolynomial.X q) =
      (∑ i, MvPolynomial.X (q.1, i) * MvPolynomial.C (b₁.repr (b₀ i) q.2)) -
        MvPolynomial.C (b₁.repr (c q.1) q.2) := by
  change coordinateChangeBackward b₀ b₁ c (MvPolynomial.X q) = _
  simp only [coordinateChangeBackward, MvPolynomial.aeval_X]

/-- The actual algebra equivalence evaluates on the same original frame
obtained by adding the actual center to the second-basis directions. -/
theorem aeval_coordinateChangeAlgEquiv
    (b₀ : _root_.Module.Basis σ k E) (b₁ : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) (y : Fin 2 × τ → k) (p : CoordinateRing k σ) :
    MvPolynomial.aeval y (coordinateChangeAlgEquiv b₀ b₁ c p) =
      MvPolynomial.aeval (uncenteredCoordinates b₀ b₁ c y) p :=
  aeval_coordinateChangeForward b₀ b₁ c y p

/-- The actual inverse algebra equivalence evaluates on the centered
coordinates of the same original frame. -/
theorem aeval_coordinateChangeAlgEquiv_symm
    (b₀ : _root_.Module.Basis σ k E) (b₁ : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) (x : Fin 2 × σ → k) (p : CoordinateRing k τ) :
    MvPolynomial.aeval x ((coordinateChangeAlgEquiv b₀ b₁ c).symm p) =
      MvPolynomial.aeval (centeredCoordinates b₀ b₁ c x) p :=
  aeval_coordinateChangeBackward b₀ b₁ c x p

/-- Pulling a genuine centered polynomial back to the original pair
preserves its value at that pair as its true origin value. This is the
scalar compatibility needed for a subsequent principal-neighborhood proof. -/
theorem aeval_coordinateChangeAlgEquiv_symm_at_center
    (b₀ : _root_.Module.Basis σ k E) (b₁ : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) (p : CoordinateRing k τ) :
    MvPolynomial.aeval (centerCoordinates b₀ c)
        ((coordinateChangeAlgEquiv b₀ b₁ c).symm p) =
      MvPolynomial.aeval (0 : Fin 2 × τ → k) p := by
  rw [aeval_coordinateChangeAlgEquiv_symm, centeredCoordinates_centerCoordinates]

end InfiniteField

end ChenRanks.Resonance.IsotropicFrame
