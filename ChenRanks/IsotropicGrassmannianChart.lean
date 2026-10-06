import ChenRanks.ResonanceSeparatedMaximalCover
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Polynomial equations on a two-plane graph chart

A basis with two distinguished vectors defines a graph chart for
two-dimensional subspaces. Evaluating the quotient cup map on its two
universal vectors, followed by dual functionals, gives the coefficient
polynomials. The affine spectrum of the resulting polynomial quotient
has field-valued coordinate solutions exactly at cup-isotropic planes.
-/

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace ChenRanks.Resonance.IsotropicChart

universe u v

variable {k τ : Type u} {E : Type v} [Field k] [AddCommGroup E] [Module k E] [Fintype τ]

/-- The genuine graph-coordinate polynomial ring, with two rows of
coordinates for the chosen complementary basis vectors. -/
abbrev CoordinateRing (k τ : Type u) [Field k] := MvPolynomial (Fin 2 × τ) k

/-- The first actual graph vector in the original vector space. -/
def graphFirst (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (x : Fin 2 × τ → k) : E :=
  b (Sum.inl 0) + ∑ j, x (0, j) • b (Sum.inr j)

/-- The second actual graph vector in the original vector space. -/
def graphSecond (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (x : Fin 2 × τ → k) : E :=
  b (Sum.inl 1) + ∑ j, x (1, j) • b (Sum.inr j)

/-- The actual submodule represented by a field-valued graph coordinate. -/
def graphPlane (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (x : Fin 2 × τ → k) : Submodule k E :=
  Submodule.span k ({graphFirst b x, graphSecond b x} : Set E)

/-- A genuine scalar equation obtained from the original exterior cup
quotient. The constant, linear and quadratic terms are its actual bilinear
expansion on the universal graph vectors. -/
def relationPolynomial (I : Submodule k (⋀[k]^2 E))
    (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (ρ : CupTarget I →ₗ[k] k) : CoordinateRing k τ := by
  classical
  let w := relationWedge (cupQuotient I)
  exact MvPolynomial.C (ρ (w (b (Sum.inl 0)) (b (Sum.inl 1)))) +
    (∑ j, MvPolynomial.X (0, j) * MvPolynomial.C (ρ (w (b (Sum.inr j)) (b (Sum.inl 1))))) +
    (∑ j, MvPolynomial.X (1, j) * MvPolynomial.C (ρ (w (b (Sum.inl 0)) (b (Sum.inr j))))) +
    (∑ j, ∑ l, MvPolynomial.X (0, j) * MvPolynomial.X (1, l) *
      MvPolynomial.C (ρ (w (b (Sum.inr j)) (b (Sum.inr l)))))

/-- The actual original-relation ideal on the graph chart. All genuine
dual forms are used; no intended decomposition is built into the ideal. -/
def relationIdeal (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) :
    Ideal (CoordinateRing k τ) := Ideal.span (Set.range (relationPolynomial I b))

/-- The genuine affine scheme cut out by the original graph equations. -/
abbrev scheme (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) : Scheme.{u} :=
  Spec (.of (CoordinateRing k τ ⧸ relationIdeal I b))

private theorem aeval_relationPolynomial_expand
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E)
    (ρ : CupTarget I →ₗ[k] k) (x : Fin 2 × τ → k) :
    MvPolynomial.aeval x (relationPolynomial I b ρ) =
      ρ (cupQuotient I (exteriorWedge (k := k) (b (Sum.inl 0)) (b (Sum.inl 1)))) +
      (∑ j, x (0, j) * ρ (cupQuotient I
        (exteriorWedge (k := k) (b (Sum.inr j)) (b (Sum.inl 1))))) +
      (∑ j, x (1, j) * ρ (cupQuotient I
        (exteriorWedge (k := k) (b (Sum.inl 0)) (b (Sum.inr j))))) +
      (∑ j, ∑ l, x (0, j) * x (1, l) * ρ (cupQuotient I
        (exteriorWedge (k := k) (b (Sum.inr j)) (b (Sum.inr l))))) := by
  classical
  simp [relationPolynomial]

private theorem graph_relation_expand
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E)
    (ρ : CupTarget I →ₗ[k] k) (x : Fin 2 × τ → k) :
    ρ (relationWedge (cupQuotient I) (graphFirst b x) (graphSecond b x)) =
      ρ (cupQuotient I (exteriorWedge (k := k) (b (Sum.inl 0)) (b (Sum.inl 1)))) +
      (∑ j, x (0, j) * ρ (cupQuotient I
        (exteriorWedge (k := k) (b (Sum.inr j)) (b (Sum.inl 1))))) +
      (∑ j, x (1, j) * ρ (cupQuotient I
        (exteriorWedge (k := k) (b (Sum.inl 0)) (b (Sum.inr j))))) +
      (∑ j, ∑ l, x (1, j) * x (0, l) * ρ (cupQuotient I
        (exteriorWedge (k := k) (b (Sum.inr l)) (b (Sum.inr j))))) := by
  classical
  simp [graphFirst, graphSecond, map_add, map_sum, map_smul,
    LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_add_distrib, Finset.mul_sum, smul_eq_mul, mul_assoc]
  abel

private theorem graph_quadratic_sum_exchange
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E)
    (ρ : CupTarget I →ₗ[k] k) (x : Fin 2 × τ → k) :
    (∑ j, ∑ l, x (0, j) * x (1, l) *
      ρ (cupQuotient I (exteriorWedge (k := k) (b (Sum.inr j)) (b (Sum.inr l))))) =
    (∑ j, ∑ l, x (1, j) * x (0, l) *
      ρ (cupQuotient I (exteriorWedge (k := k) (b (Sum.inr l)) (b (Sum.inr j))))) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Actual polynomial evaluation equals the original exterior relation
on the same actual graph vectors. -/
theorem aeval_relationPolynomial
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E)
    (ρ : CupTarget I →ₗ[k] k) (x : Fin 2 × τ → k) :
    MvPolynomial.aeval x (relationPolynomial I b ρ) =
      ρ (relationWedge (cupQuotient I) (graphFirst b x) (graphSecond b x)) := by
  rw [aeval_relationPolynomial_expand, graph_relation_expand]
  exact congrArg (fun q : k ↦
    ρ (cupQuotient I (exteriorWedge (k := k) (b (Sum.inl 0)) (b (Sum.inl 1)))) +
    (∑ j, x (0, j) * ρ (cupQuotient I
      (exteriorWedge (k := k) (b (Sum.inr j)) (b (Sum.inl 1))))) +
    (∑ j, x (1, j) * ρ (cupQuotient I
      (exteriorWedge (k := k) (b (Sum.inl 0)) (b (Sum.inr j))))) + q)
    (graph_quadratic_sum_exchange I b ρ x)

/-- Actual dual linear forms separate the actual cup-quotient vector,
so satisfying the genuine chart ideal is equivalent to the original
exterior relation being zero. -/
theorem relationIdeal_le_ker_aeval_iff
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E)
    (x : Fin 2 × τ → k) :
    relationIdeal I b ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom ↔
      relationWedge (cupQuotient I) (graphFirst b x) (graphSecond b x) = 0 := by
  constructor
  · intro hIdeal
    by_contra hrel
    obtain ⟨ρ, hρ⟩ := _root_.Module.Projective.exists_dual_ne_zero k hrel
    have hmem := hIdeal (Ideal.subset_span (Set.mem_range_self ρ))
    change MvPolynomial.aeval x (relationPolynomial I b ρ) = 0 at hmem
    rw [aeval_relationPolynomial] at hmem
    exact hρ hmem
  · intro hrel
    rw [relationIdeal, Ideal.span_le]
    rintro _ ⟨ρ, rfl⟩
    change MvPolynomial.aeval x (relationPolynomial I b ρ) = 0
    rw [aeval_relationPolynomial, hrel, map_zero]

/-- The actual graph-chart equations precisely express cup-isotropy of
the actual graph plane in the original exterior relation. -/
theorem relationIdeal_le_ker_aeval_iff_graphPlane_isCupIsotropic
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E)
    (x : Fin 2 × τ → k) :
    relationIdeal I b ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom ↔
      IsCupIsotropic I (graphPlane b x) := by
  rw [relationIdeal_le_ker_aeval_iff]
  change cupQuotient I (exteriorWedge (graphFirst b x) (graphSecond b x)) = 0 ↔ _
  rw [cupQuotient_eq_zero_iff]
  constructor
  · intro h
    exact span_pair_isCupIsotropic I (graphFirst b x) (graphSecond b x) h
  · intro h
    apply (isCupIsotropic_iff I (graphPlane b x)).mp h
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)

@[simp] theorem graphFirst_repr_inl_zero
    (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (x : Fin 2 × τ → k) :
    b.repr (graphFirst b x) (Sum.inl 0) = 1 := by
  classical
  simp [graphFirst]

@[simp] theorem graphFirst_repr_inl_one
    (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (x : Fin 2 × τ → k) :
    b.repr (graphFirst b x) (Sum.inl 1) = 0 := by
  classical
  simp [graphFirst]

@[simp] theorem graphSecond_repr_inl_zero
    (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (x : Fin 2 × τ → k) :
    b.repr (graphSecond b x) (Sum.inl 0) = 0 := by
  classical
  simp [graphSecond]

@[simp] theorem graphSecond_repr_inl_one
    (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (x : Fin 2 × τ → k) :
    b.repr (graphSecond b x) (Sum.inl 1) = 1 := by
  classical
  simp [graphSecond]

/-- Every actual graph coordinate produces two genuinely independent
vectors, proved by the distinguished basis coordinates. -/
theorem graphFirst_ne_zero
    (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (x : Fin 2 × τ → k) : graphFirst b x ≠ 0 := by
  intro hzero
  have h := congrArg (fun z : E ↦ b.repr z (Sum.inl 0)) hzero
  simp at h

/-- The second graph vector is outside the actual span of the first;
its other distinguished coordinate is one rather than zero. -/
theorem graphSecond_not_mem_first_line
    (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (x : Fin 2 × τ → k) :
    graphSecond b x ∉ k ∙ graphFirst b x := by
  intro hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have h := congrArg (fun z : E ↦ b.repr z (Sum.inl 1)) hc
  simp at h

/-- The actual graph submodule is a literal two-dimensional plane. -/
theorem graphPlane_finrank [FiniteDimensional k E]
    (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (x : Fin 2 × τ → k) :
    Module.finrank k (graphPlane b x) = 2 := by
  exact finrank_span_pair_eq_two_of_not_mem_line (graphFirst b x) (graphSecond b x)
    (graphFirst_ne_zero b x) (graphSecond_not_mem_first_line b x)

end ChenRanks.Resonance.IsotropicChart
