import ChenRanks.IsotropicGrassmannianChart
import Mathlib.AlgebraicGeometry.Restrict

/-!
# The genuine open scheme of ordered isotropic two-frames

The coordinates are the two complete rows in a basis of the original E.
The ideal is formed from the original cup quotient, evaluated on their
actual exterior product. The rank-two open is the union of the genuine
principal opens of the ordinary two-by-two minors. Neither a component
list nor a reducedness or finiteness assertion is used in these objects.
-/

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace ChenRanks.Resonance.IsotropicFrame

universe u v

variable {k σ : Type u} {E : Type v} [Field k] [AddCommGroup E] [Module k E]
  [Fintype σ]

/-- The actual polynomial coordinates of two complete original vectors. -/
abbrev CoordinateRing (k σ : Type u) [Field k] := MvPolynomial (Fin 2 × σ) k

/-- The actual original vector specified by one coordinate row. -/
def row (b : _root_.Module.Basis σ k E) (x : Fin 2 × σ → k) (r : Fin 2) : E :=
  ∑ j, x (r, j) • b j

/-- The actual span of the two original vectors. -/
def plane (b : _root_.Module.Basis σ k E) (x : Fin 2 × σ → k) : Submodule k E :=
  Submodule.span k ({row b x 0, row b x 1} : Set E)

/-- The actual quadratic original cup relation, tested by a genuine dual. -/
def relationPolynomial (I : Submodule k (⋀[k]^2 E))
    (b : _root_.Module.Basis σ k E) (ρ : CupTarget I →ₗ[k] k) : CoordinateRing k σ := by
  classical
  exact ∑ j, ∑ l, MvPolynomial.X (0, j) * MvPolynomial.X (1, l) *
    MvPolynomial.C (ρ (relationWedge (cupQuotient I) (b j) (b l)))

/-- The genuine ideal of all original cup equations. -/
def relationIdeal (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis σ k E) :
    Ideal (CoordinateRing k σ) := Ideal.span (Set.range (relationPolynomial I b))

/-- The genuine original isotropic ordered-pair affine scheme. -/
abbrev scheme (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis σ k E) : Scheme.{u} :=
  Spec (.of (CoordinateRing k σ ⧸ relationIdeal I b))

/-- A genuine two-by-two coordinate minor. -/
def minor (j l : σ) : CoordinateRing k σ :=
  MvPolynomial.X (0, j) * MvPolynomial.X (1, l) -
    MvPolynomial.X (0, l) * MvPolynomial.X (1, j)

/-- The actual rank-two open, defined by ordinary nonvanishing minors
inside the genuine original ordered-pair scheme. -/
def rankTwoOpen (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis σ k E) :
    (scheme I b).Opens :=
  ⨆ j, ⨆ l, PrimeSpectrum.basicOpen (Ideal.Quotient.mk (relationIdeal I b) (minor j l))

/-- The actual open subscheme of ordered isotropic two-frames. -/
abbrev frameScheme (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis σ k E) :
    Scheme.{u} := (rankTwoOpen I b).toScheme

@[simp] theorem repr_row (b : _root_.Module.Basis σ k E)
    (x : Fin 2 × σ → k) (r : Fin 2) (j : σ) : b.repr (row b x r) j = x (r, j) := by
  classical
  simp [row, Finsupp.single_apply]

private theorem quadratic_sum_exchange
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis σ k E)
    (ρ : CupTarget I →ₗ[k] k) (x : Fin 2 × σ → k) :
    (∑ j, ∑ l, x (0, j) * x (1, l) *
      ρ (relationWedge (cupQuotient I) (b j) (b l))) =
    (∑ j, ∑ l, x (1, j) * x (0, l) *
      ρ (relationWedge (cupQuotient I) (b l) (b j))) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Evaluation is exactly the actual original cup relation on the same rows. -/
theorem aeval_relationPolynomial
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis σ k E)
    (ρ : CupTarget I →ₗ[k] k) (x : Fin 2 × σ → k) :
    MvPolynomial.aeval x (relationPolynomial I b ρ) =
      ρ (relationWedge (cupQuotient I) (row b x 0) (row b x 1)) := by
  classical
  calc
    _ = ∑ j, ∑ l, x (0, j) * x (1, l) *
        ρ (relationWedge (cupQuotient I) (b j) (b l)) := by
      simp [relationPolynomial]
    _ = ∑ j, ∑ l, x (1, j) * x (0, l) *
        ρ (relationWedge (cupQuotient I) (b l) (b j)) :=
      quadratic_sum_exchange I b ρ x
    _ = _ := by
      simp [row, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- Actual duals separate the quotient vector; no relation detector is assumed. -/
theorem relationIdeal_le_ker_aeval_iff
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis σ k E)
    (x : Fin 2 × σ → k) :
    relationIdeal I b ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom ↔
      relationWedge (cupQuotient I) (row b x 0) (row b x 1) = 0 := by
  constructor
  · intro hIdeal
    by_contra hrel
    obtain ⟨ρ, hρ⟩ := _root_.Module.Projective.exists_dual_ne_zero k hrel
    have h := hIdeal (Ideal.subset_span (Set.mem_range_self ρ))
    change MvPolynomial.aeval x (relationPolynomial I b ρ) = 0 at h
    rw [aeval_relationPolynomial] at h
    exact hρ h
  · intro hrel
    rw [relationIdeal, Ideal.span_le]
    rintro _ ⟨ρ, rfl⟩
    change MvPolynomial.aeval x (relationPolynomial I b ρ) = 0
    rw [aeval_relationPolynomial, hrel, map_zero]

/-- The actual original pair equations are precisely isotropy of its actual span. -/
theorem relationIdeal_le_ker_aeval_iff_plane_isCupIsotropic
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis σ k E)
    (x : Fin 2 × σ → k) :
    relationIdeal I b ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom ↔
      IsCupIsotropic I (plane b x) := by
  rw [relationIdeal_le_ker_aeval_iff]
  change cupQuotient I (exteriorWedge (row b x 0) (row b x 1)) = 0 ↔ _
  rw [cupQuotient_eq_zero_iff]
  constructor
  · exact span_pair_isCupIsotropic I (row b x 0) (row b x 1)
  · intro h
    apply (isCupIsotropic_iff I (plane b x)).mp h
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)

omit [Fintype σ] in
@[simp] theorem aeval_minor (x : Fin 2 × σ → k) (j l : σ) :
    MvPolynomial.aeval x (minor (k := k) j l) =
      x (0, j) * x (1, l) - x (0, l) * x (1, j) := by
  simp [minor]

/-- A genuine nonzero minor forces the same two original rows to be independent. -/
theorem rows_linearIndependent_of_minor_ne_zero
    (b : _root_.Module.Basis σ k E) (x : Fin 2 × σ → k) (j l : σ)
    (hminor : MvPolynomial.aeval x (minor (k := k) j l) ≠ 0) :
    LinearIndependent k ![row b x 0, row b x 1] := by
  rw [aeval_minor] at hminor
  apply linearIndependent_fin2.mpr
  constructor
  · intro hzero
    change row b x 1 = 0 at hzero
    have hj := congrArg (fun z : E ↦ b.repr z j) hzero
    have hl := congrArg (fun z : E ↦ b.repr z l) hzero
    simp only [repr_row, map_zero, Finsupp.zero_apply] at hj hl
    exact hminor (by rw [hj, hl]; ring)
  · intro c hc
    change c • row b x 1 = row b x 0 at hc
    have hj := congrArg (fun z : E ↦ b.repr z j) hc
    have hl := congrArg (fun z : E ↦ b.repr z l) hc
    simp only [map_smul, Finsupp.smul_apply, repr_row, smul_eq_mul] at hj hl
    exact hminor (by rw [← hj, ← hl]; ring)

/-- Independence of the actual rows has a genuine nonzero minor witness. -/
theorem exists_minor_ne_zero_of_rows_linearIndependent
    (b : _root_.Module.Basis σ k E) (x : Fin 2 × σ → k)
    (hli : LinearIndependent k ![row b x 0, row b x 1]) :
    ∃ j l, MvPolynomial.aeval x (minor (k := k) j l) ≠ 0 := by
  classical
  have hsecond : row b x 1 ≠ 0 := (linearIndependent_fin2.mp hli).1
  have hex : ∃ j, x (1, j) ≠ 0 := by
    by_contra h
    push Not at h
    apply hsecond
    simp [row, h]
  obtain ⟨j, hj⟩ := hex
  by_contra h
  push Not at h
  have hproportional : (x (0, j) / x (1, j)) • row b x 1 = row b x 0 := by
    apply b.repr.injective
    ext l
    simp only [map_smul, Finsupp.smul_apply, repr_row, smul_eq_mul]
    have hl := h j l
    rw [aeval_minor] at hl
    calc
      (x (0, j) / x (1, j)) * x (1, l) =
          (x (0, j) * x (1, l)) / x (1, j) := by ring
      _ = (x (0, l) * x (1, j)) / x (1, j) :=
        congrArg (fun z : k ↦ z / x (1, j)) (sub_eq_zero.mp hl)
      _ = x (0, l) := mul_div_cancel_right₀ _ hj
  exact (linearIndependent_fin2.mp hli).2 (x (0, j) / x (1, j)) hproportional

/-- The real minor condition is equivalent to actual original independence. -/
theorem rows_linearIndependent_iff_exists_minor_ne_zero
    (b : _root_.Module.Basis σ k E) (x : Fin 2 × σ → k) :
    LinearIndependent k ![row b x 0, row b x 1] ↔
      ∃ j l, MvPolynomial.aeval x (minor (k := k) j l) ≠ 0 :=
  ⟨exists_minor_ne_zero_of_rows_linearIndependent b x,
    fun ⟨j, l, h⟩ ↦ rows_linearIndependent_of_minor_ne_zero b x j l h⟩

/-- An actual coordinate solution gives an actual point of the original scheme. -/
def coordinatePoint (I : Submodule k (⋀[k]^2 E))
    (b : _root_.Module.Basis σ k E) (x : Fin 2 × σ → k)
    (hIdeal : relationIdeal I b ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom) :
    scheme I b :=
  PrimeSpectrum.comap (Ideal.Quotient.liftₐ (relationIdeal I b)
    (MvPolynomial.aeval x) hIdeal).toRingHom ⟨⊥, inferInstance⟩

/-- Membership in the genuine rank-two open at the actual coordinate point
is exactly independence of its same two original vectors. -/
theorem coordinatePoint_mem_rankTwoOpen_iff
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis σ k E)
    (x : Fin 2 × σ → k)
    (hIdeal : relationIdeal I b ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom) :
    coordinatePoint I b x hIdeal ∈ rankTwoOpen I b ↔
      LinearIndependent k ![row b x 0, row b x 1] := by
  rw [rows_linearIndependent_iff_exists_minor_ne_zero]
  have hminor (j l : σ) :
      coordinatePoint I b x hIdeal ∈
        PrimeSpectrum.basicOpen (Ideal.Quotient.mk (relationIdeal I b) (minor j l)) ↔
      MvPolynomial.aeval x (minor (k := k) j l) ≠ 0 := by
    change (Ideal.Quotient.mk (relationIdeal I b) (minor j l)) ∉
      Ideal.comap (Ideal.Quotient.liftₐ (relationIdeal I b)
        (MvPolynomial.aeval x) hIdeal).toRingHom (⊥ : Ideal k) ↔ _
    change (Ideal.Quotient.liftₐ (relationIdeal I b)
      (MvPolynomial.aeval x) hIdeal)
        (Ideal.Quotient.mk (relationIdeal I b) (minor j l)) ≠ 0 ↔ _
    rfl
  unfold rankTwoOpen
  constructor
  · intro h
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp h
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hj
    exact ⟨j, l, (hminor j l).mp hl⟩
  · rintro ⟨j, l, h⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨j, TopologicalSpace.Opens.mem_iSup.mpr ⟨l, (hminor j l).mpr h⟩⟩

end ChenRanks.Resonance.IsotropicFrame
