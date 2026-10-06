import ChenRanks.FiniteSimultaneousDualSeparation

/-!
# Actual avoidance of finitely many proper affine subspaces

Each proper original submodule gives a genuine nonzero quotient vector
and a genuine quotient-dual separating functional. A finite family of
actual nonzero affine polynomials then constructs one original point
outside all the original affine translates. No generic point or
simultaneous-avoidance premise is supplied. This algebraic construction
applies over the real field needed for actual piecewise-linear disks.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks

variable {k V ι : Type*} [Field k] [Infinite k] [AddCommGroup V]
  [Module k V] [Fintype ι]

/-- Finitely many proper original affine translates admit an actual
simultaneously avoiding original point, including an empty family. -/
theorem exists_point_avoiding_finite_affine_subspaces
    (S : ι → Submodule k V) (a : ι → V) (hS : ∀ i, S i ≠ ⊤) :
    ∃ z : V, ∀ i, z - a i ∉ S i := by
  classical
  have hchoose : ∀ i, ∃ v : V, v ∉ S i := by
    intro i
    by_contra h
    push Not at h
    apply hS i
    apply Submodule.ext
    intro v
    simp only [Submodule.mem_top, iff_true]
    exact h v
  let v : ι → V := fun i => Classical.choose (hchoose i)
  have hv : ∀ i, v i ∉ S i := fun i => Classical.choose_spec (hchoose i)
  have hquot : ∀ i, (S i).mkQ (v i) ≠ 0 := by
    intro i hz
    exact hv i ((Submodule.Quotient.mk_eq_zero (S i)).mp hz)
  have hdual : ∀ i, ∃ f : Module.Dual k (V ⧸ S i),
      f ((S i).mkQ (v i)) = 1 :=
    fun i => Module.Projective.exists_dual_eq_one k (hquot i)
  let ψ : (i : ι) → Module.Dual k (V ⧸ S i) :=
    fun i => Classical.choose (hdual i)
  let φ : ι → Module.Dual k V := fun i => (ψ i).comp (S i).mkQ
  have hφ : ∀ i, φ i (v i) = 1 :=
    fun i => Classical.choose_spec (hdual i)
  have hφS : ∀ i x, x ∈ S i → φ i x = 0 := by
    intro i x hx
    change ψ i ((S i).mkQ x) = 0
    have hxq : (S i).mkQ x = 0 := (Submodule.Quotient.mk_eq_zero (S i)).mpr hx
    rw [hxq, map_zero]
  let q : ι → MvPolynomial ι k := fun i =>
    (∑ j, MvPolynomial.C (φ i (v j)) * MvPolynomial.X j) -
      MvPolynomial.C (φ i (a i))
  have hq : ∀ i, q i ≠ 0 := by
    intro i hz
    have h0 : MvPolynomial.eval (fun _ : ι => (0 : k)) (q i) = -φ i (a i) := by
      simp [q]
    have h1 : MvPolynomial.eval (Pi.single i 1) (q i) = 1 - φ i (a i) := by
      simp [q, Pi.single_apply, hφ]
    have hz0 := congrArg (MvPolynomial.eval (fun _ : ι => (0 : k))) hz
    rw [h0, map_zero] at hz0
    have hza : φ i (a i) = 0 := neg_eq_zero.mp hz0
    have hz1 := congrArg (MvPolynomial.eval (Pi.single i 1)) hz
    rw [h1, hza, sub_zero, map_zero] at hz1
    exact one_ne_zero hz1
  obtain ⟨y, hy⟩ := mvPolynomial_exists_simultaneous_nonzero_evaluation k ι ι q hq
  let z : V := ∑ j, y j • v j
  have hz : ∀ i, φ i (z - a i) = MvPolynomial.eval y (q i) := by
    intro i
    simp only [z, q, map_sub, map_sum, map_smul, RingHom.id_apply,
      smul_eq_mul, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  refine ⟨z, ?_⟩
  intro i hzi
  exact hy i ((hz i).symm.trans (hφS i (z - a i) hzi))

end ChenRanks
