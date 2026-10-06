import ChenRanks.PhaseGridClosingPaths

/-!
# Genuine uniqueness of continuous phase lifts before endpoint identification

The same projected path and the same actual initial value determine a
continuous lift into the genuine phase-grid complement. The proof uses
the actual covering map Circle.exp twice, and does not require the
terminal values to have been identified in advance. The filling lemmas
are the corresponding restriction statements for a genuine continuous
filling and a genuine edge map. Their factorization and initial-value
equalities are ordinary map data; actual simplex constructions must
prove those equalities when using the lemmas.
-/

noncomputable section

open unitInterval

namespace ChenRanks

/-- The two actual exponential phases and an actual initial point
uniquely determine a continuous grid-complement path. There is no
assumption on its terminal value. -/
theorem phaseGridContinuousMap_eq_of_projected_phase_eq
    (p q : C(I, PhaseGridComplement))
    (hphase : ∀ t : I, argumentPlanePhaseMap (p t).val =
      argumentPlanePhaseMap (q t).val)
    (hzero : p 0 = q 0) : p = q := by
  let p₁ : C(I, ℝ) := ⟨fun t => (p t).val.1,
    continuous_fst.comp (continuous_subtype_val.comp p.continuous)⟩
  let q₁ : C(I, ℝ) := ⟨fun t => (q t).val.1,
    continuous_fst.comp (continuous_subtype_val.comp q.continuous)⟩
  let p₂ : C(I, ℝ) := ⟨fun t => (p t).val.2,
    continuous_snd.comp (continuous_subtype_val.comp p.continuous)⟩
  let q₂ : C(I, ℝ) := ⟨fun t => (q t).val.2,
    continuous_snd.comp (continuous_subtype_val.comp q.continuous)⟩
  have h₁ : Circle.exp ∘ p₁ = Circle.exp ∘ q₁ := by
    funext t
    exact congrArg Prod.fst (hphase t)
  have h₂ : Circle.exp ∘ p₂ = Circle.exp ∘ q₂ := by
    funext t
    exact congrArg Prod.snd (hphase t)
  have h₁₀ : p₁ 0 = q₁ 0 := congrArg (fun z : PhaseGridComplement => z.val.1) hzero
  have h₂₀ : p₂ 0 = q₂ 0 := congrArg (fun z : PhaseGridComplement => z.val.2) hzero
  have he₁ : (p₁ : I → ℝ) = q₁ :=
    Circle.isCoveringMap_exp.eq_of_comp_eq p₁.continuous q₁.continuous h₁ 0 h₁₀
  have he₂ : (p₂ : I → ℝ) = q₂ :=
    Circle.isCoveringMap_exp.eq_of_comp_eq p₂.continuous q₂.continuous h₂ 0 h₂₀
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  exact Prod.ext (congrFun he₁ t) (congrFun he₂ t)

/-- The existing selected lift projects to its actual original phases. -/
theorem phaseGridLiftedOriginalPath_projects
    (γ : C(I, TwicePuncturedComplex)) (t : I) :
    argumentPlanePhaseMap (phaseGridLiftedOriginalPath γ t).val =
      twicePuncturedComplexPhasePair (γ t) := by
  change
    (Circle.exp (circlePathArgumentLift (twicePuncturedComplexZeroPhase.comp γ) t),
      Circle.exp (circlePathArgumentLift (twicePuncturedComplexOnePhase.comp γ) t)) =
      (twicePuncturedComplexZeroPhase (γ t), twicePuncturedComplexOnePhase (γ t))
  exact Prod.ext
    (circlePathArgumentLift_projects (twicePuncturedComplexZeroPhase.comp γ) t)
    (circlePathArgumentLift_projects (twicePuncturedComplexOnePhase.comp γ) t)

private theorem continuousLift_deck_projects (n : ℤ × ℤ) (x : PhaseGridComplement) :
    argumentPlanePhaseMap (phaseGridDeckTranslation n x).val =
      argumentPlanePhaseMap x.val := by
  change (Circle.exp (x.val.1 + (n.1 : ℝ) * (2 * Real.pi)),
    Circle.exp (x.val.2 + (n.2 : ℝ) * (2 * Real.pi))) =
      (Circle.exp x.val.1, Circle.exp x.val.2)
  simp only [Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]

/-- Actual projected phases and the principal initial point identify
a continuous candidate lift with the actual selected covering lift. -/
theorem phaseGridContinuousLift_eq_selected
    (γ : C(I, TwicePuncturedComplex)) (θ : C(I, PhaseGridComplement))
    (hphase : ∀ t : I, argumentPlanePhaseMap (θ t).val =
      twicePuncturedComplexPhasePair (γ t))
    (hzero : θ 0 = phaseGridPrincipalPoint (γ 0)) :
    θ = (phaseGridLiftedOriginalPath γ).toContinuousMap := by
  apply phaseGridContinuousMap_eq_of_projected_phase_eq
  · intro t
    exact (hphase t).trans (phaseGridLiftedOriginalPath_projects γ t).symm
  · change θ 0 = phaseGridLiftedOriginalPath γ 0
    rw [Path.source]
    exact hzero

/-- The corresponding actual identification for any genuine integer
translate of the selected lift. No terminal-value condition is needed. -/
theorem phaseGridContinuousLift_eq_translated_selected
    (γ : C(I, TwicePuncturedComplex)) (θ : C(I, PhaseGridComplement)) (n : ℤ × ℤ)
    (hphase : ∀ t : I, argumentPlanePhaseMap (θ t).val =
      twicePuncturedComplexPhasePair (γ t))
    (hzero : θ 0 = phaseGridDeckTranslation n (phaseGridPrincipalPoint (γ 0))) :
    θ = ((phaseGridLiftedOriginalPath γ).map
      (phaseGridDeckTranslation n).continuous).toContinuousMap := by
  apply phaseGridContinuousMap_eq_of_projected_phase_eq
  · intro t
    change argumentPlanePhaseMap (θ t).val =
      argumentPlanePhaseMap (phaseGridDeckTranslation n (phaseGridLiftedOriginalPath γ t)).val
    rw [continuousLift_deck_projects]
    exact (hphase t).trans (phaseGridLiftedOriginalPath_projects γ t).symm
  · change θ 0 = phaseGridDeckTranslation n (phaseGridLiftedOriginalPath γ 0)
    rw [Path.source]
    exact hzero

/-- Restricting a genuine based filling to a genuine edge gives the
selected edge lift whenever its actual source is the principal point. -/
theorem phaseGridFilling_edge_eq_selected
    {X : Type*} [TopologicalSpace X]
    (s : C(X, TwicePuncturedComplex)) (G : C(X, PhaseGridComplement))
    (hprojects : ∀ x : X, argumentPlanePhaseMap (G x).val =
      twicePuncturedComplexPhasePair (s x))
    (e : C(I, X))
    (hzero : G (e 0) = phaseGridPrincipalPoint (s (e 0))) :
    G.comp e = (phaseGridLiftedOriginalPath (s.comp e)).toContinuousMap := by
  apply phaseGridContinuousLift_eq_selected
  · intro t
    exact hprojects (e t)
  · exact hzero

/-- The same true restriction statement for a filling edge whose
actual source is the true deck translate by n of the principal point. -/
theorem phaseGridFilling_edge_eq_translated_selected
    {X : Type*} [TopologicalSpace X]
    (s : C(X, TwicePuncturedComplex)) (G : C(X, PhaseGridComplement))
    (hprojects : ∀ x : X, argumentPlanePhaseMap (G x).val =
      twicePuncturedComplexPhasePair (s x))
    (e : C(I, X)) (n : ℤ × ℤ)
    (hzero : G (e 0) = phaseGridDeckTranslation n (phaseGridPrincipalPoint (s (e 0)))) :
    G.comp e = ((phaseGridLiftedOriginalPath (s.comp e)).map
      (phaseGridDeckTranslation n).continuous).toContinuousMap := by
  apply phaseGridContinuousLift_eq_translated_selected
  · intro t
    exact hprojects (e t)
  · exact hzero

end ChenRanks
