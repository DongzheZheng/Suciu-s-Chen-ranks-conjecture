import ChenRanks.IsotropicFrameOriginalNeighborhood
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Finiteness of separated maximal isotropic subspaces

Each independent isotropic ordered pair defines a point of the frame
scheme. Its maximal isotropic extension and principal neighborhood give
an open neighborhood whose solutions lie in that extension. The
coordinate-point image lies in a Noetherian prime spectrum and is
therefore compact. A finite open subcover, together with uniqueness for
nonzero intersections, proves finiteness of the maximal isotropic
subspaces of dimension at least two.

The separation hypothesis is an equality of exterior subspaces.
-/

noncomputable section

open TopologicalSpace

namespace ChenRanks.Resonance.IsotropicFrame

universe u v

variable {k σ : Type u} {E : Type v} [Field k] [AddCommGroup E] [Module k E]
  [Fintype σ] [Infinite k]

/-- Genuine original coordinate frames satisfying the actual original
cup ideal and actual independence of their same two original rows. -/
abbrev CoordinateFrameWitness (I : Submodule k (⋀[k]^2 E))
    (b : _root_.Module.Basis σ k E) :=
  {x : Fin 2 × σ → k //
    relationIdeal I b ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom ∧
      LinearIndependent k ![row b x 0, row b x 1]}

omit [Infinite k] in
/-- Every true polynomial principal-open condition at the actual coordinate
point is precisely nonvanishing of the original scalar evaluation. -/
theorem coordinatePoint_mem_basicOpen_iff
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis σ k E)
    (x : Fin 2 × σ → k)
    (hIdeal : relationIdeal I b ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom)
    (p : CoordinateRing k σ) :
    coordinatePoint I b x hIdeal ∈
      PrimeSpectrum.basicOpen (Ideal.Quotient.mk (relationIdeal I b) p) ↔
        MvPolynomial.aeval x p ≠ 0 := by
  change (Ideal.Quotient.mk (relationIdeal I b) p) ∉
    Ideal.comap (Ideal.Quotient.liftₐ (relationIdeal I b)
      (MvPolynomial.aeval x) hIdeal).toRingHom (⊥ : Ideal k) ↔ _
  change (Ideal.Quotient.liftₐ (relationIdeal I b)
    (MvPolynomial.aeval x) hIdeal)
      (Ideal.Quotient.mk (relationIdeal I b) p) ≠ 0 ↔ _
  rfl

/-- An actual isotropic frame produces its actual maximal extension and
its genuine original principal neighborhood, all constructed from it. -/
theorem exists_maximal_principal_neighborhood_of_coordinate_frame
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis σ k E)
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
      2 ≤ Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)
    (a : CoordinateFrameWitness I b) :
    ∃ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P ∧
      2 ≤ Module.finrank k P ∧
      ∃ t : CoordinateRing k σ, MvPolynomial.aeval a.val t ≠ 0 ∧
        ∀ x : Fin 2 × σ → k,
          relationIdeal I b ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom →
          MvPolynomial.aeval x t ≠ 0 → row b x 0 ∈ P ∧ row b x 1 ∈ P := by
  letI : FiniteDimensional k E := b.finiteDimensional_of_finite
  have hfirst : row b a.val 0 ≠ 0 := by
    intro hzero
    have hrel : (1 : k) • row b a.val 0 + (0 : k) • row b a.val 1 = 0 := by
      simp only [hzero, smul_zero, zero_smul, add_zero]
    exact one_ne_zero ((LinearIndependent.pair_iff.mp a.property.2) 1 0 hrel).1
  have hnot : row b a.val 1 ∉ k ∙ row b a.val 0 := by
    intro hmem
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
    have hrel : (-t) • row b a.val 0 + (1 : k) • row b a.val 1 = 0 := by
      rw [one_smul, ← ht, neg_smul, neg_add_cancel]
    exact one_ne_zero ((LinearIndependent.pair_iff.mp a.property.2) (-t) 1 hrel).2
  have hdim : 2 ≤ Module.finrank k (plane b a.val) :=
    two_le_finrank_span_pair_of_not_mem_line (row b a.val 0) (row b a.val 1) hfirst hnot
  have hiso : IsCupIsotropic I (plane b a.val) :=
    (relationIdeal_le_ker_aeval_iff_plane_isCupIsotropic I b a.val).mp a.property.1
  obtain ⟨P, hUP, hP, hdimP⟩ := exists_maximal_isotropic_extension_finrank_ge
    (relationWedge (cupQuotient I)) (plane b a.val)
    ((isCupIsotropic_iff_isIsotropic I (plane b a.val)).mp hiso) 2 hdim
  have ha₀ : row b a.val 0 ∈ P := hUP (Submodule.subset_span (by simp))
  have ha₁ : row b a.val 1 ∈ P := hUP (Submodule.subset_span (by simp))
  obtain ⟨t, ht, hrows⟩ := exists_original_principal_neighborhood_rows_mem
    I b P ((isCupIsotropic_iff_isIsotropic I P).mpr hP.1)
      (hsep P hP hdimP) a.val ha₀ ha₁ a.property.2
  exact ⟨P, hP, hdimP, t, ht, hrows⟩

/-- Finiteness of the actual maximal isotropic spaces of dimension at least
two, derived from the actual coordinate-point subset of a Noetherian
spectrum, its genuine open neighborhoods and their finite subcover. -/
theorem finite_maximal_isotropic_of_separated_with_basis
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis σ k E)
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
      2 ≤ Module.finrank k P → mixedExterior P ⊓ I = pureExterior P) :
    {P : Submodule k E |
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P ∧
        2 ≤ Module.finrank k P}.Finite := by
  classical
  letI : FiniteDimensional k E := b.finiteDimensional_of_finite
  let A := CoordinateFrameWitness I b
  have hall : ∀ a : A,
      ∃ P : Submodule k E,
        IsMaximalIsotropic (relationWedge (cupQuotient I)) P ∧
        2 ≤ Module.finrank k P ∧
        ∃ t : CoordinateRing k σ, MvPolynomial.aeval a.val t ≠ 0 ∧
          ∀ x : Fin 2 × σ → k,
            relationIdeal I b ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom →
            MvPolynomial.aeval x t ≠ 0 → row b x 0 ∈ P ∧ row b x 1 ∈ P :=
    fun a ↦ exists_maximal_principal_neighborhood_of_coordinate_frame I b hsep a
  choose P hP hdim t ht hrows using hall
  let pt (a : A) : scheme I b := coordinatePoint I b a.val a.property.1
  let Z : Set (scheme I b) := Set.range pt
  let Uo (a : A) : (scheme I b).Opens :=
    PrimeSpectrum.basicOpen (Ideal.Quotient.mk (relationIdeal I b) (t a))
  let U (a : A) : Set (scheme I b) := (Uo a).1
  have hcompact : IsCompact Z := NoetherianSpace.isCompact Z
  have hopen (a : A) : IsOpen (U a) := (Uo a).isOpen
  have hcover : Z ⊆ ⋃ a : A, U a := by
    rintro q ⟨a, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨a, ?_⟩
    change coordinatePoint I b a.val a.property.1 ∈ Uo a
    exact (coordinatePoint_mem_basicOpen_iff I b a.val a.property.1 (t a)).mpr (ht a)
  obtain ⟨G, hG⟩ := hcompact.elim_finite_subcover U hopen hcover
  have hfinite : (P '' (G : Set A)).Finite := G.finite_toSet.image P
  apply hfinite.subset
  rintro Q ⟨hQ, hdimQ⟩
  letI : Nontrivial Q := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank k Q)
  obtain ⟨a₀, ha₀⟩ := exists_ne (0 : Q)
  obtain ⟨a₁, hpairQ⟩ :=
    exists_linearIndependent_pair_of_one_lt_finrank (by omega : 1 < Module.finrank k Q) ha₀
  have hpair : LinearIndependent k ![(a₀ : E), (a₁ : E)] := by
    have hfun : (fun r : Fin 2 ↦ Q.subtype (![a₀, a₁] r)) =
        ![(a₀ : E), (a₁ : E)] := by
      funext r
      fin_cases r <;> rfl
    rw [← hfun]
    exact hpairQ.map' Q.subtype (LinearMap.ker_eq_bot.mpr Q.injective_subtype)
  let x := centerCoordinates b ![(a₀ : E), (a₁ : E)]
  have hx₀ : row b x 0 = (a₀ : E) := by
    change row b (centerCoordinates b ![(a₀ : E), (a₁ : E)]) 0 = _
    rw [row_centerCoordinates]
    rfl
  have hx₁ : row b x 1 = (a₁ : E) := by
    change row b (centerCoordinates b ![(a₀ : E), (a₁ : E)]) 1 = _
    rw [row_centerCoordinates]
    rfl
  have hxI : relationIdeal I b ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom := by
    apply (relationIdeal_le_ker_aeval_iff I b x).mpr
    rw [hx₀, hx₁]
    exact hQ.1 (a₀ : E) a₀.property (a₁ : E) a₁.property
  have hxpair : LinearIndependent k ![row b x 0, row b x 1] := by
    rw [hx₀, hx₁]
    exact hpair
  let a : A := ⟨x, hxI, hxpair⟩
  have haZ : pt a ∈ Z := Set.mem_range_self a
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hG haZ)
  obtain ⟨hjG, haj⟩ := Set.mem_iUnion.mp hj
  have haj' : coordinatePoint I b a.val a.property.1 ∈ Uo j := haj
  have hxt : MvPolynomial.aeval a.val (t j) ≠ 0 :=
    (coordinatePoint_mem_basicOpen_iff I b a.val a.property.1 (t j)).mp haj'
  have hmem := hrows j a.val a.property.1 hxt
  have haP : (a₀ : E) ∈ P j := by
    have h := hmem.1
    change row b x 0 ∈ P j at h
    rw [hx₀] at h
    exact h
  have ha₀E : (a₀ : E) ≠ 0 := fun h ↦ ha₀ (Q.injective_subtype h)
  have hsep' : mixedExterior (P j) ⊓ LinearMap.ker (cupQuotient I) = pureExterior (P j) := by
    simpa only [cupQuotient, Submodule.ker_mkQ] using hsep (P j) (hP j) (hdim j)
  have heq : P j = Q := maximalIsotropic_eq_of_nonzero_intersection_of_separated
    (cupQuotient I) (P j) Q (hP j) hQ hsep' haP a₀.property ha₀E
  exact ⟨j, hjG, heq⟩

end ChenRanks.Resonance.IsotropicFrame

namespace ChenRanks.Resonance

universe u v

variable {k : Type u} {E : Type v} [Field k] [AddCommGroup E] [Module k E]
  [FiniteDimensional k E] [Infinite k]

/-- The basis-free original finite-dimensional statement uses a genuinely
constructed finite basis. The finite-family conclusion is never a premise. -/
theorem finite_maximal_cup_isotropic_of_separated
    (I : Submodule k (⋀[k]^2 E))
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
      2 ≤ Module.finrank k P → mixedExterior P ⊓ I = pureExterior P) :
    {P : Submodule k E |
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P ∧
        2 ≤ Module.finrank k P}.Finite := by
  let b : _root_.Module.Basis (ULift.{u} (Fin (Module.finrank k E))) k E :=
    (_root_.Module.finBasis k E).reindex Equiv.ulift.symm
  exact IsotropicFrame.finite_maximal_isotropic_of_separated_with_basis I b hsep

end ChenRanks.Resonance
