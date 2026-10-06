import ChenRanks.ActualProjectiveResonanceComponentVectors
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Dimension counts of the actual projective components

The component type is the native irreducible-component subtype of the
annihilator-quotient Proj. Its dimension is computed from the span of its
actual vector evaluation points. Both definitions precede, and do not use,
the maximal-isotropic component classification.

Under the genuine geometric separation condition, that classification and
the proved vector-span equality give an equivalence with the actual maximal
isotropic family, preserving dimensions. The resulting count equality does
not assume a component enumeration or assign a dimension by an index.
This generic result still requires the actual singular-cohomology dictionary
before it can be applied to the arrangement Chen-rank statement.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

namespace ChenRanks.Koszul

open ChenRanks.Resonance

universe u

variable (k E : Type u) [Field k] [AddCommGroup E] [_root_.Module k E]
variable {ι : Type u} [Fintype ι]
  (b : _root_.Module.Basis ι k (_root_.Module.Dual k E))
variable (I : Submodule k (⋀[k]^2 E))

/-- The actual native irreducible components, without an assumed index set. -/
abbrev ActualProjectiveResonanceComponent :=
  {C : Set (actualProjectiveResonanceScheme k (_root_.Module.Dual k E) b
    (exteriorAnnihilator k E 2 I)) //
      C ∈ irreducibleComponents
        (actualProjectiveResonanceScheme k (_root_.Module.Dual k E) b
          (exteriorAnnihilator k E 2 I))}

variable [FiniteDimensional k E]

/-- The actual affine vector-span dimension of a native projective component. -/
def actualProjectiveResonanceComponentDimension
    (C : ActualProjectiveResonanceComponent k E b I) : ℕ :=
  _root_.Module.finrank k (actualProjectiveComponentAffineSpan k E b I C.val)

/-- The cardinality of the actual dimension fiber of native components. -/
def actualProjectiveResonanceComponentDimensionCount (m : ℕ) : ℕ :=
  Nat.card {C : ActualProjectiveResonanceComponent k E b I //
    actualProjectiveResonanceComponentDimension k E b I C = m}

variable [IsAlgClosed k] [CharZero k]
variable (hsep : ∀ P : Submodule k E,
  IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
    2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)

/-- The actual original subspace determines its actual native component. -/
def actualProjectiveLinearConeComponent
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) :
    ActualProjectiveResonanceComponent k E b I :=
  ⟨actualProjectiveLinearCone k E b I P.val,
    actualProjectiveLinearCone_mem_irreducibleComponents k E b I hsep P⟩

theorem actualProjectiveLinearConeComponent_injective :
    Function.Injective (actualProjectiveLinearConeComponent k E b I hsep) := by
  intro P Q h
  have hsets := congrArg Subtype.val h
  apply Subtype.ext
  calc
    P.val = actualProjectiveComponentAffineSpan k E b I
        (actualProjectiveLinearCone k E b I P.val) :=
      (actualProjectiveComponentAffineSpan_linearCone k E b I hsep P).symm
    _ = actualProjectiveComponentAffineSpan k E b I
        (actualProjectiveLinearCone k E b I Q.val) := congrArg
      (actualProjectiveComponentAffineSpan k E b I) hsets
    _ = Q.val := actualProjectiveComponentAffineSpan_linearCone k E b I hsep Q

theorem actualProjectiveLinearConeComponent_surjective :
    Function.Surjective (actualProjectiveLinearConeComponent k E b I hsep) := by
  intro C
  have hC : C.val ∈ Set.range (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
      actualProjectiveLinearCone k E b I P.val) :=
    Eq.mp (congrArg (fun T => C.val ∈ T)
      (irreducibleComponents_actualProjectiveResonanceScheme_eq_range k E b I hsep))
      C.property
  obtain ⟨P, hP⟩ := hC
  exact ⟨P, Subtype.ext hP⟩

/-- The proved classification gives the genuine component equivalence. -/
def actualProjectiveResonanceComponentEquiv :
    OriginalMaximalIsotropicFamily (cupQuotient I) ≃
      ActualProjectiveResonanceComponent k E b I :=
  Equiv.ofBijective (actualProjectiveLinearConeComponent k E b I hsep)
    ⟨actualProjectiveLinearConeComponent_injective k E b I hsep,
      actualProjectiveLinearConeComponent_surjective k E b I hsep⟩

theorem actualProjectiveResonanceComponentEquiv_dimension
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) :
    actualProjectiveResonanceComponentDimension k E b I
        (actualProjectiveResonanceComponentEquiv k E b I hsep P) =
      _root_.Module.finrank k P.val := by
  change _root_.Module.finrank k (actualProjectiveComponentAffineSpan k E b I
    (actualProjectiveLinearCone k E b I P.val)) = _
  rw [actualProjectiveComponentAffineSpan_linearCone k E b I hsep P]

/-- Actual dimensions are preserved on the literal dimension fibers. -/
def actualProjectiveResonanceComponentDimensionFiberEquiv (m : ℕ) :
    {P : OriginalMaximalIsotropicFamily (cupQuotient I) //
      _root_.Module.finrank k P.val = m} ≃
    {C : ActualProjectiveResonanceComponent k E b I //
      actualProjectiveResonanceComponentDimension k E b I C = m} :=
  (actualProjectiveResonanceComponentEquiv k E b I hsep).subtypeEquiv
    (fun P => by rw [actualProjectiveResonanceComponentEquiv_dimension k E b I hsep P])

/-- The native component fiber count equals the original subspace fiber count. -/
theorem actualProjectiveResonanceComponentDimensionCount_eq
    (m : ℕ) :
    actualProjectiveResonanceComponentDimensionCount k E b I m =
      originalMaximalIsotropicDimensionCount (cupQuotient I)
        (fun P hP hdim => by
          simpa only [cupQuotient, Submodule.ker_mkQ] using hsep P hP hdim) m := by
  classical
  let hsep' : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
        2 ≤ _root_.Module.finrank k P →
          mixedExterior P ⊓ LinearMap.ker (cupQuotient I) = pureExterior P :=
    fun P hP hdim => by
      simpa only [cupQuotient, Submodule.ker_mkQ] using hsep P hP hdim
  letI := originalMaximalIsotropicFamilyFintype (cupQuotient I) hsep'
  have hc := Nat.card_congr
    (actualProjectiveResonanceComponentDimensionFiberEquiv k E b I hsep m)
  change Nat.card {C : ActualProjectiveResonanceComponent k E b I //
    actualProjectiveResonanceComponentDimension k E b I C = m} = _
  rw [← hc, Nat.card_eq_fintype_card]
  rfl

end ChenRanks.Koszul
