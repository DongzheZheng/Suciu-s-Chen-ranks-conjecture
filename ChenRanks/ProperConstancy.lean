import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Kaehler.Basic

/-!
# Constancy of regular functions on actual proper integral schemes

This is a geometric step of the vertical-function argument. The objects here
are mathlib schemes and their rings of global sections, not a predicate which
asserts fibre constancy. A universally closed integral scheme over an
algebraically closed field has no additional global regular functions.

This does not yet extend rational functions without codimension-one poles
to global regular functions, construct the general fibre, or identify its
rational differential with the ambient rational differential.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace ChenRanks

universe u

variable {k : Type u} [Field k]

/-- The actual structure map on scalar-valued global regular functions. -/
def globalScalarMap {X : Scheme} (f : X ⟶ Spec (.of k)) : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom

/-- Properness (in fact universal closedness) and integrality imply that
all global regular functions are scalars over an algebraically closed field. -/
theorem globalScalarMap_bijective [IsAlgClosed k]
    {X : Scheme} (f : X ⟶ Spec (.of k))
    [IsIntegral X] [UniversallyClosed f] :
    Function.Bijective (globalScalarMap f) := by
  have h : (globalScalarMap f).IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  exact IsAlgClosed.ringHom_bijective_of_isIntegral (globalScalarMap f) h

/-- Constancy as an equality in the actual ring of global sections. -/
theorem global_regular_function_constant [IsAlgClosed k]
    {X : Scheme} (f : X ⟶ Spec (.of k))
    [IsIntegral X] [UniversallyClosed f] (s : Γ(X, ⊤)) :
    ∃ c : k, globalScalarMap f c = s :=
  (globalScalarMap_bijective f).2 s

/-- The complex proper-variety instance used in the manuscript. -/
theorem complex_proper_regular_function_constant
    {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    [IsIntegral X] [IsProper f] (s : Γ(X, ⊤)) :
    ∃ c : ℂ, globalScalarMap f c = s :=
  global_regular_function_constant f s

/-- The universal differential of every actual global regular function
vanishes, with the scalar algebra induced by the scheme's structure map. -/
theorem global_regular_differential_eq_zero [IsAlgClosed k]
    {X : Scheme} (f : X ⟶ Spec (.of k))
    [IsIntegral X] [UniversallyClosed f] :
    letI : Algebra k Γ(X, ⊤) := (globalScalarMap f).toAlgebra
    ∀ s : Γ(X, ⊤), KaehlerDifferential.D k Γ(X, ⊤) s = 0 := by
  letI : Algebra k Γ(X, ⊤) := (globalScalarMap f).toAlgebra
  intro s
  obtain ⟨c, rfl⟩ := global_regular_function_constant f s
  exact (KaehlerDifferential.D k Γ(X, ⊤)).map_algebraMap c

/-- The entire module of relative Kähler differentials of global sections
is zero; this follows from actual scalar surjectivity. -/
theorem global_kaehlerDifferentials_subsingleton [IsAlgClosed k]
    {X : Scheme} (f : X ⟶ Spec (.of k))
    [IsIntegral X] [UniversallyClosed f] :
    letI : Algebra k Γ(X, ⊤) := (globalScalarMap f).toAlgebra
    Subsingleton Ω[Γ(X, ⊤)⁄k] := by
  letI : Algebra k Γ(X, ⊤) := (globalScalarMap f).toAlgebra
  exact KaehlerDifferential.subsingleton_of_surjective k Γ(X, ⊤)
    (globalScalarMap_bijective f).2

end ChenRanks
