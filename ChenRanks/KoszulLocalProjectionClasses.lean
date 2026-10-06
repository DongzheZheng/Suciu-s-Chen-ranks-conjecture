import ChenRanks.KoszulLocalProjectionAction

/-!
# True projected exterior classes in the literal original localization

Actual separation eliminates every mixed class with a transverse dual
factor. The actual projection differs from the identity by such a factor.
The genuine exterior-power universal property therefore proves that the
actual projected exterior input gives the very same original localized
class, for every exterior element, not only for decomposable elements.

No generator-class identity, injectivity, local module isomorphism,
projective stalk comparison, or reducedness is an input.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

private theorem exterior_class_projection_of_mixed_zero
    (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (N : Type*) [AddCommGroup N] [_root_.Module k N]
    (B : (⋀[k]^2 V) →ₗ[k] N) (q : V →ₗ[k] V)
    (hmixed : ∀ a b, B (exteriorWedge a (q b - b)) = 0) :
    B.comp (exteriorPower.map 2 q) = B := by
  apply exteriorPower.linearMap_ext
  ext f
  have hf : exteriorPower.ιMulti k 2 f = exteriorWedge (f 0) (f 1) := by
    change exteriorPower.ιMulti k 2 f = exteriorPower.ιMulti k 2 ![f 0, f 1]
    congr 1
    ext i
    fin_cases i <;> rfl
  have hqf : exteriorPower.map 2 q (exteriorPower.ιMulti k 2 f) =
      exteriorWedge (q (f 0)) (q (f 1)) := by
    rw [exteriorPower.map_apply_ιMulti]
    change exteriorPower.ιMulti k 2 (q ∘ f) =
      exteriorPower.ιMulti k 2 ![q (f 0), q (f 1)]
    congr 1
    ext i
    fin_cases i <;> rfl
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply]
  rw [hqf, hf]
  have hright := hmixed (q (f 0)) (f 1)
  have eright : exteriorWedge (k := k) (q (f 0)) (q (f 1) - f 1) =
      exteriorWedge (k := k) (q (f 0)) (q (f 1)) - exteriorWedge (k := k) (q (f 0)) (f 1) := by
    simp only [← exteriorWedgeBilin_apply, map_sub]
  rw [eright, map_sub] at hright
  have hleft : B (exteriorWedge (q (f 0) - f 0) (f 1)) = 0 := by
    rw [wedgeTwo_swap, map_neg, hmixed (f 1) (f 0), neg_zero]
  have eleft : exteriorWedge (k := k) (q (f 0) - f 0) (f 1) =
      exteriorWedge (k := k) (q (f 0)) (f 1) - exteriorWedge (k := k) (f 0) (f 1) := by
    simp only [← exteriorWedgeBilin_apply, map_sub, LinearMap.sub_apply]
  rw [eleft, map_sub] at hleft
  exact (sub_eq_zero.mp hright).trans (sub_eq_zero.mp hleft)

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E]
variable (P : Submodule k E) (I : Submodule k (⋀[k]^2 E))

/-- The actual constant exterior-class map, obtained from the original
second differential and the literal tensor-product inclusion. -/
def componentPointExteriorClassLinear (eP : P) :
    (⋀[k]^2 (_root_.Module.Dual k E)) →ₗ[k] componentPointOriginalModule k E P I eP :=
  (coefficientExtendedSecondMap k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)
    (ambientComponentPointLocalRing k E P eP)).restrictScalars k ∘ₗ
      TensorProduct.mk k (S k (_root_.Module.Dual k E)) (⋀[k]^2 (_root_.Module.Dual k E)) 1

@[simp] theorem componentPointExteriorClassLinear_apply (eP : P)
    (w : ⋀[k]^2 (_root_.Module.Dual k E)) :
    componentPointExteriorClassLinear k E P I eP w =
      coefficientExtendedExteriorClass k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)
        (ambientComponentPointLocalRing k E P eP) w := rfl

variable [FiniteDimensional k E]

/-- Separation proves the exact mixed-class vanishing needed for the
actual projection. A true finite basis is chosen, rather than supplied. -/
theorem actualPointLocalized_projectionDifference_class_zero
    (hsep : I ⊓ mixedExterior P ≤ pureExterior P) (eP : P)
    (v : _root_.Module.Dual k E) (hv : v (eP : E) = 1)
    (a b : _root_.Module.Dual k E) :
    componentPointExteriorClassLinear k E P I eP
      (exteriorWedge a (componentDualProjection k E P b - b)) = 0 := by
  letI : _root_.Module.Free k P.dualAnnihilator :=
    _root_.Module.Free.of_basis (_root_.Module.Basis.ofVectorSpace k P.dualAnnihilator)
  let c := _root_.Module.finBasis k P.dualAnnihilator
  exact actualPointLocalized_mixedClass_eq_zero_of_separation k E P I c hsep
    (eP : E) eP.property v hv a
    ⟨componentDualProjection k E P b - b,
      componentDualProjection_sub_mem_annihilator k E P b⟩

/-- Every genuine exterior element has the same actual localized class
after the true projection. Exterior universal-property extensionality
extends the proved mixed-class identity to the entire actual exterior
power. -/
theorem actualPointLocalized_projectedExterior_class
    (hsep : I ⊓ mixedExterior P ≤ pureExterior P) (eP : P)
    (v : _root_.Module.Dual k E) (hv : v (eP : E) = 1)
    (w : ⋀[k]^2 (_root_.Module.Dual k E)) :
    componentPointExteriorClassLinear k E P I eP
      (exteriorPower.map 2 (componentDualProjection k E P) w) =
      componentPointExteriorClassLinear k E P I eP w := by
  exact DFunLike.congr_fun (exterior_class_projection_of_mixed_zero k (_root_.Module.Dual k E)
    (componentPointOriginalModule k E P I eP) (componentPointExteriorClassLinear k E P I eP)
    (componentDualProjection k E P)
    (actualPointLocalized_projectionDifference_class_zero k E P I hsep eP v hv)) w

end ChenRanks.Koszul
