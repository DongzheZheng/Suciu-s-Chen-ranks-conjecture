import ChenRanks.KoszulFunctoriality
import ChenRanks.KoszulPresentation

/-!
# Identity, composition, and presentation naturality of the actual maps

The maps are the previously constructed maps on the original symmetric
algebras, tensor terms, and original quotient modules. All identities
are proved on actual generators or actual quotient representatives.
Relation containments describe genuine quadratic data, rather than
asserting eventual injectivity, local isomorphism, or the Chen formula.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V W X : Type*) [AddCommGroup V] [AddCommGroup W] [AddCommGroup X]
  [_root_.Module k V] [_root_.Module k W] [_root_.Module k X]

omit [AddCommGroup W] [AddCommGroup X] [_root_.Module k W] [_root_.Module k X] in
/-- The true symmetric-algebra map induced by the identity is the identity. -/
theorem symmetricMap_id :
    symmetricMap k V V (LinearMap.id : V →ₗ[k] V) = AlgHom.id k (S k V) := by
  apply SymmetricAlgebra.algHom_ext
  ext v
  change symmetricMap k V V (LinearMap.id : V →ₗ[k] V) (SymmetricAlgebra.ι k V v) =
    SymmetricAlgebra.ι k V v
  rw [symmetricMap_ι, LinearMap.id_apply]

/-- The true symmetric-algebra maps respect actual composition. -/
theorem symmetricMap_comp (f : V →ₗ[k] W) (g : W →ₗ[k] X) :
    (symmetricMap k W X g).comp (symmetricMap k V W f) =
      symmetricMap k V X (g.comp f) := by
  apply SymmetricAlgebra.algHom_ext
  ext v
  change symmetricMap k W X g (symmetricMap k V W f (SymmetricAlgebra.ι k V v)) =
    symmetricMap k V X (g.comp f) (SymmetricAlgebra.ι k V v)
  rw [symmetricMap_ι, symmetricMap_ι, symmetricMap_ι]
  rfl

omit [AddCommGroup W] [AddCommGroup X] [_root_.Module k W] [_root_.Module k X] in
/-- The actual first tensor map induced by the identity fixes each tensor. -/
theorem tensorOneMap_id (z : C1 k V) :
    tensorOneMap k V V (LinearMap.id : V →ₗ[k] V) z = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | add z t hz ht => simp only [map_add, hz, ht]
  | tmul s v => rw [tensorOneMap_tmul, symmetricMap_id, AlgHom.id_apply, LinearMap.id_apply]

/-- The actual first tensor maps respect composition, on actual tensors. -/
theorem tensorOneMap_comp (f : V →ₗ[k] W) (g : W →ₗ[k] X) (z : C1 k V) :
    tensorOneMap k W X g (tensorOneMap k V W f z) =
      tensorOneMap k V X (g.comp f) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add z t hz ht => simp only [map_add, hz, ht]
  | tmul s v =>
      rw [tensorOneMap_tmul, tensorOneMap_tmul, tensorOneMap_tmul,
        ← AlgHom.comp_apply, symmetricMap_comp]
      rfl

/-- The actual second tensor maps also respect actual composition. -/
theorem tensorTwoMap_comp (f : V →ₗ[k] W) (g : W →ₗ[k] X) (z : C2 k V) :
    tensorTwoMap k W X g (tensorTwoMap k V W f z) =
      tensorTwoMap k V X (g.comp f) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add z t hz ht => simp only [map_add, hz, ht]
  | tmul s w =>
      simp only [tensorTwoMap, TensorProduct.map_tmul]
      change symmetricMap k W X g (symmetricMap k V W f s) ⊗ₜ[k]
          exteriorPower.map 2 g (exteriorPower.map 2 f w) =
        symmetricMap k V X (g.comp f) s ⊗ₜ[k] exteriorPower.map 2 (g.comp f) w
      rw [← AlgHom.comp_apply, symmetricMap_comp, exteriorPower.map_comp, LinearMap.comp_apply]

variable (K : Submodule k (⋀[k]^2 V)) (L : Submodule k (⋀[k]^2 W))
  (N : Submodule k (⋀[k]^2 X))

/-- Actual relation containment is closed under actual composition. -/
theorem composedRelationContainment (f : V →ₗ[k] W) (g : W →ₗ[k] X)
    (hKL : K ≤ L.comap (exteriorPower.map 2 f))
    (hLN : L ≤ N.comap (exteriorPower.map 2 g)) :
    K ≤ N.comap (exteriorPower.map 2 (g.comp f)) := by
  intro z hz
  change exteriorPower.map 2 (g.comp f) z ∈ N
  rw [exteriorPower.map_comp, LinearMap.comp_apply]
  exact hLN (hKL hz)

/-- Composition holds for the genuine maps of original quotient modules. -/
theorem moduleMap_comp (f : V →ₗ[k] W) (g : W →ₗ[k] X)
    (hKL : K ≤ L.comap (exteriorPower.map 2 f))
    (hLN : L ≤ N.comap (exteriorPower.map 2 g)) :
    (moduleMap k W X g L N hLN).comp (moduleMap k V W f K L hKL) =
      moduleMap k V X (g.comp f) K N
        (composedRelationContainment k V W X K L N f g hKL hLN) := by
  apply LinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro x
  simp only [LinearMap.comp_apply, moduleMap_mk]
  have hx : cycleMap k W X g (cycleMap k V W f x) = cycleMap k V X (g.comp f) x := by
    apply Subtype.ext
    exact tensorOneMap_comp k V W X f g x.val
  rw [hx]

omit [AddCommGroup W] [AddCommGroup X] [_root_.Module k W] [_root_.Module k X] in
/-- The true identity exterior map preserves the original quadratic data. -/
theorem identityRelationContainment :
    K ≤ K.comap (exteriorPower.map 2 (LinearMap.id : V →ₗ[k] V)) := by
  intro z hz
  simpa only [exteriorPower.map_id, LinearMap.id_apply] using hz

omit [AddCommGroup W] [AddCommGroup X] [_root_.Module k W] [_root_.Module k X] in
/-- The genuine identity map on original quotient modules is the identity. -/
theorem moduleMap_id :
    moduleMap k V V (LinearMap.id : V →ₗ[k] V) K K
      (identityRelationContainment k V K) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro x
  rw [moduleMap_mk, LinearMap.id_apply]
  have hx : cycleMap k V V (LinearMap.id : V →ₗ[k] V) x = x := by
    apply Subtype.ext
    exact tensorOneMap_id k V x.val
  rw [hx]

omit [AddCommGroup X] [_root_.Module k X] in
/-- The genuine second-term presentation map commutes with the genuine
canonical original-module map. This identifies the actual maps used in
the local comparison, rather than merely comparing dimensions. -/
theorem moduleMap_secondTensorToModule (f : V →ₗ[k] W)
    (hKL : K ≤ L.comap (exteriorPower.map 2 f)) (z : C2 k V) :
    moduleMap k V W f K L hKL (secondTensorToModule k V K z) =
      secondTensorToModule k W L (tensorTwoMap k V W f z) := by
  change moduleMap k V W f K L hKL (Submodule.Quotient.mk (delta2ToCycles k V z)) =
    Submodule.Quotient.mk (delta2ToCycles k W (tensorTwoMap k V W f z))
  rw [moduleMap_mk]
  have hz : cycleMap k V W f (delta2ToCycles k V z) =
      delta2ToCycles k W (tensorTwoMap k V W f z) := by
    apply Subtype.ext
    exact tensorOneMap_delta2 k V W f z
  rw [hz]

end ChenRanks.Koszul
