import ChenRanks.KoszulObjects

/-!
# Actual quotient maps of Koszul modules

A linear map of generating spaces induces the actual map of symmetric
algebras and tensor Koszul complexes. Naturality of both differentials
proves that this map descends to the original Koszul quotient whenever
it carries the actual quadratic relations into the target relations.
For the canonical image relation space this condition is derived.

These are the maps in the manuscript's stable-decomposition theorem.
No assertion of their eventual injectivity or surjectivity is assumed.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [CommRing k]
variable (V W : Type*) [AddCommGroup V] [AddCommGroup W]
  [_root_.Module k V] [_root_.Module k W]
variable (f : V →ₗ[k] W)

/-- The actual algebra map on polynomial coefficients. -/
def symmetricMap : S k V →ₐ[k] S k W :=
  SymmetricAlgebra.lift (SymmetricAlgebra.ι k W ∘ₗ f)

@[simp] theorem symmetricMap_ι (v : V) :
    symmetricMap k V W f (SymmetricAlgebra.ι k V v) = SymmetricAlgebra.ι k W (f v) := by
  simp [symmetricMap]

/-- The actual first tensor map. -/
def tensorOneMap : C1 k V →ₗ[k] C1 k W :=
  TensorProduct.map (symmetricMap k V W f).toLinearMap f

@[simp] theorem tensorOneMap_tmul (s : S k V) (v : V) :
    tensorOneMap k V W f (s ⊗ₜ[k] v) =
      symmetricMap k V W f s ⊗ₜ[k] f v := rfl

/-- Naturality of actual multiplication. -/
theorem delta1_tensorOneMap (z : C1 k V) :
    delta1 k W (tensorOneMap k V W f z) =
      symmetricMap k V W f (delta1 k V z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z t hz ht => simpa only [map_add] using congrArg₂ (· + ·) hz ht
  | tmul s v => simp

/-- Actual scalar compatibility, with the target action through the
constructed map of symmetric algebras. -/
theorem tensorOneMap_smul (s : S k V) (z : C1 k V) :
    tensorOneMap k V W f (s • z) =
      symmetricMap k V W f s • tensorOneMap k V W f z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z t hz ht => simpa only [smul_add, map_add] using congrArg₂ (· + ·) hz ht
  | tmul t v =>
    simp only [TensorProduct.smul_tmul', smul_eq_mul, tensorOneMap_tmul, map_mul]

/-- Naturality of the actual alternating second differential. -/
theorem tensorOneMap_delta2Linear :
    tensorOneMap k V W f ∘ₗ delta2Linear k V =
      delta2Linear k W ∘ₗ exteriorPower.map 2 f := by
  apply exteriorPower.linearMap_ext
  ext a
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    delta2Linear_wedge, exteriorPower.map_apply_ιMulti, Function.comp_apply,
    map_sub, tensorOneMap_smul, tensorOneMap_tmul, map_one, symmetricMap_ι]

/-- The actual second tensor map. -/
def tensorTwoMap : C2 k V →ₗ[k] C2 k W :=
  TensorProduct.map (symmetricMap k V W f).toLinearMap (exteriorPower.map 2 f)

/-- Naturality of the actual second differential. -/
theorem tensorOneMap_delta2 (z : C2 k V) :
    tensorOneMap k V W f (delta2 k V z) = delta2 k W (tensorTwoMap k V W f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z t hz ht => simpa only [map_add] using congrArg₂ (· + ·) hz ht
  | tmul s w =>
    change tensorOneMap k V W f (s • delta2Linear k V w) =
      symmetricMap k V W f s • delta2Linear k W (exteriorPower.map 2 f w)
    rw [tensorOneMap_smul]
    exact congrArg (fun z ↦ symmetricMap k V W f s • z)
      (DFunLike.congr_fun (tensorOneMap_delta2Linear k V W f) w)

/-- The actual map on cycles, constructed from differential naturality. -/
def cycleMap : LinearMap.ker (delta1 k V) →ₗ[k] LinearMap.ker (delta1 k W) where
  toFun z := ⟨tensorOneMap k V W f z, by
    apply LinearMap.mem_ker.mpr
    rw [delta1_tensorOneMap, LinearMap.mem_ker.mp z.property, map_zero]⟩
  map_add' _ _ := by apply Subtype.ext; exact map_add _ _ _
  map_smul' _ _ := by apply Subtype.ext; exact map_smul _ _ _

variable (K : Submodule k (⋀[k]^2 V)) (L : Submodule k (⋀[k]^2 W))

/-- The target relation space in the paper's canonical quotient map. -/
def quadraticImage : Submodule k (⋀[k]^2 W) := K.map (exteriorPower.map 2 f)

/-- The actual exterior map on the supplied relation modules. -/
def quadraticRestriction (h : K ≤ L.comap (exteriorPower.map 2 f)) : K →ₗ[k] L :=
  ((exteriorPower.map 2 f).comp K.subtype).codRestrict L (fun w ↦ h w.property)

/-- Actual polynomial coefficients and relation factors are both mapped. -/
def relationTensorMap (h : K ≤ L.comap (exteriorPower.map 2 f)) :
    (S k V ⊗[k] K) →ₗ[k] (S k W ⊗[k] L) :=
  TensorProduct.map (symmetricMap k V W f).toLinearMap
    (quadraticRestriction k V W f K L h)

theorem cycleMap_relationMap (h : K ≤ L.comap (exteriorPower.map 2 f))
    (z : S k V ⊗[k] K) :
    cycleMap k V W f (relationMap k V K z) =
      relationMap k W L (relationTensorMap k V W f K L h z) := by
  apply Subtype.ext
  have ht : tensorTwoMap k V W f
      (AlgebraTensorModule.lTensor (S k V) (S k V) K.subtype z) =
      AlgebraTensorModule.lTensor (S k W) (S k W) L.subtype
        (relationTensorMap k V W f K L h z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z t hz ht => simpa only [map_add] using congrArg₂ (· + ·) hz ht
    | tmul s w => rfl
  change tensorOneMap k V W f (delta2K k V K z) =
    delta2K k W L (relationTensorMap k V W f K L h z)
  rw [delta2K, LinearMap.comp_apply, tensorOneMap_delta2, ht]
  rfl

/-- The real relation image is carried into the real target relation image. -/
theorem cycleMap_relationRange (h : K ≤ L.comap (exteriorPower.map 2 f)) :
    (LinearMap.range (relationMap k V K)).restrictScalars k ≤
      ((LinearMap.range (relationMap k W L)).restrictScalars k).comap
        (cycleMap k V W f) := by
  rintro z ⟨t, rfl⟩
  exact ⟨relationTensorMap k V W f K L h t, (cycleMap_relationMap k V W f K L h t).symm⟩

/-- The actual original quotient map, with no decomposition hypothesis. -/
def moduleMap (h : K ≤ L.comap (exteriorPower.map 2 f)) :
    Module k V K →ₗ[k] Module k W L :=
  ((LinearMap.range (relationMap k V K)).restrictScalars k).mapQ
    ((LinearMap.range (relationMap k W L)).restrictScalars k)
    (cycleMap k V W f) (cycleMap_relationRange k V W f K L h)

@[simp] theorem moduleMap_mk (h : K ≤ L.comap (exteriorPower.map 2 f))
    (z : LinearMap.ker (delta1 k V)) :
    moduleMap k V W f K L h (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (cycleMap k V W f z) := rfl

/-- Polynomial scalar compatibility of the actual quotient map. -/
theorem moduleMap_smul (h : K ≤ L.comap (exteriorPower.map 2 f))
    (s : S k V) (z : Module k V K) :
    moduleMap k V W f K L h (s • z) =
      symmetricMap k V W f s • moduleMap k V W f K L h z := by
  refine Submodule.Quotient.induction_on _ z ?_
  intro t
  change Submodule.Quotient.mk (cycleMap k V W f (s • t)) =
    Submodule.Quotient.mk (symmetricMap k V W f s • cycleMap k V W f t)
  congr 1
  apply Subtype.ext
  exact tensorOneMap_smul k V W f s t.val

/-- The original quotient map as an actual semilinear map for the
proved symmetric-algebra scalar homomorphism. -/
def moduleMapSemilinear (h : K ≤ L.comap (exteriorPower.map 2 f)) :
    Module k V K →ₛₗ[(symmetricMap k V W f).toRingHom] Module k W L where
  toFun := moduleMap k V W f K L h
  map_add' := (moduleMap k V W f K L h).map_add
  map_smul' := moduleMap_smul k V W f K L h

/-- For the actual exterior image of K, containment is a proved fact. -/
theorem quadraticImage_containment :
    K ≤ (quadraticImage k V W f K).comap (exteriorPower.map 2 f) := by
  intro w hw
  exact Submodule.mem_map_of_mem hw

/-- The paper's canonical map to the quotient with actual image relations. -/
def canonicalModuleMap : Module k V K →ₗ[k]
    Module k W (quadraticImage k V W f K) :=
  moduleMap k V W f K (quadraticImage k V W f K)
    (quadraticImage_containment k V W f K)

end ChenRanks.Koszul
