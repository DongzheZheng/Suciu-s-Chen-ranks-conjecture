import ChenRanks.KoszulFunctorialityCalculus
import ChenRanks.KoszulGradedFunctoriality
import ChenRanks.KoszulOriginalModuleStructures

/-!
# Genuine Koszul functoriality under actual linear equivalences

A genuine linear equivalence transports the genuine quadratic submodule
by its actual exterior-square map. Its inverse satisfies the actual
reverse relation containment. Composition and identity on the original
quotients then prove both inverse formulas. The already proved original
degree diagrams derive bijectivity of the actual homogeneous maps for
arbitrary genuine bases. No bijective module-map, grading-compatibility,
eventual or effective assertion is supplied as a premise.
-/

noncomputable section

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V W : Type*) [AddCommGroup V] [AddCommGroup W]
  [_root_.Module k V] [_root_.Module k W]

local instance (priority := 2500) equivalenceOriginalGroups
    (U : Type*) [AddCommGroup U] [_root_.Module k U]
    (J : Submodule k (⋀[k]^2 U)) : AddCommGroup (Module k U J) :=
  originalModuleAddCommGroup k U J

local instance (priority := 2500) equivalenceOriginalMonoids
    (U : Type*) [AddCommGroup U] [_root_.Module k U]
    (J : Submodule k (⋀[k]^2 U)) : AddCommMonoid (Module k U J) :=
  (originalModuleAddCommGroup k U J).toAddCommMonoid

local instance (priority := 2500) equivalenceOriginalCoefficients
    (U : Type*) [AddCommGroup U] [_root_.Module k U]
    (J : Submodule k (⋀[k]^2 U)) : _root_.Module k (Module k U J) :=
  originalModuleScalarModule k U J

variable (K : Submodule k (⋀[k]^2 V)) (e : V ≃ₗ[k] W)

/-- Actual inverse linear equivalences carry the actual image relations
back into the original quadratic submodule. -/
theorem linearEquivalenceQuadraticInverseContainment :
    quadraticImage k V W e.toLinearMap K ≤
      K.comap (exteriorPower.map 2 e.symm.toLinearMap) := by
  rintro z ⟨w, hw, rfl⟩
  change exteriorPower.map 2 e.symm.toLinearMap
    (exteriorPower.map 2 e.toLinearMap w) ∈ K
  have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    ext v
    exact e.symm_apply_apply v
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, he,
    exteriorPower.map_id, LinearMap.id_apply]
  exact hw

/-- Both actual original module maps compose to the original identity. -/
theorem linearEquivalenceModuleMap_inverse_apply (z : Module k V K) :
    moduleMap k W V e.symm.toLinearMap
      (quadraticImage k V W e.toLinearMap K) K
      (linearEquivalenceQuadraticInverseContainment k V W K e)
      (moduleMap k V W e.toLinearMap K (quadraticImage k V W e.toLinearMap K)
        (quadraticImage_containment k V W e.toLinearMap K) z) = z := by
  have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    ext v
    exact e.symm_apply_apply v
  have hc := moduleMap_comp k V W V K
    (quadraticImage k V W e.toLinearMap K) K e.toLinearMap e.symm.toLinearMap
    (quadraticImage_containment k V W e.toLinearMap K)
    (linearEquivalenceQuadraticInverseContainment k V W K e)
  simp only [he] at hc
  have h := DFunLike.congr_fun hc z
  rw [moduleMap_id] at h
  exact h

/-- The opposite composition is also the actual original identity. -/
theorem linearEquivalenceModuleMap_apply_inverse
    (z : Module k W (quadraticImage k V W e.toLinearMap K)) :
    moduleMap k V W e.toLinearMap K (quadraticImage k V W e.toLinearMap K)
      (quadraticImage_containment k V W e.toLinearMap K)
      (moduleMap k W V e.symm.toLinearMap
        (quadraticImage k V W e.toLinearMap K) K
        (linearEquivalenceQuadraticInverseContainment k V W K e) z) = z := by
  have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
    ext w
    exact e.apply_symm_apply w
  have hc := moduleMap_comp k W V W
    (quadraticImage k V W e.toLinearMap K) K
    (quadraticImage k V W e.toLinearMap K) e.symm.toLinearMap e.toLinearMap
    (linearEquivalenceQuadraticInverseContainment k V W K e)
    (quadraticImage_containment k V W e.toLinearMap K)
  simp only [he] at hc
  have h := DFunLike.congr_fun hc z
  rw [moduleMap_id] at h
  exact h

/-- Actual equivalences of generating spaces induce bijective maps of
literal original quotient modules, with the actual image relations. -/
theorem linearEquivalenceModuleMap_bijective :
    Function.Bijective
      (moduleMap k V W e.toLinearMap K (quadraticImage k V W e.toLinearMap K)
        (quadraticImage_containment k V W e.toLinearMap K)) :=
  ⟨Function.LeftInverse.injective (linearEquivalenceModuleMap_inverse_apply k V W K e),
    Function.RightInverse.surjective (linearEquivalenceModuleMap_apply_inverse k V W K e)⟩

variable {ι τ : Type*} [Fintype ι] [Fintype τ]
variable (b : _root_.Module.Basis ι k V) (c : _root_.Module.Basis τ k W)

/-- Every actual homogeneous map is bijective, for arbitrary original
bases. Both degree-preservation statements come from the true tensor
and original quotient diagrams, rather than a supplied compatibility. -/
theorem linearEquivalenceHomogeneousModuleMap_bijective (r : ℕ) :
    Function.Bijective
      (homogeneousModuleMap k V W b c e.toLinearMap K
        (quadraticImage k V W e.toLinearMap K)
        (quadraticImage_containment k V W e.toLinearMap K) r) := by
  let L := quadraticImage k V W e.toLinearMap K
  let hf := quadraticImage_containment k V W e.toLinearMap K
  let hg := linearEquivalenceQuadraticInverseContainment k V W K e
  let S := homogeneousModuleEquivOriginalDegree k V b K r
  let T := homogeneousModuleEquivOriginalDegree k W c L r
  constructor
  · intro x y hxy
    apply S.injective
    apply Subtype.ext
    apply (linearEquivalenceModuleMap_bijective k V W K e).1
    have hx := homogeneousModuleMap_originalDiagram k V W b c e.toLinearMap K L hf r x
    have hy := homogeneousModuleMap_originalDiagram k V W b c e.toLinearMap K L hf r y
    exact hx.symm.trans ((congrArg (fun t => (T t).val) hxy).trans hy)
  · intro z
    let x : LinearMap.range (degreeCycleToUngraded k V b K r) :=
      ⟨moduleMap k W V e.symm.toLinearMap L K hg (T z).val,
        moduleMap_originalDegree_mem k W V c b e.symm.toLinearMap L K hg r
          (T z).val (T z).property⟩
    refine ⟨S.symm x, ?_⟩
    apply T.injective
    apply Subtype.ext
    have hd := homogeneousModuleMap_originalDiagram k V W b c e.toLinearMap K L hf r
      (S.symm x)
    exact hd.trans ((congrArg
      (fun t => moduleMap k V W e.toLinearMap K L hf t.val)
      (S.apply_symm_apply x)).trans
        (linearEquivalenceModuleMap_apply_inverse k V W K e (T z).val))

end ChenRanks.Koszul
