import ChenRanks.GroupAlgebraAugmentationCotangent

/-! The native dual of the actual augmentation cotangent space is the
actual vector space of additive characters of the original group. The
linear equivalence is derived from the original cotangent universal
property. It neither assigns a cotangent dimension nor identifies any
higher lower-central quotient or completed Lie algebra.
-/

noncomputable section

namespace ChenRanks.GroupAlgebra

variable (k G : Type*) [Field k] [Group G]

/-- A true original character space, with its native pointwise operations. -/
def augmentationCotangentDualCharacters :
    Module.Dual k (augmentationCotangent k G) ≃ₗ[k] (Additive G →+ k) where
  toFun f := f.toAddMonoidHom.comp (augmentationCotangentCharacter k G)
  invFun χ := augmentationCotangentLift k G k χ
  left_inv f := by
    apply (augmentationCotangentLift_unique k G k
      (f.toAddMonoidHom.comp (augmentationCotangentCharacter k G)) f
      (fun _ => rfl)).symm
  right_inv χ := by
    apply AddMonoidHom.ext
    intro g
    exact augmentationCotangentLift_class k G k χ g.toMul
  map_add' f h := by
    apply AddMonoidHom.ext
    intro g
    rfl
  map_smul' c f := by
    apply AddMonoidHom.ext
    intro g
    rfl

@[simp]
theorem augmentationCotangentDualCharacters_apply
    (f : Module.Dual k (augmentationCotangent k G)) (g : G) :
    augmentationCotangentDualCharacters k G f (Additive.ofMul g) =
      f (augmentationCotangentClass k G g) := rfl

@[simp]
theorem augmentationCotangentDualCharacters_symm_class
    (χ : Additive G →+ k) (g : G) :
    (augmentationCotangentDualCharacters k G).symm χ
      (augmentationCotangentClass k G g) = χ (Additive.ofMul g) :=
  augmentationCotangentLift_class k G k χ g

end ChenRanks.GroupAlgebra
