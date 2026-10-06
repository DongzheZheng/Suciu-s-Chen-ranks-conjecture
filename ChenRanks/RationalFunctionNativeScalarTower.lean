import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Algebra.Tower

/-!
# Native rational-function scalar compatibility

An actual algebra homomorphism supplies the scalar tower for its induced
action. The library construction proves this from the algebra-map square
using actual scalar multiplication, multiplicativity and the homomorphism's
scalar compatibility.
-/

noncomputable section

namespace ChenRanks

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

/-- An actual rational-function algebra homomorphism supplies the native
scalar tower for its actual induced field action. -/
theorem nativeRatFuncAlgHom_scalarTower (g : RatFunc k →ₐ[k] L) :
    letI : Algebra (RatFunc k) L := g.toRingHom.toAlgebra
    letI : SMul (RatFunc k) L := g.toRingHom.toAlgebra.toSMul
    letI : Module (RatFunc k) L :=
      @Algebra.toModule (RatFunc k) L
        (inferInstanceAs (CommSemiring (RatFunc k))) (inferInstanceAs (Semiring L))
        g.toRingHom.toAlgebra
    IsScalarTower k (RatFunc k) L := by
  letI : Algebra (RatFunc k) L := g.toRingHom.toAlgebra
  letI : SMul (RatFunc k) L := g.toRingHom.toAlgebra.toSMul
  letI : Module (RatFunc k) L :=
    @Algebra.toModule (RatFunc k) L
      (inferInstanceAs (CommSemiring (RatFunc k))) (inferInstanceAs (Semiring L))
      g.toRingHom.toAlgebra
  exact IsScalarTower.of_algHom g

end ChenRanks
