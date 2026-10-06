import ChenRanks.KoszulHomogeneousAnnihilator
import ChenRanks.KoszulGradedFunctoriality
import ChenRanks.KoszulResonanceSupport
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

/-!
# Genuine projective evaluation points and the actual annihilator

For a vector `e`, the actual symmetric-algebra map on its evaluation
functional maps the dual generator space to a one-dimensional generator
space. Its genuine homogeneous kernel is prime. If `e` is nonzero, an
actual functional evaluating to one proves that this prime is relevant,
and hence defines a native `ProjectiveSpectrum` point.

On each actual homogeneous piece in the target, evaluation at one is
proved injective from the genuine one-variable homogeneous dimension and
explicit actual preimages. The proved homogeneity of the original module's
actual annihilator therefore identifies its vanishing at the affine
evaluation with its containment in the true homogeneous line kernel.

The final statement concerns the native projective zero locus at these
actual vector-line points. It is not a scheme reducedness theorem, an
identification of all projective points, or an equality of ideals.
-/

noncomputable section

open scoped BigOperators DirectSum

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]

/-- The actual basis of the genuine one-dimensional generator space. -/
def singleCoefficientBasis : _root_.Module.Basis Unit k k :=
  _root_.Module.Basis.singleton Unit k

/-- Actual evaluation at one in the genuine one-variable symmetric algebra. -/
def lineEvaluationOne : S k k →ₐ[k] k := pointEvaluation k k (LinearMap.id : k →ₗ[k] k)

/-- Powers of the actual generator have their actual polynomial degree. -/
theorem singleCoefficient_generator_pow_mem (n : ℕ) :
    (SymmetricAlgebra.ι k k (1 : k)) ^ n ∈
      homogeneousS k k (singleCoefficientBasis k) n := by
  induction n with
  | zero => simpa only [pow_zero] using homogeneousS_one k k (singleCoefficientBasis k)
  | succ n hn =>
    rw [pow_succ]
    exact homogeneousS_mul k k (singleCoefficientBasis k) hn
      (homogeneousS_ι k k (singleCoefficientBasis k) (1 : k))

/-- The genuine evaluation map restricted to an actual homogeneous piece. -/
def lineDegreeEvaluation (n : ℕ) :
    homogeneousS k k (singleCoefficientBasis k) n →ₗ[k] k :=
  (lineEvaluationOne k).toLinearMap.comp
    (homogeneousS k k (singleCoefficientBasis k) n).subtype

/-- Explicit actual multiples of the actual generator power evaluate to
arbitrary field elements on every actual homogeneous piece. -/
theorem lineDegreeEvaluation_surjective (n : ℕ) :
    Function.Surjective (lineDegreeEvaluation k n) := by
  intro c
  refine ⟨⟨c • (SymmetricAlgebra.ι k k (1 : k)) ^ n,
    (homogeneousS k k (singleCoefficientBasis k) n).smul_mem c
      (singleCoefficient_generator_pow_mem k n)⟩, ?_⟩
  change lineEvaluationOne k (c • (SymmetricAlgebra.ι k k (1 : k)) ^ n) = c
  simp [lineEvaluationOne]

/-- Genuine one-variable homogeneous pieces have dimension one. Hence
their actual evaluation at one is injective, by the proved surjectivity
and actual equal finite dimensions. -/
theorem lineDegreeEvaluation_injective (n : ℕ) :
    Function.Injective (lineDegreeEvaluation k n) := by
  have hdim : _root_.Module.finrank k (homogeneousS k k (singleCoefficientBasis k) n) =
      _root_.Module.finrank k k := by
    rw [homogeneousS_finrank k k (singleCoefficientBasis k) n]
    simp
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr
    (lineDegreeEvaluation_surjective k n)

variable (E : Type*) [AddCommGroup E] [_root_.Module k E]
variable {ι : Type*} [Fintype ι]
  (b : _root_.Module.Basis ι k (_root_.Module.Dual k E))

/-- The genuine symmetric-algebra map induced by evaluation on the vector. -/
def lineSymmetricMap (e : E) : S k (_root_.Module.Dual k E) →ₐ[k] S k k :=
  symmetricMap k (_root_.Module.Dual k E) k (pointOfVector k E e)

/-- The actual line map preserves the actual homogeneous pieces. -/
def lineGradedMap (e : E) :
    homogeneousS k (_root_.Module.Dual k E) b →+*ᵍ
      homogeneousS k k (singleCoefficientBasis k) where
  toRingHom := (lineSymmetricMap k E e).toRingHom
  map_mem := fun {n} {s} hs ↦
    symmetricMap_homogeneous k (_root_.Module.Dual k E) k b
      (singleCoefficientBasis k) (pointOfVector k E e) n s hs

/-- The true homogeneous ideal of the actual vector line is the genuine
kernel of its actual graded symmetric-algebra map. -/
def lineHomogeneousKernel (e : E) : HomogeneousIdeal (homogeneousS k (_root_.Module.Dual k E) b) :=
  (⊥ : HomogeneousIdeal (homogeneousS k k (singleCoefficientBasis k))).comap
    (lineGradedMap k E b e)

omit [Fintype ι] in
@[simp] theorem lineHomogeneousKernel_toIdeal (e : E) :
    (lineHomogeneousKernel k E b e).toIdeal = RingHom.ker (lineSymmetricMap k E e).toRingHom := rfl

omit [Fintype ι] in
theorem mem_lineHomogeneousKernel (e : E) (s : S k (_root_.Module.Dual k E)) :
    s ∈ lineHomogeneousKernel k E b e ↔ lineSymmetricMap k E e s = 0 := by
  change s ∈ (lineHomogeneousKernel k E b e).toIdeal ↔ _
  rw [lineHomogeneousKernel_toIdeal, RingHom.mem_ker]
  rfl

instance lineHomogeneousKernel_isPrime (e : E) :
    (lineHomogeneousKernel k E b e).toIdeal.IsPrime := by
  rw [lineHomogeneousKernel_toIdeal]
  exact RingHom.ker_isPrime (lineSymmetricMap k E e).toRingHom

/-- Composing actual line evaluation at one with the actual line map
recovers the original affine evaluation, proved on genuine generators. -/
theorem lineEvaluationOne_comp_lineSymmetricMap (e : E) :
    (lineEvaluationOne k).comp (lineSymmetricMap k E e) =
      pointEvaluation k (_root_.Module.Dual k E) (pointOfVector k E e) := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro φ
  simp [lineSymmetricMap, lineEvaluationOne]

omit [Fintype ι] in
/-- The genuine line ideal is contained in the genuine affine evaluation
ideal by the actual composition identity. -/
theorem lineHomogeneousKernel_le_pointEvaluationKernel (e : E) :
    (lineHomogeneousKernel k E b e).toIdeal ≤
      pointEvaluationKernel k (_root_.Module.Dual k E) (pointOfVector k E e) := by
  intro s hs
  change pointEvaluation k (_root_.Module.Dual k E) (pointOfVector k E e) s = 0
  have hz := (mem_lineHomogeneousKernel k E b e s).mp hs
  have hc := DFunLike.congr_fun (lineEvaluationOne_comp_lineSymmetricMap k E e) s
  change lineEvaluationOne k (lineSymmetricMap k E e s) =
    pointEvaluation k (_root_.Module.Dual k E) (pointOfVector k E e) s at hc
  rw [hz, map_zero] at hc
  exact hc.symm

variable (K : Submodule k (⋀[k]^2 (_root_.Module.Dual k E)))

/-- The actual annihilator vanishes at the affine evaluation precisely
when it lies in the genuine homogeneous line ideal. The reverse direction
uses its proved actual homogeneity and actual injectivity in each true
one-variable homogeneous piece. -/
theorem annihilator_lineKernel_iff_pointEvaluationKernel (e : E) :
    _root_.Module.annihilator (S k (_root_.Module.Dual k E))
        (Module k (_root_.Module.Dual k E) K) ≤ (lineHomogeneousKernel k E b e).toIdeal ↔
      _root_.Module.annihilator (S k (_root_.Module.Dual k E))
          (Module k (_root_.Module.Dual k E) K) ≤
        pointEvaluationKernel k (_root_.Module.Dual k E) (pointOfVector k E e) := by
  constructor
  · exact fun h ↦ h.trans (lineHomogeneousKernel_le_pointEvaluationKernel k E b e)
  · intro h s hs
    apply (mem_lineHomogeneousKernel k E b e s).mpr
    have hpieces : ∀ n : ℕ,
        lineSymmetricMap k E e (homogeneousProjection k (_root_.Module.Dual k E) b n s) = 0 := by
      intro n
      let t : homogeneousS k k (singleCoefficientBasis k) n :=
        ⟨lineSymmetricMap k E e (homogeneousProjection k (_root_.Module.Dual k E) b n s),
          (lineGradedMap k E b e).map_mem
            (homogeneousProjection_mem k (_root_.Module.Dual k E) b n s)⟩
      have heval := h (homogeneousProjection_mem_annihilator k (_root_.Module.Dual k E)
        b K s n hs)
      change pointEvaluation k (_root_.Module.Dual k E) (pointOfVector k E e)
        (homogeneousProjection k (_root_.Module.Dual k E) b n s) = 0 at heval
      have ht : lineDegreeEvaluation k n t = 0 := by
        change lineEvaluationOne k (lineSymmetricMap k E e
          (homogeneousProjection k (_root_.Module.Dual k E) b n s)) = 0
        have hc := DFunLike.congr_fun (lineEvaluationOne_comp_lineSymmetricMap k E e)
          (homogeneousProjection k (_root_.Module.Dual k E) b n s)
        exact hc.trans heval
      have hz : t = 0 := lineDegreeEvaluation_injective k n (by simpa only [map_zero] using ht)
      simpa only [ZeroMemClass.coe_zero] using congrArg Subtype.val hz
    rw [← sum_homogeneousProjection k (_root_.Module.Dual k E) b s, map_sum]
    exact Finset.sum_eq_zero (fun n _ ↦ hpieces n)

variable [FiniteDimensional k E]

/-- A genuine nonzero vector line gives a relevant homogeneous prime.
An actual functional evaluating to one provides a degree-one element of
the irrelevant ideal whose genuine image in the line algebra is nonzero. -/
theorem lineHomogeneousKernel_relevant {e : E} (he : e ≠ 0) :
    ¬ HomogeneousIdeal.irrelevant (homogeneousS k (_root_.Module.Dual k E) b) ≤
      lineHomogeneousKernel k E b e := by
  intro h
  obtain ⟨φ, hφ⟩ := exists_point_normalized_vector k (_root_.Module.Dual k E)
    (pointOfVector k E e) (pointOfVector_ne_zero k E he)
  have hmem : SymmetricAlgebra.ι k (_root_.Module.Dual k E) φ ∈
      HomogeneousIdeal.irrelevant (homogeneousS k (_root_.Module.Dual k E) b) :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide)
      (homogeneousS_ι k (_root_.Module.Dual k E) b φ)
  have hz := (mem_lineHomogeneousKernel k E b e _).mp (h hmem)
  have hc := congrArg (lineEvaluationOne k) hz
  simp [lineSymmetricMap, lineEvaluationOne, hφ] at hc

/-- The genuine projective point of an actual nonzero vector line. Its
prime is homogeneous and relevant, rather than the affine maximal ideal. -/
def vectorProjectivePoint (e : E) (he : e ≠ 0) :
    ProjectiveSpectrum (homogeneousS k (_root_.Module.Dual k E) b) where
  asHomogeneousIdeal := lineHomogeneousKernel k E b e
  isPrime := inferInstance
  not_irrelevant_le := lineHomogeneousKernel_relevant k E b he

variable [CharZero k]

/-- At the native projective point of a genuine nonzero vector, the
canonical original-module annihilator zero locus detects the genuine
resonance point set. No projective scheme reducedness is asserted. -/
theorem vectorProjectivePoint_mem_annihilatorZeroLocus
    (I : Submodule k (⋀[k]^2 E)) {e : E} (he : e ≠ 0) :
    vectorProjectivePoint k E b e he ∈ ProjectiveSpectrum.zeroLocus
        (homogeneousS k (_root_.Module.Dual k E) b)
        (_root_.Module.annihilator (S k (_root_.Module.Dual k E))
          (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :
          Set (S k (_root_.Module.Dual k E))) ↔
      e ∈ ChenRanks.Resonance.resonance I := by
  change _root_.Module.annihilator (S k (_root_.Module.Dual k E))
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) ≤
    (lineHomogeneousKernel k E b e).toIdeal ↔ _
  rw [annihilator_lineKernel_iff_pointEvaluationKernel]
  exact annihilator_point_iff_resonance k E I he

end ChenRanks.Koszul
