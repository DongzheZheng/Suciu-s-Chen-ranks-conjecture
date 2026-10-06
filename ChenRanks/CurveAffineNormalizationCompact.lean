import ChenRanks.CurveAffineNormalization

/-! Quasi-compactness of the actual affine coefficient normalization is
the native compactness theorem for the actual prime spectrum. It does not
assert properness over the original field. -/

noncomputable section

namespace ChenRanks

universe u

variable (k L : Type u) [Field k] [Field L] [Algebra (RatFunc k) L]

/-- The actual affine normalization is quasi-compact, as its underlying
space is the actual prime spectrum of its actual integral-closure ring. -/
theorem curveAffineNormalization_compactSpace :
    CompactSpace (curveAffineNormalization k L) := by
  letI : CommRing (curveAffineNormalizationRing k L) :=
    curveAffineNormalizationRing_commRing k L
  change CompactSpace (PrimeSpectrum (curveAffineNormalizationRing k L))
  exact PrimeSpectrum.compactSpace

end ChenRanks
