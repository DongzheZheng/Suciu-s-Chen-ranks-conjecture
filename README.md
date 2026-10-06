# Chen Ranks and Resonance: Lean Verification

A Lean 4 formalization of the effective Chen-rank formula for finite complex hyperplane arrangements. Version 1.0 verifies the passage from geometric separation to the rational Chen ranks of the complement's fundamental group, with explicit stable ranges.

**The sole external mathematical input is the effective canonical Koszul decomposition of Aprodu–Farkas–Raicu–Suciu (AFRS).** It is retained as the explicit theorem parameter `hAFRS`. The arrangement separation theorem and all group, cohomology, finiteness, component-counting, and deconing comparisons are proved within the formalization.

## Main results

Let $\mathcal A$ consist of $N$ distinct affine hyperplanes in $\mathbb C^d$, let $M(\mathcal A)$ be its complement, choose $x\in M(\mathcal A)$, and set $G=\pi_1(M(\mathcal A),x)$. Write $\theta_q(G)$ for the $q$th rational Chen rank, and $h_m(\mathcal A)$ for the number of irreducible projective resonance components whose affine cones have vector-space dimension $m$. Then

$$
\theta_q(G)=(q-1)\sum_{m=2}^{N}h_m(\mathcal A)\binom{m+q-2}{q}
$$

holds in the following ranges:

| Arrangement | Verified range | Public theorem |
|---|---|---|
| Affine | $q\ge\max\{2,N-1\}$ | `chenRanks_affine` |
| Central | $q\ge\max\{2,N-2\}$ | `chenRanks_central` |

The public declarations are in [`ChenRanks/ChenRankFormula.lean`](ChenRanks/ChenRankFormula.lean), in the namespace `ChenRanks.AffineArrangement`. Their conclusions use the rationalization of the lower-central quotient of the complement's maximal metabelian quotient and the intrinsic resonance-component counts. Empty arrangements and the small-dimensional cases are included.

```lean
import ChenRanks

#check ChenRanks.AffineArrangement.chenRanks_affine
#check ChenRanks.AffineArrangement.chenRanks_central
```

See [Mathematical scope](docs/MathematicalScope.md) for the precise objects, the external input, and the degree conventions.

## Build and audit

The project pins Lean **4.29.0** and Mathlib commit
`8a178386ffc0f5fef0b77738bb5449d50efeea95`.

With the pinned Lean toolchain available, run:

```sh
lake exe cache get
lake build
python3 scripts/verify.py --skip-build
```

The verification script checks the release source manifest and pinned dependencies, runs all three audit modules, and regenerates the declaration output and certificate. It checks 14 transitive axiom queries, including both public theorems.

Source integrity can also be checked without invoking Lean:

```sh
python3 scripts/verify.py --check-sources
```

The final declarations have been checked by the Lean kernel. Their transitive axiom audits report only the standard foundational constants `propext`, `Classical.choice`, and `Quot.sound`. The AFRS decomposition appears as the explicit parameter `hAFRS` in the theorem types.

The [verification certificate](verification/Certificate.json) records the input and the checked result, and the [source manifest](verification/SourceManifest.json) identifies the release sources by SHA-256.

## References

- [Associated manuscript](https://doi.org/10.13140/RG.2.2.31932.40329).
- M. Aprodu, G. Farkas, C. Raicu, and A. I. Suciu, [*The effective Chen Ranks Conjecture*](https://arxiv.org/html/2512.10160v1), Theorem 1.1 and its proof, including equations (1.7) and (7.9). These establish the effective canonical decomposition used as the single external input.
