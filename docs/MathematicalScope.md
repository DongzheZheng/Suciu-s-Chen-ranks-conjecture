# Mathematical Scope

Version 1.0 verifies the effective Chen-rank formula for every finite complex affine hyperplane arrangement, and its improved range for central arrangements, relative to one explicit AFRS decomposition input. This document specifies the mathematical statement and its representation in Lean.

## Arrangements and Chen ranks

An arrangement is a finite family of distinct hyperplanes

$$
\mathcal A=\{H_i\}_{i\in I},\qquad
H_i=\{z\in\mathbb C^d:\ell_i(z)=c_i\},
$$

where each $\ell_i$ is a nonzero complex linear functional. The finite label type is `ι`, and $N=|I|$ is `Fintype.card ι`. Distinctness is part of `ChenRanks.AffineArrangement`; repeated defining equations do not count as additional hyperplanes. No essentiality condition is imposed.

The complement is the topological subspace

$$
M(\mathcal A)=\mathbb C^d\setminus\bigcup_i H_i.
$$

For a basepoint $x\in M(\mathcal A)$, put $G=\pi_1(M(\mathcal A),x)$ and $G''=[G',G']$. With $\Gamma_1(H)=H$ and $\Gamma_{j+1}(H)=[H,\Gamma_j(H)]$, the rational Chen rank is

$$
\theta_q(G)=\dim_{\mathbb Q}\left(
\mathbb Q\otimes_{\mathbb Z}
\frac{\Gamma_q(G/G'')}{\Gamma_{q+1}(G/G'')}
\right).
$$

The underlying objects are defined in [`ArrangementObjects.lean`](../ChenRanks/ArrangementObjects.lean) and [`ChenObjects.lean`](../ChenRanks/ChenObjects.lean). The main conclusions retain `Module.rank` as a cardinal. Finite-dimensionality and the comparison with the corresponding natural-number dimension are proved internally.

## Resonance and component counts

Let $E=H^1(M(\mathcal A);\mathbb C)$, with its singular cup product. The first resonance variety is

$$
\mathcal R^1(\mathcal A)=\{0\}\cup
\{a\in E\setminus\{0\}:\exists b\notin\mathbb C a,\ a\smile b=0\}.
$$

The formalization constructs the projective resonance support from the annihilator of the associated Koszul module and compares it with this singular-cohomology resonance variety. The number $h_m(\mathcal A)$ counts its irreducible projective components whose linear affine cones have vector-space dimension $m$; equivalently, these projective components have dimension $m-1$. Thus $m$ in the formula denotes the cone dimension.

The Lean count is `A.singularProjectiveComponentDimensionCount m`, defined in [`ArrangementSingularProjectiveComponents.lean`](../ChenRanks/ArrangementSingularProjectiveComponents.lean). It is derived from the intrinsic projective components. The finiteness of the relevant family, the agreement with logarithmic coordinates, and the bounds $2\le m\le N$ are proved within the project. The finite numerical sum is defined in [`ArrangementChenRankSum.lean`](../ChenRanks/ArrangementChenRankSum.lean).

## The single external input

The input is the proposition

```lean
hAFRS : ChenRanks.Koszul.AFRSEffectiveCanonicalDecomposition
```

Its complete definition is in [`AFRSEffectiveCanonicalDecompositionInput.lean`](../ChenRanks/AFRSEffectiveCanonicalDecompositionInput.lean). It quantifies finite-dimensional complex vector spaces $E$ and quadratic subspaces $I\subseteq\bigwedge^2 E$.

A subspace $P\subseteq E$ is isotropic if $\bigwedge^2P\subseteq I$, and is maximal isotropic if it has no strictly larger isotropic extension. The separation condition required by the input is

$$
(P\wedge E)\cap I=\bigwedge^2P
$$

for every maximal isotropic $P$ with $\dim P\ge2$. Here $P\wedge E$ is the span of the mixed exterior products, and $\bigwedge^2P$ is understood through its natural inclusion into $\bigwedge^2E$.

For such data, let $I^\perp\subseteq\bigwedge^2E^\vee$ be the exterior annihilator. The restriction maps $E^\vee\to P^\vee$ induce the canonical homogeneous Koszul map

$$
\Phi_r:W_r(E^\vee,I^\perp)
\longrightarrow
\prod_{\substack{P\text{ maximal isotropic}\\\dim P\ge2}}
W_r(P^\vee,0).
$$

The input asserts that $\Phi_r$ is bijective when

$$
\dim E\ge3,\qquad r\ge\dim E-3.
$$

Here $W(V,K)$ is the Koszul module
$\ker\delta_1/\operatorname{im}(\delta_2|_{\operatorname{Sym}(V)\otimes K})$, with its usual shifted grading. The project constructs this module, its grading, and the canonical maps. The finite family of factors is also constructed from separation.

This input is the effective canonical decomposition supplied by [Aprodu–Farkas–Raicu–Suciu, *The effective Chen Ranks Conjecture*](https://arxiv.org/html/2512.10160v1), Theorem 1.1 and its proof, particularly equations (1.7) and (7.9). The cited proof establishes the canonical-map form used here. Version 1.0 accepts this statement as its sole literature input, represented by a theorem argument rather than an `axiom` declaration.

## Internal deductions and stable ranges

For the arrangement's quadratic cup data, the project proves the separation condition required by the input. It then proves the comparison between the original group Chen quotient and the corresponding Koszul homogeneous piece, together with its finite dimension and the component-dimension formula. Consequently the final affine theorem requires only an arrangement, a complement basepoint, a degree in the stated range, and `hAFRS`.

The code's lower-central index begins at zero: `lowerCentralPiece H k` represents $\Gamma_{k+1}(H)/\Gamma_{k+2}(H)$. The Chen degree $q$ therefore corresponds to

$$
k=q-1,\qquad r=q-2.
$$

For an affine arrangement, $\dim E=N$. The AFRS bound $r\ge N-3$, together with $q\ge2$, gives

$$
q\ge\max\{2,N-1\}.
$$

For a central arrangement, every $c_i=0$. In the nonempty case the proof constructs a decone with $N-1$ distinct hyperplanes, transports the Chen quotient and the resonance-component counts, and applies the affine result to that decone. This gives

$$
q\ge\max\{2,N-2\}.
$$

The choice of a deconing hyperplane is internal. The public central theorem does not require that choice or a nonemptiness assumption. Empty arrangements and the cases outside the input's ambient-dimension range are handled by internal proofs.

## Verified interface

The public theorems in [`ChenRankFormula.lean`](../ChenRanks/ChenRankFormula.lean) have the same conclusion:

$$
\theta_q(G)=(q-1)\sum_{m=2}^{N}
 h_m(\mathcal A)\binom{m+q-2}{q}.
$$

`chenRanks_affine` uses the affine range, and `chenRanks_central` uses the central range and the defining centrality condition. The supplied hypotheses contain no additional separation, finite-dimensionality, group-comparison, or component-counting assertions.

The verification script runs the two mathematical audit modules and [`Verification.lean`](../Verification.lean). Together they display the full AFRS proposition, the group-rank and component-count conclusions, and 14 transitive axiom queries. The only foundational constants reported for the final declarations are `propext`, `Classical.choice`, and `Quot.sound`. These audits check the conditional deductions; the explicit `hAFRS` argument remains the single external mathematical input.

The associated [manuscript](https://doi.org/10.13140/RG.2.2.31932.40329) is available separately. The repository contains the formalization and its verification records.
