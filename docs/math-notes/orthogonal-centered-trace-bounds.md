# Genuine expected centered single-Haar trace decay

Published milestones on `feat/orthogonal-trace-words`:

- `db82bf8`: actual cyclic row-code inverse and row-network transfer,
  `OrthogonalPairingRowTransfer.lean`.
- `c5b7a52`: genuine finite no-fixed-cycle orbit count,
  `OrthogonalPermutationCycleBound.lean`.
- `4d492a6`: actual centered contraction bound, uniform expected trace
  reciprocal decay and limit zero, `OrthogonalCenteredTraceBounds.lean`.

All modules are in `FreeProbability/RandomMatrix`; older sources are unchanged.

## Exact actual row and cycle-count prerequisites

`traceRowEdgeCode` is the actual site equivalence with endpoints
`right(k)` and `left(finRotate r k)`. Its inverse and both endpoint formulas
are proved. `traceRowNetwork_eq_pairingNetwork` identifies the EXISTING true
row network with this paired network, preserving arbitrary complex scalar
values; `traceRowNetwork_norm_le` supplies its genuine raw-loop power bound.

For any finite permutation with no fixed sites,
`permutationOrbit_length_ge_two` shows each ALL-orbit contains its seed and
its distinct image. `twice_permutationOrbit_card_le` consequently proves
`2 card(SameCycle quotient)≤card(sites)` by actual orbit-fiber exhaustion.
Singleton cycles are explicitly considered and excluded by the actual
no-fixed-site hypothesis, rather than discarded from an indexing structure.
The empty type is included.

## Kernel-verified expected trace result

For positive word length `r`, actual centered complex deterministic factors
`A_k,B_k`, and Haar-distributed real orthogonal `U`, the genuine expectation
of the normalized cyclic trace

```
N^-1 Tr(∏ordered k Uℂ A_k Uℂᵀ B_k)
```

satisfies, eventually in dimension `N`,

```
‖traceWordMoment(A,B)‖ ≤ C_r/N (∏k ‖toEuclideanCLM(A_k)‖)
                              (∏k ‖toEuclideanCLM(B_k)‖),
C_r = M^2 (r M^r + 2 M^(r+1)),  M=card(OrdinaryPairing r).
```

The theorem `eventually_centered_traceWordMoment_norm_le` quantifies ALL
complex deterministic factors after one eventual dimension threshold.
Its only matrix hypotheses are that EVERY `A_k` and `B_k` has zero ordinary
trace. The threshold depends only on `r`, through already proved actual
Weingarten bounds; it does not depend on the matrices.

`eventually_centered_traceWordMoment_uniform_bound` adds a genuine common
bound `K≥0` on every literal Euclidean operator norm and concludes the
explicit bound `C_r K^(2*r)/N`. `tendsto_centered_traceWordMoment` then proves
that these actual expected traces tend to zero for dimension-dependent
uniformly operator-bounded centered deterministic families.

Positive length is explicit. The empty word is not incorrectly asserted to
have vanishing expectation. All these expectations are actual Bochner
integrals against normalized compact orthogonal Haar; no desired moment,
trace formula, cycle estimate or vanishing limit is a premise.

## Actual cancellation and dimension counting

`centered_pairingNetwork_nonzero_loop_bound` proves that a nonzero actual
centered paired network has no fixed singleton selected cycle: an actual
singleton would contribute the genuine zero matrix trace. Thus its loop
count is at most half the deterministic edge count.

For each actual trace-word pairing contraction, a zero row or column network
kills the contraction. Otherwise both loop counts satisfy this genuine
bound and their sum is at most `r`. The sharp paired-network operator norms
and the actual `N^-1` normalization give
`centered_tracePairingContraction_norm_le`: contraction size at most
`N^(r-1)` times the product of ALL matrix operator norms.

The actual Weingarten weights are bounded by a degree constant times
`N^-r` (the already proved stronger distance factor is at most one).
Multiplying true weights by true contractions gives `1/N` per pairing term;
summing the finite double pairing index produces `C_r`. No noncrossing
geodesic classification is needed for this ALL-centered single-Haar result.

## Verification and failed engineering approaches

Focused builds passed without warnings at the three source checkpoints
(3036, 3028, and 3041 jobs). The row/cycle prerequisites' seven declarations
and the centered module's six public definitions/theorems were transitively
audited with only `propext`, `Classical.choice`, and `Quot.sound`.
Source integrity, staged whitespace checks and diff reviews passed. Every
source commit was pushed immediately, separately.

The initial row-code inverse simplifier unfolded cyclic rotation and its
inverse into finite arithmetic, leaving inconvenient subtraction goals;
retaining the genuine equivalence applications allowed exact cancellation.
The cardinality sum theorem takes implicit arguments in this pinned version.
A scalar inverse-power proof was closed by definitional equality after
extracting positive word length as a successor; no added premise was needed.
All intended statements were preserved.

## Precise remaining Goal 9 scope

This is a genuine SINGLE-Haar expected centered cyclic trace theorem, not a
full almost-sure joint asymptotic-freeness assertion for arbitrary independent
Haar conjugates. A multiple-trace exact formula and centered cycle count are
next dependencies for an actual second-moment `O(N^-2)` bound. Variance,
probabilistic realizations, concentration or summability/Borel-Cantelli must
be proved before almost-sure conclusions. Independent Haar colors need real
product Haar integration and color-respecting contractions; arbitrary
alternating words must be matched to the intended family interface. Marginal
law limits and their relation to the abstract free limit remain separate
requirements where needed. Low-dimensional pseudoinverse integration also
remains outside this stable-range asymptotic theorem.
