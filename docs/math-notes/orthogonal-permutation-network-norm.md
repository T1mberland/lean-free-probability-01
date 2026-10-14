# Actual Euclidean operator-norm bounds for permutation networks

Verified source milestone `1038796` on `feat/orthogonal-trace-words`:
`FreeProbability/RandomMatrix/OrthogonalPermutationNetworkNorm.lean`.
Depends on actual cycle-trace identity `932ec1c`. Older sources are unchanged.

## Proven scope and explicit norm model

For arbitrary finite index `α`, actual permutation `σ`, complex deterministic
matrices with finite color dimension `n`, the genuine network satisfies

```
‖Network(σ,M)‖ ≤ card(n)^card(SameCycle quotient σ) ∏a ‖toEuclideanCLM(M_a)‖.
```

`permutationNetwork_norm_le` has literal continuous-linear-map operator norms
in its Lean statement. Internally the explicitly opened
`Matrix.Norms.L2Operator` scope identifies matrix multiplication with the
Euclidean Hilbert-space operator norm, via `Matrix.cstar_norm_def`.
The default entrywise matrix norm is not used for a product bound.

The result includes empty color dimensions and empty index sets. An empty
index gives the genuine bound `1≤0^0*1=1` when both are empty. Every actual
orbit has positive length; the ordered cycle bound therefore does not need
to assert norm one for an identity acting on a zero-dimensional space.

Public results in `FreeProbability.Orthogonal`:

- `trace_norm_le_card_mul_Euclidean_opNorm`: actual complex trace is at most
  dimension times the actual Euclidean operator norm.
- `trace_ordered_product_norm_le`: a genuine positive-length ordered cycle
  trace is at most dimension times the product of the operator norms.
- `permutationNetwork_norm_le`: the displayed whole-network bound.
- `permutationNetwork_eq_zero_of_fixed_trace_zero`: if an ACTUAL fixed point
  `a` of `σ` has `Tr(M_a)=0`, the genuine network is zero. No network
  cancellation premise is added.

The zero theorem identifies the actual orbit as a singleton, evaluates its
length-one ordered product, and uses that zero factor in the actual cycle
trace product. The norm theorem uses true unit-basis diagonal inner products,
Cauchy-Schwarz and the actual operator bound, then genuine product
submultiplicativity and exact label exhaustion across all orbit enumerations.

## Verification and engineering

Focused compilation passed without warnings (3031 jobs). All four public
results' transitive audits contain only `propext`, `Classical.choice`, and
`Quot.sound`. Source integrity, staged whitespace checks and source review
passed; the source commit was pushed immediately.

Initial elaboration fixes specified the complex scalar for an inner-product
bound and used the nonnegative real product inequality `prod_le_prod₀`.
A large definitional-equality search at the product-label transport was
resolved by isolating the generic commutative-monoid exhaustion identity
and applying an explicitly typed scalar congruence, without increasing
heartbeat limits. A fixed-point reflexivity proof was expressed without
referring to an endpoint variable eliminated by equality substitution.
No mathematical statement or norm choice changed during these repairs.

## Proposed centered pairing route, not yet a theorem

The original paired row/column networks still need actual oriented half-cycle
transfer to the generic permutation network and genuine deterministic-edge
label exhaustion. Once those are established, there is a useful route to
centered trace-word decay without classifying noncrossing geodesics:

If EVERY deterministic `A_j` and `B_j` has zero ordinary trace, a singleton
cycle in either actual network kills that network. If neither network has
such a singleton, every component consumes at least two of its `r` labels,
so the combined component count is at most `r`. This would bound the actual
normalized pairing contraction by `N^(r-1)` times the product of Euclidean
operator norms. Combined with the proved true Weingarten bound
`O(N^(-r-d(p,q)))`, the fixed finite pairing sum would give an actual expected
single-Haar centered cyclic trace bound `O(1/N)`.

These counting, orientation and contraction-transfer statements remain
unproved here. Single-Haar expectation decay would not by itself establish
joint freeness of an arbitrary independent Haar family. Multiple traces,
color-respecting independent product Haar integrals and the analogous cycle
count are further prerequisites for a proposed second-moment `O(N^-2)`
bound; summability/Borel-Cantelli and the precise random variables and
convergence assumptions are required before any almost-sure assertion.
No expected, variance or almost-sure asymptotic-freeness theorem is claimed
by this norm milestone. Low-dimensional pseudoinverse integration also
remains separate.
