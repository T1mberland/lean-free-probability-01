# Cumulant calculus: current mathematical obligations

## Verified generic interval products and Kreweras moments

`cumulant_intervalProducts_top` takes an independently supplied monotone
surjection `Fin n → Fin m`, with `m > 0`. Its left side is the actual sorted
product over each nonempty interval fiber. Its right side sums original
cumulant contributions over partitions whose join with the fiber partition is
top. Fusion plans are eliminated from the public statement.

`NoncrossingPartition.kreweras` is a constructed right complement. Equality of
membership in every chord interval `[u,v)` defines its classes. The theorem
`interleave_nonCrossing_iff` proves that an original/complementary alternating
partition is noncrossing exactly when the complementary partition refines the
constructed complement. Hence maximality is proved, not assumed.

`FreelyIndependent.expectation_prod_eq_kreweras_sum` and
`expectation_pow_mul_eq_kreweras_sum` prove actual mixed and product power
moments as cumulant–moment Kreweras sums. These are algebraic moment identities.
They do not prove an analytic S-transform identity or identify spectral support.

## Verified boxed multiplicative cumulants

The exact combinatorial statement is now proved:
`interleave_sup_pairInterval_eq_top_iff` says that, for `q ≤ p.kreweras`, the
interleaving of `p` and `q` joined with the adjacent original/complementary pair
partition is top exactly when `q = p.kreweras`.

The proof does not assume forest or connectivity hypotheses. Exact deletion
identities give the actual count `|p| + |K(p)| = n + 1` for `n > 0`, and the
actual join `p ∨ K(p) = top`. Raw joins with consecutive interval partitions are
already noncrossing. Collapsing interleaved adjacent pairs recovers the raw join
of the constituent partitions, so compatibility introduces no artificial closure
merges. A bipartite graph on actual blocks has at most `n` index edges; raw top
join implies genuine graph connectivity and hence at most `n + 1` vertices.
A proper complementary refinement has strictly more blocks than `K(p)`, which
contradicts this bound. The length-zero case is handled separately in the
combinatorial equivalence.

`FreelyIndependent.cumulant_prod_eq_kreweras_sum` consequently proves boxed
convolution for actual products of two free tuples, and
`cumulant_replicate_mul_eq_kreweras_sum` for every positive-order cumulant of
`a * b`. Positive order is necessary under the library's zero empty-cumulant
convention: the empty partition contribution equals one. No traciality,
positivity, or commutativity is assumed. Rotation and order anti-isomorphism
remain separate optional complement identities. Analytic S-transform
multiplicativity and spectral convolution realization remain open.

## Optional multiplicative Möbius interval extensions

The literal Goal 1 subtargets are covered by the verified cumulant calculus,
actual noncrossing combinatorics, full lattice inversion, generic interval product
identities, and actual boxed free-product formulas. The refinements in this
section are useful optional extensions, not blockers to those requested results.
Integration status remains the coordinator's responsibility.

The lower refinement interval is already order-isomorphic to the product of the
noncrossing lattices on its actual blocks. Two reusable incidence dependencies
are now proved: `incidence_mu_orderIso` gives finite-poset order-isomorphism
invariance over arbitrary coefficient rings; `incidence_mu_pi` gives the actual
Möbius function of a finite dependent product of finite posets as the coordinate
product over commutative coefficient rings. Combining these with the existing
block-refinement order isomorphism supplies the intended interval-factor route.
That final specialization and closed Catalan coefficients are optional further
extensions. Rotation/order anti-isomorphism of the complement is also optional
rather than a missing premise of the now-proved boxed formula.

## Verified quantified non-iid CLT extension

The iid free CLT is proved over any `RCLike` field, including real and complex
scalars, with actual second moments and explicit pairing limits. The independent
non-iid extension is now proved in `CumulantTriangularEstimates` and
`CumulantTriangularCLT`: centered free triangular arrays, convergence of their
averaged actual second moments, and uniform bounds on each fixed higher-order
marginal cumulant imply the semicircular cumulant shape and pairing moment
convergence. Source algebras may vary with the row. The norm estimate is
`||kappa_k(N^(-1/2) sum a_i)|| <= N * (sqrt N)^(-k) * C_k`.
These are explicit quantitative hypotheses, not an unconditional free Lindeberg
theorem. No norm or strong spectral convergence is claimed.
