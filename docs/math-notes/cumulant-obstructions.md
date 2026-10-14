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

## Boxed multiplicative cumulants

The missing precise combinatorial statement is:

For `q ≤ p.kreweras`, the interleaving of `p` and `q` joined with the interval
partition of adjacent original/complementary pairs is top if and only if
`q = p.kreweras`.

Combining this statement with the verified generic interval-product formula,
mixed-block vanishing, and contribution factorization would prove the boxed
convolution formula for actual free product cumulants.

Maximal compatibility alone does not prove the missing statement. The actual
complementary block count is now proved:
`card_blocks_add_kreweras p hn` gives `|p| + |K(p)| = n + 1` for `n > 0`.
At `n = 0` both block families are empty; the tree count does not apply.

The proof uses exact complement deletion identities. An adjacent original chord
forces a complementary singleton; `kreweras_of_adjacent` transports the whole
complement through deletion. A noninitial original singleton gives a duplicated
complementary position via `kreweras_of_singleton_succ`. Every partition on at
least two positions has one of these two reductions, so a cyclic boundary case
is unnecessary for the count.

Remaining obligations are genuine connectivity of the bipartite block-incidence
graph, and the implication from the alternating adjacent-pair top join to raw
incidence connectivity. A strict complementary refinement has more blocks and
cannot be connected with only `n` index edges. Establishing this reasoning in
Lean still requires the relevant graph/setoid transport. Rotation and the order
anti-isomorphism remain separate unproved identities. No conditional substitute
is counted as the boxed formula.

## Multiplicative Möbius interval factors

The actual finite noncrossing Möbius function and all-partition inversion are
proved in `NoncrossingMobius`. The lower refinement interval is order-isomorphic
to the product of the noncrossing lattices on its actual blocks.

Mathlib's incidence-algebra implementation supplies the binary-product Möbius
identity `mu_prod_mu`, but its source lists the general Pi identity as a TODO.
It also lacks a ready order-isomorphism invariance theorem. Before the desired
blockwise Möbius factorization can be reused directly, prove these two general
incidence-algebra dependencies or supply equivalent uniqueness arguments.
Closed Catalan coefficients remain a further mathematical obligation.

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
