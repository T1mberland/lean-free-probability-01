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

Maximal compatibility alone does not prove the missing statement. A suitable
route is to prove that the bipartite block-incidence graph of `p` and its actual
complement is a tree, or equivalently establish the relevant connectedness and
block count `|p| + |K(p)| = n + 1` for `n > 0`. (For `n = 0`, both
block counts are zero, so the tree count does not apply.) Dropping complementary refinement blocks must
then disconnect the pair grouping. Rotation/order anti-isomorphism and block
cardinality identities remain unproved. No conditional substitute is counted as
the boxed formula.

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

## Independent non-iid CLT extension

The iid free CLT is already proved over any `RCLike` field, including real and
complex scalars, with actual second moments and explicit pairing limits. The
next independent extension allows centered free triangular arrays without
identical marginal laws. Its hypotheses are convergence of the averaged second
moments and uniform bounds on each fixed higher-order marginal cumulant. The
normalization estimates then imply the semicircular cumulant shape and pairing
moment convergence. These are explicitly quantified hypotheses; no norm or
strong spectral convergence follows from this argument.
