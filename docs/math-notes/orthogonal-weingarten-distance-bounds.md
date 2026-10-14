# Sharp ordinary-distance bounds for actual Weingarten entries

Verified source milestone `46b45bd`:
`FreeProbability/RandomMatrix/OrthogonalWeingartenDistanceBounds.lean`.
Depends on genuine pairing metric `e844941` and actual inverse uniform bound
`406b97a`; all earlier sources remain unchanged.

## Exact verified scope

Let `M=card(OrdinaryPairing r)` and let `d(p,q)` be the genuine raw pairing
join distance. For each fixed half-degree `r`, eventually in `N`,
simultaneously for ALL intrinsic ordinary pairings `p,q`,

```
|N^r G_N^{-1}(p,q)| ≤ (r M^r + 2 M^(r+1)) (1/N)^d(p,q).
```

`G_N` is the actual Gram matrix and its inverse is the literal nonsingular
matrix inverse. Crossing pairings are included. The constant is explicit;
the dimension threshold is existential through the already proved leading
limits. No asymptotic bound or inverse expansion is supplied as a premise.
The off-diagonal exponent is the full genuine distance, rather than merely
one whenever pairings differ. No optimality of the constant is claimed.

Public declarations in `FreeProbability.Orthogonal`:

- `normalizedPairingGram_eq_distance_power`: in every nonzero dimension,
  the normalized Gram entry is exactly `(1/N)^d(p,q)`.
- `ordinaryPairing_card_pos`: at least one intrinsic pairing exists in every
  half-degree.
- `rescaledWeingartenWeight_zero`: in half-degree zero, every rescaled
  inverse entry is EXACTLY one, for ALL dimensions including zero.
- `eventually_rescaledWeingartenWeight_distance_bound`: the displayed sharp
  distance-sensitive uniform bound.

## Finite proof rather than an infinite-series premise

Write `A=N^{-r}G`, `R=N^r G^{-1}`, `E=I-A`, and `x=1/N`. Genuine inverse
identities give `RA=I`. Elementary finite induction then proves, for every
natural `k`,

```
R = Σ(j<k) E^j + R E^k.
```

The genuine distance triangle bounds the entries of each finite power:
`|(E^k)(p,q)| ≤ M^k x^d(p,q)`. Independently, the reciprocal-dimension bound
on every error entry gives the crude estimate
`|(E^k)(p,q)| ≤ M^k x^k`. With `k=r`, the first bound controls the finite
sum and the second controls the remainder using the actual eventual
uniform bound `|R(p,q)|≤2`. Since `d(p,q)≤r`, the remainder has at least the
required power of reciprocal dimension. This also works for `r=0`; the
separate exact scalar theorem records the stronger degenerate case.
No matrix norm convention or infinite path summability enters the proof.

## Verification and proof engineering

Focused compilation passed without warnings (3026 jobs). All four public
results' transitive dependency audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. Source-integrity and whitespace checks
passed, staged source was reviewed, and the source commit was pushed
immediately.

The initial power induction fixed endpoint pairings too early; generalizing
the endpoints gave the required induction hypothesis. Rewriting the inverse
expansion induction hypothesis everywhere also rewrote the inverse factor
on the right; a directional calculation avoided that unwanted substitution.
For evaluating finite matrix sums, the actual `Matrix.sum_apply` theorem
resolved a dependent/implicit-transparency issue with generic function-sum
rewrites. A degree-zero simplification was ordered before substituting equal
pairing endpoints so that its loop-count equality retained the right shape.
None of these repairs weakened the intended statement.

## Remaining mathematical frontier

This closes the inverse-distance rate dependency from the entry-moment
notes. Actual normalized trace-word integration, cycle/contraction power
counts, norm bounds for deterministic matrix contractions, and centered
leading-term cancellation remain unproved here. In particular the bound
alone is not a proof of asymptotic freeness. Product Haar/color-respecting
expansions, fluctuations, concentration, almost-sure convergence, and the
low-dimensional invariant spanning/pseudoinverse regime remain separate
obligations.
