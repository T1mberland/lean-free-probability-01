# Uniform errors for actual orthogonal Weingarten weights

Verified source milestone: `406b97a`,
`FreeProbability/RandomMatrix/OrthogonalWeingartenBounds.lean`.
This extends the genuine leading-limit milestone `2e93cc9` without changing
any earlier source.

## Proven scope

For each fixed half-degree `r`, simultaneously for every intrinsic ordinary
pairing `p,q`, the actual nonsingular inverse of the actual pairing Gram
matrix satisfies, eventually in the dimension `N`,

```
|N^r G_N^{-1}(p,q) - δ(p,q)| ≤ 2 card(OrdinaryPairing r) / N.
```

The quantifier order gives one dimension threshold for all entries. The
threshold is existential through the genuine previously proved limits; no
explicit threshold is claimed. The pairing index includes crossing pairings,
with orientation and block-numbering duplicates removed. The result includes
half-degree zero. It imposes no moment-formula or inverse premise.

Public declarations in `FreeProbability.Orthogonal`:

- `normalizedPairingGram_entry_error_le`: in every positive dimension,
  every normalized Gram entry differs from the identity by at most `1/N`.
- `eventually_rescaledWeingartenWeight_abs_le_two`: all actual rescaled
  inverse entries eventually have absolute value at most two.
- `rescaledWeingarten_mul_normalizedPairingGram`: the actual rescaled
  Weingarten matrix is a left inverse of the normalized Gram for `N≥r`,
  `N≠0`.
- `eventually_rescaledWeingartenWeight_error_le`: the displayed uniform
  reciprocal-dimension estimate.

## Proof and verification

The raw quotient-loop count is at most `r`, with equality exactly on the
pairing diagonal. Thus off-diagonal normalized Gram entries are powers of
`1/N` with strictly positive exponent. Finiteness of the pairing index and
the actual leading limits provide a simultaneous inverse-entry bound.
The genuine inverse identity gives `R-I = R(I-A)`. Entrywise finite-sum
estimates give the explicit constant, avoiding any ambiguity about matrix
norm choices.

The first elaboration attempt rewrote `r` directly while pairing arguments
had types depending on `r`; this produced an ill-typed rewrite motive. A
separate scalar reciprocal-power lemma with independent natural indices
resolved this issue without changing a mathematical statement.

Focused Lake compilation passed with exit zero and no warnings (3024 jobs).
All four public declarations' transitive dependency audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. The source-integrity guard and
diff whitespace check passed. The source commit was pushed immediately.

## Remaining obligations

This is an entrywise estimate for fixed degree, not asymptotic freeness or a
random-matrix convergence theorem. Loop-distance-dependent inverse bounds,
trace-word contraction and cancellation estimates, variance/concentration
and almost-sure modes remain separate mathematical obligations. The
low-dimensional (`N<r`) invariant spanning/pseudoinverse formula also remains
separate from this stable-range asymptotic development.
