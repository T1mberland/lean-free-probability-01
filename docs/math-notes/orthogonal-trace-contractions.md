# Actual cyclic matrix-unit contractions and two network sums

Verified source `15515f0` on `feat/orthogonal-trace-words`:
`FreeProbability/RandomMatrix/OrthogonalTraceContractions.lean`.
Depends on actual trace-word expansion `6349c65`. Earlier sources are unchanged.

## Proven scope

For arbitrary complex deterministic `A_k,B_k` and positive degree `r`, the
actual normalized trace of the ordered deterministic code factors satisfies

```
coefficient(s) = N^-1 (∏k A_k(b_k,d_k)) (∏k B_k(c_k,a_next(k))).
```

`next` is the actual finite cyclic rotation `finRotate r`, so the last
matrix entry returns to the first site. The theorem retains the actual
ordered matrix product on its left; a cyclic-entry identity is not assumed.
It holds also for empty matrix dimension.

The exact code equivalence identifies a function of four indices per word
position with independently chosen row and column functions on `Fin(2*r)`.
Define the row network as the actual finite sum

```
Row(B,p) = Σi (∏k B_k(i(right k),i(left(next k)))) δp(i),
```

and the column network as

```
Col(A,q) = Σj (∏k A_k(j(left k),j(right k))) δq(j).
```

The genuine deterministic pairing contraction from the trace-word formula
then factors exactly:

```
C_pq(A,B) = N^-1 Row(B,p) Col(A,q).
```

All ordinary pairings, crossing included, are allowed; no additional cycle,
norm, trace, positivity or centering hypotheses occur. These are literal
finite network sums, not names for presumed products of cycle traces.

Degree zero is handled separately: the actual contraction is `N^-1 N`, the
normalized trace of the identity. Applying the positive-degree network
factorization to zero degree would incorrectly lose this dimension factor;
the theorem deliberately requires `0<r` and the separate exact theorem
preserves the genuine empty-word convention, including `N=0`.

Public declarations in `FreeProbability.Orthogonal`:

- `traceContractionCoefficient_eq_cyclic_entries`.
- `traceCodeEquiv`.
- `traceRowNetwork`, `traceColumnNetwork`.
- `tracePairingContraction_eq_network_product`.
- `tracePairingContraction_zero`.

## Proof and verification

The ordered product of genuine one-row matrices is evaluated entrywise by
induction, multiplying adjacent row entries. Summing its diagonal closes the
cyclic edge. Extracting the deterministic scalar factors yields the actual
coefficient formula. The explicit code equivalence and genuine independent
finite sums give the network factorization.

Focused compilation passed without warnings (3023 jobs). All three theorem
transitive audits contain only `propext`, `Classical.choice`, and `Quot.sound`;
the code equivalence uses only `propext` and `Quot.sound`. Source integrity,
staged whitespace checks and source review passed, and the source commit was
pushed immediately.

The product-entry induction initially fixed endpoints too early; generalizing
them gave the necessary hypothesis. Simplifying a `Fin.succ 0` to its numeral
left the equality-test instance with a mismatched dependent type under
implicit transparency. An explicitly typed `change` reconstructed the exact
same scalar finite sum before simplification. Code inverse projections were
exposed with exact equivalence identities instead of unfolding the entire
structure. Explicit finite-sum commutation aligned independent network
indices without changing the order of matrix factors. No mathematical
statement was weakened during these repairs.

## Next dependent milestone

Each network is a two-regular index graph formed by the pairing edges and
the deterministic matrix edges. The genuine decomposition into cycle traces
of ordered matrices and transposes, its component count, and Euclidean
operator-norm bounds remain to be proved. Those bounds must combine with the
already proved true Weingarten distance exponent; crude entrywise estimates
are insufficient to claim normalized trace asymptotic freeness. Centered
leading-cycle cancellation, independent Haar colors, fluctuations,
concentration and almost-sure convergence remain separate later obligations.
