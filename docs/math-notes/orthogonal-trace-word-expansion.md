# Actual complex orthogonal Haar trace-word expansion

Verified source milestone `6349c65` on `feat/orthogonal-trace-words`:
`FreeProbability/RandomMatrix/OrthogonalTraceWordExpansion.lean`.
The branch depends on published asymptotic chain `b110052`; the exact formula
itself imports the actual stable integration milestone `e4b842f`.
All earlier sources remain unchanged.

## Exact intended interfaces and proved scope

For arbitrary complex deterministic square matrices `A_k,B_k`, the actual
word and its actual normalized Haar integral are

```
traceWord(A,B,U) = card(n)^(-1) Tr(∏ordered k (Uℂ A_k Uℂᵀ B_k)),
traceWordMoment(A,B) = ∫ traceWord(A,B,U) dHaar(U).
```

`U` belongs to the genuine real orthogonal group, and `complexMatrix` casts
its actual entries to complex numbers. Its transpose equals its adjoint,
proved as `complexMatrix_conjTranspose`. The matrix product is the ordered
product of `List.ofFn`, not a commutative finite product.

A code assigns `(a,b,c,d)` to every position `k`. Define the deterministic
matrix-unit factor

```
D_k(code) = A_k(b,d) • (single(a,c,1) B_k).
```

`traceContractionCoefficient` is the actual normalized trace of the ordered
product of these factors. `traceSites` orders the Haar sites as all first U
entries followed by all second U entries; `traceRows` selects `(a,c)` and
`traceCols` selects `(b,d)`. This is an actual equivalence with `Fin(2*r)`.
The deterministic contraction `tracePairingContraction A B p q` sums these
coefficients against both ordinary paired deltas.

Public proved mathematical results in `FreeProbability.Orthogonal`:

- `traceWord_eq_entryMonomial_sum`: exact pointwise expansion, all dimensions
  and degrees, with actual real-entry monomials cast to complex values.
- `traceWordMoment_eq_entryMoment_sum`: the exact expansion after actual
  Bochner integration.
- `integrable_traceWord`: integrability established from actual compact Haar
  and continuous entry monomials.
- `traceWordMoment_eq_weingarten_contractions`: for `r≤card(n)`,

```
traceWordMoment(A,B) = Σp,q (G_n^(-1)(p,q) : ℂ) C_pq(A,B).
```

The inverse is literal nonsingular matrix inversion, and ALL ordinary
pairings including crossings are used. Neither a trace formula, pairing
formula, projection range nor contraction identity is an extra premise.

The normalization is deliberately total: `card(n)^(-1)` is zero in empty
dimension. `traceWordMoment_zero` gives the empty-word moment as
`card(n)^(-1) card(n)`; `traceWordMoment_zero_of_card_pos` proves it is one
in positive dimension. `traceWordMoment_of_card_zero` proves zero at EVERY
degree in dimension zero. Thus no accidental zero-dimensional normalization
or empty-product convention is hidden in the expansion.

## Proof and checks

Expand the actual matrix block `U A Uᵀ B` as a sum of matrix units weighted
by two actual Haar entries. A proved noncommutative ordered-product-of-sums
identity gives the code sum. Scalar factors commute with matrix multiplication,
so the paired Haar entries combine into the actual `2*r`-entry monomial.
Actual continuity on the compact group gives integrability, finite-integral
linearity and real-to-complex integral transport yield the entry moments,
and the already proved stable Weingarten formula gives the contraction sum.

Focused build passed without warnings (3022 jobs). All eight public theorem
transitive audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
Source-integrity and staged whitespace checks passed, the source diff was
reviewed, and the new branch was immediately pushed with upstream tracking.

An initial `simp` invocation with sum commutation looped; explicit finite-sum
reordering and splitting the matrix-unit conjunction resolved it. Expanding
an ordered product of sums also required explicitly commuting the two OUTER
scalar-index sums, without commuting matrix factors. The scalar coefficient
normalization was unfolded after exposing its definition to complete the
trace calculation. No statement or hypothesis was weakened during repair.

## Remaining dependencies

The explicit deterministic matrix-unit contractions still need a genuine
cycle/index-network interpretation, corresponding cycle counts, and bounds
under uniform Euclidean operator-norm hypotheses on the deterministic
matrices. Matrix row-norm bounds are not a substitute for this scope.
The raw pairing-distance bounds are now available, but their exponents must
be combined with actual contraction powers to control trace sums. Centered
leading-term cancellation remains a separate theorem and is not implied by
this exact integration formula alone.

Independent Haar families additionally need actual product integration and
color-respecting contractions. Expected asymptotic freeness, fluctuations,
concentration, almost-sure convergence and low-dimensional pseudoinverse
integration remain open here. No random-matrix convergence claim is made.
