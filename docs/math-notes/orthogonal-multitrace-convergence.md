# Actual two-trace products, second moments and almost sure convergence

Published source checkpoints on `feat/orthogonal-multitrace-bounds`, depending
on the actual multitrace chain through `b3071c3` and its notes `6677412`:

- `32432ff`: `OrthogonalMultiTraceProducts.lean`.
- `ab161c9`: `OrthogonalMultiTraceSecondMoment.lean`.
- `44e4e23`: `OrthogonalMultiTraceConvergence.lean`.
- `677a3ee`: `OrthogonalMultiTraceAlmostSure.lean`.

All earlier sources are unchanged and frozen. This note supersedes the open
two-trace and almost-sure obligations in the earlier three-module notes.

## Actual product identity

A disjoint sum of arbitrary finite permutations factors the genuine finite
coloring network into the product of its two original networks. This is a
finite sum identity, not factorization of expectations. The actual
integer-power SameCycle relation is proved to preserve the summand tag;
its quotient is equivalent to the disjoint sum of the original quotients.
Thus actual cycle counts add, retaining fixed singleton cycles.

Networks, actual orbit quotients and counts are transported through a
bijection of site types. A positive cyclic Fin index has exactly one orbit,
including length one. Transporting two positive cyclic words from
`Fin r ⊕ Fin s` to `Fin (r+s)` gives `twoTracePermutation r s`, with exactly
two actual cycles. `multiTraceWord_twoTrace` proves the actual two-cycle
observable equals `traceWord A B U * traceWord C D U`, with the SAME U in
both factors, for every orthogonal matrix U and every matrix dimension.
Empty dimensions are retained; positivity of both word lengths is explicit.

## Genuine quadratic expectation and absolute second moment

`twoTraceWordMoment` is the actual Bochner integral of that product against
normalized compact orthogonal Haar measure. Its equality with the actual
multitrace moment and integrability are proved, not supplied as premises.
The previous genuine multitrace bound gives an eventual bound

```
|E_Haar[traceWord(A,B,U) traceWord(C,D,U)]|
  ≤ C_(r+s) K^(2(r+s)) N^-2.
```

Both words have positive lengths; every deterministic factor is genuinely
trace-centered, and every literal Euclidean operator norm is bounded by
K≥0. The threshold depends only on the degrees, not on the factors.

Entrywise complex conjugation is a genuine matrix ring homomorphism. The
source proves that it preserves trace centering and the literal Euclidean
operator norm. Because actual orthogonal entries are real, conjugating a
trace word conjugates its deterministic factors in the SAME order. No
incorrect adjoint-order or independence shortcut is used.
Consequently `traceWordSecondMoment_eq_twoTrace` identifies the actual
real squared-norm integral with that actual same-Haar conjugate product.
`eventually_centered_traceWordSecondMoment_bound` proves

```
E_Haar[|traceWord(A,B,U)|^2] ≤ C_(2r) K^(4r) N^-2,  r>0.
```

The moment is proved nonnegative; squared trace norms are genuinely
integrable. No second-moment or variance estimate is assumed. An explicit
centered-around-the-mean variance object has not been introduced by this
chain; the proved absolute second moment is stronger for convergence to zero.

## Mean square, summability and almost sure scope

`tendsto_centered_traceWordSecondMoment` proves mean square decay for
arbitrary dimension-dependent centered deterministic factors with a common
operator bound. `summable_centered_traceWordSecondMoment` proves summability
over ALL dimensions: the eventual actual N^-2 estimate and the real p-series
test handle the tail, and no restriction removes the finite unstable prefix.

`ae_centered_traceWord_tendsto` is a genuine almost sure result. Its input
is any common measurable space Ω with measure μ and random matrices
`X N : Ω → orthogonalGroup(Fin N)` measure-preserving from μ to the ACTUAL
normalized compact Haar measure in each dimension. For every fixed r>0 and
centered uniformly bounded deterministic families A_N/B_N, it concludes

```
for μ-almost every ω, traceWord(A_N,B_N,X_N(ω)) → 0.
```

No independence across dimensions is required. Measure-preserving marginal
laws transfer both integrability and the actual squared-norm integral through
`integral_map`, without imposing an injective sampling map. Tonelli and the
summable actual second moments give almost-everywhere summability of squared
trace norms; series terms tend to zero, and the square-root transport gives
actual complex trace convergence. This proves a centered alternating-word
criterion for one Haar conjugation versus deterministic bounded factors.

## Checks and failed approaches

Focused builds were warning-free with explicit exit zero: 3045, 3046, 3050,
and 3051 jobs. All 16, 14, 3, and 1 public declarations respectively were
directly transitively audited with only `propext`, `Classical.choice`, and
`Quot.sound`. Exact almost-sure signature was printed and reviewed. The
source guard and whitespace/diff checks passed; every commit was immediately
pushed successfully.

Distinct finite-function enumeration instances required an extensional
finite-universe equality in the cyclic network sum, rather than assuming
definitional equality. Real norm unfolding in the Tonelli conversion needed
explicit absolute-value simplification. A reverse complex-star simp loop was
replaced by a typed equality and `norm_star`; no resource or heartbeat increase
was used. Function composition at the square-root limit was explicitly typed
before simplification. None of the intended mathematical inputs were weakened.

## Remaining dependencies

Convergence in probability and simultaneous countably many fixed words remain
useful interfaces to derive from this chain. No uncountable intersection of
almost-sure sets is asserted. Random deterministic inputs need an actual
independent product-law/Fubini extension, rather than an assumed conditional
expectation estimate. Multiple independent Haar colors need actual product
Haar integration and color-respecting contraction combinatorics.

Marginal star-law convergence and full joint-law/asymptotic-freeness packaging
remain separate intended interfaces. Low-dimensional full orthogonal invariant
spanning/pseudoinverse integration, strong convergence, and outlier statements
are not proved by this chain. Goal certification and integration are coordinator
responsibilities; these are verified published feature results until integrated.
