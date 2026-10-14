# Genuine centered multi-trace Haar expansion and cycle-count decay

Published source milestones on `feat/orthogonal-multitrace-bounds`:

- `b7b4acf`: `OrthogonalMultiTraceExpansion.lean`.
- `7171e29`: `OrthogonalMultiTraceContractions.lean`.
- `b3071c3`: `OrthogonalMultiTraceBounds.lean`.

All are new `FreeProbability/RandomMatrix` modules depending on the verified
single-trace chain `5d3f9f6`; previous files remain unchanged.

## Exact actual multi-trace object

For an actual permutation `π` on `Fin r`, let `m` be the cardinality of its
actual `SameCycle` quotient, including fixed singleton cycles. Define

```
multiTraceWord(π,A,B,U)
  = N^-m permutationNetwork(π, k ↦ Uℂ A_k Uℂᵀ B_k).
```

The source proves this is the product of genuine normalized ordered matrix
traces, one per ACTUAL cycle of `π`. `multiTraceWordMoment` is its actual
Bochner integral against the genuine orthogonal Haar probability measure.
No product-of-expectations or independence assumption is made.

Actual block matrix expansion and finite scalar product-of-sums yield its
entry monomial code expansion. Integrability is proved from actual compact
Haar and continuity. Finite integral linearity yields real entry moments
cast to complex values. The previously proved true stable Weingarten formula
then gives the actual inverse-Gram pairing-contraction sum.

Empty index degree is handled exactly: zero cycles give empty trace product
one, even in matrix dimension zero. Nonempty index in matrix dimension zero
has actual multi-trace word zero. These conventions differ legitimately from
one empty single matrix trace; no nonexistent cycle is inserted.

## Genuine contraction and counting

The multi-trace code matrix units force the actual row coloring at each
index, giving the deterministic coefficient

```
N^-m (∏k A_k(b_k,d_k)) (∏k B_k(c_k,a_(πk))).
```

The actual row deterministic-edge code pairs `right(k)` with `left(πk)`;
its inverse and endpoint formulas are proved. Its finite sum is identified
with the genuine paired network, with the true raw-loop operator-norm bound.
Actual independent row/column code colorings then prove exactly

```
Contraction(π,A,B,p,q) = N^-m Row(π,B,p) Column(A,q).
```

No cycle or coloring factorization premise is supplied.
Every centered nonzero paired network has no fixed selected singleton, as
already proved through its actual zero cycle trace. Thus its raw loop count
is at most half its `r` deterministic labels. If neither row nor column
network vanishes, their loop counts sum to at most `r`. Hence the actual
centered contraction is bounded by

```
N^(r-m) (∏k ‖toEuclideanCLM(A_k)‖) (∏k ‖toEuclideanCLM(B_k)‖).
```

The genuine cycle count `m≤r` and positivity `m>0` for `r>0` are separately
proved. All norms in public statements are literal Euclidean operator norms.

## Kernel-verified expectation rate

`eventually_centered_multiTraceWordMoment_norm_le` proves, for fixed `r`,
eventually in `N`, for ALL permutations `π` and ALL centered complex matrix
factors after the SAME threshold,

```
‖multiTraceWordMoment(π,A,B)‖
  ≤ C_r N^-m (∏k ‖toEuclideanCLM(A_k)‖) (∏k ‖toEuclideanCLM(B_k)‖),
C_r = M^2(r M^r + 2 M^(r+1)), M=card(OrdinaryPairing r).
```

The uniform norm corollary gives `C_r K^(2r) N^-m` for a genuine common
bound `K≥0` on every operator norm. The threshold depends ONLY on `r` via
actual Weingarten bounds. `tendsto_centered_multiTraceWordMoment` proves zero
limit for nonempty index and uniformly bounded dimension-dependent centered
families. At degree zero the bound has exponent zero and no decay assertion
is made; the exact empty product remains one.

## Verification and engineering

Focused builds passed without warnings (3042, 3043 and 3044 jobs). Twelve,
eight and six public definitions/theorems respectively were transitively
audited with only `propext`, `Classical.choice`, and `Quot.sound`.
Source integrity, staged whitespace checks and diff review passed at every
checkpoint; each source commit was pushed immediately.

The first expansion transport encountered different actual finite-function
enumeration instances; an extensional finite-universe equality, rather than
assuming definitional equality, made the sum congruence precise. Unused
finite/decidable-color assumptions in code-coordinate helpers were removed.
Scalar power compensation was proved separately with independent natural
indices, preventing dependent dimension rewrites in pairing types. No target
integration, cycle, decay or limit statement was weakened or supplied as a
premise.

## Remaining probability modes and family scope

This proves actual single-Haar products of centered normalized traces. A
specific product of a trace word and its complex conjugate still must be
identified with the actual two-cycle object, with doubled degree, true
concatenation permutation and norm/centering preservation. Only then may
an actual nonnegative second-moment `O(N^-2)` or variance bound be claimed.
Almost-sure convergence additionally needs a genuine probabilistic
realization and summability/Borel-Cantelli transfer; independence across
dimensions need not be assumed if the bounds suffice, but this must be
proved in the stated interface.

Arbitrary independent Haar families need product Haar/color-respecting
integration and intended alternating-word interfaces. Marginal convergence,
full joint asymptotic freeness and low-dimensional pseudoinverse integration
remain separate obligations. No variance or almost-sure theorem is claimed
by these three source checkpoints.
