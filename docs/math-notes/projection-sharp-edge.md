# Actual right support edge of free half-projection products

## Verified sharp-edge checkpoint

The six-module sharp support chain is verified and published through
`d367204` on `feat/projection-product-germs`. Integration is recorded
separately by the coordinator. The intended actual right support edge is
now proved for every supplied finite free half-trace projection family,
for all lengths `L>=2`, including the boundary length two:

`lambda_L = L^L / (2^L * (L-1)^(L-1))`.

The public theorem `iteratedHalfProjection_law_support_isGreatest` states
that this number is the greatest point of the ACTUAL product law's support.
`iteratedHalfProjection_law_right_edge` states equality with its support
supremum. These are genuine support theorems, not scalar critical-point
calculations.

The actual product is the previously defined finite recursive positive
sandwich of the supplied projections. Its actual law is
`iteratedPositiveProbabilityLaw`, constructed as a spectral probability
measure in the given ambient C-star probability space. The hypotheses are
original full-family freeness, projection membership in the original free
algebras, genuine star projections, half expectations, and a tracial
normalized positive state. No actual support bound, moment summability,
product equation, prefix independence, or product S identity is assumed.
Nonzero means are derived where needed. Faithfulness is not required.

## Verified dependency modules and hashes

- `0ae1e0e`, `ProjectionProductMomentSummability.lean`: the actual Neumann
  sum supplies true Taylor coefficients `phi(P^k)`. A scalar Picard
  supersolution `0<=r<1` gives analyticity of the genuine reciprocal
  `1/(1-Q)` on its disk. Cauchy expansions on smaller closed disks and
  analytic-series uniqueness identify the actual moment coefficients.
  This proves TRUE absolute moment summability on the enlarged disk and
  an ACTUAL law support bound by the reciprocal scalar radius.
- `89223d8`, `ProjectionProductCalibration.lean`: normalized critical
  parameter `q=1/(L-1)` and critical reciprocal value are evaluated exactly.
  Continuity yields positive supersolutions strictly below one for every
  subcritical moment parameter, including length two. The actual-law
  support upper bound by `lambda_L` follows from the genuine moment and
  support bridge.
- `66f54e3`, `ProjectionProductCurveMaximum.lean`: the normalized curve
  `F_L(q)=2^L*q/(1+q)^L` increases before the critical parameter and decreases
  after it. It never exceeds the reciprocal critical edge at any `q>=0`.
- `58d42ec`, `ProjectionProductMomentContinuation.lean`: the sum of TRUE
  law moment coefficients is defined separately from the ambient inverse.
  Its cleared half-projection polynomial equation holds near zero, then
  throughout every disk inside its TRUE radius by the analytic identity
  theorem. Clearing denominators avoids assumptions about complex zeros.
- `9897fbf`, `ProjectionProductLawMomentBounds.lean`: true positive-law
  moments are nonnegative. The complex coefficient sum at a real parameter
  is the embedded real law moment sum, which is at least one where its
  series converges. An ACTUAL law support bound gives a true Taylor radius
  bound independent of the ambient operator norm.
- `d367204`, `ProjectionProductSupportLower.lean`: any strictly smaller
  positive proposed support bound contradicts the true moment equation and
  the global scalar curve maximum. Compactness and nonempty probability
  support, combined with the upper bound, give actual support membership
  of `lambda_L`, its greatest-point property, and the exact support supremum.

Every focused module build completed without warnings. All major theorem
statements and the exact edge definition were inspected. The transitive
checks use only `propext`, `Classical.choice`, and `Quot.sound`; the
source-integrity guard and staged diff checks passed. All milestone commits
were pushed immediately and push success was checked. No pinned dependency
revision or toolchain was changed.

## Why the lower bound is about actual support

Assume the actual law were supported below a positive `b<lambda_L`.
Positive law moment bounds produce a genuinely convergent true coefficient
series on disks below `1/b`. Choose a real parameter strictly between
`1/lambda_L` and `1/b`, with a larger disk still below `1/b`. Analytic
continuation gives the cleared moment equation at that parameter.
The actual real sum `I` is at least one. The resulting nonnegative
`q=(I-1)/I` solves `F_L(q)=u`, while the global scalar bound forces
`F_L(q)<=1/lambda_L<u`, a contradiction.

No ambient operator inverse is used beyond its resolvent domain. This is
necessary in a nonfaithful state: the ambient spectrum can contain spectral
components absent from the actual probability law. Equality of actual-law
support and the ambient operator spectrum requires a separate suitable
faithfulness premise. The current theorem deliberately states the actual
probability-law edge, with no faithfulness hypothesis.

## Remaining physical exterior branch

The exact law edge alone does not finish the full intended Goal 7 statement.
The genuine exterior parameterization and physical branch must still be
connected to the actual Cauchy integral, with the correct branch interval
and boundary behavior. The length-two normalized critical value is `q=1`,
corresponding to `w` tending to infinity; no finite `w=1/(L-2)` argument is
valid there.

A separate new milestone `3d8a9d9`, `ProjectionProductCauchyMoment.lean`,
already proves that the literal actual real Cauchy integral satisfies
`x*G_mu(x)=I(1/x)` for the FULL actual-law right exterior `x>lambda_L`.
It uses absolute Bochner series summation and the actual support bound.
It is not part of the six-module frozen sharp-edge chain.

Next, derive the true positive parameter `w=x*G_mu(x)-1`, prove the rational
exterior curve equation, select `0<q<1/(L-1)` using genuine Picard bounds
and analytic matching, and prove uniqueness in the physical interval.
An operator-resolvent corollary must use its actual resolvent-set domain or
an explicitly justified faithful spectrum/support equality.

## Proof engineering discoveries

- Actual spectral-law moment integrals must be typed as REAL integrals
  before their complex embedding. Otherwise an expected complex type can
  move the coercion inside the integrand instead of embedding the integral.
- Let-bound probability measures can obscure coefficient equalities under
  norm simplification. Expose the literal measure definition before
  comparing the true real moment coefficients.
- The cleared polynomial allows identity-theorem continuation over a whole
  connected complex disk without assuming the denominator `I` is nonzero
  throughout that disk. Positivity is needed only at the selected real point.
- Complex-to-real polynomial transfer is reliable after an explicitly typed
  complex equation, real-embedding injectivity, and controlled cast pushing.
- Scalar derivative simplification must reduce pointwise function powers
  and additions before expanding successor powers; otherwise ring
  normalization treats unevaluated function expressions as unrelated atoms.

These were proof and elaboration issues, not resource failures. Builds
remained serialized by the shared lock.
