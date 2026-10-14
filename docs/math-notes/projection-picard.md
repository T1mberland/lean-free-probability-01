# Picard summability prerequisites for the projection-product edge

## Frozen verified checkpoint

The scalar/polynomial/coefficient chain is verified and published through
`ecedffb` on `feat/projection-product-germs`. Coordinator integration is
recorded separately; publication alone does not mark a result integrated.

- `ea956c8`, `ProjectionProductPicard.lean`: real scalar recurrence
  `P(0)=0`, `P(k+1)=(t/2^L)*(1+P(k))^L`. For `t>=0`, the iterates are
  nonnegative and monotone. Any nonnegative scalar supersolution `r` bounds
  every iterate. They genuinely converge to their supremum; continuity and
  the shifted sequence prove the limit is a fixed point. The limit is
  nonnegative and below every nonnegative supersolution.
- `0c66326`, `ProjectionProductPicardPolynomial.lean`: genuine real
  polynomial Picard iterates `P(k+1)=C(2^-L)*X*(1+P(k))^L` have all
  coefficients nonnegative. Their polynomial evaluations equal the scalar
  recurrence exactly. Every finite coefficient sum at `t>=0` is bounded by
  the same scalar supersolution.
- `ecedffb`, `ProjectionProductPicardStabilization.lean`: coefficients below
  order `k` cease changing after `k` steps and remain fixed. The stabilized
  coefficient at degree `n` is the coefficient of polynomial step `n+1`.
  All these coefficients are nonnegative. A scalar supersolution proves
  genuine summability of the infinite coefficient series, and its actual
  sum is at most `r`. Generic coefficient-agreement lemmas for polynomial
  multiplication and powers hold over any semiring.

Every module compiled without warnings under the common build lock. All
major declarations were checked transitively and depend only on
`propext`, `Classical.choice`, and `Quot.sound`; the source-integrity guard
passed. No additional dependency revision or toolchain change was made.

## Exact distinction from the actual probability law

`ProjectionProductMomentEquation` (`e5a6259`) independently derives, near
zero, the actual resolvent moment equation of the given free half projections:

`z*(w+1/2)^L = w*(1+w)^(L-1)`.

For the genuine change of variable `q=w/(1+w)`, it proves

`2^L*q = z*(1+q)^L`.

The Picard results above do not yet identify the stabilized coefficient
series with this actual analytic `q`. Positive moments of `w` do not by
themselves imply positive coefficients of `q=w/(1+w)`. That implication
must not be assumed.

The support bridge (`b01daeb`, `ProjectionProductMomentSupport`) is already
proved: for a positive probability law with integrable moments and `b>0`,
actual support is contained in `(-infinity,b]` exactly when its actual
positive moment series is summable for every `0<t<1/b`. This is a Tonelli
and geometric-series theorem. It has no assumed spectral-edge premise.
The finite product's actual law discharges positivity and integrability.

The remaining intended chain for lengths above two is:

1. Establish the exact formal equation and uniqueness for the stabilized
   Picard series.
2. Construct its analytic sum and identify it near zero with the actual
   `q`, using a proved expansion and local implicit-equation uniqueness.
3. Transfer `w=Q/(1-Q)` to the actual moment coefficients, with `Q(t)<1`
   on the subcritical interval. Prove true actual moment summability there.
4. Use the verified support bridge for the upper edge bound and the
   supercritical fixed-point obstruction for the matching lower bound.
5. Identify the physical exterior parameterization from the actual Cauchy
   transform and actual law support, rather than just scalar calculus.

Length two must retain its boundary behavior: critical `q=1` corresponds to
`w` tending to infinity. The coordinator is handling length-two results
separately. No theorem in this Picard chain claims a general actual right
edge or a physical-branch identification.

## Failed approaches and engineering discoveries

- Unrestricted simplification of recursive Picard polynomials together with
  `mul_comm` loops through multiplication rewrite rules. Explicit evaluation
  lemmas and one controlled recursion unfolding resolve this without raising
  recursion depth or resource limits.
- Simplifying the recursive polynomial equation on both sides unfolded an
  inner step needed by coefficient stabilization. A typed `change` exposes
  only the two outer steps; convolution and power agreement then apply.
- Rewriting an equation `z=...` throughout a moment equation also rewrites
  the argument of the actual moment function. Congruence on only the outer
  scalar factor avoids this incorrect tactic shape.
- A denominator power expanded before cancellation hid the required
  nonzero power. Cancelling the whole power with a proved nonzero base
  before successor-power expansion resolved the field calculation.
- Passing a measure support conull fact directly to `.mono` can elaborate
  it as a null-complement equality. State it explicitly as an almost-
  everywhere support-membership proposition first.

These were genuine Lean proof/elaboration errors, not resource exhaustion.
Focused builds waiting for the common lock remained serialized. No extra
heavy builds were launched to respond to those waits.
