# Actual analytic Picard identification

## Frozen verified checkpoint

The analytic Picard chain is verified and published through `b9bf87d` on
`feat/projection-product-germs`. Integration is recorded separately by the
coordinator. This checkpoint adds four modules to the preceding frozen
Picard summability chain (`9e10479`).

- `040d0cc`, `ProjectionProductPicardFormal.lean`: the formal series of the
  already genuinely summable stabilized coefficients solves
  `Q=C(2^-L)*X*(1+Q)^L`. That equation has at most one formal solution over
  any semiring; no extra constant-coefficient hypothesis is needed.
- `c640cc0`, `ProjectionProductSeriesEvaluation.lean`: absolute convergence
  of genuine complex scalar series is preserved by formal sums, products,
  and powers, and actual evaluations respect these operations. A formal
  implicit equation plus proved absolute convergence therefore becomes a
  literal equation for the actual scalar sum.
- `380c8a4`, `ProjectionProductPicardAnalytic.lean`: the mapped complex
  Picard coefficients have proved absolute convergence throughout every
  disk bounded by a scalar supersolution. The actual sum has norm at most
  that supersolution. It satisfies the actual implicit equation and has a
  proved scalar Taylor expansion whose radius is at least the supplied
  disk radius. A concrete half-unit disk yields unconditional analyticity
  at zero and the actual normalization `Q(0)=0`.
- `b9bf87d`, `ProjectionProductPicardIdentification.lean`: the constructed
  analytic sum is exactly the normalized ACTUAL resolvent moment germ
  `psi_P/(1+psi_P)` of any supplied finite free half-trace projection family
  in a tracial C-star probability space. Consequently the actual moment
  function germ equals the actual analytic sum `Q/(1-Q)`.

The last identification is an actual mathematical achievement, not a
formal-series comparison. The inverse parameter
`F(q)=2^L*q/(1+q)^L` has proved strict derivative `2^L != 0` at zero. Its
actual local inverse identifies any two continuous normalized local
solutions. Both the true probability moment function and the constructed
sum discharge continuity, normalization, and their actual equations.
No assumption of positive coefficients of the original normalized moment
function is introduced.

All four modules compiled without warnings under the common lock. Each
major declaration was audited transitively with only `propext`,
`Classical.choice`, and `Quot.sound`; the integrity guard passed. These
changes did not alter the pinned Lean toolchain or mathlib revision.

## Remaining quantitative transfer at this checkpoint

The statements above identify germs. They do not yet transfer the larger
Picard convergence disks to the TRUE power-moment coefficient series of the
actual law. The next exact proof obligation is:

1. Prove the actual inverse expectation has a genuine scalar Taylor series
   with coefficients `phi(P^k)` using the existing actual Neumann sum.
2. For a positive disk radius `t` and a scalar supersolution `0<=r<1`, the
   constructed reciprocal `1/(1-Q)` is analytic on the disk. On every
   smaller closed disk its differentiability supplies a Cauchy-integral
   Taylor expansion.
3. Use the actual local equality and analytic-series uniqueness to identify
   these coefficients with the actual moments, proving their absolute
   summability throughout the larger disk without assuming it.
4. Apply the already verified positive-law support/moment-summability
   equivalence to obtain an actual support upper bound.

This transfer is being implemented in the separate new
`ProjectionProductMomentSummability.lean`; it is not part of this frozen
checkpoint.

## Remaining sharp edge and physical branch

For `L>2`, calibrate actual scalar supersolutions below one at every
parameter less than

`t_star = 2^L*(L-1)^(L-1)/L^L`.

Then prove the matching obstruction beyond `t_star`, connect it to the
actual law support lower bound, and identify the genuine exterior Cauchy
parameterization and its physical branch. These claims remain separate
from the local identification above. A formal derivative or critical-point
calculation cannot replace them. Length two has critical `q=1`, hence
`w` tending to infinity. Calibration must choose a strict subcritical
`r<1`, for example by continuity from below at the critical parameter;
using the critical value itself would violate the strict majorant hypothesis.

Actual law support and operator spectrum are distinct without a suitable
faithfulness premise. The law construction, local matching, and marginal
law independence above require no faithfulness. Universal free realization
of arbitrary compact input laws remains a separate construction task.

## Proof engineering discoveries

- Genuine multiplication evaluation uses the antidiagonal Cauchy-product
  theorem with proved norm summability of both factor series. A bare formal
  multiplication equality is not an evaluation proof.
- The real-to-complex Picard map preserves the formal equation. Nonnegative
  coefficients and modulus comparison then prove actual complex convergence
  and its norm bound without assuming either.
- The scalar formal Taylor series uses `FormalMultilinearSeries.ofScalars`;
  norm summability directly supplies a radius bound, and the sum admits a
  genuine `HasFPowerSeriesOnBall` expansion.
- Rewriting `Q=...` through both sides of a fixed-point equation changes the
  inner `Q` expressions unnecessarily. Apply congruence only to the outer
  factor and cancel the known nonzero scalar instead.
- NNReal radius coercions into ENNReal are not always definitionally equal
  to the corresponding fractional numeral. A proved coercion equality is
  needed; this is an elaboration issue, not a mathematical extra hypothesis.
