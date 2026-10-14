# Actual finite free positive and projection products

## Verified development checkpoint

Branch `feat/projection-product-germs`, mathematical source checkpoint
`ac57b17`. This is development history; integration is recorded separately by
the coordinator. All modules below passed focused kernel compilation, the
source-integrity guard, and transitive declaration checks with only
`propext`, `Classical.choice`, and `Quot.sound`.

- `aced769`, `ProjectionProductFunctionalCalculus`: an actual positive
  element's ambient `CFC.sqrt` belongs to any closed star subalgebra containing
  it. Real self-adjoint functional calculus on the closed subtype, followed
  by the subtype inclusion, avoids an extra subtype positive-order premise.
  Self-adjoint or star-stable generators identify the underlying closed star
  algebra with the ordinary closed generated algebra.
- `62fdf70`, `ProjectionProductGrouped`: grouping singleton-generated
  algebras equals generating the actual elements in each grouping fiber.
  Original family freeness implies freeness of these closed star algebras.
  The actual sandwich S-transform identity therefore applies between groups.
- `ce91885`, `ProjectionProductIteration`: the empty product is `1`; each
  next stage is `sqrt(prefix) * next * sqrt(prefix)`. Every actual stage is
  positive and belongs to every closed star algebra containing its positive
  factors. The preceding factors lie in the false fiber of
  `prefixLastGroup`, and the last factor lies in its true fiber.
- `c7d324d`, `ProjectionProductMoments`: under a tracial state and original
  full-family freeness, the actual first moment equals the product of all
  marginal first moments. Nonzero individual means imply a nonzero product
  mean; it is not an extra assumption.
- `f6fca7f`, `ProjectionProductS`: the actual S-transform germ of the finite
  positive product equals the product of actual marginal S-transform germs,
  including their removable values at zero. The empty-family normalization
  is proved as well. Each induction step derives prefix-versus-next
  freeness from the original family.
- `abc6e36`, `ProjectionProductRational`: actual projection products have
  germ `prod_i (1+w)/(E(p_i)+w)`. For half-trace projections the actual mean
  is `(1/2)^L`, the S germ is `((1+w)/(1/2+w))^L`, and the selected inverse
  moment germ is `w/(1+w) * ((1+w)/(1/2+w))^L`. These statements hold for
  every finite length, so length two is retained.
- `d81513d`, `ProjectionProductLaw`: a genuine spectral probability measure
  of the actual finite positive product, compact nonnegative support, and
  literal power-moment representation. Actual projection products are
  positive contractions, so their actual law has support in `[0,1]`.
- `ac57b17`, `ProjectionProductLawIndependence`: all powers, and then actual
  probability laws, agree for two given finite free positive families in
  different ambient algebras when their marginal moments or genuine
  marginal laws agree. In particular, the law of a given free half-trace
  projection family depends only on its number of factors.

## Scope and hypotheses

The supplied ambient algebra is a C-star algebra with its star order. A
normalized positive state constructs actual spectral probability measures;
traciality is used for actual square-root sandwich moment transfer. Actual
original-family freeness is required, rather than only pairwise freeness.
The grouping map and original algebra families have no cardinality
restriction in the grouping prerequisites. Product tuples themselves are
finite. Nonzero marginal means are required only for the inverse/S germs.
They are not required for construction or determination of the laws.

No theorem above assumes prefix freeness, square-root membership in a prefix
algebra, a supplied product distribution, a product S-transform identity,
or the existence of a free realization of arbitrary compact input measures.
Faithfulness is unnecessary for these actual law statements. Equality of
operator spectrum with actual law support would require separate suitable
faithfulness hypotheses.

## Remaining physical branch and spectral support obligation

The right edge required by Goal 7 is not proved by the local rational germs
or by the coarse support inclusion `[0,1]`. The remaining intended number is

`lambda_L = L^L / (2^L (L-1)^(L-1))`, for `L >= 2`.

The intended exterior curve is

`z_L(w) = (w+1/2)^L / (w(1+w)^(L-1))`.

For `L > 2` its positive critical point is `w=1/(L-2)`. Length two has a
boundary critical value as `w` tends to infinity, so the finite-critical-
point argument cannot be applied to that case.

A useful exact change of variable is `q=w/(1+w)`. The intended actual inverse
relation becomes `chi = 2^L q/(1+q)^L`, with critical
`q=1/(L-1)`; its limiting value yields the same proposed edge, including
`q=1` at length two. This change is not itself an actual support theorem.

Two rigorous routes under investigation:

1. Derive the actual local polynomial moment equation from the selected
   inverse germ, extend the actual Cauchy equation on a connected analytic
   domain, and prove that a real holomorphic continuation of the measure's
   Cauchy transform across a real interval forces zero mass there. Relate
   failure of the physical branch at the critical point to actual support.
   A reusable Cauchy-support exclusion theorem is currently missing.
2. Derive a positive recursive series for `Q(t)` with
   `Q=(t/2^L)(1+Q)^L`, prove its genuine summability on the subcritical
   interval using monotone Picard bounds, and recover the actual moment
   series as `W=Q/(1-Q)`. Supercritical fixed-point impossibility can then
   identify its radius, with a separate positive compact-law theorem
   relating moment-series radius to the actual right support edge.
   The positive implicit-series summability and radius/support interfaces
   are currently missing; coefficient positivity alone is insufficient.

Pinned mathlib has no ready Lagrange reversion, Pringsheim, or the required
Stieltjes-transform support-exclusion theorem found by the reviewer. These
are precise mathematical prerequisites, not compilation failures. Do not
replace the physical/support obligation with formal critical-point calculus.
