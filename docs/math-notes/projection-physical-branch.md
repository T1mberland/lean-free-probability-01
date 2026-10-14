# Actual physical branch of finite free half-projection products

This checkpoint establishes the physical branch for the law of the actual positive
iterated product of a GIVEN finite freely independent family of half-trace
projections in a complex C-star algebra, under a normalized positive tracial state.
It applies to every length L >= 2, including length two. It requires neither
faithfulness nor an assumed free realization of arbitrary marginal measures.
Goal certification and integration remain coordinator responsibilities.

## Frozen verified source chain

- `3d8a9d9`: `ProjectionProductCauchyMoment.lean`; genuine exterior Cauchy
  integral satisfies x G_mu(x) = the true law moment sum at 1/x.
- `63647cc`: `ProjectionProductPhysicalPositivity.lean`; Cauchy kernel is
  genuinely integrable and actual w(x) = x G_mu(x) - 1 is strictly positive.
- `74ce973`: `ProjectionProductPhysicalCurve.lean`; actual w satisfies
  z_L(w) = x, where z_L(w) = (w+1/2)^L / (w (1+w)^(L-1)).
- `c379894`: `ProjectionProductPhysicalSelection.lean`; actual normalized
  q = w/(1+w) lies in (0,1/(L-1)). This is derived from genuine analytic
  Picard/law-series matching throughout their shared disk and a supersolution
  strictly below the critical normalized parameter.
- `ee3fa8f`: `ProjectionProductPhysicalUniqueness.lean`; the ACTUAL Cauchy
  parameter is the unique positive root in that normalized physical interval.
- `b9dcde1`: `ProjectionProductPhysicalDomain.lean`; standard domain is
  w > 0 and (L = 2 or w < 1/(L-2)). Length two has no finite w critical point.
- `401d9ff`: `ProjectionProductPhysicalParameterization.lean`; the rational
  curve maps that domain EXACTLY onto (lambda_L,infinity), and actual Cauchy
  w(z_L(w)) = w for EVERY physical w.

All exterior statements hold on the FULL law right exterior x > lambda_L,
not merely near infinity. All family freeness, branch selection, moment
convergence and actual support prerequisites are proved dependencies.

## Public endpoints

`halfProjectionExteriorW_physical_interval`,
`halfProjectionExteriorW_unique_physical`,
`existsUnique_halfProjection_standard_physical_root`,
`halfProjectionExteriorW_curve_inverse`, and
`halfProjectionExteriorCurve_image_physical_domain` are the principal endpoints.
The existing sharp-edge chain establishes `IsGreatest` of actual law support
at lambda_L = L^L/(2^L (L-1)^(L-1)), independently of faithfulness.

Each module passed focused locked compilation and important declarations passed
transitive standard-logic audits. Source-integrity guard passed before publication;
all commits were pushed immediately. A minor failed elaboration in the image proof
required explicit `Set.mem_Ioc` unfolding; no statement was changed.

## Scope and next work

The measure Cauchy transform is genuine on its law exterior even if ambient
operator spectrum is larger under a nonfaithful state. Full ambient-resolvent
identification there consequently requires faithful support-spectrum equality;
without faithfulness use the actual operator resolvent set only.

Next independent refinements are actual infinity normalization, finite critical
coordinate and its genuine derivative for L > 2, the infinite-w boundary for L = 2,
and faithful actual spectrum/operator-Cauchy corollaries. These refinements must
not delay integration of the verified physical chain. General realization of all
compact marginal laws and unrelated conditional subordination are separate goals.
