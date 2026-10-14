# Physical limits, critical coordinates, and ambient spectrum

This adds refinements to the frozen actual-law physical branch through `401d9ff`
and its notes `b3a58a5`. Every statement concerns GIVEN full free finite families
of half-trace projections under a normalized positive tracial state. Law statements
require no faithfulness. Every completed source is frozen after this checkpoint.

## Published verified milestones

- `6be9139`, `ProjectionProductPhysicalLimitsCriticalEdge.lean`:
  for L >= 3, w_critical = 1/(L-2) normalizes to q_critical = 1/(L-1),
  z_L(w_critical) = lambda_L, and the ACTUAL exterior curve has derivative zero
  there. The actual law support has `IsGreatest` at this critical curve value.
  The normalized moment curve has derivative zero at q_critical for ALL L >= 2.
- `aa3739d`, `ProjectionProductPhysicalLimitsInfinity.lean`:
  actual w(x) = x G_mu(x)-1 tends to zero as x tends to positive infinity;
  actual x G_mu(x) tends to one. Proof uses true law moments and the analytic
  expectation germ, without assigning ambient inverses outside their domain.
- `7c17f68`, `ProjectionProductPhysicalLimitsTwo.lean`:
  z_2(w) = 1 + 1/(4w(1+w)) is strictly decreasing for positive w and tends
  to one at infinity. The ACTUAL length-two law has greatest support point one,
  and its ACTUAL Cauchy parameter tends to positive infinity as x decreases
  to one from above. There is no finite w critical point at length two.
- `e75218e`, `ProjectionProductPhysicalSpectrum.lean`:
  faithfulness identifies the greatest ACTUAL ambient spectral point and its
  supremum with lambda_L, and guarantees the entire sharp right exterior lies
  in the actual complex resolvent set. The operator Cauchy transform there
  equals the law Cauchy integral, and its normalized parameter equals the
  verified actual physical parameter.

## Precise law versus spectrum distinction

The law support edge, true integral exterior branch, root selection, uniqueness,
full domain-image equality, critical law-support connection, infinity
normalization, and length-two boundary all require NO faithfulness.

The generic theorem
`iteratedProjection_operatorCauchyTransform_eq_realLawCauchy` also requires no
faithfulness, but explicitly requires the argument to lie in the ACTUAL ambient
resolvent set. It does not infer this from law exterior under a nonfaithful state.

The faithful wrappers use the existing proven support-spectrum equality to derive
actual full exterior resolvent membership. Their `IsFaithful` hypothesis is used
for ambient spectrum identification, not appended to the law theorems.

## Verification and engineering notes

Each milestone passed warning-free focused compilation under the shared build
lock. All important declarations were checked transitively with only standard
Lean logical foundations. The source-integrity guard passed before each atomic
commit, each staged diff was checked, and each commit was pushed immediately.

Minor failed elaborations involved explicit real integral typing before complex
embedding, scalar-tower transport, interval membership unfolding, and inferred
constant functions in limit statements. All were corrected without changing
mathematical statements or adding premises. A lock wait behind coordinator
integration was normal serialization, not a compilation or resource failure.

Goal certification and final integration are coordinator-owned. Universal free
realization of arbitrary compact laws and conditional subordination are separate
obligations. The next assigned independent frontier is Haar-unitary conjugation.
