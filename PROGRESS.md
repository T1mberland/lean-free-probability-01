# Progress

## Scope and status

This project develops reusable Lean 4 foundations for free probability, operator
algebras, and random matrices. Its targets are mathematical results described in
[docs/PROJECT_GOAL.md](docs/PROJECT_GOAL.md), with an audit and dependency roadmap
in [docs/DEPENDENCIES.md](docs/DEPENDENCIES.md). No particular application is a
completion criterion.

## Verified foundations

| Modules | Results |
| --- | --- |
| `Algebraic.ProbabilitySpace`, `Freeness`, `MixedMoments`, `MixedMomentUniqueness` | Normalized expectations, centering, restriction and pullback; free mixed second through fourth moments; uniqueness of all labeled mixed moments from free marginals |
| `Algebraic.Distribution`, `DistributionComparison`, `MomentConvergence`, `Invariance` | Word and polynomial joint distributions, comparison across ambient algebras, polynomial/moment convergence equivalence, and simultaneous unitary-conjugation invariance |
| `Algebraic.StarProbabilitySpace`, `PositiveExpectation`, `Analytic.Expectation`, `Matrix.NormalizedTrace` | Positive star-compatible states, positivity on the full ordered cone, norm-one continuous expectation and Cauchy–Schwarz on ordered unital C-star algebras, and positive faithful normalized matrix trace |
| `OperatorValued.ConditionalExpectation` | Linear retractions onto subalgebras, bimodule identities, centering, freeness with amalgamation, and the mixed second-moment identity |
| `Combinatorics.NoncrossingPartition`, `Cumulant`, `PartitionMultilinear`, `CumulantMultilinear`, `NoncrossingSingleton` | Noncrossing partitions, constructive all-order moment–cumulant inversion and uniqueness, cumulant multilinearity, and singleton-block combinatorics |
| `Algebraic.CumulantFreeness`, `Combinatorics.CumulantNaturality` | Vanishing mixed cumulants implies freeness; cumulants commute with expectation-preserving maps |
| `Combinatorics.NoncrossingPairing` | Intrinsic two-element-block pairings, unique partners and their fixed-point-free involution, even size, and existence of an adjacent pair |
| `Combinatorics.NoncrossingInterval` | Every equivalence class has a least representative; every nonempty noncrossing partition has an actual convex interval block, represented by inclusive endpoints |
| `Fock.WordSpace`, `Fock.VacuumState` | Complete Hilbert word model, bounded isometric canonical creation and adjoint annihilation, operator-wide canonical relation, positive normalized vacuum state, self-adjoint centered candidates with variance one and norm at most two |
| `Analytic.MomentSeries`, `Transform`, `ProjectionTransform`, `TransformNaturality` | Actual operator inverse and resolvent expectations, convergent moment power/Laurent expansions, analytic inverse moment and S-transforms, exact idempotent transform, scalar scaling, and equality of transform germs from common moments |
| `Analytic.CauchyHalfPlane`, `CauchyNaturality`, `MomentConvergence` | Resolvent-set analyticity, strict upper-half-plane imaginary-part negativity, norm bounds, equality from moments at every nonreal argument for selfadjoint variables, and transform convergence under an eventual uniform source norm bound |
| `Matrix.RankOneSecular`, `HermitianResolvent` | Exact secular and Sherman–Morrison identities; spectral resolvent expansions; positivity and monotonicity; rank-one norm thresholds; at most one exterior eigenvalue counted with multiplicity |

Representative declarations include:

- `FreelyIndependent.mixed_moments_unique` and
  `sameStarDistribution_of_selfAdjoint_free_marginals`.
- `moment_cumulant_formula_all`, `cumulantMultilinear_eq`,
  `MixedCumulantsVanish.freelyIndependent`, and `freeCumulant_map`.
- `StarProbabilitySpace.continuousExpectation_norm`,
  `hasSum_cauchyTransform`, `analyticAt_sTransform_zero`,
  `sTransform_idempotent_eventually`, and
  `cauchyTransform_eq_of_powerMoments_nonreal`.
- `rankOne_norm_le_iff_resolvent_le`,
  `rankOne_exterior_eigenvalue_indices_subsingleton`, and
  `posSemidef_norm_mono`.

## Fock construction checkpoint

The word-space and vacuum-state modules are integrated, checked and published on
`main` at `9f85ea8` (worker commits `778c6b0`, `6291082`). The audit covers 1039
declarations. `Fock.annihilation_creation` is an equality of bounded operators,
and `Fock.vacuumExpectation_star_mul_self` proves positivity as the actual squared
norm of the vacuum image. The fourth vacuum moment two is a checked usage example.
These results impose no finite/countable restriction on the generator type.

General Hilbert-space tensor-power identification, arbitrary-vector creation,
exact norm two, the full joint Wick law, freeness, and faithful tracial vacuum
restriction on the generated algebra remain open. Polynomial Wick and right
operator milestones are being developed separately; the vacuum state on all
bounded operators is not claimed faithful or tracial.

## Haar probability and concentration

The orthogonal Haar modules establish a normalized compact-group probability,
left/right/inversion invariance, all-order entry integrability, and row/column
parity constraints. Exact entry second moments and the full row fourth-moment
tensor are proved, together with quadratic-form means, variance bounds, and
Chebyshev deviations. Independent-row bilinear fourth moments have a summable
dimension rate and an almost-sure zero limit under arbitrary cross-width
couplings with a linearly growing first dimension.

Orthogonal transitivity, invariant spherical-probability uniqueness, and the
complete normalized Gaussian representation of Haar image vectors are proved.
The sign mask has an independent half-Bernoulli law; the active coordinate count
has the binomial law, an exact exponential deviation bound, and an almost-sure
density limit of one half.

General centered independent-sum second and fourth moments and independent-array
complete-convergence tools allow nonidentical coordinate laws and arbitrary
coupling between rows. Gaussian square and positive-part-square means and fourth
moments give almost-sure energy-fraction limits. Fresh Haar weights acting on a
measurable nonzero random input have joint direction, gate-count, and energy
product laws independent of the input history. Extinction errors are kept
explicit in finite-dimensional probability bounds.

These results live in [RandomMatrix](FreeProbability/RandomMatrix). General
orthogonal Weingarten asymptotics, conditional sphere sampling, conditioned
random-matrix estimates, and summable centered-quadratic tails remain open.

## Additional examples

[Applications/ReLU](FreeProbability/Applications/ReLU) contains verified examples
using the general matrix and probability interfaces:

- Diagonal gates have the actual active-coordinate rank, are positive
  projections, and give Euclidean operator contractions.
- Finite triangular products have exact bulk and scalar products, a closed
  transported-row expansion, and a bulk-plus-rank-one Gram representation.
  Their exterior norm criterion follows from the scalar secular equation.
- A concrete finite-depth independent-Haar model with positive gains has proved
  measurability, the exact scaled ReLU recursion, an extinction bound, and
  almost-sure forward gate/energy/amplitude limits under arbitrary width coupling.
  The results extend to independent measurable almost-surely nonzero random
  initial inputs.
- Explicit rational functions have verified critical-point evaluations, global
  minima and uniqueness at depths at least three, depth-two infimum and limit,
  and strict subcriticality of the associated finite sums. Identification with
  a free spectral law remains open.

These are available examples of proved tools and calculations. They establish
neither general strong convergence nor a Jacobian operator-norm limit.

## Verification and publication

- Lean 4.34.1; mathlib revision
  `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- `lake build`, the direct `Verification/Axioms.lean` audit, and the source
  integrity guard passed. The transitive audit covers 954 library declarations
  and permits only `propext`, `Classical.choice`, and `Quot.sound`.
- GitHub Actions repeats the build, source guard, and transitive audit.
- The analytic transform milestones were integrated through
  [PR #1](https://github.com/T1mberland/lean-free-probability/pull/1). Verified
  milestones and feature branches are published promptly; repository workflow
  is recorded in [AGENTS.md](AGENTS.md).

## Next mathematical priorities

The current assignments, integration hashes, design decisions and execution queue
are maintained in [docs/EXECUTION_QUEUE.md](docs/EXECUTION_QUEUE.md). The verified
starting snapshot was published as `faf32e8` on `main` and
`feat/verified-baseline` in `T1mberland/lean-free-probability-01`. The integration
build and audits still pass for 954 declarations. Cumulant/pairing and Fock workers
have isolated worktrees; their active tasks are not yet integrated results.

Pairing fundamentals were subsequently integrated and checked on `main` at
`6ade2b4` (worker milestone `ab82d17`). Full builds, the source guard and the
transitive axiom audit pass for 970 library declarations. Interval blocks and
word-Fock operators were separately published worker milestones. Interval blocks
are now integrated and checked at `f419315` (worker source `4df3696`); builds and
audits pass for 973 declarations. The word-Fock milestone awaits its integration
checkpoint. These prerequisites do not establish the full cumulant or Fock goals.

1. Complete cumulant calculus: refinement and interval-block combinatorics, unit
   insertion, adjacent products, and freeness implies vanishing mixed cumulants.
2. Construct full Fock space, bounded creation operators, semicircular systems,
   joint Wick moments, and a faithful tracial vacuum state on the generated algebra.
3. Develop free difference quotients and integration by parts, then operator-valued
   semicircular covariance and Dyson resolvent identities.
4. Construct spectral measures and faithful tracial analytic interfaces, then
   spectral-edge certificates, convolution, projection-product laws, and subordination.
5. Develop Haar conjugation and joint asymptotic freeness with distinct convergence
   modes; then Wick words, free Gaussian OU, noncommutative integration and entropy.

The detailed audit records the earliest missing dependencies for each target.
Existing matrix and ReLU examples remain verified tools; their rational edge
calculations do not establish a free spectral support theorem.
