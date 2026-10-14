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
| `Algebraic.CumulantFreeness`, `Combinatorics.CumulantNaturality` | Full freeness–mixed-cumulant equivalence and all-order adjacent-product formula; cumulants commute with expectation-preserving maps |
| `Algebraic.CumulantUnit`, `CumulantCenter` | Arbitrary-position/order at least two unit-cumulant vanishing, scalar insertion/shift and individual/all-coordinate centering invariance over arbitrary fields and noncommutative algebras |
| `Combinatorics.NoncrossingPairing` | Intrinsic two-element-block pairings, unique partners and their fixed-point-free involution, even size, and existence of an adjacent pair |
| `Combinatorics.NoncrossingInterval` | Every equivalence class has a least representative; every nonempty noncrossing partition has an actual convex interval block, represented by inclusive endpoints |
| `Combinatorics.NoncrossingSingletonInsertion`, `BlockWordTransport` | Arbitrary-position singleton insertion/deletion equivalence, exact actual-block transport, ordered block-word compatibility and singleton contribution/sum factorization |
| `Combinatorics.NoncrossingLattice`, `NoncrossingAdjacent` | Complete refinement lattice with least noncrossing closure, adjacent contraction equivalence/order isomorphism and quotient adjunction |
| `Combinatorics.NoncrossingAdjacentMerge`, `NoncrossingRestriction`, `NoncrossingBlockRefinement`, `BlockRefinementContribution`, `NoncrossingAdjacentFiber` | Exact raw adjacent merges and top-fiber two-block bound; ordered restriction/refinement inverses with actual-block and contribution transport; exact adjacent global/local fiber equivalence and weighted sum factorization |
| `Fock.WordSpace`, `Fock.VacuumState` | Complete Hilbert word model, bounded isometric canonical creation and adjoint annihilation, operator-wide canonical relation, positive normalized vacuum state, self-adjoint centered candidates with variance one and norm at most two |
| `Fock.WickWord`, `Fock.RightOperators` | Polynomial Wick operators generate orthonormal word vectors from the vacuum; vacuum separating for the commutant; unitary word reversal and genuinely commuting left/right semicircular operators |
| `Fock.GeneratedState`, `Fock.ClosedGeneratedState` | Actual restricted positive normalized vacuum states, proved faithful and tracial on both polynomial generated algebra and its operator-norm closure; completeness of the closed generated algebra |
| `Fock.SemicircularNorm`, `Fock.CStarModel` | Exact operator norm two from finite-chain Rayleigh bounds; inherited C-star structure and faithful/tracial probability interfaces; actual subtype generators with norm two, selfadjointness, centering and variance one |
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

## Current checked development state

The latest checked and published integration is `95c414c` on `main`; full builds,
the direct transitive axiom audit and source guard pass for 3794 declarations.
Exact source/integration hashes are preserved in the execution ledger.

`cumulant_ofFn_eq_zero_of_unit`, `cumulant_eq_zero_of_one_mem`,
`cumulant_update_algebraMap`, `cumulant_update_add_algebraMap`, and
`cumulant_update_center` are integrated from worker source `36a6578`. They require
neither freeness nor positivity nor traciality. The adjacent-product identity and full freeness–mixed-cumulant equivalence are
integrated at `e54c402`. Lattice/adjacent-contraction
milestones (`a54a473`, `c84f43d`) are integrated at `3678bca`. Explicit raw-adjacent
merge, whole-word centering, restriction/local-refinement and exact adjacent-fiber
sum proofs are integrated at `1708387`. The fiber theorem concerns arbitrary
block weights, not an assumed cumulant product identity. Ordered fusion and duplicated-block transports are integrated prerequisites of
the all-order adjacent-product theorem. Full refinement/Möbius inversion is
integrated at `168898a`, including arbitrary normalized moment functions and
every partition.

The complete word-Hilbert model has bounded creation/adjoints, canonical operator
relations, a positive vacuum state, Wick vectors and commuting right operators.
`Fock.closedGeneratedVacuumState_isFaithful` and
`Fock.closedGeneratedVacuumState_tracial` are proved properties of the actual
state restricted to the norm-closed generated algebra. No faithful/tracial claim
is made on all bounded Fock operators. No finite/countable generator restriction
is imposed. Fourth moment two and orthogonal two-letter Wick words are checked
usage examples.

Exact norm two and explicit C-star-model compatibility (`f881b61`, `7310a7b`) are
integrated at `2058aab`. Genuine polynomial/closed-marginal freeness and its
faithful-C-star-ambient bridge (`7350c11`, `54fde61`, `de87f86`) are integrated at `041906e`, including repeated nonadjacent colors. The full
joint noncrossing Wick formula and Catalan moments are integrated at `648a7d6`. Arbitrary-vector creation, chosen-Hilbert-basis transport, the completed length
decomposition and a genuine completed-tensor isometry are integrated at
`871fc9f`. The ℓ²(I) levels are genuine completed tensor levels, with literal
tensor creation; original-H tensor coherence and the unconditional full-Fock package are
integrated at `5c2e9cb`. Explicit recursively completed tensor powers and the
unitary onto their Hilbert sum, exact tensor-domain operators and actual
faithful tracial generated tensor C-star model with literal joint Wick/Catalan
laws are integrated at `8334d17`.
The canonical spectral density and full spectrum are integrated at `9a2bdad`.
Every arbitrary orthonormal family in a complete complex Hilbert space now has
a genuine adapted full F(H), including all H, literal completed-tensor creation,
scalar vacuum and grading. Its literal generated C-star state is faithful and
tracial, its fields are free with norm two, and actual joint Wick/Catalan and
explicit spectral density laws hold. `exists_fullFock_semicircular_family`
packages the general existence theorem without a spanning/countability assumption.
Integrated through [PR #5](https://github.com/T1mberland/lean-free-probability-01/pull/5)
at checked main `68de4fe`, with full builds, audits and arbitrary-family usage.
Goals 1, 2, 3 and 6 are certified complete; seven full goals remain open. Equality
with an independently chosen basis model is an optional coherence extension.

Formal R-transform additivity/scaling and the algebraic free CLT are integrated
at `65ea73e`. The CLT gives explicit pairing-moment limits for
centered identically distributed free triangular arrays over real or complex
scalars, allowing varying ambient algebras. Convergence to a supplied
semicircular-cumulant realization is conditional on that realization; no norm
or spectral convergence is claimed. Analytic R-transform identification remains
separate from the formal series theorem. The actual Fock semicircular-cumulant
law and variance-one polynomial/star CLT with that concrete target are integrated
at `cf3c085`, removing the target-existence assumption in that
case.

`cumulant_consecutiveProducts` and its all-partition join-fiber formula are
integrated at `7bb8314` for any supplied finite adjacent-fusion plan. The independent monotone surjective quotient, pointwise sorted fiber-product
identity and corresponding top join-fiber cumulant theorem are integrated at
`18afd0f`. The actual Kreweras greatest compatible complement and free
alternating-moment formula are also integrated at that checkpoint.
Genuine positive-degree complementary block count, raw connectivity and the
actual boxed product-cumulant formula are integrated via
[PR #1](https://github.com/T1mberland/lean-free-probability-01/pull/1) at `76af384`.
`FreelyIndependent.cumulant_prod_eq_kreweras_sum` and its repeated-product
variant require no trace, positivity or commutation assumptions. The full
build, kernel audit, integrity guard and boxed usage example pass on main.
Every literal Goal 1 subtarget is covered; rotation/closed-form μ identities
are optional extensions. Analytic S multiplication remains Goal 7.

The actual algebraic tensor free difference quotient satisfies the full
noncommutative polynomial Leibniz rule. Polynomial and matrix-valued polynomial
integration by parts in the actual faithful tracial Fock C-star state are
integrated at `ea6149a`. Actual one-generator resolvent IBP on every resolvent-set point and its Cauchy
quadratic equation are integrated at `7386526`. Generated-algebra full domain
and inverse compatibility, restricted-state resolvent IBP and actual unique
lower-half-plane Cauchy branch are integrated through
[PR #4](https://github.com/T1mberland/lean-free-probability-01/pull/4) at `0f40468`.
Entire exponential IBP for every scalar and finite-matrix polynomial, with
actual norm-convergent exponentials and unrestricted complex parameter, is
integrated through [PR #8](https://github.com/T1mberland/lean-free-probability-01/pull/8)
at `9715c11`. Actual full polynomial/matrix resolvent IBP, including the own generated-state
interfaces, is integrated through
[PR #10](https://github.com/T1mberland/lean-free-probability-01/pull/10) at `287bcf7`.
Norm-convergent analytic-series extensions for scalar/matrix polynomials and
closed C-star states are integrated through [PR #11](https://github.com/T1mberland/lean-free-probability-01/pull/11)
at checked main `5706254`. Explicit value and derivative absolute bounds and an
infinite geometric-series example are kernel verified. Full build 3634,
Verification 3637, transitive audit 3497 and source guard pass, certifying Goal 3.

Actual spectral probability measures are constructed from positive CFC
functionals using Riesz representation; real continuous-functional-calculus
expectations have their integral representation. Faithfulness gives actual
support equal to real spectrum, without traciality. These declarations are
integrated at `9ca8caa`. General complex/Cauchy representation and exact spectral-law determinacy by
all power moments are integrated at `ab262d5`;
bounded-moment weak spectral-law and pointwise all-nonreal Cauchy convergence
are integrated through [PR #2](https://github.com/T1mberland/lean-free-probability-01/pull/2)
at `427f72b`. Full main build/audits and non-exterior Fock usage pass for 2636
declarations, certifying Goal 6. The actual canonical Fock spectral law is identified with the independently
proved semicircle density, and its full support/operator spectrum is `[-2,2]`,
integrated through [PR #3](https://github.com/T1mberland/lean-free-probability-01/pull/3)
at checked main `9a2bdad`. The arbitrary-family realization is published and
awaits its integration checkpoint.

A quantitative non-iid free triangular-array CLT is integrated at `8cb664e`: each entry is centered, averaged second moments converge, and each
fixed higher-order marginal cumulant has a uniform bound. Normalized power
moments then converge to the explicit pairing sequence. These are sufficient
quantitative assumptions, not an optimal Lindeberg condition or a spectral limit.

The actual finite-matrix Fock model has a coefficient-range conditional
expectation, covariance positive at every matrix amplification, genuine scalar
state complete positivity, all-order ordered/interspersed Wick laws and actual
covariance moment recursion. These are integrated through
[PR #6](https://github.com/T1mberland/lean-free-probability-01/pull/6) at `a1f942b`.
The actual affine matrix resolvent now satisfies
`m(z)^-1=zI-C0-eta(m(z))` on its WHOLE actual resolvent set, including every
nonreal point for Hermitian coefficients, integrated through
[PR #9](https://github.com/T1mberland/lean-free-probability-01/pull/9) at `e7f693e`.
The proof uses actual CStarMatrix inverses and determinant invertibility, never
formal-series substitutes. General arbitrary-base CP covariance realization,
half-plane/exterior properties, physical-branch uniqueness and entrywise matching
remain separate Goal 4 obligations.

For an actual self-adjoint idempotent p, `spectralMeasure_projection` proves
its actual law is `(1-alpha)delta0+alpha delta1`, alpha=Re(phi(p)) in [0,1].
The corresponding actual S germ uses the same alpha and the precise nonzero
first-moment domain. Integrated through
[PR #7](https://github.com/T1mberland/lean-free-probability-01/pull/7) at `8d38c42`.
This proves the projection piece; free-positive S multiplication and projection
product support/edge remain open.

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
  integrity guard passed. The latest integrated transitive audit covers 3794 library declarations
  and permits only `propext`, `Classical.choice`, and `Quot.sound`.
- GitHub Actions repeats the build, source guard, and transitive audit.
- The analytic transform milestones were integrated through
  [PR #1](https://github.com/T1mberland/lean-free-probability/pull/1). Verified
  milestones and feature branches are published promptly; repository workflow
  is recorded in [AGENTS.md](AGENTS.md).

## Next mathematical priorities

The exact dependency queue, isolated assignments, source hashes and integration
checks are maintained in [docs/EXECUTION_QUEUE.md](docs/EXECUTION_QUEUE.md).
Goals 1, 2, 3 and 6 are certified complete; seven goals remain open.

1. Integrate published actual matrix half-plane/exterior, normalized analytic
   physical-branch and spectral-edge results; construct general arbitrary-base
   completely positive covariance and entrywise-model comparison.
2. Construct positive free-product law and S multiplication, then projection-product
   support and physical spectral edge. The actual projection law is integrated.
3. Integrate general homogeneous Wick norm bounds and reverse-overlap products;
   develop second quantization and completely positive OU.
4. Develop conditional L² projections/subordination, noncommutative integration,
   noncommutative Lᵖ/entropy, and Haar freeness by distinct convergence modes.

Matrix and ReLU examples remain verified supporting tools. Their rational
critical-point calculations do not establish a spectral-support theorem.

## Recent Wick and matrix physical-branch checkpoints

[PR #12](https://github.com/T1mberland/lean-free-probability-01/pull/12) integrated
actual normal ordering, reversed-overlap Wick multiplication and the general
finite homogeneous Haagerup bound at checked main `be0f163`. Full build 3644,
Verification 3647, audit 3594 and source guard pass. Declaration
`Fock.norm_homogeneousWick_le_degree_mul_vacuumNorm` bounds actual operator norm
by (degree+1) times actual vacuum norm for arbitrary color sets. Goal 10 remains
open beyond its Wick prerequisite.

Matrix physical theory through worker `6692fe8` is integrated through
[PR #13](https://github.com/T1mberland/lean-free-probability-01/pull/13) at checked
main `3f6b367` (full 3656, Verification 3659, audit 3707, source guard): strict negative imaginary part, actual analyticity/derivative and
normalization at infinity, uniqueness of normalized analytic upper-half-plane
Dyson branches, full real-right-exterior positive definiteness and differentiated
Lyapunov identities. No fixed-point uniqueness for all matrices at one argument
is claimed. General arbitrary-base CP covariance and entrywise comparison remain
open. Core edge variational `094e84d` is integrated through
[PR #14](https://github.com/T1mberland/lean-free-probability-01/pull/14) at checked main
`06f8254` (full 3661, Verification 3664, audit 3770 and source guard).
It identifies the actual real-spectrum top edge with the infimum over ALL positive
definite Z of the actual largest eigenvalue of C₀+Z+Σ Cᵢ Z⁻¹ Cᵢ. No positivity
or commutation assumptions are imposed on the Hermitian coefficients.
Positive-state/density bounds (`4246351`, `ae23f1c`) are integrated through
[PR #15](https://github.com/T1mberland/lean-free-probability-01/pull/15) at checked
main `5131911` (full 3663, Verification 3666, audit 3784 and source guard).
A singular-density example gives an actual edge lower bound of three.
Actual full-right-exterior spectral-gap bounds are integrated through
[PR #16](https://github.com/T1mberland/lean-free-probability-01/pull/16) at checked
main `95c414c` (full 3664, Verification 3667, audit 3794 and source guard).
Quantitative finite Fock approximation, singular edge limits and deterministic
edge-subspace results remain open for Goal 5.

Generic topological closure freeness (`9409551`) is published and reviewed,
undergoing integration. Continuous expectation and topological algebra operations
suffice, without positivity, traciality, norms or completeness. Actual near-zero
Neumann-inverse membership is the next missing analytic S-product dependency.
