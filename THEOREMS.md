# Theorem overview

Selected entry points, not an exhaustive list or a completion roadmap. Names
below are relative to `FreeProbability`; links lead to their source modules.
Read the full Lean statement for all parameters and hypotheses. [INDEX.json](INDEX.json)
is the generated catalogue of named source declarations and module imports.

## Probability spaces and freeness

The algebraic `ProbabilitySpace` is a normalized linear functional; positivity,
faithfulness and traciality are separate structures or assumptions.

- [`ProbabilitySpace`](FreeProbability/Algebraic/ProbabilitySpace.lean)
- [`freelyIndependent_iff_mixedCumulantsVanish`](FreeProbability/Algebraic/CumulantCharacterization.lean)

## Noncrossing partitions and cumulants

Constructive moment–cumulant inversion and noncrossing Möbius inversion.

- [`moment_cumulant_formula_all`, `freeCumulant_unique_of_moment_formula`](FreeProbability/Combinatorics/Cumulant.lean)
- [`cumulant_eq_mobius_sum`](FreeProbability/Combinatorics/NoncrossingMobius.lean)

## Formal R-transform and free central limit theorems

Formal power-series additivity and triangular-array moment/cumulant convergence,
with centered freeness, variance convergence and higher-cumulant bounds. These
are not general analytic additive-convolution or strong-convergence statements.

- [`FreelyIndependent.formalRTransform_sum`](FreeProbability/Algebraic/FormalRTransform.lean)
- [`freeCLT_triangular_cumulants`, `freeCLT_triangular_pairingMoments`](FreeProbability/Algebraic/CumulantTriangularCLT.lean)

## Full Fock semicircular systems

Orthonormal families in complete complex Hilbert spaces, with semicircular
fields and a faithful tracial state on the generated model. Faithfulness is not
asserted on all bounded Fock operators.

- [`Fock.exists_fullFock_semicircular_family`](FreeProbability/Fock/OrthonormalFamilySpectrum.lean)
- [`Fock.tensorClosedVacuumState_joint_free_wick`](FreeProbability/Fock/TensorJointLaw.lean)

## Wick formulas and integration by parts

Concrete Fock and closed-generated-state polynomial and resolvent identities.
Resolvent statements retain their invertibility/domain assumptions.

- [`Fock.joint_free_wick`](FreeProbability/Fock/WickFormula.lean)
- [`Fock.closedGeneratedVacuumState_polynomial_integrationByParts`](FreeProbability/Fock/PolynomialIntegrationByParts.lean)
- [`Fock.closedGeneratedVacuumState_matrixPolynomial_resolvent_integrationByParts`](FreeProbability/Analytic/FockPolynomialResolventMatrixCStar.lean)

## Spectral probability measures

Spectral measures for self-adjoint elements in C-star probability spaces.
Support equals spectrum under faithfulness. Weak convergence from power moments
requires the stated norm bounds, and does not imply operator-norm convergence.

- [`spectralMeasure_support_eq_spectrum`](FreeProbability/Analytic/SpectralMeasureSupport.lean)
- [`tendsto_spectralProbabilityMeasure_of_bounded_power_moments`](FreeProbability/Analytic/SpectralMeasureConvergence.lean)

## Multiplicative S-transform and projection products

Analytic S-transform multiplication near zero for given free elements with
nonzero first moments. Sharp law-support edges for products of at least two
free half-projections require traciality; the law edge does not require
faithfulness. Universal free-product realization is not asserted here.

- [`StarProbabilitySpace.sTransform_mul_eventually`](FreeProbability/Analytic/MultiplicativeResolventS.lean)
- [`StarProbabilitySpace.iteratedHalfProjection_law_support_isGreatest`, `StarProbabilitySpace.iteratedHalfProjection_law_right_edge`](FreeProbability/Analytic/ProjectionProductSupportLower.lean)

## Conditional expectations and amalgamated freeness

Algebraic bimodule conditional expectations and freeness over a subalgebra,
not general normal conditional expectations or analytic subordination.

- [`ConditionalExpectation`, `FreelyIndependentOver`, `FreelyIndependentOver.expectation_mul`](FreeProbability/OperatorValued/ConditionalExpectation.lean)

## Matrix Dyson equations and spectral edges

The concrete finite-matrix Fock model, with Hermitian coefficients. The edge
formula does not require positive or commuting coefficients. Arbitrary-base
operator-valued covariance realization is outside these statements.

- [`Fock.operatorMatrixArgumentCauchy_inverse_dyson`](FreeProbability/OperatorValued/MatrixArgumentDyson.lean)
- [`Fock.operatorMatrixPencilTopEdge_variational`](FreeProbability/OperatorValued/MatrixEdgeVariational.lean)

## Orthogonal Haar integration and asymptotics

Stable-range inverse-Gram integration and almost-sure centered trace decay for
centered, uniformly operator-norm-bounded deterministic inputs and Haar marginals.
The latter does not require independence across dimensions. General multiple-Haar
joint asymptotic freeness and strong convergence are not claimed.

- [`Orthogonal.entryMoment_eq_weingarten_delta_sum`](FreeProbability/RandomMatrix/OrthogonalWeingarten.lean)
- [`Orthogonal.ae_centered_traceWord_tendsto`](FreeProbability/RandomMatrix/OrthogonalMultiTraceAlmostSure.lean)

## Free Ornstein–Uhlenbeck analysis

Concrete von Neumann OU normality and semigroup laws, the full-Fock number
operator domain, and damped Wick bounds. These do not constitute a complete
entropy or noncommutative L1 theory.

- [`Fock.ouVonNeumannTimeCP_isLUB`](FreeProbability/Fock/OrnsteinUhlenbeckVonNeumannNormality.lean)
- [`Fock.ouVonNeumannTimeCP_add`](FreeProbability/Fock/OrnsteinUhlenbeckVonNeumannVacuumSemigroup.lean)
- [`Fock.numberOperatorDomain`, `Fock.numberOperator`](FreeProbability/Fock/OrnsteinUhlenbeckNumberOperatorDomain.lean)
- [`Fock.norm_dampedWickReconstruction_apply_le`](FreeProbability/Fock/WickDampedReconstructionBounds.lean)

## Finite-matrix resolvents and perturbations

Finite real Hermitian matrix statements, with explicit positivity and exterior
resolvent assumptions as applicable. Use the Euclidean operator-norm convention.

- [`hermitian_resolvent_eq`, `rankOne_norm_le_iff_resolvent_le`, `rankOne_exterior_eigenvalues_unique`](FreeProbability/Matrix/HermitianResolvent.lean)
