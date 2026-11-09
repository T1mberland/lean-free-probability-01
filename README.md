# Free Probability in Lean 4

[![Lean verification](https://github.com/T1mberland/lean-free-probability-01/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/T1mberland/lean-free-probability-01/actions/workflows/lean.yml)

A reusable, kernel-checked foundation for free probability in Lean 4. The library
is intended for researchers and contributors building formal probability,
operator-algebra, and random-matrix arguments.

The targets are concrete reusable theorems: cumulant characterization of freeness,
Fock-space semicircular systems, free Wick and integration-by-parts formulas,
operator-valued Dyson equations, spectral measures and edge formulas, free
convolution and subordination, Haar freeness, and free Gaussian analysis.
The full mathematical scope is in [docs/PROJECT_GOAL.md](docs/PROJECT_GOAL.md);
the [dependency audit](docs/DEPENDENCIES.md) records implemented interfaces and
remaining work. Earlier development records are retained in the
[archive](docs/archive/README.md).

## Available foundations

- Normalized noncommutative probability spaces, positive expectations, free
  independence, joint star-distributions, and moment convergence.
- Noncrossing partitions, constructive free cumulants, moment–cumulant inversion,
  and cumulant multilinearity.
- Conditional expectations and algebraic freeness with amalgamation.
- Cauchy transforms, convergent moment expansions, analytic inverse moment
  transforms, and S-transforms with an explicit nonzero first-moment domain.
- Orthogonal Haar probability, exact low-order moments, spherical laws, and
  concentration and almost-sure convergence tools.
- Positive matrix traces, Hermitian resolvents, and finite-rank perturbations.

The [dependency graph](docs/DEPENDENCIES.md) distinguishes verified interfaces
from unfinished theory. [ReLU examples](FreeProbability/Applications/ReLU)
illustrate the matrix and Haar-probability tools.

## Build

Install elan, then run:

```sh
lake exe cache get
lake build
lake build Verification
```

Lean and mathlib are pinned; `lake-manifest.json` locks transitive dependencies.
The cache is an optimization: all project proofs are checked by Lean, and
dependencies can also be rebuilt from source.

## Small example

```lean
import FreeProbability

open FreeProbability

example {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    (φ : ProbabilitySpace 𝕜 A) (a : A) :
    φ.expectation (φ.center a) = 0 :=
  φ.expectation_center a
```

Individual modules can also be imported directly, such as
`FreeProbability.Algebraic.ProbabilitySpace`.

## Mathematical conventions

`ProbabilitySpace 𝕜 A` is the algebraic layer: a unital linear functional on an
associative unital algebra over a field. Positivity, star compatibility,
faithfulness, and traciality are additional structures or properties.
Scalar-valued free independence is defined for families of unital subalgebras.

Analytic matrix statements explicitly select the Euclidean operator norm
(`Matrix.Norms.L2Operator` or an equivalent operator model). Algebraic matrix
identities and compactness in the entrywise topology do not assert operator-norm
convergence.

## Contributing and sources

Use focused feature branches and reviewable changes. Before
integration, run the build, source integrity guard, and transitive axiom audit:

```sh
lake build
python3 scripts/check_integrity.py
lake env lean Verification/Axioms.lean
```

See [CONTRIBUTING.md](CONTRIBUTING.md) for build and review expectations and
[docs/SOURCES.md](docs/SOURCES.md) for public references and attribution.

## Documentation and licensing

The [documentation index](docs/README.md) separates the mathematical roadmap,
proof-design notes and historical records. Proof-design notes can describe open
work; only the corresponding Lean declarations establish formal results.

Third-party attribution and the included Apache 2.0 text are preserved. This
repository does not yet specify a project-wide license; the third-party license
file alone does not license the entire project. A project-wide license needs to
be chosen by the maintainers before presenting this as freely reusable code.
