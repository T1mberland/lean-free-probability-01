# Mathematical target audit and dependencies

Targets are the concrete theorems in [PROJECT_GOAL.md](PROJECT_GOAL.md). This audit
compares actual existing declarations with those targets. Open entries are
obligations, not assumptions that count as established results.

See [EXECUTION_QUEUE.md](EXECUTION_QUEUE.md) for current isolated worker
assignments, verification checkpoints, design decisions and successive tasks.

## Audit of the eleven goals

| Goal | Existing reusable results | Earliest missing dependencies and remaining target |
| --- | --- | --- |
| 1. Cumulant characterization | Recursive inversion, multilinearity/naturality, mixed vanishing implies freeness; singleton/interval/pairing fundamentals; singleton sum transport; all-order unit/scalar/full-centering calculus; NC lattice, adjacent contraction/raw merge and exact local/global refinement fibers with contribution sums | Full adjacent-product identity and freeness equivalence integrated; general refinement factorization and actual Möbius inversion undergoing integration; multi-product formulas and Kreweras remain. Pairing decomposition/counting integrated |
| 2. Fock semicircular systems | Complete Hilbert word model, bounded canonical creation/adjoints and canonical relation; positive vacuum state, selfadjointness/centering/variance one and exact norm two; Wick vacuum vectors/right commutation; actual faithful tracial C-star generated model | General completed tensor-power identification and arbitrary-vector creation; semicircular spectral law. Genuine closed-generator freeness is integrated; joint Wick formula and Catalan moments integrated |
| 3. Free integration by parts | Word products and polynomial/joint-distribution interfaces | All-degree actual word integration-by-parts integrated. Noncommutative polynomial tensor bimodule derivations, matrix amplification and analytic convergence extensions remain |
| 4. Operator-valued Dyson | `ConditionalExpectation`, bimodule identities, algebraic amalgamated freeness, mixed second moment | Completely positive covariance and operator-valued semicircular realization/Wick recursion; amplified tracial expectation and Dyson proof, physical branch, entrywise comparison |
| 5. Spectral-edge formula | Matrix operator-norm, positivity-order and Hermitian resolvent tools | Faithful semicircular pencil, spectral endpoint and Dyson theory; variational identity, exterior derivative/Lyapunov identities, finite Fock truncation bounds and edge certificates |
| 6. Spectral distributions | Positive continuous states, Cauchy resolvents, geometric moment expansions, half-plane properties, equality and convergence from bounded moments | Spectral probability measures from continuous functional calculus; faithfulness gives support–spectrum equality; integral transform representation. Existing moment-transform and analytic S-transform implementations should be reused |
| 7. Multiplicative convolution | `sTransform_idempotent_eventually`, `sTransform_zero`, transform scaling and naturality; rational projection-product parameter calculus | Positive free realizations and spectral laws; convolution well-definedness and S-transform product theorem; projection measure, physical branch and support identification. Rational critical points alone prove no spectral edge |
| 8. Conditional subordination | Algebraic conditional expectations and explicit nonzero-mean inverse-transform domain | Tracial noncommutative L² and von Neumann conditional expectation; analytic multiplicative subordination, exterior continuation, enlarged conditioning and annihilating-projection specialization |
| 9. Haar freeness | Orthogonal Haar probability/invariance, low-order moments, spherical/Gaussian laws, concentration and almost-sure array convergence; algebraic joint moments | Abstract Haar-unitary star-law and free conjugation; general orthogonal pairing integration and joint asymptotic estimates. Separate expected, probability, almost-sure and strong convergence interfaces |
| 10. Free Gaussian OU/entropy | General positive expectations; actual polynomial Wick vacuum vectors with `Fock.vacuumExpectation_wick_star_mul` orthogonality | Wick contractions/norm bounds and second quantization; complete positivity and normal OU extension; noncommutative Lᵖ, entropy, data processing, lower semicontinuity and dimension-independent regularization |
| 11. Follow-up foundations | Scalar and algebraic operator-valued probability, cumulants, analytic transform tools | Formal R-additivity and algebraic moment free CLT integrated; concrete variance-one faithful tracial Fock target integrated. Positive free products, analytic additive convolution/R identification, operator-valued cumulants, second-order/annular theory and genus expansions remain |

No major target is certified complete by these supporting interfaces. See
[PROGRESS.md](../PROGRESS.md) for verified declarations and their current scope.

## First development path

Refinement and interval-block combinatorics support noncrossing deletion,
contraction and insertion maps. Those maps support unit insertion and
adjacent-product cumulant identities, then the missing direction of the freeness
characterization. Finite lattice structure and its incidence algebra are needed
for the separate Möbius-inversion goal; recursive inversion is already available
and should not be replaced.

Full Fock space is a separate first-priority path. Establish its Hilbert-space
model and bounded creation operators before claiming semicircular moments,
faithfulness or traciality. The vacuum state on all bounded Fock operators is not
a substitute for its faithful tracial restriction to the semicircular algebra.

```mermaid
graph TD
  NC[Noncrossing refinement and interval blocks] --> CALC[Unit insertion and adjacent products]
  CALC --> CUM[Full cumulant characterization of freeness]
  NC --> MOB[Lattice incidence algebra and Mobius inversion]
  FOCK[Hilbert tensor powers and full Fock space] --> CREATE[Bounded creation and annihilation]
  CREATE --> WICK[Semicircular joint Wick formula]
  WICK --> TRACE[Faithful tracial generated algebra]
  WICK --> IBP[Free difference quotients and integration by parts]
  WICK --> OV[Operator-valued semicircular Wick recursion]
  OV --> DYSON[Dyson equation and physical branch]
  TRACE --> SPEC[Spectral probability measures]
  SPEC --> EDGE[Spectral-edge variational certificates]
  DYSON --> EDGE
  TRACE --> CONV[Positive free convolution and S multiplication]
  CUM --> CONV
  CONV --> PROJ[Projection-product spectral law and edge]
  CONV --> SUB[Conditional multiplicative subordination]
  L2[Tracial L2 and normal conditional expectations] --> SUB
  HAAR[Haar-unitary law and orthogonal integration] --> ASYM[Joint asymptotic freeness by convergence mode]
  CUM --> ASYM
  WICK --> OU[Wick contractions and completely positive OU]
  TRACE --> LP[Noncommutative Lp and normal entropy]
  OU --> ENT[Dimension-independent conditional entropy bound]
  LP --> ENT
```

[Sources and attribution](SOURCES.md) records dependency provenance. Existing
matrix and ReLU modules are examples and reusable tools, not application targets.
