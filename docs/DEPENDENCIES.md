# Mathematical target audit and dependencies

Targets are the concrete theorems in [PROJECT_GOAL.md](PROJECT_GOAL.md). This audit
compares actual existing declarations with those targets. Open entries are
obligations, not assumptions that count as established results.

See [EXECUTION_QUEUE.md](EXECUTION_QUEUE.md) for current isolated worker
assignments, verification checkpoints, design decisions and successive tasks.

## Audit of the eleven goals

| Goal | Existing reusable results | Earliest missing dependencies and remaining target |
| --- | --- | --- |
| 1. Cumulant calculus — complete | All-order freeness iff mixed cumulants vanish; inversion, multilinearity/naturality; unit/scalar/centering and adjacent/interval-product calculus; actual refinement lattice and Möbius inversion; pairings, Catalan counts and interval blocks; greatest Kreweras complement, exact block counts/raw connectivity; actual alternating moments and boxed product cumulants | Certified after PR #1 merge and full main checks at `76af384`. Rotation/closed-form μ are optional; analytic S multiplication belongs to Goal 7 |
| 2. Fock semicircular systems — complete | Complete full F(H) for arbitrary complete complex H and arbitrary ON family without spanning/countability assumptions; original-H literal completed tensor creation/adjoints, scalar vacuum and grading; canonical relations and self-adjoint/centered/variance-one/norm-two fields; actual faithful tracial literal generated C-star state, freeness and joint Wick/Catalan; explicit semicircle density and exact operator spectrum | Certified after PR #5 and full main checks at `68de4fe`. Independently chosen-model unitary coherence is optional |
| 3. Free integration by parts | All-degree actual word IBP; polynomial/joint-distribution interfaces | Actual tensor polynomial derivative with full Leibniz, polynomial and finite-matrix IBP are integrated. Actual single-generator resolvent IBP and Cauchy quadratic on the full resolvent set integrated; general polynomial resolvent, matrix analytic and exponential extensions remain |
| 4. Operator-valued Dyson | `ConditionalExpectation`, bimodule identities, algebraic amalgamated freeness, mixed second moment | Completely positive covariance and operator-valued semicircular realization/Wick recursion; amplified tracial expectation and Dyson proof, physical branch, entrywise comparison |
| 5. Spectral-edge formula | Matrix operator-norm, positivity-order and Hermitian resolvent tools | Faithful semicircular pencil, spectral endpoint and Dyson theory; variational identity, exterior derivative/Lyapunov identities, finite Fock truncation bounds and edge certificates |
| 6. Spectral distributions — complete | Actual compact spectral probability measures; real/complex continuous CFC integral representation; faithful support=spectrum; whole-resolvent Cauchy spectral integral; algebraic power/polynomial compatibility and equality iff power moments; bounded moment convergence gives actual weak laws and every pointwise nonreal Cauchy limit; existing moment/local inverse/S-germ APIs | Certified after PR #2 and full main checks at `427f72b`. Norm boundedness is explicit; uniform or derivative convergence is not claimed. S multiplication remains Goal 7 |
| 7. Multiplicative convolution | `sTransform_idempotent_eventually`, `sTransform_zero`, transform scaling and naturality; rational projection-product parameter calculus | Positive free realizations and spectral laws; convolution well-definedness and S-transform product theorem; projection measure, physical branch and support identification. Rational critical points alone prove no spectral edge |
| 8. Conditional subordination | Algebraic conditional expectations and explicit nonzero-mean inverse-transform domain | Tracial noncommutative L² and von Neumann conditional expectation; analytic multiplicative subordination, exterior continuation, enlarged conditioning and annihilating-projection specialization |
| 9. Haar freeness | Orthogonal Haar probability/invariance, low-order moments, spherical/Gaussian laws, concentration and almost-sure array convergence; algebraic joint moments | Abstract Haar-unitary star-law and free conjugation; general orthogonal pairing integration and joint asymptotic estimates. Separate expected, probability, almost-sure and strong convergence interfaces |
| 10. Free Gaussian OU/entropy | General positive expectations; actual polynomial Wick vacuum vectors with `Fock.vacuumExpectation_wick_star_mul` orthogonality | Wick contractions/norm bounds and second quantization; complete positivity and normal OU extension; noncommutative Lᵖ, entropy, data processing, lower semicontinuity and dimension-independent regularization |
| 11. Follow-up foundations | Scalar and algebraic operator-valued probability, cumulants, analytic transform tools | Formal R-additivity and algebraic moment free CLT integrated; concrete variance-one faithful tracial Fock target integrated. Quantitative non-iid moment CLT integrated under explicit cumulant bounds and averaged variance convergence. Positive free products, analytic additive convolution/R identification, operator-valued cumulants, second-order/annular theory and genus expansions remain |

Goals 1, 2 and 6 are certified complete at checked main `76af384`, `68de4fe`
and `427f72b`; the other eight targets remain open. Supporting interfaces alone do not certify a target. See
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
