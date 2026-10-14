# Actual almost sure centered multicolor trace criterion

## Verified mathematical scope

The main declaration `FreeProbability.Orthogonal.ae_coloredTraceWord_tendsto`
(`6d288ce`, `OrthogonalColoredTraceCriterion.lean`) proves almost sure vanishing
of the actual normalized trace of every fixed nonempty adjacent-alternating word
of orthogonally conjugated centered native matrices. Colors form an arbitrary
finite type; nonadjacent colors may repeat. Native deterministic or random
coefficient data may depend on dimension through different measurable types.

The hypotheses are actual normalized orthogonal Haar marginals, joint
independence of the entire augmented family consisting of the native data and
all Haar coordinates at each dimension, and source-almost-everywhere native
trace-zero and uniform Euclidean operator norm bounds. Independence between
different dimensions is unnecessary. Pairwise independence alone is not the
joint hypothesis. No shorter-word limit or desired freeness premise is assumed.

The normalized trace uses inverse matrix dimension, hence is zero in dimension
zero. Operator norms throughout are literal `Matrix.toEuclideanCLM` norms, not
the default entry norm on matrices.

## Dependency checkpoints

All sources below are new `FreeProbability/RandomMatrix/OrthogonalColoredTrace*.lean`
modules, individually verified and immediately published:

| Commit | Module suffix | Actual achievement |
| --- | --- | --- |
| `60a80f7` | Center | Exact centering, zero trace and operator norm bound, including empty dimension |
| `b69dec5` | Perturbation | Finite ordered product perturbation estimates and trace restoration |
| `58ea88d` | Independence | Whole native-data/other-Haar tuple independent of selected Haar coordinate |
| `f02d2f4` | Segments | True ordered selected-color segmentation; shorter, nonempty alternating runs |
| `fadbbd5` | Words | Exact selected-color trace regrouping and actual word operator norm bounds |
| `aaa8ba6` | VariableData | Genuine single-Haar random-input second moment and almost sure criterion for dimension-varying data types |
| `b7c57bf` | RunData | Measurable grouped native/run data with true source bounds |
| `2ae071e` | RightCenter | Vanishing trace change on centering the other-color runs |
| `84c1de4` | CyclicStep | Conditional selected-color step with explicit shorter-run limits |
| `c1af3a6` | Endpoints | Exact equal-endpoint cyclic merger and fresh coefficient slot |
| `6d288ce` | Criterion | Strong induction discharges every shorter-run limit; full fixed-word almost sure criterion |

The Modes module (`af06c11`) separately supplies actual observable measurability, the
almost sure wrapper deriving coordinate measurability from Haar marginals,
convergence in measure, expected trace convergence by genuine domination, and
simultaneous convergence of any countable collection of fixed words. Bounds
may vary with the word. It does not assert an uncountable common full-measure
set.

## Proof design and repaired approaches

For cyclically alternating words, choose the first color and split into its
native coefficients and nonempty other-color runs. Each run is strictly shorter;
strong induction gives its trace limit. Center the runs and use the actual
independent-input single-Haar criterion; a finite perturbation estimate restores
the original trace.

For equal endpoint colors, rotate the last coefficient to the first and merge
in the order **last times first**. A fresh index in `alpha + Unit` prevents
changing other occurrences of the original coefficient. Center this product:
the resulting word and the nonempty interior are both shorter. The scalar
coefficient is uniformly bounded, so no scalar convergence premise is needed.
Length one is exact native centeredness; the empty word is excluded.

Engineering failures were genuine Lean elaboration issues, not resource
failures: operator norm bounds require an explicit continuous linear map;
`List.ofFn` transports require an explicit composed function; endpoint length
arithmetic requires explicit list length simplification; squeeze majorants use
the parameter named `a`; proof-only section hypotheses in Modes require an
explicit `include`; the dominated convergence API takes integrability before
the domination bound. These were repaired without weakening statements or
raising heartbeat limits.

## Verification and remaining obligations

Each source passed its focused serialized Lake build, direct transitive
standard logical-dependency audit, source-integrity guard and diff checks before
publication. The reviewer approved the full criterion and endpoint order and
nonempty-interior logic. Integration into main and project certification belong
to the coordinator; feature publication alone is not integration.

This is an actual centered-word criterion for Haar-conjugated native families.
A reusable full joint marginal star-law convergence theorem, bare independent
Haar unitary word interfaces, and strong operator norm/spectral convergence
remain separate obligations. Low-dimensional invariant spanning and the
pseudoinverse Haar formula are also not completed by this criterion.
