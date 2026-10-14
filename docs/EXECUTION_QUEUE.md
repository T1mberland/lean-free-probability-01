# Autonomous execution ledger

The eleven target statements are in [PROJECT_GOAL.md](PROJECT_GOAL.md). The
verified dependency audit is in [DEPENDENCIES.md](DEPENDENCIES.md). An active task
is not a verified result; a feature-branch result is not integrated until the
integration checkout passes the full build and audits.

## Verified integration baseline

- Baseline commit: `faf32e8` (`chore: establish verified free probability baseline`).
- Published branches: `main`, `feat/verified-baseline` on
  `T1mberland/lean-free-probability-01`.
- Lean 4.34.1 and mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` remain pinned.
- Baseline integration checks: `lake build` (3404 jobs), `lake build Verification`
  (3406 jobs), direct transitive axiom audit (954 declarations), source guard.
- At the baseline, all eleven goals remained open. Existing results and their scope are listed in
  the dependency audit; none is considered complete merely by having a module.

## Goal status and dependency-aware queue

Latest checked integration: `287bcf7`, published on `main` through
[PR #10](https://github.com/T1mberland/lean-free-probability-01/pull/10). Full builds
3629/3632 jobs, source guard and transitive audit of 3337 declarations pass.
Goals 1, 2 and 6 are certified complete; eight full goals remain open. Actual
matrix covariance/Wick/recursion and entire exponential IBP are published and
queued for sequential integration. Historical checkpoints retain their scope.

| Goal | Status | Earliest work and dependency |
| --- | --- | --- |
| 1. Cumulant calculus | Complete on checked main `76af384`, PR #1 | All requested calculus and combinatorial subtargets verified; optional rotation/closed μ and Goal 7 S multiplication are separate |
| 2. Full Fock systems | Complete on checked main `68de4fe`, PR #5 | All literal arbitrary-H/ON-family structure/state/Wick/spectral subtargets verified; independently chosen-model coherence optional |
| 3. Free integration by parts | Active proof path selected | Actual polynomial tensor derivative/Leibniz and polynomial/matrix IBP integrated; analytic extensions remain |
| 4. Operator-valued Dyson | Blocked on operator-valued realization | Completely positive covariance, amplified moments and Wick recursion precede Dyson and physical branch |
| 5. Spectral edges | Blocked on goals 2, 4 and 6 | Faithful pencils and spectral/Dyson theory precede variational identity and certificates |
| 6. Spectral distributions | Complete on checked main `427f72b`, PR #2 | Actual measures/CFC/support/Cauchy/moment compatibility and bounded convergence are integrated; uniform/derivative convergence is separate |
| 7. Multiplicative convolution | Blocked on goals 1, 2 and 6 | Positive realizations, S-transform multiplication and actual spectral laws; rational critical-point computations are supporting special cases |
| 8. Conditional subordination | Blocked on goals 6 and 7 and noncommutative L² | Normal conditional expectations, analytic subordination, then exterior continuation and projection specialization |
| 9. Haar freeness | Independent algebraic groundwork ready | Haar-unitary star law and free conjugation; general orthogonal pairing integration precedes asymptotic trace estimates |
| 10. OU and entropy | Wick/tracial prerequisites integrated; OU construction ready | Wick basis/contractions, completely positive second quantization, normal noncommutative Lᵖ and entropy precede dimension-independent bound |
| 11. Follow-up milestones | Active; formal R and algebraic CLT integrated | Formal R and moment CLT with actual unitvariance target integrated; positive free products, analytic convolution, operator-valued/annular/genus theory remain |

## Active assignments and isolation

| Role | Branch / worktree | Exclusive ownership | Current milestone |
| --- | --- | --- | --- |
| Coordinator | `main`, `/home/user/Projects/lean-free-prob` | Central imports, verification, configuration, ledgers, integration | Review, integrate verified branches sequentially, publish, select successive milestones |
| Worker A (`cumulants`) | `feat/operator-valued-matrix`, `/home/user/Projects/lean-fp-cumulants` | New `OperatorValued/Matrix*.lean`; completed cumulant feature preserved | Actual matrix conditional expectation, all finite covariance amplification positivity, matrix semicircular realization |
| Worker B (`fock`) | `feat/wick-contractions`, `/home/user/Projects/lean-fp-fock` | New `Fock/WickProduct*.lean`, `Fock/WickNorm*.lean`; published analytic features preserved | Actual Wick normal order, word norm bounds and reverse-overlap contractions |
| Reviewer | Read-only integration checkout | No writes, Git mutations or builds | Audit statements, prerequisites and precise scope |

Source checkouts and `.lake` directories are separate. All heavy builds and Lean
checks use `/tmp/lean-fp-build.lock`; full builds occur at integration checkpoints.
Workers publish each commit immediately and never merge or edit central files.

## Design decisions and approaches to avoid

1. Preserve the existing recursive cumulant inversion and multilinearity. A bare
   noncrossing sum over labeled words is not automatically an algebraic state:
   it must respect unit insertion and adjacent products. Mixed-moment uniqueness
   alone therefore does not bypass those missing combinatorial identities.
2. Reverse freeness strategy: use unit insertion to center mixed cumulants;
   alternating centered words use freeness and the singleton-block theorem;
   nonalternating words require an adjacent-product identity and induction.
   This is a proposed proof path, not a verified theorem.
3. Mathlib's normed algebraic Hilbert tensor product is not generally complete.
   Complete tensor powers before forming the full Hilbert direct sum. A complete
   `lp (fun _ : List I => ℂ) 2` word realization is a genuine model for an orthonormal
   one-particle basis; its identification with general tensor Fock space remains
   a separate mathematical obligation.
4. Creation via the linear isometry induced by an orthogonal family of word
   embeddings can avoid duplicated summability proofs. Its adjoint is the
   annihilation operator. These are implementation directions pending checks.
5. Traciality must concern the algebra generated by the selected orthonormal
   semicircular family (or an explicit real form). Generating by `s(h)` for every
   vector of a complex Hilbert space generally fails traciality: `e` and `i e`
   already give unequal reversed second moments. Faithfulness on all bounded
   Fock operators is false; commuting right operators and a dense vacuum orbit
   are a candidate proof for the intended generated-algebra restriction.

## Next independent tasks

### Publication infrastructure note

GitHub currently advertises `feat/verified-baseline` as its default branch.
`main` is nevertheless the explicit checked integration branch and is published
after every checkpoint. The available GitHub connector has no repository-settings
mutation, and no browser surface is available to change the default. This does
not block commits, pushes, or mathematical work; no credentials were invented.

### Checked integration checkpoint: pairing fundamentals

`6ade2b4` is checked and published on `main`; worker source milestone `ab82d17`
was integrated through `f30dffe`. The module `Combinatorics.NoncrossingPairing`
provides `NoncrossingPartition.IsPairing.card_eq_twice`, `.even`,
`.existsUnique_partner`, `.exists_adjacent`, and
`NoncrossingPairing.partner_partner`, `.rel_iff`, `.not_nonempty_of_odd`.
Full library and verification builds, the direct audit and the source guard pass;
the audit covers 970 declarations. An odd weighted pairing-sum example is checked.

Published next milestones awaiting integration: interval blocks (`4df3696`) and
complete word-Fock creation/adjoint operators with canonical relation and first
two vacuum moments (`778c6b0`). Neither is recorded as integrated yet.

### Checked integration checkpoint: interval blocks

`f419315` is checked and published on `main`; worker source `4df3696` was
integrated through `dd6d9bb`. Declarations:
`NoncrossingPartition.exists_least_representative`, `.exists_interval_block`,
and `.exists_Icc_block`. Full builds, direct audit and source guard pass for
973 declarations. Worker A is pursuing restriction/deletion calculus next.

### Checked integration checkpoint: word-Fock operators and vacuum state

`9f85ea8` is checked and published on `main`; worker sources `778c6b0` and
`6291082` were integrated through `68eeebb` and `a87b51f`. The modules
`Fock.WordSpace` and `Fock.VacuumState` prove the operator canonical relation,
positive normalized vacuum state, creation/annihilation norm one, selfadjointness,
centering, covariance and semicircular norm at most two. Full builds, direct audit
and source guard pass for 1039 declarations. A fourth-moment-two example is
checked without assuming a full distribution. Generated trace/faithfulness,
freeness, exact norm two and general tensor identification are not yet integrated.

### Checked integration checkpoint: singleton insertion and ordered sums

`18f3ce7` is checked and published on `main`; worker sources `8b88486`,
`c8ea122` were integrated through `01cc71f`, `6ae4fff`. Singleton insertion is an
equivalence at every prescribed position, with exact actual-block transport.
`orderedBlockWord_image`, `orderedPartitionContribution_insertSingleton`, and
`sum_orderedPartitionContribution_singleton` give exact ordered word/product/sum
transport for arbitrary block weights. Full builds, direct audit and source guard
pass for 1070 declarations. Unit-cumulant vanishing is the next obligation, not
a hypothesis or a consequence asserted by the transport module.

### Checked integration checkpoint: Wick vectors and right operators

`131f134` is checked and published on `main`; sources `e2d7aa8`, `0e0a63b`
were integrated through `7384bb4`, `3affad8`. `wick_vacuum` realizes every word,
`vacuumExpectation_wick_star_mul` proves exact orthogonality, and the commutant
separating lemma follows from this cyclicity. `commute_semicircular_rightSemicircular`
is an operator equality on all vectors, with boundary cases handled explicitly.
Full builds, direct audit and source guard pass for 1127 declarations.

Reviewed published milestones awaiting integration: polynomial/closed faithful
tracial generated states (`53f5bd8`, `979669a`) and general unit-cumulant vanishing
with scalar/centering invariance (`36a6578`). No full Wick/freeness or norm-two
result is counted from these supporting milestones.

### Checked integration checkpoint: faithful tracial generated states

`51bd061` is checked and published on `main`; sources `53f5bd8`, `979669a`
were integrated through `56d675e`, `2ead787`. `generatedVacuumState_isFaithful`
and the polynomial trace theorem use proved right commutation/cyclicity, not
assumed faithfulness or trace. `closedGeneratedVacuumState_isFaithful` and
`closedGeneratedVacuumState_tracial` extend to the actual operator-norm-closed
generated algebra; an explicit completeness instance is provided. Full builds,
direct audit and source guard pass for 1184 declarations. A commutator-expectation
example checks the public closed trace interface. Exact norm two (`f881b61`) and
unit/scalar cumulants (`36a6578`) await their integration checkpoints.

### Checked integration checkpoint: unit/scalar cumulants

`84af7d3` is checked and published on `main`; worker source `36a6578` was
integrated through `d1e24d9`. `cumulant_ofFn_eq_zero_of_unit` and
`cumulant_eq_zero_of_one_mem` prove arbitrary-position unit vanishing at every
order at least two. Scalar insertion/shift and individual-coordinate centering
invariance follow from actual multilinearity, with no freeness/trace/positivity
assumption. The noncommutative ordered product deletion and proper-block
strong-induction step are audited. Full builds, direct audit and source guard
pass for 1200 declarations; a third-order centering usage example is checked.

### Checked integration checkpoint: noncrossing lattice and adjacent quotient

`3678bca` is checked and published on `main`; sources `a54a473`, `c84f43d`
were integrated through `cee3530`, `f90dcf2`. Arbitrary intersections give the
actual complete refinement lattice; joins use least noncrossing closure, not an
unjustified raw-setoid join. Adjacent contraction is an actual equivalence and
order isomorphism with partitions relating the two adjacent positions, with
`contract_le_iff` as quotient adjunction. Full builds, direct audit and source
guard pass for 1234 declarations. Special raw adjacent-join preservation is
published separately (`8fe5122`) and not assumed by this module.

### Checked integration checkpoint: exact norm two and C-star compatibility

`2058aab` is checked and published on `main`; sources `f881b61`, `7310a7b`
were integrated through `293d29f`, `0f6f269`. Finite chains have squared norm
`n+1` and Rayleigh numerator `2n`; `semicircular_rayleigh_bound` and an explicit
positive-gap Archimedean argument prove `norm_semicircular = 2`.
`CStarModel` verifies the inherited C-star structure and actual closed-generator
norm/selfadjoint/centering/variance statements. Full builds, direct audit and
source guard pass for 1270 declarations. No spectral law or full Wick formula
is inferred from the norm alone.

### Checked integration checkpoint: local refinements and adjacent fibers

`1708387` is checked and published on `main`. Sources/integration mappings:
`8fe5122`→`0bb05ee`, `8e72bab`→`e861b39`, `fef5c89`→`dba2ab4`,
`375b360`→`a96b8c6`, `01ae6aa`→`083654c`, `3231976`→`af6afed`.
Raw adjacent joins preserve noncrossing and merge at most two blocks.
Restriction/local-refinement are actual inverse constructions with exact block
and contribution transport. `adjacentFiberEquiv` and
`sum_adjacentPartitionFiber_contribution` identify each global join fiber with
local endpoint-covering refinements and fixed outside factors, for arbitrary
weights. Whole-word centering is integrated. Full builds, direct audit and source
guard pass for 1336 declarations. The actual adjacent cumulant product theorem
remains unproved; its finite-index/ordered-word transport is a separate next task.

Worker B was synchronized from clean `de87f86` with verified `main` at this
checkpoint: merge `e28ccb6` was published immediately, focused FreeCStarModel
build and source guard passed, and the worktree was clean before writing resumed.
The operator right-annihilation boundary commutator and word recursion were
selected ahead of pairing splitting to advance genuine integration by parts.

### Failed approach and implementation observations

- Full integration detected a duplicate `FreelyIndependent.comap` in the Fock
  bridge: the baseline `Algebraic.DistributionComparison` already provides a more
  general pullback theorem. The standalone module build had not imported that
  interface. Fix `3eaf5df` (integration `8f3ff3a`) removes the duplicate and imports
  the existing API; the genuine free-model theorem is unchanged. Reviews now
  scan new declaration names across the entire repository, and combined imports
  are checked before integration.
- A generic direct `.comap` proof term in `FreeCStarModel` caused Lean elaboration
  `whnf`/`isDefEq` heartbeat timeouts at 200k and 800k; this was an elaboration
  problem, not resource exhaustion. Explicit ambient parameters and direct
  labeled-list transport compiled in 2.3s without retaining a raised heartbeat.
- Continuous-linear-map scalar rewrites sometimes required pointwise extensionality
  in one-color Wick spans; ordinary generic `zero_smul`/`add_smul` rewrites were
  insufficient. The final proofs use the actual operator application API.

### Independent spectral-measure proof path

For a positive normalized state and self-adjoint `a`, pull the real part of the
expectation back along `cfcHom` on the compact real spectrum. Positivity follows
from `cfcHom_mono` and the existing positive-state API. `RealRMK.rieszMeasure` and
`RealRMK.integral_rieszMeasure` then give a regular measure; evaluating one gives
probability normalization. Push forward along the spectrum subtype inclusion.
This path does not need traciality or Fock space. Full support needs faithfulness,
using nonzero continuous bump functions and injectivity of the functional
calculus. Complex Cauchy integral representation remains a subsequent theorem.
This is a reviewed strategy, not a completed declaration.

- Following unit calculus and adjacent contraction: prove raw adjacent-join
  preservation, block/fiber product formulas, then the reverse freeness implication.
- Following faithful tracial closed realization: integrate exact norm two and
  C-star compatibility; prove genuine freeness and joint Wick recursion.
- When a worker becomes available: polynomial free difference quotient Leibniz
  rules, or spectral-measure representation prerequisites, with exclusive files.

Update this ledger at each integration checkpoint with exact declarations, commit
hashes, checks, failed approaches and newly unblocked tasks.

### Checked integration checkpoint: genuine freeness

`041906e` is checked and published on `main`: polynomial/closed-generator
freeness and its actual faithful C-star bridge are integrated from `7350c11`,
`54fde61`, `de87f86`, with duplicate-name fix `3eaf5df` → `8f3ff3a`.
Full builds, direct transitive audit and source guard pass for 1403 declarations.
The alternating fourth-moment usage example permits repeated nonadjacent labels.

### Pending integration: complete cumulant characterization

Sources/integration mappings: `481a876`→`0798b2a`, `4ea8b76`→`3a92bc7`,
`6a41526`→`a81345d`, `7f7d3be`→`5f1a9fd`, `fa71c82`→`1c47807`,
`712dc4d`→`2647876`, `5f10939`→`304ce45`, `eab9ffa`→`d0f933f`.
`cumulant_fuseAdjacent` is the all-order actual adjacent product formula;
`freelyIndependent_iff_mixedCumulantsVanish` is the intended algebraic equivalence
for arbitrary fields/rings/algebras without positivity, trace or centering
assumptions. Read-only mathematical review and combined checks pass: full build (3443 jobs),
Verification (3446 jobs), direct audit of 1481 declarations, source guard and
un-centered mixed-third-cumulant usage example. Main integration remains pending.
These close the central characterization, not every subgoal of Goal 1.

### Publication recovery

Transient GitHub DNS failures were reported and recovered. Worker A's RCLike CLT
commit was pushed on normal retry. Worker B's verified pairing-count tree
`4d9338de851652b929825c80c8303f923d51cd37` was published through the authorized
GitHub connector as `0138b7555e43ac153c1d1d02224c153d4a2490fa`; the matching local
commit was `8ebf75af94fdfdec3a4cfc12e2857088fcbaa47a`. Coordinator reconciliation
merge `a860eb6` preserved both histories and was pushed successfully after DNS
recovered. No shared history was rewritten. Workers then resumed.

### Checked integration checkpoint: full freeness characterization

`e54c402` is checked and published on `main`, full build 3443 jobs,
Verification 3446 jobs, transitive audit 1481 declarations and source guard.
The earlier pending source mappings above are now integrated. Full all-order
algebraic freeness iff mixed cumulants vanish and actual adjacent-product
calculus hold. Möbius inversion/Kreweras remain separate Goal 1 obligations.

### Pending integration: actual joint Wick and Catalan moments

Sources/integration mappings: `629978b`→`e2bcbe6`, `04ff2f2`→`2a84510`,
`27ba7c5`→`6894027`, `9898bed`→`8313535`, `790afa1`→`ea6ee91`,
`86ae38e`→`5f2e2bb`, `8ebf75a`→`89adb4d`, `d61905d`→`d2d471c`,
`04df539`→`7639c43`. Rank-one vacuum boundary commutators give actual
all-degree word IBP. The independently constructed first-partner pairing
equivalence and weighted recursion imply literal joint Wick for actual Fock
operators, then Catalan even and zero odd moments in the faithful tracial
C-star model. Read-only review and combined checks pass: full build 3451 jobs, Verification
3454 jobs, transitive audit 1684 declarations, source guard and genuine sixth
moment usage. Main integration remains pending. The single
pinned Catalan mathlib cache artifact was reused from the isolated worker cache;
no dependency revision or toolchain changed. Spectral density identification,
polynomial tensor derivative packaging and general tensor identification remain.

### Checked integration checkpoint: genuine Wick and Catalan law

`648a7d6` is checked and published on `main`; previous pending mappings are now
integrated. Full build 3451 jobs, Verification 3454 jobs, direct transitive audit
1684 declarations, source guard and sixth-moment-five example pass. The literal
joint noncrossing-pairing formula and actual one-generator Catalan moments hold
in the constructed faithful tracial C-star model. Spectral measure/density
identification remains open. Word IBP is genuine, but full tensor derivative
and matrix/analytic Goal 3 statements are not claimed complete.

### Pending integration: formal R and algebraic free CLT

Sources/integration mappings: `5b65e83`→`e387fae`, `e405d98`→`ab1414b`,
`5a57e0e`→`fdd8a87`, `b0a7b1c`→`8b9f0a1`, `d38b5b7`→`33fbaf8`,
`d939ad4`→`35ab4c4`, `fb0b4ca`→`bfbfa6a`, `edc1176`→`d8b2c5b`,
`38756c4`→`41ac34c`, `aab1feb`→`3193dd5`. Finite free sums give all-order
cumulant additivity; the R transform is explicitly formal. All moment/cumulant
limits hold for genuine centered iid free triangular arrays over RCLike scalars
with arbitrary varying ambient algebras. Explicit pairing-moment limits require
no limiting realization; polynomial/star-distribution corollaries require an
actual supplied semicircular-cumulant target and star selfadjointness where
appropriate. No uniform norm bound, spectral convergence or strong convergence
is introduced. Read-only mathematics review and global name scan approved;
combined checks pass: full build 3467 jobs, Verification 3470 jobs,
direct transitive audit 1736 declarations and source guard. Main integration pending.

### Checked integration checkpoint: formal R and moment free CLT

`65ea73e` is checked and published on `main`; previous source mappings are now
integrated. Full build 3467 jobs, Verification 3470 jobs, direct audit 1736
declarations and source guard pass. Formal R-additivity/scaling and explicit
real/complex moment free CLT are established. Analytic R identification,
positive additive convolution, operator-valued/annular/genus theory remain.

### Pending integration: concrete free-CLT target

Coordinator source `1557ef0` proves
`Fock.closedSemicircular_hasSemicircularCumulants` by actual Fock moments and
uniqueness of recursive inversion. Source `848bf59` gives
`Fock.freeCLT_convergesTo_closedSemicircular` and
`Fock.freeCLT_convergesInStarDistribution_closedSemicircular`: centered unitvariance
iid free triangular arrays converge to the actual faithful tracial C-star
semicircular generator. No assumed target realization remains in these
variance-one statements. Star convergence needs self-adjoint source entries;
no spectral or operator-norm convergence is claimed. Focused builds and major
axiom audits and read-only review pass. Combined full build 3469 jobs,
Verification 3472 jobs, direct audit 1739 declarations and source guard pass.
Main integration pending.

### Checked integration checkpoint: concrete free-CLT target

`cf3c085` is checked and published on `main`: sources `1557ef0`, `848bf59` are
integrated. Full build 3469 jobs, Verification 3472 jobs, direct audit 1739
declarations and source guard pass. Actual semicircular cumulants and
variance-one polynomial/star CLT converge to a constructed faithful tracial
C-star target. Arbitrary-variance explicit pairing moment limits were already
integrated; actual-target arbitrary nonnegative variance scaling remains ready.

### Pending integration: full refinement and Möbius inversion

Sources/integration mappings: `428fe53`→`6f51e87`, `f9be448`→`3cc39c3`,
`f784e03`→`37992d1`, `01aa2a9`→`8858742`. The entire lower NC refinement
interval is order-isomorphic to the product of its ordered-block NC lattices;
actual blocks and contributions factor with proved disjointness. The complete
refinement zeta convolution holds for any normalized moment function. Actual
mathlib incidence-algebra Möbius inversion gives `partitionCumulant_eq_mobius_sum`
for every partition and `freeCumulant_eq_mobius_sum` for nonempty words; the
empty-word exclusion is necessary because its scalar cumulant is zero.
`cumulant_eq_mobius_sum` specializes to actual probability spaces. Mathematical
review and combined checks pass: full build 3474 jobs, Verification 3477 jobs,
direct transitive audit 1768 declarations and source guard. Main integration
pending. Kreweras complement and full
multi-product cumulant fibers remain separate obligations.

### Checked integration checkpoint: Möbius inversion

`168898a` is checked and published on `main`; prior pending source mappings are
now integrated. Full build 3474 jobs, Verification 3477 jobs, direct audit 1768
declarations and source guard pass. Genuine lattice Möbius inversion is complete;
Kreweras complement/general multi-product identities are separate Goal 1 tasks.
The single pinned IncidenceAlgebra cache artifact was downloaded successfully;
no revision or toolchain changed.

### Pending integration: arbitrary vectors and complete Hilbert sums

Sources/integration mappings: `10a56ef`→`2268da9`, `200886a`→`efac3a9`,
`743e27e`→`1976ef7`, `aef7967`→`3d134fd`. Arbitrary ℓ²-vector creation has
exact norm and adjoint Gram relation; actual HilbertBasis representation
transports it to every vector of the original complex Hilbert space.
`lengthDecomposition` is a surjective complete Hilbert-sum equivalence, including
infinite amplitudes and arbitrary index types. `completedTensorEquiv` identifies
the GENUINE completion of ℓ²(I,ℂ) ⊗ E with ℓ²(I,E) for complete complex Hilbert E;
the algebraic tensor is never asserted complete. Source `2c0598f` → `75cd2c3` proves actual scalar vacuum level, successor
completed-tensor/level equivalence and literal arbitrary-vector tensor creation.
Together with length decomposition, the ℓ²(I) model has genuine completed tensor
levels. Explicit original-H tensor coherence remains ongoing. No trace
claim is made for generators indexed by all complex vectors. Combined checks
pending; vector/basis/length/tensor reviews and global name scans approved.
The initial combined build passed before adding tensor levels. The final combined
full build 3480 jobs, Verification 3483 jobs, direct audit 1942 declarations and
source guard pass. Main integration pending.

### Checked integration checkpoint: completed tensor levels

`871fc9f` is checked and published on `main`, previous pending source mappings
integrated. Full build 3480 jobs, Verification 3483 jobs, direct audit 1942
declarations and source guard pass. Arbitrary-vector creation, Hilbert-basis
transport, complete length decomposition and genuine tensor-level recursion
are integrated. Creation is literally tensoring by the input ℓ² vector. Explicit
original-H tensor coherence is separately published as `aac1e11`; a named
recursive completed TensorPower and general full-Fock package are ongoing.

### Pending integration: consecutive product cumulants

Sources/integration mappings: `e8d1865`→`7c9b492`, `68a5a09`→`2c47857`,
`e065136`→`952e257`. All-partition adjacent product identities iterate over any
supplied finite adjacent-fusion plan. Its quotient is monotone/surjective with
nonempty interval fibers; exact contract/expand adjunction proves the standard
join-fiber formula. `cumulant_consecutiveProducts` handles nonempty final tuples
and preserves noncommutative order. Mathematical review and global name scan
approved; combined full build 3483 jobs, Verification 3486 jobs, direct audit
2042 declarations and source guard pass. Main integration pending. Constructing a plan from an arbitrary
independently specified interval partition/composition and proving pointwise
product-by-fiber identification are still separate obligations. Kreweras remains
open; this milestone does not silently assume those construction theorems.

### Checked integration checkpoint: consecutive-product plans

`7bb8314` is checked and published on `main`, prior source mappings integrated.
Full build 3483 jobs, Verification 3486 jobs, direct audit 2042 declarations
and source guard pass. Standard join-fiber cumulant formulas hold for all
supplied finite consecutive-fusion plans. Every monotone surjective finite
quotient plan-existence theorem is published separately (`670aae1`); direct
pointwise products over quotient fibers remain being completed.

### Pending integration: original-H full Fock package

Sources/integration mappings: `aac1e11`→`b7af568`, `914ff46`→`c6f5501`.
Completion transports actual linear isometry equivalences; the original H
enters genuine completed H ⊗ level recursion and literal creation action.
`FullFock H` exists for every complete complex Hilbert H using mathlib's actual
Hilbert-basis existence theorem, with full grading, exact operator norms,
canonical relation and vacuum annihilation. The named recursively completed
TensorPower/direct-sum equivalence is the next presentation theorem, avoiding
universe problems by a scalar-isomorphic base level. General basis independence
and spectral density identification remain separate obligations. Original-H
coherence and FullFock package reviewed; full build 3485 jobs, Verification
3488 jobs, direct transitive audit 2083 declarations and source guard pass.
Main integration pending.

### Checked integration checkpoint: unconditional general-H full Fock

`5c2e9cb` is checked and published on `main`, previous source mappings integrated.
Full build 3485 jobs, Verification 3488 jobs, direct audit 2083 declarations
and source guard pass. General-H original tensor coherence and unconditional
chosen-basis full-Fock existence are complete. Explicit recursive TensorPower,
its genuine complete Hilbert sum/unitary and operators on that exact domain
are separately published (`8466cf7`, `90ca303`). Their intrinsic generated
algebra and joint-law transport remain queued; spectral measures remain open.

### Pending integration: polynomial and matrix integration by parts

Coordinator sources: `6d077fb` definitions and word Leibniz; `19b414a` full
polynomial tensor bimodule Leibniz; `b590295` literal prefix/suffix derivative
sum and all-polynomial IBP; `c22ae11` actual faithful tracial C-star wrapper;
`c5d2237` matrix amplification and matrix tensor Leibniz.
`freeDifferenceQuotient_mul` uses left multiplication on the first tensor factor
and right multiplication on the second. `tensorPolynomialExpectation` is the
actual bilinear product of evaluated expectations, never a multiplicative
expectation homomorphism. Polynomial IBP follows actual vacuum word recursion;
no Wick/freeness/IBP assumption is used. Finite rectangular matrix-valued
polynomials satisfy the genuine idMatrix ⊗ τ identity, with scalar semicircular
matrix multiplication; matrix Leibniz is also proved. Focused builds, source
guard and representative axiom audits pass; polynomial review approved,
closed-state/matrix review and name scan approved. Combined full build 3488
jobs, Verification 3491 jobs, direct audit 2146 declarations, source guard and
noncommutative repeated-letter derivative usage pass. Main integration pending.
Norm-convergent analytic
extensions, especially exponential/resolvent domains, remain Goal 3 obligations.

### Implementation observations

- Pinned `MonoidAlgebra` wraps Finsupp. Linear extension must use its actual
  coefficient linear equivalence, not a definitional Finsupp coercion.
- Pinned TensorProduct.inductionOn derives zero from elementary tensors and
  accepts only elementary/addition cases. No deprecated induction was retained.
- StarSubalgebra inclusion `.val` may simplify to `.subtype`; explicit map
  equations/pointwise proofs avoided inappropriate rewrite matching.

### Checked integration checkpoint: polynomial and matrix IBP

`ea6149a` is checked and published on `main`; coordinator sources listed above
are integrated. Full build 3488 jobs, Verification 3491 jobs, direct audit 2146
declarations, source guard and a noncommutative repeated-letter derivative usage
pass. The polynomial and rectangular matrix subtargets of Goal 3 are complete;
analytic exponential/resolvent extensions remain open with explicit domains.

### Pending integration: generic grouping and Kreweras moments

Sources/integration mappings: `670aae1`→`242e414`, `83574f9`→`8e3dd1f`,
`a1c2613`→`96fb920`, `65dce9c`→`cf12051`, `4b4cffe`→`c6c9384`,
`7b8bfb6`→`cd00b5a`, `4fd1146`→`3ac4d5c`, `dc1a0dc`→`f4faa97`.
Every monotone surjective finite quotient is realized by a fusion plan and its
outputs equal literal sorted fiber products. `cumulant_intervalProducts_top`
is the independently specified arbitrary consecutive-grouping theorem, with
no plan witness assumed. Genuine right Kreweras construction/maximality has
exact alternating interleave NC iff q ≤ K(p), antitonicity and endpoints.
Parity partition classification and actual-block factorization imply
`FreelyIndependent.expectation_eq_kreweras_sum` for all alternating tuples
from two free algebras, including order zero; no positivity/trace/centering
assumptions. Mathematical reviews and global name scans approved; combined
checks pass: full build 3496 jobs, Verification 3499 jobs, direct audit 2266
declarations and source guard. Main integration pending. K² rotation, complementary block counts and product-cumulant
boxed convolution/analytic S-transform remain separately unproved.

### Next independent work

Worker B published the complete tensor-domain checkpoint through `f1657b9`.
Goal 6 now uses exclusive new `Analytic/SpectralMeasure*.lean` files on a focused
`feat/spectral-measures` branch based on checked main, retaining the isolated
worktree/cache. Targeted pinned RealRMK cache hydration is authorized when absent.
Worker A continues Kreweras product-cumulant combinatorics in its exclusive files.
Coordinator integrates sequentially, then selects analytic IBP extensions or
free-CLT variance scaling; reviewer remains read-only.

### Checked integration checkpoint: general products and Kreweras moments

`18afd0f` is checked and published on `main`, previous source mappings integrated.
Full build 3496 jobs, Verification 3499 jobs, direct audit 2266 declarations
and source guard pass. Independently specified consecutive products and genuine
Kreweras maximality/interleaving/alternating moments are complete. Actual pair
products and (a*b)^n corollaries are published (`0fe24b6`, `955cadb`) and queued.
Worker obstruction record `bb081f0` in `docs/math-notes/cumulant-obstructions.md`
precisely separates boxed top-fiber connectivity/tree counting and missing
Pi Möbius/order-isomorphism APIs. No boxed/S-transform result is claimed.
Worker A advances a conditional non-iid triangular-array CLT while these
mathematical dependencies remain open.

### Pending integration: exact tensor-domain semicircular model

Sources/integration mappings: `8466cf7`→`d465a86`, `90ca303`→`f348f65`,
`c5e9ec3`→`9cbe9c1`, `73dc31f`→`fb92008`, `f1657b9`→`cfc3534`.
TensorPower's successor is literally the genuine completion of original H
⊗ previous power; the zero level is explicitly scalar-unitary for universe
consistency. The full-Fock unitary is onto the actual completed tensor-power
Hilbert sum. Creation/annihilation act on that exact domain and creation sends
a degree-n vector to its literal completed h⊗f in degree n+1. Chosen orthonormal
basis fields have actual norm two/selfadjointness and freeness in intrinsic
closed singleton algebras. The literal norm-closed generated tensor C-star state
is proved positive, normalized, faithful and tracial. Actual literal joint Wick
and Catalan laws hold there. No trace is asserted on all bounded operators or
all complex-vector fields. Mathematical reviews/global name scans approved;
combined full build 3501 jobs, Verification 3504 jobs, direct audit 2453
declarations and source guard pass. Main integration pending. Arbitrary
orthonormal-family/basis-independent transport
and semicircular spectral measure/density remain separate obligations.

Worker B switched from clean `f1657b9` to `feat/spectral-measures` based on checked
main `ea6149a`; no tensor history was changed. Targeted RealRMK cache hydration
fetched eight pinned cache files under the common lock. Actual positive real CFC
functional is published as `c592166`; probability measure representation is next.

### Checked integration checkpoint: exact tensor-domain semicircular system

`8334d17` is checked and published on `main`, previous source mappings integrated.
Full build 3501 jobs, Verification 3504 jobs, direct audit 2453 declarations
and source guard pass. The actual recursively completed tensor-sum domain has
bounded canonical operators, literal tensor action, selected basis semicircular
fields and an intrinsic faithful tracial generated C-star algebra, genuine
freeness and literal joint Wick/Catalan laws. Semicircular spectral law and
arbitrary orthonormal-family/basis-independent interfaces remain separate.

### Pending integration: actual resolvent IBP

Coordinator source `3111620` gives
`Fock.rightAnnihilation_resolvent_commutator`,
`Fock.vacuumExpectation_semicircular_mul_resolvent`,
`Fock.vacuumExpectation_resolvent_quadratic` and a nonreal-domain corollary.
The generic inverse commutator is proved for actual units. Its sign yields
[rightAnnihilation_i,R_j]=δij R_j Pvac R_j, and actual rank-one vacuum evaluation
gives τ(s_i R_j)=δij τ(R_j)^2 throughout the actual operator resolvent set.
The resolvent expectation satisfies G²-zG+1=0 using the genuine inverse identity
and normalization. No power-series assumption, assumed spectral density or
assumed transform formula is used. This is currently the raw bounded-Fock vacuum
statement; membership/compatibility of the inverse in the generated C-star model
and general polynomial/matrix resolvents are separate next tasks. Focused build,
representative axiom audits, source guard and mathematical review pass. Combined
full build 3502 jobs, Verification 3505 jobs and direct audit 2459 declarations
pass. Main integration pending.

### Newly ready review queue

Spectral sources `c592166`, `d6ee62a`, `4a9dedf` construct positive real CFC
functional, actual spectral probability measure, real CFC integral representation
and faithfulness implies actual support=spectrum; first two reviewed, support
review underway. No traciality is assumed. General complex/Cauchy representation
and semicircular measure identification are the worker's next tasks.
A's `608b229`, `86ddce2` give a quantitative non-iid triangular-array moment CLT,
conditional on all-entry centering, actual averaged-second-moment convergence
and uniform fixed-higher-order marginal cumulant bounds. A's `0f7d1dc` proves
exact Kreweras adjacent-chord deletion, a genuine new prerequisite toward the
previously recorded boxed-complement connectivity/block-count obligation.

### Checked integration checkpoint: actual resolvent IBP

`7386526` is checked and published on `main`; coordinator source `3111620` is
integrated. Full build 3502 jobs, Verification 3505 jobs, direct audit 2459
declarations and source guard pass. The all-resolvent-set single-generator IBP
and actual Cauchy quadratic are complete, with nonreal domain proved. General
polynomial/matrix resolvents, generated-algebra compatibility and exponential
extensions remain explicit next tasks.

### Pending integration: actual spectral measures and faithful support

Sources/integration mappings: `c592166`→`bb9f9a3`, `d6ee62a`→`060aba7`,
`4a9dedf`→`176b50b`. Actual positive real CFC functional and RMK representation
construct `spectralMeasureOnSpectrum` and `spectralMeasure`, with genuine
probability normalization. Real continuous CFC expectations have integral
representation. Concentration gives support inclusion; actual faithfulness,
CFC injectivity and continuous Urysohn bumps give
`spectralMeasure_support_eq_spectrum`. No traciality/support assumption or
spectral-measure existence assumption is used. This represents full complex
expectations only for REAL-valued CFC functions; general complex/Cauchy integral
representation is a subsequent worker theorem. All three mathematical reviews
and global name scans approved. Combined full build 3515 jobs, Verification
3518 jobs, direct transitive audit 2493 declarations and source guard pass.
Main integration pending. Targeted pinned RMK
and Support cache artifacts reused/downloaded under the common lock; no
revision/toolchain update or unnecessary dependency rebuild.

### Checked integration checkpoint: spectral measures and faithful support

`9ca8caa` is checked and published on `main`, previous source mappings integrated.
Full build 3515 jobs, Verification 3518 jobs, direct audit 2493 declarations
and source guard pass. The actual spectral probability measure, real CFC integral
representation and faithful support=spectrum are complete. DNS interrupted
publication of `9ca8caa` and worker `707f09a`; local commits were preserved,
failures reported immediately and normal SSH retries succeeded. No connector
publication/history reconciliation was needed for this occurrence.

### Pending integration: quantitative non-iid free CLT

Sources/integration mappings: `608b229`→`691197c`, `86ddce2`→`bd5e0c0`.
`FreelyIndependent.norm_cumulant_normalized_sum_le` gives an actual finite-size
higher-order estimate; `freeCLT_triangular_cumulants` and
`freeCLT_triangular_pairingMoments` give full limits for varying ambient algebras
without identical distribution. Hypotheses explicitly require each entry
centered, true averaged second-moment convergence and uniform bounds on each
fixed higher-order marginal cumulant. No positivity/trace/spectral convergence
is assumed or concluded. This is a conditional quantitative non-iid theorem,
not a replacement for the completed iid CLT or an optimal Lindeberg result.
Mathematical review and global name scan approved; full build 3517 jobs,
Verification 3520 jobs, direct audit 2503 declarations and source guard pass.
Main integration pending.

A's `9403369`, `acaeae1` now prove the genuine positive-degree Kreweras block
count through exact signature deletions and boundary-free NC reduction. Both
reviewed and queued; complementary connectivity/top join fiber still remains.
B's `707f09a`, `3c19e01` give complex CFC and actual all-resolvent-set Cauchy
spectral integral representation, avoiding global-continuity restrictions.
Complex CFC reviewed; Cauchy review and integration next. Compact moment-law
uniqueness is the next independent spectral task.

### Checked integration checkpoint: quantitative non-iid CLT

`8cb664e` is checked and published on `main`, previous source mappings integrated.
Full build 3517 jobs, Verification 3520 jobs, direct audit 2503 declarations
and source guard pass. The non-iid triangular-array theorem is established
under its explicit sufficient cumulant bounds and averaged variance convergence.
The positive-degree Kreweras count is also now published/reviewed; count does
not by itself prove the remaining complementary connectivity/top-fiber identity.

### Pending integration: complex spectral calculus and Cauchy law

Sources/integration mappings: `707f09a`→`bbc8723`, `3c19e01`→`92e49c7`,
`e40267d`→`b3d1842`. Complex spectral CFC representation requires continuity
only on the actual spectrum, never artificial global continuity.
`resolvent_eq_cfc_inverse_kernel` identifies the actual inverse via genuine CFC;
`cauchyTransform_eq_spectralIntegral` covers every actual resolvent point,
including real exterior points. Actual spectral power, real polynomial and
complex polynomial integrals agree with algebraic expectations; all powers
are integrable. No faithfulness or trace assumption is needed for representation.
Complex-CFC, Cauchy, moment and uniqueness reviews/global name scans approved.
Additional source `0945dfb` → `aed52fc` proves equality of actual spectral
probability laws across different bounded ambient C-star algebras from all
power moments by Stone-Weierstrass and actual measure uniqueness. Source
`a8aaa49` → `39a6232` gives the reverse and exact iff. Combined checks are
repeated for these related new source additions: full build 3521 jobs,
Verification 3524 jobs, direct audit 2520 declarations and source guard pass.
Main integration pending.
Weak spectral-law convergence and full nonreal Cauchy convergence under explicit
uniform bounds remain next compatibility tasks; no full Goal 6 certification yet.

### Worker synchronization and target-scope audit

From clean published `0945dfb`, coordinator merged checked `main` `8cb664e`
into the isolated spectral branch as `0b91789`, pushed immediately, then checked
focused uniqueness build and the source guard in that actual worker directory.
The worktree was clean before writing resumed. No central-file ownership changed.

Read-only Goal 6 audit confirms canonical `CStarAlgebra.spectralOrder` and
`spectralOrderedRing` supply the order interfaces for any C-star algebra;
they are not restrictive additional mathematical hypotheses. New actual spectral
measure/CFC/Cauchy statements need no faithfulness or trace except faithfulness
for full support. Baseline analytic transform convergence is only in the exterior
region under eventual uniform source bounds and explicit target norm condition.
Weak measure convergence and all-nonreal Cauchy convergence are being proved
separately. They are not inferred from the exterior theorem or claimed prematurely.

### Checked integration checkpoint: Cauchy law and spectral determinacy

`ab262d5` is checked and published on `main`, previous source mappings integrated.
Full build 3521 jobs, Verification 3524 jobs, direct audit 2520 declarations
and source guard pass. Actual complex CFC/Cauchy representation on the whole
resolvent domain and spectral law equality iff all power moments are complete.
Weak law/full nonreal transform convergence under explicit bounds remain active.

### Pending integration: Kreweras deletions/count/raw connectivity

Sources/integration mappings: `0fe24b6`→`243d2dc`, `955cadb`→`98f85de`,
`bb081f0`→`476127d`, `ea139ba`→`a2a3c46`, `0f7d1dc`→`da0456d`,
`15d5ce4`→`90751b9`, `9403369`→`ed7c9e5`, `acaeae1`→`dee4866`,
`b88ad6b`→`3a48bab`, `caebd84`→`07eca02`, `b6947cf`→`4548bd9`,
`b25eb57`→`d9c7cdf`, `292e68e`→`1e92f7f`, `9a45c36`→`1fcc5ed`,
`0417fd3`→`7f55eca`.
Actual alternating pair products and (a*b)^n moments have the Kreweras formula.
Adjacent original chords and noninitial singleton insertion have exact
complement transports; a boundary-free reduction yields
`card_blocks_add_kreweras` for n>0. At n=0 the usual n+1 count is false, and all
empty identities are handled separately. Raw interval joins are genuinely NC
without extra closure merges. Actual refinement block maps give strict block
count for proper refinement. `interleave_sup_pairKernel` and
`sup_val_of_le_kreweras` prove compatible joins are RAW joins;
`sup_kreweras_val_eq_top` is genuine raw connectivity, not merely NC closure top.
All mathematical reviews and name scans approved; combined checks pending.
The finite incidence-graph connected block-count bound and exact doubled
pairing top-fiber iff still precede boxed product cumulants. Worker graph bound
currently compiles but is not yet published/integrated. Thirty-five uncached
mathlib graph dependencies were built serially under the common lock; they are
preserved. Future missing mathlib targets are hydrated from the pinned cache
first, avoiding unnecessary dependency rebuilds. The worker-owned obstruction
record is integrated from its published checkpoints; later updates remain on
its branch until reviewed and integrated.

### Pending integration: complete requested cumulant calculus

Additional sources/integration mappings: `18bee10`→`920f0d0`,
`c0011e6`→`12ef517`, `eb9bdcf`→`0d8e604`, `89c22f2`→`c7af250`,
`6301f8b`→`a1a4676`, `20ddb01`→`60480d6`, `0fb2000`→`fd7d800`,
`b84b8b4`→`598546f`, `ddc03b5`→`8842e0d`.
Actual incidence-graph connectivity and finite edge bound give the connected
block-count bound without assuming a tree. Genuine K count and strict refinement
then prove the exact doubled top fiber q=K(p), including the separate empty case.
`FreelyIndependent.cumulant_prod_eq_kreweras_sum` and its repeated-product variant
are the full actual boxed formulas for positive-order coordinatewise products
of two free tuples, with no trace, positivity, commutation or connectivity
premises. The optional actual K incidence tree, finite-poset Möbius order-isomorphism
invariance and finite dependent-product μ formula are also integrated into this
feature. Source guard caught a forbidden token only in a documentation comment;
`c0011e6` rephrases it with no proof change or audit relaxation. The targeted
pinned graph cache hydrated 33 missing files instead of rebuilding dependencies.
All mathematical reviews/global name scans approved. Final combined full build passes
3574 jobs, Verification 3577 jobs, direct transitive audit 2626 declarations,
and source guard. The ordinary second-cumulant centered-free-product usage
example also kernel-compiles. Main integration and certification remain pending.

Read-only literal Goal 1 audit confirms all requested mathematical subtargets
are covered by these sources and existing integrated prerequisites. Rotation
identities and explicit Catalan closed-form μ coefficients are useful extensions,
not requirements named in the goal specification. Goal 1 will be certified only
after this integration passes the main build/audits and meaningful boxed usage.
No whole-project completion is implied.

### Safe worker reassignment after verified branch checkpoints

Worker A completed/pushed through clean `ddc03b5`, then coordinator switched its
isolated worktree to `feat/operator-valued-matrix` from checked main `ab262d5`.
Exclusive files are new `OperatorValued/Matrix*.lean`; actual scalar-state matrix
conditional expectation `a594efa` and all finite amplified Hermitian covariance
positivity `bf0e7eb` are published. General arbitrary-B completely positive
semicircular realization remains a separate Goal 4 obligation.
Worker B completed/pushed the spectral/density checkpoint through clean `edb2f06`,
then coordinator switched its isolated worktree to `feat/orthonormal-fock` from
checked main `ab262d5`. Exclusive new `Fock/OrthonormalFamily*.lean` extends an
arbitrary ON family to a true Hilbert basis and builds a family-adapted complete
Fock realization. It does not identify operators on the preexisting fixed
chosen-basis tensor model without a separate proved unitary. Both earlier branches
and all published histories are preserved; no uncommitted work was overwritten.

### PR integration workflow

The user requested PRs and appropriate merges. Successive verified integration
checkpoints now use explicit PRs targeting `main`, preserving atomic source
commits with merge commits. Local full builds, mathematical statement review,
transitive audits and source checks precede each merge; GitHub protections are
respected. Main is checked again after merging.

### Pending PR: actual weak spectral laws and all-nonreal transforms

Worker sources `d24b590`→`e123b38`, `ce0a337`→`45a9e76` construct the
actual `ProbabilityMeasure` weak topology and prove convergence from all power
moments under an eventual common operator-norm bound. Ambient C-star algebras
may vary, and the filter is arbitrary. Continuous real/complex integrals converge;
Cauchy transforms converge at every nonreal point, without an exterior radius
restriction. This is pointwise convergence, not uniform convergence or convergence
of derivatives. Read-only Goal 6 audit approves the exact statements and confirms
canonical C-star orders supply the public order interfaces. Main integration,
full checks and usage verification remain pending before Goal 6 certification.

Combined full build passes 3530 jobs, Verification 3533 jobs, direct transitive
axiom audit 2530 declarations and source guard. A canonical Fock-generator
sequence usage example proves convergence at `z = I` inside the norm-two disk,
using the actual all-order Catalan moments and the full nonreal theorem.

### Checked PR integration: complete cumulant calculus

[PR #1](https://github.com/T1mberland/lean-free-probability-01/pull/1) merged
head `8adf5f1` as `76af384`; all atomic source commits are retained. Main full
build 3574 jobs, Verification 3577 jobs, direct audit 2626 declarations and
source guard pass. Boxed-product usage and independent exact-goal review pass.
Goal 1 is complete. GitHub Actions was still running at merge; local checks
are the verified evidence recorded here, with no claim of CI completion.

### Checked PR integration: spectral distributions and convergence

[PR #2](https://github.com/T1mberland/lean-free-probability-01/pull/2) merged
head `415f92e` as `427f72b`. Main full build 3583 jobs, Verification 3586,
direct audit 2636 declarations and source guard pass. The Fock sequence example
at `z=I` compiles, and exact Goal 6 review approves the statements. Goal 6 is
complete; nine goals remain open. PR #1 GitHub Actions run `38537828341`
subsequently completed successfully; PR #2 CI completion is not yet claimed.

### Pending PR: actual semicircle density and full operator spectrum

Worker sources/integration mappings: `d927565`→`64a4790`, `2f8a5ed`→`59c09b6`,
`64cd736`→`e6b1f54`, `2322a53`→`6d7b495`, `00432f6`→`dd48978`,
`edb2f06`→`b4aff6f`. Actual compact Fock probability laws are constructed from
the previously proved CFC state. Independently evaluated square-root integrals
prove all Catalan/odd moments and normalization of
`semicircleMeasure = volume.withDensity(ofReal(sqrt(4-x²)/(2π)))`.
A general compact probability moment-uniqueness theorem then identifies the
actual Fock law with this explicit measure. Positive interior density and closed
support prove full support `[-2,2]`; faithfulness and spectral permanence yield
the exact spectrum of both the generated-algebra element and original bounded
operator. No semicircle-law premise is assumed. Mathematical review approves
all sources; combined checks and main integration pending.

### Arbitrary orthonormal-family completion scope

Read-only review of published `466a0ca` confirms the adapted model is the FULL
F(H), including all H through the actual extending Hilbert basis, not only the
span of the supplied family. Scalar vacuum and Hilbert direct-sum grading are
actual, completed tensor successors are onto unitaries, and original-H creation
has literal tensor action. The literal Goal 2 construction permits this basis
choice depending on an arbitrary ON family. Equality with an independently fixed
chosen-basis realization is an optional coherence extension, not a missing
existence hypothesis. Direct actual adapted spectral-law/density wrappers remain
queued; full Goal 2 is not certified before their integration and all checks.

Density integration checks pass: full build 3589 jobs, Verification 3592,
direct transitive audit 2730 declarations and source integrity guard. Actual
endpoint spectrum and density fourth-moment usage examples kernel-compile.
Main integration pending.

### Checked PR integration: actual density and exact spectrum

[PR #3](https://github.com/T1mberland/lean-free-probability-01/pull/3) merged
head `1ef5e1c` as `9a2bdad`. Main full build 3589, Verification 3592,
direct audit 2730 declarations and source guard pass, with endpoint/density
usage. Worker B was clean at `466a0ca`; coordinator synced checked density
main as `4dafad8`, pushed and verified focused builds and guard in B's actual
worktree. B then published `2fe8a2f`, the direct arbitrary-family spectral
wrapper and existence theorem. Read-only review approves full literal Goal 2
scope; its integration and certification remain pending.

From clean `2fe8a2f`, coordinator switched B to `feat/fock-exponential-ibp`
from checked `9a2bdad`. Exclusive new `Analytic/FockExponential*.lean` proves
actual Duhamel ray derivatives and norm-entire single-generator exponential
IBP. The earlier ON branch and all published histories are preserved.

### Pending PR: generated-algebra resolvents and physical scalar branch

Coordinator `Analytic/FockResolventCStar` maps actual ring inverses through
algebra homomorphisms at invertible inputs. Genuine spectral permanence gives
full domain equality and intrinsic/ambient inverse compatibility. Actual
restricted vacuum-state resolvent IBP and Cauchy quadratic now hold on every
resolvent point, including real exterior points. The two quadratic roots have
product one; inversion flips the imaginary sign, proving uniqueness of the
strict lower-half-plane root. Existing strict Cauchy negativity identifies the
actual upper-half-plane physical branch without a guessed square-root formula.
A StarSubalgebra subtype algebra homomorphism avoids competing native/subalgebra
instance elaboration; focused build passes with unchanged statements. Whole
Goal 3 remains open (general polynomial/matrix analytic and exponential cases).

Coordinator source `ae9e3f8` is published. Combined full build 3590 jobs,
Verification 3593 jobs, direct transitive audit 2755 declarations and integrity
guard pass. Mathematical review approves all seven statements. The physical
branch usage computes actual `G(3i/2)=-i/2`. Main integration remains pending.

### Checked PR integration: actual generated resolvents and physical branch

[PR #4](https://github.com/T1mberland/lean-free-probability-01/pull/4) merged
head `e19831f` as `0f40468`. Main full build 3590, Verification 3593,
direct audit 2755 declarations and source guard pass, including the actual
physical-branch value `G(3i/2)=-i/2`. General polynomial/matrix analytic and
exponential extensions remain separate Goal 3 obligations.

### Pending PR: full arbitrary-orthonormal-family semicircular realization

Published worker milestones `b2d991f`, `1ef85fa`, `466a0ca`, `2fe8a2f`
(with coordinator prerequisite sync `4dafad8`) are assembled with original
history retained in integration merge `70aab26`. The extending Hilbert basis
spans all H, so the complete Fock model is for H itself. Original-H creators
have literal completed-tensor successor action, scalar vacuum, direct-sum
grading and canonical relations. The literal norm-closed algebra generated by
only the prescribed family's fields has an actual faithful tracial vacuum
state, genuine freeness, all-order joint Wick/Catalan moments and the actual
semicircle density/full spectrum. No spanning/countability or supplied-state
hypothesis is used. `exists_fullFock_semicircular_family` packages the general
existence statement; fixed independently chosen-model coherence remains optional.
All four modules reviewed; no collisions or mathematical objections. Combined
build and audit results are recorded below; main integration and Goal 2
certification remain pending. The arbitrary-family usage combines faithfulness,
sixth moment five and the actual density without any spanning assumption.

Combined ON-family full build passes 3594 jobs, Verification 3597 jobs,
direct transitive audit 2913 declarations and source guard. Arbitrary-family
usage kernel-compiles.

### Checked PR integration: full arbitrary-family Fock goal

[PR #5](https://github.com/T1mberland/lean-free-probability-01/pull/5) merged
head `458d944` as `68de4fe`. Main full build 3594 jobs, Verification 3597,
direct audit 2913 declarations and source guard pass, with arbitrary-family
usage. All literal Goal 2 subtargets are certified; eight goals remain open.
GitHub PR CI runs for #2 (`38538477082`), #3 (`38538933882`), #4
(`38540161510`) and #5 (`38540587555`) subsequently completed successfully.

### Pending PR: actual matrix semicircular calculus

Published original A commits `a594efa`, `bf0e7eb`, `0a751c2`, `fa59547`,
`a01f261`, `9a6c7a8`, `3582815`, `13dce41` are assembled as `e705793`;
`e1fb2bb`, `ab1d85c`, `8b7be88`, `c38c759` as `be2986c`, retaining original
history. Actual matrix range-target conditional expectation fixes coefficients
and is a two-sided bimodule retract. Hermitian coefficient covariance is positive
at every finite amplification. Any scalar C-star probability state is bundled
as a genuine completely positive map on ALL positive C-star matrix inputs,
using actual cone closure rather than a Gram-only positivity premise.
Actual closed-Fock coefficient sums give the Hermitian semicircular matrix
model, centering and exact covariance. All-order ordered joint/interspersed
matrix Wick identities preserve noncommuting coefficients. Actual matrix tensor
FDQ calculus, power cuts and expectation contraction prove
`closedMatrixMoment_recursion`: M(k+1)=sum_{j<k} eta(Mj)M(k-1-j), with M0=I,
M1=0, derived from actual polynomial IBP. No moment law is assumed.
All twelve sources have independent mathematical review and no collisions.
The first eight passed full build 3608, Verification 3611 and audit 2983 plus
integrity guard. Final related recursion additions undergo combined checks.
The concrete two noncommuting Pauli coefficients give actual covariance 2I;
a generic fourth-moment usage retains both noncrossing nestings.
General arbitrary-base CP-covariance realization, actual analytic Dyson and
physical matrix branch remain unproved Goal 4 obligations. Formal power-series
Dyson, currently assigned A, is not a substitute for the actual resolvent equation.

Final related matrix recursion checks pass: full build 3612 jobs, Verification
3615 jobs, direct transitive audit 3029 declarations and source guard. Both
Pauli covariance and ordered fourth-moment usage kernel-compile. The fourth
moment simplifier required retaining the covariance linear-map head; expanded
map-sum normal forms were mathematically equal but syntactically different.
No statement or proof requirement was weakened. Main integration pending.

### Checked PR integration: actual matrix covariance/Wick/recursion

[PR #6](https://github.com/T1mberland/lean-free-probability-01/pull/6) merged
head `4a91c65` as `a1f942b`. Main full build 3612, Verification 3615,
direct audit 3029 declarations and source guard pass. Both concrete Pauli
and generic fourth-moment usage pass. Goal 4 remains open as specified above.

### Pending PR: actual projection probability law

Coordinator source `c49bb0d` proves actual spectral concentration on {0,1},
exact ENNReal-weighted Dirac decomposition and identification of the mass at
one with the original state expectation. Finite probability masses give
alpha=Re(phi(p)) in [0,1], hence the actual law
`(1-alpha) delta0 + alpha delta1`. No Bernoulli law, faithfulness or trace is
assumed. Generic `measure_eq_two_dirac_of_concentration` works even without
finiteness, given distinct measurable singleton points. The existing analytic
idempotent S germ is rewritten with the same real trace parameter under its
precise nonzero-first-moment domain. This proves the projection piece of Goal 7,
not free-positive convolution, S multiplication or the product spectral edge.
Read-only review approves all eight statements, with no collisions. Full build
3613 jobs, Verification 3616, direct audit 3038 declarations and source guard
pass. The half-trace two-atom usage kernel-compiles. Main integration pending.
Important proof choices: first power integral determines actual weights;
measure order bounds use pointwise ENNReal add positivity (Measure has no
CanonicallyOrderedAdd instance); native let-bound measures are rewritten through
explicit equality types. No theorem statements were weakened.

### Checked PR integration: actual projection law

[PR #7](https://github.com/T1mberland/lean-free-probability-01/pull/7) merged
head `b718223` as `8d38c42`. Main full build 3613, Verification 3616,
direct audit 3038 declarations and source guard pass with half-trace usage.
Goal 7's projection piece is complete; its full convolution/edge target remains open.

### Pending PR: actual entire exponential IBP

Published B originals `7a17965`, `c2ce33a`, `270ee91`, `3a30233`, `15963db`
are assembled in `49225a7` (original histories retained). Real-ray Banach
Duhamel proves [C,expX]=integral exp((1-u)X)[C,X]exp(uX), with actual continuous
integrands and integrability. For every noncommutative polynomial and EVERY
complex parameter t, actual scalar Fock exponential IBP contracts the genuine
FDQ with exponential sandwiches. Inclusion preserves actual exponentials, so
the same identity holds in the literal faithful tracial generated C-star state.
Finite matrices use a genuine Banach operator norm and same-ring product
completeness, never a falsely asserted C-star norm. Their actual MATRIX
exponential (not entrywise exponentials) satisfies finite double-index FDQ
contraction preserving multiplication order. All five modules have independent
review with no collisions. Full build 3618, Verification 3621, direct audit
3148 declarations and guard pass; mixed actual exponential usage at `t=10i`
compiles. 'Entire' here asserts identities for every complex t, not a separately
proved complex holomorphic derivative theorem. Main integration pending.

### Polynomial resolvent isolation and synchronization

B's focused `feat/polynomial-resolvent-ibp` branches from its published exponential
checkpoint, a justified dependency on actual insertion/sandwich calculus. Sources
`ccc3edd` and `2d34626` prove actual scalar and matrix inverse IBP on WHOLE
resolvent domains with no self-adjointness or exterior-radius restriction.
The inverse is of the matrix itself, never of each entry. Coordinator synced
clean `2d34626` with checked main `8d38c42` as `66eab22`, pushed immediately,
then focused builds and source guard passed in B's actual worktree. B now reuses
the integrated generic inverse homomorphism helper and published `31e3618`
for closed scalar-state transport; matrix closed-state transport is active.
Only coordinator performs integration merges; workers own disjoint new files.

### Checked PR integration: entire scalar and matrix exponential IBP

[PR #8](https://github.com/T1mberland/lean-free-probability-01/pull/8) merged
head `a7dfb5c` as `9715c11`. Main full build 3618, Verification 3621,
direct audit 3148 declarations and source guard pass, including mixed actual
exponential usage at unrestricted large imaginary parameter. PR #6 CI run
`38541695353` and #7 run `38542953659` also subsequently succeeded.

### Pending PR: actual affine matrix resolvent Dyson

A originals `81f634c`, `aad1504`, `3497b44`, `88c578b`, `b875863`,
`ada440a`, `4614f12` are assembled as `476449e` with original history retained.
The formal centered moment-series equation and uniqueness, actual affine moment
recursion and affine formal equation are explicitly formal/moment statements.
Separately, actual CStarMatrix operator resolvents and rank-one boundary
commutators prove the full actual inverse Dyson equation. Arbitrary deterministic
matrix argument B has domain exactly IsUnit(embed B-H), preserving noncommuting
matrix order. Actual m is the entrywise vacuum of the WHOLE actual inverse.
The identity (B-eta(m))m=I makes det(m) invertible, hence m is genuinely
invertible; actual inverse Dyson follows. Substituting B=zI-C0 proves actual
affine m(z)^-1=zI-C0-eta(m(z)) on the entire resolvent set. Hermitian C0 and
coefficients imply every nonreal z lies in the actual domain, without positivity,
commutation or exterior radius assumptions. The finite empty-matrix case is
handled by the actual determinant-one/trivial-ring identities.
All seven modules have mathematical review and no collisions. A concrete
noncommuting Hermitian drift/coefficient example at z=I kernel-compiles.
Combined build/audit counts are recorded below; main integration pending.
General arbitrary-base covariance realization, half-plane/exterior positivity,
physical uniqueness and entrywise/reduced model matching remain Goal 4 obligations.

### Worker feature regression and isolated next tasks

A `8775e6e` was published with a linter-cleanup proof regression after a failed
verification result was overlooked. It was reported immediately, never integrated
or certified, and corrected by pushed `efc7f32` after inspected successful focused
build/axiom/guard checks. Root's current Dyson PR pins earlier verified `4614f12`.
Worker-owned `docs/math-notes/matrix-development.md` at `dfd75d8` records the
regression, inverse proof design and precise remaining blockers. Future integration
must include both regression and correction, verify the combined tree, and avoid
claiming standalone `8775e6e` verified. Strict matrix imaginary positivity is active,
using actual vacuum-vector norm and inverse action, without faithfulness on all
bounded Fock operators. The PSD corrected feature is not yet integrated.
B's whole polynomial resolvent branch completed/pushed at clean `8ac8c1a` and
has mathematical review. Coordinator reassigned its clean worktree to
`feat/analytic-series-ibp` from checked `9715c11`, preserving the published
resolvent branch. Exclusive new FockAnalyticSeries modules prove genuine norm
convergence with explicit value and derivative coefficient bounds; no central
files or A-owned Matrix modules are shared.

Actual affine Dyson combined checks pass: full build 3625 jobs, Verification
3628 jobs, direct transitive audit 3295 declarations and source guard.
Noncommuting Hermitian affine usage at z=I compiles. Main integration pending.

### Checked PR integration: actual affine inverse Dyson

[PR #9](https://github.com/T1mberland/lean-free-probability-01/pull/9) merged
head `620695f` as `e7f693e`. Main full build 3625 jobs, Verification 3628,
direct audit 3295 declarations and source guard pass, including noncommuting
Hermitian drift/coefficient usage at z=I. Goal 4 remains open as specified.

### Pending PR: actual full-domain polynomial resolvent IBP

Published B originals `ccc3edd`, `2d34626`, `31e3618`, `8ac8c1a` (with
coordinator prerequisite sync `66eab22`) are assembled as `48a940a`, retaining
history. Generic complex-algebra inverse commutator, actual scalar/matrix
polynomial FDQ insertions and genuine full-matrix inverses give resolvent IBP
at every actual invertibility point, with no self-adjointness, radius, or
entrywise inverse premise. Closed scalar-state transport proves exact intrinsic
and ambient domains via spectral permanence; closed matrix transport covers
ALL intrinsic matrix resolvent points using true whole-inverse homomorphism
compatibility. Reverse matrix domain equality is optional and not assumed.
All four sources independently reviewed, with no collisions. Full code build
3629 jobs, Verification 3632, direct audit 3337 declarations and source guard
pass; ordered two-letter usage keeps the correct boundary factor. Its polynomial
field was explicitly annotated ℂ, and singleton FDQ expanded before FreeMonoid
simplification; the actual theorem/domain was unchanged. Main integration pending.

### Independent next cycle after analytic sources published

B completed/pushed analytic-series feature through clean `3047563`; all final
scalar/matrix/closed wrappers now reviewed. Literal Goal 3 audit confirms full
checklist once polynomial resolvent and analytic series integrations/main checks
and usage pass. Norm-analytic series require explicit value AND derivative
absolute bounds; no optimal convergence radius, unrestricted value-only
FDQ-convergence or general contour calculus is claimed. B was reassigned from
clean `3047563` to `feat/wick-contractions` from checked `e7f693e`, preserving
all published analytic branches. New isolated WickProduct/WickNorm files target
actual normal order, reverse-overlap contraction and norm bounds for Goal 10.
Normal-order source `ea7aa32` had a transient GitHub server push rejection
`fatal error in commit_refs`. Local commit was preserved and further writes held;
a second normal push succeeded immediately, with upstream confirmed. No unresolved
publication blocker remains. Single-word bound `128a21f` is also published.
These are not yet integrated OU/entropy results. A's strict imaginary positivity
and normalized analytic physical-branch results are published/reviewed in part
and queued separately; global pointwise-root uniqueness remains unclaimed.

### Checked PR integration: whole-domain polynomial resolvents

[PR #10](https://github.com/T1mberland/lean-free-probability-01/pull/10) merged
head `1fd8768` as `287bcf7`. Main full build 3629, Verification 3632,
direct audit 3337 declarations and source guard pass, with ordered-polynomial
boundary usage. No restriction to self-adjoint polynomials or exterior radii.

### Pending PR: complete requested norm-analytic IBP

B originals `6c67499`, `7599c97`, `54efb25`, `67dadbb`, `3047563`
are assembled as `a79418d`, original history retained. Actual Banach sums
`analyticSeries c X` and continuous commutators preserve operator order at
every power cut. Explicit absolute value bound ensures value convergence;
explicit derivative bound ensures absolute convergence of every contracted FDQ
cut series. Core commutator mapping needs only the value bound, while the public
polynomial derivative convergence uses both bounds. Scalar and full-matrix
polynomial IBP, including actual faithful tracial closed-state versions, follows
from actual rank-one insertions and continuous maps of genuine sums.
Matrix norms are explicitly coherent Banach row-sum norms, not falsely C-star
norms; unit norm for entry theorems is derived from r:N and scalar vacuum,
with no added nonempty target premise. Empty matrices are covered in transport.
All five modules independently reviewed, no collisions. Literal Goal 3 review
confirms the intended checklist is covered after these sources and the already
integrated polynomial/exponential/resolvent calculus pass main checks and usage.
A true infinite geometric example c_n=(1/4)^n verifies BOTH convergence bounds
against the actual norm-two field, not merely assuming them. It kernel-compiles.
General contour calculus, optimal radii, unrestricted value-only FDQ convergence
and independently chosen-model coherence are not claimed or required for this goal.
Combined counts are recorded below; main integration and certification pending.

Feature integration checks passed: full build 3634 jobs, Verification 3637,
direct transitive axiom audit 3497 declarations and source-integrity guard.
All counts are for the combined integration branch including the concrete infinite
geometric-series usage. Publication and checked main certification follow via PR.

### Checked analytic-series PR and Goal 3 certification

PR #11 merged head `0680326` as `57062543a2a255925fe1433d617444adca28aaa5`.
Main full 3634, Verification 3637, direct audit 3497 and source guard pass.
Independent literal checklist review plus actual infinite geometric-series usage
certify Goal 3. Goals 1, 2, 3 and 6 are complete; seven full targets remain open.

### Pending Wick contraction and homogeneous norm integration

Published worker branch `feat/wick-contractions` at `4594b56` is preserved and
merged into `feat/integrate-wick-norms`, with original atomic history. Ten modules
prove actual normal ordering, reversed suffix/prefix contraction products, creator
Gram/Bessel estimates, coefficient-preserving tuple cuts and the general finite
homogeneous Haagerup bound: operator norm at most (degree+1) times actual vacuum
Hilbert norm. Arbitrary color sets, degree zero and empty color sets are covered.
Independent mathematical review approves the exact operator statements.
This is Goal 10's Wick prerequisite, not completely positive OU or entropy.
B's clean worktree switched from published `4594b56` to `feat/second-quantization`
from checked `5706254`, with exclusive NEW Fock/SecondQuantization*.lean ownership.
It targets actual full-Fock lifts of one-particle Hilbert unitaries, vacuum/tensor
grading and creator conjugation for eventual rotation dilation. No assertion that
arbitrary complex unitaries preserve a chosen real semicircular algebra is made.
A continues exclusive new OperatorValued/Matrix*.lean edge variational work;
reviewer remains read-only. Coordinator alone owns integration and central files.

Combined Wick feature passes full build 3644, Verification 3647, direct audit
3594 declarations and source guard. Concrete degree-two Wick square verifies
all three surviving operator contractions; its first attempt differed only by
addition order and was repaired with commutativity, without statement changes.
CI for PRs #8, #9 and #10 is confirmed successful (runs 38544010777,
38545132352, 38548126213); PR #11 run 38551786693 remains in progress.

### Checked Wick PR and pending physical matrix integration

PR #12 merged head `c1522bc` as `be0f1635216209e18c7f5e1681b6fc0d1203c21e`.
Main passes full 3644, Verification 3647, direct audit 3594 and source guard.
General homogeneous Wick inequality and all reversed-overlap products are now
integrated; OU CP/normal/Lp/entropy remain open.

Physical sources through `6692fe8` are preserved on `feat/integrate-matrix-physical`.
Twelve new modules include the previously reported failed `8775e6e` imaginary-part
cleanup ONLY WITH its corrective `efc7f32` and later Gram/strict-positivity fixes.
No claim is made that the failing intermediate commit alone was verified.
Actual analytic derivative is minus the expectation of the true squared inverse.
Normalization is z*m(z) to identity at infinity; normalized analytic Dyson
uniqueness holds on connected unbounded open domains, specialized to upper half
plane. This is not arbitrary fixed-argument root uniqueness. Strict actual
negative imaginary part uses invertible vacuum Gram vectors, without pretending
faithfulness on all bounded Fock operators. Full right spectral exterior gives
actual inverse positivity and actual m positive definite, including empty matrices.
Actual derivative of Dyson gives d=-m*m+m*eta(d)*m, preserving order.
Explicit norms: expectation entry control uses elementwise supremum; covariance
contraction uses row operator norm. No unsupported C-star contractivity is asserted.
Read-only reviewer approves corrected chain and new coreedge `094e84d` separately;
physical PR precedes distinct edge PR, preserving precise scopes and atomic history.

Combined physical integration passes full build 3656 jobs, Verification 3659,
direct audit 3707 declarations and source guard. The noncommuting drift/Pauli
coefficient example at z=I proves STRICT negative imaginary part. Its missing
ComplexOrder scope was a genuine example elaboration error, fixed locally;
no resource/stale-artifact failure or mathematical statement change occurred.
The twelve mathematical modules compiled before that example repair.

### Checked physical matrix PR and pending exact edge integration

PR #13 merged head `44044e9` as `3f6b367201402627452e38deccdcefc5609c8675`.
Main passes full 3656, Verification 3659, direct audit 3707 and source guard.
Actual negative-imaginary positivity, normalized analytic physical branch, full
right-exterior positivity and actual derivative/Lyapunov are integrated.
Goal 4 remains open for arbitrary base C-star CP-covariance and entrywise models.

Worker original edge sources `5f94a49`, `872b04d`, `fb67bf9`, `0eebeb2`,
`094e84d` and updated design notes `3983e9c` are preserved in a separate edge
integration branch. Actual creator Gram gives completion square and every
positive definite Z an operator comparison. Actual largest Hermitian-matrix
eigenvalue is proved equal to real spectral maximum. Sharpness is not assumed:
for EVERY x above the genuine real-operator spectral maximum, Z=m(x)^-1 is
positive definite and makes the variational matrix EXACTLY xI by actual Dyson.
Infimum nonemptiness/lower boundedness and midpoint argument give the reverse
inequality, without asserting an optimizer at the edge. Matrix size nonempty
is natural for the actual nonempty top spectrum/eigenvalue; color set may be empty.
ALL positive definite tests and arbitrary Hermitian coefficients are allowed.
Independent read-only reviewer approves full equality, correcting its earlier
upper-bound-only review before `094e84d` existed. Usage constructs this exact
positive test for a noncommuting diagonal drift and swap coefficient.
Goal 5 remains open beyond the core formula and actual exterior/Lyapunov pieces.

### Independent next queue: multiplicative convolution analytic route

Read-only research identifies a smaller centered-resolvent proof using existing
moment inverse right-uniqueness instead of unproved formal boxed inversion.
First tasks: positive sandwich sqrt(a)b sqrt(a) actual spectral law and cyclic
trace equality of all its powers with (ab)^n; generic continuity of freeness under
norm closure, ensuring the centered actual inverse factors are free.
For alpha=chi_a(w), beta=chi_b(w), c=1+w, A=(1-alpha*a)^-1,
B=(1-beta*b)^-1, x=A-cI and y=B-cI, exact inverse algebra should yield
A(1-gamma*ab)B=c(I-xy/(wc)), with removable gamma=c*alpha*beta/w.
Centered factors x,y are order w, hence the actual geometric inverse converges
near zero. Alternating freeness makes expectation of B(xy)^n A zero for n>=1,
while n=0 gives c^2. Actual inverse germ uniqueness then gives S_ab=S_a*S_b;
cyclic moment equality transfers this to the positive sandwich. THESE ARE
UNPROVED TASKS, not accomplished results. Actual convolution on arbitrary
positive compact laws also needs general positive free realization (Goal 11).
Known formal obstruction: boxed cumulant formula alone does not supply the
Lagrange/tree inverse-moment identity or the formal-to-analytic coefficient bridge.
Useful existing names: cumulant_prod_eq_kreweras_sum,
TransformNaturality.momentInverse_eq_of_eventually_right_inverse,
sTransform_eventually_eq_of_powerMoments, hasSum_expectation_inverse.

Combined edge feature passes full build 3661 jobs, Verification 3664, direct
transitive audit 3770 declarations and source guard. The concrete noncommuting
exact-witness example compiles. PR #11 CI run 38551786693 is now confirmed
successful; later PR CI results will be tracked separately from local checks.

### Checked core-edge PR and pending actual state/density inequalities

PR #14 merged head `a96b320` as `06f8254cea94a1595923028b1724ab6ac743c329`.
Main full 3661, Verification 3664, direct audit 3770 and source guard pass.
Core exact finite-matrix variational formula is integrated; Goal 5 stays open.
PR #12 CI 38552187192 and #13 CI 38552538959 were still in progress at last check.

Worker sources `4246351` and `ae23f1c` preserved on state-bound integration branch.
Weighted CS is derived from genuine normalized positive scalar-state CS with
actual positive square root of Z. Summation/AMGM and genuine Hermitian-matrix
spectral order give each variational test's lower bound; the already proved
actual infimum theorem gives actual edge at least Re(phi C0)+2sqrt(sum|phi Ci|²).
No traciality of the arbitrary state is needed, and no desired edge premise is
added. Actual density state tr(rho X) is constructed for ALL PSD rho of trace1,
including singular rho, with star/positivity/normalization genuinely proved.
Cyclic trace of actual conjugate Gram gives positivity. Both statements reviewed
without mathematical blocker or declaration collisions. Concrete singular rho
=diag(1,0) tests diagonal drift and two noncommuting Pauli coefficients for b>=3.

A's next exclusive new MatrixCauchySpectralBounds.lean derives actual
0<m(x)<=(x-b)^-1 I for every x>b from CFC inverse order and positive unital E,
without restricting to x>norm(H). B continues independent SecondQuantization*.lean.
The quantitative Fock depth blocker is exact shifted degree-window equivalence:
left creation preserves right tails, giving copies of the depth-N compression.
Uniform degree windows should count diagonal energy N times and offdiagonal
energy N-1 times, suggesting explicit b_N<=b<=b_N+2||L||/N (UNPROVED).
Creator Gram supplies ||L||²=||sum Ci²||; a Rayleigh/spectral-sup bridge is also
needed. Sine-window refinement to O(N^-2) requires further trigonometric work.
Generic normclosure freeness is a shorter independent Goal 7 prerequisite.

Combined state/density integration passes full build 3663, Verification 3666,
direct axiom audit 3784 and source guard. Concrete singular-density b>=3 example
passes. Worker-owned notes update `74d0cfd` is integrated without modifying the
worker's checkout. Independent reviewer approves both general states and densities.

Read-only closure-freeness research gives a precise minimal proof: for fixed
alternating labels, expectation of the product of centered coordinates is a
continuous function on the finite product. Original freeness makes it zero on
product of original algebras. `closure_pi_set` and the closed zero preimage extend
it to product of closures. Expectation continuity suffices; no positivity,
traciality or completeness is needed. `ProbabilitySpace.center_mem`,
`expectation_center`, `center_of_expectation_eq_zero`, `continuous_list_prod`
and `List.ofFn_get` supply the intended interfaces. This task is still unproved.
