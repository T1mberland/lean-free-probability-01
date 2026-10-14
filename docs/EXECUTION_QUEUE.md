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
- All eleven goals remain open. Existing results and their scope are listed in
  the dependency audit; none is considered complete merely by having a module.

## Goal status and dependency-aware queue

Latest checked integration: `1708387`, published on `main`, with full builds,
source guard and transitive audit passing for 1336 declarations. Unit/full-centering
calculus, adjacent raw merges/refinement fibers and norm-two/C-star model are integrated.
Ordered fusion/duplicated-block transports and genuine closed-generator freeness
feature milestones are published but await integration. Historical checkpoints
below retain the state at each checkpoint; this paragraph records current status.

| Goal | Status | Earliest work and dependency |
| --- | --- | --- |
| 1. Cumulant calculus | Active; one implication and unit/scalar calculus integrated | Adjacent-product contraction fibers, then freeness implies mixed vanishing; pairing decomposition, Kreweras and Möbius/product calculus remains |
| 2. Full Fock systems | Active; faithful tracial C-star word model with exact norm two integrated | Integrate published freeness; general tensor-power identification, joint Wick, Catalan and spectral law remain |
| 3. Free integration by parts | Active proof path selected | Right-annihilation vacuum-boundary commutator and telescoping word recursion; polynomial tensor-bimodule derivation bundling and matrix/analytic extensions remain |
| 4. Operator-valued Dyson | Blocked on semicircular realization | Completely positive covariance, amplified moments and Wick recursion precede Dyson and physical branch |
| 5. Spectral edges | Blocked on goals 2, 4 and 6 | Faithful pencils and spectral/Dyson theory precede variational identity and certificates |
| 6. Spectral distributions | Independent research ready | Continuous functional calculus and positive-functional representation precede spectral measure and faithful support identification |
| 7. Multiplicative convolution | Blocked on goals 1, 2 and 6 | Positive realizations, S-transform multiplication and actual spectral laws; rational critical-point computations are supporting special cases |
| 8. Conditional subordination | Blocked on goals 6 and 7 and noncommutative L² | Normal conditional expectations, analytic subordination, then exterior continuation and projection specialization |
| 9. Haar freeness | Independent algebraic groundwork ready | Haar-unitary star law and free conjugation; general orthogonal pairing integration precedes asymptotic trace estimates |
| 10. OU and entropy | Blocked on Wick and tracial realization | Wick basis/contractions, completely positive second quantization, normal noncommutative Lᵖ and entropy precede dimension-independent bound |
| 11. Follow-up milestones | Open; select after prerequisites | Positive free products, R-additivity/CLT, operator-valued cumulants, annular and genus theory have separate dependencies |

## Active assignments and isolation

| Role | Branch / worktree | Exclusive ownership | Current milestone |
| --- | --- | --- | --- |
| Coordinator | `main`, `/home/user/Projects/lean-free-prob` | Central imports, verification, configuration, ledgers, integration | Review, integrate verified branches sequentially, publish, select successive milestones |
| Worker A (`cumulants`) | `feat/cumulant-characterization`, `/home/user/Projects/lean-fp-cumulants` | New cumulant-related `Combinatorics` and `Algebraic` files except B's reserved pairing-decomposition file; existing `Algebraic/CumulantFreeness.lean` if needed | Exact adjacent fibers published; ordered fused-block transport and product identity, then reverse freeness |
| Worker B (`fock`) | `feat/fock-semicircular`, `/home/user/Projects/lean-fp-fock` | New `Fock`/`Semicircular` files and exclusively `Combinatorics/NoncrossingPairingDecomposition.lean` | Closed freeness and C-star bridge published; sync main, right-annihilation moment recursion/IBP, then pairing split and literal NC Wick |
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
