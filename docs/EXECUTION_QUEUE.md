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

| Goal | Status | Earliest work and dependency |
| --- | --- | --- |
| 1. Cumulant calculus | Active; one implication already verified | Pairings, interval/deletion/insertion maps, unit insertion and adjacent products, then freeness implies mixed vanishing; Kreweras/lattice/product calculus remains |
| 2. Full Fock systems | Active; concrete complete word model integrated | General tensor-power identification, joint Wick, norm two, freeness and faithful tracial generated algebra remain |
| 3. Free integration by parts | Ready for algebraic groundwork | Polynomial tensor-bimodule derivations independent of Fock; semicircular integration-by-parts requires Wick recursion |
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
| Worker A (`cumulants`) | `feat/cumulant-characterization`, `/home/user/Projects/lean-fp-cumulants` | New cumulant-related `Combinatorics` and `Algebraic` files; existing `Algebraic/CumulantFreeness.lean` if needed | Unit/scalar/centering cumulants published; adjacent products and reverse freeness next |
| Worker B (`fock`) | `feat/fock-semicircular`, `/home/user/Projects/lean-fp-fock` | New `Fock` and `Semicircular` files | Closed faithful/tracial generated state published; exact norm two, freeness and full Wick next |
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

- Following pairing fundamentals: construct noncrossing interval restriction and
  deletion/insertion equivalences; prove unit insertion, then adjacent products.
- Following creation operators: vacuum action and adjoint relations, semicircular
  second moments/selfadjointness, right operators and Wick recursion.
- When a worker becomes available: polynomial free difference quotient Leibniz
  rules, or spectral-measure representation prerequisites, with exclusive files.

Update this ledger at each integration checkpoint with exact declarations, commit
hashes, checks, failed approaches and newly unblocked tasks.
