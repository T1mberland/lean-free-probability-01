# Genuine leading orthogonal Weingarten asymptotics

Verified mathematical milestones on `feat/compact-haar-averaging`:

- `d6d807b`, `RandomMatrix/OrthogonalPairingLoopBounds.lean`.
- `2e93cc9`, `RandomMatrix/OrthogonalWeingartenAsymptotics.lean`.

These depend on the frozen TRUE stable entry integration formula `e4b842f` and
its notes `17bd38e`. Integration and goal certification are coordinator-owned.

## Exact results

`pairingLoopCount` counts ACTUAL classes of the raw ordinary pairing join.
`pairingLoopCount_le` proves at most r classes. `pairingLoopCount_eq_iff` proves
that r classes occur PRECISELY when the intrinsic pairing indices agree;
`pairingLoopCount_lt_of_ne` gives strict off-diagonal decay. These proofs use the
actual surjective quotient map and finite-cardinality injectivity, not an assumed
combinatorial metric or a noncrossing closure.

`normalizedPairingGram r N` is the literal matrix N^(-r)*G(Fin N,r).
`tendsto_normalizedPairingGram` proves this TRUE matrix converges to the identity
as the natural coordinate dimension N tends to infinity. Every entry is an
actual power N^(-(r-loops)); the loop theorem supplies diagonal exponent zero
and strictly positive off-diagonal exponents.

`tendsto_normalizedPairingGram_inverse` uses genuine determinant-based continuity
of the LITERAL nonsingular matrix inverse at the identity. It is not a formal
power-series inverse or an assumed inverse limit.

`normalizedPairingGram_inverse_eq` identifies this inverse with the true rescaled
Weingarten matrix N^r*G^(-1) in stable nonzero dimension. The eventual hypotheses
N >= max(r,1) are derived automatically when taking the limit. Consequently
`tendsto_rescaledPairingGram_inverse` proves the matrix limit I and
`tendsto_rescaledWeingartenWeight` proves, for EVERY intrinsic p,q,
N^r*G(Fin N,r)^(-1)(p,q) -> delta_(p,q).

No limit, inverse, projection, spanning, entry-integration or random-word freeness
premise is assumed. Each is a proved actual dependency. Order zero is included;
finite initial degenerate dimensions do not affect the at-infinity limit.

## Verification and remaining estimates

Both modules compile warning free under the common build lock. Principal
statements passed transitive standard-logic audits; the literal rescaled weight
limit was inspected. Integrity guard and staged diff checks passed before atomic
commits, all immediately pushed.

Failed elaborations concerned equality orientation, actual matrix scalar evaluation,
a root/matrix inverse-multiplication name collision, and diagonal substitution
inside an eventual equality. They were repaired without changing statements.

The leading weight limit is a genuine ASYMPTOTIC PREREQUISITE, not a proof of
joint random-matrix asymptotic freeness. Next useful estimates are explicit
O(1/N) rescaled-error bounds, stronger loop-distance decay and contraction bounds
for actual joint trace words. Probability, almost-sure and strong convergence
require their own further arguments. Low-dimension invariant spanning and
pseudoinverse integration also remain separate obligations. No full Goal 9
completion is asserted by these checkpoints.
