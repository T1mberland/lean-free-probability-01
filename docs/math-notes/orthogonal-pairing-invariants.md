# Actual ordinary pairing invariant tensors

Verified milestone `c7a8dc1` on `feat/compact-haar-averaging`:
`RandomMatrix/OrthogonalPairingInvariant.lean`, depending on actual tensor
representation and projection `2196e3f` and notes `5a2f0e8`.

## Precise proved statements

`PairingSites r` is an ARBITRARY site equivalence
`Fin (2*r) ≃ Fin r × Fin 2`. It specifies all ordinary ordered pairings;
no noncrossing predicate is imposed, and crossing pairings are allowed.

`pairingTensor e` is the ACTUAL Euclidean tensor vector obtained by summing
literal tuple-coordinate basis vectors over all assignments of coordinate labels
to pairs. No invariance or abstract tensor-spanning property is assumed in its
definition.

`pairingTensor_coefficient` proves that each actual coordinate is exactly the
product of paired Kronecker deltas. Its proof reduces the genuine basis sum using
finite tuple factorization, not an assumed indicator formula.

`pairingTensor_invariant` proves that EVERY such vector is ACTUALLY fixed by
EVERY orthogonal matrix under the genuine arbitrary-order tensor representation.
It expands the actual finite sum, factors the full tuple sum into one contraction
per pair, and uses the actual row orthogonality U U^T = I. Consequently
`pairingTensor_mem_fixedVectors` proves actual invariant-subspace membership and
`tensorPowerAverage_pairingTensor` proves the genuine Haar integral fixes it.

The statements cover all r and finite coordinate types n, including r = 0 and
empty n. They do not require a generic-dimension or nonempty-index hypothesis.

## Verification and remaining obligations

The focused module compiles warning free under the shared lock. Four principal
declarations passed transitive standard-logic audits; actual coefficient and
invariance statements were inspected. Integrity guard and staged diff checks
passed before the atomic commit, which was immediately pushed.

Failed elaborations concerned Euclidean coordinate evaluation commuting with
finite sums, PiLp rather than WithLp extensionality, and explicit dependent
function arguments for reverse Fintype.prod_sum rewriting. These were corrected
without statement changes or extra mathematical premises.

This proves the pairing vectors lie IN the actual invariant subspace. It does
NOT prove that they SPAN every invariant tensor. The orthogonal first fundamental
theorem is the precise remaining general integration obligation. Intrinsic
perfect-matching quotient interfaces, pairing Gram entries and their closed
loop-count formula, and inverse/pseudoinverse treatment of low-dimensional
linear dependencies are useful further prerequisites. No Weingarten formula,
joint asymptotic freeness, probability/almost-sure convergence or strong
convergence is claimed. Goal certification and integration remain coordinator-owned.
