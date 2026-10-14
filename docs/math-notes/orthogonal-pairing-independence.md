# Genuine pairing independence and stable Gram inverse

Verified checkpoints on `feat/compact-haar-averaging`:

- `112feb9`, `RandomMatrix/OrthogonalPairingIndependence.lean`.
- `a25584a`, `RandomMatrix/OrthogonalPairingInvertible.lean`.

These depend on the frozen actual pairing Gram chain through `fead3e2` and its
notes `e3f49cd`. Integration and goal certification remain coordinator-owned.

## Exact mathematical results

`OrdinaryPairing r` is the quotient of site codes by equality of their RAW
ordinary pairing Setoids. This removes redundant pair numbering and orientation
BEFORE any independence claim. The actual intrinsic tensor is obtained from a
representative; earlier actual coefficient formulas ensure this is the same
mathematical tensor for every equivalent code.

`ordinaryPairingTensor_isolating_coefficient` constructs a genuine tuple colored
with r DISTINCT coordinate labels and proves evaluation there is one for the
selected intrinsic pairing and zero for every other one. It uses the actual
Kronecker-delta coefficient theorem and the fact that refinement of two pairings
with the same r quotient classes forces equality.

`ordinaryPairingTensor_linearIndependent` proves the ACTUAL family of ALL
intrinsic ordinary pairing tensors is linearly independent when N = card n >= r.
The proof evaluates a genuine zero linear combination at each isolating tuple.
It allows crossing pairings, includes r = 0 and N = 0, and does not assume any
invariant-tensor spanning statement or Gram invertibility.

`ordinaryPairingGram_eq_gram` identifies the exact dimension/quotient-class
loop-count matrix with the TRUE Euclidean Gram matrix of the actual tensors.
`ordinaryPairingGram_posSemidef` holds in ALL dimensions. When N >= r,
`ordinaryPairingGram_posDef`, `ordinaryPairingGram_det_ne_zero` and
`ordinaryPairingGram_isUnit` prove genuine strict positivity and invertibility.
`ordinaryPairingGram_inverse` proves BOTH literal matrix inverse identities.
Small-dimension degeneracies are not hidden by asserting invertibility there.

## Verification and interrupted-state recovery

The independence source was preserved untracked across a deliberate interruption.
On resumption, the authoritative isolated feature worktree was revalidated and
two final elaboration failures were repaired: equality of Setoid images cannot
be substituted as equality of their codes, and a conditional rewrite required
simp rather than proposition-dependent rewrite transport.

Both modules compile warning free under the common lock. Important declarations
passed transitive standard-logic audits; exact independence and both inverse
statements were inspected. Integrity guard and staged diff checks passed before
each atomic commit, and every commit was pushed immediately.

## Precise remaining spanning obligation

Independence and a true Gram inverse do NOT imply the pairing tensors span ALL
invariant tensors. The orthogonal first fundamental theorem remains unproved.
A proposed stable-dimension route is to subtract a pairing combination agreeing
on distinct-color two-site block tuples, then prove the remaining invariant tensor
zero by induction on its number of used colors. Reflections kill odd color counts;
a repeated even block of size at least four has an unused coordinate when N >= r.
A genuine 45-degree plane rotation splits that block, and proper splits use more
colors while the two unsplit endpoints have equal coefficients by permutation
invariance. This could force the residual coefficient to vanish. None of those
rotation/recurrence or spanning steps is claimed proved by these checkpoints.
All-dimension spanning, general entry integration, asymptotic freeness and its
probability/almost-sure/strong convergence strengths remain separate obligations.
