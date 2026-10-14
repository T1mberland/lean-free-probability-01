# Genuine ordinary pairing Gram and dimension powers

Verified mathematical milestone `fead3e2` on `feat/compact-haar-averaging`:
`RandomMatrix/OrthogonalPairingGram.lean`. It depends on genuine pairing
invariance `c7a8dc1` and its notes `137fd46`, both frozen.

## Exact achieved statements

`pairingSetoid e` is the ORDINARY equivalence relation on actual sites obtained
as the kernel of the pair-number map of an arbitrary `PairingSites r` code.
Crossing pairings are permitted. Its join is the raw Setoid lattice join,
not a noncrossing closure or a restricted partition join.

`pairingTensor_coefficient_indicator` identifies a genuine tensor coefficient
with the indicator of actual coordinate labelings constant on this pairing
relation. `sum_quotient_colorings` counts compatible labelings via the actual
`Setoid.liftEquiv`, which identifies them bijectively with functions from the
actual quotient classes to the coordinate type.

`pairingTensor_inner` proves the TRUE Euclidean Gram entry
inner(pairingTensor e, pairingTensor f) =
(card n) ^ card(Quotient(pairingSetoid e join pairingSetoid f)).

`card_pairingSetoid_quotient` proves a pairing has exactly r classes.
`pairingTensor_norm_sq` consequently proves the actual squared norm is (card n)^r.
`pairingTensor_eq_of_pairingSetoid_eq` proves that redundant pair numbering or
orientations in a code do not change the actual tensor when its pairing relation
is unchanged.

Every statement covers all r and finite n, including empty n and r = 0. The
zeroth-order scalar tensor correctly has norm squared 0^0 = 1. No lower dimension
bound, genericity, linear independence or Gram invertibility is assumed.

## Verification and precise remaining obligations

The focused module compiles warning free under the shared build lock. Six principal
declarations passed transitive standard-logic audits, and literal Gram and norm
statements were inspected. Integrity guard and staged diff checks passed before
the atomic commit, which was pushed immediately.

Failed elaborations involved explicit raw Setoid relation unfolding, the explicit
map argument of quotient-kernel equivalences, and the lattice identity spelling
`sup_idem`. All were corrected without changing intended statements.

The Gram formula does NOT prove that ordinary pairing vectors span ALL invariant
tensors. The orthogonal first fundamental theorem remains the precise missing
integration theorem. Stable-dimension independence/invertibility and general
low-dimensional pseudoinverse treatment are separate linear algebra prerequisites;
raw PairingSites codes themselves are redundant and cannot constitute an
independent basis. General matrix-entry Weingarten formulas and joint asymptotic
freeness are not claimed. Expected traces, convergence in probability, almost-sure
moments and strong convergence remain distinct open strengths. Goal certification
and integration are coordinator-owned.
