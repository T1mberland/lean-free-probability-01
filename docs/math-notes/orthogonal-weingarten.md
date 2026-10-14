# Genuine stable orthogonal Weingarten integration

Verified milestone `e4b842f` on `feat/compact-haar-averaging`:
`RandomMatrix/OrthogonalWeingarten.lean`, depending on actual stable invariant
spanning `3f66716`, zero-step `cd608f9`, and notes `d885a9f`, all frozen.

## Exact full entry-integration result

`entryMoment_eq_weingarten_delta_sum` proves, for ALL actual index tuples
 i,j : Fin(2r) -> n with N = card n >= r,

entryMoment(i,j) = sum over ALL intrinsic ordinary pairings p,q of
 delta_p(i) * (ordinaryPairingGram n r)^(-1)(p,q) * delta_q(j).

The deltas are LITERAL products of the paired Kronecker indicators. The left
side is the GENUINE Bochner integral of the actual product of matrix entries
against normalized orthogonal Haar probability. The inverse is the literal
actual matrix inverse, proved earlier to exist with both inverse identities.
Crossing pairings are included; redundant site codes are quotiented by their
raw ordinary pairing relations before summation. The formula includes order
zero and all stable-dimension degenerate cases.

`tensorPowerAverage_eq_pairingGram_inverse` proves the actual Haar projection
formula for ANY vector in the genuine tensor representation, not merely basis
vectors. Actual invariant span supplies a genuine finite expansion of the
averaged vector. Integrating inner products against the actual fixed pairing
vectors gives Gram*c = the vector of original inner products. The actual inverse
then determines c. Evaluating the projection of the actual tuple basis vector
and using the verified averaging/entryMoment identification yields the formula.

There are NO assumed integration, pairing, projection, invariant spanning, Gram
or inverse premises. All are kernel-verified dependencies. The explicit
restriction N >= r remains part of the intended stable result.

## Verification and remaining obligations

The focused module compiles warning free under the shared lock. Three public
principal declarations passed transitive standard-logic audits, and the literal
Kronecker-delta entry statement was inspected. Integrity guard and staged diff
checks passed before the atomic commit, immediately pushed.

Failed elaborations involved bundled projection evaluation and matrix/function
transparency during rewriting. Explicit typed intermediate equalities repaired
the proof; no hypothesis or statement was weakened.

The general LOW-DIMENSION N < r invariant-spanning and pseudoinverse integration
problem is still open. General joint asymptotic freeness is also not claimed by
an exact integration formula. Next useful stable prerequisites are normalized
Gram convergence N^(-r)G -> I, continuity of its actual inverse and asymptotic
Weingarten weight estimates, followed by genuine joint word contraction bounds.
Expected normalized traces, convergence in probability, almost-sure moments and
strong convergence require their own estimates and hypotheses. Integration and
goal certification remain coordinator responsibilities.
