# Actual positive bounded inverse of the shifted number operator

This checkpoint constructs the literal degree-weight map on the whole complete
`TensorFullFock H` and proves that it is exactly the two-sided inverse of `N+1`
with the previously verified weighted-square-summability operator domain. The
original complex Hilbert space is arbitrary and complete, including the zero
space; no cardinality or finite-dimensionality hypothesis is added.

## Verified source milestones

- `cd7787d`, `OrnsteinUhlenbeckNumberResolvent.lean`:
  `numberResolventWeight n` is the real positive scalar `1/(n+1)` viewed in ℂ.
  Its norm and the norm of `n * numberResolventWeight n` are both at most one.
  `numberResolvent H` is an actual continuous linear map on every completed
  Fock vector, with precisely those coordinate weights. Both its vector norm
  bound and its operator norm bound are at most one.
- `3024532`, `OrnsteinUhlenbeckNumberResolventInverse.lean`:
  `numberResolvent_mem_domain` proves that EVERY ambient vector is sent into
  the EXACT domain `{f | Memℓp (fun n => n • f_n) 2}`. The actual
  `numberResolventDomain` has that proved subtype-valued output.
  `numberShift` is literally the domain-restricted operator `N+1`.
  Both identities are verified:

  `numberShift (numberResolventDomain f) = f` for every ambient vector,

  `numberResolventDomain (numberShift g) = g` for every true-domain vector.

  Thus `numberShift_bijective` establishes onto and injective behavior with
  exactly the intended source domain and whole completed Fock target.
- `319faa8`, `OrnsteinUhlenbeckNumberResolventPositive.lean`:
  real coordinate weights prove symmetry of the actual bounded map and
  `numberResolvent_adjoint`, its genuine Hilbert adjoint equality. The
  quadratic form is nonnegative on every completed Fock vector. The pinned
  Hilbert-operator positivity characterization then proves
  `numberResolvent_nonneg` in the FULL bounded-operator cone.

## Exact domain and positivity scope

The range theorem uses the actual weighted output norm bound, not an assumed
regularity interface. The inverse identities are coordinatewise identities of
actual completed Fock vectors, and their source is the genuine number-operator
domain rather than a finite-grade span or quadratic-form domain.

The resolvent itself is a bounded self-adjoint positive Hilbert operator. No
generic unbounded-self-adjoint package is assumed for the number operator.
Its separately verified exact weak-adjoint graph and closed graph are preserved
as earlier results. Positivity here is the real full Hilbert-operator cone;
it is not a merely conditional Gram-matrix positivity assertion.

## Verification

All three final focused builds completed with exit code zero under the common
build lock. Fifteen principal direct axiom audits completed with exit code zero
and used only `propext`, `Classical.choice`, and `Quot.sound`. Proof-source
integrity and whitespace diff checks passed. Every atomic mathematical commit
was pushed successfully before subsequent work. Frozen number-operator,
symmetry, intrinsic OU and ambient sources were unchanged.

## Remaining mathematical obligations

The bounded inverse is a concrete operator-domain prerequisite. It does not by
itself verify strong differentiation of the OU degree semigroup. A genuine
infinitesimal-generator theorem still requires a Hilbert norm limit of difference
quotients on the weighted operator domain, using the nonnegative-time/right-sided
domain at time zero. The quadratic-form domain and its closed form remain
separate from that operator domain.

Whole-von-Neumann GNS/cyclic L2 completion, order-supremum normality of the
intrinsic OU map, intrinsic L1 extension, hypercontractivity, logarithmic Sobolev
inequalities, and entropy results remain separate obligations. No general
negative-time damping map or global WOT continuity on unbounded nets is inferred.
