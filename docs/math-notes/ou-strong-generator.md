# Exact right strong OU generator on completed tensor Fock space

This checkpoint verifies the actual right-sided Hilbert-norm derivative of
nonnegative-time degree damping for every vector in the genuine number-operator
domain, and proves the converse domain characterization. The ambient space is
the actual complete sum of recursively completed tensor powers for any complete
complex Hilbert space, with no cardinality or nontriviality assumption.

## Verified source milestones

- `a778d08`, `OrnsteinUhlenbeckGeneratorScalar.lean`:
  the actual real coefficient `exp(-t)^n` has derivative `-n` at zero. The error
  `e_n(t)=(exp(-t)^n-1)/t+n` tends to zero from the right and satisfies the sharp
  bound `0≤e_n(t)≤n` for every `t>0`. This follows from the genuine exponential
  inequality and upper bound, including degree zero.
- `a677f5d`, `OrnsteinUhlenbeckGeneratorError.lean`:
  the error vector is constructed in complete Fock space for every vector in
  the EXACT weighted operator domain. Coordinate squared norms are dominated
  by `‖(Nf)_n‖²`, whose sum is finite by actual square summability of `Nf`.
  The pinned Tannery dominated-sum theorem, the actual ℓ² norm formula, and
  square-root continuity prove its full Hilbert-norm zero limit. This is not
  just coordinate convergence or a finite-grade special case.
- `452c87c`, `OrnsteinUhlenbeckGeneratorDerivative.lean`:
  `ouGeneratorDamping H t` is the actual bounded degree map at `max(t,0)`.
  It equals the original map for nonnegative time. The constructed error
  vector is proved equal to the genuine difference quotient plus `Nf` there.
  `ouGenerator_right_tendsto` proves the actual norm limit

  `(D_t f-f)/t → -Nf` as `t→0` through positive times,

  for EVERY vector in the exact weighted operator domain.
- `495071d`, `OrnsteinUhlenbeckGeneratorDomain.lean`:
  the genuine quotient is defined for every ambient vector. If any strong
  right quotient limit `z` exists, continuous evaluation in every actual
  completed tensor grade forces `z_n=-n f_n`. Square summability of the
  actual vector `-z` forces `f` into the exact operator domain. Consequently
  `ouGenerator_graph_iff` identifies the FULL actual right strong generator
  graph with `-N`, and `ouGenerator_domain_iff` says strong quotient-limit
  existence is exactly membership in that domain.
- `990bb91`, `OrnsteinUhlenbeckGeneratorCalculus.lean`:
  real-variable slope and the complex-scaled quotient are proved equal via
  the actual scalar tower. `ouGenerator_hasDerivWithinAt` supplies the
  standard derivative interface at zero within `Set.Ici 0`.
  `ouGenerator_hasDerivWithinAt_iff` proves its exact converse graph/domain
  characterization, not merely a sufficient domain restriction.

## Proper time and operator domains

The actual semigroup is bounded on nonnegative time. The total real-time
function above uses time zero at negative times solely to supply a legitimate
real-variable derivative-within-set interface. All generator statements concern
right-sided time or `Set.Ici 0`. No negative-time bounded exponential map on all
Fock vectors, nor an unrestricted two-sided derivative at zero, is asserted.

The derivative domain is exactly square summability after multiplying tensor
degree `n` by `n`. The proof does not replace this operator domain by the
quadratic-form domain or by finite-grade vectors. The converse establishes that
there are no extra strong right differentiable vectors outside this domain.

## Verification and proof decisions

All five final focused builds completed with exit code zero under the common
build lock. Twenty principal direct axiom audits completed with exit code zero
and used only `propext`, `Classical.choice`, and `Quot.sound`. Proof-source
integrity and whitespace diff checks passed. Each atomic mathematical commit
was pushed successfully before subsequent work. Frozen number-operator,
resolvent, state-symmetry, and intrinsic OU sources were unchanged.

The domination is sharper than the initial proposed factor-two norm bound:
`|e_n(t)|≤n` suffices. The square bound is exactly the genuine `Nf` squared norm,
so no added summability assumption is introduced. The reverse direction uses
continuous coordinate evaluation and uniqueness of actual Hilbert limits.

## Remaining obligations

The full completed-Fock right strong generator and its exact domain are now
verified. A separately packaged generic unbounded-operator or C0-semigroup
interface has not been introduced. Its literal graph characterization is
available for any such future packaging.

Transport of this generator to a separately identified whole-von-Neumann
GNS/cyclic L2 completion, the distinct closed quadratic-form package,
order-supremum normality of intrinsic OU, intrinsic L1 extension,
hypercontractivity, logarithmic Sobolev inequalities, and entropy results remain
separate obligations. No operator-norm time differentiability on the whole
von Neumann algebra follows from the Hilbert-vacuum generator theorem alone.
