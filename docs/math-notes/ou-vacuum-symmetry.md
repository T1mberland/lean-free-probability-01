# Whole-double-commutant OU state symmetry

These results concern the actual intrinsic OU CP maps on the literal prescribed-
field double commutant. The field family is arbitrary: no orthonormality,
spanning, countability, or nontriviality assumption is needed for the stated
identities. For an orthonormal family, the independently verified faithful
vacuum state gives the genuine faithful state-L2 interpretation.

## Verified milestones

- `d4cf1e4`, `OrnsteinUhlenbeckVonNeumannVacuumSymmetry.lean`:
  `degreeDamping_inner_symmetric` and `degreeDamping_adjoint` prove that the
  actual completed-Fock degree operator is self-adjoint. The proof uses its
  real scalar weights and the actual ℓ² inner-product sum. The actual state
  cross quadratic form is exactly the actual vacuum inner product.
  `ouVonNeumannTimeCP_state_symmetric` proves, for EVERY pair of elements in
  the whole double commutant,

  `τ(P_t(A)* B) = τ(A* P_t(B))`.

- `b7421a8`, `OrnsteinUhlenbeckVonNeumannVacuumSymmetryPositive.lean`:
  the actual degree semigroup and self-adjointness give the exact identity

  `τ(A* P_t(A)) = ‖P_(t/2)(A) Ω‖² = τ(P_(t/2)(A)* P_(t/2)(A))`.

  Consequently the correlation is nonnegative in the genuine complex order,
  and its real part is at most `τ(A* A)`. These are state identities and bounds
  for the actual CP map on every algebra element, not just finite Wick sums.

## Dependencies and checks

The proof uses the previously verified all-operator vacuum-damping identity
`P_t(T) Ω = D_t(T Ω)`. It assumes no polynomial-density assertion for the double
commutant, WOT-closure equivalence, or all-ambient-operator semigroup law.

Both final focused builds completed with exit code zero under the shared build
lock. Eight principal direct axiom audits completed with exit code zero and
used only `propext`, `Classical.choice`, and `Quot.sound`. Source-integrity and
whitespace diff checks passed. Both atomic mathematical commits were pushed
successfully before subsequent work. Earlier frozen sources were unchanged.

## Remaining obligations

The statements above establish actual bounded degree-operator self-adjointness,
whole-algebra state symmetry, and positive half-time correlations. They do not
construct an unbounded number operator or assert differentiation of the
semigroup on unspecified vectors. A generator theorem must specify its true
square-summability domain and verify differentiation there. A Dirichlet-form
domain may differ from the operator domain and must not be silently conflated
with it.

Normality as preservation of bounded increasing positive suprema, complete
whole-von-Neumann GNS/cyclic L2 extension, intrinsic L1 extension,
hypercontractivity, logarithmic Sobolev inequalities, and entropy results remain
separate obligations. Global WOT continuity on unbounded nets and operator-norm
time continuity on the whole double commutant are not inferred from these
state-symmetry identities.
