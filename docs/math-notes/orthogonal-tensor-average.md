# Actual orthogonal tensor representation and averaging coefficients

Verified milestone `2196e3f` on `feat/compact-haar-averaging`:
`RandomMatrix/OrthogonalTensorAverage.lean`. It depends on actual compact Haar
averaging `37af4ef`, genuine orthogonal projection `eb16668`, and notes `34dcc10`.
The two compact averaging modules and this tensor module are frozen after this
checkpoint. Goal certification and integration remain coordinator-owned.

## Exact proved scope

For EVERY tensor order k and EVERY finite real coordinate type n, define the
actual tuple-coordinate matrix T_k(U) by
T_k(U)(i,j) = product over a in Fin k of U(i(a),j(a)).

`tensorPowerMatrix_mul`, `tensorPowerMatrix_one`, and
`tensorPowerMatrix_mem_orthogonal` prove genuine multiplication, identity and
orthogonality. Multiplication expands a product of coordinate sums into the FULL
sum over ALL tuples via `Fintype.prod_sum`. This supplies the actual group
homomorphism, rather than assuming a representation law or a tensor formula.

The actual orthogonal matrix is transported through the established Euclidean
continuous-linear star homomorphism and the genuine unitary/operator isometry
equivalence. `tensorPowerRepresentation` proves continuous vector orbits directly
from its coordinate products and sums.

`tensorPowerAverage_orthogonal_projection` proves that the ACTUAL normalized Haar
Bochner average is self-adjoint and idempotent, with EXACT range the invariant
tensors and EXACT kernel their orthogonal complement.

`tensorPowerAverage_basis_coefficient` identifies EACH literal coordinate of its
actual averaged tuple basis vector with the GENUINE Haar matrix-entry integral
`entryMoment i j`. This is a proof about actual integrals, not a formal pairing
sum or an assumed Weingarten expression.

Order zero is included: the empty tuple type is a singleton even if n is empty,
and the zeroth representation is the scalar identity. Empty n at positive order
has the genuine zero-dimensional space. No positivity, generic dimension or
nonempty coordinate assumption excludes these cases.

## Verification and remaining mathematical obligations

The module compiles warning free under the common lock. Six principal declarations
passed transitive standard-logic audits; literal coefficient and exact projection
statements were inspected. Integrity guard and staged diff checks passed before
the atomic commit, which was immediately pushed.

Failed elaborations concerned deprecated conditional spelling, opposite scalar
multiplication in matrix-column application, and the scalar of the coordinate
continuous-linear projection. They were repaired without statement changes.

Next construct ACTUAL vectors for ALL ordinary pairings and prove invariance from
actual row orthogonality. Noncrossing pairings alone are insufficient for orthogonal
integration. Spanning of ALL invariant tensors by ordinary pairing vectors is a
separate first fundamental theorem. Pairing Gram inverse/pseudoinverse formulas
also need exact degeneracy treatment in small dimensions. These are not assumed
by this milestone. Joint asymptotic freeness and probability/almost-sure/strong
convergence estimates remain separate further obligations.
