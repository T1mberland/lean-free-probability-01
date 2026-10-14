# Actual compact Haar averaging as orthogonal projection

Branch `feat/compact-haar-averaging` starts from checked main `bbdba56`.
This is a genuine general integration prerequisite for Goal 9, not an assumed
pairing formula or a claim of random-matrix asymptotic freeness.

## Verified source milestones

- `37af4ef`, `Algebraic/CompactHaarAverage.lean`: actual compact Haar measure
  normalized on the WHOLE group; continuous isometric representation; actual
  Bochner averaging operator, genuine integrability, linearity and contraction
  bound one; exact range equals the group-fixed vectors; actual idempotency.
- `eb16668`, `Algebraic/CompactHaarAverageProjection.lean`: genuine symmetry
  and self-adjointness of the bounded averaging operator; operator idempotency;
  `LinearMap.IsProj` onto the actual fixed-vector subspace; exact kernel equals
  its orthogonal complement; actual residual is orthogonal to all fixed vectors.

`CompactIsometricRepresentation.averageCLM_orthogonal_projection` bundles
self-adjointness, idempotency, exact fixed range and exact orthogonal kernel.
Every part is derived from actual normalized Haar integration, continuity and
the genuine isometric group action. Projection, pairing, invariant-tensor
spanning and first fundamental theorem hypotheses are NOT assumed.

## Exact scope

The averaging results currently use REAL Hilbert representations, consistent
with the orthogonal integration application. The generic representation structure
also accepts compatible complex unitary spaces, but complex-linear averaging
and complex self-adjoint projection results are not asserted by this checkpoint.
Initial generic scalar elaboration required an explicit coherent real scalar
restriction; the verified target was fixed to the approved real orthogonal case.

The group is an arbitrary compact topological group with its Borel measure
structure; the normalized actual Haar construction supplies probability and
left invariance. The Hilbert target is complete and can be infinite dimensional.
There is no finite-dimensional restriction on the proved projection theorem.
Continuity is required for each genuine vector orbit, not an assumed tensor
coefficient formula. Integrability follows from continuous compact support.

Left invariance makes the actual averaged vector invariant. Integrating a
constant orbit preserves any invariant vector. Isometry preserves inner products
against fixed vectors, so the actual integral is symmetric; this proves
self-adjointness without adding an inversion-invariance premise.

## Verification and remaining dependencies

Both modules compile warning free under the common build lock. Important results
passed transitive standard-logic audits; exact range and bundled projection
statements were inspected. Integrity guard and staged diff checks passed before
atomic commits, and every commit was immediately pushed.

Failed elaborations concerned real scalar restriction, probability real-measure
lemma naming, explicit integral measure inference, bundled linear-map reduction,
inner-product notation scope and the scalar parameter of inner_self_eq_zero.
All were repaired before publication. No resource failure occurred.

Next construct the ACTUAL orthogonal tensor representation and identify its Haar
averaging matrix coefficients with genuine entry integrals. Spanning of invariant
tensors by pairings is an additional first-fundamental-theorem obligation; only
then can pairing Gram inverse or pseudoinverse formulas be justified, with low
dimension degeneracies treated honestly. General joint asymptotic estimates and
probability/almost-sure/strong convergence remain distinct further obligations.
Integration and goal certification are coordinator-owned.
