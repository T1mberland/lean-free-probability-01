# Finite matrix semicircular development notes

## Scope and actual inverse route

The matrix branch constructs actual finite complex matrix conditional expectations,
completely positive scalar-state amplifications, and covariance
`eta(D) = sum_i C_i * D * C_i`, realized by genuine scalar Fock semicirculars.
It does not construct a correspondence/Fock model for an arbitrary C-star base
algebra and arbitrary completely positive covariance. That Goal 4 obligation is open.

The scalar vacuum boundary identity and vacuum-projection contraction hold for
every bounded operator. Matrix amplifications preserve coefficient order:

- `[diag(rightAnnihilation i), H] = embed(C_i) * diag(vacuumProjection)`;
- `E(T * embed(C_i) * diag(vacuumProjection) * S) = E(T) * C_i * E(S)`.

The inverse commutator identity yields actual resolvent integration by parts
without power-series convergence or analytic continuation. Commits `b875863`,
`ada440a`, and `4614f12` prove actual scalar, arbitrary matrix-argument, and affine
matrix-pencil Dyson identities. Their exact domains are invertibility of the actual
operator difference. Hermitian scalar-argument pencils admit every nonreal argument.
Determinant multiplicativity verifies the averaged inverse matrix is invertible.
Faithfulness and traciality are not required for these identities.

The coefficient bounded-operator algebra uses its canonical spectral order locally
to synthesize the genuine CStarMatrix norm and C-star structure. This is a definition,
not an added positivity hypothesis.

## Imaginary-part checkpoint and regression

`8775e6e` was a published **unverified regression**, not a verified milestone.
A final linter cleanup removed a real arithmetic step in the complex coefficient
proof after an earlier successful compile. The worker mistakenly committed before
inspecting the combined verification output. The coordinator was notified immediately
and excluded that commit from integration.

Corrective commit `efc7f32` restores the precise real/imaginary proof. The worker
inspected the successful warning-free focused build, exact declaration audit,
source-integrity guard and diff before committing and publishing this correction.
The combined source verifies the actual identity
`-Im(m(z)) = Im(z) * E(R(z) * R(z)^*)` and upper-half-plane positive semidefiniteness.
Integrating `8775e6e` requires `efc7f32` and renewed integration checks.
Strict positive definiteness was subsequently verified in `2517611` and `aa623b8`: actual inverse matrices have strictly positive vacuum Gram forms by injectivity on finite vacuum vectors, with no faithfulness assumption on all bounded operators. The genuine affine matrix Cauchy transform consequently has strictly negative Hermitian imaginary part throughout the upper half-plane. Pointwise uniqueness among all negative-imaginary matrices at a fixed argument remains open.

Actual analytic milestones `f0f64be` and `c72773e` subsequently establish derivative
`-E(R^2)`, analyticity on the actual open resolvent domain, decay to zero, and
normalization `z m(z) -> I` at infinity. The CLM continuity construction uses
the explicitly chosen elementwise supremum norm on its ordinary matrix target;
its entry bound is not a C-star matrix contractivity theorem.

Actual analytic branch uniqueness was subsequently proved in `eb9cf12` and
`4247301`: any branch analytic in the upper half-plane, satisfying Dyson and
normalized `z F(z) -> I` at infinity WITHIN that domain, equals the actual affine
Fock matrix Cauchy transform. The actual branch supplies its own analyticity,
normalization, and strict imaginary-part sign. The proof uses the exact ordered
Dyson difference identity, row operator norm contraction near infinity, and the
analytic identity principle on a connected open domain. This does not prove
uniqueness of all pointwise matrix solutions at one fixed argument.

`406666b` gives the sufficient genuine norm-exterior resolvent domain
`|z| > norm(P)`, including both real exteriors and the empty matrix dimension.
This norm-bound theorem is only a sufficient special case.

`7ae6c69` proves preservation of the actual full positive C-star matrix cone for
every scalar state and every finite matrix dimension, via square-cone closure
and verified Gram positivity. `5406b9d` then proves genuine positive definite
Cauchy transforms and actual inverse Dyson on the FULL real right exterior
`forall t in spectrum Real P, t < x`, including empty dimensions. The true inverse
is positive by continuous functional calculus; positivity plus verified finite
matrix invertibility gives strict positive definiteness. No faithfulness of the
vacuum state on all bounded operators is assumed.

`6692fe8` derives the actual Lyapunov derivative identity
`d = -m^2 + m eta(d) m`, where `d = -E(R^2)`, at every genuine resolvent point.
`5f94a49` proves actual matrix creator Gram contraction; `872b04d` supplies an
actual positive star-algebra embedding of deterministic matrices. The exact
completion-of-square certificate `fb67bf9` proves, for EVERY positive definite Z,
`P <= embed(C0 + Z + eta(Z^-1))`, without positivity or commutativity of the
Hermitian coefficients. Empty dimensions are included in this comparison.

`0eebeb2` defines real spectral maxima and identifies the finite Hermitian matrix
maximum with its actual largest eigenvalue. `094e84d` proves the full finite-matrix
core variational formula for the genuine Fock top edge:
`sup spectrum Real P = inf_{Z.PosDef} lambdaMax(C0 + Z + eta(Z^-1))`.
The matrix dimension is nonempty so its genuine spectral maximum exists. The
upper bound uses the true square certificate; every x above the edge supplies
an actual positive definite witness Z = m(x)^-1 with variational matrix x I.
No minimizer at the edge, singular limit, or quantitative truncation is asserted.
This core theorem does not alone complete all auxiliary obligations of Goal 5.

## Next dependencies

1. Positive-state and density-matrix spectral-edge inequalities, further
   exterior bounds, quantitative finite-depth Fock approximations, and singular
   or deterministic edge certificates.
2. Matrix upper-half-plane argument invertibility and pointwise physical
   uniqueness, beyond the normalized analytic branch theorem.
3. Compatibility with the generated closed matrix C-star model and analytic norm
   bounds required by general interfaces. Norm choices must be explicit: entry
   bounds give contractivity into the elementwise supremum norm, whereas a row
   operator norm incurs dimension factors and full C-star matrix contractivity
   requires an actual unital completely positive argument.
4. General arbitrary-base completely positive covariance realization.

## Proof engineering observations

Generic rewrite inference on semireducible matrix/CStarMatrix actions can select
unintended function-space instances. Explicit typed arguments to `Matrix.smul_mul`,
`star_sub`, `star_smul`, and `sub_smul` resolve the concrete instances. Entrywise
finite matrix sums should use `Matrix.sum_apply`. These are elaboration issues,
not mathematical obstructions. Inspect each verification result before publication;
a successful source guard does not imply a successful build.

A failed Lyapunov proof approach rewrote the self-referential rearrangement
`d = -(m^2 - m eta(d) m)` across the entire target. This rewrote occurrences
of d inside its own right-hand side and exhausted elaboration heartbeats, even
with a large limit. A directional calculation proves the same identity promptly
at the default limit; no increased limit remains in the published theorem.
