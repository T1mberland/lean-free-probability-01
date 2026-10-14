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
Strict positive definiteness and physical analytic branch uniqueness remain open.

## Next dependencies

1. Strict positive definiteness of the imaginary part for actual inverse matrices.
2. Matrix upper-half-plane argument invertibility and analytic branch uniqueness,
   beyond an invertibility-conditioned Dyson identity.
3. Compatibility with the generated closed matrix C-star model and analytic norm
   bounds required by general interfaces.
4. General arbitrary-base completely positive covariance realization.

## Proof engineering observations

Generic rewrite inference on semireducible matrix/CStarMatrix actions can select
unintended function-space instances. Explicit typed arguments to `Matrix.smul_mul`,
`star_sub`, `star_smul`, and `sub_smul` resolve the concrete instances. Entrywise
finite matrix sums should use `Matrix.sum_apply`. These are elaboration issues,
not mathematical obstructions. Inspect each verification result before publication;
a successful source guard does not imply a successful build.
