# Genuine ordinary pairing distance

Verified source milestone `e844941`:
`FreeProbability/RandomMatrix/OrthogonalPairingDistance.lean`.
All earlier source milestones remain unchanged.

## Proven results

`pairingDistance p q` is the natural number
`r - pairingLoopCount p q`, where the loop count is the number of classes of
the ORDINARY raw Setoid join of the two intrinsic pairings. Crossing pairings
are included. There is no noncrossing closure and no proposed graph metric
substituted for this definition.

Public declarations in `FreeProbability.Orthogonal`:

- `pairingDistance_eq_zero_iff`: distance zero exactly when the intrinsic
  pairings are equal.
- `pairingDistance_comm`: symmetry.
- `pairingDistance_triangle`: `d(p,s) ≤ d(p,q)+d(q,s)`.
- `card_quotient_join_triangle`: the stronger general finite-partition
  theorem, for arbitrary Setoids `p,q,s` on any finite type,

```
card Quotient(p∨q) + card Quotient(q∨s)
  ≤ card Quotient(q) + card Quotient(p∨s).
```

This includes empty underlying types and half-degree zero without exceptional
assumptions. No distance or partition-rank inequality is supplied as a premise.

## Mathematical proof

For a finite equivalence relation `s`, let `C(s)` be the real vector space of
functions constant on its classes. Pullback along the actual quotient map
is injective and has precisely this range, so `dim C(s)=card Quotient(s)`.
The raw join satisfies `C(s∨t)=C(s)∩C(t)` by the universal property of Setoid
supremum.

Put `X=C(p)∩C(q)` and `Y=C(q)∩C(s)`. Then `X+Y⊂C(q)` and
`X∩Y⊂C(p)∩C(s)`. The actual finite-dimensional identity
`dim(X+Y)+dim(X∩Y)=dim X+dim Y` proves the general inequality.
Every pairing has `r` quotient classes, so this gives the stated triangle
inequality after natural subtraction with the already verified loop bounds.

## Verification and failed engineering approaches

Focused compilation passed without warnings (3023 jobs). All four public
results' transitive dependency audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. Source-integrity and whitespace checks
passed, and the source commit was pushed immediately.

An initial use of the nonexistent capitalized Setoid field `Rel` was fixed
to the actual field `r`. Rewriting local submodule definitions under finrank
then exposed dependent typeclass instances, making rewrite motives ill-typed.
Taking `congrArg` of the actual submodule equality with the explicitly typed
function `S ↦ finrank ℝ S` resolved the transport. No mathematical hypothesis
or desired statement changed. Graph connectivity, pairing-switch distance
and partition-library submodularity were unnecessary alternative routes.

## Next dependency

The distance triangle now gives exponent control for products along paths in
the normalized Gram error matrix. A separate genuine Neumann-series/path
argument is still required for sharp actual inverse-entry rates
`N^r |G_N^{-1}(p,q)| = O(N^{-d(p,q)})`. No such sharper rate is claimed here.
It should use the literal inverse identities and true convergent series,
with finite path-count estimates and separately bounded tail terms.
Actual normalized trace expansion, deterministic contraction bounds,
centered leading cancellation, fluctuations and random convergence modes
remain the later obligations documented in the entry-moment notes.
